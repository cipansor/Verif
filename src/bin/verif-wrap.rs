//! `RUSTC_WRAPPER` entry point: verify a crate's contracts as part of `cargo build`.
//!
//! `RUSTC_WRAPPER=/path/to/verif-wrap cargo build` forwards every `rustc` call
//! through this binary. For the *primary* package -- cargo sets
//! `CARGO_PRIMARY_PACKAGE=1` for the crate being built, and never for a
//! dependency -- it additionally runs `verif`'s frontend on the crate source and
//! fails the build if a contract does not hold. Every other call (a dependency, a
//! build script, a proc-macro) is forwarded untouched, so the wrapper verifies
//! exactly the crate under development and nothing it depends on.
//!
//! This is the `RUSTC_WRAPPER` half of C8: verification that runs as part of the
//! normal build, with no separate `cargo verif` step to remember.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

fn main() -> ExitCode {
    let mut it = std::env::args_os().skip(1);
    let Some(rustc) = it.next() else {
        eprintln!("verif-wrap: no compiler given; set RUSTC_WRAPPER to this binary only");
        return ExitCode::from(2);
    };
    let args: Vec<OsString> = it.collect();

    if std::env::var("CARGO_PRIMARY_PACKAGE").as_deref() == Ok("1") && !is_build_script(&args) {
        if let Some(src) = source_arg(&args) {
            if let Err(code) = verify(&rustc, Path::new(&src), &args) {
                return code;
            }
        }
    }

    match Command::new(&rustc).args(&args).status() {
        Ok(s) => ExitCode::from(u8::try_from(s.code().unwrap_or(1)).unwrap_or(1)),
        Err(e) => {
            eprintln!("verif-wrap: could not run {}: {e}", rustc.to_string_lossy());
            ExitCode::from(2)
        }
    }
}

/// The crate's source file among rustc's arguments: the positional argument that is an
/// existing file, *after* consuming option values. A flag value can itself be an existing
/// file -- `--crate-name app` where `app` is an extensionless binary root -- so the value
/// of every value-taking flag is skipped before the filesystem is consulted, or the
/// wrapper would verify the wrong file and leave the real target's contracts unchecked.
fn source_arg(args: &[OsString]) -> Option<OsString> {
    let mut skip_next = false;
    for a in args {
        let s = a.to_string_lossy();
        if skip_next {
            skip_next = false;
            continue;
        }
        if s.starts_with('-') {
            if takes_value(&s) {
                skip_next = true;
            }
            continue;
        }
        if Path::new(a.as_os_str()).is_file() {
            return Some(a.clone());
        }
    }
    None
}

/// rustc flags that take a separate value argument (so the next argument is not the input).
fn takes_value(flag: &str) -> bool {
    matches!(
        flag,
        "--crate-name"
            | "--crate-type"
            | "--edition"
            | "--emit"
            | "--out-dir"
            | "-o"
            | "--extern"
            | "-L"
            | "--cfg"
            | "--target"
            | "--print"
            | "-C"
            | "--cap-lints"
            | "--color"
            | "--error-format"
            | "--json"
            | "--sysroot"
            | "-A"
            | "-W"
            | "-D"
            | "-F"
            | "--remap-path-prefix"
            | "--check-cfg"
            | "-Z"
            | "--diagnostic-width"
            | "--env-set"
    )
}

/// Is this rustc invocation compiling a package's `build.rs`? Cargo names a build
/// script `build_script_build`, and a build script may use `[build-dependencies]` that
/// `crate_options` does not resolve, so it is forwarded unchanged rather than verified.
fn is_build_script(args: &[OsString]) -> bool {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let s = a.to_string_lossy();
        if s == "--crate-name" {
            if let Some(v) = it.next() {
                return v.to_string_lossy().starts_with("build_script");
            }
        } else if let Some(v) = s.strip_prefix("--crate-name=") {
            return v.starts_with("build_script");
        }
    }
    false
}

/// The invocation's own `--extern`/`-L dependency=` arguments, canonicalised. These are
/// Cargo's *exact* artifacts for this target, profile and feature set -- the crate's own
/// library, renamed deps (the alias is the `--extern` name, not the artifact basename),
/// and a custom or workspace target directory -- so forwarding them beats re-deriving
/// from `[dependencies]` and ranking rlibs by modification time.
fn invocation_externs(args: &[OsString]) -> (Vec<(String, PathBuf)>, Vec<PathBuf>) {
    let mut externs = Vec::new();
    let mut paths = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let s = a.to_string_lossy();
        if let Some(v) = s.strip_prefix("--extern=") {
            push_extern(&mut externs, v);
        } else if s == "--extern" {
            if let Some(v) = it.next() {
                push_extern(&mut externs, &v.to_string_lossy());
            }
        } else if s == "-L" {
            // Cargo may pass `-L dependency=…` as two arguments; the joined form is
            // `-Ldependency=…`. The two-arg form left `paths` with an empty entry
            // (from `strip_prefix("-L")` on `-L`), which the MIR emitter then passed
            // as `-L dependency=` -- rustc rejects it and the build stops.
            if let Some(v) = it.next() {
                push_search(&mut paths, &v.to_string_lossy());
            }
        } else if let Some(v) = s.strip_prefix("-L") {
            push_search(&mut paths, v);
        }
    }
    (externs, paths)
}

fn push_extern(externs: &mut Vec<(String, PathBuf)>, v: &str) {
    if let Some((name, path)) = v.split_once('=') {
        externs.push((name.to_string(), canonical(Path::new(path))));
    }
}

fn push_search(paths: &mut Vec<PathBuf>, v: &str) {
    // `-L kind=path` or `-L path`; only dependency search paths matter to the emit.
    match v.split_once('=') {
        Some((kind, path)) if kind == "dependency" || kind == "all" => {
            paths.push(canonical(Path::new(path)))
        }
        Some(_) => {}
        None => paths.push(canonical(Path::new(v))),
    }
}

fn canonical(p: &Path) -> PathBuf {
    std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf())
}

/// Run the frontend on `src`. A failed verdict prints the failing functions and
/// returns exit code 1; a setup error is also a failure, because a wrapper that
/// silently verified nothing would look like it had.
fn verify(rustc: &OsString, src: &Path, args: &[OsString]) -> Result<(), ExitCode> {
    let rustc = rustc.to_string_lossy().into_owned();
    // Cargo passes the crate's source as a path relative to the build directory.
    // `crate_options` walks up from the file to find the manifest and its
    // `target/`, which a relative path resolves against the *process* cwd -- so
    // canonicalise first, or the dependency rlibs are never found.
    let src = std::fs::canonicalize(src).unwrap_or_else(|_| src.to_path_buf());
    let src = src.as_path();
    // A cross target with a different pointer width or endianness is a program the
    // model does not represent (it hardcodes 64-bit `usize` and its own byte order),
    // so a proof would be about a different layout -- refuse rather than pass.
    if let Some(reason) = target_refusal(&rustc, args) {
        eprintln!(
            "verif-wrap: refusing to verify for this target: {reason}. The executor models \
             `usize` at 64 bits and `to_be`/`to_le` at its own endianness; build without the \
             wrapper for a target it does not model."
        );
        return Err(ExitCode::from(2));
    }
    let mut opts = verif::mir::verify::crate_options(src);
    // The invocation's own `--extern`/`-L` are Cargo's *exact* artifacts for this
    // target, profile and feature set (the crate's own library, renamed deps, a custom
    // or workspace target dir), so forward them rather than re-deriving from
    // `[dependencies]` and ranking rlibs by mtime.
    let (externs, search_paths) = invocation_externs(args);
    if !externs.is_empty() {
        opts.externs = externs;
        opts.probed_with = None;
    }
    if !search_paths.is_empty() {
        opts.search_paths = search_paths;
    }
    // Cargo passes `--cfg feature="..."` (and `--target`) to the real compilation.
    // The MIR emit is a *separate* compilation, so without them a `cfg!(feature=...)`
    // would evaluate the other way and the verifier could approve a contract the
    // build violates. Forward the semantic flags (not the output ones).
    opts.rustc_args = semantic_args(args);
    match verif::mir::verify::verify_file_with_opts(&rustc, src, &[], &opts) {
        Ok(report) if report.is_clean() => Ok(()),
        Ok(report) => {
            eprintln!("verif-wrap: {}: verification failed", src.display());
            for (name, outcome) in &report.outcomes {
                if !outcome.is_verified() {
                    eprintln!("  {name}: {outcome}");
                }
            }
            for m in &report.missing {
                eprintln!("  {m}: MISSING (contract carried, no MIR body)");
            }
            Err(ExitCode::from(1))
        }
        Err(e) => {
            eprintln!("verif-wrap: could not verify {}: {e}", src.display());
            Err(ExitCode::from(1))
        }
    }
}

/// The `--cfg` and `--target` arguments of a rustc invocation, in `--flag value` or
/// `--flag=value` form. These change what `cfg!(...)` evaluates to and which target
/// the program is for, so the MIR emit must see them; output flags (`--out-dir`,
/// `--emit`) must not, because the emit replaces them.
fn semantic_args(args: &[OsString]) -> Vec<String> {
    let mut out = Vec::new();
    let mut it = args.iter().peekable();
    while let Some(a) = it.next() {
        let s = a.to_string_lossy();
        if s == "--cfg" || s == "--target" {
            if let Some(v) = it.next() {
                out.push(s.into_owned());
                out.push(v.to_string_lossy().into_owned());
            }
        } else if s.starts_with("--cfg=") || s.starts_with("--target=") {
            out.push(s.into_owned());
        }
    }
    out
}

/// Why the model cannot represent the `--target` in `args`, if it cannot.
fn target_refusal(rustc: &str, args: &[OsString]) -> Option<String> {
    let mut target: Option<String> = None;
    let mut it = args.iter().peekable();
    while let Some(a) = it.next() {
        let s = a.to_string_lossy();
        if s == "--target" {
            target = it.next().map(|v| v.to_string_lossy().into_owned());
        } else if let Some(t) = s.strip_prefix("--target=") {
            target = Some(t.to_string());
        }
    }
    let target = target?;
    let out = Command::new(rustc)
        .args(["--print", "cfg", "--target", &target])
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    let (mut ptr, mut endian) = (None, None);
    for line in text.lines() {
        if let Some(v) = line.strip_prefix("target_pointer_width=") {
            ptr = Some(v.trim_matches('"').to_string());
        }
        if let Some(v) = line.strip_prefix("target_endian=") {
            endian = Some(v.trim_matches('"').to_string());
        }
    }
    let host_endian = if cfg!(target_endian = "little") { "little" } else { "big" };
    let mut reasons = Vec::new();
    if let Some(p) = &ptr {
        if p != "64" {
            reasons.push(format!("pointer width {p}, but the model is 64-bit"));
        }
    }
    if let Some(e) = &endian {
        if e != host_endian {
            reasons.push(format!("endianness {e}, but the model is {host_endian}"));
        }
    }
    if reasons.is_empty() { None } else { Some(reasons.join("; ")) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Cargo passes `-L dependency=…` as **two** arguments; the joined `-Ldependency=…` is
    /// the other form. The two-arg form used to leave `paths` with an empty entry (from
    /// `strip_prefix("-L")` on a bare `-L`), which the MIR emitter passed as
    /// `-L dependency=` -- rustc rejects it and the build stops.
    #[test]
    fn invocation_externs_reads_two_arg_l_search_paths() {
        use std::ffi::OsString;
        let args: Vec<OsString> = [
            "--crate-name", "app", "-L", "dependency=/tmp/verif-x", "-L", "all=/tmp/verif-y",
            "-Ldependency=/tmp/verif-z",
        ]
        .iter()
        .map(OsString::from)
        .collect();
        let (_, paths) = invocation_externs(&args);
        assert!(paths.iter().any(|p| p.ends_with("verif-x")), "two-arg dependency path, got {paths:?}");
        assert!(paths.iter().any(|p| p.ends_with("verif-y")), "two-arg all path, got {paths:?}");
        assert!(paths.iter().any(|p| p.ends_with("verif-z")), "joined path, got {paths:?}");
        assert!(
            !paths.iter().any(|p| p.as_os_str().is_empty()),
            "no empty search path may be recorded, got {paths:?}"
        );
    }

    #[test]
    fn source_arg_skips_a_crate_name_value() {
        // `--crate-name app` (a valid Cargo argument: a *bare* name, not a path rustc
        // would reject) must not be taken as the input. The value is skipped because
        // `--crate-name` takes a value (`takes_value`), not because it is not a file.
        assert!(takes_value("--crate-name"));
        let dir = std::env::temp_dir().join(format!("verif_srcarg_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let lib = dir.join("lib.rs");
        std::fs::write(&lib, "\n").unwrap();
        let args = vec![
            OsString::from("--crate-name"),
            OsString::from("app"),
            OsString::from("--edition"),
            OsString::from("2024"),
            lib.clone().into_os_string(),
        ];
        let picked = source_arg(&args).expect("an input");
        assert_eq!(Path::new(&picked), lib.as_path(), "must pick lib.rs, not the crate-name value");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn source_arg_skips_an_existing_crate_name_file() {
        // The regression the bare-name test cannot catch: `--crate-name app` where `app`
        // *is* an existing file. If `--crate-name` were not skipped, `source_arg` would pick
        // `app` (a file) instead of `lib.rs`, so this case actually discriminates.
        let dir = std::env::temp_dir().join(format!("verif_srcarg3_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let lib = dir.join("lib.rs");
        std::fs::write(&lib, "\n").unwrap();
        let app = dir.join("app");
        std::fs::write(&app, "\n").unwrap();
        let args = vec![
            OsString::from("--crate-name"),
            app.into_os_string(),
            OsString::from("--edition"),
            OsString::from("2024"),
            lib.clone().into_os_string(),
        ];
        let picked = source_arg(&args).expect("an input");
        assert_eq!(
            Path::new(&picked),
            lib.as_path(),
            "must pick lib.rs, not the existing `--crate-name` file"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn source_arg_finds_a_custom_extension_path() {
        let dir = std::env::temp_dir().join(format!("verif_srcarg2_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let lib = dir.join("library.rust");
        std::fs::write(&lib, "\n").unwrap();
        let args = vec![OsString::from("--edition"), OsString::from("2024"), lib.clone().into_os_string()];
        let picked = source_arg(&args).expect("an input");
        assert_eq!(Path::new(&picked), lib.as_path(), "a custom-extension input is found by is_file");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_32_bit_target_is_refused_and_the_host_is_not() {
        // The probe needs a real `rustc`; skip if there is none.
        if Command::new("rustc").arg("--version").output().map(|o| !o.status.success()).unwrap_or(true) {
            eprintln!("verif-wrap: no rustc; skipping target_refusal test");
            return;
        }
        // No `--target` means the host layout, which the model assumes.
        assert!(target_refusal("rustc", &[]).is_none(), "the host target is modelled");
        // A 32-bit target's pointer width is not.
        let args = vec![OsString::from("--target"), OsString::from("i686-unknown-linux-gnu")];
        assert!(
            target_refusal("rustc", &args).is_some(),
            "a 32-bit pointer width must be refused"
        );
    }
}

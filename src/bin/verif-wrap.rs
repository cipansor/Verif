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
use std::path::Path;
use std::process::{Command, ExitCode};

fn main() -> ExitCode {
    let mut it = std::env::args_os().skip(1);
    let Some(rustc) = it.next() else {
        eprintln!("verif-wrap: no compiler given; set RUSTC_WRAPPER to this binary only");
        return ExitCode::from(2);
    };
    let args: Vec<OsString> = it.collect();

    if std::env::var("CARGO_PRIMARY_PACKAGE").as_deref() == Ok("1") {
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

/// The crate's source file among rustc's arguments: the one positional argument
/// that ends in `.rs`. A flag *value* (`--crate-name foo`, `--out-dir dir`) does
/// not end in `.rs`, so the input file is the only match.
fn source_arg(args: &[OsString]) -> Option<OsString> {
    args.iter()
        .find(|a| {
            let s = a.to_string_lossy();
            !s.starts_with('-') && s.ends_with(".rs")
        })
        .cloned()
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
    let mut opts = verif::mir::verify::crate_options(src);
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

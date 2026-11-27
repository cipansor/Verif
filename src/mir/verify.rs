//! The end-to-end driver: source in, verdicts out.
//!
//! This is the layer that ties the three stages together and owns the two
//! things the other modules cannot know about: how to get MIR out of `rustc`,
//! and how to decide *which* functions to verify. It is also where the honesty
//! of the whole frontend is enforced, in one rule:
//!
//! > A function is reported verified only when every obligation was proved
//! > *and* every path was explored. A cutoff is reported as a cutoff.
//!
//! That rule is why [`FnOutcome`] has a distinct `Incomplete` state instead of
//! folding cutoffs into `Verified`.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::SystemTime;

use crate::mir::exec;
use crate::mir::parse::{self, MirFn, MirProgram, Ty, USIZE_WIDTH};

// The report types are part of the public verdict surface -- `FnOutcome`
// carries a `MirReport` -- so they are re-exported here rather than leaving a
// crate-internal type in a public signature.
pub use crate::mir::exec::{MirReport, Obligation, ObligationKind};
use crate::mir::spec::{self, SpecError, Specs};
use crate::smt::{self, Verdict};

/// The Rust edition a file is compiled under.
///
/// The frontend has to compile *the program the user ships*, and that program's
/// edition lives in its `Cargo.toml`. Pinning one edition unconditionally is the
/// mistake this type exists to fix: `--edition=2024` refuses a valid 2021 crate
/// (`extern "C" { … }` must be `unsafe` there) and lowers some code differently
/// from the edition that ships, so a verdict could be about a program nobody
/// built. The edition is therefore *resolved* (see [`resolve_edition`]), never
/// assumed, and it is recorded on every report.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Edition {
    /// Rust 2015, `rustc`'s own default.
    Rust2015,
    /// Rust 2018.
    Rust2018,
    /// Rust 2021.
    Rust2021,
    /// Rust 2024, the crate's own edition.
    Rust2024,
}

impl Edition {
    /// The spelling `rustc --edition=` takes.
    pub fn as_str(self) -> &'static str {
        match self {
            Edition::Rust2015 => "2015",
            Edition::Rust2018 => "2018",
            Edition::Rust2021 => "2021",
            Edition::Rust2024 => "2024",
        }
    }

    /// Parse a manifest or override spelling.
    ///
    /// Only the four numeric forms are accepted, so a typo is an error rather
    /// than a silent fallback to an edition the program does not use.
    pub fn parse(s: &str) -> Option<Edition> {
        match s.trim() {
            "2015" => Some(Edition::Rust2015),
            "2018" => Some(Edition::Rust2018),
            "2021" => Some(Edition::Rust2021),
            "2024" => Some(Edition::Rust2024),
            _ => None,
        }
    }
}

impl std::fmt::Display for Edition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "edition {}", self.as_str())
    }
}

/// Options that shape a frontend run.
#[derive(Clone, Debug, Default)]
pub struct MirOptions {
    /// The Rust edition to compile under.
    ///
    /// `None` resolves it: from the nearest `Cargo.toml`'s `package.edition`
    /// first, then `VERIF_EDITION`. A file with neither is an *error*, never a
    /// silent default -- see [`resolve_edition`].
    pub edition: Option<Edition>,
    /// Crates to make resolvable when `rustc` compiles the file, as
    /// `(crate name, rlib path)` pairs.
    ///
    /// This is what lets a source file *name* `verif` -- `use verif::spec;` above
    /// an in-code contract block -- compile at all. The frontend runs `rustc` on a
    /// single file with no Cargo graph behind it, so without an `--extern` entry
    /// every `use verif::…` is `E0432: unresolved import`.
    ///
    /// The paths are the caller's to find: a `build.rs` locates the rlib it is
    /// already linked against ([`extern_options`] does that), and a test passes a
    /// known artifact. The frontend deliberately does not guess a path, because a
    /// guessed rlib is either the wrong compiler's or the wrong features', and
    /// both surface as a compiler error about a program that is fine.
    pub externs: Vec<(String, PathBuf)>,
    /// Extra `-L dependency=` directories `rustc` searches when resolving an
    /// extern's own dependencies.
    ///
    /// An `--extern` names one crate; that crate's *transitive* dependencies are
    /// found only through a search path. `verif` depends on `verif-arithmetic`, so
    /// naming `verif` without a search path for `verif-arithmetic` resolves the
    /// outer crate and then fails on the inner one -- an error naming a crate the
    /// caller never mentioned. [`extern_options`] fills this in.
    pub search_paths: Vec<PathBuf>,
    /// The compiler the externs were *probed* with, when they came from
    /// [`extern_options`] or [`extern_options_with`].
    ///
    /// An rlib's metadata is compiler-specific, so the probe's answer is only about
    /// *that* compiler: a candidate it accepts is not thereby readable by another.
    /// Probing with one toolchain and emitting MIR with another therefore fails
    /// `E0514` -- or worse, silently drops the extern and reports `E0432` for a crate
    /// that is perfectly usable. Recording the probe compiler lets
    /// [`verify_file_with_opts`] refuse the mismatch and name both, rather than
    /// leaving it to a compiler error about a program that is fine.
    ///
    /// `None` means "the caller supplied these by hand", which is not checked: a
    /// hand-built [`MirOptions`] may legitimately name a prebuilt rlib.
    pub probed_with: Option<String>,
    /// A directory for the proof cache (U7), or `None` to verify every run.
    ///
    /// When set, a function whose *decided* verdict (`Verified`/`Failed`) is already
    /// in the cache for this file's key is reused instead of re-verified. The key
    /// covers the MIR text, the source text, the edition and the engine hash, so any
    /// change to the program or the engine is a miss — never a stale hit. Only the
    /// library-side option is here; `cargo verif` sets it from `--cache`.
    pub cache: Option<PathBuf>,
    /// Extra arguments passed verbatim to the MIR-emitting `rustc` invocation.
    ///
    /// The `RUSTC_WRAPPER` entry point fills this with the *semantic* flags Cargo
    /// passes the real compilation -- `--cfg` and `--target` -- so the MIR it emits
    /// is the program Cargo is actually building. Without them, `cfg!(feature =
    /// "fast")` would evaluate to `false` during verification and `true` in the
    /// artifact, and the verifier could approve a contract the build violates (a
    /// false pass). Edition and `--extern` are handled separately (they are part of
    /// [`MirOptions`] proper).
    ///
    /// [`crate_options`] fills it too, from the crate's own manifest and build
    /// script, because `cargo verif --file src/lib.rs` is the *other* way a real
    /// crate reaches the frontend and it has no `RUSTC_WRAPPER` to borrow Cargo's
    /// flags from. A crates.io tarball publishes its dependencies as
    /// `[dependencies.foo]` tables and enables its default features through
    /// `[features]`, and `serde_json` refuses to compile without
    /// `--cfg feature="std"` -- so without this, every published crate failed
    /// `compile_error!` before a single function was read.
    pub rustc_args: Vec<String>,
    /// Environment variables the MIR-emitting `rustc` runs with, as
    /// `(name, value)` pairs.
    ///
    /// Cargo exports the package's metadata to the compiler (`CARGO_PKG_VERSION`
    /// and friends, `CARGO_MANIFEST_DIR`, `CARGO_CRATE_NAME`), and a crate that
    /// reads one with `env!` fails to compile without it. [`crate_options`] derives
    /// the set from the manifest, so a real crate compiles as it does under Cargo.
    /// A caller that needs nothing here leaves it empty; the process environment is
    /// inherited either way.
    pub rustc_env: Vec<(String, String)>,
}

/// Everything a build script needs to let its own source name a crate: the
/// `--extern` entry for `verif`, and the search paths its dependencies live on.
///
/// A `build.rs` is compiled against its `[build-dependencies]`, and Cargo lays those
/// artifacts out under the `build` directory above `$OUT_DIR`. This finds
/// `lib<name>-<hash>.rlib` there and returns it together with the directories the
/// crate's own dependencies live in, so [`MirOptions`] can name `verif` *and*
/// resolve `verif-arithmetic` through it.
///
/// **Two rlibs for one crate name is normal, not an error.** Cargo builds a crate
/// once per unit, so a crate that is both a `[dependencies]` and a
/// `[build-dependencies]` entry (which is what the zero-cost recipe is) has two
/// rlibs of the same name. They are interchangeable for the one job this needs --
/// resolving the crate name so `use verif::spec;` parses -- but they are not
/// interchangeable across *toolchains*, so the choice is **verified rather than
/// guessed**: each candidate in turn is handed to `rustc` on a one-line probe, and
/// the first that compiles is the one returned. A stale rlib from another compiler
/// fails the probe (`E0514`) and the next candidate is tried. `None` means no
/// candidate compiled, which the caller turns into a skipped verification rather
/// than a wrong one.
///
/// The typical `build.rs`:
///
/// ```ignore
/// let opts = verif::mir::verify::extern_options("verif").unwrap_or_default();
/// let report = verif::mir::verify::verify_file_with_opts("rustc", Path::new("src/lib.rs"), &[], &opts)?;
/// ```
#[cfg(feature = "std")]
pub fn extern_options(name: &str) -> Option<MirOptions> {
    // The probe must use the compiler that will *consume* the rlib, which is the
    // MIR emitter -- so this resolves the same way [`verify_file_opts`] does. A
    // rlib's metadata is compiler-specific: an rlib the producing compiler accepts
    // is not thereby acceptable to a different one, so probing with any compiler
    // but the emitter only proves the wrong thing. When the emitter names another
    // toolchain, a candidate it cannot read fails the probe (`E0514`) and the next
    // is tried; `None` then means "no rlib this emitter can read", which is the
    // honest answer. A caller whose emitter is not `VERIF_RUSTC` must use
    // [`extern_options_with`] so lookup and emission name one compiler.
    let rustc = std::env::var("VERIF_RUSTC").unwrap_or_else(|_| "rustc".into());
    extern_options_with(&rustc, name)
}

/// [`extern_options`] with the compiler named explicitly.
///
/// The rlib returned is the one **this** compiler accepts, so the caller must pass
/// the same compiler to [`verify_file_with_opts`]/[`emit_mir_with_opts`]. Use this
/// when the emitter is chosen by the caller rather than by `VERIF_RUSTC` -- a test
/// that pins a specific toolchain, or a build script that resolved its own
/// `rustc`. Mixing the two (probe with one compiler, emit with another) is the
/// `E0514` failure this parameter exists to prevent.
#[cfg(feature = "std")]
pub fn extern_options_with(rustc: &str, name: &str) -> Option<MirOptions> {
    let roots = build_script_roots()?;
    let prefix = format!("lib{}-", name.replace('-', "_"));
    let mut found: Vec<PathBuf> = Vec::new();
    for root in &roots {
        let Ok(entries) = std::fs::read_dir(root) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            let Some(f) = p.file_name().and_then(|s| s.to_str()) else {
                continue;
            };
            if f.starts_with(&prefix) && (f.ends_with(".rlib") || f.ends_with(".rmeta")) {
                found.push(p);
            }
        }
    }
    found.sort();
    found.dedup();
    // Newest first, so a stale artifact from an earlier build is tried last.
    found.sort_by_key(|p| {
        std::cmp::Reverse(
            std::fs::metadata(p).and_then(|m| m.modified()).ok(),
        )
    });
    let search: Vec<PathBuf> = roots;
    // One identity for the whole loop: `canonical_compiler` runs `rustc -vV`, and the
    // probing compiler does not change between candidates.
    let probed_with = Some(canonical_compiler(rustc));
    for cand in found {
        let mut opts = MirOptions {
            externs: vec![(name.to_string(), cand.clone())],
            search_paths: search.clone(),
            probed_with: probed_with.clone(),
            ..MirOptions::default()
        };
        opts.search_paths.retain(|r| r.is_dir());
        if extern_compiles(rustc, &opts) {
            return Some(opts);
        }
    }
    None
}

/// `MirOptions` that make a crate's *own dependencies* resolvable when the frontend
/// compiles one of its files, so `cargo verif --file src/lib.rs` works on a crate that
/// `use`s another crate.
///
/// The rlibs live in the crate's own `target/<profile>/deps`; the crate names come
/// from the manifest's `[dependencies]` table (dev/build deps are not linked by the
/// verified source, so they are skipped). Each name's newest `lib<name>-*.rlib` (or
/// `*.rmeta` -- cargo's pipelined build writes a dependency's `.rmeta` before its
/// `.rlib`, and a dependent crate compiles against either, so a `RUSTC_WRAPPER` that
/// verifies mid-build must accept both or race the `.rlib`) is picked and the whole
/// set is *probed* with the emitting compiler (`extern_compiles`);
/// if the probe fails -- no rlib built yet, or a stale one from another toolchain --
/// this returns `MirOptions::default()`, so the caller falls back to a compile error
/// that names the unresolved import rather than a guessed path. A guessed rlib is
/// either the wrong compiler's or the wrong features', and both surface as a compiler
/// error about a program that is fine.
#[cfg(feature = "std")]
pub fn crate_options(file: &Path) -> MirOptions {
    let Some(manifest) = nearest_manifest(file) else {
        return MirOptions::default();
    };
    let crate_root = manifest.parent().map(|p| p.to_path_buf()).unwrap_or_default();
    let Ok(text) = std::fs::read_to_string(&manifest) else {
        return MirOptions::default();
    };
    let deps = dependency_packages(&text);
    // The crate's own compilation environment, which Cargo supplies and a bare
    // `rustc` does not: the features its manifest enables by default, the `cfg`s
    // its build script printed, its crate name, and the `CARGO_PKG_*` variables a
    // source may read with `env!`. Without these a published crate fails
    // `compile_error!`/`E0425` before a function is read -- `serde_json` is the
    // measured example (`requires that either std or alloc feature is enabled`,
    // then `cannot find type Chunk`, which is `#[cfg(fast_arithmetic = "64")]`).
    let target_dir = target_dir_for(&crate_root);
    let crate_name = lib_crate_name(&text);
    let mut rustc_args = cfg_args(&text, &target_dir);
    if let Some(name) = &crate_name {
        rustc_args.push("--crate-name".to_string());
        rustc_args.push(name.clone());
    }
    let base = MirOptions {
        rustc_args,
        rustc_env: package_env(&manifest, &text, crate_name.as_deref()),
        ..MirOptions::default()
    };
    if deps.is_empty() {
        return base;
    }
    // Where a dependency's rlib can land: `<profile>/deps` (a normal build) and every
    // `<profile>/build/<pkg>/<hash>/out` (a build-script output, which some toolchains
    // and this container's cargo use for a path dependency too). Searching both is the
    // same set `build_script_roots` walks for a build script.
    // The real target directory: a custom `[build] target-dir`, `CARGO_TARGET_DIR`,
    // or a workspace's shared `target/`, none of which is `<crate_root>/target`.
    let mut dirs: Vec<PathBuf> = Vec::new();
    for profile in ["debug", "release"] {
        let prof_dir = target_dir.join(profile);
        let dep_dir = prof_dir.join("deps");
        if dep_dir.is_dir() {
            dirs.push(dep_dir);
        }
        if let Ok(pkgs) = std::fs::read_dir(prof_dir.join("build")) {
            for pkg in pkgs.flatten() {
                if let Ok(hashes) = std::fs::read_dir(pkg.path()) {
                    for h in hashes.flatten() {
                        let out = h.path().join("out");
                        if out.is_dir() {
                            dirs.push(out);
                        }
                    }
                }
            }
        }
    }
    if dirs.is_empty() {
        return base;
    }
    let rustc = std::env::var("VERIF_RUSTC").unwrap_or_else(|_| "rustc".into());
    let mut externs: Vec<(String, PathBuf)> = Vec::new();
    for (key, pkg) in &deps {
        // The extern name is the `[dependencies]` key (what the source `use`s); the
        // rlib is named after the *package* -- a renamed dep (`foo = { package =
        // "bar" }`) links `libbar-*.rlib` as `--extern foo=...`.
        let us = extern_name(key);
        let prefix = format!("lib{}-", extern_name(pkg));
        let mut best: Option<(PathBuf, std::time::SystemTime)> = None;
        for d in &dirs {
            let Ok(entries) = std::fs::read_dir(d) else {
                continue;
            };
            for e in entries.flatten() {
                let p = e.path();
                let Some(f) = p.file_name().and_then(|s| s.to_str()) else {
                    continue;
                };
                if f.starts_with(&prefix) && (f.ends_with(".rlib") || f.ends_with(".rmeta")) {
                    if let Ok(mt) = std::fs::metadata(&p).and_then(|m| m.modified()) {
                        if best.as_ref().map(|(_, b)| mt > *b).unwrap_or(true) {
                            best = Some((p, mt));
                        }
                    }
                }
            }
        }
        if let Some((rlib, _)) = best {
            externs.push((us.clone(), rlib));
        }
    }
    if externs.is_empty() {
        return base;
    }
    let opts = MirOptions {
        externs,
        search_paths: dirs,
        probed_with: Some(canonical_compiler(&rustc)),
        ..base.clone()
    };
    if extern_compiles(&rustc, &opts) {
        opts
    } else {
        // The probe failed (no rlib yet, or one from another toolchain), so the
        // externs are dropped and the caller gets a compiler error naming the
        // unresolved import. The *cfgs* are still correct -- they come from the
        // manifest, not from the artifacts -- so they are kept: a crate with no
        // dependencies at all still needs its feature flags to compile.
        base
    }
}

/// The `--cfg` flags a crate's own source needs to compile the way Cargo compiles
/// it: the features its manifest enables by default, and the `cfg`s its build
/// script printed.
///
/// Both are part of the program, not decoration. `serde_json`'s `lib.rs` is
/// `compile_error!` without `feature="std"`, and its `Chunk` type is declared under
/// `#[cfg(fast_arithmetic = "64")]`, which only the build script emits. Without
/// them `cargo verif --file` fails on every published crate before reading a
/// function -- a tool that could not run on the code it is for.
fn cfg_args(text: &str, target_dir: &Path) -> Vec<String> {
    let mut out = Vec::new();
    for f in enabled_features(text) {
        out.push("--cfg".to_string());
        out.push(format!("feature=\"{f}\""));
    }
    for c in build_script_cfgs(text, target_dir) {
        out.push("--cfg".to_string());
        out.push(c);
    }
    out
}

/// The crate's own name, as Cargo spells it: `[lib] name` when declared, else the
/// package name with hyphens turned into underscores.
///
/// `rustc` would otherwise derive the name from the file stem (`lib` for
/// `src/lib.rs`), which is not the crate's name -- and a crate whose source says
/// `#![no_mangle]` or reads `env!("CARGO_CRATE_NAME")` would see the wrong one.
fn lib_crate_name(text: &str) -> Option<String> {
    let name = manifest_value(text, "lib", "name")
        .or_else(|| manifest_value(text, "package", "name"))?;
    let name = name.trim();
    if name.is_empty() {
        None
    } else {
        Some(name.replace('-', "_"))
    }
}

/// The `CARGO_PKG_*` / `CARGO_MANIFEST_*` variables Cargo exports to the compiler.
///
/// A crate that reads one with `env!` does not compile without it, and these are
/// ordinary in published code (`env!("CARGO_PKG_VERSION")`). The values come from
/// the manifest, which is the same source Cargo reads, so they agree with the
/// artifact's. A key the manifest does not set becomes the empty string, as Cargo
/// does -- an absent variable would be a compile error instead.
fn package_env(manifest: &Path, text: &str, crate_name: Option<&str>) -> Vec<(String, String)> {
    let pkg = |k: &str| manifest_value(text, "package", k).unwrap_or_default();
    let version = pkg("version");
    let (core, pre) = version
        .split_once('-')
        .map(|(a, b)| (a.to_string(), b.to_string()))
        .unwrap_or_else(|| (version.clone(), String::new()));
    let mut parts = core.split('.');
    let mut next = || parts.next().unwrap_or("").to_string();
    let mut out = vec![
        ("CARGO_PKG_NAME".to_string(), pkg("name")),
        ("CARGO_PKG_VERSION".to_string(), version),
        ("CARGO_PKG_VERSION_MAJOR".to_string(), next()),
        ("CARGO_PKG_VERSION_MINOR".to_string(), next()),
        ("CARGO_PKG_VERSION_PATCH".to_string(), next()),
        ("CARGO_PKG_VERSION_PRE".to_string(), pre),
    ];
    for (env, key) in [
        ("CARGO_PKG_AUTHORS", "authors"),
        ("CARGO_PKG_DESCRIPTION", "description"),
        ("CARGO_PKG_HOMEPAGE", "homepage"),
        ("CARGO_PKG_REPOSITORY", "repository"),
        ("CARGO_PKG_LICENSE", "license"),
        ("CARGO_PKG_LICENSE_FILE", "license-file"),
        ("CARGO_PKG_RUST_VERSION", "rust-version"),
        ("CARGO_PKG_README", "readme"),
    ] {
        out.push((env.to_string(), pkg(key)));
    }
    if let Some(dir) = manifest.parent() {
        out.push(("CARGO_MANIFEST_DIR".to_string(), dir.display().to_string()));
    }
    out.push(("CARGO_MANIFEST_PATH".to_string(), manifest.display().to_string()));
    if let Some(n) = crate_name {
        out.push(("CARGO_CRATE_NAME".to_string(), n.to_string()));
    }
    out
}

/// The `[features]` table as `(name, items)` pairs.
///
/// A focused reader, like [`manifest_value`]: it joins a multi-line array (Cargo
/// publishes one) and splits on top-level commas, but it does not evaluate
/// anything. An entry it cannot read is skipped rather than guessed, which loses
/// a feature name and leaves the compile error naming it.
fn feature_table(text: &str) -> Vec<(String, Vec<String>)> {
    let mut out = Vec::new();
    let mut in_features = false;
    let mut pending = String::new();
    let mut depth = 0i32;
    for raw in text.lines() {
        let line = strip_toml_comment(raw).trim();
        if depth == 0 && line.starts_with('[') {
            in_features = line.trim_start_matches('[').trim_end_matches(']').trim() == "features";
            continue;
        }
        if !in_features || line.is_empty() {
            continue;
        }
        if !pending.is_empty() {
            pending.push(' ');
        }
        pending.push_str(line);
        depth += bracket_delta(line);
        if depth > 0 {
            continue;
        }
        if let Some((k, v)) = pending.split_once('=') {
            let name = unquote_toml_key(k.trim());
            if !name.is_empty() {
                out.push((name.to_string(), quoted_items(v)));
            }
        }
        pending.clear();
        depth = 0;
    }
    out
}

/// `[` minus `]`, counting only brackets outside string literals.
fn bracket_delta(line: &str) -> i32 {
    let mut d = 0i32;
    let mut in_str = false;
    let mut prev = '\0';
    for c in line.chars() {
        match c {
            '"' if prev != '\\' => in_str = !in_str,
            '[' if !in_str => d += 1,
            ']' if !in_str => d -= 1,
            _ => {}
        }
        prev = c;
    }
    d
}

/// The double-quoted strings of a TOML array, in order.
fn quoted_items(v: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = v;
    while let Some(start) = rest.find('"') {
        let after = &rest[start + 1..];
        let Some(end) = after.find('"') else { break };
        out.push(after[..end].to_string());
        rest = &after[end + 1..];
    }
    out
}

/// The feature names Cargo enables for a plain `cargo build`, i.e. the `default`
/// feature and everything it reaches transitively.
///
/// A plain name is a feature of *this* crate (or an implicit feature named after an
/// optional dependency). `dep/feat` enables a feature on a dependency and, unless
/// written `dep?/feat`, the dependency itself -- whose implicit feature Cargo also
/// passes as a `cfg`. Emitting a `cfg` for a name nothing declares is harmless but
/// noisy under a crate's `#![deny(warnings)]`, so only known names are emitted.
fn enabled_features(text: &str) -> Vec<String> {
    let table = feature_table(text);
    let optional = optional_dependencies(text);
    let known = |name: &str| table.iter().any(|(n, _)| n == name);
    let items_of = |name: &str| table.iter().find(|(n, _)| n == name).map(|(_, v)| v.clone());
    let mut enabled: BTreeSet<String> = BTreeSet::new();
    let mut stack: Vec<String> = Vec::new();
    if known("default") {
        enabled.insert("default".to_string());
        stack.extend(items_of("default").unwrap_or_default());
    }
    while let Some(item) = stack.pop() {
        if let Some((dep, _)) = item.split_once('/') {
            let dep = dep.trim_end_matches('?');
            if !item.contains("?/")
                && (known(dep) || optional.iter().any(|d| d == dep))
                && enabled.insert(dep.to_string())
            {
                stack.extend(items_of(dep).unwrap_or_default());
            }
            continue;
        }
        if !known(&item) && !optional.contains(&item) {
            continue;
        }
        if enabled.insert(item.clone()) {
            stack.extend(items_of(&item).unwrap_or_default());
        }
    }
    enabled.into_iter().collect()
}

/// The dependency names declared `optional = true`, which Cargo turns into implicit
/// features of the same name.
fn optional_dependencies(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut in_deps = false;
    let mut sub_table: Option<String> = None;
    for raw in text.lines() {
        let line = strip_toml_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        if let Some(inner) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            let inner = inner.trim();
            in_deps = inner == "dependencies";
            sub_table = inner
                .strip_prefix("dependencies.")
                .map(|n| unquote_toml_key(n.trim()).to_string());
            continue;
        }
        if in_deps {
            if let Some((k, v)) = line.split_once('=') {
                if v.contains("optional") && v.contains("true") {
                    out.push(unquote_toml_key(k.trim()).to_string());
                }
            }
        } else if let Some(name) = &sub_table {
            if line.starts_with("optional")
                && line.split_once('=').map(|(_, v)| v.trim() == "true").unwrap_or(false)
            {
                out.push(name.clone());
            }
        }
    }
    out
}

/// The `cfg`s the crate's own build script printed, from Cargo's record of its
/// output.
///
/// Cargo runs the script and writes its stdout to `<target>/<profile>/build/<pkg>/
/// <hash>/run/stdout` (older Cargos: `output`); the `cargo:rustc-cfg=` lines are
/// the cfgs the real compilation gets. Only the *newest* record is used, because a
/// host and a target build can each have one and their cfgs can contradict
/// (`fast_arithmetic="32"` and `"64` would both become true).
fn build_script_cfgs(text: &str, target_dir: &Path) -> Vec<String> {
    let Some(pkg) = manifest_value(text, "package", "name") else {
        return Vec::new();
    };
    let pkg = pkg.trim();
    let mut best: Option<(SystemTime, Vec<String>)> = None;
    for profile in ["debug", "release"] {
        let Ok(entries) = std::fs::read_dir(target_dir.join(profile).join("build")) else {
            continue;
        };
        for pkg_dir in entries.flatten() {
            let name = pkg_dir.path();
            let Some(dir_name) = name.file_name().and_then(|s| s.to_str()) else {
                continue;
            };
            if dir_name != pkg && !dir_name.starts_with(&format!("{pkg}-")) {
                continue;
            }
            let Ok(hashes) = std::fs::read_dir(pkg_dir.path()) else { continue };
            for h in hashes.flatten() {
                for f in [h.path().join("run").join("stdout"), h.path().join("output")] {
                    let Ok(body) = std::fs::read_to_string(&f) else { continue };
                    let cfgs: Vec<String> = body
                        .lines()
                        .filter_map(|l| l.strip_prefix("cargo:rustc-cfg="))
                        .map(|c| c.trim().to_string())
                        .filter(|c| !c.is_empty())
                        .collect();
                    if cfgs.is_empty() {
                        continue;
                    }
                    let mt = std::fs::metadata(&f)
                        .and_then(|m| m.modified())
                        .unwrap_or(SystemTime::UNIX_EPOCH);
                    if best.as_ref().map(|(b, _)| mt > *b).unwrap_or(true) {
                        best = Some((mt, cfgs));
                    }
                }
            }
        }
    }
    best.map(|(_, c)| c).unwrap_or_default()
}

/// The crate names in a manifest's `[dependencies]` table. Handles `name = "1"`,
/// `name = { … }`, and the `[dependencies.name]` sub-table form; skips dev and build
/// dependencies, which the verified source does not link.
///
/// The extern name is a dependency's manifest key: Rust spells a crate with
/// underscores, so a hyphenated key (`embedded-hal`) becomes the extern
/// `embedded_hal`. A hyphenated `--extern embedded-hal=...` names nothing the source
/// can `use`.
fn extern_name(dep: &str) -> String {
    dep.replace('-', "_")
}

#[cfg(test)]
fn dependency_names(text: &str) -> Vec<String> {
    dependency_packages(text).into_iter().map(|(k, _)| k).collect()
}

/// The `[dependencies]` table as `(extern_key, package_name)` pairs.
///
/// The extern name is the manifest key (what the source `use`s); the *package* is what
/// the rlib is named after. For a plain dependency the two agree; for a renamed one
/// (`foo = { package = "bar" }`) they differ, and the rlib is `libbar-*.rlib` linked as
/// `--extern foo=...`. Reading only the key searched for `libfoo-*.rlib`, found nothing,
/// and dropped the extern -- a lost proof for any renamed dependency.
fn dependency_packages(text: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = Vec::new();
    let mut in_deps = false;
    for raw in text.lines() {
        let line = strip_toml_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            let inner = line.trim_start_matches('[').trim_end_matches(']').trim();
            in_deps = inner == "dependencies";
            if let Some(rest) = inner.strip_prefix("dependencies.") {
                let name = rest.trim().trim_matches('"').trim_matches('\'').trim();
                if !name.is_empty() {
                    out.push((name.to_string(), name.to_string()));
                }
                in_deps = false;
            }
            continue;
        }
        if in_deps {
            if let Some(eq) = line.find('=') {
                let name = line[..eq]
                    .split('.')
                    .next()
                    .unwrap_or("")
                    .trim()
                    .trim_matches('"')
                    .trim_matches('\'')
                    .trim();
                if !name.is_empty() {
                    let pkg = rename_target(&line[eq + 1..]).unwrap_or_else(|| name.to_string());
                    out.push((name.to_string(), pkg));
                }
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// The `package = "name"` of a renamed dependency's inline table, or `None`. The
/// `package` word must be a standalone key (preceded by `{`, `,` or whitespace, not a
/// letter) so a value that merely contains `package` is not misread.
fn rename_target(value: &str) -> Option<String> {
    let bytes = value.as_bytes();
    let mut from = 0;
    while let Some(rel) = value[from..].find("package") {
        let at = from + rel;
        let boundary = at == 0 || !bytes[at - 1].is_ascii_alphanumeric() && bytes[at - 1] != b'_';
        if boundary {
            let after = value[at + "package".len()..].trim_start();
            if let Some(after) = after.strip_prefix('=') {
                let after = after.trim_start();
                for q in ['"', '\''] {
                    if let Some(rest) = after.strip_prefix(q) {
                        if let Some(end) = rest.find(q) {
                            return Some(rest[..end].to_string());
                        }
                    }
                }
            }
        }
        from = at + "package".len();
    }
    None
}

/// The target directory for `crate_root`: `CARGO_TARGET_DIR` if set (cargo's own
/// precedence), else what `cargo metadata` reports (a custom `[build] target-dir` or a
/// workspace's shared `target/`), else the conventional `<crate_root>/target`.
#[cfg(feature = "std")]
fn target_dir_for(crate_root: &Path) -> PathBuf {
    if let Ok(t) = std::env::var("CARGO_TARGET_DIR") {
        if !t.is_empty() {
            return PathBuf::from(t);
        }
    }
    cargo_target_directory(crate_root).unwrap_or_else(|| crate_root.join("target"))
}

#[cfg(feature = "std")]
fn cargo_target_directory(crate_root: &Path) -> Option<PathBuf> {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let out = std::process::Command::new(cargo)
        .arg("metadata")
        .arg("--format-version=1")
        .arg("--no-deps")
        .current_dir(crate_root)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    target_directory_from_metadata(&String::from_utf8_lossy(&out.stdout))
}

/// The `"target_directory":"…"` field of a `cargo metadata --format-version=1` blob,
/// with the JSON string escapes (`\\`, `\"`, `\n`, `\t`) decoded.
#[cfg(feature = "std")]
fn target_directory_from_metadata(metadata: &str) -> Option<PathBuf> {
    // Read `target_directory` only from the **top-level** object. Cargo prints each
    // package's user-defined `[package.metadata]` before the root `target_directory`, so a
    // `target_directory` nested in a package's metadata would otherwise be found first --
    // and the dependency search would look in the wrong directory. Track the brace depth
    // (skipping string contents) and accept the key only at depth 1.
    let bytes = metadata.as_bytes();
    let mut depth = 0i32;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'"' => {
                let start = i + 1;
                // Scan to the next *unescaped* quote: a JSON string may contain `\"`,
                // and a `[`/`]`/`{`/`}` between two escaped quotes (in a package
                // description) would otherwise change the depth and hide the root
                // `target_directory`.
                let end = json_string_end(bytes, start)?;
                if depth == 1 && &metadata[start..end] == "target_directory" {
                    return read_json_string(bytes, end + 1);
                }
                // Not the key: skip the whole string (its contents hold no braces).
                i = end + 1;
            }
            b'{' | b'[' => {
                depth += 1;
                i += 1;
            }
            b'}' | b']' => {
                depth -= 1;
                i += 1;
            }
            _ => i += 1,
        }
    }
    None
}

/// The byte index of the `"` that closes the JSON string whose opening quote is just
/// before `start`, skipping `\X` escape pairs so an escaped quote (`\"`) does not end
/// the string early.
#[cfg(feature = "std")]
fn json_string_end(bytes: &[u8], start: usize) -> Option<usize> {
    let mut k = start;
    while k < bytes.len() {
        match bytes[k] {
            b'\\' => k += 2,
            b'"' => return Some(k),
            _ => k += 1,
        }
    }
    None
}

/// After a key's closing quote at byte `from`, skip whitespace and `:`, then read the
/// JSON string value, decoding `\\`, `\"`, `\n`, `\t`, `\r`, `\/` and `\uXXXX`.
///
/// The decoded bytes are collected and validated as UTF-8 at the end: a non-ASCII
/// character is several bytes, and decoding each byte with `byte as char` would turn
/// `artefácts` into `artefÃ¡cts`, so the dependency search would look in the wrong
/// directory.
#[cfg(feature = "std")]
fn read_json_string(bytes: &[u8], from: usize) -> Option<PathBuf> {
    let mut j = from;
    while j < bytes.len() && bytes[j].is_ascii_whitespace() {
        j += 1;
    }
    if j >= bytes.len() || bytes[j] != b':' {
        return None;
    }
    j += 1;
    while j < bytes.len() && bytes[j].is_ascii_whitespace() {
        j += 1;
    }
    if j >= bytes.len() || bytes[j] != b'"' {
        return None;
    }
    j += 1;
    let mut out: Vec<u8> = Vec::new();
    while j < bytes.len() {
        match bytes[j] {
            b'"' => return String::from_utf8(out).ok().map(PathBuf::from),
            b'\\' => {
                j += 1;
                if j < bytes.len() {
                    match bytes[j] {
                        b'n' => out.push(b'\n'),
                        b't' => out.push(b'\t'),
                        b'r' => out.push(b'\r'),
                        b'u' => {
                            if j + 4 < bytes.len() {
                                let hex = std::str::from_utf8(&bytes[j + 1..j + 5]).ok()?;
                                let cp = u32::from_str_radix(hex, 16).ok()?;
                                let ch = char::from_u32(cp)?;
                                let mut buf = [0u8; 4];
                                out.extend_from_slice(ch.encode_utf8(&mut buf).as_bytes());
                                j += 4;
                            }
                        }
                        // `\"`, `\\`, `\/` decode to the escaped byte itself.
                        o => out.push(o),
                    }
                }
            }
            o => out.push(o),
        }
        j += 1;
    }
    None
}

/// A compiler *identity*, so two spellings of one compiler compare equal.
///
/// A path cannot answer this. `rustc` on `PATH` is usually a rustup **shim** -- a
/// symlink to `rustup` itself, which dispatches to a toolchain at run time -- so
/// `~/.cargo/bin/rustc` and
/// `~/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc` are the same
/// compiler under two paths, and `std::fs::canonicalize` reports them as different
/// (it follows the symlink to `rustup`, not the toolchain `rustup` would dispatch
/// to). What decides whether an rlib's metadata is readable is the compiler's own
/// account of which build it is: `-vV`'s `commit-hash` and `host`. Two spellings of
/// one toolchain agree on both; two toolchains cannot.
///
/// A binary that cannot answer `-vV` falls back to its canonical path, which is the
/// best identity available and still separates two files.
fn canonical_compiler(p: &str) -> String {
    commit_identity(p).unwrap_or_else(|| {
        std::fs::canonicalize(p)
            .map(|c| c.to_string_lossy().into_owned())
            .unwrap_or_else(|_| p.to_string())
    })
}

/// `commit-hash/host` from `rustc -vV`, when the binary answers.
///
/// `commit-hash` names the build and `host` the target its metadata is written for,
/// and both are read rather than the version banner: `1.100.0` names a release while
/// the commit names a build, and metadata compatibility follows the build.
fn commit_identity(p: &str) -> Option<String> {
    let out = Command::new(p).arg("-vV").output().ok()?;
    if !out.status.success() {
        return None;
    }
    let text = String::from_utf8(out.stdout).ok()?;
    let mut commit = None;
    let mut host = None;
    for line in text.lines() {
        if let Some(v) = line.strip_prefix("commit-hash: ") {
            commit = Some(v.trim());
        } else if let Some(v) = line.strip_prefix("host: ") {
            host = Some(v.trim());
        }
    }
    Some(format!("{}/{}", commit?, host?))
}

/// Refuse to emit with a compiler other than the one the externs were probed with.
///
/// The probe's answer is about the probing compiler only, so a mismatch is not a
/// weaker proof -- it is `E0514` on a usable crate, or a dropped extern and `E0432`.
/// The error names both compilers and the fix, because the alternative is a reader
/// debugging a compiler message about a program that is fine.
fn check_probe_compiler(rustc: &str, opts: &MirOptions) -> Result<(), String> {
    let Some(probed) = opts.probed_with.as_deref() else {
        return Ok(());
    };
    let emitting = canonical_compiler(rustc);
    if emitting == probed {
        return Ok(());
    }
    Err(format!(
        "the externs were probed with `{probed}` but MIR would be emitted with `{emitting}`: \
         an rlib's metadata is compiler-specific, so probe and emit must name one compiler \
         -- pass the same `rustc` to `extern_options_with` and `verify_file_with_opts`"
    ))
}

/// Does `rustc` accept this extern? A one-line probe compiled to metadata: cheap,
/// toolchain-accurate, and the only way to tell a current rlib from a stale one
/// without parsing rustc's metadata format.
#[cfg(feature = "std")]
fn extern_compiles(rustc: &str, opts: &MirOptions) -> bool {
    if opts.externs.is_empty() {
        return false;
    }
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-extern-probe-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let src = dir.join("probe.rs");
    let mut cmd = Command::new(rustc);
    cmd.arg("--edition=2021")
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        .arg("-o")
        .arg(dir.join("probe.rmeta"));
    // Every extern, not just the first (rustc can leave a later path unloaded until
    // used), and under a *synthetic* alias: an artifact named `core`/`std`/`alloc`
    // passed as `--extern core=…` would redirect the probe's implicit prelude lookup.
    // The real MIR emit keeps the real names, so only the probe is aliased.
    let mut crates = String::new();
    for (i, (_, p)) in opts.externs.iter().enumerate() {
        let syn = format!("__verif_probe_{i}");
        crates.push_str(&format!("extern crate {syn};\n"));
        cmd.arg("--extern").arg(format!("{syn}={}", p.display()));
    }
    for d in &opts.search_paths {
        cmd.arg("-L").arg(format!("dependency={}", d.display()));
    }
    // `no_std` so the probe does not inject `std` (a `panic_halt`-style dependency
    // would otherwise clash); the synthetic aliases keep `core` free for the prelude.
    let body = format!("#![no_std]\n#![allow(unused_extern_crates)]\n{crates}");
    if std::fs::write(&src, body).is_err() {
        return false;
    }
    let ok = cmd.arg(&src).output().map(|o| o.status.success()).unwrap_or(false);
    let _ = std::fs::remove_dir_all(&dir);
    ok
}

/// The directories a build script's dependency artifacts live in.
///
/// `$OUT_DIR` is `<target>/<profile>/build/<pkg>/<hash>/out` -- but the number of
/// components between `build` and `out` is Cargo's business, not ours, so this
/// walks up to the directory *named* `build` rather than counting levels. The
/// artifacts then sit in `<profile>/deps` and in every `<profile>/build/<dep>/*/out`
/// beside it. A depth-based walk broke the first time Cargo nested a package
/// directory under `build/`, which is why this one is structural.
///
/// **Under cross-compilation the profile directory in `OUT_DIR` is the wrong one.**
/// `OUT_DIR` belongs to the package being built, so for `--target <triple>` it sits
/// under `target/<triple>/<profile>/`, while a *build dependency* is compiled for the
/// **host** and lands in `target/<profile>/`. The frontend's `rustc` runs on the
/// host too, so only the host artifact can pass its probe -- searching the target
/// directory finds rlibs for the wrong machine, every candidate fails, and
/// `extern_options` returns `None` even though the usable rlib exists. So when
/// `HOST != TARGET` the host profile directory is added, derived from the target
/// profile directory by replacing the triple component. The target directory is kept
/// as well: it costs one failed probe and it is what a non-cross build uses.
#[cfg(feature = "std")]
fn build_script_roots() -> Option<Vec<PathBuf>> {
    let out = PathBuf::from(std::env::var("OUT_DIR").ok()?);
    let host = std::env::var("HOST").ok();
    let target = std::env::var("TARGET").ok();
    build_script_roots_from(&out, host.as_deref(), target.as_deref())
}

/// The pure core of [`build_script_roots`]: no environment, no globals.
///
/// Split out so the cross-compilation layout can be tested by passing paths and
/// names directly. The first version of the test set `OUT_DIR`/`HOST`/`TARGET` with
/// `std::env::set_var`, which needs an `unsafe` block on edition 2024 -- and gate 17
/// pins the number of `unsafe` blocks in `src/`, so a test must not need one. Making
/// the logic a function of its inputs is the fix that keeps the surface at two.
fn build_script_roots_from(
    out: &std::path::Path,
    host: Option<&str>,
    target: Option<&str>,
) -> Option<Vec<PathBuf>> {
    let build_dir = out.ancestors().find(|a| a.file_name().is_some_and(|n| n == "build"))?;
    let profile = build_dir.parent()?;
    let mut roots = vec![profile.join("deps")];
    collect_outs(build_dir, &mut roots);
    // `target/<triple>/<profile>` -> `target/<profile>`, but only when the triple
    // component is really there (a host build has `target/<profile>` already).
    if let (Some(h), Some(t)) = (host, target) {
        if h != t {
            if let (Some(triple_dir), Some(root)) =
                (profile.parent(), profile.parent().and_then(|p| p.parent()))
            {
                if triple_dir.file_name().is_some_and(|n| n == t) {
                    if let Some(name) = profile.file_name() {
                        let host_profile = root.join(name);
                        roots.push(host_profile.join("deps"));
                        collect_outs(&host_profile.join("build"), &mut roots);
                    }
                }
            }
        }
    }
    roots.retain(|r| r.is_dir());
    if roots.is_empty() {
        None
    } else {
        Some(roots)
    }
}

/// Add every `<build>/<dep>/<hash>/out` directory under `build_dir` to `roots`.
fn collect_outs(build_dir: &std::path::Path, roots: &mut Vec<PathBuf>) {
    if let Ok(entries) = std::fs::read_dir(build_dir) {
        for e in entries.flatten() {
            if let Ok(inner) = std::fs::read_dir(e.path()) {
                for i in inner.flatten() {
                    roots.push(i.path().join("out"));
                }
            }
        }
    }
}

/// Resolve the edition to compile `file` under: explicit first, then
/// `VERIF_EDITION`, then the nearest `Cargo.toml`.
///
/// There is deliberately no silent default for a *loose* file -- a `.rs` with no
/// manifest above it has no crate edition to infer, and compiling it under an
/// edition the program does not use is the exact mismatch this resolution removes.
/// A real package, however, *does* have a default: Cargo assigns edition 2015 to a
/// `[package]` that omits `edition`, so a manifest that declares a package without
/// the key resolves to 2015 rather than to an error. The two are different
/// questions -- "what edition is this crate?" and "what edition is this file?" --
/// and only the second has no answer.
pub fn resolve_edition(file: &Path, explicit: Option<Edition>) -> Result<Edition, String> {
    if let Some(e) = explicit {
        return Ok(e);
    }
    if let Ok(v) = std::env::var("VERIF_EDITION") {
        if !v.is_empty() {
            return Edition::parse(&v).ok_or_else(|| {
                format!(
                    "VERIF_EDITION is `{v}`, which is not an edition; use 2015, 2018, 2021 or 2024"
                )
            });
        }
    }
    if let Some(e) = edition_from_manifest(file) {
        return Ok(e);
    }
    Err(format!(
        "no Rust edition for {}: it has no `Cargo.toml` and `VERIF_EDITION` is unset. The \
         edition is what the program is compiled under, so it is never guessed -- set \
         `VERIF_EDITION` to 2015, 2018, 2021 or 2024",
        file.display()
    ))
}

/// The edition a file's crate declares, read from the nearest `Cargo.toml`.
///
/// `package.edition` is read directly; `edition.workspace = true` (or
/// `edition = { workspace = true }`) is resolved against the workspace root's
/// `[workspace.package]`. A `[package]` that *omits* `edition` resolves to 2015,
/// which is Cargo's default for a package that does not state one -- so a valid
/// 2015 package is verified, not refused. A manifest the reader cannot parse
/// yields `None`, so the caller reports "no edition" rather than a wrong one.
///
/// Public because it is the manifest half of [`resolve_edition`]: a caller may
/// want to ask what a manifest declares without the environment fallbacks.
pub fn edition_from_manifest(file: &Path) -> Option<Edition> {
    let manifest = nearest_manifest(file)?;
    let text = std::fs::read_to_string(&manifest).ok()?;
    match manifest_value(&text, "package", "edition") {
        // `edition.workspace = true` / `edition = { workspace = true }`: the value
        // lives in the workspace root.
        Some(v) if v == "workspace" => {
            let root = workspace_root(&manifest, &text)?;
            let root_text = std::fs::read_to_string(&root).ok()?;
            Edition::parse(&manifest_value(&root_text, "workspace.package", "edition")?)
        }
        Some(v) => Edition::parse(&v),
        // No `edition` key. Cargo defaults a `[package]` to edition 2015, so a
        // real package resolves to 2015; a manifest with no `[package]` at all
        // (a pure virtual workspace) declares no crate, so it yields `None` and
        // the caller reports "no edition" as before.
        None => declares_package(&text).then_some(Edition::Rust2015),
    }
}

/// Whether a manifest declares a `[package]` table.
///
/// This is the tell between "a package that omitted `edition`" (Cargo's 2015
/// default applies) and "a manifest with no package" (nothing to default).
fn declares_package(text: &str) -> bool {
    text.lines().any(|raw| {
        let line = strip_toml_comment(raw).trim();
        line.strip_prefix('[')
            .and_then(|l| l.strip_suffix(']'))
            .map(|inner| inner.trim() == "package")
            .unwrap_or(false)
    })
}

/// The nearest `Cargo.toml` at or above `file`, if any.
fn nearest_manifest(file: &Path) -> Option<PathBuf> {
    let abs = std::fs::canonicalize(file).unwrap_or_else(|_| file.to_path_buf());
    let mut dir: Option<&Path> = abs.parent();
    while let Some(d) = dir {
        let candidate = d.join("Cargo.toml");
        if candidate.is_file() {
            return Some(candidate);
        }
        dir = d.parent();
    }
    None
}

/// The workspace root for a member manifest.
///
/// Cargo's `package.workspace` key names the root explicitly, and it may point
/// *outside* the member's ancestor chain (`workspace = "../ws"`), so it is
/// resolved first: searching ancestors only would fail a valid workspace member
/// whose root is not above it. When the key is absent, the root is the nearest
/// ancestor manifest that declares `[workspace]`.
fn workspace_root(manifest: &Path, text: &str) -> Option<PathBuf> {
    if let Some(rel) = manifest_value(text, "package", "workspace") {
        if rel != "workspace" {
            let dir = manifest.parent()?;
            let candidate = dir.join(rel).join("Cargo.toml");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    let mut dir = manifest.parent()?;
    loop {
        let candidate = dir.join("Cargo.toml");
        if candidate.is_file() {
            let text = std::fs::read_to_string(&candidate).ok()?;
            if text.lines().any(|l| l.trim().starts_with("[workspace")) {
                return Some(candidate);
            }
        }
        dir = dir.parent()?;
    }
}

/// The value of a scalar key in a table of a TOML-ish manifest.
///
/// This is a focused reader, not a TOML parser: it handles the spellings a
/// `Cargo.toml` uses for an edition (`edition = "2024"`, `edition.workspace =
/// true`, `edition = { workspace = true }`) and returns `Some("workspace")` for
/// the two inherited forms. Anything else it might read is something it could read
/// *wrongly*, so it reads nothing else.
fn manifest_value(text: &str, table: &str, key: &str) -> Option<String> {
    let mut current = String::new();
    for raw in text.lines() {
        let line = strip_toml_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        if let Some(inner) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            current = inner.trim().to_string();
            continue;
        }
        if current != table {
            continue;
        }
        let Some((lhs, rhs)) = line.split_once('=') else { continue };
        // TOML permits a *quoted* key (`"edition" = "2024"`), which Cargo accepts
        // and treats exactly as the bare spelling. Comparing the raw left-hand side
        // missed it, so a quoted edition key read as *no* edition and the 2015
        // default was applied -- verification then compiled a different edition
        // from Cargo. A dotted key (`edition.workspace`) is not quoted as a whole,
        // so only the bare key is unquoted here.
        let lhs = unquote_toml_key(lhs.trim());
        let rhs = rhs.trim();
        if lhs == format!("{key}.workspace") {
            return Some(if rhs == "true" { "workspace".into() } else { rhs.into() });
        }
        if lhs == key {
            // `edition = { workspace = true }`
            if rhs.starts_with('{') {
                return Some(if rhs.contains("workspace") && rhs.contains("true") {
                    "workspace".into()
                } else {
                    rhs.into()
                });
            }
            return Some(rhs.trim_matches('"').to_string());
        }
    }
    None
}

/// Strip surrounding double quotes from a TOML key, if present.
///
/// A TOML key may be quoted (`"edition" = "2024"`); Cargo reads it identically to
/// the bare spelling. The reader compares keys as strings, so it has to normalise
/// the spelling or a quoted key silently reads as absent.
fn unquote_toml_key(k: &str) -> &str {
    k.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or(k)
}

/// Drop a trailing `#` comment, respecting string literals so a `#` inside one is
/// not mistaken for a comment.
fn strip_toml_comment(line: &str) -> &str {
    let mut in_str = false;
    let mut prev = '\0';
    for (i, c) in line.char_indices() {
        match c {
            '"' if prev != '\\' => in_str = !in_str,
            '#' if !in_str => return &line[..i],
            _ => {}
        }
        prev = c;
    }
    line
}

/// Where the MIR text came from, so failures can say so.
#[derive(Clone, Debug)]
pub enum MirSource {
    /// `rustc --emit=mir` on this file.
    Emitted {
        /// The Rust source the MIR was emitted from.
        file: PathBuf,
        /// The MIR text `rustc` printed.
        mir: String,
    },
    /// A pre-generated dump, which lets a build without nightly reuse one.
    File(PathBuf),
    /// Dump text supplied directly, for tests.
    Inline(String),
}

/// The extra environment for `rustc` when the source declares a crate-level
/// `#![feature(…)]`.
///
/// A modelled shape may name a library method that is *stable* on the toolchain the
/// crate is built with but *unstable* on the MSRV floor -- the C6 corpus's
/// `cast_unsigned`/`cast_signed` (`integer_sign_cast`), `is_multiple_of`
/// (`unsigned_is_multiple_of`) and signed `midpoint` (`num_midpoint_signed`) are
/// stable from 1.87 and gated on 1.85. The corpus must compile on the floor (gate 14
/// runs the frontend's own suite against it), so it carries a `#![feature(…)]`
/// header, and `rustc` refuses a feature gate on a stable channel unless
/// `RUSTC_BOOTSTRAP` is set.
///
/// The bootstrap is scoped to a source that *declares* a feature, never set
/// globally: a file with no gate is compiled exactly as before, so this cannot
/// change the lowering of ordinary code. It is inert on current stable too, where
/// the features are already stable and the gate is a no-op warning.
fn bootstrap_env(file: &Path) -> Vec<(&'static str, &'static str)> {
    let declares_feature = std::fs::read_to_string(file)
        .map(|s| s.lines().any(|l| l.trim_start().starts_with("#![feature(")))
        .unwrap_or(false);
    if declares_feature {
        vec![("RUSTC_BOOTSTRAP", "1")]
    } else {
        Vec::new()
    }
}

/// Get MIR text for a Rust file, or explain why not.
///
/// `rustc --emit=mir` is a *stable* flag -- `-Zunpretty=mir` is the nightly-only
/// spelling, and this frontend deliberately does not use it, so the frontend runs
/// on the same stable compiler that builds the crate (checked down to the MSRV,
/// 1.85). The error is returned rather than papered over, because "the frontend
/// could not run" and "the code is wrong" must never be reported the same way.
///
/// The edition is *resolved*, never assumed: `VERIF_EDITION` first, then the
/// nearest `Cargo.toml`'s `package.edition`. A file with neither is an error,
/// because the edition changes the lowering -- `panic!("literal")` is one
/// diverging call under 2015 but an `Arguments` chain plus `std::rt::panic_fmt`
/// under 2024, and `extern "C" { … }` must be `unsafe` only from 2024 -- so a
/// verdict under the wrong edition would be about a program nobody built. See
/// [`resolve_edition`].
///
/// The compiler is taken from `VERIF_RUSTC` when set, and otherwise from
/// `rustc` on `PATH`. The dedicated variable exists so that pointing this tool at
/// a *different* compiler -- a nightly, or the rustc_public oracle's toolchain --
/// does not disturb the `rustc` that cargo is using to build the test suite;
/// setting `RUSTC` would do exactly that.
pub fn emit_mir(file: &Path) -> Result<String, String> {
    emit_mir_opts(file, &MirOptions::default()).map(|(text, _edition)| text)
}

/// [`emit_mir`] with the compiler named explicitly.
///
/// This exists so a test can point at a *specific* toolchain -- the MSRV, say, or
/// a nightly -- without mutating the process environment, which is a race when
/// tests run in parallel.
pub fn emit_mir_with(rustc: &str, file: &Path) -> Result<String, String> {
    emit_mir_with_opts(rustc, file, &MirOptions::default()).map(|(text, _edition)| text)
}

/// [`emit_mir`] with the run's options, returning the resolved edition too.
pub fn emit_mir_opts(
    file: &Path,
    opts: &MirOptions,
) -> Result<(String, Edition), String> {
    let rustc = std::env::var("VERIF_RUSTC").unwrap_or_else(|_| "rustc".into());
    emit_mir_with_opts(&rustc, file, opts)
}

/// [`emit_mir_with`] with the run's options, returning the resolved edition too.
///
/// The edition is resolved before `rustc` is invoked, so a file whose edition
/// cannot be determined fails with "no edition" rather than with a compiler error
/// about a program compiled under the wrong one.
pub fn emit_mir_with_opts(
    rustc: &str,
    file: &Path,
    opts: &MirOptions,
) -> Result<(String, Edition), String> {
    let edition = resolve_edition(file, opts.edition)?;
    // `rustc` writes its intermediate artifacts next to the output path, so the
    // output goes to a temp file rather than to `/dev/stdout` -- pointing it at
    // `/dev` makes rustc try to create a temp directory there and fail.
    // The name must be unique per *call*, not just per process: tests run in
    // parallel threads of one process, and a shared name means one test deletes
    // the file another is about to read.
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let out_path = std::env::temp_dir().join(format!(
        "verif-mir-{}-{}-{}.mir",
        std::process::id(),
        seq,
        file.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default()
    ));
    let mut cmd = Command::new(rustc);
    cmd.arg(format!("--edition={}", edition.as_str()))
        .arg("--crate-type=lib")
        .arg("--emit=mir")
        .arg("-o")
        .arg(&out_path);
    // An `--extern name=path` makes the crate nameable; the crate's own
    // dependencies are found through `-L dependency=` search paths, which the
    // caller supplies because only it knows where the artifacts live. Without the
    // search path the extern resolves and its *dependency* does not, and the error
    // names the inner crate rather than the one the caller asked for.
    for (name, path) in &opts.externs {
        cmd.arg("--extern").arg(format!("{}={}", name, path.display()));
    }
    for dir in &opts.search_paths {
        cmd.arg("-L").arg(format!("dependency={}", dir.display()));
    }
    for a in &opts.rustc_args {
        cmd.arg(a);
    }
    // Cargo's package metadata (`CARGO_PKG_VERSION`, `CARGO_MANIFEST_DIR`, …) is
    // part of the program: a crate that reads one with `env!` does not compile
    // without it. Set them on the child so the inherited environment is augmented
    // rather than replaced.
    for (k, v) in &opts.rustc_env {
        cmd.env(k, v);
    }
    let out = cmd
        .arg(file)
        .envs(bootstrap_env(file))
        .output()
        .map_err(|e| format!("could not run rustc: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "rustc failed on {} under {}: {}",
            file.display(),
            edition,
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let text = std::fs::read_to_string(&out_path).map_err(|e| {
        format!(
            "rustc produced no MIR for {} under {} ({e}); `--emit=mir` is stable, so this is a \
             missing output file rather than a toolchain problem",
            file.display(),
            edition
        )
    })?;
    let _ = std::fs::remove_file(&out_path);
    if text.trim().is_empty() {
        return Err(format!(
            "rustc produced empty MIR for {} under {}; `--emit=mir` is stable, so check the \
             file's crate type and that it defines an item with a body",
            file.display(),
            edition
        ));
    }
    Ok((text, edition))
}

/// What happened to one function.
#[derive(Clone, Debug)]
pub enum FnOutcome {
    /// Every obligation proved and every path explored.
    Verified {
        /// How many obligations were discharged.
        obligations: usize,
        /// How many of those were rustc-emitted panic conditions.
        panics_ruled_out: usize,
    },
    /// A definite failure, with the obligation that failed.
    Failed {
        /// Which obligation failed, e.g. `panic: attempt to compute ...`.
        kind: String,
        /// The counterexample, as variable assignments.
        detail: String,
    },
    /// Not decided: a budget, an unmodelled construct, or an open obligation.
    /// This is *not* a pass.
    Incomplete {
        /// The obligations that were discharged before the path was cut short.
        report: Box<MirReport>,
        /// Why the verification is incomplete: budgets, unmodelled constructs,
        /// or obligations the engine could not decide.
        reasons: Vec<String>,
    },
    /// The function was skipped, with the reason.
    Skipped {
        /// Why the function was not verified at all.
        reason: String,
    },
}

impl FnOutcome {
    /// True only for [`FnOutcome::Verified`]. `Incomplete` is not a pass.
    pub fn is_verified(&self) -> bool {
        matches!(self, FnOutcome::Verified { .. })
    }
}

impl std::fmt::Display for FnOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FnOutcome::Verified { obligations, panics_ruled_out } => write!(
                f,
                "verified ({obligations} obligation(s), {panics_ruled_out} panic(s) ruled out)"
            ),
            FnOutcome::Failed { kind, detail } => write!(f, "FAILED: {kind} — {detail}"),
            FnOutcome::Incomplete { reasons, .. } => {
                write!(f, "incomplete ({} reason(s))", reasons.len())?;
                for r in reasons.iter().take(3) {
                    write!(f, "\n      - {r}")?;
                }
                Ok(())
            }
            FnOutcome::Skipped { reason } => write!(f, "skipped: {reason}"),
        }
    }
}

/// Verify one function from a parsed program plus its source contracts.
pub fn verify_function(prog: &MirProgram, f: &MirFn, specs: &Specs) -> FnOutcome {
    // A 128-bit type is wider than the engine, whose every width-taking
    // constructor asserts `1..=64`. Refusing here, before any of them runs, is
    // what keeps the refusal whole: the argument seeding, the loop havoc and the
    // contract bindings all consult a type's width, and a 128-bit local would be a
    // panic in whichever came first. A panic is not a refusal -- it takes the run
    // down and reports nothing -- so this guard must precede them all.
    if let Some(ty) = f.first_unrepresentable_type() {
        return FnOutcome::Skipped {
            reason: format!(
                "`{ty:?}` is wider than the engine's 64-bit words, so the function is not modelled"
            ),
        };
    }
    // Resolved by tail as well as exactly: the dump names an inherent method
    // `<impl at …>::f` while the contract is keyed by the source's `f`. An
    // unresolved contract is not "no contract" here -- it is the false-proof
    // case, where the body would be checked against `true` and no `ensures`.
    //
    // An *inherited* trait contract comes with a rename, because the declaration
    // and the implementation may name their parameters differently and the
    // contract means the declaration's names. Binding it by the implementation's
    // own names would attach `ret == a` to the wrong argument -- a false proof.
    let (contract, rename) = match specs.contract_for_fn(f) {
        Ok(x) => x,
        Err(reason) => return FnOutcome::Skipped { reason },
    };
    // A clause the frontend does not take is refused rather than ignored. This
    // is the silent-loss direction: `/// ensuers: ret == 99` was dropped, so the
    // function had no postcondition, was checked against `true`, and came back
    // `Verified` with zero obligations -- a green report for a claim nobody read.
    // A `variant:` is the same shape from the other side: the reader wrote a
    // termination measure and the tool ignored it, so a total-correctness claim
    // would rest on nothing. Refusing names the line and the keyword it looks
    // like, which is what a typo needs, and it is the same discipline as an
    // unreadable `requires`.
    if let Some(c) = contract {
        if let Some((line, text)) = c.unknown.first() {
            return FnOutcome::Skipped {
                reason: format!(
                    "line {line}: `{text}` is not a clause this frontend takes; refusing \
                     rather than verifying the function without it"
                ),
            };
        }
    }
    // Two contracts for one function: the impl's own and the trait's it inherits.
    // `resolve` can only return one, so the other would be dropped without a word.
    // Refused, naming both, because a claim the source wrote must not vanish.
    if let Some(reason) = specs.contract_conflict(&f.name) {
        return FnOutcome::Skipped { reason };
    }
    let arg_vars = spec::arg_vars_named(f, rename.as_ref());
    // The *entry* value of each reference argument, keyed by the contract's name
    // for it, for `old(c)` in a postcondition. A bare `c` in an `ensures` is the
    // value at *return* (see the `post` closure), so this is the only route back to
    // the input. Built once, from the same bindings `arg_vars` uses, so a name and
    // its entry value cannot disagree.
    let old_args_for_post: BTreeMap<String, smt::Var> = f
        .arg_locals
        .iter()
        .filter_map(|&l| {
            if !matches!(f.ty_of(l), Some(Ty::Ref(_))) {
                return None;
            }
            let name = spec::arg_name_of(f, rename.as_ref(), l)?;
            let v = *arg_vars.get(&name)?;
            Some((name, v))
        })
        .collect();
    let signed = spec::signed_args_named(f, rename.as_ref());
    // Fields of struct-typed arguments, bound to their own symbolic inputs. The
    // same bindings are handed to the executor as seeds, so `c.lo` in a contract
    // and `((*_1).0)` in the body name one variable.
    let mut fields = spec::field_env_named(f, rename.as_ref(), &specs.structs, &specs.enums);
    // Named `const` items the contract may name, from the program's own table --
    // the same one the executor folds a body's `const LIMIT` from, so a contract's
    // `LIMIT` and the body's `LIMIT` are one value. The executor's `Env` carries
    // this table for the invariant path already; this is the contract path's copy.
    fields.consts = prog.consts.clone();
    // Slice element references a contract names, bound before the rewrite runs so
    // each `xs[k]` has a binding to rewrite to. Done here, once, rather than on
    // demand, because the postcondition is evaluated inside a closure that cannot
    // hold a `&mut`.
    if let Some(c) = contract {
        for text in c.requires.iter().chain(c.ensures.iter()).chain(c.invariants.iter()) {
            fields.bind_index_refs(text, &arg_vars);
        }
    }
    let ret_signed = f.ret_ty.is_signed();

    // A loop invariant. The clause carries no loop label, so it can only be
    // attached when there is exactly one to attach it to. A function with
    // several `invariant:` lines is refused rather than guessed at: pairing the
    // wrong text with the wrong loop would check a preservation obligation that
    // does not mean what the source says, which is the one failure this crate
    // exists to avoid.
    let invariant: Option<&str> = match contract {
        None => None,
        Some(c) => match c.invariants.len() {
            0 => None,
            1 => Some(c.invariants[0].as_str()),
            _ => {
                return FnOutcome::Skipped {
                    reason: "several `invariant:` clauses, and there is no way to say which \
                             loop each belongs to"
                        .to_string(),
                }
            }
        },
    };

    // The loop termination measure, if the contract carries one. A `variant:`
    // without an `invariant:` is refused rather than ignored: the measure has no
    // loop head to be evaluated at (the invariant is what locates the loop), so
    // taking it would mean guessing which loop it is about. Ignoring it silently
    // would be worse still -- the reader wrote a termination claim and the tool
    // would report partial correctness as if it were total.
    let variant: Option<&str> = match contract {
        None => None,
        Some(c) => match c.variant.as_deref() {
            None => None,
            Some(v) => {
                if c.invariants.is_empty() {
                    return FnOutcome::Skipped {
                        reason: "a `variant:` was declared with no `invariant:`; the measure \
                                 needs the loop the invariant locates"
                            .to_string(),
                    };
                }
                Some(v)
            }
        },
    };

    // The loop-unwinding bound, if the contract carries one. It applies to a
    // function's loops whether or not it also has an `invariant:`: an invariant
    // decides a loop by induction (no unwinding), but a *second* loop with no
    // invariant is still unwound, and the bound governs it. It is not tied to the
    // invariant the way `variant:` is, so a lone `unwind:` is honoured rather than
    // refused.
    let unwind: Option<u32> = contract.and_then(|c| c.unwind);

    // Build the precondition. No contract means `true`, which is the right
    // default: a function with no `requires` is checked for panic freedom on
    // every input.
    let mut pre = None;
    if let Some(c) = contract {
        for r in &c.requires {
            match spec::eval_requires(r, &arg_vars, &signed, &fields) {
                Ok(p) => pre = Some(match pre {
                    None => p,
                    Some(prev) => smt::and(prev, p),
                }),
                Err(e) => {
                    return FnOutcome::Skipped {
                        reason: format!("unreadable `requires`: {e}"),
                    }
                }
            }
        }
    }

    // A symbolic subscript is modelled as an ite chain, which is an honest model
    // of the element only where the index is in range. The chain cannot make that
    // true on its own, so the *precondition* has to establish it: if `requires`
    // does not imply the bound, the subscript is refused rather than checked
    // against a chain that quietly returned the wrong element for an
    // out-of-range index.
    //
    // Conjoining the bound into the precondition instead would be unsound in the
    // direction that matters: it would strengthen what the source asked to be
    // checked, so a contract proved under `i < 4` would claim to hold without it.
    //
    // A slice needs *two* facts. `i < len` says the named index is in range, and
    // `len <= MAX_INDEX_CHAIN` says the enumeration covers the whole slice -- so
    // a read at some *other* index the body uses is also covered rather than
    // falling through the chain to a wrong value. The second is a fact about the
    // length, not the index, which is why bounding the index alone is not enough.
    for (idx, bound) in fields.index_guards() {
        // Two facts, checked separately so the refusal names the one that is
        // missing. A combined message would leave a user who wrote one of the two
        // bounds unable to tell which one the checker wanted.
        let (cond, what) = match bound {
            spec::IndexBound::Const(n) => (smt::ult_const(idx, n), format!("`i < {n}`")),
            spec::IndexBound::Len(len) => (
                smt::and(smt::ult(idx, len), smt::ule_const(len, spec::MAX_INDEX_CHAIN)),
                format!("`i < xs.len()` and `xs.len() <= {}`", spec::MAX_INDEX_CHAIN),
            ),
        };
        let established = match pre {
            Some(p) => smt::prove(smt::implies(p, cond)) == smt::Verdict::Valid,
            None => false,
        };
        if established {
            continue;
        }
        // Which half is missing, for a slice. An array has only the one fact, so
        // it keeps the plain message.
        let detail = match bound {
            spec::IndexBound::Const(_) => String::new(),
            spec::IndexBound::Len(len) => {
                let in_range = match pre {
                    Some(p) => smt::prove(smt::implies(p, smt::ult(idx, len)))
                        == smt::Verdict::Valid,
                    None => false,
                };
                let bounded = match pre {
                    Some(p) => {
                        smt::prove(smt::implies(p, smt::ule_const(len, spec::MAX_INDEX_CHAIN)))
                            == smt::Verdict::Valid
                    }
                    None => false,
                };
                match (in_range, bounded) {
                    (false, false) => " (neither `i < xs.len()` nor `xs.len() <= 64` holds)",
                    (false, true) => " (`i < xs.len()` does not hold)",
                    (true, false) => {
                        " (`xs.len() <= 64` does not hold: the slice may be longer than the \
                         enumeration covers)"
                    }
                    (true, true) => "",
                }
                .to_string()
            }
        };
        return FnOutcome::Skipped {
            reason: format!(
                "a symbolic index is not known to be in range: the precondition does not \
                 imply {what}{detail}, and the subscript is only modelled there"
            ),
        };
    }

    // Build the postcondition as a closure over the return value.
    //
    // An unreadable `ensures` must not be quietly dropped: folding it into `true`
    // would verify the function with no postcondition checked. The closure
    // returns a `Result` for that reason, and `exec` turns an error into an
    // unmodelled path. The parse is also checked *here*, up front, so that a
    // function with no reachable `return` cannot leave the error unmentioned.
    //
    // The check reuses `arg_vars` and the return local's own index and width, so
    // it declares exactly the handles the run itself will declare. It must not
    // reset the arena to get "throwaway" variables: `pre` and `arg_vars` are
    // already live handles in this context, and a reset would invalidate them,
    // which would drop the precondition from every path and make the whole run
    // unsound in the other direction.
    let ensures: Vec<String> = contract.map(|c| c.ensures.clone()).unwrap_or_default();
    if !ensures.is_empty() {
        // Local `_0` is the return place; `Ty::width` is `Some` for a scalar
        // return, which is the only case where a bare `ret` can be read. For an
        // aggregate there is no single word, so the probe must pass `None` here
        // exactly as the run does -- a fabricated one-bit word would let a bare
        // `ret` in an aggregate contract parse against it, and the width then
        // comes out as 1, so `ret <= 5` is refused with a message about a
        // "1-bit width" that has nothing to do with the function.
        let probe_ret = f.ret_ty.width().map(|w| smt::var_named(0, w.clamp(1, 64)));
        // The probe must resolve exactly what the real postcondition will, so
        // `ret.N` is bound here too. Leaving it out would make the probe fail on a
        // contract the run could have handled, and the function would be skipped
        // for a reason that is not true of it.
        //
        // Only the components a contract *names* are probed. Binding every
        // declared component made a `(u8, &u8)` return unprobeable -- component 1
        // is a reference with no bit-vector width -- so a contract about `ret.0`
        // alone skipped the whole function. A component the contract does name and
        // that has no width is still refused, because then the name really cannot
        // be resolved.
        let mut probe_fields = fields.clone();
        let named_components = spec::named_ret_components(&ensures);
        if let Ty::Tuple(ts) = &f.ret_ty {
            for i in &named_components {
                match ts.get(*i as usize) {
                    Some(ty) if probe_fields.probe_ret_slot(*i, ty).is_some() => {}
                    _ => {
                        return FnOutcome::Skipped {
                            reason: format!(
                                "cannot bind `ret.{i}`: the component's type has no bit-vector width"
                            ),
                        };
                    }
                }
            }
        }
        // The probe's `ret` is `None` exactly when the return type has no single
        // word, so the aggregate message is the honest one here.
        let probe_absent =
            if probe_ret.is_some() { spec::RET_IS_UNKNOWN } else { spec::RET_IS_AGGREGATE };
        // An enum return: bind the discriminant so `ret.is_ok()` and friends parse
        // in the probe exactly as they will in the run. The tag is a `usize`-wide
        // word (the enum's discriminant type), which is the width the run passes.
        // The probe discards its result, so a throwaway variable is enough; it must
        // only be the right *width* for `eq_const` to be well-formed.
        //
        // The *payload* bindings (`ret.Ok`, `ret.Run`) are probed too, and they are
        // gated on the enum layout rather than on the success/failure pair: a user
        // enum with neither `Ok` nor `Some` has no `is_ok`, but its payloads are
        // still meaningful.
        if spec::ret_enum_def(&f.ret_ty, &specs.enums).is_some() {
            // A throwaway tag, above every slot the run will use so it cannot
            // collide with a live variable (see `probe_ret_enum_slot`). The probe
            // discards its result; it only has to be the right *width* for
            // `eq_const` to be well-formed.
            if let Some(tag) = probe_fields.probe_ret_enum_slot(USIZE_WIDTH) {
                if let Some((ok, err)) = spec::enum_ret_discriminants(&f.ret_ty, &specs.enums) {
                    probe_fields.bind_ret_enum(tag, ok, err);
                }
                // A contract naming a payload (`ret.Ok`, `ret.Some`, `ret.Err`,
                // `ret.None`, `ret.Run`) binds a variable of the payload's own width
                // and sign, guarded on the discriminant. The payload type comes from
                // the enum's layout (`Result<u8, u8>` gives `Ok: u8`, `Err: u8`),
                // which is the same table the run reads.
                probe_fields.probe_ret_payloads(&f.ret_ty, &specs.enums, tag, &ensures);
            }
        }
        if let Some(err) = ensures.iter().find_map(|e| {
            spec::eval_ensures(
                e,
                &arg_vars,
                probe_ret,
                probe_absent,
                &signed,
                ret_signed,
                &probe_fields,
                &old_args_for_post,
            )
            .err()
        }) {
            return FnOutcome::Skipped { reason: format!("unreadable `ensures`: {err}") };
        }
    }
    let args_for_post = arg_vars.clone();
    let fields_for_post = fields.clone();
    // The names bound to a reference-to-scalar argument. A bare one in an `ensures`
    // means its value at *return*, so the `post` closure must rebind it to the final
    // value -- and, when the final value is not known on this path, *remove* it, so
    // the name is refused rather than silently read as the entry value. Falling back
    // to the entry value is the false proof this shape closed.
    let ref_arg_names: Vec<String> = f
        .arg_locals
        .iter()
        .filter(|&&l| matches!(f.ty_of(l), Some(Ty::Ref(_))))
        .filter_map(|&l| spec::arg_name_of(f, rename.as_ref(), l))
        .collect();
    // The return type's components, for a postcondition that names `ret.N`. The
    // type comes from the MIR (`-> (u8, u8)`), so the binding is to the declared
    // shape rather than to whichever elements a particular path happened to
    // write: a path that leaves `_0.1` unwritten must make `ret.1` a refusal, not
    // a silently dropped conjunct.
    let ret_components: Vec<Ty> = match &f.ret_ty {
        Ty::Tuple(ts) => ts.clone(),
        _ => Vec::new(),
    };
    // Which refusal to give when a bare `ret` is unbound. It is decided from the
    // return *type*: a scalar return can only be unbound because its value is
    // unknown on this path, while an aggregate has no single word to bind at all.
    let ret_absent = if f.ret_ty.width().is_some() {
        spec::RET_IS_UNKNOWN
    } else {
        spec::RET_IS_AGGREGATE
    };
    // The recursion contract: when the function declares a `decreases:` measure,
    // a self-call is answered by the contract instead of being inlined. The
    // measure is required -- without it there is no induction principle and the
    // assumption would be circular -- so its absence leaves `rec` as `None` and
    // the call falls back to inlining. See `exec::Recursion`. Built here, before
    // `signed` is moved into the `post` closure below.
    let rec = match contract {
        Some(c) if !c.decreases.is_empty() => {
            if c.decreases.len() > 1 {
                return FnOutcome::Skipped {
                    reason: "several `decreases:` clauses, and there is no way to say which \
                             measure the recursion counts down"
                        .to_string(),
                };
            }
            Some(exec::Recursion {
                requires: c.requires.clone(),
                ensures: c.ensures.clone(),
                decreases: c.decreases[0].clone(),
                signed: signed.clone(),
                consts: prog.consts.clone(),
                ret_signed,
            })
        }
        _ => None,
    };

    let post = if ensures.is_empty() {
        None
    } else {
        let enum_ret = spec::enum_ret_discriminants(&f.ret_ty, &specs.enums);
        Some(move |ret: Option<smt::Var>,
                   projs: &[(u32, smt::Var)],
                   ret_payloads: &[(u64, smt::Var)],
                   ref_final: &[(u32, smt::Var)],
                   ref_len_unknown: &[u32]| {
            // A reference argument's name denotes the value the body left at the
            // target, so a bare `c` in the postcondition is bound to the *final*
            // value. Binding it to the entry value instead (which `arg_vars` holds)
            // was a false proof: `ensures: c == 0` on `*c = 5` verified, because
            // `c` still named the input. The entry value stays reachable through
            // `old(c)`, which is why the two maps are handed over separately.
            //
            // A reference argument whose final value is not known on this path is
            // *removed* from the map rather than left at its entry value: a bare
            // name that could not be read at return must be refused, never quietly
            // resolved to the input. `old(name)` still works -- the entry value is
            // known regardless of what the body did.
            let mut args = args_for_post.clone();
            let mut fields = fields_for_post.clone();
            for name in &ref_arg_names {
                args.remove(name);
            }
            for (l, v) in ref_final {
                // The argument's source name. `arg_name_of` only covers *width-
                // bearing* args (a `Vec`/slice has no single word), so the name is
                // taken from the debug binding directly, with the contract's
                // rename applied -- the same rule `arg_bindings` uses.
                let Some(name) = spec::arg_name_any(f, rename.as_ref(), *l) else {
                    continue;
                };
                // A Vec/slice/array argument's length is the post-state length (a
                // slice or array's is unchanged, so this is a no-op; a `&mut Vec`'s
                // is the pushed length). Reading the entry length was a false proof.
                let len_name = format!("{name}__len");
                match fields.vars.get_mut(&len_name) {
                    Some(slot) => *slot = *v,
                    None => {
                        args.insert(name, *v);
                    }
                }
            }
            // A `&mut Vec` argument whose length is unknown on this path (the body
            // rebound a Vec reference, aliasing the storage): *remove* the length
            // binding so `v.len()` in the postcondition is refused, rather than read
            // back from the entry value (a false proof for `v.push(1); v = w`).
            for l in ref_len_unknown {
                if let Some(name) = spec::arg_name_any(f, rename.as_ref(), *l) {
                    let len_name = format!("{name}__len");
                    fields.vars.remove(&len_name);
                    // The refused length must not fall through to a crate constant of the
                    // same *generated* name (`const out__len = 0`), which would resolve the
                    // postcondition to the wrong value -- a false proof. Remove it from the
                    // const table too, so the name is genuinely unbound (refused).
                    fields.consts.remove(&len_name);
                }
            }
            // Bind each declared component that this path actually produced.
            for (i, ty) in ret_components.iter().enumerate() {
                let i = i as u32;
                // Declared but unwritten on this path: binding a *fresh*
                // unconstrained variable would be wrong, because a postcondition
                // about `ret.1` would then pass vacuously. Leaving it unbound makes
                // the parser refuse the name instead.
                if let Some((_, v)) = projs.iter().find(|(k, _)| *k == i) {
                    fields.bind_ret(i, ty, *v);
                }
            }
            // An enum return: bind the discriminant, so `ret.is_ok()` and friends
            // read the tag the body produced. `ret` here is the tag variable the
            // executor passed (the return word for an enum-returning function), and
            // the discriminants are the same ones the body's `switchInt` compares.
            if let Some(tag) = ret {
                // `ret.is_ok()`/`is_some()` need a success/failure pair, which only
                // `Result`/`Option` and a user enum with `Ok`/`Some` have. A user
                // enum with neither is refused those methods, but its *payloads*
                // (`ret.Run`) are still bound below: a payload is meaningful
                // whenever the layout names the variant, regardless of the
                // success/failure reading.
                if let Some((ok, err)) = enum_ret {
                    fields.bind_ret_enum(tag, ok, err);
                }
                // The payloads a contract names (`ret.Ok`, `ret.Some`, `ret.Run`),
                // each bound to the variable the executor holds for it and guarded
                // on the discriminant. The payload values come from `ret_payloads`,
                // keyed by the payload's *discriminant* -- the executor writes a
                // downcast payload under the variant's own number, so the two agree
                // by construction.
                spec::bind_ret_payloads(
                    &mut fields,
                    &f.ret_ty,
                    &specs.enums,
                    tag,
                    ret_payloads,
                    &ensures,
                );
            }
            // `ret` is `None` when the return value is an aggregate: there is no
            // single word to stand for it, and the parser refuses a bare `ret`
            // rather than checking it against a fabricated value. Components are
            // still reachable as `ret.0`, `ret.1` through `fields`.
            let mut acc: Option<crate::smt::Pred> = None;
            for e in &ensures {
                let p = spec::eval_ensures(
                    e,
                    &args,
                    ret,
                    ret_absent,
                    &signed,
                    ret_signed,
                    &fields,
                    &old_args_for_post,
                )
                .map_err(|err| err.to_string())?;
                acc = Some(match acc {
                    None => p,
                    Some(prev) => smt::and(prev, p),
                });
            }
            Ok(acc.unwrap_or_else(|| smt::truth(true)))
        })
    };

    // Arguments the precondition pins to a constant. The executor seeds those
    // arguments with their literal, which is sound -- every model of `pre` has the
    // argument equal to it -- and is what makes a body whose operand is pinned build
    // its operations on a literal, where the constant folds collapse them. Without
    // it a pinned 64-bit divider is built symbolically and the query is refused for
    // the size of its own diagram even though the precondition leaves one input.
    let mut pin_buf = [(0u32, 0u64); smt::MAX_PINS];
    let n_pins = match pre {
        Some(p) => smt::pinned_vars(p, &mut pin_buf),
        None => 0,
    };
    let pins: Vec<(u32, u64)> = pin_buf[..n_pins].to_vec();

    // The callees a call may be answered from a contract rather than a body. A
    // name the dump already contains is not in here: its body is inlined, which
    // is strictly more precise than assuming what it promised.
    let callees = exec::CalleeEnv::new(prog, specs);
    let report = exec::verify_fn(
        prog,
        f,
        pre,
        post,
        exec::LoopSpec { invariant, variant, unwind },
        &callees,
        &exec::Seeds {
            fields: fields.seeds.clone(),
            nested: fields.nested_seeds.clone(),
            lens: fields.len_seeds.clone(),
            field_lens: fields.path_len_seeds.clone(),
            array_lens: fields.array_lens.clone(),
            slice_steps: fields.slice_chain_steps(),
            elems: fields.elem_seeds.clone(),
            path_elems: fields.path_elem_seeds.clone(),
            tags: fields.tag_seeds.clone(),
            payload_seeds: fields.payload_seeds.clone(),
            pins,
        },
        rec,
    );

    // A definite failure outranks incompleteness: a counterexample is a result.
    // The polarity is per-kind, so this cannot just look for `Counterexample`:
    // a postcondition fails on a `Counterexample` or an `Unsat`, and a panic
    // fails on a `Counterexample` or a `Valid` (a panic that happens on *every*
    // input, which has no witness to show).
    if let Some(ob) = report.first_failure() {
        // The diagnosis is per-kind: an `Unsat` postcondition holds for *no*
        // input, while a `Valid` panic fires on *every* input. Both leave no
        // witness, so the detail cannot be one shared string.
        //
        // The witness is rendered with the source names the `debug` bindings
        // recorded, so a report says `x = 224` rather than `v1:u8 = 224`. A
        // variable with no source name -- a temporary, a promoted constant --
        // keeps its `v{index}:u{width}` spelling, so the fallback is exactly the
        // old rendering.
        let names: Vec<(&str, u32)> =
            f.local_names.iter().map(|(&l, n)| (n.as_str(), l)).collect();
        return FnOutcome::Failed {
            kind: ob.kind.to_string(),
            detail: ob.failure_detail_named(&names),
        };
    }
    if report.undecided() > 0 {
        let mut reasons = report.unknown_paths.clone();
        reasons.push(format!("{} obligation(s) the engine could not decide", report.undecided()));
        return FnOutcome::Incomplete { report: Box::new(report), reasons };
    }
    if !report.unknown_paths.is_empty() {
        return FnOutcome::Incomplete {
            reasons: report.unknown_paths.clone(),
            report: Box::new(report),
        };
    }
    FnOutcome::Verified {
        obligations: report.obligations.len(),
        panics_ruled_out: report.panics_ruled_out(),
    }
}

/// The result for a whole file.
#[derive(Clone, Debug, Default)]
pub struct FileReport {
    /// The file these results are about.
    pub source: PathBuf,
    /// The edition the file was compiled under.
    ///
    /// A `verified` that does not say which edition it holds under is only half a
    /// claim: the edition changes the lowering, so the verdict is about *this*
    /// edition's program. It is `None` only for a run whose MIR text was supplied
    /// directly (tests), where no edition was involved.
    pub edition: Option<Edition>,
    /// One outcome per verified function, in contract order.
    pub outcomes: Vec<(String, FnOutcome)>,
    /// The source `(file, line)` of each reported function, keyed by the report key.
    /// A diagnostic convenience -- a report that says `v1:u8 = 224` names the variable
    /// but not where the function is, and `cargo verif` puts the file and line in its
    /// SARIF `artifactLocation`/`region`. The file is `Some` for a multi-file crate
    /// (the module a method lives in, via the line map) and `None` for a single-file
    /// source, where the root file is implied. The line is `0` when the scanner could
    /// not place the function, never a guessed line.
    pub lines: std::collections::BTreeMap<String, (Option<PathBuf>, usize)>,
    /// Functions that carried a contract but were not found in the MIR. A
    /// non-empty list means the run covered less than the contracts asked for.
    pub missing: Vec<String>,
}

impl FileReport {
    /// How many functions were fully verified.
    pub fn verified(&self) -> usize {
        self.outcomes.iter().filter(|(_, o)| o.is_verified()).count()
    }

    /// How many functions had a definite counterexample.
    pub fn failed(&self) -> usize {
        self.outcomes.iter().filter(|(_, o)| matches!(o, FnOutcome::Failed { .. })).count()
    }

    /// How many functions were left undecided.
    pub fn incomplete(&self) -> usize {
        self.outcomes.iter().filter(|(_, o)| matches!(o, FnOutcome::Incomplete { .. })).count()
    }

    /// How many functions were skipped outright.
    pub fn skipped(&self) -> usize {
        self.outcomes.iter().filter(|(_, o)| matches!(o, FnOutcome::Skipped { .. })).count()
    }

    /// True only when nothing failed, nothing was incomplete, nothing was
    /// skipped, and every contracted function was found. A skipped function is
    /// *not* a pass: it means a contract could not be read, so the function was
    /// never checked, and counting it as clean would turn an unreadable contract
    /// into a green report.
    pub fn is_clean(&self) -> bool {
        self.failed() == 0
            && self.incomplete() == 0
            && self.skipped() == 0
            && self.missing.is_empty()
    }
}

/// Verify every contracted function in one source file.
///
/// `only` restricts the run to the named functions, which is what a per-file
/// contract test wants: verifying the whole file on every call would be slow and
/// would report unrelated functions.
pub fn verify_file(source: &Path, only: &[String]) -> Result<FileReport, String> {
    verify_file_opts(source, only, &MirOptions::default())
}

/// [`verify_file`] with the run's options (currently the edition).
pub fn verify_file_opts(
    source: &Path,
    only: &[String],
    opts: &MirOptions,
) -> Result<FileReport, String> {
    let rustc = std::env::var("VERIF_RUSTC").unwrap_or_else(|_| "rustc".into());
    verify_file_with_opts(&rustc, source, only, opts)
}

/// [`verify_file`] with the compiler named explicitly. See [`emit_mir_with`].
pub fn verify_file_with(
    rustc: &str,
    source: &Path,
    only: &[String],
) -> Result<FileReport, String> {
    verify_file_with_opts(rustc, source, only, &MirOptions::default())
}

/// [`verify_file_with`] with the run's options.
pub fn verify_file_with_opts(
    rustc: &str,
    source: &Path,
    only: &[String],
    opts: &MirOptions,
) -> Result<FileReport, String> {
    check_probe_compiler(rustc, opts)?;
    let text = std::fs::read_to_string(source)
        .map_err(|e| format!("could not read {}: {e}", source.display()))?;
    // The `--cfg` set is passed to the *reader* as well as to rustc, so a
    // `#[cfg]`-gated enum variant is present or absent here exactly as it is in the
    // compiled code. Without it a disabled variant widens the tag domain (a `match`
    // then looks like it can fall through to `unreachable`) and an enabled one
    // missing from a numbering shifts every later implicit discriminant.
    let specs = spec::extract_crate_with_cfgs(source, &text, &opts.rustc_args);
    let (mir, edition) = emit_mir_with_opts(rustc, source, opts)?;
    let prog =
        parse::parse_program_scoped(&mir, &enum_layouts(&specs), &specs.crate_consts, &specs.const_generics, &specs.impl_owners, &specs.impl_traits, &specs.impl_trait_args, &specs.declared_traits);

    let (targets, missing) = resolve_targets(&prog, &specs);
    let mut report = FileReport {
        source: source.to_path_buf(),
        edition: Some(edition),
        missing,
        ..Default::default()
    };
    // The cache key covers the MIR, the source (contracts), the edition, the `--cfg`
    // set the source was read with and the engine (via `VERIF_ENGINE_HASH`); a change
    // to any of them is a miss. The cfg set is there because the reader *evaluates*
    // it: turning a feature on can add an enum variant (and so widen the tag domain)
    // without changing a byte of MIR or source, and a key without it reused the old
    // proof across that change.
    let cache_key = opts.cache.as_ref().map(|_| {
        super::cache::file_key(&mir, &specs.snapshot, &format!("{edition:?}"), &opts.rustc_args)
    });
    let cached = match (&opts.cache, &cache_key) {
        (Some(dir), Some(k)) => super::cache::load(dir, k),
        _ => super::cache::Entries::new(),
    };
    let mut fresh = super::cache::Entries::new();
    let mut recomputed = false;
    for (key, f) in select(&prog, &targets, only) {
        if let Some(c) = specs.resolve(&f.name) {
            let (file, line) = specs.original_loc(c.line);
            report.lines.insert(key.clone(), (file, line));
        }
        // Keyed by the MIR definition name (`f.name`), which is unique per function
        // -- two trait impls of one method share a *report label* (`S::check`) but not
        // a definition name (their impl locations differ). Keying on the label would
        // let one impl's verdict stand in for the other (a false proof).
        let outcome = match cached.get(&f.name) {
            Some(c) => c.to_outcome(),
            None => {
                let fresh_outcome = smt::with_fresh(|| verify_function(&prog, f, &specs));
                // Only a *cacheable* verdict this run computed is worth writing back:
                // a hit is already in the file, and a `Skipped`/`Incomplete` is never
                // stored, so counting it would create an empty entry on a cold run
                // and rewrite the file on a warm one.
                recomputed |= super::cache::Cached::of(&fresh_outcome).is_some();
                fresh_outcome
            }
        };
        if let Some(c) = super::cache::Cached::of(&outcome) {
            fresh.insert(f.name.clone(), c);
        }
        report.outcomes.push((key, outcome));
    }
    if let (Some(dir), Some(k)) = (&opts.cache, &cache_key) {
        if recomputed {
            // Merge with the previous entries, so a `--function` run does not drop
            // the verdicts it did not recompute.
            let mut merged = cached;
            for (n, c) in fresh {
                merged.insert(n, c);
            }
            let _ = super::cache::store(dir, k, &merged);
        }
    }
    for m in &report.missing {
        if let Some(c) = specs.by_fn.get(m) {
            let (file, line) = specs.original_loc(c.line);
            report.lines.insert(m.clone(), (file, line));
        }
    }
    Ok(report)
}

/// The executor's view of each enum: names in declaration order, so a
/// `(base as Variant)` downcast resolves to the discriminant the `switchInt`
/// compares against.
///
/// The spec reader carries payload types the parser has no use for, so only the
/// names cross over. Both views are read from the same source in the same pass,
/// which is what keeps a downcast's index and a contract's `Enum::Variant`
/// constant in step by construction rather than by convention.
fn enum_layouts(specs: &Specs) -> BTreeMap<String, parse::EnumLayout> {
    specs
        .enums
        .iter()
        .map(|(name, def)| {
            let variants = def.variants.iter().map(|(v, _, d)| (v.clone(), *d)).collect();
            (name.clone(), parse::EnumLayout { variants })
        })
        .collect()
}

/// The `(report key, function)` pairs for every function the source declared a
/// contract for, plus the contracted names the dump did not contain.
///
/// A free function's contract is keyed by its bare name, which is unique in a
/// file. A method's is keyed by the `(line, column)` of its `impl`, so it is
/// matched to the dump function carrying that same location -- never by the
/// method's bare name alone, which two `impl` blocks can share. A method the dump
/// does not contain is reported missing, exactly like a free function, so a
/// contract cannot be silently dropped.
///
/// The report key is the bare method name when no other contracted method shares
/// it, and `Owner::method` when one does: two methods named `value` would
/// otherwise collapse into one `outcomes` entry and only one of them would be
/// visible. The bare name is preferred because it is what a reader looks for, and
/// it is exactly what the MIR dump itself uses as the method's tail.
/// Whether a method's MIR definition name (`<impl at FILE:L:C: L:C>::m`) names the file
/// a contract came from. Compares the full path, then the basename (rustc prints the
/// path as it resolved it, which may differ in spelling from the path the caller used).
/// When either side has no file, it does not constrain -- the line and column alone do.
fn impl_file_matches(name: &str, want: Option<&Path>) -> bool {
    // Strict full-path comparison, mirroring `Specs::snapshot_line_for`: a basename
    // fallback would let two same-named files in different directories match, and an
    // absent file must not be treated as "no constraint" (that would match any file).
    // The map's file and rustc's `impl at FILE` share the root spelling, so the full
    // path agrees; a mismatch refuses the pairing (the method is `missing`).
    match (spec::impl_file(name), want) {
        (Some(f), Some(w)) => spec::same_file(Path::new(f), w),
        // A `None` want is a single-file `Specs` (no line map): pair by location alone.
        // The caller still requires a singleton candidate set, so ambiguity is refused.
        (Some(_), None) => true,
        _ => false,
    }
}

/// Like [`impl_file_matches`] but WITHOUT the bare-basename fallback: true only when
/// the impl file is the *same* path as the wanted file (or canonicalises to it). Used
/// to prefer an exact candidate over the loose basename one, so an unrelated
/// same-basename file at the same coordinates does not force an ambiguity refusal.
fn impl_file_matches_exact(name: &str, want: Option<&Path>) -> bool {
    match (spec::impl_file(name), want) {
        (Some(f), Some(w)) => {
            let fp = Path::new(f);
            fp == w || matches!((fp.canonicalize(), w.canonicalize()), (Ok(a), Ok(b)) if a == b)
        }
        (Some(_), None) => true,
        _ => false,
    }
}

fn resolve_targets<'a>(
    prog: &'a MirProgram,
    specs: &Specs,
) -> (Vec<(String, &'a MirFn)>, Vec<String>) {
    // Every method that will be a target, from its own contract or from a trait
    // declaration's, so the tail count below sees both kinds. Counting only
    // `by_method` let two impls of one contracted trait both be keyed by the bare
    // tail, and one `outcomes` entry then hid the other -- the same collapse the
    // location key exists to prevent.
    let method_targets = trait_method_targets(specs);
    // Counted over *distinct* functions, not table entries: a method that declares
    // its own contract and also inherits its trait's appears in both, and counting
    // it twice would spell its key `Owner::method` even though it is the only one
    // -- a key the tests and the report do not expect, for a method that is not
    // ambiguous at all.
    let mut distinct: BTreeSet<(usize, usize, String)> = specs.by_method.keys().cloned().collect();
    distinct.extend(method_targets.iter().cloned());
    let mut tail_counts: BTreeMap<&str, usize> = BTreeMap::new();
    for (_, _, method) in &distinct {
        *tail_counts.entry(method.as_str()).or_default() += 1;
    }

    let mut targets: Vec<(String, &MirFn)> = Vec::new();
    let mut missing: Vec<String> = Vec::new();

    // The contract key is the full source path; the MIR definition name is the
    // shortest crate-unique suffix of it. An exact match wins outright (so
    // `a::f` and `b::a::f` stay apart -- rustc prints both in full once they
    // collide); only when there is none does a unique `::`-aligned suffix count.
    //
    // Both directions of ambiguity are refused, not guessed at. A key that
    // suffix-matches several dump functions is refused, and so is a dump function
    // that several keys suffix-match: either pairing would check one body against
    // another's contract. The second case is the one a `#[cfg]`-excluded item
    // creates -- the key still comes from the source, but its body is not in the
    // dump, so its suffix lands on a *different* compiled function, which would
    // otherwise be reported `Verified` against the wrong contract and conceal
    // that the excluded item was never checked at all.
    let keys: Vec<&String> = specs.by_fn.keys().collect();
    let mut chosen: Vec<Option<usize>> = vec![None; keys.len()];
    let mut exact_owner: BTreeMap<usize, usize> = BTreeMap::new();
    for (ki, key) in keys.iter().enumerate() {
        if let Some(fi) = prog.fns.iter().position(|f| f.name == **key) {
            chosen[ki] = Some(fi);
            exact_owner.insert(fi, ki);
        }
    }
    // A key with exactly one suffix candidate proposes it; a candidate a key
    // already claimed exactly, or that more than one key proposes, is refused.
    let mut proposed: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (ki, key) in keys.iter().enumerate() {
        if chosen[ki].is_some() {
            continue;
        }
        let mut cand: Option<usize> = None;
        let mut count = 0usize;
        for (fi, f) in prog.fns.iter().enumerate() {
            if spec::is_path_suffix(key, &f.name) {
                cand = Some(fi);
                count += 1;
            }
        }
        if count == 1 {
            proposed.entry(cand.unwrap()).or_default().push(ki);
        }
    }
    for (fi, kis) in proposed {
        if kis.len() == 1 && !exact_owner.contains_key(&fi) {
            chosen[kis[0]] = Some(fi);
        }
    }
    for (ki, key) in keys.iter().enumerate() {
        match chosen[ki] {
            Some(fi) => targets.push(((*key).clone(), &prog.fns[fi])),
            // A declaration with no body is *assumed* at each call, which is the
            // modular case rather than a contract whose body went missing. It has
            // no MIR by construction, so reporting it `missing` would make every
            // file that calls an external function unclean.
            None if specs.bodyless.contains(*key) => {}
            None => missing.push((*key).clone()),
        }
    }
    // The report key for a method: the bare tail when it is unique, `Owner::method`
    // when two contracted methods share it.
    let method_key = |line: usize, col: usize, method: &str, f: &MirFn| {
        let ambiguous = tail_counts.get(method).copied().unwrap_or(0) > 1
            || specs.by_fn.contains_key(method);
        if ambiguous {
            match prog.impl_owners.get(&(line, col)) {
                Some(owner) => format!("{owner}::{method}"),
                None => f.name.clone(),
            }
        } else {
            method.to_string()
        }
    };
    let mut seen: BTreeSet<(usize, usize, String)> = BTreeSet::new();
    for (line, col, method) in specs.by_method.keys() {
        seen.insert((*line, *col, method.clone()));
        let method = method.as_str();
        // The `by_method` key is a *snapshot* line; the MIR's `impl_loc` is rustc's
        // original line. Translate through the line map so a method in a module (whose
        // snapshot line differs from its file's) still pairs with its body, and check the
        // file so two `impl`s at the same line and column in different files stay apart.
        let (orig_file, orig_line) = specs.original_loc(*line);
        let candidates: Vec<&_> = prog.fns.iter().filter(|f| f.impl_loc == Some((orig_line, *col))
            && f.name.rsplit("::").next() == Some(method)
            && impl_file_matches(&f.name, orig_file.as_deref())).collect();
        // Prefer the exact-file body over a bare-name fallback so an earlier
        // same-basename match cannot beat the exact file; with no file, or no exact
        // candidate, the pairing must be unambiguous (exactly one body) or it is refused.
        let chosen = match orig_file.as_deref() {
            Some(w) => {
                let exact: Vec<&_> = candidates.iter().copied()
                    .filter(|f| spec::impl_file(&f.name).map(Path::new) == Some(w)).collect();
                if exact.len() == 1 { Some(exact[0]) }
                else if exact.is_empty() && candidates.len() == 1 { Some(candidates[0]) }
                else { None }
            }
            None if candidates.len() == 1 => Some(candidates[0]),
            None => None,
        };
        match chosen {
            Some(f) => targets.push((method_key(*line, *col, method, f), f)),
            None => missing.push(method.to_string()),
        }
    }
    // An `impl` that declares no contract of its own but implements a trait that
    // *does*: the implementation is where the promise is kept or broken, so it is a
    // target. Without this the trait's contract was inherited by `resolve` (so a
    // call to it was answered correctly) but never *checked* on any body, and the
    // declaration itself is not in `by_fn` to be reported missing either -- the
    // promise would be silently unenforced, which is the one outcome this frontend
    // treats as worse than a refusal.
    let mut enforced: BTreeSet<String> = BTreeSet::new();
    for (line, col, method) in method_targets {
        // The impl's own contract, if it has one, is already the entry above; the
        // trait's is then a *second* specification of the same function, and
        // `resolve` can only hand back one of them. Reporting it is the only
        // honest answer: silently preferring either would drop a claim the source
        // wrote. See `verify_function`, which refuses on `contract_conflict`.
        let (orig_file, orig_line) = specs.original_loc(line);
        let all: Vec<&MirFn> = prog.fns.iter().filter(|f| f.impl_loc == Some((orig_line, col))
            && f.name.rsplit("::").next() == Some(method.as_str())
            && impl_file_matches(&f.name, orig_file.as_deref())).collect();
        // Prefer an exact-path candidate over the bare-basename fallback: an unrelated
        // file that merely shares a basename at the same coordinates must not force a
        // refusal. Only multiple candidates at the *same* location are truly ambiguous.
        let exact: Vec<&MirFn> = all.iter().copied()
            .filter(|f| impl_file_matches_exact(&f.name, orig_file.as_deref())).collect();
        let pool: &[&MirFn] = if !exact.is_empty() { &exact } else { &all };
        let Some(f) = pool.first().copied() else {
            continue;
        };
        if pool.len() > 1 {
            // Two `#[path]` inclusions of one file place the impl at the same file,
            // line and column, so this pairing cannot tell them apart. Picking either
            // would check one body and silently skip the other -- a clean verdict over
            // an unchecked impl. Refuse: report it visibly unchecked, do not mark the
            // declaration enforced.
            missing.push(format!(
                "{}::{method} (ambiguous: implemented in more than one module inclusion)",
                specs.impl_traits[&(line, col)]
            ));
            continue;
        }
        // Normalise the trait key the same way `trait_method_targets` does, or an
        // impl of a `use crate::Trait` imported name is *checked* (discovery strips
        // the prefix) yet its declaration is also reported `missing` under the
        // unstripped `crate::Trait::m` -- double-counted in coverage.
        let tr = &specs.impl_traits[&(line, col)];
        let tr = tr.strip_prefix("crate::").unwrap_or(tr);
        enforced.insert(format!("{tr}::{method}"));
        if seen.insert((line, col, method.clone())) {
            targets.push((method_key(line, col, &method, f), f));
        }
    }
    // A trait declaration whose contract no implementation in this file carries is
    // a promise with nothing to keep it. It has no MIR, so it can never be a
    // target, and leaving it unmentioned would make the run `is_clean()` while the
    // claim was never checked -- the silent-loss shape this frontend refuses
    // everywhere else. Reported like any other un-found contract, with the reason
    // spelled out so it is not mistaken for a missing body.
    for key in specs.by_trait.keys() {
        if !enforced.contains(key) {
            missing.push(format!("{key} (a trait declaration with no implementation in this file)"));
        }
    }
    (targets, missing)
}

/// Every `(impl line, impl column, method)` whose contract comes from a *trait
/// declaration* rather than from the implementation.
///
/// A declaration has no body and so can never be a target itself; the implementations
/// are where it has to be checked. This is the inverse of
/// [`crate::mir::spec::Specs::trait_contract`]: that one asks "what does this impl
/// inherit for this method", this one enumerates the pairs so they can be checked.
///
/// Only a trait declaration the scanner read is enumerated, so an `impl` of a trait
/// declared elsewhere (an external trait, or one whose declaration is in another
/// file) contributes nothing -- there is no contract text to check it against.
fn trait_method_targets(specs: &Specs) -> Vec<(usize, usize, String)> {
    let mut out = Vec::new();
    for ((line, col), tr) in &specs.impl_traits {
        // Every declaration the trait carries, which is every method of it this
        // scanner read a contract for. A trait with no contracted method
        // contributes nothing, so an impl of it is left as it was: checked for
        // panic freedom, with no postcondition to establish. Strip a `crate::`
        // prefix (an imported trait) the same way `trait_contract` does, or a method
        // with only an inherited contract never becomes a target.
        let tr = tr.strip_prefix("crate::").unwrap_or(tr);
        let prefix = format!("{tr}::");
        for key in specs.by_trait.keys() {
            if let Some(method) = key.strip_prefix(&prefix) {
                out.push((*line, *col, method.to_string()));
            }
        }
    }
    out
}

/// The targets to check: all of them when `only` is empty, otherwise those whose
/// report key or bare tail is named in `only`.
///
/// A name in `only` that matches no contracted target is still looked up in the
/// dump, so naming a function that carries no contract keeps checking it for panic
/// freedom rather than silently reporting nothing.
fn select<'a>(
    prog: &'a MirProgram,
    targets: &[(String, &'a MirFn)],
    only: &[String],
) -> Vec<(String, &'a MirFn)> {
    if only.is_empty() {
        return targets.to_vec();
    }
    let mut out: Vec<(String, &'a MirFn)> = Vec::new();
    for want in only {
        let mut found = false;
        for (key, f) in targets {
            // `key` is the report key (a method's `Owner::method`, or a free
            // function's full source path). A request matches the key, the MIR
            // name, or a bare tail of either -- so `f`, `a::f` and `Owner::f` all
            // find their target without over-matching a different owner.
            if want == key
                || f.name == *want
                || key.rsplit("::").next() == Some(want.as_str())
                || f.name.rsplit("::").next() == Some(want.as_str())
            {
                out.push((key.clone(), *f));
                found = true;
            }
        }
        if !found {
            if let Some(f) = prog.get(want) {
                out.push((want.clone(), f));
            }
        }
    }
    out
}

/// Verify a whole MIR dump, using contracts from a companion source file.
pub fn verify_mir_text(
    mir: &str,
    specs: &Specs,
    only: &[String],
) -> Result<FileReport, String> {
    let prog =
        parse::parse_program_scoped(mir, &enum_layouts(specs), &specs.crate_consts, &specs.const_generics, &specs.impl_owners, &specs.impl_traits, &specs.impl_trait_args, &specs.declared_traits);
    let (targets, missing) = resolve_targets(&prog, specs);
    let mut report = FileReport { missing, ..Default::default() };
    // A request matching both a bare tail and a full path (e.g. `f` and `m::f`)
    // selects the same MIR definition twice; dedupe by definition pointer so it is
    // verified once. Two *distinct* methods that share a display key (two traits'
    // `S::check`) have different pointers and both survive.
    let mut seen: Vec<*const MirFn> = Vec::new();
    for (key, f) in select(&prog, &targets, only) {
        let ptr = f as *const MirFn;
        if seen.contains(&ptr) {
            continue;
        }
        seen.push(ptr);
        let outcome = smt::with_fresh(|| verify_function(&prog, f, specs));
        report.outcomes.push((key, outcome));
    }
    Ok(report)
}

/// A helper for tests and tools: parse a dump and return function names.
pub fn function_names(mir: &str) -> Vec<String> {
    parse::parse_program(mir).fns.iter().map(|f| f.name.clone()).collect()
}

/// Map from name to parsed function, for callers that want to inspect the IR.
pub fn functions(mir: &str) -> BTreeMap<String, MirFn> {
    parse::parse_program(mir)
        .fns
        .into_iter()
        .map(|f| (f.name.clone(), f))
        .collect()
}

/// The `Verdict` for a predicate, as a convenience for callers that want to ask
/// a one-off question of the engine under the same arena discipline.
pub fn decide(p: crate::smt::Pred) -> Verdict {
    smt::with_fresh(|| smt::prove(p))
}

/// Re-exported so a caller can name the error type without reaching into `spec`.
pub type ContractError = SpecError;

/// Emit a `#[test]` that reproduces a **panic** counterexample (U3).
///
/// A counterexample is the verifier's evidence; a test makes it executable. The
/// *values* come from the counterexample, the argument *order* from the source's
/// parameter list ([`spec::function_params`]), so the emitted call is the one the
/// verifier refuted. While the bug exists the call panics and the test fails;
/// fixing the function makes it pass -- the "failing-then-fixed" shape U3's exit
/// criterion asks for.
///
/// Only a *panic* with a concrete witness is emitted. A postcondition failure has
/// no panic to reproduce, and emitting a test for it would need the postcondition
/// re-stated in Rust, which the frontend does not model; the refusal is the honest
/// answer rather than a guessed test.
pub fn emit_test_source(
    file: &std::path::Path,
    report: &FileReport,
    name: &str,
) -> Result<String, String> {
    let outcome = report.outcomes.iter().find(|(n, _)| n == name).map(|(_, o)| o);
    let Some(FnOutcome::Failed { kind, detail }) = outcome else {
        return Err(format!(
            "`{name}` did not fail with a counterexample, so there is nothing to \
             reproduce (only a `Failed` outcome becomes a test)"
        ));
    };
    if !kind.starts_with("panic") {
        return Err(format!(
            "`{name}` failed on `{kind}`, not a panic; a non-panic failure has no call \
             to reproduce, so it is not emitted as a test"
        ));
    }
    let src = std::fs::read_to_string(file)
        .map_err(|e| format!("could not read {}: {e}", file.display()))?;
    let params = spec::function_params(&src, name).ok_or_else(|| {
        format!(
            "could not read `{name}`'s parameter list (a method, or a signature the \
             scanner cannot read whole); refusing to guess the call order"
        )
    })?;
    // `a = 1, b = 2` -> (a, 1), (b, 2). The value is emitted verbatim: an integer
    // literal infers the parameter's type, and one that does not fit fails to
    // compile rather than silently changing the input.
    let values: Vec<(&str, &str)> = detail
        .split(", ")
        .filter_map(|p| p.split_once(" = "))
        .map(|(n, v)| (n.trim(), v.trim()))
        .collect();
    let mut args = Vec::new();
    for (pname, ty) in &params {
        let Some((_, v)) = values.iter().find(|(n, _)| n == pname) else {
            return Err(format!(
                "the counterexample does not assign `{pname}`, so the call cannot be built"
            ));
        };
        args.push(render_arg(pname, ty, v)?);
    }
    let sanitized: String = name
        .chars()
        .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    Ok(format!(
        "#[test]\nfn {sanitized}_reproduces_the_counterexample() {{\n    \
         // `verif` refuted `{name}`: {kind} at `{detail}`.\n    \
         // While the bug exists this call panics, so the test fails; fix the\n    \
         // function and it passes.\n    \
         let _ = {name}({});\n}}\n",
        args.join(", ")
    ))
}

/// Render one counterexample value as a Rust argument for a parameter of type `ty`.
///
/// The counterexample stores *bit patterns* -- a `bool` `false` is `0`, an `i8` `-1`
/// is `255` -- so the value is typed back before it is passed: `false`/`true` for a
/// `bool`, sign-extended for a signed integer, the unsigned value otherwise. Emitting
/// the raw decimal would give `bad(0)` for a `bool` and `bad(255)` for an `i8`: an
/// uncompilable call, or one that does not reproduce the counterexample. The literal
/// is emitted unsuffixed so it takes the parameter's own type by inference.
fn render_arg(pname: &str, ty: &super::parse::Ty, raw: &str) -> Result<String, String> {
    let v: i128 = raw
        .trim()
        .parse()
        .map_err(|_| format!("the counterexample value `{raw}` for `{pname}` is not an integer"))?;
    if matches!(ty, super::parse::Ty::Bool) {
        return Ok(if v != 0 { "true".into() } else { "false".into() });
    }
    let Some(w) = ty.width() else {
        return Err(format!(
            "`{pname}` is not a scalar type the emitter can synthesise a value for"
        ));
    };
    let w = u32::from(w);
    if w == 0 || w > 64 {
        return Err(format!("`{pname}` has an unsupported width {w}"));
    }
    let mask: u128 = if w == 64 { u128::MAX } else { (1u128 << w) - 1 };
    let bits = (v as u128) & mask;
    if ty.is_signed() {
        let signed =
            if (bits >> (w - 1)) & 1 == 1 { bits as i128 - (1i128 << w) } else { bits as i128 };
        Ok(format!("{signed}"))
    } else {
        Ok(format!("{bits}"))
    }
}

#[cfg(test)]
mod edition_tests {
    use super::*;
    use std::path::PathBuf;

    /// A scratch directory unique per call, so tests can run in parallel.
    fn scratch(tag: &str) -> PathBuf {
        use std::sync::atomic::{AtomicU64, Ordering};
        static SEQ: AtomicU64 = AtomicU64::new(0);
        let seq = SEQ.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir()
            .join(format!("verif-edition-unit-{}-{seq}-{tag}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        dir
    }

    /// A `[package]` that omits `edition` is Cargo's 2015 default, not an error.
    ///
    /// Cargo assigns edition 2015 to a package that does not state one, so
    /// refusing it would stop verification of a package that builds. The
    /// distinction is between a real package (a default applies) and a loose file
    /// (nothing to default) -- and the second must still be refused, or the tool
    /// would compile under an edition the program may not use.
    #[test]
    fn a_package_without_an_edition_defaults_to_2015_but_a_loose_file_does_not() {
        let dir = scratch("no-edition");
        let manifest = dir.join("Cargo.toml");
        std::fs::write(&manifest, "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n").unwrap();
        let src = dir.join("probe.rs");
        std::fs::write(&src, "pub fn f() {}\n").unwrap();
        assert_eq!(
            edition_from_manifest(&src),
            Some(Edition::Rust2015),
            "a package that omits `edition` must resolve to Cargo's 2015 default"
        );

        // A manifest with no `[package]` (a pure virtual workspace) declares no
        // crate, so there is nothing to default and the resolution is `None`.
        std::fs::write(&manifest, "[workspace]\nmembers = [\"a\"]\n").unwrap();
        assert_eq!(
            edition_from_manifest(&src),
            None,
            "a manifest with no `[package]` has no crate edition to default"
        );

        // A loose file (no manifest above it) is still refused by `resolve_edition`
        // when nothing else supplies the edition.
        let loose = std::env::temp_dir().join(format!(
            "verif-loose-{}-{}.rs",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::write(&loose, "pub fn f() {}\n").unwrap();
        // Only assert when no override is set, since the env is process-global.
        if std::env::var("VERIF_EDITION").map(|v| v.is_empty()).unwrap_or(true) {
            assert!(
                resolve_edition(&loose, None).is_err(),
                "a loose file with no edition anywhere must be refused, not defaulted"
            );
        }
        let _ = std::fs::remove_dir_all(&dir);
        let _ = std::fs::remove_file(&loose);
    }

    /// An explicit `package.edition` and a workspace-inherited one both resolve.
    #[test]
    fn a_stated_edition_and_a_workspace_inheritance_both_resolve() {
        let dir = scratch("stated");
        let src = dir.join("probe.rs");
        std::fs::write(&src, "pub fn f() {}\n").unwrap();
        let manifest = dir.join("Cargo.toml");
        std::fs::write(&manifest, "[package]\nname = \"d\"\nedition = \"2021\"\n").unwrap();
        assert_eq!(edition_from_manifest(&src), Some(Edition::Rust2021));

        // `edition.workspace = true` reads the value from the workspace root.
        let root = scratch("ws-root");
        std::fs::write(
            root.join("Cargo.toml"),
            "[workspace]\nmembers = [\"member\"]\n[workspace.package]\nedition = \"2018\"\n",
        )
        .unwrap();
        let member = root.join("member");
        let _ = std::fs::create_dir_all(&member);
        let m_src = member.join("probe.rs");
        std::fs::write(&m_src, "pub fn f() {}\n").unwrap();
        std::fs::write(
            member.join("Cargo.toml"),
            "[package]\nname = \"m\"\nedition.workspace = true\n",
        )
        .unwrap();
        assert_eq!(
            edition_from_manifest(&m_src),
            Some(Edition::Rust2018),
            "`edition.workspace = true` must resolve against the workspace root"
        );

        // An unparseable edition is a refusal, not a fallback.
        std::fs::write(&manifest, "[package]\nname = \"d\"\nedition = \"2030\"\n").unwrap();
        assert_eq!(edition_from_manifest(&src), None, "an unknown edition is refused");

        let _ = std::fs::remove_dir_all(&dir);
        let _ = std::fs::remove_dir_all(&root);
    }
    /// `extern_options` names the crate *and* the search path its dependencies live
    /// on, because an `--extern` alone resolves the outer crate and then fails on its
    /// transitive dependency. An artifact that no build produced is a refusal rather
    /// than a guessed path -- the guess would surface as a compiler error about
    /// correct code, the confusing direction.
    #[test]
    fn extern_options_refuses_when_the_artifact_is_absent() {
        // A crate name that no build ever produced has no rlib to find, so the
        // answer is a refusal rather than a guessed path. (This deliberately does
        // not mutate `OUT_DIR`: `set_var` is unsafe in edition 2024 and mutating the
        // environment under a parallel test harness is a data race.)
        assert!(
            extern_options("a-crate-that-no-build-ever-produced").is_none(),
            "an absent artifact must be refused, never guessed"
        );
    }

    /// Under cross-compilation the *host* profile directory is the one that holds a
    /// usable build dependency, and the search must reach it.
    ///
    /// `$OUT_DIR` belongs to the package being built, so for `--target <triple>` it
    /// sits under `target/<triple>/<profile>/`, while a build dependency is compiled
    /// for the host and lands in `target/<profile>/`. Before the fix the host
    /// directory was never searched: every candidate was a target rlib, every probe
    /// failed, and `extern_options` returned `None` though the usable rlib existed.
    ///
    /// The test drives the *pure* core with explicit paths and names, so it needs no
    /// `std::env::set_var` and therefore no `unsafe` block -- gate 17 pins that
    /// surface at two, and a test is not allowed to raise it.
    #[test]
    fn a_cross_build_searches_the_host_profile_directory() {
        let root = std::env::temp_dir().join(format!("verif-cross-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let triple = "thumbv7em-none-eabihf";
        // target/<triple>/debug/build/pkg/hash/out  (the package being built)
        let out = root.join(triple).join("debug").join("build").join("pkg").join("hash").join("out");
        std::fs::create_dir_all(&out).unwrap();
        // target/debug/deps  (where the host build dependency lives)
        let host_deps = root.join("debug").join("deps");
        std::fs::create_dir_all(&host_deps).unwrap();
        // target/<triple>/debug/deps  (the target artifact, unusable by a host probe)
        let target_deps = root.join(triple).join("debug").join("deps");
        std::fs::create_dir_all(&target_deps).unwrap();

        let roots = build_script_roots_from(&out, Some("x86_64-unknown-linux-gnu"), Some(triple))
            .expect("a build directory exists");
        let _ = std::fs::remove_dir_all(&root);

        assert!(
            roots.contains(&host_deps),
            "the host profile's deps directory must be searched under cross-compilation: {roots:?}"
        );
        assert!(
            roots.contains(&target_deps),
            "the target profile directory is still searched (a non-cross build uses it): {roots:?}"
        );
    }

    /// A *host* build (`HOST == TARGET`) does not add a phantom directory, and the
    /// profile directory it already has is the one it searches. This is the control
    /// for the test above: a fix that always appended a "host" root would pass the
    /// cross case and pollute every ordinary build.
    #[test]
    fn a_host_build_searches_only_its_own_profile_directory() {
        let root = std::env::temp_dir().join(format!("verif-host-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let out = root.join("debug").join("build").join("pkg").join("hash").join("out");
        std::fs::create_dir_all(&out).unwrap();
        let deps = root.join("debug").join("deps");
        std::fs::create_dir_all(&deps).unwrap();

        let roots = build_script_roots_from(&out, Some("x86_64-unknown-linux-gnu"), Some("x86_64-unknown-linux-gnu"))
            .expect("a build directory exists");
        let _ = std::fs::remove_dir_all(&root);

        let deps_roots: Vec<_> = roots.iter().filter(|r| r.ends_with("deps")).collect();
        assert_eq!(
            deps_roots,
            vec![&deps],
            "a host build searches exactly one deps directory -- its own: {roots:?}"
        );
    }

    /// The extern plumbing reaches `rustc`: a file that imports a crate the frontend
    /// was not told about fails with `E0432`, and the same file with the crate passed
    /// as an extern compiles. This is the failure the `externs` field exists to fix,
    /// and it is pinned here because a silent `--extern` that never reaches the
    /// command line would otherwise look identical to one that works.
    #[test]
    fn an_unresolvable_import_names_the_missing_extern() {
        let dir = std::env::temp_dir().join(format!("verif-extern-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        let src = dir.join("m.rs");
        std::fs::write(
            &src,
            "use some_crate_nobody_linked::thing;\npub fn f() -> u8 { thing() }\n",
        )
        .unwrap();
        let opts = MirOptions { edition: Some(Edition::Rust2021), ..MirOptions::default() };
        let err = emit_mir_with_opts("rustc", &src, &opts).expect_err("an unknown crate cannot resolve");
        assert!(
            err.contains("E0432") || err.contains("unresolved import"),
            "the refusal must name the unresolved import, got: {err}"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

}

/// The extern probe must be run by the compiler that will *consume* the rlib.
///
/// A rlib carries compiler-specific metadata, so an rlib one toolchain produced is
/// not thereby readable by another. This pins the consequence the API is built on:
/// [`extern_compiles`] answers about *that* compiler, so a caller that probes with
/// one toolchain and emits MIR with another has proved the wrong thing. It also
/// pins the positive half -- the same rlib is accepted by its own compiler -- so the
/// test cannot pass by refusing everything.
#[cfg(all(test, feature = "std"))]
mod extern_probe_tests {
    use super::*;

    /// `dependency_names` reads the `[dependencies]` table and *only* it: dev and
    /// build dependencies are not linked by the verified source, so naming them would
    /// add an `--extern` for a crate the file never sees. Both value shapes
    /// (`name = "1"`, `name = { … }`) and the `[dependencies.name]` sub-table are read.
    #[test]
    fn dependency_names_reads_the_dependencies_table_only() {
        let toml = "[package]\nname = \"x\"\n\
                    [dependencies]\n\
                    serde = \"1\"\n\
                    foo = { path = \"../foo\" }\n\
                    [dev-dependencies]\n\
                    criterion = \"0.5\"\n\
                    [build-dependencies]\n\
                    cc = \"1\"\n\
                    [dependencies.bar]\n\
                    version = \"1\"\n";
        assert_eq!(dependency_names(toml), vec!["bar", "foo", "serde"]);
        // No `[dependencies]` at all -> nothing, so `crate_options` is the default.
        assert!(dependency_names("[package]\nname = \"x\"\n").is_empty());
    }

    /// A hyphenated manifest key becomes an underscored extern, because that is the
    /// name Rust spells (`use embedded_hal`), and a hyphenated `--extern
    /// embedded-hal=...` names nothing the source can `use`. Found by the external
    /// crate demo (C8): `embedded-hal` resolved to no extern and the file failed
    /// `E0433` even though the rlib was found.
    #[test]
    fn a_listed_toolchain_matches_its_short_name() {
        let host = "x86_64-unknown-linux-gnu";
        assert!(names_toolchain("stable-x86_64-unknown-linux-gnu", "stable", host));
        assert!(names_toolchain("1.85-x86_64-unknown-linux-gnu", "1.85", host));
        assert!(names_toolchain("nightly", "nightly", host));
        assert!(!names_toolchain("stable-x86_64-unknown-linux-gnu", "1.85", host));
        assert!(!names_toolchain("stableness", "stable", host));
        // A *dated* nightly is a different toolchain: accepting it would make
        // `have("nightly")` look up the undated name, which rustup then installs.
        assert!(!names_toolchain(
            "nightly-2026-10-23-x86_64-unknown-linux-gnu",
            "nightly",
            host
        ));
        // So is the same channel installed for *another* host: `rustup which
        // --toolchain stable` resolves the default host, so the lookup would miss
        // the install the preflight just found.
        assert!(!names_toolchain("stable-aarch64-apple-darwin", "stable", host));
        assert!(!names_toolchain("stable-x86_64-unknown-linux-gnu", "stable", ""));
    }

    #[test]
    fn a_hyphenated_dependency_name_is_an_underscored_extern() {
        assert_eq!(extern_name("embedded-hal"), "embedded_hal");
        assert_eq!(extern_name("scratch_dep"), "scratch_dep");
    }

    /// The *path* and the *identity* of a toolchain's `rustc`, when it is installed.
    ///
    /// The two are deliberately returned together, because they are not
    /// interchangeable: `canonical_compiler` yields an identity (`commit-hash/host`),
    /// which is what the probe guard compares, but it is **not** an executable --
    /// `Command::new` on it fails. A test that used the identity as the program
    /// would skip itself at the first spawn and report `ok` having tested nothing,
    /// which is the defect this helper exists to make impossible to write by accident.
    /// `rustup toolchain list` prints `stable-x86_64-unknown-linux-gnu (default)`,
    /// not `stable`, so a name match has to accept the `-<triple>` suffix -- otherwise
    /// the compatibility tests skip their assertions on a machine where CI installed
    /// exactly the toolchains they need.
    fn names_toolchain(listed: &str, toolchain: &str, host: &str) -> bool {
        if listed == toolchain {
            return true;
        }
        // A `-<triple>` suffix is the same toolchain only when the triple is *this*
        // host's: `rustup which --toolchain stable` resolves the default host, so an
        // install for another host is a different toolchain that the lookup would
        // then fail on. A *dated* nightly (`nightly-2026-10-23-x86_64-…`) is a
        // different toolchain too.
        let Some(rest) = listed.strip_prefix(toolchain).and_then(|r| r.strip_prefix('-')) else {
            return false;
        };
        !host.is_empty() && rest == host
    }

    /// The host triple `rustup which --toolchain <name>` would resolve.
    fn host_triple() -> Option<String> {
        let out = Command::new("rustc").arg("-vV").output().ok()?;
        let text = String::from_utf8(out.stdout).ok()?;
        text.lines()
            .find_map(|l| l.strip_prefix("host: "))
            .map(|h| h.trim().to_string())
    }

    fn have(toolchain: &str) -> Option<(String, String)> {
        // `rustup which --toolchain X` *installs* a missing `X`, silently and over the
        // network: a test would block for minutes (or forever, with no network) instead
        // of skipping. `rustup toolchain list` answers from the local state.
        let listed = Command::new("rustup").args(["toolchain", "list"]).output().ok()?;
        let installed = String::from_utf8(listed.stdout).ok()?;
        let host = host_triple().unwrap_or_default();
        if !installed
            .split_whitespace()
            .any(|w| names_toolchain(w, toolchain, &host))
        {
            return None;
        }
        let out = Command::new("rustup")
            .args(["which", "--toolchain", toolchain, "rustc"])
            .output()
            .ok()?;
        if !out.status.success() {
            return None;
        }
        let path = String::from_utf8(out.stdout).ok()?.trim().to_string();
        if path.is_empty() {
            return None;
        }
        let id = canonical_compiler(&path);
        Some((path, id))
    }

    /// The path `rustc` on `PATH` actually runs, and that path's identity.
    ///
    /// `rustup which rustc` (no `--toolchain`) resolves the *active* toolchain, which
    /// is the one a bare `rustc` dispatches to -- including a directory override. Using
    /// `--toolchain stable` here would be wrong under an override: the bare name would
    /// then name a different build than the one asked about.
    fn active() -> Option<(String, String)> {
        let out = Command::new("rustup").args(["which", "rustc"]).output().ok()?;
        if !out.status.success() {
            return None;
        }
        let path = String::from_utf8(out.stdout).ok()?.trim().to_string();
        if path.is_empty() {
            return None;
        }
        let id = canonical_compiler(&path);
        Some((path, id))
    }

    #[test]
    fn the_probe_answers_for_the_compiler_that_will_read_the_rlib() {
        // The compiler that built this test binary's `verif` rlib. The *path* is what
        // gets spawned; the identity is only ever compared.
        let producer_path = std::env::var("RUSTC")
            .ok()
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "rustc".into());
        let producer = canonical_compiler(&producer_path);
        // A *different* toolchain, if one is installed. Without one there is nothing
        // to compare against, and the test says so rather than passing vacuously.
        let other = ["1.85", "nightly", "stable"]
            .into_iter()
            .filter_map(have)
            .find(|(_, id)| *id != producer);
        let Some((other_path, other_id)) = other else {
            eprintln!(
                "skipped: no second toolchain installed, so there is no cross-compiler \
                 case to test (producer identity {producer})"
            );
            return;
        };

        // Build a tiny rlib with `producer`, then ask both compilers to read it.
        let dir = std::env::temp_dir().join(format!(
            "verif-extern-cross-{}",
            std::process::id()
        ));
        let _ = std::fs::create_dir_all(&dir);
        let src = dir.join("lib.rs");
        std::fs::write(&src, "pub fn seven() -> u8 { 7 }\n").unwrap();
        let rlib = dir.join("libprobe_crate.rlib");
        let built = Command::new(&producer_path)
            .args(["--crate-type=lib", "--crate-name", "probe_crate", "-o"])
            .arg(&rlib)
            .arg(&src)
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false);
        if !built {
            let _ = std::fs::remove_dir_all(&dir);
            panic!(
                "the producing compiler ({producer_path}, identity {producer}) must be able \
                 to build a trivial rlib; without it there is nothing to probe"
            );
        }

        let opts = MirOptions {
            externs: vec![("probe_crate".into(), rlib.clone())],
            ..MirOptions::default()
        };
        // The producing compiler reads its own rlib. `extern_compiles` *spawns* the
        // compiler, so it takes the path -- passing the identity here would fail to
        // spawn and read as "rejected", which is why the two are kept apart.
        assert!(
            extern_compiles(&producer_path, &opts),
            "the compiler that built the rlib must accept it ({producer_path}, {producer})"
        );
        // A different toolchain must not -- and that is exactly why the probe and
        // the emitter have to name one compiler. The identities are asserted apart
        // first, so a wrong `other` (the same build under another spelling) cannot
        // make the negative assertion below pass for the wrong reason.
        assert_ne!(producer, other_id, "the cross toolchain must be a different build");
        assert!(
            !extern_compiles(&other_path, &opts),
            "a different toolchain ({other_path}, {other_id}) must not accept an rlib \
             built by {producer_path} ({producer})"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A probed-extern set may only be used by the compiler that probed it.
    ///
    /// This is the invariant the whole `extern_options_with` signature exists for, so
    /// it is checked rather than documented: a mismatch is refused with both compilers
    /// named. The `None` case (hand-built options) is *not* refused -- a caller may
    /// legitimately point at a prebuilt rlib -- so the guard cannot pass by refusing
    /// everything.
    #[test]
    fn a_probed_extern_set_is_refused_by_a_different_compiler() {
        let dir = std::env::temp_dir().join(format!("verif-probe-guard-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        let src = dir.join("lib.rs");
        std::fs::write(&src, "pub fn one() -> u8 { 1 }\n").unwrap();

        // Hand-built options are not checked: `probed_with` is `None`.
        let hand_built = MirOptions { edition: Some(Edition::Rust2021), ..MirOptions::default() };
        assert!(
            check_probe_compiler("rustc", &hand_built).is_ok(),
            "a hand-built option set names its own rlib and must not be refused"
        );

        // A probed set records its compiler and refuses any other. `check_probe_compiler`
        // canonicalises whatever it is given, so it must be handed an *executable path*
        // here: an identity is not a program, and passing one would exercise the
        // fallback that returns the string unchanged rather than a second compiler.
        let probed = MirOptions {
            edition: Some(Edition::Rust2021),
            probed_with: Some(canonical_compiler("rustc")),
            ..MirOptions::default()
        };
        assert!(
            check_probe_compiler("rustc", &probed).is_ok(),
            "the probing compiler must be accepted"
        );
        let active_id = canonical_compiler("rustc");
        if let Some((other_path, other_id)) = ["1.85", "nightly", "stable"]
            .into_iter()
            .filter_map(have)
            .find(|(_, id)| *id != active_id)
        {
            let err = check_probe_compiler(&other_path, &probed)
                .expect_err("a different compiler must be refused");
            // The error names the *identity* of the emitting compiler, which is what the
            // guard compares; asserting on the identity is what proves the second
            // toolchain was actually identified rather than failing to spawn.
            assert!(
                err.contains(&other_id),
                "the error must name the emitting compiler's identity {other_id}: {err}"
            );
            assert_ne!(active_id, other_id, "the two must be different builds");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A bare name and the absolute path naming the same compiler are one identity.
    ///
    /// This is the whole point of [`canonical_compiler`], and it is easy to get wrong.
    /// `rustc` on `PATH` is the rustup *shim*, a different file from the toolchain
    /// binary, so neither `fs::canonicalize` nor a `PATH` search equates them -- only
    /// the compiler's own `-vV` does. The previous version of the guard test could not
    /// see that: it canonicalised *both* operands with the same helper, so a helper
    /// that returned its input unchanged still compared equal. This test compares a
    /// bare name against an absolute path obtained independently, from `rustup which`.
    ///
    /// The absolute path is the **active** toolchain's, resolved by `rustup which rustc`
    /// with no `--toolchain`, not `stable`'s: a bare `rustc` dispatches to whatever the
    /// override selects, so asking for `stable` explicitly would compare two different
    /// builds whenever a directory override points elsewhere, and fail while the
    /// identification was correct.
    #[test]
    fn a_bare_compiler_name_and_its_absolute_path_are_one_identity() {
        let Some((abs, abs_id)) = active() else {
            eprintln!("skipped: no rustup, so there is no shim/path pair to compare");
            return;
        };
        let bare = canonical_compiler("rustc");
        assert_eq!(
            bare, abs_id,
            "a bare `rustc` (the rustup shim) and `rustup which`'s path ({abs}) name one \
             compiler and must canonicalise to one identity; got {bare:?} vs {abs_id:?}"
        );
        // The property the guard depends on: a probed set built from the absolute path
        // accepts the bare name rather than refusing it as a second toolchain.
        let probed = MirOptions {
            probed_with: Some(canonical_compiler(&abs)),
            ..MirOptions::default()
        };
        assert!(
            check_probe_compiler("rustc", &probed).is_ok(),
            "a bare name naming the probed compiler must not be refused"
        );
    }

    /// Two different toolchains are two identities.
    ///
    /// The guard is only useful if it can tell them apart, so the identity is not
    /// "some string that two binaries might share". `1.85` and stable are different
    /// builds and must differ.
    #[test]
    fn two_toolchains_are_two_identities() {
        let (Some((a_path, a)), Some((b_path, b))) = (have("stable"), have("1.85")) else {
            eprintln!("skipped: stable and 1.85 must both be installed to compare them");
            return;
        };
        assert_ne!(
            a, b,
            "stable ({a_path}) and 1.85 ({b_path}) are different builds and must not \
             share an identity"
        );
    }
}

#[cfg(test)]
mod render_tests {
    use super::*;

    #[test]
    fn render_arg_types_a_counterexample_value() {
        use super::parse::Ty;
        assert_eq!(render_arg("b", &Ty::Bool, "0").unwrap(), "false");
        assert_eq!(render_arg("b", &Ty::Bool, "1").unwrap(), "true");
        assert_eq!(render_arg("x", &Ty::I8, "255").unwrap(), "-1");
        assert_eq!(render_arg("x", &Ty::I8, "128").unwrap(), "-128");
        assert_eq!(render_arg("x", &Ty::U8, "255").unwrap(), "255");
        assert_eq!(render_arg("x", &Ty::I8, "127").unwrap(), "127");
        assert!(render_arg("x", &Ty::Other("S".into()), "0").is_err());
    }

    #[test]
    fn dependency_names_reads_dotted_and_quoted_keys() {
        let toml = "[dependencies]\ndep.path = \"../dep\"\nfoo = \"1\"\n\n                    [dependencies.\"bar\"]\nversion = \"1\"\n";
        let names = super::dependency_names(toml);
        assert!(names.contains(&"dep".to_string()), "dotted key -> `dep`, got {names:?}");
        assert!(names.contains(&"foo".to_string()), "got {names:?}");
        assert!(names.contains(&"bar".to_string()), "quoted sub-table, got {names:?}");
        assert!(
            !names.iter().any(|n| n.contains('.') || n.contains('"')),
            "no dots or quotes may survive, got {names:?}"
        );
    }

    /// A renamed dependency's rlib is named after the *package*, not the manifest key:
    /// `foo = { package = "bar" }` links `libbar-*.rlib` as `--extern foo=...`. Reading
    /// only the key searched for `libfoo-*.rlib` and dropped the extern.
    #[test]
    fn dependency_packages_reads_a_rename() {
        let toml = "[dependencies]\nserde = \"1\"\nfoo = { package = \"bar\", path = \"../bar\" }\nsub = { version = \"1\" }\n";
        let mut got = super::dependency_packages(toml);
        got.sort();
        assert_eq!(
            got,
            vec![
                ("foo".to_string(), "bar".to_string()),
                ("serde".to_string(), "serde".to_string()),
                ("sub".to_string(), "sub".to_string()),
            ]
        );
    }

    /// `cargo metadata`'s `target_directory` is the authority for a custom `[build]
    /// target-dir` or a workspace's shared `target/`; the extractor reads just that field.
    #[cfg(feature = "std")]
    #[test]
    fn target_directory_from_metadata_reads_the_field() {
        use std::path::PathBuf;
        let m = r#"{"packages":[],"target_directory":"/tmp/ws/target","version":1}"#;
        assert_eq!(super::target_directory_from_metadata(m), Some(PathBuf::from("/tmp/ws/target")));
        // A Windows-style path is JSON-escaped (`\\`), so the decoded value is `C:\ws\target`.
        let m2 = r#"{"target_directory":"C:\\ws\\target"}"#;
        assert_eq!(super::target_directory_from_metadata(m2), Some(PathBuf::from(r"C:\ws\target")));
        // A package's user-defined metadata prints before the root `target_directory`; a
        // nested `target_directory` must not shadow the real top-level one.
        let nested = r#"{"packages":[{"metadata":{"target_directory":"/wrong"}}],"target_directory":"/right"}"#;
        assert_eq!(super::target_directory_from_metadata(nested), Some(PathBuf::from("/right")));
        // A non-ASCII path is multi-byte; each byte must decode as one char, not as a
        // separate Latin-1 char (`artefácts` must stay `artefácts`, not `artefÃ¡cts`).
        let unicode = r#"{"target_directory":"artefácts"}"#;
        assert_eq!(super::target_directory_from_metadata(unicode), Some(PathBuf::from("artefácts")));
        // A `\uXXXX` escape decodes to the code point (`\u00e1` is `á`).
        let esc = r#"{"target_directory":"a\u00e1b"}"#;
        assert_eq!(super::target_directory_from_metadata(esc), Some(PathBuf::from("aáb")));
        // A `[` between two escaped quotes in a preceding description must not change
        // the brace depth and hide the root `target_directory`.
        let quoted = r#"{"packages":[{"description":"Parses the quoted \"[\" token"}],"target_directory":"/x/target"}"#;
        assert_eq!(super::target_directory_from_metadata(quoted), Some(PathBuf::from("/x/target")));
        assert_eq!(super::target_directory_from_metadata("{}"), None);
    }
}

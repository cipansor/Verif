//! The `cargo verif` binary (U2): end to end.
//!
//! These tests run the *built* binary (`CARGO_BIN_EXE_cargo-verif`, which cargo
//! sets for an integration test of the same package) on a throwaway crate, and
//! assert the exit code and the printed report. That is the only way to check
//! what a user actually sees: the library tests pin `FileReport`, and these pin
//! the command that renders it and maps it to a process exit code.
//!
//! A true contract must exit `0` and print "all contracts held"; a false one must
//! exit `1` and name the failing obligation. A `--function` filter must verify
//! only that function, so a clean function in a file with a broken one still
//! exits `0`.
#![cfg(feature = "std")]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

static SEQ: AtomicU32 = AtomicU32::new(0);

/// A throwaway crate directory, so the frontend resolves an edition from a real
/// `Cargo.toml` rather than a loose file.
fn scratch_crate(lib_rs: &str) -> PathBuf {
    let n = SEQ.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "verif-cargo-verif-{}-{}",
        std::process::id(),
        n
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("create scratch crate");
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"scratch\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
    )
    .expect("write manifest");
    std::fs::write(dir.join("src").join("lib.rs"), lib_rs).expect("write lib.rs");
    dir
}

/// Run the built binary on a file and return `(exit code, combined output)`.
fn run(args: &[&str], file: &Path) -> (i32, String) {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_cargo-verif"));
    if let Ok(rustc) = std::env::var("VERIF_RUSTC") {
        cmd.env("VERIF_RUSTC", rustc);
    }
    cmd.arg("--file").arg(file);
    for a in args {
        cmd.arg(a);
    }
    let out = cmd.output().expect("run cargo-verif");
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.code().unwrap_or(-1), text)
}

/// True when a compiler is reachable, so the test does not fail on a machine
/// with none. Reported, not silently passed.
fn have_rustc() -> bool {
    if let Ok(rustc) = std::env::var("VERIF_RUSTC") {
        return Command::new(rustc).arg("--version").output().map(|o| o.status.success()).unwrap_or(false);
    }
    Command::new("rustc").arg("--version").output().map(|o| o.status.success()).unwrap_or(false)
}

const TWO_FNS: &str = r#"
macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }
spec! { requires: x > 0, ensures: ret == x, }
pub fn id_pos(x: u32) -> u32 { x }
spec! { requires: true, ensures: ret == 7, }
pub fn wrong(x: u32) -> u32 { x }
"#;

#[test]
fn a_true_contract_exits_zero() {
    if !have_rustc() {
        eprintln!("cargo_verif: no rustc; skipping");
        return;
    }
    let dir = scratch_crate(TWO_FNS);
    let lib = dir.join("src").join("lib.rs");
    let (code, text) = run(&["--function", "id_pos"], &lib);
    assert_eq!(code, 0, "a true contract must exit 0, output:\n{text}");
    assert!(text.contains("all contracts held"), "output:\n{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_false_contract_exits_one_and_names_the_failure() {
    if !have_rustc() {
        eprintln!("cargo_verif: no rustc; skipping");
        return;
    }
    let dir = scratch_crate(TWO_FNS);
    let lib = dir.join("src").join("lib.rs");
    let (code, text) = run(&[], &lib);
    assert_eq!(code, 1, "a false contract must exit 1, output:\n{text}");
    assert!(text.contains("FAILED"), "the report must name the failure, output:\n{text}");
    assert!(
        text.contains("postcondition"),
        "the failing obligation is the postcondition, output:\n{text}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn json_output_is_a_single_object_with_a_summary() {
    if !have_rustc() {
        eprintln!("cargo_verif: no rustc; skipping");
        return;
    }
    let dir = scratch_crate(TWO_FNS);
    let lib = dir.join("src").join("lib.rs");
    let (code, text) = run(&["--format", "json"], &lib);
    // `wrong` fails, so the run is not clean and exits 1 -- but the JSON is still
    // emitted (a machine consumer wants the report, not just the exit code).
    assert_eq!(code, 1, "a false contract must exit 1, output:\n{text}");
    let json = text.trim();
    assert!(json.starts_with('{') && json.ends_with('}'), "one JSON object:\n{json}");
    for key in ["\"file\":", "\"outcomes\":", "\"summary\":", "\"clean\":false", "\"failed\":1"] {
        assert!(json.contains(key), "JSON must carry {key}:\n{json}");
    }
    assert!(json.contains("\"name\":\"wrong\""), "JSON must name the failing function:\n{json}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_function_filter_ignores_the_broken_sibling() {
    if !have_rustc() {
        eprintln!("cargo_verif: no rustc; skipping");
        return;
    }
    // The same file has a broken `wrong`, but selecting `id_pos` must still be
    // clean -- the filter is a real restriction, not a label.
    let dir = scratch_crate(TWO_FNS);
    let lib = dir.join("src").join("lib.rs");
    let (code, text) = run(&["--fn", "id_pos"], &lib);
    assert_eq!(code, 0, "--function id_pos must ignore `wrong`, output:\n{text}");
    assert!(!text.contains("wrong"), "the broken sibling must not be reported:\n{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

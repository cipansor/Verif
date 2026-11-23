//! `verif-wrap` as `RUSTC_WRAPPER` (C8): verification that runs during `cargo build`.
//!
//! `RUSTC_WRAPPER=/path/to/verif-wrap cargo build` forwards every `rustc` call
//! through the wrapper, which verifies the *primary* package's contracts and fails
//! the build on a false one. These tests build a throwaway crate with the wrapper
//! set: a true contract must build, a false one must fail and name the obligation,
//! and a *dependency's* false contract must **not** fail the build (the wrapper
//! verifies the crate under development, not what it depends on).
#![cfg(feature = "std")]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

static SEQ: AtomicU32 = AtomicU32::new(0);

fn scratch_dir() -> PathBuf {
    let n = SEQ.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-wrap-{}-{}", std::process::id(), n));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("create scratch crate");
    dir
}

fn scratch_crate(lib_rs: &str) -> PathBuf {
    let dir = scratch_dir();
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"wrap_scratch\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
    )
    .expect("write manifest");
    std::fs::write(dir.join("src").join("lib.rs"), lib_rs).expect("write lib.rs");
    dir
}

fn have_cargo() -> bool {
    Command::new("cargo")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Build `dir` with `verif-wrap` as the wrapper; return `(exit code, output)`.
fn build_with_wrapper(dir: &Path) -> (i32, String) {
    let mut cmd = Command::new("cargo");
    cmd.arg("build").arg("--quiet").current_dir(dir);
    cmd.env("RUSTC_WRAPPER", env!("CARGO_BIN_EXE_verif-wrap"));
    cmd.env("CARGO_TARGET_DIR", dir.join("target"));
    if let Ok(rustc) = std::env::var("VERIF_RUSTC") {
        cmd.env("VERIF_RUSTC", rustc);
    }
    let out = cmd.output().expect("run cargo build");
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.code().unwrap_or(-1), text)
}

const TRUE_CONTRACT: &str = r#"
/// requires: x > 0
/// ensures: ret == x
pub fn id_pos(x: u32) -> u32 { x }
"#;

const FALSE_CONTRACT: &str = r#"
/// ensures: ret == 7
pub fn wrong(x: u32) -> u32 { x }
"#;

#[test]
fn a_true_contract_builds() {
    if !have_cargo() {
        eprintln!("rustc_wrapper: no cargo; skipping");
        return;
    }
    let dir = scratch_crate(TRUE_CONTRACT);
    let (code, text) = build_with_wrapper(&dir);
    assert_eq!(code, 0, "a true contract must build, output:\n{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_false_contract_fails_the_build() {
    if !have_cargo() {
        eprintln!("rustc_wrapper: no cargo; skipping");
        return;
    }
    let dir = scratch_crate(FALSE_CONTRACT);
    let (code, text) = build_with_wrapper(&dir);
    assert_ne!(code, 0, "a false contract must fail the build, output:\n{text}");
    assert!(
        text.contains("verification failed"),
        "the wrapper must say the build failed verification, output:\n{text}"
    );
    assert!(
        text.contains("postcondition"),
        "the failing obligation is the postcondition, output:\n{text}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// The wrapper verifies the *primary* package only: a dependency's false contract
/// does not fail the build. This is the `CARGO_PRIMARY_PACKAGE` guard, and without
/// it every dependency would have to carry contracts the wrapper then enforced.
#[test]
fn a_dependencys_false_contract_does_not_fail_the_build() {
    if !have_cargo() {
        eprintln!("rustc_wrapper: no cargo; skipping");
        return;
    }
    let dir = scratch_dir();
    std::fs::create_dir_all(dir.join("dep").join("src")).expect("create dep");
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"wrap_app\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
         \n[dependencies]\nwrap_dep = { path = \"dep\" }\n",
    )
    .expect("write app manifest");
    std::fs::write(
        dir.join("src").join("lib.rs"),
        "pub fn use_dep(x: u32) -> u32 { wrap_dep::wrong(x) }\n",
    )
    .expect("write app lib");
    std::fs::write(
        dir.join("dep").join("Cargo.toml"),
        "[package]\nname = \"wrap_dep\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
    )
    .expect("write dep manifest");
    std::fs::write(
        dir.join("dep").join("src").join("lib.rs"),
        FALSE_CONTRACT,
    )
    .expect("write dep lib");

    let (code, text) = build_with_wrapper(&dir);
    assert_eq!(
        code, 0,
        "a dependency's false contract must not fail the build, output:\n{text}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

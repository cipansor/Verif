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

/// Build `dir` with `verif-wrap` as the wrapper into `target`; return `(exit code, output)`.
fn build_with_wrapper_dir(dir: &Path, target: &Path) -> (i32, String) {
    let mut cmd = Command::new("cargo");
    cmd.arg("build").arg("--quiet").current_dir(dir);
    cmd.env("RUSTC_WRAPPER", env!("CARGO_BIN_EXE_verif-wrap"));
    cmd.env("CARGO_TARGET_DIR", target);
    if let Ok(rustc) = std::env::var("VERIF_RUSTC") {
        cmd.env("VERIF_RUSTC", rustc);
    }
    let out = cmd.output().expect("run cargo build");
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.code().unwrap_or(-1), text)
}

/// Build `dir` with `verif-wrap` into `dir/target`; return `(exit code, output)`.
fn build_with_wrapper(dir: &Path) -> (i32, String) {
    build_with_wrapper_dir(dir, &dir.join("target"))
}

/// Build `dir` with **no** wrapper into `target`; return `(exit code, output)`.
fn build_unwrapped(dir: &Path, target: &Path) -> (i32, String) {
    let out = Command::new("cargo")
        .arg("build")
        .arg("--quiet")
        .current_dir(dir)
        .env("CARGO_TARGET_DIR", target)
        .env_remove("RUSTC_WRAPPER")
        .output()
        .expect("run cargo build");
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
fn a_binary_that_imports_its_own_library_builds() {
    if !have_cargo() {
        eprintln!("rustc_wrapper: no cargo; skipping");
        return;
    }
    let dir = scratch_dir();
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"wrap_ownlib\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("src").join("lib.rs"),
        "/// ensures: ret == 42\npub fn answer() -> u8 { 42 }\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("src").join("main.rs"),
        "fn main() { let _ = wrap_ownlib::answer(); }\n",
    )
    .unwrap();
    let (code, text) = build_with_wrapper(&dir);
    assert_eq!(code, 0, "a binary importing its own library must build (Cargo's --extern forwarded), output:\n{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_build_script_with_a_build_only_dependency_is_forwarded() {
    if !have_cargo() {
        eprintln!("rustc_wrapper: no cargo; skipping");
        return;
    }
    let dir = scratch_dir();
    let bdep = dir.join("bdep");
    std::fs::create_dir_all(bdep.join("src")).unwrap();
    std::fs::write(
        bdep.join("Cargo.toml"),
        "[package]\nname = \"bdep\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    std::fs::write(bdep.join("src").join("lib.rs"), "pub fn val() -> u8 { 1 }\n").unwrap();
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"wrap_bs\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
         [build-dependencies]\nbdep = { path = \"bdep\" }\n",
    )
    .unwrap();
    std::fs::write(dir.join("build.rs"), "fn main() { let _ = bdep::val(); }\n").unwrap();
    std::fs::write(dir.join("src").join("lib.rs"), "pub fn x() -> u8 { 2 }\n").unwrap();
    let (code, text) = build_with_wrapper(&dir);
    assert_eq!(code, 0, "a build script with a build-only dependency must be forwarded, output:\n{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn enabling_verification_after_an_unwrapped_build_still_rejects_a_false_contract() {
    // An unwrapped build then a wrapped build that reuses its artifacts would skip the
    // check. The documented isolation (a dedicated target dir per mode) makes the
    // wrapped build fresh, so an unchanged false contract is still rejected.
    if !have_cargo() {
        eprintln!("rustc_wrapper: no cargo; skipping");
        return;
    }
    let dir = scratch_crate(FALSE_CONTRACT);
    let (code, text) = build_unwrapped(&dir, &dir.join("target-plain"));
    assert_eq!(code, 0, "an unwrapped build must succeed, output:\n{text}");
    let (code, text) = build_with_wrapper_dir(&dir, &dir.join("target-verified"));
    assert_ne!(code, 0, "a fresh wrapped build must reject the false contract, output:\n{text}");
    assert!(text.contains("wrong"), "the failing function must be named: {text}");
    let _ = std::fs::remove_dir_all(&dir);
}

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

/// Build `dir` with `verif-wrap` and extra cargo arguments.
fn build_with_wrapper_args(dir: &Path, extra: &[&str]) -> (i32, String) {
    let mut cmd = Command::new("cargo");
    cmd.arg("build").arg("--quiet").args(extra).current_dir(dir);
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

/// C9: the wrapper must forward Cargo's `--cfg feature=...` to the MIR emit, or a
/// contract that holds without a feature and fails with it would pass the build.
///
/// `!cfg!(feature = "fast")` is `true` without the feature and `false` with it. The
/// verifier emits its *own* MIR, so without forwarding `--cfg` it always sees the
/// feature off and approves `ensures: ret == true` even for the `--features fast`
/// build, whose artifact returns `false`.
#[test]
fn a_feature_that_flips_a_cfg_makes_the_contract_fail() {
    if !have_cargo() {
        eprintln!("rustc_wrapper: no cargo; skipping");
        return;
    }
    let dir = scratch_dir();
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"wrap_feat\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n\
         [features]\nfast = []\n",
    )
    .expect("write manifest");
    std::fs::write(
        dir.join("src").join("lib.rs"),
        "/// ensures: ret == true\npub fn is_slow() -> bool { !cfg!(feature = \"fast\") }\n",
    )
    .expect("write lib.rs");

    // Without the feature the contract holds and the build passes.
    let (code0, t0) = build_with_wrapper(&dir);
    assert_eq!(code0, 0, "without `fast` the contract holds, output:\n{t0}");

    // With `fast` the body returns `false`, so `ret == true` is false and the build
    // must fail -- which it only can if the wrapper forwarded `--cfg feature=fast`.
    let (code1, t1) = build_with_wrapper_args(&dir, &["--features", "fast"]);
    assert_ne!(
        code1, 0,
        "with `fast` the contract is false, so the build must fail; the wrapper must \
         forward `--cfg feature=fast` to the MIR emit, output:\n{t1}"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

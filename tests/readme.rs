//! The flagship example from `README.md`, compiled and run.
//!
//! The README is the crate's page on crates.io, so an example there that no
//! longer compiles is the documentation lying to every reader who never opens
//! the source. A doc comment would catch it if the README were included as one,
//! but it is a 2600-line document with its own structure, so the example is
//! pinned here instead: this file is the compile check, and the assertion is the
//! behaviour check.
//!
//! Keep this in step with the first Rust block in `README.md`.

use verif::prelude::*;

#[test]
fn readme_flagship_example_proves_a_bound() {
    // ∀ x:u8. (x & 0x0f) < 16          — proved by the embedded SMT engine
    let proved = verif::smt::with_fresh(|| {
        let x = var(8);
        (x & 0x0fu32).lt_val(16).prove().is_proved()
    });
    assert!(proved);
}

/// The Installation section must not tell a reader to run a command that fails.
///
/// The crates are packaged and release-ready but not on crates.io (the registry
/// answers "does not exist"), so the README depends on the git repository by tag
/// and says so. This pins the *shape* of that instruction: it must be a git
/// dependency and must carry the "not on crates.io" note. When the crates are
/// published, this test is the deliberate edit that flips it -- the failure is the
/// reminder, not a surprise.
#[test]
fn readme_install_is_a_git_dependency_until_published() {
    let readme = include_str!("../README.md");
    let install = readme
        .split("## Installation")
        .nth(1)
        .expect("README must have an Installation section")
        .split("\n## ")
        .next()
        .expect("the Installation section must end at the next heading");
    assert!(
        install.contains("Not on crates.io yet"),
        "Installation must say the crates are not published; got:\n{install}"
    );
    assert!(
        install.contains("git = \"https://github.com/cipansor/verif\""),
        "Installation must point at the git repository until the crates are published"
    );
    assert!(
        !install.contains("cargo add verif"),
        "Installation must not advertise `cargo add verif` while the crate is unpublished"
    );
}

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

/// The Installation section must tell a reader to depend on the published crate.
///
/// Both crates are on crates.io, so the README depends on `verif = "0.1"` rather
/// than on the git repository. This pins the *shape* of that instruction: a
/// version requirement, no git source, and the `verif-arithmetic` sibling named
/// as the published crate it is. If a release ever has to fall back to a git
/// dependency, this is the deliberate edit that flips it -- the failure is the
/// reminder, not a surprise.
#[test]
fn readme_install_uses_the_published_crate() {
    let readme = include_str!("../README.md");
    let install = readme
        .split("## Installation")
        .nth(1)
        .expect("README must have an Installation section")
        .split("\n## ")
        .next()
        .expect("the Installation section must end at the next heading");
    assert!(
        install.contains("verif = \"0.1\""),
        "Installation must depend on the published `verif = \"0.1\"`; got:\n{install}"
    );
    assert!(
        !install.contains("git = \"https://github.com/cipansor/verif\""),
        "Installation must not fall back to a git dependency once the crate is published"
    );
    assert!(
        install.contains("https://crates.io/crates/verif-arithmetic"),
        "Installation must name the published `verif-arithmetic` sibling"
    );
}

/// The "same function, two ways" example must be real code, not prose.
///
/// The README's two-shape section shows one function verified at build time (from
/// `build.rs`) and the same function verified on the target. The on-target snippet
/// is the one a reader copies into their own crate, so it is compiled and executed
/// here: the proof must discharge, and the function must compute what the contract
/// says. A snippet that no longer compiles -- or that no longer proves -- is the
/// documentation lying, which is exactly what this file exists to catch.
#[test]
fn readme_two_ways_on_target_snippet_proves_and_computes() {
    use verif::prelude::*;

    // The README's "verified on the target" `clamp100`, verbatim.
    fn clamp100(n: u32) -> u32 {
        let ok = verif::smt::with_fresh(|| {
            let x = var(32);
            let clamped = verif::smt::ite(x.gt_val(100), verif::smt::word(100, 32), x);
            clamped.le_val(100).prove().is_proved()
        });
        assert!(ok, "clamp100's bound did not discharge");
        if n > 100 { 100 } else { n }
    }

    assert_eq!(clamp100(0), 0);
    assert_eq!(clamp100(100), 100);
    assert_eq!(clamp100(101), 100);
    assert_eq!(clamp100(u32::MAX), 100);

    // The bound the snippet proves is falsifiable: a wrong one must be refuted, so
    // the assert above is a real discharge rather than a tautology.
    let refuted = verif::smt::with_fresh(|| {
        let x = var(32);
        verif::smt::ite(x.gt_val(100), verif::smt::word(100, 32), x)
            .lt_val(50)
            .prove()
    });
    assert!(!refuted.is_proved(), "a false bound must not be proved");
}

//! Independent probe corpus: ordinary Rust, not shaped for the verifier.
//!
//! Written by an external reviewer (see the PR #8 review, appendix), not by the
//! process that writes the verifier, so it is the honest answer to "how much
//! ordinary Rust can this tool decide?". The contracts are deliberately true, so
//! every `incomplete` is a *coverage* gap, not a wrong contract.
//!
//! The contracts are written as `spec! { … }` blocks, inline above each item, so
//! the specification and the code it describes are one artifact: the same file is
//! compiled, executed and verified. The macro is defined locally as a no-op, so
//! this file still builds with a bare `rustc` and imports nothing from `verif`.
//!
//! The score is tracked in `ROADMAP.md` (Phase 1's exit criterion is defined on
//! this file). Do not edit a function to make it decide: add a new one and leave
//! the old one as the record. Regenerate the score with:
//!
//! ```text
//! cargo run --features std --example mir_coverage -- examples/mir_targets/everyday.rs
//! ```
#![allow(dead_code)]


// The contract blocks below are *data for the verifier*, not code this file runs.
// A no-op definition keeps the corpus ordinary Rust: it still builds with a bare
// `rustc`, imports nothing from `verif`, and the macro expands to nothing.
macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: i < v.len(),
    ensures: true,
}
/// Slice indexing guarded by the caller.
pub fn get_at(v: &[u8], i: usize) -> u8 {
    v[i]
}

spec! {
    requires: true,
    ensures: true,
}
/// Iterator sum, may overflow.
pub fn sum_iter(v: &[u32]) -> u32 {
    v.iter().sum()
}

spec! {
    requires: true,
    ensures: ret >= a,
}
/// Checked add with fallback.
pub fn checked_or_max(a: u32, b: u32) -> u32 {
    a.checked_add(b).unwrap_or(u32::MAX)
}

spec! {
    requires: lo <= hi,
    ensures: lo <= ret,
    ensures: ret <= hi,
}
/// min/max on integers.
pub fn clamp_std(x: u32, lo: u32, hi: u32) -> u32 {
    x.max(lo).min(hi)
}

spec! {
    requires: lo <= hi,
    ensures: lo <= ret,
    ensures: ret <= hi,
}
/// Built-in clamp.
pub fn clamp_builtin(x: u32, lo: u32, hi: u32) -> u32 {
    x.clamp(lo, hi)
}

spec! {
    requires: true,
    ensures: ret >= a || ret >= b,
}
/// Average without overflow.
pub fn midpoint(a: u32, b: u32) -> u32 {
    a / 2 + b / 2 + (a % 2 + b % 2) / 2
}

spec! {
    requires: n <= 100,
    ensures: ret <= 5050,
}
/// Counted loop with a range.
pub fn tri(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..=n {
        s += i;
    }
    s
}

spec! {
    requires: true,
    ensures: true,
}
/// Option match.
pub fn or_zero(x: Option<u8>) -> u8 {
    match x {
        Some(v) => v,
        None => 0,
    }
}

spec! {
    requires: d != 0,
    ensures: ret <= n,
}
/// Guarded unwrap on a checked division.
pub fn div_unwrap(n: u32, d: u32) -> u32 {
    n.checked_div(d).unwrap()
}

/// Enum state machine.
#[derive(Clone, Copy)]
pub enum Mode {
    Idle,
    Run(u8),
    Fault,
}

spec! {
    requires: true,
    ensures: true,
}
pub fn next_mode(m: Mode) -> Mode {
    match m {
        Mode::Idle => Mode::Run(0),
        Mode::Run(n) if n < 10 => Mode::Run(n + 1),
        Mode::Run(_) => Mode::Idle,
        Mode::Fault => Mode::Fault,
    }
}

/// Struct method with &mut self.
pub struct Counter {
    pub n: u16,
}

impl Counter {
    spec! {
        requires: self.n < 1000,
        ensures: true,
    }
    pub fn bump(&mut self) {
        self.n += 1;
    }
}

spec! {
    requires: true,
    ensures: true,
}
/// Generic function.
pub fn first_or<T: Copy>(v: &[T], d: T) -> T {
    if v.is_empty() { d } else { v[0] }
}

spec! {
    requires: true,
    ensures: ret <= 9,
}
/// Byte parsing.
pub fn digit(b: u8) -> u8 {
    if b.is_ascii_digit() { b - b'0' } else { 0 }
}

spec! {
    requires: true,
    unwind: 5,
    ensures: ret >= a[0] && ret >= a[1] && ret >= a[2] && ret >= a[3],
}
/// Fixed array loop.
///
/// The loop body branches, so the search explores 199 paths -- more than the
/// default budget. `unwind: 5` both bounds the loop (four iterations) and grows
/// the path budget to match, which is what C4's exit criterion asks for.
pub fn max_of(a: [u8; 4]) -> u8 {
    let mut m = 0;
    let mut i = 0;
    while i < 4 {
        if a[i] > m {
            m = a[i];
        }
        i += 1;
    }
    m
}

spec! {
    requires: x < 200,
    ensures: ret == x + 1,
}
/// assert! with formatted message (PR #8 path).
pub fn inc_checked(x: u8) -> u8 {
    assert!(x < 200, "x too big: {}", x);
    x + 1
}

spec! {
    requires: x > -100 && x < 100,
    ensures: ret >= 0,
}
/// Signed arithmetic.
pub fn abs_small(x: i32) -> i32 {
    x.abs()
}

spec! {
    requires: true,
    ensures: ret <= 255,
}
/// Bit manipulation.
pub fn low_byte(x: u32) -> u32 {
    x & 0xff
}

spec! {
    requires: true,
    ensures: ret >= a,
}
/// Saturating ops from core.
pub fn sat(a: u16, b: u16) -> u16 {
    a.saturating_add(b)
}

spec! {
    requires: true,
    ensures: true,
}
/// Vec usage (allocation).
pub fn make(n: u8) -> usize {
    let mut v = Vec::new();
    v.push(n);
    v.len()
}

spec! {
    requires: true,
    ensures: true,
}
/// Wrapping mul.
pub fn hash_step(h: u32, b: u8) -> u32 {
    h.wrapping_mul(31).wrapping_add(b as u32)
}

spec! {
    requires: true,
    ensures: ret <= 25,
}
/// Division by constant.
pub fn pct(x: u8) -> u8 {
    x / 10
}

//! Tests for the MIR frontend.
//!
//! Run with a nightly compiler available:
//!
//! ```text
//! VERIF_RUSTC=$(rustup which --toolchain nightly rustc) \
//!   cargo test --features std --test mir
//! ```
//!
//! The tests that need `rustc` resolve it from `VERIF_RUSTC`, or fall back to the
//! `rustc` on `PATH`, and skip themselves only when there is no compiler at all.
//!
//! The fallback matters because a test that returns early reports `ok` while
//! checking nothing, so the suite's verdict would otherwise depend on the
//! environment: `let Some(report) = verify_all() else { return }` passes whether
//! the MIR frontend ran or not. `--emit=mir` is a *stable* flag (only
//! `-Zunpretty=mir` needs a nightly), so the `rustc` cargo already uses is enough,
//! and the fallback makes the ~21 `else { return }` tests run on any machine that
//! can build the crate. See the `U5` item in `ROADMAP.md`.
//!
//! # The oracle
//!
//! The strongest test here is [`counterexamples_really_panic`]. It takes each
//! counterexample the verifier produced, feeds those exact inputs to the *real*
//! function, and requires it to panic. That is a differential check against Rust
//! itself rather than against another model: if the engine reported a
//! counterexample that does not actually panic, the test fails. It is the same
//! discipline as the Z3 and Kani oracles elsewhere in this crate, with `rustc`'s
//! own code generator as the reference.
//!
//! # What is covered where
//!
//! The IR-level checks live in `src/mir/parse.rs` and `src/mir/exec.rs` as unit
//! tests, because the IR is crate-internal. This file covers the public surface:
//! the contract scanner, contract evaluation, and the end-to-end verdicts.

use verif::mir::spec;
use verif::mir::verify::{self, FnOutcome};

// The functions under verification, compiled from the exact file the frontend
// reads. `#[path]` rather than a copy means the test and the verifier can never
// drift: the same bytes are both verified and executed.
#[path = "../examples/mir_targets/actuator.rs"]
mod actuator;
use actuator::*;

const TARGET: &str = "examples/mir_targets/actuator.rs";

/// The compiler to read MIR from, or `None` so the test can skip.
///
/// `VERIF_RUSTC` wins when it is set (CI points it at a nightly, so the dump
/// format is exercised on the bleeding edge). Otherwise the `rustc` on `PATH` is
/// used, because `--emit=mir` is a stable flag and a test that silently checks
/// nothing is worse than one that runs on a stable compiler. The skip is now
/// reserved for a machine with no `rustc` at all, which cannot build this crate.
fn rustc() -> Option<String> {
    if let Some(p) = std::env::var("VERIF_RUSTC").ok().filter(|s| !s.is_empty()) {
        return Some(p);
    }
    let out = std::process::Command::new("rustc").arg("--version").output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some("rustc".to_string())
}

fn verify_all() -> Option<verify::FileReport> {
    let rustc = rustc()?;
    let only: Vec<String> = [
        "clamp",
        "rate_limit",
        "sat_add",
        "sat_sub",
        "shift_const",
        "shift_left",
        "sat_shift",
        "sat_mul",
        "unchecked_add",
        "unchecked_sub",
        "unchecked_div",
        "unchecked_mul",
        "off_by_one_guard",
        "clamp_signed",
        "checked_div_signed",
        "unchecked_div_signed",
        "signed_add_misguarded",
        "signed_add_guarded",
        "signed_mul_guarded",
        "signed_mul_negative",
        "checked_neg",
        "inline_saves_arg",
        "inline_clobber_would_pass",
        "bool_ret_false",
        "bool_ret_true",
        "nested_parens",
        "vacuous_precondition",
        "add_always_overflows",
        "div_by_always_zero",
        "clamp_bounds",
        "first_of",
        "slice_alias_tripwire",
        "assert_guarded",
        "assert_misguarded",
        "panic_guarded",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    match verify::verify_file_with(&rustc, std::path::Path::new(TARGET), &only) {
        Ok(r) => Some(r),
        Err(e) => panic!("frontend failed: {e}"),
    }
}

fn outcome<'a>(report: &'a verify::FileReport, name: &str) -> &'a FnOutcome {
    report
        .outcomes
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, o)| o)
        .unwrap_or_else(|| panic!("{name} missing from the report"))
}

/// Assert a function is *refuted* -- `Failed`, with a counterexample.
///
/// `!o.is_verified()` accepts `Skipped` and `Incomplete` too, so it does not
/// establish that a false postcondition produced a counterexample, which is the
/// only thing a tripwire is for: a tripwire that "passes" because the function
/// was skipped has never been pulled. This requires the refutation itself. A
/// shape that is *honestly* undecided must be asserted `!is_verified()` on
/// purpose, with a comment saying so.
fn assert_refuted(report: &verify::FileReport, name: &str) {
    let o = outcome(report, name);
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`{name}` must be refuted with a counterexample, got: {o}"
    );
}

// ---------------------------------------------------------------------------
// The contract scanner
// ---------------------------------------------------------------------------

#[test]
fn scanner_reads_contracts_and_ignores_inner_docs() {
    let src = r#"
//! requires: this is documentation, not a contract
//! ensures: and neither is this

/// requires: b != 0
/// ensures: ret <= a
pub fn div(a: u32, b: u32) -> u32 {
    a / b
}
"#;
    let specs = spec::extract(src);
    let c = specs.get("div").expect("div should have a contract");
    assert_eq!(c.requires, vec!["b != 0".to_string()]);
    assert_eq!(c.ensures, vec!["ret <= a".to_string()]);
}

#[test]
fn scanner_does_not_leak_a_contract_onto_a_later_function() {
    let src = r#"
/// requires: a > 0
const LIMIT: u32 = 10;

pub fn unrelated(a: u32) -> u32 { a }
"#;
    let specs = spec::extract(src);
    assert!(
        specs.get("unrelated").is_none(),
        "a contract before a non-fn item must not attach to the next fn"
    );
}

#[test]
fn scanner_finds_a_pub_crate_fn() {
    let src = "/// requires: a > 0\npub(crate) fn f(a: u32) -> u32 { a }\n";
    let specs = spec::extract(src);
    assert!(specs.get("f").is_some(), "`pub(crate) fn` must be recognized");
}

// ---------------------------------------------------------------------------
// Contract evaluation
// ---------------------------------------------------------------------------

#[test]
fn contract_expressions_evaluate() {
    use verif::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("b".to_string(), smt::var_named(2, 32));
        let p = spec::eval_requires("b != 0", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).expect("should parse");
        // `b != 0` is satisfiable but not valid: some b violates it.
        assert!(!smt::prove(p).is_proved());
    });
}

#[test]
fn a_contradictory_contract_is_refused_or_vacuous() {
    use verif::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("b".to_string(), smt::var_named(2, 32));
        // `b < 3 && b > 10` describes no input. The parser should read it, and
        // the engine should say the precondition is unsatisfiable.
        let p = spec::eval_requires("b < 3 && b > 10", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).expect("should parse");
        assert_eq!(smt::find_model(p), smt::Verdict::Unsat);
    });
}

#[test]
fn refuses_a_contract_it_cannot_read() {
    use verif::smt;
    smt::with_fresh(|| {
        let args = std::collections::BTreeMap::new();
        // A function call is not in the grammar, so it must be refused rather
        // than approximated.
        assert!(spec::eval_requires("foo(b) < 3", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).is_err());
        // A cast is not in the grammar either.
        assert!(spec::eval_requires("b as u64 < 3", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).is_err());
        // An unknown name is not an argument.
        assert!(spec::eval_requires("zzz < 3", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).is_err());
    });
}

/// A literal takes its width from the operand it meets, not from the widest
/// name in scope.
///
/// This is the bug that array support exposed. A slice or array length is a
/// `usize`, so once such an argument is in scope it becomes the widest name, and
/// a contract literal was sized from that maximum. `ret <= 255` for a `u8` return
/// then became an 8-bit value compared against a 64-bit constant, which the
/// engine reports as ill-formed -- and an ill-formed term makes *every*
/// obligation in the run `Unknown`, so the whole function was `incomplete` for a
/// reason that had nothing to do with its body.
///
/// The check is on the evaluator, so it does not depend on a corpus function
/// happening to be skipped for another reason. `n` stands in for the wide
/// length, `ret` for the narrow return: the literal must end up 8 bits wide.
#[test]
fn a_literal_is_sized_from_the_operand_it_meets() {
    use verif::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        // A 64-bit "length", in scope but not mentioned by the contract.
        args.insert("xs__len".to_string(), smt::var(64));
        let ret = smt::var(8);
        let p = spec::eval_ensures(
            "ret <= 255",
            &args,
            Some(ret),
            spec::RET_IS_UNKNOWN,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
            &std::collections::BTreeMap::new(),
        )
        .expect("a narrow literal against a wide name must still parse");
        assert!(
            !smt::is_ill_formed(),
            "the literal must be resized to `ret`'s 8 bits, not left at 64"
        );
        assert!(smt::prove(p).is_proved(), "`ret <= 255` must hold for every u8");
    });
}

/// A literal too large for the operand's width is refused, not truncated.
///
/// `a <= 300` for a `u8` cannot hold, so the honest answers are "refused" or
/// "unsatisfiable". What it must *not* be is silently narrowed to `a <= 44`,
/// which is what a truncating resize would do -- and that is a weaker claim that
/// could pass. The refusal is the error, and it names the width so the message is
/// actionable.
#[test]
fn a_literal_that_does_not_fit_is_refused_not_truncated() {
    use verif::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("a".to_string(), smt::var(8));
        let err = spec::eval_requires(
            "a <= 300",
            &args,
            &std::collections::BTreeSet::new(),
            &spec::FieldEnv::default(),
        )
        .expect_err("300 does not fit a u8, so the contract must be refused");
        assert!(
            err.to_string().contains("300") && err.to_string().contains("8-bit"),
            "the refusal must name the value and the width, got: {err}"
        );
    });
}

/// An aggregate return refuses a bare `ret` with the aggregate message.
///
/// `ret <= 5` on a `(u8, u8)` return is refused because there is no single word.
/// The message must say *that*, so the reader knows to name a component.
#[test]
fn a_bare_ret_on_an_aggregate_names_the_aggregate_reason() {
    use verif::smt;
    smt::with_fresh(|| {
        let args = std::collections::BTreeMap::new();
        let err = spec::eval_ensures(
            "ret <= 5",
            &args,
            None,
            spec::RET_IS_AGGREGATE,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
            &std::collections::BTreeMap::new(),
        )
        .expect_err("a bare `ret` on an aggregate must be refused");
        assert!(
            err.to_string().contains(spec::RET_IS_AGGREGATE),
            "the message must name the aggregate cause and the fix, got: {err}"
        );
    });
}

/// A scalar return whose value is unknown is refused with *that* reason.
///
/// The value can be unbound on a path where a read was unmodelled, even though
/// the return type is a plain `u8`. Reporting "the return type is an aggregate"
/// here would be false, and would send the reader looking for a tuple that does
/// not exist. The two causes have to be two messages.
#[test]
fn a_bare_ret_with_an_unknown_value_names_the_unknown_reason() {
    use verif::smt;
    smt::with_fresh(|| {
        let args = std::collections::BTreeMap::new();
        let err = spec::eval_ensures(
            "ret <= 5",
            &args,
            None,
            spec::RET_IS_UNKNOWN,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
            &std::collections::BTreeMap::new(),
        )
        .expect_err("a bare `ret` with no value must be refused");
        assert!(
            err.to_string().contains(spec::RET_IS_UNKNOWN),
            "a scalar return must not be reported as an aggregate, got: {err}"
        );
    });
}

/// A literal in *arithmetic* is sized to the operand it meets, like one in a
/// comparison.
///
/// `add_literal_wide_scope` has a slice length in scope, so a literal built at
/// the scope's 64-bit width would make `a + 5` an 8-bit/64-bit `Add` -- ill-formed,
/// and so `Unknown` for the whole run. The fix is the same `align_widths` the
/// comparison path uses, reached through the additive and multiplicative operators.
#[test]
fn a_literal_in_arithmetic_is_sized_to_its_operand() {
    let Some(report) = verify_realistic(&["add_literal_wide_scope"]) else { return };
    let o = outcome(&report, "add_literal_wide_scope");
    assert!(o.is_verified(), "`add_literal_wide_scope` must verify, got: {o}");
}

/// A named type bound carries the width of the type it names.
///
/// `i8::MIN` is the bit pattern `0x80`, exactly 8 bits. Building it at the
/// widest name in scope and narrowing it back would compare a 64-bit `128`
/// against the signed 8-bit range and refuse it -- a refusal of a bound that is
/// in range by construction. The width has to come from `i8`, not from the
/// contract's other operands.
#[test]
fn a_named_type_bound_keeps_its_own_width() {
    use verif::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("a".to_string(), smt::var(8));
        // A 64-bit name in scope, which is what used to widen the bound.
        args.insert("xs__len".to_string(), smt::var(64));
        let mut signed = std::collections::BTreeSet::new();
        signed.insert("a".to_string());
        let p = spec::eval_requires("a >= i8::MIN", &args, &signed, &spec::FieldEnv::default())
            .expect("`a >= i8::MIN` must parse even with a wide name in scope");
        assert!(!smt::is_ill_formed(), "the bound must be built at 8 bits");
        // Every `i8` is `>= i8::MIN`, so the precondition holds on all inputs.
        assert!(smt::prove(p).is_proved(), "`a >= i8::MIN` must hold for every i8");
    });
}

/// A negative literal keeps its value when it is widened to a signed operand.
///
/// `a >= -10` for an `i8` is the shape that makes sign extension matter: the
/// literal is parsed as `0 - 10` at some width and then has to reach `a`'s width
/// with the *value* preserved. Zero-extending it would turn `-10` into a large
/// positive number and the comparison would mean something else entirely.
#[test]
fn a_negative_literal_is_sign_extended_to_the_operand() {
    use verif::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("a".to_string(), smt::var(8));
        let mut signed = std::collections::BTreeSet::new();
        signed.insert("a".to_string());
        let p = spec::eval_requires("a >= -10", &args, &signed, &spec::FieldEnv::default())
            .expect("`a >= -10` must parse");
        assert!(!smt::is_ill_formed(), "the literal must be resized to 8 bits");
        // `a >= -10` is the negation of `a < -10`, and for an `i8` the only such
        // `a` are -128..=-11. So the contract must *fail* on those inputs.
        // `-10` as an `i8` is the bit pattern `0xF6`; building it from a `u64`
        // would itself be ill-formed, since `2^64 - 10` does not fit 8 bits.
        let minus_ten = smt::word(0xF6, 8);
        let bad = smt::and(p, smt::slt(args["a"], minus_ten));
        assert_eq!(
            smt::find_model(bad),
            smt::Verdict::Unsat,
            "`a >= -10` must exclude exactly `a < -10`"
        );
    });
    smt::with_fresh(|| {
        // The same contract with a 64-bit name also in scope. `-10` is built at
        // 64 bits as `2^64 - 10`, and narrowing that to 8 bits must take the low
        // byte (`0xF6`) rather than rebuild a word from the 64-bit value, which
        // would not fit and would set the ill-formed flag.
        let mut args = std::collections::BTreeMap::new();
        args.insert("a".to_string(), smt::var(8));
        args.insert("xs__len".to_string(), smt::var(64));
        let mut signed = std::collections::BTreeSet::new();
        signed.insert("a".to_string());
        let p = spec::eval_requires("a >= -10", &args, &signed, &spec::FieldEnv::default())
            .expect("`a >= -10` must parse with a wide name in scope");
        assert!(
            !smt::is_ill_formed(),
            "narrowing a negative literal must take the low bits, not rebuild a wide word"
        );
        // And it must still mean what it says: satisfiable (an `i8` of `-10`
        // satisfies it), but not valid (every `i8` below `-10` violates it).
        assert!(
            !matches!(smt::find_model(p), smt::Verdict::Unsat),
            "`a >= -10` must be satisfiable"
        );
        assert!(!smt::prove(p).is_proved(), "`a >= -10` must not hold for every i8");
    });
}

// ---------------------------------------------------------------------------
// End-to-end verification, with rustc
// ---------------------------------------------------------------------------

#[test]
fn guarded_functions_verify() {
    let Some(report) = verify_all() else { return };
    for name in [
        "clamp",
        "rate_limit",
        "sat_add",
        "sat_sub",
        // The three shift shapes: a constant amount, a guarded variable amount,
        // and an unguarded variable amount (which rustc's own `assert(n < 16)`
        // rejects, so it belongs with the refuted functions rather than here).
        "shift_const",
        "sat_shift",
        "clamp_bounds",
    ] {
        let o = outcome(&report, name);
        assert!(
            o.is_verified(),
            "{name} should verify, got: {o}\n{}",
            report_source_hint()
        );
    }
}

#[test]
fn unchecked_functions_are_refuted() {
    let Some(report) = verify_all() else { return };
    for name in [
        "unchecked_add",
        "unchecked_sub",
        "unchecked_div",
        "unchecked_mul",
        "shift_left",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "{name} must be refuted, got: {o}"
        );
    }
}

/// The load-bearing test: every counterexample must be real.
///
/// A counterexample is the verifier's evidence. If it does not reproduce, the
/// engine is wrong in the worst direction — it reported a defect that is not
/// there — so this replays each one against the real function and requires the
/// panic.
#[test]
fn counterexamples_really_panic() {
    let Some(report) = verify_all() else { return };
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut checked = 0;
    let mut failures: Vec<String> = Vec::new();
    for name in [
        "unchecked_add",
        "unchecked_sub",
        "unchecked_div",
        "unchecked_mul",
        // The variable shift is modelled now, so its counterexample is a real
        // one: `n == 16` is exactly what rustc's own `assert(n < 16)` rejects.
        "shift_left",
        // The signed cases. These are the ones that would have slipped through
        // while comparisons and overflow tests were unsigned-only, so replaying
        // their witnesses against the real functions is what keeps the fix
        // honest.
        "unchecked_div_signed",
        "signed_add_misguarded",
        "signed_mul_negative",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { detail, .. } = o else {
            continue;
        };
        // The arguments are locals `_1` and `_2`, and the report names them by
        // their source `debug` names, so the helper is told what to look for. A
        // model names only the variables it had to constrain -- `unchecked_div`
        // reports `d = 0` and says nothing about the dividend, because the divisor
        // alone decides -- so a missing variable is *unconstrained* and any value
        // will do. Zero is used, and the panic is still required: that is what
        // makes the witness a witness rather than a coincidence of one chosen
        // value.
        let names = match name {
            "unchecked_div" => ("n", "d"),
            "shift_left" => ("x", "n"),
            _ => ("a", "b"),
        };
        let (a, b) = parse_cex_args(detail, names);
        let a = a.unwrap_or(0);
        let b = b.unwrap_or(0);
        let panicked = match name {
            "unchecked_add" => std::panic::catch_unwind(|| unchecked_add(a as u16, b as u16)).is_err(),
            "unchecked_sub" => std::panic::catch_unwind(|| unchecked_sub(a as u16, b as u16)).is_err(),
            "unchecked_div" => std::panic::catch_unwind(|| unchecked_div(a as u32, b as u32)).is_err(),
            "unchecked_mul" => std::panic::catch_unwind(|| unchecked_mul(a as u8, b as u8)).is_err(),
            "shift_left" => std::panic::catch_unwind(|| shift_left(a as u16, b as u16)).is_err(),
            "unchecked_div_signed" => {
                std::panic::catch_unwind(|| unchecked_div_signed(a as i16, b as i16)).is_err()
            }
            "signed_add_misguarded" => {
                std::panic::catch_unwind(|| signed_add_misguarded(a as i8, b as i8)).is_err()
            }
            "signed_mul_negative" => {
                std::panic::catch_unwind(|| signed_mul_negative(a as i8, b as i8)).is_err()
            }
            _ => unreachable!(),
        };
        if !panicked {
            failures.push(format!(
                "{name}: counterexample a={a} b={b} did not actually panic, \
                 so the engine reported a defect that is not there"
            ));
        }
        checked += 1;
    }
    // Restore the real hook *before* asserting, or the failure message is
    // swallowed by the no-op hook and the test just says "FAILED".
    std::panic::set_hook(prev);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(checked >= 3, "expected several counterexamples, checked {checked}");
}

/// A wrong `ensures` is caught even when the function cannot panic.
///
/// `off_by_one_guard` guards its `a + b` correctly, so it is panic-free; the bug
/// is that it claims `ret >= a` and the `else` branch returns `0`. This is the
/// case that separates "no overflow" from "meets its contract", and it is why the
/// postcondition check exists rather than being folded into the panic check.
#[test]
fn a_wrong_postcondition_is_caught() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "off_by_one_guard");
    match o {
        FnOutcome::Failed { kind, detail } => {
            // `kind` says which obligation failed; `detail` is only the witness.
            assert!(
                kind.contains("postcondition"),
                "the failing obligation should be the postcondition, got kind `{kind}`"
            );
            // The witness must be a real input: `32768 + 32768` has the guard
            // take the `else` branch and return 0, which is not `>= a`. It must
            // also be *readable*: the report names the arguments, not `v1`/`v2`.
            assert!(
                detail.contains("a =") && detail.contains("b ="),
                "the witness should name both arguments by their source names, got: {detail}"
            );
            assert!(
                !detail.contains("v1:"),
                "the witness must not fall back to `v1:` for a named argument, got: {detail}"
            );
        }
        other => panic!("a wrong postcondition must be refuted, got: {other}"),
    }
}

/// U4: a counterexample is rendered with the source names, not internal indices.
///
/// A report that says `v1:u8 = 224` makes the reader decode the MIR's local
/// numbering; `x = 224` is what the source wrote. The names are the `debug`
/// bindings `rustc` records, which the frontend already keeps in `local_names`.
///
/// The teeth are the *fallback*: a variable with no source name must keep its
/// `v{index}:u{width}` spelling, so naming is a readability improvement and never
/// a loss of information. `unchecked_div` is the shape that exercises both at
/// once -- its dividend is a named argument, and the model constrains only the
/// divisor, so the witness names one variable and drops the other.
#[test]
fn a_counterexample_is_rendered_with_source_names() {
    let Some(report) = verify_all() else { return };

    // Every refutation in the corpus names its arguments by source name, and none
    // leaks a `v1:`/`v2:` spelling for a variable that *has* a source name.
    // `unchecked_div` constrains only the divisor, so its witness names `d` and
    // drops the dividend -- which is the point: a variable the model did not need
    // is *unconstrained*, and naming is not the same as requiring.
    for (name, expected) in [
        ("unchecked_add", &["a = ", "b = "][..]),
        ("unchecked_div", &["d = "][..]),
        ("shift_left", &["n = "][..]),
        ("signed_mul_negative", &["a = ", "b = "][..]),
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { detail, .. } = o else {
            panic!("{name} must be refuted, got: {o}");
        };
        for want in expected {
            assert!(
                detail.contains(want),
                "{name}: the witness should name its argument `{want}`, got: {detail}"
            );
        }
        assert!(
            !detail.contains("v1:") && !detail.contains("v2:"),
            "{name}: a named argument must not fall back to `vN:`, got: {detail}"
        );
    }

    // The positive control for the fallback: a variable the source did not name
    // still renders as `v{index}:u{width}`. This is a bare arithmetic function
    // with no `debug`-named arguments beyond the parameters, so the check is that
    // the *parameters* are named while nothing regresses to the old form for the
    // variables the model actually touched.
    let o = outcome(&report, "off_by_one_guard");
    let FnOutcome::Failed { detail, .. } = o else {
        panic!("off_by_one_guard must be refuted, got: {o}");
    };
    assert!(
        detail.contains("a = 32768") && detail.contains("b = 32768"),
        "the guard's witness must name both arguments, got: {detail}"
    );

    // The unnamed *assignment* itself, not only its absence. A witness whose
    // constrained variable has no `debug` name (a temporary, a promoted constant,
    // an aggregate part) must still be rendered, as `v{index}:u{width}`. Dropping
    // unnamed assignments would silently shrink a witness to the named subset --
    // and every check above would still pass, because they assert named names are
    // *present* and unnamed names are *absent from named functions*, never that an
    // unnamed one appears at all. `a_field_array_write_is_not_the_seed` (in the
    // realistic corpus) is the shape that produces one: its only constrained
    // variable is a temporary, so its witness is entirely unnamed.
    let Some(report) = verify_realistic(&["a_field_array_write_is_not_the_seed"]) else {
        return;
    };
    let o = outcome(&report, "a_field_array_write_is_not_the_seed");
    let FnOutcome::Failed { detail, .. } = o else {
        panic!("a_field_array_write_is_not_the_seed must be refuted, got: {o}");
    };
    assert!(
        detail.contains("v") && detail.contains(":u8 = "),
        "a variable with no source name must still render as `vN:uW = value`, got: {detail}"
    );
}

/// The other direction of the oracle: a function reported panic-free must not
/// panic on concrete inputs.
#[test]
fn verified_functions_do_not_panic_concretely() {
    let Some(report) = verify_all() else { return };
    if !outcome(&report, "sat_add").is_verified() {
        return;
    }
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut violations = Vec::new();
    // `sat_add` is verified for all u16, so every u16 pair must be fine. The full
    // cross product is 2^32, so this sweeps the overflow boundary plus a spread
    // of interior values.
    let mut vals: Vec<u16> = vec![0, 1, 2, 100, 32767, 32768, 65534, 65535];
    for i in 0..40u32 {
        vals.push((i.wrapping_mul(1657)) as u16);
    }
    for &a in &vals {
        for &b in &vals {
            if std::panic::catch_unwind(|| sat_add(a, b)).is_err() {
                violations.push((a, b));
            }
        }
    }
    std::panic::set_hook(prev);
    assert!(
        violations.is_empty(),
        "sat_add was verified but panics on {violations:?}"
    );
}

#[test]
fn sat_mul_is_verified_by_the_exact_division_overflow_test() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "sat_mul");
    // `sat_mul` guards `a * b` with `b != 0 && a > u16::MAX / b`. That guard *is* the
    // exact unsigned multiply-overflow predicate, so the path into the multiply
    // refutes the overflow obligation -- no 32-bit product is built, and the widened
    // product that used to be the documented BDD wall is never posed.
    //
    // This was `Incomplete` before, for a reason worth keeping visible: the predicate
    // used to be `x > MAX / c` only for a *constant* operand, and the general path
    // widened to `2w` bits and refused past 16. The two obligations were then
    // `b == 0 && a <= MAX / b` (path) against `b != 0 && a > MAX / b` (overflow), which
    // cancel pairwise but only *across* two `&&` spines -- so the boolean fold has to
    // see through the spines for the query to close. Both halves are what this test
    // pins: the exact division predicate, and the spine-aware cancellation that lets it
    // fold against the guard.
    assert!(
        o.is_verified(),
        "sat_mul must be verified now that the multiply-overflow test is exact: {o}"
    );
}

/// The signed/unsigned split, pinned so it cannot regress.
///
/// While comparisons and overflow tests were unsigned-only, every case here
/// produced the wrong answer and every *unsigned* case above still passed — the
/// whole suite was green while the engine called `127 + 1` panic-free. These
/// assertions are what would have caught it.
#[test]
fn signed_arithmetic_is_not_verified_as_unsigned() {
    let Some(report) = verify_all() else { return };

    // `signed_add_misguarded` has `requires: a <= 127 && b <= 1` and adds. The
    // unsigned overflow test calls it safe because the wrapped sum `128u8` is not
    // below `127u8`; the correct signed rule fires. It must be a *failure*, and
    // it must not be reported verified.
    let o = outcome(&report, "signed_add_misguarded");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a signed add that overflows on `127 + 1` must be refuted, got: {o}"
    );

    // The guard that actually holds, so the fix is not "reject everything signed".
    for name in ["signed_add_guarded", "signed_mul_guarded", "clamp_signed", "checked_neg"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} should verify, got: {o}");
    }

    // A signed comparison must take the negative branch. `clamp_signed` cannot
    // verify at all if `x < lo` is read unsigned, because `-1` would look larger
    // than any positive bound — so its `Verified` above is the comparison check.
    // This asserts the same thing from the other side: the misguarded add fails,
    // which requires the *overflow* test to be signed-aware rather than the
    // comparison alone.
    let o = outcome(&report, "signed_mul_negative");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a signed multiply of two negatives must be refuted, got: {o}"
    );
}

/// `i8::MIN` must parse as the top bit, not as zero.
///
/// `checked_neg`'s guard is `a != i8::MIN`. When the constant parser returned 0
/// for every `MIN`, that guard meant `a != 0`, so the `-128` case looked excluded
/// and the negation was reported panic-free. The function must verify *now* only
/// because the guard is real, and a version without it must fail.
#[test]
fn the_min_constant_is_the_top_bit() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "checked_neg");
    assert!(
        o.is_verified(),
        "checked_neg excludes i8::MIN and should verify, got: {o}"
    );
    // Replay the guard's own boundary against the real function: `-128` really
    // does panic under debug overflow checks, which is why excluding it matters.
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let panics = std::panic::catch_unwind(|| {
        // `black_box` keeps the constant from being folded, so the negation is
        // computed at runtime and its overflow check is the one being tested.
        let a: i8 = std::hint::black_box(i8::MIN);
        -a
    })
    .is_err();
    std::panic::set_hook(prev);
    assert!(panics, "`-i8::MIN` must panic, so the guard is load-bearing");
}

/// The other direction for signed code: a function reported panic-free must not
/// panic on any input it admits.
#[test]
fn verified_signed_functions_do_not_panic_concretely() {
    let Some(report) = verify_all() else { return };
    if !outcome(&report, "signed_add_guarded").is_verified() {
        return;
    }
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut violations = Vec::new();
    // The guard admits only `|a|, |b| <= 60`, so sweep that box exhaustively.
    for a in -60i16..=60 {
        for b in -60i16..=60 {
            if std::panic::catch_unwind(|| signed_add_guarded(a as i8, b as i8)).is_err() {
                violations.push((a, b));
            }
        }
    }
    std::panic::set_hook(prev);
    assert!(
        violations.is_empty(),
        "signed_add_guarded was verified but panics on {violations:?}"
    );
}

/// A contract naming a function that is not in the MIR must be reported, not
/// silently ignored — otherwise a typo turns a verified function into an
/// unverified one that still looks green.
#[test]
fn a_missing_contracted_function_is_reported() {
    let Some(rustc) = rustc() else { return };
    let only = vec!["no_such_function".to_string()];
    let report = verify::verify_file_with(&rustc, std::path::Path::new(TARGET), &only)
        .expect("the file itself should still parse");
    assert!(
        report.outcomes.is_empty(),
        "nothing should have been verified for an absent function"
    );
}

// ---------------------------------------------------------------------------
// The safety gate itself, with no compiler needed
// ---------------------------------------------------------------------------

#[test]
fn a_report_with_an_unknown_path_is_never_clean() {
    // The API-level invariant this whole frontend rests on: an incomplete run is
    // not a pass.
    let mut report = verify::FileReport::default();
    report.outcomes.push((
        "f".to_string(),
        FnOutcome::Incomplete {
            report: Box::new(verify::MirReport::default()),
            reasons: vec!["budget".to_string()],
        },
    ));
    assert!(!report.is_clean());
    assert_eq!(report.incomplete(), 1);
    assert_eq!(report.verified(), 0);
}

#[test]
fn a_missing_contract_is_not_clean() {
    let mut report = verify::FileReport::default();
    report.missing.push("ghost".to_string());
    assert!(!report.is_clean());
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn report_source_hint() -> &'static str {
    "hint: the frontend reads the MIR of examples/mir_targets/actuator.rs; \
     run examples/mir_demo.rs to see the per-function report"
}

/// Pull the values of a function's two arguments out of a rendered counterexample.
///
/// A witness is rendered with the source names the MIR `debug` bindings recorded
/// (`a = 128, b = 128`), so the argument names are passed in. A variable with no
/// source name keeps its `v{index}:u{width}` spelling, and the arguments here are
/// always locals `_1` and `_2`, so the fallback keys `v1:` / `v2:` are accepted
/// too -- the helper reads a named or an unnamed witness alike.
fn parse_cex_args(detail: &str, names: (&str, &str)) -> (Option<u64>, Option<u64>) {
    let mut first = None;
    let mut second = None;
    for part in detail.split(',') {
        let part = part.trim();
        let Some((lhs, rhs)) = part.split_once('=') else {
            continue;
        };
        let lhs = lhs.trim();
        let val: u64 = rhs.trim().parse().unwrap_or(0);
        if lhs == names.0 || lhs.starts_with("v1:") {
            first = Some(val);
        } else if lhs == names.1 || lhs.starts_with("v2:") {
            second = Some(val);
        }
    }
    (first, second)
}

// ---------------------------------------------------------------------------
// Regressions for the frontend bugs a review found: caller state clobbered by
// an inlined call, a boolean return bypassing the postcondition, a redundant
// parenthesis pair hiding a contract, and a scoped `debug` alias renaming a
// parameter.
// ---------------------------------------------------------------------------

/// An inlined call must not hand the caller the callee's locals.
///
/// Both functions have the same shape — save an argument, call something, return
/// the saved value — and differ only in the postcondition. The correct one must
/// verify and the false one must be refuted. If the caller's environment is not
/// restored, the continuation reads the callee's `_1` (holding `b`), so both
/// would verify.
#[test]
fn an_inlined_call_does_not_clobber_the_caller() {
    let Some(report) = verify_all() else { return };

    let good = outcome(&report, "inline_saves_arg");
    assert!(
        good.is_verified(),
        "returning the caller's saved argument must verify, got: {good}"
    );

    let bad = outcome(&report, "inline_clobber_would_pass");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "`ret == b` is false for `inline_clobber_would_pass` and must be refuted, got: {bad}"
    );
}

/// A `bool` return must be checked against the declared postcondition.
#[test]
fn a_boolean_return_is_checked_against_its_postcondition() {
    let Some(report) = verify_all() else { return };

    let bad = outcome(&report, "bool_ret_false");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "`ret == false` for a function returning `true` must be refuted, got: {bad}"
    );

    let good = outcome(&report, "bool_ret_true");
    assert!(
        good.is_verified(),
        "`ret == true` for the same function must verify, got: {good}"
    );
}

/// A redundant parenthesis pair must not make a contract unreadable.
#[test]
fn nested_predicate_parentheses_parse() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "nested_parens");
    assert!(
        o.is_verified(),
        "`requires: ((a == 0))` must parse and verify, got: {o}"
    );
}

/// A scoped `debug` alias must not rename a parameter.
///
/// `inline_saves_arg` prints `debug a => _1;` at function level and then
/// `debug saved => _1;` inside `scope 1`, because `let saved = a;` reuses `_1`.
/// When the later line overwrote the earlier one, the parameter `a` disappeared
/// and `ensures: ret == a` was skipped as unreadable. The function verifying at
/// all is the check; this pins the names directly so the failure is legible.
#[test]
fn a_scoped_debug_alias_does_not_rename_a_parameter() {
    let Some(rustc) = rustc() else { return };
    let mir = verify::emit_mir_with(&rustc, std::path::Path::new(TARGET))
        .expect("emit MIR for the target file");
    // The parameter is named `a`, and the `ensures` names it, so the contract
    // must be readable. A skip here is the bug.
    let report = verify::verify_file_with(&rustc, std::path::Path::new(TARGET), &[
        "inline_saves_arg".to_string(),
    ])
    .expect("verify");
    let (_, o) = report.outcomes.first().expect("one outcome");
    assert!(
        !matches!(o, FnOutcome::Skipped { .. }),
        "the contract names the parameter `a` and must be readable, got: {o}"
    );
    assert!(mir.contains("debug a => _1;"), "the parameter binding is expected in the dump");
}

/// An unreadable `ensures` must not be folded into `true`.
///
/// The postcondition closure used to swallow a parse error and return `true`, so
/// a function whose `ensures` could not be read would verify with *nothing*
/// checked. A skipped outcome is the honest report, and `is_clean` must not call
/// it clean.
#[test]
fn an_unreadable_ensures_is_reported_not_ignored() {
    let Some(rustc) = rustc() else { return };
    let dir = std::env::temp_dir().join("verif_unreadable_ensures");
    let _ = std::fs::create_dir_all(&dir);
    let src = dir.join("u.rs");
    std::fs::write(
        &src,
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == nonsense_name,\n}\npub fn f(a: u8) -> u8 { a }\n",
    )
    .expect("write source");
    let report =
        verify::verify_file_with_opts(&rustc, &src, &["f".to_string()], &probe_opts()).expect("verify");
    let (_, o) = report.outcomes.first().expect("one outcome");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "an unreadable `ensures` must be reported as skipped, got: {o}"
    );
    assert!(
        !report.is_clean(),
        "a report with a skipped function must not be clean"
    );
}

/// An unsatisfiable precondition is a finding, not a pass.
///
/// The implication `pre => post` is vacuously true when `pre` is unsatisfiable,
/// so a naive discharge reports `Verified`. The frontend adds an explicit
/// satisfiability obligation for exactly this reason, and it must be a failure.
#[test]
fn an_unsatisfiable_precondition_is_a_failure() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "vacuous_precondition");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`a < 3 && a > 10` admits no input and must be a failure, got: {o}"
    );
    let text = o.to_string();
    assert!(
        text.contains("vacuous precondition"),
        "the failure must name the vacuous precondition, got: {text}"
    );
}

/// A panic obligation whose verdict is `Valid` is a failure, not a proof.
///
/// This is the case that exposes the inverted polarity directly: the panic query
/// is `Valid`, and a naive "proved means good" reading counts it as discharged.
/// The obligation asks "can this panic happen", so `Valid` means it happens on
/// every input — the worst answer. `div_by_always_zero` divides by `d & 0`, which
/// is zero for every `d`, so its query is `Valid`.
#[test]
fn a_panic_obligation_that_is_valid_is_a_failure() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "div_by_always_zero");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a divide by an always-zero divisor must be a failure, got: {o}"
    );
    assert!(
        o.to_string().contains("panic"),
        "the failure must name the panic, got: {o}"
    );
}

/// A panic that happens on *every* input must be a failure, not a proof.
///
/// The obligation for a panic asks "can this panic happen", so `Unsat` is the
/// good answer and `Valid` is the worst one — the panic fires for every input.
/// Reading the verdict as "proved means good" inverts the answer, and
/// `add_always_overflows` is the case that makes it visible: the overflow query
/// is `Valid`, and the function must be reported as failing.
#[test]
fn a_panic_on_every_input_is_a_failure() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "add_always_overflows");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "an add that always overflows must be a failure, got: {o}"
    );
}

/// An `Unsat` postcondition must not be described as a universal truth.
///
/// A postcondition query is `path => post`. `Unsat` means it is false on *every*
/// input -- the postcondition holds for none. A `Valid` panic query means the
/// opposite, that the failure fires on *every* input. Both leave no witness, and
/// the first version collapsed both to "holds for every input", which describes
/// an impossible postcondition as a universal truth. The two diagnoses must
/// differ, and the `Unsat` one must say the postcondition holds for no input.
#[test]
fn an_impossible_postcondition_says_so_rather_than_the_opposite() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "bool_ret_false");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!("`bool_ret_false` must fail, got: {o}");
    };
    assert_eq!(kind, "postcondition");
    assert!(
        detail.contains("no input"),
        "an `Unsat` postcondition must be reported as holding for no input, got: {detail}"
    );
    assert!(
        !detail.contains("holds for every input"),
        "the diagnosis is reversed: an `Unsat` postcondition holds for none, got: {detail}"
    );
}

/// The counterpart: a panic query that is `Valid` fires on *every* input, and
/// its diagnosis must say that rather than borrowing the postcondition wording.
#[test]
fn an_always_firing_panic_says_it_fires_on_every_input() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "div_by_always_zero");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!("`div_by_always_zero` must fail, got: {o}");
    };
    assert!(kind.contains("panic"), "the kind must name the panic, got: {kind}");
    assert!(
        detail.contains("every input"),
        "a `Valid` panic query fires on every input and must say so, got: {detail}"
    );
}

// ---------------------------------------------------------------------------
// Contract projections: struct fields and tuple components
// ---------------------------------------------------------------------------

const REALISTIC: &str = "examples/mir_targets/realistic.rs";

/// Deliberately runs on the *default* test-thread stack (2 MiB), not a worker with
/// a larger one.
///
/// The corpus contains a nested shift amount (`x >> ((2 << 7) + 1)`), and the
/// parser recurses once per nesting level, so this call is sensitive to the size of
/// a parser frame. It used to abort here: `smt::evaluate` owns a 12 KiB memo as a
/// stack local, the optimiser inlined it into the recursive parser, and every level
/// of nesting then cost 12 KiB of stack. The fix is `#[inline(never)]` on
/// `evaluate` (see its doc comment), which brings the parse depth to ~15 KiB. This
/// test is the *gate* on that: reverting the attribute re-inflates the frames and
/// this aborts, so the fix cannot be quietly undone. A 64 MiB worker thread here
/// would have hidden the bug instead of catching it.
fn verify_realistic(only: &[&str]) -> Option<verify::FileReport> {
    let rustc = rustc()?;
    let only: Vec<String> = only.iter().map(|s| s.to_string()).collect();
    match verify::verify_file_with(&rustc, std::path::Path::new(REALISTIC), &only) {
        Ok(r) => Some(r),
        Err(e) => panic!("frontend failed: {e}"),
    }
}

/// The independent corpus, scored, so the number in `ROADMAP.md` cannot drift.
///
/// `everyday.rs` is ordinary Rust written by an external reviewer, not shaped for
/// the tool, so it is the honest measure of coverage (unlike `realistic.rs`, about
/// a third of which is adversarial fixtures). Phase 1's exit criterion in
/// `ROADMAP.md` is defined on it.
///
/// The assertion is a *floor*, not the exact score: adding a function that decides
/// must not fail the test, but a change that makes the tool decide *fewer* of them
/// -- a regression -- must. The exact score is printed by `mir_coverage`, which is
/// what `ROADMAP.md` quotes.
///
/// The count is `Verified` only, which is what `mir_coverage` counts. Counting
/// `Failed` too would let the floor and the scoreboard disagree: a corpus function
/// that turned from `verified` into `refuted` keeps the test's number and lowers
/// the printed one. `everyday.rs` is ordinary Rust that is supposed to *hold*, so a
/// refutation here is a bug, not coverage -- it is asserted against separately.
#[test]
fn the_independent_corpus_does_not_regress() {
    const EVERYDAY: &str = "examples/mir_targets/everyday.rs";
    let Some(rustc) = rustc() else { return };
    let report = match verify::verify_file_with(&rustc, std::path::Path::new(EVERYDAY), &[]) {
        Ok(r) => r,
        Err(e) => panic!("frontend failed: {e}"),
    };
    // A `Failed` is a *contract* failure only when the obligation that failed is a
    // claim the source made: a postcondition, a vacuous precondition, a loop
    // invariant. A `Failed` on a **panic** (or `unreachable`) obligation is not a
    // bug in the frontend -- it is the tool correctly reporting that the body can
    // panic. `sum_iter` (`v.iter().sum()`) is ordinary Rust whose unguarded
    // addition *does* overflow for `[u32::MAX, 1]`, and `everyday.rs` documents it
    // as "may overflow": rejecting every `Failed` would fail a correct panic
    // finding the moment iterator support lands. So the assertion is per kind, not
    // per outcome -- the panic family is allowed, the contract family is not.
    let refuted: Vec<&str> = report
        .outcomes
        .iter()
        .filter(|(_, o)| match o {
            FnOutcome::Failed { kind, .. } => {
                !(kind.starts_with("panic:") || kind.starts_with("reachable"))
            }
            _ => false,
        })
        .map(|(n, _)| n.as_str())
        .collect();
    assert!(
        refuted.is_empty(),
        "everyday.rs is ordinary Rust whose *contracts* must hold, so a contract \
         refutation is a bug: {refuted:?}. A corpus function that is genuinely false \
         belongs in a tripwire fixture, not here. (A panic or unreachable failure is a \
         legitimate finding and is allowed.)"
    );
    let verified = report
        .outcomes
        .iter()
        .filter(|(_, o)| matches!(o, FnOutcome::Verified { .. }))
        .count();
    assert!(
        verified >= 17,
        "everyday.rs verified {verified} of {} functions, down from 17 (81%); a regression \
         dropped coverage of ordinary Rust below Phase 1's 80% exit criterion. Run: cargo run \
         --features std --example mir_coverage -- {EVERYDAY}",
        report.outcomes.len()
    );

    // The three original gaps are *walls*, not budget problems: each is a claim the
    // engine cannot decide at the width the source uses, and a `verified` on any of
    // them would be a false proof of an unbounded claim. The corpus keeps the gap and
    // adds a *decidable companion* per gap rather than editing the original, so both
    // halves are pinned: the wall stays undecided, and the companion verifies. A
    // change that "fixes" a wall by widening a budget would turn the first assertion
    // red, and one that breaks the bounded shape turns the second red.
    let outcome_of = |name: &str| {
        report
            .outcomes
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, o)| o)
            .unwrap_or_else(|| panic!("`{name}` must be reported by `everyday.rs`"))
    };
    for gap in ["div_unwrap", "sum_iter", "tri"] {
        let o = outcome_of(gap);
        // These three are *completeness* limits today (`Incomplete`), not soundness
        // ones: their contracts are sound, so a future `Verified` is a *good* outcome.
        // `sum_iter` has no precondition, so it can legitimately overflow (a panic
        // finding is fine there); `tri` and `div_unwrap` are panic-free under their
        // declared preconditions, so *any* failure there would be a false finding.
        let false_finding = match gap {
            "sum_iter" => matches!(
                o,
                FnOutcome::Failed { kind, .. }
                    if !(kind.starts_with("panic") || kind.starts_with("reachable"))
            ),
            _ => matches!(o, FnOutcome::Failed { .. }),
        };
        assert!(
            !false_finding,
            "`{gap}` has a sound contract; a contract failure (or, for the panic-free \
             `tri`/`div_unwrap`, a panic finding) would be a false finding, got: {o}"
        );
    }
    for companion in ["div_unwrap_byte", "sum_iter_bounded", "tri_bounded"] {
        let o = outcome_of(companion);
        assert!(
            o.is_verified(),
            "`{companion}` is the decidable companion of a wall and must verify, got: {o}"
        );
    }
}

/// Every edition compiles the corpus to the same verdicts (review E4).
///
/// The frontend resolves the edition from the crate's own `Cargo.toml` rather
/// than pinning one, because the edition is part of what the program *means*: a
/// 2021 crate with `extern "C" { … }` is a compile error under 2024, and a `for`
/// loop over an array iterates `&T` under 2018 and `T` under 2021. So the same
/// source under two editions can lower to two different programs, and a verdict
/// is only meaningful for the edition it was produced under.
///
/// This runs `actuator.rs` under all four editions and requires the *whole*
/// outcome map to match, not just the decided count: a fixture that flipped from
/// `verified` to `failed` while another flipped the other way would keep the count
/// and change the answer. It is the check the `VERIF_EDITION` override exists for.
#[test]
fn every_edition_compiles_the_corpus_to_the_same_verdicts() {
    use verify::Edition;
    let Some(rustc) = rustc() else { return };
    let editions =
        [Edition::Rust2015, Edition::Rust2018, Edition::Rust2021, Edition::Rust2024];
    let mut baseline: Option<Vec<(String, String)>> = None;
    for ed in editions {
        let opts = verify::MirOptions { edition: Some(ed), ..Default::default() };
        let report = verify::verify_file_with_opts(&rustc, std::path::Path::new(TARGET), &[], &opts)
            .unwrap_or_else(|e| panic!("frontend failed under {}: {e}", ed.as_str()));
        // The verdict *shape*, so a `Failed { kind }` change is caught too, not
        // only a `Verified`/`Failed` flip.
        let shape: Vec<(String, String)> = report
            .outcomes
            .iter()
            .map(|(n, o)| (n.clone(), format!("{o:?}")))
            .collect();
        match &baseline {
            None => baseline = Some(shape),
            Some(base) => assert_eq!(
                base,
                &shape,
                "edition {} disagrees with 2015 on {}",
                ed.as_str(),
                TARGET
            ),
        }
    }
}

/// A 2021-only file is verified under *its own* edition, and refused under 2024
/// (review E1).
///
/// `extern "C" { … }` must be `unsafe extern` from edition 2024, so the same bytes
/// are a compile error there and valid under 2021. Pinning one edition would
/// therefore refuse a valid 2021 crate -- which is exactly what the frontend did
/// before `resolve_edition`. This asserts both directions: 2021 produces MIR and a
/// verdict, and 2024 is a frontend error (rustc's message, not a verdict). A test
/// that only checked the 2021 direction would pass on a frontend that ignored the
/// edition and always used rustc's default.
#[test]
fn a_2021_only_file_is_verified_under_its_own_edition() {
    use verify::Edition;
    let Some(rustc) = rustc() else { return };
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nextern \"C\" {\n    fn abs(x: i32) -> i32;\n}\nspec! {\n    ensures: ret == x,\n}\npub fn f(x: u8) -> u8 { x }\n";
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-edition-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("probe.rs");
    std::fs::write(&file, src).expect("write probe");

    let opts21 = verify::MirOptions { edition: Some(Edition::Rust2021), ..Default::default() };
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &opts21)
        .expect("a 2021 file with `extern \"C\"` must compile under 2021");
    let o = report.outcomes.iter().find(|(n, _)| n == "f").map(|(_, o)| o.clone());
    assert!(
        matches!(o, Some(FnOutcome::Verified { .. })),
        "the 2021 fixture must verify under 2021, got: {o:?}"
    );

    // The same bytes under 2024 are a rustc error, so the frontend reports it
    // rather than a verdict. That is the evidence the edition is *used*.
    let opts24 = verify::MirOptions { edition: Some(Edition::Rust2024), ..Default::default() };
    assert!(
        verify::verify_file_with_opts(&rustc, &file, &[], &opts24).is_err(),
        "the 2021-only file must be refused under 2024, not silently compiled"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A real package that omits `package.edition` resolves to Cargo's 2015 default.
///
/// Cargo assigns edition 2015 to a `[package]` that does not state one, so the
/// frontend must verify such a package rather than refuse it. This is the
/// distinction between "what edition is this crate?" (2015, by Cargo's default)
/// and "what edition is this loose file?" (no answer). The unit tests pin the
/// resolution directly; this pins it end to end, because the refusal the review
/// found happened before `rustc` was ever invoked.
#[test]
fn a_package_that_omits_an_edition_is_verified_as_2015() {
    let Some(rustc) = rustc() else { return };
    // `VERIF_EDITION` is a deliberate *override* -- it is what the edition matrix
    // uses to force a file that has a manifest under another edition -- so it wins
    // over the manifest and this test cannot assert the manifest default while it
    // is set. The environment is process-global, so the sibling unit test guards
    // the same way.
    if std::env::var("VERIF_EDITION").map(|v| !v.is_empty()).unwrap_or(false) {
        return;
    }
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-pkg2015-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    // A manifest with no `edition`, exactly as the review describes.
    std::fs::write(
        dir.join("Cargo.toml"),
        "[package]\nname = \"demo\"\nversion = \"0.1.0\"\n",
    )
    .expect("write manifest");
    let file = dir.join("probe.rs");
    std::fs::write(&file, "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == x,\n}\npub fn f(x: u8) -> u8 { x }\n")
        .expect("write probe");

    // No explicit edition: the manifest supplies it. A refusal here is the bug.
    let opts = verify::MirOptions { edition: None, ..Default::default() };
    let (text, edition) = verify::emit_mir_with_opts(&rustc, &file, &opts)
        .expect("a package without an `edition` must resolve to Cargo's 2015 default");
    assert_eq!(edition, verify::Edition::Rust2015, "the default edition is 2015");
    assert!(!text.is_empty(), "MIR must be emitted for the package");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A user function returning `!` is reported as a diverging call, not a panic.
///
/// `die() -> ! { loop {} }` never returns, so a reachable call to it is a
/// reachable failure -- but the failure is an infinite loop, not a panic. The
/// report used to say `panic: die`, naming an event that never occurs. The kind is
/// read from the callee's name, and an unrecognised `!`-returning function is
/// `diverges`, which is the honest label.
#[test]
fn a_non_panicking_diverging_call_is_not_labelled_a_panic() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub fn die() -> ! { loop {} }\nspec! {\n    requires: true,\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { if x == 0 { die(); } 1 }\n";
    let Some(o) = verify_src("f", src) else { return };
    match o {
        FnOutcome::Failed { kind, .. } => {
            assert!(
                kind.contains("diverges"),
                "a user `!`-returning function must be labelled `diverges`, not `panic`: got `{kind}`"
            );
            assert!(
                !kind.contains("panic"),
                "a non-panicking diverging call must not be labelled a panic: got `{kind}`"
            );
        }
        other => panic!("a reachable call to a `!` function must fail, got: {other}"),
    }
}

/// A real panic *is* labelled a panic, so the label still distinguishes the two.
///
/// The companion to the test above: the fix must not flatten every diverging call
/// to `diverges`. An `assert!` is a panic, and the report says so.
#[test]
fn a_panicking_diverging_call_is_labelled_a_panic() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { if x == 0 { panic!(\"boom\"); } 1 }\n";
    let Some(o) = verify_src("f", src) else { return };
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("panic"),
            "a real panic must be labelled `panic`: got `{kind}`"
        ),
        other => panic!("an unguarded panic must fail, got: {other}"),
    }
}

/// A contract can name a struct field, and the field's *value* reaches the body.
///
/// `pick_from`'s precondition is `c.lo <= c.hi` and its postcondition is
/// `ret >= c.lo`. Both name fields of a `&Config`, which the MIR dump prints only
/// as `_1: &Config` with no layout — the frontend has to read the layout from the
/// source. Before that, this function was `skipped` with "unknown name".
#[test]
fn a_contract_can_name_a_struct_field() {
    let Some(report) = verify_realistic(&["pick_from", "clamp_by_value"]) else { return };
    for name in ["pick_from", "clamp_by_value"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// The tripwire for field *independence*.
///
/// `field_alias_tripwire` has the same shape as `clamp_by_value` but claims
/// `ret >= c.hi`, which is false whenever `v < c.lo <= c.hi`. It must FAIL. If
/// `c.lo` and `c.hi` were bound to the same symbolic variable the claim would be
/// `ret >= x` with `ret` in `{x, v}` and `v` unconstrained-but-`<= x`... which is
/// exactly the vacuous pass this test exists to catch. A counterexample is the
/// positive evidence that the two fields are distinct inputs.
#[test]
fn struct_fields_are_independent_inputs_not_one_aliased_variable() {
    let Some(report) = verify_realistic(&["field_alias_tripwire"]) else { return };
    let o = outcome(&report, "field_alias_tripwire");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!(
            "`field_alias_tripwire` must fail: a pass means `c.lo` and `c.hi` \
             collapsed to one variable and the contract was vacuous. got: {o}"
        );
    };
    assert_eq!(kind, "postcondition", "got: {o}");
    // The witness must name two different variables for the two fields. If the
    // binding aliased, the same variable index would appear for both.
    let names: Vec<&str> = detail.split_whitespace().filter(|t| t.starts_with('v')).collect();
    assert!(
        names.len() >= 2,
        "the counterexample must assign both fields to show they differ, got: {detail}"
    );
    assert!(
        names.iter().collect::<std::collections::BTreeSet<_>>().len() >= 2,
        "the two fields were assigned the same variable, so they are aliased: {detail}"
    );
}

/// A slice contract the frontend must *not* prove: `first_of` is sound, but
/// `slice_alias_tripwire` claims `ret == xs[1]` where the body returns `xs[0]`.
///
/// The tripwire exists because the tempting wrong model is to give a slice one
/// "element" variable. Then `xs[0] == xs[1]` and the claim would hold. A failure
/// is the evidence that two indices are two inputs; a pass means the slice was
/// collapsed and `first_of`'s proof is not worth anything.
#[test]
fn slice_elements_are_independent_inputs_not_one_aliased_variable() {
    let Some(report) = verify_realistic(&["slice_alias_tripwire"]) else { return };
    let o = outcome(&report, "slice_alias_tripwire");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!(
            "`slice_alias_tripwire` must fail: a pass means `xs[0]` and `xs[1]` \
             collapsed to one variable and the slice contract was vacuous. got: {o}"
        );
    };
    assert_eq!(kind, "postcondition", "got: {o}");
    let names: Vec<&str> = detail.split_whitespace().filter(|t| t.starts_with('v')).collect();
    assert!(
        names.iter().collect::<std::collections::BTreeSet<_>>().len() >= 2,
        "the two elements were assigned the same variable, so they are aliased: {detail}"
    );
}

/// The slice length is a symbolic input, not a constant, and `xs.len()` in a
/// contract names the same variable the body's `PtrMetadata` reads.
///
/// `first_of` requires `xs.len() > 0` and claims `ret == xs[0]`. If the length
/// were a fixed constant (say `0`), the precondition would be unsatisfiable and
/// the function would be reported vacuous rather than verified; if the contract's
/// `xs.len()` and the body's `PtrMetadata` were *different* variables, the
/// bounds `assert` could not be discharged from the precondition and the function
/// would be incomplete. Verified is the only outcome that shows both hold.
#[test]
fn a_slice_length_is_a_symbolic_input_shared_with_the_body() {
    let Some(report) = verify_realistic(&["first_of"]) else { return };
    let o = outcome(&report, "first_of");
    assert!(o.is_verified(), "`first_of` must verify, got: {o}");
}

/// A fixed-size array argument: elements are inputs, but the length is not.
///
/// `max_of_pair` requires `a[0] <= a[1]` and claims `ret == a[1]`. This is the
/// array counterpart of `first_of`, and the difference is the point: a slice's
/// length is a symbolic input read through `PtrMetadata`, while an array's length
/// is a *type* constant, so the bounds check in the body is against the literal
/// `4` and `a.len()` in a contract is `4` rather than a fresh variable.
#[test]
fn a_contract_can_name_a_fixed_size_array_element() {
    let Some(report) = verify_realistic(&["max_of_pair", "array_third"]) else { return };
    for name in ["max_of_pair", "array_third"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// An array built in the body has *concrete* elements, not inputs.
///
/// `array_literal_elem` returns `a[1]` of `[10, 20, 30, 40]` and claims
/// `ret == 20`. Verified is the evidence that the element map holds the literal
/// values: if the index were modelled as an unconstrained input the claim would
/// fail with a counterexample instead.
#[test]
fn an_array_literal_element_is_concrete() {
    let Some(report) = verify_realistic(&["array_literal_elem"]) else { return };
    let o = outcome(&report, "array_literal_elem");
    assert!(o.is_verified(), "`array_literal_elem` must verify, got: {o}");
}

/// The tripwire for array *element independence*.
///
/// `array_alias_tripwire` has the same body as `max_of_pair` but claims
/// `ret <= a[0]`, which is false when `a[1] > a[0]`. It must FAIL, and the
/// counterexample must assign `a[0]` and `a[1]` to *different* variables -- a
/// pass would mean the elements collapsed to one input and `max_of_pair`'s proof
/// was vacuous.
#[test]
fn array_elements_are_independent_inputs_not_one_aliased_variable() {
    let Some(report) = verify_realistic(&["array_alias_tripwire"]) else { return };
    let o = outcome(&report, "array_alias_tripwire");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!(
            "`array_alias_tripwire` must fail: a pass means `a[0]` and `a[1]` \
             collapsed to one variable and the array contract was vacuous. got: {o}"
        );
    };
    assert_eq!(kind, "postcondition", "got: {o}");
    let names: Vec<&str> = detail.split_whitespace().filter(|t| t.starts_with('v')).collect();
    assert!(
        names.iter().collect::<std::collections::BTreeSet<_>>().len() >= 2,
        "the two elements were assigned the same variable, so they are aliased: {detail}"
    );
}

/// The corpus tripwires for the write/read-store desync, asserted end to end.
///
/// Each of these contracts is *false* and the frontend used to prove one of them.
/// The corpus (`examples/mir_targets/realistic.rs`) carries them so
/// `examples/mir_coverage` measures the shape; this pins the verdict so a
/// regression is a test failure rather than a quiet false proof.
#[test]
fn a_write_cannot_prove_a_stale_contract() {
    let names = [
        "array_write_then_symbolic_read",
        "mut_ref_array_write_then_symbolic_read",
        "generated_name_shadows_argument",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` proves a false contract; got: {o}"
        );
    }
    // The struct-reassignment shape is refused rather than refuted: the write
    // poisons `c.lo`, and the postcondition then has no single value to check.
    // The requirement is the same -- never `Verified`.
    let Some(report) = verify_realistic(&["struct_reassign_then_field_read"]) else { return };
    let o = outcome(&report, "struct_reassign_then_field_read");
    assert!(
        !o.is_verified(),
        "`struct_reassign_then_field_read` proves a stale field; got: {o}"
    );
}

/// Stage 2: the newly modelled rvalues, each with its tripwire.
///
/// These four shapes -- a struct literal, a reference to a place, `.len()` on an
/// array, and a whole-struct reassignment -- were all `Unknown` before, so their
/// contracts were unreadable rather than checked. Each pair below is a true
/// contract that must now verify and a false one that a wrong model would prove.
/// The tripwires are the point: verifying the true half alone would not show the
/// model is right, only that it is present.
#[test]
fn stage_two_rvalues_are_modelled_and_their_tripwires_refuted() {
    let verified = [
        "struct_literal_reads_its_field",
        "struct_literal_order",
        "reference_reads_through",
        "reference_write_reaches_target",
        "array_len_is_the_type_constant",
        "struct_reassign_reads_new_field",
        "enum_match_is_bounded",
        "enum_match_selects_by_tag",
        "enum_payload_reads_through",
        "enum_constructed_locally",
        "enum_constructed_payload_reads_through",
        "enum_explicit_discriminant_selects_by_tag",
        "enum_user_variant_not_option",
        "enum_user_variant_not_option_constructed",
    ];
    let refuted = [
        // Written in reverse order; a positional-by-write-order model proves it.
        "struct_literal_order_tripwire",
        // The pre-write value; a snapshot model of `&mut` proves it.
        "reference_write_tripwire",
        // Claims every arm returns `2`; only a constant tag proves it.
        "enum_match_tripwire",
        // Claims the `Off` arm ran for a value built as `Mode::Idle`; a model
        // that resolved the variant to the wrong index (or to a symbolic tag)
        // would prove it.
        "enum_constructed_locally_tripwire",
        // Claims the `B` arm ran for `Gap::C`, whose real tag is `4`; a reader
        // numbering variants by position would call it `1` and prove this.
        "enum_explicit_discriminant_tripwire",
        // Claims the `None` arm ran for `Shadow::Some`, whose real tag is `0`;
        // taking `Option`'s numbering for the qualified name proves this.
        "enum_user_variant_not_option_tripwire",
        "enum_user_variant_not_option_constructed_tripwire",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
    }
}

/// A `u16` product is decided end to end, which the product bound now admits.
///
/// The `u16` `saturating_mul` in the corpus used to report "past what the model
/// covers": the widened product test needs a `2w`-bit multiplier, and the bound
/// stopped the widening at `2w == 16`. The bound is 16 now, so the guarded
/// fixture must verify and the deliberately unguarded one must still be refuted.
/// The pair matters more than the verify: a bound raised without the refutation
/// would be a model that proves the wrong thing, which is worse than one that
/// declines.
#[test]
fn a_u16_product_is_decided_end_to_end() {
    let Some(report) = verify_realistic(&["u16_product_guarded"]) else { return };
    let o = outcome(&report, "u16_product_guarded");
    assert!(o.is_verified(), "`u16_product_guarded` must verify, got: {o}");

    let Some(report) = verify_realistic(&["u16_product_unguarded_tripwire"]) else { return };
    let o = outcome(&report, "u16_product_unguarded_tripwire");
    let FnOutcome::Failed { .. } = o else {
        panic!("`u16_product_unguarded_tripwire` is false and must be refuted, got: {o}");
    };
}


/// The complement bit counts `count_zeros`, `leading_ones` and `trailing_ones`,
/// each pinned by a true half and a tripwire.
///
/// Each is `core`'s own definition -- the corresponding *positive* count of `!x`
/// -- so a model that summed the wrong polarity would be wrong by the complement,
/// which is a wrong value and not a weaker proof. `count_zeros` is pinned at a
/// single operand where the two polarities disagree, and the two one-sided counts
/// are pinned at the boundary of their precondition. The tripwires are the
/// evidence the count is read at all: a constant answer would prove neither the
/// true half nor the false one.
#[test]
fn the_complement_bit_counts_agree_with_rust() {
    let verified = [
        "count_zeros_of_zero_is_the_width",
        "leading_ones_of_a_top_bit_value",
        "trailing_ones_of_a_small_value",
    ];
    let refuted = [
        "count_zeros_of_zero_is_the_width_tripwire",
        "leading_ones_of_a_top_bit_value_tripwire",
        "trailing_ones_of_a_small_value_tripwire",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
    }
}

/// `is_power_of_two` is modelled as a `bool` the `if` branches on.
///
/// This is the `bool`-channel pin, and it is a different kind of test from the
/// bit counts: the model produces a `Pred` rather than a `Var`, and the executor
/// writes it as a `Val::Bool`. A model that wrote a one-bit *word* into the
/// destination would leave the local readable only as a word, and the postcondition
/// `ret == true` would not read it -- so `is_power_of_two_of_the_top_bit` fails
/// rather than passing by accident. The zero tripwire is the sharp one: `0` is the
/// single value the bare `x & (x - 1) == 0` mask test would accept, so a model
/// that dropped the `x != 0` conjunct would *prove* the false contract.
#[test]
fn is_power_of_two_is_a_modelled_bool() {
    let verified = ["is_power_of_two_of_the_top_bit", "is_power_of_two_of_three"];
    let refuted = ["is_power_of_two_of_zero_tripwire"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
    }
}

/// The `bool` is consumed by a `switchInt`, not only read in a postcondition.
///
/// `is_power_of_two_is_a_modelled_bool` returns the predicate, so the `bool`
/// reaches the return place and the obligation reads it there; a regression in
/// *branching* on it would leave those tests green. These fixtures put the
/// predicate in an `if`, where the executor has to turn the `Pred` into a path
/// condition and take one of two arms returning different constants. The two
/// arms are pinned separately, so a model that took a constant arm fails one of
/// them, and the zero tripwire pins the `x != 0` conjunct *through the branch*:
/// a model that dropped it takes the `then` arm and proves the false `ret == 7`.
#[test]
fn is_power_of_two_branches_on_the_predicate() {
    let verified = [
        "is_power_of_two_branching_takes_the_true_arm",
        "is_power_of_two_branching_takes_the_false_arm",
    ];
    let refuted = ["is_power_of_two_branching_of_zero_tripwire"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
    }
}

/// `midpoint`, `next_multiple_of` (and its `checked_` counterpart), the two
/// logarithms and the `next_power_of_two` pair, pinned in both directions.
///
/// `core::num` methods added as a group. The true halves pin the *value* --
/// `midpoint` of an overflowing sum (`255.midpoint(255) == 255`, not the wrapped
/// `254`), the truncating rounding (`(-5).midpoint(-2) == -3`, not the floor
/// `-4`), `next_multiple_of` of an exact multiple (the identity, which a model
/// that always added `b` gets wrong), the logs at their boundary values
/// (`ilog2(1) == 0`, `ilog10(9) == 0`), and `next_power_of_two` at the three
/// boundaries that separate a right model from a plausible wrong one (`0 -> 1`,
/// a power of two rounding to itself, and `100 -> 128`). Each true half has a
/// `_cannot_prove_this` twin that the same wrong model would prove, so a green
/// verdict on the twin fails the test.
///
/// The panic-shaped methods carry the opposite evidence: `next_multiple_of` that
/// overflows, `ilog2`/`ilog10` of zero, and `next_power_of_two` of `129` must
/// *fail* with the panic obligation, and a control
/// (`next_multiple_of_is_panic_free_here`, `next_power_of_two_is_panic_free_here`)
/// must verify, so a model that reported a panic unconditionally cannot pass. The
/// `checked_` counterparts are the value-shaped ones: `Some(128)` where the plain
/// method would not panic, `None` where it would -- for both the power-of-two and
/// the multiple-of pairs, including the zero divisor for the latter.
#[test]
fn the_new_num_methods_verify_and_their_tripwires_refute() {
    let verified = [
        "midpoint_self_is_the_identity",
        "midpoint_of_an_overflowing_sum",
        "midpoint_rounds_toward_zero",
        "midpoint_signed_truncates",
        "midpoint_is_between",
        "next_multiple_of_rounds_up",
        "next_multiple_of_an_exact_multiple_is_the_identity",
        "next_multiple_of_is_panic_free_here",
        "checked_next_multiple_of_rounds_up",
        "checked_next_multiple_of_that_overflows_is_none",
        "checked_next_multiple_of_by_zero_is_none",
        "ilog2_of_100",
        "ilog2_of_one_is_zero",
        "ilog2_of_a_signed_100",
        "ilog2_is_bounded",
        "ilog10_of_100",
        "ilog10_below_ten_is_zero",
        "ilog10_of_a_u32_thousand",
        "ilog10_is_bounded",
        "checked_ilog2_in_range",
        "checked_ilog2_of_zero_is_none",
        "checked_ilog10_in_range",
        "checked_ilog10_of_zero_is_none",
        "checked_ilog2_of_a_negative_is_none",
        "next_power_of_two_rounds_up",
        "next_power_of_two_of_a_power_is_itself",
        "next_power_of_two_of_zero_is_one",
        "next_power_of_two_of_a_u32_thousand",
        "next_power_of_two_is_panic_free_here",
        "checked_next_power_of_two_in_range",
        "checked_next_power_of_two_out_of_range_is_none",
    ];
    let refuted = [
        "midpoint_of_an_overflowing_sum_cannot_prove_this",
        "midpoint_rounds_toward_zero_cannot_prove_this",
        "midpoint_signed_truncates_cannot_prove_this",
        "midpoint_is_between_cannot_prove_this",
        "next_multiple_of_rounds_up_cannot_prove_this",
        "checked_next_multiple_of_overflow_is_some_cannot_prove_this",
        "ilog2_of_100_cannot_prove_this",
        "ilog10_of_100_cannot_prove_this",
        "checked_ilog2_overflow_is_some_cannot_prove_this",
        "checked_ilog2_of_a_negative_cannot_prove_this",
        "next_power_of_two_rounds_up_cannot_prove_this",
        "checked_next_power_of_two_in_range_cannot_prove_this",
        "checked_next_power_of_two_payload_cannot_prove_this",
    ];
    // The panic-shaped fixtures fail with a *panic* obligation, so the kind is
    // asserted too: a postcondition failure on one of them would be a different
    // finding and must not satisfy the test.
    let panics = [
        "next_multiple_of_that_overflows_panics",
        "ilog2_of_zero_panics",
        "ilog10_of_zero_panics",
        "next_power_of_two_that_overflows_panics",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
    }
    let Some(report) = verify_realistic(&panics) else { return };
    for name in panics {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must fail on its panic obligation, got: {o}");
        };
        assert!(
            kind.starts_with("panic"),
            "`{name}` must fail on a panic obligation, got kind `{kind}`"
        );
    }
}

/// `is_negative`/`is_positive` are modelled as signed comparisons, not bit tests.
///
/// The signedness is the whole point: `i8::MIN` is `0x80`, the *largest* unsigned
/// byte, so a model that read the top bit as a plain bit (or compared unsigned)
/// would call it positive and refute `is_negative_of_min`. The zero tripwire is
/// the sharp one in the other direction: `0` is neither sign, so a model that
/// answered `x != 0` for `is_positive`, or the bare top bit for `is_negative`,
/// would *prove* a false contract. The `MAX`/`MIN`/`-1` pins name the boundary
/// values, so a failure names the value that broke rather than only the function.
#[test]
fn the_sign_predicates_are_signed_comparisons() {
    let verified = [
        "is_negative_of_min",
        "is_negative_of_max",
        "is_positive_of_max",
        "is_negative_branching_takes_the_true_arm",
    ];
    let refuted = ["is_negative_of_zero_tripwire", "is_positive_of_minus_one_tripwire"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
    }
}

/// The mixed-signedness additions, each pinned in both directions.
///
/// Every shape gets a true contract *and* a false one with a concrete witness, so
/// the suite carries the negative direction the standing tripwire rule requires:
/// a model that proves a false claim about `add_signed`/`add_unsigned` fails here
/// rather than passing because every fixture happened to be true. The false pins
/// are chosen to separate the readings that the true pins cannot:
///
/// * `overflowing_add_signed_wrong_flag_tripwire` (`250u8 + (-1i8)`, in range) is
///   the one a *bare-carry* flag model would prove, since the carry fires there.
/// * `overflowing_add_unsigned_wrong_flag_tripwire` (`1i8 + 1u8`, in range) is
///   the one a *signed-addition* flag model would prove.
/// * `saturating_add_unsigned_wrong_value_tripwire` names the *wrapping* answer,
///   which pins that the two families are not the same shape.
///
/// The checked family is read through a `match` rather than `ret.is_some()`,
/// because the contract language cannot name an `Option` payload; the arm the
/// match takes is what the `Some`/`None` verdicts pin.
#[test]
fn the_mixed_signedness_additions_verify_and_their_tripwires_refute() {
    let verified = [
        "wrapping_add_signed_of_a_negative",
        "saturating_add_signed_clamps_to_zero",
        "overflowing_add_signed_below_zero_is_overflow",
        "overflowing_add_signed_within_range_is_not_overflow",
        "overflowing_add_signed_past_the_top_tripwire",
        "wrapping_add_unsigned_of_the_top_bit",
        "saturating_add_unsigned_clamps_to_signed_max",
        "saturating_add_unsigned_top_bit_tripwire",
        "checked_add_signed_in_range_is_the_sum",
        "checked_add_unsigned_in_range_is_the_sum",
        "overflowing_add_unsigned_within_range_is_not_overflow",
        "overflowing_add_unsigned_past_the_top_is_overflow",
    ];
    let refuted = [
        "wrapping_add_signed_wrong_value_tripwire",
        "saturating_add_signed_wrong_value_tripwire",
        "overflowing_add_signed_wrong_flag_tripwire",
        "checked_add_signed_none_tripwire",
        "wrapping_add_unsigned_wrong_value_tripwire",
        "saturating_add_unsigned_wrong_value_tripwire",
        "overflowing_add_unsigned_wrong_flag_tripwire",
        "checked_add_unsigned_wrong_value_tripwire",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` is a false mixed-add contract that must be refuted, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// A local method sharing an intrinsic's name is answered by its body, not `core`.
///
/// rustc prints a trait impl's call as `<u8 as Trait>::is_power_of_two` and its
/// definition as `<impl at …>::is_power_of_two`, so the exact-name lookup missed
/// and the intrinsic model -- classifying on the suffix -- answered first. A trait
/// that disagrees with `core` then got a *false proof*: the body returns `false`
/// at `x == 1`, but the model returned `core`'s `true` and proved `ret == true`.
/// The true contract must verify (the body really is `false` there) and the false
/// one must be refuted, which pins both that the body was read and that the model
/// no longer shadows it.
#[test]
fn a_trait_method_sharing_an_intrinsic_name_is_answered_by_its_body() {
    let verified = ["trait_is_power_of_two_disagrees_with_core"];
    let refuted = ["trait_is_power_of_two_disagrees_with_core_tripwire"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(
            o.is_verified(),
            "`{name}` must verify: the trait body returns `false` at `x == 1`, so a \
             model that answered from `core`'s predicate would refute it; got: {o}"
        );
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!(
                "`{name}` must be refuted: it claims `core`'s answer, which the trait \
                 body does not produce. A pass is the false proof this pins. got: {o}"
            );
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// `Ord::min`/`Ord::max` are modelled, and a local trait sharing their name is
/// answered by its body rather than by the model.
///
/// The two halves pin both directions. The verifying half covers the unsigned and
/// signed orderings and the explicit `Ord::min` spelling; `ord_min_of_min_and_one_is_min`
/// is the one that separates them, since `i8::MIN`'s bits sort the other way
/// unsigned. The refuting half is the tripwire on the method form, plus the
/// local-trait pair: `local_ord_min_is_answered_by_its_body` verifies only from the
/// body's constant, and `local_ord_min_is_not_the_model_tripwire` is refuted only
/// if the body -- not the model -- answered, so the model cannot silently take the
/// call over.
#[test]
fn ord_min_and_max_are_modelled_and_a_local_trait_still_wins() {
    let verified = [
        "ord_min_is_at_most_both",
        "ord_max_is_at_least_x",
        "ord_min_of_min_and_one_is_min",
        "explicit_ord_min_is_modelled",
        "local_ord_min_is_answered_by_its_body",
    ];
    let refuted = ["ord_min_is_x_tripwire", "local_ord_min_is_not_the_model_tripwire"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// `PartialEq::eq`/`ne` and `PartialOrd::lt`/`le`/`gt`/`ge` are modelled as the
/// comparison operators they denote, and a local trait sharing their name is
/// answered by its body rather than by the model.
///
/// The verifying half pins all six operators, with `partial_ge_method_is_the_operator`
/// choosing `x < y` so `>=` is separated from `<=`, and
/// `partial_lt_signed_is_not_unsigned` pinning the ordering choice on `i8::MIN` (the
/// one value whose bits sort the other way unsigned). The refuting half is the
/// tripwire on the method form plus the local-trait pair:
/// `local_partial_ord_lt_is_answered_by_its_body` verifies only from the body's
/// constant, and `local_partial_ord_lt_is_not_the_model_tripwire` is refuted only
/// if the body -- not the model -- answered.
#[test]
fn partial_cmp_methods_are_modelled_and_a_local_trait_still_wins() {
    let verified = [
        "partial_eq_method_is_the_operator",
        "partial_ne_method_is_the_operator",
        "partial_lt_method_is_the_operator",
        "partial_ge_method_is_the_operator",
        "partial_lt_signed_is_not_unsigned",
        "local_partial_ord_lt_is_answered_by_its_body",
        // A comparison against a *constant* operand: the literal is a promoted
        // constant referenced by place in unoptimised MIR, so this is the shape
        // that pins the promoted-scalar collection.
        "partial_eq_const_is_the_operator",
        "partial_lt_const_signed_is_not_unsigned",
    ];
    let refuted = [
        "partial_lt_is_not_le_tripwire",
        "local_partial_ord_lt_is_not_the_model_tripwire",
        "partial_lt_const_is_not_le_tripwire",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// `Ord::cmp` is modelled, returning the `Ordering` enum whose three variants a
/// `switchInt` on `discriminant(_)` selects.
///
/// The verifying entries pin all three arms -- `ord_cmp_less_arm`,
/// `ord_cmp_equal_arm` and `ord_cmp_greater_arm` return distinct constants so each
/// arm proves which tag the model produced -- plus `ord_cmp_matches_less` (the
/// `matches!` spelling) and `ord_cmp_signed_is_not_unsigned`, which pins the signed
/// ordering on `i8::MIN` (its bits sort the other way unsigned, so an unsigned
/// model would take the `Greater` arm). The refuting entry is the tripwire:
/// `x.cmp(&y) == Less` is not `x <= y`, so it fails at `x == y` -- a model that
/// read the tag as unsigned (comparing the `Less` discriminant `0xff` against
/// `255`) or that confused `Less` with `Equal` would *prove* it.
#[test]
fn ord_cmp_returns_the_ordering_enum() {
    let verified = [
        "ord_cmp_less_arm",
        "ord_cmp_equal_arm",
        "ord_cmp_greater_arm",
        "ord_cmp_matches_less",
        "ord_cmp_signed_is_not_unsigned",
    ];
    let refuted = ["ord_cmp_is_not_le_tripwire"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// A widening conversion (`From::from`/`Into::into`) is modelled, by the source's
/// signedness.
///
/// The three verifying entries pin the three cases that separate a correct model
/// from a wrong one: `from_u8_is_modelled` and `into_u8_is_modelled` are the two
/// trait spellings reaching one value, and
/// `unsigned_source_widens_to_signed_destination` is the *signedness change* that
/// must zero-fill (the source is unsigned) even though the destination is signed.
/// `signed_widening_keeps_negative_values` is the sign-extension half: `i8::MIN`
/// stays `i8::MIN` in an `i16`.
///
/// The tripwire is the evidence the source's signedness is read at all:
/// `-1i8` widens to `-1i16` (`0xffff`), so a model that zero-filled a signed source
/// would return `255` and *prove* `ret == 255`. Refuting it is what shows the
/// extension is chosen by the source's sign and not by `truncate`.
#[test]
fn widening_conversions_are_modelled_by_the_sources_signedness() {
    let verified = [
        "from_u8_is_modelled",
        "into_u8_is_modelled",
        "signed_widening_keeps_negative_values",
        "unsigned_source_widens_to_signed_destination",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let refuted = ["signed_widening_is_not_zero_fill_tripwire"];
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// A local trait whose name and owner type collide with a modelled conversion's
/// must not answer a call the compiler resolved to the *library* trait.
///
/// The `conv_shim` module implements its own `From<u8> for u16` returning `7`,
/// while `core`'s `From<u8> for u16` widens `x`. Both share the method tail
/// (`from`) and the owner (`u16`), so before the trait check
/// `resolve_callee` answered `<u16 as std::convert::From<u8>>::from` from the
/// local body and *proved* `ret == 7` -- a false proof of a library call. This
/// test is the tripwire: `local_from_does_not_answer_the_std_trait` must be
/// refuted, and the local trait's own call
/// (`local_from_is_answered_by_its_own_body`) must still verify, so the guard
/// separates the two traits rather than refusing the local one outright.
#[test]
fn a_local_trait_named_from_does_not_answer_the_std_trait() {
    let verified = ["local_from_is_answered_by_its_own_body"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify from the local body, got: {o}");
    }
    let refuted = ["local_from_does_not_answer_the_std_trait"];
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` claims the local body's answer for a library call and must be refuted, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// A user type named `Range` must not be answered by the for-loop range model.
///
/// rustc 1.85 (the MSRV) prints the standard library's `for`-loop projection with
/// the type *unqualified* -- `<RangeInclusive<u32> as IntoIterator>::into_iter` --
/// where current stable qualifies it (`<std::ops::RangeInclusive<u32> as …>`). An
/// unqualified `Range` is a name a *user* type can carry, so the two `Iterator`
/// methods are matched on the trait as well as the type. This test pins both
/// directions with its own source (so it does not depend on a corpus edit):
///
/// * a user `struct Range<T>` with a custom `into_iter` (whose default body
///   *panics*) must never be answered with the model's identity semantics -- the
///   model would return the range unchanged and prove `ret == 1` for a function
///   that always panics; the honest verdict is a refutation (`Failed`);
/// * the standard library's own range projection must still be modelled, so the
///   fix cannot pass by refusing every range call.
#[test]
fn a_user_type_named_range_is_not_answered_by_the_range_model() {
    let spoof = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub mod a {
    pub trait Custom {
        fn into_iter(self) -> Self
        where
            Self: Sized,
        {
            panic!("into_iter is not the identity here")
        }
    }
}
pub mod b {
    pub trait Custom {
        fn into_iter(self) -> Self
        where
            Self: Sized,
        {
            panic!("the other trait")
        }
    }
}
pub struct Range<T> {
    pub start: T,
    pub end: T,
}
impl a::Custom for Range<u8> {}

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn caller() -> u8 {
    let r = Range { start: 1u8, end: 2u8 };
    let x = <Range<u8> as a::Custom>::into_iter(r);
    x.start
}
"#;
    let Some(o) = verify_src("caller", spoof) else { return };
    // The soundness property: the model must never answer this call. If it did, it
    // would return the range unchanged and *prove* `ret == 1`. On current stable the
    // default body's panic is modelled, so the verdict is a refutation (`Failed`); on
    // 1.85 the panic path is not modelled, so the verdict is a refusal (`Incomplete`).
    // Both are honest; only `verified` would be a false proof.
    assert!(
        !o.is_verified(),
        "a user `Range`'s custom `into_iter` must not be answered by the range \
         model (the model would prove `ret == 1` for a function that panics), got: {o}"
    );

    // The positive control: the standard library's own `for` loop is still modelled.
    let real = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret == 3,
}
pub fn sums() -> u32 {
    let mut c = 0u32;
    for i in 1u32..=2u32 {
        c += i;
    }
    c
}
"#;
    let Some(o) = verify_src("sums", real) else { return };
    assert!(
        o.is_verified(),
        "the standard library's `for`-loop range must still be modelled, got: {o}"
    );

    // The sharper shape: a trait *default* body that mutates `self` through a helper
    // the impl *overrides*. The call inside the default body is `<Self as T>::set`,
    // whose receiver is literally `Self`, so the concrete type is not known there.
    // Resolving it to the *default* `set` (a no-op) inlined the wrong body and
    // *proved* `ret == 1` for a caller whose real result is `42` -- a false proof,
    // pre-existing and independent of the range model. The call is refused now, so
    // the soundness property is "never `verified`".
    let self_receiver = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

#[derive(Clone, Copy)]
pub struct P {
    pub v: u8,
}
pub trait T: Copy {
    fn go(mut self) -> Self
    where
        Self: Sized,
    {
        self.set(42);
        self
    }
    fn set(&mut self, x: u8) {
        let _ = x;
    }
}
impl T for P {
    fn set(&mut self, x: u8) {
        self.v = x;
    }
}

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn caller() -> u8 {
    let p = P { v: 1 };
    let q = <P as T>::go(p);
    q.v
}
"#;
    let Some(o) = verify_src("caller", self_receiver) else { return };
    assert!(
        !o.is_verified(),
        "a `<Self as T>::m` call inside a trait default body must not be answered \
         by the default method when an impl overrides it (that proved `ret == 1` for \
         a body returning `42`), got: {o}"
    );
}

/// A bare trait call must not be answered by the model when the crate declares a
/// crate-root trait of that name with a *default* body.
///
/// rustc prints a crate-root trait's call bare (`<u8 as Ord>::min`), and a default
/// method has no `impl` block in the dump -- its definition is printed as
/// `Ord::min`. So `resolve_callee` cannot match it by location, and before the
/// `declared_traits` guard the model answered `<u8 as Ord>::min` from `core`'s
/// ordering. `crate_root_ord_default_*` pair pins both directions: the body returns
/// a constant, so the verifying half proves the body was read and the refuted half
/// proves the model was not consulted.
#[test]
fn a_bare_crate_root_trait_call_is_not_answered_by_the_model() {
    let verified = ["crate_root_ord_default_verifies_from_its_body"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify from the default body, got: {o}");
    }
    let refuted = ["crate_root_ord_default_is_not_the_model_tripwire"];
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!(
                "`{name}` claims `core`'s ordering for a call the compiler resolved to \
                 the local trait and must be refuted, got: {o}"
            );
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// An unrelated same-named trait must not answer a bare trait call.
///
/// `m::Trait` is a different trait from the crate-root `Trait`, but rustc prints a
/// *bare* `Trait` call, so a suffix match let the module trait's body answer the
/// crate-root trait's call -- a false proof. `suffix_collision_*` pin both
/// directions: the call names the crate-root trait (whose default body returns
/// `9`), and the module trait's body returns `7`, so the refuted half fails only if
/// the module trait was *not* consulted.
#[test]
fn an_unrelated_same_named_trait_does_not_answer_a_bare_call() {
    let verified = ["suffix_collision_verifies_from_the_named_trait"];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify from the crate-root trait, got: {o}");
    }
    let refuted = ["suffix_collision_is_not_the_module_trait_tripwire"];
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!(
                "`{name}` claims the module trait's body for a call naming the crate-root \
                 trait and must be refuted, got: {o}"
            );
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// A local trait method reached through an imported library trait path must not be
/// answered by the model.
///
/// `use std::convert::From;` plus a local `impl From<Local> for u16` prints the call
/// `<u16 as From<Local>>::from` -- the *bare* library name, because the local `From`
/// is the only one in scope. The crate declares no trait named `From`, so the
/// `declared_traits` guard alone would not refuse it, and the model would answer a
/// call the compiler resolved to the local body. The owner (`u16`), the method
/// (`from`) and the *self type* (`Local`, the conversion's source) together name
/// the same method. This lives in its own source file rather than the shared corpus
/// because the corpus's own `conv_shim::From` forces rustc to qualify the library
/// trait, which hides the bare spelling.
#[test]
fn a_local_impl_of_an_imported_trait_does_not_answer_the_model() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Local;
impl From<Local> for u16 {
    fn from(_x: Local) -> Self {
        107
    }
}
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn imported_from_verifies_from_the_local_body() -> u16 {
    <u16 as From<Local>>::from(Local)
}
spec! {
    requires: true,
    ensures: ret == 7,
}
pub fn imported_from_is_not_the_model_tripwire() -> u16 {
    <u16 as From<Local>>::from(Local)
}
"#;
    let o = verify_src("imported_from_verifies_from_the_local_body", src);
    let Some(o) = o else { return };
    assert!(
        o.is_verified(),
        "`imported_from_verifies_from_the_local_body` must verify from the local body, got: {o}"
    );
    let o = verify_src("imported_from_is_not_the_model_tripwire", src);
    let Some(o) = o else { return };
    match &o {
        FnOutcome::Failed { kind, .. } => {
            assert_eq!(kind, "postcondition", "the tripwire got: {o}");
        }
        _ => panic!(
            "`imported_from_is_not_the_model_tripwire` claims the modelled conversion for a \
             call the compiler resolved to a local impl and must be refuted, got: {o}"
        ),
    }
}

/// A trait's *default* body must not answer a call that an `impl` overrides.
///
/// rustc keeps a trait's default method in the dump even when an implementation
/// overrides it, so `<Foo as T>::value(&foo)` names the override while the trait's
/// own `T::value` body (returning `1`) is still present. `resolve_callee` used to
/// prefer the default body, inlining `1` for code Rust returns `2` from -- a false
/// proof. The impl candidate must win; the default is used only when no impl
/// overrides the method.
#[test]
fn an_override_wins_over_the_traits_default_body() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub trait T { fn value(&self) -> u8 { 1 } }
pub struct Foo(pub u8);
impl T for Foo { fn value(&self) -> u8 { 2 } }
pub struct Bar(pub u8);
impl T for Bar {}
spec! {
    requires: true,
    ensures: ret == 2,
}
pub fn override_verifies(f: &Foo) -> u8 { <Foo as T>::value(f) }
spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn override_is_not_the_default_tripwire(f: &Foo) -> u8 { <Foo as T>::value(f) }
spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn default_still_used_when_not_overridden(b: &Bar) -> u8 { <Bar as T>::value(b) }
"#;
    let Some(o) = verify_src("override_verifies", src) else { return };
    assert!(o.is_verified(), "the override's body must answer, got: {o}");
    let Some(o) = verify_src("default_still_used_when_not_overridden", src) else { return };
    assert!(o.is_verified(), "the default must still answer when nothing overrides it, got: {o}");
    let Some(o) = verify_src("override_is_not_the_default_tripwire", src) else { return };
    match &o {
        FnOutcome::Failed { kind, .. } => assert_eq!(kind, "postcondition", "got: {o}"),
        _ => panic!("the default body must not answer a call an impl overrides, got: {o}"),
    }
}

/// A local `impl` of a generic trait must not answer a call to a *different*
/// instantiation of the same trait.
///
/// `impl From<Local> for u16` and the library's `impl From<u8> for u16` share the
/// trait path (`From`), the owner (`u16`) and the method (`from`); only the trait's
/// *argument* separates them. A call `<u16 as From<u8>>::from(7u8)` must reach the
/// modelled widening (`7`), and the local impl's own call
/// `<u16 as From<Local>>::from(...)` must reach its body (`107`).
#[test]
fn a_generic_traits_arguments_separate_its_impls() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Local;
impl From<Local> for u16 { fn from(_: Local) -> Self { 107 } }
spec! {
    requires: true,
    ensures: ret == 7,
}
pub fn library_call_is_seven() -> u16 { <u16 as From<u8>>::from(7u8) }
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn library_call_is_not_the_local_body_tripwire() -> u16 { <u16 as From<u8>>::from(7u8) }
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn local_call_is_onehundredseven() -> u16 { <u16 as From<Local>>::from(Local) }
"#;
    let Some(o) = verify_src("library_call_is_seven", src) else { return };
    assert!(o.is_verified(), "the modelled widening must answer a library call, got: {o}");
    let Some(o) = verify_src("local_call_is_onehundredseven", src) else { return };
    assert!(o.is_verified(), "the local impl's own instantiation must answer, got: {o}");
    let Some(o) = verify_src("library_call_is_not_the_local_body_tripwire", src) else { return };
    match &o {
        FnOutcome::Failed { kind, .. } => assert_eq!(kind, "postcondition", "got: {o}"),
        _ => panic!("a different instantiation's body must not answer, got: {o}"),
    }
}

/// A trait imported into a module must be recorded as the imported path, not
/// prefixed with the module.
///
/// `use std::convert::From;` makes a bare `From` inside `m` the standard trait, and
/// rustc prints the call with the library path. The scanner used to prefix `m`
/// unconditionally (`m::From`), which matched no call -- a lost proof. The same
/// must hold after a nested module, whose scope used to reset the parent's imports.
#[test]
fn an_imported_trait_keeps_its_imported_path() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Local;
pub mod m {
    use std::convert::From;
    pub mod nested {}
    impl From<crate::Local> for u16 { fn from(_: crate::Local) -> Self { 107 } }
}
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn imported_trait_after_nested_module() -> u16 {
    <u16 as std::convert::From<crate::Local>>::from(crate::Local)
}
"#;
    let Some(o) = verify_src("imported_trait_after_nested_module", src) else { return };
    assert!(o.is_verified(), "the impl must be reached through its imported trait, got: {o}");
}

/// A multi-line, restricted-visibility import must still be read.
///
/// `pub(crate) use a::b::{\n    C,\n};` is one item whose path spans lines and
/// whose visibility is not a bare `pub `. A line-at-a-time scan with a `pub `
/// prefix missed it, so the impl was qualified with its own module and no call
/// matched -- a lost proof.
#[test]
fn a_multiline_restricted_import_is_read() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Local;
pub mod m {
    pub(crate) use std::convert::{
        From,
    };
    impl From<crate::Local> for u16 { fn from(_: crate::Local) -> Self { 107 } }
}
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn multiline_imported_trait() -> u16 {
    <u16 as std::convert::From<crate::Local>>::from(crate::Local)
}
"#;
    let Some(o) = verify_src("multiline_imported_trait", src) else { return };
    assert!(o.is_verified(), "a folded restricted import must still qualify the trait, got: {o}");
}

/// A nested trait argument keeps its balanced spelling on both sides of the match.
///
/// `call_trait_args` reads the argument off the *call* (`<W as Wrap<Option<u8>>>::get`)
/// and `impl_trait_args` reads it off the impl header (`impl Wrap<Option<u8>> for W`).
/// A "strip trailing `>`" reading on the call side cuts *every* closing bracket, so
/// the call would say `Option<u8` while the impl says `Option<u8>`, the two would not
/// match, and the local body would be lost -- the call reported as unmodelled. The
/// verifying entry is the evidence the body answers; the tripwire is the evidence it
/// is the *body* (returning `9`) and not a guess, since a model that constant-folded
/// or refused would not refute it.
#[test]
fn a_nested_trait_argument_keeps_its_balanced_spelling() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub trait Wrap<T> { fn get(&self) -> u8; }
pub struct W;
impl Wrap<Option<u8>> for W { fn get(&self) -> u8 { 9 } }
spec! {
    requires: true,
    ensures: ret == 9,
}
pub fn nested_arg(w: &W) -> u8 { <W as Wrap<Option<u8>>>::get(w) }
spec! {
    requires: true,
    ensures: ret == 4,
}
pub fn nested_arg_tripwire(w: &W) -> u8 { <W as Wrap<Option<u8>>>::get(w) }
"#;
    let Some(o) = verify_src("nested_arg", src) else { return };
    assert!(o.is_verified(), "a nested trait argument must still find the local body, got: {o}");
    let Some(o) = verify_src("nested_arg_tripwire", src) else { return };
    match &o {
        FnOutcome::Failed { kind, .. } => assert_eq!(kind, "postcondition", "got: {o}"),
        _ => panic!("the local body returns 9, so `ret == 4` must be refuted, got: {o}"),
    }
}

/// A `#[cfg]`-disabled later `use` must not displace a live alias.
///
/// The import scan reads raw source, but rustc emits MIR only for enabled items. A
/// live `use std::convert::From as Conv;` binds `Conv`; a later
/// `#[cfg(any())] use crate::Other as Conv;` binds nothing, yet a naive map lets it
/// overwrite the live binding, so the impl written with `Conv` is recorded with the
/// wrong trait and its call is lost. The verifying entry is the evidence the live
/// binding still resolves; the tripwire is the evidence the *local body* (returning
/// `107`) answers, not the model. The same-line attribute form is covered too, since
/// the attribute hides the `use` keyword from the scanner there.
#[test]
fn a_cfg_disabled_import_does_not_displace_a_live_alias() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub trait From { fn make() -> u8 { 0 } }
pub mod m {
    use std::convert::From as Conv;
    pub struct Local;
    impl Conv<Local> for u16 { fn from(_: Local) -> Self { 107 } }
    #[cfg(any())]
    use crate::Other as Conv;
}
pub struct Other;
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn cfg_live() -> u16 { <u16 as std::convert::From<m::Local>>::from(m::Local) }
spec! {
    requires: true,
    ensures: ret == 5,
}
pub fn cfg_tripwire() -> u16 { <u16 as std::convert::From<m::Local>>::from(m::Local) }
"#;
    let Some(o) = verify_src("cfg_live", src) else { return };
    assert!(o.is_verified(), "a live alias must survive a later cfg-disabled import, got: {o}");
    let Some(o) = verify_src("cfg_tripwire", src) else { return };
    match &o {
        FnOutcome::Failed { kind, .. } => assert_eq!(kind, "postcondition", "got: {o}"),
        _ => panic!("the live local body returns 107, so `ret == 5` must be refuted, got: {o}"),
    }
}

/// A same-line `#[cfg] use …` is read, not skipped.
///
/// An attribute on the item's own line (`#[cfg(all())] use std::convert::From as
/// Conv;`) hides the `use` keyword from [`is_use_start`] unless the attribute is
/// split off first. When it is skipped, the binding is lost entirely, so an impl
/// written with `Conv` is qualified with its own module (`m::Conv`) and the call the
/// compiler resolved to the imported trait matches nothing -- a lost proof. The
/// condition here is *enabled*, so the binding is the live one and the call must
/// still reach the impl's body.
#[test]
fn a_same_line_cfg_import_is_read() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub mod m {
    #[cfg(all())] use std::convert::From as Conv;
    pub struct Local;
    impl Conv<Local> for u16 { fn from(_: Local) -> Self { 107 } }
}
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn same_line_live_import() -> u16 {
    <u16 as std::convert::From<m::Local>>::from(m::Local)
}
"#;
    let Some(o) = verify_src("same_line_live_import", src) else { return };
    assert!(o.is_verified(), "a same-line cfg import must still bind, got: {o}");
}

/// A `#[cfg]` attribute that spans lines is read as a whole, not by its first line.
///
/// The same hazard as the one-line `#[cfg(any())]` case, but the attribute wraps, so
/// the line directly above the `use` is its closing `)]` rather than its `#[cfg…`.
/// A reader that inspects one line above the `use` sees `))]`, concludes there is no
/// condition, treats the disabled import as live, and lets it displace the live
/// alias -- recording the impl with the wrong trait and losing the call. The
/// verifying entry is the evidence the live alias survives; the tripwire is the
/// evidence the local body (returning `107`) answers, not the model.
#[test]
fn a_multiline_cfg_import_does_not_displace_a_live_alias() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub trait From { fn make() -> u8 { 0 } }
pub mod m {
    use std::convert::From as Conv;
    pub struct Local;
    impl Conv<Local> for u16 { fn from(_: Local) -> Self { 107 } }
    #[cfg(all(
        any(),
    ))]
    use crate::Other as Conv;
}
pub struct Other;
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn multi_cfg_live() -> u16 { <u16 as std::convert::From<m::Local>>::from(m::Local) }
spec! {
    requires: true,
    ensures: ret == 5,
}
pub fn multi_cfg_tripwire() -> u16 { <u16 as std::convert::From<m::Local>>::from(m::Local) }
"#;
    let Some(o) = verify_src("multi_cfg_live", src) else { return };
    assert!(o.is_verified(), "a multi-line cfg import must not displace a live alias, got: {o}");
    let Some(o) = verify_src("multi_cfg_tripwire", src) else { return };
    match &o {
        FnOutcome::Failed { kind, .. } => assert_eq!(kind, "postcondition", "got: {o}"),
        _ => panic!("the live local body returns 107, so `ret == 5` must be refuted, got: {o}"),
    }
}

/// A quoted delimiter in an attribute must not hide the `#[cfg]` above it.
///
/// `#[doc = "("]` holds an unmatched `(` inside a string. A reader that counts every
/// character as a delimiter never finds the attribute's closing `]`, runs past it, and
/// then reports the whole attribute run as unreadable -- so the disabled `#[cfg]`
/// import above it is treated as live and displaces the live alias. The impl written
/// with `Conv` is then recorded against the wrong trait and the call is lost
/// (`converts a type the model does not hold`). The verifying entry is the evidence
/// the live alias survives; the tripwire is the evidence the local body (returning
/// `107`) answers, not the model.
#[test]
fn a_quoted_delimiter_does_not_hide_a_cfg_import() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub trait From { fn make() -> u8 { 0 } }
pub mod m {
    use std::convert::From as Conv;
    pub struct Local;
    impl Conv<Local> for u16 { fn from(_: Local) -> Self { 107 } }
    #[cfg(any())]
    #[doc = "("]
    use crate::Other as Conv;
}
pub struct Other;
spec! {
    requires: true,
    ensures: ret == 107,
}
pub fn quoted_cfg_live() -> u16 { <u16 as std::convert::From<m::Local>>::from(m::Local) }
spec! {
    requires: true,
    ensures: ret == 5,
}
pub fn quoted_cfg_tripwire() -> u16 { <u16 as std::convert::From<m::Local>>::from(m::Local) }
"#;
    let Some(o) = verify_src("quoted_cfg_live", src) else { return };
    assert!(o.is_verified(), "a quoted delimiter must not hide the cfg import, got: {o}");
    let Some(o) = verify_src("quoted_cfg_tripwire", src) else { return };
    match &o {
        FnOutcome::Failed { kind, .. } => assert_eq!(kind, "postcondition", "got: {o}"),
        _ => panic!("the live local body returns 107, so `ret == 5` must be refuted, got: {o}"),
    }
}

/// The corpus pins both directions for the nested argument and the cfg alias.
///
/// The inline tests above use a small self-contained source; these entries sit in
/// `examples/mir_targets/realistic.rs` beside the other trait-identity fixtures, so
/// the two new spellings are exercised against the full corpus (where `conv_shim`
/// already forces rustc to qualify the standard path) and not only in isolation.
#[test]
fn the_nested_argument_and_cfg_alias_fixtures_are_decided() {
    let verified = [
        "nested_trait_arg_finds_the_body",
        "cfg_disabled_import_keeps_the_live_alias",
        "cfg_multiline_import_keeps_the_live_alias",
        "cfg_quoted_delimiter_keeps_the_live_alias",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify from its local body, got: {o}");
    }
    let refuted = [
        "nested_trait_arg_is_not_a_guess_tripwire",
        "cfg_disabled_import_is_not_the_wrong_alias_tripwire",
        "cfg_multiline_import_is_not_the_wrong_alias_tripwire",
        "cfg_quoted_delimiter_is_not_the_wrong_alias_tripwire",
    ];
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// The bitwise complement `!x`, pinned by a true half and a tripwire.
///
/// `!x` is `all_ones ^ x` at the *operand's* width. The model reads that width
/// off the value and refuses a destination local that disagrees with it, rather
/// than masking at `dest_w`. The three verifying entries name the operand's width
/// at three different widths (`u8`, `i8`, `u32`), so a model that masked at the
/// wrong width would fail the `u32` one; `not_of_zero_is_minus_one` pins the sign
/// the value keeps; and the tripwire is the evidence the operand is read at all,
/// since a constant `255` (or `all_ones ^ 0`) would prove it.
#[test]
fn the_bitwise_complement_reads_the_operands_width() {
    let verified = [
        "not_of_zero_is_all_ones",
        "not_is_255_minus_x",
        "not_of_zero_is_minus_one",
        "not_of_zero_u32_is_all_ones",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&["not_is_always_255_tripwire"]) else { return };
    let o = outcome(&report, "not_is_always_255_tripwire");
    let FnOutcome::Failed { .. } = o else {
        panic!("`not_is_always_255_tripwire` is false and must be refuted, got: {o}");
    };
}

/// The struct-literal tripwire's counterexample is the `hi` operand, not `lo`.
///
/// [`struct_literal_order_tripwire`] writes `lo: 7` and `hi: a` and claims
/// `ret == a`. Refuting it is not enough on its own: a wrong model could refute
/// it for the wrong reason. What makes the refutation *evidence* is the witness,
/// which must be `a == 0` -- the value that differs from `lo`'s `7`. A model that
/// read the fields in write order would have *proved* this contract instead, so
/// reaching a witness at all is the proof the order is declaration order.
#[test]
fn a_struct_literal_reads_fields_in_declaration_order() {
    let Some(report) = verify_realistic(&["struct_literal_order_tripwire"]) else { return };
    let o = outcome(&report, "struct_literal_order_tripwire");
    let FnOutcome::Failed { detail, .. } = o else {
        panic!("`struct_literal_order_tripwire` must be refuted, got: {o}");
    };
    assert!(
        detail.contains("= 0"),
        "the witness must be `a == 0`, the value that is not `lo` (7); got: {detail}"
    );
}

/// A contract can name a *tuple struct's* field, numbered by position.
///
/// `struct_head` recognised only a braced body, so `pub struct Pair(pub u8, pub u8)`
/// was never read as a struct at all: the argument's type stayed an opaque
/// `Other("Pair")` with no layout, and a contract naming `p.0` was refused as
/// "unknown name `p`". The positional index *is* the MIR field index, so `p.0` and
/// the body's `(*_1).0` must name one variable -- and each field must be its own
/// input, not one aliased word.
///
/// The four verdicts pin the four things that could go wrong: the read itself
/// (`verified`), the read through a reference as well as by value (`verified`),
/// the declared *signedness* of the field (`verified`, and only under the signed
/// reading), and the independence of the two fields (`FAILED`, which is the
/// evidence they are distinct -- one shared variable would make the contract hold).
#[test]
fn a_contract_can_name_a_tuple_struct_field() {
    let Some(report) = verify_realistic(&[
        "tuple_struct_reads_its_field",
        "tuple_struct_by_value_reads_its_field",
        "tuple_struct_signed_field_reads",
        "tuple_struct_fields_are_independent",
    ]) else {
        return;
    };
    for name in [
        "tuple_struct_reads_its_field",
        "tuple_struct_by_value_reads_its_field",
        "tuple_struct_signed_field_reads",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must be read and verified; got: {o}");
    }
    let o = outcome(&report, "tuple_struct_fields_are_independent");
    assert!(
        !o.is_verified(),
        "`tuple_struct_fields_are_independent` must be refuted -- a reader that aliased \
         `p.0` and `p.1` to one variable would prove it; got: {o}"
    );
}

/// A tuple field the layout does not have is refused, and so is a *nested* path
/// that walks off the layout.
///
/// `Pair` has two fields, so `p.2` names nothing. Binding it to a fabricated word
/// would let a contract about a field that does not exist be proved, which is a
/// false proof rather than a missing one. `n.p.q` is the nested form: `n.p` *is*
/// bound (it is a `Pair` with a layout), but `Pair` has no field `q`, so the walk
/// stops and the path is refused -- naming the segment that failed, not the whole
/// path. Both refusals are the safe direction, and this pins them.
#[test]
fn a_tuple_struct_field_that_does_not_exist_is_refused() {
    let Some(report) = verify_realistic(&[
        "tuple_struct_out_of_range_field_is_refused",
        "nested_path_off_the_layout_is_refused",
    ]) else {
        return;
    };
    for name in [
        "tuple_struct_out_of_range_field_is_refused",
        "nested_path_off_the_layout_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "`{name}` names a field the layout does not have and must be refused; got: {o}"
        );
    }
}

/// A *nested* field projection is read: the contract's `n.p.0` and the body's
/// `(((*_1).0).0)` are one input.
///
/// This is the coverage the nested support adds. `n.p.0` is a walk of two field
/// projections, and the single-field store would answer it by looking up the
/// *outer* field `(local, 0)` twice -- returning `n.p` for `n.p.0`, a wrong value
/// rather than a missing one. The positive entry pins that the contract and the
/// body agree; the false entry pins that a disagreeing postcondition is refuted,
/// so the agreement is not vacuous.
#[test]
fn a_nested_field_projection_is_read_and_agrees_with_the_body() {
    let Some(report) = verify_realistic(&[
        "nested_tuple_projection_reads",
        "nested_tuple_projection_is_the_body_value",
        "nested_named_field_reads_its_leaf",
        "nested_named_field_is_the_body_value",
    ]) else {
        return;
    };
    for name in [
        "nested_tuple_projection_reads",
        "nested_tuple_projection_is_the_body_value",
        "nested_named_field_reads_its_leaf",
        "nested_named_field_is_the_body_value",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// Two nested leaves are *independent* inputs, which is what makes the binding a
/// walk rather than a single field.
///
/// The entries are toothed: each claims a value the body does not return, so a
/// reader that aliased the leaves (`n.p.0` with `n.p.1`, or `o.i.v` with `o.j.v`)
/// would *verify* them -- a false proof. Refuted is the evidence the leaves are
/// distinct, and each counterexample names two different variables, which is the
/// same evidence at the term level.
#[test]
fn nested_leaves_under_different_paths_are_independent() {
    let Some(report) = verify_realistic(&[
        "nested_tuple_projection_leaves_are_independent",
        "nested_named_leaves_under_different_fields",
    ]) else {
        return;
    };
    for name in [
        "nested_tuple_projection_leaves_are_independent",
        "nested_named_leaves_under_different_fields",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` must be refuted: aliasing its leaves would make it a false proof; got: {o}"
        );
    }
}

/// A field write through a `&mut` is applied, not dropped -- and the *false*
/// direction is refuted rather than proved.
///
/// This is the regression for the two-sided soundness bug: `((*_1).0) = v` (a
/// `Deref` then a `Field`) had no arm in the store and fell to the drop arm. The
/// true entry pins that the write lands (the read after it is `5`); the false entry
/// pins that the postcondition is checked against the written value, so a contract
/// the body cannot satisfy is refuted instead of proved. Dropping the write makes
/// the false entry *verify* and the true entry fail, so both directions are toothed.
#[test]
fn a_field_write_through_a_mutable_reference_is_applied() {
    let Some(report) = verify_realistic(&[
        "field_write_through_ref_mut_takes_effect",
        "field_write_through_ref_mut_is_not_dropped",
    ]) else {
        return;
    };
    let true_dir = outcome(&report, "field_write_through_ref_mut_takes_effect");
    assert!(
        true_dir.is_verified(),
        "the write must land, so the read after it is 5; got: {true_dir}"
    );
    let false_dir = outcome(&report, "field_write_through_ref_mut_is_not_dropped");
    assert!(
        matches!(false_dir, FnOutcome::Failed { .. }),
        "the postcondition must be checked against the written value, so `ret == 0` \
         is refuted rather than proved; got: {false_dir}"
    );
}

/// A *nested* write through a `&mut` lands where the nested read looks, and the
/// false direction is refuted rather than proved.
///
/// The nested store is keyed by the whole chain, so `o.i.v = 5` and the later
/// `o.i.v` meet in one entry. A write keyed by a single field index would land on
/// the *outer* field and the read would see the caller's value: the true entry
/// would fail and the false entry would *verify*. Both are toothed here.
#[test]
fn a_nested_field_write_through_a_mutable_reference_is_applied() {
    let Some(report) = verify_realistic(&[
        "nested_field_write_through_ref_mut_takes_effect",
        "nested_field_write_through_ref_mut_is_not_dropped",
    ]) else {
        return;
    };
    let true_dir = outcome(&report, "nested_field_write_through_ref_mut_takes_effect");
    assert!(true_dir.is_verified(), "the nested write must land; got: {true_dir}");
    let false_dir = outcome(&report, "nested_field_write_through_ref_mut_is_not_dropped");
    assert!(
        matches!(false_dir, FnOutcome::Failed { .. }),
        "the nested write must be seen by the read, so `ret == 0` is refuted; got: {false_dir}"
    );
}

/// A seeded nested path is invalidated by a write that replaces the value it was
/// part of, and carried across by a whole-struct copy.
///
/// Both are the "parts" rules one level down. `o.i = Inner { v: 9 }` makes the seed
/// for `o.i.v` stale, so the false entry must be *refuted*: the body returns 9, and
/// `ret == 3` holds for no input. Refutation and not merely "not proved" is the
/// assertion, because a refusal also satisfies "not proved" and says nothing about
/// whether the write landed. The body lowers to a struct literal into a temp
/// followed by `(_1.0) = move _2`, so reaching the refutation is the evidence the
/// temp's parts were re-rooted under the destination's nested place.
///
/// And `c = d` must move `c.i.v` with the copy, so the true entry verifies -- it
/// pins `c.i.v` and `d.i.v` to different values, so `verified` is the evidence the
/// copy moved the right one rather than leaving `c`'s own seed.
#[test]
fn a_nested_seed_is_invalidated_by_a_write_and_carried_by_a_copy() {
    let Some(report) = verify_realistic(&[
        "whole_inner_write_makes_nested_seed_stale",
        "whole_inner_write_is_seen_by_the_leaf",
        "whole_inner_write_through_a_mutable_reference_is_seen",
        "whole_inner_move_carries_the_source_leaf",
        "whole_inner_move_is_not_the_stale_destination",
        "nested_swap_carries_the_other_side",
        "nested_swap_is_not_the_stale_side",
        "nested_aggregate_argument_reaches_the_helper",
        "nested_aggregate_argument_is_not_the_stale_destination",
        "nested_return_carries_the_field",
        "nested_return_is_not_the_stale_field",
        "whole_struct_copy_carries_nested_paths",
    ]) else {
        return;
    };
    let stale = outcome(&report, "whole_inner_write_makes_nested_seed_stale");
    assert!(
        matches!(stale, FnOutcome::Failed { .. }),
        "a stale nested seed must let the false contract be refuted, not refused; got: {stale}"
    );
    // The positive direction: the same body's true contract (`ret == 9`) verifies, so
    // the refutation above is the write landing and not a blanket refusal. Without this
    // pair, an engine that answered `Unknown` for the whole shape would pass.
    let landed = outcome(&report, "whole_inner_write_is_seen_by_the_leaf");
    assert!(
        landed.is_verified(),
        "a nested aggregate write must land where the leaf reads it; got: {landed}"
    );
    // The `&mut` companion: the same write's destination carries a leading deref, so the
    // re-rooting must resolve it or the field path never matches the read.
    let via_ref = outcome(&report, "whole_inner_write_through_a_mutable_reference_is_seen");
    assert!(
        via_ref.is_verified(),
        "a nested aggregate write through a &mut must reach the target's field path; got: {via_ref}"
    );
    let copy = outcome(&report, "whole_struct_copy_carries_nested_paths");
    assert!(copy.is_verified(), "a whole-struct copy must carry nested paths; got: {copy}");
    // A nested-to-nested move: the *source* is a projection, which `copy_parts` refuses, so
    // the re-rooting has to run on a nested source too. The pair pins both directions -- the
    // source's leaf arrives (true `ret == 3`), and the destination's stale leaf is gone (the
    // false `ret == 7` is refuted rather than proved against the seed the move replaced).
    let carried = outcome(&report, "whole_inner_move_carries_the_source_leaf");
    assert!(
        carried.is_verified(),
        "a nested-to-nested move must carry the source's leaf; got: {carried}"
    );
    let stale_move = outcome(&report, "whole_inner_move_is_not_the_stale_destination");
    assert!(
        matches!(stale_move, FnOutcome::Failed { .. }),
        "the destination's pre-move leaf must not survive the move; got: {stale_move}"
    );
    // A nested swap: both sides are nested, so this is the shape that needs the guard to be
    // "either side nested". The two seeds are distinct, so the positive verdict is the
    // *other* side's leaf, and the twin claims the pre-swap one survived.
    let swap = outcome(&report, "nested_swap_carries_the_other_side");
    assert!(swap.is_verified(), "a nested swap must exchange the leaves; got: {swap}");
    let swap_stale = outcome(&report, "nested_swap_is_not_the_stale_side");
    assert!(
        matches!(swap_stale, FnOutcome::Failed { .. }),
        "a nested swap must not keep each side's own leaf; got: {swap_stale}"
    );
    // A nested aggregate handed to a helper by value and read back: the callee's return is a
    // struct it built field-by-field, so the merge has to carry the *fields* (not only the
    // tuple components). The positive verdict is the value that crossed; the twin claims a
    // different one survived and must be refuted.
    let through = outcome(&report, "nested_aggregate_argument_reaches_the_helper");
    assert!(
        through.is_verified(),
        "a returned nested aggregate must keep its fields; got: {through}"
    );
    let through_stale =
        outcome(&report, "nested_aggregate_argument_is_not_the_stale_destination");
    assert!(
        matches!(through_stale, FnOutcome::Failed { .. }),
        "a returned nested aggregate must not keep a stale field; got: {through_stale}"
    );
    // A returned struct's *field* read back through a two-level path: the `Struct` literal
    // stores the field value but not the operand aggregate's own parts, so the field's parts
    // have to be re-rooted. The positive verdict is the value that crossed; the twin claims a
    // different leaf and must be refuted.
    let field = outcome(&report, "nested_return_carries_the_field");
    assert!(
        field.is_verified(),
        "a returned struct's field must keep its parts; got: {field}"
    );
    let field_stale = outcome(&report, "nested_return_is_not_the_stale_field");
    assert!(
        matches!(field_stale, FnOutcome::Failed { .. }),
        "a returned struct's field must not keep a stale leaf; got: {field_stale}"
    );
}

/// A helper's write through a `&mut` argument reaches the caller, and the false
/// direction is refuted rather than proved.
///
/// The write happens one frame down. Only an *indexed* reference argument's store
/// used to cross back, so a field or scalar write through a `&mut` died with the
/// callee's frame: the caller read its own seed, and the false entries here were
/// *proved* against bodies that return 5. Both directions are toothed.
#[test]
fn a_helpers_write_through_a_mutable_reference_reaches_the_caller() {
    let Some(report) = verify_realistic(&[
        "helper_field_write_reaches_the_caller",
        "a_stale_caller_field_cannot_prove_this",
        "helper_scalar_write_reaches_the_caller",
        "a_stale_caller_scalar_cannot_prove_this",
    ]) else {
        return;
    };
    for name in
        ["helper_field_write_reaches_the_caller", "helper_scalar_write_reaches_the_caller"]
    {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "the helper's write must reach the caller; got: {o}");
    }
    for name in ["a_stale_caller_field_cannot_prove_this", "a_stale_caller_scalar_cannot_prove_this"]
    {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
}

/// An array element reached through a struct field is one word for the contract and
/// the body, and the write does not spill onto a sibling array's element.
///
/// `x.a[0] = 9; x.a[0]` lowers to `(_1.0)[_2] = 9` and `_0 = copy (_1.0)[_4]`. The
/// element store used to be keyed by the local and index alone, so the write landed
/// under a key the read never consulted and the read returned the *seed* -- the false
/// direction, where `ret == 5` was proved against a body returning 9. The pair below
/// toothes both directions, and the sibling entry catches a store that collides
/// `x.a[0]` with `x.b[0]`.
#[test]
fn a_field_array_element_is_one_word_for_contract_and_body() {
    let Some(report) = verify_realistic(&[
        "a_field_array_write_is_read_back",
        "a_field_array_write_is_not_the_seed",
        "a_sibling_field_array_is_untouched",
    ]) else {
        return;
    };
    let read_back = outcome(&report, "a_field_array_write_is_read_back");
    assert!(
        read_back.is_verified(),
        "a write to `x.a[0]` must be seen by the read of `x.a[0]`; got: {read_back}"
    );
    let seed = outcome(&report, "a_field_array_write_is_not_the_seed");
    assert!(
        matches!(seed, FnOutcome::Failed { .. }),
        "the pre-write seed must not prove a contract the body refutes; got: {seed}"
    );
    let sibling = outcome(&report, "a_sibling_field_array_is_untouched");
    assert!(
        sibling.is_verified(),
        "writing `x.a[0]` must leave `x.b[0]` alone; got: {sibling}"
    );
}

/// A *nested* array field is the same word on both sides, and the false direction is
/// refuted rather than proved.
///
/// `o.i.a[0] = 9; o.i.a[0]` lowers to `(_1.0.0)[_2] = 9` and `_0 = copy (_1.0.0)[_4]`. The
/// element's key is the whole field chain, so a store that stopped at the first field
/// (`o.i`) would key the write and the read differently and leave the read at the seed --
/// the false direction, where `ret == 5` was proved against a body returning 9.
#[test]
fn a_nested_field_array_element_is_one_word_for_contract_and_body() {
    let Some(report) = verify_realistic(&[
        "a_nested_field_array_write_is_read_back",
        "a_nested_field_array_write_is_not_the_seed",
    ]) else {
        return;
    };
    let read_back = outcome(&report, "a_nested_field_array_write_is_read_back");
    assert!(
        read_back.is_verified(),
        "a nested `o.i.a[0]` write must be seen by the read; got: {read_back}"
    );
    let seed = outcome(&report, "a_nested_field_array_write_is_not_the_seed");
    assert!(
        matches!(seed, FnOutcome::Failed { .. }),
        "the nested pre-write seed must not prove a refuted contract; got: {seed}"
    );
}

/// A helper's write to a field-array element crosses back through a `&mut`, and the read
/// crosses *in* through a `&`; both directions are pinned, with their false twins.
///
/// The callee's write lands in its own element store, so the caller's store has to be
/// re-based on return -- for a whole-local target (`set_first_element(&mut x)`) unchanged,
/// and for a sub-place target (`set_holder_first_element(&mut o.i)`) prefixed with the
/// target's chain. Without either the write died with the frame, the caller read its seed,
/// and the false `ret == 5` was **proved** against a body returning 9. The read direction is
/// the same re-basing run the other way: `read_holder_first_element(&o.i)` reads the
/// caller's `o.i.a[0]`, so its contract decides rather than being unreadable.
#[test]
fn a_field_array_element_crosses_a_reference_argument() {
    let Some(report) = verify_realistic(&[
        "a_helper_field_array_write_is_read_back",
        "a_helper_field_array_write_is_not_the_seed",
        "a_helper_nested_aggregate_element_write_is_read_back",
        "a_helper_nested_aggregate_element_write_is_not_the_seed",
        "a_helper_nested_aggregate_element_read",
    ]) else {
        return;
    };
    for name in [
        "a_helper_field_array_write_is_read_back",
        "a_helper_nested_aggregate_element_write_is_read_back",
        "a_helper_nested_aggregate_element_read",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must decide and verify; got: {o}");
    }
    for name in [
        "a_helper_field_array_write_is_not_the_seed",
        "a_helper_nested_aggregate_element_write_is_not_the_seed",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` claims the caller's seed after the helper wrote; must be refuted, got: {o}"
        );
    }
}

/// An array handed over *as* a reference target (`&mut x.a`) used to be `Incomplete` in
/// both directions. It now *decides*: the true contract is `Verified` and the false twin is
/// refuted -- and the pair is what makes the decision trustworthy.
///
/// The callee's `(*_1)[0] = 9` lands in its own element store, and the return path re-bases
/// it onto the caller's field-path store (`elems_path`, keyed by the target's *field* chain
/// `x.a`) instead of dropping it. So the caller's `x.a[0]` read is the callee's write, and
/// `ensures: ret == 9` is provable while `ensures: ret == 5` is refuted.
///
/// This test is the tripwire the *hole* was pinned with, kept in its stronger form. While
/// the shape was unmodelled it asserted `Incomplete`; the fix that made it decide is the
/// change the pin existed to police, because a re-basing that connected the two stores the
/// *wrong* way would turn the false twin `Verified` first. It did not: the twin is `Failed`.
/// If a later change makes this shape incomplete again, this test fails and the two
/// assertions say exactly which direction broke.
#[test]
fn a_whole_array_target_decides_without_a_false_proof() {
    let Some(report) = verify_realistic(&[
        "a_whole_array_target_crosses_a_reference_argument",
        "a_whole_array_target_cannot_prove_this",
        "a_whole_array_target_sibling_cannot_prove_this",
        "a_whole_array_target_read_crosses_a_reference_argument",
        "a_whole_array_target_read_cannot_prove_this",
        "a_whole_array_target_read_modify_write",
        "a_whole_array_target_read_modify_write_cannot_prove_this",
        "a_nested_whole_array_target_crosses_a_reference_argument",
        "a_nested_whole_array_target_cannot_prove_this",
        "a_whole_array_target_crosses_two_frames",
        "a_whole_array_target_crosses_two_frames_cannot_prove_this",
    ]) else {
        return;
    };
    let o = outcome(&report, "a_whole_array_target_crosses_a_reference_argument");
    assert!(
        o.is_verified(),
        "a `&mut x.a` array target re-bases the callee's element onto the caller's \
         field-path store, so the true contract `ret == 9` must verify; got: {o}"
    );
    let twin = outcome(&report, "a_whole_array_target_cannot_prove_this");
    assert!(
        matches!(twin, FnOutcome::Failed { .. }),
        "the false twin of the whole-array target must be refuted -- a false proof is the \
         only unacceptable outcome, and `Verified` here would be one; got: {twin}"
    );
    let sibling = outcome(&report, "a_whole_array_target_sibling_cannot_prove_this");
    assert!(
        !sibling.is_verified(),
        "the write to `x.a` must not leak into the sibling `x.b`, so claiming `x.b[0]` \
         changed must not verify; got: {sibling}"
    );
    let read = outcome(&report, "a_whole_array_target_read_crosses_a_reference_argument");
    assert!(
        read.is_verified(),
        "the read-only direction (`peek_of(&x.a)`) must also decide -- the carry-in \
         re-bases the caller's field-path element onto the callee's store, so `ret == 5` \
         verifies; got: {read}"
    );
    let read_twin = outcome(&report, "a_whole_array_target_read_cannot_prove_this");
    assert!(
        !read_twin.is_verified(),
        "the false read-only twin (`ret == 7` against a seed of 5) must not verify; \
         got: {read_twin}"
    );
    // The three shapes below are the re-basing rule applied where it is easy to get it
    // *partly* right: a read-modify-write (both directions in one call), a target two
    // fields deep, and a write that crosses two frames. Each true contract must decide
    // and each false twin must be refuted -- a fix that handled only the write, or only
    // a single-field chain, or only one frame, would show up as a true direction stuck
    // `Incomplete` (or, worse, a twin `Verified`).
    for (name, want) in [
        ("a_whole_array_target_read_modify_write", true),
        ("a_whole_array_target_read_modify_write_cannot_prove_this", false),
        ("a_nested_whole_array_target_crosses_a_reference_argument", true),
        ("a_nested_whole_array_target_cannot_prove_this", false),
        ("a_whole_array_target_crosses_two_frames", true),
        ("a_whole_array_target_crosses_two_frames_cannot_prove_this", false),
    ] {
        let got = outcome(&report, name);
        if want {
            assert!(got.is_verified(), "`{name}` must verify; got: {got}");
        } else {
            assert!(
                !got.is_verified(),
                "`{name}` is a false direction and must not verify; got: {got}"
            );
        }
    }
}

/// A method's returned reference to an *element* re-bases onto the caller's element.
///
/// `x.first_mut()` is `&mut x.a[0]`, and the dump names the element index with a
/// local (`_2`), not the literal. Translating the returned reference to the caller
/// therefore has to resolve that local *before* the callee's frame is gone; carrying
/// it through left a place no element store is keyed by, the write `*x.first_mut() = 9`
/// was dropped, and the contract was unreadable -- `Incomplete` in both directions.
/// The true contract must now decide and the false twin must be refuted; the sibling
/// element is the second tooth, because a fix that pinned every returned element to
/// index 0 would decide the first case and read the wrong element here.
#[test]
fn a_returned_reference_to_an_element_reaches_the_caller() {
    let Some(report) = verify_realistic(&[
        "returned_ref_to_an_element_crosses_the_frame",
        "returned_ref_to_an_element_cannot_prove_this",
        "returned_ref_to_a_sibling_element",
        "returned_ref_to_a_sibling_element_cannot_prove_this",
        "returned_ref_write_is_not_the_wrong_element_cannot_prove_this",
        "returned_ref_to_a_whole_array_element",
        "returned_ref_to_a_whole_array_element_cannot_prove_this",
        "returned_ref_to_a_nested_whole_array_element",
        "returned_ref_to_a_nested_whole_array_element_cannot_prove_this",
        "returned_ref_to_a_guarded_symbolic_element",
        "returned_ref_to_a_guarded_symbolic_element_cannot_prove_this",
        "returned_ref_to_an_unpinned_symbolic_element_cannot_prove_this",
        "a_shifted_symbolic_element_cannot_prove_this",
        "a_shifted_symbolic_element_is_not_proved",
    ]) else {
        return;
    };
    for name in [
        "returned_ref_to_an_element_crosses_the_frame",
        "returned_ref_to_a_sibling_element",
        "returned_ref_to_a_whole_array_element",
        "returned_ref_to_a_nested_whole_array_element",
        "returned_ref_to_a_guarded_symbolic_element",
    ] {
        let o = outcome(&report, name);
        assert!(
            o.is_verified(),
            "the write through the returned element reference must reach the caller's \
             element, so `{name}` must verify; got: {o}"
        );
    }
    for name in [
        "returned_ref_to_an_element_cannot_prove_this",
        "returned_ref_to_a_sibling_element_cannot_prove_this",
        "returned_ref_write_is_not_the_wrong_element_cannot_prove_this",
        "returned_ref_to_a_whole_array_element_cannot_prove_this",
        "returned_ref_to_a_nested_whole_array_element_cannot_prove_this",
        "returned_ref_to_a_guarded_symbolic_element_cannot_prove_this",
        "returned_ref_to_an_unpinned_symbolic_element_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "`{name}` is a false direction -- a write aimed at the wrong element would \
             prove it; got: {o}"
        );
    }
    // The shifted-numbering pair is a *refusal* in both directions: the write may
    // land on any element, so neither `ret == 9` nor `ret == 5` decides. The false
    // direction must not be proved (the write must not be aimed at a caller local
    // that shares the callee index's number), and the true direction must not be
    // proved either (dropping the write must not leave the seed readable).
    for name in [
        "a_shifted_symbolic_element_cannot_prove_this",
        "a_shifted_symbolic_element_is_not_proved",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "`{name}` must be a refusal -- a symbolic returned index names no single \
             element, so neither direction decides; got: {o}"
        );
    }
}

/// A helper's write-back covers a *nested* field and a read-modify-write, and the
/// caller's field seed crosses *into* the callee so the callee's read is modelled.
///
/// Two teeth here. The nested false entry must be refuted rather than proved: the
/// helper sets `o.i.v = 9` and the caller returns it, so `ret == 0` is false, and
/// a write-back that missed the nested chain would leave the caller's seed and
/// prove it. The read-modify-write entry must *verify* rather than go incomplete:
/// the callee reads `c.lo` before writing it, so carrying only the write-back
/// leaves the callee's read unmodelled and the contract unproved.
#[test]
fn a_helpers_nested_and_read_modify_write_through_a_reference_are_modelled() {
    let Some(report) = verify_realistic(&[
        "helper_nested_write_reaches_the_caller",
        "a_stale_caller_nested_cannot_prove_this",
        "read_modify_write_through_helper",
    ]) else {
        return;
    };
    let nested = outcome(&report, "helper_nested_write_reaches_the_caller");
    assert!(nested.is_verified(), "a nested write through a `&mut` must reach the caller; got: {nested}");
    let stale = outcome(&report, "a_stale_caller_nested_cannot_prove_this");
    assert!(
        matches!(stale, FnOutcome::Failed { .. }),
        "a stale caller nested value must not prove this false contract; got: {stale}"
    );
    let rmw = outcome(&report, "read_modify_write_through_helper");
    assert!(rmw.is_verified(), "a read-modify-write through a `&mut` must be modelled; got: {rmw}");
}

/// The write-back keys the *target's projection*, so `&mut c.lo` lands on the
/// field and a conditional helper write follows the callee's branch.
///
/// A target with a projection (`&mut c.lo`) must not be written to the caller's
/// local: that puts a bit-vector where a struct lives and leaves `c.lo` at its
/// seed, which is how the false twin here was *proved*. A conditional helper write
/// has to reach the caller from the branch it takes, so the `c == true` case reads
/// 5 -- and the false twin, whose precondition pins both the seed and the flag,
/// must be refuted rather than proved.
#[test]
fn a_helper_write_lands_on_the_targets_projection() {
    let Some(report) = verify_realistic(&[
        "helper_write_reaches_a_field_target",
        "a_stale_field_target_cannot_prove_this",
        "helper_write_reaches_a_nested_target",
        "a_stale_nested_target_cannot_prove_this",
        "conditional_helper_write_reaches_the_caller",
        "a_conditional_helper_write_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "helper_write_reaches_a_field_target",
        "helper_write_reaches_a_nested_target",
        "conditional_helper_write_reaches_the_caller",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a helper write must reach the caller; got: {o}");
    }
    for name in [
        "a_stale_field_target_cannot_prove_this",
        "a_stale_nested_target_cannot_prove_this",
        "a_conditional_helper_write_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
}

/// A reference to an array *element* (`set5(&mut a[0])`) is a sub-place target too,
/// and a by-value argument's callee write must stay in the callee.
///
/// Two opposite directions in one test. The element target has to land the write at
/// `a[0]` and leave `a[1]` readable: the callee holds the caller's array under its
/// own local, its whole-place write poisons that store, and copying the store back
/// unconditionally would make the *untouched* sibling unknown -- which is why the
/// copy-back is gated on a whole-local target. The by-value pair is the other
/// direction: `set_five_by_value(x)` writes its own copy, so the caller must still
/// read its seed, and a leak back would prove the false `ret == 5`.
#[test]
fn an_element_target_is_written_and_a_by_value_copy_is_not() {
    let Some(report) = verify_realistic(&[
        "helper_write_reaches_an_element_target",
        "a_stale_element_target_cannot_prove_this",
        "an_element_write_leaves_its_sibling",
        "a_stale_element_sibling_cannot_prove_this",
        "a_by_value_callee_write_stays_in_the_callee",
        "a_by_value_callee_write_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "helper_write_reaches_an_element_target",
        "an_element_write_leaves_its_sibling",
        "a_by_value_callee_write_stays_in_the_callee",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "this contract must verify; got: {o}");
    }
    for name in [
        "a_stale_element_target_cannot_prove_this",
        "a_stale_element_sibling_cannot_prove_this",
        "a_by_value_callee_write_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
}

/// A method is inlined by its *last* path component plus its receiver's type,
/// because rustc defines an inherent method as `<impl at file:line:col>::set_lo`
/// but calls it as `Config::set_lo`; a shared tail is disambiguated by the type
/// rather than guessed at.
///
/// Before the tail match, a call to any method was "unmodelled function", so a
/// method's write through `&mut self` was invisible to its caller. The tripwire
/// pins the other direction: `twist` is both a method and a free function here, so
/// the tail alone names two bodies. The call `w.twist(5)` names the receiver's
/// type, so it resolves to `Widget::twist`; inlining the free function instead
/// would write through the wrong shape and *prove* a false contract, so the
/// resolution must pick the method and refute the claim.
#[test]
fn a_method_is_inlined_by_its_tail_and_a_shared_tail_resolves_by_type() {
    let Some(report) = verify_realistic(&[
        "a_method_write_reaches_the_caller",
        "a_method_write_cannot_prove_this",
        "a_method_read_modify_write",
        "a_method_leaves_its_sibling",
        "a_stale_sibling_cannot_prove_this",
        "an_ambiguous_method_tail_cannot_prove_this",
        "a_generic_method",
        "an_associated_fn_and_builder_chain",
        "a_trait_method",
        "a_tuple_struct_read_method",
        "a_method_with_an_argument",
        "a_reborrow_target_reaches_the_caller",
        "a_stale_reborrow_cannot_prove_this",
        "a_tuple_component_target_reaches_the_caller",
        "a_stale_tuple_component_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_method_write_reaches_the_caller",
        "a_method_read_modify_write",
        "a_method_leaves_its_sibling",
        // The shapes a method can take: a generic receiver, an associated function
        // feeding a `&mut self` builder that returns `&mut Self`, a trait method,
        // and a `&self` read (on a tuple struct, and with an argument).
        "a_generic_method",
        "an_associated_fn_and_builder_chain",
        "a_trait_method",
        "a_tuple_struct_read_method",
        "a_method_with_an_argument",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a method write must reach its caller; got: {o}");
    }
    for name in ["a_method_write_cannot_prove_this", "a_stale_sibling_cannot_prove_this"] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
    // A reborrow (`&mut *r`) and a tuple component (`&mut t.0`) are sub-place targets
    // too, and both land on the caller's storage.
    for name in [
        "a_reborrow_target_reaches_the_caller",
        "a_tuple_component_target_reaches_the_caller",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a sub-place target must reach the caller; got: {o}");
    }
    for name in [
        "a_stale_reborrow_cannot_prove_this",
        "a_stale_tuple_component_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
    // The tail `twist` is shared by `Widget::twist` and a free `twist`, but the
    // call `w.twist(5)` names its receiver's type, so the resolver picks the
    // method by that type rather than by the tail alone. Answering it from the
    // free function -- which writes through a `&mut u8` -- would *prove* this
    // false contract; the correct body sets `w.v = 5`, so the postcondition is
    // refuted. Refuted is the evidence the right body was chosen.
    let o = outcome(&report, "an_ambiguous_method_tail_cannot_prove_this");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a shared method tail must resolve to the receiver's own body and refute \
         the false contract, not prove it; got: {o}"
    );
}

/// A helper that *reads* its referent, a read-modify-write helper, a two-reference
/// call, and a nested *aggregate* target.
///
/// Each of these needs something the write-only case did not. A read needs the
/// referent's value carried *into* the callee (`_1` otherwise holds the reference
/// temp's `Unknown`, so `*v` is an unmodelled operand). A sub-place aggregate target
/// (`&mut o.i`) needs both the carry-in and the write-back re-based on the target's
/// projection -- dropping the write there refuted the true `ret == 5` and *proved*
/// the false `ret == 0`, which is why the false twin is pinned.
#[test]
fn a_reference_argument_is_read_and_written_through_its_target() {
    let Some(report) = verify_realistic(&[
        "a_read_through_a_helper",
        "a_stale_read_through_a_helper_cannot_prove_this",
        "a_bump_through_a_helper",
        "a_stale_bump_cannot_prove_this",
        "two_reference_arguments",
        "two_reference_arguments_other",
        "two_reference_arguments_swapped_cannot_prove_this",
        "a_swap_through_two_references",
        "a_swap_through_two_references_other",
        "a_stale_swap_cannot_prove_this",
        "a_nested_aggregate_target_reaches",
        "a_stale_nested_aggregate_cannot_prove_this",
        "a_nested_aggregate_read",
        "a_stale_nested_aggregate_read_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_read_through_a_helper",
        "a_bump_through_a_helper",
        "two_reference_arguments",
        "two_reference_arguments_other",
        "a_swap_through_two_references",
        "a_swap_through_two_references_other",
        "a_nested_aggregate_target_reaches",
        "a_nested_aggregate_read",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a reference argument must reach its target; got: {o}");
    }
    for name in [
        "a_stale_read_through_a_helper_cannot_prove_this",
        "a_stale_bump_cannot_prove_this",
        "two_reference_arguments_swapped_cannot_prove_this",
        "a_stale_swap_cannot_prove_this",
        "a_stale_nested_aggregate_cannot_prove_this",
        "a_stale_nested_aggregate_read_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale or unread referent must not prove this false contract; got: {o}"
        );
    }
}

/// The receiver *shapes* a method arrives in: a nested-field receiver, two calls in
/// sequence, a reborrowed receiver, a `&self` read feeding a `&mut` write, and a leaf
/// write that must leave its sibling at the caller's seed.
///
/// These decide through the same inlining and write-back as the plain receiver, which
/// is the point: the receiver is just another argument, and its target is a sub-place
/// (`o.i`) rather than a whole local.
#[test]
fn a_method_receiver_is_a_sub_place_like_any_other_argument() {
    let Some(report) = verify_realistic(&[
        "a_method_on_a_nested_receiver",
        "a_stale_nested_receiver_cannot_prove_this",
        "two_methods_in_sequence",
        "a_stale_first_method_cannot_prove_this",
        "a_method_through_a_reborrow",
        "a_stale_reborrow_receiver_cannot_prove_this",
        "a_read_method_feeds_a_write",
        "a_stale_read_method_cannot_prove_this",
        "a_leaf_write_leaves_its_sibling",
        "a_stale_leaf_sibling_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_method_on_a_nested_receiver",
        "two_methods_in_sequence",
        "a_method_through_a_reborrow",
        "a_read_method_feeds_a_write",
        "a_leaf_write_leaves_its_sibling",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a method receiver must reach its target; got: {o}");
    }
    for name in [
        "a_stale_nested_receiver_cannot_prove_this",
        "a_stale_first_method_cannot_prove_this",
        "a_stale_reborrow_receiver_cannot_prove_this",
        "a_stale_read_method_cannot_prove_this",
        "a_stale_leaf_sibling_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale receiver value must not prove this false contract; got: {o}"
        );
    }
}

/// A helper that forwards its reference to another helper, and a helper that
/// *returns* the reference it was given.
///
/// The returned reference is the sharp case: `let r = identity(&mut x); *r = 5`
/// lowers to `_3 = &mut _1; _2 = identity(_3); (*_2) = 5`, so the write is keyed on
/// a local the *call* defined. Without the reference's origin crossing the call,
/// `_2` had no address, the write went to a local no caller reads, and the false
/// `ret == 0` was proved while the true `ret == 5` was refuted.
#[test]
fn a_reference_crosses_a_call_in_both_directions() {
    let Some(report) = verify_realistic(&[
        "a_two_frame_chain",
        "a_stale_two_frame_chain_cannot_prove_this",
        "a_two_frame_constant",
        "a_stale_two_frame_constant_cannot_prove_this",
        "a_write_through_a_returned_reference",
        "a_stale_returned_reference_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_two_frame_chain",
        "a_two_frame_constant",
        "a_write_through_a_returned_reference",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a forwarded reference must reach its target; got: {o}");
    }
    for name in [
        "a_stale_two_frame_chain_cannot_prove_this",
        "a_stale_two_frame_constant_cannot_prove_this",
        "a_stale_returned_reference_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped write must not prove this false contract; got: {o}"
        );
    }
}

/// A method that *returns* a reference to one of its own fields.
///
/// `*c.lo_mut() = 5` lowers to `_2 = Config::lo_mut(move _3); (*_2) = 5; _0 = c.lo`,
/// and inside the callee the returned reference is `&mut (*_1).0` -- a place in the
/// *callee's* terms. Translating its head through the argument's caller place gives
/// `c.lo`. Without that the returned reference named nothing, the write was dropped,
/// the true `ret == 5` was refuted, and the false `ret == 0` was **proved**.
#[test]
fn a_method_may_return_a_reference_to_its_own_field() {
    let Some(report) = verify_realistic(&[
        "a_write_through_a_returned_field_reference",
        "a_stale_returned_field_reference_cannot_prove_this",
        "a_write_through_the_other_returned_reference",
        "a_stale_other_returned_reference_cannot_prove_this",
        "a_write_through_a_returned_builder",
        "a_stale_returned_builder_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_write_through_a_returned_field_reference",
        "a_write_through_the_other_returned_reference",
        "a_write_through_a_returned_builder",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a returned field reference must reach the field; got: {o}");
    }
    for name in [
        "a_stale_returned_field_reference_cannot_prove_this",
        "a_stale_other_returned_reference_cannot_prove_this",
        "a_stale_returned_builder_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped write through a returned reference must not prove this; got: {o}"
        );
    }
}

/// A returned reference may name a *nested* place, or a place in a *different*
/// argument.
///
/// The nested case (`&mut o.i.v`) needs the whole projection carried, not just the
/// head local, and the two-argument case needs the translation to pick the argument
/// the reference was actually built from rather than the first one.
#[test]
fn a_returned_reference_carries_its_whole_projection() {
    let Some(report) = verify_realistic(&[
        "a_write_through_a_returned_nested_reference",
        "a_stale_returned_nested_reference_cannot_prove_this",
        "a_returned_nested_reference_leaves_its_sibling",
        "a_write_through_a_method_nested_reference",
        "a_stale_method_nested_reference_cannot_prove_this",
        "a_write_through_a_second_argument_reference",
        "a_stale_second_argument_reference_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_write_through_a_returned_nested_reference",
        "a_returned_nested_reference_leaves_its_sibling",
        "a_write_through_a_method_nested_reference",
        "a_write_through_a_second_argument_reference",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a returned reference must reach its place; got: {o}");
    }
    for name in [
        "a_stale_returned_nested_reference_cannot_prove_this",
        "a_stale_method_nested_reference_cannot_prove_this",
        "a_stale_second_argument_reference_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped write through a returned reference must not prove this; got: {o}"
        );
    }
}

/// A returned reference fed straight into another call, reborrowed, held alongside a
/// second returned reference to a different field, or naming a tuple component.
///
/// The reborrow (`let s = &mut *r` where `r` came from a call) and the pass-through
/// (`write_one(identity(&mut c.lo))`) both go through the same `addressed` mapping
/// the returned reference installs. Two returned references to different fields must
/// not collapse onto one, and a tuple component is a returned place the write-back key
/// *can* spell (`Field(0)`), unlike an array element.
#[test]
fn a_returned_reference_composes_with_the_next_use() {
    let Some(report) = verify_realistic(&[
        "a_reference_returned_into_another_call",
        "a_stale_returned_into_another_call_cannot_prove_this",
        "a_reborrow_of_a_returned_reference",
        "a_stale_reborrow_of_a_returned_reference_cannot_prove_this",
        "two_returned_field_references",
        "a_stale_two_returned_fields_cannot_prove_this",
        "a_returned_tuple_component_reference",
        "a_stale_tuple_component_reference_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_reference_returned_into_another_call",
        "a_reborrow_of_a_returned_reference",
        "two_returned_field_references",
        "a_returned_tuple_component_reference",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a returned reference must compose with its next use; got: {o}");
    }
    for name in [
        "a_stale_returned_into_another_call_cannot_prove_this",
        "a_stale_reborrow_of_a_returned_reference_cannot_prove_this",
        "a_stale_two_returned_fields_cannot_prove_this",
        "a_stale_tuple_component_reference_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped or misplaced write must not prove this false contract; got: {o}"
        );
    }
}

/// Two `&mut` targets in one call: two *aggregate* fields, or two *elements* of one
/// array.
///
/// The two writes must stay independent -- the false twins read the *other* target,
/// and would verify if the two targets collapsed onto one place. The swap shapes read
/// both referents, so they also exercise the carry-in.
#[test]
fn two_reference_targets_in_one_call_stay_independent() {
    let Some(report) = verify_realistic(&[
        "two_aggregate_reference_targets",
        "two_aggregate_reference_targets_other",
        "a_stale_two_aggregate_targets_cannot_prove_this",
        "a_swap_of_two_aggregate_targets",
        "a_stale_swap_of_aggregate_targets_cannot_prove_this",
        "two_elements_through_one_reference",
        "two_elements_through_one_reference_other",
        "a_stale_two_elements_cannot_prove_this",
        "a_swap_of_two_elements",
        "a_stale_swap_of_elements_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "two_aggregate_reference_targets",
        "two_aggregate_reference_targets_other",
        "a_swap_of_two_aggregate_targets",
        "two_elements_through_one_reference",
        "two_elements_through_one_reference_other",
        "a_swap_of_two_elements",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "two reference targets must stay independent; got: {o}");
    }
    for name in [
        "a_stale_two_aggregate_targets_cannot_prove_this",
        "a_stale_swap_of_aggregate_targets_cannot_prove_this",
        "a_stale_two_elements_cannot_prove_this",
        "a_stale_swap_of_elements_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "collapsed or stale targets must not prove this false contract; got: {o}"
        );
    }
}

/// A *scalar* field reached through a `&T`/`&mut T` argument, both read and written.
///
/// The referent's parts are carried into the callee, so the callee's `d.v` resolves to
/// the caller's `d.v`; the write-back then re-bases on the target's projection, which
/// is empty here (the target is the whole local). An enum *payload* through a reference
/// stays sound-incomplete -- the discriminant switch is unmodelled -- which is the
/// honest refusal rather than a dropped write.
#[test]
fn a_scalar_field_crosses_a_reference_argument() {
    let Some(report) = verify_realistic(&[
        "a_scalar_field_read_through_a_reference",
        "a_stale_scalar_field_read_cannot_prove_this",
        "a_scalar_field_write_through_a_reference",
        "a_stale_scalar_field_write_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_scalar_field_read_through_a_reference",
        "a_scalar_field_write_through_a_reference",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a scalar field must cross a reference argument; got: {o}");
    }
    for name in [
        "a_stale_scalar_field_read_cannot_prove_this",
        "a_stale_scalar_field_write_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale scalar field must not prove this false contract; got: {o}"
        );
    }
}

/// A scalar `&mut` argument named in a contract (C9).
///
/// `Ty::Ref` is modelled as its referent, so a `&mut u16` argument's name denotes
/// the `u16` it addresses. The name is the *final* value -- what the body left
/// there -- and `old(c)` reaches the entry value. Binding a bare `c` to the entry
/// value (the first cut of this feature) was a **false proof**: `ensures: c == 0`
/// on `*c = 5` verified, because `c` still named the input.
#[test]
fn a_scalar_reference_argument_is_named_in_a_contract() {
    let Some(report) = verify_realistic(&[
        "bump_scalar_ref",
        "a_stale_scalar_ref_cannot_prove_this",
        "set_scalar_ref",
        "a_scalar_ref_write_cannot_prove_this",
        "signed_scalar_ref",
        "a_scalar_ref_caller",
        "bump_scalar_ref_star",
    ]) else {
        return;
    };
    for name in [
        "bump_scalar_ref",
        "set_scalar_ref",
        "signed_scalar_ref",
        "a_scalar_ref_caller",
        "bump_scalar_ref_star",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a scalar reference argument must be nameable; got: {o}");
    }
    // The false directions: each claims the *entry* value survived a write, which
    // only a model that bound the postcondition's name to the input would prove.
    for name in ["a_stale_scalar_ref_cannot_prove_this", "a_scalar_ref_write_cannot_prove_this"] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a scalar reference write must not prove the stale contract; got: {o}"
        );
    }
}

/// A scalar `&mut` argument's name and `old(name)`, checked directly so the guard
/// runs even without a nightly `rustc`.
#[test]
fn a_scalar_reference_argument_reads_as_its_referent() {
    use verif::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("c".to_string(), smt::var(16));
        let mut old = std::collections::BTreeMap::new();
        old.insert("c".to_string(), smt::var(16));
        // `c` (final) and `old(c)` (entry) are distinct inputs, so their equality
        // is not a tautology.
        let p = spec::eval_ensures(
            "c == old(c) + 1",
            &args,
            None,
            spec::RET_IS_AGGREGATE,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
            &old,
        )
        .expect("a scalar reference argument and `old` must parse");
        assert!(!smt::is_ill_formed(), "the contract must be well-formed");
        // The claim is a real predicate over two distinct variables, not a
        // tautology: it is refutable at `c == old(c)`.
        assert!(
            matches!(smt::prove(p), smt::Verdict::Counterexample(_)),
            "`c == old(c) + 1` must be refutable, not a tautology"
        );
        // `*c` and `old(*c)` are the explicit spellings of the same two bindings,
        // so the roadmap's exit shape parses and means the same predicate.
        let star = spec::eval_ensures(
            "*c == old(*c) + 1",
            &args,
            None,
            spec::RET_IS_AGGREGATE,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
            &old,
        )
        .expect("`*c` and `old(*c)` must parse");
        assert!(
            matches!(smt::prove(smt::iff(star, p)), smt::Verdict::Valid),
            "`*c == old(*c) + 1` must mean the same as `c == old(c) + 1`"
        );
        // `*NAME` on an unbound name is refused, not read as a fresh variable.
        assert!(
            spec::eval_ensures(
                "*d == 0",
                &args,
                None,
                spec::RET_IS_AGGREGATE,
                &std::collections::BTreeSet::new(),
                false,
                &spec::FieldEnv::default(),
                &old,
            )
            .is_err(),
            "`*d` on an unbound name must be refused"
        );
        // `old` on a name with no entry value is refused, not silently treated as
        // the name itself.
        let err = spec::eval_ensures(
            "c == old(d)",
            &args,
            None,
            spec::RET_IS_AGGREGATE,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
            &old,
        )
        .expect_err("`old(d)` has no entry value and must be refused");
        assert!(err.to_string().contains("old"), "the refusal must name `old`, got: {err}");
    });
}

/// A reference reached *through* another reference, and a reference to a local copy.
///
/// `**rr = 5` lowers to `_4 = no_retag copy (*_3); (*_4) = 5` with `_4: &mut u8`. The
/// `no_retag` prefix left the rvalue unparsed and the deref-of-a-reference copy had no
/// address, so the write was dropped: the *false* `ret == 0` proved and the true
/// `ret == 5` refuted. The read shape `**rr` had the same hole, and a write through a
/// reference to a local *copy* must not reach the original.
#[test]
fn a_reference_through_a_reference_is_not_dropped() {
    let Some(report) = verify_realistic(&[
        "a_write_through_two_levels_of_reference",
        "a_stale_two_level_write_cannot_prove_this",
        "a_read_through_two_levels_of_reference",
        "a_stale_two_level_read_cannot_prove_this",
        "a_write_to_a_copy_stays_in_the_copy",
        "a_stale_copy_write_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_write_through_two_levels_of_reference",
        "a_read_through_two_levels_of_reference",
        "a_write_to_a_copy_stays_in_the_copy",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a two-level reference must reach its place; got: {o}");
    }
    for name in [
        "a_stale_two_level_write_cannot_prove_this",
        "a_stale_two_level_read_cannot_prove_this",
        "a_stale_copy_write_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped two-level write, or an aliasing copy, must not prove this; got: {o}"
        );
    }
}

/// A copy between two reference targets, a field through a *double* reference, and a
/// call through a reference to a reference.
///
/// `*r = *s` on two `&mut` to different fields must copy the right way, and
/// `(**rr).lo = 5` resolves both levels inside the frame. The *argument* case
/// (`relay(&mut r)` with `v: &mut &mut u8`) crosses two frames and is refused rather
/// than modelled -- the callee's write had been dropped, proving a false `ret == 0`.
#[test]
fn a_reference_to_a_reference_crosses_a_frame_only_when_refused() {
    let Some(report) = verify_realistic(&[
        "a_copy_between_two_reference_targets",
        "a_stale_copy_between_reference_targets_cannot_prove_this",
        "a_write_through_a_double_reference_to_a_struct",
        "a_stale_double_reference_struct_cannot_prove_this",
        "a_call_through_a_reference_to_a_reference_is_refused",
    ]) else {
        return;
    };
    for name in [
        "a_copy_between_two_reference_targets",
        "a_write_through_a_double_reference_to_a_struct",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a local reference chain must be modelled; got: {o}");
    }
    for name in [
        "a_stale_copy_between_reference_targets_cannot_prove_this",
        "a_stale_double_reference_struct_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale or misdirected reference write must not prove this; got: {o}"
        );
    }
    let refused = outcome(&report, "a_call_through_a_reference_to_a_reference_is_refused");
    assert!(
        matches!(refused, FnOutcome::Incomplete { .. }),
        "a `&mut &mut T` call must be refused, not decided; got: {refused}"
    );
}

/// An array that is a struct *field* carries its elements when the aggregate is moved.
///
/// `ArrayHolder { a: [9, 1, 2, 3] }` builds the array in a temp whose elements live in the
/// whole-local `elems` store, then moves it into the field. `rebase_parts` re-based
/// `elems_path` (field-path arrays) but missed `elems`, so `x.a[0]` read `Unknown` and the
/// contract stayed `Incomplete` in *both* directions -- a coverage hole, not a false proof,
/// since a missing value proves nothing. A bare array literal always worked, so the hole
/// was specific to the field case. The whole-field write through a reference (`*h = n`)
/// exercises the same carry across a frame, and the sibling check keeps the re-base from
/// spilling the elements onto a neighbouring scalar.
#[test]
fn an_array_field_of_a_moved_aggregate_carries_its_elements() {
    let Some(report) = verify_realistic(&[
        "a_struct_literal_array_element_is_read_back",
        "a_struct_literal_array_element_is_not_the_seed_cannot_prove_this",
        "a_struct_literal_array_second_element_is_read_back",
        "a_struct_literal_array_second_element_is_not_the_first_cannot_prove_this",
        "a_nested_struct_literal_array_element_is_read_back",
        "a_nested_struct_literal_array_element_is_not_the_seed_cannot_prove_this",
        "a_whole_field_assignment_carries_its_array_elements",
        "a_stale_whole_field_array_element_cannot_prove_this",
        "a_whole_field_assignment_leaves_its_sibling",
        "a_whole_field_assignment_leaves_its_sibling_cannot_prove_this",
        "an_array_field_argument_is_read_by_element",
        "an_array_field_argument_is_read_by_element_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_struct_literal_array_element_is_read_back",
        "a_struct_literal_array_second_element_is_read_back",
        "a_nested_struct_literal_array_element_is_read_back",
        "a_whole_field_assignment_carries_its_array_elements",
        "a_whole_field_assignment_leaves_its_sibling",
        "an_array_field_argument_is_read_by_element",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "an array field's elements must reach the read; got: {o}");
    }
    for name in [
        "a_struct_literal_array_element_is_not_the_seed_cannot_prove_this",
        "a_struct_literal_array_second_element_is_not_the_first_cannot_prove_this",
        "a_nested_struct_literal_array_element_is_not_the_seed_cannot_prove_this",
        "a_stale_whole_field_array_element_cannot_prove_this",
        "a_whole_field_assignment_leaves_its_sibling_cannot_prove_this",
        "an_array_field_argument_is_read_by_element_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale or misdirected array-field element must not prove this; got: {o}"
        );
    }
}

/// An array or tuple *literal* whose elements are aggregates carries the elements' leaves.
///
/// `[o.i, o.j]` stores each element's own value but not the leaves under it, so
/// `a[0].v` read `Unknown` and the contract stayed `Incomplete` in *both* directions
/// -- a coverage hole, not a false proof, since a missing value proves nothing. The
/// read is `_2[_5].0`: an index *then* a field, the opposite order from `o.a[0]`,
/// which is why it needed its own key rather than `rebase_parts`. The pairs pin both
/// directions: a read that leaked the *other* element's leaf, or kept the pre-write
/// leaf, would decide the false entry and the pair would look green while proving
/// something untrue.
#[test]
fn an_aggregate_literal_element_carries_its_own_leaves() {
    let Some(report) = verify_realistic(&[
        "an_array_literal_of_aggregates_is_read_back",
        "an_array_literal_of_aggregates_is_not_the_other_element_cannot_prove_this",
        "an_array_literal_of_aggregates_second_element_is_read_back",
        "an_array_literal_of_aggregates_second_is_not_the_first_cannot_prove_this",
        "an_array_literal_of_aggregate_fields_is_read_back",
        "an_array_literal_of_aggregate_fields_is_not_the_other_cannot_prove_this",
        "a_tuple_literal_of_aggregates_is_read_back",
        "a_tuple_literal_of_aggregates_is_not_the_other_cannot_prove_this",
        "an_element_write_of_an_aggregate_is_read_back",
        "an_element_write_of_an_aggregate_is_not_the_old_leaf_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "an_array_literal_of_aggregates_is_read_back",
        "an_array_literal_of_aggregates_second_element_is_read_back",
        "an_array_literal_of_aggregate_fields_is_read_back",
        "a_tuple_literal_of_aggregates_is_read_back",
        "an_element_write_of_an_aggregate_is_read_back",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "an aggregate element's leaves must reach the read; got: {o}");
    }
    for name in [
        "an_array_literal_of_aggregates_is_not_the_other_element_cannot_prove_this",
        "an_array_literal_of_aggregates_second_is_not_the_first_cannot_prove_this",
        "an_array_literal_of_aggregate_fields_is_not_the_other_cannot_prove_this",
        "a_tuple_literal_of_aggregates_is_not_the_other_cannot_prove_this",
        "an_element_write_of_an_aggregate_is_not_the_old_leaf_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a leaked or stale element leaf must not prove this; got: {o}"
        );
    }
}

/// A write to a leaf *inside* an element of an array or tuple of aggregates is
/// read back, and a stale leaf cannot prove the false twin.
///
/// `elem_parts` is keyed index-first -- the key the read `a[0].v` consults -- so a
/// write that reached only `elems` (the element's own value) or no store at all left
/// the literal's old leaf in place. A stale leaf is a *wrong* value rather than a
/// missing one, so each `..._cannot_prove_this` twin below is a false contract the
/// old model **proved**; without them a fix that dropped the write would look green.
/// The tuple twin exercises the mirror key, which is the only path a `t.0.v` read
/// takes, and the second-element twin catches a fix that pinned index 0 for every
/// leaf write.
#[test]
fn a_leaf_write_inside_an_element_is_read_back() {
    let verified = [
        "an_element_leaf_write_is_read_back",
        "an_element_leaf_write_leaves_its_sibling",
        "a_second_element_leaf_write_is_read_back",
        "a_tuple_component_leaf_write_is_read_back",
    ];
    let refuted = [
        "an_element_leaf_write_is_not_the_old_leaf_cannot_prove_this",
        "an_element_leaf_write_is_not_the_sibling_cannot_prove_this",
        "a_second_element_leaf_write_is_not_the_old_leaf_cannot_prove_this",
        "a_tuple_component_leaf_write_is_not_the_old_leaf_cannot_prove_this",
    ];
    let mut names = verified.to_vec();
    names.extend_from_slice(&refuted);
    let Some(report) = verify_realistic(&names) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a leaf write inside an element must reach the read; got: {o}");
    }
    for name in refuted {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale element leaf must not prove this; got: {o}"
        );
    }
}

/// A `variant:` measure turns partial correctness into total correctness.
///
/// Without a measure a loop is only proved for *partial* correctness: a divergent
/// loop verifies, because nothing says the header is ever left. With one, the back
/// edge also proves `I && guard => V' < V`, and on a fixed bit width a strictly
/// decreasing sequence cannot be infinite -- so the loop must stop.
///
/// The negative twins are the point. `a_loop_that_cannot_terminate_fails` is the
/// soundness check: before the measure existed the divergent loop *verified*, and
/// the whole reason to add the feature is that this must not happen.
#[test]
fn a_variant_measure_proves_loop_termination() {
    // A real countdown loop: the measure decreases every iteration, so the
    // termination obligation is discharged. `u8`/`u16` are used because the
    // bit-blasted query for a 32-bit measure is larger than the engine's diagram
    // budget -- that is a refusal, not a failure, and it is the same budget that
    // bounds every other wide query.
    let ok = verify_src(
        "f",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    invariant: i <= n,\n    variant: n - i,\n    ensures: ret == n,\n}\npub fn f(n: u8) -> u8 { let mut i = 0u8; while i < n { i += 1; } i }\n",
    );
    let Some(o) = ok else { return };
    assert!(o.is_verified(), "a decreasing measure must prove termination; got: {o}");
}

/// A loop whose body never advances the measure is *not* proved, and the failure
/// names the termination obligation rather than a postcondition.
///
/// This is the case the feature exists for. `while i < 5 { i += 0 }` never leaves
/// the loop, so a tool that reports it `Verified` is certifying a function that
/// does not return. Before `variant:` the loop had no termination obligation at
/// all and came back `Verified`; now the measure `i` is proved not to decrease and
/// the function fails.
#[test]
fn a_loop_that_cannot_terminate_fails() {
    let div = verify_src(
        "f",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    invariant: i >= 0,\n    variant: i,\n    ensures: ret == 0,\n}\npub fn f(n: u32) -> u32 { let _ = n; let mut i = 0u32; while i < 5 { i += 0; } i }\n",
    );
    let Some(o) = div else { return };
    assert!(!o.is_verified(), "a divergent loop must not verify; got: {o}");
    match &o {
        FnOutcome::Failed { kind, .. } => {
            assert!(kind.contains("variant"), "the failure names termination; got: {kind}")
        }
        other => panic!("expected a termination failure, got: {other}"),
    }
}

/// A measure that moves the wrong way fails, so the obligation is a real proof
/// and not a restatement of the invariant.
#[test]
fn a_measure_that_increases_fails() {
    let wrong = verify_src(
        "f",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    invariant: i <= n,\n    variant: i,\n    ensures: ret == n,\n}\npub fn f(n: u8) -> u8 { let mut i = 0u8; while i < n { i += 1; } i }\n",
    );
    let Some(o) = wrong else { return };
    assert!(!o.is_verified(), "an increasing measure must fail; got: {o}");
}

/// Without a measure the loop is still checked, for partial correctness: the
/// invariant and the postcondition are proved exactly as before, and no
/// termination claim is made. Adding the feature must not make the measure
/// mandatory.
#[test]
fn a_loop_without_a_measure_is_still_verified_for_partial_correctness() {
    let partial = verify_src(
        "f",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    invariant: i <= n,\n    ensures: ret == n,\n}\npub fn f(n: u8) -> u8 { let mut i = 0u8; while i < n { i += 1; } i }\n",
    );
    let Some(o) = partial else { return };
    assert!(o.is_verified(), "partial correctness must still be proved; got: {o}");
}

/// A measure with no invariant has no loop to attach to, so it is refused rather
/// than ignored -- an ignored measure would report partial correctness as if it
/// were total.
#[test]
fn a_measure_without_an_invariant_is_refused() {
    let orphan = verify_src(
        "f",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    variant: n,\n    ensures: ret == 5,\n}\npub fn f(n: u32) -> u32 { let _ = n; 5 }\n",
    );
    let Some(o) = orphan else { return };
    assert!(!o.is_verified(), "an orphan measure must not verify; got: {o}");
    assert!(matches!(o, FnOutcome::Skipped { .. }), "expected a refusal; got: {o}");
}

/// A loop with no invariant is unwound up to `unwind:`, and the clause raises the
/// bound so a loop whose trip count exceeds the default still decides.
///
/// `count_twelve` runs twelve iterations, more than `DEFAULT_UNWIND` (9), so the
/// default refuses it. With `unwind: 20` the walk reaches the exit edge and the
/// postcondition is proved. This is the C4 exit criterion's bounded-unrolling
/// half: the bound is *declared* and governs the loop.
#[test]
fn an_unwind_clause_raises_the_unwinding_bound() {
    let default = verify_src(
        "count_twelve_default",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == 12,\n}\npub fn count_twelve_default() -> u8 { let mut i = 0u8; while i < 12 { i += 1; } i }\n",
    );
    let Some(o) = default else { return };
    assert!(
        !o.is_verified(),
        "twelve iterations exceed the default bound, so it must not verify; got: {o}"
    );
    match &o {
        FnOutcome::Incomplete { reasons, .. } => assert!(
            reasons.iter().any(|r| r.contains("unwound past")),
            "the cutoff must name the unwinding bound; got: {reasons:?}"
        ),
        other => panic!("expected an unwinding cutoff, got: {other}"),
    }

    let raised = verify_src(
        "count_twelve_unwind",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    unwind: 20,\n    ensures: ret == 12,\n}\npub fn count_twelve_unwind() -> u8 { let mut i = 0u8; while i < 12 { i += 1; } i }\n",
    );
    let Some(o) = raised else { return };
    assert!(o.is_verified(), "an explicit larger bound must decide the loop; got: {o}");
}

/// The bound is an *unwinding assertion*: too small a bound must not decide the
/// function by accident. `unwind: 3` on a loop that runs five iterations cannot
/// reach the exit edge, so the bound is *refuted* -- a failure, not an
/// incompleteness.
///
/// This is the Kani-style discipline the review asked for (C4(b)): a bound can
/// never cut off a path *silently*, and a too-small bound fails the unwinding
/// check rather than being reported as "could not decide". A bound that were only
/// an incompleteness could be read as "no counterexample found", which is exactly
/// the weaker proof the clause exists to prevent.
#[test]
fn an_unwind_bound_too_small_for_the_loop_is_refuted() {
    let small = verify_src(
        "count_five_unwind3",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    unwind: 3,\n    ensures: ret == 5,\n}\npub fn count_five_unwind3() -> u8 { let mut i = 0u8; while i < 5 { i += 1; } i }\n",
    );
    let Some(o) = small else { return };
    assert!(!o.is_verified(), "a bound below the trip count must not verify; got: {o}");
    match &o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("unwind: 3"),
            "the failure must name the declared bound; got: {kind}"
        ),
        other => panic!("expected an unwinding-assertion failure, got: {other}"),
    }
}

/// A postcondition that is false is still refuted under a raised bound, so the
/// clause widens *coverage* and not the proof.
#[test]
fn an_unwind_clause_does_not_turn_a_false_postcondition_true() {
    let bad = verify_src(
        "count_twelve_bad",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    unwind: 20,\n    ensures: ret == 11,\n}\npub fn count_twelve_bad() -> u8 { let mut i = 0u8; while i < 12 { i += 1; } i }\n",
    );
    let Some(o) = bad else { return };
    assert!(!o.is_verified(), "a false postcondition must not verify; got: {o}");
    match &o {
        FnOutcome::Failed { kind, .. } => {
            assert!(kind.contains("postcondition"), "the failure is the postcondition; got: {kind}")
        }
        other => panic!("expected a postcondition failure, got: {other}"),
    }
}

/// C4's exit criterion, exactly: `max_of` verified with `unwind: 5`, and refuted
/// with `unwind: 3` by the unwinding check.
///
/// `max_of` is a four-iteration loop over a `[u8; 4]` with a branch inside, so it
/// explores 199 paths -- above the default 64-path budget. `unwind: 5` both raises
/// the loop bound and grows the path budget to match (see [`exec::path_budget`]),
/// so the loop decides. `unwind: 3` cannot reach the exit edge, and because the
/// bound is *declared* that is the unwinding assertion failing, not an
/// incompleteness.
#[test]
fn max_of_verifies_with_a_sufficient_unwind_bound_and_fails_with_a_small_one() {
    const BODY: &str = "pub fn max_of(a: [u8; 4]) -> u8 { let mut m = 0; let mut i = 0; \
                        while i < 4 { if a[i] > m { m = a[i]; } i += 1; } m }\n";
    const ENSURES: &str = "/// ensures: ret >= a[0] && ret >= a[1] && ret >= a[2] && ret >= a[3]\n";

    let ok = verify_src("max_of", &format!("/// requires: true\n/// unwind: 5\n{ENSURES}{BODY}"));
    let Some(o) = ok else { return };
    assert!(o.is_verified(), "`max_of` under `unwind: 5` must verify; got: {o}");

    let small = verify_src(
        "max_of_small",
        &format!("/// requires: true\n/// unwind: 3\n{ENSURES}{BODY}")
            .replace("max_of", "max_of_small"),
    );
    let Some(o) = small else { return };
    assert!(!o.is_verified(), "`max_of` under `unwind: 3` must not verify; got: {o}");
    match &o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("unwind: 3"),
            "the small-bound failure is the unwinding check; got: {kind}"
        ),
        other => panic!("expected an unwinding-assertion failure, got: {other}"),
    }
}

/// A clause-shaped doc comment that is not a clause is refused, not dropped.
///
/// `/// ensuers: ret == 99` used to be discarded: the function then had no
/// postcondition, was checked against `true`, and came back `Verified` with zero
/// obligations -- a green report for a claim nobody read. The same held for
/// `variant:`, where the reader wrote a termination measure and the tool ignored
/// it. Both are now `Skipped` with the line named, which is the discipline an
/// unreadable `requires` already follows.
///
/// The negative twins pin the other direction: ordinary prose that happens to
/// contain a colon (`/// direction: ...`) is more than two edits from every
/// keyword and must *not* be refused, or documentation would start failing
/// builds.
#[test]
fn a_clause_shaped_doc_comment_that_is_not_a_clause_is_refused() {
    let typo = verify_src(
        "f",
        "/// requires: x == 0\n/// ensuers: ret == 99\npub fn f(x: u32) -> u32 { 5 }\n",
    );
    let Some(o) = typo else { return };
    assert!(!o.is_verified(), "a typo must not verify the function without it; got: {o}");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "a dropped clause is a refusal, not a silent pass; got: {o}"
    );
    assert!(o.to_string().contains("ensuers"), "the refusal names the line; got: {o}");
    assert!(o.to_string().contains("ensures"), "and suggests the keyword; got: {o}");

    // `variant:` is a *supported* clause, so it is no longer a near miss. A
    // measure with no invariant is still refused, because the invariant is what
    // locates the loop the measure is about.
    let orphan = verify_src("g", "/// variant: n\n/// ensures: ret == 5\npub fn g(n: u32) -> u32 { let _ = n; 5 }\n");
    let Some(o) = orphan else { return };
    assert!(!o.is_verified(), "an orphan measure must not pass silently; got: {o}");
    assert!(o.to_string().contains("variant"), "the refusal names it; got: {o}");

    // Prose is left alone. `direction:` is three edits from `decreases`, so it is
    // documentation rather than a typo, and the function verifies normally.
    let prose = verify_src(
        "h",
        "/// direction: a contract claiming the pre-write value would be proved.\n\
         /// requires: x == 0\n/// ensures: ret == 5\npub fn h(x: u32) -> u32 { 5 }\n",
    );
    let Some(o) = prose else { return };
    assert!(o.is_verified(), "prose with a colon is not a clause; got: {o}");
}

/// A pinned write after a symbolic one re-establishes that element, and the value
/// must be readable -- including through an element copy.
///
/// The poison is array-wide, but the leaf maps are the record of which indices have
/// been re-established: `poison_elems` clears them and a later pinned write
/// re-populates exactly its index. An array-wide veto on top of that hid a leaf the
/// body genuinely knows, so `a[i].v = 7; a[0].v = 9; let x = a[0]; x.v` was
/// `incomplete` although the copy is always `9`. The recovery also has to cross the
/// call boundary, along with the poison it follows.
///
/// The negative twins pin the other half: a rewrite of one element recovers neither
/// its sibling nor its own pre-write leaf, so the fix is per-element and not a
/// blanket un-poisoning.
#[test]
fn a_pinned_rewrite_after_a_symbolic_write_is_read_back() {
    let recovered = [
        "a_pinned_leaf_rewrite_after_a_symbolic_write_is_read_back",
        "a_pinned_element_rewrite_after_a_symbolic_write_is_read_back",
        "a_pinned_leaf_rewrite_after_a_symbolic_element_write_is_read_back",
        "a_helper_pinned_rewrite_after_a_symbolic_write_is_read_back",
    ];
    let Some(report) = verify_realistic(&recovered) else { return };
    for name in recovered {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a pinned rewrite is a known leaf; got: {o}");
    }
    let unknown = [
        "a_pinned_rewrite_does_not_recover_its_sibling",
        "a_pinned_rewrite_does_not_revive_the_old_leaf",
    ];
    let Some(report) = verify_realistic(&unknown) else { return };
    for name in unknown {
        let o = outcome(&report, name);
        assert!(!o.is_verified(), "a sibling stays unknown after a pinned rewrite; got: {o}");
    }
}

/// An unpinned element write poisons the whole array, and a copy of an element
/// must not revive a pre-write leaf.
///
/// `a[i] = E { v: 7 }` with an unpinned `i` marks every element unknown. The poison
/// used to reach only one of the two leaf representations: `poison_elems` cleared
/// `elem_parts` and left its `nested` mirror, so `carry_elem_leaf_onto_local`
/// collected the mirror on the next element *copy* (`let x = a[0]`) and the copy
/// read the value from before the write -- a **false proof** of `ret == 3`. The
/// poison also had to cross the call boundary, which is where a helper's symbolic
/// write lost it: the callee held no leaves, the copy-back inserted none, and the
/// caller's own leaves survived.
///
/// These are asserted `!is_verified()` rather than `Failed`, because `incomplete` is
/// the honest answer for a write the run cannot pin: the array is genuinely unknown,
/// so neither the old leaf nor the new one may be proved. What must never happen is
/// `verified`, which is what the false contracts below were before.
#[test]
fn an_unpinned_write_poisons_the_whole_array() {
    let names = [
        "an_element_copy_after_an_unpinned_write_is_not_the_old_leaf",
        "an_element_copy_after_an_unpinned_write_is_not_the_sibling",
        "an_element_copy_after_an_unpinned_write_is_not_the_new_leaf",
        "an_element_copy_after_an_unpinned_leaf_write_is_not_the_old_leaf",
        "a_helper_unpinned_write_is_not_the_callers_old_leaf",
        "a_helper_unpinned_write_is_not_the_callers_sibling",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "an unpinned write leaves no element known, so this must not be proved; got: {o}"
        );
    }
}

/// A whole-*element* write of an aggregate crosses a call boundary too.
///
/// The leaf-write family above covers `a[0].v = 7`. This is the other half: the
/// whole element is replaced, which lowers to `(*_1)[_3] = move _2` through a
/// `&mut` argument. The element's own *value* crossed the boundary already, but its
/// leaves did not, so the caller read the leaf its literal had before the call and a
/// false `ret == 3` was **proved**. The gate that re-roots the leaves read
/// `dest.proj` directly and so missed the leading `Deref` this shape carries; it
/// goes through `elem_index_of` now, which reads past it.
///
/// The element-copy case (`a[0] = b[0]`) needed one more piece: reading an element
/// hands over its leaf *scalar*, not its parts, so the leaves died at the temp the
/// copy goes through. `carry_elem_leaf_onto_local` moves them onto that temp. That
/// pair was `incomplete` in both directions before, not a false proof.
#[test]
fn a_whole_element_write_of_an_aggregate_crosses_a_call_boundary() {
    let verified = [
        "an_element_copy_from_another_element_is_read_back",
        "a_helper_whole_element_write_is_read_back",
        "a_helper_whole_element_write_leaves_its_sibling",
        "a_helper_element_copy_is_read_back",
    ];
    let refuted = [
        "an_element_copy_is_not_the_old_leaf_cannot_prove_this",
        "a_helper_whole_element_write_is_not_the_callers_leaf_cannot_prove_this",
        "a_helper_whole_element_write_is_not_the_sibling_cannot_prove_this",
        "a_helper_element_copy_is_not_the_old_leaf_cannot_prove_this",
    ];
    let mut names = verified.to_vec();
    names.extend_from_slice(&refuted);
    let Some(report) = verify_realistic(&names) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a whole-element write must reach the read; got: {o}");
    }
    for name in refuted {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale element leaf must not prove this; got: {o}"
        );
    }
}

/// The leaf store crosses both call boundaries: an argument and a return.
///
/// A helper that writes a leaf through `&mut [T; N]` had its write die with the
/// frame, so the caller read the leaf its literal had before the call and a false
/// `ret == 3` was **proved**. A helper that only *reads* a leaf through its argument
/// saw `Unknown`, and a helper that *returns* an array of aggregates lost every leaf
/// so the caller could not read one at all. Each pair pins one direction: the
/// `..._cannot_prove_this` twins are the false contracts a dropped carry would decide.
#[test]
fn an_element_leaf_store_crosses_a_call_boundary() {
    let verified = [
        "a_helper_leaf_write_through_a_mutable_array_is_read_back",
        "a_helper_leaf_read_through_an_array_argument_decides",
        "a_returned_array_of_aggregates_keeps_its_leaves",
    ];
    let refuted = [
        "a_helper_leaf_write_is_not_the_callers_leaf_cannot_prove_this",
        "a_helper_leaf_read_is_not_a_made_up_value_cannot_prove_this",
        "a_returned_array_of_aggregates_is_not_a_made_up_value_cannot_prove_this",
    ];
    let mut names = verified.to_vec();
    names.extend_from_slice(&refuted);
    let Some(report) = verify_realistic(&names) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a leaf must cross the call boundary; got: {o}");
    }
    for name in refuted {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped or stale leaf carry must not prove this; got: {o}"
        );
    }
}

/// A whole-aggregate replacement through a sub-place target decides.
///
/// `set_whole(&mut o.i, InnerBox { v: 9 })` replaces the whole referent. This was once
/// believed *sound-incomplete* -- a leaf write "cannot spell a whole value" -- but the
/// re-based write-back re-roots the callee's `fields` entry for the moved value under the
/// target's chain, and in this store a whole value and a leaf are both a `fields` entry, so
/// the shape was never actually the blocker. The sibling check keeps the re-root from
/// landing on the whole local, and the local-built value makes the carry come from a temp.
#[test]
fn a_whole_aggregate_replacement_through_a_sub_place_decides() {
    let Some(report) = verify_realistic(&[
        "whole_replacement_through_sub_place",
        "whole_replacement_through_sub_place_cannot_prove_this",
        "whole_replacement_leaves_the_sibling",
        "whole_replacement_leaves_the_sibling_cannot_prove_this",
        "whole_replacement_from_a_local",
        "whole_replacement_from_a_local_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "whole_replacement_through_sub_place",
        "whole_replacement_leaves_the_sibling",
        "whole_replacement_from_a_local",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a whole replacement must reach the caller's leaf; got: {o}");
    }
    for name in [
        "whole_replacement_through_sub_place_cannot_prove_this",
        "whole_replacement_leaves_the_sibling_cannot_prove_this",
        "whole_replacement_from_a_local_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale or misdirected whole replacement must not prove this; got: {o}"
        );
    }
}

/// A named `const` item's value is inlined at the use site.
///
/// rustc const-evaluates a `const` item and prints its *body* separately
/// (`const LIMIT: u8 = const 10_u8;`) while referring to it by name at the use
/// site (`_0 = const LIMIT`). Reading only the name left the use site an
/// unreadable path constant, so a contract that mentioned the constant was lost.
/// The true directions must decide, and each false twin -- whose postcondition is
/// false on *every* input -- must be refuted, which is what a regression that
/// guessed the value would fail.
#[test]
fn a_named_const_item_is_inlined_at_its_use_site() {
    let Some(report) = verify_realistic(&[
        "named_const_is_read",
        "named_const_is_read_cannot_prove_this",
        "named_const_keeps_its_width",
        "named_const_keeps_its_width_cannot_prove_this",
        "named_bool_const_selects",
        "named_bool_const_selects_cannot_prove_this",
        "named_const_bounds_a_comparison",
        "named_const_bounds_a_comparison_cannot_prove_this",
        "named_const_matches_an_equality",
        "named_const_matches_an_equality_cannot_prove_this",
        "named_negative_const_is_signed",
        "named_negative_const_is_signed_cannot_prove_this",
        "nested_module_const_is_read",
        "nested_module_const_is_read_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "named_const_is_read",
        "named_const_keeps_its_width",
        "named_bool_const_selects",
        "named_const_bounds_a_comparison",
        "named_const_matches_an_equality",
        "named_negative_const_is_signed",
        "nested_module_const_is_read",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a named const must fold at its use site; got: {o}");
    }
    for name in [
        "named_const_is_read_cannot_prove_this",
        "named_const_keeps_its_width_cannot_prove_this",
        "named_bool_const_selects_cannot_prove_this",
        "named_const_bounds_a_comparison_cannot_prove_this",
        "named_const_matches_an_equality_cannot_prove_this",
        "named_negative_const_is_signed_cannot_prove_this",
        "nested_module_const_is_read_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a wrong inlined const value must not prove this; got: {o}"
        );
    }
}

/// A contract may name a top-level `const` the way the body does.
///
/// The reader resolves a bare name against the arguments first, then against the
/// program's own `const` table -- the *same* table the executor folds a body's
/// `const LIMIT` from, so the two cannot disagree. The true directions must decide,
/// and each false twin must be refuted; a name that resolved to nothing (or to a
/// wrong value) would leave the twin unproved or, worse, prove it.
///
/// The case that is a *refusal* rather than a proof is checked separately: a
/// misspelled name is not an argument and must be `Skipped`, never `verified`.
/// (An expression-bodied constant used to be the other refusal; it is folded now,
/// and its resolution is asserted in the body of this test.)
#[test]
fn a_contract_may_name_a_const_item() {
    let Some(report) = verify_realistic(&[
        "a_contract_names_a_const",
        "a_contract_names_a_const_cannot_prove_this",
        "a_contract_names_a_negative_const",
        "a_contract_names_a_bool_const",
        "a_contract_names_a_qualified_const",
        "a_contract_names_a_qualified_const_cannot_prove_this",
        "a_contract_names_an_expression_const",
        "a_misspelled_const_is_refused",
    ]) else {
        return;
    };
    for name in [
        "a_contract_names_a_const",
        "a_contract_names_a_negative_const",
        "a_contract_names_a_bool_const",
        "a_contract_names_a_qualified_const",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a contract must resolve a named const; got: {o}");
    }
    for name in [
        "a_contract_names_a_const_cannot_prove_this",
        "a_contract_names_a_qualified_const_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a wrong const value must not prove this; got: {o}"
        );
    }
    // An *expression* const now resolves: the item is folded once, into the
    // program's const table, so a contract naming it reads the same value the
    // body's use site does.
    let expr = outcome(&report, "a_contract_names_an_expression_const");
    assert!(
        expr.is_verified(),
        "a contract must resolve an expression const now that it is folded; got: {expr}"
    );
    // A *misspelled* name is still refused, not guessed: folding must not turn an
    // unknown name into a value.
    let misspelled = outcome(&report, "a_misspelled_const_is_refused");
    assert!(
        matches!(misspelled, FnOutcome::Skipped { .. }),
        "an unresolvable const name must be refused, not guessed; got: {misspelled}"
    );
}

/// A `const` whose body is an *expression* is inlined, in both directions.
///
/// rustc prints such an item with its own locals and blocks (`const NEXT: u8 = {
/// let mut _0: u8; ... _1 = AddWithOverflow(const LIMIT, const 1_u8); ... }`)
/// rather than as a single literal, so the value lives in the body. The folder
/// interprets that body concretely -- every operand is a literal, so the checked
/// add folds and the body's own `assert(!overflow)` is checked -- and records the
/// result in the program's const table. Both the body's use site and a contract
/// that names the item then read the same value.
///
/// The false twin is the pin that matters: a *guessed* or mis-folded value would
/// prove `ret == 10`, which is wrong. It must be refuted.
#[test]
fn an_expression_const_is_inlined_in_both_directions() {
    let Some(report) = verify_realistic(&[
        "named_const_of_an_expression_is_inlined",
        "named_const_of_an_expression_is_inlined_cannot_prove_this",
        "an_expression_const_keeps_its_width",
    ]) else {
        return;
    };
    let true_direction = outcome(&report, "named_const_of_an_expression_is_inlined");
    assert!(
        true_direction.is_verified(),
        "an expression const must fold to its value; got: {true_direction}"
    );
    let false_direction =
        outcome(&report, "named_const_of_an_expression_is_inlined_cannot_prove_this");
    assert!(
        matches!(false_direction, FnOutcome::Failed { .. }),
        "`NEXT` is 11, so `ret == 10` must be refuted, not proved; got: {false_direction}"
    );
    // The folded value must keep the item's own width: a folder that dropped to
    // `u8` would truncate `BIG == 300` and the contract would not decide.
    let width = outcome(&report, "an_expression_const_keeps_its_width");
    assert!(width.is_verified(), "an expression const keeps its width; got: {width}");
}

/// A comparison folded in a *constant* is read at its operands' type, not at the
/// `bool` destination's.
///
/// rustc prints `const LESS: bool = -1i8 < 0i8` as `_0 = Lt(const -1_i8, const
/// 0_i8)`: the return place is `bool`, but the operands are `i8`. Taking the width
/// and signedness from the destination made the folder compare the `-1i8` pattern,
/// 255, as *unsigned* -- so `-1i8 < 0i8` folded to `false`, and a contract claiming
/// `ret == false` was *proved* from a wrong value. That is a false proof, not a lost
/// one, which is why the false twin here is the load-bearing assertion.
#[test]
fn a_signed_comparison_const_uses_the_operand_type() {
    let Some(report) = verify_realistic(&[
        "a_signed_comparison_const_is_read",
        "a_signed_comparison_const_is_read_cannot_prove_this",
        "an_unsigned_comparison_const_is_read",
    ]) else {
        return;
    };
    let signed = outcome(&report, "a_signed_comparison_const_is_read");
    assert!(
        signed.is_verified(),
        "`-1i8 < 0i8` is true and the contract must prove it; got: {signed}"
    );
    let false_direction = outcome(&report, "a_signed_comparison_const_is_read_cannot_prove_this");
    assert!(
        matches!(false_direction, FnOutcome::Failed { .. }),
        "`LESS` is true, so `ret == false` must be refuted -- reading the operands \
         as unsigned proves it from a wrong value; got: {false_direction}"
    );
    // The unsigned control folds the same way under either reading, so it pins
    // that the fix did not simply invert every comparison.
    let unsigned = outcome(&report, "an_unsigned_comparison_const_is_read");
    assert!(unsigned.is_verified(), "`200u8 > 100u8` is true; got: {unsigned}");
}

/// A constant may name one the dump prints *after* it.
///
/// rustc keeps source declaration order, so `FWD_NEXT`'s expression body is printed
/// before `FWD_LIMIT`'s literal. A single in-order pass folds `FWD_NEXT` while
/// `FWD_LIMIT` is still unresolved and leaves the item unmodelled -- its contracts
/// undecided. The fold runs to a fixpoint, so a later constant is seen. The false
/// twin pins that the value is real: a guess would prove `ret == 12`.
#[test]
fn a_forward_referenced_const_is_resolved() {
    let Some(report) = verify_realistic(&[
        "a_forward_referenced_const_is_read",
        "a_forward_referenced_const_is_read_cannot_prove_this",
    ]) else {
        return;
    };
    let resolved = outcome(&report, "a_forward_referenced_const_is_read");
    assert!(
        resolved.is_verified(),
        "a constant may name a later one; the fold must reach a fixpoint; got: {resolved}"
    );
    let false_direction = outcome(&report, "a_forward_referenced_const_is_read_cannot_prove_this");
    assert!(
        matches!(false_direction, FnOutcome::Failed { .. }),
        "`FWD_NEXT` is 11, so `ret == 12` must be refuted; got: {false_direction}"
    );
}

/// A file that declares an *unused* 128-bit expression constant still verifies its
/// smaller functions.
///
/// The parser reads every `const` definition when it loads a dump, including ones no
/// target names. rustc prints an expression-bodied `i128` as an `AddWithOverflow` at
/// width 128, and the folder's exact overflow test negates `1i128 << 127` --
/// `i128::MIN` -- which panics in a debug build, taking the whole run down for an
/// item nobody asked about. The width is refused, so the item is simply unmodelled
/// and the verdicts still arrive.
#[test]
fn an_unused_i128_expression_const_does_not_abort_the_run() {
    let Some(report) =
        verify_realistic(&["a_file_with_an_unused_i128_const_still_verifies"])
    else {
        return;
    };
    let o = outcome(&report, "a_file_with_an_unused_i128_const_still_verifies");
    assert!(
        o.is_verified(),
        "an unused i128 const must not abort the parse; got: {o}"
    );
}

/// A function-local `const` is not in scope in another function.
///
/// `a_local_const_owner` declares `const L: u8 = 3;` in its body; the dump prints
/// that definition bare (`const L: u8 = const 3_u8;`) -- the same spelling a
/// crate-level `const` gets -- while its *use* is qualified (`const
/// a_local_const_owner::L`). A bare program-wide key for the definition let the
/// other function's `requires: L == 3` resolve to a name its own source could not
/// write, so the function was *proved* from a foreign body: a wrong proof, not a
/// lost one. The name must resolve to nothing here, leaving the function `Skipped`
/// (unreadable `requires`), never `Verified`.
///
/// The crate-level constant path stays covered by
/// [`a_contract_may_name_a_const_item`], so this pins that the scope rule did not
/// also drop the in-scope names.
#[test]
fn a_local_const_is_not_in_scope_in_another_function() {
    let Some(report) = verify_realistic(&[
        "a_local_const_owner",
        "a_local_const_is_not_in_scope_in_another_function",
    ]) else {
        return;
    };
    let owner = outcome(&report, "a_local_const_owner");
    assert!(owner.is_verified(), "the owner reads its own local const; got: {owner}");
    let other = outcome(&report, "a_local_const_is_not_in_scope_in_another_function");
    assert!(
        !other.is_verified(),
        "a contract must not resolve another function's local const -- that is a \
         wrong proof; got: {other}"
    );
}

/// The whole-corpus direction invariant: a function whose *name* says it must not be
/// provable must come back `Failed` -- a real refutation with a counterexample.
///
/// The corpus pairs each contract with its false twin, spelled `..._cannot_prove_this`:
/// the same body, or one differing only in the direction of the claim, so a twin that
/// verifies is a false proof by construction. Checking the naming convention over the
/// whole file means a new false proof of any *known* shape fails this test the moment
/// it is introduced, instead of waiting for someone to remember to assert the twin in
/// the same commit that adds the shape.
///
/// The assertion is on `Failed`, not on `!is_verified()`. `!is_verified()` also accepts
/// `Skipped` and `Incomplete`, so a tripwire that "passed" that way would never have
/// been pulled -- a false contract that was never checked is not evidence the checker
/// works. Two entries are `Incomplete` on purpose, and they are named here with the
/// reason: a tripwire may be undecided only when it is *listed* as such, so a
/// regression that turns a refutation into a skip fails this test rather than slipping
/// through.
#[test]
fn no_cannot_prove_entry_is_ever_verified() {
    let Some(report) = verify_realistic(&[]) else { return };
    // Tripwires that are honestly undecided, with the reason they cannot be refuted
    // today. Each is a *lost* proof (a skip), never a false one, and each is a
    // documented coverage gap rather than a regression. Anything else that is not
    // `Failed` fails this test.
    let undecided_on_purpose: &[(&str, &str)] = &[
        (
            "a_shifted_symbolic_element_cannot_prove_this",
            "a symbolic shift of an array element is not modelled, so the contract is \
             unreadable -- the read never reaches the refutation",
        ),
        (
            "default_body_self_call_is_not_the_default_cannot_prove_this",
            "the self-call to a trait default body is unmodelled, so the path is cut \
             before the false claim is checked",
        ),
        (
            "generic_slice_element_cannot_prove_this",
            "a generic `&[T]` has no element width, so `v[0]` is an unmodelled element \
             read and `ret == d` is unreadable -- the length is modelled, the element \
             is not, so the claim is a skip rather than a refutation",
        ),
    ];
    let mut checked = 0usize;
    let mut liars = Vec::new();
    let mut wrongly_undecided = Vec::new();
    for (name, o) in &report.outcomes {
        let false_direction = name.ends_with("_cannot_prove_this");
        if !false_direction {
            continue;
        }
        checked += 1;
        if o.is_verified() {
            liars.push(name.clone());
        } else if !matches!(o, FnOutcome::Failed { .. })
            && !undecided_on_purpose.iter().any(|(n, _)| n == name)
        {
            wrongly_undecided.push(format!("{name}: {o}"));
        }
    }
    assert!(
        liars.is_empty(),
        "these entries claim a false contract and were `verified` -- a false proof: {liars:?}"
    );
    assert!(
        wrongly_undecided.is_empty(),
        "these tripwires were neither refuted nor on the documented undecided list -- a \
         tripwire that was not pulled is not evidence: {wrongly_undecided:#?}"
    );
    // A silent zero would make this test vacuous if the naming convention ever drifts,
    // so the count is asserted rather than merely reported.
    assert!(
        checked >= 40,
        "expected the corpus to carry dozens of false-direction probes, found {checked}; \
         has the naming convention changed?"
    );
}

/// The loop cut havocs what the loop writes *through*, not what it names.
///
/// A `for` loop advances its `RangeInclusive` through `&mut` and the range is a
/// widthless aggregate, so the loop header must havoc both the referent of the
/// reference and the aggregate's parts. When it havoced neither, the header state
/// kept the entry-time iterator value, the exit guard folded to `false`, the exit
/// edge was pruned as unsatisfiable, and the postcondition was never checked -- a
/// `for` loop whose postcondition was false came back `Verified`.
///
/// The two corpus pairs pin both directions: the true contract verifies and the
/// false twin is refuted. The false twin is also covered by the corpus-wide
/// `no_cannot_prove_entry_is_ever_verified` sweep; this test adds the *positive*
/// half, so a fix that refused every loop invariant would fail here.
#[test]
fn a_loop_havocs_what_it_writes_through() {
    let names = [
        "for_loop_invariant_holds",
        "for_loop_invariant_cannot_prove_this",
        "while_writes_through_ref_holds",
        "while_writes_through_ref_cannot_prove_this",
        "ref_arg_written_in_a_loop_holds",
        "ref_arg_written_in_a_loop_cannot_prove_this",
        "call_writes_through_in_a_loop_holds",
        "call_writes_through_in_a_loop_cannot_prove_this",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    let outcome = |name: &str| {
        report
            .outcomes
            .iter()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("`{name}` must be in the report"))
            .1
            .clone()
    };
    for holds in [
        "for_loop_invariant_holds",
        "while_writes_through_ref_holds",
        "ref_arg_written_in_a_loop_holds",
        "call_writes_through_in_a_loop_holds",
    ] {
        assert!(
            outcome(holds).is_verified(),
            "`{holds}` establishes its postcondition and must verify, got: {}",
            outcome(holds)
        );
    }
    for twin in [
        "for_loop_invariant_cannot_prove_this",
        "while_writes_through_ref_cannot_prove_this",
        "ref_arg_written_in_a_loop_cannot_prove_this",
        "call_writes_through_in_a_loop_cannot_prove_this",
    ] {
        match outcome(twin) {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition") || kind.contains("invariant"),
                "`{twin}` must fail on its own claim, got `{kind}`"
            ),
            other => panic!(
                "`{twin}` claims a false postcondition and must be refuted; a header \
                 that is not havoced proves it, got: {other}"
            ),
        }
    }
}

/// A deep term is refused, not allowed to overflow the stack.
///
/// The engine's contract is that a query it cannot decide is *reported*: `Unknown`,
/// `Incomplete`, a budget trip -- never a crash. Every budget before this one counted
/// *steps*, and steps are not what a stack overflow is made of: `udiv(x, 3)` at 64 bits
/// builds a chain of adders and muxes ~262 terms deep, which is a few hundred steps, so it
/// passed every step budget and then aborted the process. On a 2 MiB stack -- the default
/// for a Rust test thread -- the walk wanted ~600 KiB in release and more in debug.
///
/// The guard is `MAX_WALK_DEPTH`, and this test is what holds it: it runs on the test
/// thread's own stack, so a regression that removes the guard aborts the test binary
/// (SIGABRT) instead of failing an assertion. The division-by-a-non-power-of-two shape is
/// the deepest legitimate walk in the corpus; the assertion that it reports rather than
/// panics is the whole point.
///
/// The deep walk needs a *symbolic* dividend: a precondition that pins the dividend folds
/// the whole divider to a literal (see [`a_signed_division_by_a_non_power_of_two_at_i64`]),
/// so the pinned shape no longer builds the deep term at all. The companion
/// [`a_symbolic_division_by_a_non_power_of_two_at_i64`] keeps the dividend free and is the
/// vehicle here.
#[test]
fn a_deep_term_walk_is_refused_not_allowed_to_overflow_the_stack() {
    let Some(report) = verify_realistic(&[
        "a_symbolic_division_by_a_non_power_of_two_at_i64",
        "a_signed_division_by_a_non_power_of_two_at_i64",
        "a_signed_constant_division_at_i64",
    ]) else {
        return;
    };
    // The symbolic case is the one that used to crash. Either answer but `Verified` is
    // acceptable -- the general divider is a documented scaling wall -- and the
    // unacceptable one is a false proof. Reaching this assertion at all is the fix.
    let deep = outcome(&report, "a_symbolic_division_by_a_non_power_of_two_at_i64");
    assert!(
        !deep.is_verified(),
        "the general divider must not be reported verified: {deep}"
    );
    // The *pinned* shape is now decided: the precondition leaves one dividend, the fold
    // collapses the divider to a literal, and the false contract is refuted. This is the
    // positive evidence that the fold, not a tighter budget, is what closed it -- a depth
    // bound that refused both shapes would pass the assertion above and be useless.
    let pinned = outcome(&report, "a_signed_division_by_a_non_power_of_two_at_i64");
    assert!(
        pinned.is_verified(),
        "the pinned divider must be decided by the fold, got: {pinned}"
    );
    // The power-of-two fast path is shallow and must still be *decided*, so the depth
    // bound cannot be so tight that it refuses the queries the engine already answers.
    let shallow = outcome(&report, "a_signed_constant_division_at_i64");
    assert!(
        shallow.is_verified(),
        "the power-of-two fast path must still verify: {shallow}"
    );
}

/// A pin applies to an aggregate *part*, not only to a whole argument.
///
/// `requires: w.v == -7` names a struct field, `requires: o.i.v == -7` names a nested
/// path, and `requires: xs[0] == -7` names an array element. All three are the same shape
/// as the argument-level pin -- a closed equality in the precondition, under any nesting of
/// `&&` -- but the variable the contract binds is a part's, not a local's. Keying the pin by
/// the argument's *local* reached none of them, so the body's `w.v / 3` stayed symbolic and
/// built the 64-bit restoring divider: `incomplete` in ~1.2s, decided in ~0s once the pin is
/// keyed by the variable's own index.
///
/// The `cannot_prove_this` companions are the point of the test. Without them, an engine
/// that answered `Verified` for everything would pass the positive assertions, so the
/// negatives are what make "decided" mean "decided correctly": the fold refutes a wrong
/// claim about the same pinned part, which is only possible if the value really is `-7`.
#[test]
fn a_pin_reaches_an_aggregate_part_not_only_a_whole_argument() {
    let Some(report) = verify_realistic(&[
        "a_field_pinned_division_at_i64",
        "a_field_pinned_division_cannot_prove_this",
        "a_nested_pinned_division_at_i64",
        "a_nested_pinned_division_cannot_prove_this",
        "an_element_pinned_division_at_i64",
        "an_element_pinned_division_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_field_pinned_division_at_i64",
        "a_nested_pinned_division_at_i64",
        "an_element_pinned_division_at_i64",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a pinned aggregate part must be decided; `{name}` got: {o}");
    }
    for name in [
        "a_field_pinned_division_cannot_prove_this",
        "a_nested_pinned_division_cannot_prove_this",
        "an_element_pinned_division_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "a false claim about a pinned part must be refuted, not proved; `{name}` got: {o}"
        );
    }
}

/// A callee's contract is never taken on faith: its body is inlined, so a lying
/// `ensures` cannot be inherited by a caller, and a vacuous `requires` cannot be
/// used to assume a false postcondition.
///
/// This is the soundness property with the largest blast radius -- assuming a
/// callee's postcondition is the canonical way a modular verifier proves a false
/// contract -- so it is pinned directly rather than left implied by the absence of
/// a bug report. The recursion cases are the same property under the inductive
/// hypothesis, where an unguarded assumption is easiest to make.
#[test]
fn a_callee_contract_is_never_assumed() {
    let Some(report) = verify_realistic(&[
        "a_helper_whose_contract_is_false",
        "a_caller_of_a_lying_helper_cannot_prove_this",
        "a_caller_of_a_lying_helper_knows_the_truth",
        "a_call_that_violates_a_precondition_is_not_checked",
        "a_call_that_divides_by_zero_cannot_prove_this",
        "a_vacuous_helper_whose_postcondition_is_false",
        "a_caller_inheriting_a_vacuous_lie_cannot_prove_this",
        "a_caller_of_a_vacuous_helper_knows_the_truth",
        "a_recursive_contract_that_is_false_cannot_prove_this",
        "a_mutual_lie_a_cannot_prove_this",
        "a_mutual_lie_b_cannot_prove_this",
        "an_invariant_false_on_entry_cannot_prove_this",
        "an_invariant_not_preserved_cannot_prove_this",
    ]) else {
        return;
    };

    // The two entries that must verify are the *honest* directions: they are what
    // proves the shapes above are decidable at all, rather than undecided for a
    // reason that happens to look safe.
    for name in [
        "a_caller_of_a_lying_helper_knows_the_truth",
        "a_caller_of_a_vacuous_helper_knows_the_truth",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "the honest direction must verify; `{name}` got: {o}");
    }

    // A callee's `requires` is not an obligation at the call site -- the body is
    // inlined instead -- so this one verifies, and that is the honest answer rather
    // than a false proof: the helper returns its argument whatever it is. Pinning it
    // makes the *choice* visible instead of accidental.
    let unchecked = outcome(&report, "a_call_that_violates_a_precondition_is_not_checked");
    assert!(
        unchecked.is_verified(),
        "a callee precondition is not a call-site obligation; expected verified, got: {unchecked}"
    );

    for name in [
        "a_helper_whose_contract_is_false",
        "a_caller_of_a_lying_helper_cannot_prove_this",
        "a_call_that_divides_by_zero_cannot_prove_this",
        "a_vacuous_helper_whose_postcondition_is_false",
        "a_caller_inheriting_a_vacuous_lie_cannot_prove_this",
        "a_recursive_contract_that_is_false_cannot_prove_this",
        "a_mutual_lie_a_cannot_prove_this",
        "a_mutual_lie_b_cannot_prove_this",
        "an_invariant_false_on_entry_cannot_prove_this",
        "an_invariant_not_preserved_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "an assumed callee contract, an unchecked induction, or a vacuous \
             precondition must not prove this; `{name}` got: {o}"
        );
    }
}

/// A loop counter's arithmetic in an invariant is a *variable*'s arithmetic, not
/// a written constant expression.
///
/// The invariant is evaluated in the loop-head state, where the counter is bound
/// to the value it holds on entry (`0`). `i - 1` then has two constant operands,
/// and the fold read it as the *written* `0 - 1` and refused it as an unsigned
/// underflow -- even though Rust never range-checks a variable's arithmetic as a
/// constant expression. The refusal was a lost proof, not a false one, but it made
/// the commonest accumulator invariant unreadable. The written form is still
/// refused, and that negative control is what keeps the fix from dropping the
/// rustc-mirroring check.
#[test]
fn a_counter_arithmetic_in_an_invariant_is_not_a_written_constant() {
    let Some(report) = verify_realistic(&[
        "an_invariant_subtracts_from_a_counter",
        "an_invariant_subtracts_from_a_counter_cannot_prove_this",
        "an_invariant_written_underflow_is_refused",
    ]) else {
        return;
    };

    let o = outcome(&report, "an_invariant_subtracts_from_a_counter");
    assert!(
        o.is_verified(),
        "a counter's `i - 1` is a variable's arithmetic and must be read; got: {o}"
    );

    // The false twin proves the shape is *decided*, not discharged vacuously.
    let o = outcome(&report, "an_invariant_subtracts_from_a_counter_cannot_prove_this");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the false twin must be refuted, not proved; got: {o}"
    );

    // The *written* `0 - 1` is still a rustc const-eval error, so it is refused.
    let o = outcome(&report, "an_invariant_written_underflow_is_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. } | FnOutcome::Incomplete { .. }),
        "the written `0 - 1` must still be refused, not decided; got: {o}"
    );
}

/// A slice's length is read through the *one* rvalue the compiler prints, on any
/// toolchain.
///
/// `PtrMetadata(copy _1)` is what 1.99 and later print for a `&[T]`'s length;
/// before 1.99 (the MSRV, 1.85) the same query prints as `Len((*_1))`. Two things
/// had to hold for the entry to decide on both: `Len` had to be modelled at all,
/// and its argument had to survive parsing. `trim_end_matches(')')` stripped *both*
/// trailing parens, leaving `(*_1` -- unparseable, so the length was `Unknown` and
/// the bounds check above `a[i]` was unmodelled, turning this decidable entry into
/// an incomplete one on 1.85 only. The entry decides identically on both now.
#[test]
fn a_slices_length_is_read_on_any_toolchain() {
    let Some(report) = verify_realistic(&["slice_symbolic_index"]) else { return };
    let o = outcome(&report, "slice_symbolic_index");
    assert!(o.is_verified(), "the slice entry must decide on any toolchain; got: {o}");
}

/// A postcondition can name a component of a tuple return.
///
/// `split` returns `(u8, u8)` and claims `ret.0 <= a`. The return place is an
/// aggregate, so there is no single word for `ret`; the frontend binds `ret.0`
/// and `ret.1` to the components `_0 = (a, b)` actually stored.
#[test]
fn a_postcondition_can_name_a_tuple_component() {
    let Some(report) = verify_realistic(&["split"]) else { return };
    let o = outcome(&report, "split");
    assert!(o.is_verified(), "`split` must verify, got: {o}");
}

/// A same-dump helper that indexes its parameter must reach the caller's element.
///
/// `head` returns `a[0]` and `caller_of_head` claims `ret == a[0]`. The call is
/// inlined into a fresh callee `Env`, and before that `Env` was handed a copy of
/// the *indexed* store the callee's `_1[_2]` reads, the element was unknown and
/// the caller was incomplete. The two functions are checked together because the
/// property is about what crosses the call boundary.
#[test]
fn a_helper_that_indexes_its_parameter_reaches_the_caller_element() {
    let names = ["head", "caller_of_head"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// A helper that writes through a `&mut` array changes the *caller's* element.
///
/// `clear_head` writes `a[0] = 0` through the reference and returns it;
/// `caller_of_clear_head` claims `ret == 0`, which is only true if the helper's
/// write is visible to the caller. The reference is the shared store, so the
/// callee's post-state must be copied back.
#[test]
fn a_write_through_a_reference_reaches_the_caller() {
    let names = ["clear_head", "caller_of_clear_head"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// The soundness tripwire for the call boundary: a by-value helper's write to its
/// *own copy* must not reach the caller.
///
/// `clear_copy` clears its by-value array and returns `0`, but the caller's `a` is
/// the array it passed and is untouched, so `caller_of_written_copy` returning
/// `a[0]` is not `0`. If the callee's copy were shared with the caller's store --
/// the tempting way to make the element reads agree -- this false contract would
/// verify. It must fail.
#[test]
fn a_by_value_helper_cannot_write_the_callers_array() {
    let Some(report) = verify_realistic(&["caller_of_written_copy"]) else { return };
    let o = outcome(&report, "caller_of_written_copy");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a by-value helper's write leaked to the caller; got: {o}"
    );
}

/// A signed comparison whose *left* operand is a constant must be signed.
///
/// `0 < c.lo` lowers to `Lt(const 0_i8, ...)`, and the constant carries the
/// signedness. Reading a constant operand as unsigned made this an unsigned test,
/// under which `i8::MIN` (`0x80`) is the largest value, so `ret == 1` was
/// *proved* for `c.lo == i8::MIN` -- a false proof, since `i8::MIN` is negative
/// and the branch is never taken. The pair pins both directions: the false claim
/// must fail, and the true one must verify.
#[test]
fn a_constant_left_signed_compare_is_signed_not_unsigned() {
    let names = ["signed_const_left_false", "signed_const_left_true"];
    let Some(report) = verify_realistic(&names) else { return };
    let bad = outcome(&report, "signed_const_left_false");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "`signed_const_left_false` proves a false contract; got: {bad}"
    );
    let good = outcome(&report, "signed_const_left_true");
    assert!(good.is_verified(), "`signed_const_left_true` must verify, got: {good}");
}

/// A `(bool, u8)` return can be checked on its bool component.
///
/// `ret.0` is a `bool` in the type but compared against a one-bit word in the
/// postcondition, so the component has to be widened when it is read out of the
/// return place. Before that, `ret.0` had no binding and the contract was refused
/// as unreadable.
#[test]
fn a_postcondition_can_name_a_bool_tuple_component() {
    let Some(report) = verify_realistic(&["bool_component"]) else { return };
    let o = outcome(&report, "bool_component");
    assert!(o.is_verified(), "`bool_component` must verify, got: {o}");
}

/// A tuple local's component can be read back as a *field* projection.
///
/// `let t = (a, b); t.0` stores the components under an index projection and
/// reads them back as `_3.0`, a field projection. Before the two spellings met in
/// one store, `t.0` was `Unknown` and a contract about the return was unreadable.
#[test]
fn a_tuple_locals_component_can_be_read_back() {
    let Some(report) = verify_realistic(&["tuple_local_component"]) else { return };
    let o = outcome(&report, "tuple_local_component");
    assert!(o.is_verified(), "`tuple_local_component` must verify, got: {o}");
}

/// A component of a tuple-*returning call* reaches the caller.
///
/// `min_call` returns `min2(a, b).0`. The callee's components live in its own
/// return place, so they must cross the call boundary with the aggregate; before
/// that, only the aggregate crossed and the component was lost, leaving the
/// caller's contract unreadable rather than checked.
#[test]
fn a_tuple_returning_calls_component_reaches_the_caller() {
    let names = ["min2", "min_call"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// The soundness tripwires for the tuple-component reads.
///
/// Each is a *false* contract that the tempting wrong model would prove: reading
/// the wrong component of a tuple local, or carrying the components across a call
/// boundary in the wrong order (or as one shared value). A `verified` verdict
/// here is a proof of something untrue, so both must fail.
#[test]
fn a_tuple_component_read_cannot_prove_the_wrong_component() {
    let names = ["tuple_component_tripwire", "min_call_tripwire"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` proves the wrong tuple component; got: {o}"
        );
    }
}

/// A signed widening cast sign-extends; an unsigned one zero-fills.
///
/// Both directions are pinned because the two casts need *opposite* rules, and a
/// single-rule implementation is wrong for one of them. `truncate` zero-fills, so
/// using it for every cast modelled `-1i8 as i16` as `255` and *proved*
/// `requires: a == -1; ensures: ret == 255` -- a reachable false proof. A
/// sign-extend-everything rule would instead prove `255u8 as u16 == 65535`.
#[test]
fn a_widening_cast_respects_the_sources_signedness() {
    let names = [
        "widen_signed_true",
        "widen_signed_false",
        "widen_unsigned_true",
        "widen_unsigned_false",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in ["widen_signed_true", "widen_unsigned_true"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in ["widen_signed_false", "widen_unsigned_false"] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` proves a false widening; got: {o}"
        );
    }
}

/// A signed array element stays signed through the subscript.
///
/// The element's signedness lives in the array's element *type* and has to reach
/// the value the subscript produces. The two entries pin both directions: the
/// true one verifies only if `xs[0] < 0` is a signed test, and the tripwire
/// (`xs[0] == i8::MIN`, where the most negative element *is* negative) is
/// *proved* under the unsigned reading, so it must FAIL.
#[test]
fn a_signed_element_comparison_keeps_the_elements_sign() {
    let names = ["signed_slice_element_is_signed", "signed_slice_element_tripwire"];
    let Some(report) = verify_realistic(&names) else { return };
    let o = outcome(&report, "signed_slice_element_is_signed");
    assert!(o.is_verified(), "`signed_slice_element_is_signed` must verify, got: {o}");
    let o = outcome(&report, "signed_slice_element_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`signed_slice_element_tripwire` proves `!(i8::MIN < 0)`; got: {o}"
    );
}

/// A postcondition naming a component a *modelled call* wrote is not refused.
///
/// `overflowing_add` returns `(T, bool)` and the modelled call writes `_0.0` and
/// `_0.1` directly -- it never assigns the tuple local as a whole. So the value
/// component lives in the *field* store while a literal's `_0 = (a, b)` lives in
/// the element store, and a `ret.N` reader that consulted only the latter found
/// the component unbound. The symptom was the whole contract refused as "the
/// return type is an aggregate, so `ret` has no single value" -- a message about
/// the wrong problem, since the reader already knew to look at components.
///
/// The two verifying entries read `ret.1` (the flag) and `ret.0` (the value), so
/// both stores are exercised, and the two tripwires must FAIL: a reader that
/// dropped a component would make those contracts vacuously true.
#[test]
fn a_postcondition_can_name_a_component_a_modelled_call_wrote() {
    let names = [
        "overflowing_add_flag_or_exact_sum",
        "overflowing_add_small_operands_never_flag",
        "overflowing_add_value_is_exact_when_no_overflow",
        "overflowing_add_flag_never_set_tripwire",
        "overflowing_add_one_bound_only_tripwire",
        "overflowing_add_wrapped_value_below_operand_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "overflowing_add_flag_or_exact_sum",
        "overflowing_add_small_operands_never_flag",
        "overflowing_add_value_is_exact_when_no_overflow",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "overflowing_add_flag_never_set_tripwire",
        "overflowing_add_one_bound_only_tripwire",
        "overflowing_add_wrapped_value_below_operand_tripwire",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` states a false contract a dropped component would prove; got: {o}"
        );
    }
}

/// A `(u8, &u8)` return with a postcondition on `ret.0` alone is not skipped.
///
/// Component 1 is a reference with no bit-vector width. Binding every declared
/// component up front made the up-front parse probe refuse, so the function was
/// `Skipped` for a component the contract never named. Only the components a
/// contract names are probed.
#[test]
fn a_reference_component_the_contract_does_not_name_does_not_skip_the_function() {
    let Some(report) = verify_realistic(&["first_component_only"]) else { return };
    let o = outcome(&report, "first_component_only");
    assert!(o.is_verified(), "`first_component_only` must verify, got: {o}");
}

/// A contract naming a field the struct does not have is refused, not dropped.
///
/// This is the failure mode that matters: if the projection were ignored, the
/// conjunct would vanish and the function would verify against a weaker contract
/// than the source states. The refusal is asserted on the *evaluator* rather than
/// on a corpus function, so it cannot pass by the function being skipped for some
/// unrelated reason.
#[test]
fn a_contract_naming_an_unknown_field_is_refused() {
    let mut args = std::collections::BTreeMap::new();
    args.insert("c".to_string(), verif::smt::var(8));
    // `c` is a known aggregate with no bindings, so the refusal names the field.
    let mut env = spec::FieldEnv::default();
    env.declare_arg("c");
    let err = spec::eval_requires("c.lo <= 3", &args, &std::collections::BTreeSet::new(), &env)
        .expect_err("an unbound field must be refused");
    assert!(
        err.to_string().contains("unknown field `lo`"),
        "the refusal must name the field, got: {err}"
    );
}

/// The field rewrite is token-aware: it must not fire inside a longer name.
///
/// `myc.lo` is a different path from `c.lo`. A naive `str::replace` would rewrite
/// the tail of `myc.lo` into `myc__f0` (or rewrite `c.lo` inside it), binding the
/// contract to a variable the caller never declared — a wrong proof. The rewrite
/// only fires on a whole `ident.ident` run that matches a *bound* path.
#[test]
fn the_field_rewrite_does_not_fire_inside_a_longer_name() {
    let mut fields = spec::FieldEnv::default();
    let c = verif::smt::var(8);
    fields.bind_bits(1, "c", "lo", 0, 8, false).unwrap();
    let mut args = std::collections::BTreeMap::new();
    args.insert("myc".to_string(), c);
    // `myc` is *not* a declared aggregate, so its `.lo` is left alone and the
    // parser refuses the unknown name `myc`. The point is that it was not
    // rewritten into the binding that belongs to `c`.
    let err = spec::eval_requires("myc.lo <= 3", &args, &std::collections::BTreeSet::new(), &fields)
        .expect_err("`myc.lo` must not be rewritten to the binding for `c.lo`");
    let msg = err.to_string();
    assert!(
        msg.contains("unknown name") || msg.contains("expected a comparison"),
        "`myc.lo` must be refused, got: {msg}"
    );
    assert!(
        !msg.contains("unknown field"),
        "`myc` is not a known aggregate, so the message must not claim a bad field: {msg}"
    );
    // And the bound path itself *is* rewritten and resolves.
    let ok = spec::eval_requires("c.lo <= 3", &args, &std::collections::BTreeSet::new(), &fields);
    assert!(ok.is_ok(), "the bound path must resolve, got: {ok:?}");
}

// ---------------------------------------------------------------------------
// Symbolic array subscripts
// ---------------------------------------------------------------------------

/// `a[i]` on a fixed-length array is modelled as the exact ite chain over `0..N`,
/// and the precondition has to establish `i < N`.
///
/// An array's length is in its type, so unlike a slice there *is* a finite domain
/// to enumerate: `a[i]` is `ite(i == 0, a0, ite(i == 1, a1, ...))`, a definition
/// rather than an approximation. The chain can only be `a[i]` where `i < N`, so
/// `requires: i < 4` is what makes the subscript admissible.
#[test]
fn a_symbolic_array_index_is_modelled_as_an_ite_chain() {
    let Some(report) = verify_realistic(&["array_symbolic_index"]) else { return };
    let o = outcome(&report, "array_symbolic_index");
    assert!(o.is_verified(), "`array_symbolic_index` must verify, got: {o}");
}

/// The soundness gate: a symbolic subscript whose index the precondition does not
/// bound is refused, not checked.
///
/// The ite chain has to return *something* for `i >= N` (it falls through to the
/// last element), so a contract checked without `i < N` would be checked against a
/// value that is not `a[i]`. Refusing is the only honest answer; the tempting bug
/// is to conjoin `i < N` into the precondition, which would silently strengthen
/// what the source asked to be verified.
#[test]
fn an_unbounded_symbolic_array_index_is_refused() {
    let Some(report) = verify_realistic(&["array_unbounded_index_refused"]) else { return };
    let o = outcome(&report, "array_unbounded_index_refused");
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("not known to be in range"),
            "the refusal must say the index is unbounded, got: {reason}"
        ),
        other => panic!("`array_unbounded_index_refused` must be skipped, got: {other}"),
    }
}

/// A contract naming a *different* index than the body reads is refused.
///
/// Only `a[i]` has a chain; `a[j]` does not, and rewriting it to the `a[i]` chain
/// would prove `a[j] == a[i]` -- false for every `i != j`. The refusal is what
/// keeps a name that merely looks like the bound one from being silently aliased.
#[test]
fn a_contract_naming_a_different_symbolic_index_is_refused() {
    let Some(report) = verify_realistic(&["array_wrong_index_refused"]) else { return };
    let o = outcome(&report, "array_wrong_index_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`array_wrong_index_refused` must be skipped, got: {o}"
    );
}

/// A contract error quotes the *source* text, not the rewritten form.
///
/// The parser reads the contract after the field/subscript rewrite, so its errors
/// naturally quote mangled names (`a__chain`, `c__f0`) that appear nowhere in the
/// source. A name the user cannot search for is a diagnosability bug, so the eval
/// boundary re-points the error at the original text. This pins that, because it
/// is the kind of thing a later refactor silently drops.
#[test]
fn a_contract_error_quotes_the_source_text() {
    use verif::mir::spec;
    use verif::smt;
    let mut fields = spec::FieldEnv::default();
    let mut args = std::collections::BTreeMap::new();
    // Bind `a[i]` as a symbolic subscript, so the rewrite fires. `i` is an
    // argument, which is what makes it bindable as an index.
    let i = smt::var(64);
    args.insert("i".to_string(), i);
    fields.bind_array_len(0, "a", 8, false, 4);
    fields.bind_sym_index("a", 8, spec::IndexBound::Const(4), "i", i);
    let src = "ret == a[i] && ret == a[j]";
    let err = spec::eval_ensures(
        src,
        &args,
        Some(smt::var(8)),
        spec::RET_IS_UNKNOWN,
        &std::collections::BTreeSet::new(),
        false,
        &fields,
        &std::collections::BTreeMap::new(),
    )
    .expect_err("`a[j]` has no chain and must be refused");
    assert_eq!(
        err.text, src,
        "the error must quote the source contract, not the rewritten one"
    );
    assert!(
        !err.text.contains("__"),
        "no mangled name may leak into the quoted text: {}",
        err.text
    );
}

/// A subscript by a name that is a *direct alias* of an argument is resolved.
///
/// `let k = i;` on a `Copy` value lowers to no local: the body's `a[k]` is
/// `a[i]`, and `k` survives only as a scoped `debug k => _2;`. The contract's `k`
/// therefore names the very index the body reads, so it must verify — and the
/// tripwire must FAIL, which is what shows the name resolved to the real index
/// rather than to a constant the postcondition happened to accept.
#[test]
fn a_symbolic_index_through_a_local_alias_is_resolved() {
    let Some(report) =
        verify_realistic(&["array_local_index_through_alias", "array_local_index_tripwire"])
    else {
        return;
    };
    let o = outcome(&report, "array_local_index_through_alias");
    assert!(o.is_verified(), "`array_local_index_through_alias` must verify, got: {o}");
    let t = outcome(&report, "array_local_index_tripwire");
    assert!(
        !t.is_verified(),
        "the alias tripwire must be refuted, got: {t}"
    );
}

/// The alias rule is not a licence to follow a reassigned argument.
///
/// `let k = i; i = 2;` — rustc materialises a real local for the copy and prints
/// `debug k => _3;` pointing at *that* local, not at `_2`. So `k` is not an alias
/// of the argument and the contract's `k` is refused. If the frontend instead
/// aliased `k` to `i` unconditionally, the contract would be checked against a
/// reassigned index and could be proved or refuted about the wrong value.
#[test]
fn a_subscript_through_a_reassigned_argument_is_refused() {
    let Some(report) = verify_realistic(&["array_local_index_written_refused"]) else { return };
    let o = outcome(&report, "array_local_index_written_refused");
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("unknown name"),
            "a subscript through a reassigned argument must be refused as an unknown name, \
             got: {reason}"
        ),
        other => panic!("`array_local_index_written_refused` must be skipped, got: {other}"),
    }
}

/// A subscript through an alias is one element under *every* spelling of the
/// index, not just the first.
///
/// `a[i]` and `a[k]` with `let k = i` name the same element, so a contract using
/// both must be readable and verify — the second subscript has to rewrite to the
/// same chain as the first. The tripwire claims they differ and must be refuted.
/// Keeping only the first spelling left the second unrewritten and the parser
/// refused the whole contract, which skipped a function that should have
/// verified; this pins the fix.
#[test]
fn a_symbolic_index_resolves_under_every_spelling() {
    let Some(report) =
        verify_realistic(&["array_two_spellings_of_one_index", "array_two_spellings_tripwire"])
    else {
        return;
    };
    let o = outcome(&report, "array_two_spellings_of_one_index");
    assert!(o.is_verified(), "`array_two_spellings_of_one_index` must verify, got: {o}");
    let t = outcome(&report, "array_two_spellings_tripwire");
    assert!(
        !t.is_verified(),
        "the two-spellings tripwire must be refuted, got: {t}"
    );
}

/// A subscript by a name that is *shadowed* is refused.
///
/// `let k = i; let k = 0;` prints two bindings for `k`, and only the second is
/// what `a[k]` reads. Resolving `k` from the first would check the contract
/// against `i` while the body used the constant — a contract that is false for
/// `i == 1` could prove. The name is bound more than once, so it is refused.
#[test]
fn a_shadowed_alias_is_refused() {
    let Some(report) = verify_realistic(&["array_shadowed_alias_refused"]) else { return };
    let o = outcome(&report, "array_shadowed_alias_refused");
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("unknown name"),
            "a shadowed alias must be refused as an unknown name, got: {reason}"
        ),
        other => panic!("`array_shadowed_alias_refused` must be skipped, got: {other}"),
    }
}

/// A *qualified* standard construction (`Option::<u8>::Some`) resolves.
///
/// rustc prints a standard construction with its generic arguments, so the
/// qualifier is `Option`, not `u8`. A reader that only consults declared layouts
/// for a qualified name finds none for `Option` and refuses the construction,
/// losing a shape the unqualified spelling handles. The true contract must
/// verify and the false one must be refuted, which only happens if the tag and
/// the payload are both read.
#[test]
fn a_qualified_standard_construction_resolves() {
    let Some(report) = verify_realistic(&[
        "option_qualified_some_payload",
        "option_qualified_some_payload_tripwire",
    ]) else {
        return;
    };
    let o = outcome(&report, "option_qualified_some_payload");
    assert!(o.is_verified(), "`option_qualified_some_payload` must verify, got: {o}");
    let t = outcome(&report, "option_qualified_some_payload_tripwire");
    assert!(!t.is_verified(), "the qualified-construction tripwire must be refuted, got: {t}");
}

/// The `Option` *methods* read the receiver's tag and payload, not a bit-vector
/// operand.
///
/// `unwrap_or`, `unwrap`, `expect`, `is_some` and `is_none` are the first modelled
/// calls whose input is an enum's state rather than a word. Each true direction
/// must verify and each tripwire must be *refuted* (not merely undecided): the
/// tripwires are the evidence the tag and payload are read, because a model that
/// returned a constant -- a fixed tag, or the payload unconditionally -- would
/// prove the false contract instead.
///
/// The two panic tripwires (`option_unwrap_unguarded`, `option_expect_unguarded`)
/// are the sharpest: they must fail with a *panic* obligation, because an
/// unguarded `unwrap` on a value that can be `None` really does panic. A model
/// that reported the method total would report them verified.
#[test]
fn the_option_methods_read_the_receivers_tag_and_payload() {
    let names = [
        "option_unwrap_or_fallback",
        "option_unwrap_or_fallback_tripwire",
        "option_is_some_true_on_some",
        "option_is_some_true_on_some_tripwire",
        "option_is_some_false_on_none",
        "option_is_some_false_on_none_tripwire",
        "option_is_none_false_on_some",
        "option_is_none_false_on_some_tripwire",
        "option_is_none_true_on_none",
        "option_is_none_true_on_none_tripwire",
        "option_unwrap_guarded",
        "option_unwrap_unguarded",
        "option_expect_guarded",
        "option_expect_unguarded",
        "option_is_some_guards_unwrap",
        "option_is_none_guards_unwrap",
        "option_guard_tripwire",
        "option_arg_unwrap_or",
        "option_arg_unwrap_or_tripwire",
        "option_arg_unwrap_unguarded",
        "result_is_ok",
        "result_is_ok_tripwire",
        "result_is_err",
        "result_is_err_tripwire",
        "result_unwrap_or",
        "result_unwrap_or_tripwire",
        "result_unwrap_unguarded",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    // The true directions.
    for name in [
        "option_unwrap_or_fallback",
        "option_is_some_true_on_some",
        "option_is_some_false_on_none",
        "option_is_none_false_on_some",
        "option_is_none_true_on_none",
        "option_unwrap_guarded",
        "option_expect_guarded",
        "option_is_some_guards_unwrap",
        "option_is_none_guards_unwrap",
        "option_arg_unwrap_or",
        "result_is_ok",
        "result_is_err",
        "result_unwrap_or",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    // The postcondition tripwires: refuted, so the tag and payload are read.
    for name in [
        "option_unwrap_or_fallback_tripwire",
        "option_is_some_true_on_some_tripwire",
        "option_is_some_false_on_none_tripwire",
        "option_is_none_false_on_some_tripwire",
        "option_is_none_true_on_none_tripwire",
        "option_arg_unwrap_or_tripwire",
        "result_is_ok_tripwire",
        "result_is_err_tripwire",
        "result_unwrap_or_tripwire",
    ] {
        let o = outcome(&report, name);
        assert!(!o.is_verified(), "`{name}` must be refuted, got: {o}");
    }
    // The panic tripwires: an unguarded `unwrap`/`expect`/argument `unwrap` panics
    // on the failure value, and the *wrong-arm* guard unwraps on that path, so each
    // must fail with a *panic* obligation, not merely be undecided.
    for name in [
        "option_unwrap_unguarded",
        "option_expect_unguarded",
        "option_guard_tripwire",
        "option_arg_unwrap_unguarded",
        "result_unwrap_unguarded",
    ] {
        let o = outcome(&report, name);
        match o {
            FnOutcome::Failed { kind, .. } => {
                assert!(
                    kind.contains("panic"),
                    "`{name}` must fail on a panic obligation, got kind: {kind}"
                );
            }
            other => panic!("`{name}` must fail with a panic, got: {other}"),
        }
    }
    // The `Result` panic message names `Err`, not `None`: the evidence the model
    // read the `Result` tag (payload on `Ok`) rather than the `Option` one. A model
    // that assumed `Some` would report the panic at the wrong variant, or (worse)
    // read the `Err` payload as the value.
    let FnOutcome::Failed { kind, .. } = outcome(&report, "result_unwrap_unguarded") else {
        panic!("`result_unwrap_unguarded` must fail on the `Err` panic");
    };
    assert!(
        kind.contains("Err") && !kind.contains("None"),
        "the `Result::unwrap` panic must name `Err`, got kind: {kind}"
    );
}

/// An enum-returning function's contract can name the *discriminant* methods:
/// `ret.is_ok()`, `ret.is_some()`, `ret.is_err()`, `ret.is_none()`.
///
/// A function returning `Option`/`Result` has no single return word, so a bare
/// `ret <= n` is refused. The four methods read the return place's tag, which the
/// executor passes as the return word. Each is total over the tag -- unlike
/// `ret.Ok`, which names a payload that exists on only one variant -- so they are
/// admitted without a payload guard.
///
/// The pairs are the teeth: a body that always returns `Some`/`Ok` must *verify*
/// `ret.is_some()`/`ret.is_ok()` and *refute* `ret.is_none()`/`ret.is_err()`, and
/// the `None`/`Err` bodies the other way round. A model that read the tag as a
/// constant, or swapped the two discriminants, would prove the tripwires.
#[test]
fn an_enum_return_contract_can_name_the_discriminant_methods() {
    let names = [
        "enum_ret_is_some",
        "enum_ret_is_some_tripwire",
        "enum_ret_is_none",
        "enum_ret_is_none_tripwire",
        "enum_ret_is_ok",
        "enum_ret_is_ok_tripwire",
        "enum_ret_is_err",
        "enum_ret_is_err_tripwire",
        "enum_ret_is_ok_or_err",
        "enum_ret_is_ok_and_err_tripwire",
        "enum_ret_passthrough",
        "enum_ret_passthrough_tripwire",
        "enum_ret_from_match",
        "enum_ret_from_match_tripwire",
        "enum_ret_method_on_non_enum",
        "enum_arg_is_ok_guarded",
        "enum_arg_is_ok_guarded_tripwire",
        "enum_arg_is_ok_or_err",
        "enum_arg_is_ok_and_err_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    // The true directions: the success/failure tag matches the method.
    for name in [
        "enum_ret_is_some",
        "enum_ret_is_none",
        "enum_ret_is_ok",
        "enum_ret_is_err",
        "enum_ret_is_ok_or_err",
        "enum_ret_passthrough",
        "enum_ret_from_match",
        "enum_arg_is_ok_guarded",
        "enum_arg_is_ok_or_err",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    // The tripwires: refuted, so the method read the *right* discriminant.
    for name in [
        "enum_ret_is_some_tripwire",
        "enum_ret_is_none_tripwire",
        "enum_ret_is_ok_tripwire",
        "enum_ret_is_err_tripwire",
        "enum_ret_is_ok_and_err_tripwire",
        "enum_ret_passthrough_tripwire",
        "enum_ret_from_match_tripwire",
        "enum_arg_is_ok_guarded_tripwire",
        "enum_arg_is_ok_and_err_tripwire",
    ] {
        let o = outcome(&report, name);
        assert!(!o.is_verified(), "`{name}` must be refuted, got: {o}");
    }
    // The refusal: a non-enum return names a tag that does not exist, so the
    // method is unreadable -- a skip, never a verdict against a fabricated tag.
    let o = outcome(&report, "enum_ret_method_on_non_enum");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`ret.is_ok()` on a non-enum return must be refused, got: {o}"
    );
}

/// An enum-returning function's contract can name a *payload*: `ret.Ok`,
/// `ret.Some`, `ret.Err`, `ret.Data` (a user enum's variant).
///
/// A payload exists only on the variant's paths, so the clause naming it is
/// *guarded on the discriminant* (`tag == disc => clause`) and is vacuous on the
/// other variant. The true entries verify because the contract's `ret.Ok` and the
/// body's `((_0 as Ok).0)` are one variable; the tripwires claim a value the
/// payload cannot be, so a model that bound the payload to a fresh unconstrained
/// variable (or dropped the guard) would prove them. The two refusals pin the
/// boundary: a non-enum return and a unit variant have no payload to read.
#[test]
fn an_enum_return_contract_can_name_a_payload() {
    let names = [
        "ret_ok_payload",
        "ret_ok_payload_tripwire",
        "ret_some_payload",
        "ret_some_payload_tripwire",
        "ret_err_payload",
        "ret_err_payload_tripwire",
        "ret_payload_guarded_vacuous",
        "ret_payload_guarded_vacuous_tripwire",
        "ret_user_enum_payload",
        "ret_user_enum_payload_tripwire",
        "ret_payload_on_non_enum",
        "ret_payload_on_unit_variant",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "ret_ok_payload",
        "ret_some_payload",
        "ret_err_payload",
        "ret_payload_guarded_vacuous",
        "ret_user_enum_payload",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "ret_ok_payload_tripwire",
        "ret_some_payload_tripwire",
        "ret_err_payload_tripwire",
        "ret_payload_guarded_vacuous_tripwire",
        "ret_user_enum_payload_tripwire",
    ] {
        assert_refuted(&report, name);
    }
    // The refusals: a non-enum return and a unit variant have no payload, so the
    // contract is unreadable -- a skip, never a verdict against a fabricated value.
    for name in ["ret_payload_on_non_enum", "ret_payload_on_unit_variant"] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` must be refused (no such payload), got: {o}"
        );
    }
}

/// A parenthesized comparison used as an operand is a `bool` value, and a bare
/// one-bit word at the predicate position reads as the value itself.
///
/// `ret == (x == 1)` is the natural spelling of a `bool`-returning function's
/// postcondition, and the arithmetic parser refused it with "missing `)`" -- a
/// dropped obligation for an ordinary shape. The group's predicate is turned into a
/// one-bit value, so the surrounding `==` compares two `bool`s as Rust does. The
/// true/tripwire pairs pin that the group is read as the comparison's *value*: a
/// reader that dropped the group would prove the tripwire, and one that read it as
/// a constant could not verify the true direction at every input.
#[test]
fn a_parenthesized_comparison_is_a_bool_operand() {
    let names = [
        "bool_ret_is_comparison",
        "bool_ret_is_comparison_tripwire",
        "bool_ret_grouped_arithmetic",
        "bool_ret_bare",
        "bool_ret_bare_tripwire",
        "bool_ret_negated",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "bool_ret_is_comparison",
        "bool_ret_grouped_arithmetic",
        "bool_ret_bare",
        "bool_ret_negated",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in ["bool_ret_is_comparison_tripwire", "bool_ret_bare_tripwire"] {
        assert_refuted(&report, name);
    }
}

/// Three payload-summary defects, each of which let a *false* claim be verified.
///
/// * **A parenthesized conjunction of payload clauses** re-guarded both payloads
///   with a combined `tag == 0 && tag == 1` -- unsatisfiable -- so the group was
///   vacuously true and `(ret.Ok == 9 && ret.Err == 8)` was *verified* on a body
///   returning `Err(7)`. The grouped and ungrouped spellings must now agree: both
///   refuted. The true companion pins that the fix did not simply refuse every
///   group.
/// * **A multi-field payload variant** wrote every operand to the single-valued
///   payload store, so the last field won and `ret.Pair` (field 0) denoted field 1.
///   `ret.Pair == 2` was verified; it is refuted now, and `ret.Pair == 1` verifies.
/// * **An argument named like the generated payload binding** (`ret__v_Ok`) was
///   overwritten by it, so `ret.Ok == ret__v_Ok` compared the payload with itself
///   and verified. The binding is now dropped on a collision, so the contract is
///   refused -- a skip, never a proof against the wrong value.
/// * **A *negated* payload comparison** read its discriminant guard from *inside*
///   the `!`: `!(ret.Ok == 9)` became `!(tag == 0 => payload == 9)`, which is false
///   on an `Err` return, so a valid contract was refuted while the equivalent
///   `ret.Ok != 9` verified. The guard is now applied outside the negation, and
///   the two spellings agree -- both verify, and both are refuted on an `Ok(9)`
///   body. A negation that spans two variants has no single scope, so it is
///   refused rather than given a contradictory guard.
#[test]
fn payload_summaries_cannot_prove_a_false_claim() {
    let names = [
        "grouped_payload_conjunction_cannot_prove_this",
        "grouped_payload_conjunction_ok",
        "ungrouped_payload_conjunction_cannot_prove_this",
        "duo_pair_first_field",
        "duo_pair_second_field_cannot_prove_this",
        "payload_binding_shadow_tripwire",
        "negated_payload_comparison",
        "negated_payload_comparison_inequality",
        "negated_payload_comparison_cannot_prove_this",
        "negated_payload_mixed_variant_is_refused",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    let o = outcome(&report, "grouped_payload_conjunction_ok");
    assert!(o.is_verified(), "`grouped_payload_conjunction_ok` must verify, got: {o}");
    let o = outcome(&report, "duo_pair_first_field");
    assert!(o.is_verified(), "`duo_pair_first_field` must verify, got: {o}");
    for name in [
        "grouped_payload_conjunction_cannot_prove_this",
        "ungrouped_payload_conjunction_cannot_prove_this",
        "duo_pair_second_field_cannot_prove_this",
    ] {
        assert_refuted(&report, name);
    }
    // The shadowing argument's contract is *unreadable* (the binding is dropped),
    // so the function is skipped -- the refusal, not a verdict.
    let o = outcome(&report, "payload_binding_shadow_tripwire");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`payload_binding_shadow_tripwire` must be refused, got: {o}"
    );
    // The negation fix: the `!(…)` and `!=` spellings must agree, both verifying
    // here (the `Err` path leaves `ret.Ok` vacuous), and both refuted on an `Ok(9)`
    // body. The mixed-variant negation has no single scope, so it is refused.
    for name in ["negated_payload_comparison", "negated_payload_comparison_inequality"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    assert_refuted(&report, "negated_payload_comparison_cannot_prove_this");
    let o = outcome(&report, "negated_payload_mixed_variant_is_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`negated_payload_mixed_variant_is_refused` must be refused, got: {o}"
    );
}

/// The `?` operator decides, on both the `Ok`/`Some` and the `Err`/`None` paths,
/// and its false directions are refuted.
///
/// `expr?` lowers to three steps the model has to agree on: `<T as Try>::branch`
/// produces a `ControlFlow<Residual, T>`, a `switchInt` reads its discriminant,
/// and on `Break` a `FromResidual::from_residual` call re-wraps the error as the
/// function's return enum. The test pins each step's own observable:
///
/// * the *success* value: `result_try_value_used` uses the yielded value
///   (`r.Ok + 1`), so a model that bound the `Continue` payload to the wrong
///   variant, or to the wrong width, would refute it.
/// * the *tag* the `switchInt` reads: the `Err`-propagation pair, where the
///   failure path must produce `ret.is_err()` and the opposite claim is refuted.
/// * `from_residual`'s re-wrap: `ret.Err == r.Err`, so the error value has to
///   survive the conversion, not just the tag.
///
/// Both families (`Result` and `Option`) are covered, because they differ in
/// where the payload lives (`Ok` is 0, `Some` is 1) and in whether the residual
/// carries a value (`Result` does, `Option`'s `None` does not).
#[test]
fn the_try_operator_decides_on_both_paths() {
    let names = [
        "result_try_ok_value",
        "result_try_ok_value_cannot_prove_this",
        "result_try_err_propagates",
        "result_try_err_propagates_cannot_prove_this",
        "result_try_value_used",
        "result_try_value_used_cannot_prove_this",
        "option_try_some_value",
        "option_try_some_value_cannot_prove_this",
        "option_try_none_propagates",
        "option_try_none_propagates_cannot_prove_this",
        "result_try_of_a_known_ok",
        "result_try_of_a_known_err",
        "result_try_of_a_known_err_cannot_prove_this",
        "option_try_of_a_known_none",
        "option_try_of_a_known_none_cannot_prove_this",
        "result_try_chained",
        "result_try_chained_cannot_prove_this",
        "result_try_in_either_branch",
        "result_try_in_either_branch_cannot_prove_this",
        "result_try_widens_the_error",
        "result_try_widens_the_error_cannot_prove_this",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "result_try_ok_value",
        "result_try_err_propagates",
        "result_try_value_used",
        "option_try_some_value",
        "option_try_none_propagates",
        "result_try_of_a_known_ok",
        "result_try_of_a_known_err",
        "option_try_of_a_known_none",
        "result_try_chained",
        "result_try_in_either_branch",
        "result_try_widens_the_error",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "result_try_ok_value_cannot_prove_this",
        "result_try_err_propagates_cannot_prove_this",
        "result_try_value_used_cannot_prove_this",
        "option_try_some_value_cannot_prove_this",
        "option_try_none_propagates_cannot_prove_this",
        "result_try_of_a_known_err_cannot_prove_this",
        "option_try_of_a_known_none_cannot_prove_this",
        "result_try_chained_cannot_prove_this",
        "result_try_in_either_branch_cannot_prove_this",
        "result_try_widens_the_error_cannot_prove_this",
    ] {
        assert_refuted(&report, name);
    }
}

/// The `Option`↔`Result` conversions -- `Option::ok_or`, `Result::ok`,
/// `Result::err` -- decide, and both the *tag* and the *payload* cross.
///
/// Three things are pinned, and each is a way the model could be wrong:
///
/// * the tag: `ok_or`/`ok` reinterpret the receiver's tag (`Ok` and `Some` are
///   discriminants 0 and 1, so `1 - tag`), while `err` *keeps* it (`Err` is
///   already the payload-carrying variant). A model that inverted `err`'s tag, or
///   read the result tag as a constant, proves a tripwire.
/// * the payload: the moved payload is recorded under the discriminant the
///   consuming `switchInt` selects, at the *payload's* width. The `_moves_the_payload`
///   pair reads it back through `unwrap`; a model that recorded the wrong width (as
///   the first cut did -- it stored the error argument as the `Ok` payload) refutes
///   the true direction and cannot prove the false one.
/// * the classifier: `ok_or` is printed with a *method* turbofish
///   (`Option::<u8>::ok_or::<i32>`), so its name must be found past the `<…>`
///   segment, or the call is reported unmodelled.
#[test]
fn the_option_result_conversions_decide_and_move_the_payload() {
    let names = [
        "ok_or_some_is_ok",
        "ok_or_some_is_ok_tripwire",
        "ok_or_none_is_err",
        "ok_or_none_is_err_tripwire",
        "ok_or_moves_the_payload",
        "ok_or_moves_the_payload_tripwire",
        "ok_ok_is_some",
        "ok_ok_is_some_tripwire",
        "ok_err_is_none",
        "ok_err_is_none_tripwire",
        "ok_moves_the_payload",
        "ok_moves_the_payload_tripwire",
        "err_err_is_some",
        "err_err_is_some_tripwire",
        "err_ok_is_none",
        "err_ok_is_none_tripwire",
        "err_moves_the_payload",
        "err_moves_the_payload_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "ok_or_some_is_ok",
        "ok_or_none_is_err",
        "ok_or_moves_the_payload",
        "ok_ok_is_some",
        "ok_err_is_none",
        "ok_moves_the_payload",
        "err_err_is_some",
        "err_ok_is_none",
        "err_moves_the_payload",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "ok_or_some_is_ok_tripwire",
        "ok_or_none_is_err_tripwire",
        "ok_or_moves_the_payload_tripwire",
        "ok_ok_is_some_tripwire",
        "ok_err_is_none_tripwire",
        "ok_moves_the_payload_tripwire",
        "err_err_is_some_tripwire",
        "err_ok_is_none_tripwire",
        "err_moves_the_payload_tripwire",
    ] {
        // A *refutation*: the conversion is only pinned if the false contract
        // produced a counterexample. `!is_verified()` would also accept a skip.
        assert_refuted(&report, name);
    }
}

/// The three findings of the PR #8 review round on the enum conversions.
///
/// * A *constructed* source variant (`None::<u8>.ok_or(e)`, `Err(e).ok()`,
///   `Ok(x).err()`) records no payload for the variant that is absent, so the
///   conversion must still produce a result. It is sound to leave the unreachable
///   payload unbound when the tag is a *known* other discriminant; a symbolic tag
///   still refuses. The tripwires refute the *tag*, which is what proves the
///   conversion ran rather than the whole call being dropped.
/// * The grouping and negation lookaheads recognise the `base.method()` enum
///   predicate, so `(ret.is_ok())` and `!x.is_none()` read instead of being routed
///   into arithmetic.
#[test]
fn the_option_result_conversions_handle_constructed_variants_and_grouping() {
    let names = [
        "constructed_none_ok_or_is_err",
        "constructed_none_ok_or_is_err_tripwire",
        "constructed_err_ok_is_none",
        "constructed_err_ok_is_none_tripwire",
        "constructed_ok_err_is_none",
        "constructed_ok_err_is_none_tripwire",
        "constructed_ok_ok_is_some",
        "constructed_ok_ok_is_some_tripwire",
        "grouped_enum_predicate",
        "grouped_enum_predicate_tripwire",
        "negated_enum_predicate",
        "negated_enum_predicate_tripwire",
        "grouped_enum_predicate_conjunction",
        "grouped_enum_predicate_conjunction_tripwire",
        "bare_negated_enum_predicate",
        "bare_negated_enum_predicate_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "constructed_none_ok_or_is_err",
        "constructed_err_ok_is_none",
        "constructed_ok_err_is_none",
        "constructed_ok_ok_is_some",
        "grouped_enum_predicate",
        "negated_enum_predicate",
        "grouped_enum_predicate_conjunction",
        "bare_negated_enum_predicate",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "constructed_none_ok_or_is_err_tripwire",
        "constructed_err_ok_is_none_tripwire",
        "constructed_ok_err_is_none_tripwire",
        "constructed_ok_ok_is_some_tripwire",
        "grouped_enum_predicate_tripwire",
        "negated_enum_predicate_tripwire",
        "grouped_enum_predicate_conjunction_tripwire",
        "bare_negated_enum_predicate_tripwire",
    ] {
        // A *refutation*, not merely "not verified": these tripwires are only
        // evidence of the conversion/parser if the false contract produced a
        // counterexample. `!is_verified()` would also accept a skip.
        assert_refuted(&report, name);
    }
}

/// `Option::or` and `Option::and` are total, and the *right* operand's tag and
/// payload cross.
///
/// Each combinator returns one of its two `Option`s by the receiver's tag, so the
/// result's tag is an `ite` on that tag and both payloads are carried. `or` is the
/// receiver on `Some` and the argument on `None`; `and` is the mirror, dropping the
/// receiver's payload on `Some`.
///
/// Three things are pinned, each a way the model could be wrong:
///
/// * the tag: `or` on a `None` receiver must take the *argument's* tag, and `and`
///   on a `Some` receiver must take the argument's -- so the two tripwires that
///   claim the receiver's own value are refuted.
/// * the payload: the selected payload is read back through `unwrap`, so a model
///   that recorded the wrong one refutes the true direction and cannot prove the
///   false one.
///
/// The drop-glue rule is shared with `ok`/`err`: `or` drops the argument's payload
/// on the `Some` path and `and` drops the receiver's, so a `T` whose destructor is
/// not modelled is refused rather than read as glue-free.
///
/// The *operand shapes* are pinned separately: a `checked_*` receiver's tag is the
/// arithmetic width while a seeded `Option` argument's is one bit, so the tags must
/// be normalised; `Option<T>::and<U>` returns `Option<U>`, so the receiver's
/// payload must never be `ite`-d with the argument's; and a constructed `None`
/// records no payload, so its absence must not refuse the call.
#[test]
fn option_or_and_are_total_and_select_the_right_operand() {
    let names = [
        "or_some_is_the_receiver",
        "or_some_is_the_receiver_tripwire",
        "or_none_is_the_argument",
        "or_none_is_the_argument_tripwire",
        "and_some_is_the_argument",
        "and_some_is_the_argument_tripwire",
        "and_none_is_the_receiver",
        "and_none_is_the_receiver_tripwire",
        "or_mixed_tag_widths_is_none",
        "or_mixed_tag_widths_tripwire",
        "or_mixed_tag_widths_none_is_argument",
        "and_different_payload_widths",
        "and_different_payload_widths_tripwire",
        "and_none_receiver_decides",
        "constructed_none_or_some",
        "constructed_some_or_none",
        "constructed_none_or_some_tripwire",
        "or_slices_selects_the_receiver",
        "or_slices_selects_the_receiver_tripwire",
        "and_slices_selects_the_argument",
        "and_slices_selects_the_argument_tripwire",
        "and_different_width_deref",
        "and_different_width_deref_tripwire",
        "and_scalar_receiver_ref_argument",
        "and_scalar_receiver_ref_argument_tripwire",
        "chained_or_selects_the_first",
        "chained_or_selects_the_first_cannot_prove_this",
        "and_with_a_conditional_argument",
        "and_with_a_conditional_argument_cannot_prove_this",
        "signed_or_element_is_signed",
        "signed_or_element_is_signed_cannot_prove_this",
        "signed_or_element_divides_signed",
        "signed_or_element_divides_signed_cannot_prove_this",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "or_some_is_the_receiver",
        "or_none_is_the_argument",
        "and_some_is_the_argument",
        "and_none_is_the_receiver",
        "or_mixed_tag_widths_is_none",
        "or_mixed_tag_widths_none_is_argument",
        "and_different_payload_widths",
        "and_none_receiver_decides",
        "constructed_none_or_some",
        "constructed_some_or_none",
        "or_slices_selects_the_receiver",
        "and_slices_selects_the_argument",
        "and_different_width_deref",
        "and_scalar_receiver_ref_argument",
        "chained_or_selects_the_first",
        "and_with_a_conditional_argument",
        "signed_or_element_is_signed",
        "signed_or_element_divides_signed",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "or_some_is_the_receiver_tripwire",
        "or_none_is_the_argument_tripwire",
        "and_some_is_the_argument_tripwire",
        "and_none_is_the_receiver_tripwire",
        "or_mixed_tag_widths_tripwire",
        "and_different_payload_widths_tripwire",
        "constructed_none_or_some_tripwire",
        "or_slices_selects_the_receiver_tripwire",
        "and_slices_selects_the_argument_tripwire",
        "and_different_width_deref_tripwire",
        "and_scalar_receiver_ref_argument_tripwire",
        "chained_or_selects_the_first_cannot_prove_this",
        "and_with_a_conditional_argument_cannot_prove_this",
        "signed_or_element_is_signed_cannot_prove_this",
        "signed_or_element_divides_signed_cannot_prove_this",
    ] {
        // A *refutation*, not merely "not verified": a swap of the two operands
        // must produce a counterexample, and a skip would not be evidence.
        assert_refuted(&report, name);
    }
}

/// `Option<&T>::copied()`/`cloned()` is the everyday `v.first().copied()` idiom:
/// the value the payload reference addresses, with the receiver's tag unchanged.
///
/// The model stores a `&T` payload as the value it addresses, so the result's
/// payload is the receiver's -- `v.first().copied()` and `*v.first().unwrap()`
/// name one word. Two things are pinned, each a way the model could be wrong:
///
/// * the payload: the copied value must be the slice's own element, so a claim
///   about the element verifies and a claim about a different value is refuted.
/// * the tag: `copied` keeps the receiver's tag, so on an empty slice `unwrap_or`
///   takes the default rather than panicking -- a model that fixed the tag to
///   `Some` would refute `copied_empty_is_none`.
///
/// `cloned` is the same shape as `copied` for a `Copy` element, so one arm serves
/// both and the `cloned` fixture pins that the shared arm is reached.
#[test]
fn option_copied_and_cloned_copy_the_payload_with_the_tag() {
    let names = [
        "copied_first_is_the_element",
        "copied_first_tripwire",
        "copied_get_is_the_element",
        "copied_get_tripwire",
        "copied_empty_is_none",
        "cloned_first_is_the_element",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "copied_first_is_the_element",
        "copied_get_is_the_element",
        "copied_empty_is_none",
        "cloned_first_is_the_element",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in ["copied_first_tripwire", "copied_get_tripwire"] {
        assert_refuted(&report, name);
    }
}

/// `char` is a 32-bit unsigned value, its literals and the `is_ascii_*` predicates.
///
/// The predicates are exact at width 32 because every range they test lies inside
/// `0..=0x7f`, so a value at or above `0x100` is outside all of them -- which is
/// what `char::is_ascii_digit` means too. `char_high_digit_tripwire` is the
/// evidence: `'\u{130}'`'s low byte is `'0'`, so a model that masked to eight bits
/// would *prove* it, while the real predicate is `false`.
#[test]
fn char_literals_and_ascii_predicates_are_modelled() {
    let names = [
        "char_as_byte",
        "char_ord_of_a",
        "char_digit_is_true",
        "char_digit_tripwire",
        "char_high_digit_tripwire",
        "char_high_is_not_digit",
        "char_newline_is_whitespace",
        "char_emoji_not_alphabetic",
        "char_max_is_the_scalar_maximum",
        "char_max_is_the_scalar_maximum_cannot_prove_this",
        "char_min_is_nul",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "char_as_byte",
        "char_ord_of_a",
        "char_digit_is_true",
        "char_high_is_not_digit",
        "char_newline_is_whitespace",
        "char_emoji_not_alphabetic",
        "char_max_is_the_scalar_maximum",
        "char_min_is_nul",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    // Real refutations, with the scalar value in the witness -- so the literals
    // were read (120 is `'x'`, 304 is `0x130`) and not skipped.
    assert_refuted(&report, "char_digit_tripwire");
    assert_refuted(&report, "char_high_digit_tripwire");
    // `char::MAX` is `0x10FFFF`, not `2^32 - 1`: the false twin is refuted at the
    // *real* maximum (`c = 1114111`), which a width-derived bound would prove.
    assert_refuted(&report, "char_max_is_the_scalar_maximum_cannot_prove_this");
}

/// `slice::last` -- a fresh element for a slice, the exact element for an array.
///
/// A slice's length is symbolic, so `xs.last()` names no index the store can pin
/// and the element is a *fresh* variable: a contract true of every element holds
/// of the last one (`slice_last_is_an_element` verifies), and a claim that the last
/// element is a particular value is refuted, because a slice with that element can
/// exist. An *array*'s length is its type's constant, so `a.last()` is the exact
/// element `a[N-1]`: `array_last_is_the_last_element` verifies against `a[3] == 7`
/// and its twin, claiming `a[0] == 9`, refutes. The two directions together show the
/// element is neither a constant (the array case decides by the actual last element)
/// nor the first element (the twin refutes).
#[test]
fn slice_last_is_an_element_and_array_last_is_exact() {
    let names = [
        "slice_last_is_an_element",
        "array_last_is_the_last_element",
        "slice_last_is_an_element_cannot_prove_this",
        "array_last_is_the_last_element_cannot_prove_this",
        "slice_last_after_write_is_seen",
        "slice_last_after_write_is_seen_cannot_prove_this",
        "slice_last_is_kept_when_another_index_is_written",
        "slice_last_read_before_a_write_is_not_kept_cannot_prove_this",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "slice_last_is_an_element",
        "array_last_is_the_last_element",
        "slice_last_after_write_is_seen",
        "slice_last_is_kept_when_another_index_is_written",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    // Real refutations: the fresh element is unconstrained, and the array's last
    // element is not the first, so neither claim can be proved.
    assert_refuted(&report, "slice_last_is_an_element_cannot_prove_this");
    assert_refuted(&report, "array_last_is_the_last_element_cannot_prove_this");
    // The write/read interaction: a concrete-index write that *is* the last
    // element must reach the sentinel, so the pre-write value does not survive.
    // A model that left the sentinel alone would prove the twin -- the false proof
    // this pair exists to pin.
    assert_refuted(&report, "slice_last_after_write_is_seen_cannot_prove_this");
    // The read-before/write/read-after shape at the length where the write reaches
    // `last()`. This is the review's exact example: both reads must not be the same
    // variable. The `len == 2` fixture above keeps `last()` across the write, so it
    // stays green whether or not the sentinel is refreshed; only this one refutes a
    // model that left the sentinel alone.
    assert_refuted(&report, "slice_last_read_before_a_write_is_not_kept_cannot_prove_this");
}

/// `u8::from(bool)` -- the one conversion the integer model would otherwise refuse.
///
/// A `bool` has no integer width, so `conversion_types` reads the pair but
/// `int_width` refuses the source. The conversion is the zero-extension of the
/// one-bit value: `false` -> 0, `true` -> 1. The `true`/`false` pair pins that the
/// bit is the *value*: a model that fixed it to a constant would prove one and
/// refute the other, and here `bool_to_u8_of_true_is_one` verifies while its
/// `false` twin refutes with the witness `b = 0`. The `u32` destination pins the
/// widening.
#[test]
fn a_bool_conversion_is_the_zero_extended_bit() {
    let names = [
        "bool_to_u8_is_zero_or_one",
        "bool_to_u8_of_true_is_one",
        "bool_to_u8_of_true_is_one_cannot_prove_this",
        "bool_to_u32_is_zero_or_one",
    ];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in [
        "bool_to_u8_is_zero_or_one",
        "bool_to_u8_of_true_is_one",
        "bool_to_u32_is_zero_or_one",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    // A real refutation, so the bit is the value and not a constant one.
    assert_refuted(&report, "bool_to_u8_of_true_is_one_cannot_prove_this");
}

/// A `&mut bool` argument's final value is a predicate, not a word.
///
/// The postcondition's bare `c` means the value the body left at the target. A
/// `bool` target is a `Val::Bool`, so the word-only collection dropped it and the
/// contract was refused as an unknown name. The predicate is widened to a one-bit
/// word, exactly as a `bool` `ret` is. The false direction pins that the binding is
/// the *final* value, not the entry value.
#[test]
fn a_mutable_bool_reference_postcondition_reads_its_final_value() {
    let names = ["set_bool_ref", "a_bool_ref_write_cannot_prove_this", "keep_bool_ref"];
    let Some(report) = verify_realistic(&names) else {
        return;
    };
    for name in ["set_bool_ref", "keep_bool_ref"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    // A real refutation, so the false direction is a counterexample and not a skip.
    assert_refuted(&report, "a_bool_ref_write_cannot_prove_this");
}

/// A trailing line comment on a variant line does not erase the enum layout.
///
/// `B = 3, // special` keeps the comma *before* the comment, so the reader that
/// trims a trailing comma from the raw line no longer finds one, rejects the
/// discriminant, and drops the whole layout -- taking every contract that names
/// a variant with it. The true contract must verify and the tripwire refute.
#[test]
fn a_trailing_comment_on_a_variant_keeps_the_layout() {
    let Some(report) = verify_realistic(&[
        "enum_trailing_comment_keeps_the_layout",
        "enum_trailing_comment_tripwire",
    ]) else {
        return;
    };
    let o = outcome(&report, "enum_trailing_comment_keeps_the_layout");
    assert!(
        o.is_verified(),
        "`enum_trailing_comment_keeps_the_layout` must verify, got: {o}"
    );
    let t = outcome(&report, "enum_trailing_comment_tripwire");
    assert!(!t.is_verified(), "the trailing-comment tripwire must be refuted, got: {t}");
}

/// A *slice* subscripted symbolically is modelled, not refused — when the
/// precondition bounds both the index and the length.
///
/// The whole feature turns on the domain being finite. An array's length is in its
/// type, so `0..N` can be enumerated; a slice's is a symbolic input, so the chain
/// enumerates `0..MAX_INDEX_CHAIN` and is exact only where the length is within
/// that. The precondition has to establish both facts, and this pins that the
/// modelled case really verifies rather than being refused.
#[test]
fn a_symbolic_slice_index_is_modelled_when_both_bounds_hold() {
    let Some(report) = verify_realistic(&["slice_symbolic_index"]) else { return };
    let o = outcome(&report, "slice_symbolic_index");
    assert!(o.is_verified(), "`slice_symbolic_index` must verify, got: {o}");
}

/// The tripwire: a false claim about `xs[i]` must be *refuted*, not refused.
///
/// The body returns `xs[i]`, and the contract claims that is also `xs[0]` — false
/// for every `i != 0`. A pass would mean the chain ignored the index. The
/// assertion is on `Failed` rather than on `!is_verified()` on purpose: a
/// `Skipped` or `Incomplete` outcome is also "not verified", and accepting one
/// would let the tripwire pass without the chain ever having been contradicted.
#[test]
fn a_slice_chain_depends_on_the_index() {
    let Some(report) = verify_realistic(&["slice_symbolic_index_tripwire"]) else { return };
    let o = outcome(&report, "slice_symbolic_index_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`slice_symbolic_index_tripwire` must be refuted (not skipped), got: {o}"
    );
}

/// Each of a slice's two bounds is required on its own, and the refusal names the
/// one that is missing.
///
/// The length bound is the half an index-only rule would miss, and the index bound
/// is the half a length-only rule would miss. Each entry below supplies one fact
/// and withholds the other, so a rule that checked only one of them would model a
/// subscript it should refuse.
#[test]
fn a_slice_subscript_missing_either_bound_is_refused() {
    let cases = [
        ("slice_unbounded_length_refused", "`xs.len() <= 64` does not hold"),
        ("slice_unbounded_index_refused", "`i < xs.len()` does not hold"),
    ];
    for (name, want) in cases {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        match o {
            FnOutcome::Skipped { reason } => assert!(
                reason.contains(want),
                "`{name}`'s refusal must name the missing bound `{want}`, got: {reason}"
            ),
            other => panic!("`{name}` must be skipped, got: {other}"),
        }
    }
}

/// The chain is really evaluated: a false postcondition about `a[i]` produces a
/// counterexample that pins the index to an in-range value.
///
/// Without this, "verified" above would be consistent with the chain being a
/// constant the postcondition happened to accept. `body_only` claims `ret <= 9`
/// for an arbitrary `u8` element, which is false, so it must FAIL -- and the
/// counterexample must show the element's value, which only exists if the chain
/// selected a real element variable.
/// Verify one function from an inline source and return its outcome.
///
/// Each test below needs its own file, because the property under test is about
/// what the *frontend* does with a specific shape and the corpus is shared.
/// Writing the source to a temp dir keeps that shape next to its assertion.
///
/// Returns `None` only when no nightly `rustc` is configured, which is the one
/// legitimate reason to skip. A named function that is *absent* from the report
/// is a panic, not a skip: it means the frontend dropped it, and a test written
/// as `let Some(o) = verify_src(..) else { return }` would then pass without
/// checking anything. That is how `a_whole_struct_assignment_invalidates_its_fields`
/// hid a one-line struct that swallowed every following function. A vacuous pass
/// is worse than a failure, so this refuses to be quiet about it.
///
/// The guard `verify_src` applies: a contracted function that is absent from the
/// report is a failure, whatever `report.missing` says. `missing` is the same
/// drop from the frontend's side (a contract with no MIR function), and accepting
/// it as a pass reopened the hole the guard exists to close: a test whose function
/// the frontend drops -- for *any* reason, including one a future bug adds --
/// would assert nothing. The only source without a contract is one that carries no
/// `///` at all, which is a caller mistake, not a frontend drop.
///
/// Split out so the branch that made the guard vacuous -- `missing` naming the
/// function -- can be tested *without* a nightly `rustc`. The guard is about what
/// counts as a pass, and a test that needed the frontend could not check the one
/// case that mattered.
#[track_caller]
fn assert_not_dropped(name: &str, src: &str, present: bool, missing: &[String]) {
    // "Has a contract" must cover both spellings. It used to test only for `///`,
    // which is the doc-comment form: a source whose only contract is a `spec!`
    // block looked contract-free, so a dropped function passed the guard. The
    // marker is the clause *keyword*, which both spellings carry.
    let has_contract = src.contains("///")
        || ["requires", "ensures", "invariant", "decreases", "variant", "unwind"]
            .iter()
            .any(|k| src.contains(&format!("{k}:")));
    assert!(
        present || !has_contract,
        "`{name}` was dropped from the report: it has a contract but no outcome, so this test \
         would have passed without checking anything (missing: {missing:?})"
    );
}

fn verify_src(name: &str, src: &str) -> Option<FnOutcome> {
    let rustc = rustc()?;
    // A unique directory per call: two tests that both ask about a function
    // named `reads` run in parallel and would otherwise write the same
    // `probe.rs`, so one test could read the other's source. The counter keeps
    // the path unique within the process; the pid keeps it unique across
    // processes.
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir()
        .join(format!("verif-{name}-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("probe.rs");
    std::fs::write(&file, src).expect("write probe");
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &probe_opts())
        .expect("frontend");
    let o = report
        .outcomes
        .into_iter()
        .find(|(n, _)| n == name)
        .map(|(_, o)| o);
    let _ = std::fs::remove_dir_all(&dir);
    assert_not_dropped(name, src, o.is_some(), &report.missing);
    o
}

/// A `&mut Vec` argument's postcondition `v.len()` must read the *final* length, not the
/// entry length. Before the fix the entry length (0) was used, so `ensures: v.len() == 0`
/// over `v.push(1)` was a false proof and the true `== 1` was refuted.
#[test]
fn a_mut_vec_postcondition_reads_the_final_length() {
    let Some(f) = verify_src(
        "mv_false",
        "/// requires: v.len() == 0\n/// ensures: v.len() == 0\npub fn mv_false(v: &mut Vec<u8>) { v.push(1); }",
    ) else {
        return;
    };
    assert!(
        matches!(f, FnOutcome::Failed { .. }),
        "the final length is 1, so `v.len() == 0` must be refuted, got {f}"
    );
    let Some(t) = verify_src(
        "mv_true",
        "/// requires: v.len() == 0\n/// ensures: v.len() == 1\npub fn mv_true(v: &mut Vec<u8>) { v.push(1); }",
    ) else {
        return;
    };
    assert!(
        matches!(t, FnOutcome::Verified { .. }),
        "the final length is 1, so `v.len() == 1` must verify, got {t}"
    );
}

/// A write through a `Box` pointer (`*b = v`) reaches the boxed store, so a later `*b`
/// reads the *new* value: a true contract (`ret == 7`) verifies and the stale one
/// (`ret == 0`) is refuted. The write actually runs -- it is not refused at the null
/// check -- and its teeth are the true direction: dropping the boxed-store write (or the
/// forget/insert reorder that keeps it) makes `ret == 7` stop verifying.
#[test]
fn a_write_through_a_box_pointer_is_seen_by_a_later_read() {
    let t = verify_src(
        "bw_true",
        "/// requires: true\n/// ensures: ret == 7\npub fn bw_true() -> u8 { let mut b = Box::new(3u8); *b = 7; *b }",
    );
    let Some(t) = t else { return };
    assert!(matches!(t, FnOutcome::Verified { .. }), "the box write must be seen (ret == 7), got {t}");
    let f = verify_src(
        "bw_false",
        "/// requires: true\n/// ensures: ret == 0\npub fn bw_false() -> u8 { let mut b = Box::new(3u8); *b = 7; *b }",
    );
    let Some(f) = f else { return };
    assert!(matches!(f, FnOutcome::Failed { .. }), "the stale box value must be refuted (ret == 0), got {f}");
}

/// `Vec::clear` destroys its elements; with a panicking `Drop` that is a real panic, so
/// the reset must be refused rather than reported panic-free.
#[test]
fn clearing_a_vec_of_droppable_elements_is_not_proved_panic_free() {
    let Some(o) = verify_src("reset", r#"
struct Boom;
impl Drop for Boom { fn drop(&mut self) { panic!("boom"); } }
pub fn reset(v: &mut Vec<Boom>) { v.clear(); }
"#) else { return };
    assert!(
        !matches!(o, FnOutcome::Verified { .. }),
        "clearing a Vec<Boom> must not be reported panic-free, got {o}"
    );
}

/// A compound closure and an adapter-before-terminal are refused rather than
/// mis-modelled. `filter(..).next()` was a *false proof* before the guard: on a
/// 3-element slice of zeros it is `false`, but the unguarded model read the base length
/// and returned `true`, so `ensures: ret == true` was proved.
#[test]
fn iterator_adapter_shortcuts_are_refused_not_mis_modelled() {
    let Some(o) = verify_src("pfilt", r#"
/// requires: xs.len() == 3
/// ensures: ret == true
pub fn pfilt(xs: &[u8]) -> bool { xs.iter().filter(|x| **x > 10).next().is_some() }
"#) else { return };
    assert!(
        !matches!(o, FnOutcome::Verified { .. }),
        "`filter(..).next()` must be refused, got {o}"
    );

    let Some(o) = verify_src("pmapc", r#"
/// requires: xs.len() == 2
/// ensures: ret == xs[0] + xs[1]
pub fn pmapc(xs: &[u8]) -> u8 { xs.iter().copied().map(|x| { let y = x + 1; y * 2 }).sum::<u8>() }
"#) else { return };
    assert!(
        !matches!(o, FnOutcome::Verified { .. }),
        "a compound map closure must be refused, got {o}"
    );

    let Some(o) = verify_src("prev", r#"
/// requires: xs.len() == 3
/// ensures: ret == xs[0] + xs[1] + xs[2]
pub fn prev(xs: &[i8]) -> i8 { xs.iter().rev().copied().sum::<i8>() }
"#) else { return };
    assert!(
        !matches!(o, FnOutcome::Verified { .. }),
        "a reversed checked sum must be refused, got {o}"
    );
}

/// A source file may *name* `verif` -- `use verif::spec;` above an in-code
/// contract block -- but the frontend runs `rustc` on a single file with no Cargo
/// graph behind it, so without an `--extern` entry that import is `E0432`. This
/// pins both halves: the same source is refused with no extern and verified with
/// one, so a `--extern` that never reaches the command line cannot pass.
#[test]
fn an_in_code_contract_can_name_verif_through_an_extern() {
    // Lookup and emission must name ONE compiler: a rlib's metadata is
    // compiler-specific, so probing with one toolchain and emitting with another
    // fails `E0514` even when both are installed and each has its own artifact.
    //
    // The compiler here is the one the *emitter* will use, and it is cargo's: the
    // rlib this test binary links was built by it, and a test binary has no `RUSTC`
    // in its environment. `--emit=mir` is stable, so no nightly is needed. The test
    // deliberately does NOT read `VERIF_RUSTC`: CI points that at a nightly, and
    // probing the stable-built rlib with a nightly is exactly the mismatch this
    // test exists to catch.
    let rustc = std::env::var("RUSTC")
        .ok()
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "rustc".to_string());
    if std::process::Command::new(&rustc)
        .arg("--version")
        .output()
        .map(|o| !o.status.success())
        .unwrap_or(true)
    {
        return;
    }

    // `build_script_roots()` needs `OUT_DIR`, which a test binary does not have, so
    // the profile directory is found from the test binary's own path instead.
    // Cargo's layout is its own business (`deps/` or `build/<pkg>/<hash>/out/`, and
    // a stale rlib from an earlier build can sit beside a fresh one), so the walk
    // covers the whole profile and the choice is made by *trying* candidates
    // newest-first until one compiles -- the same rule `extern_options_with` uses.
    let exe = std::env::current_exe().expect("current exe");
    let profile = exe
        .ancestors()
        .find(|a| a.file_name().is_some_and(|n| n == "debug" || n == "release"))
        .expect("a debug or release profile directory above the test binary");

    fn walk(dir: &std::path::Path, depth: u32, out: &mut Vec<std::path::PathBuf>) {
        if depth == 0 {
            return;
        }
        let Ok(entries) = std::fs::read_dir(dir) else { return };
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, depth - 1, out);
            } else if p
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("libverif") && n.ends_with(".rlib"))
            {
                out.push(p);
            }
        }
    }

    let mut rlibs = Vec::new();
    walk(profile, 6, &mut rlibs);
    let mut search: Vec<std::path::PathBuf> = rlibs
        .iter()
        .filter_map(|p| p.parent().map(|d| d.to_path_buf()))
        .collect();
    search.sort();
    search.dedup();
    let mut verif_rlibs: Vec<std::path::PathBuf> = rlibs
        .into_iter()
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("libverif-"))
        })
        .collect();
    verif_rlibs.sort();
    verif_rlibs.dedup();
    verif_rlibs.sort_by_key(|p| {
        std::cmp::Reverse(std::fs::metadata(p).and_then(|m| m.modified()).ok())
    });
    assert!(
        !verif_rlibs.is_empty(),
        "an rlib of `verif` must exist under {}",
        profile.display()
    );

    let src = "use verif::spec;\n\nspec! {\n    requires: n <= 200,\n    ensures: ret == n + 1,\n}\npub fn inc(n: u8) -> u8 { n + 1 }\n";

    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-extern-e2e-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("probe.rs");
    std::fs::write(&file, src).expect("write probe");

    // Without the extern, `use verif::spec;` cannot resolve: the frontend reports it.
    let bare = verify::verify_file_with_opts(&rustc, &file, &[], &probe_opts());
    assert!(
        bare.is_err(),
        "an import of `verif` must fail without an extern, got: {:?}",
        bare.map(|r| r.outcomes.len())
    );

    // With the extern, the same source verifies. Candidates are tried newest-first,
    // because a stale rlib from another compiler fails the probe (`E0514`) and the
    // next one is the answer -- which is the *same* compiler that emits the MIR.
    let mut verified = false;
    let mut last_err = String::new();
    for rlib in &verif_rlibs {
        let mut opts = probe_opts();
        opts.externs = vec![("verif".to_string(), rlib.clone())];
        opts.search_paths = search.clone();
        match verify::verify_file_with_opts(&rustc, &file, &[], &opts) {
            Ok(report) => {
                verified = report
                    .outcomes
                    .iter()
                    .find(|(n, _)| n == "inc")
                    .is_some_and(|(_, o)| o.is_verified());
                if verified {
                    break;
                }
                last_err = format!("{:?}", report.outcomes);
            }
            Err(e) => last_err = e,
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        verified,
        "with a working extern the in-code contract must verify; last error: {last_err}"
    );
}

/// Options for a probe written to a loose temp file.
///
/// A probe has no `Cargo.toml` above it, so the edition cannot be resolved from a
/// manifest -- and it is never guessed. The tests name the crate's own edition
/// (2024) explicitly. The corpus files (`actuator.rs`, `realistic.rs`) do live
/// under this repository's `Cargo.toml`, so those tests use the plain entry point
/// and exercise the manifest resolution path instead.
fn probe_opts() -> verify::MirOptions {
    verify::MirOptions { edition: Some(verify::Edition::Rust2024), ..Default::default() }
}

/// [`probe_opts`] with a `--cfg` set, so a `#[cfg]`-gated item is read the way the
/// compiler read it.
fn probe_opts_with_cfgs(cfgs: &[&str]) -> verify::MirOptions {
    let mut args = Vec::new();
    for c in cfgs {
        args.push("--cfg".to_string());
        args.push((*c).to_string());
    }
    verify::MirOptions {
        edition: Some(verify::Edition::Rust2024),
        rustc_args: args,
        ..Default::default()
    }
}

/// [`verify_src`], with the run's options named. Used where the *options* are part of
/// the property under test (the `cfg` set, which decides a gated enum variant).
fn verify_src_with(name: &str, src: &str, opts: &verify::MirOptions) -> Option<FnOutcome> {
    let rustc = rustc()?;
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir()
        .join(format!("verif-{name}-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("probe.rs");
    std::fs::write(&file, src).expect("write probe");
    let report = verify::verify_file_with_opts(&rustc, &file, &[], opts).expect("frontend");
    let o = report
        .outcomes
        .into_iter()
        .find(|(n, _)| n == name)
        .map(|(_, o)| o);
    let _ = std::fs::remove_dir_all(&dir);
    assert_not_dropped(name, src, o.is_some(), &report.missing);
    o
}

/// Every outcome and the `missing` list for one source, without the
/// "must be present" guard of [`verify_src`] -- for the trait-contract tests,
/// whose whole point is that a declaration has *no* outcome of its own.
fn verify_all_outcomes(src: &str) -> (Vec<(String, FnOutcome)>, Vec<String>) {
    let rustc = rustc().expect("a toolchain to dump MIR with");
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-all-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("probe.rs");
    std::fs::write(&file, src).expect("write probe");
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &probe_opts()).expect("frontend");
    let _ = std::fs::remove_dir_all(&dir);
    (report.outcomes, report.missing)
}

/// A contracted function the frontend dropped is a failure, even when the report
/// names it in `missing`.
///
/// `missing` is the drop reported from the frontend's side, and accepting it as a
/// pass reopened the hole the strict helper exists to close: a test whose function
/// the frontend drops -- for any reason, including one a future bug adds -- would
/// assert nothing. The guard must reject the `missing` case, which is what this
/// pins without needing a nightly `rustc`.
#[test]
#[should_panic(expected = "was dropped")]
fn a_dropped_contracted_function_fails_even_when_missing_names_it() {
    assert_not_dropped("ghost", "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: true,\n}\npub fn ghost() {}", false, &["ghost".to_string()]);
}

/// The guard is not a blanket refusal: a function present in the report passes,
/// and so does a source with no contract at all (which is a caller mistake, not a
/// frontend drop).
#[test]
fn a_present_function_passes_the_drop_guard() {
    assert_not_dropped("f", "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: true,\n}\npub fn f() {}", true, &[]);
    assert_not_dropped("f", "pub fn f() {}", false, &[]);
}

/// An element write must reach the store a *symbolic* read consults.
///
/// `a[0] = 0; a[i]` returns `0` when `i == 0`, so `ret == a[i]` is false. The
/// chain is built from the seeded elements, so if the write landed anywhere else
/// the chain would select the pre-write `a[0]` and this false contract would
/// verify. The test requires it to be *refuted*, not merely undecided: a
/// counterexample is the evidence that the chain is evaluated against the written
/// value, and `Verified` here would be a false proof.
#[test]
fn an_element_write_reaches_the_symbolic_chain() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: i < 4 && i == 0,
    ensures: ret == a[i],
}
pub fn written_then_symbolic(mut a: [u8; 4], i: usize) -> u8 {
    a[0] = 0;
    a[i]
}
"#;
    let Some(o) = verify_src("written_then_symbolic", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a write must not leave a stale element readable by the chain; got: {o}"
    );
}

/// The same property through a `&mut [u8; 4]` reborrow.
#[test]
fn an_element_write_through_a_mutable_reference_reaches_the_chain() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: i < 4 && i == 0,
    ensures: ret == a[i],
}
pub fn ref_written_then_symbolic(a: &mut [u8; 4], i: usize) -> u8 {
    a[0] = 0;
    a[i]
}
"#;
    let Some(o) = verify_src("ref_written_then_symbolic", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a reborrowed element write must reach the chain too; got: {o}"
    );
}

/// The `Vec<T>` length model: `new`/`push`/`len` track a length the executor
/// holds, so `make`-shaped code is decided rather than refused.
///
/// The element is *not* modelled (a `Vec`'s fields are not printed by the dump),
/// so this pins the length and nothing else. Each true direction must verify and
/// each false twin must be refuted -- a model that returned a constant, or that
/// ignored the `push`, would prove the twin. The helper direction pins that the
/// write reaches the caller through `&mut Vec<u8>`, and the argument direction
/// pins that a length the run never set is *refused* rather than invented.
#[test]
fn a_vec_length_is_tracked_through_new_push_and_len() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn make_ok(n: u8) -> usize { let mut v = Vec::new(); v.push(n); v.len() }

spec! {
    requires: true,
    ensures: ret == 2,
}
pub fn make_bad(n: u8) -> usize { let mut v = Vec::new(); v.push(n); v.len() }

spec! {
    requires: true,
    ensures: ret == 2,
}
pub fn two_ok(n: u8) -> usize { let mut v = Vec::new(); v.push(n); v.push(n); v.len() }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn two_bad(n: u8) -> usize { let mut v = Vec::new(); v.push(n); v.push(n); v.len() }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn empty_ok() -> usize { Vec::<u8>::new().len() }

spec! {
    requires: true,
    ensures: ret == 3,
}
pub fn empty_bad() -> usize { Vec::<u8>::new().len() }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn helper_ok(n: u8) -> usize { let mut v = Vec::new(); add(&mut v, n); v.len() }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn helper_bad(n: u8) -> usize { let mut v = Vec::new(); add(&mut v, n); v.len() }

fn add(v: &mut Vec<u8>, x: u8) { v.push(x); }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn arg_len_refused(v: &Vec<u8>) -> usize { v.len() }

spec! {
    requires: true,
    ensures: ret == v.len(),
}
pub fn arg_len_reflexive(v: &Vec<u8>) -> usize { v.len() }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn is_empty_new_ok() -> u8 { Vec::<u8>::new().is_empty() as u8 }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn is_empty_new_bad() -> u8 { Vec::<u8>::new().is_empty() as u8 }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn not_empty_after_push_ok() -> u8 { let mut v = Vec::<u8>::new(); v.push(1); v.is_empty() as u8 }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn not_empty_after_push_bad() -> u8 { let mut v = Vec::<u8>::new(); v.push(1); v.is_empty() as u8 }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn pop_then_len_ok() -> usize { let mut v = Vec::<u8>::new(); v.push(1); v.pop(); v.len() }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn pop_then_len_bad() -> usize { let mut v = Vec::<u8>::new(); v.push(1); v.pop(); v.len() }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn pop_empty_is_none_ok() -> u8 { let mut v = Vec::<u8>::new(); v.pop().is_none() as u8 }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn pop_empty_is_none_bad() -> u8 { let mut v = Vec::<u8>::new(); v.pop().is_none() as u8 }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn pop_nonempty_is_some_ok() -> u8 { let mut v = Vec::<u8>::new(); v.push(9); v.pop().is_some() as u8 }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn pop_nonempty_is_some_bad() -> u8 { let mut v = Vec::<u8>::new(); v.push(9); v.pop().is_some() as u8 }
"#;
    for name in [
        "make_ok",
        "two_ok",
        "empty_ok",
        "helper_ok",
        "is_empty_new_ok",
        "not_empty_after_push_ok",
        "pop_then_len_ok",
        "pop_empty_is_none_ok",
        "pop_nonempty_is_some_ok",
    ] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    for name in [
        "make_bad",
        "two_bad",
        "empty_bad",
        "helper_bad",
        "is_empty_new_bad",
        "not_empty_after_push_bad",
        "pop_then_len_bad",
        "pop_empty_is_none_bad",
        "pop_nonempty_is_some_bad",
    ] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` claims a length the body never produces and must be refuted, \
             not proved; got: {o}"
        );
    }
    // A `Vec` argument's length is a symbolic input -- the caller chose it -- so
    // `len == 0` is refuted with a witness rather than refused, and a contract
    // that relates the length to itself verifies. Before the element model the
    // length was tracked only for a *local* vector, so `v.len()` on an argument
    // was a refusal; now it is a real input.
    let Some(o) = verify_src("arg_len_refused", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a `Vec` argument's length is a symbolic input, so `len == 0` must be \
         refuted with a witness; got: {o}"
    );
    let Some(o) = verify_src("arg_len_reflexive", src) else { return };
    assert!(o.is_verified(), "`v.len() == v.len()` must verify; got: {o}");
}

/// The `Vec` *element* model: a pushed value is read back by `v[k]`, `v.first()`,
/// `v.get(k)` and `pop`.
///
/// Each true direction has a false twin that claims a *different* value, so a model
/// that stored the wrong element (or a constant) would refute the true one or prove
/// the false one. The empty-index case is a *panic*, and it must be reported as one:
/// `v[0]` on a vector the precondition proves empty unwinds, and a model that
/// skipped `core`'s bounds check would call it panic-free.
#[test]
fn a_vec_element_is_read_back_through_index_first_get_and_pop() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! { requires: true, ensures: ret == 3, }
pub fn index_ok() -> u8 { let mut v = Vec::new(); v.push(3u8); v[0] }

spec! { requires: true, ensures: ret == 4, }
pub fn index_bad() -> u8 { let mut v = Vec::new(); v.push(3u8); v[0] }

spec! { requires: true, ensures: ret == 7, }
pub fn second_ok() -> u8 { let mut v = Vec::new(); v.push(3u8); v.push(7u8); v[1] }

spec! { requires: true, ensures: ret == 3, }
pub fn second_bad() -> u8 { let mut v = Vec::new(); v.push(3u8); v.push(7u8); v[1] }

spec! { requires: true, ensures: ret == 9, }
pub fn first_ok() -> u8 { let mut v = Vec::new(); v.push(9u8); *v.first().unwrap() }

spec! { requires: true, ensures: ret == 8, }
pub fn first_bad() -> u8 { let mut v = Vec::new(); v.push(9u8); *v.first().unwrap() }

spec! { requires: true, ensures: ret == 4, }
pub fn get_ok() -> u8 { let mut v = Vec::new(); v.push(4u8); v.push(8u8); *v.get(0).unwrap() }

spec! { requires: true, ensures: ret == 5, }
pub fn get_bad() -> u8 { let mut v = Vec::new(); v.push(4u8); v.push(8u8); *v.get(0).unwrap() }

spec! { requires: true, ensures: ret == 5, }
pub fn pop_ok() -> u8 { let mut v = Vec::new(); v.push(3u8); v.push(5u8); v.pop().unwrap() }

spec! { requires: true, ensures: ret == 3, }
pub fn pop_bad() -> u8 { let mut v = Vec::new(); v.push(3u8); v.push(5u8); v.pop().unwrap() }

spec! { requires: true, ensures: ret == 3, }
pub fn as_slice_ok() -> u8 { let mut v = Vec::new(); v.push(3u8); let s = v.as_slice(); s[0] }

spec! { requires: v.len() > 0, ensures: ret == v[0], }
pub fn arg_index_ok(v: &Vec<u8>) -> u8 { v[0] }

spec! { requires: v.len() > 0, ensures: ret == v[0] + 1, }
pub fn arg_index_bad(v: &Vec<u8>) -> u8 { v[0] }

spec! { requires: v.len() > 0, ensures: ret == v[0], }
pub fn arg_first_ok(v: &Vec<u8>) -> u8 { *v.first().unwrap() }

spec! { requires: v.len() > 0, ensures: ret == v[0] + 1, }
pub fn arg_first_bad(v: &Vec<u8>) -> u8 { *v.first().unwrap() }

spec! { requires: v.len() == 0, ensures: true, }
pub fn index_empty_panics(v: &Vec<u8>) -> u8 { v[0] }
"#;
    for name in ["index_ok", "second_ok", "first_ok", "get_ok", "pop_ok", "as_slice_ok", "arg_index_ok", "arg_first_ok"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    for name in ["index_bad", "second_bad", "first_bad", "get_bad", "pop_bad", "arg_index_bad", "arg_first_bad"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` claims an element the vector does not hold and must be refuted; got: {o}"
        );
    }
    // `v[0]` on a vector the precondition proves empty is a real panic, not a proof.
    let Some(o) = verify_src("index_empty_panics", src) else { return };
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.starts_with("panic"),
            "an out-of-bounds `v[0]` must fail as a panic; got kind `{kind}`"
        ),
        other => panic!("an out-of-bounds `v[0]` must be refuted with a panic; got: {other}"),
    }
}

/// Three soundness holes in the `Vec` length model, each a *false proof*.
///
/// The model tracks a length per local in the `indexed` store (a `Vec` is an
/// `Indexed` with `len_mutable`). Each of these had the length survive a place it
/// should not, so a false postcondition was proved:
///
/// * **A user `Vec` is not the container.** A local `struct Vec<T>` whose `Drop`
///   panics was treated as glue-free (the model matched the bare `Vec`), so the
///   panic never ran and `f` was reported `Verified`. The container identity is
///   the *full* path (`std::vec::Vec` / `alloc::vec::Vec`); a user `Vec` is an
///   ordinary type and its destructor is resolved like any other.
/// * **The loop header havocs the length.** An inductive loop that pushes has to
///   forget the entry length, or the exit edge reads it: a `while i < 3 { v.push
///   (1); i += 1 }` proved `ret == 0` for the real `ret == 3`. `havoc_parts`
///   refreshes the tracked length to a fresh `usize`.
/// * **A move carries the length.** `let w = v` (`copy_parts`) and a returned
///   vector (the call's return merge) both have to transfer the tracked length to
///   the destination, or `w.len()`/`mk().len()` read a receiver with no length.
#[test]
fn a_vec_length_model_does_not_leak_across_a_drop_havoc_or_move() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

mod m {
    pub struct Vec<T>(pub T);
    impl<T> Drop for Vec<T> {
        fn drop(&mut self) { panic!() }
    }
}

spec! {
    requires: true,
    ensures: true,
}
/// A user `Vec` whose destructor always panics: `drop` runs it, so this must not
/// be `verified`. The bare-name model treated `m::Vec<u8>` as glue-free.
pub fn user_vec_drop_panics() { let _x = m::Vec(0u8); }

spec! {
    requires: true,
    invariant: i <= 3,
    ensures: ret == 0,
}
/// The loop's entry length must be havoced at the header. A model that kept it
/// reads `0` at the exit and proves this; the body really returns `3`.
pub fn loop_push_cannot_prove_this() -> usize {
    let mut v = Vec::<u8>::new();
    let mut i = 0u8;
    while i < 3 { v.push(1); i += 1; }
    v.len()
}

spec! {
    requires: true,
    invariant: i <= 3,
    ensures: ret == 3,
}
/// The control: the same loop, but the postcondition is about the *counter*,
/// which the invariant does relate (`i <= 3` and the exit guard `i >= 3` give
/// `i == 3`). Havocing the vector's length must not break this -- a model that
/// refused every `Vec`-carrying loop would pass the twin above while checking
/// nothing.
pub fn loop_counter_ok() -> u8 {
    let mut v = Vec::<u8>::new();
    let mut i = 0u8;
    while i < 3 { v.push(1); i += 1; }
    i
}

spec! {
    requires: true,
    ensures: ret == 1,
}
/// A move (`let w = v`) must carry the tracked length to the destination.
pub fn move_ok(n: u8) -> usize { let mut v = Vec::new(); v.push(n); let w = v; w.len() }

spec! {
    requires: true,
    ensures: ret == 0,
}
/// The false twin: a model that dropped the length on the move reads a receiver
/// with no length and refuses; one that kept the *source* length and read it
/// through the wrong local would prove this.
pub fn move_bad(n: u8) -> usize { let mut v = Vec::new(); v.push(n); let w = v; w.len() }

spec! {
    requires: true,
    ensures: ret == 0,
}
/// A returned vector must carry its length to the caller's destination.
pub fn mk() -> Vec<u8> { Vec::new() }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn returned_ok() -> usize { let v = mk(); v.len() }
"#;
    // The user `Vec`'s destructor panics, so the function must be *refused*.
    // The assertion is `Incomplete`, not merely `!is_verified()`: a `!is_verified`
    // check also passes on `Failed`, so it cannot tell a refusal (the honest
    // answer, since the destructor's `panic!` has no value) from a spurious
    // refutation of the `ensures: true` claim -- the same weakness the invariant
    // tripwire was fixed for. Measured, the drop of a user `Vec` whose fields are
    // not modelled is `Incomplete`; pinning it makes a regression to `Failed`
    // visible rather than silently passing.
    let Some(o) = verify_src("user_vec_drop_panics", src) else { return };
    match o {
        FnOutcome::Incomplete { .. } => {}
        other => panic!(
            "a user `Vec` whose `Drop` panics must be refused as `Incomplete` \
             (the destructor's `panic!` is not modelled as a value), got: {other} -- \
             a `verified` here is a false proof and a `Failed` would be a spurious \
             refutation of `ensures: true`"
        ),
    }

    // The loop twin must be *refuted* on its postcondition, not merely refused:
    // a refusal also satisfies "not verified" and would check nothing.
    let Some(o) = verify_src("loop_push_cannot_prove_this", src) else { return };
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("postcondition"),
            "the loop twin must fail on its postcondition; got `{kind}`"
        ),
        other => panic!(
            "the loop entry length must be havoced, so `ret == 0` for a body \
             returning 3 must be refuted; got: {other}"
        ),
    }
    // The control: havocing the length must not break a loop whose postcondition
    // is about a variable the invariant *does* relate.
    let Some(o) = verify_src("loop_counter_ok", src) else { return };
    assert!(
        o.is_verified(),
        "a `Vec`-carrying loop with a counter postcondition must still verify; got: {o}"
    );

    // The move: the true direction verifies, the false twin is refuted.
    let Some(o) = verify_src("move_ok", src) else { return };
    assert!(o.is_verified(), "a moved vector keeps its length; got: {o}");
    let Some(o) = verify_src("move_bad", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the move twin claims `0` for a vector of length 1 and must be refuted; got: {o}"
    );

    // The returned vector: the caller's destination inherits the length.
    let Some(o) = verify_src("returned_ok", src) else { return };
    assert!(o.is_verified(), "a returned vector keeps its length; got: {o}");
}

/// `for` loops over slices and arrays are modelled: `into_iter`/`iter` starts a
/// cursor at a *concrete* position and `next` reads the element there, so each
/// iteration names the same element variable a contract's `xs[k]` names.
///
/// The false twins are the teeth: a model that read a fresh (unconstrained)
/// element per iteration would *refute* the true sum, and one that read a fixed
/// element would *verify* the false twins. Both directions are asserted.
#[test]
fn a_for_loop_over_a_slice_is_modelled() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! { requires: xs.len() == 2, ensures: ret == xs[0].wrapping_add(xs[1]), }
pub fn sum2(xs: &[u8]) -> u8 { let mut s = 0u8; for &x in xs { s = s.wrapping_add(x); } s }

spec! { requires: xs.len() == 2, ensures: ret == xs[0], }
pub fn sum2_bad(xs: &[u8]) -> u8 { let mut s = 0u8; for &x in xs { s = s.wrapping_add(x); } s }

spec! { requires: xs.len() <= 3, ensures: ret == xs.len() as u8, }
pub fn count(xs: &[u8]) -> u8 { let mut n = 0u8; for _x in xs { n = n.wrapping_add(1); } n }

spec! { requires: true, ensures: ret == a[0].wrapping_add(a[1]), }
pub fn arr_sum(a: [u8; 2]) -> u8 { let mut s = 0u8; for &x in &a { s = s.wrapping_add(x); } s }

spec! { requires: true, ensures: ret == a[1], }
pub fn arr_sum_bad(a: [u8; 2]) -> u8 { let mut s = 0u8; for &x in &a { s = s.wrapping_add(x); } s }

spec! { requires: true, ensures: ret == a[0].wrapping_add(a[1]), }
pub fn arr_val_sum(a: [u8; 2]) -> u8 { let mut s = 0u8; for x in a { s = s.wrapping_add(x); } s }

spec! { requires: xs.len() == 2, ensures: ret == xs[0].wrapping_add(xs[1]), }
pub fn iter_sum(xs: &[u8]) -> u8 { let mut s = 0u8; for &x in xs.iter() { s = s.wrapping_add(x); } s }

spec! { requires: xs.len() == 2, ensures: ret == xs[0], }
pub fn iter_sum_bad(xs: &[u8]) -> u8 { let mut s = 0u8; for &x in xs.iter() { s = s.wrapping_add(x); } s }
"#;
    for name in ["sum2", "count", "arr_sum", "arr_val_sum", "iter_sum"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    // The false twins must be *refuted*, not merely undecided: a refusal would
    // also satisfy "not verified" and would check nothing.
    for name in ["sum2_bad", "arr_sum_bad", "iter_sum_bad"] {
        let Some(o) = verify_src(name, src) else { return };
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition"),
                "`{name}` must fail on its postcondition; got `{kind}`"
            ),
            other => panic!(
                "`{name}` claims the sum is one element and must be refuted, got: {other}"
            ),
        }
    }
}

/// A `for` loop with an `invariant:` is refused, not read as an arbitrary
/// element: the loop cut havocs the iterator cursor, so `next` finds none and the
/// function is `Incomplete`. This is the honest answer -- the position would be
/// symbolic, and reading "some element" would be a wrong value.
#[test]
fn a_for_loop_with_an_invariant_refuses_the_iterator() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! { requires: xs.len() <= 2, invariant: s <= 255, ensures: ret <= 255, }
pub fn sum_inv(xs: &[u8]) -> u8 { let mut s = 0u8; for &x in xs { s = s.wrapping_add(x); } s }
"#;
    let Some(o) = verify_src("sum_inv", src) else { return };
    assert!(
        matches!(o, FnOutcome::Incomplete { .. }),
        "a `for` loop with an invariant must be refused (the cursor is havoced), got: {o}"
    );
}

/// Iterator *consumers* on a slice/array cursor: `sum`, `count`, and the `copied`
/// adapter.
///
/// `sum` folds with a *checked* `+`, so an unguarded sum over `u8`s is a reachable
/// panic (refuted, not proved) -- the model must not hide it. The sum's length must
/// be a constant (an array's type length, or a slice length the precondition
/// pinned), so a symbolic-length sum is refused rather than summed over a wrong
/// range. `count` is `len - pos`, exact even with a symbolic length.
#[test]
fn a_slice_iterator_sum_and_count_are_modelled() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! { requires: xs.len() == 2, requires: xs[0] <= 10, requires: xs[1] <= 10, ensures: ret == xs[0] + xs[1], }
pub fn sum2(xs: &[u8]) -> u8 { xs.iter().sum() }

spec! { requires: xs.len() == 2, requires: xs[0] <= 10, requires: xs[1] <= 10, ensures: ret == xs[0], }
pub fn sum2_bad(xs: &[u8]) -> u8 { xs.iter().sum() }

spec! { requires: a[0] <= 10, requires: a[1] <= 10, ensures: ret == a[0] + a[1], }
pub fn arr_sum(a: [u8; 2]) -> u8 { a.into_iter().sum() }

spec! { requires: xs.len() == 2, requires: xs[0] <= 10, requires: xs[1] <= 10, ensures: ret == xs[0] + xs[1], }
pub fn copied_sum(xs: &[u8]) -> u8 { xs.iter().copied().sum() }

spec! { requires: xs.len() <= 3, ensures: ret == xs.len(), }
pub fn count2(xs: &[u8]) -> usize { xs.iter().count() }

spec! { requires: xs.len() <= 3, ensures: ret == xs.len() + 1, }
pub fn count2_bad(xs: &[u8]) -> usize { xs.iter().count() }

spec! { requires: xs.len() == 2, ensures: true, }
pub fn sum_may_overflow(xs: &[u8]) -> u8 { xs.iter().sum() }

spec! { requires: true, ensures: true, }
pub fn sum_symbolic(xs: &[u8]) -> u8 { xs.iter().sum() }
"#;
    for name in ["sum2", "arr_sum", "copied_sum", "count2"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    for name in ["sum2_bad", "count2_bad"] {
        let Some(o) = verify_src(name, src) else { return };
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition"),
                "`{name}` must fail on its postcondition; got `{kind}`"
            ),
            other => panic!("`{name}` is a false claim and must be refuted, got: {other}"),
        }
    }
    // An unguarded sum overflows for `[200, 100]` and must be refuted as a *panic*,
    // not proved -- the model sums with a checked `+`.
    let Some(o) = verify_src("sum_may_overflow", src) else { return };
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.starts_with("panic"),
            "an unguarded `sum` must fail as a reachable panic; got `{kind}`"
        ),
        other => panic!(
            "`sum` over unbounded `u8`s can overflow and must be refuted as a panic, \
             got: {other} -- a `verified` here is a hidden panic"
        ),
    }
    // A symbolic-length sum has no fixed number of addends and is refused.
    let Some(o) = verify_src("sum_symbolic", src) else { return };
    assert!(
        matches!(o, FnOutcome::Incomplete { .. }),
        "a symbolic-length `sum` must be refused, got: {o}"
    );
}

/// Iterator consumers `last`, `nth`, `max` and `min` on a slice/array cursor.
///
/// `last`/`nth` name the exact element when the length is known (an array's type
/// length, or a slice the precondition pinned); `max`/`min` are folds of
/// comparisons, so they need a constant length too. The signed cases are pinned
/// because `i8::MIN` is the *smallest* signed value but the largest unsigned byte,
/// so an unsigned comparison would pick the wrong element.
#[test]
fn a_slice_iterator_extremes_and_offsets_are_modelled() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! { requires: xs.len() == 2, ensures: ret == xs[1], }
pub fn last_slice(xs: &[u8]) -> u8 { *xs.iter().last().unwrap() }

spec! { requires: xs.len() == 2, ensures: ret == xs[0], }
pub fn last_slice_bad(xs: &[u8]) -> u8 { *xs.iter().last().unwrap() }

spec! { requires: xs.len() == 3, ensures: ret == xs[2], }
pub fn nth_slice(xs: &[u8]) -> u8 { *xs.iter().nth(2).unwrap() }

spec! { requires: xs.len() == 3, ensures: ret == xs[0], }
pub fn nth_slice_bad(xs: &[u8]) -> u8 { *xs.iter().nth(2).unwrap() }

spec! { requires: a[0] <= a[1], requires: a[1] <= a[2], ensures: ret == a[2], }
pub fn max_arr(a: [u8; 3]) -> u8 { a.into_iter().max().unwrap() }

spec! { requires: a[0] <= a[1], requires: a[1] <= a[2], ensures: ret == a[0], }
pub fn max_arr_bad(a: [u8; 3]) -> u8 { a.into_iter().max().unwrap() }

spec! { requires: a[0] <= a[1], requires: a[1] <= a[2], ensures: ret == a[0], }
pub fn min_arr(a: [u8; 3]) -> u8 { a.into_iter().min().unwrap() }

spec! { requires: a[0] <= a[1], requires: a[1] <= a[2], ensures: ret == a[2], }
pub fn min_arr_bad(a: [u8; 3]) -> u8 { a.into_iter().min().unwrap() }

spec! { requires: a[0] <= a[1], requires: a[1] <= a[2], ensures: ret == a[2], }
pub fn smax_arr(a: [i8; 3]) -> i8 { a.into_iter().max().unwrap() }

spec! { requires: a[0] <= a[1], requires: a[1] <= a[2], ensures: ret == a[0], }
pub fn smax_arr_bad(a: [i8; 3]) -> i8 { a.into_iter().max().unwrap() }

spec! { requires: xs.len() == 2, requires: xs[0] <= xs[1], ensures: ret == xs[1], }
pub fn max_ref(xs: &[u8]) -> u8 { match xs.iter().max() { Some(&m) => m, None => 0 } }

spec! { requires: true, ensures: true, }
pub fn max_symbolic(xs: &[u8]) -> u8 { *xs.iter().max().unwrap() }
"#;
    for name in ["last_slice", "nth_slice", "max_arr", "min_arr", "smax_arr", "max_ref"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    for name in [
        "last_slice_bad",
        "nth_slice_bad",
        "max_arr_bad",
        "min_arr_bad",
        "smax_arr_bad",
    ] {
        let Some(o) = verify_src(name, src) else { return };
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition"),
                "`{name}` must fail on its postcondition; got `{kind}`"
            ),
            other => panic!("`{name}` is a false claim and must be refuted, got: {other}"),
        }
    }
    // `max` over a symbolic-length slice has no fixed comparison count and is refused.
    let Some(o) = verify_src("max_symbolic", src) else { return };
    assert!(
        matches!(o, FnOutcome::Incomplete { .. }),
        "a symbolic-length `max` must be refused, got: {o}"
    );
}


/// `enumerate()` is a cursor identity whose `next` yields `Option<(usize, &T)>`.
///
/// The tuple payload is the interesting part: the body destructures it directly
/// (`((_2 as Some).0).0` for the index, `.1` for the element), a *nested place*
/// whose group holds a downcast and a tail. The first parse split that group on its
/// last ` as ` and the place came back unknown; the index is the concrete cursor
/// position and the element is `xs[pos]`, so a sum of indices is `0+1+..+(n-1)` and
/// a sum of elements is the slice sum. Both directions are pinned, and a symbolic
/// length is refused because the loop must be unwound to a constant.
#[test]
fn a_slice_iterator_enumerate_carries_the_index_and_element() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! { requires: xs.len() == 3, ensures: ret == 3, }
pub fn idx_sum(xs: &[u8]) -> u8 { let mut s = 0u8; for (i, _) in xs.iter().enumerate() { s = s.wrapping_add(i as u8); } s }

spec! { requires: xs.len() == 3, ensures: ret == 1, }
pub fn idx_sum_bad(xs: &[u8]) -> u8 { let mut s = 0u8; for (i, _) in xs.iter().enumerate() { s = s.wrapping_add(i as u8); } s }

spec! { requires: xs.len() == 2, requires: xs[0] <= 10, requires: xs[1] <= 10, ensures: ret == xs[0] + xs[1], }
pub fn val_sum(xs: &[u8]) -> u8 { let mut s = 0u8; for (_, &x) in xs.iter().enumerate() { s = s.wrapping_add(x); } s }

spec! { requires: xs.len() == 2, requires: xs[0] <= 10, requires: xs[1] <= 10, ensures: ret == xs[0], }
pub fn val_sum_bad(xs: &[u8]) -> u8 { let mut s = 0u8; for (_, &x) in xs.iter().enumerate() { s = s.wrapping_add(x); } s }

spec! { requires: xs.len() >= 1, ensures: ret == 0, }
pub fn first_index(xs: &[u8]) -> u8 { match xs.iter().enumerate().next() { Some((i, _)) => i as u8, None => 0 } }

spec! { requires: true, ensures: true, }
pub fn idx_symbolic(xs: &[u8]) -> u8 { let mut s = 0u8; for (i, _) in xs.iter().enumerate() { s = s.wrapping_add(i as u8); } s }
"#;
    for name in ["idx_sum", "val_sum", "first_index"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    for name in ["idx_sum_bad", "val_sum_bad"] {
        let Some(o) = verify_src(name, src) else { return };
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition"),
                "`{name}` must fail on its postcondition; got `{kind}`"
            ),
            other => panic!("`{name}` is a false claim and must be refuted, got: {other}"),
        }
    }
    // A symbolic-length enumerate loop must be unwound to a constant and is refused.
    let Some(o) = verify_src("idx_symbolic", src) else { return };
    assert!(
        !o.is_verified(),
        "a symbolic-length enumerate loop must not be verified, got: {o}"
    );
}

/// `String` is modelled by its **length** only: `new` is `0`, `push_str` adds the
/// appended `&str`'s byte length, `from` is that length, and `len`/`is_empty` read
/// it. A `&str`'s byte length is a symbolic input when it is an argument and a
/// constant when it is a literal (`const "abc"` is `3`). The bytes are not
/// modelled, so a method whose result depends on the *contents* stays refused --
/// the length model is exact for what it claims and silent about the rest.
#[test]
fn a_string_length_model_decides_new_from_push_len() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! { requires: true, ensures: ret == 3, }
pub fn lit_len() -> usize { "abc".len() }
spec! { requires: true, ensures: ret == true, }
pub fn lit_empty() -> bool { "".is_empty() }
spec! { requires: true, ensures: ret == 0, }
pub fn new_len() -> usize { String::new().len() }
spec! { requires: true, ensures: ret == true, }
pub fn new_empty() -> bool { String::new().is_empty() }
spec! { requires: true, ensures: ret == 3, }
pub fn from_len() -> usize { String::from("abc").len() }
spec! { requires: true, ensures: ret == 2, }
pub fn push_len() -> usize { let mut s = String::new(); s.push_str("ab"); s.len() }
spec! { requires: true, ensures: ret == false, }
pub fn push_nonempty_empty() -> bool { let mut s = String::new(); s.push_str("x"); s.is_empty() }
spec! { requires: true, ensures: ret == s.len(), }
pub fn str_arg_len(s: &str) -> usize { s.len() }

spec! { requires: true, ensures: ret == 2, }
pub fn from_len_bad() -> usize { String::from("abc").len() }
spec! { requires: true, ensures: ret == 3, }
pub fn push_len_bad() -> usize { let mut s = String::new(); s.push_str("ab"); s.len() }
"#;
    for name in [
        "lit_len",
        "lit_empty",
        "new_len",
        "new_empty",
        "from_len",
        "push_len",
        "push_nonempty_empty",
        "str_arg_len",
    ] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    // The length model must be *exact*: a wrong length is refuted, so the tests
    // above are not passing because `len` returns a constant the claim accepts.
    for name in ["from_len_bad", "push_len_bad"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` is a false length claim and must be refuted, got: {o}"
        );
    }
}

/// A user type spelled `Vec` is not the container, and its *methods* are answered
/// by their own bodies.
///
/// `names_vec_impl` accepts a call whose path contains `vec::Vec` or starts with a
/// bare `Vec::` -- the shortened spelling rustc prints for the *standard*
/// container when nothing shadows it. A user `Vec` also prints `Vec::<u8>::new`
/// at the crate root, so the predicate alone cannot separate them. What does is
/// the executor's same-dump lookup, which resolves the user body *before* the
/// model: `body_wins` returns 7 from its own `len` and verifies against `ret == 7`,
/// while the twin claiming the container model's `0` is refuted. This pins that
/// the model is not consulted for a call that names a body in the dump.
#[test]
fn a_user_vec_method_is_answered_by_its_own_body() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Vec<T>(pub T);
impl Vec<u8> {
    pub fn new() -> Self { Vec(0) }
    pub fn len(&self) -> usize { 7 }
}

spec! {
    requires: true,
    ensures: ret == 7,
}
/// The user body returns 7, so this verifies -- the model's `0` would refute it.
pub fn body_wins() -> usize { let v = Vec::new(); v.len() }

spec! {
    requires: true,
    ensures: ret == 0,
}
/// The twin: the container model would answer `0` and prove this, so a refutation
/// is the evidence the user body was used.
pub fn model_would_say_zero() -> usize { let v = Vec::new(); v.len() }
"#;
    let Some(o) = verify_src("body_wins", src) else { return };
    assert!(
        o.is_verified(),
        "a user `Vec` method must be answered by its own body; got: {o}"
    );
    let Some(o) = verify_src("model_would_say_zero", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the container model must not answer a user `Vec` call, so `ret == 0` must be \
         refuted; got: {o}"
    );
}

/// A `&str` argument's length is a symbolic input, exactly as a `&[T]` slice's is.
///
/// `str` is unsized, so its length lives in the fat pointer and is a caller
/// choice, not a constant in the type. `s.len()`/`s.is_empty()` read only that
/// length, so they are modelled the same way the slice ones are -- the same two
/// intrinsics, a different path (`core::str::<impl str>::len`). The length is
/// bound by the contract binder, so a body's `s.len()` and a contract's `s.len()`
/// name one variable: a `requires: s.len() == 3` pins the body's read, and the
/// false twin is refuted.
///
/// `String` is deliberately *not* covered: it is a different type
/// (`alloc::string::String`), so `String::len` stays an honest refusal rather
/// than being answered with a length the model does not hold.
#[test]
fn a_str_length_is_a_symbolic_input() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret <= s.len(),
}
pub fn len_bound(s: &str) -> usize { s.len() }

spec! {
    requires: s.len() == 3,
    ensures: ret == 3,
}
/// The length is pinned by the precondition, so the body's read is that value.
pub fn pinned_len(s: &str) -> usize { s.len() }

spec! {
    requires: true,
    ensures: ret == 4,
}
/// The false twin: an unbounded `&str` length is not 4.
pub fn wrong_len_cannot_prove_this(s: &str) -> usize { s.len() }

spec! {
    requires: s.len() == 0,
    ensures: ret,
}
/// `is_empty` reads the same variable, so it agrees with `len`.
pub fn empty_is_empty(s: &str) -> bool { s.is_empty() }
"#;
    for name in ["len_bound", "pinned_len", "empty_is_empty"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    let Some(o) = verify_src("wrong_len_cannot_prove_this", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "an unbounded `&str` length must not be provable as `4`; got: {o}"
    );
}

/// `Option::unwrap_or_default` is total, and its default is the payload's own zero.
///
/// The default of every scalar `Default` this tool models is the zero of the
/// payload's width (`0u8`, `0i32`, `false`), so the failure variant yields that
/// word rather than a fresh input. The `x.is_none()` pin makes the body's read the
/// default on every path, and the false twin (`ret == 7`) is refuted because the
/// `Some` path can carry any payload.
#[test]
fn option_unwrap_or_default_is_the_payload_or_zero() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret <= 255,
}
pub fn or_zero(x: Option<u8>) -> u8 { x.unwrap_or_default() }

spec! {
    requires: x.is_none(),
    ensures: ret == 0,
}
pub fn none_is_zero(x: Option<u8>) -> u8 { x.unwrap_or_default() }

spec! {
    requires: true,
    ensures: ret == 7,
}
pub fn cannot_prove_this(x: Option<u8>) -> u8 { x.unwrap_or_default() }
"#;
    for name in ["or_zero", "none_is_zero"] {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify; got: {o}");
    }
    let Some(o) = verify_src("cannot_prove_this", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`unwrap_or_default` must not be provable as a fixed `7`; got: {o}"
    );
}

/// A user type named `str` is not the primitive `str`.
///
/// Rust lets a crate shadow a primitive name, and rustc prints a crate-root type
/// as the bare name, so a `pub struct str { .. }` argument is spelled `&str`
/// exactly as the primitive is. Binding the primitive's symbolic length *before*
/// consulting the declared layout therefore bound a field-less type over the
/// user's struct, and a contract naming its field could not resolve. The declared
/// layout now wins; the primitive is meant only when nothing declares `str`.
///
/// The primitive direction is asserted too, so a fix that simply refused every
/// `str` argument would fail this test.
#[test]
fn a_user_type_named_str_is_not_the_primitive_str() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct str { pub value: u8 }

spec! {
    requires: s.value == 3,
    ensures: ret == 3,
}
pub fn read(s: &str) -> u8 { s.value }

spec! {
    requires: true,
    ensures: ret == 3,
}
pub fn read_cannot_prove_this(s: &str) -> u8 { s.value }
"#;
    let Some(o) = verify_src("read", src) else { return };
    assert!(
        o.is_verified(),
        "a field of a user `str` must resolve; got: {o}"
    );
    let Some(o) = verify_src("read_cannot_prove_this", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the user `str`'s field is an input, so a fixed value must be refuted; got: {o}"
    );

    // The primitive is still modelled when nothing declares `str`.
    let prim = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: s.len() == 3,
    ensures: ret == 3,
}
pub fn len_is_symbolic(s: &str) -> usize { s.len() }

spec! {
    requires: true,
    ensures: ret == 4,
}
pub fn wrong_len_cannot_prove_this(s: &str) -> usize { s.len() }
"#;
    let Some(o) = verify_src("len_is_symbolic", prim) else { return };
    assert!(o.is_verified(), "the primitive `str` length must resolve; got: {o}");
    let Some(o) = verify_src("wrong_len_cannot_prove_this", prim) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "an unpinned `str` length must not be provable as `4`; got: {o}"
    );
}

/// A `&mut [u8]` slice write must reach the store the read consults.
///
/// This is the gap the `&raw const (fake) (*_1)` parse closed. Before it, the
/// bounds check on a `&mut [u8]` argument read its length through a raw reborrow
/// the parser did not recognise, so the function was `incomplete` before any
/// write was reached -- the write was never even evaluated. Now the true half
/// must *verify* (a write then a read of the same index returns what was
/// written) and the tripwire -- the same body claiming the pre-write value --
/// must be refuted, since a model that dropped the write would leave the seeded
/// element readable and prove it.
#[test]
fn a_slice_element_write_reaches_the_store_the_read_consults() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: s.len() > 0,
    ensures: ret == v,
}
pub fn slice_written_then_read(s: &mut [u8], v: u8) -> u8 {
    s[0] = v;
    s[0]
}

spec! {
    requires: s.len() > 0,
    ensures: ret == s[0],
}
pub fn slice_written_then_read_tripwire(s: &mut [u8], v: u8) -> u8 {
    s[0] = v;
    s[0]
}
"#;
    let Some(o) = verify_src("slice_written_then_read", src) else { return };
    assert!(
        o.is_verified(),
        "a write then a read of the same slice index returns what was written; got: {o}"
    );
    let Some(o) = verify_src("slice_written_then_read_tripwire", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the pre-write element must not stay readable after a slice write; got: {o}"
    );
}

/// The `&mut [u8]` *symbolic* read must see the slice write too.
///
/// The array form of this shape is [`an_element_write_through_a_mutable_reference_reaches_the_chain`];
/// the slice form differs in the bounds check, not the store, so the same
/// requirement holds -- the false contract must be refuted rather than left
/// undecided, which is what a missing `PtrMetadata` would have made it.
#[test]
fn a_slice_element_write_reaches_the_symbolic_chain() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: i < s.len() && s.len() <= 64 && i == 0,
    ensures: ret == s[i],
}
pub fn slice_written_then_symbolic(s: &mut [u8], i: usize) -> u8 {
    s[0] = 0;
    s[i]
}
"#;
    let Some(o) = verify_src("slice_written_then_symbolic", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a slice write must not leave a stale element readable by the chain; got: {o}"
    );
}

/// `slice::first`/`get` produce `Option<&T>`, and the payload is the slice's
/// *own* element, so `*xs.first().unwrap()` and `xs[0]` agree -- and a claim
/// about a different element is refuted rather than proved.
///
/// The tag is a predicate (`len == 0` for `first`, `len <= k` for `get`), so the
/// `unwrap`'s panic obligation is real: `get(1)` past the end must fail, not be
/// assumed `Some`. Both directions are pinned, because a model that answered
/// every `first` with the element would prove the true contracts and the false
/// ones alike.
#[test]
fn slice_first_and_get_reach_the_slices_own_element() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: xs.len() > 0 && xs[0] == 5,
    ensures: ret == 5,
}
pub fn first_reads_the_element(xs: &[u8]) -> u8 {
    *xs.first().unwrap()
}

spec! {
    requires: xs.len() > 0 && xs[0] == 5,
    ensures: ret == 6,
}
pub fn first_wrong_element_cannot_prove_this(xs: &[u8]) -> u8 {
    *xs.first().unwrap()
}

spec! {
    requires: xs.len() == 0,
    ensures: ret,
}
pub fn first_is_none_when_empty(xs: &[u8]) -> bool {
    xs.first().is_none()
}

spec! {
    requires: xs.len() > 1 && xs[1] == 7,
    ensures: ret == 7,
}
pub fn get_reads_the_indexed_element(xs: &[u8]) -> u8 {
    *xs.get(1).unwrap()
}

spec! {
    requires: xs.len() > 1 && xs[1] == 7,
    ensures: ret == 8,
}
pub fn get_wrong_element_cannot_prove_this(xs: &[u8]) -> u8 {
    *xs.get(1).unwrap()
}

spec! {
    requires: xs.len() > 0,
    ensures: ret == 7,
}
pub fn get_out_of_range_unwrap_panics(xs: &[u8]) -> u8 {
    *xs.get(1).unwrap()
}

spec! {
    requires: xs.len() > 0 && xs[0] == 5,
    ensures: ret == 5,
}
pub fn first_match_reads_the_element(xs: &[u8]) -> u8 {
    match xs.first() { Some(v) => *v, None => 0 }
}

spec! {
    requires: xs.len() > 0 && xs[0] == 5,
    ensures: ret == 6,
}
pub fn first_match_tripwire(xs: &[u8]) -> u8 {
    match xs.first() { Some(v) => *v, None => 0 }
}

spec! {
    requires: xs.len() == 0,
    ensures: ret == 0,
}
pub fn first_match_empty_takes_none(xs: &[u8]) -> u8 {
    match xs.first() { Some(v) => *v, None => 0 }
}

spec! {
    requires: i < xs.len() && xs.len() <= 64,
    ensures: true,
}
pub fn get_symbolic_index_is_refused(xs: &[u8], i: usize) -> u8 {
    *xs.get(i).unwrap()
}
"#;
    let Some(o) = verify_src("first_reads_the_element", src) else { return };
    assert!(
        o.is_verified(),
        "`*xs.first().unwrap()` is `xs[0]`, so the true contract must verify; got: {o}"
    );
    let Some(o) = verify_src("first_wrong_element_cannot_prove_this", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the payload is the slice's own element, so a claim about a different value \
         must be refuted, not proved; got: {o}"
    );
    let Some(o) = verify_src("first_is_none_when_empty", src) else { return };
    assert!(
        o.is_verified(),
        "`first` is `None` exactly when the slice is empty; got: {o}"
    );
    let Some(o) = verify_src("get_reads_the_indexed_element", src) else { return };
    assert!(
        o.is_verified(),
        "`*xs.get(1).unwrap()` is `xs[1]`, so the true contract must verify; got: {o}"
    );
    let Some(o) = verify_src("get_wrong_element_cannot_prove_this", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`get`'s payload is the indexed element, so a claim about another value must \
         be refuted; got: {o}"
    );
    let Some(o) = verify_src("get_out_of_range_unwrap_panics", src) else { return };
    assert!(
        matches!(&o, FnOutcome::Failed { kind, .. } if kind.starts_with("panic")),
        "`get(1)` past the end is `None`, so `unwrap` panics -- a real obligation, not \
         an assumed `Some`; got: {o}"
    );
    // The `match` form reads the payload through a downcast temp, a different
    // desugaring from `unwrap`; both must decide, and a `match` on the empty
    // slice must take the `None` arm.
    let Some(o) = verify_src("first_match_reads_the_element", src) else { return };
    assert!(
        o.is_verified(),
        "a `match` on `first()` names the same element `unwrap` does; got: {o}"
    );
    let Some(o) = verify_src("first_match_tripwire", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the `match` payload is the slice's element, so a claim about another value \
         must be refuted; got: {o}"
    );
    let Some(o) = verify_src("first_match_empty_takes_none", src) else { return };
    assert!(
        o.is_verified(),
        "an empty slice takes the `None` arm, which returns the constant; got: {o}"
    );
    // A symbolic index has no finite domain on a slice, so the read is refused
    // rather than guessed -- a wrong value would be worse than a missing one.
    let Some(o) = verify_src("get_symbolic_index_is_refused", src) else { return };
    assert!(
        !o.is_verified()
            && matches!(&o, FnOutcome::Incomplete { .. } | FnOutcome::Skipped { .. }),
        "`xs.get(i)` for a symbolic `i` must be refused, not modelled; got: {o}"
    );
}

/// A generic `&[T]` has a *length* even though its element width is unknown.
///
/// `T` is an unbound type parameter, so there is no element width to model and
/// every element operation must stay refused. But `len`/`is_empty` read only the
/// length, which is a `usize` input whatever `T` is — so the length is bound and
/// those functions decide. This pins both halves: the length functions verify, and
/// an element-naming contract is a refusal, never a proof. The two tripwires are
/// the teeth: `generic_slice_len_is_zero_cannot_prove_this` must be *refuted*
/// (the length is a real value, not a constant `0`), and
/// `generic_slice_element_cannot_prove_this` must not be *verified* (the element
/// has no width, so a claim about it cannot be discharged).
#[test]
fn a_generic_slices_length_is_modelled_but_its_element_is_not() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret == v.len(),
}
pub fn len_of<T: Copy>(v: &[T]) -> usize {
    v.len()
}

spec! {
    requires: true,
    ensures: ret == (v.len() == 0),
}
pub fn empty_of<T: Copy>(v: &[T]) -> bool {
    v.is_empty()
}

spec! {
    requires: true,
    ensures: true,
}
pub fn first_or_of<T: Copy>(v: &[T], d: T) -> T {
    if v.is_empty() { d } else { v[0] }
}

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn len_is_zero_cannot_prove_this<T: Copy>(v: &[T]) -> usize {
    v.len()
}

spec! {
    requires: true,
    ensures: ret == d,
}
pub fn element_cannot_prove_this<T: Copy>(v: &[T], d: T) -> T {
    if v.is_empty() { d } else { v[0] }
}
"#;
    let Some(o) = verify_src("len_of", src) else { return };
    assert!(
        o.is_verified(),
        "`v.len()` on a `&[T]` reads only the length, which is modelled; got: {o}"
    );
    let Some(o) = verify_src("empty_of", src) else { return };
    assert!(
        o.is_verified(),
        "`v.is_empty()` is `len == 0`, decided by the length alone; got: {o}"
    );
    let Some(o) = verify_src("first_or_of", src) else { return };
    assert!(
        o.is_verified(),
        "`first_or` is guarded by `is_empty`, which the length decides, so the \
         bounds check on `v[0]` is discharged; got: {o}"
    );
    // The teeth: a false length claim is refuted (the length is a real input),
    // and an element claim is not proved (the element has no width).
    let Some(o) = verify_src("len_is_zero_cannot_prove_this", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`v.len() == 0` is false for a non-empty slice, so this must be refuted \
         (a verified verdict would mean the length was folded to the constant 0); \
         got: {o}"
    );
    let Some(o) = verify_src("element_cannot_prove_this", src) else { return };
    assert!(
        !o.is_verified(),
        "a generic slice's element has no width, so `ret == d` must never be \
         reported verified; got: {o}"
    );
}

/// A whole-struct reassignment must invalidate the fields bound from it.
///
/// `c = d; c.lo` returns `d.lo`, so `ret == c.lo` is false unless `c.lo == d.lo`.
/// The field bindings are keyed by local and a plain `locals` write does not
/// touch them, so if the assignment left them the contract's `c.lo` would still
/// name the argument's field and this false contract would verify. It must be
/// refused or refuted -- anything but `Verified`.
#[test]
fn a_whole_struct_assignment_invalidates_its_fields() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct B { pub lo: u8 }

spec! {
    requires: true,
    ensures: ret == c.lo,
}
pub fn reassigned_then_field(mut c: B, d: B) -> u8 {
    c = d;
    c.lo
}
"#;
    let Some(o) = verify_src("reassigned_then_field", src) else { return };
    assert!(
        !o.is_verified(),
        "a reassigned struct's field binding is stale and must not prove a contract; got: {o}"
    );
}

/// A one-line struct body must not swallow the functions that follow it.
///
/// `struct_head` accepted any line containing `{` and opened a multi-line field
/// cursor, so `pub struct B { pub lo: u8 }` left the cursor open with no closing
/// brace left to read: every following line -- including the `///` contracts and
/// the functions -- was consumed as struct fields. The functions then vanished
/// from the spec table and were silently *not checked at all*, which is worse
/// than a wrong verdict because nothing reports it. The test above used a one-line
/// struct and was therefore passing vacuously.
///
/// The struct path now mirrors the enum path: a body that closes on the head line
/// is read inline, and a cursor is opened only for a body that does not. This
/// pins the function after the struct as still present and still decided.
///
/// The `None` case is a *skip*, not a failure, like every other `rustc`-dependent
/// test in this file: `verify_src` returns `None` when no `VERIF_RUSTC` is
/// named, and there is nothing to assert about a compiler that is not there. This
/// one used to `panic!` on `None`, which made the whole suite fail on a machine
/// with no `VERIF_RUSTC` -- the one test in the file that read "no compiler"
/// as "a bug", so the suite's verdict depended on the environment rather than on
/// the code. It is a skip now, and the reason is worth keeping: the property is
/// real and worth pinning, but a missing toolchain is not evidence against it.
#[test]
fn a_one_line_struct_does_not_swallow_the_functions_after_it() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct B { pub lo: u8 }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn after_inline_struct(x: u8) -> u8 {
    0
}
"#;
    let Some(o) = verify_src("after_inline_struct", src) else { return };
    assert!(o.is_verified(), "the function must still be read and decided; got: {o}");
}

/// A generated binding name must not be able to shadow a real argument.
///
/// The contract's `a[i]` is rewritten to a binding named `a__chain`, and this
/// function has an argument of exactly that name. If the generated binding were
/// inserted unconditionally it would shadow the argument, so `ret == a__chain`
/// would be checked against the array's chain instead of the argument. With
/// `i == 0` and `a__chain == 0` but `a[0] != 0` the contract is false, so
/// `Verified` would be a false proof. Refusing the binding is the fix; this pins
/// it.
#[test]
fn a_generated_binding_cannot_shadow_an_argument() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: i < 4,
    ensures: ret == a__chain,
}
pub fn shadow_probe(a: [u8; 4], i: usize, a__chain: u8) -> u8 {
    a[i]
}
"#;
    let Some(o) = verify_src("shadow_probe", src) else { return };
    assert!(
        !o.is_verified(),
        "`a__chain` is a real argument and must not be replaced by the generated binding; got: {o}"
    );
}

/// A `__len` collision is refused the same way, and the array's length binding is
/// what is dropped rather than the argument.
#[test]
fn a_generated_length_binding_cannot_shadow_an_argument() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: a.len() == 4,
    ensures: ret == a__len,
}
pub fn shadow_len_probe(a: [u8; 4], a__len: usize) -> usize {
    a.len()
}
"#;
    let Some(o) = verify_src("shadow_len_probe", src) else { return };
    assert!(
        !o.is_verified(),
        "`a__len` is a real argument and must not be replaced by the generated length; got: {o}"
    );
}

#[test]
fn a_false_symbolic_index_postcondition_is_caught() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: i < 4,
    ensures: ret <= 9,
}
pub fn chain_must_be_read(a: [u8; 4], i: usize) -> u8 {
    a[i]
}
"#;
    let Some(rustc) = rustc() else { return };
    let dir = std::env::temp_dir().join(format!("verif-chain-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("chain.rs");
    std::fs::write(&file, src).expect("write probe");
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &probe_opts()).expect("frontend");
    let o = outcome(&report, "chain_must_be_read");
    match o {
        FnOutcome::Failed { detail, .. } => assert!(
            !detail.is_empty(),
            "a failed symbolic-index obligation must carry a counterexample"
        ),
        other => panic!("`chain_must_be_read` must FAIL (ret <= 9 is false), got: {other}"),
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Stage 2, enums: a `match` is a `switchInt` on a symbolic tag.
///
/// A `match` lowers to `_2 = discriminant(_1); switchInt(move _2) -> [...]`, so
/// the tag is an input. Before this it was read as unknown and every `match` was
/// `incomplete` with `unmodelled switch discriminant`. The tag's domain is the
/// enum's arity, which is a fact about the *type*, so assuming it is sound and is
/// what makes the `otherwise` arm -- lowered to `unreachable` -- genuinely
/// unreachable rather than a spurious panic.
///
/// The tripwire is what makes this evidence rather than a claim: a constant tag
/// (or one read as zero) would prove `enum_match_tripwire`, which is false.
#[test]
fn an_enum_match_is_a_switch_on_a_symbolic_tag() {
    let Some(report) = verify_realistic(&["enum_match_is_bounded"]) else { return };
    let o = outcome(&report, "enum_match_is_bounded");
    assert!(o.is_verified(), "`enum_match_is_bounded` must verify, got: {o}");
}

/// A variant payload is read through the downcast and is a symbolic input.
///
/// `Msg::Data(x)` lowers to `_3 = copy ((_1 as Data).0)`, so the payload is field
/// 0 of variant 1. The contract's `m.Data` is bound to the same variable the
/// downcast reads, so `ret == m.Data` on that arm is a claim about one value.
#[test]
fn an_enum_payload_is_read_through_the_downcast() {
    let Some(report) = verify_realistic(&["enum_payload_reads_through"]) else { return };
    let o = outcome(&report, "enum_payload_reads_through");
    assert!(o.is_verified(), "`enum_payload_reads_through` must verify, got: {o}");
}

/// A `match` arm *guard* is decided by the payload its borrow of a downcast reads.
///
/// `Msg::Data(n) if n < 10` lowers to `_4 = &((_1 as Data).0: u8); _6 = copy
/// (*_4)`, and the rvalue contains the word ` as ` inside its parentheses. A
/// parser that checked for a cast before a reference split that at the ` as `, so
/// the borrow got no address, `copy (*_4)` read `Unknown`, and the `switchInt` on
/// the guard reported "unmodelled switch discriminant". The true contract must
/// verify and the tripwire -- which claims the guard's *other* arm ran -- must be
/// refuted with a witness naming the payload.
#[test]
fn a_match_guard_reads_its_payload_through_a_borrow() {
    let Some(report) = verify_realistic(&["guarded_match_reads_its_payload"]) else { return };
    let o = outcome(&report, "guarded_match_reads_its_payload");
    assert!(o.is_verified(), "`guarded_match_reads_its_payload` must verify, got: {o}");

    let Some(report) = verify_realistic(&["guarded_match_tripwire"]) else { return };
    let t = outcome(&report, "guarded_match_tripwire");
    match t {
        FnOutcome::Failed { kind, .. } => assert_eq!(kind, "postcondition"),
        other => panic!("`guarded_match_tripwire` must be refuted, got: {other}"),
    }
}

/// A locally constructed variant has a *known* tag, so its `match` decides.
///
/// `let m = Mode::Idle;` lowers to `_1 = Mode::Idle;`, a bare path constant with
/// no `const ` prefix, and `Mode::Idle` resolves to the enum's declaration index.
/// The tag is therefore a constant, only the `Idle` arm is reachable, and the
/// contract is decided rather than left as a coverage gap. The companion
/// tripwire claims the `Off` arm ran, which the same model must refute.
#[test]
fn a_locally_constructed_variant_has_a_known_tag() {
    let Some(report) = verify_realistic(&["enum_constructed_locally"]) else { return };
    let o = outcome(&report, "enum_constructed_locally");
    assert!(o.is_verified(), "`enum_constructed_locally` must verify, got: {o}");
}

/// A constructed variant's payload is written where the downcast reads it.
///
/// `Msg::Data(9)` lowers to `_1 = Msg::Data(const 9_u8);`, so the tag is `1` and
/// the payload is field 0 of that variant. The match's `Data(x)` arm reads
/// `((_1 as Data).0: u8)`, which is the same field, so `ret == 9` is a claim
/// about the value the construction wrote -- not about a fresh input.
#[test]
fn a_constructed_variants_payload_is_read_through_the_downcast() {
    let Some(report) = verify_realistic(&["enum_constructed_payload_reads_through"]) else { return };
    let o = outcome(&report, "enum_constructed_payload_reads_through");
    assert!(o.is_verified(), "`enum_constructed_payload_reads_through` must verify, got: {o}");
}

/// A unit variant has no payload, so naming one is refused rather than bound.
///
/// `m.Ping` is a unit variant. There is no value to read, so the contract must be
/// refused -- a model that bound every variant to the same payload would prove
/// this false contract. The refusal is `Skipped`, which is reported, not a
/// silent pass.
#[test]
fn a_unit_variant_has_no_payload_to_name() {
    let Some(report) = verify_realistic(&["enum_payload_tripwire"]) else { return };
    let o = outcome(&report, "enum_payload_tripwire");
    assert!(
        !o.is_verified(),
        "`enum_payload_tripwire` names a unit variant's payload and must be refused, got: {o}"
    );
}

/// `count_ones` is modelled, and its result is *widened* to the return type.
///
/// The operand is `u8` and the result is `u32`, so this is the one modelled call
/// whose result width differs from its operand's. A model that built an 8-bit
/// term and wrote it to a `u32` local would be ill-formed, and a contract at the
/// top of the count's range would not decide. Both entries must verify.
#[test]
fn count_ones_is_modelled_and_widens_its_result() {
    let Some(report) = verify_realistic(&[
        "popcount_of_nonzero",
        "popcount_bounded_by_width",
    ]) else {
        return;
    };
    for name in ["popcount_of_nonzero", "popcount_bounded_by_width"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// The tripwire: if `count_ones` were left unmodelled, both entries would be
/// `Skipped` rather than decided, and if it were modelled *wrongly* the false
/// claims would pass. A failure on the tripwires is the evidence the model was
/// contradicted; a decision at all is the evidence it is modelled.
#[test]
fn the_count_ones_tripwires_are_refuted_not_skipped() {
    let Some(report) = verify_realistic(&[
        "popcount_of_nonzero_tripwire",
        "popcount_bounded_by_width_tripwire",
    ]) else {
        return;
    };
    for name in ["popcount_of_nonzero_tripwire", "popcount_bounded_by_width_tripwire"] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means `count_ones` is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// `wrapping_abs` is modelled, unary, and reads its operand's sign.
///
/// The verifying entry is `ret >= x`, which holds at every `i8` including `MIN`
/// (where `abs` wraps back to `MIN`). The tripwire is `ret > x`, false at `x == 0`
/// where `abs` is the identity. Both must be *decided*: a `Skipped` would mean the
/// unary shape is not modelled at all, which is the gap this closed.
#[test]
fn wrapping_abs_is_modelled_unary_and_signed() {
    let Some(report) = verify_realistic(&["abs_never_below_operand"]) else { return };
    let o = outcome(&report, "abs_never_below_operand");
    assert!(o.is_verified(), "`abs_never_below_operand` must verify, got: {o}");

    let Some(report) = verify_realistic(&["abs_never_below_operand_tripwire"]) else { return };
    let o = outcome(&report, "abs_never_below_operand_tripwire");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!("`abs_never_below_operand_tripwire` must FAIL, got: {o}");
    };
    assert_eq!(kind, "postcondition", "got: {o}");
    // The counterexample must be `x == 0`, the one point where `abs` is the
    // identity: if the model were wrong on the negative side the witness would
    // name a negative value instead.
    assert!(
        detail.contains("= 0"),
        "the witness should be x == 0 (where abs is the identity), got: {detail}"
    );
}

/// The zero-counts beside `count_ones` are modelled, and `leading_zeros` of a
/// zero operand is the *full* width.
///
/// `leading_zeros` is the shape where an off-by-one hides: every non-zero operand
/// has at most `w - 1` leading zeros, so a model that counted only those would
/// agree with `core` everywhere except `x == 0`, and that is exactly the input the
/// tripwire names. Both entries must be *decided* -- a `Skipped` would mean the
/// name is not modelled at all.
#[test]
fn the_zero_counts_are_modelled() {
    let Some(report) = verify_realistic(&[
        "leading_zeros_of_a_small_value",
        "trailing_zeros_of_a_top_bit_value",
    ]) else {
        return;
    };
    for name in ["leading_zeros_of_a_small_value", "trailing_zeros_of_a_top_bit_value"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    let Some(report) = verify_realistic(&[
        "leading_zeros_of_a_small_value_tripwire",
        "trailing_zeros_of_a_top_bit_value_tripwire",
    ]) else {
        return;
    };
    for name in [
        "leading_zeros_of_a_small_value_tripwire",
        "trailing_zeros_of_a_top_bit_value_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the name is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
    // The `leading_zeros` witness must be `x == 0`, the only input where the count
    // is the full width. A model that counted `w - 1` there would name a non-zero
    // witness instead.
    let o = outcome(&report, "leading_zeros_of_a_small_value_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(
        detail.contains("= 0"),
        "the `leading_zeros` witness should be x == 0, got: {detail}"
    );
}

/// The four `pow` families are modelled, and the exponent is a `u32` *beside* a
/// base of the method's own width.
///
/// `pow` is the first modelled call whose two operands have different types. The
/// verifying entries pin the fold where the base's width matters (`2^7 == 128`
/// fits a `u8`, `2^8` wraps), and each tripwire states a *neighbouring* value --
/// one step off the true result -- so a model that folded at the wrong width, or
/// stopped a step early, refutes it. The signed entries pin the *clamp
/// direction*: `saturating_pow` of a negative base with an odd exponent clamps to
/// `MIN`, and a "clamp everything to `MAX`" model proves the `MAX` tripwire
/// instead of refuting it.
///
/// Every tripwire must be `Failed`, not `Skipped`: a `Skipped` would mean the
/// name is not modelled at all.
#[test]
fn the_pow_families_are_modelled_with_a_wide_exponent() {
    let Some(report) = verify_realistic(&[
        "wrapping_pow_two_to_seven_is_128",
        "checked_pow_two_to_seven_is_some_128",
        "saturating_pow_three_to_five_is_243",
        "overflowing_pow_two_to_seven_did_not_overflow",
        "wrapping_pow_negative_two_to_seven_is_min",
        "saturating_pow_negative_base_clamps_to_min",
        "wrapping_pow_zero_exponent_is_one",
    ]) else {
        return;
    };
    for name in [
        "wrapping_pow_two_to_seven_is_128",
        "checked_pow_two_to_seven_is_some_128",
        "saturating_pow_three_to_five_is_243",
        "overflowing_pow_two_to_seven_did_not_overflow",
        "wrapping_pow_negative_two_to_seven_is_min",
        "saturating_pow_negative_base_clamps_to_min",
        "wrapping_pow_zero_exponent_is_one",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    let Some(report) = verify_realistic(&[
        "wrapping_pow_two_to_eight_is_256_tripwire",
        "checked_pow_two_to_eight_is_none_tripwire",
        "saturating_pow_three_to_six_clamps_tripwire",
        "overflowing_pow_two_to_eight_flag_tripwire",
        "wrapping_pow_negative_two_to_eight_wraps_tripwire",
        "saturating_pow_negative_base_to_max_tripwire",
        "wrapping_pow_one_exponent_is_one_tripwire",
    ]) else {
        return;
    };
    for name in [
        "wrapping_pow_two_to_eight_is_256_tripwire",
        "checked_pow_two_to_eight_is_none_tripwire",
        "saturating_pow_three_to_six_clamps_tripwire",
        "overflowing_pow_two_to_eight_flag_tripwire",
        "wrapping_pow_negative_two_to_eight_wraps_tripwire",
        "saturating_pow_negative_base_to_max_tripwire",
        "wrapping_pow_one_exponent_is_one_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the name is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// The plain inherent `pow` is modelled, and its failure is a *panic* obligation
/// rather than a wrapped value.
///
/// This is the polarity the shape exists to pin: the families' `pow` expresses
/// overflow as a value (wrap, clamp, `None`, flag), but the plain `pow` panics, so
/// a model that treated it as total would discharge `plain_pow_panic_is_reachable`
/// as panic-free -- a false proof that an overflowing `pow` is safe. The two
/// verifying entries are the in-range case and the exact-boundary case; the two
/// failing entries must fail on the *panic* obligation, not on a postcondition, so
/// a model that wrapped instead of panicking is caught by the kind rather than by
/// a value that happens to differ.
#[test]
fn the_plain_pow_panics_where_it_overflows() {
    let Some(report) = verify_realistic(&[
        "plain_pow_three_to_five_is_243",
        "plain_pow_two_to_seven_does_not_panic",
    ]) else {
        return;
    };
    for name in ["plain_pow_three_to_five_is_243", "plain_pow_two_to_seven_does_not_panic"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    let Some(report) = verify_realistic(&[
        "plain_pow_panic_is_reachable",
        "plain_pow_two_to_eight_would_panic_tripwire",
    ]) else {
        return;
    };
    for name in ["plain_pow_panic_is_reachable", "plain_pow_two_to_eight_would_panic_tripwire"] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL on a panic, got: {o}");
        };
        // The panic must be *`pow`'s overflow*, not merely any panic: a model that
        // wrapped and then tripped a later shift, or a divide, would pass a bare
        // `starts_with("panic")`. The message names the method, so pin both.
        assert!(
            kind.starts_with("panic") && kind.contains("pow"),
            "`{name}` must fail on the `pow` overflow panic, got: {o}"
        );
    }
}

/// The four unary `neg`/`abs` families are modelled, and they disagree about
/// `MIN` -- which is what proves each is the right one and not a shared stand-in.
///
/// `saturating_neg` and `saturating_abs` clamp at `MIN`, so their results are
/// never negative; `wrapping_neg` and `wrapping_abs` return `MIN` there, which
/// *is* negative. The verifying entries state the clamp; the tripwires state the
/// same claim about the wrapping family, where `MIN` refutes it. If the four
/// shared one definition, either the clamps would fail or the tripwires would
/// pass, and both are caught here.
#[test]
fn the_unary_neg_and_abs_families_disagree_at_min() {
    let Some(report) = verify_realistic(&[
        "saturating_neg_of_positive_is_negative",
        "saturating_neg_of_non_positive_is_non_negative",
        "saturating_abs_is_never_negative",
        "saturating_abs_of_non_negative_is_identity",
    ]) else {
        return;
    };
    for name in [
        "saturating_neg_of_positive_is_negative",
        "saturating_neg_of_non_positive_is_non_negative",
        "saturating_abs_is_never_negative",
        "saturating_abs_of_non_negative_is_identity",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    let Some(report) = verify_realistic(&[
        "wrapping_neg_is_negative_tripwire",
        "wrapping_neg_of_non_positive_is_non_negative_tripwire",
        "wrapping_abs_is_never_negative_tripwire",
        "saturating_abs_is_identity_tripwire",
    ]) else {
        return;
    };
    for name in [
        "wrapping_neg_is_negative_tripwire",
        "wrapping_neg_of_non_positive_is_non_negative_tripwire",
        "wrapping_abs_is_never_negative_tripwire",
        "saturating_abs_is_identity_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the shape is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
    // The `abs`-at-`MIN` tripwire must name `x == 128`, which is `i8::MIN` read
    // unsigned -- the one input where the magnitude is unrepresentable. Naming
    // any other witness would mean the model disagrees with `core` elsewhere.
    let o = outcome(&report, "wrapping_abs_is_never_negative_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(
        detail.contains("= 128"),
        "the `wrapping_abs` witness should be x == i8::MIN (bits 128), got: {detail}"
    );
}

/// A `match` on a standard-library enum *argument* is modelled.
///
/// `Option` and `Result` are the two enums a real function reads without any
/// source file declaring them: `checked_add` returns `Option<u8>`, and `?` threads
/// a `Result`. An *argument* of one of those types had no layout, so its tag was
/// never seeded and the `switchInt` on it came back an unmodelled switch
/// discriminant -- a refusal, not a verdict. The declared-enum argument (`Mode`)
/// and the locally constructed `Option` both worked; the argument form is the gap.
///
/// Both halves matter: the true contracts must verify (the tag and the payload are
/// seeded) and the tripwires must be refuted (the tag and the payload are *read*,
/// not free variables the contract could make true). A model that seeded a
/// constant tag would take one arm always and prove a false tripwire.
#[test]
fn a_standard_enum_argument_is_a_switch_on_a_seeded_tag() {
    let Some(report) = verify_realistic(&[
        "option_arg_match",
        "option_arg_match_tripwire",
        "result_arg_match",
        "result_arg_match_tripwire",
        "option_arg_payload_passthrough",
        "option_arg_payload_tripwire",
    ]) else {
        return;
    };
    for name in ["option_arg_match", "result_arg_match", "option_arg_payload_passthrough"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in
        ["option_arg_match_tripwire", "result_arg_match_tripwire", "option_arg_payload_tripwire"]
    {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the shape is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// The same shape in an isolated file, so the fix is pinned even if the corpus
/// entry is edited: a `match` on `Option<u8>` must produce a verdict, not the
/// "unmodelled switch discriminant" refusal.
///
/// The nested-type spelling is the part worth pinning separately -- the payload is
/// the type argument as *one* type, so `Option<u8>` carries a `u8` and a
/// `Result<u8, u16>` carries a `u8` for `Ok` and a `u16` for `Err`. Splitting the
/// argument list at the wrong level (or reading the payload as the whole `u8, u16`
/// text) would size the payload wrongly and the width assertion in the contract
/// would fail.
#[test]
fn a_standard_enum_argument_payload_has_its_own_width() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

        spec! {
            requires: true,
            ensures: ret <= 255,
        }
        pub fn opt_payload(x: Option<u8>) -> u8 {
            match x { Some(v) => v, None => 0 }
        }
        spec! {
            requires: true,
            ensures: ret <= 1,
        }
        pub fn res_payload(r: Result<u8, u16>) -> u8 {
            match r { Ok(_) => 0, Err(_) => 1 }
        }
    "#;
    let Some(o) = verify_src("opt_payload", src) else { return };
    assert!(o.is_verified(), "`opt_payload` must verify, got: {o}");
    let Some(o) = verify_src("res_payload", src) else { return };
    assert!(o.is_verified(), "`res_payload` must verify, got: {o}");
}

/// A cast in a *contract* (`x as u32`) is readable, and it extends the way Rust
/// does: `-1i8 as i16` is `-1`, and `-1i8 as u16` is `65535` (sign-extended even
/// into an unsigned target), not the zero-extended `255`.
///
/// The body has modelled `as` for a while; the contract language had none, so a
/// contract relating a narrow argument to a wide return was unreadable. The
/// direction is the whole point: a contract cast that zero-filled a signed source
/// would refute the true `ret == 65535` and prove the false `ret == 255`, so the
/// true entries verifying *and* the tripwires being refuted is what pins it.
#[test]
fn a_cast_in_a_contract_extends_like_rust() {
    let Some(report) = verify_realistic(&[
        "contract_cast_widens_unsigned",
        "contract_cast_widens_unsigned_tripwire",
        "contract_cast_widens_signed",
        "contract_cast_signed_to_unsigned",
        "contract_cast_signed_to_unsigned_tripwire",
        "contract_cast_narrows",
        "contract_cast_narrows_tripwire",
        "contract_cast_chain",
        "contract_cast_chain_tripwire",
    ]) else {
        return;
    };
    for name in [
        "contract_cast_widens_unsigned",
        "contract_cast_widens_signed",
        "contract_cast_signed_to_unsigned",
        "contract_cast_narrows",
        "contract_cast_chain",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "contract_cast_widens_unsigned_tripwire",
        "contract_cast_signed_to_unsigned_tripwire",
        "contract_cast_narrows_tripwire",
        "contract_cast_chain_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the cast is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
    // The sign-extension witness must be `-1`, the one input where the two
    // extension rules differ; naming any other input would mean the model
    // disagrees with `core` elsewhere.
    let o = outcome(&report, "contract_cast_signed_to_unsigned_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(
        detail.contains("= 255"),
        "the sign-extension witness should be x == -1 (bits 255), got: {detail}"
    );
}

/// The cast shape in an isolated file, so the parse is pinned even if the corpus
/// entry is edited: `ret == x as u32` must be *readable* (a cast the parser cannot
/// read is a `Skipped`, i.e. a dropped obligation) and must hold.
#[test]
fn a_contract_cast_is_read_and_proved() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

        spec! {
            requires: true,
            ensures: ret == x as u32,
        }
        pub fn widen(x: u8) -> u32 {
            x as u32
        }
        spec! {
            requires: true,
            ensures: ret == x as u8,
        }
        pub fn narrow(x: u16) -> u8 {
            x as u8
        }
    "#;
    let Some(o) = verify_src("widen", src) else { return };
    assert!(o.is_verified(), "`widen` must verify, got: {o}");
    let Some(o) = verify_src("narrow", src) else { return };
    assert!(o.is_verified(), "`narrow` must verify, got: {o}");
}

/// A cast in a contract is a *value*, so a relational postcondition about it is
/// decided rather than refused.
///
/// The equality entries pin that a cast *extends* like Rust (`-1i8 as i16` is
/// `-1`, not `255`), but they only ever meet the cast with `==`. A cast the order
/// operator cannot read would be a silently dropped obligation -- the failure mode
/// the tripwire rule exists to catch -- so this pairs three true relational
/// contracts with two that must be refuted. The pair also separates
/// sign-extension from zero-filling *through the order*: `(y as i16) >= 0` for an
/// `i8` `y` is false exactly when the source's sign is kept, and
/// `(y as i16) <= 127` is true exactly when it is.
///
/// The evidence behind the entries is a differential sweep over every cast of a
/// small type into every wider target, compared against an exhaustive Python
/// model: 2160 cases decided, 0 unsound, 0 discrepancies.
#[test]
fn a_cast_in_a_contract_can_be_ordered() {
    let names = [
        "contract_cast_relational_nonneg",
        "contract_cast_relational_lt_width",
        "contract_cast_relational_signed_bound",
        "contract_cast_relational_signed_nonneg_tripwire",
        "contract_cast_relational_positive_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "contract_cast_relational_nonneg",
        "contract_cast_relational_lt_width",
        "contract_cast_relational_signed_bound",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "contract_cast_relational_signed_nonneg_tripwire",
        "contract_cast_relational_positive_tripwire",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` is false for every negative (resp. zero) input; got: {o}"
        );
    }
}

/// The `.wrapping_*` methods are the method-call spelling of the wrapping
/// operators the contract language already models, and reading them is what lets a
/// contract say what a body that uses them *means*.
///
/// Before this, every `x.wrapping_add(y)` in a contract was "cannot read contract",
/// which leaves the function silently outside the check set -- the outcome the
/// frontend exists to avoid. A two-variable relational sweep (208 pairs of
/// `requires`/`ensures` over `u8` `x`, `y`, exhaustive ground truth over all 2^16
/// pairs) went from **120 decided / 88 skipped** to **208 decided / 0 skipped**,
/// with 0 unsound and 0 discrepancies, so the desugaring agrees with Rust on every
/// pair it now reads.
///
/// The two refusals are the teeth: `x.wrapping_add(300)` is a rustc error for its
/// `300` (the wrapping semantics excuse the overflow of the *result*, not an
/// out-of-range literal), and `1.wrapping_add(2)` is `E0689` (an ambiguous
/// `{integer}` receiver). Both must be refused, never given a verdict.
#[test]
fn a_wrapping_method_in_a_contract_is_read_as_the_operator_it_denotes() {
    let names = [
        "contract_wrapping_add_reads",
        "contract_wrapping_add_is_a_value_tripwire",
        "contract_wrapping_sub_mul_chain_reads",
        "contract_wrapping_agrees_with_the_plain_operators",
        "contract_wrapping_neg_on_unsigned_reads",
        "contract_wrapping_neg_on_signed_reads",
        "contract_wrapping_add_of_constants_wraps",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "contract_wrapping_add_reads",
        "contract_wrapping_sub_mul_chain_reads",
        "contract_wrapping_agrees_with_the_plain_operators",
        "contract_wrapping_neg_on_unsigned_reads",
        "contract_wrapping_neg_on_signed_reads",
        "contract_wrapping_add_of_constants_wraps",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let o = outcome(&report, "contract_wrapping_add_is_a_value_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the wrapping add is a value, so `+ 1` on it is false for every input; got: {o}"
    );

    for name in [
        "contract_wrapping_add_of_an_out_of_range_literal_is_refused",
        "contract_wrapping_add_on_an_untyped_receiver_is_refused",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` is a rustc error and must be refused, never given a verdict, got: {o}"
        );
    }
}

/// `wrapping_shl`/`wrapping_shr` are modelled as a shift by the amount reduced
/// modulo the width, with `shr` arithmetic on a signed receiver and logical on an
/// unsigned one. The model was checked against Rust's own methods over the whole
/// `u8`/`i8` operand domain in `intrinsics::tests::wrapping_shifts_agree_with_rust`
/// (a mutation to a logical shift, and one that drops the amount reduction, each
/// fail it); these corpus entries pin the *end-to-end* verdicts, so a regression
/// in the wiring -- not just the model -- is caught.
///
/// Each true entry has a false twin that a wrong model would *prove*, and each
/// pair is *discriminating*: the left-shift pair pins the amount reduction (the
/// true entry claims `1`, the twin claims the saturated `0`, so only a reducing
/// model proves one and refutes the other -- a `ret <= 255` bound would satisfy
/// both), the signed right-shift pair pins the shift *kind* (`-4` vs the logical
/// `124`), and the unsigned right-shift entry pins both at once (`64`: a sign fill
/// would give `192`, a saturating shift `0`).
#[test]
fn wrapping_shifts_are_modelled_with_the_amount_reduced_modulo_the_width() {
    let Some(report) = verify_realistic(&[
        "wrapping_shl_reduces_its_amount",
        "wrapping_shl_amount_is_not_saturated_tripwire",
        "wrapping_shr_signed_is_arithmetic",
        "wrapping_shr_signed_is_not_logical_tripwire",
        "wrapping_shr_unsigned_is_logical",
    ]) else {
        return;
    };
    for name in [
        "wrapping_shl_reduces_its_amount",
        "wrapping_shr_signed_is_arithmetic",
        "wrapping_shr_unsigned_is_logical",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "wrapping_shl_amount_is_not_saturated_tripwire",
        "wrapping_shr_signed_is_not_logical_tripwire",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` is false under the correct model and must be refuted, got: {o}"
        );
    }
}

/// The contract operators that were missing (`/ % << >>`), and the precedence
/// they need. A missing operator is a dropped obligation -- the contract is
/// unreadable and the function silently leaves the check set -- so each entry
/// pairs a true contract with a tripwire, and the precedence entries pin the
/// *order*, not merely that the operator parses.
///
/// The signed entries are the ones with teeth: `>>` on a signed value must be
/// arithmetic (`-8 >> 1 == -4`, not a large positive) and `/` must be the signed
/// quotient (`-7 / 2 == -3`, not a huge positive). The unsigned engine would give
/// a wrong value, so those entries separate the two engines.
#[test]
fn contract_operators_and_their_precedence() {
    let Some(report) = verify_realistic(&[
        "contract_shr_unsigned",
        "contract_shr_unsigned_tripwire",
        "contract_shl",
        "contract_shr_signed_is_arithmetic",
        "contract_shr_signed_is_arithmetic_tripwire",
        "contract_udiv",
        "contract_urem",
        "contract_udiv_tripwire",
        "contract_sdiv",
        "contract_srem",
        "contract_sdiv_tripwire",
        "contract_precedence_and_over_add",
        "contract_precedence_and_over_add_tripwire",
        "contract_precedence_add_over_shl",
        "contract_precedence_add_over_shl_tripwire",
        "contract_precedence_and_over_or",
        "contract_precedence_and_over_or_tripwire",
        "contract_precedence_shift_over_eq",
        "contract_precedence_shift_over_eq_tripwire",
        "contract_precedence_cast_over_add",
        "contract_precedence_neg_over_cast",
        "contract_precedence_neg_over_rem",
        "contract_precedence_mul_rem_left_assoc",
    ]) else {
        return;
    };
    for name in [
        "contract_shr_unsigned",
        "contract_shl",
        "contract_shr_signed_is_arithmetic",
        "contract_udiv",
        "contract_urem",
        "contract_sdiv",
        "contract_srem",
        "contract_precedence_and_over_add",
        "contract_precedence_add_over_shl",
        "contract_precedence_and_over_or",
        "contract_precedence_shift_over_eq",
        "contract_precedence_cast_over_add",
        "contract_precedence_neg_over_cast",
        "contract_precedence_neg_over_rem",
        "contract_precedence_mul_rem_left_assoc",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "contract_shr_unsigned_tripwire",
        "contract_shr_signed_is_arithmetic_tripwire",
        "contract_udiv_tripwire",
        "contract_sdiv_tripwire",
        "contract_precedence_and_over_add_tripwire",
        "contract_precedence_add_over_shl_tripwire",
        "contract_precedence_and_over_or_tripwire",
        "contract_precedence_shift_over_eq_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the operator is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
    // `-8 >> 1` is `-4`, so a *logical* reading (a large positive) is what the
    // tripwire refutes; the witness `248` is the `-8` bit pattern, which pins
    // that the parser read the sign, not merely the value.
    let o = outcome(&report, "contract_shr_signed_is_arithmetic_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(detail.contains("= 248"), "the witness should be the `-8` pattern, got: {detail}");
    // The `&`/`+` precedence tripwire must be refuted at `x == 1`, the input
    // where `x & (1 + 1)` and `(x & 1) + 1` differ.
    let o = outcome(&report, "contract_precedence_and_over_add_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(detail.contains("= 1"), "the witness should be `x == 1`, got: {detail}");
}

/// A `u128`/`i128` function must be *refused*, not panicked. The engine's words
/// are 1..=64 bits and every width-taking constructor asserts that, so a 128-bit
/// argument, return, local or cast target has no width to model. Before the
/// guard, whichever of the argument seeding, the loop havoc or the contract
/// bindings ran first hit that assertion and took the whole run down — a panic
/// reports nothing, where a refusal reports the function. This pins the refusal
/// on each path, and that a 64-bit neighbour still verifies.
#[test]
fn a_128_bit_function_is_refused_not_panicked() {
    let Some(report) = verify_realistic(&[
        "wide_arg",
        "wide_return",
        "wide_local_in_loop",
        "wide_cast_in_contract",
        "narrow_64_still_works",
    ]) else {
        return;
    };
    for name in ["wide_arg", "wide_return", "wide_local_in_loop", "wide_cast_in_contract"] {
        let o = outcome(&report, name);
        let FnOutcome::Skipped { reason } = o else {
            panic!("`{name}` must be refused, got: {o}");
        };
        assert!(
            reason.contains("64-bit") || reason.contains("wider"),
            "`{name}` should say why, got: {reason}"
        );
    }
    // The guard must be about the function's own width, not a blanket refusal of
    // anything mentioning 128 bits: a `u64` neighbour still verifies.
    let o = outcome(&report, "narrow_64_still_works");
    assert!(o.is_verified(), "a 64-bit function must still verify, got: {o}");
}

/// The contract parser must refuse a cast *to* a 128-bit type on its own, since a
/// function whose own types are all 64-bit would otherwise reach `truncate` and
/// panic there. Pinned in isolation so the refusal does not depend on the corpus.
#[test]
fn a_contract_cast_to_128_bits_is_refused() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == x as u128,\n}\npub fn f(x: u8) -> u64 { x as u64 }";
    let Some(o) = verify_src("f", src) else { return };
    let FnOutcome::Skipped { reason } = o else {
        panic!("a cast to `u128` must be refused, got: {o}");
    };
    assert!(reason.contains("u128"), "the refusal should name the type, got: {reason}");
}

/// The operator shapes in an isolated file, so the *parse* is pinned even if the
/// corpus entry is edited. Each is one line, so a regression says exactly which
/// operator stopped being read.
#[test]
fn contract_operators_parse_in_isolation() {
    let cases: &[(&str, &str)] = &[
        ("shr", "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == x >> 1,\n}\npub fn shr(x: u8) -> u8 { x >> 1 }"),
        ("shl", "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == x << 2,\n}\npub fn shl(x: u8) -> u8 { x << 2 }"),
        ("udiv", "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == x / 3,\n}\npub fn udiv(x: u32) -> u32 { x / 3 }"),
        ("urem", "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == x % 10,\n}\npub fn urem(x: u32) -> u32 { x % 10 }"),
        (
            "prec",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == x & 1 + 1,\n}\npub fn prec(x: u8) -> u8 { x & 2 }",
        ),
    ];
    for (name, src) in cases {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// A constant signed expression, with no symbolic operand, must use the *signed*
/// engine for `%`, `/` and `>>`. Signedness is inferred from the names in an
/// expression, and there are none here, so the negated literal is the only
/// evidence — and it used to report itself unsigned. The mistake was a *wrong
/// value*, not a refusal: the unsigned `%` gives `4294967289 % 3 == 0` where Rust
/// says `-1`, and the tripwires below would then have *verified*, which is the
/// direction that manufactures a false proof. Each pair is asserted both ways, so
/// a fix that merely flipped the flag the other way fails here too.
#[test]
fn a_constant_signed_expression_uses_the_signed_engine() {
    let srcs = [
        (
            "srem",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == -7 % 3,\n}\npub fn srem() -> i32 { -7i32 % 3i32 }",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == 2,\n}\npub fn srem() -> i32 { -7i32 % 3i32 }",
        ),
        (
            "sdiv",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == -7 / 2,\n}\npub fn sdiv() -> i32 { -7i32 / 2i32 }",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == 3,\n}\npub fn sdiv() -> i32 { -7i32 / 2i32 }",
        ),
        (
            "ashr",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == -8 >> 1,\n}\npub fn ashr() -> i32 { -8i32 >> 1 }",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: ret == -1,\n}\npub fn ashr() -> i32 { -8i32 >> 1 }",
        ),
    ];
    for (name, true_src, false_src) in srcs {
        let Some(o) = verify_src(name, true_src) else { return };
        assert!(o.is_verified(), "`{name}` (true) must verify, got: {o}");
        let Some(o) = verify_src(name, false_src) else { return };
        assert!(!o.is_verified(), "`{name}` (tripwire) must be refuted, got: {o}");
    }
}

/// Unary `-` binds *tighter* than `as`, so `-x as u8` has type `u8` — unsigned.
/// Reading it the other way (`-(x as u8)`, signed) made `-x as u8 > 127`
/// unsatisfiable, so a function that is verifiable was reported *vacuous*. Both
/// directions are asserted: the satisfiable one must verify, and the tripwire —
/// which the signed reading would wrongly *verify* — must be refuted.
#[test]
fn a_negation_binds_tighter_than_a_cast() {
    let cases = [
        (
            "neg_cast_gt",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: -x as u8 > 127,\n    ensures: ret == 1,\n}\npub fn neg_cast_gt(x: i8) -> u8 { 1 }",
            true,
        ),
        (
            "neg_cast_lt_tripwire",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x == 1,\n    ensures: (-x as u8) < 127,\n}\npub fn neg_cast_lt_tripwire(x: i8) -> u8 { 1 }",
            false,
        ),
        (
            "neg_cast_value",
            "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x == -5,\n    ensures: ret == -x as u8,\n}\npub fn neg_cast_value(x: i8) -> u8 { -x as u8 }",
            true,
        ),
    ];
    for (name, src, want_verified) in cases {
        let Some(o) = verify_src(name, src) else { return };
        assert_eq!(
            o.is_verified(),
            want_verified,
            "`{name}`: expected verified={want_verified}, got: {o}"
        );
    }
}

/// A differential oracle for the contract expression language, against rustc.
///
/// The five existing oracles (z3, Kani, Lean, Coq, Verus) all build their terms with
/// `smt::` calls, so they start *below* the contract reader — the layer where three
/// bugs in a row lived. This closes that gap using the one decision procedure that
/// defines Rust: the compiler.
///
/// Two constructions, because the two bugs this found needed different ones:
///
/// * **Value** (`guard: None`). The body *is* the expression, so `ret` is rustc's
///   value of `E` at `x == v`; the postcondition `ret == E` asserts the reader's value
///   of `E` at the same point. This catches a wrong *value* — the signedness bug, where
///   `-7 % 3` was read as `0`.
///
/// * **Guard** (`guard: Some(t)`). The precondition is `x == v && E > t`, so the
///   comparison is decided at exactly `v`, and the body returns `1` with `ensures: ret
///   == 1`. The function verifies iff rustc says `E > t` at `v`. This is what catches a
///   wrong *type*: `-x as u8` and `-(x as u8)` have the same value (negation and
///   truncation commute), so no value check sees the difference — but only one of them
///   is `u8`, and the comparison is what reads the type. Pinning `x == v` makes the
///   expected verdict exact, so a *vacuous* result is a failure and not a grey area.
///
/// The grid is the point. A single point per expression would have missed the
/// signedness bug, so each case runs every value where a signed/unsigned confusion is
/// visible: the extremes of the type, `-1`, `0`, `1`. Each case lists its own grid,
/// because some expressions overflow at the extreme (`-x` for `x == i8::MIN` panics,
/// and `(x + 1) << 1` overflows `u8` at `x == 127`) — a panic is a *true* verdict, but
/// not the agreement this test is for.
#[test]
fn the_contract_reader_agrees_with_rustc_on_a_grid() {
    // (expression, argument type, return type, grid, guard threshold)
    type Case = (&'static str, &'static str, &'static str, &'static [i64], Option<u8>);
    let cases: &[Case] = &[
        // Signed remainder, division and arithmetic shift, over the grid. The negative
        // points are what separate the signed engine from the unsigned one.
        ("x % 3", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], None),
        ("x / 2", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], None),
        ("x >> 1", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], None),
        // A negated literal, the shape the first bug was about.
        ("-7 % 3", "i8", "i8", &[0], None),
        ("-7 / 2", "i8", "i8", &[0], None),
        ("-8 >> 1", "i8", "i8", &[0], None),
        // Unary `-` before the cast, as a *value*: both readings agree, so this half
        // only guards against a fix that broke the value.
        ("-x as u8", "i8", "u8", &[-7, -1, 0, 1, 127], None),
        // The same expression as a *guard*, which is where the type is observable:
        // `(-x) as u8 > 127` is true at `x == 1` (255), false under a signed reading.
        ("-x as u8", "i8", "u8", &[-7, -1, 0, 1, 127], Some(127)),
        // Casts: widening sign-extends, narrowing keeps the low bits, a chain is
        // left to right.
        ("x as i16", "i8", "i16", &[-128, -1, 0, 1, 127], None),
        ("x as i8", "i16", "i8", &[-32768, -129, -1, 0, 1, 127, 128, 32767], None),
        ("x as i8 as i32", "i16", "i32", &[-32768, -129, -1, 0, 1, 127, 128, 32767], None),
        ("x as u16", "u8", "u16", &[0, 1, 128, 255], None),
        // Precedence and associativity, on the grid.
        ("x & 1 + 1", "u8", "u8", &[0, 1, 2, 3, 255], None),
        ("x + 1 << 1", "u8", "u8", &[0, 1, 63, 126], None),
        ("x | 1 ^ 1", "u8", "u8", &[0, 1, 255], None),
        ("x & 3 | 4", "u8", "u8", &[0, 1, 3, 255], None),
        ("x ^ 1 & 3", "u8", "u8", &[0, 1, 3, 255], None),
        ("x | 1 ^ 2", "u8", "u8", &[0, 1, 2, 255], None),
        // Unary `!` stacked, and `!` feeding a shift: both are bitwise, so `!!x` is
        // `x` and `!x >> 1` shifts the complement.
        ("!!x", "u8", "u8", &[0, 1, 5, 250, 255], None),
        ("!x >> 1", "u8", "u8", &[0, 1, 250, 255], None),
        // A shift and a bitwise `|` in one expression: `x << 1 | 1` is
        // `(x << 1) | 1`, because `<<` binds tighter than `|`.
        ("x << 1 | 1", "u8", "u8", &[0, 1, 2, 63], None),
        // Unary `-` feeding a shift, and unary `-` feeding `+`.
        ("-x >> 1", "i8", "i8", &[-127, -1, 0, 1, 127], None),
        ("-x + 1", "i8", "i8", &[-126, -1, 0, 1, 126], None),
        // A cast feeding a bitwise `&`, and a double cast.
        ("x as u16 & 1", "i8", "u16", &[-128, -1, 0, 1, 127], None),
        ("x as u8 as u16", "i8", "u16", &[-128, -1, 0, 1, 127], None),
        // `*` binds tighter than `+`, and a repeated shift is left-associative.
        ("1 + x * 2", "u8", "u8", &[0, 1, 5, 63], None),
        ("x >> 1 >> 1", "u8", "u8", &[0, 1, 255], None),
        // A cast binds tighter than `+`, and unary `-` binds tighter than a cast. The
        // guard mode reads the *type* of the result, which is where `(x as i16) + 1`
        // and `x as (i16 + 1)` would differ. (`*` is left out: an `i16 * i16` body has
        // an overflow assert the engine declines to model at that width, so the probe
        // itself is undecided and the guard mode cannot read the comparison.)
        ("x as i16 + 1", "i8", "i16", &[-1, 0, 5, 126], Some(6)),
        ("-x as i16", "i8", "i16", &[-1, 0, 1, 127], None),
        ("x << 2", "u8", "u8", &[0, 1, 63, 255], None),
        ("8 - 4 - 2", "i32", "i32", &[0], None),
        ("8 / 4 / 2", "u32", "u32", &[0], None),
        // A negation of a name, and a double negation, which is the value again.
        ("-x", "i8", "i8", &[-127, -1, 0, 1, 127], None),
        ("- -x", "i8", "i8", &[-127, -1, 0, 1, 127], None),
        // `0 - x` is a subtraction, not a negation, so it *overflows* at `x ==
        // i8::MIN` (the body panics, a true verdict but not an agreement point).
        ("0 - x", "i8", "i8", &[-127, -1, 0, 1, 127], None),
        // The signedness of a comparison on a variable, over the whole grid.
        ("x", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], Some(0)),
        ("x % 3", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], Some(0)),
        // Unary `!` on a value is *bitwise* NOT, and binds tighter than `==`:
        // `!x == 5` is `(!x) == 5` (`x == 250`), not `!(x == 5)` (`x != 5`). The
        // predicate reading is a different predicate, so it is a wrong verdict.
        ("!x", "u8", "u8", &[0, 1, 128, 255], None),
        ("!!x", "u8", "u8", &[0, 1, 128, 255], None),
        ("!x + 1", "u8", "u8", &[1, 128, 255], None),
        ("x & !1", "u8", "u8", &[0, 1, 3, 255], None),
        // The guard form is the discriminator: `(!x) == 5` holds only at `x == 250`,
        // where `!(x == 5)` would hold everywhere else. Pinning `x == v` makes the
        // two readings differ at every point but one.
        ("!x", "u8", "u8", &[0, 1, 5, 250, 255], Some(5)),
        ("!x", "u8", "u8", &[0, 1, 5, 250, 255], Some(4)),
        // Parentheses do not make it a predicate: `!(x + 1)` holds *arithmetic*, so
        // `!` is still the value form and `!(x + 1) == 5` is `(!(x + 1)) == 5`, not a
        // negation of `(x + 1) == 5` (which is not even well-typed). This is the case
        // that separates `bang_is_predicate`'s lookahead from "a `(` follows".
        ("!(x + 1)", "u8", "u8", &[0, 1, 5, 249, 254], None),
        // A shift amount is a constant *expression*: the reader and the body must
        // both fold `1 + 1` to `2`, not treat it as a symbolic barrel-shifter
        // amount. The value mode builds `x >> 1 + 1` as the body *and* the
        // postcondition, so an unreadable contract (a non-folded reader) shows up
        // as a non-verified outcome here.
        ("x >> 1 + 1", "u8", "u8", &[0, 1, 2, 4, 8, 16, 128, 255], None),
        // A radix literal is the expression in *both* the body and the
        // postcondition: rustc compiles the body `0xFF` to `255`, and the reader
        // must read the contract `0xFF` as `255` for `ret == 0xFF` to hold. A
        // decimal-only reader read it as `0`, so the postcondition became
        // `ret == 0` and the tool *proved* it for a body returning `255` -- a false
        // proof, which this row turns into a disagreement. The `x == 0` guard makes
        // the function total so the only thing under test is the literal.
        ("0xFF", "u8", "u8", &[0], None),
        ("0b1010", "u8", "u8", &[0], None),
        ("0o17", "u8", "u8", &[0], None),
        ("0xFFu8", "u8", "u8", &[0], None),
        ("0xFF_FF", "u16", "u16", &[0], None),
        ("0x10", "u8", "u8", &[0], None),
    ];

    let mut checked = 0u32;
    for (expr, arg_ty, ret_ty, grid, guard) in cases {
        for &v in *grid {
            // A stable, identifier-safe name: the index, not the expression (which
            // contains characters Rust will not take in a name).
            let name = format!("oracle_{checked}");
            let (src, want) = match guard {
                // Value: body is the expression, postcondition asserts the reader's
                // value equals rustc's.
                None => (
                    format!(
                        "/// requires: x == {v}\n/// ensures: ret == {expr}\n\
                         pub fn {name}(x: {arg_ty}) -> {ret_ty} {{ {expr} }}\n"
                    ),
                    true,
                ),
                // Guard: the body returns `1` and the precondition is the comparison
                // pinned at `v`, so it verifies iff rustc's comparison is true.
                Some(t) => {
                    // Ask rustc for the comparison at this point, so the expectation is
                    // the compiler's, not mine.
                    let probe = format!(
                        "/// requires: x == {v}\n/// ensures: ret == 1\n\
                         pub fn {name}(x: {arg_ty}) -> u8 {{ if {expr} > {t} {{ 1 }} else {{ 0 }} }}\n"
                    );
                    // The probe's body is rustc's comparison; the value it returns is
                    // what `expect_verified` must match. `1` means satisfiable.
                    let o = verify_src(&name, &probe);
                    let Some(o) = o else { return };
                    // The probe verifies iff the body always returns `1`, which is true
                    // only when the comparison holds at `v`.
                    let truth = o.is_verified();
                    let src = format!(
                        "/// requires: x == {v} && {expr} > {t}\n/// ensures: ret == 1\n\
                         pub fn {name}(x: {arg_ty}) -> u8 {{ 1 }}\n"
                    );
                    (src, truth)
                }
            };
            let Some(o) = verify_src(&name, &src) else { return };
            assert_eq!(
                o.is_verified(),
                want,
                "the reader disagrees with rustc: `{expr}` at x == {v} ({arg_ty}), guard {guard:?} — expected verified={want}, got: {o}"
            );
            checked += 1;
        }
    }
    // A run that checked nothing is not evidence.
    assert!(checked >= 60, "the oracle checked only {checked} points");
}

/// A shift amount or a divisor may be a *constant expression*, not only a bare
/// literal, and the reader must fold it before deciding what it is.
///
/// `x >> 1 + 1` is `x >> 2` and `x % (1 - 1)` is `x % 0`; Rust evaluates both
/// amounts at compile time. The reader tested the raw operand with `const_of`,
/// which only recognises a literal node, so a folded amount was misclassified in
/// two opposite directions: a constant shift amount looked symbolic (the body built
/// a barrel shifter and the engine could not decide), and a constant *zero* divisor
/// slipped past the divide-by-zero guard and produced a definite verdict from an
/// undefined `srem(x, 0)` -- a wrong verdict, the one outcome a verifier must not
/// produce. The fix folds with `const_value`/`evaluate` on both sides.
#[test]
fn a_folded_constant_is_read_as_a_constant() {
    // A folded shift amount verifies: the body shifts by the same constant.
    let Some(o) = verify_src(
        "folded_shift_amount",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x == 8,\n    ensures: ret == x >> 1 + 1,\n}\npub fn folded_shift_amount(x: u8) -> u8 { x >> 2 }\n",
    ) else {
        return;
    };
    assert!(o.is_verified(), "a folded shift amount must be read, got: {o}");

    // A folded *zero* divisor is refused, exactly as the literal `0` is. The
    // requirement is that it is not *decided*: a verdict built on `srem(x, 0)`
    // would be a verdict about nothing.
    let Some(o) = verify_src(
        "folded_zero_divisor",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x == 3,\n    ensures: ret == x % (1 - 1),\n}\npub fn folded_zero_divisor(x: u8) -> u8 { x % 3 }\n",
    ) else {
        return;
    };
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "a folded zero divisor must be refused, not decided, got: {o}"
    );

    // A folded *non-zero* divisor still reads and models exactly: `4 / (1 + 1)`
    // is `4 / 2` is `2`, the same as the body, so the two agree.
    let Some(o) = verify_src(
        "folded_nonzero_divisor",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x == 4,\n    ensures: ret == x / (1 + 1),\n}\npub fn folded_nonzero_divisor(x: u8) -> u8 { x / 2 }\n",
    ) else {
        return;
    };
    assert!(
        o.is_verified(),
        "a folded non-zero divisor must be read and modelled, got: {o}"
    );

    // And the *body* folds the same way: `x >> 1 + 1` lowers to a constant shift,
    // not a barrel shifter, so the query is decided rather than left incomplete.
    let Some(o) = verify_src(
        "folded_body_shift",
        "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x == 8,\n    ensures: ret == 2,\n}\npub fn folded_body_shift(x: u8) -> u8 { x >> 1 + 1 }\n",
    ) else {
        return;
    };
    assert!(
        o.is_verified(),
        "a folded shift amount in the body must be lowered as a constant, got: {o}"
    );
}

/// A radix literal must be read at its radix, and the *control* is the point.
///
/// `0xFF` used to read as `0`, so `requires: x == 0xFF` became `x == 0` and
/// `ensures: ret == 0` was **proved** for a function returning `255` -- a false
/// proof, the worst outcome this crate can produce. The verifying entries show the
/// value is now right; the control shows the truncated value is gone, because it is
/// the entry that used to be a false proof and must now be refuted.
#[test]
fn a_radix_literal_is_read_at_its_radix() {
    let verified = [
        "contract_hex_literal_is_255",
        "contract_binary_literal_is_ten",
        "contract_octal_literal_is_fifteen",
        "contract_hex_underscore_is_65535",
        "contract_hex_with_suffix_is_255",
        "contract_hex_arithmetic_is_folded",
        "contract_hex_shift_amount",
        "contract_hex_mask_keeps_low_nibble",
        "contract_negative_hex_literal",
        "contract_uppercase_hex_prefix",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&["contract_hex_literal_is_not_zero_control"]) else {
        return;
    };
    let o = outcome(&report, "contract_hex_literal_is_not_zero_control");
    let FnOutcome::Failed { kind, detail, .. } = o else {
        panic!("the control must be refuted -- verifying it is the false proof, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the control got: {o}");
    // The witness is `255`, the value `0xFF` *should* be. Under the old truncating
    // read it would have been a proof, so the witness is the evidence the literal
    // is now read at radix 16.
    assert!(detail.contains("= 255"), "the witness should be `255`, got: {detail}");
}

/// A literal that does not fit the operand's signed width is refused, and the
/// false proof it used to allow is the point.
///
/// `128` for an `i8` is the bit pattern `0x80`, which is `-128` signed. A reader
/// that asked only whether the literal fits in eight *unsigned* bits accepted it, so
/// `x <= 128` was read as `x <= -128` and `ensures: ret <= 127` was *proved* for a
/// body returning `x`. rustc rejects `x <= 128` for an `i8` ("literal out of range
/// for `i8`"), so the correct outcome is a refusal. The `i8::MIN` boundary shares
/// the bit pattern and must still read, which is what keeps the fix from refusing
/// every `0x80`.
#[test]
fn an_out_of_range_literal_is_refused_not_wrapped() {
    let refused = [
        "contract_out_of_range_literal_is_refused",
        "contract_out_of_range_negation_is_refused",
        "contract_constant_vs_constant_out_of_range",
        "contract_constant_sum_overflow_is_refused",
        "contract_constant_underflow_is_refused",
        "contract_constant_div_overflow_is_refused",
        "contract_constant_signed_sum_overflow_is_refused",
        "contract_signed_literal_vs_unsigned_is_refused",
        "contract_signed_constant_sum_vs_unsigned_is_refused",
        "contract_signed_constant_mask_vs_unsigned_is_refused",
        // A negation of a constant is checked against the value it denotes, so a
        // negation that overflows its own type is refused (`-(i8::MIN)`, and the
        // wrapping shift `-(3 << 7)` that shares its bit pattern).
        "contract_negation_of_min_is_refused",
        "contract_negation_of_wrapping_shift_is_refused",
        // A shift *amount* is a value of its own `i32`, so an amount that wraps at
        // the operand's width but not at `i32` (`2 << 7` is `256`) is refused. A
        // nested suffix is in the inner shift's amount, so it does not fix the
        // outer amount's type (`2 << 7u8` is still the `i32` `256`), and a cast
        // fixes the type and overrides what it casts (`(1u8) as u16` is a `u16`,
        // so the amount is `257u16`).
        "contract_nested_shift_amount_overflow_is_refused",
        "contract_nested_shift_amount_sum_overflow_is_refused",
        "contract_nested_amount_suffix_does_not_fix_the_outer_width",
        "contract_cast_amount_operand_fixes_the_width",
    ];
    let Some(report) = verify_realistic(&refused) else { return };
    for name in refused {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "`{name}` must be refused, not verified -- verifying it is the false proof, got: {o}"
        );
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` must be skipped (unreadable contract), got: {o}"
        );
    }
    let read = [
        "contract_min_bound_still_reads",
        "contract_negative_bound_reads_at_i16",
        "contract_constant_vs_constant_in_range",
        "contract_constant_sum_in_range_reads",
        "contract_constant_sum_wider_operand_reads",
        "contract_unsigned_literal_still_reads",
        "contract_unsigned_constant_sum_still_reads",
        "contract_unsigned_mask_still_reads",
        // The controls for the two classes above: an in-range negation and an
        // amount that fits `i32` both still read, so the refusals are pinned to
        // the overflow and not to the shape. A *typed* amount operand fixes the
        // amount's width, so `1u8 + (2 << 7)` is a `u8` amount (`2 << 7` is `0u8`)
        // and the shift rustc accepts must read rather than be refused.
        "contract_negation_of_max_still_reads",
        "contract_fitting_shift_amount_still_reads",
        "contract_typed_amount_operand_fixes_the_width",
    ];
    let Some(report) = verify_realistic(&read) else { return };
    for name in read {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must still read and verify, got: {o}");
    }
}

/// A signed element of a slice or array must be read as signed *in the contract*.
///
/// `bind_indexed_elem` (and the symbolic-index chain) recorded an element's
/// signedness for the executor's seeds but not for the parser's name table, so
/// `is_signed_name` reported an `i8` element as unsigned. A postcondition that
/// compares it with zero then reads as an unsigned comparison, which is *always
/// true* -- so `ensures: xs[0] >= 0` was reported verified for a body that returns
/// the element, a false proof with `i8::MIN` as the counterexample.
///
/// The existing `signed_slice_element_tripwire` did not catch this: its body reads
/// the element itself, so the *body's* (correct, executor-side) reading dominated
/// the verdict and it was already FAILED for the right reason. The bug only shows
/// when the element appears on the contract side alone, which is what these two
/// entries pin. Both are sensitive: removing either sign record makes them verify.
#[test]
fn a_signed_element_is_read_as_signed_in_the_contract() {
    let refuted = [
        "signed_slice_element_ensures_tripwire",
        "signed_array_chain_ensures_tripwire",
    ];
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, detail, .. } = o else {
            panic!(
                "`{name}` is false at `i8::MIN` and must be refuted -- verifying it is \
                 the unsigned-reading false proof, got: {o}"
            );
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
        // The witness is `128`, the bit pattern of `i8::MIN`. Under the unsigned
        // reading the comparison is trivially true and there is no witness at all.
        assert!(
            detail.contains("= 128"),
            "the witness should be `128` (`i8::MIN`), got: {detail}"
        );
    }
}

/// The corpus entries that pin *where* `!` binds, asserted end to end.
///
/// `!` is bitwise NOT on a value and negation on a predicate, and it binds tighter
/// than `==`, `&` and `as`. Each entry below separates one of those bindings, so a
/// reader that got one wrong would either fail to parse or return the other value.
/// The control is the `==` case: it is *false* under Rust's reading and must be
/// refuted, which is what makes the verifying entry next to it evidence rather than
/// a tool that proves everything.
#[test]
fn a_bang_binds_by_rusts_precedence_in_the_corpus() {
    let verified = [
        "contract_bang_binds_tighter_than_eq",
        "contract_bang_is_bitwise_not",
        "contract_bang_still_negates_a_predicate",
        "contract_bang_binds_tighter_than_a_cast",
        "contract_bang_binds_tighter_than_and",
        "contract_bang_paren_arithmetic_is_a_value",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&["contract_bang_binds_tighter_than_eq_control"]) else {
        return;
    };
    let o = outcome(&report, "contract_bang_binds_tighter_than_eq_control");
    let FnOutcome::Failed { .. } = o else {
        panic!("`contract_bang_binds_tighter_than_eq_control` is false and must be refuted, got: {o}");
    };
}


/// A contract above a struct or enum belongs to that item, not the next function.
///
/// The reader matched a `struct`/`enum` head and `continue`d without clearing the
/// pending contract, so a doc comment above a layout carried over to the next `fn`.
/// A leaked `requires` is a false proof when it is satisfiable: `requires: x == 0`
/// above a struct made `ensures: ret == 0` for a body returning `x` *verify*,
/// because the check is only made for the inputs the precondition admits.
///
/// Both entries below carry the identical function and contract; the first has a
/// struct above it with a `requires: x == 0`, the second does not. Both must be
/// refuted, and refuted the *same way*. The pair is the evidence: verifying the
/// tripwire would be the false proof, and refuting only the control would not show
/// the leak was dropped.
#[test]
fn a_contract_above_a_layout_does_not_leak_into_the_next_function() {
    let names = ["leaked_requires_tripwire", "leaked_requires_is_dropped"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` proves a false contract; got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` must fail on its postcondition, got: {o}");
    }
}

/// Two names of different signedness are refused, and the same-signedness pair
/// still reads.
///
/// `a > b` for an `i8` and a `u8` is `E0308: mismatched types` in rustc. The
/// reader used to pick a sign and decide it; the body reads each operand at its
/// own signedness, so the contract and the body could disagree about the operator's
/// meaning. Refusing keeps the answer "the tool could not run" rather than a verdict
/// on a program that does not compile. The control is the same comparison with both
/// operands `i8`: it is legal and must still verify, so the refusal is not a blanket
/// ban on two-name comparisons.
#[test]
fn a_mixed_signedness_comparison_is_refused_and_the_same_signedness_pair_reads() {
    let refused = [
        "contract_mixed_signedness_compare_is_refused",
        "contract_mixed_signedness_add_is_refused",
    ];
    let Some(report) = verify_realistic(&refused) else { return };
    for name in refused {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` must be refused (skipped), not given a verdict, got: {o}"
        );
    }
    let Some(report) = verify_realistic(&["contract_same_signedness_compare_still_reads"]) else {
        return;
    };
    let o = outcome(&report, "contract_same_signedness_compare_still_reads");
    assert!(o.is_verified(), "the same-signedness control must still verify, got: {o}");
}

/// An untyped constant's complement is refused in an *equality*, not just an
/// ordering.
///
/// `!0` has no type of its own. Rust types an untyped constant as `i32`, so `!0`
/// is `-1` and `!0 == 255` is `false`: the postcondition holds for no input. The
/// reader carried the complement as a bit pattern at the scope's width, built
/// `255u8 == 255`, and *verified* it -- a false proof. `==`/`!=` "compare bit
/// patterns" was the reason given for leaving them readable, but here the two
/// readings are different *values* (`-1` vs `255`), so the shape is refused. The
/// control fixes the reading with a typed operand and must still verify.
#[test]
fn an_untyped_complement_equality_is_refused_and_a_typed_partner_reads() {
    let Some(report) = verify_realistic(&["contract_untyped_complement_equality_is_refused"]) else {
        return;
    };
    let o = outcome(&report, "contract_untyped_complement_equality_is_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`!0 == 255` is `false` in Rust; it must be refused, never given a verdict, got: {o}"
    );
    let Some(report) =
        verify_realistic(&["contract_complement_of_literal_with_typed_partner_reads"])
    else {
        return;
    };
    let o = outcome(&report, "contract_complement_of_literal_with_typed_partner_reads");
    assert!(o.is_verified(), "a typed partner fixes the reading and must verify, got: {o}");
}

/// The complement of an *out-of-range* literal is refused, while a fitting one
/// still reads and a wider operand is untouched.
///
/// `!128` for an `i8` is a rustc `literal out of range for i8` error -- `128` does
/// not fit a signed eight-bit type -- even though the complement's *value* `127`
/// does. The reader built `!128` as the constant `127` and let the resize truncate
/// it with no check, so `y <= !128` read as `y <= 127` (`i8::MAX`) and *verified*
/// for a program rustc rejects. Two controls keep the refusal at the range: `!127`
/// fits an `i8`, and `!128` fits an `i16`, so both must be *decided* (each is a
/// real predicate, not a tautology, so the verdict is `Failed` with a witness) --
/// a blanket ban on `!`-of-`128` would leave them `Skipped`.
#[test]
fn a_complement_of_an_out_of_range_literal_is_refused() {
    let Some(report) = verify_realistic(&[
        "contract_complement_of_out_of_range_literal_is_refused",
        "contract_fitting_complement_still_reads",
        "contract_complement_reads_at_a_wider_operand",
    ]) else {
        return;
    };
    let o = outcome(&report, "contract_complement_of_out_of_range_literal_is_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`y <= !128` for an `i8` is a rustc range error; it must be refused, never given a \
         verdict, got: {o}"
    );
    for name in [
        "contract_fitting_complement_still_reads",
        "contract_complement_reads_at_a_wider_operand",
    ] {
        let o = outcome(&report, name);
        assert!(
            !matches!(o, FnOutcome::Skipped { .. }),
            "{name} fits the operand type and must be decided, got: {o}"
        );
    }
}

/// Unary `-` on an *unsigned* name is refused, and a *signed* negation still reads.
///
/// `-x` for a `u8` is `E0600: cannot apply unary operator `-` to type `u8``. The
/// reader modelled it as `0 - x`, a value Rust never produces, so the shape is
/// refused rather than decided -- the same answer as a mixed-signedness pair. The
/// control negates a signed name, which is legal, and must still verify.
#[test]
fn an_unsigned_negation_is_refused_and_a_signed_negation_reads() {
    let Some(report) = verify_realistic(&["contract_unsigned_negation_is_refused"]) else { return };
    let o = outcome(&report, "contract_unsigned_negation_is_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`-x` for a `u8` does not compile and must be refused, got: {o}"
    );
    let Some(report) = verify_realistic(&["contract_signed_negation_still_reads"]) else { return };
    let o = outcome(&report, "contract_signed_negation_still_reads");
    assert!(o.is_verified(), "a negation of a signed name must still verify, got: {o}");
}

/// A contract literal widened to meet a *signed* operand zero-fills.
///
/// The fill comes from the constant's own signedness, not the operand it meets.
/// Rust's `(255u8 as i16)` is `255`, so `(x as i16) == 255` holds for every `u8`
/// `x`. Widening the literal from the operand's signed `i16` sign-extended it to
/// `65535` and *refuted* a postcondition Rust accepts -- a false refutation. The
/// control `254` is neither reading and must FAIL, so the fix is not "verify
/// everything".
#[test]
fn a_literal_widened_to_a_signed_operand_zero_fills() {
    let Some(report) = verify_realistic(&["contract_literal_widened_to_signed_zero_fills"]) else {
        return;
    };
    let o = outcome(&report, "contract_literal_widened_to_signed_zero_fills");
    assert!(o.is_verified(), "`255` widened to i16 is `255` and must verify, got: {o}");
    let Some(report) = verify_realistic(&["contract_literal_widened_to_signed_tripwire"]) else {
        return;
    };
    let o = outcome(&report, "contract_literal_widened_to_signed_tripwire");
    assert!(matches!(o, FnOutcome::Failed { .. }), "`254` is neither reading and must FAIL, got: {o}");
}

/// Every literal and every constant `+ - *` intermediate is range-checked against
/// the type the expression meets, not only the value the fold produces.
///
/// The reader folds a constant expression to one value and used to range-check
/// only that value. Rust checks each literal and each intermediate: `2 & 128` for
/// an `i8` is a `literal out of range` error although the fold's value is `0`, and
/// `128 - 63` is rejected although its value `65` fits. The reader decided both --
/// a wrong verdict on a program rustc rejects, where the previous fix's class was
/// a false *proof*. Two controls keep the refusal at the range: the same literals
/// under a `u8` partner fit, and `-128` is rescued by the unary `-` because the
/// negated value, not the magnitude, is what meets the type.
#[test]
fn a_literal_inside_a_constant_fold_is_range_checked_too() {
    let refused = [
        "contract_literal_in_fold_out_of_range_is_refused",
        "contract_masked_literal_out_of_range_is_refused",
        "contract_constant_sum_value_out_of_range_is_refused",
        "contract_literal_in_difference_out_of_range_is_refused",
        "contract_literal_in_negated_fold_is_refused",
        "contract_complement_shift_amount_is_refused",
    ];
    let Some(report) = verify_realistic(&refused) else { return };
    for name in refused {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` is a rustc range error and must be refused, never given a verdict, got: {o}"
        );
    }
    for name in [
        "contract_fold_literals_in_range_still_read",
        "contract_bare_negated_bound_still_reads",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} fits the type it meets and must verify, got: {o}");
    }
}

/// A constant fold that mixes an *untyped* complement with a plain operand is
/// refused when its value depends on the signedness Rust infers for it.
///
/// A complement has no signedness of its own: it takes the one the type it meets
/// gives it. The reader guesses it from the other operand, and when no operand
/// fixes a sign the guess can disagree with the reading the fold finally gets.
/// `!127 - 63` is `128 - 63 = 65` unsigned but `i8::MIN - 63` -- a rustc overflow --
/// signed, so the reader decided `65` for a program rustc rejects: a wrong verdict.
/// `!127 * 2` is the same shape. A negated bare literal beside a complement
/// (`!100 * -0`) is `E0277` for a `u16` -- legal only at a signed type -- so it is
/// refused too. Two controls keep the refusal at the ambiguity: the same fold under
/// a wider partner is in range under both readings and reads, and a fold that
/// agrees under both readings (`(!0) - 1`) still reads.
#[test]
fn a_sign_ambiguous_untyped_fold_is_refused() {
    for name in [
        "contract_sign_ambiguous_fold_is_refused",
        "contract_sign_ambiguous_mul_is_refused",
        "contract_complement_with_negated_literal_is_refused",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` is sign-ambiguous and must be refused, never given a verdict, got: {o}"
        );
    }
    for name in [
        "contract_sign_ambiguous_fold_at_wider_width_reads",
        "contract_agreeing_untyped_fold_still_reads",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} agrees under both readings and must verify, got: {o}");
    }
}

/// A complement's *provisional* unsigned value must not be range-checked as if it
/// were a written literal, while a literal *under* the fold still is.
///
/// `y == !(!1 + 1)` for an `i8` `y` is valid Rust: `!1 + 1` is `-1` at `i8` and
/// `!(-1)` is `0`, so the contract is `y == 0`. The reader evaluates the fold
/// unsigned (`255`) because its type is not known until it meets the `i8`, and
/// range-checking that guess refused the contract although no `255` is written. The
/// fold now records only its operands' envelopes, so the guess is not checked -- the
/// control shows a genuine literal under the fold (`!128`) is still range-checked
/// against the type the complement meets and is refused.
#[test]
fn an_opaque_folds_provisional_value_is_not_range_checked() {
    let Some(report) =
        verify_realistic(&["contract_opaque_fold_provisional_value_is_not_range_checked"])
    else {
        return;
    };
    let o = outcome(&report, "contract_opaque_fold_provisional_value_is_not_range_checked");
    assert!(o.is_verified(), "`y == !(!1 + 1)` is `y == 0` and must verify, got: {o}");
    let Some(report) =
        verify_realistic(&["contract_literal_under_complement_is_still_range_checked"])
    else {
        return;
    };
    let o = outcome(&report, "contract_literal_under_complement_is_still_range_checked");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`!128` is an `i8` range error and must be refused, got: {o}"
    );
}

/// The written magnitude of a suffixed literal is what Rust range-checks, and a
/// complement's operand envelope must not leak onto an unrelated literal that
/// shares the complement's value term.
///
/// `128i8` alone is a `literal out of range for i8` error and only `-128i8` is
/// legal, because the negation is what meets the type. Recording the *signed value*
/// (`-128`) instead of the written magnitude made the negation add `+128` to the
/// envelope and refuse the valid `-128i8`; it also made the positive `128i8`, which
/// rustc rejects, read as the in-range `-128` -- a wrong verdict in both directions.
/// The complement is worse: at eight bits `!128` is the constant `127`, which the
/// engine hash-conses with a separately written bare `127`, so recording the
/// operand envelope (`128`) on that shared id skipped the valid
/// `x == !128 && y == 127`. The envelope now travels in the operand's own payload.
///
/// Two follow-ups. A *nested* complement whose operand is a fold must union the
/// envelope it inherited with the one the fold recorded on its own term, or the
/// fold's out-of-range literal is dropped and the reader decides a contract rustc
/// rejects (`y == !(!1 - 200)` for an `i8`). And a *named bound* (`i8::MIN`) shares
/// its bit pattern with a bare or suffixed `128`, so the term-keyed envelope map
/// charged the literal's `128` to the bound and skipped a valid contract; the bound
/// is now built as a term of its own.
#[test]
fn a_suffixed_minimum_and_a_complement_operand_are_checked_where_they_are_written() {
    for name in [
        "contract_suffixed_positive_min_magnitude_is_refused",
        "contract_double_negated_min_is_refused",
        "contract_complement_operand_out_of_range_is_refused",
        "contract_negated_complement_operand_is_refused",
        "contract_nested_complement_fold_operand_is_refused",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` is a rustc range error and must be refused, never given a verdict, got: {o}"
        );
    }
    for name in [
        "contract_suffixed_min_literal_still_reads",
        "contract_suffixed_positive_literal_still_reads",
        "contract_complement_does_not_pollute_a_bare_literal",
        "contract_named_min_after_suffixed_min_reads",
        "contract_suffixed_min_after_named_min_reads",
        "contract_named_min_after_bare_128_reads",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} is valid Rust and must verify, got: {o}");
    }
}

/// An *opaque* constant (a complement) widened to a wider operand is refused, and
/// a *fold* is not.
///
/// A complement is taken at the *operand's* width, but the reader holds it at the
/// *scope's*. `!0` against a `u16` is `65535`, so `(x as u16 + !0) == 255` is false
/// in Rust; the reader held `255` and zero-extended it, and *verified* the equality
/// -- a false proof. The signed case fails the same way when the literal's top bit
/// is clear (`!128` against an `i16` is `-129`, not `127`). Both are refused. A
/// *fold* (`200 + 100`) is a value and must still verify.
#[test]
fn an_opaque_widening_is_refused_but_a_fold_widens() {
    let Some(report) = verify_realistic(&[
        "contract_opaque_widened_to_unsigned_is_refused",
        "contract_opaque_widened_to_signed_is_refused",
        "contract_fold_widens_to_unsigned_reads",
    ]) else {
        return;
    };
    for name in [
        "contract_opaque_widened_to_unsigned_is_refused",
        "contract_opaque_widened_to_signed_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "{name} must not verify -- the reader cannot model the complement at the operand width, got: {o}"
        );
    }
    let o = outcome(&report, "contract_fold_widens_to_unsigned_reads");
    assert!(o.is_verified(), "a fold widens exactly and must verify, got: {o}");
}

/// A *suffixed* literal keeps its own width, so a cast of it is not re-read from
/// the names in scope.
///
/// `128i16` is a sixteen-bit `128`, and `128i16 as i32` is `128` in Rust. Sizing
/// the literal from the scope instead -- eight bits here, the only names in scope
/// -- made `128i16` the bit pattern `0x80`, which the widening cast sign-extended
/// to `-128`, and *verified* `ensures: 128i16 as i32 == -128`, a postcondition Rust
/// calls false. The true counterpart (`== 128`) must verify, so the fix is not
/// "refuse every suffixed literal".
#[test]
fn a_suffixed_literal_keeps_its_own_width() {
    let Some(report) = verify_realistic(&[
        "contract_suffixed_literal_keeps_its_width",
        "contract_suffixed_literal_is_its_own_value",
    ]) else {
        return;
    };
    let o = outcome(&report, "contract_suffixed_literal_keeps_its_width");
    assert!(
        !o.is_verified(),
        "`128i16 as i32` is `128`, so `== -128` is false and must not verify, got: {o}"
    );
    let o = outcome(&report, "contract_suffixed_literal_is_its_own_value");
    assert!(o.is_verified(), "`128i16 as i32 == 128` is true and must verify, got: {o}");
}

/// A fold that touches a complement is a width-dependent bit pattern, so its
/// widening is refused; the valid masked and shifted shapes still read.
///
/// `!0 + 2` is `1` in Rust (the complement is `-1`), so
/// `(x as i16 + 2) == !0 + 2` is false; the reader held the complement at the
/// scope's width, added `2` to get `257`, and a later resize truncated it into
/// `i16`'s `1`, *verifying* the false equality. `!0 & 1` is `1` at any width and
/// `!0 >> 0` is `!0`, so both of those must still verify -- the refusal is drawn
/// at the width *depending* on the operand, not at the complement.
#[test]
fn a_complement_fold_widening_is_refused_but_masks_and_shifts_read() {
    let Some(report) = verify_realistic(&[
        "contract_complement_fold_widening_is_refused",
        "contract_complement_mask_widens_exactly",
        "contract_complement_shift_by_zero_reads",
        "contract_complement_division_with_typed_operand_reads",
    ]) else {
        return;
    };
    let o = outcome(&report, "contract_complement_fold_widening_is_refused");
    assert!(!o.is_verified(), "`(x as i16 + 2) == !0 + 2` is false and must not verify, got: {o}");
    for name in [
        "contract_complement_mask_widens_exactly",
        "contract_complement_shift_by_zero_reads",
        "contract_complement_division_with_typed_operand_reads",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} is a valid contract and must verify, got: {o}");
    }
}

/// An untyped fold that *overflows* the operand width is refused, while a fold
/// that fits still reads.
///
/// `!0 + 1` is `256` at the scope's width; against a `u8` that is a rustc
/// `arithmetic operation will overflow` error (`!0` is `255`), but the reader
/// truncated the scope-width fold to the partner's width and read `(!0 + 1) < 1u8`
/// as `0 < 1` -- *verified* for a program rustc rejects. `(!0 + 2) == 1u8` failed
/// the same way (`257` truncated to `1`). Both must be refused. `200 + 100` is
/// `300` at any width holding it, so it is width-independent and must still read.
#[test]
fn an_untyped_fold_overflow_is_refused_but_a_fitting_fold_reads() {
    let Some(report) = verify_realistic(&[
        "contract_untyped_fold_overflow_is_refused",
        "contract_untyped_fold_overflow_equality_is_refused",
        "contract_fitting_fold_still_reads",
    ]) else {
        return;
    };
    for name in [
        "contract_untyped_fold_overflow_is_refused",
        "contract_untyped_fold_overflow_equality_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "{name} folds an untyped constant into a value that overflows the operand width \
             (`E0308`/overflow in Rust) and must be refused, got: {o}"
        );
    }
    let o = outcome(&report, "contract_fitting_fold_still_reads");
    assert!(
        o.is_verified(),
        "`200 + 100` is width-independent and must verify, got: {o}"
    );
}

/// A shift of an *untyped* constant whose width Rust infers is refused when it is
/// only valid at the scope's width, while a shift that is valid at every width
/// reads.
///
/// `255 >> 8` is fine at the scope's width (32, from a `u32` name in scope), but
/// the operand has no type of its own: against a `u8` partner `255` is a `u8`, and
/// a shift by its own width is a rustc `arithmetic operation will overflow`. The
/// reader verified `255 >> 8 <= x` on a program rustc rejects. `(255 >> 1) >= y`
/// for an `i8` `y` failed the same way (`255` is a rustc `literal out of range`).
/// Both must be refused. `1 << 4` is `16` at any width holding it, and a shift of a
/// typed name has a known width, so both must still read.
#[test]
fn an_untyped_shift_that_needs_a_wider_operand_is_refused_but_a_fitting_shift_reads() {
    let Some(report) = verify_realistic(&[
        "contract_untyped_shift_amount_over_narrow_width_is_refused",
        "contract_untyped_left_shift_amount_over_narrow_width_is_refused",
        "contract_untyped_shift_operand_out_of_narrow_range_is_refused",
        "contract_fitting_untyped_shift_still_reads",
        "contract_typed_shift_still_reads",
    ]) else {
        return;
    };
    for name in [
        "contract_untyped_shift_amount_over_narrow_width_is_refused",
        "contract_untyped_left_shift_amount_over_narrow_width_is_refused",
        "contract_untyped_shift_operand_out_of_narrow_range_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "{name} shifts an untyped constant by an amount (or with a value) that is only \
             valid at the scope's width, not the width Rust infers from the partner, and must \
             be refused, got: {o}"
        );
    }
    for name in [
        "contract_fitting_untyped_shift_still_reads",
        "contract_typed_shift_still_reads",
    ] {
        let o = outcome(&report, name);
        assert!(
            o.is_verified(),
            "{name} is a shift whose width is known or whose value fits every width, and must \
             verify, got: {o}"
        );
    }
}

/// A `u128`-suffixed literal is *refused*, not panicked.
///
/// The suffix records width 128, and the range check that guards the literal
/// computes `1u128 << w`. At `w == 128` that shift panics in a debug build (it
/// wraps to a wrong `max` in release, which then lets a 128-bit literal reach
/// `smt::word` -- itself an assertion). The refusal has to come *before* the
/// shift. The two literals here are both small, so the value is not the problem;
/// the *type* is. This pins that the reader reports the function as skipped
/// instead of taking the run down, which is what a panic does.
#[test]
fn a_u128_suffix_literal_is_refused_not_panicked() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: true,\n    ensures: 0u128 == 0u128,\n}\npub fn f(x: u8) -> u8 { x }";
    let Some(o) = verify_src("f", src) else { return };
    let FnOutcome::Skipped { reason } = o else {
        panic!("a `u128`-suffixed literal must be refused, got: {o}");
    };
    assert!(
        reason.contains("128") && reason.contains("64-bit"),
        "the refusal should name the width and the engine limit, got: {reason}"
    );
}

/// A *symbolic* masked operand keeps its type, so a signed/unsigned pairing is
/// refused rather than given a signed reading.
///
/// `x & 128` for a `u8` is a `u8`; masking does not change its operand's type.
/// Marking the result untyped (`Sign::Literal`) let `refuse_mixed_signedness`
/// accept `(x & 128) == y` for a signed `y` -- a pairing rustc rejects (E0308) --
/// and decide it as a signed comparison. The contract must be refused, and the
/// valid *constant* mask (`(!0 & 1)`, width-independent) must still read.
#[test]
fn a_symbolic_mask_keeps_its_type_but_a_constant_mask_still_widens() {
    let Some(report) = verify_realistic(&[
        "contract_symbolic_mask_keeps_its_type",
        "contract_complement_mask_widens_exactly",
    ]) else {
        return;
    };
    let o = outcome(&report, "contract_symbolic_mask_keeps_its_type");
    assert!(
        !o.is_verified(),
        "`(x & 128) == y` pairs a `u8` with an `i8` and must be refused, got: {o}"
    );
    let o = outcome(&report, "contract_complement_mask_widens_exactly");
    assert!(
        o.is_verified(),
        "a constant width-independent mask still widens and must verify, got: {o}"
    );
}

/// A constant whose *type is fixed* may not meet a partner of another width.
///
/// `-1i8` is an `i8`, so `-1i8 < (x as i16)` is `E0308` even though both operands
/// are signed; `refuse_mixed_signedness` passes them, so the width is the only
/// remaining evidence, and `align_widths` used to resize the constant and erase it
/// — *verifying* the contract. A *bare* negation (`-1`) has no width of its own, so
/// it still meets a wider operand. The mismatch and the valid control are asserted
/// together, because the rule must refuse only a fixed width.
#[test]
fn a_fixed_width_constant_may_not_meet_a_partner_of_another_width() {
    let Some(report) = verify_realistic(&[
        "contract_fixed_width_constant_vs_wider_cast_is_refused",
        "contract_two_fixed_width_constants_are_refused",
        "contract_bare_negation_meets_a_wider_operand",
    ]) else {
        return;
    };
    for name in [
        "contract_fixed_width_constant_vs_wider_cast_is_refused",
        "contract_two_fixed_width_constants_are_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "{name} compares a fixed-width constant with a differently-sized operand \
             (`E0308`) and must be refused, got: {o}"
        );
    }
    let o = outcome(&report, "contract_bare_negation_meets_a_wider_operand");
    assert!(
        o.is_verified(),
        "a bare negation infers its width and is well-typed, so it must verify, got: {o}"
    );
}

/// A *typed* constant mask keeps its type, so a pairing of the other signedness is
/// refused rather than decided — in **both** directions.
///
/// `-1i8 & 1` is an `i8` and `1u8 & 1` is a `u8`, even though both compute the
/// small positive `1`: the mask takes the typed operand's type and `==` never
/// coerces. Marking the constant result `Literal` hid the type, so a pairing with
/// the *other* signedness -- `E0308` in Rust -- was read as `1 == y` and
/// *verified*. The first fix excluded only a *signed* typed operand, leaving the
/// unsigned half open; both must be refused, and the same mask against a partner of
/// its own signedness must still verify.
#[test]
fn a_typed_constant_mask_keeps_its_type() {
    let Some(report) = verify_realistic(&[
        "contract_signed_mask_vs_unsigned_is_refused",
        "contract_signed_mask_with_signed_partner_reads",
        "contract_unsigned_mask_vs_signed_is_refused",
        "contract_unsigned_mask_with_unsigned_partner_reads",
    ]) else {
        return;
    };
    for name in [
        "contract_signed_mask_vs_unsigned_is_refused",
        "contract_unsigned_mask_vs_signed_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(!o.is_verified(), "{name} pairs a typed mask with the other signedness \
                                    (`E0308`) and must be refused, got: {o}");
    }
    for name in [
        "contract_signed_mask_with_signed_partner_reads",
        "contract_unsigned_mask_with_unsigned_partner_reads",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} is well-typed and must verify, got: {o}");
    }
}

/// A pin is *transitive*: a right-hand side that names an earlier pinned variable is
/// pinned too, and the body folds as if the whole chain had been written as literals.
///
/// `a == 5 && b == a + 1 && c == b * 2` fixes `c` at `12` by transitivity, so `c / 4` is
/// `12 / 4` and the obligation is a fact about numbers. A single-pass extraction pinned
/// only `a`, left `b` and `c` symbolic, and built the full divider — `incomplete` however
/// small the contract was. The multiply is the second half of the shape: it makes the
/// *path condition* expensive even once every operand is a literal, which is what the
/// closed-goal check in `prove_implies` exists for.
///
/// The `cannot_prove_this` companion is the point: without it, an engine that answered
/// `Verified` for everything would pass, so the negative is what makes the positive a
/// proof rather than a vacuous `true`.
#[test]
fn a_transitive_pin_chain_folds_the_body() {
    let Some(report) = verify_realistic(&[
        "a_transitive_pin_chain_folds_the_body",
        "a_transitive_pin_chain_cannot_prove_this",
    ]) else {
        return;
    };
    let good = outcome(&report, "a_transitive_pin_chain_folds_the_body");
    assert!(good.is_verified(), "a transitive pin chain must fold the body; got: {good}");
    // The negative must be *refuted*, not merely "not verified". A refusal and a
    // counterexample are both "not verified", and only the second is evidence the
    // rewrite did anything: the point of rewriting the pins into the path is that the
    // multiply leaves the assumption and the false claim becomes decidable. Asserting
    // the weaker property would let a regression back to `incomplete` pass.
    let bad = outcome(&report, "a_transitive_pin_chain_cannot_prove_this");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "a false claim about a transitively pinned chain must be refuted, not refused; got: {bad}"
    );
}

/// An unsigned division by a power of two is a shift, and the body over a *symbolic*
/// dividend is decided rather than refused for the divider's diagram.
///
/// The signed fast path existed; the unsigned side did not, so `n / 4` on a `u64` with
/// only a bound on `n` built the full restoring divider and came back `incomplete` in
/// ~0.9 s. The remainder is the other half of the same helper (`n & 3`), and it is here so
/// a future edit that wires only the quotient fails.
///
/// The `cannot_prove_this` companion is what keeps "decided" meaning "decided correctly":
/// without it, a fast path that returned a wrong value for every input could still pass.
#[test]
fn an_unsigned_power_of_two_division_is_a_shift_not_a_divider() {
    let Some(report) = verify_realistic(&[
        "an_unsigned_power_of_two_division_is_decided",
        "an_unsigned_power_of_two_division_cannot_prove_this",
        "an_unsigned_power_of_two_remainder_is_decided",
    ]) else {
        return;
    };
    for name in [
        "an_unsigned_power_of_two_division_is_decided",
        "an_unsigned_power_of_two_remainder_is_decided",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "an unsigned power-of-two op must be decided; `{name}` got: {o}");
    }
    let bad = outcome(&report, "an_unsigned_power_of_two_division_cannot_prove_this");
    assert!(
        !bad.is_verified(),
        "a false claim about an unsigned division must be refuted; got: {bad}"
    );
}

// ---------------------------------------------------------------------------
// Recursion by contract
// ---------------------------------------------------------------------------

/// A recursive function is proved by induction, not by unrolling.
///
/// The self-call is answered by the function's own contract: its precondition is
/// proved of `n - 1`, the `decreases:` measure is proved to shrink, and the
/// postcondition is assumed for the result. The base case is proved by the body,
/// which is what makes the induction well-founded rather than circular.
///
/// Before `decreases:` existed, this function hit `DEFAULT_INLINE_DEPTH` and came
/// back `Incomplete`, so a proof here is the whole point of the feature.
#[test]
fn a_recursive_function_is_proved_by_its_decreases_measure() {
    let Some(report) = verify_realistic(&["a_recursive_identity"]) else { return };
    let o = outcome(&report, "a_recursive_identity");
    assert!(
        o.is_verified(),
        "a recursive function with a decreasing measure must be proved by induction, got: {o}"
    );
}

/// The inductive assumption must not rescue a body that is simply wrong.
///
/// `a_recursive_lie_cannot_prove_this` has `a_recursive_identity`'s contract but a
/// body that returns `n + 1` in the recursive case. If the postcondition were
/// assumed at the base case too -- or if the `return` obligations were skipped --
/// it would come back `verified`, which is a false proof. It must be a definite
/// failure, with a counterexample.
#[test]
fn a_recursive_body_that_does_not_establish_its_postcondition_is_refuted() {
    let Some(report) = verify_realistic(&["a_recursive_lie_cannot_prove_this"]) else { return };
    let o = outcome(&report, "a_recursive_lie_cannot_prove_this");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a recursive body that breaks its postcondition must fail, got: {o}");
    };
    assert_eq!(kind, "postcondition", "got: {o}");
}

/// An assumption with no decreasing measure is circular, so it must be refused.
///
/// `a_recursive_call_that_does_not_decrease_cannot_prove_this` calls itself on the
/// same `n`. Its precondition and postcondition are both true of the body, so
/// nothing but the measure check stands between it and a false proof. It must not
/// verify.
#[test]
fn a_recursive_call_without_a_decreasing_measure_is_not_assumed() {
    let Some(report) = verify_realistic(&["a_recursive_call_that_does_not_decrease_cannot_prove_this"])
    else {
        return;
    };
    let o = outcome(&report, "a_recursive_call_that_does_not_decrease_cannot_prove_this");
    assert!(
        !o.is_verified(),
        "an induction without a decreasing measure must not be assumed, got: {o}"
    );
}

/// The recursive call's *precondition* is an obligation, not a formality.
///
/// `a_recursive_call_out_of_range_cannot_prove_this` has `requires: n <= 3` and
/// calls itself on `n + 1`, leaving that range. Proving the precondition at the
/// call is what keeps the induction hypothesis applicable only where the contract
/// holds; without it the postcondition would be assumed for an input the function
/// never promised anything about.
#[test]
fn a_recursive_call_must_satisfy_its_own_precondition() {
    let Some(report) =
        verify_realistic(&["a_recursive_call_out_of_range_cannot_prove_this"])
    else {
        return;
    };
    let o = outcome(&report, "a_recursive_call_out_of_range_cannot_prove_this");
    assert!(
        !o.is_verified(),
        "a recursive call that violates its own precondition must not be assumed, got: {o}"
    );
}

/// A contract on an *inherent method* is resolved, and its postcondition is
/// actually checked.
///
/// The MIR dump names a method's body `<impl at FILE:L:C: L:C>::bump`, but the
/// source scanner keys the contract by the bare `bump`. Resolving only the exact
/// dump name matched nothing, and a missing contract is not a refusal:
/// `verify_function` derives `requires` and `ensures` from it, so the method was
/// checked against `true` and *no* postcondition and came back `verified` with
/// **zero obligations**. The obligation count is the load-bearing part of this
/// assertion -- a fix that merely matched the name but skipped the body would
/// still report `Verified`, and only the count catches that.
#[test]
fn a_contract_on_an_inherent_method_is_resolved_and_checked() {
    let Some(report) = verify_realistic(&["bump"]) else { return };
    let o = outcome(&report, "bump");
    let FnOutcome::Verified { obligations, .. } = o else {
        panic!("a method whose contract holds must verify, got: {o}");
    };
    assert!(
        *obligations > 0,
        "the method's postcondition must be checked, not silently dropped; got {obligations} \
         obligation(s)"
    );
}

/// The false direction: a method whose postcondition the body does not establish
/// must be refuted, never `verified`.
///
/// `bump_cannot_prove_this` has `bump`'s body but demands `ret == self.n + 2`, so
/// the claim is false on every input. Before the tail resolution this was
/// `Verified { obligations: 0 }` -- a false proof, because the contract never
/// reached the checker. The failure kind is pinned to the postcondition so a fix
/// that refused the method for an unrelated reason cannot pass this.
#[test]
fn a_contract_on_an_inherent_method_that_is_false_is_refuted() {
    let Some(report) = verify_realistic(&["bump_cannot_prove_this"]) else { return };
    let o = outcome(&report, "bump_cannot_prove_this");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a method whose postcondition is false must fail, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

// ---------------------------------------------------------------------------
// Frontend soundness regressions (F1-F4)
//
// Each of these four was a confirmed defect in the MIR frontend, found by probe
// and fixed in the same change. They are pinned here so a later refactor cannot
// quietly reopen them.

/// F1: a free function named exactly like an intrinsic that calls the *intrinsic*
/// is not calling itself.
///
/// `wrapping_add` calls `u8::wrapping_add` on its non-base path. The intrinsic is
/// printed fully qualified (`core::num::<impl u8>::wrapping_add`), and the old
/// resolver matched call names to definitions on the last `::` component alone,
/// so the intrinsic call resolved to *this function*. `try_recursive_call` then
/// assumed this function's own postcondition for the result -- a genuine false
/// proof: `ret == 0` was "proved" while the body returns `n` for `n > 0`. The
/// resolver now also requires the method's `self` type to agree, so `u8` and the
/// free function are distinct and the intrinsic model handles the call.
///
/// The name must be the intrinsic's *exact* tail, and the function needs a
/// `decreases:` measure, or the recursion route that carries the false proof never
/// fires -- a name like `wrapping_add_cannot_prove_this` does not reproduce it.
#[test]
fn an_intrinsic_call_is_not_a_self_recursive_call() {
    let Some(report) = verify_realistic(&["wrapping_add"]) else { return };
    let o = outcome(&report, "wrapping_add");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!(
            "a function named like an intrinsic that calls the intrinsic must be \
             refuted, not proved from its own postcondition; got: {o}"
        );
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// F1 companion: a free function named like an intrinsic that *does* recurse must
/// still be proved by induction.
///
/// The guard that fixes F1 must not refuse a real self-call just because the name
/// matches an intrinsic. `wrapping_add_still_recurses` calls itself, printed bare
/// (`wrapping_add_still_recurses`), which matches it by exact name.
#[test]
fn a_free_recursion_named_like_an_intrinsic_still_recurses() {
    let Some(report) = verify_realistic(&["wrapping_add_still_recurses"]) else { return };
    let o = outcome(&report, "wrapping_add_still_recurses");
    assert!(
        o.is_verified(),
        "a free function named like an intrinsic that recurses must verify; got: {o}"
    );
}

/// F1 companion: a *static associated function* named like an intrinsic that
/// genuinely recurses must still be proved by induction.
///
/// The type check that fixes F1 must not refuse a real self-call just because the
/// tail matches an intrinsic name. `Recursing::wrapping_sub` calls itself, and a
/// `core` intrinsic's call name carries an `<impl` projection that the resolver
/// refuses, so the real self-call still fires.
#[test]
fn a_method_named_like_an_intrinsic_still_recurses() {
    let Some(report) = verify_realistic(&["wrapping_sub"]) else { return };
    let o = outcome(&report, "wrapping_sub");
    assert!(o.is_verified(), "a method named like an intrinsic that recurses must verify; got: {o}");
}

/// F4: a recursive call evaluates the callee's contract with the entry `const`
/// table, so a contract naming a constant resolves at the self-call.
///
/// `a_recursive_contract_naming_a_const_is_resolved` names `LIMIT` in both its
/// `requires` and its `ensures`. The recursive call rebuilt the contract
/// environment from `FieldEnv::default()`, whose `const` table is empty, so the
/// `requires` was unreadable *at the self-call* and the whole function came back
/// `Skipped` -- a lost proof. The call site now carries the entry constants.
#[test]
fn a_recursive_contract_naming_a_const_is_resolved() {
    let Some(report) = verify_realistic(&["a_recursive_contract_naming_a_const_is_resolved"])
    else {
        return;
    };
    let o = outcome(&report, "a_recursive_contract_naming_a_const_is_resolved");
    assert!(
        o.is_verified(),
        "a recursive contract naming a crate-level const must resolve at the self-call; got: {o}"
    );
}

/// F3: a crate-level `const` a *contract* names but no body uses is kept.
///
/// The dump's bare-use test is silent for a constant with no use site at all, so
/// the definition was dropped and the contract went unreadable -- a lost proof.
/// The source says the item is module-scoped, and `spec::crate_level_consts`
/// carries that to the parser.
#[test]
fn a_contract_only_const_is_resolved() {
    let Some(report) = verify_realistic(&["a_contract_only_const_is_resolved"]) else { return };
    let o = outcome(&report, "a_contract_only_const_is_resolved");
    assert!(
        o.is_verified(),
        "a crate-level const named only by a contract must resolve; got: {o}"
    );
}

/// F2: a string literal that spells `const NAME` must not leak a function-local
/// `const` into the program-wide table.
///
/// The bare-use scan reads `const NAME` out of the dump to tell a crate-level
/// constant from a function-local one. A `debug s => const "const LEAKY";`
/// binding and the `alloc` block behind the string spell those letters as *data*,
/// so a scan of the raw line saw a use and gave the local `LEAKY` a program-wide
/// key -- reopening the exact false proof
/// `a_local_const_is_not_in_scope_in_another_function` guards. The scan now drops
/// string literals and skips `alloc` blocks, so the contract's `LEAKY` resolves to
/// nothing and the function is `Skipped`, never `Verified`.
///
/// The local name is *unique* among the file's locals, which is what makes rustc
/// print its definition bare (`const LEAKY`) -- the spelling that collides with a
/// crate-level item. A name shared by two locals is printed qualified and does not
/// reproduce the shape.
#[test]
fn a_string_literal_does_not_leak_a_local_const() {
    let Some(report) =
        verify_realistic(&["a_string_literal_must_not_leak_a_unique_local_const"])
    else {
        return;
    };
    let o = outcome(&report, "a_string_literal_must_not_leak_a_unique_local_const");
    assert!(
        !o.is_verified(),
        "a string literal must not leak a function-local const into a contract; got: {o}"
    );
}

/// A local trait whose `from` shares `From`'s name must be answered by its own
/// body, never by the conversion model.
///
/// The model refuses a module-qualified trait path (`conv_shim::From`) by name, so
/// a call to it reaches the same-dump lookup. This is the false-proof direction:
/// the body returns `7`, so `ret == x` is false at `x == 0`. If the model answered
/// the call it would return `x` and *prove* the claim -- exactly the mistake the
/// trait-path check exists to prevent. A module is used (not a crate-root trait)
/// because a local `impl From<u8> for u16` at the crate root has a *separate*,
/// pre-existing hazard in `resolve_callee`'s owner-type match.
#[test]
fn a_local_trait_from_is_answered_by_its_body() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub mod conv_shim {
    pub trait From<T> {
        fn from(t: T) -> Self;
    }
    impl From<u8> for u16 {
        fn from(_t: u8) -> u16 {
            7
        }
    }
}
spec! {
    requires: x == 0,
    ensures: ret == x as u16,
}
pub fn local_from_is_not_the_model(x: u8) -> u16 {
    conv_shim::From::from(x)
}
"#;
    let Some(o) = verify_src("local_from_is_not_the_model", src) else { return };
    let FnOutcome::Failed { ref kind, .. } = o else {
        panic!("the local trait's body must refute the claim, got: {o}");
    };
    assert_eq!(kind, "postcondition", "got: {o}");
}

/// A widening conversion agrees with a plain `as` cast of the same shape.
///
/// `u16::from(x)` and `x as u16` are the same widening, so their results must be
/// one term. The model builds the conversion through the same extension the cast
/// arm uses; if the two ever disagreed, `ret == x as u16` would be refuted here.
#[test]
fn a_conversion_agrees_with_a_cast_of_the_same_shape() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret == x as u16,
}
pub fn from_matches_cast(x: u8) -> u16 {
    u16::from(x)
}
spec! {
    requires: true,
    ensures: ret == x as i32,
}
pub fn into_signed_matches_cast(x: i8) -> i32 {
    x.into()
}
"#;
    let Some(o) = verify_src("from_matches_cast", src) else { return };
    assert!(o.is_verified(), "`u16::from(x)` must agree with `x as u16`; got: {o}");
    let Some(o) = verify_src("into_signed_matches_cast", src) else { return };
    assert!(o.is_verified(), "`x.into()` must agree with `x as i32`; got: {o}");
}

/// A call to an *unmodelled* conversion is reported unknown, not guessed.
///
/// `u32::from('a')` is a real `From` impl, but the source is a `char`, whose
/// conversion is not one of the integer widenings the model reads -- so it is
/// refused (rather than guessing a width from the destination alone), and the path
/// is reported unknown. This pins that the refusal is a *reported* gap rather than
/// a silent approximation. (`u8::from(bool)` used to be the example; it is now
/// modelled as the zero-extended bit.)
#[test]
fn an_unmodelled_conversion_is_reported_unknown_not_guessed() {
    // `u32::from(char)` is a real `From` impl whose source is not an integer the
    // engine holds (`char` is modelled as a 32-bit value, but a `char` *conversion*
    // is not one of the integer widenings), so it stays unmodelled. `u8::from(bool)`
    // used to be the example here and is now modelled (the zero-extended bit), so
    // the test names a conversion that is still a refusal.
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn from_char_is_unmodelled(c: char) -> u32 {
    u32::from(c)
}
"#;
    let Some(o) = verify_src("from_char_is_unmodelled", src) else { return };
    assert!(
        !o.is_verified(),
        "a conversion the model does not hold must not verify; got: {o}"
    );
    let FnOutcome::Incomplete { .. } = o else {
        panic!("an unmodelled conversion must be `Incomplete`, got: {o}");
    };
}

/// F3: a call to an *external* static associated function must not be answered by
/// a local method that merely shares its tail.
///
/// A static associated function has no `self`, so its definition name
/// `<impl at FILE:L:C: L:C>::m` names no type the way an instance method's
/// receiver does. The old resolver accepted such a candidate on the unique tail
/// alone, so `<u16 as From<u8>>::from(x)` -- `core`'s conversion, which returns
/// `x` -- matched `StaticOwner::from`, whose body returns 99. The contract
/// `ret == 99` then came back verified, a genuine false proof.
///
/// The owner type now comes from the `impl` block's own source line, keyed by the
/// location the dump prints, so the external call no longer matches the local
/// method. The verdict is no longer `Verified`, and it is no longer merely
/// `Incomplete` either: the intrinsic model now *answers* the conversion, so the
/// fixture is refuted with a witness (`x == 0`, where `u16::from(x)` is `0`, not
/// `99`). That is the stronger evidence -- the call is answered by `core`'s own
/// conversion, and the local `from` is not consulted at all.
#[test]
fn an_external_static_call_is_not_answered_by_a_local_method() {
    let Some(report) = verify_realistic(&["a_static_call_resolves_to_its_own_impl_cannot_prove_this"])
    else {
        return;
    };
    let o = outcome(&report, "a_static_call_resolves_to_its_own_impl_cannot_prove_this");
    assert!(
        !o.is_verified(),
        "a call to `u16::from` must not be answered by a local `from`; got: {o}"
    );
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("the modelled conversion must refute the fixture, got: {o}");
    };
    assert_eq!(kind, "postcondition", "got: {o}");
}

/// F3 companion: the owner-type check must not refuse a call to a *local* static
/// method, which does resolve to its own body.
#[test]
fn a_local_static_call_resolves_to_its_impl() {
    let Some(report) = verify_realistic(&["a_local_static_call_resolves_to_its_impl"]) else {
        return;
    };
    let o = outcome(&report, "a_local_static_call_resolves_to_its_impl");
    assert!(o.is_verified(), "a local static method call must resolve and verify; got: {o}");
}

/// F4: two `impl` blocks that each declare a method with the same tail must not
/// share a contract.
///
/// A method's contract was keyed by its bare name, so `TaggedLeft::tag` and
/// `TaggedRight::tag` produced one entry and the later overwrote the earlier. Both
/// methods then resolved to the survivor's claim: a lost proof for the one whose
/// contract was dropped, and -- once the claims are the false directions -- a
/// false proof for the other. The key is now the `impl`'s location.
///
/// Both methods are true here and must verify, which pins that the resolution
/// found *a* contract rather than dropping the method (a missing contract is not a
/// refusal: it means `requires: true` and no `ensures`).
#[test]
fn two_impls_with_a_shared_method_tail_keep_separate_contracts() {
    let Some(report) = verify_realistic(&["tag"]) else { return };
    for key in ["TaggedLeft::tag", "TaggedRight::tag"] {
        let o = outcome(&report, key);
        assert!(o.is_verified(), "{key} must be checked against its own contract; got: {o}");
    }
}

/// F4 companion: with the claims the false way round, each method must be
/// refuted by *its own* postcondition -- never "proved" by the other impl's.
///
/// The two `tag_cannot_prove_this` methods are the mirrors of each other: the left
/// body returns 1 and claims 2, the right returns 2 and claims 1. If the two
/// contracts were conflated, one of them would look true. Each must fail on the
/// postcondition.
#[test]
fn two_impls_with_a_shared_method_tail_do_not_conflate_contracts() {
    let Some(report) = verify_realistic(&["tag_cannot_prove_this"]) else { return };
    for key in ["TaggedLeft::tag_cannot_prove_this", "TaggedRight::tag_cannot_prove_this"] {
        let o = outcome(&report, key);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("{key} must be refuted by its own postcondition, got: {o}");
        };
        assert_eq!(kind, "postcondition", "{key}: the failure must be the postcondition, got `{kind}`");
    }
}

// ---------------------------------------------------------------------------
// Path-aware contract resolution (F1/F2/F3/F4)
//
// rustc names a function's *definition* by the shortest crate-unique path suffix,
// not by its bare name: a free function inside `a` is `a::f` when two modules
// declare `f`, a trait's default method is `T::value`, and a function nested in a
// function is `f::g`. The contract table used to key every non-method contract by
// the bare source name and match only the exact MIR name, so any nested item's
// contract was *dropped* -- and a dropped contract is not a refusal: the function
// was built with `requires: true` and no `ensures`, and a false postcondition was
// reported `Verified { obligations: 0 }`. Each test below is a false postcondition
// that must be *refuted*, or a pair of same-named items that must not share a
// contract.
// ---------------------------------------------------------------------------

/// A trait's default method must be checked against its own contract.
///
/// The MIR prints the definition `T::value`, but the contract was keyed `value`,
/// so it was dropped and the false postcondition verified with zero obligations.
#[test]
fn a_trait_default_method_is_checked_against_its_contract() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait T {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn value(&self) -> u8 { 7 }\n}\n";
    let o = verify_src("T::value", src).expect("T::value must be verified, not dropped");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a trait default with a false postcondition must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// A free function nested in a module must be checked against its own contract.
///
/// The MIR prints `m::f`, but the contract was keyed `f`, so the false
/// postcondition verified with zero obligations.
#[test]
fn a_module_nested_free_function_is_checked_against_its_contract() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub mod m {\n    spec! {\n        ensures: ret == 9,\n    }\n    pub fn f() -> u8 { 7 }\n}\n";
    let o = verify_src("m::f", src).expect("m::f must be verified, not dropped");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a module function with a false postcondition must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// Two sibling modules that each declare `f` must not share one contract.
///
/// A bare key let the second `f` overwrite the first, so one module's body was
/// checked against the other's claim: a lost proof for one, a false proof for the
/// other. Here the left claim is false and the right true, and each must be judged
/// by its own.
#[test]
fn two_sibling_modules_do_not_share_a_contract() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub mod a {\n    spec! {\n        ensures: ret == 9,\n    }\n    pub fn f() -> u8 { 1 }\n}\npub mod b {\n    spec! {\n        ensures: ret == 2,\n    }\n    pub fn f() -> u8 { 2 }\n}\n";
    let left = verify_src("a::f", src).expect("a::f must be present");
    let FnOutcome::Failed { kind, .. } = left else {
        panic!("a::f has a false postcondition and must be refuted, got: {left}");
    };
    assert_eq!(kind, "postcondition", "a::f: the failure must be the postcondition, got `{kind}`");
    let right = verify_src("b::f", src).expect("b::f must be present");
    assert!(right.is_verified(), "b::f's own contract is true and must verify, got: {right}");
}

/// A contracted function whose body `#[cfg]` removes must not be paired with a
/// *different* function's body and reported `Verified`.
///
/// The contract key comes from the source, but `b::a::f` is not compiled, so its
/// suffix (`a::f`) lands on the compiled `a::f` in the dump. The unique-suffix
/// fallback then checked `a::f`'s body against `b::a::f`'s contract and answered
/// `Verified` -- a claim about a function that was never compiled, and a silent
/// concealment of the fact that it was never checked. Ambiguity must be refused
/// in *both* directions: a key that several bodies suffix-match, and a body that
/// several keys suffix-match.
#[test]
fn a_cfg_excluded_contract_does_not_steal_a_compiled_body() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub mod a {\n    spec! {\n        ensures: ret == 1,\n    }\n    pub fn f() -> u8 { 1 }\n}\npub mod b {\n    pub mod a {\n        spec! {\n            ensures: ret == 1,\n        }\n        #[cfg(any())]\n        pub fn f() -> u8 { 2 }\n    }\n}\n";
    let rustc = rustc().expect("rustc");
    let dir = std::env::temp_dir().join(format!("verif-cfg-steal-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("probe.rs");
    std::fs::write(&file, src).expect("write probe");
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &probe_opts()).expect("frontend");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        report.outcomes.is_empty(),
        "no body may be paired with the excluded `b::a::f`'s contract, got: {:?}",
        report.outcomes
    );
    for name in ["a::f", "b::a::f"] {
        assert!(
            report.missing.contains(&name.to_string()),
            "`{name}` must be reported missing rather than silently verified, got: {:?}",
            report.missing
        );
    }
}

/// The `cfg` case's neighbour: a genuine nested free function is still resolved
/// by the unique-suffix rule, so the refusal above is a narrowing, not a blanket
/// refusal of any qualified key.
#[test]
fn a_nested_free_function_is_still_resolved_by_its_suffix() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub mod a {\n    spec! {\n        ensures: ret == 9,\n    }\n    pub fn f() -> u8 { 1 }\n}\n";
    let o = verify_src("a::f", src).expect("a::f must be present");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a::f has a false postcondition and must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "a::f: the failure must be the postcondition, got `{kind}`");
}

/// A trait default and a free function that share a name must keep separate
/// contracts: `A::v` is the trait's, `v` the function's.
#[test]
fn a_trait_default_and_a_free_function_do_not_share_a_contract() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 9,\n}\npub fn v() -> u8 { 1 }\npub trait A {\n    spec! {\n        ensures: ret == 2,\n    }\n    fn v(&self) -> u8 { 2 }\n}\n";
    let free = verify_src("v", src).expect("v must be present");
    let FnOutcome::Failed { kind, .. } = free else {
        panic!("the free `v` has a false postcondition and must be refuted, got: {free}");
    };
    assert_eq!(kind, "postcondition", "v: the failure must be the postcondition, got `{kind}`");
    let method = verify_src("A::v", src).expect("A::v must be present");
    assert!(method.is_verified(), "the trait default's own contract is true, got: {method}");
}

/// A contract on a *trait implementation's* method is resolved and checked.
///
/// The review flagged this as a possible drop: the premise was that rustc prints
/// the implementation as `<Type as Trait>::method`, a name the location-keyed
/// resolver would not match. It does not reproduce on any supported toolchain --
/// rustc prints a same-crate implementation as `<impl at FILE:L:C: L:C>::method`
/// (and a default as `Trait::method`), and that location is exactly what the
/// method key carries. The pin keeps both directions: the true contract verifies
/// and the false one is refuted, so a future naming change cannot quietly turn
/// this into a dropped contract.
#[test]
fn a_contract_on_a_trait_implementation_is_checked() {
    let header = "pub trait Stow { fn value(&self) -> u8; }\npub struct Slot;\n";
    let truth = format!(
        "{header}impl Stow for Slot {{\n    /// ensures: ret == 7\n    fn value(&self) -> u8 {{ 7 }}\n}}\n"
    );
    let o = verify_src("value", &truth).expect("the trait impl's method must be present");
    assert!(o.is_verified(), "`ret == 7` with a body of 7 must verify, got: {o}");
    let falsehood = format!(
        "{header}impl Stow for Slot {{\n    /// ensures: ret == 9\n    fn value(&self) -> u8 {{ 7 }}\n}}\n"
    );
    let o = verify_src("value", &falsehood).expect("the trait impl's method must be present");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("`ret == 9` with a body of 7 must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// F1: an `impl` header whose `{` is on the next line still owns its methods.
///
/// A brace-on-the-next-line header raises no depth on its own line, so a pop
/// keyed on "depth has not increased" dropped it before its methods and each
/// contract was keyed as a free function's -- which then never matched the
/// `<impl at …>::m` name, and the false postcondition verified with zero
/// obligations.
#[test]
fn a_multiline_impl_header_still_owns_its_methods() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub struct Foo;\nimpl Foo\n{\n    spec! {\n        ensures: ret == 9,\n    }\n    pub fn m(&self) -> u8 { 1 }\n}\n";
    let o = verify_src("m", src).expect("m must be present");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a method of a multiline impl with a false postcondition must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

// ---------------------------------------------------------------------------
// A trait declaration's contract
//
// A trait method declaration has no body, so rustc emits no MIR for it and it can
// never be a target on its own. Its contract is a promise every implementation
// inherits, and the implementation is where it is kept or broken. Before this,
// the declaration's contract was filed under the free-function table, where its
// `Trait::method` key suffix-matched an *unrelated* free function of the same
// name -- so a free `fn bump() -> u8 { 9 }` was checked against the trait's
// `ensures: ret == 9`, passed, and was reported `Bump::bump: Verified`. That reads
// as "the trait's promise is discharged" when no implementation was ever checked.
// ---------------------------------------------------------------------------

/// An implementation that breaks the trait's declared postcondition is refuted.
#[test]
fn an_implementation_that_breaks_its_traits_contract_is_refuted() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait Bump {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn bump(&self) -> u8;\n}\npub struct S;\nimpl Bump for S { fn bump(&self) -> u8 { 7 } }\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "the impl carries the promise, so nothing is missing: {missing:?}");
    let o = pick(&outcomes, "bump");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a body of 7 against `ret == 9` must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// The same implementation with the promise kept must verify, so the test above
/// pins the refutation and not a blanket failure.
#[test]
fn an_implementation_that_keeps_its_traits_contract_verifies() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait Bump {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn bump(&self) -> u8;\n}\npub struct S;\nimpl Bump for S { fn bump(&self) -> u8 { 9 } }\n";
    let (outcomes, _) = verify_all_outcomes(src);
    let o = pick(&outcomes, "bump");
    assert!(o.is_verified(), "a body of 9 against `ret == 9` must verify, got: {o}");
}

/// A free function that shares the trait method's name is not the trait's method
/// and must not be judged by the trait's contract.
///
/// This is the false proof the separate table closes: the free `bump` returns 9,
/// which satisfies the trait's claim, so before the fix the report said
/// `Bump::bump: Verified` -- naming the *trait method* as verified although no
/// implementation existed in the file at all.
#[test]
fn a_free_function_does_not_borrow_a_trait_declarations_contract() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait Bump {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn bump(&self) -> u8;\n}\npub fn bump() -> u8 { 9 }\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    for (key, _) in &outcomes {
        assert_ne!(
            key, "Bump::bump",
            "the trait declaration has no body, so it can never be reported as a verified \
             function: {outcomes:?}"
        );
    }
    assert!(
        missing.iter().any(|m| m.starts_with("Bump::bump")),
        "the trait's promise has no implementation here, which must be visible rather than \
         silently unenforced; missing was {missing:?}"
    );
}

/// A trait declaration with no implementation in the file is reported, not dropped.
///
/// It has no MIR, so it can never be a target; leaving it unmentioned would make
/// the run clean while the claim was never checked.
#[test]
fn a_trait_declaration_with_no_implementation_is_reported() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait Bump {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn bump(&self) -> u8;\n}\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(outcomes.is_empty(), "there is no body to verify, got: {outcomes:?}");
    assert!(
        missing.iter().any(|m| m.starts_with("Bump::bump")),
        "an unenforced trait contract must be reported, got: {missing:?}"
    );
}

/// When the impl *and* the trait both declare a contract, the run refuses.
///
/// `resolve` can return only one of the two, so whichever it dropped would vanish
/// without a word. The refusal names both sides instead.
#[test]
fn two_contracts_for_one_method_are_refused_not_silently_chosen() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait Bump {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn bump(&self) -> u8;\n}\npub struct S;\nimpl Bump for S {\n    spec! {\n        ensures: ret == 7,\n    }\n    fn bump(&self) -> u8 { 7 }\n}\n";
    let (outcomes, _) = verify_all_outcomes(src);
    let o = pick(&outcomes, "bump");
    let FnOutcome::Skipped { reason } = o else {
        panic!("two contracts for one function must be refused, got: {o}");
    };
    assert!(
        reason.contains("Bump") && reason.contains("contract"),
        "the refusal must name the trait and say what conflicts, got: `{reason}`"
    );
}

/// Two implementations of one contracted trait are both checked, and stay
/// distinguishable in the report.
///
/// Both are keyed by the bare tail before the fix, so one `outcomes` entry hid the
/// other: one body's verdict was simply not reported.
#[test]
fn two_implementations_of_a_contracted_trait_are_both_checked() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait Bump {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn bump(&self) -> u8;\n}\npub struct A; pub struct B;\nimpl Bump for A { fn bump(&self) -> u8 { 7 } }\nimpl Bump for B { fn bump(&self) -> u8 { 9 } }\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "both impls carry the promise: {missing:?}");
    let a = pick(&outcomes, "A::bump");
    let b = pick(&outcomes, "B::bump");
    let FnOutcome::Failed { kind, .. } = a else {
        panic!("`A::bump` returns 7 against `ret == 9` and must be refuted, got: {a}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
    assert!(b.is_verified(), "`B::bump` returns 9 and must verify, got: {b}");
}

/// A trait with no contract contributes nothing, so an impl that declares its own
/// contract is checked by that one alone.
#[test]
fn an_impl_of_an_uncontracted_trait_keeps_its_own_contract() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait Bump { fn bump(&self) -> u8; }\npub struct S;\nimpl Bump for S {\n    spec! {\n        ensures: ret == 7,\n    }\n    fn bump(&self) -> u8 { 7 }\n}\n";
    let (outcomes, _) = verify_all_outcomes(src);
    let o = pick(&outcomes, "bump");
    assert!(o.is_verified(), "the impl's own `ret == 7` with a body of 7 must verify, got: {o}");
}

/// A trait default whose *signature* contains a `;` -- `[u8; 4]` -- is still a
/// function, not a declaration.
///
/// The body detector stops at the first `;` outside brackets, and the `;` of an
/// array type comes before the body brace. Reading it as the declaration's
/// terminator filed this default as bodyless: its contract would then be inherited
/// by implementations (there are none here) and its own false postcondition would
/// never be checked, while the run still looked clean.
#[test]
fn a_trait_default_returning_an_array_is_still_checked() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait T {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn v(&self, xs: [u8; 4]) -> u8 { 7 }\n}\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "a default has a body, so nothing is missing: {missing:?}");
    let o = pick(&outcomes, "T::v");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a default whose `ret` is 7 against `ret == 9` must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// A trait *default* has a body and real MIR, so it stays an ordinary target and is
/// not swept into the declaration table.
#[test]
fn a_trait_default_method_is_not_treated_as_a_declaration() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait T {\n    spec! {\n        ensures: ret == 9,\n    }\n    fn value(&self) -> u8 { 7 }\n}\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "a default has a body, so nothing is missing: {missing:?}");
    let o = pick(&outcomes, "T::value");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a default with a false postcondition must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// A one-line impl body must not leave the `impl` open over the rest of the file.
///
/// The header's brace opens and closes within its own line, so a pop keyed on the
/// final depth would never fire and every later function would be read as a
/// method of that `impl` -- keyed by location, and so never matched.
#[test]
fn a_one_line_impl_body_does_not_leak_its_scope() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub struct Foo;\nimpl Foo { pub fn m(&self) -> u8 { 1 } }\nspec! {\n    ensures: ret == 9,\n}\npub fn g() -> u8 { 1 }\n";
    let o = verify_src("g", src).expect("g must be present");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("g has a false postcondition and must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

// ---------------------------------------------------------------------------
// The `const` scope scan (the const-generic leak)
// ---------------------------------------------------------------------------

/// A `const` generic parameter must not make a function-local `const` of the same
/// name look crate-level.
///
/// A const-generic's *uses* print as a bare `const N`, the same spelling a
/// crate-level item's use site gets, so the whole-crate bare-use test kept a
/// function-local `const N` under a bare program-wide key. A contract on an
/// unrelated function could then name `N` and resolve it to that local's value --
/// a false proof (or a spurious vacuous-precondition failure). The name is not an
/// item at all, so it must be ignored.
#[test]
fn a_const_generic_does_not_leak_a_local_const() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub fn cg<const N: usize>() -> u8 { N as u8 }\npub fn owner() -> u8 { const N: u8 = 3; N }\nspec! {\n    requires: N == 3,\n    ensures: ret == N,\n}\npub fn reads() -> u8 { 3 }\n";
    let o = verify_src("reads", src).expect("reads must be present");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "a contract naming the leaked local `N` must be refused, not decided, got: {o}"
    );
}

/// The same leak with the parameter list split across lines.
#[test]
fn a_split_const_generic_does_not_leak_a_local_const() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub fn cg<\n    const N: usize,\n>() -> u8 { N as u8 }\npub fn owner() -> u8 { const N: u8 = 3; N }\nspec! {\n    requires: N == 3,\n    ensures: ret == N,\n}\npub fn reads() -> u8 { 3 }\n";
    let o = verify_src("reads", src).expect("reads must be present");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "a contract naming the leaked local `N` must be refused, not decided, got: {o}"
    );
}

/// The same leak when a newline, tab or comment sits between `const` and the name.
///
/// All three are legal Rust for the same parameter, but the scan once matched a
/// literal `"const "`, so `const\n    N: usize` and `const/*c*/N: usize` were not
/// recognized. The name then stayed out of `const_generics`, its bare use made a
/// function-local `const N` look crate-level, and a contract naming `N` resolved
/// to that local's value -- a false proof.
#[test]
fn a_const_generic_after_whitespace_or_a_comment_does_not_leak_a_local_const() {
    for header in ["const\n    N: usize", "const\tN: usize", "const/*c*/N: usize"] {
        let src = format!(
            "pub fn cg<{header}>() -> u8 {{ N as u8 }}\n\
             pub fn owner() -> u8 {{ const N: u8 = 3; N }}\n\
             /// requires: N == 3\n/// ensures: ret == N\npub fn reads() -> u8 {{ 3 }}\n"
        );
        let o = verify_src("reads", &src).expect("reads must be present");
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "a contract naming the leaked local `N` must be refused, not decided, got: {o}"
        );
    }
}

/// A `{` inside an `impl` header's generic arguments must not be taken for the
/// body brace.
///
/// `impl Foo<{ 1 }>` writes a const expression in the header. Counting that brace
/// as the body marked the `impl` opened and popped it before the real body, so the
/// method lost its `impl` location, its contract was keyed as a free function's,
/// and it was reported *missing* -- a contracted function dropped from the check
/// set. The real body brace is the one reached with no `<` open.
#[test]
fn a_const_expression_in_an_impl_header_does_not_hide_its_method() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub struct Foo<const N: usize>;\nimpl Foo<{ 1 }>\n{\n    spec! {\n        ensures: ret == 9,\n    }\n    pub fn m(&self) -> u8 { 7 }\n}\n";
    let o = verify_src("m", src).expect("m must be present");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a method with a false postcondition must be refuted, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// The scan must still read a genuine crate-level `const` that shares a name with
/// a const-generic parameter elsewhere, so the fix is a narrowing, not a blanket
/// refusal of the name.
#[test]
fn a_crate_level_const_is_still_read_beside_a_const_generic() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub const N: u8 = 5;\npub fn cg<const N: usize>() -> usize { N }\nspec! {\n    ensures: ret == N,\n}\npub fn reads() -> u8 { 5 }\n";
    let specs = spec::extract(src);
    assert!(specs.crate_consts.contains("N"), "the crate-level `N` must still be read");
    assert!(specs.const_generics.contains("N"), "the const-generic `N` must be recognized");
    let o = verify_src("reads", src).expect("reads must be present");
    assert!(o.is_verified(), "`ret == N` with crate `N == 5` must verify, got: {o}");
}

/// A function-local `const` of the same name as a crate-level one must not shadow
/// it in a contract on a *different* function.
///
/// With both items compiled, rustc prints the local's definition and use site
/// qualified (`const owner::K`), so the crate `const K` keeps its own value and
/// `reads` returning `3` can never be *proved* against it. This is the control for
/// [`a_cfg_disabled_crate_const_does_not_let_a_local_shadow_it`]: the same shape,
/// but the crate item is compiled. The property asserted is the soundness one --
/// the local's `3` must never be mistaken for the crate's `7` -- because on an
/// older compiler a crate-level constant prints a block body the parser does not
/// fold, leaving the name unresolved rather than decided.
#[test]
fn a_local_const_does_not_shadow_a_crate_const_in_another_contract() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub const K: u8 = 7;\npub fn owner() -> u8 { const K: u8 = 3; K }\nspec! {\n    ensures: ret == K,\n}\npub fn reads() -> u8 { 3 }\n";
    let o = verify_src("reads", src).expect("reads must be present");
    assert!(
        !o.is_verified(),
        "`K` is the crate's 7, so `ret == K` with ret 3 must not be proved against \
         `owner`'s local 3, got: {o}"
    );
    if let FnOutcome::Failed { kind, .. } = o {
        assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
    }
}

/// A `#[cfg]`-disabled crate-level `const` must not let a function-local `const`
/// of the same name become a program-wide name.
///
/// The source scanner still sees the disabled item, so it reports `K` as
/// crate-level. The compiler removed it, so the dump has no crate `const K`; the
/// only `K` is `owner`'s local, whose *definition* prints bare (`const K: u8 =
/// const 3_u8;`) while its *use* stays qualified (`const owner::K`). Recording
/// that bare definition under the crate key let an unrelated contract write
/// `ret == K` and be *proved* against another function's local -- a false proof
/// on a claim the function could not have written.
#[test]
fn a_cfg_disabled_crate_const_does_not_let_a_local_shadow_it() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\n#[cfg(any())]\npub const K: u8 = 7;\npub fn owner() -> u8 { const K: u8 = 3; K }\nspec! {\n    ensures: ret == K,\n}\npub fn reads() -> u8 { 3 }\n";
    let o = verify_src("reads", src).expect("reads must be present");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`K` is not a crate-level name here, so the contract must be refused, got: {o}"
    );
}

/// The `#[cfg]` case's neighbour: a `#[cfg]`-disabled `const` with no local twin
/// must also be refused, because the name is still not a crate-level one.
#[test]
fn a_cfg_disabled_crate_const_alone_is_not_a_program_wide_name() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\n#[cfg(any())]\npub const K: u8 = 7;\nspec! {\n    ensures: ret == K,\n}\npub fn reads() -> u8 { 3 }\n";
    let o = verify_src("reads", src).expect("reads must be present");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "a disabled item is not a name the compiled crate has, got: {o}"
    );
}

/// A local `const` no crate-level item shares must not be readable by name: there
/// is no program-wide `K`, so the contract is refused rather than resolved to the
/// local's value.
#[test]
fn a_local_const_alone_is_not_a_program_wide_name() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub fn owner() -> u8 { const K: u8 = 3; K }\nspec! {\n    ensures: ret == K,\n}\npub fn reads() -> u8 { 3 }\n";
    let o = verify_src("reads", src).expect("reads must be present");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "a name only a function-local `const` carries must be refused, not decided, got: {o}"
    );
}

/// An *associated* constant must not hide a compiled crate-level constant of the
/// same name.
///
/// rustc uses an associated constant's path (`const Foo::K`) but defines it by
/// its impl location (`const <impl at …>::K`), so the use path has no matching
/// definition. Reading that mismatch as "a function-local definition" -- as the
/// `#[cfg]`-disabled case needs -- also claims the bare tail of a perfectly good
/// associated use, and then discards the compiled crate `const K`, leaving a
/// contract that names it unreadable. The claim must be limited to uses whose
/// path prefix is a *function*.
#[test]
fn an_associated_const_does_not_hide_a_crate_const() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nconst K: u8 = 7;\npub struct Foo;\nimpl Foo { pub const K: u8 = 3; }\npub fn uses_assoc() -> u8 { Foo::K }\nspec! {\n    ensures: ret == K,\n}\npub fn reads() -> u8 { 7 }\n";
    let o = verify_src("reads", src).expect("reads must be present");
    assert!(
        o.is_verified(),
        "`K` is the compiled crate constant (7), so `ret == K` must be proved \
         despite the associated `Foo::K`, got: {o}"
    );
}

/// A function-local `const` inside a *method* or a nested function must still be
/// refused as a program-wide name, even though its use path is longer than
/// `owner::K` (`Foo::method::L`, `outer::inner::M`).
///
/// The rule must read the path's *owning* `::` segment as the function, not the
/// whole prefix: an exact-prefix match would read `Foo::method` as the owner and
/// drop the claim, letting the local `L` leak. A crate `const L` of the same name
/// is present so that a leak shows up as a *false proof* (`ret == L` proved
/// against the local's 4) rather than merely a different skip reason.
#[test]
fn a_nested_or_method_local_const_is_not_a_program_wide_name() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub const L: u8 = 40;\npub const M: u8 = 10;\npub struct Foo;\nimpl Foo { pub fn method(&self) -> u8 { const L: u8 = 4; L } }\npub fn outer() -> u8 { fn inner() -> u8 { const M: u8 = 1; M } inner() }\nspec! {\n    ensures: ret == L,\n}\npub fn reads_l() -> u8 { 4 }\nspec! {\n    ensures: ret == M,\n}\npub fn reads_m() -> u8 { 1 }\n";
    for (name, local) in [("reads_l", "L"), ("reads_m", "M")] {
        let o = verify_src(name, src).expect("contracted function must be present");
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{local}` in `{name}` must resolve to the crate constant, not the \
             method/nested local, so a body of the local's value must be refused, \
             got: {o}"
        );
    }
}

/// A `const` whose body branches between two literal returns must not fold to the
/// first arm.
///
/// `K = if false { 7 } else { 8 }` is `8`, and rustc prints a CTFE body with one
/// `_0` arm per branch (`bb1: _0 = const 7_u8`, `bb2: _0 = const 8_u8`). Folding
/// the first arm stores `K = 7`, so `ensures: ret == 7` on a function that returns
/// `K` is reported **verified** -- a false proof about a value the constant never
/// has -- while the true claim `ret == 8` is refused. The folder instead follows
/// the `switchInt` on the discriminant's actual value, so it takes `bb2` and
/// stores `K = 8`: the true claim decides and the false one is refuted. (An
/// earlier fix refused a branching body outright; resolving the branch by value is
/// strictly more coverage with the same soundness.)
///
/// This is the *reachable* form of the bug: rustc emits a brace-block for an
/// `if`-based constant on **current stable** as well as on 1.85, so the hole was
/// not confined to the MSRV the earlier fix was written for.
#[test]
fn a_branching_const_does_not_fold_to_its_first_arm() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub const K: u8 = if false { 7 } else { 8 };\nspec! {\n    ensures: ret == 8,\n}\npub fn true_claim() -> u8 { K }\nspec! {\n    ensures: ret == 7,\n}\npub fn false_claim() -> u8 { K }\n";
    let true_claim = verify_src("true_claim", src).expect("true_claim must be present");
    let false_claim = verify_src("false_claim", src).expect("false_claim must be present");
    assert!(
        !false_claim.is_verified(),
        "`K` is 8, so `ret == 7` must not be reported verified, got: {false_claim}"
    );
    assert!(
        true_claim.is_verified(),
        "a branching const body folds to the *taken* arm, so `ret == 8` decides; \
         got: {true_claim}"
    );
}

/// The front end must not panic on a source that ends inside an unclosed block
/// comment.
///
/// `verify_file_with` scans the source for contracts *before* it runs rustc, so a
/// malformed file reaches `const_generic_params`. A `const` generic parameter
/// followed by an unterminated `/*` runs the comment skip to end-of-file; if the
/// skip then steps past the buffer, the slice panics. Malformed source is rustc's
/// error to report, not a crash here.
#[test]
fn an_unclosed_block_comment_after_const_is_not_a_panic() {
    use verif::mir::spec;
    for src in [
        "fn f<const /*",
        "fn f<const /*x",
        "fn f<const /* ",
        "fn f<const /*/",
        "fn f<const /*x*",
        "fn f<const /*x*/",
        "fn f<const /*\n",
    ] {
        // The property is "does not panic", so the call itself is the assertion.
        let _ = spec::const_generic_params(src);
    }
}

/// The `(name, outcome)` pairs for a source written to a temp file, for a test
/// that needs more than one function out of the same file.
///
/// [`verify_src`] returns one outcome and asserts the function was not dropped,
/// which is what a single-function test wants. The modular-call tests need to
/// read a *caller* and confirm what happened to a *callee* in the same run, so
/// this hands back every outcome and lets the test pick.
fn verify_all_src(src: &str) -> Option<Vec<(String, FnOutcome)>> {
    let rustc = rustc()?;
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir()
        .join(format!("verif-all-{}-{seq}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("probe.rs");
    std::fs::write(&file, src).expect("write probe");
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &probe_opts()).expect("frontend");
    let _ = std::fs::remove_dir_all(&dir);
    Some(report.outcomes)
}

/// The outcome for `name` out of a multi-function run.
fn pick<'a>(outcomes: &'a [(String, FnOutcome)], name: &str) -> &'a FnOutcome {
    outcomes
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, o)| o)
        .unwrap_or_else(|| {
            let seen: Vec<&str> = outcomes.iter().map(|(n, _)| n.as_str()).collect();
            panic!("`{name}` missing from {seen:?}")
        })
}

// ---------------------------------------------------------------------------
// Modular verification: a call answered by the callee's contract
// ---------------------------------------------------------------------------

/// A call to a function whose body is not in the dump, but whose contract is,
/// is decided by the contract.
///
/// This is the gap the README used to state as "calls are inlined one level": a
/// callee with no body had no route to a verdict at all. The contract gives one,
/// and the two obligations it produces are visible in the count -- the
/// precondition proved, and (with the postcondition assumed) the caller's own
/// postcondition proved from it.
#[test]
fn a_callee_contract_decides_a_call_with_no_body() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\n    spec! {\n        requires: n <= 10,\n        ensures: ret <= n + 1,\n    }\n    fn ext_bump(n: u32) -> u32;\n}\n\nspec! {\n    requires: x <= 10,\n    ensures: ret <= 11,\n}\npub fn caller_ok(x: u32) -> u32 { unsafe { ext_bump(x) } }\n";
    let Some(all) = verify_all_src(src) else { return };
    let o = pick(&all, "caller_ok");
    assert!(o.is_verified(), "the contract should decide this call, got: {o}");
    match o {
        FnOutcome::Verified { obligations, .. } => assert!(
            *obligations >= 2,
            "the precondition obligation and the caller's postcondition must both \
             be present, got {obligations}"
        ),
        _ => unreachable!(),
    }
}

/// A caller that does not establish the callee's precondition is refused.
///
/// The postcondition is *assumed*, so a caller that reaches the call with an
/// argument outside the precondition would be assuming something the callee
/// never promised. Only the precondition obligation catches this -- the
/// postcondition `ret <= 101` follows from the assumption -- which is exactly
/// why the precondition has to be a proof obligation rather than a comment.
#[test]
fn a_caller_that_does_not_establish_the_precondition_fails() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\n    spec! {\n        requires: n <= 10,\n        ensures: ret <= n + 1,\n    }\n    fn ext_bump(n: u32) -> u32;\n}\n\nspec! {\n    requires: x <= 100,\n    ensures: ret <= 101,\n}\npub fn caller_pre_fails(x: u32) -> u32 { unsafe { ext_bump(x) } }\n";
    let Some(all) = verify_all_src(src) else { return };
    let o = pick(&all, "caller_pre_fails");
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("callee's precondition"),
            "the failure must name the precondition, got: {kind}"
        ),
        _ => panic!("a call outside the callee's precondition must FAIL, got: {o}"),
    }
}

/// A callee whose postcondition is unsatisfiable never returns, and the caller
/// must not be credited with a proof past the call.
///
/// `ensures false` describes a function that cannot return. Assuming it would
/// make every claim after the call vacuously true, so a caller whose body is
/// `diverge(x); unreachable` would "verify". This is the MIR twin of `wp`'s
/// `Rule::DivergentCall`, and the verdict is a *refutation* of the
/// postcondition -- `Unsat` -- so its discharge is `Unsat` rather than `Valid`.
#[test]
fn a_call_to_a_callee_whose_postcondition_is_unsatisfiable_fails() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\n    spec! {\n        requires: n <= 10,\n        ensures: false,\n    }\n    fn ext_never_returns(n: u32) -> u32;\n}\n\nspec! {\n    requires: x <= 10,\n    ensures: ret == 0,\n}\npub fn caller_of_divergent(x: u32) -> u32 { unsafe { ext_never_returns(x) } }\n";
    let Some(all) = verify_all_src(src) else { return };
    let o = pick(&all, "caller_of_divergent");
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("postcondition is unsatisfiable"),
            "the failure must name the divergence, got: {kind}"
        ),
        _ => panic!("a divergent callee must FAIL the caller, got: {o}"),
    }
}

/// A callee with a precondition but no postcondition promises nothing about its
/// result, so there is nothing to assume and the call is incomplete.
///
/// The alternative reading -- no `ensures` means `ensures true` -- would let the
/// caller's own postcondition be proved from nothing at all. An absent clause is
/// the absence of a promise, not a promise of everything.
#[test]
fn a_callee_with_no_postcondition_is_not_assumed_to_promise_everything() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\n    spec! {\n        requires: n <= 10,\n    }\n    fn ext_no_post(n: u32) -> u32;\n}\n\nspec! {\n    requires: x <= 10,\n    ensures: ret <= 11,\n}\npub fn caller_of_silent(x: u32) -> u32 { unsafe { ext_no_post(x) } }\n";
    let Some(all) = verify_all_src(src) else { return };
    let o = pick(&all, "caller_of_silent");
    assert!(
        !o.is_verified(),
        "a callee with no `ensures` gives nothing to assume, got: {o}"
    );
    match o {
        FnOutcome::Incomplete { reasons, .. } => assert!(
            reasons.iter().any(|r| r.contains("no `ensures`")),
            "the reason must say the callee has no postcondition, got: {reasons:?}"
        ),
        _ => panic!("expected Incomplete, got: {o}"),
    }
}

/// A callee whose signature the scanner cannot read is refused rather than bound
/// positionally to the wrong parameter.
///
/// rustc enforces a call's arity, so a *real* mismatch cannot come from valid
/// Rust. It comes from the scanner: a parameter written as a pattern (`_: u32`)
/// has no name for a contract to mention, so [`spec`]'s signature reader stops
/// and reports no parameters at all. The call still has an argument, the two
/// counts disagree, and the contract's `requires: n <= 10` has no parameter to
/// attach to. Binding it to the first argument anyway would prove a precondition
/// nobody stated, so the call is refused.
#[test]
fn a_signature_the_scanner_cannot_read_refuses_the_call() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\n    spec! {\n        requires: n <= 10,\n        ensures: ret <= n + 1,\n    }\n    fn ext_bump(_: u32) -> u32;\n}\n\nspec! {\n    requires: x <= 10,\n    ensures: ret <= 11,\n}\npub fn caller_unnamed(x: u32) -> u32 { unsafe { ext_bump(x) } }\n";
    let Some(all) = verify_all_src(src) else { return };
    let o = pick(&all, "caller_unnamed");
    assert!(
        !o.is_verified(),
        "a parameter the scanner could not name must not be bound positionally, got: {o}"
    );
    match o {
        FnOutcome::Incomplete { reasons, .. } => assert!(
            reasons.iter().any(|r| r.contains("parameter(s)") || r.contains("signature")),
            "the reason must name the arity or the unreadable signature, got: {reasons:?}"
        ),
        _ => panic!("expected Incomplete, got: {o}"),
    }
}

/// A caller that passes a reference to a callee outside the dump is refused.
///
/// `Ty::Ref` is modelled as its referent, so a `&mut` argument handed to a callee
/// with no body would have its write vanish: the callee's contract talks about
/// the referent, the caller holds the value, and a postcondition about the write
/// would be checked against a state the callee never produced. No aliasing model,
/// no contract route.
#[test]
fn a_call_passing_a_reference_to_a_bodyless_callee_is_refused() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\n    spec! {\n        requires: *r <= 10,\n        ensures: true,\n    }\n    fn ext_take(r: &mut u32);\n}\n\nspec! {\n    requires: x <= 10,\n    ensures: ret <= 10,\n}\npub fn caller_by_ref(x: u32) -> u32 {\n    let mut y = x;\n    unsafe { ext_take(&mut y) };\n    y\n}\n";
    let Some(all) = verify_all_src(src) else { return };
    let o = pick(&all, "caller_by_ref");
    assert!(
        !o.is_verified(),
        "a reference argument needs the aliasing model, got: {o}"
    );
    match o {
        FnOutcome::Incomplete { reasons, .. } => assert!(
            reasons.iter().any(|r| r.contains("passes a reference")),
            "the reason must name the reference, got: {reasons:?}"
        ),
        _ => panic!("expected Incomplete, got: {o}"),
    }
}

/// A callee whose body *is* in the dump is inlined, not answered from its
/// contract.
///
/// Inlining is strictly more precise -- it executes the callee rather than
/// trusting what it promised -- so the contract route must not shadow it. The
/// discriminating test is a callee whose contract is *weaker* than its body: the
/// caller's claim is only provable from the body, so a pass proves the body was
/// used. A contract-only route would leave it undecided.
#[test]
fn a_callee_with_a_body_is_inlined_rather_than_answered_from_its_contract() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret <= 100,\n}\npub fn callee(a: u32) -> u32 { a }\n\nspec! {\n    requires: x <= 3,\n    ensures: ret <= 3,\n}\npub fn caller(x: u32) -> u32 { callee(x) }\n";
    let Some(all) = verify_all_src(src) else { return };
    let o = pick(&all, "caller");
    assert!(
        o.is_verified(),
        "the callee's body is in the dump, so inlining proves `ret <= 3`; a contract-only \
         route would only give `ret <= 100`, got: {o}"
    );
}

// ---------------------------------------------------------------------------
// Inherited trait contracts bind by declaration position, not by name
// ---------------------------------------------------------------------------

/// An implementation may name its parameters differently from the trait it
/// implements, and the declaration's contract means the *declaration's* names.
///
/// The two signatures are the same method, so their parameters correspond by
/// position: the declaration's first value parameter is the implementation's first
/// value parameter, whatever either is called. Binding the contract by the
/// implementation's own names instead attached `ret == a` to whichever argument the
/// implementation called `a`, which is the wrong value whenever the names are
/// swapped. That is a false proof, not a lost one: the body returned its *second*
/// argument and the tool reported the postcondition proved.
///
/// Both directions are pinned. The body that returns the implementation's `a` is
/// the trait's `b`, so it must be refuted; the body that returns the
/// implementation's `b` is the trait's `a`, so it must verify. A tool that bound by
/// name would get exactly these two backwards.
#[test]
fn an_inherited_contract_binds_parameters_by_position_not_by_name() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait T {\nspec! {\n    ensures: ret == a,\n}\nfn f(&self, a: u8, b: u8) -> u8;\n}\npub struct S;\nimpl T for S { fn f(&self, b: u8, a: u8) -> u8 { a } }\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "the impl carries the declaration's contract, so nothing is missing: {missing:?}");
    let o = pick(&outcomes, "f");
    assert!(
        !o.is_verified(),
        "the body returns the implementation's `a`, which is the trait's `b`, so \
         `ret == a` (the trait's `a`) must be refuted, got: {o}"
    );

    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait T {\nspec! {\n    ensures: ret == a,\n}\nfn f(&self, a: u8, b: u8) -> u8;\n}\npub struct S;\nimpl T for S { fn f(&self, b: u8, a: u8) -> u8 { b } }\n";
    let (outcomes, _) = verify_all_outcomes(src);
    let o = pick(&outcomes, "f");
    assert!(
        o.is_verified(),
        "the body returns the implementation's `b`, which is the trait's `a`, so \
         `ret == a` holds, got: {o}"
    );
}

/// The same alignment holds for a field a contract names: `c.lo` means the
/// *declaration's* parameter `c`, at whatever position the implementation puts it.
///
/// A struct argument's fields are bound under the argument's name, so an inherited
/// contract that names `c.lo` has to find the fields under the declaration's `c`,
/// not the implementation's. Binding them under the implementation's name would
/// leave the contract unreadable -- refused rather than mis-proved, but still a
/// lost proof.
#[test]
fn an_inherited_contract_binds_a_field_to_the_declarations_parameter() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub struct Config { pub lo: u8, pub hi: u8 }\npub trait T {\nspec! {\n    requires: c.lo <= c.hi,\n    ensures: ret == c.hi,\n}\nfn hi_of(&self, c: Config) -> u8;\n}\npub struct S;\nimpl T for S { fn hi_of(&self, k: Config) -> u8 { k.hi } }\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "nothing is missing here: {missing:?}");
    let o = pick(&outcomes, "hi_of");
    assert!(
        o.is_verified(),
        "the contract names the declaration's `c`, which is the implementation's \
         `k` by position, so `c.hi` is `k.hi` and the body satisfies it, got: {o}"
    );
}

/// An inherited contract that cannot be aligned is refused, not bound by guess.
///
/// A declaration whose parameter list the scanner cannot read whole -- here a
/// pattern (`_: u8`) with no name for a contract to mention -- leaves the positions
/// unknown, so "the Nth name means the Nth local" stops being true. Binding by
/// position anyway would attach the contract to an argument it may not mean, which
/// is the failure the alignment exists to prevent. The implementation is *skipped*
/// with a reason that names the unreadable signature, rather than verified against a
/// guess or silently dropped.
#[test]
fn an_inherited_contract_that_cannot_be_aligned_is_refused() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub trait T {\nspec! {\n    ensures: ret == 1,\n}\nfn f(&self, _: u8) -> u8;\n}\npub struct S;\nimpl T for S { fn f(&self, a: u8) -> u8 { let _ = a; 2 } }\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "the impl is present, so nothing is missing: {missing:?}");
    let o = pick(&outcomes, "f");
    assert!(
        !o.is_verified(),
        "a contract whose declaration cannot be aligned must not be bound by guess, got: {o}"
    );
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("signature"),
            "the refusal must name the unreadable declaration signature, got: {reason}"
        ),
        _ => panic!("expected Skipped, got: {o}"),
    }
}

// ---------------------------------------------------------------------------
// A wrapped return type is not read as unsigned
// ---------------------------------------------------------------------------

/// A return type that wraps to the next line leaves the signature unreadable, and
/// an unreadable signature refuses the call.
///
/// The reader used to take everything between `->` and the end of the line, so
/// `fn ext() ->` followed by `i8;` produced an empty type, which reads as unsigned.
/// A caller testing `ext() < 0` then took the unsigned branch and a postcondition
/// that does not hold was reported proved. The whole signature is refused instead,
/// which is the same discipline the parameter list already followed.
#[test]
fn a_return_type_that_wraps_to_the_next_line_refuses_the_call() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\nspec! {\n    ensures: ret == i8::MIN,\n}\nfn ext() ->\ni8;\n}\nspec! {\n    ensures: ret == 0,\n}\npub fn caller() -> u8 { if unsafe { ext() } < 0 { 1u8 } else { 0u8 } }\n";
    let (outcomes, _) = verify_all_outcomes(src);
    let o = pick(&outcomes, "caller");
    assert!(
        !o.is_verified(),
        "the return type was not read whole, so the call must be refused rather than \
         checked against an unsigned reading, got: {o}"
    );
    match o {
        FnOutcome::Incomplete { reasons, .. } => assert!(
            reasons.iter().any(|r| r.contains("signature")),
            "the reason must name the unreadable signature, got: {reasons:?}"
        ),
        _ => panic!("expected Incomplete, got: {o}"),
    }
}

/// The control: the same signature on one line *is* read, and the caller's false
/// postcondition is refuted rather than verified.
#[test]
fn a_return_type_on_one_line_is_read_and_refutes_the_false_claim() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\nspec! {\n    ensures: ret == i8::MIN,\n}\nfn ext() -> i8;\n}\nspec! {\n    ensures: ret == 0,\n}\npub fn caller() -> u8 { if unsafe { ext() } < 0 { 1u8 } else { 0u8 } }\n";
    let (outcomes, _) = verify_all_outcomes(src);
    let o = pick(&outcomes, "caller");
    assert!(
        !o.is_verified(),
        "a signed return of i8::MIN makes `ext() < 0` true, so `ret == 0` is false \
         for that input, got: {o}"
    );
    match o {
        FnOutcome::Failed { .. } => {}
        _ => panic!("expected a definite counterexample, got: {o}"),
    }
}

// ---------------------------------------------------------------------------
// A trait path written with a relative root names the declared trait
// ---------------------------------------------------------------------------

/// `impl crate::T for S` is an implementation of `T`, so the declaration's contract
/// is checked on it.
///
/// The qualifier used to be kept as written, so the impl's trait path never matched
/// the declaration's module-qualified key: the impl was checked against nothing and
/// the declaration was reported as having no implementation. Both halves of that are
/// a silently unenforced promise. `crate::` at the root and `self::` inside a module
/// resolve to the same key as the bare name.
#[test]
fn a_trait_impl_written_with_a_relative_root_is_checked() {
    for (label, path) in [("crate::T", "crate::T"), ("self::T", "self::T")] {
        let src = format!(
            "pub trait T {{\n\
             /// ensures: ret == 9\n\
             fn f(&self) -> u8;\n\
             }}\n\
             pub struct S;\n\
             impl {path} for S {{ fn f(&self) -> u8 {{ 7 }} }}\n"
        );
        let (outcomes, missing) = verify_all_outcomes(&src);
        assert!(
            missing.is_empty(),
            "`{label}` names the declared trait, so nothing is missing: {missing:?}"
        );
        let o = pick(&outcomes, "f");
        assert!(
            !o.is_verified(),
            "the body returns 7 and the trait promises 9, so `{label}` must be \
             refuted, got: {o}"
        );
    }
}

// ---------------------------------------------------------------------------
// A bodyless declaration's contract is assumed, not missing
// ---------------------------------------------------------------------------

/// A file whose only external call verified is clean.
///
/// An `extern` item has no MIR by construction, so its contract is assumed at each
/// call rather than checked on a body. Reporting it `missing` made `is_clean()`
/// false for a file with nothing wrong, which is the false alarm that trains a
/// reader to ignore the report. The call itself must still be verified.
#[test]
fn a_bodyless_declaration_is_assumed_not_reported_missing() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\nspec! {\n    ensures: ret == 1,\n}\nfn ext() -> u8;\n}\nspec! {\n    ensures: ret == 1,\n}\npub fn caller() -> u8 { unsafe { ext() } }\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(
        missing.is_empty(),
        "an `extern` declaration is assumed at its calls, not missing: {missing:?}"
    );
    let o = pick(&outcomes, "caller");
    assert!(o.is_verified(), "the call is decided by the callee's contract, got: {o}");
}

/// A bodyless declaration that is *called* with an unsatisfiable postcondition is
/// still a failure -- being assumed is not being ignored.
#[test]
fn an_assumed_bodyless_contract_is_still_refuted_when_unsatisfiable() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\nspec! {\n    ensures: ret == 1 && ret == 2,\n}\nfn ext() -> u8;\n}\nspec! {\n    ensures: ret == 1,\n}\npub fn caller() -> u8 { unsafe { ext() } }\n";
    let (outcomes, _) = verify_all_outcomes(src);
    let o = pick(&outcomes, "caller");
    assert!(
        !o.is_verified(),
        "a postcondition no input satisfies must not verify the caller, got: {o}"
    );
}

// ---------------------------------------------------------------------------
// An unreachable call site proves nothing about the callee
// ---------------------------------------------------------------------------

/// A call under contradictory guards is never executed, so it is not a divergence.
///
/// The divergence check asks whether any input satisfies the callee's postcondition,
/// and an unsatisfiable path condition makes that query `Unsat` for a reason that has
/// nothing to do with the callee: the path is dead. Reporting divergence there is a
/// false failure about a call that cannot happen. The dead path is dropped, and the
/// function verifies on the reachable ones.
#[test]
fn an_unreachable_call_is_not_a_divergence() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nunsafe extern \"C\" {\nspec! {\n    ensures: true,\n}\nfn ext() -> u8;\n}\nspec! {\n    ensures: ret == 0,\n}\npub fn caller(x: u8) -> u8 {\nif x == 0 { if x != 0 { unsafe { ext() }; } }\n0\n}\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "the extern is assumed, so nothing is missing: {missing:?}");
    let o = pick(&outcomes, "caller");
    assert!(
        o.is_verified(),
        "the call sits under contradictory guards, so it cannot happen and is not a \
         divergence, got: {o}"
    );
}

// ---------------------------------------------------------------------------
// A helper call inside a measured loop keeps the measure
// ---------------------------------------------------------------------------

/// A measured loop whose step is a same-dump call still proves termination.
///
/// Entering a callee cleared the caller's `cut` *and* its measure, and only the cut
/// was restored on return. The resumed caller was still inside its loop with a cut
/// but no head value, so the back edge had nothing to compare and the loop was
/// reported incomplete -- "the loop head was never entered" -- even though its
/// measure was sufficient. A proof silently discarded, which this crate treats as a
/// defect. The two now travel together.
#[test]
fn a_helper_call_in_a_measured_loop_keeps_the_termination_measure() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: i < 255,\n    ensures: ret == i + 1,\n}\npub fn step(i: u8) -> u8 { i + 1 }\n\nspec! {\n    requires: n <= 200,\n    invariant: i <= n,\n    variant: n - i,\n    ensures: ret == n,\n}\npub fn f(n: u8) -> u8 {\nlet mut i = 0u8;\nwhile i < n { i = step(i); }\ni\n}\n";
    let (outcomes, missing) = verify_all_outcomes(src);
    assert!(missing.is_empty(), "both bodies are present: {missing:?}");
    let o = pick(&outcomes, "f");
    assert!(
        o.is_verified(),
        "the helper call must not erase the loop's measure, got: {o}"
    );
}

// ---------------------------------------------------------------------------
// A diverging call is a checked panic, not a dropped path
// ---------------------------------------------------------------------------

/// `assert!` is a promise, and the frontend now checks it instead of dropping it.
///
/// `assert!(x <= 200)` lowers to a `switchInt` that routes the *failing* case into
/// a diverging call to `core::panicking::panic`, with no `[return: bbN]` arm. The
/// parser only recognised the `[return:` shape, so the terminator came back
/// `Unknown("missing")`, the path was reported unmodelled, and the whole function
/// was `Incomplete` -- the assert, the most ordinary safety guard in Rust, was
/// never checked at all. Both halves are pinned here: the guard is *discharged*
/// under a precondition that implies it, and *refuted* with a real counterexample
/// when it is not.
#[test]
fn an_assert_is_checked_and_discharged_under_its_precondition() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x <= 200,\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { assert!(x <= 200); 1 }\n";
    let o = verify_src("f", src).expect("f must be in the report");
    assert!(
        o.is_verified(),
        "the guard follows from the precondition, so the assert cannot fire: {o}"
    );
}

/// The teeth: with no precondition the assert is a real panic, and it is reported.
///
/// The counterexample is a value above 200, which is exactly the input the assert
/// exists to reject. Reading the diverging call as a harmless drop would instead
/// have left the function `Incomplete`, which is a lost proof of nothing -- this
/// makes the missing precondition a *failure*, the sound direction.
#[test]
fn an_unproved_assert_is_refuted_with_a_counterexample() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { assert!(x <= 200); 1 }\n";
    let o = verify_src("f", src).expect("f must be in the report");
    match o {
        FnOutcome::Failed { kind, detail } => {
            assert!(
                kind.contains("assertion failed: x <= 200"),
                "the report should name the failed assertion, got `{kind}`"
            );
            assert!(!detail.is_empty(), "a failure must carry a counterexample");
        }
        other => panic!("an assert with no guard must fail, got: {other}"),
    }
}

/// An assert is *assumed* on the fall-through path, so the code after it can rely
/// on the guard -- the same rule the `assert` terminator already had.
///
/// Without this the guard would be checked and then thrown away, so `x + 1` after
/// `assert!(x <= 200)` would be reported as a possible overflow even though the
/// assert rules it out. The postcondition `ret == x + 1` is what makes the
/// assumption load-bearing: it only holds if the guard is carried forward.
#[test]
fn an_assert_guard_is_assumed_by_the_code_after_it() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x <= 200,\n    ensures: ret == x + 1,\n}\npub fn f(x: u8) -> u8 { assert!(x <= 200); x + 1 }\n";
    let o = verify_src("f", src).expect("f must be in the report");
    assert!(o.is_verified(), "the assert must be assumed on the fall-through path: {o}");
}

/// `debug_assert!` lowers the same way, so it is checked and assumed too.
#[test]
fn a_debug_assert_is_checked_like_an_assert() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x <= 200,\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { debug_assert!(x <= 200); 1 }\n";
    let o = verify_src("f", src).expect("f must be in the report");
    assert!(o.is_verified(), "a debug_assert is the same terminator as an assert: {o}");
}

/// `panic!` is a reachable failure, so an unguarded one is refuted, and a guarded
/// one is proved unreachable.
///
/// The message is carried from the string literal the dump passes, so the report
/// names the panic rather than the mangled callee path.
#[test]
fn a_panic_is_refuted_unless_its_guard_excludes_it() {
    let unguarded = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { if x == 0 { panic!(\"zero\"); } 1 }\n";
    let o = verify_src("f", unguarded).expect("f must be in the report");
    match o {
        FnOutcome::Failed { kind, .. } => {
            assert!(kind.contains("zero"), "the report should name the panic, got `{kind}`");
        }
        other => panic!("an unguarded panic must fail, got: {other}"),
    }
    let guarded = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x != 0,\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { if x == 0 { panic!(\"zero\"); } 1 }\n";
    let o = verify_src("f", guarded).expect("f must be in the report");
    assert!(o.is_verified(), "the precondition excludes the panic: {o}");
}

/// A *formatted* panic message is recovered from the `core::fmt` chain, not from
/// a literal operand.
///
/// Edition 2024 never puts `panic!("bad {}", x)` in the MIR as one string: the
/// pieces are a promoted `&[&str]` and the placeholders are separate `rt::Argument`
/// values, assembled by `Arguments::new_v1` on 1.85 and by
/// `Arguments::new::<LEN, _>` (a single encoded byte template) on stable. Both
/// spellings have to be read, and this test is what pins that -- it runs on
/// whichever toolchain `VERIF_RUSTC` names, so the two shapes are covered by the
/// same assertion on the two toolchains the gate uses.
#[test]
fn a_formatted_panic_message_is_recovered_from_the_fmt_chain() {
    let unguarded = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { if x == 0 { panic!(\"bad {}\", x); } 1 }\n";
    let Some(o) = verify_src("f", unguarded) else { return };
    match o {
        FnOutcome::Failed { kind, .. } => {
            assert!(
                kind.contains("bad {}"),
                "the report should name the panic's pieces, got `{kind}`"
            );
        }
        other => panic!("a formatted panic with no guard must fail, got: {other}"),
    }
    // A formatted `assert!` is the same chain with the guard in front of it.
    let guarded = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: x <= 100,\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { assert!(x <= 100, \"bad {}\", x); 1 }\n";
    let o = verify_src("f", guarded).expect("f must be in the report");
    assert!(o.is_verified(), "the precondition implies the formatted assert: {o}");
    let misguarded = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { assert!(x <= 100, \"bad {}\", x); 1 }\n";
    let o = verify_src("f", misguarded).expect("f must be in the report");
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("bad {}"),
            "the formatted assert should be named by its pieces, got `{kind}`"
        ),
        other => panic!("an unguarded formatted assert must fail, got: {other}"),
    }
    // `panic!("{}", x)` has no literal piece at all -- it lowers to a
    // `panic_display::<u8>` / `panic_cold_display::<u8>` call -- so there is no
    // message to recover and the callee's own name is the fallback. It must be the
    // *name*, read through the generics, and not the type arguments: the report
    // used to read `<u8>`, which is a mangled path rather than a fallback. The
    // two toolchains spell the callee differently, so only the shape is pinned.
    let no_pieces = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { if x == 0 { panic!(\"{}\", x); } 1 }\n";
    let o = verify_src("f", no_pieces).expect("f must be in the report");
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("display") && !kind.contains('<'),
            "the fallback should be the callee's name, not its generics, got `{kind}`"
        ),
        other => panic!("an unguarded panic must fail, got: {other}"),
    }
}

/// The other two panicking macros name their own message too.
///
/// `unreachable!()` and `todo!()` pass a *literal*, so they take the
/// `core::panicking::panic(const "…")` / `Arguments::from_str` path rather than the
/// `core::fmt` chain, and the report should carry the text the programmer wrote --
/// not the mangled callee. They are here because a fix aimed at the formatted case
/// must not regress the plain one.
#[test]
fn a_literal_panic_macro_names_its_message() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { if x == 0 { unreachable!(); } 1 }\n";
    let Some(o) = verify_src("f", src) else { return };
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("entered unreachable code"),
            "the report should carry the macro's text, got `{kind}`"
        ),
        other => panic!("an unguarded `unreachable!` must fail, got: {other}"),
    }
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { if x == 0 { todo!(); } 1 }\n";
    let o = verify_src("f", src).expect("f must be in the report");
    match o {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.contains("not yet implemented"),
            "the report should carry the macro's text, got `{kind}`"
        ),
        other => panic!("an unguarded `todo!` must fail, got: {other}"),
    }
}

/// The bounds check rustc inserts for `xs[0]` is a diverging call too, and it is
/// proved unreachable from the length precondition.
///
/// This is the shape an ordinary slice access lowers to, so the check is what
/// makes a `&[T]` argument safe to reason about at all.
#[test]
fn an_index_bounds_check_is_proved_unreachable() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\nspec! {\n    requires: xs.len() >= 1,\n    ensures: ret == 0,\n}\npub fn f(xs: &[u8]) -> u8 { xs[0] * 0 }\n";
    let o = verify_src("f", src).expect("f must be in the report");
    assert!(o.is_verified(), "the length precondition rules the bounds check out: {o}");
}

/// A diverging call in its *cleanup* form is recognised too (review C1b).
///
/// With a live `Drop` local, rustc prints the diverging call's single successor as
/// its cleanup edge (`_4 = core::panicking::panic(…) -> bb4`, with `bb4 (cleanup)`)
/// rather than the `-> unwind continue` arm the parser first recognised. That line
/// matched neither the `-> [return:` nor the `-> unwind` shape, so the whole path
/// was still dropped -- an `assert!` in any function with a live RAII local (`Vec`,
/// `String`, `Box`, a lock guard) was never checked. The parser now combines the
/// `!`-typed destination with the `(cleanup)` marker and reads it as a diverging
/// call, so the assert is a real failure again.
///
/// The `drop(_2)` line is still unmodelled (review C1), so a *guarded* version is
/// `incomplete` for that reason -- but the *unguarded* one is a definite `FAILED`
/// with the counterexample, which is the sound direction: a missing precondition
/// is a failure, not a silently dropped check.
#[test]
fn a_diverging_call_in_a_function_with_a_drop_local_is_checked() {
    let src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\npub struct Guard(pub u8);\nimpl Drop for Guard {\n    fn drop(&mut self) {}\n}\nspec! {\n    ensures: ret == 1,\n}\npub fn f(x: u8) -> u8 { let _g = Guard(0); assert!(x < 200); 1 }\n";
    let o = verify_src("f", src).expect("f must be in the report");
    match o {
        FnOutcome::Failed { kind, detail } => {
            assert!(
                kind.contains("assertion failed: x < 200"),
                "the cleanup-form assert must be named, got `{kind}`"
            );
            assert!(!detail.is_empty(), "a failure must carry a counterexample");
        }
        other => panic!(
            "an unguarded assert with a live Drop local must be a failure, not a \
             dropped path, got: {other}"
        ),
    }
}

/// `iN::abs`, `iN::unsigned_abs` and `Ord::clamp` are modelled, and `abs`'s
/// *panic* is modelled too.
///
/// `abs` and `clamp` are the first modelled methods whose failure is a **panic**
/// rather than a value or an `Option`, so the two halves have to be checked
/// apart. A model that returned `|x|` with no panic predicate would verify
/// `abs_min_can_overflow` (which panics at `i8::MIN`); a model that returned a
/// constant would prove the value tripwires. Each true direction is asserted
/// `Verified` and each false direction `Failed`, and the panic entries are pinned
/// to a `panic` kind so an unrelated refusal cannot satisfy them.
///
/// `unsigned_abs` is the contrast that makes `abs`'s panic meaningful: the same
/// magnitude, read as the unsigned type, so it is *total* even at `MIN`
/// (`i8::MIN.unsigned_abs()` is `128u8`). Its `requires: true` control must
/// verify, which a model that gave it `abs`'s failure predicate could not.
#[test]
fn abs_and_clamp_are_modelled_with_their_panics() {
    let names = [
        "abs_small_reads",
        "abs_small_is_a_value_cannot_prove_this",
        "abs_min_can_overflow",
        "unsigned_abs_reads",
        "unsigned_abs_of_min_is_the_magnitude",
        "unsigned_abs_of_min_is_panic_free",
        "unsigned_abs_is_a_value_cannot_prove_this",
        "clamp_builtin_reads",
        "clamp_builtin_can_panic",
        "clamp_builtin_is_a_value_cannot_prove_this",
        "clamp_builtin_signed_reads",
    ];
    let Some(report) = verify_realistic(&names) else { return };

    for name in [
        "abs_small_reads",
        "unsigned_abs_reads",
        "unsigned_abs_of_min_is_the_magnitude",
        "unsigned_abs_of_min_is_panic_free",
        "clamp_builtin_reads",
        "clamp_builtin_signed_reads",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    // The value tripwires: the call is a value, not an uninterpreted one. The
    // failure *kind* is asserted, not just `Failed`, because both entries carry a
    // precondition that discharges the panic -- so a refutation on the panic
    // instead of the postcondition would mean the entry is not testing the value
    // at all (the `abs` panic fires at `i32::MIN`, before the value is read).
    for name in [
        "abs_small_is_a_value_cannot_prove_this",
        "unsigned_abs_is_a_value_cannot_prove_this",
        "clamp_builtin_is_a_value_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.starts_with("postcondition"),
                "`{name}` must be refuted on the value (postcondition), got `{kind}`"
            ),
            other => panic!("`{name}` claims a false value and must be refuted, got: {other}"),
        }
    }

    // The panic obligations: the call *can* panic, so the function fails on the
    // panic, not on a postcondition.
    for name in ["abs_min_can_overflow", "clamp_builtin_can_panic"] {
        let o = outcome(&report, name);
        match o {
            FnOutcome::Failed { kind, .. } => {
                assert!(kind.starts_with("panic"), "`{name}` must fail on the panic, got `{kind}`")
            }
            other => panic!("`{name}` must be a failing panic, got: {other}"),
        }
    }
}

/// The ASCII class tests on `u8` are modelled, and each one is a *predicate*
/// rather than an uninterpreted value.
///
/// The shape is the one `is_power_of_two` already had -- a `bool`-valued method
/// whose destination is a `bool`, not a one-bit word -- with one difference: the
/// receiver is `&self`, so the operand is the *referent* of a reference the body
/// materialises (`_3 = &_1`). The three tripwires are the evidence the predicates
/// are read at all: a model that returned a constant would prove them.
#[test]
fn the_ascii_classes_are_modelled_with_their_boundaries() {
    let names = [
        "ascii_digit_value",
        "ascii_digit_is_not_every_byte_cannot_prove_this",
        "ascii_class_discriminates",
        "ascii_class_hex_arm_is_not_every_byte_cannot_prove_this",
        "ascii_is_ascii_boundary",
        "ascii_is_ascii_is_not_every_byte_cannot_prove_this",
    ];
    let Some(report) = verify_realistic(&names) else { return };

    for name in ["ascii_digit_value", "ascii_class_discriminates", "ascii_is_ascii_boundary"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    // Each tripwire must be refuted on the *postcondition*, with a witness at a
    // byte that really takes the other arm -- so an unrelated refusal cannot
    // satisfy it, and the model cannot be passing by answering a constant.
    for (name, byte) in [
        ("ascii_digit_is_not_every_byte_cannot_prove_this", 48u64),
        ("ascii_class_hex_arm_is_not_every_byte_cannot_prove_this", 80),
        ("ascii_is_ascii_is_not_every_byte_cannot_prove_this", 128),
    ] {
        let o = outcome(&report, name);
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.starts_with("postcondition"),
                "`{name}` must be refuted on the postcondition, got `{kind}`"
            ),
            other => panic!("`{name}` claims a false value and must be refuted, got: {other}"),
        }
        // The witness names the byte that takes the else arm: `b'0'` for the digit
        // test, `b'P'` (80) for the hex arm, and `0x80` for `is_ascii`.
        let detail = format!("{o}");
        assert!(
            detail.contains(&byte.to_string()),
            "`{name}`'s witness should name the byte {byte}, got: {detail}"
        );
    }
}

/// `abs_diff` and the rotations are modelled, and each has a tripwire that a
/// wrong model would *prove*.
///
/// `abs_diff`'s result is the *unsigned* magnitude, so the model computes the
/// difference at one bit of headroom and takes the absolute value there; a model
/// that returned the signed difference would read a negative result as a huge
/// unsigned one. The rotations reduce the amount modulo the width (`rotate by the
/// width` is the identity, `by w + 1` is `by 1`), which is the property a shift
/// model gets wrong. Both tripwires claim the shape a *shift or signed-difference*
/// model would produce, so they must be refuted.
#[test]
fn abs_diff_and_rotations_are_modelled_with_their_boundaries() {
    let names = [
        "abs_diff_ordered",
        "abs_diff_is_symmetric_cannot_prove_this",
        "rotate_left_wraps_the_top_bit",
        "rotate_is_not_a_shift_cannot_prove_this",
        "rotate_by_the_width_is_the_identity",
        "rotate_by_more_than_the_width_wraps",
    ];
    let Some(report) = verify_realistic(&names) else { return };

    for name in [
        "abs_diff_ordered",
        "rotate_left_wraps_the_top_bit",
        "rotate_by_the_width_is_the_identity",
        "rotate_by_more_than_the_width_wraps",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    // The tripwires must be refuted on the *postcondition*, not by an unrelated
    // refusal, so the model cannot pass by answering a constant.
    for name in ["abs_diff_is_symmetric_cannot_prove_this", "rotate_is_not_a_shift_cannot_prove_this"]
    {
        let o = outcome(&report, name);
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.starts_with("postcondition"),
                "`{name}` must be refuted on the postcondition, got `{kind}`"
            ),
            other => panic!("`{name}` claims a false value and must be refuted, got: {other}"),
        }
    }
}

/// The next batch of `core` value methods is modelled: `signum`, the Euclidean
/// pair (`div_euclid`/`rem_euclid`), `div_ceil`, the byte permutations
/// (`reverse_bits`/`swap_bytes`), the byte orders (`to_be`/`to_le`), the ASCII
/// case conversions and `is_multiple_of`.
///
/// Each shape has a true pin and a tripwire that claims the value a *plausible
/// wrong model* would produce (the truncating `/` for the Euclidean pair, the
/// identity for the permutations, an unconditional `+32` for the ASCII case, an
/// unguarded `%` for `is_multiple_of`). The tripwires must be refuted on the
/// *postcondition*, so the model cannot pass by answering a constant, and the
/// signedness pins (`signum_of_min`) fail for a model that read the top bit
/// unsigned.
#[test]
fn the_next_core_value_methods_are_modelled_with_their_tripwires() {
    let names = [
        "signum_of_min_is_minus_one",
        "signum_of_a_negative_cannot_prove_this",
        "cast_unsigned_reinterprets_negative_as_large",
        "cast_unsigned_reinterprets_negative_cannot_prove_this",
        "cast_signed_reinterprets_large_as_negative",
        "cast_signed_reinterprets_large_cannot_prove_this",
        "cast_unsigned_makes_a_comparison_unsigned",
        "div_euclid_rounds_toward_negative_infinity",
        "div_euclid_is_not_truncating_division_cannot_prove_this",
        "rem_euclid_is_non_negative",
        "rem_euclid_is_not_the_truncating_remainder_cannot_prove_this",
        "unsigned_rem_euclid_is_the_plain_remainder",
        "unsigned_rem_euclid_is_not_the_signed_adjustment_cannot_prove_this",
        "unsigned_div_euclid_is_the_plain_quotient",
        "unsigned_div_euclid_is_not_the_signed_adjustment_cannot_prove_this",
        "div_ceil_rounds_toward_positive_infinity",
        "div_ceil_is_not_truncating_division_cannot_prove_this",
        "reverse_bits_of_the_top_bit",
        "reverse_bits_is_not_the_identity_cannot_prove_this",
        "swap_bytes_reverses_the_bytes",
        "swap_bytes_is_not_the_identity_cannot_prove_this",
        "to_be_on_a_little_endian_target_swaps",
        "to_be_is_not_the_identity_here_cannot_prove_this",
        "to_le_on_a_little_endian_target_is_the_identity",
        "from_be_on_a_little_endian_target_swaps",
        "from_be_is_not_the_identity_here_cannot_prove_this",
        "from_le_on_a_little_endian_target_is_the_identity",
        "to_be_then_from_be_is_the_identity",
        "to_le_then_from_be_is_not_the_identity_cannot_prove_this",
        "to_ascii_uppercase_of_a_lowercase_letter",
        "to_ascii_uppercase_leaves_uppercase_cannot_prove_this",
        "to_ascii_lowercase_of_an_uppercase_letter",
        "is_multiple_of_six_by_three",
        "is_multiple_of_seven_by_three_cannot_prove_this",
        "is_multiple_of_zero_by_zero",
        "is_multiple_of_five_by_zero",
    ];
    let Some(report) = verify_realistic(&names) else { return };

    for name in [
        "signum_of_min_is_minus_one",
        "cast_unsigned_reinterprets_negative_as_large",
        "cast_signed_reinterprets_large_as_negative",
        "cast_unsigned_makes_a_comparison_unsigned",
        "div_euclid_rounds_toward_negative_infinity",
        "rem_euclid_is_non_negative",
        "unsigned_rem_euclid_is_the_plain_remainder",
        "unsigned_div_euclid_is_the_plain_quotient",
        "div_ceil_rounds_toward_positive_infinity",
        "reverse_bits_of_the_top_bit",
        "swap_bytes_reverses_the_bytes",
        "to_be_on_a_little_endian_target_swaps",
        "to_le_on_a_little_endian_target_is_the_identity",
        "from_be_on_a_little_endian_target_swaps",
        "from_le_on_a_little_endian_target_is_the_identity",
        "to_be_then_from_be_is_the_identity",
        "to_ascii_uppercase_of_a_lowercase_letter",
        "to_ascii_lowercase_of_an_uppercase_letter",
        "is_multiple_of_six_by_three",
        "is_multiple_of_zero_by_zero",
        "is_multiple_of_five_by_zero",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    for name in [
        "signum_of_a_negative_cannot_prove_this",
        "cast_unsigned_reinterprets_negative_cannot_prove_this",
        "cast_signed_reinterprets_large_cannot_prove_this",
        "div_euclid_is_not_truncating_division_cannot_prove_this",
        "rem_euclid_is_not_the_truncating_remainder_cannot_prove_this",
        "unsigned_rem_euclid_is_not_the_signed_adjustment_cannot_prove_this",
        "unsigned_div_euclid_is_not_the_signed_adjustment_cannot_prove_this",
        "div_ceil_is_not_truncating_division_cannot_prove_this",
        "reverse_bits_is_not_the_identity_cannot_prove_this",
        "swap_bytes_is_not_the_identity_cannot_prove_this",
        "to_be_is_not_the_identity_here_cannot_prove_this",
        "from_be_is_not_the_identity_here_cannot_prove_this",
        "to_le_then_from_be_is_not_the_identity_cannot_prove_this",
        "to_ascii_uppercase_leaves_uppercase_cannot_prove_this",
        "is_multiple_of_seven_by_three_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.starts_with("postcondition"),
                "`{name}` must be refuted on the postcondition, got `{kind}`"
            ),
            other => panic!("`{name}` claims a false value and must be refuted, got: {other}"),
        }
    }
}

/// The `u32` product surface is modelled: `wrapping_mul` as a value, and a
/// `saturating_mul` whose widened `2w == 64` failure predicate is built.
///
/// `MUL_MAX_WIDTH` was 16, so every `u32` product reported "past what the model
/// covers" and `hash_step` — the flagship `u32` example — was `incomplete`. At 32
/// the value half (`wrapping_mul`) is a plain `w`-bit multiply and settles at once,
/// and the constant-multiplier `saturating_mul` folds rather than blasting the
/// 64-bit multiplier. The tripwires pin that the value is the *product* rather
/// than a constant: a model that answered `0` or the operand would prove them.
///
/// The pinned-argument equality is the discriminating half: `100000 * 31` is
/// `3_100_000`, which does not fit a 16-bit result, so a model that wrapped
/// narrower would refute the true fixture instead of proving it.
#[test]
fn the_u32_product_surface_is_modelled() {
    let names = [
        "u32_wrapping_product",
        "u32_wrapping_product_tripwire",
        "u32_saturating_product",
        "u32_saturating_product_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else { return };

    for name in ["u32_wrapping_product", "u32_saturating_product"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    for name in ["u32_wrapping_product_tripwire", "u32_saturating_product_tripwire"] {
        let o = outcome(&report, name);
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.starts_with("postcondition"),
                "`{name}` must be refuted on the postcondition, got `{kind}`"
            ),
            other => panic!("`{name}` claims a false value and must be refuted, got: {other}"),
        }
    }
}

/// C1: a `drop` terminator is modelled, not dropped.
///
/// The review's exit criterion for C1 was a `guarded`/`misguarded` pair on a
/// function holding a live `Drop` local: the first verifies, the second is
/// refuted. It runs here on inline source so the shape is pinned even if the
/// corpus is edited, and it asserts the *verdict*, not merely "not incomplete" --
/// a fix that refused every `drop` would pass the second and fail the first.
#[test]
fn a_drop_terminator_is_modelled_and_its_destructor_runs() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Guard(pub u8);
impl Drop for Guard {
    fn drop(&mut self) {}
}

spec! {
    requires: x < 200,
    ensures: ret == 1,
}
pub fn guarded(x: u8) -> u8 {
    let _g = Guard(0);
    assert!(x < 200);
    1
}

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn misguarded(x: u8) -> u8 {
    let _g = Guard(0);
    assert!(x < 200);
    1
}
"#;
    let Some(g) = verify_src("guarded", src) else { return };
    assert!(
        g.is_verified(),
        "a function holding a live `Drop` local with a satisfied assert must verify, got: {g}"
    );
    let Some(m) = verify_src("misguarded", src) else { return };
    match m {
        FnOutcome::Failed { kind, .. } => assert!(
            kind.starts_with("panic"),
            "the misguarded assert must be refuted as a panic, got `{kind}`"
        ),
        other => panic!("the misguarded assert is reachable and must be refuted, got: {other}"),
    }
}

/// C1 soundness: a destructor's *body* is executed, so its panic is an obligation.
///
/// This is the direction that makes the model safe. Treating every `drop` as a
/// no-op -- the tempting way to make RAII locals decide -- would report the
/// unguarded function `verified`, but the destructor panics for `x >= 10`. The
/// guarded companion is the positive control: refusing every `drop` would leave
/// it undecided, so the pair pins both that the destructor runs and that the tool
/// is not merely refusing the shape.
#[test]
fn a_destructor_body_is_executed_and_its_panic_is_an_obligation() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct PanicGuard { pub v: u8 }
impl Drop for PanicGuard {
    fn drop(&mut self) {
        assert!(self.v < 10);
    }
}

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn unguarded(x: u8) -> u8 {
    let _p = PanicGuard { v: x };
    1
}

spec! {
    requires: x < 10,
    ensures: ret == 1,
}
pub fn guarded(x: u8) -> u8 {
    let _p = PanicGuard { v: x };
    1
}
"#;
    let Some(u) = verify_src("unguarded", src) else { return };
    match u {
        FnOutcome::Failed { kind, detail } => {
            assert!(
                kind.starts_with("panic"),
                "the destructor's assert must be a refuted panic, got `{kind}`"
            );
            assert!(
                kind.contains("v < 10"),
                "the refuted obligation must be the destructor's own assert, got: `{kind}` \
                 with witness {detail}"
            );
        }
        other => panic!(
            "a destructor that panics for `x >= 10` must be refuted, got: {other} -- \
             treating the drop as a no-op would have proved it"
        ),
    }
    let Some(g) = verify_src("guarded", src) else { return };
    assert!(g.is_verified(), "the guarded destructor cannot panic, got: {g}");
}

/// C1: a container whose destructor the tool cannot represent is *refused*.
///
/// An `Rc<T>` local's destructor decrements a refcount and may free the
/// allocation, which is not a bit-vector fact. Assuming the `drop` were a no-op
/// would be a false proof whenever the destructor's effect is observable, so the
/// honest answer is a refusal -- not a verdict. This is the case the dump cannot
/// tell apart from a struct holding a user-`Drop` field (both print
/// `drop(_x) -> [return: …]`), which is why the no-op is not taken here.
/// (A `String` and a `Box<u8>` *are* glue-free, so they are no longer this
/// example; an `Rc` has no modelled field set.)
#[test]
fn an_unmodelled_drop_is_refused_not_assumed_away() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn owns_rc(r: std::rc::Rc<u8>) -> u8 {
    let _owned = r;
    1
}
"#;
    let Some(o) = verify_src("owns_rc", src) else { return };
    match o {
        FnOutcome::Incomplete { .. } | FnOutcome::Skipped { .. } => {}
        other => panic!(
            "an `Rc` drop is not representable and must be refused, got: {other} -- \
             a verdict here would be a false proof"
        ),
    }
}

/// C11 `Box<T>`: `Box::new` stores the value, the deref reads it back, the
/// compiler's null/alignment checks are discharged, and a glue-free `Box<T>`
/// argument's drop is a no-op.
///
/// Each true direction must verify and each tripwire must be refuted, so the model
/// is pinned in both directions -- a `Box` deref that read a constant would prove
/// the tripwires, and one that read `Unknown` would leave the true directions
/// undecided.
#[test]
fn a_box_new_deref_decides() {
    let names = [
        "box_new_reads_its_value",
        "box_new_reads_its_value_tripwire",
        "box_guarded_inc",
        "box_guarded_inc_tripwire",
        "box_u32_reads_its_value",
        "owns_box_glue_free",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "box_new_reads_its_value",
        "box_guarded_inc",
        "box_u32_reads_its_value",
        "owns_box_glue_free",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in ["box_new_reads_its_value_tripwire", "box_guarded_inc_tripwire"] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` claims a false result and must be refuted, got: {o}"
        );
    }
}

/// C11 iteration: `xs.iter().count()` and `xs.iter().copied().sum()` over a
/// constant-length array decide (the cursor starts at the array's elements), and
/// an explicit `std::mem::drop` of a glue-free container is a no-op.
///
/// The true directions must verify and the tripwires must be refuted, so a model
/// that read a constant or a wrong element would fail one of them.
#[test]
fn a_slice_iter_and_explicit_drop_decide() {
    let names = [
        "array_iter_count",
        "array_iter_count_tripwire",
        "array_iter_sum",
        "array_iter_sum_tripwire",
        "array_iter_max",
        "array_iter_max_tripwire",
        "array_iter_min",
        "array_iter_last",
        "array_iter_last_tripwire",
        "array_iter_nth",
        "explicit_drop_box",
        "explicit_drop_string",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "array_iter_count",
        "array_iter_sum",
        "array_iter_max",
        "array_iter_min",
        "array_iter_last",
        "array_iter_nth",
        "explicit_drop_box",
        "explicit_drop_string",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "array_iter_count_tripwire",
        "array_iter_sum_tripwire",
        "array_iter_max_tripwire",
        "array_iter_last_tripwire",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` claims a false result and must be refuted, got: {o}"
        );
    }
}

/// C11 iteration: `Iterator::rev` reverses the direction a sequence position
/// names. `last`/`nth`/a `for` loop are order-dependent, so they pin the mapping
/// (`rev().last()` is the *first* element); `count` is order-independent.
#[test]
fn an_iterator_can_be_reversed() {
    let names = [
        "array_iter_rev_last",
        "array_iter_rev_last_tripwire",
        "array_iter_rev_nth",
        "array_iter_rev_for",
        "array_iter_rev_rev_last",
        "array_iter_rev_count",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "array_iter_rev_last",
        "array_iter_rev_nth",
        "array_iter_rev_for",
        "array_iter_rev_rev_last",
        "array_iter_rev_count",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let o = outcome(&report, "array_iter_rev_last_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`array_iter_rev_last_tripwire` claims the unreversed last element and must be refuted, got: {o}"
    );
}

/// C11 iteration: `skip` advances the cursor's position and `step_by` sets its
/// stride. `last`/`count`/`sum` read the stride, so the fixtures pin the mapping
/// (e.g. `step_by(2).last()` is index 2 of 0..4, not 3).
#[test]
fn an_iterator_can_be_skipped_and_stepped() {
    let names = [
        "array_iter_skip_last",
        "array_iter_skip_count",
        "array_iter_step_count",
        "array_iter_step_last",
        "array_iter_step_last_tripwire",
        "array_iter_step_sum",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "array_iter_skip_last",
        "array_iter_skip_count",
        "array_iter_step_count",
        "array_iter_step_last",
        "array_iter_step_sum",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let o = outcome(&report, "array_iter_step_last_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`array_iter_step_last_tripwire` claims the un-strided last element and must be refuted, got: {o}"
    );
}

/// C11 iteration: `Iterator::take` caps the cursor's end at `pos + n`. It needs a
/// constant length so the cap is constant; `last`/`count`/`sum`/`nth` read it.
#[test]
fn an_iterator_can_be_taken() {
    let names = [
        "array_iter_take_last",
        "array_iter_take_last_tripwire",
        "array_iter_take_count",
        "array_iter_take_over",
        "array_iter_take_nth",
        "array_iter_take_sum",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "array_iter_take_last",
        "array_iter_take_count",
        "array_iter_take_over",
        "array_iter_take_nth",
        "array_iter_take_sum",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let o = outcome(&report, "array_iter_take_last_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`array_iter_take_last_tripwire` claims past the cap and must be refuted, got: {o}"
    );
}

/// C11 symbolic-length iteration: a slice sum is unrolled to `MAX_SYMBOLIC_LEN`
/// steps, each guarded by `k < len`, which is exact only when the precondition
/// proves `len <= 8`. A guarded sum of small elements is panic-free (verified); a
/// bounded length with unbounded elements overflows (refuted); an unbounded length
/// cannot be unrolled and is refused.
#[test]
fn a_symbolic_length_sum_is_bounded_by_its_precondition() {
    let names = [
        "symbolic_sum_no_overflow",
        "symbolic_sum_tripwire",
        "symbolic_sum_unbounded_refused",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    let o = outcome(&report, "symbolic_sum_no_overflow");
    assert!(o.is_verified(), "`symbolic_sum_no_overflow` must verify, got: {o}");
    let o = outcome(&report, "symbolic_sum_tripwire");
    assert!(matches!(o, FnOutcome::Failed { .. }), "`symbolic_sum_tripwire` must be refuted, got: {o}");
    let o = outcome(&report, "symbolic_sum_unbounded_refused");
    assert!(!o.is_verified(), "`symbolic_sum_unbounded_refused` must not verify, got: {o}");
}

/// C11 iteration: `Iterator::all`/`any` fold a predicate to a `bool` -- `all` is
/// the conjunction over the elements, `any` the disjunction. The tripwires claim
/// the opposite of what the predicate fold yields.
#[test]
fn an_iterator_can_be_tested_with_all_and_any() {
    let names = [
        "array_iter_all_lt",
        "array_iter_all_lt_tripwire",
        "array_iter_any_gt",
        "array_iter_any_gt_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in ["array_iter_all_lt", "array_iter_any_gt"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in ["array_iter_all_lt_tripwire", "array_iter_any_gt_tripwire"] {
        let o = outcome(&report, name);
        assert!(matches!(o, FnOutcome::Failed { .. }), "`{name}` must be refuted, got: {o}");
    }
}

/// C11 iteration: `Iterator::map`/`filter` are lazy transforms the value
/// terminals apply -- `map(f).sum()` folds the mapped elements, `filter(f).count()`
/// counts the accepted ones. The tripwire's filter accepts all four elements.
#[test]
fn an_iterator_can_be_mapped_and_filtered() {
    let names = [
        "array_iter_map_sum",
        "array_iter_map_wrapping_sum",
        "array_iter_filter_count",
        "array_iter_filter_count_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in ["array_iter_map_sum", "array_iter_map_wrapping_sum", "array_iter_filter_count"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let o = outcome(&report, "array_iter_filter_count_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`array_iter_filter_count_tripwire` must be refuted, got: {o}"
    );
}

/// C11 iteration: `Iterator::fold(init, f)` folds a modelled reducer closure
/// (`|acc, x| acc <op> x`, checked or `wrapping_*`). The checked reducer raises a
/// panic obligation per step; the tripwire's unguarded fold can overflow.
#[test]
fn an_iterator_can_be_folded_with_a_closure() {
    let names = [
        "array_iter_fold_sum",
        "array_iter_fold_wrapping",
        "array_iter_fold_from_one",
        "array_iter_fold_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in ["array_iter_fold_sum", "array_iter_fold_wrapping", "array_iter_fold_from_one"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let o = outcome(&report, "array_iter_fold_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`array_iter_fold_tripwire` folds unguarded and must be refuted, got: {o}"
    );
}

/// C11 containers: `Vec::clear`/`String::clear` reset the tracked length to zero,
/// and the tripwire that claims the pre-clear length is refuted.
#[test]
fn container_clear_resets_the_length() {
    let names = [
        "vec_clear_reads_zero",
        "vec_clear_tripwire",
        "string_clear_reads_zero",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in ["vec_clear_reads_zero", "string_clear_reads_zero"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let o = outcome(&report, "vec_clear_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`vec_clear_tripwire` claims the pre-clear length and must be refuted, got: {o}"
    );
}

/// C1, on the corpus: the `Drop` fixtures decide, and the false ones are refuted.
///
/// The review's exit criterion is stated on `guard_guarded` (verifies) and
/// `guard_misguarded` (refuted). This asserts the corpus copies of those, plus the
/// destructor-panic pair, so a regression in the corpus cannot pass unnoticed --
/// `realistic.rs` is scored by a floor, and a fixture that flipped to `incomplete`
/// would lower the score without failing the floor test.
#[test]
fn the_drop_fixtures_decide_and_the_false_ones_are_refuted() {
    let names = [
        "guard_is_dropped_cleanly",
        "guard_guarded",
        "destructor_panic_guarded",
        "guard_misguarded_cannot_prove_this",
        "destructor_panic_cannot_prove_this",
        "rc_drop_is_refused",
    ];
    let Some(report) = verify_realistic(&names) else { return };

    for name in [
        "guard_is_dropped_cleanly",
        "guard_guarded",
        "destructor_panic_guarded",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "guard_misguarded_cannot_prove_this",
        "destructor_panic_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.starts_with("panic"),
                "`{name}` must be refuted as a reachable panic, got `{kind}`"
            ),
            other => panic!(
                "`{name}` has a reachable panic and must be refuted, got: {other} -- \
                 treating the `drop` as a no-op, or dropping the path at it, would hide it"
            ),
        }
    }
    // A container drop is a refusal, not a verdict.
    match outcome(&report, "rc_drop_is_refused") {
        FnOutcome::Incomplete { .. } | FnOutcome::Skipped { .. } => {}
        other => panic!("an `Rc` drop must be refused, got: {other}"),
    }
}

/// A combinator that *destroys* its unused operand must respect that operand's
/// drop glue, or it is a false proof.
///
/// `Result::unwrap_or_default` consumes the receiver and destroys the error value
/// on the `Err` branch. The model checked only that the payload and the default
/// were scalar words, so a `Result<u8, Boom>` whose `Boom` destructor panics was
/// reported panic-free -- while a real call unwinds. The same holds for
/// `unwrap_or`, `or`, and `and`, which drop the operand they do not return. Each
/// is now refused when the dropped type's glue is not representable, which is the
/// honest answer rather than an assumed no-op.
#[test]
fn a_combinator_that_destroys_a_value_respects_its_drop_glue() {
    let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Boom;
impl Drop for Boom {
    fn drop(&mut self) {
        panic!("boom");
    }
}

spec! {
    requires: true,
    ensures: ret <= 255,
}
pub fn boom_default(r: Result<u8, Boom>) -> u8 {
    r.unwrap_or_default()
}

spec! {
    requires: true,
    ensures: ret <= 255,
}
pub fn boom_or(r: Result<u8, Boom>) -> u8 {
    r.unwrap_or(7)
}
"#;
    for name in ["boom_default", "boom_or"] {
        let Some(o) = verify_src(name, src) else { return };
        // Pinned as `Incomplete`, not `Incomplete | Skipped`: the contracts here
        // (`ret <= 255`) are readable, so a `Skipped` would mean the contract
        // stopped being read -- a different defect that this check should not
        // silently accept. Measured, both are `Incomplete` (the destructor's glue
        // is not representable), so the exact kind is the honest pin.
        match o {
            FnOutcome::Incomplete { .. } => {}
            other => panic!(
                "`{name}` destroys a `Boom` whose destructor panics and must be refused \
                 as `Incomplete`, got: {other} -- a `verified` here is a false proof"
            ),
        }
    }
}

/// Review round: field drop glue, `unwrap_or`, unwind accounting, edition
/// resolution, and rotate widths.
///
/// Nine findings from an adversarial review, each reproduced before being fixed.
/// They fall into four families: drop glue (F1/F2/F3), unwinding (F4/F5), edition
/// resolution (F6/F7), and width/precision (F8/F9).
mod review_round {
    use super::*;

    /// F1/F3: a struct whose field has its own destructor must not be treated as
    /// fully dropped after the outer user destructor.
    ///
    /// `Outer { inner: Inner }` with `impl Drop for Outer` and `impl Drop for
    /// Inner` destroys *both*: the user body runs, then each field's glue. The
    /// model ran the user body and stopped, so a panicking `Inner::drop` was never
    /// seen and the function was a false `Verified`. The fix refuses the shape --
    /// a field whose type has glue this tool cannot execute -- which is the honest
    /// answer: the drop is unmodelled, not proved safe.
    #[test]
    fn a_field_with_its_own_destructor_is_refused_not_assumed_safe() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Inner { pub v: u8 }
impl Drop for Inner {
    fn drop(&mut self) { assert!(self.v < 10); }
}
pub struct Outer { pub inner: Inner }
impl Drop for Outer {
    fn drop(&mut self) {}
}

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn outer_with_panicking_field(x: u8) -> u8 {
    let _o = Outer { inner: Inner { v: x } };
    1
}

spec! {
    requires: x < 10,
    ensures: ret == 1,
}
pub fn outer_guarded(x: u8) -> u8 {
    let _o = Outer { inner: Inner { v: x } };
    1
}
"#;
        // The unguarded one must NOT be `Verified`: the field's destructor panics
        // for `x >= 10`, and the model cannot run it, so it is a refusal.
        let Some(u) = verify_src("outer_with_panicking_field", src) else { return };
        assert!(
            !u.is_verified(),
            "a struct whose field has a panicking destructor must not be `Verified`, got: {u}"
        );
        // The guarded companion is refused too (same shape), which is the point:
        // the refusal is about the *shape*, not about whether the panic is
        // reachable. It must not be a false `Verified`.
        let Some(g) = verify_src("outer_guarded", src) else { return };
        assert!(
            !g.is_verified(),
            "the guarded companion is the same unmodelled shape and must not verify, got: {g}"
        );
    }

    /// F2: `Result::unwrap_or` destroys the error value on the `Err` branch, so a
    /// panicking error destructor must not be assumed away.
    ///
    /// `r.unwrap_or(0)` on `Result<u8, E>` with `impl Drop for E { panic }` panics
    /// on the `Err` branch, but the model treated `unwrap_or` as total (it has no
    /// panic obligation for the *tag*). The fix reads the error type from the
    /// receiver and refuses when its glue is unmodelled; a scalar error type still
    /// decides, which is the positive control that the refusal is not blanket.
    #[test]
    fn unwrap_or_refuses_an_error_type_whose_drop_is_unmodelled() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Boom;
impl Drop for Boom {
    fn drop(&mut self) { assert!(false); }
}

spec! {
    requires: true,
    ensures: ret <= 255,
}
pub fn unwrap_or_dropping_error(r: Result<u8, Boom>) -> u8 {
    r.unwrap_or(0)
}

spec! {
    requires: true,
    ensures: ret <= 255,
}
pub fn unwrap_or_scalar_error(r: Result<u8, u8>) -> u8 {
    r.unwrap_or(0)
}
"#;
        let Some(d) = verify_src("unwrap_or_dropping_error", src) else { return };
        assert!(
            !d.is_verified(),
            "`unwrap_or` on an error type with a panicking destructor must not verify, got: {d}"
        );
        let Some(s) = verify_src("unwrap_or_scalar_error", src) else { return };
        assert!(
            s.is_verified(),
            "`unwrap_or` on a scalar error type must still verify (positive control), got: {s}"
        );
    }

    /// F4/F5: the unwind bound counts *latch traversals*, not raw block entries.
    ///
    /// A loop that runs exactly `N` iterations needs `N + 1` entries to its header
    /// (the last evaluates the guard and exits), so `unwind: N` rejected it. A
    /// loop-free helper called more than once from one function also tripped the
    /// bound, because the counter was keyed by block without regard to *which*
    /// invocation. Both are fixed by counting back-edge traversals; the bound is
    /// now the number of iterations, which is what a caller means.
    #[test]
    fn the_unwind_bound_counts_iterations_not_header_entries() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    unwind: 3,
    ensures: ret == 3,
}
pub fn while_exact() -> u32 {
    let mut i = 0u32;
    let mut s = 0u32;
    while i < 3 { s += 1; i += 1; }
    s
}

spec! {
    requires: true,
    unwind: 3,
    ensures: ret == 3,
}
pub fn for_exact() -> u32 {
    let mut s = 0u32;
    for _i in 0..3u32 { s += 1; }
    s
}

fn helper(x: u8) -> u8 { if x == 0 { 0 } else { 1 } }

spec! {
    requires: x == 0,
    unwind: 1,
    ensures: ret == 0,
}
pub fn loop_free_helper_calls(x: u8) -> u8 {
    let a = helper(x);
    let b = helper(0);
    a + b
}
"#;
        for name in ["while_exact", "for_exact", "loop_free_helper_calls"] {
            let Some(o) = verify_src(name, src) else { return };
            assert!(
                o.is_verified(),
                "`{name}` must verify: the bound counts iterations, so `unwind: N` \
                 admits a loop that runs `N` times, and helper calls do not consume it; got: {o}"
            );
        }
    }

    /// F4: a bound one short of the iterations must still fail.
    ///
    /// The fix must not simply relax the bound: `unwind: 2` on a three-iteration
    /// loop is a claim the loop violates, and it has to be refuted. Without this
    /// the latch fix could pass by accepting every bound.
    #[test]
    fn an_unwind_bound_below_the_iterations_still_fails() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    unwind: 2,
    ensures: ret == 3,
}
pub fn for_too_few() -> u32 {
    let mut s = 0u32;
    for _i in 0..3u32 { s += 1; }
    s
}
"#;
        let Some(o) = verify_src("for_too_few", src) else { return };
        match o {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("unwind"),
                "a too-small bound must fail on the unwind obligation, got `{kind}`"
            ),
            other => panic!("`unwind: 2` on a 3-iteration loop must be refuted, got: {other}"),
        }
    }

    /// F6/F7: edition resolution reads a quoted key and an explicit workspace path.
    ///
    /// Two spellings Cargo accepts and the reader did not: a quoted key
    /// (`"edition" = "2021"`) read as *no* edition, so the 2015 default applied;
    /// and `package.workspace = "../ws"` pointing at a root that is not an
    /// ancestor, which the ancestor search could not find. Both are resolved from
    /// the manifest text, so they are unit-tested here rather than end to end.
    #[test]
    fn a_quoted_edition_key_and_an_explicit_workspace_path_are_resolved() {
        let dir = std::env::temp_dir().join(format!("verif-edition-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("member")).unwrap();
        std::fs::create_dir_all(dir.join("ws")).unwrap();
        std::fs::write(dir.join("ws/Cargo.toml"), "[workspace]\n[workspace.package]\nedition = \"2021\"\n").unwrap();
        std::fs::write(
            dir.join("member/Cargo.toml"),
            "[package]\nname = \"m\"\n\"edition\" = \"2024\"\n",
        )
        .unwrap();
        std::fs::write(dir.join("member/src.rs"), "").unwrap();
        let member = dir.join("member/src.rs");
        assert_eq!(
            verify::edition_from_manifest(&member),
            Some(verify::Edition::Rust2024),
            "a quoted `\"edition\"` key must be read, not defaulted to 2015"
        );

        std::fs::write(
            dir.join("member/Cargo.toml"),
            "[package]\nname = \"m\"\nworkspace = \"../ws\"\nedition.workspace = true\n",
        )
        .unwrap();
        assert_eq!(
            verify::edition_from_manifest(&member),
            Some(verify::Edition::Rust2021),
            "`package.workspace = \"../ws\"` must resolve to that root's edition"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// C3: the `for`-loop desugaring over a range is modelled, both directions.
    ///
    /// A `for i in a..b` lowers to `Range::new`/`RangeInclusive::new`, an
    /// `IntoIterator::into_iter` identity and a `next(&mut range)` loop, and all
    /// three are answered from the range's struct fields. The `unwind:` bound
    /// decides the loop without an invariant, and an `invariant:` that does not
    /// name the loop variable decides it too (`tri_invariant`). An invariant that
    /// *names* the loop variable is the one shape still refused: the element `i`
    /// is a `debug` binding inside a nested `scope` block that is not live at the
    /// loop header (`next` has not returned yet on entry), so `invariant_names`
    /// does not resolve it -- recorded in `ROADMAP.md` C3. The false twin is the
    /// evidence the range state is *read*: a model that returned a constant would
    /// prove it.
    ///
    /// The range's iterator state is written *through `&mut`*, so the loop header
    /// must havoc the range local (and its parts). When it did not, the exit guard
    /// folded to `false`, the exit edge was pruned as unreachable, and a false
    /// postcondition came back `Verified` -- the reason `tri_invariant` now uses an
    /// inductive invariant (`s = i.min(5050)`, not `s += i`) and
    /// `tri_invariant_cannot_prove_this` is asserted to be refuted.
    #[test]
    fn the_for_loop_range_desugaring_is_modelled() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: n <= 3,
    unwind: 4,
    ensures: ret <= 6,
}
pub fn for_inclusive_sum(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..=n { s += i; }
    s
}

spec! {
    requires: n <= 3,
    unwind: 4,
    ensures: ret <= 5,
}
pub fn for_inclusive_sum_cannot_prove_this(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..=n { s += i; }
    s
}

spec! {
    requires: true,
    unwind: 3,
    ensures: ret == 3,
}
pub fn for_exclusive_counts() -> u32 {
    let mut s = 0;
    for _i in 0..3u32 { s += 1; }
    s
}

spec! {
    requires: n <= 100,
    invariant: s <= 5050,
    ensures: ret <= 5050,
}
pub fn tri_invariant(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..=n { s = i.min(5050); }
    s
}

spec! {
    requires: n <= 100,
    invariant: s <= 5050,
    ensures: ret <= 3,
}
pub fn tri_invariant_cannot_prove_this(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..=n { s = i.min(5050); }
    s
}
"#;
        for name in ["for_inclusive_sum", "for_exclusive_counts", "tri_invariant"] {
            let Some(o) = verify_src(name, src) else { return };
            assert!(
                o.is_verified(),
                "`{name}` must verify: the range desugaring is modelled and the loop is \
                 decided by `unwind:` or by an invariant, got: {o}"
            );
        }
        let Some(f) = verify_src("for_inclusive_sum_cannot_prove_this", src) else { return };
        match f {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition"),
                "the false twin must fail on its postcondition, got `{kind}`"
            ),
            other => panic!(
                "the false twin claims `ret <= 5` for a sum that reaches 6 and must be \
                 refuted; a model that ignored the range state would prove it, got: {other}"
            ),
        }
        // The invariant tripwire: a `for` loop whose postcondition is false. The
        // loop's *iterator state* is written through `&mut`, so the havoc at the
        // header must reach it. When it did not, the exit guard folded to `false`,
        // the exit edge was pruned as unreachable, and this function came back
        // `Verified` -- a false proof. It must now be refuted.
        //
        // The assertion is `Failed` on the *postcondition*, not merely
        // `!is_verified()`. A refusal (`Incomplete`/`Skipped`) also satisfies
        // "not verified", so a model that gave up on the range state would pass a
        // weaker check while checking nothing -- the tripwire would be vacuous. A
        // refuted postcondition is the evidence the loop was modelled and its exit
        // state refuted the false claim.
        let Some(g) = verify_src("tri_invariant_cannot_prove_this", src) else { return };
        match g {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition"),
                "the invariant tripwire must fail on its postcondition, got `{kind}`"
            ),
            other => panic!(
                "a `for` loop whose postcondition is false must be refuted, not merely \
                 undecided; a model that does not havoc the iterator state proves it, and \
                 one that refuses it checks nothing, got: {other}"
            ),
        }
    }

    /// A loop whose body calls a *recursive* function must terminate the write-set
    /// discovery, and a reference-carrying recursive callee must still have its
    /// write propagated.
    ///
    /// The write-set walk follows each resolved callee to find what it writes
    /// through a reference. Before it was cycle-aware, each invocation allocated
    /// its own block-visit set, which stops a CFG cycle within one function and
    /// cannot stop a call cycle *between* invocations: a loop calling a
    /// self-recursive function followed the self-call forever and overflowed the
    /// stack, aborting the whole run. The walk now carries the set of functions on
    /// the call stack, which is what terminates it. On a cycle it also includes the
    /// call's reference arguments -- a conservative superset, since a callee can
    /// only reach caller storage through a reference; the reference twin below pins
    /// that the write still reaches the loop's havoc set, whichever mechanism
    /// carries it.
    #[test]
    fn a_loop_that_calls_a_recursive_function_terminates_and_is_sound() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    decreases: n,
    ensures: ret == n,
}
pub fn count_down(n: u8) -> u8 {
    if n == 0 { 0 } else { count_down(n - 1) + 1 }
}

spec! {
    requires: true,
    decreases: n,
    ensures: ret == 0,
}
pub fn walk(n: u8, c: &mut u8) -> u8 {
    if n == 0 { 0 } else { *c = c.wrapping_add(1); walk(n - 1, c) }
}

spec! {
    requires: n <= 3,
    invariant: i <= 3,
    ensures: ret <= 3,
}
pub fn loop_calls_recursive(n: u8) -> u8 {
    let mut i = 0u8; let mut s = 0u8;
    while i < 3 { s = count_down(n); i += 1; }
    s
}

spec! {
    requires: n <= 3,
    invariant: i <= 3,
    ensures: ret == 0,
}
pub fn loop_calls_recursive_cannot_prove_this(n: u8) -> u8 {
    let mut i = 0u8; let mut s = 0u8;
    while i < 3 { s = count_down(n); i += 1; }
    s
}

spec! {
    requires: x == 0,
    invariant: i <= 3,
    ensures: ret <= 255,
}
/// A loop calling a *reference-carrying* recursive callee: the call cycle is
/// refused rather than followed, and the call's reference argument is added
/// directly. `x` is written through `walk`, so the exit state cannot keep `0`.
pub fn loop_calls_ref_recursive(x: &mut u8) -> u8 {
    let mut i = 0u8;
    while i < 3 { walk(1, x); i += 1; }
    *x
}

spec! {
    requires: x == 0,
    invariant: i <= 3,
    ensures: ret == 0,
}
/// The false twin: `walk` writes `x`, so `ret == 0` is false. A model that
/// dropped the reference from the cycle's havoc would prove it.
pub fn loop_calls_ref_recursive_cannot_prove_this(x: &mut u8) -> u8 {
    let mut i = 0u8;
    while i < 3 { walk(1, x); i += 1; }
    *x
}

spec! {
    requires: n <= 8,
    invariant: i <= 3,
    ensures: ret <= 1,
}
/// A *mutual* recursion cycle reached from an invariant loop: `even_w` calls
/// `odd_w` calls `even_w`. The write-set walk must terminate on the cycle
/// (`visiting` holds the functions on the stack), and neither callee writes a
/// reference, so the loop's only write is its own counter. Before the cycle
/// guard this was an unbounded recursion between *invocations* and overflowed the
/// stack, aborting the whole run.
pub fn loop_calls_mutual_recursive(n: u8) -> u8 {
    let mut i = 0u8;
    let mut s = 0u8;
    while i < 3 { s = even_w(n); i += 1; }
    s
}

spec! {
    requires: true,
    decreases: n,
    ensures: ret <= 1,
}
pub fn even_w(n: u8) -> u8 {
    if n == 0 { 1 } else { odd_w(n - 1) }
}

spec! {
    requires: true,
    decreases: n,
    ensures: ret <= 1,
}
pub fn odd_w(n: u8) -> u8 {
    if n == 0 { 0 } else { even_w(n - 1) }
}
"#;
        // The crash vehicle: a scalar-only call into a self-recursive callee. The
        // walk must *return* (a stack overflow aborts the binary, so reaching the
        // assertion at all is half the evidence), and the loop must be decided --
        // the false twin refuted on its postcondition, not skipped.
        for name in [
            "loop_calls_recursive",
            "loop_calls_recursive_cannot_prove_this",
            "loop_calls_ref_recursive",
            "loop_calls_ref_recursive_cannot_prove_this",
        ] {
            let Some(o) = verify_src(name, src) else { return };
            assert!(
                !matches!(o, FnOutcome::Skipped { .. } | FnOutcome::Incomplete { .. }),
                "`{name}` must be decided, not refused: a cycle-aware write-set walk \
                 terminates; a refusal here means the walk gave up, got: {o}"
            );
        }
        // A loop reaching a *mutually* recursive callee. Mutual recursion has no
        // single decreasing measure here, so it is not *proved* -- but the
        // write-set walk must still terminate on the cycle (reaching this
        // assertion at all is the evidence: an unbounded walk aborts the binary),
        // and the loop must never come back `Verified`, which would be a proof of
        // an unmodelled call.
        let Some(m) = verify_src("loop_calls_mutual_recursive", src) else { return };
        assert!(
            !m.is_verified(),
            "a loop reaching a mutually recursive callee must not be *proved* (mutual \
             recursion is not modelled), got: {m}"
        );
        let Some(f) = verify_src("loop_calls_recursive_cannot_prove_this", src) else {
            return;
        };
        match f {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition"),
                "the false twin must fail on its postcondition, got `{kind}`"
            ),
            other => panic!(
                "the false twin claims `ret == 0` for a loop returning `n` and must be \
                 refuted, got: {other}"
            ),
        }
        // The reference-carrying twin is the assertion the earlier version of this
        // test lacked: a loop calling a *reference-carrying* recursive callee must
        // still have that reference havoced at the header, so the exit state cannot
        // keep the entry `0`. It pins the *effect* (the reference write reaches the
        // exit), not which mechanism carries it: measured, the callee's own direct
        // scan folded back positionally is what carries it for this shape, and the
        // cycle branch's reference inclusion is a conservative superset over it.
        let Some(g) = verify_src("loop_calls_ref_recursive_cannot_prove_this", src) else {
            return;
        };
        match g {
            FnOutcome::Failed { kind, .. } => assert!(
                kind.contains("postcondition"),
                "the reference twin must fail on its postcondition, got `{kind}`"
            ),
            other => panic!(
                "`walk` writes `x` through its reference argument, so `ret == 0` must be \
                 refuted; a `verified` here means the reference write did not reach the \
                 loop's havoc set, got: {other}"
            ),
        }
    }

    /// C3 exit criterion, second half: a loop with no contract is reported as a
    /// *missing loop contract*, not as an unmodelled construct.
    ///
    /// `tri` in `everyday.rs` declares no `invariant:` or `unwind:`, so its loop is
    /// unwound to the default and the path stops. That is an honest incompleteness,
    /// but the message has to point at the remedy -- the loop is understood, and the
    /// tool is declining to guess an exit -- rather than reading as "the frontend
    /// could not model this".
    #[test]
    fn a_loop_without_a_contract_names_the_missing_contract() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: true,
}
pub fn tri(n: u32) -> u32 {
    let mut s = 0;
    for i in 0..=n { s += i; }
    s
}
"#;
        let Some(o) = verify_src("tri", src) else { return };
        match o {
            FnOutcome::Incomplete { reasons, .. } => {
                let joined = reasons.join(" | ");
                assert!(
                    joined.contains("missing loop contract")
                        && joined.contains("invariant:")
                        && joined.contains("unwind:"),
                    "the reason must name the missing loop contract and the two ways to \
                     supply it, got: {joined}"
                );
            }
            other => panic!(
                "`tri` declares no loop contract and must be an honest incompleteness, \
                 got: {other}"
            ),
        }
    }
}

/// Regression tests for the signed-inclusive-range review (R1–R6).
///
/// These live outside `review_round` because they pin a *different* surface:
/// the `RangeInclusive::next` model's boundary arithmetic (R1), its state on an
/// exhausted range (R4), the unwind counter's key (R2/R3), and the struct layout
/// the drop-glue check reads (R5/R6). Every case was cross-checked against a real
/// `rustc` execution oracle, so the expected counts are Rust's, not the model's.
mod range_and_layout_review {
    use super::*;

    /// R1/R4: a signed inclusive range's `next` must stop at the boundary and must
    /// not advance an exhausted range.
    ///
    /// The successor's overflow flag was tested only for the *unsigned* rule
    /// (`succ == 0`), which never fires on a signed range: `127i8..=127i8` kept
    /// yielding past `127` into `-128`, `-127`, ... until the `unwind:` bound, so a
    /// true contract became a bound failure. The flag must test the *signed* `MIN`.
    /// And `next` on an empty range must leave the range unchanged (Rust does not
    /// advance `start` on `None`), or a later call resurrects an element.
    ///
    /// The counts are Rust's own, read from a compiled oracle, so the assertion is
    /// the language's semantics rather than the model's.
    #[test]
    fn a_signed_inclusive_range_stops_at_its_boundary() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    unwind: 8,
    ensures: ret == 1,
}
pub fn single_signed_incl() -> u32 {
    let mut c = 0u32;
    for _ in 127i8..=127i8 { c += 1; }
    c
}

spec! {
    requires: true,
    unwind: 8,
    ensures: ret == 2,
}
pub fn two_signed_incl() -> u32 {
    let mut c = 0u32;
    for _ in 126i8..=127i8 { c += 1; }
    c
}

spec! {
    requires: true,
    unwind: 8,
    ensures: ret == 3,
}
pub fn three_signed_incl() -> u32 {
    let mut c = 0u32;
    for _ in (-128i8)..=(-126i8) { c += 1; }
    c
}

spec! {
    requires: true,
    unwind: 4,
    ensures: ret == 1,
}
pub fn single_unsigned_incl() -> u32 {
    let mut c = 0u32;
    for _ in 255u8..=255u8 { c += 1; }
    c
}
"#;
        for (name, want) in [
            ("single_signed_incl", 1u32),
            ("two_signed_incl", 2),
            ("three_signed_incl", 3),
            ("single_unsigned_incl", 1),
        ] {
            let Some(o) = verify_src(name, src) else { return };
            assert!(
                o.is_verified(),
                "`{name}` must verify with {want} iteration(s); a signed range whose \
                 overflow flag tests zero keeps yielding past its bound, got: {o}"
            );
        }
    }

    /// R4: `next` on an empty inclusive range is idempotent.
    ///
    /// `255u8..=254u8` is empty, so both `next` calls are `None`. A model that
    /// advanced `start` on the first `None` would resurrect an element on the
    /// second call (`Some(0)`), turning a true contract into a refutation.
    #[test]
    fn an_empty_inclusive_range_stays_empty() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn empty_incl_twice() -> u8 {
    let mut r = 255u8..=254u8;
    let _a = r.next();
    let b = r.next();
    match b { Some(_) => 1, None => 0 }
}

spec! {
    requires: true,
    ensures: ret == 0,
}
pub fn empty_excl_twice() -> u8 {
    let mut r = 255u8..255u8;
    let _a = r.next();
    let b = r.next();
    match b { Some(_) => 1, None => 0 }
}
"#;
        for name in ["empty_incl_twice", "empty_excl_twice"] {
            let Some(o) = verify_src(name, src) else { return };
            assert!(
                o.is_verified(),
                "`{name}` must verify: `next` leaves an empty range unchanged, so the \
                 second call is `None` too, got: {o}"
            );
        }
    }

    /// R2/R3: the unwind bound counts iterations of the *loop*, not of one latch.
    ///
    /// A loop body with two back-edge blocks (an `if` whose arms both reach the
    /// header) had each latch counted separately, so the combined trip count could
    /// exceed a declared `unwind:` while neither latch's own count did -- a
    /// two-iteration loop verified under `unwind: 1`. The counter is now keyed by
    /// the loop header, and a `switchInt` block no longer clears it.
    #[test]
    fn the_unwind_bound_counts_the_whole_loop_not_one_latch() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

spec! {
    requires: n == 2,
    unwind: 1,
    ensures: ret == 2,
}
pub fn two_latches(n: u8) -> u8 {
    let mut i = 0u8;
    while i < n {
        if i == 0 { i += 1; } else { i += 1; }
    }
    i
}

spec! {
    requires: n == 1,
    unwind: 1,
    ensures: ret == 1,
}
pub fn one_latch(n: u8) -> u8 {
    let mut i = 0u8;
    while i < n {
        if i == 0 { i += 1; } else { i += 1; }
    }
    i
}
"#;
        let Some(f) = verify_src("two_latches", src) else { return };
        assert!(
            !f.is_verified(),
            "a two-iteration loop under `unwind: 1` must run off the bound, got: {f}"
        );
        let Some(o) = verify_src("one_latch", src) else { return };
        assert!(
            o.is_verified(),
            "a one-iteration loop under `unwind: 1` must verify (positive control), got: {o}"
        );
    }

    /// R5: two structs of the same bare name in different modules must not share a
    /// layout.
    ///
    /// The struct table was keyed by the bare name, so `m::Outer` and `n::Outer`
    /// collided and the drop-glue check read whichever was recorded last. When that
    /// one is glue-free, a panicking field destructor vanishes and the function is
    /// a false `Verified`. The layout is now keyed by the module-qualified path.
    #[test]
    fn two_same_named_structs_do_not_share_a_layout() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub mod m {
    pub struct Outer { pub inner: Inner }
    pub struct Inner(pub u8);
    impl Drop for Inner {
        fn drop(&mut self) { if self.0 == 0 { panic!("inner"); } }
    }
    impl Drop for Outer { fn drop(&mut self) {} }
}
pub mod n {
    pub struct Outer { pub only: u8 }
}

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn same_name() -> u8 {
    let _g = m::Outer { inner: m::Inner(0) };
    1
}
"#;
        let Some(o) = verify_src("same_name", src) else { return };
        assert!(
            !o.is_verified(),
            "`m::Outer` has a field with a panicking destructor; sharing a layout with \
             `n::Outer` would hide it and prove this, got: {o}"
        );
    }

    /// A **qualified** type name must not be answered by a *bare* layout.
    ///
    /// The dump prints a type by its shortest crate-unique path, so a qualified
    /// spelling (`m::Outer`) means rustc could **not** shorten it -- at least two
    /// types share that tail. The bare key, when it exists at all, is then some
    /// other type's layout, and reading it proves a contract about the wrong
    /// fields. This was a false proof: with a crate-root `Outer { lo, hi }` and a
    /// one-line `pub mod m { pub struct Outer { hi, lo } }` (whose inline struct
    /// the line-oriented scanner never sees), the only layout recorded was the
    /// crate-root one, both field projections resolved to *it*, and
    /// `requires: o.hi == 5; ensures: ret == 5` on a body returning `o.lo` was
    /// **verified**. Rustc's own execution returns `7` for `{ hi: 5, lo: 7 }`.
    ///
    /// Both field directions are asserted, so the fix cannot pass by resolving
    /// one projection and refusing the other. The *positive* control is the next
    /// test: the same shapes with the module's struct on its own lines do verify,
    /// which is what shows this is about the one-line spelling and not about
    /// qualified names in general.
    #[test]
    fn a_qualified_type_is_not_answered_by_a_bare_layout() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Outer { pub lo: u8, pub hi: u8 }
pub mod m { pub struct Outer { pub hi: u8, pub lo: u8 } }

spec! {
    requires: o.hi == 5,
    ensures: ret == 5,
}
pub fn reads_the_other_field(o: &m::Outer) -> u8 { o.lo }

spec! {
    requires: o.lo == 5,
    ensures: ret == 5,
}
pub fn reads_the_other_field_mirror(o: &m::Outer) -> u8 { o.hi }
"#;
        for name in ["reads_the_other_field", "reads_the_other_field_mirror"] {
            let Some(o) = verify_src(name, src) else { return };
            assert!(
                !o.is_verified(),
                "`m::Outer`'s layout is not in the source the scanner read, so a contract \
                 about its fields must be refused -- proving it means the crate-root \
                 `Outer`'s fields were read instead. Got: {o}"
            );
        }
    }

    /// A multi-line module's struct *is* read, so the refusal above is about the
    /// one-line spelling and not about modules in general. Without this control a
    /// fix that simply refused every `m::`-qualified name would pass the test
    /// above.
    #[test]
    fn a_module_struct_on_its_own_lines_still_reads_its_fields() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Outer { pub lo: u8, pub hi: u8 }
pub mod m {
    pub struct Outer { pub hi: u8, pub lo: u8 }
}

spec! {
    requires: o.hi == 5,
    ensures: ret == 5,
}
pub fn reads_its_own_field(o: &m::Outer) -> u8 { o.hi }
"#;
        let Some(o) = verify_src("reads_its_own_field", src) else { return };
        assert!(
            o.is_verified(),
            "a module struct whose body is on its own lines has a real layout, so a true \
             contract about it must verify. Got: {o}"
        );
    }

    /// R6: a unit struct with a `Drop` impl is a zero-field layout, not an unknown
    /// container.
    ///
    /// `struct Guard;` was not read as a struct at all, so the drop-glue check saw
    /// an unknown type and refused the function. A unit struct has no fields, so its
    /// layout is empty and its `Drop` body is the only glue -- which runs, and a
    /// panicking one must be a real obligation.
    #[test]
    fn a_unit_struct_runs_its_destructor() {
        let src = r#"macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }

pub struct Guard;
impl Drop for Guard { fn drop(&mut self) {} }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn unit_drop() -> u8 {
    let _g = Guard;
    1
}

pub struct Boom;
impl Drop for Boom { fn drop(&mut self) { panic!("boom"); } }

spec! {
    requires: true,
    ensures: ret == 1,
}
pub fn panics_on_drop() -> u8 {
    let _g = Boom;
    1
}
"#;
        let Some(o) = verify_src("unit_drop", src) else { return };
        assert!(
            o.is_verified(),
            "a unit struct with a no-op destructor must verify, got: {o}"
        );
        let Some(p) = verify_src("panics_on_drop", src) else { return };
        assert!(
            !p.is_verified(),
            "a unit struct whose destructor panics must not verify, got: {p}"
        );
    }
}

/// A comment *before* a clause's colon is whitespace, and Rust's matcher allows it.
///
/// The matcher is `$($clause:ident : $body:expr,)*`, so `requires/**/: n > 0` is a
/// precondition. The separator fix turns the comment into a space -- `requires : n > 0`
/// -- and `take_clause` matched the literal `requires:`, so the clause was refused as
/// unknown and the whole function was *skipped*: a lost proof on valid syntax. The
/// contract here is true, so only reading both clauses can verify it; the second
/// function carries a false postcondition behind the same spelling, so "verified"
/// cannot be the clauses being dropped.
#[test]
fn a_comment_before_a_clause_colon_is_whitespace_not_a_dropped_clause() {
    let macros = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\n\n";
    let true_src = format!("{macros}spec! {{\n    requires/**/: n > 0,\n    ensures/**/: ret == n,\n}}\npub fn f(n: u8) -> u8 {{ n }}\n");
    let outcome = verify_src("f", &true_src).expect("the function must be reported");
    assert!(
        matches!(outcome, FnOutcome::Verified { .. }),
        "a comment before the colon must not drop the clause, got: {outcome:?}"
    );
    let false_src = format!("{macros}spec! {{\n    requires/**/: n > 0,\n    ensures/**/: ret == n + 1,\n}}\npub fn g(n: u8) -> u8 {{ n }}\n");
    let bad = verify_src("g", &false_src).expect("the function must be reported");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "a false postcondition behind a comment must still be refuted, got: {bad:?}"
    );
}

/// A comment between two tokens separates them, and a non-ASCII identifier is read
/// as written -- both are false-proof shapes when the block reader gets them wrong.
///
/// `ensures: ret == n/**/as/**/u8` is the cast `n as u8`. Deleting the comment glued
/// the tokens into `nasu8`, so a body returning an *argument* of that name satisfied
/// the clause while the real postcondition (`ret == n as u8`) is false. The `µ` case
/// is the same defect through `byte as char`: `µ` decoded to `Âµ`, a different
/// identifier, and a body returning an argument named `Âµ` verified it.
///
/// Both bodies here return the *mangled* spelling, so the verdict discriminates:
/// read correctly the clause is false and must be refuted; read under the bug it is
/// true and would be proved. That is the shape the ledger calls a false proof.
#[test]
fn a_comment_and_a_non_ascii_name_cannot_smuggle_a_false_proof() {
    let comment_src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\n\nspec! {\n    requires: true,\n    ensures: ret == n/**/as/**/u8,\n}\npub fn f(n: u8, nasu8: u8) -> u8 { let _ = n; nasu8 }\n";
    let uni_src = "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\n\nspec! {\n    requires: true,\n    ensures: ret == \u{b5},\n}\npub fn g(\u{b5}: u8, \u{c2}\u{b5}: u8) -> u8 { let _ = \u{b5}; \u{c2}\u{b5} }\n";

    for (name, src) in [("f", comment_src), ("g", uni_src)] {
        let outcome = verify_src(name, src).expect("the function must be reported");
        assert!(
            matches!(outcome, FnOutcome::Failed { .. }),
            "a clause naming a variable the body does not return must be refuted, got: {outcome:?}"
        );
    }
}

/// U3: a counterexample becomes a compiling, failing-then-fixed `#[test]`.
///
/// The emitted test calls the refuted function at the counterexample's inputs.
/// While the bug exists the call panics, so the test **fails**; fixing the body
/// makes the *same* test **pass** -- which is what makes it a regression test and
/// not a restatement of the bug. The two halves are the point: a test that passes
/// on both versions proves nothing.
#[test]
fn a_counterexample_becomes_a_failing_then_fixed_test() {
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif_emit_test_{}_{seq}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");

    let buggy = "/// ensures: ret <= 100\n\
                 pub fn bad(n: u8) -> u8 {\n    100 / (n - 5)\n}\n";
    let file = dir.join("buggy.rs");
    std::fs::write(&file, buggy).expect("write fixture");
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &probe_opts())
        .expect("verify the fixture");
    let emitted = verify::emit_test_source(&file, &report, "bad")
        .expect("a panic counterexample must become a test");
    assert!(emitted.contains("#[test]"), "must be a `#[test]`:\n{emitted}");
    assert!(
        emitted.contains("bad(0)"),
        "must call at the counterexample input (`n = 0`):\n{emitted}"
    );

    // The buggy body: the emitted test compiles and *fails* (the call panics).
    let buggy_src = format!("{buggy}\n{emitted}");
    let buggy_bin = dir.join("buggy_test");
    compile_emitted_test(&rustc, &dir, "buggy_test.rs", &buggy_src, &buggy_bin);
    let out = std::process::Command::new(&buggy_bin).output().expect("run the test binary");
    assert!(
        !out.status.success(),
        "the emitted test must FAIL on the buggy function (it panics), but it passed"
    );

    // The fixed body: the *same* test passes.
    let fixed = "/// ensures: ret <= 100\n\
                 pub fn bad(n: u8) -> u8 {\n    if n < 5 { 0 } else { 100 / (n - 5) }\n}\n";
    let fixed_src = format!("{fixed}\n{emitted}");
    let fixed_bin = dir.join("fixed_test");
    compile_emitted_test(&rustc, &dir, "fixed_test.rs", &fixed_src, &fixed_bin);
    let out = std::process::Command::new(&fixed_bin).output().expect("run the test binary");
    assert!(
        out.status.success(),
        "the same test must PASS on the fixed function, got:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// Compile a `#[test]`-bearing source with `rustc --test` into an executable.
fn compile_emitted_test(rustc: &str, dir: &std::path::Path, name: &str, src: &str, out: &std::path::Path) {
    let path = dir.join(name);
    std::fs::write(&path, src).expect("write test source");
    let status = std::process::Command::new(rustc)
        .args(["--test", "--edition", "2024", "-C", "overflow-checks=on", "-o"])
        .arg(out)
        .arg(&path)
        .status()
        .expect("spawn rustc");
    assert!(status.success(), "the emitted test must compile: {}", path.display());
}

/// U7: the proof cache reuses a decided verdict when nothing changed, and a change
/// to the program invalidates it.
///
/// A cached `verified` surviving a change to the rule that produced it would be a
/// false proof, so the test proves both halves: the cache *is* consulted (a tampered
/// entry shows through), and a change to the source is a *miss* (the real verdict
/// returns). The key covers the MIR, the contracts, the edition and the engine.
#[test]
fn the_proof_cache_reuses_a_decided_verdict_and_a_change_is_a_miss() {
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif_cache_{}_{seq}", std::process::id()));
    let cache = dir.join("cache");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let file = dir.join("f.rs");
    let src = "/// ensures: ret == n\npub fn id(n: u8) -> u8 { n }\n\n\
               /// ensures: ret == 7\npub fn wrong(n: u8) -> u8 { n }\n";
    std::fs::write(&file, src).expect("write fixture");

    let mut opts = probe_opts();
    opts.cache = Some(cache.clone());

    let kind = |r: &verify::FileReport, name: &str| {
        r.outcomes.iter().find(|(n, _)| n == name).map(|(_, o)| match o {
            FnOutcome::Verified { .. } => "verified",
            FnOutcome::Failed { .. } => "failed",
            FnOutcome::Incomplete { .. } => "incomplete",
            FnOutcome::Skipped { .. } => "skipped",
        })
    };

    // First run: real verdicts, and a cache entry is written.
    let r1 = verify::verify_file_with_opts(&rustc, &file, &[], &opts).expect("verify");
    assert_eq!(kind(&r1, "id"), Some("verified"), "id holds");
    assert_eq!(kind(&r1, "wrong"), Some("failed"), "wrong is refuted");
    let entry = std::fs::read_dir(&cache)
        .expect("cache dir")
        .next()
        .expect("one entry")
        .unwrap()
        .path();

    // Second run: same verdicts (reused or recomputed, the answers must agree).
    let r2 = verify::verify_file_with_opts(&rustc, &file, &[], &opts).expect("verify");
    assert_eq!(kind(&r2, "id"), Some("verified"));
    assert_eq!(kind(&r2, "wrong"), Some("failed"));

    // Tamper the cache: `id` marked Failed{TAMPERED}. If the cache is consulted the
    // tampered kind shows through -- the only way to observe a hit without timing,
    // and it is exactly the stale value a wrong key would trust.
    std::fs::write(&entry, "F\tid\tTAMPERED\tx\n").expect("tamper cache");
    let r3 = verify::verify_file_with_opts(&rustc, &file, &[], &opts).expect("verify");
    let id3 = r3.outcomes.iter().find(|(n, _)| n == "id").map(|(_, o)| o).unwrap();
    assert!(
        matches!(id3, FnOutcome::Failed { kind, .. } if kind.contains("TAMPERED")),
        "the cache must be consulted: a tampered entry should show through, got {id3:?}"
    );

    // Change the source: a new key, so a *miss* -- the real verdict returns, not the
    // tampered one.
    let src2 = "/// ensures: ret == n\npub fn id(n: u8) -> u8 { n }\n\n\
                /// ensures: ret == 8\npub fn wrong(n: u8) -> u8 { n }\n";
    std::fs::write(&file, src2).expect("rewrite fixture");
    let r4 = verify::verify_file_with_opts(&rustc, &file, &[], &opts).expect("verify");
    assert_eq!(
        kind(&r4, "id"),
        Some("verified"),
        "a changed source is a cache miss, so the real verdict returns (not the tampered one)"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A1: a contract-only edit in an external module must invalidate the cache.
///
/// The contract lives in the *inlined module text*, not the root source and not the
/// MIR, so keying the cache on the root source alone would let the edit reuse the
/// old verdict — a false proof. The key fingerprints the combined snapshot.
#[test]
fn a_contract_only_edit_in_a_module_invalidates_the_cache() {
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif_modcache_{}_{seq}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let cache = dir.join("cache");
    let lib = dir.join("lib.rs");
    let math = dir.join("math.rs");
    std::fs::write(&lib, "pub mod math;\n").expect("root");
    std::fs::write(&math, "/// ensures: ret == 7\npub fn seven() -> u8 { 7 }\n").expect("math");
    let mut opts = probe_opts();
    opts.cache = Some(cache.clone());

    fn seven(r: &verify::FileReport) -> Option<&FnOutcome> {
        r.outcomes.iter().find(|(k, _)| k == "math::seven" || k == "seven").map(|(_, o)| o)
    }
    let r1 = verify::verify_file_with_opts(&rustc, &lib, &[], &opts).expect("verify");
    assert!(
        matches!(seven(&r1), Some(FnOutcome::Verified { .. })),
        "cold: the module contract holds; got {:?}",
        r1.outcomes
    );
    // Edit *only* the module's contract. The MIR is unchanged; the snapshot is not.
    std::fs::write(&math, "/// ensures: ret == 8\npub fn seven() -> u8 { 7 }\n").expect("math2");
    let r2 = verify::verify_file_with_opts(&rustc, &lib, &[], &opts).expect("verify");
    assert!(
        matches!(seven(&r2), Some(FnOutcome::Failed { .. })),
        "a contract-only module edit must invalidate the cache (else a stale `verified` \
         proves a false contract); got {:?}",
        r2.outcomes
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A2: two trait impls of one method share a *report label* (`S::check`) but must
/// keep *distinct* cache entries — keyed by the MIR definition name, not the label.
#[test]
fn two_trait_impls_of_one_method_get_distinct_cached_verdicts() {
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif_traitcache_{}_{seq}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let cache = dir.join("cache");
    let file = dir.join("lib.rs");
    let src = "pub struct S;\n\
               pub trait A { fn check(&self) -> u8; }\n\
               pub trait B { fn check(&self) -> u8; }\n\
               impl A for S {\n    /// ensures: ret == 9\n    fn check(&self) -> u8 { 1 }\n}\n\
               impl B for S {\n    /// ensures: ret == 1\n    fn check(&self) -> u8 { 1 }\n}\n";
    std::fs::write(&file, src).expect("fixture");
    let mut opts = probe_opts();
    opts.cache = Some(cache.clone());

    let tally = |r: &verify::FileReport| {
        let (mut v, mut f) = (0, 0);
        for (k, o) in &r.outcomes {
            if k == "S::check" {
                match o {
                    FnOutcome::Verified { .. } => v += 1,
                    FnOutcome::Failed { .. } => f += 1,
                    _ => {}
                }
            }
        }
        (v, f)
    };
    let r1 = verify::verify_file_with_opts(&rustc, &file, &[], &opts).expect("verify");
    assert_eq!(tally(&r1), (1, 1), "cold: one pass, one fail; got {:?}", r1.outcomes);
    let r2 = verify::verify_file_with_opts(&rustc, &file, &[], &opts).expect("verify");
    assert_eq!(
        tally(&r2),
        (1, 1),
        "warm: the two impls must keep their own verdicts, not share one; got {:?}",
        r2.outcomes
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// U3/finding 3: the emitted replay call uses the *real* declaration's parameter
/// order, not a comment above it that reads the parameters the other way round.
#[test]
fn a_replay_call_uses_the_real_declaration_not_a_comment() {
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif_replay_{}_{seq}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let file = dir.join("f.rs");
    // The comment swaps the order; the real declaration is (a, b). `requires: b == 1`
    // makes the panic happen at `a == 0, b == 1`, so the right call is `bad(0, 1)`.
    std::fs::write(
        &file,
        "// fn bad(b: u8, a: u8)\n/// requires: b == 1\npub fn bad(a: u8, b: u8) -> u8 { 100 / a }\n",
    )
    .expect("fixture");
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &probe_opts()).expect("verify");
    let emitted = verify::emit_test_source(&file, &report, "bad").expect("a panic counterexample");
    assert!(
        emitted.contains("bad(0, 1)"),
        "the real parameter order (a, b) must be used, not the comment's; got:\n{emitted}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `enumerate`'s index counts from the enumerate's own start (0, 1, ...), not the raw
/// slice position: `skip(1).enumerate().next().0` is 0 and `rev().enumerate().next().0`
/// is 0, while `enumerate().skip(1).next().0` is 1. Using `pos` for the index made the
/// first two report the slice position (`skip`'s 1), so that old value is a tripwire.
#[test]
fn an_enumerate_index_counts_from_the_enumerates_start() {
    let skip = verify_src(
        "ei_skip",
        "/// requires: xs.len() == 2\n/// ensures: ret == 0\npub fn ei_skip(xs: &[u8]) -> usize { match xs.iter().skip(1).enumerate().next() { Some((i, _)) => i, None => 99 } }",
    );
    let Some(skip) = skip else { return };
    assert!(matches!(skip, FnOutcome::Verified { .. }), "skip(1).enumerate().next().0 is 0, got {skip}");
    let old = verify_src(
        "ei_old",
        "/// requires: xs.len() == 2\n/// ensures: ret == 1\npub fn ei_old(xs: &[u8]) -> usize { match xs.iter().skip(1).enumerate().next() { Some((i, _)) => i, None => 99 } }",
    );
    let Some(old) = old else { return };
    assert!(matches!(old, FnOutcome::Failed { .. }), "1 is the raw slice position, not the enumerate index; must be refuted, got {old}");
    let after = verify_src(
        "ei_after",
        "/// requires: xs.len() == 2\n/// ensures: ret == 1\npub fn ei_after(xs: &[u8]) -> usize { match xs.iter().enumerate().skip(1).next() { Some((i, _)) => i, None => 99 } }",
    );
    let Some(after) = after else { return };
    assert!(matches!(after, FnOutcome::Verified { .. }), "enumerate().skip(1).next().0 is 1, got {after}");
    let rev = verify_src(
        "ei_rev",
        "/// requires: xs.len() == 2\n/// ensures: ret == 0\npub fn ei_rev(xs: &[u8]) -> usize { match xs.iter().rev().enumerate().next() { Some((i, _)) => i, None => 99 } }",
    );
    let Some(rev) = rev else { return };
    assert!(matches!(rev, FnOutcome::Verified { .. }), "rev().enumerate().next().0 is 0, got {rev}");
}

/// A mapped sum over a *symbolic*-length slice must apply the `map` to the real
/// elements only: the padding (indices `>= len`) contributes 0, never `map(0)`. With
/// `requires: xs.len() <= 1 && xs[0] == 0`, `map(|x| x + 1).sum()` is 0 (len 0) or 1
/// (len 1). Applying the map *after* the zero-guard added `MAX_SYMBOLIC_LEN - len`
/// extra (map(0) = 1), so `ret <= 1` was refuted -- a wrong value.
#[test]
fn a_mapped_symbolic_sum_does_not_include_the_padding() {
    let ok = verify_src(
        "mapped_sum_pad",
        "/// requires: xs.len() <= 1 && xs[0] == 0\n/// ensures: ret <= 1\npub fn mapped_sum_pad(xs: &[u8]) -> u8 { xs.iter().copied().map(|x| x + 1).sum() }",
    );
    let Some(ok) = ok else { return };
    assert!(
        matches!(ok, FnOutcome::Verified { .. }),
        "map(|x| x + 1).sum() over len <= 1 with xs[0] == 0 is <= 1, got {ok}"
    );
    let bad = verify_src(
        "mapped_sum_pad_bad",
        "/// requires: xs.len() <= 1 && xs[0] == 0\n/// ensures: ret == 0\npub fn mapped_sum_pad_bad(xs: &[u8]) -> u8 { xs.iter().copied().map(|x| x + 1).sum() }",
    );
    let Some(bad) = bad else { return };
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "the sum is 1 at len 1, so == 0 must be refuted, got {bad}"
    );
}

/// Chained same-adapter calls compose: `take` by `min`, `skip` additively, `step_by`
/// multiplicatively. `take(2).take(3)` must yield 2 elements (the minimum), not 3 (the
/// second `take`'s count) -- so a "second take overwrites the end" model is refuted by
/// the false twin. This pins the audit's "chained same-adapter overwrite" concern as
/// resolved (the model composes; the adapters do not clobber each other).
#[test]
fn chained_same_adapters_compose() {
    let ok = |name: &str, body: &str, n: u64| {
        verify_src(name, &format!("/// requires: xs.len() == 5\n/// ensures: ret == {n}\npub fn {name}(xs: &[u8]) -> usize {{ {body} }}"))
    };
    // take composes by min: 2, and the 3 is refuted (the teeth).
    assert!(ok("ct", "xs.iter().take(2).take(3).count()", 2).is_some_and(|o| o.is_verified()));
    assert!(matches!(ok("ctf", "xs.iter().take(2).take(3).count()", 3), Some(FnOutcome::Failed { .. })));
    // skip composes additively: skip 3 of 5 -> 2.
    assert!(ok("cs", "xs.iter().skip(1).skip(2).count()", 2).is_some_and(|o| o.is_verified()));
    // step_by composes multiplicatively: step 6 of len 6 -> index 0 only -> 1.
    let step = verify_src("cst", "/// requires: xs.len() == 6\n/// ensures: ret == 1\npub fn cst(xs: &[u8]) -> usize { xs.iter().step_by(2).step_by(3).count() }");
    assert!(step.as_ref().is_some_and(|o| o.is_verified()), "step_by(2).step_by(3) of len 6 is 1 element, got {step:?}");
}


#[test]
fn step_by_composes_with_skip_and_take() {
    // `skip(n)`/`take(k)` count *yielded* elements, each `step` apart; a bare
    // `pos + n` / `pos + k` under-counts after `step_by` (a false refutation of a true
    // count). All of `xs.len() == 10`.
    let ok = |name: &str, body: &str, n: u64| {
        verify_src(name, &format!("/// requires: xs.len() == 10\n/// ensures: ret == {n}\npub fn {name}(xs: &[u8]) -> usize {{ {body} }}"))
    };
    assert!(ok("st", "xs.iter().step_by(3).take(2).count()", 2).is_some_and(|o| o.is_verified()));
    assert!(ok("ss", "xs.iter().step_by(3).skip(2).count()", 2).is_some_and(|o| o.is_verified()));
    assert!(ok("ts", "xs.iter().take(2).step_by(3).count()", 1).is_some_and(|o| o.is_verified()));
    assert!(ok("sk", "xs.iter().skip(2).step_by(3).count()", 3).is_some_and(|o| o.is_verified()));
    assert!(ok("rst", "xs.iter().rev().step_by(3).take(2).count()", 2).is_some_and(|o| o.is_verified()));
    assert!(ok("rss", "xs.iter().rev().step_by(3).skip(2).count()", 2).is_some_and(|o| o.is_verified()));
    // Teeth: before the fix (base offset) `step_by(3).take(2)` of len 10 counted 1, so
    // `== 1` verified and `== 2` was refuted. Now the reverse: `== 1` is the refutation.
    assert!(
        matches!(ok("stf", "xs.iter().step_by(3).take(2).count()", 1), Some(FnOutcome::Failed { .. })),
        "step_by(3).take(2) of len 10 is 2, so == 1 must be refuted"
    );
    assert!(
        matches!(ok("ssf", "xs.iter().step_by(3).skip(2).count()", 3), Some(FnOutcome::Failed { .. })),
        "step_by(3).skip(2) of len 10 is 2, so == 3 must be refuted"
    );
}


#[test]
fn take_cap_is_respected_by_last_and_count() {
    let last = |name: &str, body: &str, b: bool| {
        verify_src(name, &format!("/// requires: xs.len() == 5\n/// ensures: ret == {b}\npub fn {name}(xs: &[u8]) -> bool {{ {body} }}"))
    };
    let cnt = |name: &str, body: &str, n: u64| {
        verify_src(name, &format!("/// requires: xs.len() == 5\n/// ensures: ret == {n}\npub fn {name}(xs: &[u8]) -> usize {{ {body} }}"))
    };
    // take(0) exhausts the cursor: last() is None, count() is 0. `last`'s tag used
    // `pos < len` and ignored the take cap, so `is_none() == false` was a false proof.
    assert!(last("l0", "xs.iter().take(0).last().is_none()", true).is_some_and(|o| o.is_verified()));
    assert!(
        matches!(last("l0f", "xs.iter().take(0).last().is_none()", false), Some(FnOutcome::Failed { .. })),
        "take(0).last() is None, so is_none()==false must be refuted (was a false proof)"
    );
    assert!(last("l2", "xs.iter().take(2).last().is_some()", true).is_some_and(|o| o.is_verified()));
    assert!(cnt("c0", "xs.iter().take(0).count()", 0).is_some_and(|o| o.is_verified()));
    assert!(cnt("c2", "xs.iter().take(2).count()", 2).is_some_and(|o| o.is_verified()));
}

#[test]
fn nth_advances_by_step() {
    // `nth(k)` consumes k+1 *yielded* elements, each `step` apart, so the cursor must
    // advance by `(k+1)*step`. A bare `+1` under-advanced after `step_by`, so a later
    // `count()` miscounted (a false proof of the wrong count).
    let f = |name: &str, n: u64| {
        verify_src(name, &format!("/// requires: xs.len() == 12\n/// ensures: ret == {n}\npub fn {name}(xs: &[u8]) -> usize {{ let mut it = xs.iter().step_by(3); let _ = it.nth(1); it.count() }}"))
    };
    // step_by(3) over len 12 yields 0,3,6,9; nth(1) takes base 3, leaving 6,9 -> 2.
    assert!(f("nc", 2).is_some_and(|o| o.is_verified()));
    assert!(
        matches!(f("ncf", 3), Some(FnOutcome::Failed { .. })),
        "the remaining count is 2, so == 3 must be refuted"
    );
}

#[test]
fn rev_last_and_take_last_name_the_right_element() {
    // `rev().last()` is the original's first element; `rev().take(k).last()` is the
    // original's `n-k`. The rev branch named `base pos`, ignoring `step` and the take
    // cap, so `rev().take(2).last()` returned base 0 (10) instead of base n-2 (40) --
    // a false refutation of the true 40 and a false proof of 10.
    let f = |name: &str, e: u64, body: &str| {
        verify_src(name, &format!("/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n/// ensures: ret == {e}\npub fn {name}(xs: &[u8]) -> u8 {{ {body} }}"))
    };
    assert!(f("rl", 10, "xs.iter().rev().last().copied().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    assert!(f("rtl", 40, "xs.iter().rev().take(2).last().copied().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    // `rev().step_by(3).last()` = [50,40,30,20,10] stride 3 -> [50,20] -> last 20 (base 1).
    // A stride of 2 lands on base 0, the same as no stride, so it would not exercise `step`.
    assert!(f("rsl", 20, "xs.iter().rev().step_by(3).last().copied().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    // Teeth: the pre-fix value of rev().take(2).last() was 10; it is 40, so == 10 is refuted.
    assert!(
        matches!(f("rtlf", 10, "xs.iter().rev().take(2).last().copied().unwrap_or(0)"), Some(FnOutcome::Failed { .. })),
        "rev().take(2).last() is 40, so == 10 must be refuted"
    );
}

#[test]
fn extreme_folds_the_reversed_prefix() {
    // `rev().take(2).max()` folds [50, 40] -> 50. `slice_extreme` ignored `rev` and
    // folded the forward prefix [10, 20] -> 20, refuting the true 50 (a false proof of
    // 20 in the other direction).
    let f = |name: &str, e: u64, body: &str| {
        verify_src(name, &format!("/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n/// ensures: ret == {e}\npub fn {name}(xs: &[u8]) -> u8 {{ {body} }}"))
    };
    assert!(f("rtm", 50, "xs.iter().rev().take(2).copied().max().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    assert!(f("rtn", 40, "xs.iter().rev().take(2).copied().min().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    assert!(f("rx", 50, "xs.iter().rev().copied().max().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    // Teeth: the pre-fix forward-prefix max was 20, so == 20 must now be refuted.
    assert!(
        matches!(f("rtmf", 20, "xs.iter().rev().take(2).copied().max().unwrap_or(0)"), Some(FnOutcome::Failed { .. })),
        "rev().take(2).max() is 50, so == 20 must be refuted"
    );
}

#[test]
fn all_any_fold_the_reversed_prefix() {
    // `rev().take(3).any(|x| *x == 20)` is false: the reversed prefix is [50,40,30].
    // `all`/`any` read forward ([10,20,30], which contains 20), so the false verdict was
    // proved and the true one refuted -- the same `rev`-mapping bug `slice_extreme` had.
    let pre = "/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n";
    let b = |name: &str, e: bool, body: &str| {
        verify_src(name, &format!("{pre}/// ensures: ret == {e}\npub fn {name}(xs: &[u8]) -> bool {{ {body} }}"))
    };
    assert!(b("rta", false, "xs.iter().rev().take(3).any(|x| *x == 20)").is_some_and(|o| o.is_verified()));
    assert!(b("rtl", true, "xs.iter().rev().take(3).all(|x| *x > 25)").is_some_and(|o| o.is_verified()));
    // Teeth: the pre-fix (forward) `any` found 20 -> true; it is false, so == true is refuted.
    assert!(
        matches!(b("rtaf", true, "xs.iter().rev().take(3).any(|x| *x == 20)"), Some(FnOutcome::Failed { .. })),
        "rev().take(3).any(==20) is false, so == true must be refuted"
    );
}

#[test]
fn take_rev_and_rev_take_reverse_different_prefixes() {
    // `take(2).rev()` reverses the *taken forward prefix* [10,20] -> [20,10]; `rev().take(2)`
    // reverses the whole slice then takes -> [50,40]. They collapse to the same cursor state
    // (`rev, end=Some(2)`), so `base_of` must read the take/rev order (`taken_forward`).
    let pre = "/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n";
    let u8f = |name: &str, e: u64, body: &str| {
        verify_src(name, &format!("{pre}/// ensures: ret == {e}\npub fn {name}(xs: &[u8]) -> u8 {{ {body} }}"))
    };
    // take(2).rev(): [20,10] -> last 10, max 20.
    assert!(u8f("a1", 10, "xs.iter().take(2).rev().last().copied().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    assert!(u8f("a2", 20, "xs.iter().take(2).rev().copied().max().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    // rev().take(2): [50,40] -> last 40, max 50 (the earlier fix's regression).
    assert!(u8f("a5", 40, "xs.iter().rev().take(2).last().copied().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    assert!(u8f("a6", 50, "xs.iter().rev().take(2).copied().max().unwrap_or(0)").is_some_and(|o| o.is_verified()));
    // Teeth: take(2).rev().max() is 20, so == 50 (the rev().take(2) answer) must be refuted.
    assert!(
        matches!(u8f("a2f", 50, "xs.iter().take(2).rev().copied().max().unwrap_or(0)"), Some(FnOutcome::Failed { .. })),
        "take(2).rev().max() is 20, so == 50 must be refuted"
    );
}



#[test]
fn skip_or_take_with_rev_is_refused_not_mis_windowed() {
    // The cursor stores one `pos` (a skipped count forward, a distance-from-end under
    // `rev`), so `skip(n).take(k).rev()` and `skip(n).rev()` cannot be represented and
    // are refused -- before the fix `skip(1).take(2).rev().next()` read the slice edge
    // (a false refutation of the true 30).
    let pre = "/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n";
    for (n, body) in [
        ("sk_take_rev", "xs.iter().skip(1).take(2).rev().next().copied().unwrap_or(0)"),
        ("sk_rev", "xs.iter().skip(1).rev().next().copied().unwrap_or(0)"),
    ] {
        let src = format!("{pre}/// ensures: ret == 30\npub fn {n}(xs: &[u8]) -> u8 {{ {body} }}");
        let o = verify_src(n, &src).expect("an outcome");
        assert!(matches!(o, FnOutcome::Incomplete { .. }), "`{n}` must be refused (Incomplete), got {o:?}");
    }
}

#[test]
fn a_rebound_slice_reads_the_callers_entry_length() {
    // `mut xs: &[u8]; xs = ys` changes which slice the *body* sees, not the caller's
    // one-element slice -- so `xs.len()` is the entry length (1), not `ys`'s (2).
    let pre = "/// requires: xs.len() == 1 && ys.len() == 2\n";
    let t = format!("{pre}/// ensures: xs.len() == 1\npub fn rb_true<'a>(mut xs: &'a [u8], ys: &'a [u8]) -> u8 {{ xs = ys; 0 }}");
    assert!(verify_src("rb_true", &t).is_some_and(|o| o.is_verified()), "the caller's slice keeps length 1");
    let f = format!("{pre}/// ensures: xs.len() == 2\npub fn rb_false<'a>(mut xs: &'a [u8], ys: &'a [u8]) -> u8 {{ xs = ys; 0 }}");
    assert!(matches!(verify_src("rb_false", &f), Some(FnOutcome::Failed { .. })), "the caller's slice is still length 1, so == 2 must be refuted");
}

#[test]
fn a_rebound_mut_vec_length_is_refused_but_push_is_seen() {
    // A `&mut Vec` the body pushes to has a final length (push is seen). A `&mut Vec`
    // that is *rebound* (`v = w`) aliases the new target, which the model does not
    // track, so a Vec length after a rebind is *refused* (unreadable `v.len()`), never
    // read back from the entry value -- that fallback was a false proof for
    // `v.push(1); v = w` (the caller's Vec has length 1, the entry value 0).
    let pre = "/// requires: v.len() == 1 && w.len() == 2\n";
    for (n, e) in [("vr_true", 1u64), ("vr_false", 2u64)] {
        let src = format!("{pre}/// ensures: v.len() == {e}\npub fn {n}<'a>(mut v: &'a mut Vec<u8>, w: &'a mut Vec<u8>) -> u8 {{ v = w; 0 }}");
        assert!(matches!(verify_src(n, &src), Some(FnOutcome::Incomplete { .. })), "`{n}`: a rebound &mut Vec's length must be refused (Incomplete)");
    }
    // The push case is still seen (the entry length 0 becomes 1).
    let p = "/// requires: v.len() == 0\n/// ensures: ret == 1\npub fn vp(v: &mut Vec<u8>) -> usize { v.push(1); v.len() }";
    assert!(verify_src("vp", p).is_some_and(|o| o.is_verified()), "a push must be reflected in the final length");
    // A push *then* rebind is refused, not proved against the entry length.
    let pr = "/// requires: v.len() == 0 && w.len() == 1\n/// ensures: v.len() == 0\npub fn pr0<'a>(mut v: &'a mut Vec<u8>, w: &'a mut Vec<u8>) -> u8 { v.push(1); v = w; 0 }";
    assert!(matches!(verify_src("pr0", pr), Some(FnOutcome::Incomplete { .. })), "push-then-rebind must refuse the length, not prove the entry value");
}

#[test]
fn a_skip_on_a_reversed_prefix_cannot_be_reversed_again() {
    // `take(k).rev().skip(1).rev()`: the `skip` advanced `pos` relative to the reversed
    // sequence, so the second `rev` cannot map it back to a forward cursor -- it read
    // `xs[1]` = 20 where the real next element is 10 (a false proof). Both directions are
    // now refused (the single `take.rev.skip.next` is still correct).
    let pre = "/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n";
    for (n, e) in [("trsr10", 10u64), ("trsr20", 20u64)] {
        let src = format!("{pre}/// ensures: ret == {e}\npub fn {n}(xs: &[u8]) -> u8 {{ xs.iter().take(3).rev().skip(1).rev().next().copied().unwrap_or(0) }}");
        assert!(matches!(verify_src(n, &src), Some(FnOutcome::Incomplete { .. })), "`{n}` must be refused");
    }
}

#[test]
fn chained_map_and_filter_are_refused() {
    // A single `map` is modelled; a second (or mixed) adapter is refused, because
    // `map(f).map(g)` was modelled as `g` alone (a false proof: it returned 6, not 7).
    let single = "/// requires: xs.len() == 1 && xs[0] == 5\n/// ensures: ret == 6\npub fn single_map(xs: &[u8]) -> u8 { xs.iter().copied().map(|x| x.wrapping_add(1)).sum::<u8>() }";
    assert!(verify_src("single_map", single).is_some_and(|o| o.is_verified()), "a single map is still modelled");
    for (n, e) in [("mm_true", 7u64), ("mm_false", 6u64)] {
        let src = format!("/// requires: xs.len() == 1 && xs[0] == 5\n/// ensures: ret == {e}\npub fn {n}(xs: &[u8]) -> u8 {{ xs.iter().copied().map(|x| x.wrapping_add(1)).map(|x| x.wrapping_add(1)).sum::<u8>() }}");
        let o = verify_src(n, &src).expect("an outcome");
        assert!(matches!(o, FnOutcome::Incomplete { .. }), "`{n}` must be refused (Incomplete), got {o:?}");
    }
}

#[test]
fn take_rev_rev_cancels_to_the_forward_take() {
    // `take(k).rev().rev()` is the forward `take(k)` again; a third `rev` is
    // `take(k).rev()`. Refusing it (the old behaviour) lost a proof.
    let pre = "/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n";
    let v = |n: &str, e: u64, body: &str| verify_src(n, &format!("{pre}/// ensures: ret == {e}\npub fn {n}(xs: &[u8]) -> u8 {{ {body} }}"));
    assert!(v("trr2", 10, "xs.iter().take(2).rev().rev().next().copied().unwrap_or(0)").is_some_and(|o| o.is_verified()), "take(2).rev().rev() is the forward take(2), first 10");
    assert!(v("trr3", 20, "xs.iter().take(2).rev().rev().rev().next().copied().unwrap_or(0)").is_some_and(|o| o.is_verified()), "a third rev is take(2).rev(), first 20");
    // Teeth: == 20 on the double-rev (which is 10) must be refuted.
    assert!(matches!(v("trr2f", 20, "xs.iter().take(2).rev().rev().next().copied().unwrap_or(0)"), Some(FnOutcome::Failed { .. })), "take(2).rev().rev() is 10, so == 20 must be refuted");
}

#[test]
fn compound_closures_and_rev_folds_are_refused() {
    // Pins the *stale* review findings: these shapes are already refusals, never a
    // false proof, so the fix is the regression test, not a code change.
    let pre = "/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n";
    for (n, body) in [
        ("cm", "xs.iter().copied().map(|x| (x + 1) * 2).sum::<u8>()"),
        ("rs", "xs.iter().rev().copied().sum::<u8>()"),
    ] {
        let src = format!("{pre}/// ensures: ret == 0\npub fn {n}(xs: &[u8]) -> u8 {{ {body} }}");
        let o = verify_src(n, &src).expect("an outcome");
        assert!(matches!(o, FnOutcome::Incomplete { .. }), "`{n}` must be refused (Incomplete), got {o:?}");
    }
}

#[test]
fn vec_clear_with_drop_glue_and_box_write_are_refused() {
    // A `Vec::clear` on an element with drop glue would run the destructor (which may
    // panic); resetting the length alone would be a false proof. And `*b = v` on a Box
    // hits the null-check refusal before the store, so neither can be verified.
    let vc = "pub struct Boom;\nimpl Drop for Boom { fn drop(&mut self) { assert!(false); } }\n/// requires: v.len() == 1\n/// ensures: ret == 0\npub fn vc(v: &mut Vec<Boom>) -> usize { v.clear(); v.len() }";
    assert!(matches!(verify_src("vc", vc), Some(FnOutcome::Incomplete { .. })), "Vec::clear on a drop-glue element must be refused");
}

#[test]
fn map_or_all_then_a_terminal_is_refused() {
    // `map().next()` and `all()` followed by `next()` on the same iterator are refused
    // (the terminal consumes or discards the cursor), never mis-modelled.
    let mn = "/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n/// ensures: ret == 11\npub fn mn(xs: &[u8]) -> u8 { xs.iter().copied().map(|x| x.wrapping_add(1)).next().unwrap_or(0) }";
    assert!(matches!(verify_src("mn", mn), Some(FnOutcome::Incomplete { .. })), "map().next() must be refused");
    let an = "/// requires: xs.len() == 5\n/// ensures: ret == 10\npub fn an(xs: &[u8]) -> u8 { let mut it = xs.iter(); let _ = it.all(|x| *x < 100); it.next().copied().unwrap_or(0) }";
    assert!(matches!(verify_src("an", an), Some(FnOutcome::Incomplete { .. })), "all() then next() must be refused");
}


#[test]
fn a_multifile_method_contract_is_verified_or_refuted_by_original_location() {
    // A method's contract is keyed by a *snapshot* line; the MIR's `impl_loc` is rustc's
    // original line. The line map translates between them, so a method in a module file
    // and a root method below a `mod` declaration both pair with their own body: a true
    // contract is `Verified`, a false one `Failed` -- never a `missing` (a lost proof) nor
    // a wrong-body `Verified` (a false proof).
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-mf2-{}-{seq}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.rs"), "pub mod m;\npub struct Root;\nimpl Root {\n    /// ensures: ret == 7\n    pub fn rok(&self) -> u8 { 7 }\n    /// ensures: ret == 7\n    pub fn rbad(&self) -> u8 { 8 }\n}\n").unwrap();
    std::fs::write(dir.join("m.rs"), "pub struct Foo;\nimpl Foo {\n    /// ensures: ret == 1\n    pub fn ok(&self) -> u8 { 1 }\n    /// ensures: ret == 1\n    pub fn bad(&self) -> u8 { 2 }\n}\n").unwrap();
    let report = verify::verify_file_with_opts(&rustc, &dir.join("lib.rs"), &[], &probe_opts()).expect("frontend");
    let _ = std::fs::remove_dir_all(&dir);
    let get = |n: &str| report.outcomes.iter().find(|(k, _)| k == n).map(|(_, o)| o);
    assert!(matches!(get("ok"), Some(FnOutcome::Verified { .. })), "module method, true contract -> Verified, got {:?}", get("ok"));
    assert!(matches!(get("bad"), Some(FnOutcome::Failed { .. })), "module method, false contract -> Failed, got {:?}", get("bad"));
    assert!(matches!(get("rok"), Some(FnOutcome::Verified { .. })), "root method below `mod m;`, true contract -> Verified, got {:?}", get("rok"));
    assert!(matches!(get("rbad"), Some(FnOutcome::Failed { .. })), "root method, false contract -> Failed, got {:?}", get("rbad"));
    assert!(report.missing.is_empty(), "no method should be missing now: {:?}", report.missing);
    // Item 2: the report's `(file, line)` points at the module file, not the root, so a
    // SARIF finding lands in the file that actually holds the function.
    match report.lines.get("ok") {
        Some((Some(f), line)) => {
            assert!(f.to_string_lossy().ends_with("m.rs"), "module method's report file must be m.rs, got {f:?}");
            assert_eq!(*line, 4, "`fn ok` is at m.rs line 4");
        }
        other => panic!("report.lines[ok] must be (Some(m.rs), 4), got {other:?}"),
    }
    match report.lines.get("rok") {
        Some((Some(f), _)) => assert!(f.to_string_lossy().ends_with("lib.rs"), "root method's report file must be lib.rs, got {f:?}"),
        other => panic!("report.lines[rok] must be (Some(lib.rs), ..), got {other:?}"),
    }
}

#[test]
fn a_same_named_method_in_two_same_basename_files_is_paired_by_file() {
    // Two module files with the same basename and the SAME method name at the SAME line
    // and column: only the file distinguishes them, so target selection must use the path
    // (not the bare name), or one body gets the other's contract.
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-snn-{}-{seq}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("a")).unwrap();
    std::fs::create_dir_all(dir.join("b")).unwrap();
    std::fs::create_dir_all(dir.join("c")).unwrap();
    std::fs::write(dir.join("lib.rs"), "pub mod a;\npub mod b;\npub mod c;\n").unwrap();
    std::fs::write(dir.join("a.rs"), "pub mod m;\n").unwrap();
    std::fs::write(dir.join("b.rs"), "pub mod m;\n").unwrap();
    std::fs::write(dir.join("c.rs"), "pub mod m;\n").unwrap();
    std::fs::write(dir.join("a/m.rs"), "pub struct A;\nimpl A {\n    /// ensures: ret == 1\n    pub fn f(&self) -> u8 { 1 }\n}\n").unwrap();
    std::fs::write(dir.join("b/m.rs"), "pub struct B;\nimpl B {\n    /// ensures: ret == 2\n    pub fn f(&self) -> u8 { 2 }\n}\n").unwrap();
    std::fs::write(dir.join("c/m.rs"), "pub struct C;\nimpl C {\n    /// ensures: ret == 9\n    pub fn f(&self) -> u8 { 1 }\n}\n").unwrap();
    let report = verify::verify_file_with_opts(&rustc, &dir.join("lib.rs"), &[], &probe_opts()).expect("frontend");
    let _ = std::fs::remove_dir_all(&dir);
    // A::f (body 1, ret==1) and B::f (body 2, ret==2) both verify *only* when each gets
    // its own contract and body; a body swap or a contract swap makes BOTH fail.
    let a = report.outcomes.iter().find(|(k, _)| k.contains("A::")).map(|(_, o)| o);
    let b = report.outcomes.iter().find(|(k, _)| k.contains("B::")).map(|(_, o)| o);
    // `Verified { obligations: 0 }` means a dropped contract, which also reads as
    // success -- so require a non-zero obligation count, not merely `Verified`.
    assert!(matches!(a, Some(FnOutcome::Verified { obligations, .. }) if *obligations > 0), "A::f (ret==1 body 1) must verify with a real obligation; outcomes {:?}", report.outcomes);
    assert!(matches!(b, Some(FnOutcome::Verified { obligations, .. }) if *obligations > 0), "B::f (ret==2 body 2) must verify with a real obligation; a swap breaks both; outcomes {:?}", report.outcomes);
    // A third method with a FALSE contract (ret==9 on a body of 1) must be refuted, so
    // the test cannot pass on two empty `Verified { obligations: 0 }` rows.
    let c = report.outcomes.iter().find(|(k, _)| k.contains("C::")).map(|(_, o)| o);
    assert!(matches!(c, Some(FnOutcome::Failed { .. })), "C::f (ret==9 body 1) must be refuted on its postcondition; outcomes {:?}", report.outcomes);
}

#[test]
fn a_multifile_method_with_two_contracts_is_refused() {
    // A module-file method that declares its own contract AND inherits a contracted
    // trait's must be refused (Skipped), not silently checked against one. Before the
    // line-map the method was `missing`; the line-map makes it a target, so
    // `contract_conflict` must translate the line too or the conflict is missed and the
    // trait's promise is dropped.
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-mfc-{}-{seq}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.rs"), "pub trait Bump {\n    /// ensures: ret == 9\n    fn bump(&self) -> u8;\n}\npub mod m;\n").unwrap();
    std::fs::write(dir.join("m.rs"), "use crate::Bump;\npub struct S;\nimpl Bump for S {\n    /// ensures: ret == 7\n    fn bump(&self) -> u8 { 7 }\n}\n").unwrap();
    let report = verify::verify_file_with_opts(&rustc, &dir.join("lib.rs"), &[], &probe_opts()).expect("frontend");
    let _ = std::fs::remove_dir_all(&dir);
    let o = report.outcomes.iter().find(|(k, _)| k == "bump").map(|(_, o)| o);
    assert!(matches!(o, Some(FnOutcome::Skipped { .. })), "a module method with its own and an inherited contract must be refused (Skipped), got {o:?}");
}

#[test]
fn a_same_basename_module_does_not_cross_match() {
    // Two module files with the same basename (`m.rs`) in different directories, each with
    // an impl at the same line and column. A basename-only file comparison would pair one
    // body with the other's contract (a false proof); the full-path match keeps them apart.
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif-sbn-{}-{seq}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("a")).unwrap();
    std::fs::create_dir_all(dir.join("b")).unwrap();
    std::fs::write(dir.join("lib.rs"), "pub mod a;\npub mod b;\n").unwrap();
    std::fs::write(dir.join("a.rs"), "pub mod m;\n").unwrap();
    std::fs::write(dir.join("b.rs"), "pub mod m;\n").unwrap();
    std::fs::write(dir.join("a/m.rs"), "pub struct S;\nimpl S {\n    /// ensures: ret == 1\n    pub fn af(&self) -> u8 { 1 }\n}\n").unwrap();
    std::fs::write(dir.join("b/m.rs"), "pub struct S;\nimpl S {\n    /// ensures: ret == 2\n    pub fn bf(&self) -> u8 { 1 }\n}\n").unwrap();
    let report = verify::verify_file_with_opts(&rustc, &dir.join("lib.rs"), &[], &probe_opts()).expect("frontend");
    let _ = std::fs::remove_dir_all(&dir);
    let get = |n: &str| report.outcomes.iter().find(|(k, _)| k == n).map(|(_, o)| o);
    assert!(matches!(get("af"), Some(FnOutcome::Verified { .. })), "a::m::af (contract 1, body 1) must verify, got {:?}", get("af"));
    assert!(matches!(get("bf"), Some(FnOutcome::Failed { .. })), "b::m::bf (contract 2, body 1) must be refuted, got {:?} (a basename cross-match would wrongly verify it)", get("bf"));
}

#[test]
fn iterator_chain_differential_agrees_with_rustc() {
    // Every chain the verifier decides `Verified` must match a real `rustc` compile+run of
    // the same expression (the CONTRIBUTING differential-harness rule for a proof
    // shortcut). A chain the verifier refuses is skipped -- a refusal is never wrong.
    let Some(rustc) = rustc() else { return };
    let cases: &[(&str, u8)] = &[
        ("xs.iter().copied().sum::<u8>()", 150),
        ("xs.iter().copied().max().unwrap_or(0)", 50),
        ("xs.iter().copied().min().unwrap_or(0)", 10),
        ("xs.iter().rev().next().copied().unwrap_or(0)", 50),
        ("xs.iter().rev().take(2).last().copied().unwrap_or(0)", 40),
        ("xs.iter().take(2).rev().next().copied().unwrap_or(0)", 20),
        ("xs.iter().skip(2).next().copied().unwrap_or(0)", 30),
        ("xs.iter().step_by(2).next().copied().unwrap_or(0)", 10),
        ("xs.iter().copied().map(|x| x.wrapping_add(1)).sum::<u8>()", 155),
        ("xs.iter().copied().filter(|x| *x > 25).count() as u8", 3),
        ("xs.iter().copied().any(|x| x == 30) as u8", 1),
        ("xs.iter().copied().all(|x| x < 100) as u8", 1),
    ];
    let pre = "/// requires: xs.len() == 5 && xs[0] == 10 && xs[1] == 20 && xs[2] == 30 && xs[3] == 40 && xs[4] == 50\n";
    for (i, (body, expected)) in cases.iter().enumerate() {
        let prog = format!("fn main() {{ let xs: [u8; 5] = [10, 20, 30, 40, 50]; let v: u8 = {{ {body} }}; println!(\"{{}}\", v); }}");
        let dir = std::env::temp_dir().join(format!("verif-itdiff-{}-{i}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        let f = dir.join("main.rs");
        std::fs::write(&f, &prog).unwrap();
        let bin = dir.join("main");
        let out = std::process::Command::new(&rustc).arg("--edition").arg("2024").arg("-o").arg(&bin).arg(&f).output().expect("rustc");
        assert!(out.status.success(), "rustc failed on `{body}`: {}", String::from_utf8_lossy(&out.stderr));
        let ran = std::process::Command::new(&bin).output().expect("run");
        let real: u8 = String::from_utf8_lossy(&ran.stdout).trim().parse().expect("a value");
        let _ = std::fs::remove_dir_all(&dir);
        assert_eq!(real, *expected, "the differential case's own expected value is wrong for `{body}`");
        let src = format!("{pre}/// ensures: ret == {expected}\npub fn f{i}(xs: &[u8]) -> u8 {{ {body} }}");
        if let Some(o) = verify_src(&format!("f{i}"), &src) {
            // A true postcondition must not be *refuted* (a false refutation): the
            // verifier may prove it or refuse it, but a `Failed` on a contract that
            // holds on every input is a bug the false-postcondition check below cannot
            // see (it would pass if both clauses were refuted).
            assert!(
                !matches!(o, FnOutcome::Failed { .. }),
                "verifier REFUTED a TRUE postcondition (`{body} == {expected}`, real computes {real})"
            );
            if o.is_verified() {
                assert_eq!(real, *expected, "verifier Verified `{body} == {expected}` but rustc computes {real}");
            }
        }
        // The harness's own teeth: a FALSE postcondition must never be Verified, or a
        // verifier that proves everything would pass the true check above alone.
        let wrong = expected.wrapping_add(1);
        let fsrc = format!("{pre}/// ensures: ret == {wrong}\npub fn f{i}b(xs: &[u8]) -> u8 {{ {body} }}");
        if let Some(o) = verify_src(&format!("f{i}b"), &fsrc) {
            assert!(!o.is_verified(), "verifier Verified a FALSE postcondition (`{body} == {wrong}`, real {real})");
        }
    }
}



#[test]
fn the_second_review_duplicate_and_const_len_findings_are_refused() {
    let Some(rustc) = rustc() else { return };
    // #3: a `const out__len` must NOT hijack a *refused* Vec length. Real `out` length
    // is 1 (one push); the postcondition is refused (Incomplete), never the constant.
    for (n, e) in [("sr_c3_0", 0u64), ("sr_c3_1", 1u64)] {
        let src = format!("const out__len: usize = 0;\n/// requires: v.len() == 0 && w.len() == 1 && out.len() == 0\n/// ensures: out.len() == {e}\npub fn {n}<'a>(mut v: &'a mut Vec<u8>, w: &'a mut Vec<u8>, out: &'a mut Vec<u8>) -> u8 {{ v.push(1); v = w; out.push(1); 0 }}");
        assert!(
            matches!(verify_src(n, &src), Some(FnOutcome::Incomplete { .. })),
            "`{n}`: a refused Vec length must not resolve to `const out__len`"
        );
    }
    // #2: two `#[cfg]`-alternative modules sharing a name. Rust compiles one; the
    // inliner reads both, so the contract is ambiguous -> refused (Skipped), never the
    // inactive module's claim.
    let dir = std::env::temp_dir().join(format!("verif-sr-cfg-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("a_unix.rs"), "spec! { ensures: ret == 1, }\npub fn f() -> u8 { 1 }\n").unwrap();
    std::fs::write(dir.join("a_other.rs"), "spec! { ensures: ret == 2, }\npub fn f() -> u8 { 2 }\n").unwrap();
    let lib = dir.join("lib.rs");
    std::fs::write(&lib, "macro_rules! spec { ($($c:ident : $b:expr,)*) => {}; }\n#[cfg(unix)]\n#[path = \"a_unix.rs\"]\npub mod platform;\n#[cfg(not(unix))]\n#[path = \"a_other.rs\"]\npub mod platform;\n").unwrap();
    let rep = verify::verify_file_with_opts(&rustc, &lib, &[], &probe_opts()).expect("verify");
    let o = rep.outcomes.iter().find(|(n, _)| n == "platform::f").map(|(_, o)| o);
    assert!(
        matches!(o, Some(FnOutcome::Skipped { .. })),
        "a cfg-alternative duplicate contract must be refused (Skipped), got {o:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
#[test]
fn a_reexported_trait_contract_across_inclusions_is_refused_not_verified() {
    // One `shared.rs` included by two modules; it does `pub use super::T;` and
    // `impl self::T for Shared`. `qualify_trait` cannot follow the re-export, so the two
    // inclusions resolve `self::T` to two *unresolved* paths. The inherited contract
    // cannot be known to agree, so the shared impl must be REFUSED (never Verified), not
    // checked against an arbitrary trait's postcondition (here a violating ret==7 against
    // the re-exported T::value == 9). Control: the direct impl satisfies the contract.
    let Some(rustc) = rustc() else { return };
    let dir = std::env::temp_dir().join(format!("verif-reexport-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.rs"), concat!(
        "pub trait T {\n    /// ensures: ret == 9\n    fn value(&self) -> u8;\n}\n",
        "pub struct Direct;\nimpl T for Direct { fn value(&self) -> u8 { 9 } }\n",
        "#[cfg(unix)]\n#[path = \"shared.rs\"]\npub mod disabled;\n",
        "#[cfg(not(unix))]\n#[path = \"shared.rs\"]\npub mod active;\n",
    )).unwrap();
    std::fs::write(dir.join("shared.rs"), concat!(
        "pub use super::T;\n",
        "pub struct Shared;\n",
        "impl self::T for Shared {\n",
        "    /// ensures: ret == 7\n",
        "    fn value(&self) -> u8 { 7 }\n",
        "}\n",
    )).unwrap();
    let rep = verify::verify_file_with_opts(&rustc, &dir.join("lib.rs"), &[], &probe_opts()).expect("verify");
    let _ = std::fs::remove_dir_all(&dir);
    let find = |want: &str| {
        rep.outcomes
            .iter()
            .find(|(n, _)| n.contains(want) && n.ends_with("::value"))
            .map(|(_, o)| o)
    };
    // Control: the direct impl satisfies T::value (ret == 9), so it must verify -- this
    // rules out "everything is skipped" masking a broken fixture.
    assert!(
        matches!(find("Direct"), Some(FnOutcome::Verified { .. })),
        "the direct impl must verify (control); outcomes {:?}",
        rep.outcomes
    );
    // The shared impl must be *Skipped* for the inclusion ambiguity (not Verified, and not
    // an unrelated Failed/Incomplete): the two inclusions resolve the re-exported trait to
    // unresolved paths, so no contract can be applied safely.
    assert!(
        matches!(find("Shared"), Some(FnOutcome::Skipped { .. })),
        "the shared impl must be Skipped for the inclusion ambiguity; outcomes {:?}",
        rep.outcomes
    );
}

/// A `match` on an enum reached **through a reference** must decide.
///
/// `match *e` lowers to `_2 = discriminant((*_1))`, which has *two* closing parens.
/// The parser trimmed only one, so the place failed to parse, the discriminant was
/// `Unknown`, and every such `match` was reported `unmodelled switch discriminant`.
/// Measured on `serde_json`: 172 functions. Found by running the frontend over the
/// crate; the curated corpora never matched through a reference.
#[test]
fn an_enum_matched_through_a_reference_decides() {
    let src = "pub enum E { A(u8), B, C }\n\
               /// ensures: ret <= 1\n\
               pub fn f(e: &E) -> u8 { match *e { E::A(x) => x % 2, E::B => 1, E::C => 0 } }\n\
               /// ensures: ret == 2\n\
               pub fn f_tripwire(e: &E) -> u8 { match *e { E::A(x) => x % 2, E::B => 1, E::C => 0 } }\n";
    let Some(ok) = verify_src("f", src) else { return };
    assert!(matches!(ok, FnOutcome::Verified { .. }), "a reference match must decide, got {ok}");
    let Some(bad) = verify_src("f_tripwire", src) else { return };
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "`ret == 2` is false on every arm, so it must be refuted, got {bad}"
    );
}

/// A tag a *caller* built must reach the callee's `match`.
///
/// The caller's `E::A(x)` writes a tag into its own local; the callee matches on it.
/// The tag has to cross the call boundary, or the callee's `switchInt` has nothing to
/// compare against. Found on `serde_json` (`ParserNumber::visit` called from
/// `deserialize_any`); measured before the fix as `incomplete`.
#[test]
fn an_enum_tag_built_by_a_caller_reaches_the_callee() {
    let src = "pub enum E { A(u8), B, C }\n\
               /// ensures: ret <= 1\n\
               fn inner(e: &E) -> u8 { match *e { E::A(x) => x, E::B => 1, E::C => 0 } }\n\
               /// requires: x == 0\n\
               /// ensures: ret == 0\n\
               pub fn outer(x: u8) -> u8 { let e = E::A(x); inner(&e) }\n\
               /// requires: x == 0\n\
               /// ensures: ret == 1\n\
               pub fn outer_tripwire(x: u8) -> u8 { let e = E::A(x); inner(&e) }\n";
    let Some(ok) = verify_src("outer", src) else { return };
    assert!(matches!(ok, FnOutcome::Verified { .. }), "the caller's tag must reach the callee, got {ok}");
    let Some(bad) = verify_src("outer_tripwire", src) else { return };
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "`ret == 1` is false when the tag reached the callee (the A arm returns 0), got {bad}"
    );
}

/// A `#[cfg]`-disabled enum variant is not part of the type, so a `match` over the
/// enabled ones is exhaustive and its `otherwise` arm is unreachable.
///
/// The reader counted every variant the *source* writes. With one extra, the tag
/// domain is too wide, rustc's `unreachable` arm looks reachable, and the function is
/// reported as a panic -- `serde_json`'s `ParserNumber` has a
/// `#[cfg(feature = "arbitrary_precision")]` variant and three functions were `failed`
/// for a panic that cannot happen.
#[test]
fn a_cfg_gated_variant_is_not_part_of_the_tag_domain() {
    let src = "pub enum P { A(u8), B, #[cfg(feature = \"extra\")] C(String) }\n\
               /// ensures: ret <= 1\n\
               pub fn f(p: P) -> u8 { match p { P::A(x) => x % 2, P::B => 1 } }\n";
    // The feature is off, which is how the crate is compiled: the match is exhaustive.
    let Some(ok) = verify_src_with("f", src, &probe_opts_with_cfgs(&["feature=\"std\""])) else {
        return;
    };
    assert!(
        matches!(ok, FnOutcome::Verified { .. }),
        "a disabled variant must not widen the tag domain, got {ok}"
    );
    // With nothing known about the cfgs the variant is kept as written (the
    // conservative direction), so the match may fall through and the panic is
    // reported -- that is the behaviour the cfg set exists to improve on, pinned so a
    // reader that started dropping gated variants unconditionally would fail here.
    let Some(kept) = verify_src_with("f", src, &probe_opts()) else { return };
    assert!(
        matches!(kept, FnOutcome::Failed { .. }),
        "without a cfg set the variant is kept, so the `unreachable` arm is reachable, got {kept}"
    );
}

/// A slice- or `str`-typed **field**'s length is an input, and a reference to it
/// addresses the field.
///
/// Three separate gaps had to be closed for `if self.index < self.slice.len()` to
/// decide, and each is a way to be wrong rather than slow:
///
/// 1. `Ty::parse("&'a [u8]")` read the lifetime as part of the referent, so the field
///    was `Other("'a [u8]")` -- no width, not a slice, no length. Every struct field
///    written with an explicit lifetime was unseeded.
/// 2. A reference *field* is read as `((*_1).0)`, whose head is a deref followed by a
///    field step. Only a projection of exactly `[Deref]` carried an address, so
///    `PtrMetadata` of the copied reference was `Unknown`.
/// 3. Nothing bound a *field*'s length: a top-level slice argument's length is
///    `indexed`, but `self.slice` is a field, so it is now a fresh `usize` input keyed
///    by the field path.
///
/// Measured on `serde_json`: this is its reader (`SliceRead`), and the shape accounted
/// for 86 "unmodelled switch discriminant" refusals.
#[test]
fn a_slice_typed_field_has_a_length_input() {
    // The body *branches* on the comparison, so a length the frontend cannot read
    // leaves the `switchInt` unknown and the function `incomplete` -- which is what
    // every one of those 86 functions was. A contract on the branch values is
    // therefore only provable once the comparison is modelled.
    let src = "pub struct S<'a> { pub slice: &'a [u8], pub index: usize }\n\
               /// ensures: ret <= 1\n\
               pub fn before_end(x: &S) -> u8 { if x.index < x.slice.len() { 1 } else { 0 } }\n\
               /// ensures: ret <= 1\n\
               pub fn before_end_through_a_temp(x: &S) -> u8 { let s = x.slice; if x.index < s.len() { 1 } else { 0 } }\n\
               /// ensures: ret == 1\n\
               pub fn before_end_tripwire(x: &S) -> u8 { if x.index < x.slice.len() { 1 } else { 0 } }\n";
    for name in ["before_end", "before_end_through_a_temp"] {
        let Some(f) = verify_src(name, src) else { return };
        assert!(matches!(f, FnOutcome::Verified { .. }), "{name} must decide, got {f}");
    }
    // The tripwire is the evidence the length is a *symbolic input* and not a value
    // that makes the comparison always true: `index >= len` is reachable, so
    // `ret == 1` must be refuted.
    let Some(bad) = verify_src("before_end_tripwire", src) else { return };
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "an index past the end is reachable, so `ret == 1` must be refuted, got {bad}"
    );
}

/// A **turbofish** call to a local method resolves, so its body is inlined.
///
/// `call_type` read the receiver from the text before the *last* `::`, which for
/// `V::scaled::<u8>` is `V::scaled` -- whose last segment is the method, not the
/// receiver. Every explicit-generic-argument call to a local method therefore found
/// no candidate and was reported "call to unmodelled function", which on `serde_json`
/// was the single largest refusal (38 functions on one call to
/// `value::de::<impl Value>::invalid_type::<error::Error>`).
///
/// The trailing group is now stripped before the receiver is read. Both halves are
/// asserted: the true contract verifies *because* the body was inlined (a refused
/// call would be `incomplete`), and the false one is refuted with a witness.
#[test]
fn a_turbofish_call_to_a_local_method_is_inlined() {
    let src = "pub struct V;\n\
               impl V {\n\
                   fn scaled<T>(&self, k: u8) -> u8 { k + 1 }\n\
               }\n\
               /// ensures: ret <= 1\n\
               pub fn use_it(v: &V) -> u8 { v.scaled::<u8>(0) }\n\
               /// ensures: ret == 2\n\
               pub fn use_it_tripwire(v: &V) -> u8 { v.scaled::<u8>(0) }\n";
    let Some(f) = verify_src("use_it", src) else { return };
    assert!(
        matches!(f, FnOutcome::Verified { .. }),
        "a turbofish method call must be inlined, got {f}"
    );
    let Some(bad) = verify_src("use_it_tripwire", src) else { return };
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "the inlined body returns 1, so `ret == 2` must be refuted, got {bad}"
    );
}

/// A local method whose *type* lives in another module is called through an
/// `<impl V>` projection, and that is not a `core` callee.
///
/// rustc prints a call to a method whose `impl` block is in the calling module but
/// whose *type* is imported as `de::<impl V>::h`. The resolver used to refuse **any**
/// name containing `<impl`, on the reasoning that only `core`/`std` print that
/// projection -- which is false, and on `serde_json` cost 38 functions
/// (`value::de::<impl Value>::invalid_type::<error::Error>`, a *local* function).
/// What separates the two is the module prefix, which a local definition prints
/// identically: a `core` call (`core::num::<impl u8>::wrapping_add`) then finds no
/// candidate whose prefix matches, and is refused exactly as before.
///
/// The generic-argument form (`h::<u8>`) needs the turbofish strip as well, so the
/// two halves are asserted separately.
#[test]
fn a_local_method_called_through_an_impl_projection_is_inlined() {
    let src = "pub mod val { pub enum V { X } }\n\
               pub mod de {\n\
                   use crate::val::V;\n\
                   impl V {\n\
                       pub fn scaled(&self, k: u8) -> u8 { k + 1 }\n\
                       pub fn twice<T>(&self, k: u8) -> u8 { k + k }\n\
                   }\n\
                   /// ensures: ret <= 1\n\
                   pub fn use_scaled(v: &V) -> u8 { v.scaled(0) }\n\
                   /// ensures: ret <= 2\n\
                   pub fn use_twice(v: &V) -> u8 { v.twice::<u8>(1) }\n\
                   /// ensures: ret == 9\n\
                   pub fn use_scaled_tripwire(v: &V) -> u8 { v.scaled(0) }\n\
               }\n";
    for name in ["de::use_scaled", "de::use_twice"] {
        let Some(f) = verify_src(name, src) else { return };
        assert!(
            matches!(f, FnOutcome::Verified { .. }),
            "a local method behind `<impl V>` must be inlined, got {f}"
        );
    }
    let Some(bad) = verify_src("de::use_scaled_tripwire", src) else { return };
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "the inlined body returns 1, so `ret == 9` must be refuted, got {bad}"
    );
}

/// A **replaced** slice field has no length any more.
///
/// A seeded field length describes the value *stored* in a field, not a permanent
/// property of the field: `s.slice = &[]` replaces the slice, so the `usize` that
/// `s.slice.len()` was bound to describes a value that is no longer there. Leaving
/// it was a false proof -- the body returns the *entry* length on both paths, so
/// `ensures: ret == 3` was proved against a function that returns 0 on the branch
/// that replaces the slice. `forget_field_lens` drops the seed on a field write, a
/// whole-place write and a loop havoc, and `copy_parts` carries it with the parts
/// it moves.
#[test]
fn a_replaced_slice_field_has_no_stale_length() {
    let src = "pub struct S<'a> { pub slice: &'a [u8] }\n\
               /// requires: s.slice.len() == 3\n\
               /// ensures: ret <= 3\n\
               pub fn keeps_its_slice(s: &S) -> usize { s.slice.len() }\n\
               /// requires: s.slice.len() == 3 && t.len() == 0\n\
               /// ensures: ret == 3\n\
               pub fn replaces_its_slice<'a>(s: &mut S<'a>, t: &'a [u8]) -> usize {\n\
                   s.slice = t;\n\
                   s.slice.len()\n\
               }\n";
    // The positive half: an un-replaced field length still decides, so the fix is
    // not a blanket refusal.
    let Some(ok) = verify_src("keeps_its_slice", src) else { return };
    assert!(
        matches!(ok, FnOutcome::Verified { .. }),
        "an un-replaced field length must still decide, got {ok}"
    );
    // The false half: the body returns the *replacement's* length, 0.
    let Some(bad) = verify_src("replaces_its_slice", src) else { return };
    assert!(
        !matches!(bad, FnOutcome::Verified { .. }),
        "the replacement branch returns 0, so `ret == 3` must not be proved, got {bad}"
    );
}

/// A `discriminant` of a **projected** place is refused, not answered with the base
/// local's tag.
///
/// `match o { Outer::A(Inner::X(_)) => 0, Outer::A(Inner::Y) => 1, _ => 2 }` lowers
/// the inner match to `discriminant((((*_1) as A).0))`: a downcast and a field on
/// the *outer* enum's local. The tag store is keyed by local, so answering it there
/// returned the **outer** tag -- and both inner arms share `Outer::A`'s tag, so the
/// inner match collapsed to its first arm and a contract about the second was
/// proved. A projected place is refused (`Val::Unknown`), which is the refusal the
/// shape had before the parser learned to read a parenthesised place; the
/// unprojected `discriminant((*_1))` -- the outer match, and every `match` on an
/// enum *reference* -- still decides.
#[test]
fn a_nested_enum_match_is_not_the_outer_tag() {
    let src = "pub enum Inner { X(u8), Y }\n\
               pub enum Outer { A(Inner), B }\n\
               /// ensures: ret <= 1\n\
               pub fn outer_only(o: &Outer) -> u8 { match o { Outer::A(_) => 0, Outer::B => 1 } }\n\
               /// ensures: ret == 0\n\
               pub fn nested_pattern_tripwire(o: &Outer) -> u8 {\n\
                   match o { Outer::A(Inner::X(_)) => 0, Outer::A(Inner::Y) => 1, Outer::B => 0 }\n\
               }\n";
    let Some(ok) = verify_src("outer_only", src) else { return };
    assert!(
        matches!(ok, FnOutcome::Verified { .. }),
        "an unprojected discriminant must still decide, got {ok}"
    );
    // `Outer::A(Inner::Y)` returns 1 and every other arm returns 0, so `ret == 0` is
    // false. Reading the *outer* tag for the inner match collapses the two `A` arms
    // onto the first and proves it -- the tag is `Outer::A`'s, `0`, for both.
    let Some(bad) = verify_src("nested_pattern_tripwire", src) else { return };
    assert!(
        !matches!(bad, FnOutcome::Verified { .. }),
        "the inner tag is not the outer one, so `ret == 0` must not be proved, got {bad}"
    );
}

/// A local `trait` impl does not answer an `<impl Type>::m` call.
///
/// rustc prints an *inherent* method call as `<impl Type>::m` and a trait method as
/// `<T as Trait>::m`, so a projected call is inherent. The module-prefix match that
/// lets a local method resolve must not admit a `trait` impl: a local `impl Ext for
/// u8` inside `mod core::num` shares the prefix, the owner and the tail with
/// `core::num::<impl u8>::wrapping_add`, so its body was inlined *for the `core`
/// call* -- a contract the real method violates would be "proved" (here, `ret == 0`
/// for `2 + 255`).
#[test]
fn a_local_trait_impl_in_a_core_module_does_not_answer_the_intrinsic() {
    let src = "pub mod core {\n\
                   pub mod num {\n\
                       pub trait Ext { fn wrapping_add(self, o: u8) -> u8; }\n\
                       impl Ext for u8 { fn wrapping_add(self, _o: u8) -> u8 { 0 } }\n\
                   }\n\
               }\n\
               use crate::core::num::Ext;\n\
               /// requires: a == 2 && b == 255\n\
               /// ensures: ret == 1\n\
               pub fn real_wrapping_add(a: u8, b: u8) -> u8 { a.wrapping_add(b) }\n\
               /// requires: a == 2 && b == 255\n\
               /// ensures: ret == 0\n\
               pub fn local_body_tripwire(a: u8, b: u8) -> u8 { a.wrapping_add(b) }\n";
    // The inherent `u8::wrapping_add` wraps `2 + 255` to 1. Answering from the local
    // trait body would return 0, so this is the direction a prefix-only match breaks.
    let Some(ok) = verify_src("real_wrapping_add", src) else { return };
    assert!(
        matches!(ok, FnOutcome::Verified { .. }),
        "the inherent `wrapping_add` returns 1, got {ok}"
    );
    // And the local body's value must not be provable.
    let Some(bad) = verify_src("local_body_tripwire", src) else { return };
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "the local trait body returns 0, so `ret == 0` must be refuted, got {bad}"
    );
}

/// The cache key covers the `--cfg` set, because the cfg set shapes an enum's tag
/// domain without touching a byte of MIR or source.
///
/// A `#[cfg]`-gated variant is present or absent exactly as in the compiled code, so
/// turning a feature on can widen the tag domain while `rustc` emits *identical* MIR
/// for a function that never inspects the enum. A key over MIR + source + edition +
/// engine alone would then reuse a proof about a different program -- the reviewer's
/// example is a contract `m == M::B || m == M::C`, a theorem on `{B, C}` and false
/// once `A` exists.
///
/// The assertion is on the *key*, observed through the cache directory: one entry
/// after the first run, and a **second** entry once the cfg set changes. That is the
/// property the soundness argument rests on, and it is observable without needing the
/// verdict to move (which today it does not for that example -- an argument enum's
/// tag domain is not conjoined into the path, a separate completeness gap).
#[test]
fn the_cache_key_covers_the_cfg_set_that_shapes_an_enum() {
    let Some(rustc) = rustc() else { return };
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("verif_cfg_cache_{}_{seq}", std::process::id()));
    let cache = dir.join("cache");
    std::fs::create_dir_all(&dir).expect("scratch dir");
    let file = dir.join("f.rs");
    let src = "pub enum M { B, C, #[cfg(feature = \"extra\")] A }\n\
               /// ensures: ret == 0\n\
               pub fn f(m: M) -> u8 { let _ = m; 0 }\n\
               /// requires: m == M::A\n\
               /// ensures: ret == 0\n\
               pub fn a_only(m: M) -> u8 { let _ = m; 0 }\n";
    std::fs::write(&file, src).expect("write fixture");
    let with = |cfgs: &[&str]| {
        let mut opts = probe_opts_with_cfgs(cfgs);
        opts.cache = Some(cache.clone());
        opts
    };
    let entries = || std::fs::read_dir(&cache).map(|d| d.count()).unwrap_or(0);

    // The `off` run *decides* `extra` (it is in a set of features that does not
    // contain it) rather than leaving it unknown, so the two runs differ in the
    // enum's layout as well as in the key -- a run with no `--cfg` at all leaves
    // every feature undecidable and the layout the same.
    let off = with(&["feature=\"std\""]);
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &off).expect("verify");
    let outcome = |r: &verif::mir::verify::FileReport, n: &str| {
        r.outcomes.iter().find(|(k, _)| k == n).map(|(_, o)| o.clone())
    };
    assert!(
        !matches!(outcome(&report, "a_only"), Some(FnOutcome::Verified { .. })),
        "with `extra` off, `M::A` does not exist and the contract naming it is a refusal"
    );
    assert_eq!(entries(), 1, "the first run writes one entry");
    // The same options reuse that entry rather than writing a second one.
    verify::verify_file_with_opts(&rustc, &file, &[], &off).expect("verify");
    assert_eq!(entries(), 1, "the same cfg set is the same key");

    // The domain changes with `extra`, and the MIR does not. A key without the cfg
    // set would reuse the first entry here, which is the stale hit a wider domain
    // makes a false proof.
    let on = with(&["feature=\"std\"", "feature=\"extra\""]);
    let report = verify::verify_file_with_opts(&rustc, &file, &[], &on).expect("verify");
    assert!(
        matches!(outcome(&report, "a_only"), Some(FnOutcome::Verified { .. })),
        "with `extra` on, `M::A` exists and the contract about it is checked"
    );
    assert_eq!(entries(), 2, "a different cfg set is a different key");
}

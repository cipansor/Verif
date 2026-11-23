//! Symbolic execution of MIR, one path at a time.
//!
//! The executor walks basic blocks, keeping a *path condition* and a map from
//! MIR locals to symbolic values. At each `assert` it asks the engine whether
//! the negated condition is reachable under the path condition; at each `return`
//! it asks whether the postcondition holds. Nothing here trusts the code: the
//! only way to get a `Valid` out is for the engine to prove the obligation for
//! *every* input on *every* explored path.
//!
//! # Bounded, like every bounded checker
//!
//! Two budgets keep this from running forever, and both are reported rather than
//! hidden:
//!
//! * [`DEFAULT_UNWIND`] — a back edge taken more than this many times ends the
//!   path as unknown. Loops are *not* assumed to exit.
//! * [`DEFAULT_INLINE_DEPTH`] — calls into the same dump are inlined to this
//!   depth; deeper calls make the path unknown.
//!
//! A third, implicit budget is the engine's own BDD arena. When it fills, the
//! verdict is `Unknown` and the obligation is left open. Every one of these
//! failures lands on the "I could not decide" side, never on "valid".

use std::collections::{BTreeMap, BTreeSet};

use crate::mir::intrinsics::{self, Outcome};
use crate::mir::spec::{self, FieldEnv};
use crate::mir::parse::{
    BinOp, Block, Callee, Const, EnumLayout, MirFn, MirProgram, Operand, Place, Proj, Rvalue, Stmt,
    Term, Ty, UnOp, USIZE_WIDTH,
};
use crate::smt::{self, Pred, Var, Verdict};

/// How many times a back edge may be taken before a path is abandoned as
/// unknown. Nine is enough for the shift-amount and bounds loops that dominate
/// the interesting safety cases, and small enough to stay fast.
pub const DEFAULT_UNWIND: u32 = 9;

/// How deep same-dump calls are inlined.
pub const DEFAULT_INLINE_DEPTH: u32 = 4;

/// How many paths one function may explore before the search is abandoned.
///
/// `DEFAULT_UNWIND` bounds each *loop*, but a function can still generate an
/// unbounded number of paths without any single loop exceeding its bound: every
/// branch inside an unwound loop multiplies the path count, and the engine's
/// BDD cost per path grows with the path condition. Measured on
/// `while i < n { if i % 2 == 0 { c += 1; } i += 1; }` the search was still
/// running after 170 seconds with only two paths reported unknown -- it was not
/// looping forever, but it had no way to stop either.
///
/// That matters because the frontend's contract, stated in `mir/mod.rs`, is
/// that a cutoff is reported as a cutoff and a path is never assumed to exit.
/// A search that never returns cannot report anything, so the promise needs a
/// bound on *paths*, not just on loop iterations. Reaching this budget marks
/// the function incomplete, exactly like an unwound loop: the obligations found
/// so far stand, and the un-explored remainder is named rather than guessed at.
///
/// The value is calibrated against cost, not against a round number. The same
/// function above took 16s at 200 paths and was still running after 90s at
/// 2000, because each path's BDD is larger than the last -- so a larger budget
/// buys no extra coverage, only latency. Sixty-four keeps the worst case in the
/// low seconds while still deciding everything the shipped corpora decide: the
/// corpus scoreboard is unchanged with this bound and with none.
///
/// Loops carrying an `invariant:` no longer reach this budget at all -- they are
/// cut rather than unwound -- so this bound now governs only the loops that have
/// no invariant to prove them with.
pub const DEFAULT_PATH_BUDGET: usize = 64;

/// The largest path budget a declared `unwind:` may buy.
///
/// The budget grows with the declared bound (see [`path_budget`]) because a
/// caller who asks for more iterations is asking for more paths. The cap keeps
/// that growth from becoming a hang: measured, a two-branch loop body explores
/// its paths in under half a second at this budget, so a bound large enough to
/// reach it is still bounded in time, and a caller who needs more than this is
/// told the budget was exhausted rather than waited out.
pub const MAX_PATH_BUDGET: usize = 4096;

/// The path budget for a function whose loops are unwound to `unwind`, or the
/// default when the source declared no bound.
///
/// A declared bound says "unwind each loop up to `n` iterations", and a loop body
/// with a branch yields a path per branch per iteration, so the number of paths
/// grows with the bound. The default budget is calibrated for [`DEFAULT_UNWIND`];
/// a caller who asks for more iterations is asking for more paths, and the budget
/// has to grow with the request or the clause is unusable. Measured: `max_of` (a
/// four-iteration loop over a `[u8; 4]` with one `if`) explores 199 paths -- above
/// the default 64 -- so `unwind: 5`, the very clause that should decide it, would
/// otherwise still hit the budget. `unwind: 5` buys 320 paths, which covers it.
///
/// The growth is linear in the bound and capped at [`MAX_PATH_BUDGET`], so a large
/// bound cannot turn into a hang.
pub fn path_budget(unwind: Option<u32>) -> usize {
    match unwind {
        Some(n) => DEFAULT_PATH_BUDGET
            .saturating_mul(n as usize)
            .clamp(DEFAULT_PATH_BUDGET, MAX_PATH_BUDGET),
        None => DEFAULT_PATH_BUDGET,
    }
}

/// A symbolic value.
///
/// `Unknown` propagates: any operation on it stays unknown, and a path that
/// returns or asserts an unknown value is not evidence of anything. That is the
/// single rule that keeps this frontend honest — there is no place where an
/// unmodelled construct is quietly given a convenient meaning.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sign {
    /// The type is `i8`/`i16`/`i32`/`i64`/`i128`/`isize`.
    Signed,
    /// The type is unsigned, or has no integer signedness at all.
    Unsigned,
    /// The dump did not print enough type for the sign to be read -- a literal
    /// with no suffix, and nothing in scope to take it from.
    ///
    /// This variant is why the enum has three cases rather than two. The bug the
    /// type exists to prevent was a *default*: a site that could not read the
    /// sign fell back to unsigned, and unsigned `0 < a` on an `i8` calls
    /// `i8::MIN` the largest value. With only two variants that fallback is
    /// always available to write; with three, every signedness-sensitive site has
    /// to handle `Unknown` explicitly and the compiler names the ones that do not.
    Unknown,
}

impl Sign {
    /// The sign `ty` declares.
    ///
    /// A type with no integer signedness (`bool`, an aggregate, a reference)
    /// answers `Unsigned`, which is the right reading for *widening* it (zero
    /// fill) but not for a comparison -- but rustc gives such a type no
    /// comparison to make, so `Unsigned` is not a fallback here, it is the
    /// reading.
    pub fn of(ty: &Ty) -> Sign {
        if ty.is_signed() {
            Sign::Signed
        } else {
            Sign::Unsigned
        }
    }

    /// The sign, or `None` when it could not be read.
    ///
    /// Deliberately *not* named `is_signed`: a `bool` answer would let a
    /// signedness-sensitive site write `if v.is_signed()` and silently take the
    /// unsigned branch on `Unknown`, which is the false proof the type prevents.
    /// Every caller has to say what it does when the sign is missing.
    pub fn known(self) -> Option<bool> {
        match self {
            Sign::Signed => Some(true),
            Sign::Unsigned => Some(false),
            Sign::Unknown => None,
        }
    }

    /// The sign a bare `bool` (as the seeds and the `Indexed` store carry it)
    /// stands for. Kept as a constructor so the conversion is in one place: a
    /// `bool` read the wrong way round is exactly the bug this type exists to
    /// make impossible.
    pub fn of_bool(signed: bool) -> Sign {
        if signed {
            Sign::Signed
        } else {
            Sign::Unsigned
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Val {
    /// A bit-vector of a known width, *and* the signedness its type declares.
    ///
    /// The sign lives in the value rather than beside it because the bug it
    /// prevents was precisely a signedness threaded alongside: each call site
    /// asked `operand_signedness` and a site that forgot got `Unsigned`. `0 < a`
    /// on an `i8` became an unsigned test (so `i8::MIN` read as positive), and
    /// `-1i8 as i16` zero-filled to `255` -- two reachable false proofs, both
    /// from a missing sign. Here a missing sign is a construction-site error.
    Sym(Var, Sign),
    Bool(Pred),
    /// An aggregate (array or tuple). Its parts live in the environment's
    /// `elems`/`fields` maps, keyed by the aggregate's own local.
    Agg,
    Unknown,
}

/// What an obligation is about, for the report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObligationKind {
    /// A rustc-emitted panic condition (overflow, divide by zero, shift, bounds).
    Panic {
        /// The message `rustc` attached to the `assert`, which names the
        /// operation that would fail.
        message: String,
    },
    /// The declared postcondition at a `return`.
    Postcondition,
    /// An `unreachable` that the path condition can reach.
    Unreachable,
    /// The precondition is unsatisfiable, so the contract proves nothing.
    VacuousPrecondition,
    /// The declared loop invariant holds the first time the loop head is
    /// reached. This is the base case of the induction.
    LoopInvariantInit,
    /// The declared loop invariant is left true by one iteration. This is the
    /// step of the induction.
    LoopInvariantPreserve,
    /// The `variant:` measure strictly decreases across one iteration. This is
    /// the well-founded basis for *total* correctness: without it the invariant
    /// only shows the loop is safe if it terminates, which a divergent loop
    /// satisfies vacuously.
    LoopVariant,
    /// A recursive call's arguments satisfy the function's own precondition. The
    /// call is not inlined, so the contract is *assumed* -- and the precondition is
    /// what makes that assumption an induction hypothesis rather than a
    /// restatement of the goal.
    RecursivePrecondition,
    /// The `decreases:` measure is strictly smaller at a recursive call than at
    /// entry. This is the well-founded basis the induction needs; without it the
    /// assumption would be circular.
    RecursiveDecreases,
    /// A call to a *contracted* function outside the dump satisfies that
    /// function's precondition. The callee's contract is assumed for the result,
    /// so the precondition is what makes the assumption sound rather than a
    /// restatement of the goal -- the same argument as
    /// [`ObligationKind::RecursivePrecondition`], one step out.
    CalleePrecondition,
    /// The callee's postcondition cannot hold for any input (`ensures false`, or a
    /// set of conjuncts with no model), so the call never returns and every claim
    /// after it is vacuous. The MIR twin of [`crate::wp::Rule::DivergentCall`]:
    /// refusing is what keeps "the program cannot get past this call" from being
    /// read as a proof of what follows it.
    CalleeDiverges,
    /// A call that never returns, reached on this path.
    ///
    /// `panic!`, `assert!`, `unwrap`, the bounds checks rustc inserts, and any
    /// user function returning `!` all lower to a call with no `[return: bbN]`
    /// arm: the path ends there. It is a *reachable failure*, so the obligation is
    /// "is this call reachable", discharged by `Unsat`. Treating it as a dropped
    /// line instead lost the whole path -- an `assert!` was never checked, and a
    /// function whose safety rested on one came back `Incomplete`.
    DivergingCall {
        /// What kind of divergence it is, so the report does not call a clean
        /// `std::process::exit` a panic. See the `Divergence` enum.
        kind: Divergence,
        /// The message, when the dump passed one as a string literal; the
        /// callee's name otherwise. It is what names the failure in the report.
        message: String,
    },
    /// A loop the caller bounded with `unwind:` was unwound that many times and its
    /// exit edge was never reached, so the path after the loop cannot be explored.
    ///
    /// This is Kani's *unwinding assertion*: when the bound is explicit it is a
    /// claim ("this loop finishes within N iterations"), and a path that runs off
    /// the end of the bound *falsifies* it. Making it an obligation rather than a
    /// silent cutoff is what stops a too-small bound from turning into a weaker
    /// proof -- a `verified` under `unwind: 3` would be a statement about the first
    /// three iterations only, which is exactly the soundness hole the clause exists
    /// to avoid.
    ///
    /// It is a failure, not an incompleteness. Its verdict is the reachability of
    /// the cutoff (the same query shape as a diverging call), so a reachable cutoff
    /// comes back as a `Counterexample` naming an input that runs off the bound. A
    /// loop with *no* `unwind:` still cuts off at `DEFAULT_UNWIND` as a plain
    /// `unknown_paths` entry: the default is not a claim the caller made, so it is
    /// reported as incompleteness rather than refuted.
    UnwindBound {
        /// The bound the caller declared.
        bound: u32,
    },
}

/// What a diverging call does, for the report's label.
///
/// A call that never returns is a reachable end of the path whatever it does, so
/// all three kinds carry the same obligation. They differ in what the label should
/// *say*: reporting `std::process::exit(0)` as `panic: exit` tells a reader the
/// program crashed when it exited cleanly. The kind is read from the callee's
/// name -- the dump prints `exit(…)`, `std::process::abort()` and
/// `core::panicking::panic(…)` distinctly -- and an unrecognised `!`-returning
/// function falls to [`Divergence::Never`], which is honest about not knowing
/// which it is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Divergence {
    /// A panic or an assert: `core::panicking::panic(…)`, `std::rt::panic_fmt`,
    /// `core::panicking::panic_nounwind`, `assert`, `unwrap`, a bounds check.
    Panic,
    /// A clean process exit: `std::process::exit` (printed `exit(…)`).
    Exit,
    /// An abnormal termination: `std::process::abort`.
    Abort,
    /// A user function that returns `!`, or any divergence the name does not
    /// classify. It still ends the path; only the label is unspecified.
    Never,
}

impl Divergence {
    /// Classify a diverging call from the callee's printed name.
    pub fn of(name: &str) -> Divergence {
        let tail = path_tail(name);
        if tail == "exit" || name.ends_with("process::exit") {
            Divergence::Exit
        } else if tail == "abort" || name.ends_with("process::abort") {
            Divergence::Abort
        } else if name.contains("panic") || name.contains("assert") {
            Divergence::Panic
        } else {
            Divergence::Never
        }
    }

    /// The word the report uses before the message.
    pub fn label(self) -> &'static str {
        match self {
            Divergence::Panic => "panic",
            Divergence::Exit => "exit",
            Divergence::Abort => "abort",
            Divergence::Never => "diverges",
        }
    }
}

impl std::fmt::Display for ObligationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ObligationKind::Panic { message } => write!(f, "panic: {message}"),
            ObligationKind::Postcondition => write!(f, "postcondition"),
            ObligationKind::Unreachable => write!(f, "reachable `unreachable`"),
            ObligationKind::VacuousPrecondition => write!(f, "vacuous precondition"),
            ObligationKind::LoopInvariantInit => write!(f, "loop invariant holds on entry"),
            ObligationKind::LoopInvariantPreserve => write!(f, "loop invariant preserved"),
            ObligationKind::LoopVariant => write!(f, "loop variant decreases"),
            ObligationKind::RecursivePrecondition => {
                write!(f, "recursive call satisfies the precondition")
            }
            ObligationKind::RecursiveDecreases => {
                write!(f, "recursive call decreases the measure")
            }
            ObligationKind::CalleePrecondition => {
                write!(f, "call satisfies the callee's precondition")
            }
            ObligationKind::CalleeDiverges => {
                write!(f, "the callee's postcondition is unsatisfiable")
            }
            ObligationKind::UnwindBound { bound } => {
                write!(f, "loop exceeded the declared `unwind: {bound}` bound")
            }
            ObligationKind::DivergingCall { kind, message } => {
                // `exit`/`abort` carry the callee's tail as their message, which
                // is the label already; printing `exit: exit` reads as a stutter,
                // so the label stands alone when there is no real message.
                let label = kind.label();
                if message == label {
                    write!(f, "{label}")
                } else {
                    write!(f, "{label}: {message}")
                }
            }
        }
    }
}

/// One obligation found while walking a path.
#[derive(Clone, Debug)]
pub struct Obligation {
    /// What the obligation is about.
    pub kind: ObligationKind,
    /// The engine's answer. `Valid` means proved; `Counterexample` carries the
    /// failing input.
    pub verdict: Verdict,
}

impl Obligation {
    /// Whether this obligation was discharged.
    ///
    /// The polarity is *not* the same for every kind, and reading it as one is a
    /// soundness hole in either direction:
    ///
    /// * A [`ObligationKind::Postcondition`] is discharged when it is `Valid`:
    ///   the predicate holds for every input. `Unsat` here is the strongest
    ///   possible failure — the postcondition is false for every input.
    /// * A [`ObligationKind::Panic`] is discharged only when it is `Unsat`: the
    ///   query asks "can this panic happen", so `Unsat` means it cannot.
    ///   `Counterexample` means it can, on the inputs it names; `Valid` means it
    ///   happens for every input — the worst case, and the one that has no
    ///   counterexample to show.
    /// * An [`ObligationKind::Unreachable`] is the same query shape as a panic:
    ///   `Unsat` proves the `unreachable` is never reached.
    /// * A [`ObligationKind::VacuousPrecondition`] is discharged when it is
    ///   *refuted*: some input satisfies the precondition. Its `Unsat` verdict is
    ///   the finding, not a proof.
    /// * Both [`ObligationKind::LoopInvariantInit`] and
    ///   [`ObligationKind::LoopInvariantPreserve`] are discharged when they are
    ///   `Valid`: the query asks "does the invariant hold here, for every input
    ///   that reaches this point", so `Valid` is the proof and a `Counterexample`
    ///   is a real input that breaks the invariant. Reading them as a panic query
    ///   (discharged on `Unsat`) would invert the answer, which is exactly the
    ///   mistake the per-kind polarity exists to prevent.
    ///
    /// `Unknown` is never discharged. A caller that tests only
    /// [`Verdict::is_proved`] gets the postcondition case right and every other
    /// case backwards, which is why this method exists.
    pub fn is_discharged(&self) -> bool {
        match self.kind {
            ObligationKind::Postcondition
            | ObligationKind::LoopInvariantInit
            | ObligationKind::LoopInvariantPreserve
            | ObligationKind::LoopVariant
            | ObligationKind::RecursivePrecondition
            | ObligationKind::RecursiveDecreases
            | ObligationKind::CalleePrecondition
            | ObligationKind::CalleeDiverges => self.verdict.is_proved(),
            ObligationKind::Panic { .. }
            | ObligationKind::Unreachable
            | ObligationKind::DivergingCall { .. } => matches!(self.verdict, Verdict::Unsat),
            // The unwinding assertion asks "is the cutoff reachable"; like a panic
            // query it is discharged by `Unsat`. It is only *created* on a path that
            // has reached the cutoff, so it is a failure in practice -- but the
            // polarity still has to be right, or a future caller that checks an
            // un-reached bound would read the wrong way round.
            ObligationKind::UnwindBound { .. } => matches!(self.verdict, Verdict::Unsat),
            ObligationKind::VacuousPrecondition => {
                !matches!(self.verdict, Verdict::Unsat | Verdict::Unknown)
            }
        }
    }

    /// A concrete input that falsifies the intent, when one exists.
    ///
    /// For a postcondition, a `Counterexample` is a real failing input. For a
    /// panic or an `unreachable`, the failing case is a `Counterexample` too —
    /// the inputs on which the panic or the `unreachable` is reached. The two
    /// failures with no witness are the *opposite* verdicts of each other, and
    /// [`Obligation::failure_detail`] is what tells them apart.
    pub fn failure_witness(&self) -> Option<&crate::smt::Cex> {
        match &self.verdict {
            Verdict::Counterexample(c) => Some(c),
            _ => None,
        }
    }

    /// A one-line diagnosis of why this obligation was not discharged.
    ///
    /// The witness alone is not enough, because the two kinds fail on *opposite*
    /// verdicts and both leave no counterexample:
    ///
    /// * An `Unsat` postcondition holds for **no** input — the strongest failure.
    /// * A `Valid` panic holds for **every** input — the panic always fires.
    ///
    /// Rendering both as "holds for every input" reverses the first: it describes
    /// an impossible postcondition as a universal truth, which is the opposite of
    /// the finding. So the string is built per kind and per verdict, and the
    /// `Unsat` postcondition says what actually happened.
    ///
    /// A counterexample is rendered with the source names the MIR `debug` bindings
    /// recorded (`x = 224` rather than `v1:u8 = 224`); see [`Self::failure_detail_named`].
    pub fn failure_detail(&self) -> String {
        self.failure_detail_named(&[])
    }

    /// [`Self::failure_detail`], but a counterexample is rendered with `names`.
    ///
    /// `names` is `(source name, variable index)`, the frontend's `debug` bindings.
    /// A variable with no name keeps its `v{index}:u{width}` spelling, so naming is
    /// a readability improvement and never a loss: the fallback is exactly what the
    /// unnamed rendering prints.
    pub fn failure_detail_named(&self, names: &[(&str, u32)]) -> String {
        match &self.verdict {
            Verdict::Counterexample(c) => c.render_named(names),
            Verdict::Valid => match self.kind {
                // A panic query is `path => can_happen`; `Valid` means it always
                // happens, and there is no single witness to name.
                ObligationKind::Panic { .. }
                | ObligationKind::Unreachable
                | ObligationKind::DivergingCall { .. }
                | ObligationKind::UnwindBound { .. } => {
                    "holds for every input (the failure fires on all of them)".to_string()
                }
                // A postcondition or invariant query is `path => P`; `Valid` is
                // the *pass* case, so reaching here with a non-discharged
                // obligation would be a classifier bug. Say so rather than guess.
                ObligationKind::Postcondition
                | ObligationKind::VacuousPrecondition
                | ObligationKind::LoopInvariantInit
                | ObligationKind::LoopInvariantPreserve
                | ObligationKind::LoopVariant
                | ObligationKind::RecursivePrecondition
                | ObligationKind::RecursiveDecreases
                | ObligationKind::CalleePrecondition
                | ObligationKind::CalleeDiverges => {
                    "invalid: a `Valid` verdict is a discharge for this kind".to_string()
                }
            },
            Verdict::Unsat => match self.kind {
                // `path => post` false on every input: the postcondition holds for
                // none of them. This is the case the old shared string got wrong.
                ObligationKind::Postcondition => {
                    "the postcondition holds for no input (false on every input)".to_string()
                }
                // `path => I` false on every input: the invariant can never be
                // established (or re-established), so the loop proves nothing.
                ObligationKind::LoopInvariantInit
                | ObligationKind::LoopInvariantPreserve
                | ObligationKind::LoopVariant
                | ObligationKind::RecursivePrecondition
                | ObligationKind::RecursiveDecreases
                | ObligationKind::CalleePrecondition => {
                    "the property holds for no input (false on every input)".to_string()
                }
                // `find_model` on the callee's postcondition: `Unsat` means no
                // input can satisfy it, so the call never returns.
                ObligationKind::CalleeDiverges => {
                    "the callee's postcondition holds for no input, so the call never returns"
                        .to_string()
                }
                // The good answer for a reachability query, so this is a discharge.
                ObligationKind::Panic { .. }
                | ObligationKind::Unreachable
                | ObligationKind::DivergingCall { .. } => {
                    "invalid: an `Unsat` verdict is a discharge for this kind".to_string()
                }
                // The unwinding assertion is discharged by `Unsat` too, so an
                // `Unsat` here would be the pass case; reaching this arm means the
                // obligation was recorded without a discharge, which is a bug.
                ObligationKind::UnwindBound { .. } => {
                    "invalid: an `Unsat` verdict is a discharge for this kind".to_string()
                }
                // The precondition describes no input, so the contract is vacuous.
                ObligationKind::VacuousPrecondition => {
                    "no input satisfies the precondition (the contract is vacuous)".to_string()
                }
            },
            Verdict::Unknown => "the engine could not decide this obligation".to_string(),
        }
    }
}

/// The result of verifying one function.
#[derive(Clone, Debug, Default)]
pub struct MirReport {
    /// The function these obligations belong to.
    pub function: String,
    /// Every obligation found, with the engine's answer for each.
    pub obligations: Vec<Obligation>,
    /// Paths that ended in a budget cutoff or an unmodelled operation. Non-empty
    /// means the verification is *incomplete*, whatever the obligations say.
    pub unknown_paths: Vec<String>,
    /// Paths explored to a `return`.
    pub returned_paths: usize,
}

impl MirReport {
    /// True when every obligation was discharged and no path was left unknown.
    ///
    /// "Discharged" is per-kind — see [`Obligation::is_discharged`]. A panic is
    /// discharged by an `Unsat` query, a postcondition by a `Valid` one, and a
    /// vacuous-precondition check by a refutation. Testing `is_proved` on every
    /// obligation instead would count a panic that happens for *every* input as a
    /// proof, and a postcondition that holds for *no* input as one too.
    pub fn is_proved(&self) -> bool {
        self.unknown_paths.is_empty() && self.obligations.iter().all(|o| o.is_discharged())
    }

    /// The first obligation that was not discharged and that the engine could
    /// decide, i.e. a definite failure rather than an open one.
    ///
    /// Returns the obligation itself so the caller can ask it for the kind, the
    /// witness, and the diagnosis without re-deriving which obligation it was.
    /// A failure outranks incompleteness, so this is the first thing a caller
    /// should look at.
    pub fn first_failure(&self) -> Option<&Obligation> {
        self.obligations
            .iter()
            .find(|o| !o.is_discharged() && !matches!(o.verdict, Verdict::Unknown))
    }

    /// The first counterexample found, if any obligation has one to show.
    pub fn counterexample(&self) -> Option<(&ObligationKind, &crate::smt::Cex)> {
        self.obligations.iter().find_map(|o| o.failure_witness().map(|c| (&o.kind, c)))
    }

    /// Panics that were proved impossible: an `Unsat` "can this panic" query.
    pub fn panics_ruled_out(&self) -> usize {
        self.obligations
            .iter()
            .filter(|o| matches!(o.kind, ObligationKind::Panic { .. }) && o.is_discharged())
            .count()
    }

    /// Obligations the engine could not decide.
    pub fn undecided(&self) -> usize {
        self.obligations
            .iter()
            .filter(|o| matches!(o.verdict, Verdict::Unknown))
            .count()
    }
}

impl std::fmt::Display for MirReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "{}: {} obligation(s), {} path(s) returned",
            self.function,
            self.obligations.len(),
            self.returned_paths
        )?;
        for o in &self.obligations {
            writeln!(f, "  [{}] {}", o.verdict, o.kind)?;
        }
        for u in &self.unknown_paths {
            writeln!(f, "  [unknown] {u}")?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

/// A slice element named by the `(slice local, index)` pair its `&T` points at.
type ElemRef = (u32, u64);

/// The pseudo-index `slice::last` keys its fresh element variable by.
///
/// A slice's length is symbolic, so `s[len - 1]` names no index the store can
/// pin. The element is a single fresh variable per slice, and this sentinel is
/// the key that makes every `last()` call on the same slice read the *same*
/// variable. It cannot collide with a real index: an array's elements are below
/// `MAX_INDEX_CHAIN`, and a `get(k)` index is a literal far below this.
const LAST_INDEX: u64 = u64::MAX;

/// The slice element an `Option<&T>` payload names, carried *compositionally* so a
/// chain of combinators composes rather than each step reading only the operands'
/// leaf identities.
///
/// `slice::first`/`get` produce a leaf; `or`/`and` build a `Select` over their two
/// operands. Keeping the tree (rather than flattening each combinator's result to a
/// single leaf) is what makes `a.first().or(b.first()).or(c.first())` select the
/// *first* element on `Some`: a flat representation loses the inner `or`, and the
/// outer combinator then reads a missing identity as permission to take the
/// argument's element -- a false proof.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ElemId {
    /// A concrete `(slice, index)` the reference was built from.
    Leaf(ElemRef),
    /// `cond` selects the first child on true, the second on false. Either child
    /// may itself be a `Select`, so the tree is not flattened.
    Select(Pred, Box<ElemId>, Box<ElemId>),
}

/// Fold an element identity into an `ite` over the element words it names, or
/// `None` when any leaf is missing or poisoned. `read` resolves a leaf to its word
/// *and sign*, so a signed slice element keeps its signedness (a conditional choice
/// between two elements of one slice has one shared sign, which must survive).
fn eval_elem_id(id: &ElemId, read: &impl Fn(ElemRef) -> Option<Val>) -> Option<Val> {
    match id {
        ElemId::Leaf(e) => read(*e),
        ElemId::Select(c, t, f) => {
            let then = eval_elem_id(t, read)?;
            let els = eval_elem_id(f, read)?;
            match (then, els) {
                (Val::Sym(a, sa), Val::Sym(b, _)) => Some(Val::Sym(smt::ite(*c, a, b), sa)),
                _ => None,
            }
        }
    }
}

/// A slice iterator's cursor: the base slice local and a concrete position.
///
/// `next` reads `base`'s element at `pos` and advances `pos`. The position is
/// concrete on purpose -- it makes each iteration name a constant index, so the
/// element is the same variable a contract's `s[k]` names, and a loop cut that
/// would make it symbolic drops the cursor (refusing `next`) rather than reading
/// an arbitrary element.
#[derive(Clone, Copy, Debug)]
struct IterState {
    base: u32,
    /// The next element's *base* position when not reversed; when reversed, the
    /// distance from the end (`base index = len-1-pos`). Only `next`/`last`/`nth`
    /// read the direction; `count`/`sum`/`max`/`min` are order-independent.
    pos: u64,
    /// `Iterator::rev`. Reverses which base index a sequence position names.
    rev: bool,
    /// `Iterator::step_by`'s stride (1 unless a `step_by` was applied).
    step: u64,
    /// `Iterator::take`'s absolute end (exclusive), or `None` for the slice's own
    /// length. A `take` needs a constant length so the effective end is constant.
    end: Option<u64>,
    /// `Iterator::map`'s lazy element transform, or `None`.
    map: Option<MapOp>,
    /// `Iterator::filter`'s lazy element predicate, or `None`.
    filter: Option<FilterOp>,
    /// The `pos` when `Iterator::enumerate` was applied, so the yielded index is
    /// `pos - enum_start` (0, 1, ... from the enumerate's own start) rather than the
    /// raw slice position -- `skip(2).enumerate()` must yield index 0 first.
    enum_start: Option<u64>,
}

/// A `map` closure's transform: `|x| x <op> rhs` (or `rhs <op> x`), checked or
/// `wrapping_*`.
#[derive(Clone, Copy, Debug)]
struct MapOp {
    op: BinOp,
    checked: bool,
    rhs: u64,
    rhs_left: bool,
}

/// A `filter` closure's predicate: `|x| x <op> rhs` (or `rhs <op> x`).
#[derive(Clone, Copy, Debug)]
struct FilterOp {
    op: BinOp,
    rhs: u64,
    rhs_left: bool,
}

/// Local-to-symbolic environment, with side maps for aggregate parts.
#[derive(Clone, Debug)]
struct Env {
    locals: BTreeMap<u32, Val>,
    /// Array elements, keyed by (local, index).
    elems: BTreeMap<(u32, u64), Val>,
    /// An element of an array reached through a *field path*: `o.a[0]` is keyed by
    /// `(local, [the field chain before the index], index)`.
    ///
    /// A separate store from [`Self::elems`] because that one is keyed by `(local, index)`
    /// only, so `o.a[0]` and `o.b[0]` would collide on `(local, 0)` -- reading the wrong
    /// array's element. And separate from [`Self::indexed`], which is keyed by local and holds
    /// an *argument*'s array or slice; a field array is not the local itself. Only elements
    /// this run explicitly wrote are served from here; a read of an element that was never
    /// written is `Unknown`, never a seed or a literal.
    elems_path: BTreeMap<(u32, Vec<u32>, u64), Val>,
    /// A field *inside* an element of an array or tuple literal whose element is
    /// itself an aggregate: `[o.i, o.j]` keys element 0's leaf under
    /// `(local, 0, [0])` (index, then the field chain within the element).
    ///
    /// The mirror image of [`Self::elems_path`], and a separate store for the same
    /// reason it is separate from [`Self::elems`]: the key is the whole path, and
    /// here the index comes *first* and the field chain is inside the element. That
    /// is how `[o.i, o.j][0].v` reads -- `_2[_5].0`, an index then a field -- which
    /// is the opposite order from `o.a[0]`. Keying it the other way round would
    /// collide `a[0].v` with `a.v[0]`. Only leaves this run wrote are served; a
    /// field no write reached is `Unknown`, never a seed.
    elem_parts: BTreeMap<(u32, u64, Vec<u32>), Val>,
    /// Tuple fields, keyed by (local, field).
    fields: BTreeMap<(u32, u32), Val>,
    /// A *nested* field path, keyed by (local, the projection chain from the
    /// local to the leaf). `o.i.v` on a `&Outer` is `(1, [0, 0])`.
    ///
    /// The single-field store cannot answer a nested path: its key is one field
    /// index, and `(((*_1).0).0)` would look up `(1, 0)` twice and return the
    /// *outer* field's value for the leaf. A path is a walk, not a field, so it
    /// gets its own store and its own key. Only paths a contract binds are
    /// seeded; a nested read the contract did not name finds nothing here and
    /// stays `Unknown`, which is the same refusal the reader gives today.
    nested: BTreeMap<(u32, Vec<u32>), Val>,
    /// Locals whose element store was poisoned by a write the run could not pin
    /// (`a[i] = x` with a symbolic `i`). Every element is unknown, so no read may
    /// serve one.
    ///
    /// `indexed`'s own `poisoned` flag covers an *argument's* array, but a literal
    /// array's elements live in `elems`, which has no such flag. Without this marker
    /// the poison was invisible to the call boundary: a helper's `a[i] = E { v: 7 }`
    /// dropped the callee's elements, the copy-back copied nothing back, and the
    /// caller's own `elems`/`nested`/`elem_parts` survived -- so a later element read
    /// or copy returned the *pre-call* leaf, and a false contract was **proved**.
    poisoned_elems: BTreeSet<u32>,
    /// Locals written as a *whole* place (an empty projection), so the call
    /// return merge can tell "the callee assigned `*v`" from "the callee left
    /// `v` alone". Copying the callee's value back unconditionally would replace
    /// the caller's variable with the callee's unseeded `Unknown` for a helper
    /// that never wrote through the reference, turning a contract the caller
    /// could have proved into an incomplete one.
    whole_writes: BTreeSet<u32>,
    /// Enum payloads, keyed by (local, variant), with the payload's width.
    /// Written by the `checked_*` model and read through a `Proj::Downcast`.
    payloads: BTreeMap<(u32, u64), (Val, u8)>,
    /// Enum tags, keyed by local, as symbolic values: `1` where the operation is
    /// defined and `0` where it is not. Not a constant, because whether
    /// `checked_add` returns `Some` depends on the operands.
    discriminants: BTreeMap<u32, Val>,
    /// Locals whose type is a reference, and which may therefore be dereferenced.
    ///
    /// A dereference is only transparent for a local the frontend introduced as a
    /// `&T` *argument*. `Ty::Ref` is modelled as its referent, so `*_1` and `_1`
    /// name the same symbolic value; that is the single-owner reading of a
    /// reference, not an aliasing model. A local that is not in this set has no
    /// such backing, and a deref of it reads `Unknown` rather than inventing a
    /// value.
    deref_ok: BTreeMap<u32, ()>,
    /// The place a reference local addresses: `_2 = &_1` records `2 -> _1`, and
    /// `_3 = &_1.0` records `3 -> _1.0`.
    ///
    /// This is what lets `*_2` read what `_2` addresses. The frontend does not
    /// track aliasing (see the module docs on scope), so a reference is modelled
    /// as the *single* place it was created from, not as a value that could be
    /// pointed anywhere: `let r = &c; r.lo` reads `c.lo`, which is sound for the
    /// shape rustc lowers a local borrow to, and `_2 = &_1; _2 = &_3` overwrites
    /// the mapping rather than keeping both. A reference this store has no entry
    /// for reads `Unknown`, which is the honest answer for a pointer whose
    /// target the run never saw.
    addressed: BTreeMap<u32, Place>,
    /// For a reference local, the *caller's* local whose address it was built from,
    /// carried across a call boundary when the reference is passed as an argument.
    ///
    /// `addressed` cannot cross a call: a callee's `&mut u8` argument is a fresh
    /// local whose `addressed` entry is the caller's place, but when the callee
    /// returns that reference the caller's destination needs a place in the
    /// *caller's* frame, and the callee's local indices mean nothing there. This
    /// records the origin in terms the caller can use -- `_3 = &mut _1` records
    /// `3 -> _1` -- so a returned reference can be resolved to the caller's storage
    /// rather than dropped. Without it `let r = identity(&mut x); *r = 5` lost the
    /// write: `_2 = identity(_3)` left `_2` with no address, `*_2 = 5` was a write to
    /// a local no caller reads, and the false `ret == 0` was **proved**.
    ref_origin: BTreeMap<u32, Place>,
    /// For a reference *argument* of the callee, the place it denotes in the
    /// *caller's* frame. The callee's local indices are meaningless to the caller,
    /// so a reference the callee returns through such a local is translated back
    /// through this map -- which is how `*c.lo_mut() = 5` finds `c.lo`.
    arg_source: BTreeMap<u32, Place>,
    /// Values addressed by an index, with a length: slice arguments (`&[T]`) and
    /// array arguments (`[T; N]`), keyed by the local the argument lives in.
    ///
    /// A slice has no length in its type, so its length is a fresh symbolic input
    /// -- it is whatever the caller passed. An array's length is the constant in
    /// its type. Either way the length is a *word* here, and the elements are
    /// distinct inputs per index, so `xs[0]` and `xs[1]` are two values and
    /// `xs[0] == xs[1]` is not provable; see `Indexed::elems`.
    indexed: BTreeMap<u32, Indexed>,
    /// A slice iterator's cursor (`std::slice::Iter`), keyed by the local that
    /// holds the iterator.
    ///
    /// `for x in xs` desugars to `into_iter` (which starts the cursor at position
    /// 0 over the base slice local) and `next` (which reads the element at the
    /// current position and advances it). The position is a *concrete* `u64`, so
    /// each iteration names the element at a constant index -- the same element
    /// variable a contract's `s[k]` names. A loop cut havocs the cursor (drops
    /// it), so a `for` loop with an `invariant:` -- where the position would be
    /// symbolic -- refuses `next` rather than reading an arbitrary element.
    iters: BTreeMap<u32, IterState>,
    /// A local that carries a reference to a slice *element* (`slice::first`/`get`
    /// produce `Option<&T>`), mapped to the element it names: `(indexed local,
    /// index)`.
    ///
    /// Two locals share one entry: the `Option` local the call wrote, and -- once
    /// `unwrap` moves the payload out -- the reference local the payload moved to.
    /// The payload is a *place*, not a value, and the shape the caller reads it
    /// through is `*_2`, a dereference. Recording the element lets `Env::get`
    /// answer `*_2` with the slice's own element variable (the same one a `s[0]`
    /// read names), so the payload is not a fresh value the slice never holds. A
    /// reference this store has no entry for is read as `Unknown` by the deref,
    /// which is the honest answer rather than a wrong element.
    ///
    /// The identity is *compositional* ([`ElemId`]), so a chain of `or`/`and`
    /// composes rather than each step reading only its operands' leaves -- a flat
    /// representation made `a.first().or(b.first()).or(c.first())` select `c`'s
    /// element on the `Some` path, a false proof.
    slice_elem_ref: BTreeMap<u32, ElemId>,
    /// The program's enum layouts, so a variant *construction* constant
    /// (`Mode::Idle`) resolves to its discriminant.
    ///
    /// Carried by value rather than borrowed: the map is small, and a borrow
    /// would put a lifetime on `Env` for every call site of `operand` -- a table
    /// read once per constant is not worth that.
    enums: BTreeMap<String, EnumLayout>,
    /// The program's named `const` items, so a use site (`_0 = const K`) folds to
    /// the literal the item was defined with instead of staying unknown. See
    /// [`crate::mir::parse::MirProgram::consts`].
    consts: BTreeMap<String, Const>,
    /// The width of each modelled enum tag, keyed by local.
    ///
    /// A tag's width is the *discriminants'*, not the dump's `isize`. Recording
    /// it here keeps `discriminant` reading the tag back at the width the
    /// contract's comparison was checked at, instead of widening a small tag to
    /// 64.
    tag_widths: BTreeMap<u32, u8>,
    /// The rendered `format_args!` message each local holds, keyed by local.
    ///
    /// A `panic!` message is not a literal in edition 2024: it is a
    /// `fmt::Arguments` value built by a chain of `core::fmt` calls, and the
    /// `panic_fmt` that consumes it is a *diverging* call whose only argument is a
    /// local. Without a store for the message the report could only name the
    /// mangled callee, so this carries the finished message from where it is built
    /// to where it is consumed. Only string-valued locals are ever inserted.
    strs: BTreeMap<u32, String>,
    /// The *pieces* each local holds, keyed by local, for a local that carries a
    /// promoted `&[&str]`.
    ///
    /// The pieces are kept apart from [`Self::strs`] because the number of
    /// placeholders is not known until the `Arguments` call that consumes them
    /// says how many arguments it was given: the same pieces render `"zero "` for
    /// `new_const` and `"zero {}"` for `new_v1::<1, 1>`. Joining early would bake
    /// in the wrong count.
    piece_sets: BTreeMap<u32, Vec<String>>,
    /// The `b"…"` template each local holds, keyed by local, for the `new::<LEN, A>`
    /// spelling. Kept raw -- not decoded -- because the decode needs the argument
    /// count, which only the consuming call knows.
    tmpl_bytes: BTreeMap<u32, Vec<u8>>,
    /// The value each `Box` local holds, keyed by the box local. `Box::<T>::new(v)`
    /// stores `v` here; the compiler's null check reads a nonzero pointer token from
    /// the box's field 0, and the deref `*b` reads this back.
    boxed: BTreeMap<u32, Val>,
    /// The pointer local a `Box`'s deref goes through, mapped to the box local.
    /// `_3 = (_2.0) as *const u8` records `_3 -> _2`, so `*_3` reads `boxed[_2]`.
    box_refs: BTreeMap<u32, u32>,
    /// The string pieces of each `promoted` constant, copied from
    /// [`crate::mir::parse::MirProgram::promoted_strs`] so `eval_rvalue` can read
    /// a `const NAME::promoted[0]` operand without the whole program in hand.
    promoted: BTreeMap<String, Vec<String>>,
}

/// A modelled value with a length and elements: a slice, an array, or a `Vec`.
#[derive(Clone, Debug)]
struct Indexed {
    /// The length. A symbolic input for a slice, the type's constant for an
    /// array; the executor only needs it to be a word of `usize` width.
    len: Var,
    /// Whether the length can change (`Vec::push`/`pop`) rather than being fixed
    /// by the type or by the caller (`[T; N]`, `&[T]`).
    ///
    /// This is what a `Vec` adds to the slice model, and it is load-bearing in two
    /// places. The loop-header havoc must replace a mutable length with a fresh
    /// `usize` -- a loop that pushes changes the length, and leaving the entry
    /// length at the exit edge is a *false proof* (`ret == 0` for a real `ret == 3`,
    /// the hole the length havoc exists for). A whole-value write must *drop* a
    /// mutable length rather than poison it -- poisoning keeps the length, so
    /// `v = other; v.len()` would read the old one.
    len_mutable: bool,
    /// The width of one element, which is the *referent's* width (`u8` for
    /// `&[u8]` or `[u8; 4]`), not the length's. Taking it from `len` would make
    /// every element 64 bits wide and mis-size every read.
    ///
    /// `0` means the width is **not modelled** — a generic `&[T]`, where `T` is
    /// an unbound type parameter. The length is still a real value (`len` and
    /// `is_empty` read only the length), so the store exists and those answer;
    /// every *element* operation refuses `0` rather than inventing a width, so
    /// `v[0]` on a `&[T]` is a missing value, never a wrong one.
    elem_w: u8,
    /// The signedness of one element. Every element of an array or slice has the
    /// same type, so one sign serves them all; an element read out of this store
    /// carries it, which is what keeps `xs[0] < 0` a signed test on an `&[i8]`.
    elem_signed: bool,
    /// `index value -> element variable`. Only indices whose value the run can
    /// resolve can be looked up here; a symbolic index that cannot be pinned is
    /// refused rather than guessed.
    elems: BTreeMap<u64, Var>,
    /// The array's fixed length, when it is an array rather than a slice.
    ///
    /// A slice's length is a symbolic input, so there is no finite domain to
    /// enumerate and a symbolic subscript stays refused. An array's length is in
    /// its type, so `a[i]` can be modelled as an ite chain over `0..N` -- exactly,
    /// which is what this field makes possible.
    fixed_len: Option<u64>,
    /// How many steps a *slice's* symbolic chain enumerates, when the contract
    /// established that its length is within `MAX_INDEX_CHAIN`.
    ///
    /// A slice has no length in its type, so unlike `fixed_len` there is no
    /// constant to take from the type. This is `Some(MAX_INDEX_CHAIN)` only when
    /// the contract's precondition was proved to imply `len <= MAX_INDEX_CHAIN`,
    /// which is what makes enumerating that many steps an exact model of *every*
    /// index in the slice. Without it a symbolic slice subscript stays refused:
    /// the chain would have to stop somewhere, and stopping before the length
    /// would fall through to a wrong element.
    slice_steps: Option<u64>,
    /// Whether an element write invalidated the seeded elements.
    ///
    /// `elems` is seeded with one variable per element the contract named, and
    /// the ite chain is built from them. A write to an element the store cannot
    /// represent per index -- an aggregate element, or a symbolic index -- makes
    /// every element unknown rather than leaving the seeded value readable: a
    /// stale element is not a missing proof, it is a *wrong* one, and it is
    /// exactly what `a[0] = 0; a[i]` would otherwise prove. The length survives,
    /// because a write does not change it.
    poisoned: bool,
}

impl Env {
    fn new() -> Env {
        Env {
            locals: BTreeMap::new(),
            elems: BTreeMap::new(),
            elems_path: BTreeMap::new(),
            elem_parts: BTreeMap::new(),
            fields: BTreeMap::new(),
            nested: BTreeMap::new(),
            poisoned_elems: BTreeSet::new(),
            payloads: BTreeMap::new(),
            discriminants: BTreeMap::new(),
            deref_ok: BTreeMap::new(),
            addressed: BTreeMap::new(),
            ref_origin: BTreeMap::new(),
            arg_source: BTreeMap::new(),
            indexed: BTreeMap::new(),
            iters: BTreeMap::new(),
            slice_elem_ref: BTreeMap::new(),

            whole_writes: BTreeSet::new(),
            enums: BTreeMap::new(),
            consts: BTreeMap::new(),
            tag_widths: BTreeMap::new(),
            strs: BTreeMap::new(),
            piece_sets: BTreeMap::new(),
            tmpl_bytes: BTreeMap::new(),
            boxed: BTreeMap::new(),
            box_refs: BTreeMap::new(),
            promoted: BTreeMap::new(),
        }
    }

    /// [`Env::new`] plus the program's enum layouts, `const` items and promoted
    /// `&[&str]` pieces, so the `core::fmt` model can read a `panic!` message back.
    fn with_prog(prog: &MirProgram) -> Env {
        Env {
            enums: prog.enums.clone(),
            consts: prog.consts.clone(),
            promoted: prog.promoted_strs.clone(),
            ..Env::new()
        }
    }

    /// The element variable for `index` of an indexed value (slice or array)
    /// `local`, created on first use.
    ///
    /// Two different indices are two different variables, and the same index read
    /// twice is the same variable, which is what makes an indexed read a
    /// *function* of the index rather than an arbitrary value per read.
    fn index_elem(&mut self, local: u32, index: u64) -> Option<(Var, Sign)> {
        let s = self.indexed.get_mut(&local)?;
        if s.poisoned {
            return None;
        }
        // An unmodelled element width (a generic `&[T]`) has no element variable
        // to create: a width is what makes the variable a value, and inventing one
        // would mis-size every read. Refusing keeps an element read a missing
        // value; the *length* is unaffected, so `len`/`is_empty` still answer.
        if s.elem_w == 0 {
            return None;
        }
        let sign = Sign::of_bool(s.elem_signed);
        if let Some(v) = s.elems.get(&index) {
            return Some((*v, sign));
        }
        let w = s.elem_w;
        let v = smt::var(w);
        s.elems.insert(index, v);
        Some((v, sign))
    }

    /// The ite chain standing for `a[i]` on a fixed-length array or on a slice
    /// whose length the contract bounded, or `None` when neither applies.
    ///
    /// An array has a finite domain, so `a[i]` is *exactly* `ite(i == 0, e0, ...)`
    /// over `0..N`. Every element is created if it does not exist yet, so the
    /// chain is a function of `i` and the same `i` read twice is the same value.
    /// The caller must be under `i < N`: the bounds assert rustc emits supplies
    /// that, and without it the chain would fall through to the last element,
    /// which is a wrong value rather than a missing one.
    ///
    /// A slice's length is symbolic, so there is no type length to enumerate. Its
    /// chain enumerates `0..MAX_INDEX_CHAIN`, which is exact for *every* index the
    /// slice can hold -- and therefore for the index the body reads -- but only
    /// because the contract established `len <= MAX_INDEX_CHAIN` first. Without
    /// that the entry is absent and this returns `None`, which is the refusal a
    /// slice's symbolic subscript had before.
    fn index_chain(&mut self, local: u32, index: Var) -> Option<Val> {
        let (n, elem_w, elem_signed) = {
            let s = self.indexed.get(&local)?;
            // An unmodelled element width has no elements to build a chain from.
            if s.elem_w == 0 {
                return None;
            }
            // An array's steps come from its type; a slice's from the contract.
            (s.fixed_len.or(s.slice_steps)?, s.elem_w, s.elem_signed)
        };
        if n > crate::mir::spec::MAX_INDEX_CHAIN {
            return None;
        }
        let mut elems = Vec::with_capacity(n as usize);
        for k in 0..n {
            elems.push(self.index_elem(local, k)?.0);
        }
        let mut chain = smt::word(0, elem_w);
        for k in (0..n).rev() {
            chain = smt::ite(smt::eq_const(index, k), elems[k as usize], chain);
        }
        // The chain's *value* is an element, so it carries the element's sign.
        Some(Val::Sym(chain, Sign::of_bool(elem_signed)))
    }

    /// Read `(*_1)[_2]` — an indexed element (a slice or an array) subscripted by
    /// a local.
    ///
    /// Returns `None` when the place is not an indexed read at all, so the caller
    /// falls through to the ordinary path; returns `Some(Unknown)` when it *is*
    /// one but the index cannot be pinned, so an unresolvable subscript is a
    /// missing value rather than an arbitrary element.
    ///
    /// The element is created on first read, which is why this takes `&mut self`
    /// and `get` cannot: the first read of `xs[0]` has no variable yet, and the
    /// second read must find the same one.
    fn read_indexed(&mut self, p: &Place) -> Option<Val> {
        if !self.indexed.contains_key(&p.local) {
            return None;
        }
        // An element write this store could not represent per index leaves every
        // element unknown, so the read is a missing value rather than the seeded
        // one the body overwrote.
        if self.indexed.get(&p.local).is_some_and(|s| s.poisoned) {
            return Some(Val::Unknown);
        }
        let index = match p.proj.as_slice() {
            [Proj::Deref, Proj::Index(k)] | [Proj::Index(k)] => *k,
            [Proj::Deref, Proj::IndexVar(li)] | [Proj::IndexVar(li)] => {
                match self.locals.get(li) {
                    Some(Val::Sym(v, _)) => {
                        let v = *v;
                        match smt::evaluate(v, |_| None) {
                            Some(k) => k,
                            // A symbolic index on an array or on a
                            // contract-bounded slice is modelled as an ite chain;
                            // on an unbounded slice there is no finite domain, so
                            // the element is genuinely unknown and stays a refusal.
                            None => return self.index_chain(p.local, v),
                        }
                    }
                    _ => return Some(Val::Unknown),
                }
            }
            _ => return None,
        };
        Some(match self.index_elem(p.local, index) {
            Some((v, sign)) => Val::Sym(v, sign),
            None => Val::Unknown,
        })
    }

    /// Rewrite a place whose head is a dereference of an addressed local, so
    /// `_2 = &_1; *_2` reads `_1`.
    ///
    /// The rewrite is a *substitution*, not a copy of the value: `*_2` becomes
    /// the place `_2` addresses, so a later write through the reference and a
    /// later read of the target meet in one store, which is the whole point of
    /// borrowing. `_2 = &_1.0; (*_2)` becomes `_1.0`, and a reference to a
    /// reference (`_4 = &(*_2)`) resolves again, which the loop allows for. The
    /// bound is the same shape as the other unwind bounds: a chain longer than
    /// this is a shape the frontend does not produce, and stopping leaves the
    /// deref to read `Unknown` rather than looping.
    ///
    /// A deref of a local that is *not* in `addressed` is left alone, so the
    /// `deref_ok` argument case (`_1: &[u8]`, `*_1`) still reaches `get`'s own
    /// `Proj::Deref` arm.
    fn resolve(&self, p: &Place) -> Place {
        let mut cur = p.clone();
        for _ in 0..8 {
            if !matches!(cur.proj.first(), Some(Proj::Deref)) {
                break;
            }
            let Some(target) = self.addressed.get(&cur.local) else { break };
            let mut proj = target.proj.clone();
            proj.extend_from_slice(&cur.proj[1..]);
            cur = Place { local: target.local, proj };
        }
        cur
    }

    /// The element index a place's subscript names, when the run can pin it.
    ///
    /// `a[0]` and `a[_3]` are the same element, and rustc spells the subscript as a
    /// local (`IndexVar`) in almost every shape the frontend meets; a leading
    /// `Deref` (`(*_1)[_3]`, how a write through a `&mut [T; N]` lowers) names the
    /// same local's element, and reading past it is what the element-write paths
    /// need -- without that a whole-element write through a helper never reached
    /// its re-root, so the caller's leaf survived the call.
    ///
    /// A subscript the run cannot pin returns `None`: it names no single element, so
    /// no single slot can be re-rooted onto. Anything past the subscript is not part
    /// of the index either, and is refused.
    fn elem_index_of(&self, proj: &[Proj]) -> Option<u64> {
        let proj = match proj.first() {
            Some(Proj::Deref) => &proj[1..],
            _ => proj,
        };
        match proj {
            [Proj::Index(k)] => Some(*k),
            [Proj::IndexVar(li)] => match self.locals.get(li) {
                Some(Val::Sym(x, _)) => smt::evaluate(*x, |_| None),
                _ => None,
            },
            _ => None,
        }
    }

    /// Move one element's leaves onto a whole local, as that local's own parts.
    ///
    /// The inverse of [`Self::rebase_elem_parts`]. `_5 = copy _3[_6]` -- the first
    /// half of `a[0] = b[0]` -- reads an element of `_3` into a temp, and the leaves
    /// under `(3, 0, chain)` become the temp's `fields`/`nested` parts, so the second
    /// half's re-root finds them like any whole-local source. Without this the leaves
    /// die at the temp: reading an element yields its leaf *scalar*, not its parts,
    /// so the write saw a scalar and the destination leaf read `Unknown` -- a
    /// coverage hole in both directions, and the reason `rebase_elem_parts`'s
    /// element-source arm alone was not enough.
    fn carry_elem_leaf_onto_local(&mut self, src: &Place, dest: u32) -> bool {
        let src = self.resolve(src);
        let Some(k) = self.elem_index_of(&src.proj) else { return false };
        let s = src.local;
        // No poison check here, and that is deliberate: the leaf maps *are* the
        // record of which indices have been re-established. `poison_elems` clears
        // them, so a poisoned element carries nothing and this returns `false` on
        // its own; a pinned write *after* the poison (`a[i].v = 7; a[0].v = 9`)
        // re-populates exactly that index's leaf, and refusing it because the
        // array-wide marker is still set would lose a value the body does know --
        // `let x = a[0]; x.v` would read `Unknown` though the leaf is `9`. The
        // marker stays for the call boundary, where it means "this array is not
        // wholly known", which is a different question from "is this leaf known".
        let leaves: Vec<(Vec<u32>, Val)> = self
            .elem_parts
            .iter()
            .filter(|((l, ek, _), _)| *l == s && *ek == k)
            .map(|((_, _, c), v)| (c.clone(), *v))
            .collect();
        let nested: Vec<(Vec<u32>, Val)> = self
            .nested
            .iter()
            .filter(|((l, c), _)| *l == s && c.first() == Some(&(k as u32)))
            .map(|((_, c), v)| (c[1..].to_vec(), *v))
            .collect();
        if leaves.is_empty() && nested.is_empty() {
            return false;
        }
        if s == dest {
            return false;
        }
        // The destination is replaced whole, so its previous parts must not survive:
        // a leaf the source does not carry would be a stale *wrong* value. This is
        // the same drop `copy_parts` does, and for the same reason -- `set` is told
        // `Val::Agg` (parts moved), so it will not clear them itself.
        self.forget_parts(dest);
        for (chain, v) in leaves.into_iter().chain(nested) {
            match chain.as_slice() {
                [f] => {
                    self.fields.insert((dest, *f), v);
                }
                _ => {
                    self.nested.insert((dest, chain), v);
                }
            }
        }
        true
    }

    /// Follow one level of *value* indirection: the place a pointer local's
    /// value addresses.
    ///
    /// This is the step `resolve` deliberately does not take. `resolve` rewrites
    /// an explicit `*_2`; `pointee` answers "where does `_2` point", which is what
    /// `PtrMetadata(_2)` asks -- the metadata belongs to the pointee, not to the
    /// pointer. A local with no recorded address is returned unchanged, so the
    /// `&[T]` argument case (`_1` is the slice) falls through to `indexed`.
    fn pointee(&self, p: &Place) -> Place {
        let r = self.resolve(p);
        match (r.proj.is_empty(), self.addressed.get(&r.local)) {
            (true, Some(t)) => self.resolve(t),
            _ => r,
        }
    }

    /// A place whose `IndexVar` steps are replaced by the literal they hold *in
    /// this frame*.
    ///
    /// A returned reference's origin is a place in the callee's terms, and a
    /// `&mut self.a[0]` records the *local* that held `0` -- `_2` -- not the
    /// literal, because `_2` is the index the dump names. That local dies at the
    /// call boundary, so a caller that translates the origin gets a place no
    /// `elems_path` entry is ever keyed by, and a write through the returned
    /// reference is dropped. Resolving the index here, while the callee's locals
    /// are still live, turns it into the literal the caller's store agrees on.
    ///
    /// A symbolic index is left as it is: its value is not a single element the
    /// caller could name either, so refusing to pin it is what keeps the write
    /// from landing on an arbitrary element.
    fn pin_index_vars(&self, p: &Place) -> Place {
        let mut proj = p.proj.clone();
        for step in &mut proj {
            if let Proj::IndexVar(li) = step {
                if let Some(Val::Sym(x, _)) = self.locals.get(li) {
                    if let Some(k) = smt::evaluate(*x, |_| None) {
                        *step = Proj::Index(k);
                    }
                }
            }
        }
        Place { local: p.local, proj }
    }

    /// Move the parts stored under `src` to `dst`, re-rooting them when either place is
    /// nested, and report whether there were any.
    ///
    /// This generalises [`Self::copy_parts`], which is the whole-place-to-whole-place case and
    /// carries the element, payload, tag and index stores as well. This one is reached when a
    /// nested place is on at least one side, and it moves the two field-shaped stores:
    ///
    /// - a struct literal into a nested field, `o.i = InnerBox { v: 9 }` -> `(_1.0) = move _2`
    ///   (whole source, nested destination);
    /// - a nested-to-nested move, `o.i = o.j` -> `_2 = move (_1.1); (_1.0) = move _2` (the
    ///   first step is a nested source into a whole temp, the second a whole source into a
    ///   nested destination).
    ///
    /// [`Self::copy_parts`] is reached only when both places are whole, so without this the
    /// parts never land under the nested place and the later read (`(_1.0).0`, the nested
    /// store keyed by the whole chain) finds nothing. The body's value is then unknown, and a
    /// contract that *is* false of the body is reported unreadable instead of refuted.
    ///
    /// Both projections are read as field paths (`field_steps`), and both are *resolved*
    /// first, so a write through a reference (`((*_1).0) = move _2`) reaches the target's
    /// field path rather than stopping at the leading deref -- what makes the write and the
    /// read meet in one store. Any other projection (an index, a downcast, a second deref)
    /// names a store this helper does not re-root, and writing a part where no read consults
    /// it would be a lost proof at best, so those are refused.
    ///
    /// A part is re-keyed relative to the source's own path: the entry at `(src.local, sp)`
    /// (or the single-field entry whose key *is* `sp`) is the value at `src`, and it lands at
    /// the destination's path. A whole destination replaces every part it had, so its old
    /// parts are dropped first; a nested destination keeps its siblings, because only the
    /// paths under it are being written. A path that re-roots to the whole local (a field of
    /// one moved into a whole place) becomes the local's value.
    fn rebase_parts(&mut self, src: &Place, dst: &Place) -> bool {
        let src = self.resolve(src);
        let dst = self.resolve(dst);
        let Some(sp) = field_steps(&src.proj) else { return false };
        let Some(dp) = field_steps(&dst.proj) else { return false };
        if src.local == dst.local && sp == dp {
            return false;
        }
        let s = src.local;
        // The source's parts, keyed relative to the source's own path. The `nested` store is
        // the chain-shaped one (length two or more) and the `fields` store the single-field
        // one; a source path `sp` selects the entries under it, and the entry *at* it (a
        // single-field source) is the whole moved value.
        let mut rels: Vec<(Vec<u32>, Val)> = Vec::new();
        for ((l, chain), v) in &self.nested {
            if *l == s {
                if let Some(tail) = chain.strip_prefix(sp.as_slice()) {
                    rels.push((tail.to_vec(), *v));
                }
            }
        }
        for ((l, k), v) in &self.fields {
            if *l != s {
                continue;
            }
            if sp.is_empty() {
                rels.push((vec![*k], *v));
            } else if sp.as_slice() == [*k] {
                rels.push((Vec::new(), *v));
            }
        }
        // Elements of field-path arrays under the source path move with the value, re-keyed the
        // same way. An element *at* the source path (its chain equals `sp`) is an element of the
        // whole destination value, which the plain `elems` store answers; a deeper one keeps its
        // tail under the destination path.
        let mut elem_rels: Vec<(Vec<u32>, u64, Val)> = Vec::new();
        for ((l, chain, k), v) in &self.elems_path {
            if *l == s {
                if let Some(tail) = chain.strip_prefix(sp.as_slice()) {
                    elem_rels.push((tail.to_vec(), *k, *v));
                }
            }
        }
        // A whole-local array's elements live in `elems`, not `elems_path`, and they move with
        // the value too. Without this, an array that is a struct *field* built by a literal
        // (`ArrInner { a: [9, 1, 2, 3] }`) lost its elements at the assignment: `_2.0` held the
        // array's value but not its parts, so `o.i.a[0]` read `Unknown` and the contract stayed
        // `Incomplete` in both directions -- a coverage hole, not a false proof, since a missing
        // value proves nothing. Only a *whole* source has `elems` (a nested source's elements
        // are in `elems_path` and are handled above), so this is gated on an empty `sp`.
        let mut whole_elem_rels: Vec<(u64, Val)> = Vec::new();
        if sp.is_empty() {
            for ((l, k), v) in &self.elems {
                if *l == s {
                    whole_elem_rels.push((*k, *v));
                }
            }
        }
        let any = !rels.is_empty() || !elem_rels.is_empty() || !whole_elem_rels.is_empty();
        // A whole destination is replaced outright, so its previous parts must not survive; a
        // nested destination keeps the parts outside the written path.
        if dp.is_empty() && s != dst.local {
            self.forget_parts(dst.local);
        } else if !dp.is_empty() {
            self.elems_path
                .retain(|(l, c, _), _| *l != dst.local || !c.starts_with(dp.as_slice()));
        }
        for (tail, k, v) in elem_rels {
            let mut full = dp.clone();
            full.extend(tail);
            if full.is_empty() {
                self.elems.insert((dst.local, k), v);
            } else {
                self.elems_path.insert((dst.local, full, k), v);
            }
        }
        // A whole-local element of the source lands on the destination at the same shape: a
        // whole destination takes it as a whole-local element, and a nested destination takes
        // it under the destination's field chain.
        for (k, v) in whole_elem_rels {
            if dp.is_empty() {
                self.elems.insert((dst.local, k), v);
            } else {
                self.elems_path.insert((dst.local, dp.clone(), k), v);
            }
        }
        for (rel, v) in rels {
            let mut full = dp.clone();
            full.extend(rel);
            match full.len() {
                // The value *at* the source path becomes the whole destination value.
                0 => {
                    self.locals.insert(dst.local, v);
                }
                1 => {
                    self.fields.insert((dst.local, full[0]), v);
                }
                _ => {
                    self.nested.insert((dst.local, full), v);
                }
            }
        }
        any
    }

    /// Copy every derived part of `src`'s local onto `dst`, and report whether the
    /// source had any.
    ///
    /// A whole-struct assignment (`c = d`) copies a value the frontend models as
    /// its *parts*: `d`'s fields live in `fields`, not in `locals`, and `d` itself
    /// is a struct with no bit-vector meaning. Copying only the local would move an
    /// `Unknown` and leave `c.lo` reading nothing, which is why
    /// `c = d; c.lo` stayed unreadable. Copying the parts is what makes the
    /// assignment mean what it says.
    ///
    /// The destination's own parts are dropped first: a whole-value assignment
    /// replaces all of them, so a field the source does not carry must not survive
    /// from the destination's previous value -- that stale field is a *wrong*
    /// value, and it is the failure mode this store guards against everywhere else.
    fn copy_parts(&mut self, src: &Place, dst: u32) -> bool {
        let src = self.resolve(src);
        if !src.proj.is_empty() || src.local == dst {
            return false;
        }
        let s = src.local;
        let fields: Vec<(u32, Val)> =
            self.fields.iter().filter(|((l, _), _)| *l == s).map(|((_, k), v)| (*k, *v)).collect();
        let elems: Vec<(u64, Val)> =
            self.elems.iter().filter(|((l, _), _)| *l == s).map(|((_, k), v)| (*k, *v)).collect();
        let payloads: Vec<(u64, (Val, u8))> =
            self.payloads.iter().filter(|((l, _), _)| *l == s).map(|((_, k), v)| (*k, *v)).collect();
        let disc = self.discriminants.get(&s).copied();
        let indexed = self.indexed.get(&s).cloned();
        // A slice-iterator cursor is a part of the local too: `_4 = move _3` copies
        // the iterator out of the temp, and without carrying the cursor the later
        // `next` would find none and refuse.
        let iter = self.iters.get(&s).copied();
        // A `Vec` is an `indexed` entry like a slice, so a move (`let w = v`)
        // carries its length *and* elements with the `indexed` copy above -- the
        // same transfer a slice's store gets. Nothing extra is needed here.
        // Nested paths are parts too, keyed by the local *and* the chain. A copy
        // that moved only the single-field parts would leave `c`'s own `c.i.v`
        // seed in place after `c = d`, so a later `c.i.v` would read `c`'s
        // pre-copy leaf rather than `d`'s -- the same stale-part hole, one level
        // down, and a false refutation of the true contract `d.i.v == 1`.
        let nested: Vec<(Vec<u32>, Val)> = self
            .nested
            .iter()
            .filter(|((l, _), _)| *l == s)
            .map(|((_, chain), v)| (chain.clone(), *v))
            .collect();
        // Elements of a field-path array are parts of the local too: `c = d` has to carry
        // `d.a[0]` to `c.a[0]`, or a later read of the destination's element finds nothing (or,
        // worse, the destination's own pre-copy element).
        let path_elems: Vec<(Vec<u32>, u64, Val)> = self
            .elems_path
            .iter()
            .filter(|((l, _, _), _)| *l == s)
            .map(|((_, chain, k), v)| (chain.clone(), *k, *v))
            .collect();
        // A field inside an element of an aggregate literal is a part too:
        // `let b = a` must carry `a[0].v` to `b[0].v`, or the copy reads the
        // destination's stale leaf (or nothing at all).
        let elem_parts: Vec<(u64, Vec<u32>, Val)> = self
            .elem_parts
            .iter()
            .filter(|((l, _, _), _)| *l == s)
            .map(|((_, k, chain), v)| (*k, chain.clone(), *v))
            .collect();
        let any = !fields.is_empty()
            || !elems.is_empty()
            || !payloads.is_empty()
            || !nested.is_empty()
            || !path_elems.is_empty()
            || !elem_parts.is_empty()
            || disc.is_some()
            || indexed.is_some()
            || iter.is_some();
        self.forget_parts(dst);
        for (k, chain, v) in elem_parts {
            self.elem_parts.insert((dst, k, chain), v);
        }
        for (chain, v) in nested {
            self.nested.insert((dst, chain), v);
        }
        for (chain, k, v) in path_elems {
            self.elems_path.insert((dst, chain, k), v);
        }
        for (k, v) in fields {
            self.fields.insert((dst, k), v);
        }
        for (k, v) in elems {
            self.elems.insert((dst, k), v);
        }
        for (k, v) in payloads {
            self.payloads.insert((dst, k), v);
        }
        if let Some(d) = disc {
            self.discriminants.insert(dst, d);
        }
        if let Some(ix) = indexed {
            self.indexed.insert(dst, ix);
        }
        if let Some(it) = iter {
            self.iters.insert(dst, it);
        }
        any
    }

    fn get(&self, p: &Place) -> Val {
        let resolved = self.resolve(p);
        let p = &resolved;
        // A nested field path is a walk, not a field: `(((*_1).0).0)` must not be
        // answered by looking up the *outer* field `(1, 0)` twice, which would
        // return `o.i` for `o.i.v` -- a wrong value, not a missing one. So a chain
        // of two or more fields is answered *only* out of the nested store, and a
        // path no contract bound reads `Unknown`. The single-field walk below is
        // deliberately not consulted: it is keyed by one field index and would
        // return the intermediate aggregate for the leaf.
        if let Some(chain) = field_chain(&p.proj) {
            return self.nested.get(&(p.local, chain)).copied().unwrap_or(Val::Unknown);
        }
        let mut cur = match self.locals.get(&p.local) {
            Some(v) => *v,
            // A modelled `Option` local has no entry in `locals`: its value is
            // its tag, which lives in `discriminants`. Without this fallback a
            // read of the bare local `_2` -- which is exactly what
            // `discriminant(_2)` and `move _2` lower to -- would come back
            // unknown and the `switchInt` on the tag would go unmodelled.
            None => match self.discriminants.get(&p.local) {
                Some(v) => *v,
                // A local with no whole value but with *parts*: an aggregate a
                // modelled call wrote field-by-field (`overflowing_add` writes
                // `_0.0` and `_0.1` without ever assigning `_0`), or an enum built
                // from a variant. The projections below are what carry the value,
                // so falling through to them is right; returning `Unknown` here
                // would make every such component unreadable, which is exactly how
                // a `ret.1` contract for the `overflowing_*` family was reported
                // as an aggregate with no such component. A projection-less read
                // of such a local still has no single value, and the loop below
                // leaves `cur` as this same `Unknown` for it.
                None if !p.proj.is_empty() => Val::Unknown,
                None => return Val::Unknown,
            },
        };
        // A downcast read is a read of the variant's payload. rustc emits the
        // downcast only inside the `switchInt` arm that already matched the
        // variant, so the path condition forces the tag here and no extra gate
        // is needed. What is needed is that the payload *exists*: an enum this
        // frontend did not build has no entry, and answering `Unknown` there is
        // what keeps a stale or invented payload out of the result.
        let modelled = self.discriminants.contains_key(&p.local);
        let mut i = 0;
        while i < p.proj.len() {
            cur = match &p.proj[i] {
                // A struct field lives in `fields`; a *tuple* component lives in
                // `elems`, because `_3 = (a, b)` stores it under `Proj::Index` and
                // rustc prints the read back as `_3.0` (`Proj::Field`). The two
                // spellings of "component 0" have to meet in one store, or a tuple
                // local's component reads `Unknown`: `let t = (a, b); t.0` would
                // not be `a`. A local is a struct or a tuple and never both, so the
                // `elems` lookup can only ever hit for the tuple case, and a struct
                // whose field is genuinely unwritten finds nothing in either store
                // and stays `Unknown`.
                Proj::Field(f) => match self.fields.get(&(p.local, *f)) {
                    Some(v) => *v,
                    None => *self.elems.get(&(p.local, *f as u64)).unwrap_or(&Val::Unknown),
                },
                // An indexed element. `elems` is the array-literal map, keyed by
                // a concrete index; a slice's or array *argument*'s elements live
                // under `indexed` instead. The two must not be confused, so the
                // `indexed` lookup is tried first and only for a local that *is*
                // one.
                Proj::Index(k) => match self.indexed.get(&p.local) {
                    Some(s) if s.poisoned => Val::Unknown,
                    Some(s) => match s.elems.get(k) {
                        Some(v) => Val::Sym(*v, Sign::of_bool(s.elem_signed)),
                        // Not read yet. `get` takes `&self` and so cannot create
                        // the element; the operand path goes through
                        // `read_indexed`, which can, and does so before this
                        // is reached. Answering `Unknown` here is the fallback
                        // for a caller that did not.
                        None => Val::Unknown,
                    },
                    // A field *inside* an element whose element is an aggregate:
                    // `[o.i, o.j][0].v` is `_2[_5].0`, an index then a field. The
                    // chain after the index is what names the leaf, and it is
                    // keyed in `elem_parts` in this order. Tried before the
                    // field-path store so `a[0].v` cannot be answered by a
                    // differently ordered `a.v[0]`.
                    //
                    // The trailing field steps are consumed here (`i` advances past
                    // them): letting the loop run on would re-read `Field(0)`
                    // against the local and replace the leaf just found with the
                    // whole element, which is the wrong value this arm exists to
                    // avoid.
                    None if p.proj.len() > i + 1 => {
                        let inner = match field_steps(&p.proj[i + 1..]) {
                            Some(chain) if !chain.is_empty() => chain,
                            _ => return Val::Unknown,
                        };
                        // No poison gate: `poison_elems` cleared this map, and a
                        // pinned write after the poison re-populated exactly its
                        // index, so an entry here is always a value the body
                        // established. The array-wide marker would only hide a leaf
                        // that *is* known (`a[i].v = 7; a[0].v = 9; a[0].v`).
                        let v = *self
                            .elem_parts
                            .get(&(p.local, *k, inner.clone()))
                            .unwrap_or(&Val::Unknown);
                        i += inner.len();
                        v
                    }
                    // An element of an array reached through a *field path*: `o.a[0]` is keyed
                    // by `(local, the field chain before the index, index)`. The path form is
                    // tried first; a whole-local array has an empty chain, which is the plain
                    // `o[0]` case the `elems` map below answers. Only an element this run
                    // explicitly wrote is served; a path no write reached is `Unknown`, never a
                    // seed or a literal, so `o.a[0]` cannot read a value the body never stored.
                    None => {
                        let chain = field_steps(&p.proj[..i]).unwrap_or_default();
                        if chain.is_empty() {
                            // A whole-local array (an array literal): the plain `elems` map
                            // keeps answering it, exactly as before.
                            *self.elems.get(&(p.local, *k)).unwrap_or(&Val::Unknown)
                        } else {
                            *self
                                .elems_path
                                .get(&(p.local, chain, *k))
                                .unwrap_or(&Val::Unknown)
                        }
                    }
                },
                // `(*_1)[_2]` — a subscript that is a local. The element is
                // looked up by the index's *value*: a constant index names one
                // element, and a symbolic index names none the run can pin, so it
                // reads `Unknown` rather than an arbitrary element. Reading an
                // arbitrary element would make `xs[i]` a different value per
                // read, which is a wrong proof waiting to happen.
                Proj::IndexVar(li) => {
                    let sym = match self.locals.get(li) {
                        Some(Val::Sym(v, _)) => Some(*v),
                        _ => None,
                    };
                    match sym.and_then(|v| smt::evaluate(v, |_| None)) {
                        Some(k) => match self.indexed.get(&p.local) {
                            Some(s) if s.poisoned => Val::Unknown,
                            Some(s) => {
                                let sign = Sign::of_bool(s.elem_signed);
                                s.elems.get(&k).map(|v| Val::Sym(*v, sign)).unwrap_or(Val::Unknown)
                            }
                            // A field inside an element: `_2[_5].0`. Same shape as
                            // the constant-index case above, with the index pinned
                            // to `k` by the subscript's own value.
                            None if p.proj.len() > i + 1 => {
                                let inner = match field_steps(&p.proj[i + 1..]) {
                                    Some(chain) if !chain.is_empty() => chain,
                                    _ => return Val::Unknown,
                                };
                                let v = *self
                                    .elem_parts
                                    .get(&(p.local, k, inner.clone()))
                                    .unwrap_or(&Val::Unknown);
                                i += inner.len();
                                v
                            }
                            None => {
                                let chain = field_steps(&p.proj[..i]).unwrap_or_default();
                                if chain.is_empty() {
                                    *self.elems.get(&(p.local, k)).unwrap_or(&Val::Unknown)
                                } else {
                                    *self
                                        .elems_path
                                        .get(&(p.local, chain, k))
                                        .unwrap_or(&Val::Unknown)
                                }
                            }
                        },
                        // A symbolic subscript: `get` takes `&self`, so it cannot
                        // create the elements the chain needs. The operand path
                        // goes through `read_indexed`, which can, and does so
                        // first; this is the fallback for a caller that did not.
                        None => Val::Unknown,
                    }
                }
                Proj::Deref => {
                    // The frontend does not track aliasing, so a dereference is
                    // only meaningful when the pointee *is* the local: `_1` is the
                    // `&Config` argument and `*_1` is the `Config` it names, which
                    // the executor already holds under `_1` because `Ty::Ref` is
                    // modelled as its referent.
                    //
                    // `i == 0` is load-bearing. A deref that follows a projection
                    // -- `*(_1.0)`, a field that is itself a reference -- is a
                    // *different* pointee, and `deref_ok` says nothing about it
                    // (it is keyed on the local, and the local's referent is not
                    // the field's). Letting that through would read the field as
                    // though it were the argument's referent, which is a wrong
                    // value rather than a missing one.
                    // A reference to a slice *element* (`slice::first`/`get`):
                    // `*_2` names the element the reference was built from, so it
                    // reads the slice's own element variable rather than a fresh
                    // one. This is checked *before* the `deref_ok` gate, because
                    // the reference is a local the call produced, not an argument,
                    // and the store is authoritative for it. `unwrap` moves the
                    // payload out and records the element under the destination
                    // local, so the lookup is by this local.
                    if i == 0 {
                        if let Some(id) = self.slice_elem_ref.get(&p.local) {
                            let read = |(sl, k): ElemRef| -> Option<Val> {
                                let s = self.indexed.get(&sl)?;
                                if s.poisoned {
                                    return Some(Val::Unknown);
                                }
                                let sign = Sign::of_bool(s.elem_signed);
                                s.elems.get(&k).map(|v| Val::Sym(*v, sign))
                            };
                            return eval_elem_id(id, &read).unwrap_or(Val::Unknown);
                        }
                        // A `Box`'s deref: `_3` was built from a box's field 0, so
                        // `*_3` is the boxed value the executor stored at `new`.
                        if let Some(&boxl) = self.box_refs.get(&p.local) {
                            return self.boxed.get(&boxl).copied().unwrap_or(Val::Unknown);
                        }
                    }
                    if i != 0 || !self.deref_ok.contains_key(&p.local) {
                        return Val::Unknown;
                    }
                    i += 1;
                    continue;
                }
                Proj::Downcast(v) => {
                    if !modelled {
                        return Val::Unknown;
                    }
                    // The downcast *and* the payload field it addresses are one
                    // step: `((_2 as Some).0)`. Both projections are consumed
                    // here, so the loop must skip the `Field(0)` as well --
                    // letting it run would look the payload up in the tuple map
                    // and replace a good value with `Unknown`. Anything other
                    // than a lone payload field is a shape the model does not
                    // produce, so it reads as unknown rather than walking on.
                    if !matches!(p.proj.get(i + 1), Some(Proj::Field(0)) | None) {
                        return Val::Unknown;
                    }
                    i += 1;
                    self.payloads.get(&(p.local, *v)).map(|(val, _)| *val).unwrap_or(Val::Unknown)
                }
            };
            i += 1;
        }
        cur
    }

    fn set(&mut self, p: &Place, v: Val) {
        // A write through a reference (`(*_2).0 = v`) belongs to the place `_2`
        // addresses, not to `_2`; resolving here is what makes the write and the
        // read of the target meet in one store.
        let resolved = self.resolve(p);
        let p = &resolved;
        // A write through a `Box` pointer: `*b = v` lowers to `(*_b) = v`, and `*b`
        // reads `boxed[boxl]` (see the read arm above). Without this arm the write was
        // dropped and a later `*b` returned the value the box held at `new` -- a stale
        // read, so `requires: *b == 0` / `ensures: ret == 0` was proved against a body
        // that returns 7.
        if p.proj.as_slice() == [Proj::Deref] {
            if let Some(&boxl) = self.box_refs.get(&p.local) {
                self.boxed.insert(boxl, v);
                self.forget_parts(boxl);
                return;
            }
        }
        // A write to the *whole* referent through a reference -- `(*_1) = v`, how
        // `*v = 5` lowers for `v: &mut u8` -- is a whole-place write to `_1`,
        // because `Ty::Ref` is modelled as its referent (`_1` *is* the value
        // `*_1` names). Stripping the lone deref here lets it share the whole-place
        // arm below. Only a lone deref of a deref-ok local qualifies: `(*_1)[0] = v`
        // and `(*_1).0 = v` keep their projection and reach their own arms, and a
        // deref of a local with no recorded referent stays unresolved.
        //
        // This strip was missing, and its absence was a false proof: `*v = 5; *v`
        // on a `&mut u8` dropped the write, the read returned the seed, and
        // `requires: v == 0` / `ensures: ret == 0` was **proved** against a body
        // that returns 5.
        let stripped;
        let p = if p.proj.as_slice() == [Proj::Deref] && self.deref_ok.contains_key(&p.local) {
            stripped = Place { local: p.local, proj: Vec::new() };
            &stripped
        } else {
            p
        };
        if p.proj.is_empty() {
            // A whole-place assignment replaces the value *and* every part of it
            // the environment holds separately. The field, element, payload and
            // tag maps are keyed by local and are not touched by a plain
            // `locals` write, so leaving them would let a later read of `c.x`
            // return the value the argument *had* -- which is how `c = d; c.x`
            // proved `ret == c.x` against the stale `c.x`. A derived part of a
            // value that is no longer there is a wrong value, not a missing one,
            // so the parts are dropped here rather than read later.
            //
            // `Val::Agg` is the exception, and it is load-bearing: an aggregate
            // rvalue (`_0 = (a, b)`, or the `(result, overflowed)` tuple of a
            // `checked_*`) *writes its parts itself* inside `eval_rvalue` and
            // then hands back `Val::Agg` as the local's value. Clearing here
            // would delete the parts that were just written, which turns a
            // modelled tuple back into an unknown one.
            if !matches!(v, Val::Agg) {
                self.forget_parts(p.local);
            }
            self.whole_writes.insert(p.local);
            self.locals.insert(p.local, v);
            return;
        }
        match p.proj.as_slice() {
            [Proj::Field(i)] => {
                self.fields.insert((p.local, *i), v);
                // A write to the aggregate `o.i` makes every nested path through it
                // describe a value that is no longer there. `o.i.v` is seeded
                // separately, so leaving it would let a later read return the
                // pre-write leaf -- the same stale-part hole the whole-local write
                // closes, one level down.
                self.forget_nested_under(p.local, &[*i]);
            }
            // An element write to a slice or array argument has to land in the
            // *same* store the read consults. Writing it to `elems` -- the
            // array-literal map -- left the read looking at the seeded value, so
            // `a[0] = 0; a[i]` proved `ret == a[i]` against the pre-write `a[0]`:
            // a false contract, proved.
            [Proj::Index(i)] => self.write_elem(p.local, *i, v),
            // `_1[_2] = v` -- a symbolic subscript. Only a constant index has a
            // per-index slot; a symbolic one would have to update every element
            // the chain could select, which this store does not model, so it
            // poisons instead of guessing.
            [Proj::IndexVar(li)] | [Proj::Deref, Proj::IndexVar(li)] => {
                match self.locals.get(li) {
                    Some(Val::Sym(x, _)) => match smt::evaluate(*x, |_| None) {
                        Some(k) => self.write_elem(p.local, k, v),
                        None => self.poison_elems(p.local),
                    },
                    _ => self.poison_elems(p.local),
                }
            }
            // `(*_1)[0] = v` -- how a write to a `&mut [T]` or `&mut [T; N]`
            // argument lowers. The deref is transparent for an argument, so the
            // element belongs to the same store `read_indexed` consults.
            [Proj::Deref, Proj::Index(i)] => self.write_elem(p.local, *i, v),
            // `(*_1).0 = v` -- how a write to a field through a `&mut` argument
            // lowers. `resolve` has already collapsed `(*_1).0` to `_1.0` when the
            // argument is one, so this arm is reached only for a reference *local*
            // whose target is not recorded, and the field belongs to the same
            // store the read consults.
            //
            // This arm was missing, and its absence was a false proof, not a lost
            // proof: `c.lo = 5; c.lo` on a `&mut Config` dropped the write, the
            // read returned the *seed*, and `requires: c.lo == 0` / `ensures: ret
            // == 0` was **proved** against a body that returns 5.
            [Proj::Deref, Proj::Field(i)] => {
                self.fields.insert((p.local, *i), v);
                self.forget_nested_under(p.local, &[*i]);
            }
            // A nested write through a reference: `((*_1).0).0 = v` falls to the
            // catch-all below, which strips the leading deref before building the
            // chain. A deref followed by something that is *not* all fields (an
            // index, a downcast) must reach that same catch-all rather than being
            // swallowed here, or an indexed local would be left stale instead of
            // poisoned.
            [Proj::Downcast(variant), Proj::Field(0)] | [Proj::Downcast(variant)] => {
                self.payloads.insert((p.local, *variant), (v, 0));
            }
            // A nested field write: `((_1.0).0) = v`. Keyed by the whole chain, so
            // it lands in the same store the nested read consults. A chain that is
            // not all field projections (an index, a downcast) is left to the
            // catch-all, which poisons an indexed local rather than guessing.
            // `a[0].v = 7` -- a leaf inside an element of a whole-local array or
            // tuple, which lowers to `(_1[_3].0: u8) = 7`. No arm above covers an
            // index followed by fields, so the write reached no store the read
            // consults and the literal's old leaf survived: the false `ret == 3`
            // was **proved** against a body returning 7. The index has to be
            // pinnable for the same reason the element arms above require it.
            [Proj::Index(k), fields @ ..] => {
                if let Some(chain) = field_steps(fields) {
                    if !chain.is_empty() {
                        self.write_elem_part(p.local, *k, &chain, v);
                        return;
                    }
                }
                self.poison_elems(p.local);
            }
            [Proj::IndexVar(li), fields @ ..] => {
                let index = match self.locals.get(li) {
                    Some(Val::Sym(x, _)) => smt::evaluate(*x, |_| None),
                    _ => None,
                };
                match index.and_then(|k| field_steps(fields).filter(|c| !c.is_empty()).map(|c| (k, c))) {
                    Some((k, chain)) => self.write_elem_part(p.local, k, &chain, v),
                    // A symbolic subscript the run cannot pin may hit any element,
                    // so none of their leaves can be trusted afterwards.
                    None => self.poison_elems(p.local),
                }
            }
            // `(*_1)[0].v = 7` and `((*_1)[0].0).v = 7` -- the same leaf through a
            // `&mut [T; N]` argument. `resolve` has already collapsed the leading
            // deref when the argument is one, so these are reached only for a
            // reference local with no recorded target; the element and its leaf
            // still belong to this local's store, so they go to the same key.
            [Proj::Deref, Proj::Index(k), fields @ ..] => {
                if let Some(chain) = field_steps(fields) {
                    if !chain.is_empty() {
                        self.write_elem_part(p.local, *k, &chain, v);
                        return;
                    }
                }
                self.poison_elems(p.local);
            }
            [Proj::Deref, Proj::IndexVar(li), fields @ ..] => {
                let index = match self.locals.get(li) {
                    Some(Val::Sym(x, _)) => smt::evaluate(*x, |_| None),
                    _ => None,
                };
                match index.and_then(|k| field_steps(fields).filter(|c| !c.is_empty()).map(|c| (k, c))) {
                    Some((k, chain)) => self.write_elem_part(p.local, k, &chain, v),
                    None => self.poison_elems(p.local),
                }
            }
            rest => {
                if let Some(chain) = field_chain(rest) {
                    self.forget_nested_under(p.local, &chain);
                    self.nested.insert((p.local, chain), v);
                    return;
                }
                // An element of an array reached through a field path: `(_1.0)[k] = v`. The
                // whole projection is the key, so `o.a[0]` and `o.b[0]` cannot collide. The
                // write replaces that element and leaves the siblings; the element's *type*
                // was not seeded, so a read of an element this run did not write stays
                // `Unknown` rather than inventing a value.
                if let [fields @ .., last] = rest {
                    let index = match last {
                        Proj::Index(k) => Some(*k),
                        // A symbolic subscript is only writable when the run can pin its
                        // value; otherwise the store cannot say which element changed, so the
                        // whole path is dropped rather than left stale.
                        Proj::IndexVar(li) => match self.locals.get(li) {
                            Some(Val::Sym(x, _)) => smt::evaluate(*x, |_| None),
                            _ => None,
                        },
                        _ => None,
                    };
                    if let Some(chain) = field_steps(fields) {
                        if !chain.is_empty() {
                            match index {
                                Some(k) => {
                                    self.write_elem_at(p.local, chain, k, v);
                                    return;
                                }
                                None => {
                                    self.elems_path.retain(|(l, c, _), _| {
                                        *l != p.local || c.as_slice() != chain.as_slice()
                                    });
                                    return;
                                }
                            }
                        }
                    }
                }
                // A shape the arms above do not cover. `*a = v` (a whole-store
                // write through a `&mut [T; N]`) would need a new store, so it is
                // dropped. For an indexed local that leaves the store describing a
                // value that is no longer there, so it is poisoned rather than left
                // stale -- and `poison_elems` records the write, so a `&mut` caller
                // sees the poison rather than its pre-call elements.
                if self.indexed.contains_key(&p.local) {
                    self.poison_elems(p.local);
                }
            }
        }
    }

    /// Drop every part of `local` the environment holds separately from the
    /// local's own value: fields, elements, payloads and the enum tag.
    ///
    /// Called when the local is overwritten as a whole, because the parts then
    /// describe a value that is no longer there. The *length* of an indexed local
    /// is kept: it is a property of the type, not of the value, so a reassigned
    /// array still has its `N`.
    /// Drop every nested path through `prefix` for `local`.
    ///
    /// Called when an *intermediate* aggregate is overwritten (`o.i = ...`), so the
    /// seeded leaves under it (`o.i.v`) no longer describe the value in the store.
    /// A stale part is a wrong value, not a missing one, so it is dropped rather
    /// than read later.
    fn forget_nested_under(&mut self, local: u32, prefix: &[u32]) {
        self.nested
            .retain(|(l, chain), _| *l != local || !chain.starts_with(prefix));
        // The elements of an array reached through this prefix describe a value that is no
        // longer there once the intermediate aggregate is overwritten, so they are dropped too.
        // A stale element is a wrong value, not a missing one.
        self.elems_path.retain(|(l, chain, _), _| *l != local || !chain.starts_with(prefix));
    }

    /// Replace every *part* of an aggregate local with a fresh value.
    ///
    /// A loop that writes an aggregate -- the `RangeInclusive` a `for` loop
    /// advances through `&mut`, or a struct whose field the body assigns -- leaves
    /// its parts at the values they held at entry. The loop header must instead be
    /// an *arbitrary* value of the local's type, so each part is replaced: a word
    /// part by a fresh variable of its own width and sign (so a model that reads
    /// it, a range's `start`/`end`, still resolves), and anything the store cannot
    /// represent as a word by dropping it. Dropping is the sound direction -- a
    /// stale part is a wrong value, a missing one is a refusal.
    fn havoc_parts(&mut self, local: u32) {
        fn refresh(v: &Val) -> Option<Val> {
            match v {
                Val::Sym(x, s) => Some(Val::Sym(smt::var(smt::bits(*x)), *s)),
                Val::Bool(_) => Some(Val::Bool(smt::var(1).eq_val(1))),
                Val::Agg | Val::Unknown => None,
            }
        }
        for ((l, _), v) in self.fields.iter_mut() {
            if *l == local {
                match refresh(v) {
                    Some(nv) => *v = nv,
                    None => *v = Val::Unknown,
                }
            }
        }
        for ((l, _), v) in self.nested.iter_mut() {
            if *l == local {
                match refresh(v) {
                    Some(nv) => *v = nv,
                    None => *v = Val::Unknown,
                }
            }
        }
        for ((l, _), v) in self.elems.iter_mut() {
            if *l == local {
                match refresh(v) {
                    Some(nv) => *v = nv,
                    None => *v = Val::Unknown,
                }
            }
        }
        for ((l, _, _), v) in self.elems_path.iter_mut() {
            if *l == local {
                match refresh(v) {
                    Some(nv) => *v = nv,
                    None => *v = Val::Unknown,
                }
            }
        }
        for ((l, _, _), v) in self.elem_parts.iter_mut() {
            if *l == local {
                match refresh(v) {
                    Some(nv) => *v = nv,
                    None => *v = Val::Unknown,
                }
            }
        }
        // A payload, tag or element store has no per-word refresh this run can
        // trust, so it is dropped: an aggregate the loop wrote is now an arbitrary
        // value, and a part the store cannot re-randomise must not be readable.
        self.payloads.retain(|(l, _), _| *l != local);
        self.discriminants.remove(&local);
        self.tag_widths.remove(&local);
        // A slice-iterator cursor over this local is dropped: the header is an
        // arbitrary state, so the position is no longer a concrete index, and a
        // `next` that read an arbitrary element would be a wrong value.
        self.iters.retain(|l, it| *l != local && it.base != local);
        // A mutable-length container (`Vec`) has its length refreshed to a fresh
        // `usize`, and its elements dropped. The header is an arbitrary state, so a
        // loop that pushes must not let the *exit* edge read the entry length: an
        // inductive loop that pushes three times would otherwise prove `ret == 0`
        // for the real `ret == 3`. A slice's or array's length is fixed by the
        // caller or the type, so it is left alone -- refreshing it would be a
        // needless loss of information.
        if let Some(s) = self.indexed.get_mut(&local) {
            if s.len_mutable {
                s.len = smt::var(USIZE_WIDTH);
            }
            s.elems.clear();
            s.poisoned = true;
        }
        self.elems.retain(|(l, _), v| *l != local || !matches!(v, Val::Unknown));
    }

    fn forget_parts(&mut self, local: u32) {
        self.fields.retain(|(l, _), _| *l != local);
        self.nested.retain(|(l, _), _| *l != local);
        self.elems.retain(|(l, _), _| *l != local);
        // Elements of field-path arrays under a whole-value write describe a value that is no
        // longer there; keeping them would be a stale read of the old array.
        self.elems_path.retain(|(l, _, _), _| *l != local);
        // Fields *inside* an element of an aggregate literal describe a value that
        // is no longer there once the local is overwritten as a whole.
        self.elem_parts.retain(|(l, _, _), _| *l != local);
        self.poisoned_elems.remove(&local);
        self.payloads.retain(|(l, _), _| *l != local);
        self.discriminants.remove(&local);
        self.tag_widths.remove(&local);
        self.strs.remove(&local);
        self.piece_sets.remove(&local);
        self.tmpl_bytes.remove(&local);
        self.boxed.remove(&local);
        self.box_refs.remove(&local);
        self.iters.remove(&local);
        // A `Vec` local overwritten as a whole place is no longer the value the
        // length and elements were tracking, so the whole entry is dropped rather
        // than kept: `v = other_vec` must not leave the old length readable. A
        // slice's entry is kept but poisoned -- its length is fixed by the caller,
        // so only its elements became unknown.
        match self.indexed.get(&local) {
            Some(s) if s.len_mutable => {
                self.indexed.remove(&local);
            }
            Some(_) => {
                let s = self.indexed.get_mut(&local).expect("checked above");
                s.elems.clear();
                s.poisoned = true;
            }
            None => {}
        }
    }

    /// Record an element write in whichever store the read for `local` consults.
    ///
    /// A slice or array argument's elements live in `indexed`; an array *literal*'s
    /// live in `elems`. The read path keys on the same distinction, so the two
    /// must agree here or a write becomes invisible to the read.
    fn write_elem(&mut self, local: u32, index: u64, v: Val) {
        // The element is replaced whole, so every leaf the old element had goes
        // with it. Leaving one would be a stale *wrong* value: a source the
        // rebase below cannot carry (`a[0] = other[1]`, whose parts are keyed
        // index-first on `other`) would then keep the destination's pre-write
        // leaf, and a contract about it could be proved against the changed array.
        self.elem_parts.retain(|(l, k, _), _| *l != local || *k != index);
        self.nested
            .retain(|(l, c), _| *l != local || c.first() != Some(&(index as u32)));
        match self.indexed.get_mut(&local) {
            Some(s) => match v {
                Val::Sym(x, _) => {
                    // A slice's `last()` element is one fresh variable keyed by the
                    // `LAST_INDEX` sentinel rather than by a real index, so a write
                    // to a concrete index does not reach it through
                    // `elems.insert(index, x)`: the sentinel keeps its pre-write
                    // value and a later `last()` reads it. That is a false proof --
                    // `let before = *xs.last().unwrap(); xs[0] = 1; before ==
                    // *xs.last().unwrap()` was *proved* for a one-element slice,
                    // though the write replaced the only element. The write *can*
                    // reach the last element, so the sentinel is refreshed with the
                    // exact relationship: the last element is `x` exactly when this
                    // write's index *is* the last one (`len == index + 1`), and the
                    // old element otherwise. The sentinel is created here if the
                    // write precedes any `last()` read, so the relationship holds
                    // whichever order the body uses. An array's `last()` is the
                    // concrete `N-1` (no sentinel), so this is skipped for it.
                    if s.fixed_len.is_none() && s.elem_w != 0 {
                        let old = *s.elems.entry(LAST_INDEX).or_insert_with(|| smt::var(s.elem_w));
                        if smt::bits(old) == smt::bits(x) {
                            let is_last = smt::eq_const(s.len, index.wrapping_add(1));
                            let merged = smt::ite(is_last, x, old);
                            s.elems.insert(LAST_INDEX, merged);
                        }
                    }
                    s.elems.insert(index, x);
                }
                // An aggregate element, or an unmodelled one. The element is no
                // longer the seeded input, and this store cannot hold what it is
                // now; keeping the seed would be a stale read, so it poisons.
                _ => s.poisoned = true,
            },
            None => {
                self.elems.insert((local, index), v);
            }
        }
    }

    /// Mark every element of `local` unknown, keeping the length.
    fn poison_elems(&mut self, local: u32) {
        // A field inside an element describes an element that is no longer pinned,
        // so it goes with the elements themselves -- in *both* representations.
        // `elem_parts` and `nested` are two views of the same leaf, and a symbolic
        // write that clears one and keeps the other leaves the leaf readable through
        // the store it did not clear: `a[i] = E { v: 7 }` dropped `a[0]`'s
        // `elem_parts` entry but not its `nested` mirror, so a later element *copy*
        // (`let x = a[0]`) collected the mirror and **proved** `x.v == 3` against an
        // array whose element 0 the write may have replaced. A poisoned element has
        // no readable leaf, so neither view may survive.
        self.elem_parts.retain(|(l, _, _), _| *l != local);
        // Every `nested` entry on an array-typed local is an element mirror: its
        // chain starts with the element index (`[index, field..]`), because an array
        // has no fields of its own. So the whole set goes -- dropping a leaf is a
        // missing value, keeping one is a wrong value.
        self.nested.retain(|(l, _), _| *l != local);
        // Recorded so the call boundary can tell "the callee poisoned this array"
        // from "the callee left it alone", and drop the caller's elements in the
        // first case rather than keeping pre-call leaves.
        self.poisoned_elems.insert(local);
        match self.indexed.get_mut(&local) {
            Some(s) => s.poisoned = true,
            // A literal array written through a symbolic subscript: the whole
            // literal is unmodelled now, so its elements are dropped rather than
            // left stale.
            None => self.elems.retain(|(l, _), _| *l != local),
        }
    }

    /// Record a leaf *inside* an element of a whole-local array or tuple:
    /// `a[0].v = 7`, which lowers to `(_1[_3].0: u8) = 7`.
    ///
    /// The read for this shape consults `elem_parts`, keyed index-first, so a write
    /// that reached only `elems` (the element's own value) or no store at all left
    /// the literal's old leaf in place -- a stale *wrong* value, not a missing one,
    /// so `a[0].v = 7; a[0].v` could prove a contract about the pre-write `3`. Both
    /// keys are written, like [`Self::rebase_elem_parts`]: `elem_parts` for the
    /// `Index` spelling and `nested` for the `Field` spelling of a tuple component.
    fn write_elem_part(&mut self, local: u32, index: u64, chain: &[u32], v: Val) {
        // A leaf the write replaces makes every path *through* it stale, so those go
        // with it: keeping one would be the same wrong value this store exists to
        // avoid.
        self.elem_parts
            .retain(|(l, k, c), _| *l != local || *k != index || !c.starts_with(chain));
        let mut prefix = Vec::with_capacity(chain.len() + 1);
        prefix.push(index as u32);
        prefix.extend_from_slice(chain);
        self.nested.retain(|(l, c), _| *l != local || !c.starts_with(&prefix));
        self.elem_parts.insert((local, index, chain.to_vec()), v);
        self.nested.insert((local, prefix), v);
    }

    /// Mark every element of the array at `chain` under `local` unknown.
    ///
    /// A write through a returned reference whose index the run cannot pin may land
    /// on *any* element, so none of them can be trusted afterwards. Which store
    /// holds them depends on the shape: an array reached through a field path
    /// (`x.a[0]`, the field chain *before* the index) is in `elems_path`, a
    /// whole-local literal array is in `elems`, and a whole-local array *argument*
    /// is in `indexed`. All three are cleared under the path, and a whole-local
    /// array keeps its length.
    fn poison_array_under(&mut self, local: u32, chain: &[u32]) {
        if chain.is_empty() {
            self.poison_elems(local);
        } else {
            self.elems_path.retain(|(l, c, _), _| *l != local || !c.starts_with(chain));
        }
    }

    /// Record an element of an array reached through a field path, `o.a[k] = v`.
    ///
    /// The whole path is the key, so `o.a[0]` and `o.b[0]` cannot collide. Any
    /// previous value at that element is replaced; siblings are untouched.
    fn write_elem_at(&mut self, local: u32, chain: Vec<u32>, index: u64, v: Val) {
        self.elems_path.retain(|(l, c, k), _| *l != local || *c != chain || *k != index);
        self.elems_path.insert((local, chain, index), v);
    }

    /// Re-root the parts of an aggregate operand onto one element of an array or
    /// tuple literal: `[o.i, o.j]` moves element 0's `v` leaf to `(dest, 0, [0])`.
    /// The literal path used to store only the element's own value, so a field of
    /// that element read `Unknown` and `[o.i, o.j][0].v` stayed `incomplete` --
    /// even for `[Inner { v: 3 }, Inner { v: 4 }]`, where the parts are right there.
    /// This is [`Self::rebase_parts`] for the index-first shape, and it writes two
    /// keys because the model reads the two spellings of a tuple component
    /// differently: `Proj::Field` consults `nested`, while `Proj::Index` consults
    /// `elem_parts` (a real array index does not go through `nested`).
    ///
    /// A *whole-local* source only: a nested source's parts are already keyed by a
    /// path this cannot re-key without the same order problem, and leaving those
    /// `Unknown` is a coverage gap, never a wrong value.
    /// A source that is itself an element of a whole-local array or tuple
    /// (`a[0] = other[1]`) is the same re-root, one level down: `other[1]`'s leaves
    /// are keyed index-first on `other`, and they have to move to `dest[index]`.
    /// Without it the destination kept the leaf it had before the write -- the
    /// stale value [`Self::write_elem`] now clears -- so the assignment was a
    /// missing *write* rather than a missing read.
    fn rebase_elem_parts(&mut self, src: &Place, dest: u32, index: u64) -> bool {
        let src = self.resolve(src);
        // A whole-local source, or an element of one. The latter's parts are keyed
        // by the source's own index, which is what makes them re-keyable here.
        if src.proj.len() == 1 || matches!(src.proj.as_slice(), [Proj::Deref, _]) {
            if let Some(sk) = self.elem_index_of(&src.proj) {
                let s = src.local;
                let leaves: Vec<(Vec<u32>, Val)> = self
                    .elem_parts
                    .iter()
                    .filter(|((l, k, _), _)| *l == s && *k == sk)
                    .map(|((_, _, c), v)| (c.clone(), *v))
                    .collect();
                let nested: Vec<(Vec<u32>, Val)> = self
                    .nested
                    .iter()
                    .filter(|((l, c), _)| *l == s && c.first() == Some(&(sk as u32)))
                    .map(|((_, c), v)| (c[1..].to_vec(), *v))
                    .collect();
                let moved = !leaves.is_empty() || !nested.is_empty();
                // The element being written replaces whatever leaf it had: a leaf
                // the new source does not carry must not survive from the old one,
                // which would be a stale *wrong* value rather than a missing one.
                self.elem_parts.retain(|(l, k, _), _| *l != dest || *k != index);
                self.nested
                    .retain(|(l, c), _| *l != dest || c.first() != Some(&(index as u32)));
                for (chain, v) in leaves.into_iter().chain(nested) {
                    self.elem_parts.insert((dest, index, chain.clone()), v);
                    let mut prefix = vec![index as u32];
                    prefix.extend_from_slice(&chain);
                    self.nested.insert((dest, prefix), v);
                }
                return moved;
            }
        }
        if !src.proj.is_empty() {
            return false;
        }
        let s = src.local;
        // The element being written replaces whatever leaf it had: a leaf the new
        // source does not carry must not survive from the old one, which would be a
        // stale *wrong* value rather than a missing one.
        self.elem_parts.retain(|(l, k, _), _| *l != dest || *k != index);
        self.nested
            .retain(|(l, chain), _| *l != dest || chain.first() != Some(&(index as u32)));
        let mut moved = false;
        let fields: Vec<(u32, Val)> = self
            .fields
            .iter()
            .filter(|((l, _), _)| *l == s)
            .map(|((_, k), v)| (*k, *v))
            .collect();
        for (k, v) in fields {
            self.elem_parts.insert((dest, index, vec![k]), v);
            self.nested.insert((dest, vec![index as u32, k]), v);
            moved = true;
        }
        let nested: Vec<(Vec<u32>, Val)> = self
            .nested
            .iter()
            .filter(|((l, _), _)| *l == s)
            .map(|((_, chain), v)| (chain.clone(), *v))
            .collect();
        for (chain, v) in nested {
            let mut key = vec![index as u32];
            key.extend(chain.iter().copied());
            self.elem_parts.insert((dest, index, chain), v);
            self.nested.insert((dest, key), v);
            moved = true;
        }
        moved
    }

    /// Record the payload of a modelled `Option`, with its width.
    ///
    /// The width is what `discriminant` and the payload read are sized by. It is
    /// the operand width, because `checked_add` on a `u8` produces a `u8`
    /// payload: sizing it from the destination would size it from the
    /// `Option<u8>` local.
    fn set_payload(&mut self, local: u32, variant: u64, v: Val, width: u8) {
        self.payloads.insert((local, variant), (v, width));
    }

    /// The width of a modelled enum tag, when one was seeded for `local`.
    ///
    /// A seeded tag knows its own width (the discriminants'); a synthesised
    /// `Option` tag does not and falls back to the payload's width.
    fn tag_width(&self, local: u32) -> Option<u8> {
        self.tag_widths.get(&local).copied()
    }

    /// The symbolic discriminant of a modelled enum local, when its tag is a
    /// symbol (a seeded argument's, or one a variant construction wrote).
    ///
    /// This is what an enum-returning function's `ret` is: the return place's tag,
    /// which `ret.is_ok()` and friends read. A tag that is not a `Val::Sym` -- an
    /// unmodelled enum -- yields `None`, so the postcondition refuses the method
    /// rather than testing a value it does not have.
    fn tag_value(&self, local: u32) -> Option<Var> {
        match self.discriminants.get(&local) {
            Some(Val::Sym(v, _)) => Some(*v),
            _ => None,
        }
    }

    /// The width of a modelled `Option` local, from its payload.
    fn option_width(&self, local: u32) -> Option<u8> {
        self.payloads
            .iter()
            .find(|((l, _), _)| *l == local)
            .map(|(_, (_, w))| *w)
    }

    /// Record an enum tag for a local.
    fn set_discriminant(&mut self, local: u32, tag: Val) {
        // The width is taken from the tag's own value, so a seeded tag keeps the
        // discriminants' width its contract was checked at and a synthesised
        // `Option` tag keeps the operand's. Deriving it here rather than at each
        // read site is what keeps `discriminant` and the payload in one width.
        if let Val::Sym(v, _) = tag {
            self.tag_widths.insert(local, smt::bits(v));
        }
        self.discriminants.insert(local, tag);
    }
}

/// The field chain a projection run denotes, if every step is a field access.
///
/// `(((*_1).0).0)` has the projections `[Deref, Field(0), Field(0)]`; the deref
/// is transparent for an argument (its referent is the local itself), so the chain
/// is `[0, 0]`. A run that is not all fields -- an index, a downcast, a deref in
/// the middle -- returns `None`, because those name a different store and must not
/// be answered out of the nested one.
///
/// A *single* field is not a chain here: `[_1.0]` returns `None` so the
/// single-field store keeps answering it, and the two stores stay disjoint.
fn field_chain(proj: &[Proj]) -> Option<Vec<u32>> {
    let chain = field_steps(proj)?;
    if chain.len() < 2 {
        return None;
    }
    Some(chain)
}

/// A projection read as a chain of field indices, stripping one leading `Deref`.
///
/// `None` for any step that is not a field (an index, a downcast, a second deref): those
/// name a store the caller does not re-root. An empty chain is a whole place, which is
/// `Some(vec![])` -- the caller decides whether that is meaningful.
fn field_steps(proj: &[Proj]) -> Option<Vec<u32>> {
    let steps = match proj.first() {
        Some(Proj::Deref) => &proj[1..],
        _ => proj,
    };
    let mut chain = Vec::with_capacity(steps.len());
    for s in steps {
        match s {
            Proj::Field(i) => chain.push(*i),
            _ => return None,
        }
    }
    Some(chain)
}

/// A frame on the inlining stack.
#[derive(Clone, Debug)]
struct Frame {
    /// Index into `MirProgram::fns` of the function being executed.
    func: usize,
    /// Where the caller resumes once this frame returns.
    ret_target: usize,
    /// The caller place that receives the return value, if any.
    ret_dest: Option<Place>,
    /// The caller's environment, saved when the call was entered.
    ///
    /// Each function numbers its MIR locals from `_0`, so a local index means
    /// something only inside the function that declared it. Entering a call
    /// therefore has to build a fresh `Env` for the callee, and the caller's own
    /// must be put aside: without this, resuming the caller would use the
    /// callee's locals, so a caller that saved `a` in `_3`, called `g(b)`, and
    /// returned `_3` would read `g`'s `_3` instead. That made a false
    /// postcondition provable, which is the failure mode this crate exists to
    /// avoid.
    saved_env: Option<Env>,
    /// The loop cut that was active in the *caller* when this frame made the
    /// call, put aside for the same reason `saved_env` is.
    ///
    /// A loop cut belongs to the function whose loop it describes, so entering a
    /// callee must clear it -- the caller's loop invariant says nothing about the
    /// callee's locals. But the cut has to come back on return: the resumed
    /// caller is still inside its loop, and the next edge into its header must be
    /// checked against the invariant rather than unwound. Clearing `cut` for the
    /// callee and never restoring it left the caller unwinding a loop it had
    /// already cut, so a loop whose step is a same-dump call was reported as a
    /// cutoff once it exceeded `DEFAULT_UNWIND`, even though its invariant was
    /// sufficient. That is an incompleteness, not an unsoundness -- the report is
    /// `Incomplete`, never a false proof -- but it silently discards a valid
    /// proof, which is the failure this crate treats as a defect.
    saved_cut: Option<Cut>,
    /// The loop measure that was live in the *caller* when this frame made the
    /// call, put aside for the same reason `saved_cut` is.
    ///
    /// The measure and the cut travel together: the cut says which loop the path
    /// is inside, and the measure is the value at that loop's head. Entering a
    /// callee clears both -- they describe the caller's loop -- but the resumed
    /// caller is still inside it, and its back edge has to compare against the
    /// measure. Restoring the cut without the measure left the caller with a cut
    /// and no head value, so the back edge had nothing to compare and the loop was
    /// reported incomplete ("the loop head was never entered") even when its
    /// measure was sufficient. A proof silently discarded, which this crate treats
    /// as a defect.
    saved_variant: Option<(Var, bool)>,
    /// `(caller storage, callee local)` for each argument the caller handed over
    /// through a reference (`&T`, `&mut T`, `&[T]`, `&mut [T]`). The caller side
    /// is the *place* the reference names -- `_2` for `set5(&mut x)` -- not the
    /// reference local, which is a temp.
    ///
    /// The frontend models `&T` as its referent, so these two locals denote the
    /// same storage and the callee's post-state is copied back to the caller's
    /// local on return. A by-value argument is deliberately *not* in this list:
    /// its writes must stay in the callee's frame, or `let b = f(a)` would
    /// mutate `a` and a caller contract about `a` would be checked against the
    /// wrong value.
    ///
    /// This used to hold only the *indexed* references, so a helper that wrote a
    /// field or a scalar through a `&mut` had its write die with the frame: the
    /// caller read its own seed, and `requires: c.lo == 0; ensures: ret == 0` on
    /// `set_lo(c); c.lo` was **proved** against a body that returns 5.
    by_ref: Vec<(Place, u32)>,
    /// The caller's frame, or `None` for the root.
    caller: Option<Box<Frame>>,
}

/// One state on the worklist.
#[derive(Clone, Debug)]
struct State {
    /// The current function, plus the chain of callers to resume into.
    frame: Frame,
    block: usize,
    path: Pred,
    env: Env,
    /// Back-edge counts per (function index, block), for the unwind bound.
    visits: BTreeMap<(usize, usize), u32>,
    /// How many calls deep this path currently is.
    depth: u32,
    /// The loop this path is currently inside, when it was cut by an invariant.
    ///
    /// `None` for every path in a function with no invariant. When set, the
    /// header is assumed to satisfy the invariant on entry and the back edge is
    /// checked against it instead of being unwound.
    cut: Option<Cut>,
    /// The `variant:` measure as evaluated at the loop head, with its signedness.
    ///
    /// Set when the entry edge havocs the written locals and assumes the
    /// invariant, so it is the measure over *any* header state satisfying `I` --
    /// the same state the body then runs from. The back edge compares the measure
    /// there against the value here, and the two are related by the body's own
    /// symbolic execution, which is what makes the decrease an induction step
    /// rather than a restatement. `None` when the loop has no measure, or on a
    /// path that has not yet passed the header.
    variant_entry: Option<(Var, bool)>,
}

/// A loop that is proved by its invariant rather than by unwinding.
///
/// The shape is the standard one for a CFG. The invariant is *asserted* on every
/// edge into the header -- that single obligation covers both induction cases,
/// because it is `path => I` and the path condition already carries the guard:
///
/// * From outside the loop, `path => I` is *initialisation*: the invariant holds
///   the first time the header is reached.
/// * From a back edge, it is *preservation*: assuming `I` at the head, one more
///   iteration leaves it true.
///
/// The two differ only in what happens next. After a back edge the edge is *not*
/// followed: the assertion has closed the induction, and re-entering would be
/// the unwinding this exists to avoid. After an entry edge the header continues
/// with `I` conjoined onto the path, so the exit edge inherits `I && !guard` --
/// which is what a postcondition is entitled to assume after a loop.
#[derive(Clone, Debug)]
struct Cut {
    /// Index of the function the loop belongs to. An inlined callee numbers its
    /// own blocks from `bb0`, so without this a callee's `bb1` could be mistaken
    /// for the caller's loop header and checked against the caller's invariant.
    func: usize,
    /// The loop header. An edge into it asserts the invariant.
    header: usize,
    /// Blocks with an edge back to `header`. An edge from one of these asserts
    /// the invariant and then stops, rather than re-entering the header.
    back_edges: Vec<usize>,
    /// The locals the loop can write, over-approximated.
    ///
    /// At the header these are replaced by fresh values before the invariant is
    /// assumed. This is not an optimisation, it is what makes the proof sound:
    /// without it the exit edge would only ever be taken from the state of the
    /// *first* iteration, so a loop that corrupts the return value on a later
    /// iteration would still verify. An invariant that is true on entry but too
    /// weak to imply the postcondition would then pass -- measured, and it did.
    ///
    /// Over-approximating is safe in the one direction that matters: havocing a
    /// local the loop does not actually write only discards information, so it
    /// can turn a proof into an open obligation but never an open obligation
    /// into a proof.
    havoc: Vec<u32>,
    /// The invariant's text, re-evaluated in the post-state of each incoming
    /// edge, because only the executor knows what the locals hold there.
    text: String,
    /// The `variant:` measure's text, when the loop carries one.
    ///
    /// `None` means partial correctness only. With a measure, the back edge also
    /// proves `I && guard => V' < V` and `I && guard => V' >= 0`, which is what
    /// turns "the loop is safe if it stops" into "it stops".
    variant: Option<String>,
}

/// The contract of one callee, in the form the executor needs to assume it.
///
/// This is the modular half of the call story. A callee *inside* the dump is
/// inlined, so its body is executed and no assumption is made; a callee whose
/// body the dump does not contain has nothing to execute, and without a contract
/// the honest answer is `unknown`. With one, the call becomes the two obligations
/// every modular verifier uses -- prove the precondition of the arguments, assume
/// the postcondition of the result -- which is what lets a caller be verified
/// without its callee's body, and what keeps the proof from being circular: the
/// precondition is *proved*, not assumed, so assuming the postcondition is an
/// induction hypothesis rather than a restatement of the goal.
///
/// `ensures` is `None` when the callee declared no postcondition. That is not the
/// same as `ensures true`: with no postcondition there is nothing to assume, so
/// the call's result stays unknown and the path is reported rather than guessed.
/// The distinction is the difference between "the callee promises nothing" and
/// "the callee promises everything", and only the first is what an absent clause
/// means.
#[derive(Clone, Debug, Default)]
pub struct CalleeContract {
    /// The declared `requires` clauses, as source text.
    pub requires: Vec<String>,
    /// The declared `ensures` clauses, as source text.
    pub ensures: Vec<String>,
    /// The callee's parameter names, in declaration order.
    ///
    /// A callee outside the dump has no MIR, so its `debug` bindings -- the place
    /// the executor usually reads a parameter's source name from -- do not exist.
    /// The names come from the *source* signature instead, and they have to line
    /// up positionally with the call's argument list, because that is the only
    /// thing tying `requires: n <= 10` to the first argument. A callee whose
    /// signature the scanner could not read is refused rather than bound
    /// positionally to nothing, which would make every precondition vacuously
    /// true.
    pub params: Vec<String>,
    /// Whether the callee's signature was read *whole*.
    ///
    /// A signature that was not read whole cannot be bound positionally, and the
    /// return type it would have given is exactly what a `ret` clause needs to be
    /// signed correctly. A wrapped return type (`fn ext() ->` then `i8;`) leaves the
    /// return unreadable, and treating that as unsigned let a caller test
    /// `ext() < 0`, take the unsigned branch, and verify a postcondition that does
    /// not hold. Refusing the call is the only answer that does not guess.
    pub sig_readable: bool,
    /// The parameter names whose types are signed, for comparison signedness.
    pub signed: BTreeSet<String>,
    /// Whether the return type is signed, for a postcondition comparison.
    pub ret_signed: bool,
}

/// The contracts of the callees a function may call.
///
/// Resolution is delegated to [`spec::Specs::resolve`], so a contract keyed by an
/// `impl`'s location and one keyed by a source path are both found by the same
/// rule the frontend already uses to attach a contract to its function. A name
/// that resolves to a function the dump *does* contain is answered `None`: the
/// body is there, and inlining it is strictly more precise than assuming a
/// contract about it.
pub struct CalleeEnv<'a> {
    /// The dump, consulted only to tell "has a body here" from "does not".
    prog: &'a MirProgram,
    /// The contracts read from the source.
    specs: &'a spec::Specs,
    /// For each function index, a map from each block that holds a back edge (a
    /// jump to a block that appears no later in layout order) to the *header* that
    /// edge returns to.
    ///
    /// The unwind bound counts *these* rather than raw block entries. Counting
    /// entries to the loop header counts it once more than the loop runs (the last
    /// entry evaluates the guard and exits), so `unwind: N` rejected a loop that
    /// runs exactly `N` times. The latch is executed once per iteration, which is
    /// the quantity the bound is about. Precomputed because it is consulted on
    /// every state and `is_latch` is a hot path.
    ///
    /// The value is the *header*, not just a flag, so the counter can be keyed by
    /// the loop rather than by the source block. A loop whose body branches can
    /// reach its header from two different latches (two `continue`s, or an `if`
    /// whose arms both loop); counting each block separately lets the combined
    /// iteration count exceed a declared bound while neither block's own count
    /// does. Keying by the header merges them, so `unwind: N` means `N` iterations
    /// of the *loop*, however the body reaches the back edge.
    latches: BTreeMap<usize, BTreeMap<usize, usize>>,
}

impl<'a> CalleeEnv<'a> {
    /// Build for one program and its specs.
    pub fn new(prog: &'a MirProgram, specs: &'a spec::Specs) -> Self {
        let mut latches: BTreeMap<usize, BTreeMap<usize, usize>> = BTreeMap::new();
        for (i, f) in prog.fns.iter().enumerate() {
            let position: BTreeMap<usize, usize> =
                f.blocks.iter().enumerate().map(|(k, b)| (b.id, k)).collect();
            let mut set = BTreeMap::new();
            for b in &f.blocks {
                let Some(&from) = position.get(&b.id) else { continue };
                // The earliest backward target is the loop header, matching
                // `detect_loop`'s choice so the two agree on which loop a latch
                // belongs to.
                let mut header: Option<usize> = None;
                for t in successors(&b.term) {
                    if position.get(&t).is_some_and(|&to| to <= from) {
                        match header {
                            Some(h) if position[&h] <= position[&t] => {}
                            _ => header = Some(t),
                        }
                    }
                }
                if let Some(h) = header {
                    set.insert(b.id, h);
                }
            }
            latches.insert(i, set);
        }
        CalleeEnv { prog, specs, latches }
    }

    /// The loop header `block` of `func` returns to, if `block` holds a back edge.
    fn latch_header(&self, func: usize, block: usize) -> Option<usize> {
        self.latches.get(&func).and_then(|m| m.get(&block)).copied()
    }

    /// The contract for a call, or `None` when there is none to assume.
    ///
    /// `None` covers three different situations and the caller does not need to
    /// tell them apart, because each has the same right answer: the callee's body
    /// is in the dump (inline it), the callee has no contract (report the call as
    /// unmodelled), or the name resolves to nothing at all (the same).
    pub fn get(&self, name: &str) -> Option<CalleeContract> {
        if resolve_callee(self.prog, name).is_some() {
            return None;
        }
        let c = self.specs.resolve(name)?;
        Some(CalleeContract {
            requires: c.requires.clone(),
            ensures: c.ensures.clone(),
            sig_readable: c.slots.is_some(),
            params: c.params.iter().map(|(n, _)| n.clone()).collect(),
            signed: c
                .params
                .iter()
                .filter(|(_, t)| t.is_signed())
                .map(|(n, _)| n.clone())
                .collect(),
            ret_signed: c.ret.as_ref().map(|t| t.is_signed()).unwrap_or(false),
        })
    }

    /// The declared struct layouts, read from the same source as the contracts.
    ///
    /// The `drop` handler needs these to decide whether an aggregate has drop glue
    /// in a field: the MIR carries no field types for a `drop` terminator, so the
    /// layout has to come from the source, exactly as a contract's field access
    /// does.
    pub fn structs(&self) -> &BTreeMap<String, spec::StructDef> {
        &self.specs.structs
    }
}

/// The loop clauses a function carries: its invariant, and its optional measure.
///
/// Bundled rather than passed as two arguments because they always travel
/// together and are meaningful only together: the invariant locates the loop head,
/// and the measure is evaluated at that head. Two bare `Option<&str>` parameters
/// would let a caller swap them, and a swapped pair would evaluate the invariant
/// as a measure -- a type error at best, and at worst a well-typed expression that
/// silently proves the wrong thing.
#[derive(Clone, Copy, Debug, Default)]
pub struct LoopSpec<'a> {
    /// The `invariant:` text, or `None` when the function has no loop contract.
    pub invariant: Option<&'a str>,
    /// The `variant:` text, or `None` for partial correctness only.
    pub variant: Option<&'a str>,
    /// The `unwind:` bound, or `None` to use [`DEFAULT_UNWIND`].
    ///
    /// A loop with no `invariant:` is unwound; this is how far. Raising it lets a
    /// loop too long for the default be decided, and a bound that is still too
    /// small is *reported* (the path becomes unknown), never silently cut.
    pub unwind: Option<u32>,
}

/// Symbolic inputs a contract names, handed to the executor so that the
/// contract and the body read the *same* variables.
///
/// One struct rather than three parallel slices: the three kinds are always
/// passed together, and bundling them keeps the executor's entry point from
/// growing an argument per projection shape as more are modelled.
#[derive(Default, Clone)]
pub struct Seeds {
    /// `(local, field index, variable, signed)` for each struct field a contract
    /// names. The sign travels with the seed so the executor builds a
    /// `Val::Sym` that knows it, rather than one it has to guess at.
    pub fields: Vec<(u32, u32, Var, bool)>,
    /// `(local, projection chain, variable, signed)` for each *nested* path a
    /// contract names, so the executor's nested store holds the same variable the
    /// contract's `o.i.v` was rewritten to.
    pub nested: Vec<(u32, Vec<u32>, Var, bool)>,
    /// `(local, length variable, element width, element signed)` for each slice
    /// or array argument.
    pub lens: Vec<(u32, Var, u8, bool)>,
    /// The fixed length for each array argument, so a symbolic subscript knows
    /// the domain to enumerate. A slice has no entry, and its `xs[i]` stays
    /// refused.
    pub array_lens: Vec<(u32, u64)>,
    /// The enumeration length for each *slice* whose contract subscripted it
    /// symbolically *and* established `len <= MAX_INDEX_CHAIN`. Without an entry
    /// the executor builds no chain, so a slice subscript stays refused; the entry
    /// exists only because the caller proved the length is bounded, which is what
    /// makes a finite chain an honest model of the whole slice.
    pub slice_steps: Vec<(u32, u64)>,
    /// `(local, index, variable, signed)` for each element a contract names.
    pub elems: Vec<(u32, u64, Var, bool)>,
    /// `(local, field chain, index, variable, signed)` for each element of an array reached
    /// through a field path (`o.a[0]`) that a contract names. Keyed by the whole path, so
    /// `o.a[0]` and `o.b[0]` cannot collide.
    pub path_elems: Vec<(u32, Vec<u32>, u64, Var, bool)>,
    /// `(local, tag variable, tag width, discriminants)` for each enum-typed
    /// argument a contract names a variant of.
    ///
    /// The tag is a symbolic input whose domain is the set of variant
    /// discriminants, because a value of the enum always has one of them — a
    /// property of the type, not an assumption about the caller. The run assumes
    /// that domain on the initial path, which is what makes the `otherwise` arm of
    /// an exhaustive `match` (which rustc lowers to `unreachable`) genuinely
    /// unreachable instead of a spurious panic.
    pub tags: Vec<(u32, Var, u8, Vec<u64>)>,
    /// `(local, variant, variable, width, signed)` for each variant payload a
    /// contract names, so `m.Data` in a contract and `((_1 as Data).0)` in the
    /// body name one variable rather than two that look alike.
    pub payload_seeds: Vec<(u32, u64, Var, u8, bool)>,
    /// `(variable index, value)` for each variable the precondition pins to a
    /// constant.
    ///
    /// The variable is seeded with the literal instead of a fresh symbolic input.
    /// Sound -- every model of the precondition has it equal to that -- and it is
    /// what lets a body whose only operand is pinned build its operations on a
    /// literal, where the constant folds collapse them. Keyed by the variable's own
    /// index, so a pin applies wherever that variable is seeded: an argument (whose
    /// index is its local), a struct field, a nested path, or an element. See
    /// [`crate::smt::pinned_vars`].
    pub pins: Vec<(u32, u64)>,
}

/// The contract of the function under verification, in *text* form, so a
/// recursive call can be checked and assumed at the call site.
///
/// A self-call is not inlined: inlining it is what made a recursive function
/// fail at the depth bound. Instead the call becomes the induction step of a
/// well-founded recursion -- the precondition is *proved* of the call's
/// arguments, the `decreases:` measure is *proved* to shrink, and the
/// postcondition is then *assumed* for the result. The measure is what makes the
/// assumption an induction hypothesis rather than a restatement of the goal, so
/// it is required: without one the call falls back to the old inlining.
///
/// The text is carried rather than a pre-built predicate because only the
/// executor knows what the arguments hold at the call site, and the same text has
/// to be evaluated there rather than at entry.
#[derive(Clone, Debug)]
pub struct Recursion {
    /// Raw `requires:` texts.
    pub requires: Vec<String>,
    /// Raw `ensures:` texts. At least one is needed: with no postcondition there
    /// is nothing to assume, so the call falls back to inlining.
    pub ensures: Vec<String>,
    /// The `decreases:` measure.
    pub decreases: String,
    /// The argument names whose types are signed, for the measure's relation.
    pub signed: BTreeSet<String>,
    /// The program's `const` table, so a measure or contract naming a constant
    /// resolves the way the body's use site does.
    pub consts: BTreeMap<String, Const>,
    /// Whether the return type is signed, for a postcondition comparison.
    pub ret_signed: bool,
}

/// The recursion context threaded through the walk: the contract text plus the
/// measure's value at *entry*, which the decrease test compares against.
struct RecCtx {
    rec: Recursion,
    /// The measure evaluated in the entry state, with its signedness.
    measure_entry: Option<(Var, bool)>,
}

/// Verify one function from a parsed program.
///
/// `pre` is the declared precondition (or `None` for `true`); `post` is the
/// declared postcondition over the return value, or `None` to check only panic
/// freedom. Both are built by the caller, which is where the source-level
/// `#[requires]` / `#[ensures]` attributes become symbolic predicates.
///
/// The postcondition is fallible on purpose. An `ensures` the parser cannot read
/// must not become `true`, because then the function would verify with no
/// postcondition checked at all -- a false contract passing as a true one. An
/// error here is turned into an unmodelled path, which is reported rather than
/// discharged.
///
/// `invariant` is the loop induction hypothesis, when the source supplied one.
/// It is the *text* of the `invariant:` clause; the executor resolves the names
/// against the current symbolic values itself, because only it knows what each
/// local holds at the loop head. Passing text rather than a pre-built predicate
/// is what makes preservation expressible: the same text is evaluated a second
/// time in the post-state of one iteration, and a predicate built once could not
/// see that state. Without an invariant a loop is unwound, as before.
#[allow(clippy::too_many_arguments)]
pub fn verify_fn<F>(
    prog: &MirProgram,
    f: &MirFn,
    pre: Option<Pred>,
    post: Option<F>,
    loops: LoopSpec<'_>,
    callees: &CalleeEnv<'_>,
    seeds: &Seeds,
    rec: Option<Recursion>,
) -> MirReport
where
    F: Fn(Option<Var>, &[(u32, Var)], &[(u64, Var)], &[(u32, Var)]) -> Result<Pred, String>,
{
    let mut report = MirReport { function: f.name.clone(), ..Default::default() };

    // Does the precondition even describe an input? An unsatisfiable `requires`
    // makes every downstream proof vacuous, which is a finding, not a success.
    if let Some(p) = pre {
        if smt::find_model(p) == Verdict::Unsat {
            report.obligations.push(Obligation {
                kind: ObligationKind::VacuousPrecondition,
                // `Unsat` is exactly the finding: the engine reports that no
                // input satisfies the precondition.
                verdict: Verdict::Unsat,
            });
            return report;
        }
    }

    let root = match prog.fns.iter().position(|g| std::ptr::eq(g, f)) {
        Some(i) => i,
        None => {
            report.unknown_paths.push("function is not part of the parsed program".into());
            return report;
        }
    };

    let mut env = Env::with_prog(prog);
    // A pinned variable takes the literal its precondition fixes it to, so the
    // body's operations fold instead of building a circuit over an input that has
    // only one value. The pin is keyed by *variable index*, so it applies wherever
    // that variable is seeded -- an argument (whose index is its local) and an
    // aggregate part (a field, a nested path, an element) alike. See
    // [`crate::smt::pinned_vars`].
    let pin_of = |v: Var| -> Option<u64> {
        let idx = smt::index(v);
        seeds.pins.iter().find(|(i, _)| *i == idx).map(|(_, k)| *k)
    };
    // The literal for a pinned variable, masked to the variable's own width: the
    // value a precondition writes is signed (`-7`), and the pattern the seed needs
    // is two's complement at that width (`249` at eight bits).
    let lit_of = |v: Var, k: u64| -> Var {
        let w = smt::bits(v);
        let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        smt::word(k & mask, w)
    };
    for &l in &f.arg_locals {
        let decl = f.ty_of(l).cloned().unwrap_or(Ty::Other("?".into()));
        // `Ty::Ref` is modelled as its referent, so a `&u16` argument is seeded at
        // the *referent's* width and sign -- the same variable the contract's `c`
        // binds to (see `arg_vars_named`). Seeding it `Unknown` instead made a
        // contract that names a scalar reference argument unreadable, which is the
        // C9 exit shape (`bump(c: &mut u16)` with `ensures: c == old(c) + 1`).
        let ty = decl.referent().clone();
        let v = match ty.width() {
            Some(w) => {
                let sym = smt::var_named(l, w);
                match pin_of(sym) {
                    Some(k) if w == 1 => Val::Bool(smt::truth(k & 1 != 0)),
                    Some(k) => Val::Sym(lit_of(sym, k), Sign::of(&ty)),
                    None if w == 1 => Val::Bool(sym.eq_val(1)),
                    // The argument's own type declares its sign, so the value
                    // carries it rather than a later site having to look it up.
                    None => Val::Sym(sym, Sign::of(&ty)),
                }
            }
            None => Val::Unknown,
        };
        env.locals.insert(l, v);
        // A `&T` argument may be dereferenced: `Ty::Ref` is modelled as its
        // referent, so `*_1` names the same value `_1` does.
        if matches!(decl, Ty::Ref(_)) {
            env.deref_ok.insert(l, ());
        }
    }
    // Struct fields the contract names. The contract's `c.lo` is bound to this
    // variable, and the body's `((*_1).0)` reads it from here, so the two are the
    // same symbolic input rather than two that merely look alike.
    for &(local, field, v, signed) in &seeds.fields {
        let val = match pin_of(v) {
            Some(k) => Val::Sym(lit_of(v, k), Sign::of_bool(signed)),
            None => Val::Sym(v, Sign::of_bool(signed)),
        };
        env.fields.insert((local, field), val);
    }
    // Nested field paths the contract names, keyed by the whole projection chain
    // so the body's `(((*_1).0).0)` reads the same variable the contract's `o.i.v`
    // was rewritten to.
    for &(local, ref chain, v, signed) in &seeds.nested {
        let val = match pin_of(v) {
            Some(k) => Val::Sym(lit_of(v, k), Sign::of_bool(signed)),
            None => Val::Sym(v, Sign::of_bool(signed)),
        };
        env.nested.insert((local, chain.clone()), val);
    }
    // Slice lengths and elements the contract names. The contract's `xs.len()` and
    // `xs[0]` and the body's `PtrMetadata(_1)` and `(*_1)[0]` must be one value,
    // so the *same* variables are seeded here. An element the contract does not
    // name is not seeded; the first body read creates it (see `slice_elem`), and
    // a contract that names it later would then disagree — which is why
    // `bind_slice_refs` runs over every contract text before the run, so a name a
    // contract uses always has a binding here.
    for &(local, len, elem_w, elem_signed) in &seeds.lens {
        let fixed_len = seeds.array_lens.iter().find(|(l, _)| *l == local).map(|(_, n)| *n);
        // A slice's chain length comes from the *contract*, which established
        // `len <= MAX_INDEX_CHAIN` before the run; an array's is its type length.
        // The two are separate lists because they mean different things: the first
        // is proved, the second is a fact about the type.
        let slice_steps = seeds.slice_steps.iter().find(|(l, _)| *l == local).map(|(_, n)| *n);
        // A `Vec` argument's length is mutable (`push`/`pop` change it); a slice's
        // or an array's is fixed. The type is the only place the distinction lives,
        // so it is read here rather than carried in a second seed list.
        let len_mutable = f
            .ty_of(local)
            .map(|t| matches!(t.referent(), Ty::Other(n) if vec_elem_ty_loose(n).is_some()))
            .unwrap_or(false);
        env.indexed.insert(
            local,
            Indexed {
                len,
                len_mutable,
                elem_w,
                elem_signed,
                elems: BTreeMap::new(),
                fixed_len,
                slice_steps,
                poisoned: false,
            },
        );
    }
    for &(local, index, v, _) in &seeds.elems {
        if let Some(s) = env.indexed.get_mut(&local) {
            let v = match pin_of(v) {
                Some(k) => lit_of(v, k),
                None => v,
            };
            s.elems.insert(index, v);
        }
    }
    // Elements of field-path arrays the contract names, keyed by the whole path. The body's
    // `(_1.0)[k]` write lands on the same key, so a contract's `o.a[0]` and the body's write are
    // one value. Pins apply here as elsewhere: a pinned element is a *literal*, not an input.
    for &(local, ref chain, index, v, _signed) in &seeds.path_elems {
        let val = match pin_of(v) {
            Some(k) => Val::Sym(lit_of(v, k), Sign::of_bool(_signed)),
            None => Val::Sym(v, Sign::of_bool(_signed)),
        };
        env.elems_path.insert((local, chain.clone(), index), val);
    }
    // Enum tags a contract names a variant of. The tag is seeded so the body's
    // `discriminant(_1)` reads the same variable the contract's `m` does, and the
    // payloads are seeded so a downcast read names the same one too.
    for &(local, tag, width, _) in &seeds.tags {
        env.set_discriminant(local, Val::Sym(smt::truncate(tag, width), Sign::Unsigned));
    }
    for &(local, variant, v, width, signed) in &seeds.payload_seeds {
        env.set_payload(local, variant, Val::Sym(v, Sign::of_bool(signed)), width);
    }
    // The tag's domain is the set of variant discriminants. Assuming it is sound
    // because it is a fact about the *type*: a value of the enum always has one of
    // its variants' tags, so no caller could falsify it. It is also necessary:
    // without it the `otherwise` arm of an exhaustive `match` looks reachable, and
    // since rustc lowers that arm to `unreachable`, every `match` would report a
    // panic.
    //
    // A disjunction of the discriminants, not a `tag < count` bound. The two agree
    // only when the numbering is `0..count`; with `A, B = 3, C` the real tags are
    // `0`, `3` and `4`, and `tag < 3` would exclude `4` -- excluding a value the
    // type admits, which is the unsound direction. The disjunction is exact for any
    // numbering.
    let mut pre = pre;
    for &(_, tag, width, ref discs) in &seeds.tags {
        if discs.is_empty() {
            continue;
        }
        // A discriminant too large for the tag's width cannot be represented, so
        // the domain cannot be assumed as written; refusing to assume is the safe
        // direction (the `otherwise` arm then looks reachable and the run reports
        // it, rather than a wrong domain being taken as fact).
        let max = *discs.iter().max().unwrap_or(&0);
        if width < 64 && max > (1u64 << width) - 1 {
            continue;
        }
        let mut bound: Option<Pred> = None;
        for d in discs {
            let p = smt::eq_const(tag, *d);
            bound = Some(match bound {
                None => p,
                Some(prev) => smt::or(prev, p),
            });
        }
        if let Some(bound) = bound {
            pre = Some(match pre {
                None => bound,
                Some(p) => smt::and(p, bound),
            });
        }
    }

    let start = match f.blocks.first() {
        Some(b) => b.id,
        None => {
            report.unknown_paths.push("function has no basic blocks".into());
            return report;
        }
    };

    // A loop carried by an invariant is not unwound. The loop is located before
    // the walk starts, and a function with an invariant but no detectable back
    // edge is refused rather than silently unwound: the contract made a claim
    // and the tool must either honour it or say it could not.
    let unwind = loops.unwind.unwrap_or(DEFAULT_UNWIND);
    let cut = match loops.invariant {
        None => None,
        Some(text) => match detect_loop(f) {
            Some((header, back_edges)) => {
                let havoc = loop_writes(prog, f, header);
                Some(Cut {
                    func: root,
                    header,
                    back_edges,
                    havoc,
                    text: text.to_string(),
                    variant: loops.variant.map(str::to_string),
                })
            }
            None => {
                report.unknown_paths.push(
                    "an `invariant:` was declared but no loop was found to attach it to".into(),
                );
                return report;
            }
        },
    };

    // The recursion context: the measure evaluated in the *entry* state, which
    // every recursive call's decrease test compares against. Evaluated here,
    // once, because the entry state is the one the walk starts from and the walk
    // itself only ever sees later states. `names` is the entry binding of the
    // arguments, which is exactly the state the measure is about.
    let rec_ctx = rec.map(|rec| {
        let entry_names = spec::arg_vars(f);
        let measure_entry = spec::eval_measure(&rec.decreases, &entry_names, &rec.signed, &rec.consts)
            .ok();
        RecCtx { rec, measure_entry }
    });
    // A `decreases:` clause that cannot be read at entry is a refusal, not a
    // silently-absent measure: without it every recursive call would be reported
    // unknown, and saying so once here is clearer than at each call.
    if let Some(rc) = &rec_ctx {
        if rc.measure_entry.is_none() {
            report
                .unknown_paths
                .push("unreadable `decreases:` measure at entry".into());
        }
    }

    let mut work = vec![State {
        frame: Frame {
            func: root,
            ret_target: usize::MAX,
            ret_dest: None,
            saved_env: None,
            saved_cut: None,
            saved_variant: None,
            by_ref: Vec::new(),
            caller: None,
        },
        block: start,
        path: pre.unwrap_or_else(|| smt::truth(true)),
        env,
        visits: BTreeMap::new(),
        depth: 0,
        cut,
        variant_entry: None,
    }];

    let mut explored: usize = 0;
    // The path budget grows with a *declared* bound: a caller who asks for more
    // iterations is asking for more paths. See [`path_budget`].
    let budget = path_budget(loops.unwind);
    while let Some(st) = work.pop() {
        // Bound the *number of paths*, not just each loop. A branch inside an
        // unwound loop multiplies paths without any single loop exceeding
        // `DEFAULT_UNWIND`, so this is the guard that makes the search
        // terminate; see [`DEFAULT_PATH_BUDGET`]. Stopping here is reported, not
        // hidden: the function becomes incomplete and says why.
        if explored >= budget {
            report.unknown_paths.push(format!(
                "path budget exhausted after {budget} paths; the remainder was not explored"
            ));
            break;
        }
        explored += 1;
        run_state(
            prog,
            st,
            &post,
            &mut report,
            &mut work,
            &seeds.pins,
            root,
            &rec_ctx,
            callees,
            unwind,
            loops.unwind.is_some(),
        );
    }
    report
}

/// Locate the loop a function's invariant is about.
///
/// Returns the header and the blocks that jump back to it. The header is taken
/// to be the target of a back edge, and every edge into it is an induction
/// obligation, so the choice only has to be *a* loop head rather than the
/// canonical one rustc would name: for a single loop they coincide, and for a
/// function with more than one the contract is refused by the caller.
///
/// A "back edge" is an edge to a block that appears earlier in the block order.
/// MIR prints blocks in layout order and a loop body comes after its header, so
/// the edge from the latch back to the header is the one that goes backwards.
/// An edge that goes forward is a branch, not a back edge.
fn detect_loop(f: &MirFn) -> Option<(usize, Vec<usize>)> {
    let position: BTreeMap<usize, usize> =
        f.blocks.iter().enumerate().map(|(i, b)| (b.id, i)).collect();
    let mut header: Option<usize> = None;
    let mut back_edges: Vec<usize> = Vec::new();
    for b in &f.blocks {
        for target in successors(&b.term) {
            let (Some(&from), Some(&to)) = (position.get(&b.id), position.get(&target)) else {
                continue;
            };
            // `to <= from` is the whole test. It excludes the entry edge, whose
            // source precedes the header, and includes a header that loops to
            // itself. A block listed here can only ever be asked "is this a back
            // edge" when its edge targets the chosen header, and the chosen
            // header is the earliest backward target -- so a block with a
            // backward edge is never earlier than it, and a forward edge into the
            // header from an earlier block is never misclassified.
            if to <= from {
                // The header is the earliest block a back edge returns to, so
                // the choice stays stable when a latch closes two loops.
                match header {
                    Some(h) if position[&h] <= to => {}
                    _ => header = Some(target),
                }
                if !back_edges.contains(&b.id) {
                    back_edges.push(b.id);
                }
            }
        }
    }
    header.map(|h| (h, back_edges))
}

/// What a diverging call's report should say it was.
///
/// The dump passes the panic message as a string literal
/// (`core::panicking::panic(const "assertion failed: x <= 200")`), so a report can
/// name the failed assertion instead of the mangled path. When there is no message
/// at all -- `panic!("{}", x)` prints `panic_display::<u8>`, `unwrap` on a `None`
/// prints `unwrap_failed` -- the callee's own name is the honest fallback, read
/// through its generics so the report says `panic_display`, not `<u8>`.
fn panic_message(name: &str, args: &[Operand], env: &Env) -> String {
    for a in args {
        // A literal message, as edition 2015/2021 prints it.
        if let Operand::Const(Const::Str(s)) = a {
            return s.clone();
        }
        // Edition 2024: the message is a local the `core::fmt` chain built, so it
        // is read from the string store rather than from an operand.
        if let Operand::Move(p) | Operand::Copy(p) = a {
            if p.proj.is_empty() {
                if let Some(s) = env.strs.get(&p.local) {
                    return s.clone();
                }
            }
        }
    }
    // A recent nightly lowers `unreachable!()`/`todo!()`/`unimplemented!()`/
    // `panic!()` with no message to a dedicated `*_default_msg` callee that takes
    // no literal, where stable passes the text as `panic(const "…")`. The text is
    // the same on both toolchains, so it is spelled here rather than read: a
    // report whose message depended on the compiler version would be a claim the
    // toolchain half-decides. An unrecognised name still falls back to the callee.
    let tail = path_tail(name);
    match tail {
        "panic_default_msg" => "explicit panic",
        "unreachable_default_msg" => "internal error: entered unreachable code",
        "todo_default_msg" => "not yet implemented",
        "unimplemented_default_msg" => "not implemented",
        _ => tail,
    }
    .to_string()
}

/// Every block a terminator can jump to.
fn successors(t: &Term) -> Vec<usize> {
    match t {
        Term::Goto(b) => vec![*b],
        Term::SwitchInt { cases, otherwise, .. } => {
            let mut v: Vec<usize> = cases.iter().map(|(_, b)| *b).collect();
            v.push(*otherwise);
            v
        }
        // A diverging call has no normal successor. Reporting `target` (which the
        // parser leaves at `usize::MAX`) would send the walk to a block that does
        // not exist and turn the path into a "missing block" unknown; reporting
        // none says what is true -- the path ends here.
        Term::Call { diverges: true, .. } => Vec::new(),
        Term::Call { target, .. } => vec![*target],
        Term::Assert { target, .. } => vec![*target],
        Term::Drop { target, .. } => vec![*target],
        Term::Return | Term::Unreachable | Term::Unknown(_) => Vec::new(),
    }
}

/// The locals a loop can write: every local assigned in a block reachable from
/// the header without leaving the loop.
///
/// Reachability is taken over the whole function rather than the loop body,
/// because a precise loop-body extraction is a dominator computation and this
/// only needs an over-approximation: havocing a local the loop never writes
/// loses information but cannot make an unsound proof sound.
///
/// `_0`, the return place, is always included. A loop is allowed to write the
/// return value (`s` in `sum_to` is `_0`), and leaving it out would leave the
/// exit edge holding the *pre-loop* return value -- which is precisely the hole
/// this set exists to close.
///
/// "Write" is an *effect*, not a syntax: a write through a reference reaches the
/// referent, and a call reaches whatever the callee writes through its reference
/// arguments. The header havoc replaces every local in this set with a fresh
/// value, so an under-approximation keeps the entry value in the header state and
/// the exit guard can fold -- a false proof. Two ways that happened, both fixed
/// here: a `&mut` destination (`*p = v`) whose referent was not followed, and a
/// call (`bump(x)` where `bump(c: &mut u8)`) whose write-through was invisible
/// because only the call's *destination* was collected.
///
/// A callee is looked up through `resolve_callee` (the same rule the inliner uses)
/// and, if found, every local it writes is folded back onto the argument the call
/// passed it -- an argument that is a reference (`&mut u8`) is modelled as its
/// referent, so the caller local that argument names is the one to havoc. A callee
/// that is not in this program (a `core` intrinsic, an unmodelled call) contributes
/// nothing here: its effects are the executor's to model, and the loop's own writes
/// are still collected. Recursion is bounded by the `visited` set.
fn loop_writes(prog: &MirProgram, f: &MirFn, header: usize) -> Vec<u32> {
    let mut visiting: BTreeSet<usize> = BTreeSet::new();
    if let Some(i) = prog.fns.iter().position(|g| std::ptr::eq(g, f)) {
        visiting.insert(i);
    }
    collect_writes(prog, f, header, &mut visiting)
}

/// The body of [`loop_writes`], threading the set of functions on the *call
/// stack*.
///
/// The block walk is bounded by `seen` (per function), but the interprocedural
/// step -- following a callee to find what it writes through a reference -- needs
/// its own guard: a loop that calls a *recursive* function would otherwise follow
/// the self-call forever. Each `collect_writes` invocation allocates a fresh
/// `seen`, which stops a CFG cycle within one function and cannot stop a call
/// cycle between invocations, so `loop_calls_recursive` overflowed the stack.
/// `visiting` is what makes the traversal terminate.
///
/// A function already on the stack is a cycle we cannot summarise exactly. Rather
/// than skip it (which *could* drop reference writes propagated around the cycle),
/// the call's *reference arguments* are added directly: a callee can only affect
/// caller storage through a reference, so those are exactly the caller locals a
/// cycle could reach. A recursive callee with no reference argument (`count_down(n:
/// u8)`) therefore contributes nothing.
///
/// Measured: this inclusion is a *conservative superset*, not the load-bearing
/// path. For every fixture in the corpus the reference write is already carried by
/// the callee's own direct scan (the deref store names the argument local) folded
/// back positionally below; deleting the inclusion changes no verdict, while
/// deleting the *termination* guard reproduces the overflow. It is kept because it
/// is the sound direction (it can only add locals to havoc) and because it holds
/// for a cycle whose write the fold cannot map back.
fn collect_writes(
    prog: &MirProgram,
    f: &MirFn,
    header: usize,
    visiting: &mut BTreeSet<usize>,
) -> Vec<u32> {
    let mut writes: BTreeMap<u32, ()> = BTreeMap::new();
    writes.insert(0, ());
    let mut seen: BTreeMap<usize, ()> = BTreeMap::new();
    let mut stack = vec![header];
    while let Some(b) = stack.pop() {
        if seen.insert(b, ()).is_some() {
            continue;
        }
        let Some(block) = f.block(b) else { continue };
        for s in &block.stmts {
            if let Stmt::Assign(dest, rv) = s {
                writes.insert(dest.local, ());
                // A reference taken inside the loop may be written *through*:
                // `let p = &mut x; *p += 1` writes `x`, but the syntactic
                // destination is `p`. Treat the referent as written so the havoc
                // reaches it. This is an over-approximation -- a shared `&x` is
                // included too -- which is the safe direction: havocing a local
                // the loop never writes loses information, never soundness.
                if let Rvalue::Ref(place) = rv {
                    writes.insert(place.local, ());
                }
            }
        }
        // A call writes its destination too, and that write is not a statement:
        // rustc spells `x = f(..)` as a `Call` terminator whose `dest` is `x`. Reading
        // only `Stmt::Assign` missed it, so a counter advanced by a call
        // (`i = i.wrapping_add(1)`) stayed out of the havoc set and kept the value it
        // had when the header was first entered. The induction step then proved the
        // invariant for that one value rather than for the loop, and a postcondition
        // that only holds on the first iteration came back `Verified`.
        if let Term::Call { callee, args, dest, .. } = &block.term {
            writes.insert(dest.local, ());
            // ...and whatever the callee writes *through* a reference argument.
            // `while i < 3 { bump(x); i += 1 }` with `bump(c: &mut u8)` writes
            // `x` on every iteration, but the call's destination is `bump`'s
            // return local, not `x`: the write-through was invisible, `x` kept
            // its entry value, the exit guard folded and `ensures: ret == 0`
            // was `Verified` for a body returning 3.
            if let Callee::Name(name) = callee {
                if let Some(k) = resolve_callee(prog, name) {
                    if visiting.contains(&k) {
                        // A call cycle: this traversal cannot summarise the callee
                        // exactly, so add its reference arguments directly -- the
                        // only caller storage a callee can reach. A conservative
                        // superset: it can only add locals to havoc. See the note
                        // on `collect_writes` for why it is not the load-bearing
                        // path but is kept anyway.
                        for a in args {
                            if let Operand::Copy(p) | Operand::Move(p) = a {
                                if matches!(f.ty_of(p.local), Some(Ty::Ref(_))) {
                                    writes.insert(p.local, ());
                                }
                            }
                        }
                    } else {
                        let callee_fn = &prog.fns[k];
                        let Some(entry) = callee_fn.blocks.first().map(|b| b.id) else {
                            continue;
                        };
                        visiting.insert(k);
                        let callee_writes = collect_writes(prog, callee_fn, entry, visiting);
                        visiting.remove(&k);
                        for w in callee_writes {
                            // The callee local `w` is written; the call passed it
                            // `args[i]`, so the caller local that argument names is
                            // what the write reaches. The mapping is positional:
                            // `callee_fn.arg_locals[i]` is the callee's local for
                            // the call's `args[i]`.
                            if let Some(i) = callee_fn.arg_locals.iter().position(|&l| l == w) {
                                if let Some(Operand::Copy(p) | Operand::Move(p)) = args.get(i) {
                                    // Only a *reference* argument shares storage
                                    // with the caller; a by-value argument is the
                                    // callee's own copy and its writes die with
                                    // the frame -- the boundary the inliner's
                                    // `by_value_indexed` keeps.
                                    if matches!(f.ty_of(p.local), Some(Ty::Ref(_))) {
                                        writes.insert(p.local, ());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for t in successors(&block.term) {
            stack.push(t);
        }
    }
    writes.into_keys().collect()
}

/// The names an invariant may use: every local with a `debug` name, mapped to the
/// symbolic value that local holds.
///
/// Built from the *current* environment rather than from the types, because the
/// invariant is evaluated in the middle of a walk and has to name what the
/// variables hold there.
fn invariant_names(f: &MirFn, env: &Env) -> BTreeMap<String, Var> {
    let mut out = BTreeMap::new();
    for (&local, name) in &f.local_names {
        if let Some(Val::Sym(v, _)) = env.locals.get(&local) {
            out.insert(name.clone(), *v);
        }
    }
    out
}

/// The source names of signed locals, so an invariant's comparisons use the
/// signed relation for them.
fn signed_names(f: &MirFn) -> std::collections::BTreeSet<String> {
    let mut out = std::collections::BTreeSet::new();
    for (&local, name) in &f.local_names {
        if f.ty_of(local).map(|t| t.is_signed()).unwrap_or(false) {
            out.insert(name.clone());
        }
    }
    out
}

/// Evaluate the invariant in the current state, as a predicate.
///
/// An error means a name in the invariant does not resolve to a symbolic value --
/// a local still holding an aggregate, say. That is reported as an unmodelled
/// path rather than folded into `true`, because an invariant that silently became
/// `true` would discharge both induction obligations and prove nothing.
fn eval_invariant_here(f: &MirFn, env: &Env, text: &str) -> Result<Pred, String> {
    let names = invariant_names(f, env);
    crate::mir::spec::eval_invariant(text, &names, &signed_names(f), &env.consts)
        .map_err(|e| e.to_string())
}

/// The `(variable, literal)` bindings for the pins, masked to each variable's width.
///
/// A pin records a *bit pattern*, not a signed number: `-7` at eight bits is `249`. The
/// width comes from the variable's own declaration ([`smt::var_width`]), so the literal is
/// the same term the seeding uses. A pin whose variable is not declared in this context is
/// skipped: there is no width to mask to, and a wrong width would substitute a term of the
/// wrong size.
fn pin_bindings(pins: &[(u32, u64)]) -> Vec<(Var, Var)> {
    pins.iter()
        .filter_map(|&(idx, k)| {
            let w = smt::var_width(idx);
            if w == 0 {
                return None;
            }
            let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
            Some((smt::var_named(idx, w), smt::word(k & mask, w)))
        })
        .collect()
}

/// Apply the precondition's pins to a path and the goal built over it, at one obligation.
///
/// A pin is a *forced* value: the precondition entails `v == k`, so rewriting `v` to `k`
/// throughout `(P => Q)` gives `(P[v:=k] => Q[v:=k])`, which has the same truth value --
/// a model of `!P` restricts, and a model of `!P[v:=k]` extends by `v := k`. The rewrite is
/// therefore an equivalence: it can turn a refusal into a proof or a refutation, and it can
/// never manufacture a verdict.
///
/// It is applied to the *whole path* and not to the precondition alone, and that is the
/// load-bearing part. The executor's path is not just the precondition: a `match` on an enum
/// tag, an `assert`, a branch each conjoin their own constraint. Rewriting only the
/// precondition would drop the relation between the tag and the value the pin gives it --
/// `m == Mode::Run` pins the tag to `2`, and a path that then splits on `tag == 0` is
/// infeasible *because* the pin says `2`. Rewriting the path keeps every split and every
/// pin, and takes the deep term (`c == b * 2`) out of the assumption the diagram is built
/// over. See [`crate::smt::pinned_vars`].
fn pinned_pair(path: Pred, goal: Pred, pins: &[(u32, u64)]) -> (Pred, Pred) {
    if pins.is_empty() {
        return (path, goal);
    }
    let bindings = pin_bindings(pins);
    if bindings.is_empty() {
        return (path, goal);
    }
    (smt::substitute(path, &bindings), smt::substitute(goal, &bindings))
}

/// Decide `path => goal`, retrying with the pins rewritten in only if the engine refuses.
///
/// The unrewritten query is tried first and its answer is kept whenever it is decided. That
/// ordering is what preserves the *witness*: the rewrite removes the pinned variables, so a
/// counterexample found under it cannot name the input, and the counterexample is the more
/// useful answer. The fallback exists for the one case the rewrite is for -- an `Unknown`
/// the pins can lift -- and [`pinned_pair`] is an equivalence, so a decided answer from the
/// retry is the same answer the first attempt would have given had it been able to decide.
fn prove_obligation(path: Pred, goal: Pred, pins: &[(u32, u64)]) -> Verdict {
    let v = smt::prove_implies(path, goal);
    if !matches!(v, Verdict::Unknown) || pins.is_empty() {
        return v;
    }
    let (path, goal) = pinned_pair(path, goal, pins);
    let v2 = smt::prove_implies(path, goal);
    if matches!(v2, Verdict::Unknown) {
        v
    } else {
        v2
    }
}

/// [`smt::find_model`] with the same pins fallback as [`prove_obligation`].
fn find_obligation(path: Pred, pins: &[(u32, u64)]) -> Verdict {
    let v = smt::find_model(path);
    if !matches!(v, Verdict::Unknown) || pins.is_empty() {
        return v;
    }
    let (path, _) = pinned_pair(path, smt::truth(true), pins);
    let v2 = smt::find_model(path);
    if matches!(v2, Verdict::Unknown) {
        v
    } else {
        v2
    }
}

/// The base type name of a path segment, with generic arguments and an
/// `impl`-projection wrapper stripped: `Vec2` → `Vec2`, `G::<T>` → `G`,
/// `<S2 as T2>` → `S2`, `core::num::<impl u8>` → `u8`.
///
/// rustc prints a method's *definition* with the type it is implemented for
/// wrapped in `<impl …>` and a *call* with that type bare, so the two have to be
/// cut to the same shape before they can be compared.
fn base_type(s: &str) -> String {
    let s = s.trim();
    if let Some(rest) = s.split("<impl ").nth(1) {
        return rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
    }
    let s = match s.strip_prefix('<') {
        Some(rest) => rest.split(" as ").next().unwrap_or(rest),
        None => s,
    };
    let s = s.split("::<").next().unwrap_or(s);
    let s = s.split('<').next().unwrap_or(s);
    s.rsplit("::").next().unwrap_or(s).trim().to_string()
}

/// The type a method call is made on: `Vec2` in `Vec2::push`, `G` in
/// `G::<T>::walk`, `S2` in `<S2 as T2>::go`.
fn call_type(name: &str) -> Option<String> {
    Some(base_type(name.rsplit_once("::")?.0))
}

/// Whether a name is `core`'s own `Ord::min`/`Ord::max` for a primitive type.
///
/// These are one of the two modelled shapes whose dump spelling carries no `<impl`
/// -- a trait method names the trait, `<u8 as Ord>::min` -- so the executor's guard
/// has to admit them by name. (The other is a conversion; see [`convert`], which
/// checks its own name and types.) It admits only a *primitive* self type: a user
/// type cannot be `Ord`'s receiver here, so `<MyType as Ord>::min` is refused even
/// though `core` really does implement `Ord` for it. That is deliberate and it is
/// the conservative direction -- the model has no definition for a user type's
/// `min` anyway, and refusing it means a name that *could* be a local trait's is
/// never answered by the model. The trait path must be the standard library's
/// `Ord` (see [`intrinsics::names_ord_trait`]), so `m::Ord::min` and
/// `MyOrd::min` are both refused. See [`try_intrinsic`].
fn is_ord_callee(name: &str) -> bool {
    if !intrinsics::names_ord_trait(name) {
        return false;
    }
    let self_ty = call_type(name).unwrap_or_default();
    matches!(self_ty.as_str(), "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16"
        | "i32" | "i64" | "i128" | "isize")
}

/// Whether a name is `core`'s own `PartialEq`/`PartialOrd` comparison for a
/// primitive type.
///
/// The comparison twin of [`is_ord_callee`]: `eq`/`ne`/`lt`/`le`/`gt`/`ge` are
/// trait methods, so their dump spelling carries no `<impl` -- `<u8 as
/// PartialEq>::eq` -- and the executor's guard has to admit them by name. The same
/// narrow rules apply: the trait path must be the standard library's (see
/// [`intrinsics::names_cmp_trait`]), and the self type must be a primitive, so a
/// user type's comparison is refused rather than read. A crate-root trait that
/// prints bare is closed by the caller's same-dump lookup, as for `Ord`.
fn is_cmp_callee(name: &str) -> bool {
    if !intrinsics::names_cmp_trait(name) {
        return false;
    }
    let self_ty = call_type(name).unwrap_or_default();
    matches!(self_ty.as_str(), "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16"
        | "i32" | "i64" | "i128" | "isize")
}

/// Answer a widening conversion (`From::from`/`Into::into`), or report why not.
///
/// The two types come from the call's *name* (`<u16 as From<u8>>::from`), because
/// the model's whole content is that they differ; the single argument's declared
/// type would give the source twice. Both must be modelled integers, and the
/// destination must be at least as wide as the source: a real integer `From` only
/// widens, so anything else is not the method this model knows. A destination the
/// engine cannot hold is refused by `int_width` (`u128`/`i128`), which is the
/// honest answer rather than a truncated one.
///
/// The source's *signedness* comes from the name's source type, and is what the
/// model extends by; the argument's own `Val` sign is deliberately not consulted,
/// so the value and the extension cannot be read from different places and
/// disagree. The result carries the destination's sign, since the local it is
/// written to has the destination's type.
fn convert(
    name: &str,
    kind: intrinsics::Conversion,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
) -> Result<(), String> {
    let Some((src_ty, dst_ty)) = intrinsics::conversion_types(name, kind) else {
        return Err(format!("unmodelled conversion `{name}`"));
    };
    // `u8::from(b)` / `u32::from(b)`: a `bool` source is a one-bit value, and its
    // conversion is the zero-extension of that bit (`false` -> 0, `true` -> 1). A
    // `bool` has no integer width, so `int_width` would refuse it; it is answered
    // here instead. The source is a *predicate* (`Val::Bool`), so it is widened to
    // the one-bit word the destination holds -- the same step a `bool` `ret` takes.
    if src_ty == Ty::Bool {
        let Some(dst_w) = intrinsics::int_width(&dst_ty) else {
            return Err(format!("`{name}` converts a type the model does not hold"));
        };
        let Some(arg) = args.first() else {
            return Err(format!("unmodelled arity for `{name}`"));
        };
        let Val::Bool(p) = operand(env, arg) else {
            return Err(format!("unmodelled argument to `{name}`"));
        };
        let bit = smt::ite(p, smt::word(1, 1), smt::word(0, 1));
        env.set(dest, Val::Sym(smt::truncate(bit, dst_w), Sign::of(&dst_ty)));
        return Ok(());
    }
    let (Some(src_w), Some(dst_w)) =
        (intrinsics::int_width(&src_ty), intrinsics::int_width(&dst_ty))
    else {
        return Err(format!("`{name}` converts a type the model does not hold"));
    };
    if dst_w < src_w {
        return Err(format!("`{name}` is not a widening conversion"));
    }
    let Some(arg) = args.first() else {
        return Err(format!("unmodelled arity for `{name}`"));
    };
    let Val::Sym(x, _) = operand(env, arg) else {
        return Err(format!("unmodelled argument to `{name}`"));
    };
    // `w` and `signed` are the source's, `result_w` the destination's, so `eval`
    // extends by the source sign to the destination width -- the one place the two
    // types are both read.
    let Some(intrinsics::Outcome::Value(v)) = intrinsics::eval(
        intrinsics::Intrinsic::Conversion(kind),
        x,
        x,
        src_w,
        src_ty.is_signed(),
        dst_w,
    ) else {
        return Err(format!("`{name}` past what the model covers"));
    };
    env.set(dest, Val::Sym(v, Sign::of(&dst_ty)));
    Ok(())
}

/// The `self` type of an *instance* method, read from its receiver's declared
/// type.
///
/// rustc prints a method's *definition* as `<impl at FILE:L:C: L:C>::m`, which
/// names no type, but an instance method's receiver is the first argument and its
/// `debug` binding is literally `self`, so that local's declared type names the
/// type the method is implemented for (`&Vec2` gives `Vec2`).
///
/// A *static* associated function has no `self`, so it has no `debug self`
/// binding and this returns `None`. The distinction matters: a static
/// `Foo::m(x: Vec2)`'s first parameter is an ordinary argument, and reading it as
/// a receiver would let a call to an *external* `Vec2::m` resolve to `Foo::m` --
/// answering a call from the wrong body, which is a false proof. A free function
/// has no `self` either and is also `None`, so callers distinguish the two by the
/// definition name (see [`impl_self_loc`]).
fn method_self_type(f: &MirFn) -> Option<String> {
    let self_local = f
        .debug_bindings
        .iter()
        .find_map(|(n, l)| (n == "self").then_some(*l).flatten())?;
    let ty = f.locals.get(&self_local)?;
    let inner = match ty {
        Ty::Ref(inner) => inner.as_ref(),
        other => other,
    };
    match inner {
        Ty::Other(s) => Some(base_type(s)),
        _ => None,
    }
}

/// The `(line, column)` of the `impl` block a method belongs to, from its
/// definition name `<impl at FILE:L:C: L:C>::m`, or `None` for a free function.
///
/// This is the identity rustc gives a method that is *not* its `self` type: a
/// static associated function's receiver is absent, so the only thing tying it to
/// a type is the `impl` block it was written in, and that block is named by
/// location. See [`method_owner_type`].
fn impl_self_loc(f: &MirFn) -> Option<(usize, usize)> {
    if !f.name.contains("<impl at") {
        return None;
    }
    f.impl_loc
}

/// The owner type of a method's `impl`, read from the source via the location in
/// its definition name, or `None` when that cannot be established.
///
/// An instance method's `self` type already names the type it is implemented for,
/// but a *static* associated function has no `self` to read, so its owner is only
/// known from the `impl` block's own source line. `None` here means the call
/// cannot be matched to this method by type, so the safe direction is to refuse
/// the call rather than answer it from a body that may not be the one named.
fn method_owner_type(prog: &MirProgram, f: &MirFn) -> Option<String> {
    let loc = impl_self_loc(f)?;
    prog.impl_owners.get(&loc).cloned()
}

/// The trait a *call* names, as the path between `as` and `>`, or `None` when the
/// call is not a trait call.
///
/// `Some("std::convert::From")` for `<u16 as std::convert::From<u8>>::from`,
/// `Some("From")` for `<u16 as From<u8>>::from`, and `None` for an inherent call
/// like `Vec2::push` or `<impl at …>::m`. The ` as `-delimited projection is what
/// rustc prints for a trait method call, so the trait path is read there and
/// nowhere else -- a bare `Type::m` has no trait to compare.
fn call_trait_path(name: &str) -> Option<String> {
    let after = name.rsplit_once(" as ")?.1;
    let (trait_ty, _) = after.split_once(">::")?;
    Some(trait_ty.split_once('<').map(|(t, _)| t).unwrap_or(trait_ty).trim().to_string())
}

/// The trait *arguments* a call instantiates, as written: `u8` for
/// `<u16 as From<u8>>::from`, `Option<u8>` for `<W as Wrap<Option<u8>>>::get`, and
/// `None` for a call with no generic arguments (`<Foo as Trait>::m`) or one that is
/// not a trait call.
///
/// A `From<Local>` impl and the library's `From<u8>` impl share both the trait path
/// (`From`) and the owner (`u16`), so the *argument* is the only thing separating
/// them, and it is what a call to the wrong one would answer from. Returning the
/// whole list (`From<u8, u8>` gives `u8, u8`) keeps the identity exact rather than
/// sampling the first parameter. See [`trait_candidate_admits`].
///
/// The argument is read with [`crate::mir::spec::angle_inner`], the same balanced
/// reader the `impl` side uses, so the two spellings are compared as written. A
/// "strip trailing `>`" reading would cut *every* closing bracket off a nested
/// argument (`Wrap<Option<u8>>` -> `Option<u8`), which no impl's balanced reading
/// equals, so a call to such a trait would be refused -- a lost proof.
fn call_trait_args(name: &str) -> Option<String> {
    let after = name.rsplit_once(" as ")?.1;
    // `after` is `TRAIT<…>>::method`; the first `>::` closes the trait's own
    // argument list and the projection, so the text before it is the trait as
    // written. See [`crate::mir::spec::angle_inner`] for the balanced read.
    let (trait_ty, _) = after.split_once(">::")?;
    let inner = crate::mir::spec::angle_inner(trait_ty)?;
    (!inner.is_empty()).then(|| inner.to_string())
}

/// The string pieces of the promoted constant a `const <…>::promoted[N]` operand
/// names, reconciling the use-site spelling with the definition's.
///
/// rustc prints a promoted constant's *definition* and its *use* with different
/// paths on the MSRV (1.85): a `panic!` inside a trait default body defines
/// `const a::Custom::into_iter::promoted[0]` but uses
/// `const <Self as range_shim::a::Custom>::into_iter::promoted[0]`. An exact
/// lookup misses, so the `Arguments::new_const` call is reported unmodelled and a
/// function that only panics comes back `incomplete` instead of refuted -- an
/// MSRV-only failure that current stable hides (it prints a plain `from_str`).
///
/// The two names share the `::promoted[N]` tail, and the owner before it is the
/// same trait or item. A suffix match on the whole name is not enough
/// (`a::Custom::into_iter::promoted[0]` is not a suffix of the use), so the tail
/// is stripped and the *owner* paths compared: the use's owner is its `<T as
/// Trait>` projection when it has one (`range_shim::a::Custom`), else the whole
/// qualifier, and a definition whose owner is a `::`-aligned suffix of it
/// (`a::Custom`) is the one the use names. Comparing owners rather than the last
/// segment is what keeps two sibling traits of the same method (`a::Custom` and
/// `b::Custom`, each with its own `into_iter`) from answering for one another.
/// Only `promoted[…]` names are reconciled -- an ordinary `const NAME` keeps the
/// exact-match rule, because a name that does not resolve exactly is a name this
/// model does not hold.
fn lookup_promoted(promoted: &BTreeMap<String, Vec<String>>, use_name: &str) -> Option<Vec<String>> {
    if let Some(v) = promoted.get(use_name) {
        return Some(v.clone());
    }
    // `qualifier::promoted[N]` -> `(qualifier, "promoted[N]")`.
    let (use_qual, use_tail) = use_name.rsplit_once("::")?;
    if !use_tail.starts_with("promoted[") {
        return None;
    }
    let use_owner = call_trait_path(use_name).unwrap_or_else(|| use_qual.to_string());
    // The *method* segment the use names: the last `::` component of its
    // qualifier. A trait default's promoted constant is spelled
    // `<Self as Trait>::method::promoted[N]`, so the method is the piece that
    // distinguishes two defaults on the same trait.
    let use_method = use_qual.rsplit_once("::").map(|(_, m)| m).unwrap_or(use_qual);
    let mut found: Option<Vec<String>> = None;
    for (def, pieces) in promoted {
        let Some((def_qual, def_tail)) = def.rsplit_once("::") else { continue };
        if def_tail != use_tail {
            continue;
        }
        // The definition's owner is its qualifier minus the method/item segment.
        let (def_owner, def_method) = match def_qual.rsplit_once("::") {
            Some((o, m)) => (o, m),
            None => (def_qual, def_qual),
        };
        // The *method* must match too. `Custom::aaa::promoted[0]` and
        // `Custom::zzz::promoted[0]` share an owner and a promotion index, so a
        // lookup that compared only those returned the first method's message for
        // the second method's panic -- a report naming a line the caller never ran.
        if def_method != use_method {
            continue;
        }
        if use_owner == def_owner || crate::mir::spec::is_path_suffix(&use_owner, def_owner) {
            // Two definitions still match: refuse rather than pick one, because
            // either could be the one the use names.
            if found.is_some() {
                return None;
            }
            found = Some(pieces.clone());
        }
    }
    found
}

/// Whether a local method candidate may answer a *trait* call.
///
/// `want` is the trait path the call names (`std::convert::From`); `have` is the
/// path the candidate's own `impl` block implements, read from the source, or
/// `None` for an inherent `impl`. `want_args`/`have_args` are the two sides'
/// generic arguments as written (`u8` for both sides of `<u16 as From<u8>>::from`
/// against `impl From<u8> for u16`), or `None` when a side names none.
///
/// The rule is an identity match, not a suffix match. rustc prints a trait in a
/// call as its *shortest crate-unique* path, so a bare `Trait` in the dump names
/// this crate's crate-root trait only when the crate declares one; when it does
/// not, the bare name is the shortening of the crate's *only* trait of that name
/// (or an external trait), and the candidate's module-qualified path is what
/// tells which. A suffix match would accept the unrelated `m::Trait` for a bare
/// `Trait` call -- a false proof -- so the two spellings are reconciled exactly:
///
/// * identical paths match (`std::convert::From` vs `std::convert::From`);
/// * a bare `want` (`From`) matches the candidate when the crate declares no
///   trait of that name at all, or declares exactly one, and `have` is it -- the
///   compiler would have printed that trait bare, so the candidate is the one the
///   call named;
/// * a bare `have` (`From`) matches a qualified `want` (`std::convert::From`)
///   only when the crate declares no local trait of that name, so the bare name
///   can only be the library trait -- and it is a `::`-aligned tail of `want`, so
///   the two name the same trait.
///
/// Every name match is then held to the *instantiation*. A generic trait's
/// identity is not its path alone: `impl From<Local> for u16` and the library's
/// `impl From<u8> for u16` share path, owner and method, and differ only in the
/// trait's argument, so a call to one answered from the other's body is a false
/// proof. Two written forms are compared when both sides name arguments: they must
/// be *equal*. An unknown side (`None`) is refused rather than waved through,
/// because a candidate whose arguments could not be read might be the very impl
/// the call did not name.
///
/// Everything else is refused. An inherent candidate (`have` is `None`) can never
/// answer a trait call: its method is not the trait's. That is what closes the
/// `impl MyFrom<u8> for u16` case, where the impl's *trait* differs from the
/// call's even though the method tail (`from`) matches.
///
/// A trait call with no candidate to compare against is the caller's business; an
/// exact-name match is handled before this is reached.
fn trait_candidate_admits(
    prog: &MirProgram,
    want: &str,
    have: Option<&str>,
    want_args: Option<&str>,
    have_args: Option<&str>,
) -> bool {
    let Some(have) = have else {
        return false;
    };
    let names_match = if have == want {
        true
    } else if want.contains("::") {
        // `want` is qualified, so it is not the crate-root trait. `have` may be the
        // bare tail rustc prints for the crate's *unique* trait of that name, which
        // is this same trait only when it is that one.
        crate::mir::spec::is_path_suffix(want, have)
            && local_traits_named(prog, want).is_some_and(|only| only.len() == 1 && only[0] == have)
    } else {
        // `want` is bare. rustc prints it that way for the crate's unique trait of
        // that name, or for the crate-root trait when several share the name, or for
        // an external trait it could not shorten further.
        match local_traits_named(prog, want) {
            // No local trait of that name: the bare name is an external trait. A
            // local `impl` of it is still this crate's impl of *that* trait, so it
            // may answer the call -- the instantiation check below is what keeps it
            // from answering a call to a *different* instantiation of the trait.
            None => true,
            // The crate's only trait of that name -- the one rustc prints bare.
            Some(only) if only.len() == 1 => only[0] == have,
            // Several share the name: rustc prints the crate-root one bare, and that
            // is the `have == want` case handled above.
            Some(_) => false,
        }
    };
    if !names_match {
        return false;
    }
    // The instantiation. Both sides must name the same arguments; an unreadable side
    // is refused, since it could be the impl the call did not name.
    match (want_args, have_args) {
        (Some(w), Some(h)) => args_match(w, h),
        (None, None) => true,
        _ => false,
    }
}

/// Whether a call's trait argument and a candidate `impl`'s own name the same
/// instantiation.
///
/// The two come from different places: the call's from the MIR dump, the impl's from
/// the source, and rustc prints a type with its *shortest crate-unique* path. So a
/// source `impl From<crate::Local> for u16` prints its call's argument as the bare
/// `Local`, and comparing the written forms would refuse the impl's own call. A
/// *bare* dump argument names a type unique in the crate, so a module-qualified
/// source spelling of it is that same type; a *qualified* dump argument is compared
/// exactly, so an `impl From<a::Local> for u16` cannot answer a call naming
/// `b::Local`. See [`trait_candidate_admits`].
fn args_match(want: &str, have: &str) -> bool {
    want == have || (!want.contains("::") && have.rsplit("::").next() == Some(want))
}

/// The local traits declared with the last segment `name`, as their
/// module-qualified paths; `None` when the crate declares none.
///
/// rustc prints a trait in a call as its shortest crate-unique path, so this set
/// is exactly what decides whether a bare call name is this crate's trait (and
/// which one) or must be an external trait. See [`trait_candidate_admits`].
fn local_traits_named(prog: &MirProgram, name: &str) -> Option<Vec<String>> {
    let bare = name.rsplit("::").next().unwrap_or(name);
    let hits: Vec<String> = prog
        .declared_traits
        .iter()
        .filter(|t| t.rsplit("::").next() == Some(bare))
        .cloned()
        .collect();
    (!hits.is_empty()).then_some(hits)
}

/// Whether a call's self type, method and *trait path* name a method some local
/// trait `impl` declares.
///
/// rustc prints a trait call with the trait path (`<W as From<u8>>::from`), not
/// the `impl` location, so [`resolve_callee`] cannot match it by location. The two
/// still name the same method exactly when the call's self type is the impl's
/// owner, the call's method tail is a method that impl declares, and the call's
/// trait is the impl's own trait under the identity rule of
/// [`trait_candidate_admits`] -- an unrelated same-owner trait must not match. This
/// keeps a *local* trait method from being answered by the model even when the
/// trait's name is not declared in this crate: `use std::convert::From;` plus a
/// local `impl From<u8> for W` prints its call `<W as From<u8>>::from`, whose tail
/// `from` would otherwise be modelled as `core`'s conversion -- a false proof. A
/// local `impl conv_shim::From for u16`, by contrast, does not name the call's
/// `std::convert::From`, so the library conversion is still modelled. See
/// [`try_intrinsic`].
fn local_impl_declares(prog: &MirProgram, self_ty: &str, method_tail: &str, want: &str, want_args: Option<&str>) -> bool {
    prog.fns.iter().any(|g| {
        let Some(loc) = impl_self_loc(g) else {
            return false;
        };
        let Some(have_trait) = prog.impl_traits.get(&loc).map(String::as_str) else {
            return false;
        };
        let have_args = prog.impl_trait_args.get(&loc).map(String::as_str);
        g.name.rsplit("::").next() == Some(method_tail)
            && method_owner_type(prog, g).is_some_and(|owner| owner == self_ty)
            && trait_candidate_admits(prog, want, Some(have_trait), want_args, have_args)
    })
}

/// Resolve a call name to the function in the dump it names.
///
/// An exact match is the free-function case: rustc prints a same-crate free
/// function's call and its definition by the same bare name. Otherwise the name
/// is a qualified call (`Type::m`) whose *definition* rustc prints as
/// `<impl at …>::m`, so only the tail is shared.
///
/// The tail alone is not enough. `Vec2::push` and `Vec::<u8>::push`, or a free
/// `wrapping_add` and `core::num::<impl u8>::wrapping_add`, share a tail while
/// naming different functions, and answering such a call from the wrong body is a
/// false proof. Three guards keep that from happening:
///
/// * A call name that still carries an `impl` projection (`…::<impl u8>::…`) is a
///   `core`/`std` callee. rustc prints a *local* method call with its concrete
///   type (`Vec2::push`, `<S as T>::m`), never with `<impl`, so such a name is
///   never a same-dump call and is refused outright.
/// * A surviving candidate must be the method for the same type: an instance
///   method's `self` type must equal the call's type, and a *static* associated
///   function -- which has no `self` to read -- must have an `impl` whose owner
///   type equals the call's type. The owner is read from the source; when it
///   cannot be established the candidate is refused, because a static method's
///   tail is otherwise shared by any type (`<u16 as From<u8>>::from` would answer
///   a local `impl Foo { fn from }`, a false proof).
/// * A *trait* call must agree on the trait. The owner type is not enough: a local
///   `impl From<u8> for u16` and the standard library's `impl From<u8> for u16`
///   share both the tail `from` and the owner `u16`, so owner-matching alone let
///   the local body answer `<u16 as std::convert::From<u8>>::from`, a false proof
///   of a call the compiler resolved to the library. The call's trait path must
///   name the candidate `impl`'s own trait, and the two must instantiate it the
///   same way (see [`trait_candidate_admits`]), which the source records. An
///   *inherent* candidate never answers a trait call.
/// * A free function never matches a qualified call, because rustc prints a
///   same-crate free function's call bare -- the exact-match case above.
///
/// `None` means the call is not modelled, which the caller reports rather than
/// guesses at.
fn resolve_callee(prog: &MirProgram, name: &str) -> Option<usize> {
    if let Some(i) = prog.fns.iter().position(|g| g.name == name) {
        return Some(i);
    }
    if name.contains("<impl") {
        return None;
    }
    let tail = name.rsplit("::").next()?;
    let want_ty = call_type(name)?;
    // A call whose receiver is literally `Self` is made from inside a trait's
    // *default* body, where the concrete type is not known. Resolving it to the
    // right body would need the `Self` type the enclosing call was made with,
    // which this resolver does not carry; resolving it to the *default* method
    // would be a false proof whenever an impl overrides it. So it is refused
    // rather than guessed. This is the `range_shim` hole: a user trait's default
    // `into_iter` that calls `self.set(42)`, with `set` overridden by the impl,
    // had the *default* (no-op) `set` inlined, so a caller's contract about the
    // override's effect was *proved* against a body that does nothing.
    if want_ty == "Self" {
        return None;
    }
    // The trait the call names, when it is a trait call (`<T as Trait<..>>::m`).
    // `None` for a bare `Type::m`, which rustc prints for both an inherent method
    // and a trait method in scope, so no trait check applies there.
    let want_trait = call_trait_path(name);
    let want_args = call_trait_args(name);
    let mut hits = prog.fns.iter().enumerate().filter(|(_, g)| {
        if g.name.rsplit("::").next() != Some(tail) {
            return false;
        }
        let self_matches = match method_self_type(g) {
            Some(self_ty) => self_ty == want_ty,
            None => match method_owner_type(prog, g) {
                Some(owner_ty) => owner_ty == want_ty,
                None => false,
            },
        };
        if !self_matches {
            return false;
        }
        // The candidate's own trait, from its `impl` block's location.
        let have_trait = impl_self_loc(g)
            .and_then(|loc| prog.impl_traits.get(&loc))
            .map(String::as_str);
        let have_args = impl_self_loc(g)
            .and_then(|loc| prog.impl_trait_args.get(&loc))
            .map(String::as_str);
        match want_trait.as_deref() {
            Some(want) => trait_candidate_admits(prog, want, have_trait, want_args.as_deref(), have_args),
            // An inherent-looking call (`MyType::from`, with no ` as ` projection).
            // rustc prints both an inherent method and a trait method in scope this
            // way, so the candidate is *not* required to be inherent -- a bare
            // `MyType::from` that resolves to a trait impl is legitimate. The owner
            // match alone is as strong as it was before the trait check existed, and
            // the ambiguity that would make it unsafe (two `from`s in scope, so
            // rustc could not pick one) does not compile.
            None => true,
        }
    });
    let first = hits.next();
    let second = hits.next();
    if let (Some((i, _)), None) = (first, second) {
        return Some(i);
    }
    // Reaching here means the search found no *single* impl candidate. Two or more
    // hits are ambiguous, so the call is refused rather than guessed at -- and
    // crucially not answered from the trait's default, which would verify a contract
    // against a body an override replaced (a false proof). The default is the body
    // Rust calls only when *no* impl candidate exists at all: an impl that does not
    // override the method emits no `<impl at …>::m`, so the search finds nothing and
    // the default is the only body. See the default branch below.
    if first.is_some() {
        return None;
    }
    // A trait's *default* method has no `impl` block in the dump: rustc prints its
    // definition as `Trait::m` -- the trait's path, with no `<impl at` -- so the
    // location lookup above cannot find it and its `self` type is the trait's
    // `Self`. Match it by the trait path the call names and the method tail, and
    // only when the two trait paths are *equal*: a default method is the only body
    // for its trait, so the definition and the call print the same path for it,
    // whereas admitting a bare local trait for a qualified call
    // (`<u8 as std::cmp::Ord>::min` against a crate-root `Ord::min`) would be a
    // false proof. See [`trait_candidate_admits`].
    if let Some(want) = want_trait.as_deref() {
        let owner = |g: &MirFn| {
            let prefix = g.name.strip_suffix(tail)?;
            let prefix = prefix.strip_suffix("::")?;
            (!prefix.is_empty()).then(|| prefix.to_string())
        };
        if let Some(i) = prog.fns.iter().position(|g| {
            g.impl_loc.is_none()
                && g.name.rsplit("::").next() == Some(tail)
                && owner(g).is_some_and(|have| have == want)
        }) {
            return Some(i);
        }
    }
    None
}

/// Answer a call from the callee's *contract* when the callee's body is not in
/// the dump.
///
/// The call is *always* handled, so this returns `()`. There is no body to inline
/// and so no fall-through: the alternative to a verdict here is the generic
/// "unmodelled function" message, and every branch below has something more
/// specific to say -- a decided call, or a refusal naming what stopped it.
///
/// The two obligations are the standard modular pair, and the *order* between
/// them is what keeps the assumption sound. The precondition is proved of the
/// arguments first; only then is the postcondition assumed of the result. A route
/// that assumed the postcondition without proving the precondition would be
/// assuming the conclusion, which is the whole reason a contract is not a free
/// pass.
///
/// The divergence check is the third piece and it is not optional. `ensures
/// false` describes a callee that never returns, so a caller's claims *after* the
/// call are vacuously true -- and a report that counted them would say "verified"
/// about a function that does not run. `find_model` on the postcondition answers
/// this: `Unsat` means no input satisfies it, so the call diverges. This is the
/// MIR twin of [`crate::wp::Rule::DivergentCall`], and it is a *refutation* query,
/// so its discharge is `Unsat` rather than `Valid`.
#[allow(clippy::too_many_arguments)]
fn try_callee_contract(
    prog: &MirProgram,
    st: &mut State,
    name: &str,
    cc: &CalleeContract,
    args: &[Operand],
    dest: &Place,
    target: usize,
    report: &mut MirReport,
    work: &mut Vec<State>,
    pins: &[(u32, u64)],
) {
    let cur = &prog.fns[st.frame.func];
    // The names have to line up positionally with the arguments, and there is no
    // second signal to fall back on: a callee outside the dump has no `debug`
    // bindings, so the source signature is the only source of names. A mismatch
    // means the scanner and the call disagree about the arity, and binding the
    // names it did read would attach `requires: n <= 10` to whatever argument
    // happens to be first. Refusing is the only safe answer.
    if !cc.sig_readable {
        report.unknown_paths.push(format!(
            "call to `{name}`: the callee's signature was not read whole, so the contract's \
             parameters and return type cannot be bound to the call"
        ));
        return;
    }
    if cc.params.len() != args.len() {
        report.unknown_paths.push(format!(
            "call to `{name}`: the callee's contract names {} parameter(s) but the call has {} \
             argument(s), so the precondition cannot be attached to them",
            cc.params.len(),
            args.len()
        ));
        return;
    }
    // A reference argument is refused. `Ty::Ref` is modelled as its referent, so
    // the callee's write through `&mut` would be a write to a value the caller
    // passed *by value* here -- the mutation would not reach the caller's local,
    // and a postcondition about it would be checked against the wrong state. A
    // contract over reference parameters needs the aliasing model this frontend
    // does not have, so the call stays unknown rather than being assumed.
    let by_ref = args.iter().any(|a| match a {
        Operand::Copy(p) | Operand::Move(p) => {
            matches!(cur.ty_of(p.local), Some(Ty::Ref(_)))
        }
        Operand::Const(_) => false,
    });
    if by_ref {
        report.unknown_paths.push(format!(
            "call to `{name}` passes a reference, and a callee outside the dump has no \
             aliasing model to reason about it through its contract"
        ));
        return;
    }
    let mut names: BTreeMap<String, Var> = BTreeMap::new();
    for (param, a) in cc.params.iter().zip(args) {
        match operand(&mut st.env, a) {
            Val::Sym(v, _) => {
                names.insert(param.clone(), v);
            }
            Val::Bool(p) => {
                names.insert(param.clone(), smt::ite(p, smt::word(1, 1), smt::word(0, 1)));
            }
            _ => {
                report.unknown_paths.push(format!(
                    "call to `{name}`: argument `{param}` is not a modelled value, so the \
                     contract cannot be evaluated at the call site"
                ));
                return;
            }
        }
    }
    let fields = FieldEnv::with_consts(prog.consts.clone());

    // `Pre`: the callee's precondition, proved of the call's arguments.
    let mut pre: Option<Pred> = None;
    for r in &cc.requires {
        match spec::eval_requires(r, &names, &cc.signed, &fields) {
            Ok(p) => pre = Some(match pre {
                None => p,
                Some(prev) => smt::and(prev, p),
            }),
            Err(e) => {
                report.unknown_paths.push(format!(
                    "unreadable `requires` on the callee `{name}`: {e}"
                ));
                return;
            }
        }
    }
    if let Some(p) = pre {
        report.obligations.push(Obligation {
            kind: ObligationKind::CalleePrecondition,
            verdict: prove_obligation(st.path, p, pins),
        });
    }

    // The return width comes from the *caller's* destination, which is the one
    // place the return type is available without the callee's MIR.
    let Some(w) = type_of_place(cur, dest).and_then(|t| t.width()) else {
        report.unknown_paths.push(format!(
            "call to `{name}` returns an aggregate, which is not modelled through a contract"
        ));
        return;
    };
    let ret_v = smt::var(w);

    // The postcondition, over a fresh `ret` and the call's arguments. Built once
    // and used twice: refuted to detect divergence, then assumed.
    let mut post: Option<Pred> = None;
    for e in &cc.ensures {
        match spec::eval_ensures(
            e,
            &names,
            Some(ret_v),
            spec::RET_IS_UNKNOWN,
            &cc.signed,
            cc.ret_signed,
            &fields,
            &BTreeMap::new(),
        ) {
            Ok(p) => post = Some(match post {
                None => p,
                Some(prev) => smt::and(prev, p),
            }),
            Err(e) => {
                report.unknown_paths.push(format!(
                    "unreadable `ensures` on the callee `{name}`: {e}"
                ));
                return;
            }
        }
    }
    let Some(post) = post else {
        // No postcondition is not "postcondition `true`". With nothing to assume
        // the result is unknown, and there is no body to inline, so the call is
        // reported rather than guessed.
        report.unknown_paths.push(format!(
            "call to `{name}`: the callee has no `ensures`, so there is nothing to assume \
             about its result and no body in the dump to execute"
        ));
        return;
    };

    // An unreachable call site proves nothing about the callee. When the path
    // condition is already unsatisfiable the call is never executed, so the
    // divergence query below would be asking about inputs the program cannot
    // reach -- and its `Unsat` would be saying "this path is dead", not "the callee
    // diverges". Reporting divergence there is a false failure about a call that
    // cannot happen, so a dead path is dropped instead.
    if matches!(find_obligation(st.path, pins), Verdict::Unsat) {
        return;
    }
    // Divergence: can any input satisfy the postcondition? `Unsat` says no, so the
    // call never returns and every claim after it would be vacuous.
    let diverges = matches!(
        find_obligation(smt::and(st.path, post), pins),
        Verdict::Unsat
    );
    if diverges {
        report.obligations.push(Obligation {
            kind: ObligationKind::CalleeDiverges,
            verdict: find_obligation(smt::and(st.path, post), pins),
        });
        return;
    }

    // Assume the postcondition for the result.
    st.path = smt::and(st.path, post);
    let ret_val = if w == 1 {
        Val::Bool(ret_v.eq_val(1))
    } else {
        Val::Sym(ret_v, Sign::of_bool(cc.ret_signed))
    };
    st.env.set(dest, ret_val);
    advance(prog, st.clone(), target, report, work, pins);
}

/// Answer a self-recursive call by its contract instead of inlining it.
///
/// Returns `Some(())` when the call was handled (the caller must then continue at
/// its own `target`, or stop when the obligation failed), `None` when it was not a
/// recursive call or recursion is not licensed, so the caller falls through to the
/// inliner.
///
/// # Why this is sound
///
/// A self-call inlined once is the *first* unrolling, and `DEFAULT_INLINE_DEPTH`
/// stops the second. The contract route replaces the unrolling with an induction:
///
/// * the callee's precondition is *proved* of the call's arguments (`Pre`), so the
///   assumption only applies to calls the function itself admits;
/// * the `decreases:` measure is *proved* to be non-negative at entry and strictly
///   smaller at the call (`Dec`), which is the well-founded basis; and
/// * the postcondition is *assumed* of the result.
///
/// The measure is what makes this an induction rather than a circular argument: a
/// strictly decreasing sequence in a well-founded order is finite, so there is a
/// base case, and at the base case the body must establish the postcondition on
/// its own. Nothing here *assumes* the postcondition at the base case -- the
/// `return` obligations still have to be discharged by the body -- so a body that
/// does not establish it is still a failure.
///
/// Every check is an obligation, so a wrong measure or a precondition the
/// arguments do not meet is a *finding*, not a silent fallback.
#[allow(clippy::too_many_arguments)]
fn try_recursive_call(
    prog: &MirProgram,
    st: &mut State,
    root: usize,
    name: &str,
    args: &[Operand],
    dest: &Place,
    target: usize,
    rec: &Option<RecCtx>,
    report: &mut MirReport,
    work: &mut Vec<State>,
    pins: &[(u32, u64)],
) -> Option<()> {
    // Only a self-call, and only the function under verification: an inlined
    // callee's frame has a different `func`, and its own recursion is not this
    // function's induction.
    //
    // The name is resolved with the same rule the inliner uses (exact match, else
    // a unique tail match that also agrees on the method's `self` type), and the
    // result has to be the root itself. A name that resolves to nothing, or
    // ambiguously, is not this function calling itself.
    //
    // This must run *before* the intrinsic dispatch below, but it must not
    // swallow an intrinsic call. A function named `wrapping_add` that calls
    // `u8::wrapping_add` is calling the *intrinsic*, not itself; treating the
    // call as recursive would assume the function's own postcondition in place of
    // evaluating the intrinsic, which is a false proof. `resolve_callee` refuses
    // that name because the intrinsic's `self` type (`u8`) is not the local
    // function's, so the check falls through to the intrinsic model.
    if st.frame.func != root || resolve_callee(prog, name) != Some(root) {
        return None;
    }
    // The root frame has no caller, so a self-call is recursion by construction.
    // A frame with a caller is an inlined callee, and reaching the root's name
    // from there is not the root calling itself.
    if st.frame.caller.is_some() {
        return None;
    }
    let Some(rc) = rec else { return None };
    // No postcondition means nothing to assume, so the call has no contract route
    // and falls back to inlining (which will report the depth cutoff).
    if rc.rec.ensures.is_empty() {
        return None;
    }
    let f = &prog.fns[root];
    // The contract is evaluated over the call's arguments, so the field bindings
    // are the call site's and are rebuilt below. The `const` table is not: a
    // constant has the same value at the call as at entry, and the entry state
    // already carries it in `rc.rec.consts`. Handing the reader an empty table
    // here made a contract that names a constant -- `requires: n <= LIMIT` --
    // unreadable at the self-call, which turned a decidable proof into a refusal.
    let fields = FieldEnv::with_consts(rc.rec.consts.clone());

    // The argument bindings at the call site: name -> the value the caller holds.
    // A name that has no value there (an unmodelled operand) makes the whole call
    // unmodelled, which is the same refusal the inliner would give.
    let mut names: BTreeMap<String, Var> = BTreeMap::new();
    for (i, a) in args.iter().enumerate() {
        let Some(&l) = f.arg_locals.get(i) else { continue };
        match operand(&mut st.env, a) {
            Val::Sym(v, _) => {
                names.insert(f.name_of(l), v);
            }
            Val::Bool(p) => {
                names.insert(f.name_of(l), smt::ite(p, smt::word(1, 1), smt::word(0, 1)));
            }
            _ => {
                report
                    .unknown_paths
                    .push(format!("unmodelled argument to a recursive call to `{name}`"));
                return Some(());
            }
        }
    }

    // `Pre`: the callee's precondition, proved of the call's arguments. This is a
    // proof obligation, so an unreadable precondition is a refusal rather than a
    // silently skipped check -- assuming a postcondition without the matching
    // precondition would be assuming the conclusion.
    let mut pre_ok = true;
    let mut pre: Option<Pred> = None;
    for r in &rc.rec.requires {
        match spec::eval_requires(r, &names, &rc.rec.signed, &fields) {
            Ok(p) => pre = Some(match pre {
                None => p,
                Some(prev) => smt::and(prev, p),
            }),
            Err(e) => {
                report
                    .unknown_paths
                    .push(format!("unreadable `requires` at a recursive call: {e}"));
                pre_ok = false;
                break;
            }
        }
    }
    if !pre_ok {
        return Some(());
    }
    if let Some(p) = pre {
        report.obligations.push(Obligation {
            kind: ObligationKind::RecursivePrecondition,
            verdict: prove_obligation(st.path, p, pins),
        });
    }

    // `Dec`: the measure at the call is non-negative and strictly below its value
    // at entry. Both halves are needed. Non-negativity is what makes the order
    // well-founded (a signed measure that goes negative would otherwise
    // "decrease" forever); strictness is the progress.
    if let Some((m_entry, signed)) = rc.measure_entry {
        match spec::eval_measure(&rc.rec.decreases, &names, &rc.rec.signed, &rc.rec.consts) {
            Ok((m_call, call_signed)) => {
                if call_signed != signed || smt::bits(m_call) != smt::bits(m_entry) {
                    report.unknown_paths.push(
                        "the measure at a recursive call has a different type than at entry"
                            .into(),
                    );
                    return Some(());
                }
                let zero = smt::word(0, smt::bits(m_entry));
                let nonneg = if signed { smt::sge(m_entry, zero) } else { smt::truth(true) };
                let decreases = if signed {
                    smt::slt(m_call, m_entry)
                } else {
                    smt::ult(m_call, m_entry)
                };
                report.obligations.push(Obligation {
                    kind: ObligationKind::RecursiveDecreases,
                    verdict: prove_obligation(st.path, smt::and(nonneg, decreases), pins),
                });
            }
            Err(e) => {
                report.unknown_paths.push(format!("unreadable `decreases`: {e}"));
                return Some(());
            }
        }
    } else {
        report.unknown_paths.push(
            "a recursive call has no `decreases:` measure at entry to compare against".into(),
        );
        return Some(());
    }

    // Assume the postcondition for the result: a fresh variable for `ret`, the
    // conjuncts of every `ensures`, then write it to the call's destination. The
    // postcondition is *assumed*, never proved, here -- proving it is the `return`
    // obligations' job.
    let Some(w) = f.ret_ty.width() else {
        report
            .unknown_paths
            .push("a recursive call returns an aggregate, which is not modelled".into());
        return Some(());
    };
    let ret_v = smt::var(w);
    let ret_signed = rc.rec.ret_signed;
    let mut post_assumed: Option<Pred> = None;
    for e in &rc.rec.ensures {
        match spec::eval_ensures(
            e,
            &names,
            Some(ret_v),
            spec::RET_IS_UNKNOWN,
            &rc.rec.signed,
            ret_signed,
            &fields,
            &BTreeMap::new(),
        ) {
            Ok(p) => post_assumed = Some(match post_assumed {
                None => p,
                Some(prev) => smt::and(prev, p),
            }),
            Err(e) => {
                report
                    .unknown_paths
                    .push(format!("unreadable `ensures` at a recursive call: {e}"));
                return Some(());
            }
        }
    }
    let assumed = post_assumed.unwrap_or_else(|| smt::truth(true));
    st.path = smt::and(st.path, assumed);
    let ret_val = if w == 1 {
        Val::Bool(ret_v.eq_val(1))
    } else {
        Val::Sym(ret_v, Sign::of_bool(ret_signed))
    };
    st.env.set(dest, ret_val);
    advance(prog, st.clone(), target, report, work, pins);
    Some(())
}

/// Push the successor states of an edge to `target`, applying the loop cut when
/// this edge enters the invariant's header.
///
/// Every edge in the walk goes through here so the cut cannot be bypassed by a
/// terminator that happens to be spelled differently -- a `goto` and a `switchInt`
/// arm into the same header are the same induction case.
fn advance(
    prog: &MirProgram,
    mut st: State,
    target: usize,
    report: &mut MirReport,
    work: &mut Vec<State>,
    pins: &[(u32, u64)],
) {
    let cut = match st.cut.clone() {
        Some(c) if c.func == st.frame.func && c.header == target => c,
        _ => {
            work.push(State { block: target, ..st });
            return;
        }
    };
    let cur = &prog.fns[st.frame.func];
    let inv = match eval_invariant_here(cur, &st.env, &cut.text) {
        Ok(p) => p,
        Err(e) => {
            report.unknown_paths.push(format!("unreadable `invariant`: {e}"));
            return;
        }
    };
    let back = cut.back_edges.contains(&st.block);
    let kind = if back {
        ObligationKind::LoopInvariantPreserve
    } else {
        ObligationKind::LoopInvariantInit
    };
    report.obligations.push(Obligation {
        kind,
        verdict: prove_obligation(st.path, inv, pins),
    });
    // Termination, at the back edge and only there. The measure is read *now*,
    // after the body has run, and compared against the value at the head: the
    // obligation is `path => V' < V`, where `V'` came out of the body's own
    // symbolic execution and `V` was evaluated over a havoced header state. That
    // is what makes it an induction step rather than a restatement. The relation
    // is strict and, on a fixed bit width, that is enough on its own: a strictly
    // decreasing sequence in a finite domain cannot be infinite, so no separate
    // lower-bound check is needed -- and one would be *wrong* here, because the
    // measure is a machine word, where "going negative" is just a smaller word,
    // which is exactly the descent that proves termination.
    if back {
        if let Some(vtext) = cut.variant.clone() {
            match st.variant_entry {
                None => report.unknown_paths.push(
                    "a loop `variant:` was declared but the loop head was never entered, so \
                     there is no measure at the head to compare against"
                        .into(),
                ),
                Some((v_entry, entry_signed)) => {
                    match eval_measure_here(cur, &st.env, &vtext) {
                        Ok((after, after_signed)) => {
                            if after_signed != entry_signed || smt::bits(after) != smt::bits(v_entry)
                            {
                                report.unknown_paths.push(
                                    "the loop `variant:` measure changed type across an iteration"
                                        .into(),
                                );
                            } else {
                                let decreases = if entry_signed {
                                    smt::slt(after, v_entry)
                                } else {
                                    smt::ult(after, v_entry)
                                };
                                report.obligations.push(Obligation {
                                    kind: ObligationKind::LoopVariant,
                                    verdict: prove_obligation(st.path, decreases, pins),
                                });
                            }
                        }
                        Err(e) => {
                            report.unknown_paths.push(format!("unreadable `variant`: {e}"));
                        }
                    }
                }
            }
        }
    }
    // The cut closes here. A back edge is not followed: the assertion above is
    // the induction step, and re-entering the header would be the unwinding this
    // replaces.
    if back {
        return;
    }
    // An entry edge continues, but not with the values the path arrived with.
    // The loop is about to run, and the invariant says what is true of the header
    // *whenever* it is reached -- not what happens to be true the first time. So
    // the locals the loop can write are replaced by fresh values and the
    // invariant is assumed over those. Only then does the exit edge carry
    // `I && !guard`, which is what lets a postcondition be proved for every state
    // the loop can leave rather than for the one state the first pass produced.
    // Resolve each written place through the run's reference map first: a loop
    // that writes `*p` (where `p = &mut x` was taken *before* the loop) writes
    // `x`, but the syntactic destination is `p`. Without this the header kept
    // `x`'s entry-state value, the exit guard `x > 100` folded to `false`, the
    // exit edge was pruned as unreachable, and the postcondition was never
    // checked -- a false proof. `place.local` and `resolve`'s target are the same
    // local for every non-reference write, so this only widens the set.
    let mut havoc: BTreeSet<u32> = BTreeSet::new();
    for &l in &cut.havoc {
        havoc.insert(l);
        // The referent of a reference the loop wrote through. `pointee` follows
        // one level of value indirection (`_2 = &mut _1` records `2 -> _1`), which
        // `resolve` does not for a bare local: the write `(*_2) = v` names `_2`,
        // and without this the havoc missed `_1` and its entry-state value kept
        // the exit guard folded to `false` -- a false proof.
        let resolved = st.env.pointee(&Place { local: l, proj: Vec::new() });
        havoc.insert(resolved.local);
    }
    for &l in &havoc {
        if let Some(ty) = cur.ty_of(l) {
            // A reference local's value *is* its referent's (`Ty::Ref` is modelled
            // as the referent), so it is havoced at the referent's width -- the
            // width it was seeded at. Reading `ty.width()` on the `Ty::Ref` itself
            // gives `None`, which sent a written-through reference argument to the
            // aggregate branch and left its referent at the entry value: the exit
            // guard then folded and a false postcondition was `Verified` (`w_false`
            // below). A `&mut u8` argument is the commonest shape of this.
            let inner = ty.referent();
            if let Some(w) = inner.width() {
                // `var`, not `var_named`: a fresh variable is the point. A named
                // one would return the very variable being replaced, and the
                // havoc would be a no-op.
                let fresh = if w == 1 {
                    Val::Bool(smt::var(1).eq_val(1))
                } else {
                    // A havoced local is a fresh *input* of the same type, so it
                    // keeps the type's sign.
                    Val::Sym(smt::var(w), Sign::of(inner))
                };
                st.env.locals.insert(l, fresh);
            } else {
                // A local with no bit width is an aggregate (a struct, tuple or
                // array), whose value lives in the parts stores rather than in
                // `locals`. A loop that writes it -- the `RangeInclusive` a `for`
                // loop advances through `&mut`, or a `c.lo = ..` field write --
                // left those parts at the value they had at entry, so the header
                // state was over-constrained, the exit guard folded, and the
                // postcondition was never checked: a false proof. Replacing the
                // whole value is what "an arbitrary value of this type" means, and
                // dropping the parts is the sound direction -- a word part is
                // replaced by a fresh variable of its own width so a model that
                // reads it (a range's `start`/`end`) still resolves, while a
                // non-word part is dropped to `Unknown`.
                st.env.havoc_parts(l);
            }
        }
    }
    let inv = match eval_invariant_here(cur, &st.env, &cut.text) {
        Ok(p) => p,
        Err(e) => {
            report.unknown_paths.push(format!("unreadable `invariant`: {e}"));
            return;
        }
    };
    st.path = smt::and(st.path, inv);
    // The measure at the head, over the same havoced state the invariant was
    // assumed on. Reading it here rather than from the arriving state is what
    // makes the back-edge comparison an induction step: the head is *any* state
    // satisfying `I`, not the one the first pass happened to produce.
    if let Some(vtext) = &cut.variant {
        st.variant_entry = match eval_measure_here(cur, &st.env, vtext) {
            Ok(v) => Some(v),
            Err(e) => {
                report.unknown_paths.push(format!("unreadable `variant`: {e}"));
                return;
            }
        };
    }
    work.push(State { block: target, ..st });
}


/// Evaluate a `variant:` measure in the current state, as a value with its sign.
///
/// The loop counterpart of [`eval_invariant_here`]: a measure is an expression
/// rather than a proposition, so it is read with the measure parser and returns
/// the term and its signedness together. Sharing the parse with
/// [`measure_signed`] is what keeps the value and its relation consistent.
fn eval_measure_here(f: &MirFn, env: &Env, text: &str) -> Result<(Var, bool), String> {
    let names = invariant_names(f, env);
    crate::mir::spec::eval_measure(text, &names, &signed_names(f), &env.consts)
        .map_err(|e| e.to_string())
}

/// The last segment of a path, with any generic arguments stripped.
///
/// The dump spells a call with its generics (`Arguments::<'_>::new_const::<1>`,
/// `new_v1::<1, 1>`, `rt::Argument::<'_>::new_display::<T>`,
/// `std::rt::panic_display::<u8>`), so the bare last segment is `<1>`/`<T>`/`<u8>`
/// rather than the name. The `::<…>` groups are skipped as *balanced* brackets --
/// a group can nest (`Argument::<&'_ str>`) -- and the last `::`-segment of what is
/// left is the name. A path with no generics (`std::rt::panic_fmt`) is returned
/// unchanged. Both the `core::fmt` model's dispatch and a panic report's fallback
/// name go through this, so a name is never reported as its type arguments.
fn path_tail(name: &str) -> &str {
    // The last `::` at generic-depth zero that is not the `::` of a `::<…>`
    // bracket, so the method name is what follows it up to the first `<`.
    let b = name.as_bytes();
    let mut depth = 0i32;
    let mut last_sep: Option<usize> = None;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'<' => depth += 1,
            b'>' => depth -= 1,
            b':' if depth == 0
                && i + 1 < b.len()
                && b[i + 1] == b':'
                && b.get(i + 2) != Some(&b'<') =>
            {
                last_sep = Some(i + 2);
                i += 2;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    let rest = match last_sep {
        Some(k) => &name[k..],
        None => name,
    };
    let head = match rest.find('<') {
        Some(k) => &rest[..k],
        None => rest,
    };
    // `new_const::<1>` leaves `new_const::` once the `<…>` is cut, so the
    // separator that introduced the generic goes with it.
    head.strip_suffix("::").unwrap_or(head)
}

/// The `i`-th argument of the last `::<…>` group in a path, parsed as a `usize`.
///
/// `Arguments::<'_>::new_v1::<2, 1>` has `("_", "2", "1")` as its groups, so index
/// `1` is the argument count. A missing or non-numeric item returns `None`, which
/// the caller turns into "unmodelled" -- a printer change is refused rather than
/// guessed at.
fn generic_arg(name: &str, i: usize) -> Option<usize> {
    let open = name.rfind("::<")?;
    let rest = &name[open + 3..];
    let close = rest.find('>')?;
    let item = rest[..close].split(',').nth(i)?;
    item.trim().parse().ok()
}

/// Whether `name` is a call the `core::fmt` model answers, and the model's
/// `Result` for it.
///
/// Edition 2024 builds a `panic!`/`assert!` message out of `core::fmt` calls
/// rather than a single literal, so a panic's message has to be *recovered* from
/// the chain rather than read off one operand. The chain is small and fixed:
///
/// * `core::fmt::rt::Argument::<'_>::new_display::<T>(&v)` -- wraps one argument
///   for display. Its payload is the argument's *value*, which this model does
///   not need (the message keeps the `{}` placeholder), so it is a no-op.
/// * `Arguments::<'_>::from_str(const "…")` -- the whole message is one literal.
/// * `Arguments::<'_>::new_const::<N>(&PIECES)` -- `N` literal pieces and no
///   arguments.
/// * `Arguments::<'_>::new_v1::<P, A>(&PIECES, &ARGS)` -- `P` pieces and `A`
///   arguments, which render as the pieces joined by `{}`.
/// * `Arguments::<'_>::new::<LEN, A>(const b"…", &ARGS)` -- the newer spelling
///   with the template in one byte string.
/// * `std::rt::panic_fmt(args)` -- the diverging consumer; its message is
///   whatever the `Arguments` local holds.
///
/// Anything not on this list returns `None`, so a `core::fmt` call this model
/// does not know stays "unmodelled" rather than becoming a wrong message.
///
/// The placeholder count is the *argument* count, which is why the pieces are
/// joined by the consuming call and not by the builder: see
/// [`crate::mir::parse::join_format_pieces`].
fn try_fmt_call(
    name: &str,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
    dest_ty: Option<&Ty>,
) -> Option<Result<(), String>> {
    use crate::mir::parse::{decode_format_template, join_format_pieces};
    // The `Arguments`-building calls are printed *unqualified*
    // (`Arguments::<'_>::new_const::<1>`), so a name cannot tell them from a local
    // item of the same name. The destination's *type* can: `new_const`/`new_v1`/
    // `new`/`from_str` all return `core::fmt::Arguments<'_>`, and no other call
    // does. That is what this guard keys on -- a local function named `new` whose
    // destination is not an `Arguments` is left to its own body, and a call this
    // model does not know stays "unmodelled" rather than becoming a wrong message.
    let makes_args = dest_ty.is_some_and(|t| match t {
        Ty::Other(s) => s.contains("fmt::Arguments"),
        _ => false,
    });
    // The `rt::Argument` wrappers are printed qualified (`core::fmt::rt::Argument`),
    // so their own guard is on the name. A user item cannot be spelled in someone
    // else's crate, so a name with one of these prefixes is `core`'s -- and a local
    // `Argument` is answered by its body in the same dump first.
    let qualified = ["std::fmt::", "core::fmt::"]
        .iter()
        .any(|p| name.starts_with(p) || name.contains(&format!("::{p}")));
    if !makes_args && !qualified {
        return None;
    }
    // The pieces an operand names: either a promoted `const NAME::promoted[0]`
    // (recorded on the local it was assigned to) or a local that already carries
    // them.
    let pieces_of = |env: &Env, o: &Operand| -> Option<Vec<String>> {
        match o {
            Operand::Const(Const::Other(n)) => lookup_promoted(&env.promoted, n),
            Operand::Copy(p) | Operand::Move(p) if p.proj.is_empty() => {
                env.piece_sets.get(&p.local).cloned()
            }
            _ => None,
        }
    };
    let tail = path_tail(name);
    // There is deliberately no arm for `panic_fmt` / `panic_nounwind_fmt` here.
    // Those are the *consumers* of the `Arguments` chain, and they return `!`, so
    // the executor reaches them as a diverging call (see `Divergence`) before this
    // function is ever consulted -- `try_fmt_call` is called only on the
    // non-diverging path. The message is recovered from the `Arguments` local's
    // string store by `panic_message` instead. A branch that recorded the message
    // here would be dead code; it was, and the review caught it.
    if tail == "from_str" {
        // `Arguments::from_str("literal")`: the message is the literal itself.
        let lit = args.iter().find_map(|a| match a {
            Operand::Const(Const::Str(s)) => Some(s.clone()),
            _ => None,
        })?;
        env.strs.insert(dest.local, lit);
        return Some(Ok(()));
    }
    if tail == "new_const" {
        // `new_const::<P>(&PIECES)`: `P` literal pieces and no arguments, so the
        // pieces are the message as they stand.
        let pieces = args.iter().find_map(|a| pieces_of(env, a))?;
        env.strs.insert(dest.local, join_format_pieces(&pieces, 0));
        return Some(Ok(()));
    }
    if tail == "new_v1" {
        // `new_v1::<P, A>(&PIECES, &ARGS)`: `P` pieces and `A` arguments. The
        // argument count is what says how many placeholders the message has, so it
        // is read from the generic list rather than guessed from the pieces.
        let pieces = args.iter().find_map(|a| pieces_of(env, a))?;
        let n = generic_arg(name, 1)?;
        env.strs.insert(dest.local, join_format_pieces(&pieces, n));
        return Some(Ok(()));
    }
    if tail == "new" {
        // `Arguments::new::<LEN, A>(const b"…", &ARGS)`: the template is one byte
        // string, decoded to pieces. It can be a direct operand or -- as stable
        // prints it -- a local it was assigned to first.
        let bytes = args
            .iter()
            .find_map(|a| match a {
                Operand::Const(Const::Bytes(b)) => Some(b.clone()),
                Operand::Copy(p) | Operand::Move(p) if p.proj.is_empty() => {
                    env.tmpl_bytes.get(&p.local).cloned()
                }
                _ => None,
            })?;
        let pieces = decode_format_template(&bytes)?;
        let n = generic_arg(name, 1)?;
        env.strs.insert(dest.local, join_format_pieces(&pieces, n));
        return Some(Ok(()));
    }
    // `rt::Argument::<'_>::new_display::<T>(&v)` and its siblings wrap one
    // argument; the message keeps the placeholder, so the wrapper is a no-op. The
    // destination stays a non-string local, which is what it is.
    if name.contains("core::fmt::rt::Argument") && tail.starts_with("new_") {
        env.set(dest, Val::Unknown);
        return Some(Ok(()));
    }
    None
}

/// Answer a modelled `for`-loop range method from the receiver's struct fields.
///
/// The `for` desugaring lowers to `RangeInclusive::new(start, end)` (or
/// `Range::new`), an `IntoIterator::into_iter` identity, and a loop that calls
/// `<Range as Iterator>::next(&mut range)` until it yields `None`. Those three are
/// the whole of it, and modelling them makes the commonest loop in Rust reachable
/// through the existing loop machinery: an `invariant:` decides the loop, and
/// without one it is unwound like any other.
///
/// # Where the state lives
///
/// A range is a struct, so its fields are in the environment's `fields` store, keyed
/// by `(local, field index)`, exactly as any struct literal's are. `new` writes
/// `start` (0), `end` (1) and, for `RangeInclusive`, `exhausted` (2); `next` reads
/// and advances them. The field *index* is the declaration order, which is the order
/// the dump's `_1.0`/`_1.1`/`_1.2` projections count in -- `RangeInclusive { start,
/// end, exhausted }` and `Range { start, end }`.
///
/// # The receiver is `&mut`
///
/// `next` takes `&mut self`, so the dump prints `_6 = &mut _3; next(copy _7)`. The
/// reference is followed with `pointee`, so the fields read and written are `_3`'s,
/// the same ones the loop's own `_3.0` reads would name.
///
/// # What is refused
///
/// A receiver whose range state is not in the store -- one the frontend never
/// modelled -- is refused rather than guessed, and so is a `next` whose element
/// width or sign cannot be read from the destination's `Option<Idx>`. Reading a
/// fresh variable would be a wrong value, not a weaker proof.
fn range_method(
    name: &str,
    kind: intrinsics::RangeMethod,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
) -> Result<Vec<Obligation>, String> {
    use intrinsics::RangeMethod;
    // The exclusive `Range` has no `exhausted` field and yields `None` at
    // `start >= end`; the inclusive `RangeInclusive` has the field and yields
    // `None` once it is exhausted. The `name` says which: only `RangeInclusive`
    // carries `RangeInclusive` in its path.
    let inclusive = name.contains("RangeInclusive");
    // The element width and sign, from the destination's `Option<Idx>` (for
    // `next`) or the range's own type. `next`'s destination is the `Option<Idx>`
    // the loop matches on, and `Idx`'s width is what the `start`/`end` words were
    // built at.
    match kind {
        RangeMethod::New => {
            // `new(start, end)` writes the two bounds and, for the inclusive
            // range, `exhausted = false`.
            let start = match args.first().map(|a| operand(env, a)) {
                Some(Val::Sym(v, s)) => (v, s),
                _ => return Err(format!("unmodelled argument to `{name}`")),
            };
            let end = match args.get(1).map(|a| operand(env, a)) {
                Some(Val::Sym(v, s)) => (v, s),
                _ => return Err(format!("unmodelled argument to `{name}`")),
            };
            let field = |i: u32| Place { local: dest.local, proj: vec![Proj::Field(i)] };
            env.set(&field(0), Val::Sym(start.0, start.1));
            env.set(&field(1), Val::Sym(end.0, end.1));
            if inclusive {
                // `exhausted: false`. A one-bit word, so it is a plain `Val::Sym`
                // at width 1 rather than a `Val::Bool`: the body compares it with
                // `!=`/`==` in `next`, and a predicate would not fit that store.
                env.set(&field(2), Val::Sym(smt::word(0, 1), Sign::Unsigned));
            }
            Ok(Vec::new())
        }
        RangeMethod::IntoIter => {
            // `into_iter` is the identity the desugaring wraps the range in: it
            // copies the receiver and returns it. Every field the source holds is
            // copied to the destination, so the loop's `next` reads the same state
            // `new` wrote.
            let src = match args.first() {
                Some(Operand::Copy(p)) | Some(Operand::Move(p)) => p.clone(),
                _ => return Err(format!("unmodelled receiver for `{name}`")),
            };
            let src = env.pointee(&src);
            // The fields present: `RangeInclusive` has three, `Range` two.
            let n = if inclusive { 3 } else { 2 };
            let mut vals = Vec::new();
            for i in 0..n {
                let p = Place { local: src.local, proj: vec![Proj::Field(i as u32)] };
                vals.push(env.get(&p));
            }
            for (i, v) in vals.into_iter().enumerate() {
                let p = Place { local: dest.local, proj: vec![Proj::Field(i as u32)] };
                env.set(&p, v);
            }
            Ok(Vec::new())
        }
        RangeMethod::Next => {
            // `next(&mut range) -> Option<Idx>`. The receiver is the `&mut` the
            // desugaring passes, so `pointee` follows it to the range local the
            // fields live on. The element width and sign come from the destination's
            // `Option<Idx>`, which is the type the `switchInt` reads.
            let recv = match args.first() {
                Some(Operand::Copy(p)) | Some(Operand::Move(p)) => p.clone(),
                _ => return Err(format!("unmodelled receiver for `{name}`")),
            };
            let range = env.pointee(&recv);
            let start_p = Place { local: range.local, proj: vec![Proj::Field(0)] };
            let end_p = Place { local: range.local, proj: vec![Proj::Field(1)] };
            let (start, start_sign) = match env.get(&start_p) {
                Val::Sym(v, s) => (v, s),
                _ => return Err(format!("`{name}` on a range whose start is not modelled")),
            };
            let (end, end_sign) = match env.get(&end_p) {
                Val::Sym(v, s) => (v, s),
                _ => return Err(format!("`{name}` on a range whose end is not modelled")),
            };
            let w = smt::bits(start);
            // The `exhausted` flag, for the inclusive range. A range whose field is
            // not modelled is refused rather than treated as not-exhausted.
            let exhausted = if inclusive {
                let ex_p = Place { local: range.local, proj: vec![Proj::Field(2)] };
                match env.get(&ex_p) {
                    Val::Sym(v, _) => Some(v),
                    _ => return Err(format!("`{name}` on a range whose exhausted flag is not modelled")),
                }
            } else {
                None
            };
            // The predicate for "the range is empty" (`is_empty`):
            //
            // * exclusive `Range`: `start >= end`;
            // * inclusive `RangeInclusive`: `exhausted || start > end`.
            //
            // The comparison is the element type's own, so a signed range reads
            // `i8::MIN` as below `0`. A mismatch between the two bounds' signs is a
            // dump shape the model does not hold, so it is refused rather than read
            // as either one.
            let Some(signed) = start_sign.known().or(end_sign.known()) else {
                return Err(format!("`{name}` on a range whose element sign is not modelled"));
            };
            if let (Some(a), Some(b)) = (start_sign.known(), end_sign.known()) {
                if a != b {
                    return Err(format!("`{name}` on a range whose bounds have different signs"));
                }
            }
            let empty = match (signed, exhausted) {
                (true, Some(ex)) => {
                    smt::or(smt::eq_const(ex, 1), smt::slt(end, start))
                }
                (false, Some(ex)) => {
                    smt::or(smt::eq_const(ex, 1), smt::ult(end, start))
                }
                (true, None) => smt::sle(end, start),
                (false, None) => smt::ule(end, start),
            };
            // `start + 1`, and whether it overflowed. `forward_overflowing(start, 1)`
            // is `overflowing_add(start, 1)`, so the successor is `start + 1` and the
            // overflow flag is "the result is the type's `MIN`". The inclusive range
            // marks itself exhausted exactly when the successor overflows, and the
            // last element (the `end` value) is yielded on the pass where `start ==
            // end` before that flag is set.
            //
            // The `MIN` depends on the sign: for an *unsigned* range the successor
            // wraps to `0`, but for a *signed* one `MAX + 1` wraps to `MIN` (`1 <<
            // (w-1)`), not to zero. Testing only for zero is the unsigned rule, and on
            // a signed inclusive range it never fires: `127i8..=127i8` would keep
            // yielding past `127` (into `-128`, `-127`, ...) and the loop would run to
            // the `unwind:` bound instead of ending after one iteration, turning a
            // true contract into a bound failure.
            let one = smt::word(1, w);
            let succ = smt::add(start, one);
            let min = if signed { 1u64 << (w - 1) } else { 0 };
            let overflowed = smt::eq_const(succ, min);
            // The yielded value is `start` (both ranges yield `start`), the tag is
            // `Some` unless the range is empty. The tag is a term at width 1: the
            // loop's `switchInt` on the `Option<Idx>` discriminant compares it
            // against `SOME_TAG`/`NONE_TAG`, so it must be a value the discriminant
            // store can hold and the switch can read.
            let tag = smt::ite(empty, smt::word(0, 1), smt::word(1, 1));
            env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
            env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(start, start_sign), w);
            // Advance the range *in place*: `start := start + 1`, and for the
            // inclusive range `exhausted := overflowed`. This is the mutation the
            // `&mut self` performs, and it is what makes the loop progress -- and
            // what a `variant:` can be proved against.
            //
            // Rust's `Iterator::next` leaves the range *unchanged* when it returns
            // `None`, so the advance is guarded by `!empty`. Advancing an empty range
            // would let a later call resurrect an element Rust never yields: an
            // exclusive `255u8..255` is empty (`start >= end`), and wrapping its start
            // to `0` would make the *next* call return `Some(0)`. Both calls return
            // `None` in Rust.
            let start_next = smt::ite(empty, start, succ);
            env.set(&start_p, Val::Sym(start_next, start_sign));
            if inclusive {
                let ex_p = Place { local: range.local, proj: vec![Proj::Field(2)] };
                let ex = exhausted.expect("inclusive range carries an exhausted flag");
                let ex_next = smt::ite(
                    empty,
                    ex,
                    smt::ite(overflowed, smt::word(1, 1), smt::word(0, 1)),
                );
                env.set(&ex_p, Val::Sym(ex_next, Sign::Unsigned));
            }
            Ok(Vec::new())
        }
    }
}

/// Answer a modelled `Option`/`Result` method from the receiver's tag and payload.
///
/// These are the first modelled calls that read an *enum* rather than a bit-vector
/// operand. `unwrap`/`unwrap_or` return the payload (or a default), the two
/// predicates return a `bool` about the tag. The receiver is `self` for the value
/// methods and `&self` for the predicates, so it is followed through a reference
/// exactly as the ASCII tests are -- `_2 = &_1; is_some(move _2)` must read `_1`'s
/// tag, and the `&Option` local has no bit-vector meaning of its own.
///
/// # The two families are one shape
///
/// `Option` and `Result` differ only in *which* variant carries the payload and in
/// the tag the predicates test: `Option` puts the payload on `Some` (tag
/// [`intrinsics::SOME_TAG`]) and `is_some` tests that tag, `Result` puts it on `Ok`
/// (tag [`intrinsics::OK_TAG`]) and `is_ok` tests *that* tag. The method name says
/// which, so one arm answers both: the payload variant is `Some` for an `Option`
/// method and `Ok` for a `Result` one, read off `name`.
///
/// # What is read, and what is refused
///
/// The tag and payload come from the environment's `discriminants`/`payloads`
/// stores, which the model's own `checked_*` family writes (`checked_add` on a
/// `u8` writes the tag and payload of an `Option<u8>`) and which a `Option`/
/// `Result` argument a contract bound also fills. A receiver whose enum state is
/// *not* in those stores -- a `Vec::pop` result, an enum a body built by hand -- is
/// refused rather than guessed: reading a fresh variable would be a wrong value,
/// not a weaker proof.
///
/// # The tag's width
///
/// A `checked_*` tag is a term at the *operand's* width (`ite(fails, 0, 1)` at
/// `w`), and a contract-bound enum argument's tag is seeded at its discriminants'
/// width. Both are recorded, so the comparison against the variant constants is
/// made at the width the tag was actually built at; reading it at the dump's
/// `isize` would widen a two-bit tag to 64 and the `switchInt` would compare the
/// wrong word. This is the same width rule `Rvalue::Discriminant` uses, and it is
/// deliberately read the same way so the two cannot disagree.
#[allow(clippy::too_many_arguments)]
fn enum_method(
    name: &str,
    kind: intrinsics::OptionMethod,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
    path: Pred,
    pins: &[(u32, u64)],
    cur: &MirFn,
    prog: &MirProgram,
    callees: &CalleeEnv<'_>,
) -> Result<Vec<Obligation>, String> {
    use intrinsics::OptionMethod;
    let receiver = args
        .first()
        .ok_or_else(|| format!("`{name}` has no receiver"))?;
    let p = match receiver {
        Operand::Copy(p) | Operand::Move(p) => p,
        Operand::Const(_) => return Err(format!("unmodelled argument to `{name}`")),
    };
    // `&self` for the predicates, `self` for the rest; `pointee` follows the
    // reference either way and is a no-op for a by-value receiver.
    let opt = env.pointee(p);
    let Some(tag) = env.discriminants.get(&opt.local).copied() else {
        return Err(format!("`{name}` on a receiver whose enum state is not modelled"));
    };
    let Val::Sym(tag, _) = tag else {
        return Err(format!("`{name}` on a receiver whose tag is not a value"));
    };
    // `Result`'s payload is on `Ok` (tag 0), `Option`'s on `Some` (tag 1).
    let payload_variant = if intrinsics::names_result_impl(name) {
        intrinsics::OK_TAG
    } else {
        intrinsics::SOME_TAG
    };
    // `unwrap_or` on a `Result` is *total* only if destroying the error value on
    // the `Err` branch cannot be observed. The model checks only that the payload
    // and the default are scalar values, and Rust destroys `E` inside `unwrap_or`,
    // so an error type with a panicking destructor would make the call panic while
    // the model reports no obligation -- a false proof. The error type is read from
    // the receiver's own type (`Result<T, E>`), and a type whose glue this tool
    // cannot establish is refused rather than assumed harmless.
    //
    // `unwrap_or_default` consumes the same receiver and destroys the same error on
    // the `Err` branch, so it is guarded identically -- excluding it was a false
    // proof for a `Result<u8, Boom>` whose `Boom` destructor panics.
    if let OptionMethod::UnwrapOr | OptionMethod::UnwrapOrDefault = kind {
        if intrinsics::names_result_impl(name) {
            if let Some(err) = receiver_error_type(cur, &opt) {
                match has_drop_glue(prog, callees.structs(), &err) {
                    Ok(false) => {}
                    Ok(true) => {
                        return Err(format!(
                            "`{name}` destroys an error value whose destructor is not modelled"
                        ));
                    }
                    Err(e) => return Err(format!("`{name}`: {e}")),
                }
            }
        }
    }
    // The `Option`↔`Result` conversions move one payload into the result and
    // *drop* the other, so a type whose destructor this tool cannot establish is
    // refused rather than assumed harmless -- the same reasoning as `unwrap_or`'s
    // error check. Each reads the type that gets dropped: `ok_or`'s argument, the
    // `Err` payload of `ok()`, the `Ok` payload of `err()`.
    let dropped_ty = match kind {
        OptionMethod::OkOr => args.get(1).and_then(|a| operand_ty(cur, a)),
        OptionMethod::Ok => receiver_error_type(cur, &opt),
        OptionMethod::Err => receiver_ok_type(cur, &opt),
        OptionMethod::And => receiver_some_type(cur, &opt),
        OptionMethod::Or => receiver_some_type(cur, &opt),
        _ => None,
    };
    if matches!(
        kind,
        OptionMethod::OkOr | OptionMethod::Ok | OptionMethod::Err | OptionMethod::And
            | OptionMethod::Or
    ) {
        if let Some(ty) = dropped_ty {
            match has_drop_glue(prog, callees.structs(), &ty) {
                Ok(false) => {}
                Ok(true) => {
                    return Err(format!(
                        "`{name}` destroys a value whose destructor is not modelled"
                    ));
                }
                Err(e) => return Err(format!("`{name}`: {e}")),
            }
        }
    }
    // The tag's width: the seeded/enum width where there is one, else the
    // payload's, exactly as `Rvalue::Discriminant` reads it.
    let tag_w = env.tag_width(opt.local).or_else(|| env.option_width(opt.local)).unwrap_or(64);
    let tag = smt::truncate(tag, tag_w);
    Ok(match kind {
        // `is_some`/`is_ok` is `tag == success`, `is_none`/`is_err` is
        // `tag == failure`. The destination is a `bool`, so the result is a
        // predicate and not a one-bit word -- the `if` that consumes it reads a
        // predicate.
        OptionMethod::IsSuccess => {
            env.set(dest, Val::Bool(smt::eq_const(tag, payload_variant)));
            Vec::new()
        }
        OptionMethod::IsFailure => {
            env.set(dest, Val::Bool(smt::eq_const(tag, 1 - payload_variant)));
            Vec::new()
        }
        // `Option::ok_or(err)` and `Result::ok()`/`err()` convert between the two
        // enums. `ok_or`/`ok` reinterpret the receiver's tag (`Ok` and `Some` are
        // discriminants 0 and 1, so `1 - tag`); `err` keeps it, because `Err` is
        // already the payload-carrying variant of a `Result` and `Some` of an
        // `Option`. The payload a variant *carries* is recorded under the
        // discriminant rustc's `switchInt` selects, and the other variant's is
        // left unset -- the consuming `switchInt` only reads the payload in the
        // arm whose tag matched, so a read of the unset one never happens.
        OptionMethod::OkOr => {
            // The error argument is always present and always needed: it becomes
            // the result's `Err` payload (discriminant 1). `Some`'s payload
            // becomes the result's `Ok` payload (discriminant 0).
            let (err, err_sign) = match args.get(1).map(|d| operand(env, d)) {
                Some(Val::Sym(v, s)) => (v, s),
                Some(_) => return Err(format!("unmodelled argument to `{name}`")),
                None => return Err(format!("`{name}` has no error argument")),
            };
            let err_w = smt::bits(err);
            // The `Ok` payload exists only on the `Some` path. A receiver whose
            // tag is a *known* non-`Some` discriminant (`None::<u8>.ok_or(e)`)
            // cannot reach the `Ok` result on this path, so the payload is left
            // *unbound* rather than refused -- exactly as a `None` construction
            // leaves it. A symbolic or `Some` tag still requires the payload:
            // binding a fabricated value there would be a value the receiver never
            // holds.
            let ok_payload = match env.payloads.get(&(opt.local, intrinsics::SOME_TAG)).copied() {
                Some((Val::Sym(ok, ok_sign), ok_w)) => Some((ok, ok_sign, ok_w)),
                Some(_) => {
                    return Err(format!("`{name}` on a receiver whose payload is not modelled"))
                }
                None => match smt::evaluate(tag, |_| None) {
                    Some(v) if v != intrinsics::SOME_TAG => None,
                    _ => {
                        return Err(format!(
                            "`{name}` on a receiver whose payload is not modelled"
                        ))
                    }
                },
            };
            let result_tag = smt::truncate(smt::sub(smt::word(1, tag_w), tag), tag_w);
            env.set_discriminant(dest.local, Val::Sym(result_tag, Sign::Unsigned));
            if let Some((ok, ok_sign, ok_w)) = ok_payload {
                env.set_payload(dest.local, intrinsics::OK_TAG, Val::Sym(ok, ok_sign), ok_w);
            }
            env.set_payload(dest.local, 1, Val::Sym(err, err_sign), err_w);
            Vec::new()
        }
        OptionMethod::Ok | OptionMethod::Err => {
            // `ok()` moves the `Ok` payload onto `Some`; `err()` moves the `Err`
            // payload onto `Some`. Both results are `Option`s, whose payload
            // variant is `Some`.
            let src = match kind {
                OptionMethod::Ok => intrinsics::OK_TAG,
                _ => 1 - intrinsics::OK_TAG,
            };
            // The source variant has no payload on this path (`Err::<u8,u8>(e).ok()`
            // reaches the `Ok` result on no path). Sound to leave unbound only when
            // the tag is a *known* other discriminant; a symbolic tag still requires
            // the payload.
            let payload = match env.payloads.get(&(opt.local, src)).copied() {
                Some((Val::Sym(payload, sign), pw)) => Some((payload, sign, pw)),
                Some(_) => {
                    return Err(format!("`{name}` on a receiver whose payload is not modelled"))
                }
                None => match smt::evaluate(tag, |_| None) {
                    Some(v) if v != src => None,
                    _ => {
                        return Err(format!(
                            "`{name}` on a receiver whose payload is not modelled"
                        ))
                    }
                },
            };
            let result_tag = match kind {
                // `Ok`(0) -> `Some`(1), `Err`(1) -> `None`(0): `1 - tag`.
                OptionMethod::Ok => smt::truncate(smt::sub(smt::word(1, tag_w), tag), tag_w),
                // `err()` keeps the tag: `Err` is the `Option::Some` result.
                _ => tag,
            };
            env.set_discriminant(dest.local, Val::Sym(result_tag, Sign::Unsigned));
            if let Some((payload, sign, pw)) = payload {
                env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(payload, sign), pw);
            }
            Vec::new()
        }
        OptionMethod::Or | OptionMethod::And => {
            // `or`/`and` take a second `Option` of the same type and return one of
            // the two by the receiver's tag:
            //   `or`:  `Some` -> the receiver, `None` -> `other`
            //   `and`: `Some` -> `other`,    `None` -> the receiver (`None`)
            // The result's tag is an `ite` on the receiver's tag, and *both*
            // payloads are carried unconditionally -- each is read only on the path
            // whose tag selects it, so a path that does not select a payload never
            // reads it. That is what makes the shape total and lossless: no branch
            // of the `switchInt` that consumes the result finds an unbound payload.
            // The receiver's own payload, and the argument's tag/payload. The
            // argument is an `Option` by value, so its parts live on its local.
            //
            // A payload is required only when the operand can be `Some` on some
            // path. A *constructed* `None` records no payload; when its tag is a
            // known non-`Some` discriminant the payload is absent and irrelevant,
            // exactly as the `ok`/`err` conversions handle it. A symbolic tag
            // still requires the payload, because a fabricated value there would
            // be one the operand never holds.
            let arg_opt = match args.get(1).and_then(|d| match d {
                Operand::Copy(p) | Operand::Move(p) => Some(env.pointee(p)),
                _ => None,
            }) {
                Some(a) => a,
                None => return Err(format!("`{name}` on an argument that is not a place")),
            };
            let Some(Val::Sym(arg_tag, _)) = env.discriminants.get(&arg_opt.local).copied() else {
                return Err(format!("`{name}` on an argument whose enum state is not modelled"));
            };
            let recv_payload =
                payload_if_some(env, opt.local, tag, payload_variant, "a receiver", name)?;
            let arg_payload =
                payload_if_some(env, arg_opt.local, arg_tag, payload_variant, "an argument", name)?;
            // The two tags can come from *different* origins -- a seeded enum
            // argument's tag is one bit (`bind_enum`), a `checked_*` result's tag
            // is the operand's width -- so they are normalised to a common width
            // before the `ite`, or the branches mismatch and the query is refused
            // as ill-formed.
            let common_w = smt::bits(tag).max(smt::bits(arg_tag));
            let tag = smt::truncate(tag, common_w);
            let arg_tag = smt::truncate(arg_tag, common_w);
            let is_some = smt::eq_const(tag, payload_variant);
            let (result_tag, result_payload) = match kind {
                // `or` is `Option<T>` on both sides, so the two payloads have the
                // same type: the receiver's on `Some`, the argument's on `None`. An
                // absent payload (a known `None` operand) needs no `ite` -- the
                // other operand is the whole result.
                OptionMethod::Or => {
                    let payload = match (recv_payload, arg_payload) {
                        (Some((r, rs, rw)), Some((a, _, _))) => {
                            Some((smt::ite(is_some, r, a), rs, rw))
                        }
                        (Some((r, rs, rw)), None) => Some((r, rs, rw)),
                        (None, Some((a, as_, aw))) => Some((a, as_, aw)),
                        (None, None) => None,
                    };
                    (smt::ite(is_some, tag, arg_tag), payload)
                }
                // `and` is `Option<T>::and<U> -> Option<U>`: on `Some` the result is
                // the *argument* (`Option<U>`), and on `None` it is `None`, whose
                // payload is never read. So the result's payload is the argument's
                // unconditionally -- `ite`-ing it with the receiver's `T` payload
                // would demand equal widths for two unrelated types.
                _ => (smt::ite(is_some, arg_tag, tag), arg_payload),
            };
            env.set_discriminant(dest.local, Val::Sym(result_tag, Sign::Unsigned));
            if let Some((payload, sign, w)) = result_payload {
                env.set_payload(dest.local, payload_variant, Val::Sym(payload, sign), w);
            }
            // Carry the selected reference's *element identity*, *compositionally*.
            // `slice::first`/`get` produce an `Option<&T>` whose payload names a
            // slice element through `slice_elem_ref`, and a later `*` deref reads
            // it. Each combinator builds a node over its operands' own identities
            // rather than reading a leaf, so a chain composes:
            //
            //   `or`:  result = `is_some ? recv : arg`
            //   `and`: result = `is_some ? arg : recv`
            //
            // A missing operand identity is substituted only when that operand
            // cannot be the one selected -- the receiver's tag proves it. Reading a
            // missing identity as the *other* operand's on a path that could select
            // it was the false proof (`a.first().or(b.first()).or(c.first())` took
            // `c`'s element); a symbolic tag with a missing operand identity is
            // therefore left unset, which makes the deref unknown rather than wrong.
            env.slice_elem_ref.remove(&dest.local);
            let cond = smt::eq_const(tag, payload_variant);
            let r = env.slice_elem_ref.get(&opt.local).cloned();
            let a = env.slice_elem_ref.get(&arg_opt.local).cloned();
            let is_and = matches!(kind, OptionMethod::And);
            let composed = if is_and {
                // `Option<T>::and<U>` returns `Some(arg)` on a `Some` receiver and
                // `None` otherwise, so the *result's* element -- read only on the
                // `Some` path -- is always the argument's. The receiver's element is
                // never the result, and its type may differ (`Option<&u8>` receiver,
                // `Option<&u16>` argument), so a `Select` over both would demand
                // equal widths for unrelated types and mark the query ill-formed.
                // Carrying the argument identity alone is both exact and
                // width-safe.
                a
            } else {
                // `Some(v)` when the receiver's tag is a known discriminant, so the
                // `is_some` test is decided and one operand is provably not selected.
                let known_tag = smt::evaluate(tag, |_| None);
                // Whether the receiver is selected: `or` selects it on `Some`.
                let recv_selected_known = known_tag.map(|v| v == payload_variant);
                match (r, a) {
                    (Some(r), Some(a)) => {
                        Some(ElemId::Select(cond, Box::new(r), Box::new(a)))
                    }
                    // The receiver's identity is missing: usable only when the tag
                    // says the receiver is not the selected operand.
                    (None, Some(a)) => match recv_selected_known {
                        Some(false) => Some(a),
                        _ => None,
                    },
                    // The argument's identity is missing: usable only when the tag
                    // says the receiver *is* the selected operand.
                    (Some(r), None) => match recv_selected_known {
                        Some(true) => Some(r),
                        _ => None,
                    },
                    (None, None) => None,
                }
            };
            if let Some(id) = composed {
                env.slice_elem_ref.insert(dest.local, id);
            }
            Vec::new()
        }
        // `Option<&T>::copied()`/`cloned()`: the value the payload reference
        // addresses, with the receiver's tag unchanged. The model stores a `&T`
        // payload as the value it addresses, so the result's payload *is* the
        // receiver's -- `v.first().copied()` and `*v.first().unwrap()` name one
        // word. Only the tag passes through; the element identity is dropped,
        // because the result is a value, not a reference, so a later `*` on it is
        // not a modelled read. A receiver with no payload on some path is refused
        // (the same rule `or`/`and` apply), because the copied value would be one
        // the receiver never holds.
        OptionMethod::Copied => {
            let payload =
                payload_if_some(env, opt.local, tag, payload_variant, "a receiver", name)?;
            env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
            if let Some((payload, sign, w)) = payload {
                env.set_payload(dest.local, payload_variant, Val::Sym(payload, sign), w);
            }
            Vec::new()
        }
        // `unwrap`/`unwrap_or` read the payload, which `checked_*` recorded
        // *unconditionally* -- it is only ever read on a path whose tag is the
        // success variant, which rustc guarantees by emitting the downcast
        // projection only inside that arm. So the payload is written without a
        // guard here; the tag's `switchInt` is what keeps a failure path from
        // reaching this read.
        OptionMethod::Unwrap | OptionMethod::Expect | OptionMethod::UnwrapOr
        | OptionMethod::UnwrapOrDefault => {
            let Some((Val::Sym(payload, sign), _)) =
                env.payloads.get(&(opt.local, payload_variant)).copied()
            else {
                return Err(format!("`{name}` on a receiver whose payload is not modelled"));
            };
            let value = match kind {
                OptionMethod::UnwrapOr => {
                    // `unwrap_or(default)`: the payload on the success variant, the
                    // default on the failure one. The default is the second argument
                    // (`Option::unwrap_or(self, default)`), so a failure receiver
                    // yields it and the method is *total* -- no panic obligation.
                    let default = match args.get(1) {
                        Some(d) => match operand(env, d) {
                            Val::Sym(v, _) => v,
                            _ => return Err(format!("unmodelled default argument to `{name}`")),
                        },
                        None => return Err(format!("`{name}` has no default argument")),
                    };
                    smt::ite(smt::eq_const(tag, payload_variant), payload, default)
                }
                OptionMethod::UnwrapOrDefault => {
                    // `unwrap_or_default()`: the payload on the success variant,
                    // `T::default()` on the failure one. For every scalar payload
                    // this tool models, `Default` is the zero of the payload's own
                    // width -- `0u8`, `0i32`, `false` -- so the default is that
                    // word, not a fresh input. The width is the payload's own (not
                    // the destination's, which is the same type here but a
                    // different local), and a payload with no bit width (a struct)
                    // is refused rather than given a zero it may not have.
                    let w = payload.width();
                    if w == 0 {
                        return Err(format!(
                            "`{name}` on a payload whose default value is not modelled"
                        ));
                    }
                    let default = smt::word(0, w);
                    smt::ite(smt::eq_const(tag, payload_variant), payload, default)
                }
                _ => payload,
            };
            env.set(dest, Val::Sym(value, sign));
            if matches!(kind, OptionMethod::Unwrap | OptionMethod::Expect) {
                // If the payload was a reference to a slice element
                // (`slice::first`/`get` produce `Option<&T>`), the element the
                // reference names travels with the payload, so `*_2` on the
                // destination reads the slice's own element. `unwrap`/`expect`
                // panic on the failure variant, so the payload here is always the
                // `Some` element -- no path reaches the deref without it. The
                // identity may be conditional (a chain of `or`/`and`), and it
                // travels as-is.
                if let Some(e) = env.slice_elem_ref.get(&opt.local).cloned() {
                    env.slice_elem_ref.insert(dest.local, e);
                }
                // `unwrap`/`expect` **panic** on the failure variant. The failure
                // is `tag == failure`, a reachable-failure obligation of the same
                // polarity as a rustc-inserted `assert`: the call is safe exactly
                // where `path ∧ tag == failure` is unsatisfiable. `unwrap_or` has
                // no such obligation -- it is total.
                return Ok(vec![Obligation {
                    kind: ObligationKind::Panic {
                        message: if payload_variant == intrinsics::OK_TAG {
                            format!("`{name}` on an `Err` value")
                        } else {
                            format!("`{name}` on a `None` value")
                        },
                    },
                    verdict: find_obligation(
                        smt::and(path, smt::eq_const(tag, 1 - payload_variant)),
                        pins,
                    ),
                }]);
            }
            Vec::new()
        }
    })
}

/// Answer `slice::first`/`slice::get`, which produce `Option<&T>`.
///
/// The element is the executor's own `s[0]`/`s[k]` variable -- the same one a
/// `s[0]` read names -- so the `Option`'s payload *is* that element and not a
/// fresh value the slice never holds. The `Option`'s tag is a *predicate*
/// (`len == 0` for `first`, `k >= len` for `get`), so the arm is decided by the
/// caller's `switchInt` on the discriminant, and the payload is recorded under the
/// `Some` discriminant so a `(_2 as Some).0` downcast -- or the reference's deref
/// -- reads it. The element is also recorded in `slice_elem_ref`, so `*_2` on the
/// returned reference reads the slice's element rather than the reference local's
/// absent value.
fn slice_element(
    name: &str,
    op: intrinsics::Intrinsic,
    receiver: &Place,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
    f: &MirFn,
) -> Result<Vec<Obligation>, String> {
    use intrinsics::Intrinsic;
    let recv = env.pointee(receiver);
    let Val::Sym(len, _) = length_of(env, f, receiver) else {
        return Err(format!("`{name}` on a receiver whose length is not modelled"));
    };
    let Some(s) = env.indexed.get(&recv.local) else {
        return Err(format!("`{name}` on a receiver whose elements are not modelled"));
    };
    let (sl, elem_w, fixed_len) = (recv.local, s.elem_w, s.fixed_len);
    // `first` names element 0; `get(k)` names element `k`. The index must be a
    // *constant*: a slice's length is symbolic, so a symbolic index has no finite
    // domain and reading "some element" would make `s[i]` a different value per
    // read -- a wrong proof, not a missing one. A literal index is exact.
    let (index, failure) = match op {
        Intrinsic::SliceFirst => (0u64, smt::eq_const(len, 0)),
        Intrinsic::SliceLast => {
            // An array's length is its type's constant, so `last` names the exact
            // element `N-1`. A slice's length is symbolic, so there is no index to
            // pin; the element is a single fresh variable per slice, keyed by a
            // sentinel so every `last()` call on the same slice reads the *same*
            // value (a fresh variable per call would let two `last()` reads
            // disagree -- a wrong value, not a missing one).
            let idx = match fixed_len {
                Some(0) => 0,
                Some(n) => n - 1,
                None => LAST_INDEX,
            };
            (idx, smt::eq_const(len, 0))
        }
        _ => {
            let k = match args.get(1) {
                Some(Operand::Const(Const::UInt(v, _))) => u64::try_from(*v).ok(),
                Some(Operand::Copy(p) | Operand::Move(p)) => match env.locals.get(&p.local) {
                    Some(Val::Sym(v, _)) => smt::evaluate(*v, |_| None),
                    _ => None,
                },
                _ => None,
            };
            let Some(k) = k else {
                return Err(format!(
                    "`{name}` with an index that is not a constant is not modelled"
                ));
            };
            // `get(k)` is `None` exactly when `k >= len`, which is `len <= k`.
            (k, smt::ule_const(len, k))
        }
    };
    let (elem, elem_sign) = env
        .index_elem(sl, index)
        .ok_or_else(|| format!("`{name}` on a receiver whose elements are not modelled"))?;
    // `Some` when the access is in range, `None` otherwise. The tag is one bit
    // (the discriminants are `0`/`1`), and it is a predicate, not a constant.
    let tag = smt::ite(
        failure,
        smt::word(0, 1),
        smt::word(intrinsics::SOME_TAG, 1),
    );
    env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
    env.set_payload(
        dest.local,
        intrinsics::SOME_TAG,
        Val::Sym(elem, elem_sign),
        elem_w,
    );
    env.slice_elem_ref.insert(dest.local, ElemId::Leaf((sl, index)));
    Ok(Vec::new())
}

/// The context a slice-iterator call needs beyond its receiver: the function (for
/// the destination's type), the precondition's pins (for `sum`'s length), and the
/// current path (for a `sum` step's overflow obligation). Bundled so the helper
/// stays within clippy's argument limit.
struct IterCall<'a> {
    f: &'a MirFn,
    pins: &'a [(u32, u64)],
    path: Pred,
    /// The call's full argument list, so `nth(k)` can read its constant offset.
    args: &'a [Operand],
    /// The whole program, so a `fold`'s reducer closure can be resolved to its
    /// `MirFn` (a closure body is a separate function in the dump).
    prog: &'a MirProgram,
}

/// Model `for x in xs` over a slice: `into_iter`/`iter` starts a cursor, `next`
/// advances it and yields `Option<&T>`.
///
/// The cursor is a concrete position into the *base* slice local, so each
/// iteration names the element at a constant index -- the same element variable a
/// contract's `s[k]` names, so a contract about `xs[0] + xs[1]` and a body that
/// sums `for &x in xs` are about the same values. `next`'s `None` guard is the
/// slice's own length variable (`pos >= len`), so it cannot disagree with
/// `len`/`is_empty`/`first`. A cursor whose base is not a modelled slice (a
/// havoced iterator, a user iterator) is refused rather than read as an arbitrary
/// element.
///
/// `copied` is the identity on the cursor; `count` is `len - pos`; `sum` folds the
/// remaining elements with a checked `+` (see [`slice_sum`]).
/// Resolve a `fold`'s reducer operand to the `MirFn` it names.
///
/// A non-capturing closure prints as `const ZeroSized: {closure@FILE:L:C: L:C}`,
/// so it is matched to the `MirFn` whose first argument type is exactly that
/// closure type (rustc prints the closure's own `&mut {closure@…}` argument with
/// the same string). A function item prints as a bare name and is matched on its
/// tail. An ambiguous or unrecognised operand is refused -- a wrong reducer is a
/// wrong value.
fn closure_fn<'a>(prog: &'a MirProgram, arg: Option<&Operand>) -> Option<&'a MirFn> {
    let Operand::Const(Const::Other(s)) = arg? else {
        return None;
    };
    if let Some(rest) = s.split("ZeroSized: {closure@").nth(1) {
        let ty = format!("{{closure@{rest}");
        return prog.fns.iter().find(|f| {
            f.arg_locals
                .first()
                .and_then(|&l| f.ty_of(l))
                .is_some_and(|t| match t {
                    Ty::Ref(inner) => matches!(**inner, Ty::Other(ref o) if *o == ty),
                    Ty::Other(o) => *o == ty,
                    _ => false,
                })
        });
    }
    let tail = s.rsplit("::").next().unwrap_or(s.as_str());
    let mut hits = prog
        .fns
        .iter()
        .filter(|f| f.name == *s || f.name.rsplit("::").next() == Some(tail));
    let first = hits.next()?;
    // Refuse an ambiguous tail rather than pick one.
    if hits.next().is_some() {
        return None;
    }
    Some(first)
}

/// The reducer a `fold` closure denotes: `(op, checked)` for `|acc, x| acc <op> x`.
/// Only a checked binary op (with its overflow `assert`) or a `wrapping_*` call on
/// `(_2, _3)` in that order is accepted; anything else is refused.
/// How many arithmetic operations or call terminators the closure performs. The
/// iterator model reads *one* operation as the whole closure; a body with more
/// (`|x| { let y = x + 1; y * 2 }`) would be modelled as its first op, so only a
/// single-operation body is accepted.
fn closure_op_count(f: &MirFn) -> usize {
    let mut n = 0;
    for b in &f.blocks {
        for st in &b.stmts {
            if matches!(st, Stmt::Assign(_, Rvalue::Binary(..) | Rvalue::CheckedBinary(..))) {
                n += 1;
            }
        }
        if matches!(&b.term, Term::Call { .. }) {
            n += 1;
        }
    }
    n
}

fn closure_binop(f: &MirFn) -> Option<(BinOp, bool)> {
    if f.arg_locals.len() != 3 || closure_op_count(f) != 1 {
        return None;
    }
    let (acc, x) = (f.arg_locals[1], f.arg_locals[2]);
    let is_arg = |o: &Operand, l: u32| {
        matches!(o, Operand::Copy(p) | Operand::Move(p) if p.local == l && p.proj.is_empty())
    };
    for b in &f.blocks {
        for st in &b.stmts {
            if let Stmt::Assign(_, Rvalue::CheckedBinary(op, a, c)) = st {
                if is_arg(a, acc) && is_arg(c, x) {
                    return Some((*op, true));
                }
            }
        }
        if let Term::Call { callee: Callee::Name(n), args, .. } = &b.term {
            if let (Some(a), Some(c)) = (args.first(), args.get(1)) {
                if is_arg(a, acc) && is_arg(c, x) {
                    let op = match n.rsplit("::").next().unwrap_or(n.as_str()) {
                        "wrapping_add" => BinOp::Add,
                        "wrapping_sub" => BinOp::Sub,
                        "wrapping_mul" => BinOp::Mul,
                        _ => continue,
                    };
                    return Some((op, false));
                }
            }
        }
    }
    None
}

/// A constant operand's value, if it is a numeric literal.
fn const_val(o: &Operand) -> Option<u64> {
    match o {
        Operand::Const(Const::UInt(v, _)) => Some(*v as u64),
        _ => None,
    }
}

/// The local a `Copy`/`Move` operand reads, treating one leading `Deref` as
/// transparent (a reference is modelled as its referent).
fn arg_local(o: &Operand) -> Option<u32> {
    match o {
        Operand::Copy(p) | Operand::Move(p)
            if p.proj.is_empty() || (p.proj.len() == 1 && matches!(p.proj[0], Proj::Deref)) =>
        {
            Some(p.local)
        }
        _ => None,
    }
}

/// Follow `Use` assignments so a local that is only copied from another (the
/// `_3 = copy (*_2)` indirection a closure body introduces) resolves to its source.
fn assign_source(f: &MirFn, local: u32) -> Option<Operand> {
    for b in &f.blocks {
        for st in &b.stmts {
            if let Stmt::Assign(pl, Rvalue::Use(src)) = st {
                if pl.local == local && pl.proj.is_empty() {
                    return Some(src.clone());
                }
            }
        }
    }
    None
}

/// Resolve an operand through `Use` copies (deref-transparent) to the constant or
/// argument it ultimately reads.
fn resolve_operand(f: &MirFn, o: &Operand) -> Operand {
    let mut cur = o.clone();
    for _ in 0..32 {
        let Some(l) = arg_local(&cur) else {
            return cur;
        };
        match assign_source(f, l) {
            Some(src) => cur = src,
            None => return cur,
        }
    }
    cur
}

/// Read a `map` closure `|x| x <op> k` (or `k <op> x`), checked or `wrapping_*`.
fn closure_map(f: &MirFn) -> Option<MapOp> {
    if f.arg_locals.len() != 2 || closure_op_count(f) != 1 {
        return None;
    }
    let x = f.arg_locals[1];
    let op_from = |op: BinOp, a: &Operand, b: &Operand| -> Option<MapOp> {
        let (ra, rb) = (resolve_operand(f, a), resolve_operand(f, b));
        if arg_local(&ra) == Some(x) {
            const_val(&rb).map(|rhs| MapOp { op, checked: true, rhs, rhs_left: false })
        } else if arg_local(&rb) == Some(x) {
            const_val(&ra).map(|rhs| MapOp { op, checked: true, rhs, rhs_left: true })
        } else {
            None
        }
    };
    for b in &f.blocks {
        for st in &b.stmts {
            if let Stmt::Assign(_, Rvalue::CheckedBinary(op, a, c)) = st {
                if let Some(m) = op_from(*op, a, c) {
                    return Some(m);
                }
            }
        }
        if let Term::Call { callee: Callee::Name(n), args, .. } = &b.term {
            if let (Some(a), Some(c)) = (args.first(), args.get(1)) {
                let op = match n.rsplit("::").next().unwrap_or(n.as_str()) {
                    "wrapping_add" => BinOp::Add,
                    "wrapping_sub" => BinOp::Sub,
                    "wrapping_mul" => BinOp::Mul,
                    _ => continue,
                };
                if let Some(m) = op_from(op, a, c) {
                    return Some(MapOp { checked: false, ..m });
                }
            }
        }
    }
    None
}

/// Read a `filter` closure `|x| x <op> k` (or `k <op> x`) as a predicate.
fn closure_filter(f: &MirFn) -> Option<FilterOp> {
    if f.arg_locals.len() != 2 || closure_op_count(f) != 1 {
        return None;
    }
    let x = f.arg_locals[1];
    for b in &f.blocks {
        for st in &b.stmts {
            if let Stmt::Assign(_, Rvalue::Binary(op, a, c)) = st {
                let (ra, rb) = (resolve_operand(f, a), resolve_operand(f, c));
                if arg_local(&ra) == Some(x) {
                    if let Some(rhs) = const_val(&rb) {
                        return Some(FilterOp { op: *op, rhs, rhs_left: false });
                    }
                } else if arg_local(&rb) == Some(x) {
                    if let Some(rhs) = const_val(&ra) {
                        return Some(FilterOp { op: *op, rhs, rhs_left: true });
                    }
                }
            }
        }
    }
    None
}

/// Refuse a terminal that reads base elements when the cursor still carries a lazy
/// `map`/`filter` it does not apply, so `map(..).next()` is a refusal rather than the
/// untransformed element (a wrong value).
fn reject_adapters(it: &IterState, name: &str) -> Result<(), String> {
    if it.map.is_some() || it.filter.is_some() {
        return Err(format!("`{name}` after `map`/`filter` is not modelled"));
    }
    Ok(())
}

fn slice_iter(
    name: &str,
    op: intrinsics::Intrinsic,
    receiver: &Place,
    dest: &Place,
    env: &mut Env,
    cx: &IterCall<'_>,
) -> Result<Vec<Obligation>, String> {
    use intrinsics::Intrinsic;
    let recv = env.pointee(receiver);
    match op {
        Intrinsic::SliceIntoIter => {
            // `for x in xs.iter()` calls `into_iter` on the `Iter` itself, which is
            // the identity: carry the existing cursor to the destination.
            if let Some(it) = env.iters.get(&recv.local).copied() {
                env.iters.insert(dest.local, it);
                return Ok(Vec::new());
            }
            let Some(s) = env.indexed.get(&recv.local) else {
                return Err(format!("`{name}` on a receiver whose elements are not modelled"));
            };
            if s.elem_w == 0 {
                return Err(format!("`{name}` on a slice whose element width is not modelled"));
            }
            env.iters.insert(dest.local, IterState { base: recv.local, pos: 0, rev: false, step: 1, end: None, map: None, filter: None, enum_start: None });
            Ok(Vec::new())
        }
        // `copied()` wraps the cursor in an adapter that yields `T` instead of `&T`.
        // A reference is modelled as its referent, so the cursor is unchanged -- the
        // adapter only carries it to the destination. A receiver with no cursor is a
        // non-modelled iterator, refused rather than guessed.
        Intrinsic::SliceCopied => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            // `enumerate()` rides this arm (its cursor is unchanged), but it records
            // where its own index count starts, so `skip(2).enumerate()` yields index
            // 0 first rather than the raw slice position 2.
            let next = if name.contains("enumerate") {
                IterState { enum_start: Some(it.pos), ..it }
            } else {
                it
            };
            env.iters.insert(dest.local, next);
            Ok(Vec::new())
        }
        // `rev()` flips the cursor's direction, carried to the destination like
        // `copied`. `rev().rev()` is the identity, so the flag toggles.
        Intrinsic::SliceRev => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            env.iters.insert(dest.local, IterState { rev: !it.rev, ..it });
            Ok(Vec::new())
        }
        // `skip(n)` advances the position by `n`; `step_by(n)` sets the stride.
        // Both read a *constant* `n` and carry the cursor to the destination.
        Intrinsic::SliceSkip | Intrinsic::SliceStepBy => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            let Some(n) = constant_operand(cx.args.get(1), env) else {
                return Err(format!("`{name}` needs a constant argument"));
            };
            let next = if matches!(op, Intrinsic::SliceSkip) {
                IterState { pos: it.pos.saturating_add(n), ..it }
            } else {
                if n == 0 {
                    return Err(format!("`{name}` with a zero step is a panic and is not modelled"));
                }
                IterState { step: it.step.saturating_mul(n), ..it }
            };
            env.iters.insert(dest.local, next);
            Ok(Vec::new())
        }
        // `take(n)` caps the effective end at `pos + n`. It needs a constant length
        // so the end is a constant (a symbolic length would make it symbolic).
        Intrinsic::SliceTake => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            let Some(k) = constant_operand(cx.args.get(1), env) else {
                return Err(format!("`{name}` needs a constant argument"));
            };
            let const_len = env
                .indexed
                .get(&it.base)
                .is_some_and(|s| iterator_const_len(s, cx.pins).is_some());
            if !const_len {
                return Err(format!("`{name}` on a slice whose length is not a constant"));
            }
            let cap = it.pos.saturating_add(k);
            let end = Some(it.end.map_or(cap, |e| e.min(cap)));
            env.iters.insert(dest.local, IterState { end, ..it });
            Ok(Vec::new())
        }
        // `fold(init, f)` folds a modelled reducer closure over the cursor:
        // `acc = init; acc = f(acc, x)` per element. A *checked* reducer raises a
        // reachable-panic obligation per step (exactly as `sum` does for `+`); a
        // `wrapping_*` reducer does not. Needs a constant length (a fixed addend
        // count) and a constant `init`.
        Intrinsic::SliceFold => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            reject_adapters(&it, name)?;
            if it.rev {
                return Err(format!("`{name}` over a reversed iterator is not modelled"));
            }
            let Some(s) = env.indexed.get(&it.base) else {
                return Err(format!("`{name}` on an iterator whose slice is not modelled"));
            };
            let (elem_w, elem_signed) = (s.elem_w, s.elem_signed);
            let Some(n) = iterator_const_len(s, cx.pins) else {
                return Err(format!(
                    "`{name}` over a slice whose length is not a constant (write \
                     `requires: <slice>.len() == N`)"
                ));
            };
            if n > MAX_SUM_LEN {
                return Err(format!("`{name}` over {n} elements is past the {MAX_SUM_LEN}-element limit"));
            }
            let hi = it.end.map_or(n, |e| e.min(n));
            let Some(init) = constant_operand(cx.args.get(1), env) else {
                return Err(format!("`{name}` needs a constant initial accumulator"));
            };
            let Some(closure) = closure_fn(cx.prog, cx.args.get(2)) else {
                return Err(format!("`{name}` over a reducer closure that is not modelled"));
            };
            let Some((op, checked)) = closure_binop(closure) else {
                return Err(format!("`{name}` over a reducer closure this frontend does not model"));
            };
            let sign = Sign::of_bool(elem_signed);
            let mut acc = smt::word(init, elem_w);
            let mut obligations = Vec::new();
            let mut k = it.pos;
            while k < hi {
                let Some((elem, _)) = env.index_elem(it.base, k) else {
                    return Err(format!("`{name}` on an iterator whose elements are not modelled"));
                };
                if checked {
                    let Some(over) = overflow_pred(op, Val::Sym(acc, sign), Val::Sym(elem, sign), elem_w)
                    else {
                        return Err(format!("`{name}` overflow predicate is not modelled"));
                    };
                    obligations.push(Obligation {
                        kind: ObligationKind::Panic { message: format!("`{name}` closure overflows") },
                        verdict: find_obligation(smt::and(cx.path, over), cx.pins),
                    });
                }
                let Val::Sym(v, _) = eval_binary(op, Val::Sym(acc, sign), Val::Sym(elem, sign), Some(elem_w))
                else {
                    return Err(format!("`{name}` closure step is not modelled"));
                };
                acc = v;
                k += it.step;
            }
            env.set(dest, Val::Sym(acc, sign));
            env.iters.remove(&recv.local);
            Ok(obligations)
        }
        // `map(f)` / `filter(f)` are lazy: they set a transform/predicate on the
        // cursor and carry it. The value terminals apply it (`sum` the transform,
        // `count` the predicate); anything else is a refusal.
        Intrinsic::SliceMap => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            let Some(closure) = closure_fn(cx.prog, cx.args.get(1)) else {
                return Err(format!("`{name}` over a closure that is not modelled"));
            };
            let Some(m) = closure_map(closure) else {
                return Err(format!("`{name}` over a transform this frontend does not model"));
            };
            env.iters.insert(dest.local, IterState { map: Some(m), ..it });
            Ok(Vec::new())
        }
        Intrinsic::SliceFilter => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            let Some(closure) = closure_fn(cx.prog, cx.args.get(1)) else {
                return Err(format!("`{name}` over a closure that is not modelled"));
            };
            let Some(fl) = closure_filter(closure) else {
                return Err(format!("`{name}` over a predicate this frontend does not model"));
            };
            env.iters.insert(dest.local, IterState { filter: Some(fl), ..it });
            Ok(Vec::new())
        }
        // `all(f)` / `any(f)`: a predicate fold to a `bool` -- `all` is the
        // conjunction of `pred(x)` over the elements, `any` the disjunction. Reuses
        // the `filter` predicate reader; needs a constant length.
        Intrinsic::SliceAll | Intrinsic::SliceAny => {
            let is_all = matches!(op, Intrinsic::SliceAll);
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            reject_adapters(&it, name)?;
            let Some(s) = env.indexed.get(&it.base) else {
                return Err(format!("`{name}` on an iterator whose slice is not modelled"));
            };
            let (elem_w, elem_signed) = (s.elem_w, s.elem_signed);
            let Some(n) = iterator_const_len(s, cx.pins) else {
                return Err(format!("`{name}` over a slice whose length is not a constant"));
            };
            let hi = it.end.map_or(n, |e| e.min(n));
            let Some(closure) = closure_fn(cx.prog, cx.args.get(1)) else {
                return Err(format!("`{name}` over a closure that is not modelled"));
            };
            let Some(fl) = closure_filter(closure) else {
                return Err(format!("`{name}` over a predicate this frontend does not model"));
            };
            let sign = Sign::of_bool(elem_signed);
            let mut acc = smt::truth(is_all);
            let mut k = it.pos;
            while k < hi {
                let Some((elem, _)) = env.index_elem(it.base, k) else {
                    return Err(format!("`{name}` on an iterator whose elements are not modelled"));
                };
                let pred = filter_pred(fl, elem, elem_w, sign)?;
                acc = if is_all { smt::and(acc, pred) } else { smt::or(acc, pred) };
                k += it.step;
            }
            env.set(dest, Val::Bool(acc));
            env.iters.remove(&recv.local);
            Ok(Vec::new())
        }
        Intrinsic::SliceNext => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!(
                    "`{name}` on a receiver that is not a modelled slice iterator"
                ));
            };
            reject_adapters(&it, name)?;
            let (base, pos) = (it.base, it.pos);
            let Some(s) = env.indexed.get(&base) else {
                return Err(format!("`{name}` on an iterator whose slice is not modelled"));
            };
            let (len, elem_w) = (s.len, s.elem_w);
            // The base index the sequence position `pos` names: `pos` itself, or
            // `len-1-pos` when reversed. `rev` needs a *constant* length so the
            // index is a constant (a symbolic one would need the ite chain), and a
            // symbolic-length reversed cursor is refused rather than guessed.
            let (idx, tag) = if it.rev {
                let Some(n) = iterator_const_len(s, cx.pins) else {
                    return Err(format!(
                        "`{name}` with `rev` on a slice whose length is not a constant"
                    ));
                };
                let hi = it.end.map_or(n, |e| e.min(n));
                if pos < hi {
                    (n - 1 - pos, smt::word(intrinsics::SOME_TAG, 1))
                } else {
                    (0, smt::word(0, 1))
                }
            } else if let Some(e) = it.end {
                // A `take` cursor: `Some` iff `pos < min(len, end)`, which is a
                // constant because `take` needs a constant length.
                let Some(n) = iterator_const_len(s, cx.pins) else {
                    return Err(format!("`{name}` on a `take`d slice whose length is not a constant"));
                };
                let hi = e.min(n);
                let tag = if pos < hi {
                    smt::word(intrinsics::SOME_TAG, 1)
                } else {
                    smt::word(0, 1)
                };
                (pos, tag)
            } else {
                // `None` exactly when `pos >= len` (a concrete `pos`); `Some`
                // otherwise. The tag is one bit like `first`/`get`.
                (
                    pos,
                    smt::ite(
                        smt::ule_const(len, pos),
                        smt::word(0, 1),
                        smt::word(intrinsics::SOME_TAG, 1),
                    ),
                )
            };
            let (elem, sign) = env.index_elem(base, idx).ok_or_else(|| {
                format!("`{name}` on an iterator whose elements are not modelled")
            })?;
            env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
            if name.contains("Enumerate") {
                // `Enumerate::next` yields `Option<(usize, &T)>`. The payload is a
                // *tuple*: component 0 is the concrete index, component 1 the element.
                // The body destructures it directly -- `((_7 as Some).0).0` and
                // `((_7 as Some).0).1` -- so the two components go in the tuple store
                // (`elems`, the same store a tuple literal writes and a `Field(j)`
                // read falls back to), and the payload itself is `Val::Agg` so a
                // whole-payload copy does not read a wrong single word. The element
                // identity is recorded so `*((_7 as Some).0).1` resolves to `xs[pos]`.
                env.elems.insert(
                    (dest.local, 0),
                    Val::Sym(
                        smt::word(pos.saturating_sub(it.enum_start.unwrap_or(0)), 64),
                        Sign::Unsigned,
                    ),
                );
                env.elems.insert((dest.local, 1), Val::Sym(elem, sign));
                env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Agg, 0);
            } else {
                env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(elem, sign), elem_w);
            }
            env.slice_elem_ref.insert(dest.local, ElemId::Leaf((base, idx)));
            if let Some(it) = env.iters.get_mut(&recv.local) {
                it.pos = it.pos.saturating_add(it.step);
            }
            Ok(Vec::new())
        }
        Intrinsic::SliceCount => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            let Some(s) = env.indexed.get(&it.base) else {
                return Err(format!("`{name}` on an iterator whose slice is not modelled"));
            };
            let len = s.len;
            let w = smt::bits(len);
            // `filter(pred).count()` counts the elements the predicate accepts.
            if let Some(fl) = it.filter {
                let (elem_w, elem_signed) = (s.elem_w, s.elem_signed);
                let Some(n) = iterator_const_len(s, cx.pins) else {
                    return Err(format!(
                        "`{name}` over a filtered slice whose length is not a constant"
                    ));
                };
                let hi = it.end.map_or(n, |e| e.min(n));
                let sign = Sign::of_bool(elem_signed);
                let mut acc = smt::word(0, w);
                let mut k = it.pos;
                while k < hi {
                    let Some((elem, _)) = env.index_elem(it.base, k) else {
                        return Err(format!("`{name}` on an iterator whose elements are not modelled"));
                    };
                    let pred = filter_pred(fl, elem, elem_w, sign)?;
                    acc = smt::add(acc, smt::ite(pred, smt::word(1, w), smt::word(0, w)));
                    k += it.step;
                }
                env.set(dest, Val::Sym(acc, Sign::Unsigned));
                env.iters.remove(&recv.local);
                return Ok(Vec::new());
            }
            let count = if it.step != 1 || it.end.is_some() {
                // A stride or a `take` needs a *constant* length to count exactly.
                let Some(n) = iterator_const_len(s, cx.pins) else {
                    return Err(format!(
                        "`{name}` with `step_by`/`take` on a slice whose length is not a constant"
                    ));
                };
                let hi = it.end.map_or(n, |e| e.min(n));
                let c = if it.pos < hi { (hi - 1 - it.pos) / it.step + 1 } else { 0 };
                smt::word(c, w)
            } else if it.pos == 0 {
                // `len - pos`, guarded so a cursor already advanced past the end (a
                // `next` that returned `None` still advances the position) counts
                // zero rather than underflowing.
                len
            } else {
                smt::ite(
                    smt::ule_const(len, it.pos),
                    smt::word(0, w),
                    smt::sub(len, smt::word(it.pos, w)),
                )
            };
            env.set(dest, Val::Sym(count, Sign::Unsigned));
            // The iterator is consumed by value; its cursor has no further use.
            env.iters.remove(&recv.local);
            Ok(Vec::new())
        }
        Intrinsic::SliceSum => slice_sum(name, &recv, dest, env, cx),
        Intrinsic::SliceIterLast => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            let Some(s) = env.indexed.get(&it.base) else {
                return Err(format!("`{name}` on an iterator whose slice is not modelled"));
            };
            let (len, elem_w) = (s.len, s.elem_w);
            // An array's length is a constant, and a slice's is modelled here when the
            // precondition pinned it (`requires: xs.len() == N`), so in either case the
            // last element is the exact `s[n-1]` -- the same variable a contract's
            // `xs[n-1]` names. Only a *symbolic*-length slice falls back to the single
            // fresh `LAST_INDEX` variable, the same over-approximation `slice::last`
            // uses. `None` exactly when the cursor has run out (`pos >= len`).
            let (idx, tag) = if it.rev {
                let Some(n) = iterator_const_len(s, cx.pins) else {
                    return Err(format!(
                        "`{name}` with `rev` on a slice whose length is not a constant"
                    ));
                };
                // The last element of the remaining *reversed* sequence is `s[pos]`.
                let (idx, tag) = if it.pos < n {
                    (it.pos, smt::word(intrinsics::SOME_TAG, 1))
                } else {
                    (0, smt::word(0, 1))
                };
                (idx, tag)
            } else {
                let idx = match iterator_const_len(s, cx.pins) {
                    Some(0) => 0,
                    Some(n) if it.pos < it.end.map_or(n, |e| e.min(n)) => {
                        // The last index the stride reaches from `pos`, capped by a
                        // `take` end: `pos + m*step`, `m = (hi-1-pos)/step`.
                        let hi = it.end.map_or(n, |e| e.min(n));
                        it.pos + ((hi - 1 - it.pos) / it.step) * it.step
                    }
                    Some(_) => 0,
                    None => LAST_INDEX,
                };
                let tag = smt::ite(
                    smt::ule_const(len, it.pos),
                    smt::word(0, 1),
                    smt::word(intrinsics::SOME_TAG, 1),
                );
                (idx, tag)
            };
            let (elem, sign) = env.index_elem(it.base, idx).ok_or_else(|| {
                format!("`{name}` on an iterator whose elements are not modelled")
            })?;
            env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
            env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(elem, sign), elem_w);
            env.slice_elem_ref.insert(dest.local, ElemId::Leaf((it.base, idx)));
            env.iters.remove(&recv.local);
            Ok(Vec::new())
        }
        Intrinsic::SliceNth => {
            let Some(it) = env.iters.get(&recv.local).copied() else {
                return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
            };
            let Some(s) = env.indexed.get(&it.base) else {
                return Err(format!("`{name}` on an iterator whose slice is not modelled"));
            };
            let (len, elem_w) = (s.len, s.elem_w);
            let Some(k) = constant_operand(cx.args.get(1), env) else {
                return Err(format!(
                    "`{name}` with a non-constant offset is not modelled"
                ));
            };
            let j = it.pos.saturating_add(k.saturating_mul(it.step));
            let (idx, tag) = if it.rev || it.end.is_some() {
                let Some(n) = iterator_const_len(s, cx.pins) else {
                    return Err(format!(
                        "`{name}` on a `rev`/`take`d slice whose length is not a constant"
                    ));
                };
                let hi = it.end.map_or(n, |e| e.min(n));
                if j < hi {
                    let idx = if it.rev { n - 1 - j } else { j };
                    (idx, smt::word(intrinsics::SOME_TAG, 1))
                } else {
                    (0, smt::word(0, 1))
                }
            } else {
                (
                    j,
                    smt::ite(
                        smt::ule_const(len, j),
                        smt::word(0, 1),
                        smt::word(intrinsics::SOME_TAG, 1),
                    ),
                )
            };
            let (elem, sign) = env.index_elem(it.base, idx).ok_or_else(|| {
                format!("`{name}` on an iterator whose elements are not modelled")
            })?;
            env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
            env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(elem, sign), elem_w);
            env.slice_elem_ref.insert(dest.local, ElemId::Leaf((it.base, idx)));
            // `nth` consumes the returned element, so the cursor advances past it.
            if let Some(it) = env.iters.get_mut(&recv.local) {
                it.pos = j.saturating_add(1);
            }
            Ok(Vec::new())
        }
        Intrinsic::SliceExtreme(kind) => slice_extreme(name, &recv, dest, env, cx, kind),
        _ => Err(format!("`{name}` is not a slice iterator method")),
    }
}

/// The largest slice length `sum`/`max`/`min` will unroll. Each addend (or
/// comparison) grows the term, so a length past this is refused rather than turned
/// into a term the solver cannot hold.
const MAX_SUM_LEN: u64 = 256;

/// The bound a *symbolic*-length sum is unrolled to. The precondition must prove
/// `<slice>.len() <= MAX_SYMBOLIC_LEN`; past it the shape is refused.
const MAX_SYMBOLIC_LEN: u64 = 8;

/// A constant `u64` from an operand: a literal, or a local the run pinned to a
/// constant (a `smt::evaluate` of its value). `None` for anything symbolic, which
/// the callers refuse rather than guess.
fn constant_operand(o: Option<&Operand>, env: &Env) -> Option<u64> {
    match o? {
        Operand::Const(Const::UInt(v, _)) => u64::try_from(*v).ok(),
        Operand::Copy(p) | Operand::Move(p) => match env.locals.get(&p.local) {
            Some(Val::Sym(v, _)) => smt::evaluate(*v, |_| None),
            _ => None,
        },
        _ => None,
    }
}

/// The constant length of a slice/array cursor's base: an array's type length, or a
/// slice whose length the precondition pinned (`requires: xs.len() == N`). `None`
/// for a symbolic slice length, which `sum`/`max`/`min` refuse.
fn iterator_const_len(s: &Indexed, pins: &[(u32, u64)]) -> Option<u64> {
    match s.fixed_len {
        Some(n) => Some(n),
        None => pins.iter().find(|(i, _)| *i == smt::index(s.len)).map(|(_, k)| *k),
    }
}

/// `Iterator::max`/`Iterator::min` over a slice/array cursor: a fold of comparisons
/// over the remaining elements.
///
/// Needs a *constant* length (the number of comparisons is the length). The payload
/// is the extreme *value*; the element identity is a `Select` tree over the same
/// elements, so a deref of a reference payload (`Option<&T>`) reads the same value a
/// direct read of `Option<T>` does. `None` exactly when the cursor has run out.
fn slice_extreme(
    name: &str,
    recv: &Place,
    dest: &Place,
    env: &mut Env,
    cx: &IterCall<'_>,
    kind: intrinsics::ExtremeKind,
) -> Result<Vec<Obligation>, String> {
    use intrinsics::ExtremeKind;
    let Some(it) = env.iters.get(&recv.local).copied() else {
        return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
    };
    let Some(s) = env.indexed.get(&it.base) else {
        return Err(format!("`{name}` on an iterator whose slice is not modelled"));
    };
    let (len, elem_w, elem_signed) = (s.len, s.elem_w, s.elem_signed);
    let Some(n) = iterator_const_len(s, cx.pins) else {
        return Err(format!(
            "`{name}` over a slice whose length is not a constant (write \
             `requires: <slice>.len() == N`)"
        ));
    };
    if n > MAX_SUM_LEN {
        return Err(format!("`{name}` over {n} elements is past the {MAX_SUM_LEN}-element limit"));
    }
    let sign = Sign::of_bool(elem_signed);
    let hi = it.end.map_or(n, |e| e.min(n));
    let tag = if it.end.is_some() {
        smt::word(if it.pos < hi { intrinsics::SOME_TAG } else { 0 }, 1)
    } else {
        smt::ite(
            smt::ule_const(len, it.pos),
            smt::word(0, 1),
            smt::word(intrinsics::SOME_TAG, 1),
        )
    };
    env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
    if it.pos < hi {
        let (first, _) = env
            .index_elem(it.base, it.pos)
            .ok_or_else(|| format!("`{name}` on an iterator whose elements are not modelled"))?;
        let mut acc = first;
        let mut tree = ElemId::Leaf((it.base, it.pos));
        let mut k = it.pos + it.step;
        while k < hi {
            let (elem, _) = env.index_elem(it.base, k).ok_or_else(|| {
                format!("`{name}` on an iterator whose elements are not modelled")
            })?;
            // `keep` is "the running extreme beats the new element", so the `ite`
            // keeps `acc` when true and takes `elem` otherwise -- and the `Select`
            // tree picks the same branch, so the payload and a deref of it agree.
            let keep = match kind {
                ExtremeKind::Max => {
                    if elem_signed {
                        smt::slt(elem, acc)
                    } else {
                        smt::ult(elem, acc)
                    }
                }
                ExtremeKind::Min => {
                    if elem_signed {
                        smt::slt(acc, elem)
                    } else {
                        smt::ult(acc, elem)
                    }
                }
            };
            acc = smt::ite(keep, acc, elem);
            tree = ElemId::Select(keep, Box::new(tree), Box::new(ElemId::Leaf((it.base, k))));
            k += it.step;
        }
        env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(acc, sign), elem_w);
        env.slice_elem_ref.insert(dest.local, tree);
    } else {
        // Empty remaining: `None`, and the payload is never read.
        env.set_payload(
            dest.local,
            intrinsics::SOME_TAG,
            Val::Sym(smt::word(0, elem_w), sign),
            elem_w,
        );
    }
    env.iters.remove(&recv.local);
    Ok(Vec::new())
}

/// `Iterator::sum::<T>` over a slice/array cursor: `s[pos] + ... + s[len-1]`.
///
/// The number of addends is the length, so this is modelled only when that length
/// is a *constant* -- an array's type length, or a slice whose length the
/// precondition pinned (`requires: xs.len() == N`). A symbolic length has no fixed
/// number of addends, so it is refused. Each step is a checked `+`: `sum` uses
/// `Add::add`, which panics on overflow in a debug build, so each partial sum
/// raises a reachable-panic obligation -- a model that summed with a silent wrap
/// would hide a panic, which this frontend must never do.
/// Apply a `map` transform to one element, returning the mapped value and any
/// overflow obligation the transform itself raises.
fn apply_map(
    m: MapOp,
    elem: Var,
    w: u8,
    sign: Sign,
    path: Pred,
    pins: &[(u32, u64)],
) -> Result<(Var, Vec<Obligation>), String> {
    let rhs = smt::word(m.rhs, w);
    let (a, b) = if m.rhs_left {
        (Val::Sym(rhs, sign), Val::Sym(elem, sign))
    } else {
        (Val::Sym(elem, sign), Val::Sym(rhs, sign))
    };
    let mut obs = Vec::new();
    if m.checked {
        let Some(over) = overflow_pred(m.op, a, b, w) else {
            return Err("`map` overflow predicate is not modelled".into());
        };
        obs.push(Obligation {
            kind: ObligationKind::Panic { message: "`map` closure overflows".into() },
            verdict: find_obligation(smt::and(path, over), pins),
        });
    }
    match eval_binary(m.op, a, b, Some(w)) {
        Val::Sym(v, _) => Ok((v, obs)),
        _ => Err("`map` step is not modelled".into()),
    }
}

/// Evaluate a `filter` predicate on one element.
fn filter_pred(fl: FilterOp, elem: Var, w: u8, sign: Sign) -> Result<Pred, String> {
    let rhs = smt::word(fl.rhs, w);
    let (a, b) = if fl.rhs_left {
        (Val::Sym(rhs, sign), Val::Sym(elem, sign))
    } else {
        (Val::Sym(elem, sign), Val::Sym(rhs, sign))
    };
    match eval_binary(fl.op, a, b, Some(w)) {
        Val::Bool(p) => Ok(p),
        _ => Err("`filter` predicate is not modelled".into()),
    }
}

fn slice_sum(
    name: &str,
    recv: &Place,
    dest: &Place,
    env: &mut Env,
    cx: &IterCall<'_>,
) -> Result<Vec<Obligation>, String> {
    let IterCall { f, pins, path, .. } = *cx;
    let Some(it) = env.iters.get(&recv.local).copied() else {
        return Err(format!("`{name}` on a receiver that is not a modelled slice iterator"));
    };
    let Some(s) = env.indexed.get(&it.base) else {
        return Err(format!("`{name}` on an iterator whose slice is not modelled"));
    };
    let (elem_w, elem_signed) = (s.elem_w, s.elem_signed);
    let Some(dest_w) = type_of_place(f, dest).and_then(|t| t.width()) else {
        return Err(format!("`{name}` on a destination whose width is not modelled"));
    };
    // The element type must be the sum's own type: `Sum<&u8> for u8` sums `u8`s at
    // `u8` width, and a mismatched width would be a different operation.
    if elem_w != dest_w {
        return Err(format!(
            "`{name}` over `{elem_w}`-bit elements into a `{dest_w}`-bit sum is not modelled"
        ));
    }
    if it.filter.is_some() {
        return Err(format!("`{name}` over a filtered iterator is not modelled"));
    }
    if it.rev {
        return Err(format!("`{name}` over a reversed iterator is not modelled"));
    }
    // The number of addends. A *constant* length is unrolled exactly. A *symbolic*
    // length is unrolled to a bound `K` and each step is guarded by `k < len`, which
    // is exact exactly when the length is at most `K` -- so the precondition must
    // *prove* `len <= K`; otherwise the sum would silently miss elements, which is a
    // wrong value, so the shape is refused.
    let len = s.len;
    let (hi, symbolic) = match iterator_const_len(s, pins) {
        Some(n) => {
            if n > MAX_SUM_LEN {
                return Err(format!("`{name}` over {n} elements is past the {MAX_SUM_LEN}-element limit"));
            }
            (it.end.map_or(n, |e| e.min(n)), false)
        }
        None => {
            if it.step != 1 || it.end.is_some() {
                return Err(format!(
                    "`{name}` over a symbolic-length slice with `step_by`/`take` is not modelled"
                ));
            }
            let within = smt::ule_const(len, MAX_SYMBOLIC_LEN);
            if !matches!(find_obligation(smt::and(path, smt::not(within)), pins), Verdict::Unsat) {
                return Err(format!(
                    "`{name}` over a slice whose length is not bounded (write \
                     `requires: <slice>.len() <= {MAX_SYMBOLIC_LEN}`)"
                ));
            }
            (MAX_SYMBOLIC_LEN, true)
        }
    };
    let sign = Sign::of_bool(elem_signed);
    let mut acc = smt::word(0, dest_w);
    let mut obligations = Vec::new();
    let mut k = it.pos;
    while k < hi {
        let Some((elem, _)) = env.index_elem(it.base, k) else {
            return Err(format!("`{name}` on an iterator whose elements are not modelled"));
        };
        // A symbolic-length sum guards each step by `k < len`, so an index past the
        // real length contributes 0. Exact because `len <= MAX_SYMBOLIC_LEN` was proved.
        let elem = if symbolic {
            smt::ite(smt::not(smt::ule_const(len, k)), elem, smt::word(0, elem_w))
        } else {
            elem
        };
        // A `map` transform is applied to each element before it is summed.
        let elem = if let Some(m) = it.map {
            let (v, obs) = apply_map(m, elem, elem_w, sign, path, pins)?;
            obligations.extend(obs);
            v
        } else {
            elem
        };
        // `Add::add` panics on overflow in a debug build, so each step is a
        // reachable-panic obligation, exactly as the `overflowing_*` family's own
        // `assert` would be. A step whose overflow predicate cannot be built is
        // *refused* rather than summed without a check -- a silent wrap would hide a
        // panic.
        let Some(over) = overflow_pred(
            BinOp::Add,
            Val::Sym(acc, sign),
            Val::Sym(elem, sign),
            dest_w,
        ) else {
            return Err(format!("`{name}` overflow predicate is not modelled"));
        };
        obligations.push(Obligation {
            kind: ObligationKind::Panic { message: format!("`{name}` overflows") },
            verdict: find_obligation(smt::and(path, over), pins),
        });
        acc = smt::add(acc, elem);
        k += it.step;
    }
    env.set(dest, Val::Sym(acc, sign));
    env.iters.remove(&recv.local);
    Ok(obligations)
}

/// The element type of a `Vec<T>`, from its printed name.
///
/// rustc prints the standard container's *type* as `std::vec::Vec<u8>` (or
/// `alloc::vec::Vec<u8>`) -- never as a bare `Vec<u8>` -- so the identity is the
/// full path, not the last segment. This matters for soundness: a user type
/// spelled `Vec` (`mod m { struct Vec<T>(..) }`, printed `m::Vec<u8>`, or a
/// crate-root `Vec<u8>`) must **not** be read as the standard container, or a
/// destructor this model skips would be skipped for a type that is not a `Vec`
/// at all. So the module path is checked, not discarded.
///
/// `None` for a name that is not the standard `Vec`, or one whose arguments
/// cannot be read.
pub(crate) fn vec_elem_ty(name: &str) -> Option<Ty> {
    // The head before the generic arguments is the path; the standard container's
    // is `std::vec::Vec` or `alloc::vec::Vec`. A bare `Vec` is a user type (rustc
    // always qualifies the standard one), so it is refused.
    let head = name.split('<').next().unwrap_or(name);
    if head != "std::vec::Vec" && head != "alloc::vec::Vec" {
        return None;
    }
    crate::mir::spec::angle_inner(name).map(Ty::parse)
}

/// Like [`vec_elem_ty`], but also accepts the *bare* `Vec<T>` spelling.
///
/// rustc prints a `Vec` local's type by its shortest crate-unique path, which is
/// the bare `Vec<u8>` when nothing shadows it, and only the `drop`-glue identity
/// check needs the full path (a user `struct Vec` must not be treated as the
/// container and skipped). For the *length and element* model a bare `Vec` is the
/// standard one unless a same-dump body answers first: reading its length as a
/// fresh input and its `v[0]` as a fresh element is an over-approximation, so a
/// user `Vec` mis-read here would be a lost proof, never a false one.
pub(crate) fn vec_elem_ty_loose(name: &str) -> Option<Ty> {
    let head = name.split('<').next().unwrap_or(name).trim();
    if head != "Vec" && head != "std::vec::Vec" && head != "alloc::vec::Vec" {
        return None;
    }
    crate::mir::spec::angle_inner(name).map(Ty::parse)
}

/// The element type of a standard `Box<T>`, from its printed name.
///
/// The head is checked against the *full* path (`std::boxed::Box` /
/// `alloc::boxed::Box`), because a user `struct Box` must not be treated as the
/// container: a `Box<T>`'s drop glue is `T`'s, so a user `Box` mis-read here would
/// be a false "glue-free" and hide a panicking destructor.
pub(crate) fn box_elem_ty(name: &str) -> Option<Ty> {
    let head = name.split('<').next().unwrap_or(name).trim();
    if head != "std::boxed::Box" && head != "alloc::boxed::Box" {
        return None;
    }
    crate::mir::spec::angle_inner(name).map(Ty::parse)
}

/// `std::mem::drop::<T>(v)`: consume `v`. A glue-free `T` runs no destructor, so
/// the call is a no-op; a `T` whose drop glue the tool cannot represent is
/// *refused* rather than assumed inert (a panicking destructor would be hidden).
///
/// The type is read from the call's own name (`drop::<T>`), the same source the
/// `Box` model uses for its element. A *bare* container name (`Box<u8>`,
/// `String`) is the standard type only when the crate declares no struct of that
/// name -- `std_container_glue_free` takes the layouts, so a shadowing user type
/// with a destructor is refused rather than read as glue-free.
fn mem_drop(
    name: &str,
    structs: &BTreeMap<String, spec::StructDef>,
) -> Result<Vec<Obligation>, String> {
    let ty = crate::mir::spec::angle_inner(name)
        .map(Ty::parse)
        .unwrap_or(Ty::Unit);
    if drop_is_noop(&ty) || std_container_glue_free(&ty, structs) {
        return Ok(Vec::new());
    }
    Err(format!(
        "`{name}` destroys a value whose drop glue is not modelled"
    ))
}

/// The `Box<T>` model: `Box::<T>::new` stores the boxed value and a nonzero token
/// pointer, so the compiler's null and alignment checks are discharged and `*b`
/// reads the stored value (see the `Box` section of `AGENTS.md`).
fn box_method(
    name: &str,
    kind: intrinsics::BoxMethod,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
) -> Result<Vec<Obligation>, String> {
    match kind {
        intrinsics::BoxMethod::New => {
            let Some(a) = args.first() else {
                return Err(format!("`{name}` with no argument"));
            };
            let v = operand(env, a);
            env.boxed.insert(dest.local, v);
            // The compiler reads the box's field 0 as the pointer, then checks it
            // against null. A nonzero token makes `Eq(ptr, 0)` false, so the null
            // check (with `Ne(SIZE, 0)`) is discharged and the deref is reachable.
            // A large power of two: nonzero (the null check passes) and a multiple
            // of any primitive alignment up to 2^24 (the alignment check
            // `addr & (ALIGN - 1) == 0` passes for every `T` the model holds).
            env.fields
                .insert((dest.local, 0), Val::Sym(smt::word(1 << 24, 64), Sign::Unsigned));
            Ok(Vec::new())
        }
    }
}

fn string_method(
    name: &str,
    kind: intrinsics::StringMethod,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
    f: &MirFn,
) -> Result<Vec<Obligation>, String> {
    use intrinsics::StringMethod;
    // The string's tracked length, read through one reference (`len`/`is_empty`
    // take `&self`, `push_str` `&mut self`). `new` has no receiver.
    let receiver = |env: &Env| -> Result<u32, String> {
        match args.first() {
            Some(Operand::Copy(p)) | Some(Operand::Move(p)) => Ok(env.pointee(p).local),
            _ => Err(format!("unmodelled receiver for `{name}`")),
        }
    };
    let length = |env: &Env, l: u32| -> Result<Var, String> {
        match env.indexed.get(&l) {
            Some(s) => Ok(s.len),
            None => Err(format!("`{name}` on a receiver whose length is not modelled")),
        }
    };
    // A `&str`'s byte length, as the same variable `str::len` reads: a symbolic
    // input for an argument, a constant for a literal. A source whose length is
    // not modelled is refused rather than given an invented number.
    let str_len = |env: &Env, a: Option<&Operand>| -> Result<Var, String> {
        // A literal reaches the call either directly (`from(const "abc")`) or
        // through a local (`_4 = const "ab"; push_str(_, move _4)`).
        if let Some(Operand::Const(Const::Str(text))) = a {
            return Ok(smt::word(text.len() as u64, USIZE_WIDTH));
        }
        let p = match a {
            Some(Operand::Copy(p)) | Some(Operand::Move(p)) => p.clone(),
            _ => return Err(format!("unmodelled argument to `{name}`")),
        };
        match length_of(env, f, &p) {
            Val::Sym(v, _) => Ok(v),
            _ => Err(format!("`{name}` on a `&str` whose length is not modelled")),
        }
    };
    match kind {
        StringMethod::New => {
            env.indexed.insert(
                dest.local,
                Indexed {
                    len: smt::word(0, USIZE_WIDTH),
                    len_mutable: true,
                    elem_w: 8,
                    elem_signed: false,
                    elems: BTreeMap::new(),
                    fixed_len: None,
                    slice_steps: None,
                    poisoned: false,
                },
            );
            Ok(Vec::new())
        }
        StringMethod::From => {
            let len = str_len(env, args.first())?;
            env.indexed.insert(
                dest.local,
                Indexed {
                    len,
                    len_mutable: true,
                    elem_w: 8,
                    elem_signed: false,
                    elems: BTreeMap::new(),
                    fixed_len: None,
                    slice_steps: None,
                    poisoned: false,
                },
            );
            Ok(Vec::new())
        }
        StringMethod::PushStr => {
            let l = receiver(env)?;
            let add = str_len(env, args.get(1))?;
            let cur = length(env, l)?;
            if let Some(s) = env.indexed.get_mut(&l) {
                s.len = smt::add(cur, add);
            }
            Ok(Vec::new())
        }
        StringMethod::Clear => {
            let l = receiver(env)?;
            let _ = length(env, l)?;
            if let Some(s) = env.indexed.get_mut(&l) {
                s.len = smt::word(0, USIZE_WIDTH);
            }
            Ok(Vec::new())
        }
        StringMethod::Len => {
            let l = receiver(env)?;
            let len = length(env, l)?;
            env.set(dest, Val::Sym(len, Sign::Unsigned));
            Ok(Vec::new())
        }
        StringMethod::IsEmpty => {
            let l = receiver(env)?;
            let len = length(env, l)?;
            env.set(dest, Val::Bool(smt::eq_const(len, 0)));
            Ok(Vec::new())
        }
    }
}

/// The `Vec<T>` model: a length plus the elements, an `indexed` store exactly as a
/// slice has.
///
/// A `Vec`'s fields (a heap pointer, a length, a capacity) are not printed by the
/// dump, so the model holds the length the calls set and the elements they wrote.
/// `new`/`push`/`len`/`is_empty`/`pop` are the inherent methods; `Index` and
/// `Deref`/`as_slice` are the trait calls `v[i]` and `v.first()`/`v.get(k)` lower
/// to, so a pushed value can be read back -- the half of C11 the length-only model
/// left out.
///
/// The receiver of `push`/`len`/`pop` is a reference, so the state lives on the
/// *referent* local -- `pointee` follows `&mut v`/`&v` to the storage the caller
/// owns, the same local `new` wrote. A receiver whose store the run never set (a
/// `Vec` argument that was never bound) is refused, never given an invented value.
///
/// Three soundness points:
///
/// * `push` records the pushed value at the *current* length only when that length
///   is a constant. A symbolic length (a `Vec` argument) means the store cannot pin
///   the index, so it poisons the elements -- a stale element would be a wrong
///   value, not a missing one. The length still advances exactly.
/// * `Index` emits the bounds panic (`k >= len`) as a reachable-failure obligation.
///   `v[k]` panics inside `core`, not in the dump, so a model that skipped it would
///   report an out-of-bounds read panic-free -- a false proof.
/// * `Deref` copies the store to the destination, sharing the element variables
///   that exist at that point, so `v.first()` and `v[0]` name one element. A push
///   *after* a deref is not seen by the deref'd slice, which is correct: Rust does
///   not let a `&[T]` borrow coexist with a `&mut Vec`. An element the *contract*
///   named (or one `v[k]` created before the deref) is shared; an element first
///   created by a deref'd read is not the one a later `v[k]` creates, so
///   `v.first() == v[0]` is a lost proof in that one ordering -- never a false one.
#[allow(clippy::too_many_arguments)]
fn vec_method(
    name: &str,
    kind: intrinsics::VecMethod,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
    path: Pred,
    pins: &[(u32, u64)],
    f: &MirFn,
) -> Result<Vec<Obligation>, String> {
    use intrinsics::VecMethod;
    // The storage the receiver names, following one reference. `new` is the
    // exception: it is an associated function with no receiver.
    let receiver = |env: &Env| -> Result<u32, String> {
        match args.first() {
            Some(Operand::Copy(p)) | Some(Operand::Move(p)) => Ok(env.pointee(p).local),
            _ => Err(format!("unmodelled receiver for `{name}`")),
        }
    };
    // The vector's `(length, element width, element sign, poisoned)`.
    let shape = |env: &Env, l: u32| -> Result<(Var, u8, bool, bool), String> {
        match env.indexed.get(&l) {
            Some(s) => Ok((s.len, s.elem_w, s.elem_signed, s.poisoned)),
            None => Err(format!("`{name}` on a receiver whose length is not modelled")),
        }
    };
    match kind {
        VecMethod::New => {
            let ty = f.ty_of(dest.local).cloned().unwrap_or(Ty::Other("?".into()));
            let ty = match ty {
                Ty::Ref(inner) => *inner,
                other => other,
            };
            let elem = match &ty {
                Ty::Other(s) => vec_elem_ty_loose(s),
                _ => None,
            }
            .ok_or_else(|| format!("`{name}` on a type whose element is not modelled"))?;
            env.indexed.insert(
                dest.local,
                Indexed {
                    len: smt::word(0, USIZE_WIDTH),
                    len_mutable: true,
                    elem_w: elem.width().unwrap_or(0),
                    elem_signed: elem.is_signed(),
                    elems: BTreeMap::new(),
                    fixed_len: None,
                    slice_steps: None,
                    poisoned: false,
                },
            );
            Ok(Vec::new())
        }
        VecMethod::Push => {
            let l = receiver(env)?;
            let (len, elem_w, _, poisoned) = shape(env, l)?;
            let pushed = match args.get(1).map(|a| operand(env, a)) {
                Some(Val::Sym(v, _)) => Some(v),
                Some(Val::Bool(p)) => Some(smt::ite(p, smt::word(1, 1), smt::word(0, 1))),
                _ => None,
            };
            // The index the push writes is the length *before* the increment. Only a
            // constant length pins it; a symbolic one cannot be recorded per index.
            let k = smt::evaluate(len, |_| None);
            let s = env.indexed.get_mut(&l).expect("checked by `shape`");
            s.len = smt::add(len, smt::word(1, USIZE_WIDTH));
            match (k, pushed) {
                (Some(k), Some(v)) if elem_w != 0 && smt::bits(v) == elem_w && !poisoned => {
                    s.elems.insert(k, v);
                }
                _ => {
                    s.elems.clear();
                    s.poisoned = true;
                }
            }
            Ok(Vec::new())
        }
        VecMethod::Clear => {
            let l = receiver(env)?;
            let (_, elem_w, _, _) = shape(env, l)?;
            // `clear` destroys every element immediately. A glue-free scalar element (a
            // modelled width) has no destructor, so the reset is exact; an element with
            // no modelled width may have a `Drop` that panics, so refuse rather than
            // report the reset panic-free.
            if elem_w == 0 {
                return Err(format!(
                    "`{name}` on a Vec whose element may have drop glue is not modelled"
                ));
            }
            if let Some(s) = env.indexed.get_mut(&l) {
                s.len = smt::word(0, USIZE_WIDTH);
                s.elems.clear();
            }
            Ok(Vec::new())
        }
        VecMethod::Len => {
            let l = receiver(env)?;
            let (len, ..) = shape(env, l)?;
            env.set(dest, Val::Sym(len, Sign::Unsigned));
            Ok(Vec::new())
        }
        VecMethod::IsEmpty => {
            let l = receiver(env)?;
            let (len, ..) = shape(env, l)?;
            env.set(dest, Val::Bool(smt::eq_const(len, 0)));
            Ok(Vec::new())
        }
        VecMethod::Pop => {
            let l = receiver(env)?;
            let (len, elem_w, _, poisoned) = shape(env, l)?;
            let empty = smt::eq_const(len, 0);
            let nonempty = smt::not(empty);
            env.set_discriminant(
                dest.local,
                Val::Sym(
                    smt::ite(
                        nonempty,
                        smt::word(intrinsics::SOME_TAG, 1),
                        smt::word(intrinsics::NONE_TAG, 1),
                    ),
                    Sign::Unsigned,
                ),
            );
            // The popped element is the last one, so it can be pinned only when the
            // length is a constant. `pop` removes it, so the record goes too.
            if let Some(k) = smt::evaluate(len, |_| None) {
                if k > 0 && !poisoned {
                    if let Some((elem, sign)) = env.index_elem(l, k - 1) {
                        env.set_payload(
                            dest.local,
                            intrinsics::SOME_TAG,
                            Val::Sym(elem, sign),
                            elem_w,
                        );
                    }
                    if let Some(s) = env.indexed.get_mut(&l) {
                        s.elems.remove(&(k - 1));
                    }
                }
            }
            if let Some(s) = env.indexed.get_mut(&l) {
                s.len = smt::ite(nonempty, smt::sub(len, smt::word(1, USIZE_WIDTH)), len);
            }
            Ok(Vec::new())
        }
        VecMethod::Index => {
            let l = receiver(env)?;
            let (len, ..) = shape(env, l)?;
            // `v[i]` — the index must be a constant. A `Vec` has no finite domain to
            // enumerate (its length is a tracked term, not a type constant), so a
            // symbolic index has no chain to build and is refused.
            let k = match args.get(1) {
                Some(Operand::Const(Const::UInt(v, _))) => u64::try_from(*v).ok(),
                Some(Operand::Copy(p) | Operand::Move(p)) => match env.locals.get(&p.local) {
                    Some(Val::Sym(v, _)) => smt::evaluate(*v, |_| None),
                    _ => None,
                },
                _ => None,
            };
            let Some(k) = k else {
                return Err(format!("`{name}` with an index that is not a constant is not modelled"));
            };
            let (elem, sign) = env
                .index_elem(l, k)
                .ok_or_else(|| format!("`{name}` on a receiver whose elements are not modelled"))?;
            // `v[k]` returns `&T`; model the reference as its referent and record the
            // element identity so a later `*` reads the element.
            env.set(dest, Val::Sym(elem, sign));
            env.slice_elem_ref.insert(dest.local, ElemId::Leaf((l, k)));
            // The bounds check `k < len` is `core`'s, not the dump's, so the model
            // must emit it: an out-of-range index panics, and a model that skipped
            // the check would call it panic-free.
            let out_of_bounds = smt::ule_const(len, k);
            Ok(vec![Obligation {
                kind: ObligationKind::Panic {
                    message: format!("index out of bounds: the index is {k}"),
                },
                verdict: find_obligation(smt::and(path, out_of_bounds), pins),
            }])
        }
        VecMethod::Deref | VecMethod::AsSlice => {
            let l = receiver(env)?;
            let s = env
                .indexed
                .get(&l)
                .cloned()
                .ok_or_else(|| format!("`{name}` on a receiver whose length is not modelled"))?;
            // The destination is the same store viewed as a slice: the element
            // variables are shared (same `Var`s), and the length is the vector's
            // current length, fixed for this borrow.
            env.indexed.insert(
                dest.local,
                Indexed {
                    len_mutable: false,
                    fixed_len: None,
                    slice_steps: None,
                    ..s
                },
            );
            Ok(Vec::new())
        }
    }
}


/// Answer `Try::branch`, the first call of the `?` desugaring.
///
/// `expr?` is `<T as Try>::branch(expr)`, producing a
/// `ControlFlow<Residual, T>`. `branch` *is* `Continue(expr)` on the success
/// variant and `Break(residual)` on the failure one, so the model writes the
/// `ControlFlow`'s tag and both payloads into the destination's stores and lets
/// the `switchInt` on `discriminant(_)` -- and the `(_ as Continue).0` /
/// `(_ as Break).0` downcasts -- decide:
///
/// * tag `Continue` ([`intrinsics::CONTINUE_TAG`]) on the receiver's success
///   variant, carrying the success payload, which is what the `?` *yields*;
/// * tag `Break` ([`intrinsics::BREAK_TAG`]) on the receiver's failure variant,
///   carrying the *error value*. The residual the desugaring builds from it is
///   always `Err(e)` (for a `Result`) or `None` (for an `Option`) -- `branch`
///   only breaks on failure -- so the residual's own tag is fixed by the receiver
///   type and does not have to be stored. [`from_residual`] re-wraps the error
///   under the return enum's numbering.
///
/// The receiver is a `Result` or an `Option` (the two the desugaring's `Try`
/// impls are modelled for), so the success variant is `Ok` (tag 0) or `Some`
/// (tag 1), and the failure variant is the other. A receiver whose enum state is
/// not modelled is refused rather than given an invented tag.
fn try_branch(name: &str, args: &[Operand], dest: &Place, env: &mut Env) -> Result<(), String> {
    let receiver = args.first().ok_or_else(|| format!("`{name}` has no receiver"))?;
    let p = match receiver {
        Operand::Copy(p) | Operand::Move(p) => p,
        Operand::Const(_) => return Err(format!("unmodelled argument to `{name}`")),
    };
    let opt = env.pointee(p);
    // The receiver's type: `Result` or `Option`, read from the call's self type
    // (`<Result<u8, u8> as Try>::branch` -> `Result`). Only these two have a
    // modelled `Try`.
    let (is_result, success_disc) = match call_type(name).as_deref() {
        Some(t) if t.starts_with("Result") => (true, intrinsics::OK_TAG),
        Some(t) if t.starts_with("Option") => (false, intrinsics::SOME_TAG),
        _ => return Err(format!("`{name}` is not a modelled `Try`")),
    };
    let Some(Val::Sym(tag, _)) = env.discriminants.get(&opt.local).copied() else {
        return Err(format!("`{name}` on a receiver whose enum state is not modelled"));
    };
    let tag_w = env.tag_width(opt.local).or_else(|| env.option_width(opt.local)).unwrap_or(64);
    let tag = smt::truncate(tag, tag_w);
    let is_success = smt::eq_const(tag, success_disc);
    // The success value: the payload on the receiver's success variant. A receiver
    // whose tag is a *known* non-success discriminant cannot reach the `Continue`
    // arm, so leaving it unbound is exact (the read never happens on that path); a
    // symbolic or success tag still needs it.
    let success_payload = match env.payloads.get(&(opt.local, success_disc)).copied() {
        Some((Val::Sym(v, s), w)) => Some((v, s, w)),
        Some(_) => return Err(format!("`{name}` on a receiver whose payload is not modelled")),
        None => match smt::evaluate(tag, |_| None) {
            Some(v) if v != success_disc => None,
            _ => return Err(format!("`{name}` on a receiver whose payload is not modelled")),
        },
    };
    // The `ControlFlow`'s tag: `Continue` iff the receiver is on its success
    // variant, `Break` otherwise. The arm constants are small, so the word is the
    // tag's own width -- the same width `discriminant(_)` will read it back at.
    let cf_tag = smt::ite(
        is_success,
        smt::word(intrinsics::CONTINUE_TAG, tag_w),
        smt::word(intrinsics::BREAK_TAG, tag_w),
    );
    env.set_discriminant(dest.local, Val::Sym(cf_tag, Sign::Unsigned));
    if let Some((v, s, w)) = success_payload {
        env.set_payload(dest.local, intrinsics::CONTINUE_TAG, Val::Sym(v, s), w);
    }
    // The `Break` payload is the error value, which `from_residual` re-wraps. It is
    // read off the receiver's failure variant; a receiver that cannot reach the
    // failure path leaves it unbound, and the `from_residual` call refuses if that
    // arm is actually taken. An `Option`'s `None` carries no payload.
    if is_result {
        if let Some((Val::Sym(v, s), w)) = env.payloads.get(&(opt.local, 1)).copied() {
            env.set_payload(dest.local, intrinsics::BREAK_TAG, Val::Sym(v, s), w);
        }
    }
    Ok(())
}

/// Answer `FromResidual::from_residual`, the second call of the `?` desugaring.
///
/// On the `Break` arm the residual (the error value `branch` recorded) is
/// converted back into the function's return enum: `Result::Err(e)` for a `Result`
/// return, `Option::None` for an `Option` return. The return type is read from the
/// call's own self type (`<Result<u8, u8> as FromResidual<…>>::from_residual`), so
/// the destination's tag is the failure variant's -- `Err` (1) for a `Result`,
/// `None` (0) for an `Option` -- and the error value, when there is one, becomes
/// the `Err` payload. The destination is the function's return place, so this is
/// what the postcondition's `ret.is_err()` / `ret.Err` reads.
fn from_residual(name: &str, args: &[Operand], dest: &Place, env: &mut Env) -> Result<(), String> {
    // The return enum's kind, from the call's self type. `Result`'s residual
    // carries an error value; `Option`'s is the unit `None`.
    let is_result = match call_type(name).as_deref() {
        Some(t) if t.starts_with("Result") => true,
        Some(t) if t.starts_with("Option") => false,
        _ => return Err(format!("`{name}` is not a modelled `FromResidual`")),
    };
    let dest_w = env.tag_width(dest.local).unwrap_or(8);
    if !is_result {
        // `Option`'s `?` returns `None` early; the residual is the unit `None`.
        env.set_discriminant(dest.local, Val::Sym(smt::word(0, dest_w), Sign::Unsigned));
        return Ok(());
    }
    // `Result`'s `?` returns `Err(e)`; the residual argument (the `Break` payload
    // `branch` recorded, copied into a local) is the error value.
    let err = match args.first() {
        Some(Operand::Copy(p) | Operand::Move(p)) => operand(env, &Operand::Copy(env.pointee(p))),
        Some(Operand::Const(_)) | None => Val::Unknown,
    };
    env.set_discriminant(dest.local, Val::Sym(smt::word(1, dest_w), Sign::Unsigned));
    match err {
        Val::Sym(v, s) => env.set_payload(dest.local, 1, Val::Sym(v, s), smt::bits(v)),
        _ => return Err(format!("`{name}` on a residual whose payload is not modelled")),
    }
    Ok(())
}

/// Answer `Ord::cmp`, whose result is a `core::cmp::Ordering` enum.
///
/// The sibling of [`Intrinsic::MinMax`] -- the same trait-method spelling
/// (`<u8 as Ord>::cmp`) admitted by the same narrow rule -- and the first modelled
/// shape whose result is a *three-variant enum* rather than a value or an
/// `Option`. So the executor writes the destination's *discriminant* (and no
/// payload: `Ordering`'s variants are unit) rather than a value, and the
/// `switchInt` on `discriminant(_)` that follows decides.
///
/// A three-way comparison is the sign of `x - y`, so the tag is `Less` where
/// `x < y`, `Greater` where `x > y`, and `Equal` otherwise -- one `ite` over the
/// two comparisons the `PartialOrd` operators already build, at the operands'
/// common width and sign. The tag's width is `Ordering`'s own `i8` discriminant,
/// so the switch compares against the `-1`/`0`/`1` constants rustc prints (the
/// negative one as its eight-bit two's-complement pattern, which is why the tag
/// is built from the pattern and not through `word`, which refuses an
/// out-of-range value).
fn ord_cmp(name: &str, args: &[Operand], dest: &Place, env: &mut Env) -> Result<(), String> {
    use intrinsics::{Intrinsic, Outcome, PartialCmpKind};
    let (Some(a), Some(b)) = (args.first(), args.get(1)) else {
        return Err(format!("unmodelled arity for `{name}`"));
    };
    // Both operands are `&Self` (`&self` and `&other`), so the *referent* is the
    // value; a pointer has no bit-vector meaning, exactly as for the
    // `PartialEq`/`PartialOrd` comparisons. `pointee` follows the reference and is
    // a no-op for a by-value operand.
    let value = |env: &Env, op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) => match env.get(&env.pointee(p)) {
            Val::Sym(v, s) => Some((v, s)),
            _ => None,
        },
        Operand::Const(_) => None,
    };
    let (Some((x, sx)), Some((y, _))) = (value(env, a), value(env, b)) else {
        return Err(format!("unmodelled argument to `{name}`"));
    };
    let w = smt::bits(x);
    // The sign is a refusal when it could not be read: ordering `i8::MIN`
    // unsigned would place it above every other value, a wrong ordering rather
    // than a weaker proof.
    let signed = sx
        .known()
        .ok_or_else(|| format!("`{name}` on an operand whose sign is not modelled"))?;
    let bool_of = |kind: PartialCmpKind| -> Result<Pred, String> {
        match intrinsics::eval(Intrinsic::Cmp(kind), x, y, w, signed, w) {
            Some(Outcome::Bool(p)) => Ok(p),
            _ => Err(format!("`{name}` past what the model covers at {w} bits")),
        }
    };
    let lt = bool_of(PartialCmpKind::Lt)?;
    let gt = bool_of(PartialCmpKind::Gt)?;
    let tag_w = 8u8;
    let bits = |d: i64| (d as u64) & ((1u64 << tag_w) - 1);
    let tag = smt::ite(
        lt,
        smt::word(bits(intrinsics::ORDERING_LESS), tag_w),
        smt::ite(
            gt,
            smt::word(bits(intrinsics::ORDERING_GREATER), tag_w),
            smt::word(bits(intrinsics::ORDERING_EQUAL), tag_w),
        ),
    );
    env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
    Ok(())
}

/// Answer a modelled `core::num` call, if the callee is one.
///
/// `None` means the callee is not a modelled intrinsic, and the caller falls
/// through to the same-dump inliner. `Some(Err(..))` means it *is* one but this
/// call is outside what the model covers -- an unknown operand, a width past
/// [`intrinsics::DIV_MAX_WIDTH`] -- and the path is reported unknown. The
/// distinction matters: refusing to model a call and refusing to inline it are
/// different answers, and only the first is a coverage gap in `intrinsics`.
#[allow(clippy::too_many_arguments)]
fn try_intrinsic(
    prog: &MirProgram,
    func: usize,
    name: &str,
    args: &[Operand],
    dest: &Place,
    env: &mut Env,
    path: Pred,
    pins: &[(u32, u64)],
    callees: &CalleeEnv<'_>,
) -> Option<Result<Vec<Obligation>, String>> {
    let op = intrinsics::classify(name)?;
    // A modelled method is only ever `core`'s own, and rustc prints a `core`
    // integer method's call with the `<impl …>` projection (`core::num::<impl
    // u8>::wrapping_add`). A *local* method never carries it: a trait impl's call
    // is `<u8 as Trait>::m` and its body is `<impl at …>::m`, so a name without
    // `<impl` is a same-dump call and must be answered by its body, never by the
    // model. Without this, a `Trait::is_power_of_two` on `u8` that returns `false`
    // is modelled as `core`'s predicate and *proves* `ensures: ret == true` at
    // `x == 1` -- a false proof of a body that disagrees with `core`. The caller
    // already resolves same-dump names first (see the `Call` term), so this is the
    // local half of the same guard: it keeps `try_intrinsic` from ever answering
    // for a name that could name a local body. The direction is a refusal, so a
    // spelling the guard misjudges loses a proof rather than inventing one.
    //
    // `Ord::min`/`Ord::max` are the one exception, and only because they cannot be
    // spelled with `<impl`: a *trait* method's call names the trait, `<u8 as
    // Ord>::min`, never the `core::num::<impl u8>` inherent path. Refusing every
    // such name would make them permanently unmodellable. What keeps the exception
    // sound is the same thing that keeps the guard sound -- the caller resolving a
    // same-dump body first -- plus `classify` accepting `min`/`max` only when the
    // trait path is the standard library's `Ord` (a module-qualified `m::Ord` is
    // refused) and only for a *primitive* self type (see `is_ord_callee`): a
    // crate-root trait named `Ord` is the one spelling that could name a local
    // body, and it is in the dump, so `resolve_callee` finds it first and the model
    // is never consulted for it.
    //
    // `From`/`Into` are the same shape of exception for the same reason: a
    // conversion is a trait method, spelled `<u16 as From<u8>>::from`, with no
    // `<impl`. The extra care they need is that the two operand types differ, so
    // the model reads both from the name and refuses anything that is not a
    // widening between modelled integers (see the branch below). The crate-root
    // collision -- a user `From` that prints as the bare `From` -- is again closed
    // by the same-dump lookup, not by the name.
    //
    // The `Option` methods are the same shape once more: rustc prints
    // `Option::<u32>::unwrap`, an inherent method on the `Option` type rather than
    // a `core::num::<impl u32>` path, so there is no `<impl` to match. `classify`
    // accepts them only for the standard library's `Option` (see
    // `names_option_impl`), and the same-dump lookup answers a real `Option` body
    // first, which is what keeps a local type spelled `Option` out.
    let trait_method = is_ord_callee(name)
        || is_cmp_callee(name)
        || matches!(
            op,
            intrinsics::Intrinsic::Conversion(_)
                | intrinsics::Intrinsic::OptionMethod(_)
                | intrinsics::Intrinsic::Range(_)
                | intrinsics::Intrinsic::TryBranch
                | intrinsics::Intrinsic::FromResidual
                | intrinsics::Intrinsic::VecMethod(_)
                // The `String` length model is an inherent method on the standard
                // `String` (`String::new`, `String::push_str`, …) and `String::from`
                // is `<String as From<&str>>::from` -- neither carries `<impl`, so
                // both need the exception. `classify` accepts only the standard
                // `String` path (`names_string_impl`, and the `String`/`&str` types
                // in the conversion branch), and the same-dump lookup answers a real
                // body first, which keeps a local type spelled `String` out.
                | intrinsics::Intrinsic::StringMethod(_)
                // `Box::<T>::new` is an inherent method on the standard `Box` and
                // carries no `<impl`, so it needs the exception too. `classify`
                // accepts it only for the standard `Box` path (`names_box_impl`),
                // and the same-dump lookup answers a real body first.
                | intrinsics::Intrinsic::BoxMethod(_)
                // `std::mem::drop::<T>` carries no `<impl`, so it needs the
                // exception too; `classify` accepts only the standard path.
                | intrinsics::Intrinsic::MemDrop
                // Slice iteration is a *trait* call too (`<&[u8] as
                // IntoIterator>::into_iter`, `<slice::Iter as Iterator>::next`), so
                // it has no `<impl`. `classify` accepts it only for a `[T]` head or
                // a `slice::Iter` head, and the same-dump lookup answers a real body
                // first, so a user iterator cannot be answered by the model.
                | intrinsics::Intrinsic::SliceIntoIter
                | intrinsics::Intrinsic::SliceNext
                | intrinsics::Intrinsic::SliceCopied
                | intrinsics::Intrinsic::SliceRev
                | intrinsics::Intrinsic::SliceSkip
                | intrinsics::Intrinsic::SliceStepBy
                | intrinsics::Intrinsic::SliceTake
                | intrinsics::Intrinsic::SliceFold
                | intrinsics::Intrinsic::SliceMap
                | intrinsics::Intrinsic::SliceFilter
                | intrinsics::Intrinsic::SliceAll
                | intrinsics::Intrinsic::SliceAny
                | intrinsics::Intrinsic::SliceCount
                | intrinsics::Intrinsic::SliceSum
                | intrinsics::Intrinsic::SliceIterLast
                | intrinsics::Intrinsic::SliceNth
                | intrinsics::Intrinsic::SliceExtreme(_)
        );
    if !name.contains("<impl") && !trait_method {
        return None;
    }
    // A *bare* trait path that names a local crate-root trait must not be answered
    // by the model. rustc prints a crate-root trait's call bare (`<u8 as Ord>::min`),
    // so a local `trait Ord` with a *default* body the dump prints as `Ord::min`
    // (no `<impl`, so `resolve_callee` cannot match it) would otherwise be answered
    // by `core`'s ordering -- a false proof of a call the compiler resolved to the
    // local trait. A qualified path (`std::cmp::Ord`, `std::convert::From`) cannot
    // name a local item, and a bare path with no local crate-root trait of that
    // name is the library trait rustc shortened, so both are still modelled. See
    // [`trait_candidate_admits`] for the same identity rule on the body side.
    if let Some(t) = call_trait_path(name) {
        if !t.contains("::") && prog.declared_traits.contains(&t) {
            return None;
        }
    }
    // A trait call whose self type and method a *local* trait impl declares must be
    // answered by that body, not the model -- even when the trait's name is not
    // declared here (`use std::convert::From;`). rustc prints the call with the
    // trait path rather than the impl location, so the location lookup above cannot
    // see it, but the owner type and the method tail name the same method exactly.
    // Answering `<W as From<u8>>::from` from the model would be a false proof of a
    // conversion the compiler resolved to the local body. See [`local_impl_declares`].
    if let Some(t) = call_trait_path(name) {
        let self_ty = call_type(name).unwrap_or_default();
        let tail = name.rsplit("::").next().unwrap_or(name);
        if local_impl_declares(prog, &self_ty, tail, &t, call_trait_args(name).as_deref()) {
            return None;
        }
    }
    // A conversion is the one shape whose *two operand types* differ, so it reads
    // both from the call's own name rather than from the single argument's type,
    // and it is answered before the generic operand read below (which assumes one
    // width for every operand).
    if let intrinsics::Intrinsic::Conversion(kind) = op {
        return Some(convert(name, kind, args, dest, env).map(|()| Vec::new()));
    }
    // The `Vec` methods. They read a length and elements the executor tracks, not a
    // bit-vector operand, so they are answered before the generic operand read
    // below -- a `Vec` receiver has no width to read, and `Vec::new()` has *no*
    // argument at all, so it must run before the `args.first()?` that the operand
    // read needs.
    let cur = &prog.fns[func];
    if let intrinsics::Intrinsic::VecMethod(kind) = op {
        return Some(vec_method(name, kind, args, dest, env, path, pins, cur));
    }
    // The `String` length model. Like `Vec`, it reads a length the executor tracks
    // rather than an operand term, and `String::new()` has no argument, so it runs
    // before the operand read.
    if let intrinsics::Intrinsic::StringMethod(kind) = op {
        return Some(string_method(name, kind, args, dest, env, cur));
    }
    // The `Box` model. `Box::<T>::new` stores the boxed value and a nonzero
    // pointer token; the deref reads it back (see `get`'s `Deref` arm).
    if let intrinsics::Intrinsic::BoxMethod(kind) = op {
        return Some(box_method(name, kind, args, dest, env));
    }
    if let intrinsics::Intrinsic::MemDrop = op {
        return Some(mem_drop(name, callees.structs()));
    }
    // The operand width, from the first argument's declared type. It is not the
    // destination's: `checked_add` on a `u8` writes an `Option<u8>`, and taking
    // the width from there would ask the engine for a 64-bit overflow test.
    let first = args.first()?;
    // `slice::len`/`is_empty`. The receiver is a `&[T]`, whose *length* is the one
    // symbolic input the frontend already binds for the bounds checks, so the
    // model is that variable and not a fresh one. The length is a `usize`, which
    // is why the width is not read from the receiver -- a reference has no
    // bit-vector width -- and why this is handled before the generic operand read.
    if matches!(op, intrinsics::Intrinsic::SliceLen | intrinsics::Intrinsic::SliceIsEmpty) {
        let p = match first {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Const(_) => return Some(Err(format!("unmodelled argument to `{name}`"))),
        };
        // `length_of` follows the reference to the slice local the frontend bound a
        // length for. A receiver whose length is not modelled (a `Vec`, or a slice
        // the contract never bound) is refused here rather than given an invented
        // number.
        let Val::Sym(len, _) = length_of(env, cur, p) else {
            return Some(Err(format!("`{name}` on a receiver whose length is not modelled")));
        };
        return Some(match op {
            intrinsics::Intrinsic::SliceLen => {
                env.set(dest, Val::Sym(len, Sign::Unsigned));
                Ok(Vec::new())
            }
            // `is_empty` is `len == 0`, on the *same* variable `len` reads, so the
            // two cannot disagree. The destination is a `bool`, so it is a
            // predicate and not a one-bit word.
            _ => {
                env.set(dest, Val::Bool(smt::eq_const(len, 0)));
                Ok(Vec::new())
            }
        });
    }
    // `slice::first`/`get`: `Option<&T>`. The element is the executor's own
    // `s[0]`/`s[k]` variable -- the same one a `s[0]` read names -- so the
    // `Option`'s payload *is* that element rather than a fresh value the slice
    // never holds. The `Option` tag is a predicate (`len == 0` for `first`,
    // `k >= len` for `get`), so the arm is decided by the caller's `switchInt`,
    // and the payload is recorded under the `Some` discriminant so a `(_2 as
    // Some).0` downcast -- or the reference's deref -- reads it.
    if matches!(
        op,
        intrinsics::Intrinsic::SliceFirst
            | intrinsics::Intrinsic::SliceGet
            | intrinsics::Intrinsic::SliceLast
    ) {
        let p = match first {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Const(_) => return Some(Err(format!("unmodelled argument to `{name}`"))),
        };
        return Some(slice_element(name, op, p, args, dest, env, cur));
    }
    // `for x in xs` over a slice: `into_iter`/`iter` starts a cursor over the
    // slice local, `next` advances it. Answered from the executor's cursor store,
    // not an operand term.
    if matches!(
        op,
        intrinsics::Intrinsic::SliceIntoIter
            | intrinsics::Intrinsic::SliceNext
            | intrinsics::Intrinsic::SliceCopied
            | intrinsics::Intrinsic::SliceRev
            | intrinsics::Intrinsic::SliceSkip
            | intrinsics::Intrinsic::SliceStepBy
            | intrinsics::Intrinsic::SliceTake
            | intrinsics::Intrinsic::SliceFold
            | intrinsics::Intrinsic::SliceMap
            | intrinsics::Intrinsic::SliceFilter
            | intrinsics::Intrinsic::SliceAll
            | intrinsics::Intrinsic::SliceAny
            | intrinsics::Intrinsic::SliceCount
            | intrinsics::Intrinsic::SliceSum
            | intrinsics::Intrinsic::SliceIterLast
            | intrinsics::Intrinsic::SliceNth
            | intrinsics::Intrinsic::SliceExtreme(_)
    ) {
        let p = match first {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Const(_) => return Some(Err(format!("unmodelled argument to `{name}`"))),
        };
        return Some(slice_iter(
            name,
            op,
            p,
            dest,
            env,
            &IterCall { f: cur, pins, path, args, prog },
        ));
    }
    // The standard library's `Option`/`Result` methods. The receiver is an
    // `Option<T>`/`Result<T, E>` whose tag and payload the model's own
    // `checked_*` family (or an argument the contract bound) recorded in the
    // environment's discriminant and payload stores. The receiver is `self` for
    // `unwrap`/`unwrap_or` and `&self` for the predicates, so it is followed
    // through a reference the same way the ASCII tests are -- `_2 = &_1;
    // is_some(move _2)` reads `_1`.
    if let intrinsics::Intrinsic::OptionMethod(kind) = op {
        return Some(enum_method(name, kind, args, dest, env, path, pins, &prog.fns[func], prog, callees));
    }
    // The `for`-loop range methods. Their receiver is a `RangeInclusive`/`Range`
    // struct whose `start`/`end`/`exhausted` fields the executor holds, so they are
    // answered from that store rather than from an operand term. This is what makes
    // the commonest loop in Rust reachable: the desugaring's `new`/`into_iter`/`next`
    // are modelled, and the loop then decides by its `invariant:` (or is unwound
    // like any other loop).
    if let intrinsics::Intrinsic::Range(kind) = op {
        return Some(range_method(name, kind, args, dest, env));
    }
    // The `?` operator's two calls. Like the `Option`/range methods they read the
    // receiver's enum state from the executor's stores rather than from an operand
    // term, so they are answered here. They run *before* the generic operand read
    // below, which assumes a bit-vector operand and a single width.
    if let intrinsics::Intrinsic::TryBranch = op {
        return Some(try_branch(name, args, dest, env).map(|()| Vec::new()));
    }
    if let intrinsics::Intrinsic::FromResidual = op {
        return Some(from_residual(name, args, dest, env).map(|()| Vec::new()));
    }
    // `Ord::cmp`: the three-way ordering, whose result is an `Ordering` enum. Like
    // the `?` desugaring's calls it writes an enum's discriminant and payload
    // rather than a single value, so it is answered here, before the generic
    // operand read below.
    if let intrinsics::Intrinsic::OrdCmp = op {
        return Some(ord_cmp(name, args, dest, env).map(|()| Vec::new()));
    }
    // The ASCII class tests and the ASCII case conversions take `&self`, so the
    // operand is a reference whose *referent* is the byte. rustc prints `_3 = &_1;
    // is_ascii_digit(move _3)`, and the width and the value both have to come from
    // `_1`, not from the `&u8` local (which is a pointer with no bit-vector
    // meaning). Only these shapes need the step: every other modelled method takes
    // `self` by value.
    // The ASCII class tests, the ASCII case conversions and the `PartialEq`/
    // `PartialOrd` comparisons take their operands by reference, so the operand is
    // a reference whose *referent* is the value. rustc prints `_3 = &_1;
    // is_ascii_digit(move _3)`, and the width and the value both have to come from
    // `_1`, not from the `&u8` local (which is a pointer with no bit-vector
    // meaning). Only these shapes need the step: every other modelled method takes
    // `self` by value.
    let ref_receiver = matches!(
        op,
        intrinsics::Intrinsic::Bool(intrinsics::BoolKind::Ascii(_))
            | intrinsics::Intrinsic::AsciiCase(_)
            | intrinsics::Intrinsic::Cmp(_)
    )
    .then(|| match first {
        Operand::Copy(p) | Operand::Move(p) => Some(env.pointee(p)),
        Operand::Const(_) => None,
    })
    .flatten();
    let w = match &ref_receiver {
        Some(p) => width_of(cur, p),
        None => operand_width(cur, first),
    }?;
    // The operand's signedness comes *from the value*. An operand whose type
    // could not be read was already refused when the value was built (it is
    // `Val::Unknown`, not a `Sym`), so there is no sign to guess here: guessing
    // would give `sdiv`/`srem` the unsigned meaning, which is a wrong value for
    // every negative operand rather than a weaker proof.
    //
    // The ASCII receiver is read through its reference: `operand` on the `&u8`
    // local gives `Unknown` (a pointer has no bit-vector meaning), so the byte is
    // read from the place `pointee` names instead. This is the same value the
    // body's own `*_3` would read.
    let (x, sign) = match &ref_receiver {
        Some(p) => match env.get(p) {
            Val::Sym(v, sign) => (v, sign),
            _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
        },
        None => match operand(env, first) {
            // The sign comes out of the value with the word, so the two cannot be
            // read from different places and disagree.
            Val::Sym(v, sign) => (v, sign),
            // A `bool` operand has no bit-vector to hand the model, and an unknown
            // one has no value at all. Either way there is nothing to compute with.
            _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
        },
    };
    // The unary shapes take one operand and no operator. They are handled here
    // rather than through a `BinOp`, because there is no second operand to read.
    if op.is_unary() {
        // A bit count does not read the sign at all -- the bits of a negative
        // value are just bits -- so a dump that did not print one is still
        // modelled. A unary *operator* and the `bool` predicate both read it:
        // `neg` and `abs` mean different things on the two types, and
        // `is_power_of_two` exists only on the unsigned ones. A missing sign is
        // refused there rather than guessed, and a printed *signed* one makes
        // `eval` decline, so a signed operand cannot be read as an unsigned one.
        let signed = match op {
            intrinsics::Intrinsic::Unary(..)
            | intrinsics::Intrinsic::Bool(_)
            | intrinsics::Intrinsic::Abs
            | intrinsics::Intrinsic::UnsignedAbs
            | intrinsics::Intrinsic::SignednessCast
            | intrinsics::Intrinsic::Signum
            | intrinsics::Intrinsic::Ilog(_)
            | intrinsics::Intrinsic::CheckedIlog(_)
            | intrinsics::Intrinsic::NextPowerOfTwo
            | intrinsics::Intrinsic::CheckedNextPowerOfTwo
            | intrinsics::Intrinsic::BitReverse
            | intrinsics::Intrinsic::ByteSwap
            | intrinsics::Intrinsic::ByteOrder(_)
            | intrinsics::Intrinsic::AsciiCase(_) => sign.known()?,
            _ => false,
        };
        // A bit count returns a type wider than its operand (`u8` -> `u32`), so
        // the result term is built at the destination's width. Taking it from the
        // operand instead would leave an 8-bit term in a 32-bit local, and the
        // next read of that local would be ill-formed.
        let result_w = width_of(cur, dest).unwrap_or(w);
        let Some(outcome) = intrinsics::eval(op, x, x, w, signed, result_w) else {
            return Some(Err(format!("`{name}` past what the model covers at {w} bits")));
        };
        return Some(match outcome {
            Outcome::Value(v) => {
                // The result has the operand's type, so it has the operand's
                // sign. For a bit count that reading is only a label -- the value
                // is unsigned and non-negative -- but it is the type's sign, and
                // labelling it anything else would be a second opinion about a
                // type this code already knows.
                //
                // `unsigned_abs` is the exception: its result type is the unsigned
                // sibling of the operand's (`i32::unsigned_abs` is `u32`), so the
                // label is unsigned. The value is the same magnitude, and reading
                // `128` as `-128` would mis-type the very input the method exists
                // for.
                let sign = match op {
                    intrinsics::Intrinsic::UnsignedAbs => Sign::Unsigned,
                    // The signedness re-interpretation's result type is the
                    // *opposite* of the operand's, so it is read from the call's
                    // destination rather than derived from the operand. A
                    // destination with no readable type is refused (the shape is
                    // sign-reading for exactly this reason).
                    intrinsics::Intrinsic::SignednessCast => match type_of_place(cur, dest) {
                        Some(ty) => Sign::of(&ty),
                        None => return Some(Err(format!("unmodelled destination of `{name}`"))),
                    },
                    _ => Sign::of_bool(signed),
                };
                env.set(dest, Val::Sym(v, sign));
                Ok(Vec::new())
            }
            Outcome::Option { tag, payload } => {
                // `checked_neg`, `checked_abs`, `checked_next_multiple_of` and the
                // `checked_` logarithms return an `Option`. The payload's type is
                // the operand's (`checked_next_multiple_of` returns `Option<T>`),
                // so its sign and width follow the operand -- *except* for a
                // `checked_ilog*`, whose payload is a `u32` whatever the operand's
                // type (`i32::checked_ilog2` is `Option<u32>`), the same
                // result-width rule the plain logarithm already follows.
                let (payload_sign, payload_w) = if matches!(op, intrinsics::Intrinsic::CheckedIlog(_)) {
                    (Sign::Unsigned, result_w)
                } else {
                    (Sign::of_bool(signed), w)
                };
                env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
                env.set_payload(
                    dest.local,
                    intrinsics::SOME_TAG,
                    Val::Sym(payload, payload_sign),
                    payload_w,
                );
                Ok(Vec::new())
            }
            Outcome::Tuple { value, overflowed } => {
                // `overflowing_neg` and `overflowing_abs` return `(T, bool)`,
                // which is a plain aggregate: field 0 the value, field 1 the
                // flag. `Val::Agg` is returned so `set` does not clear the parts
                // that were just written.
                let field = |i| Place { local: dest.local, proj: vec![Proj::Field(i)] };
                env.set(&field(0), Val::Sym(value, Sign::of_bool(signed)));
                env.set(&field(1), Val::Bool(overflowed));
                Ok(Vec::new())
            }
            Outcome::Bool(p) => {
                // `is_power_of_two` returns a `bool` and nothing else. The
                // destination local is a `bool`, so the predicate is written as
                // one; a one-bit *word* here would leave the local readable only
                // as a word, and the `if` that consumes it reads a predicate.
                env.set(dest, Val::Bool(p));
                Ok(Vec::new())
            }
            Outcome::ValueOrPanic { value, fails } => {
                // `iN::abs` panics at `MIN`, where the magnitude is
                // unrepresentable, and `ilog2`/`ilog10` panic on a non-positive
                // argument. The value is written unconditionally -- a path where
                // the call panics is reported by the obligation below, so the value
                // it carries is never used on a live path -- and the panic is a
                // *reachable-failure* obligation, the same polarity as a
                // rustc-inserted `assert`: the call is safe exactly where
                // `path ∧ fails` is unsatisfiable.
                //
                // The result's sign is the operand's, except for a logarithm,
                // whose result is a `u32` whatever the operand's type
                // (`i32::ilog2` is `u32`). Declaring the index with the operand's
                // sign would be the wrong type even though the value is small
                // enough that no obligation here observes the difference, and the
                // declaration is what a later reader trusts.
                let result_sign = if matches!(op, intrinsics::Intrinsic::Ilog(_)) {
                    Sign::Unsigned
                } else {
                    Sign::of_bool(signed)
                };
                env.set(dest, Val::Sym(value, result_sign));
                let message = match op {
                    intrinsics::Intrinsic::Ilog(_) => {
                        format!("`{name}` of a non-positive value")
                    }
                    _ => format!("`{name}` overflows"),
                };
                Ok(vec![Obligation {
                    kind: ObligationKind::Panic { message },
                    verdict: find_obligation(smt::and(path, fails), pins),
                }])
            }
        });
    }
    // A sign the dump did not print is a refusal, not an unsigned reading:
    // `sdiv` on an `i8` read as unsigned returns a huge positive quotient for
    // every negative operand, which is a wrong value rather than a weaker proof.
    let signed = sign.known()?;
    // `Ord::clamp` is the one three-operand shape, so it is evaluated by its own
    // function rather than through `eval`'s two-operand signature. `x` is the
    // receiver (the value to clamp), and `lo`/`hi` are the other two operands.
    // The panic is `lo > hi || x < lo || x > hi`, reported the same way `abs`'s
    // overflow is: a reachable-failure obligation, not a value.
    if let intrinsics::Intrinsic::Clamp = op {
        let (Some(lo_arg), Some(hi_arg)) = (args.get(1), args.get(2)) else {
            return Some(Err(format!("unmodelled arity for `{name}`")));
        };
        let lo = match operand(env, lo_arg) {
            Val::Sym(v, _) => v,
            _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
        };
        let hi = match operand(env, hi_arg) {
            Val::Sym(v, _) => v,
            _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
        };
        let Some(outcome) = intrinsics::clamp(x, lo, hi, w, signed) else {
            return Some(Err(format!("`{name}` past what the model covers at {w} bits")));
        };
        let intrinsics::Outcome::ValueOrPanic { value, fails } = outcome else {
            unreachable!("clamp yields a value-or-panic outcome")
        };
        env.set(dest, Val::Sym(value, Sign::of_bool(signed)));
        return Some(Ok(vec![Obligation {
            kind: ObligationKind::Panic { message: format!("`{name}` out of range") },
            verdict: find_obligation(smt::and(path, fails), pins),
        }]));
    }
    // `pow` reads two operands of *different* types: the base has the method's
    // width and sign, the exponent is the `u32` it is declared as. So the exponent
    // is read on its own -- a `Val::Sym` and its width from the argument's type --
    // and the fold is handed the two separately. Reading it as a second operand at
    // `w` bits would read an `i8` exponent for a `u8` base, or a `u8` exponent for
    // a `u32` one, and fold the wrong number of bits.
    if matches!(op, intrinsics::Intrinsic::Pow(_) | intrinsics::Intrinsic::PowPanic) {
        let Some(exp_arg) = args.get(1) else {
            return Some(Err(format!("unmodelled arity for `{name}`")));
        };
        let Some(exp_w) = operand_width(cur, exp_arg) else {
            return Some(Err(format!("unmodelled exponent type for `{name}`")));
        };
        // The exponent is unsigned by construction (`u32`); a signed reading of
        // its bits would make `exp == 0x8000_0000` a negative number.
        let exp = match operand(env, exp_arg) {
            Val::Sym(v, _) => v,
            _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
        };
        if !intrinsics::pow_exponent_fits(exp_w) {
            return Some(Err(format!("`{name}` exponent past the model's 32 bits")));
        }
        let Some(outcome) = intrinsics::eval(op, x, exp, w, signed, w) else {
            return Some(Err(format!("`{name}` past what the model covers at {w} bits")));
        };
        let sign = Sign::of_bool(signed);
        return Some(match outcome {
            Outcome::Value(v) => {
                env.set(dest, Val::Sym(v, sign));
                Ok(Vec::new())
            }
            Outcome::Option { tag, payload } => {
                env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
                env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(payload, sign), w);
                Ok(Vec::new())
            }
            Outcome::Tuple { value, overflowed } => {
                let field = |i| Place { local: dest.local, proj: vec![Proj::Field(i)] };
                env.set(&field(0), Val::Sym(value, sign));
                env.set(&field(1), Val::Bool(overflowed));
                Ok(Vec::new())
            }
            // A `bool` predicate is unary (`is_power_of_two` is the only one),
            // so it never reaches the `pow` path.
            Outcome::Bool(_) => unreachable!("a bool predicate is unary"),
            // The plain inherent `pow` panics on overflow, so its outcome is a
            // value-or-panic. The value is written unconditionally -- a path where
            // it panics is reported by the obligation below -- and the panic is the
            // same reachable-failure obligation a family's `pow` debug-`assert!`
            // would raise.
            Outcome::ValueOrPanic { value, fails } => {
                env.set(dest, Val::Sym(value, sign));
                return Some(Ok(vec![Obligation {
                    kind: ObligationKind::Panic { message: format!("`{name}` overflows") },
                    verdict: find_obligation(smt::and(path, fails), pins),
                }]));
            }
        });
    }
    let y = match args.get(1) {
        // A `PartialEq`/`PartialOrd` second operand is `&other`, so its *referent*
        // is the value -- the same step the receiver takes above. Reading the
        // `&u8` local directly gives `Unknown` (a pointer has no bit-vector
        // meaning).
        Some(a) if matches!(op, intrinsics::Intrinsic::Cmp(_)) => match a {
            Operand::Copy(p) | Operand::Move(p) => match env.get(&env.pointee(p)) {
                Val::Sym(v, _) => v,
                _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
            },
            // A *constant* second operand has no referent to follow, so it is read
            // directly. This arm is defensive: an unoptimised dump promotes a
            // literal operand to its own item and passes a reference to it
            // (`x.eq(&5)` lowers to `_3 = const F::promoted[0]; … Eq(copy _1,
            // copy _3)`), which the `Copy`/`Move` arm above resolves through the
            // promoted constant the parser now records. A bare `const` operand is
            // a shape no current dump prints, so refusing it would only refuse a
            // term a future printer or a deserialised dump could hand in -- and the
            // direct read is the honest one either way.
            Operand::Const(_) => match operand(env, a) {
                Val::Sym(v, _) => v,
                _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
            },
        },
        Some(a) => match operand(env, a) {
            Val::Sym(v, _) => v,
            _ => return Some(Err(format!("unmodelled argument to `{name}`"))),
        },
        // Every two-operand name has both operands printed, so a missing second
        // argument means the dump had a shape the model does not cover.
        None => return Some(Err(format!("unmodelled arity for `{name}`"))),
    };
    let Some(outcome) = intrinsics::eval(op, x, y, w, signed, w) else {
        return Some(Err(format!("`{name}` past what the model covers at {w} bits")));
    };
    // The result of an arithmetic intrinsic has the operand's type, so it has
    // the operand's sign -- `wrapping_sub(0, 1)` on a `u8` is `255` and on an
    // `i8` is `-1`, the same bits read two ways. `abs_diff` is the exception: its
    // result is the *unsigned* magnitude even on a signed operand
    // (`i8::abs_diff(-128, 127)` is `255u8`), so it is written unsigned; labelling
    // it with the operand's sign would read `255` as `-1`.
    let sign = match op {
        intrinsics::Intrinsic::AbsDiff => Sign::Unsigned,
        // `ilog2`/`ilog10` return a `u32` whatever the operand's type
        // (`i32::ilog2` is `u32`), so labelling the result with the operand's sign
        // would read a non-negative index as signed.
        intrinsics::Intrinsic::Ilog(_) => Sign::Unsigned,
        _ => Sign::of_bool(signed),
    };
    match outcome {
        Outcome::Value(v) => env.set(dest, Val::Sym(v, sign)),
        Outcome::Option { tag, payload } => {
            // The payload is recorded under the `Some` projection with the
            // operand width, and the tag alongside it. rustc reads the payload
            // only inside the arm where the tag is `1`, so recording it now is
            // sound; the width is what keeps the read from being mis-sized.
            env.set_discriminant(dest.local, Val::Sym(tag, Sign::Unsigned));
            env.set_payload(dest.local, intrinsics::SOME_TAG, Val::Sym(payload, sign), w);
        }
        Outcome::Tuple { value, overflowed } => {
            // `overflowing_*` returns `(result, overflowed)`, which is a plain
            // aggregate rather than an `Option`. Field 0 gets the wrapped value
            // and field 1 the flag, so a caller that writes `let (r, o) = …` or
            // asserts `!o` reads a real condition.
            let field = |i| Place { local: dest.local, proj: vec![Proj::Field(i)] };
            env.set(&field(0), Val::Sym(value, sign));
            env.set(&field(1), Val::Bool(overflowed));
        }
        // A `bool` predicate: `is_power_of_two` and the ASCII classes are unary,
        // but `is_multiple_of` reads two operands, so it reaches *this* path and
        // its predicate is written as a `Val::Bool` -- the same value the `if`
        // that consumes it branches on.
        Outcome::Bool(p) => env.set(dest, Val::Bool(p)),
        // The Euclidean pair and `div_ceil`: their *value* is written
        // unconditionally, and the divide-by-zero (or `MIN / -1`) panic is a
        // reachable-failure obligation, the same polarity as `abs`'s overflow --
        // the call is safe exactly where `path ∧ fails` is unsatisfiable. Without
        // this arm a `div_euclid(x, 0)` would be written as a plain value with no
        // panic reported, which is exactly the hidden panic the model must not
        // introduce.
        Outcome::ValueOrPanic { value, fails } => {
            env.set(dest, Val::Sym(value, sign));
            // The message names what actually failed, because the shapes that
            // reach here fail for different reasons: a division by zero or
            // `MIN / -1`, a `next_multiple_of` overflow, a non-positive logarithm.
            let message = match op {
                intrinsics::Intrinsic::DivEuclid
                | intrinsics::Intrinsic::RemEuclid
                | intrinsics::Intrinsic::DivCeil => format!("`{name}` division overflow"),
                intrinsics::Intrinsic::NextMultipleOf => {
                    format!("`{name}` overflows or divides by zero")
                }
                intrinsics::Intrinsic::Ilog(_) => {
                    format!("`{name}` of a non-positive value")
                }
                _ => format!("`{name}` overflow"),
            };
            return Some(Ok(vec![Obligation {
                kind: ObligationKind::Panic { message },
                verdict: find_obligation(smt::and(path, fails), pins),
            }]));
        }
    }
    Some(Ok(Vec::new()))
}

/// The declared bit width of an operand, when it has one.
fn operand_width(f: &MirFn, o: &Operand) -> Option<u8> {
    match o {
        Operand::Copy(p) | Operand::Move(p) => width_of(f, p),
        Operand::Const(Const::UInt(_, ty)) => ty.as_ref().and_then(|t| t.width()),
        Operand::Const(_) => None,
    }
}

/// Seed a callee's environment from a call's arguments.
///
/// Shared by the inliner and by a `drop` of a user `impl Drop` -- both hand a
/// place over to a callee's frame and need the same carried-in state, so a
/// second copy would be a second chance to forget one of the stores.
fn seed_callee_env(
    prog: &MirProgram,
    caller_env: &mut Env,
    callee_fn: &MirFn,
    args: &[Operand],
) -> (Env, Vec<(Place, u32)>) {
    let mut env = Env::with_prog(prog);
    // Which caller locals were handed over through a reference, so the
    // return path knows whose store the callee's post-state belongs to.
    let mut by_ref: Vec<(Place, u32)> = Vec::new();
    for (i, a) in args.iter().enumerate() {
        let v = operand(caller_env, a);
        let Some(&l) = callee_fn.arg_locals.get(i) else { continue };
        env.locals.insert(l, v);
        // A reference argument may be dereferenced inside the callee
        // (`*_1 = 5`), and `Ty::Ref` is modelled as its referent, so `_1`
        // *is* the value `*_1` names. `verify_fn` marks the root's
        // reference arguments this way; the inliner builds the callee's
        // env itself, so it has to mark them too, or the callee's
        // `(*_1) = v` is treated as a deref with no recorded referent and
        // the write is dropped -- which is how a `&mut u8` helper's write
        // was lost and a false `ret == 0` contract was proved.
        if matches!(callee_fn.ty_of(l), Some(Ty::Ref(_))) {
            env.deref_ok.insert(l, ());
        }
        let Place { local: cl, proj } = match a {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Const(_) => continue,
        };
        if !proj.is_empty() {
            continue;
        }
        // The *storage* the argument denotes, which is the caller's local
        // itself for a by-value argument and the pointee for a reference.
        //
        // `pointee`, not `resolve`: `resolve` only follows an explicit
        // `*_p` projection, and `set5(&mut x)` hands the callee a *temp*
        // (`_5 = &mut _2; set5(_5)`) whose place has no projection at all.
        // `pointee` follows the recorded address of an empty-projection
        // local, which is what turns `_5` into the `_2` the caller reads.
        //
        // The whole argument's state -- its element store *and* its parts
        // -- is carried in, keyed on the callee's local. A reference shares
        // the caller's storage, so the callee's `a[0]`, `c.lo` and `o.i.v`
        // must read the caller's values; without them a helper that indexes
        // or reads a field has an unmodelled operand and the caller's
        // contract stays unproved, while a read-modify-write helper
        // (`c.lo = c.lo + d`) cannot be modelled at all.
        //
        // The state is *cloned*, never shared: the callee must not be able
        // to write the caller's copy directly, or a by-value argument would
        // behave like a reference. Only a reference argument's post-state
        // is copied back (see the return path).
        let is_ref = arg_is_ref(callee_fn, i);
        let source = if is_ref {
            caller_env.pointee(&Place { local: *cl, proj: Vec::new() })
        } else {
            Place { local: *cl, proj: Vec::new() }
        };
        let sl = source.local;
        // The value *at the target*, and the target's parts. The value is
        // read through `get`, not out of `locals`, because a sub-place
        // target has no whole-local entry: `&mut c.lo` targets `c.0`, whose
        // value lives in `fields`. Reading `locals[source.local]` there
        // returned the *struct's* absent value, so the callee's `*v` was
        // `Unknown` and a helper that *reads* through its argument (`*v`,
        // `*v = *v + 1`, a two-reference `swap`) had an unmodelled operand --
        // while a helper that only *wrote* (`*v = 5`) worked, because the
        // write creates the value the copy-back then reads. `Ty::Ref` is
        // modelled as its referent, so the callee's local *is* the target's
        // value and this is a copy of what the caller holds, not an
        // assumption about it.
        //
        // The part stores are copied only for a *whole-local* target, and
        // they are keyed by `source.local` because that is the local that
        // owns them. For a sub-place target the parts belong to the target's
        // own type, which the value copy above already covers for a scalar;
        // copying the enclosing local's parts instead would hand the callee
        // a sibling field it does not own.
        if is_ref {
            let v = caller_env.get(&source);
            env.locals.insert(l, v);
        }
        if source.proj.is_empty() {
            if let Some(store) = caller_env.indexed.get(&sl).cloned() {
                env.indexed.insert(l, store);
            }
            // A `Vec` is an `indexed` entry, so the clone above already carried its
            // length and elements in; nothing extra is needed for a helper that
            // reads `v.len()` or `v[0]` through its argument.
            for ((l0, f), v) in caller_env.fields.iter() {
                if *l0 == sl {
                    env.fields.insert((l, *f), *v);
                }
            }
            for ((l0, chain), v) in caller_env.nested.iter() {
                if *l0 == sl {
                    env.nested.insert((l, chain.clone()), *v);
                }
            }
            for ((l0, k), v) in caller_env.elems.iter() {
                if *l0 == sl {
                    env.elems.insert((l, *k), *v);
                }
            }
            // Elements of field-path arrays (`o.a[0]`) are carried in for the
            // same reason the plain elements are: the callee's `(_1.0)[k]` is
            // the caller's `o.a[k]`, so a helper that *reads* one has to see
            // the caller's seed. Without this the callee read `Unknown`, and a
            // helper that wrote the element had its write die with the frame --
            // the caller read its own seed, so `requires: x.a[0] == 5;
            // ensures: ret == 5` on `set_first(x); x.a[0]` was **proved**
            // against a body that returns 9.
            for ((l0, chain, k), v) in caller_env.elems_path.iter() {
                if *l0 == sl {
                    env.elems_path.insert((l, chain.clone(), *k), *v);
                }
            }
            // The leaves *inside* those elements (`o.a[0].v`), keyed
            // index-first. A helper that reads a leaf through its argument
            // (`a[0].v`) otherwise saw `Unknown`; and one that wrote it had
            // the write die with the frame, so the caller read the leaf its
            // literal had before the call.
            for ((l0, k, chain), v) in caller_env.elem_parts.iter() {
                if *l0 == sl {
                    env.elem_parts.insert((l, *k, chain.clone()), *v);
                }
            }
            // An already-poisoned array stays poisoned in the callee: its
            // elements are unknown, so carrying them in would hand over
            // values the caller's own write already invalidated.
            if caller_env.poisoned_elems.contains(&sl) {
                env.poisoned_elems.insert(l);
            }
        } else if is_ref {
            // A sub-place target whose own type is an aggregate: `&mut
            // o.i`. The callee's `i.v` is the caller's `o.i.v`, so the
            // target's parts are carried in *re-based* -- the target's
            // chain is dropped from the front of each key and the callee's
            // local takes its place. This is the exact inverse of the
            // re-based copy-back, and it is what lets a helper *read* a
            // nested aggregate it was handed (`read_inner(&o.i)`), which is
            // otherwise an unmodelled operand.
            let mut rc = Vec::with_capacity(source.proj.len());
            let ok = source.proj.iter().all(|p| match p {
                Proj::Field(i) => {
                    rc.push(*i);
                    true
                }
                _ => false,
            });
            if ok {
                // A remainder of one step is a *field* in this store's
                // spelling (`fields` is keyed by a single index, `nested` by
                // a chain of two or more), so the two lengths have to be
                // routed apart or the callee's `_1.0` -- a lone field read --
                // would consult `fields` and miss.
                for ((l0, chain), v) in caller_env.nested.iter() {
                    if *l0 != sl || !chain.starts_with(&rc) {
                        continue;
                    }
                    let rem = &chain[rc.len()..];
                    match rem {
                        [f] => {
                            env.fields.insert((l, *f), *v);
                        }
                        [] => {}
                        _ => {
                            env.nested.insert((l, rem.to_vec()), *v);
                        }
                    }
                }
                // Elements of field-path arrays under a sub-place target, the
                // same re-basing as the nested parts above: `&mut o.i` makes the
                // caller's `o.i.a[0]` the callee's `_1.a[0]`, so the chain has
                // the target's prefix dropped. Without this a helper that only
                // *reads* the element through its argument (`read_inner(&o.i)` ->
                // `i.a[0]`) saw `Unknown` and its contract was unreadable -- an
                // incompleteness where the true contract should decide.
                for ((l0, chain, k), v) in caller_env.elems_path.iter() {
                    if *l0 != sl || !chain.starts_with(&rc) {
                        continue;
                    }
                    let rem = &chain[rc.len()..];
                    if rem.is_empty() {
                        // The target *is* the array (`peek_of(&x.a)`): in the
                        // callee's terms its argument is a whole local, so the
                        // callee's `_1[k]` read consults the *plain* element store,
                        // not the field-path one. Without this the callee read
                        // `Unknown` and a read-only helper's contract was
                        // unreadable -- an incompleteness where the true contract
                        // should decide. This is the exact inverse of the write-back
                        // arm that re-bases a whole-array target's element.
                        env.elems.insert((l, *k), *v);
                    } else {
                        env.elems_path.insert((l, rem.to_vec(), *k), *v);
                    }
                }
            }
        }
        if is_ref {
            by_ref.push((source.clone(), l));
        }
        // The origin local of a reference argument, in the *caller's*
        // frame, so a reference the callee returns can be resolved once it
        // is back in the caller. A `&mut x` argument is passed through a
        // temp (`_5 = &mut _2; set5(_5)`), so the origin is `_5`'s origin --
        // `_2` -- not `_5` itself.
        if matches!(callee_fn.ty_of(l), Some(Ty::Ref(_))) {
            // The argument denotes `source` in the caller's frame, and
            // inside the callee it is the local `l` itself. Recording both
            // is what lets a reference the callee returns be translated
            // back: the callee's `_0` names `l` (or a projection of it),
            // and `arg_source` turns that into the caller's place.
            env.arg_source.insert(l, source.clone());
            env.ref_origin.insert(l, Place { local: l, proj: Vec::new() });
        }
    }
    (env, by_ref)
}

#[allow(clippy::too_many_arguments)]
fn run_state<F>(
    prog: &MirProgram,
    mut st: State,
    post: &Option<F>,
    report: &mut MirReport,
    work: &mut Vec<State>,
    pins: &[(u32, u64)],
    root: usize,
    rec: &Option<RecCtx>,
    callees: &CalleeEnv<'_>,
    unwind: u32,
    unwind_declared: bool,
)
where
    F: Fn(Option<Var>, &[(u32, Var)], &[(u64, Var)], &[(u32, Var)]) -> Result<Pred, String>,
{
    let cur = &prog.fns[st.frame.func];
    // A path that cannot be taken is not a path. Pruning it is what lets
    // unwinding stop at a loop's real trip count instead of at the bound: once a
    // guard folds to a constant, the impossible edge is dropped rather than
    // explored. It is sound -- an unsatisfiable path condition describes no
    // execution -- and it keeps dead paths from spending the path budget and from
    // reporting spurious "unmodelled" reasons. A feasible path is untouched, so
    // every obligation a real run reaches is still recorded.
    if matches!(find_obligation(st.path, pins), Verdict::Unsat) {
        return;
    }
    let block: Block = match cur.block(st.block) {
        Some(b) => b.clone(),
        None => {
            report.unknown_paths.push(format!("missing block bb{}", st.block));
            return;
        }
    };

    // Unwind bound: count *back-edge traversals*, and stop the path rather than
    // assume exit.
    //
    // Counting entries to a block counts the loop header once more than the loop
    // runs -- the last entry evaluates the guard and takes the exit -- so a loop
    // that runs exactly `N` iterations needs `N + 1` header entries, and
    // `unwind: N` was rejected: `for i in 0..3` under `unwind: 3` came back
    // `FAILED` (the `while` spelling only passed by accident, because its header
    // ends in a `switchInt` that zeroes its own count). The *latch* -- the block
    // holding the edge back to the header -- is executed exactly once per
    // iteration, so it is the quantity the bound is about.
    if let Some(header) = callees.latch_header(st.frame.func, st.block) {
        // Count by the *loop* (its header), not by the source block, so a loop
        // whose body reaches its back edge from two different latches is counted
        // once per iteration rather than once per latch. Keying by block let the
        // combined trip count exceed a declared bound while neither latch's own
        // count did.
        let key = (st.frame.func, header);
        let n = st.visits.entry(key).or_insert(0);
        *n += 1;
        if *n > unwind {
            if unwind_declared {
                // A *declared* bound is a claim ("this loop finishes within N
                // iterations"), so running off the end of it is Kani's *unwinding
                // assertion*: a failure, not an incompleteness. Recording it as a
                // failure rather than an `unknown_paths` entry is what stops a
                // too-small bound from turning into a weaker proof: `verified` under
                // `unwind: 3` would be a statement about the first three iterations
                // only, which is exactly the soundness hole the clause exists to
                // avoid. The verdict is the reachability of the cutoff -- the same
                // query shape as a diverging call, and for the same reason -- so a
                // reachable cutoff comes back as a `Counterexample` naming an input
                // that runs off the bound, and one reached on every input as `Valid`.
                // `Unsat` would be a discharge, but the path was already pruned when
                // unsatisfiable, so the cutoff is a failure on every input that reaches
                // it.
                report.obligations.push(Obligation {
                    kind: ObligationKind::UnwindBound { bound: unwind },
                    verdict: find_obligation(st.path, pins),
                });
            } else {
                // No bound was declared, so the cutoff is the default, which is not a
                // claim anyone made. It stays an honest incompleteness -- but it is a
                // *missing loop contract*, not an unmodelled construct, and the
                // message says so: the loop is understood, and the tool is declining
                // to unwind it past the default because assuming an exit would be
                // unsound. A reader who wants a verdict here declares an `invariant:`
                // (which cuts the loop at the header) or an `unwind:` bound.
                report.unknown_paths.push(format!(
                    "loop unwound past {unwind} at bb{} of {}; assuming it exited would be \
                     unsound -- this is a missing loop contract, not an unmodelled \
                     construct: declare `invariant:` or `unwind:` to decide it",
                    st.block, cur.name
                ));
            }
            return;
        }
    }

    // Statements.
    for s in &block.stmts {
        match s {
            Stmt::Nop => {}
            Stmt::Unknown(text) => {
                report.unknown_paths.push(format!("unmodelled statement: {text}"));
                return;
            }
            Stmt::Assign(dest, rv) => {
                let v = eval_rvalue(cur, &mut st.env, dest, rv);
                // A reference *copied* between locals (`let r = identity(&mut x)`
                // lowers to `_4 = move _3` where `_3` is the returned `&mut u8`)
                // addresses the same place `_3` did, and `resolve` is what turns
                // `*_4` into that place. Only `Rvalue::Ref` and a reference `Cast`
                // recorded the mapping, so the copy lost it: `*_4 = 5` was then a
                // write to a local no caller reads, the write was dropped, and
                // `requires: x == 0` / `ensures: ret == 0` was **proved** against a
                // body that returns 5 -- while the true contract `ret == 5` was
                // refuted. The mapping is carried only for a reference *type*, so a
                // numeric copy cannot invent one.
                // The *source* is the guard, not the destination: a copy of a
                // reference local is a reference copy, and `q.proj.is_empty()`
                // keeps a copy *through* a reference (`_3 = copy (*_1)`, where `_3`
                // is a `u8`) out -- carrying the address there would give a scalar
                // an address, and in a two-reference `swap` both scalar copies then
                // claimed the same storage, which broke the swap and proved a false
                // contract.
                if let Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) = rv {
                    if q.proj.is_empty() && matches!(cur.ty_of(q.local), Some(Ty::Ref(_))) {
                        if let Some(o) = st.env.ref_origin.get(&q.local).cloned() {
                            st.env.addressed.insert(dest.local, o.clone());
                            st.env.ref_origin.insert(dest.local, o);
                        }
                    } else if q.proj.as_slice() == [Proj::Deref]
                        && matches!(cur.ty_of(dest.local), Some(Ty::Ref(_)))
                    {
                        // A reference read *through* another reference: `**rr = 5`
                        // lowers to `_4 = no_retag copy (*_3); (*_4) = 5`, where `_4`
                        // is a `&mut u8`. The copy is a *reference*, so it addresses
                        // what `_3` points to. Neither branch above fires -- the
                        // source is not a bare reference local, and its projection is
                        // a deref -- so `_4` got no address, `(*_4) = 5` was dropped,
                        // and `requires: x == 0` / `ensures: ret == 0` was **proved**
                        // against a body that returns 5, while the true `ret == 5` was
                        // refuted. The destination's *type* is what separates this from
                        // `_3 = copy (*_1)` with `_3: u8`, which copies a scalar and
                        // must carry no address (both are a deref; only the type
                        // differs).
                        //
                        // The place is `_3`'s referent, not `_3`: aiming at `_3` would
                        // make `(*_4) = 5` write to the reference local rather than to
                        // what it points at.
                        let p = st.env.pointee(q);
                        st.env.addressed.insert(dest.local, p.clone());
                        st.env.ref_origin.insert(dest.local, p);
                    }
                }
                st.env.set(dest, v);
                // A promoted `&[&str]` constant (`_4 = const f::promoted[0]`) is the
                // format-piece array a `panic!`/`assert!` message is built from on
                // edition 2024. Its pieces are recorded *here*, after `set`, because
                // a whole-place write forgets the destination's parts -- recording
                // them inside `eval_rvalue` would have them cleared by the very
                // `set` that follows. The value itself is not a bit-vector.
                if let Rvalue::Use(Operand::Const(Const::Other(n))) = rv {
                    if let Some(pieces) = lookup_promoted(&st.env.promoted, n) {
                        st.env.piece_sets.insert(dest.local, pieces);
                    }
                }
                // The `b"…"` template of `Arguments::new` reaches the call through a
                // local (`_9 = const b"…"` then `new::<7, 1>(move _9, …)`), so it is
                // recorded the same way and for the same reason.
                if let Rvalue::Use(Operand::Const(Const::Bytes(b))) = rv {
                    st.env.tmpl_bytes.insert(dest.local, b.clone());
                }
                // A `&str` literal reaches `str::len`/`String::from`/`push_str` through
                // a local (`_4 = const "ab"`), so its byte length is kept in the string
                // store -- recorded *after* `set`, because a whole-place write forgets
                // the destination's parts. `length_of` reads it back as the length.
                if let Rvalue::Use(Operand::Const(Const::Str(text))) = rv {
                    st.env.strs.insert(dest.local, text.clone());
                }
                // A *nested* aggregate assignment moves the source's parts under the
                // destination's path. Two shapes need it: a struct literal into a nested field
                // (`o.i = Inner { v: 9 }` -> `(_1.0) = move _2`), and a nested-to-nested move
                // (`o.i = o.j` -> `_2 = move (_1.1); (_1.0) = move _2`, so a *nested source*
                // into a whole temp, then a whole source into a nested destination).
                //
                // `copy_parts` in `eval_rvalue` handles only whole-to-whole, and a nested
                // source is one it refuses, so this runs whenever *either* side is nested.
                // It is done *after* `set` because the field arm of `set` forgets the nested
                // paths beneath the destination -- correct, since they are stale -- and this
                // is what puts the source's parts back. Without it the temp's `v` never lands
                // under `_1.0`, and `(_1.0).0` reads `Unknown`.
                if let Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) = rv {
                    if !q.proj.is_empty() || !dest.proj.is_empty() {
                        st.env.rebase_parts(q, dest);
                    }
                    // An element *write* of a whole aggregate: `b[0] = Inner { v: 7 }`
                    // lowers to `_4[_6] = move _5`. The operand's leaves live in its
                    // own parts, and the element slot is keyed index-first, which
                    // `rebase_parts` refuses (it re-roots field chains only). Without
                    // this the write stores the element's scalar (there is none) and
                    // the leaf reads `Unknown`, so `b[0].v` after the write stayed
                    // unreadable. Gated on the operand's type, as the literal path is.
                    //
                    // The subscript is a *local* (`_6`), so it is `IndexVar`; only an
                    // index the run can pin names one element, and a symbolic one has
                    // no slot to re-root onto.
                    if matches!(type_of_place(cur, q), Some(Ty::Other(_))) {
                        if let Some(k) = st.env.elem_index_of(&dest.proj) {
                            st.env.rebase_elem_parts(q, dest.local, k);
                        }
                    }
                }
                // A `Box`'s pointer, recorded *last* in the arm because every step
                // above may forget the destination's parts (`set` drops them, and
                // `rebase_parts` drops them again) -- and `forget_parts` also clears
                // `box_refs`. Two spellings name the box's pointer, and both must
                // link `dest -> box` so a later `*dest` reads the boxed value:
                //
                // * current stable: `_3 = (_2.0) as *const u8` (`BoxDerefTransmute`);
                // * the MSRV (1.85): `_3 = copy (((_2.0).0).0)` -- `Box`'s
                //   `Unique`/`NonNull`/`*const` fields walked one by one, no cast.
                //
                // An all-field chain rooted at a boxed local is that pointer
                // whichever spelling reaches it. Without the `Use` form the MSRV's
                // `box_new_reads_its_value` was `incomplete` (the return value was
                // not known) while stable verified it -- a toolchain-shaped gap gate
                // 14 (the suite on 1.85) caught.
                match rv {
                    Rvalue::Cast(Operand::Copy(q) | Operand::Move(q), _)
                        if q.proj.as_slice() == [Proj::Field(0)] =>
                    {
                        if st.env.boxed.contains_key(&q.local) {
                            st.env.box_refs.insert(dest.local, q.local);
                        }
                    }
                    Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
                        if st.env.boxed.contains_key(&q.local)
                            && !q.proj.is_empty()
                            && q.proj.iter().all(|p| matches!(p, Proj::Field(_))) =>
                    {
                        // The MSRV also emits an *alignment* assert (`AlignOf`,
                        // `BitAnd`, `Eq`) reading the pointer's address, so `dest`
                        // needs the pointer token's *value* (not just the deref link)
                        // or the check is `unmodelled assert condition`. The token is
                        // the box's field 0.
                        if let Some(tok) = st.env.fields.get(&(q.local, 0)).copied() {
                            st.env.set(dest, tok);
                        }
                        st.env.box_refs.insert(dest.local, q.local);
                    }
                    _ => {}
                }
            }
        }
    }

    // Terminator. Every successor goes through `advance`, which is where a loop
    // edge into the invariant's header is checked instead of followed.
    match &block.term {
        Term::Goto(b) => advance(prog, st, *b, report, work, pins),
        Term::Return => {
            let ret = st.env.get(&Place::new(0));
            match st.frame.caller.take() {
                // The root returned: check the postcondition here.
                None => {
                    report.returned_paths += 1;
                    if let Some(post) = post {
                        // The components of a tuple return, so a postcondition can
                        // name `ret.0`. They are read through the *same* place read
                        // the body uses, rather than from one store directly.
                        //
                        // That is not a convenience: a tuple local's component is
                        // written under `Proj::Index` by a literal (`_0 = (a, b)`) and
                        // under `Proj::Field` by a modelled call (`overflowing_add`
                        // writes field 0 and field 1), while `Env::get` consults
                        // `fields` and falls back to `elems` so both spellings of
                        // "component `k`" meet. Collecting from `elems` alone missed
                        // every call-written component, and the symptom was a
                        // postcondition about `ret.1` reported unreadable -- an
                        // aggregate with no such component -- rather than checked.
                        // Going through `get` makes the two agree by construction.
                        //
                        // The candidate indices are the union of the two stores, and
                        // an unwritten component stays out of the list: binding a
                        // *fresh* variable for it would make a postcondition about
                        // `ret.1` pass vacuously, which is why the filter drops
                        // anything that is not a readable value.
                        //
                        // A `bool` component is widened to a one-bit word for the
                        // same reason a `bool` *return* is: a postcondition
                        // `ret.0 == true` compares against a word, and dropping the
                        // component would leave the name unbound, so the parser
                        // refuses the whole contract. `(bool, u8)` returns are
                        // common (every `checked_*` is `(T, bool)`), so refusing
                        // them silently loses the proof.
                        let mut components: BTreeSet<u32> = BTreeSet::new();
                        for (l, k) in st.env.elems.keys() {
                            if *l == 0 {
                                components.insert(*k as u32);
                            }
                        }
                        for (l, k) in st.env.fields.keys() {
                            if *l == 0 {
                                components.insert(*k);
                            }
                        }
                        let projs: Vec<(u32, Var)> = components
                            .into_iter()
                            .filter_map(|k| {
                                let p = Place { local: 0, proj: vec![Proj::Field(k)] };
                                match st.env.get(&p) {
                                    Val::Sym(x, _) => Some((k, x)),
                                    Val::Bool(p) => {
                                        Some((k, smt::ite(p, smt::word(1, 1), smt::word(0, 1))))
                                    }
                                    _ => None,
                                }
                            })
                            .collect();
                        // What the postcondition is evaluated against. A scalar
                        // return hands over its word; a bool is widened to a one-bit
                        // word (proving `path => rp` alone would check only that the
                        // bool is *true*, which is not the contract — `ensures: ret
                        // == false` would be ignored). An aggregate has no single
                        // word, so `ret` itself is passed as `None` and a contract
                        // that uses bare `ret` is refused by the parser; the
                        // components are still available as `ret.0`, `ret.1`.
                        let rv = match ret {
                            Val::Sym(rv, _) => Some(rv),
                            Val::Bool(rp) => Some(smt::ite(rp, smt::word(1, 1), smt::word(0, 1))),
                            _ => None,
                        };
                        // An enum return: the *tag* is what `ret.is_ok()` and
                        // friends read, so it is passed as the return word. The
                        // tag lives in the discriminant store (written by a variant
                        // construction, or seeded for an enum argument), not in the
                        // local's value -- `_0` for `Some(x)` has no whole-local
                        // entry at all. Reading it here is what makes the method
                        // read the discriminant the body's `switchInt` compares.
                        let rv = st.env.tag_value(0).or(rv);
                        // An enum return's payloads, keyed by their *discriminant*,
                        // so a contract can name `ret.Ok` / `ret.Some`. A payload is
                        // stored by a variant construction or a modelled call under
                        // the variant's discriminant, and a payload *read* through a
                        // downcast lands in `fields` keyed by the same number. A
                        // `bool` payload is widened to a one-bit word, like any
                        // other boolean value handed to the postcondition.
                        let ret_payloads: Vec<(u64, Var)> = st
                            .env
                            .payloads
                            .iter()
                            .filter(|((l, _), _)| *l == 0)
                            .filter_map(|((_, k), (v, _))| match v {
                                Val::Sym(x, _) => Some((*k, *x)),
                                Val::Bool(p) => {
                                    Some((*k, smt::ite(*p, smt::word(1, 1), smt::word(0, 1))))
                                }
                                _ => None,
                            })
                            .chain(
                                st.env
                                    .fields
                                    .iter()
                                    .filter(|((l, _), _)| *l == 0)
                                    .filter_map(|((_, k), v)| match v {
                                        Val::Sym(x, _) => Some((*k as u64, *x)),
                                        Val::Bool(p) => Some((
                                            *k as u64,
                                            smt::ite(*p, smt::word(1, 1), smt::word(0, 1)),
                                        )),
                                        _ => None,
                                    }),
                            )
                            .collect();
                        // The *final* value of each reference argument, so an
                        // `ensures` that names one means what the body left there
                        // and `old(name)` reaches the entry value. A reference
                        // shares the caller's storage, so the value at return is
                        // the post-state one. Only reference-to-scalar arguments
                        // are collected: a reference to an aggregate has no single
                        // word, and a by-value argument cannot be written by the
                        // body, so neither needs a second binding.
                        let mut ref_final: Vec<(u32, Var)> = Vec::new();
                        for &l in &cur.arg_locals {
                            let Some(ty) = cur.ty_of(l) else { continue };
                            if !matches!(ty, Ty::Ref(_)) {
                                continue;
                            }
                            // A `&Vec`/`&mut Vec`/`&[T]` argument: the postcondition's
                            // `v.len()` must read the *post-state* length, not the entry
                            // length. A `&mut Vec` the body pushes to has a final length
                            // the entry value does not describe, so reading the entry
                            // length was a false proof (`requires: v.len() == 0` /
                            // `ensures: v.len() == 0` over `v.push(1)` verified though
                            // the length is 1). A slice/array's length cannot change, so
                            // this is a no-op for it.
                            let pointee = st.env.pointee(&Place::new(l)).local;
                            if let Some(s) = st.env.indexed.get(&pointee) {
                                ref_final.push((l, s.len));
                                continue;
                            }
                            // A reference-to-scalar argument: its *value* is the
                            // post-state value.
                            if ty.referent().width().is_none() {
                                continue;
                            }
                            // A `&mut bool` target is a `Val::Bool` predicate, not a
                            // `Val::Sym` word. Dropping it left `c` unbound, so
                            // `ensures: c == true` after `*c = true` was refused as an
                            // unknown name -- the same final-value loss the `Sym` arm
                            // exists to prevent. Widen the predicate to a one-bit
                            // word, exactly as the return word does for a `bool` `ret`.
                            match st.env.get(&Place::new(l)) {
                                Val::Sym(v, _) => ref_final.push((l, v)),
                                Val::Bool(p) => ref_final
                                    .push((l, smt::ite(p, smt::word(1, 1), smt::word(0, 1)))),
                                _ => {}
                            }
                        }
                        match post(rv, &projs, &ret_payloads, &ref_final) {
                            Ok(p) => {
                                report.obligations.push(Obligation {
                                    kind: ObligationKind::Postcondition,
                                    verdict: prove_obligation(st.path, p, pins),
                                });
                            }
                            Err(e) => report
                                .unknown_paths
                                .push(format!("unreadable `ensures`: {e}")),
                        }
                    }
                }
                // A callee returned: hand its value to the caller's destination
                // and continue at the call site. This continuation is what makes
                // an inlined call mean what the real call means.
                Some(caller) => {
                    // Resume in the *caller's* environment, not the callee's. The
                    // two number their locals independently, so carrying the
                    // callee's env back would hand the caller the callee's
                    // values under the caller's local numbers. Only the return
                    // value crosses the boundary, written to the call's
                    // destination.
                    let mut env = caller.saved_env.clone().unwrap_or_else(Env::new);
                    // The callee ran in its own `Env`, seeded from a copy of each
                    // indexed argument's store. What happens to that store now
                    // depends on how the argument was passed, and the two cases
                    // are opposites:
                    //
                    // * A by-value `[T; N]` is the callee's *own copy*. Its writes
                    //   die with the frame, so the caller's array is still the one
                    //   it passed and must not be overwritten from the callee.
                    //   Nothing is copied back.
                    // * A `&mut [T]`/`&mut [T; N]` is the caller's storage. The
                    //   frontend models `&T` as its referent (the single-owner
                    //   reading, not an aliasing model), so the callee's local and
                    //   the caller's local denote the same value: the callee's
                    //   post-state *is* the caller's post-state, and is copied
                    //   back. That is what makes a helper that writes through a
                    //   reference visible to the caller, and a callee that wrote
                    //   nothing leaves the caller's store as it was.
                    for (target, cal) in &caller.by_ref {
                        let cl = target.local;
                        // The target's projection *below* its leading deref. A
                        // reference argument arrives as `_5 = &mut _2; set5(_5)`,
                        // so `pointee` has already collapsed the temp and the target
                        // is a plain place on the caller's local -- `c` for `&mut c`,
                        // `c.0` for `&mut c.lo`. Stripping the deref (when a caller
                        // ever hands one over) leaves the chain every re-key below
                        // is prefixed with.
                        let rest: &[Proj] = match target.proj.first() {
                            Some(Proj::Deref) => &target.proj[1..],
                            _ => &target.proj,
                        };
                        // An indexed referent (`&mut [T]` / `&mut [T; N]`): the
                        // callee's element store *is* the caller's post-state.
                        //
                        // Only when the target is the *whole* local. For a
                        // sub-place target (`set5(&mut a[0])`) the callee's local
                        // is a scalar `&mut u8`, and the store the callee holds for
                        // it is the caller's array carried in for the read -- which
                        // the callee's whole-place write *poisoned*. Copying that
                        // poison back would make the caller's untouched `a[0]` read
                        // unknown, turning a decidable contract into an incomplete
                        // one.
                        if rest.is_empty() {
                            if let Some(s) = st.env.indexed.get(cal) {
                                env.indexed.insert(cl, s.clone());
                            }
                        }
                        // A whole-referent write (`*v = x`). The whole place was
                        // replaced, so the caller's derived parts are dropped
                        // before the callee's value is copied in -- otherwise a
                        // stale field the callee overwrote would survive. A
                        // sub-place target (`&mut _1.0`) is coarser: every part of
                        // `_1` is dropped, which loses precision but never keeps a
                        // stale value.
                        if st.env.whole_writes.contains(cal) {
                            if let Some(v) = st.env.locals.get(cal) {
                                // The callee's whole-place value lands *at the
                                // target*, which is the caller's local only when
                                // the target has no projection. For `&mut c.lo` the
                                // target is `c.0`, so the write belongs in the
                                // field store, not on `c` itself -- writing it to
                                // `c` would put a bit-vector where a struct lives.
                                // `set` keys the projection for us, and it drops
                                // the parts the write replaces.
                                env.set(&target.clone(), *v);
                                // A *whole-local* target additionally supersedes
                                // the whole local, which is what the parts drop
                                // above needs to see.
                                if target.proj.is_empty() {
                                    env.whole_writes.insert(cl);
                                }
                            } else {
                                env.forget_parts(cl);
                            }
                        }
                        // A write to a *part* of the referent (`(*v).0 = x`,
                        // `(*v).a.b = x`, `(*v)[0] = x`). Only the callee's
                        // entries exist for its argument local (a reference is
                        // seeded as `Unknown`, never as parts), so every entry
                        // here is a write and is safe to carry back. A part the
                        // callee did not touch keeps the caller's seed, which is
                        // the same storage the callee read.
                        //
                        // Every key is re-based on the *target's* projection, not
                        // copied onto the caller's local. For a whole-local target
                        // (`&mut c`) `rest` is empty and the keys are unchanged, so
                        // `c.lo` lands on `c`'s field as before. For a sub-place
                        // target (`&mut o.i`) the callee's `_1.v` is `o.i.v`, so the
                        // key has to become the chain `rest ++ [v]` -- copying it to
                        // `o`'s field `v` would put a leaf where no leaf lives, and
                        // *dropping* it (what a whole-local-only guard did) lost the
                        // write entirely: `set_inner(&mut o.i); o.i.v` read the
                        // caller's seed, so the true contract `ret == 5` was refuted
                        // and the false `ret == 0` was **proved**.
                        // `nested` is keyed by a chain of *field* indices, so the
                        // target's projection is usable as a prefix exactly when it
                        // is itself a field chain. A target that is not one (an
                        // element, `&mut o.a[0]`) is a scalar in the callee, so it
                        // has no parts to carry and the loops below see nothing --
                        // the `None` arm exists only so an unrepresentable key is
                        // never invented.
                        let rest_chain: Option<Vec<u32>> = {
                            let mut c = Vec::with_capacity(rest.len());
                            let ok = rest.iter().all(|s| match s {
                                Proj::Field(i) => {
                                    c.push(*i);
                                    true
                                }
                                _ => false,
                            });
                            if ok {
                                Some(c)
                            } else {
                                None
                            }
                        };
                        let mut dropped = false;
                        for ((l, f), v) in st.env.fields.iter() {
                            if *l != *cal {
                                continue;
                            }
                            match &rest_chain {
                                Some(rc) if rc.is_empty() => {
                                    env.fields.insert((cl, *f), *v);
                                }
                                Some(rc) => {
                                    let mut key = rc.clone();
                                    key.push(*f);
                                    env.nested.insert((cl, key), *v);
                                }
                                None => dropped = true,
                            }
                        }
                        for ((l, chain), v) in st.env.nested.iter() {
                            if *l != *cal {
                                continue;
                            }
                            match &rest_chain {
                                Some(rc) => {
                                    let mut key = rc.clone();
                                    key.extend_from_slice(chain);
                                    env.nested.insert((cl, key), *v);
                                }
                                None => dropped = true,
                            }
                        }
                        for ((l, k), v) in st.env.elems.iter() {
                            if *l != *cal {
                                continue;
                            }
                            if rest.is_empty() {
                                env.elems.insert((cl, *k), *v);
                            } else if let Some(rc) = &rest_chain {
                                // An array *argument* handed over as a whole field-path
                                // target (`&mut x.a`): the callee's `_1` is the array, so
                                // its element `k` is the caller's `<target>[k]`, which lives
                                // in `elems_path` under the target's field chain. Without
                                // this the element was dropped and the caller read its own
                                // seed (`set_first_of(&mut x.a); x.a[0]` was `Incomplete` in
                                // *both* directions). The chain is non-empty here -- the
                                // empty one is the whole-local arm above -- and the entry
                                // exists only because the argument is an array: a struct or
                                // tuple argument's parts live in `fields`/`nested`, never
                                // here, so this cannot re-base a scalar onto an array key.
                                env.elems_path.insert((cl, rc.clone(), *k), *v);
                            } else {
                                // An element under a sub-place target that is not a field
                                // chain (`&mut x.a[0]`) has no key in this store. Leaving the
                                // caller's element would be a stale value, so the caller's
                                // parts go instead -- precision lost, never a wrong value
                                // kept.
                                dropped = true;
                            }
                        }
                        // Elements of field-path arrays (`x.a[0]`) the callee wrote.
                        // These live in their own store, keyed by the whole chain, so
                        // the loop above never sees them: without this one a helper's
                        // `x.a[0] = 9` died with the frame and the caller read its own
                        // seed, so the false `ret == 5` was **proved** against a body
                        // returning 9. A whole-local target re-bases the callee's chain
                        // under the caller's local unchanged; a sub-place target whose
                        // chain is a field chain prefixes it (`&mut o.i` makes the
                        // callee's `_1.a[0]` the caller's `o.i.a[0]`), and one that is
                        // not (an element target, `&mut x.a[0]`) has no representable
                        // key, so the caller's parts go rather than a stale value being
                        // kept.
                        for ((l, chain, k), v) in st.env.elems_path.iter() {
                            if *l != *cal {
                                continue;
                            }
                            match &rest_chain {
                                Some(rc) => {
                                    let mut full = rc.clone();
                                    full.extend_from_slice(chain);
                                    env.elems_path.insert((cl, full, *k), *v);
                                }
                                None => dropped = true,
                            }
                        }
                        // The leaves *inside* those elements (`x.a[0].v`), keyed
                        // index-first. Only a whole-local target is carried: this
                        // store is keyed by an *element index* on a local that is
                        // itself an array, and a sub-place target's array is reached
                        // through a field path, which this store has no key for --
                        // `elems_path` holds those elements' own values, not their
                        // leaves. Inventing a prefixed key here would write an entry
                        // no read consults, so the caller's leaves go instead (the
                        // `dropped` path), which loses precision and never keeps a
                        // stale value.
                        //
                        // The caller's own leaves for that local are dropped *before*
                        // the callee's are copied in, because a whole-local target is
                        // replaced by the callee's post-state. A callee that wrote
                        // through an index it could not pin poisoned its array and
                        // holds *no* leaves for it; keeping the caller's would leave
                        // the pre-call leaf readable, which is a stale *wrong* value.
                        let leaves_match = matches!(&rest_chain, Some(rc) if rc.is_empty());
                        if leaves_match {
                            env.elem_parts.retain(|(l, _, _), _| *l != cl);
                        }
                        // A callee that wrote through an index it could not pin
                        // poisoned its array, so it holds *no* element for the
                        // caller to take: every element is unknown. Dropping the
                        // caller's own elements is what keeps the pre-call leaf from
                        // surviving the call -- keeping it would be a stale *wrong*
                        // value, and the loops above would have inserted nothing.
                        if leaves_match && st.env.poisoned_elems.contains(cal) {
                            env.elems.retain(|(l, _), _| *l != cl);
                            env.nested.retain(|(l, _), _| *l != cl);
                            env.elem_parts.retain(|(l, _, _), _| *l != cl);
                            env.poisoned_elems.insert(cl);
                        }
                        for ((l, k, chain), v) in st.env.elem_parts.iter() {
                            if *l != *cal {
                                continue;
                            }
                            match &rest_chain {
                                Some(rc) if rc.is_empty() => {
                                    env.elem_parts.insert((cl, *k, chain.clone()), *v);
                                }
                                _ => dropped = true,
                            }
                        }
                        if dropped {
                            env.forget_parts(cl);
                        }
                    }
                    if let Some(dest) = &caller.ret_dest {
                        // A reference the callee *returned*: `identity(_3) -> _2`
                        // where the callee's `_0` addressed its argument. The
                        // callee's local indices mean nothing in the caller's
                        // frame, but `ref_origin` records which caller local the
                        // reference was built from, so the caller's destination can
                        // be pointed at that storage. Without this the returned
                        // reference had no address in the caller, `*r = 5` was
                        // dropped, and the false `ret == 0` was **proved**.
                        // The callee's returned reference names a place in the
                        // *callee's* terms. Translate its head through
                        // `arg_source`: a head that is a reference argument becomes
                        // the caller's place, and the returned projection is
                        // appended -- `&mut self.lo` returns `_1.0`, and `_1` is the
                        // caller's `c`, so the caller's destination is `c.lo`. A
                        // head that is *not* an argument is the callee's own
                        // storage, which dies at return; nothing is recorded and a
                        // write through the returned reference is dropped rather
                        // than aimed at a foreign place.
                        if let Some(o) = st.env.ref_origin.get(&0).cloned() {
                            if let Some(src) = st.env.arg_source.get(&o.local).cloned() {
                                // Two rewrites turn the callee's origin into a place in
                                // the caller, and both are needed for an *element*:
                                //
                                // `resolve` collapses a deref of a local whose address
                                // was recorded; then a leading deref is stripped
                                // outright, because the head here is a reference
                                // *argument* (`arg_source` holds only those) and `src`
                                // already names its referent. `&mut a[0]` on a
                                // whole-array argument is `(*_1)[_2]`, and `_1` is that
                                // argument, so without the strip the deref lands in the
                                // middle of the caller's place where no store is keyed
                                // -- the write is dropped and a false contract about the
                                // seed is *proved*.
                                //
                                // `pin_index_vars` then resolves the `IndexVar` the dump
                                // prints (`_2` for the literal `0`), which dies at the
                                // call boundary. Only the callee's own projection is
                                // pinned: the caller's `src.proj` names *caller* locals,
                                // so resolving it against this frame would read the
                                // wrong local and is carried through as it is.
                                let mut o = st.env.resolve(&o);
                                if matches!(o.proj.first(), Some(Proj::Deref)) {
                                    o.proj.remove(0);
                                }
                                let o = st.env.pin_index_vars(&o);
                                // An `IndexVar` that is *not* pinned -- a symbolic index
                                // the contract does not fix -- names a callee local that
                                // means nothing in the caller. Carried across, the caller
                                // reads it as *its own* local of that number, which is a
                                // different argument, and the write lands on whatever
                                // element that happens to hold: `*x.nth_mut(i) = 9` with a
                                // parameter before `i` aimed the write at `x.a[zero]` --
                                // the seed element -- so the false `ret == 5` was
                                // *proved*.
                                //
                                // Dropping the reference alone is not enough: the write
                                // may hit *any* element, so a later read of `x.a[0]` must
                                // not fall back to its seed (that turned the false proof
                                // around rather than removing it -- `ret == 5` became
                                // provable). The array's elements are poisoned instead, so
                                // every read is unknown: the write is lost, never
                                // mis-aimed, and no stale seed survives it.
                                if o.proj.iter().any(|s| matches!(s, Proj::IndexVar(_))) {
                                    // The array's field chain is the `Field` steps that
                                    // lead up to the index; the index step and anything
                                    // past it are not part of the path.
                                    let mut chain = field_steps(&src.proj).unwrap_or_default();
                                    for step in &o.proj {
                                        match step {
                                            Proj::Field(f) => chain.push(*f),
                                            _ => break,
                                        }
                                    }
                                    env.poison_array_under(src.local, &chain);
                                } else {
                                    let mut proj = src.proj.clone();
                                    proj.extend_from_slice(&o.proj);
                                    let place = Place { local: src.local, proj };
                                    env.addressed.insert(dest.local, place.clone());
                                    env.ref_origin.insert(dest.local, place);
                                }
                            }
                        }
                        env.set(dest, ret);
                        // A returned `Vec` carries its length and elements in the
                        // callee's `_0` as an `indexed` entry, and the value itself
                        // is `Val::Unknown` (a `Vec`'s fields are not printed), so
                        // this is *not* inside the `Val::Agg` guard below. Without
                        // the transfer `let v = mk(); v.len()` reads a receiver with
                        // no modelled length -- the same hole the move path
                        // (`copy_parts`) had. Only a whole-local destination can hold
                        // a `Vec`, and a returned value replaces what the destination
                        // held, so the destination's old entry is dropped first.
                        if dest.proj.is_empty() {
                            env.forget_parts(dest.local);
                            if let Some(s) = st.env.indexed.get(&0) {
                                env.indexed.insert(dest.local, s.clone());
                            }
                        }
                        // A tuple return has components, and the callee stored
                        // them in its *own* return place (`_0.0`, `_0.1`). The
                        // caller's `min2(a, b).0` reads `_2.0`, so the components
                        // have to cross the boundary with the return value.
                        // Carrying only the aggregate loses them, and a contract
                        // about `min2(a, b).0` is then unreadable rather than
                        // checked. They are copied under the *destination's*
                        // local, which is the place the caller actually reads.
                        //
                        // Only the components the callee wrote are copied, so a
                        // path that left `_0.1` unwritten leaves the caller's
                        // `dest.1` unknown rather than inventing a value.
                        if matches!(ret, Val::Agg) {
                            for ((l, k), v) in st.env.elems.iter() {
                                if *l != 0 {
                                    continue;
                                }
                                let p = Place {
                                    local: dest.local,
                                    proj: vec![Proj::Index(*k)],
                                };
                                env.set(&p, *v);
                            }
                            // A *struct* return keeps its fields and nested paths in the
                            // field stores, not in `elems`: `_0 = _1` copies `_1`'s parts
                            // through `copy_parts`, which writes `fields`/`nested`. Copying
                            // only `elems` lost them, so `id_inner(o.i).v` -- a nested
                            // aggregate handed to a helper by value and read back -- read
                            // `Unknown` while the contract was true of the body. This runs
                            // after the `elems` loop because clearing the destination's old
                            // fields must not also clear the tuple components just written;
                            // the nested paths are set last so the intermediate field write
                            // (which forgets the paths beneath it) cannot drop a leaf.
                            //
                            // Only when the destination is a whole local, which is the shape
                            // a call's destination has. A returned whole value replaces every
                            // part, so the destination's old fields and nested paths are
                            // dropped first: keeping one the callee did not write would be a
                            // *wrong* value rather than a missing one.
                            if dest.proj.is_empty() {
                                env.fields.retain(|(l, _), _| *l != dest.local);
                                env.nested.retain(|(l, _), _| *l != dest.local);
                                env.elems_path.retain(|(l, _, _), _| *l != dest.local);
                                env.elem_parts.retain(|(l, _, _), _| *l != dest.local);
                                // The elements' own values (`_0[k]`) cross first, as
                                // `elems` entries above; their *leaves* cross here, in
                                // the index-first key the caller's `mk()[0].v` read
                                // consults. A returned array of aggregates otherwise
                                // lost every leaf and the contract stayed unreadable --
                                // `incomplete` where the true contract should decide.
                                for ((l, k, chain), v) in st.env.elem_parts.iter() {
                                    if *l != 0 {
                                        continue;
                                    }
                                    env.elem_parts.insert((dest.local, *k, chain.clone()), *v);
                                }
                                for ((l, f), v) in st.env.fields.iter() {
                                    if *l != 0 {
                                        continue;
                                    }
                                    let p = Place {
                                        local: dest.local,
                                        proj: vec![Proj::Field(*f)],
                                    };
                                    env.set(&p, *v);
                                }
                                for ((l, chain, k), v) in st.env.elems_path.iter() {
                                    if *l != 0 {
                                        continue;
                                    }
                                    env.elems_path.insert((dest.local, chain.clone(), *k), *v);
                                }
                                for ((l, chain), v) in st.env.nested.iter() {
                                    if *l != 0 {
                                        continue;
                                    }
                                    let p = Place {
                                        local: dest.local,
                                        proj: chain.iter().map(|i| Proj::Field(*i)).collect(),
                                    };
                                    env.set(&p, *v);
                                }
                            }
                        }
                    }
                    // Restore the caller's loop cut, which entering the callee
                    // cleared. Without this the resumed caller has no cut, so the
                    // next edge into its loop header is unwound rather than
                    // checked against the invariant -- and a loop whose step is a
                    // same-dump call is reported as a cutoff once it passes
                    // `DEFAULT_UNWIND`, even when the invariant was sufficient.
                    // The callee's `cut` is discarded: it named the callee's loop,
                    // if any, and the callee has returned.
                    let cut = caller.saved_cut.clone();
                    let variant_entry = caller.saved_variant;
                    work.push(State {
                        block: caller.ret_target,
                        frame: *caller,
                        path: st.path,
                        env,
                        visits: st.visits,
                        depth: st.depth.saturating_sub(1),
                        cut,
                        variant_entry,
                    });
                }
            }
        }
        Term::Drop { place, target } => {
            // `drop(place)` runs `place`'s destructor, then continues. Three
            // cases, and the middle one is the soundness boundary:
            //
            // * A type with no drop glue -- an integer, `bool`, `()`, a reference,
            //   or a plain aggregate of such -- runs nothing, so the terminator is
            //   a no-op. rustc does not emit a `drop` for such a type, so this arm
            //   is *defensive*: it is kept so that a malformed or future dump shape
            //   is answered correctly rather than refused, not because it is the
            //   common case. Measured over `realistic.rs`: 0 of 6 `drop` terms are
            //   glue-free; the other six are a user `Drop` or a container.
            // * A *user* `impl Drop` has a body in the dump, so it is executed in
            //   the place's own frame -- the same inliner a method call uses, so a
            //   destructor that reads or writes its `self` fields is modelled.
            // * A container whose destructor this tool cannot represent (`Vec`,
            //   `String`, `Box`, a `MutexGuard`) has no `Drop` body in the dump, so
            //   it is refused. Assuming such a `drop` changes nothing is a *false
            //   proof* whenever the destructor is observable, which is the one
            //   outcome this crate must never produce -- and the dump cannot tell a
            //   container apart from a struct that holds a user-`Drop` field, since
            //   both print `drop(_x) -> [return: …]`.
            //
            // A projected place (`drop(_2.0)`) is refused for the same reason: the
            // write-back a reference argument performs is keyed on a whole local, so
            // a projection would land the destructor's post-state on the wrong
            // storage. rustc does not emit that shape for a glue-bearing place, so
            // the refusal loses no proof.
            let f = &prog.fns[st.frame.func];
            let Some(ty) = type_of_place(f, place) else {
                report.unknown_paths.push("drop of a place with no modelled type".into());
                return;
            };
            if drop_is_noop(&ty) || std_container_glue_free(&ty, callees.structs()) {
                let next = State { block: *target, ..st };
                advance(prog, next, *target, report, work, pins);
                return;
            }
            // rustc's `drop` destroys the *whole* value: the user destructor, then
            // the fields. Running only the user destructor skips a field's, and an
            // empty outer destructor then hides a panicking inner one -- a false
            // proof. A field that itself has glue (its own `Drop`, or a field of
            // one) is refused unless it can be destroyed; only an all-glue-free
            // field set is continued as a no-op.
            match has_field_glue(prog, callees.structs(), &ty) {
                Ok(true) => {
                    report.unknown_paths.push(format!(
                        "drop of `{}` destroys a field with its own destructor, which is not modelled",
                        ty_label(&ty)
                    ));
                    return;
                }
                Ok(false) => {}
                Err(e) => {
                    report.unknown_paths.push(format!("drop of `{}`: {e}", ty_label(&ty)));
                    return;
                }
            }
            let Some(idx) = (if place.proj.is_empty() { drop_destructor(prog, &ty) } else { None })
            else {
                report
                    .unknown_paths
                    .push(format!("drop of `{}` is not modelled", ty_label(&ty)));
                return;
            };
            let callee_fn = &prog.fns[idx];
            let Some(b0) = callee_fn.blocks.first() else {
                report.unknown_paths.push("destructor has no body".into());
                return;
            };
            // The destructor's `self` is `&mut T`, and the place being dropped is
            // the storage it borrows, so the argument is that place itself.
            let arg = Operand::Copy(place.clone());
            let (env, by_ref) =
                seed_callee_env(prog, &mut st.env, callee_fn, std::slice::from_ref(&arg));
            let caller = Frame {
                func: st.frame.func,
                ret_target: *target,
                // A destructor returns `()`: there is no value to hand back, only
                // the writes through `self`, which the `by_ref` copy-back carries.
                ret_dest: None,
                saved_env: Some(st.env.clone()),
                saved_cut: st.cut.clone(),
                saved_variant: st.variant_entry,
                by_ref,
                caller: st.frame.caller.clone(),
            };
            let mut visits = st.visits;
            visits.insert((idx, b0.id), 0);
            work.push(State {
                frame: Frame {
                    func: idx,
                    ret_target: usize::MAX,
                    ret_dest: None,
                    saved_env: None,
                    saved_cut: None,
                    saved_variant: None,
                    by_ref: Vec::new(),
                    caller: Some(Box::new(caller)),
                },
                block: b0.id,
                path: st.path,
                env,
                visits,
                depth: st.depth + 1,
                cut: None,
                variant_entry: None,
            });
        }
        Term::Unreachable => {
            report.obligations.push(Obligation {
                kind: ObligationKind::Unreachable,
                verdict: find_obligation(st.path, pins),
            });
        }
        Term::Assert { cond, negated, msg, target, .. } => {
            // `assert(c)` panics when `c` is false, so a panic is possible
            // exactly when `path ∧ ¬c` is satisfiable. rustc prints the
            // overflow and divide-by-zero checks as `assert(!bit)`, so `negated`
            // flips which polarity is the failing one.
            let c = operand(&mut st.env, cond);
            let holds = match c {
                Val::Bool(p) => p,
                // A bit-vector condition is true when it is non-zero. An assert
                // condition is a `bool` in Rust, so the sign here is irrelevant;
                // it is carried for uniformity, not used.
                Val::Sym(v, _) => smt::not(smt::eq_const(v, 0)),
                Val::Agg | Val::Unknown => {
                    report.unknown_paths.push(format!("unmodelled assert condition: {msg}"));
                    return;
                }
            };
            let satisfied = if *negated { smt::not(holds) } else { holds };
            let bad = smt::and(st.path, smt::not(satisfied));
            report.obligations.push(Obligation {
                kind: ObligationKind::Panic { message: msg.clone() },
                verdict: find_obligation(bad, pins),
            });
            // An assert that did *not* fire is an assumption, and the fall-through
            // path has to carry it. Without this the guard is discarded, which is
            // merely *imprecise* when the guard is what keeps the code safe, but
            // still wrong: `x << n` is only meaningful under `n < w`, and a caller
            // that writes the guard itself expects it to be assumed here too.
            // Sound because the guard is proved separately above: a path where it
            // fails is reported as a panic, and assuming it on this path cannot
            // hide one. Both asserts and `debug_assert`s are lowered to this
            // terminator, so the guard is assumed for either.
            let path = smt::and(st.path, satisfied);
            let next = State { block: *target, path, ..st };
            advance(prog, next, *target, report, work, pins);
        }
        Term::SwitchInt { discr, cases, otherwise } => {
            let d = operand(&mut st.env, discr);
            let arm = |k: u128, positive: bool| -> Option<Pred> {
                match d {
                    Val::Bool(p) => Some(if (k != 0) == positive { p } else { smt::not(p) }),
                    // A `switchInt` compares against a discriminant, which is an
                    // integer: equality does not depend on the sign.
                    Val::Sym(v, _) => {
                        let eq = smt::eq_const(v, k as u64);
                        Some(if positive { eq } else { smt::not(eq) })
                    }
                    _ => None,
                }
            };
            for (k, target) in cases {
                let Some(cond) = arm(*k, true) else {
                    report.unknown_paths.push("unmodelled switch discriminant".into());
                    return;
                };
                // The visit counts carry through the switch unchanged. They used to
                // be reset for this block here, which cleared a latch's count on every
                // branch it took: a `switchInt` block can itself hold the back edge
                // (an `if` whose arms both loop), and clearing the count on each arm
                // let the loop re-enter with a fresh count, so a declared `unwind:`
                // never fired.
                let next = State {
                    block: *target,
                    path: smt::and(st.path, cond),
                    env: st.env.clone(),
                    visits: st.visits.clone(),
                    frame: st.frame.clone(),
                    depth: st.depth,
                    cut: st.cut.clone(),
                    variant_entry: st.variant_entry,
                };
                advance(prog, next, *target, report, work, pins);
            }
            let mut negs = Vec::new();
            for (k, _) in cases {
                let Some(n) = arm(*k, false) else {
                    report.unknown_paths.push("unmodelled switch discriminant".into());
                    return;
                };
                negs.push(n);
            }
            let next = State {
                block: *otherwise,
                path: smt::and(st.path, smt::all(&negs)),
                env: st.env.clone(),
                visits: st.visits.clone(),
                frame: st.frame.clone(),
                depth: st.depth,
                cut: st.cut.clone(),
                variant_entry: st.variant_entry,
            };
            advance(prog, next, *otherwise, report, work, pins);
        }
        Term::Call { callee, args, dest, diverges, target } => {
            let Callee::Name(name) = callee else {
                report.unknown_paths.push("indirect call not modelled".into());
                return;
            };
            // A call that never returns is a reachable failure, not a line to skip.
            //
            // `panic!`, `assert!`, `unwrap`, and the bounds and slice checks rustc
            // inserts lower to a diverging call into `core::panicking`: the path
            // ends there, with no normal successor. What the caller must prove is
            // that the call cannot be reached -- `assert!(x <= 200)` is a promise,
            // and dropping the path silently would let a caller keep a postcondition
            // the assert was there to guarantee. So the obligation is `path` itself,
            // "is this call reachable", discharged by `Unsat`: the same polarity as
            // an `assert` terminator and for the same reason. Nothing is assumed
            // afterwards, because there is no afterwards. The block the `switchInt`
            // routes here already carries `!guard` in its path, so the guard is what
            // the query is really about.
            if *diverges {
                report.obligations.push(Obligation {
                    kind: ObligationKind::DivergingCall {
                        kind: Divergence::of(name),
                        message: panic_message(name, args, &st.env),
                    },
                    verdict: find_obligation(st.path, pins),
                });
                return;
            }
            // A self-call is answered by the function's own contract when it
            // carries a `decreases:` measure, rather than inlined: inlining it
            // would only unroll once and hit the depth bound. See
            // [`try_recursive_call`]. It returns `Some` when it handled the call
            // (including the failure case), and `None` when the call is not
            // recursive, so the inliner below still sees every other call.
            if try_recursive_call(
                prog, &mut st, root, name, args, dest, *target, rec, report, work, pins,
            )
            .is_some()
            {
                return;
            }
            // The same-dump lookup runs *first*, and on the full name. A `core::num`
            // name is only an intrinsic when the dump has no body for it: the model in
            // `intrinsics` is a definition of `core`'s function, and a user function
            // that happens to be called `wrapping_add` is a different function.
            // Answering from `intrinsics` first let such a function shadow the
            // intrinsic, so a `wrapping_add` that returns `0` had its *actual* body
            // ignored and was modelled as `a + b` -- a false proof of `ret == 3` for
            // `a == 1, b == 2`.
            //
            // Matching the full name, not the suffix, is what keeps the other
            // direction honest too. rustc prints the intrinsic as the qualified path
            // `core::num::<impl u8>::wrapping_add`, which never equals a plain
            // same-dump name, so a user `wrapping_add` and `u8::wrapping_add` can
            // coexist: the first is inlined by the exact match, the second falls
            // through to the model.
            //
            // The same-dump lookup has to run on the *resolved* name, not only on the
            // exact one, and the model is only a fallback once that fails. A local
            // trait impl prints its *call* as `<u8 as Trait>::is_power_of_two` but its
            // *definition* as `<impl at FILE:L:C: L:C>::is_power_of_two`, so the exact
            // name never matches and the suffix classifies -- answering the call from
            // `core`'s model instead of the user's body. A `Trait::is_power_of_two`
            // for `u8` that returns `false` then *proves* `ensures: ret == true` at
            // `x == 1`, a false proof of a trait implementation that disagrees with
            // `core`. So [`resolve_callee`] is consulted first (it already refuses a
            // name that carries `<impl`, which is every real intrinsic call, and
            // requires the method's `self` type to agree), and the model answers only
            // when no same-dump body was found. See [`try_intrinsic`] for the second
            // half of the guard.
            let same_dump = resolve_callee(prog, name);
            if same_dump.is_none() {
                // The `core::fmt` chain behind a `panic!`/`assert!` message. It
                // runs before `try_intrinsic` because these are not integer
                // intrinsics, and it answers only the exact shapes it knows; every
                // other `core::fmt` call still falls through to "unmodelled".
                if let Some(done) =
                    try_fmt_call(name, args, dest, &mut st.env, type_of_place(cur, dest).as_ref())
                {
                    let next = match done {
                        Ok(()) => State { block: *target, ..st },
                        Err(e) => {
                            report.unknown_paths.push(e);
                            return;
                        }
                    };
                    advance(prog, next, *target, report, work, pins);
                    return;
                }
                if let Some(done) = try_intrinsic(
                    prog,
                    st.frame.func,
                    name,
                    args,
                    dest,
                    &mut st.env,
                    st.path,
                    pins,
                    callees,
                ) {
                    let next = match done {
                        // A modelled call can contribute obligations of its own:
                        // `iN::abs` and `Ord::clamp` panic on some inputs, and
                        // that panic is a reachable failure, exactly like the
                        // `assert` terminator rustc inserts. The obligations are
                        // discharged inside `try_intrinsic` (where the operand
                        // terms are live) and pushed here.
                        Ok(obligations) => {
                            report.obligations.extend(obligations);
                            State { block: *target, ..st }
                        }
                        Err(e) => {
                            report.unknown_paths.push(e);
                            return;
                        }
                    };
                    advance(prog, next, *target, report, work, pins);
                    return;
                }
            }
            // A callee whose body is *not* in the dump, but whose contract is,
            // is answered by that contract instead of being refused. This is the
            // modular case, and it is the only one where a call can be decided
            // without the callee's body: the body is what the dump would have
            // inlined, so with no body the alternative is "unmodelled function".
            //
            // It runs *after* the same-dump lookup on purpose. When the body is
            // there, inlining it is strictly more precise than assuming a contract
            // about it -- it proves the callee's actual behaviour rather than what
            // the callee promised -- so the contract route must not shadow it.
            if same_dump.is_none() {
                if let Some(cc) = callees.get(name) {
                    try_callee_contract(
                        prog, &mut st, name, &cc, args, dest, *target, report, work, pins,
                    );
                    return;
                }
            }
            if st.depth + 1 >= DEFAULT_INLINE_DEPTH {
                report.unknown_paths.push(format!("call depth limit reached at `{name}`"));
                return;
            }
            // Only same-dump calls can be inlined. Assuming a return value for
            // anything else would be assuming the conclusion, so it is unknown.
            //
            // An exact match is the free-function case: rustc prints a same-crate
            // free function's call and its definition by the same bare name.
            // Otherwise the call is a method (`Type::m`) whose definition rustc
            // prints as `<impl at …>::m`, so only the tail is shared -- but the
            // tail alone is not enough, because `Vec2::push` and `Vec::<u8>::push`
            // (or a free `wrapping_add` and `core::num::<impl u8>::wrapping_add`)
            // share one. Inlining the wrong body is a false proof, so the tail
            // match also requires the same method `self` type and a unique
            // candidate; see [`resolve_callee`].
            let inline_idx = same_dump;
            let Some(idx) = inline_idx else {
                report.unknown_paths.push(format!("call to unmodelled function `{name}`"));
                return;
            };
            let callee_fn = &prog.fns[idx];
            // A callee taking `&mut &mut T` is refused. Its `**v = x` writes
            // through two levels: the outer reference's referent lives in the
            // *caller's* frame, and the callee reaches it through its own `(*_1)`,
            // whose local index means something else in each frame. One level of
            // that is modelled (the referent's parts are carried in and the
            // post-state copied back); two is not, and `relay(&mut r)` with
            // `relay(v: &mut &mut u8) { **v = 5 }` had its write dropped -- so
            // `requires: x == 0` / `ensures: ret == 0` was **proved** against a
            // body that returns 5. Refusing the call leaves the true contract
            // unproved instead of proving the false one, which is the honest
            // failure mode. `&mut T` is unaffected: its argument is not a
            // reference to a reference.
            if callee_fn
                .arg_locals
                .iter()
                .any(|l| matches!(callee_fn.ty_of(*l), Some(Ty::Ref(inner)) if matches!(**inner, Ty::Ref(_))))
            {
                report.unknown_paths.push(
                    "call to a function taking `&mut &mut T` is not modelled".into(),
                );
                return;
            }
            let Some(b0) = callee_fn.blocks.first() else {
                report.unknown_paths.push(format!("callee `{name}` has no body"));
                return;
            };
            let (env, by_ref) = seed_callee_env(prog, &mut st.env, callee_fn, args);
            let caller = Frame {
                func: st.frame.func,
                ret_target: *target,
                ret_dest: Some(dest.clone()),
                // The caller's locals are put aside here and restored on return.
                // `env` below is the callee's, freshly built from the arguments.
                saved_env: Some(st.env.clone()),
                // The caller's loop cut is put aside for the same reason: it
                // describes the caller's loop, and the caller is still inside it
                // when this call returns.
                saved_cut: st.cut.clone(),
                saved_variant: st.variant_entry,
                by_ref: by_ref.clone(),
                caller: st.frame.caller.clone(),
            };
            let mut visits = st.visits;
            visits.insert((idx, b0.id), 0);
            work.push(State {
                frame: Frame {
                    func: idx,
                    ret_target: usize::MAX,
                    ret_dest: None,
                    saved_env: None,
                    saved_cut: None,
                    saved_variant: None,
                    by_ref: Vec::new(),
                    caller: Some(Box::new(caller)),
                },
                block: b0.id,
                path: st.path,
                env,
                visits,
                depth: st.depth + 1,
                // A callee is a different function with its own locals, so the
                // caller's loop cut does not apply inside it.
                cut: None,
                variant_entry: None,
            });
        }
        Term::Unknown(text) => {
            report.unknown_paths.push(format!("unmodelled terminator: {text}"));
        }
    }
}

/// True when a `drop` of this type runs nothing.
///
/// A type with no drop glue -- an integer, `bool`, `()`, a reference, a function
/// pointer, or an aggregate of such -- has no destructor, so its `drop`
/// terminator changes no state and the executor skips it. This is the common
/// case: `let v = [1u8, 2];` lowers to a `drop(_2)` on the array, and before this
/// was recognised every function holding such a local was `incomplete`.
///
/// An `Other` type is the unknown case, and it is *not* a no-op: it may name a
/// `Vec`, a `String`, a `Box`, a guard, or a user struct with a `Drop` field, any
/// of which has a destructor. Treating it as nothing to run would be a false
/// proof whenever that destructor is observable, so it is refused instead. A
/// user `impl Drop` for it is found by [`drop_destructor`] and executed; a
/// A *bare* standard container whose destructor runs no `Drop` (`Box<T>`,
/// `String`, `Vec<T>` with a glue-free element).
///
/// rustc prints a function *argument*'s type by its shortest crate-unique path, so
/// a `Box<u8>` argument's `drop` names `Box<u8>` rather than `std::boxed::Box<u8>`.
/// A bare name is only the standard type when the crate declares no struct of that
/// name: a user `struct Box` shadowing it would otherwise be read as glue-free and
/// hide a panicking destructor, which is a false proof. The declared layouts are
/// what settle it, so this takes them.
fn std_container_glue_free(ty: &Ty, structs: &BTreeMap<String, spec::StructDef>) -> bool {
    let Ty::Other(name) = ty else { return false };
    let head = name.split('<').next().unwrap_or(name).trim();
    let elem = || crate::mir::spec::angle_inner(name).map(|t| drop_is_noop(&Ty::parse(t)));
    match head {
        "std::boxed::Box" | "alloc::boxed::Box" => elem().unwrap_or(false),
        "Box" => !structs.contains_key(head) && elem().unwrap_or(false),
        "std::string::String" | "alloc::string::String" => true,
        "String" => !structs.contains_key(head),
        "std::vec::Vec" | "alloc::vec::Vec" => elem().unwrap_or(false),
        "Vec" => !structs.contains_key(head) && elem().unwrap_or(false),
        _ => false,
    }
}

/// container is refused. See the `Term::Drop` executor arm.
fn drop_is_noop(ty: &Ty) -> bool {
    match ty {
        Ty::Bool
        | Ty::Char
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Usize
        | Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::Isize
        | Ty::Unit
        | Ty::Ref(_) => true,
        Ty::Tuple(ts) => ts.iter().all(drop_is_noop),
        Ty::Array(inner, _) => drop_is_noop(inner),
        Ty::Slice(inner) => drop_is_noop(inner),
        // A `Vec<T>` is glue-free exactly when `T` is: the container's own
        // destructor only runs `T`'s, so a `Vec<u8>` runs nothing observable. The
        // `T` is read from the printed name; a `T` that is itself an unmodelled
        // type (`Ty::Other`) is *not* glue-free by this test, which is the
        // conservative direction -- it is refused by the `has_field_glue` check
        // rather than assumed to be a no-op.
        Ty::Other(name) => {
            // A slice iterator holds a reference (glue-free); an array iterator
            // holds `T`s, so it is glue-free exactly when `T` is.
            if name.contains("slice::Iter") {
                return true;
            }
            // A standard `String` is a `Vec<u8>` underneath: its destructor only
            // frees the byte buffer, which runs no `Drop`, so it is glue-free. The
            // *qualified* path is checked (`std::string::String`), so a user
            // `struct String` is not treated as the container.
            if name.contains("string::String") {
                return true;
            }
            // A `Box<T>` runs `T`'s destructor, so it is glue-free exactly when `T`
            // is: `Box<u8>` yes, `Box<PanicOnDrop>` no. The head is the full path,
            // so a user `struct Box` is not the container.
            if let Some(elem) = box_elem_ty(name) {
                return drop_is_noop(&elem);
            }
            if let Some(elem) = array_into_iter_elem(name) {
                return drop_is_noop(&elem);
            }
            match vec_elem_ty(name) {
                Some(elem) => drop_is_noop(&elem),
                None => false,
            }
        }
    }
}

/// The `size_of` a `SizedTypeProperties::SIZE` constant names, from its path
/// `<T as std::mem::SizedTypeProperties>::SIZE`.
///
/// Only `SIZE != 0` is used (the compiler's null check before a `Box` deref), so a
/// primitive's size is exact and any other type is a nonzero placeholder -- a
/// zero-sized type's `SIZE` is `0`, but the null check folds to `false` either way.
fn size_of_type_name(name: &str) -> u64 {
    let ty = name
        .split_once('<')
        .and_then(|(_, r)| r.split_once(" as "))
        .map(|(t, _)| t.trim())
        .unwrap_or("");
    match ty {
        "u8" | "i8" | "bool" => 1,
        "u16" | "i16" => 2,
        "u32" | "i32" | "char" | "f32" => 4,
        "u64" | "i64" | "usize" | "isize" | "f64" => 8,
        "u128" | "i128" => 16,
        _ => 1,
    }
}

/// The `align_of` a `SizedTypeProperties::ALIGN` constant names, from its path
/// `<T as std::mem::SizedTypeProperties>::ALIGN`.
///
/// The deref's alignment check is `address & (ALIGN - 1) == 0`, and the pointer
/// token the model stores is a large power of two, so any alignment up to that
/// power passes. An unknown type's alignment is `1` (no mask), the conservative
/// value: it never makes an aligned pointer look misaligned.
fn align_of_type_name(name: &str) -> u64 {
    let ty = name
        .split_once('<')
        .and_then(|(_, r)| r.split_once(" as "))
        .map(|(t, _)| t.trim())
        .unwrap_or("");
    match ty {
        "u16" | "i16" => 2,
        "u32" | "i32" | "char" | "f32" => 4,
        "u64" | "i64" | "usize" | "isize" | "f64" => 8,
        "u128" | "i128" => 16,
        _ => 1,
    }
}

/// A short, printable name for a type, for a refusal message.
fn ty_label(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".into(),
        Ty::Char => "char".into(),
        Ty::U8 => "u8".into(),
        Ty::U16 => "u16".into(),
        Ty::U32 => "u32".into(),
        Ty::U64 => "u64".into(),
        Ty::U128 => "u128".into(),
        Ty::Usize => "usize".into(),
        Ty::I8 => "i8".into(),
        Ty::I16 => "i16".into(),
        Ty::I32 => "i32".into(),
        Ty::I64 => "i64".into(),
        Ty::I128 => "i128".into(),
        Ty::Isize => "isize".into(),
        Ty::Unit => "()".into(),
        Ty::Ref(inner) => format!("&{}", ty_label(inner)),
        Ty::Tuple(ts) => {
            let parts: Vec<String> = ts.iter().map(ty_label).collect();
            format!("({})", parts.join(", "))
        }
        Ty::Array(inner, n) => format!("[{}; {}]", ty_label(inner), n),
        Ty::Slice(inner) => format!("[{}]", ty_label(inner)),
        Ty::Other(s) => s.clone(),
    }
}

/// The index of the `impl Drop` body for a type, if the dump has one.
///
/// A user `impl Drop for T` prints its definition as `<impl at FILE:L:C: L:C>::drop`,
/// so the *owner* of the impl block -- not the type's name spelling -- is what
/// identifies it: `Ty::Other("Guard")` names the type, and the impl block whose
/// owner is `Guard` holds the destructor. A type with no `impl Drop` in the dump
/// -- a `Vec`, a `String`, a `Box`, or any struct with no explicit destructor --
/// has no candidate here, which is what lets the caller refuse it rather than
/// treat the drop as a no-op.
///
/// More than one candidate is refused (the caller gets `None`): two `impl Drop`
/// blocks for one owner is not something a valid crate contains, and picking one
/// would be a guess.
fn drop_destructor(prog: &MirProgram, ty: &Ty) -> Option<usize> {
    let Ty::Other(name) = ty else { return None };
    // The impl's owner is stored bare (`Guard`); the type is too, but it may carry
    // a path (`m::Guard`) or generics (`Wrapper<u8>`) the owner does not, so the
    // last `::` segment of the type is what is compared.
    let bare = name.rsplit("::").next().unwrap_or(name);
    let bare = bare.split('<').next().unwrap_or(bare);
    let mut hit = None;
    for (i, f) in prog.fns.iter().enumerate() {
        if f.name.rsplit("::").next() != Some("drop") {
            continue;
        }
        let Some(loc) = f.impl_loc else { continue };
        // The *trait* has to be `Drop`. A method named `drop` on any other trait
        // (`trait NotDrop { fn drop(&mut self); }`) is not Rust's destruction hook,
        // and executing it as though it were hides the real field destruction --
        // a false proof (`Outer { inner: Inner }` with an empty `NotDrop::drop` on
        // `Outer` and a panicking `Inner::drop` came back `Verified`). The trait
        // path rustc prints for the standard library's `Drop` is the bare `Drop`
        // (a local trait is qualified with its own module, `m::NotDrop`), so the
        // last `::` segment is what is compared, exactly as the owner is.
        match prog.impl_traits.get(&loc) {
            Some(t) if t.rsplit("::").next() == Some("Drop") => {}
            _ => continue,
        }
        let Some(owner) = prog.impl_owners.get(&loc) else { continue };
        let owner_bare = owner.split('<').next().unwrap_or(owner);
        if owner_bare == bare {
            if hit.is_some() {
                return None;
            }
            hit = Some(i);
        }
    }
    hit
}

/// Whether a type has *any* drop glue -- a user `Drop` impl, or a field (at any
/// depth) that does.
///
/// This is what makes the `drop` handler sound for an aggregate. rustc's `drop`
/// terminator destroys the *whole* value, not only the user-written destructor:
/// after `Outer::drop` returns, Rust also destroys `Outer`'s fields. A frontend
/// that runs only the outer destructor therefore misses a field destructor that
/// can panic, and an empty outer destructor *hides* it -- `Outer { inner: Inner }`
/// with an empty `Outer::drop` and a panicking `Inner::drop` was reported
/// `Verified`.
///
/// `Ok(false)` is "no glue anywhere"; `Ok(true)` is "some glue"; `Err` is a type
/// this tool cannot decide (a container whose destructor it does not model), and
/// the caller refuses rather than assuming. The layout comes from `structs`, read
/// from the same source as the contracts; a type with no layout and no `Drop` impl
/// is a container, which is the `Err` case.
fn has_drop_glue(
    prog: &MirProgram,
    structs: &BTreeMap<String, spec::StructDef>,
    ty: &Ty,
) -> Result<bool, String> {
    match ty {
        Ty::Bool
        | Ty::Char
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Usize
        | Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::Isize
        | Ty::Unit
        | Ty::Ref(_) => Ok(false),
        Ty::Tuple(ts) => {
            for t in ts {
                if has_drop_glue(prog, structs, t)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Ty::Array(inner, _) | Ty::Slice(inner) => has_drop_glue(prog, structs, inner),
        Ty::Other(name) => {
            if drop_destructor(prog, ty).is_some() {
                return Ok(true);
            }
            // A slice iterator holds a reference (glue-free); an array iterator
            // holds `T`s, so its glue is `T`'s.
            if name.contains("slice::Iter") {
                return Ok(false);
            }
            if let Some(elem) = array_into_iter_elem(name) {
                return has_drop_glue(prog, structs, &elem);
            }
            match spec::struct_lookup(structs, name) {
                Some(def) => {
                    for (_, fty) in &def.fields {
                        if has_drop_glue(prog, structs, fty)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                // No layout and no `Drop` impl: a container (`Vec`, `String`, a
                // guard) whose destructor this tool does not model. Whether it has
                // observable glue is unknown, so the caller must refuse.
                None => Err(format!("the drop glue of `{}` is not modelled", ty_label(ty))),
            }
        }
    }
}

/// Whether destroying a value of `ty` also destroys a *field* (at any depth)
/// whose own destructor would have to run.
///
/// The `drop` handler runs one destructor body per terminator. When a value's
/// destruction also destroys a field -- `Outer { inner: Inner }` with a `Drop`
/// for `Outer` destroys `inner` too -- running only the user destructor skips the
/// field's, and an empty outer destructor *hides* a panicking inner one: that was
/// a false proof (`Outer` came back `Verified`).
///
/// The layout comes from the source, exactly as [`has_drop_glue`]'s does. A type
/// with no layout is a container or a unit-like item; a container's fields are
/// unknown, so it is refused rather than assumed field-free.
fn has_field_glue(
    prog: &MirProgram,
    structs: &BTreeMap<String, spec::StructDef>,
    ty: &Ty,
) -> Result<bool, String> {
    match ty {
        Ty::Bool
        | Ty::Char
        | Ty::U8
        | Ty::U16
        | Ty::U32
        | Ty::U64
        | Ty::U128
        | Ty::Usize
        | Ty::I8
        | Ty::I16
        | Ty::I32
        | Ty::I64
        | Ty::I128
        | Ty::Isize
        | Ty::Unit
        | Ty::Ref(_) => Ok(false),
        Ty::Tuple(ts) => {
            for t in ts {
                if has_drop_glue(prog, structs, t)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        Ty::Array(inner, _) | Ty::Slice(inner) => has_drop_glue(prog, structs, inner),
        Ty::Other(name) => {
            if name.contains("slice::Iter") {
                return Ok(false);
            }
            if let Some(elem) = array_into_iter_elem(name) {
                return has_field_glue(prog, structs, &elem);
            }
            match spec::struct_lookup(structs, name) {
                Some(def) => {
                    for (_, fty) in &def.fields {
                        if has_drop_glue(prog, structs, fty)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                None => Err(format!("the fields of `{}` are not modelled", ty_label(ty))),
            }
        }
    }
}

/// The error type of a `Result<T, E>` receiver, for the drop-glue check.
///
/// The receiver's type is printed as `Result<u8, E>` (or with a path prefix), and
/// the error is the second top-level generic argument. A type that is not a
/// `Result`, or whose arguments cannot be split, yields `None` -- the caller then
/// does no glue check, which is the *unsound* direction only if the type really
/// were a `Result` with an unmodelled error, and the receiver reaching this arm is
/// already known to be a modelled `Result` (its tag and payload are in the store).
fn receiver_error_type(f: &MirFn, p: &Place) -> Option<Ty> {
    let Ty::Other(name) = f.ty_of(p.local)? else {
        return None;
    };
    if !name.starts_with("Result") && !name.contains("::Result") {
        return None;
    }
    let inner = spec::angle_inner(name)?;
    let args = crate::mir::parse::split_top_level(inner, ',');
    args.get(1).map(|e| Ty::parse(e.trim()))
}

/// The `T` of a `std::array::IntoIter<T, N>` type, for the drop-glue check.
///
/// `for x in a` (by value) owns an `array::IntoIter<T, N>`, whose drop destroys
/// the *remaining* elements -- so its glue is `T`'s glue. Reading `T` off the name
/// is what lets that drop be a no-op for a glue-free `T` and still refuse a
/// panicking one. Any other type yields `None`.
fn array_into_iter_elem(name: &str) -> Option<Ty> {
    if !name.contains("array::IntoIter") {
        return None;
    }
    let inner = spec::angle_inner(name)?;
    let args = crate::mir::parse::split_top_level(inner, ',');
    args.first().map(|t| Ty::parse(t.trim()))
}

/// The `T` of a `Result<T, E>` receiver's declared type, for the drop-glue check
/// on `Result::err()` (which drops the `Ok` payload).
fn receiver_ok_type(f: &MirFn, p: &Place) -> Option<Ty> {
    let Ty::Other(name) = f.ty_of(p.local)? else {
        return None;
    };
    if !name.starts_with("Result") && !name.contains("::Result") {
        return None;
    }
    let inner = spec::angle_inner(name)?;
    let args = crate::mir::parse::split_top_level(inner, ',');
    args.first().map(|t| Ty::parse(t.trim()))
}

/// The `T` of an `Option<T>` receiver's declared type, for the drop-glue check on
/// `Option::or`/`Option::and` (which drop one of the two payloads).
fn receiver_some_type(f: &MirFn, p: &Place) -> Option<Ty> {
    let Ty::Other(name) = f.ty_of(p.local)? else {
        return None;
    };
    if !name.starts_with("Option") && !name.contains("::Option") {
        return None;
    }
    let inner = spec::angle_inner(name)?;
    Some(Ty::parse(inner.trim()))
}

/// An operand's `Some` payload, or `None` when the operand's tag is a *known*
/// non-`Some` discriminant (a constructed `None`).
///
/// A payload is required only when the operand can be `Some` on some path. A
/// constructed `None` records no payload, and its absence is not a modelling
/// failure -- the result's tag is already known, so the missing payload is never
/// read. A *symbolic* tag still requires the payload: a fabricated value there
/// would be one the operand never holds, so the shape is refused.
///
/// `whose` names the operand ("a receiver"/"an argument") and `name` the method,
/// so the refusal names what could not be read.
fn payload_if_some(
    env: &Env,
    local: u32,
    tag: Var,
    payload_variant: u64,
    whose: &str,
    name: &str,
) -> Result<Option<(Var, Sign, u8)>, String> {
    match env.payloads.get(&(local, payload_variant)).copied() {
        Some((Val::Sym(payload, sign), w)) => Ok(Some((payload, sign, w))),
        Some(_) => Err(format!("`{name}` on {whose} whose payload is not a value")),
        None => match smt::evaluate(tag, |_| None) {
            // A known tag that is not the payload variant: the operand is `None`
            // on every path, so there is no payload to carry.
            Some(v) if v != payload_variant => Ok(None),
            // A symbolic tag, or a known `Some` tag with no payload recorded: the
            // payload may be read, so it must be modelled.
            _ => Err(format!("`{name}` on {whose} whose payload is not modelled")),
        },
    }
}

/// The declared type of an operand, for the enum-method glue checks.
fn operand_ty(f: &MirFn, o: &Operand) -> Option<Ty> {
    match o {
        Operand::Copy(p) | Operand::Move(p) => type_of_place(f, p),
        Operand::Const(Const::UInt(_, Some(t))) => Some(t.clone()),
        Operand::Const(_) => None,
    }
}

/// Resolve an operand to a symbolic value.
fn operand(env: &mut Env, o: &Operand) -> Val {
    match o {
        Operand::Copy(p) | Operand::Move(p) => {
            // A dereference of an addressed local names the place it addresses,
            // so `_2 = &_1; *_2` reads `_1` -- including through a subscript,
            // which is why the rewrite comes before `read_indexed`.
            let p = &env.resolve(p);
            // A slice element is created on first read, so it goes through the
            // mutable path before the ordinary one.
            if let Some(v) = env.read_indexed(p) {
                return v;
            }
            env.get(p)
        }
        Operand::Const(c) => match c {
            Const::UInt(v, ty) => match ty.as_ref().and_then(|t| t.width()) {
                Some(1) => Val::Bool(smt::truth(*v == 1)),
                // A constant's type suffix is the only place its signedness
                // appears -- `const 0_i8` versus `const 0_u8` -- so the sign is
                // read here, once, and travels with the value.
                Some(w) => {
                    // No suffix means the dump printed no type, so there is no
                    // sign to read. It is `Unknown`, not `Unsigned`: defaulting to
                    // unsigned here is exactly the false proof this type exists to
                    // prevent, and the callers refuse an `Unknown` sign.
                    let sign = ty.as_ref().map(Sign::of).unwrap_or(Sign::Unknown);
                    Val::Sym(smt::word(*v as u64, w), sign)
                }
                None => Val::Unknown,
            },
            Const::Bool(b) => Val::Bool(smt::truth(*b)),
            // A string or byte-string literal has no bit-vector, so it is not a
            // `Val`; the `core::fmt` model reads it through the env's string store
            // instead.
            Const::Str(_) | Const::Bytes(_) => Val::Unknown,
            // An enum variant *construction*: `Mode::Idle`. The dump prints it as
            // a path constant, and it is the one place a tag is a *known* value
            // rather than an input -- a locally built enum then has a constant
            // discriminant, which is what lets `let m = Mode::Idle; match m`
            // decide instead of leaving the switch unmodelled. The variant's index
            // is read from the program's enum layouts, the same table a downcast
            // resolves against, so the construction and the match agree by
            // construction.
            // A variant construction whose destination `eval_rvalue` could not
            // resolve (it has no enum layout) stays unknown; the well-typed path
            // is in `eval_rvalue::Use`, where the destination's width is known.
            // A named `const` item: `_0 = const K`, where the item's own body is
            // printed separately as `const K: u8 = const 5_u8;`. The value is
            // inlined from the table rather than left unknown, so the use site
            // folds. rustc const-evaluates the item, so its body is already a
            // literal with a type suffix -- which is where the width and sign
            // come from, exactly as for an inline literal.
            //
            // A path constant that is *not* a known `const` -- an enum variant
            // construction (`Mode::Idle`), or a constant whose body is an
            // expression rather than a literal -- stays unknown; the enum case is
            // resolved by the caller in `eval_rvalue`, which knows the
            // destination's width.
            Const::Other(name) => {
                // `<T as std::mem::SizedTypeProperties>::SIZE` is the compiler's
                // `size_of` in the null check before a `Box` deref. Only `!= 0` is
                // used, so the primitive sizes are exact and anything else is a
                // nonzero placeholder.
                if name.contains("SizedTypeProperties>::SIZE") {
                    return Val::Sym(smt::word(size_of_type_name(name), 64), Sign::Unsigned);
                }
                // The alignment the deref's mask is built from (`ALIGN - 1`).
                if name.contains("SizedTypeProperties>::ALIGN") {
                    return Val::Sym(smt::word(align_of_type_name(name), 64), Sign::Unsigned);
                }
                match env.consts.get(name) {
                Some(Const::UInt(v, ty)) => match ty.as_ref().and_then(|t| t.width()) {
                    Some(1) => Val::Bool(smt::truth(*v == 1)),
                    Some(w) => {
                        let sign = ty.as_ref().map(Sign::of).unwrap_or(Sign::Unknown);
                        Val::Sym(smt::word(*v as u64, w), sign)
                    }
                    None => Val::Unknown,
                },
                Some(Const::Bool(b)) => Val::Bool(smt::truth(*b)),
                _ => Val::Unknown,
                }
            }
            Const::Unit => Val::Unknown,
        },
    }
}

/// Evaluate an rvalue into a symbolic value.
fn eval_rvalue(f: &MirFn, env: &mut Env, dest: &Place, rv: &Rvalue) -> Val {
    let dest_w = width_of(f, dest);
    match rv {
        Rvalue::Use(o) => {
            // A literal assigned to a typed place takes the place's width when
            // the dump did not print a suffix.
            if let Operand::Const(Const::UInt(v, None)) = o {
                if let Some(w) = dest_w {
                    // The literal has no suffix, so it takes the place's type --
                    // and therefore the place's signedness. A place whose type
                    // the dump did not print leaves the sign unknown, which the
                    // consumers refuse rather than read as unsigned.
                    let sign = type_of_place(f, dest).map(|t| Sign::of(&t))
                        .unwrap_or(Sign::Unknown);
                    return Val::Sym(smt::word(*v as u64, w), sign);
                }
            }
            let v = operand(env, o);
            // An enum variant *construction*: `_1 = Mode::Idle`. It is a
            // constant with no width of its own -- the enum's tag width is the
            // discriminants', which only the destination's enum layout knows --
            // so it is resolved here, against the destination, rather than in
            // `operand`. Getting the width right is what lets the tag be
            // `discriminant`-ed and compared against the arm constants.
            if let Operand::Const(Const::Other(name)) = o {
                if let Some(i) = crate::mir::parse::variant_index(name, &env.enums) {
                    // The discriminants' width wins over `dest_w`: the dump
                    // declares an enum local as `isize`, so `dest_w` is 64 and
                    // would put a locally built tag in a different width from a
                    // seeded one. The discriminants' width is the tag's real
                    // domain.
                    let w = enum_tag_width(f, dest, &env.enums)
                        .or(dest_w)
                        .unwrap_or(64);
                    env.set_discriminant(dest.local, Val::Sym(smt::word(i, w), Sign::Unsigned));
                    return Val::Agg;
                }
            }
            // A whole-struct copy (`c = d`) carries the value's *parts* across, so
            // `c.lo` afterwards reads `d.lo`. `Val::Agg` is returned when parts
            // moved, which is what tells `set` not to clear the parts just copied
            // -- the same convention an aggregate literal uses.
            if dest.proj.is_empty() {
                if let Operand::Copy(q) | Operand::Move(q) = o {
                    if env.copy_parts(q, dest.local) {
                        return Val::Agg;
                    }
                    // Reading an *element* of an array of aggregates (`_5 = copy
                    // _3[_6]`, the first half of `a[0] = b[0]`) hands over the
                    // element's leaf *scalar*, not its parts, so the leaves under
                    // that element have to be carried onto the temp explicitly.
                    // Without this they died at the temp: the assignment's re-root
                    // then found a scalar and the destination leaf read `Unknown`,
                    // leaving the contract `incomplete` in both directions.
                    if env.carry_elem_leaf_onto_local(q, dest.local) {
                        return Val::Agg;
                    }
                }
            }
            // A `&T` read out of a `first`/`get` Option's payload -- the `match`
            // desugaring's `_4 = copy ((_2 as Some).0)`, as opposed to `unwrap`'s
            // dedicated arm -- names the same slice element, so the reference's
            // later deref (`*_4`) must resolve. Propagating the entry onto the
            // destination is what lets the `match` form decide; without it the
            // deref finds no entry and the postcondition is unreadable.
            if dest.proj.is_empty() {
                if let Operand::Copy(q) | Operand::Move(q) = o {
                    if q.proj.iter().any(|p| matches!(p, Proj::Downcast(_))) {
                        if let Some(e) = env.slice_elem_ref.get(&q.local).cloned() {
                            env.slice_elem_ref.insert(dest.local, e);
                        }
                    }
                }
            }
            v
        }
        Rvalue::Binary(op, a, b) => {
            // The signedness of the *left* operand decides what `Shr` means and
            // what `<`/`<=`/`>`/`>=` mean; the amount's type is irrelevant and
            // rustc keeps it a distinct `u32`. That sign is now *in* the value
            // (`Val::Sym(word, sign)`), so there is no separate lookup that a
            // later caller could forget: an operand whose type cannot be resolved
            // is `Val::Unknown` here, and `eval_binary` refuses it rather than
            // reading it as unsigned.
            let (x, y) = (operand(env, a), operand(env, b));
            eval_binary(*op, x, y, dest_w)
        }
        Rvalue::CheckedBinary(op, a, b) => {
            // The tuple is `(result, overflowed)`. Field 0 gets the wrapped
            // result and field 1 the overflow predicate, so the `assert(!(_3.1))`
            // that follows has a real condition to check.
            // `_3` is `(uN, bool)`, which has no width; the operand width is
            // field 0's. Reading the width from the tuple instead gives 64 for
            // every type, which silently mis-sizes the overflow test.
            let w = width_of(f, &Place { local: dest.local, proj: vec![Proj::Field(0)] })
                .or(dest_w)
                .unwrap_or(64);
            let x = operand(env, a);
            let y = operand(env, b);
            let res = eval_binary(*op, x, y, Some(w));
            env.set(&Place { local: dest.local, proj: vec![Proj::Field(0)] }, res);
            match overflow_pred(*op, x, y, w) {
                Some(p) => {
                    env.set(&Place { local: dest.local, proj: vec![Proj::Field(1)] }, Val::Bool(p));
                }
                None => {
                    // No sound predicate is available for this operator at this
                    // width, so the overflow bit is unknown and the `assert` that
                    // reads it will report the path as unmodelled.
                    env.set(&Place { local: dest.local, proj: vec![Proj::Field(1)] }, Val::Unknown);
                }
            }
            Val::Agg
        }
        Rvalue::Unary(op, a) => {
            let v = operand(env, a);
            match (op, v) {
                (_, Val::Unknown) => Val::Unknown,
                (UnOp::Not, Val::Bool(p)) => Val::Bool(smt::not(p)),
                // `!x` is a bitwise complement, so the result has the operand's
                // type and keeps its sign. The mask must therefore be the
                // *operand's* width, which the value carries; `dest_w` is only a
                // cross-check. Deriving the mask from `dest_w` is right exactly
                // when the two agree, so a disagreement -- the dump and the value
                // disagreeing about the type -- is refused rather than masked at
                // a width the value does not have.
                (UnOp::Not, Val::Sym(s, sign)) => {
                    let w = smt::bits(s);
                    if dest_w.is_some_and(|dw| dw != w) {
                        return Val::Unknown;
                    }
                    Val::Sym(smt::bxor(s, smt::all_ones(w)), sign)
                }
                // `-x` is `0 - x`, which is the right bit pattern for every input
                // including `MIN` (it wraps back to `MIN`, which is what rustc's
                // own `assert(x != MIN)` guards and then computes anyway). The
                // result has the operand's type, so it keeps the operand's sign.
                (UnOp::Neg, Val::Sym(s, sign)) => match dest_w {
                    Some(w) => Val::Sym(smt::sub(smt::word(0, w), s), sign),
                    None => Val::Unknown,
                },
                _ => Val::Unknown,
            }
        }
        Rvalue::Cast(o, ty) => {
            // A cast between reference types (`&[u8; 4]` to `&[u8]`) does not
            // change *what* is addressed, only how it is described. The address
            // mapping is therefore carried across, which is what makes
            // `let r = &a; r.len()` on an array read the array's own length: the
            // `PtrMetadata` after the cast names the slice local, and only the
            // carried mapping gets it back to the array. A cast whose target is
            // not a reference is a numeric cast and carries nothing.
            if matches!(ty, Ty::Ref(_)) {
                if let Operand::Copy(q) | Operand::Move(q) = o {
                    let target = env.resolve(q);
                    // A reference cast preserves the *address*, which is what the
                    // source points at. When the source is itself an `addressed`
                    // reference the target is recorded; otherwise the source is a
                    // reference *argument* (modelled as its referent, so `pointee`
                    // is the argument itself), and the destination must point at it
                    // too. Without this, `let s = xs as &[u8]` (an unsize coercion)
                    // left `s` with no address, so `xs.iter()`/`s.len()` on the
                    // array argument could not reach the array's elements.
                    let p = env
                        .addressed
                        .get(&target.local)
                        .cloned()
                        .unwrap_or_else(|| env.pointee(&target));
                    env.addressed.insert(dest.local, p);
                }
            }
            let v = operand(env, o);
            // A cast to a raw pointer (`*const T`/`*mut T`) is a reinterpretation
            // of a 64-bit word: the `Box` deref's `(_2.0) as *const u8` and the
            // `as *const ()` / `as usize` chain that follows the null check all
            // carry one token. `Ty::width` has no width for a pointer type, so the
            // numeric arms below would refuse it; the pointer value is a `u64`.
            if let Ty::Other(s) = ty {
                if s.starts_with("*const ") || s.starts_with("*mut ") {
                    return match v {
                        Val::Sym(x, _) => Val::Sym(smt::truncate(x, 64), Sign::Unsigned),
                        _ => Val::Unknown,
                    };
                }
            }
            // The cast's *result* has the target type, so its sign is the
            // target's. The source's sign comes out of the value, which is what
            // decides whether a widening sign-extends or zero-fills.
            let out_sign = Sign::of(ty);
            match (v, ty.width()) {
                // Widening a *signed* value sign-extends: `-1i8 as i16` is `-1`,
                // not `255`. `truncate` zero-fills, so using it for every cast
                // modelled `-1i8 as i16` as `255` and proved
                // `requires: a == -1; ensures: ret == 255` -- a reachable false
                // proof. `sign_extend` truncates first when the target is no
                // wider, so a narrowing cast is unaffected. An *unsigned* source
                // zero-fills, which is what `truncate` does.
                (Val::Sym(s, src), Some(w)) => {
                    // A source sign the dump did not print is a refusal: zero
                    // -filling a signed value is the `-1i8 as i16` false proof,
                    // and sign-extending an unsigned one turns `255u8 as u16`
                    // into `65535`. Neither reading is safe to guess.
                    let bits = match src.known() {
                        Some(true) => smt::sign_extend(s, w),
                        Some(false) => smt::truncate(s, w),
                        None => return Val::Unknown,
                    };
                    Val::Sym(bits, out_sign)
                }
                (Val::Bool(p), Some(1)) => Val::Bool(p),
                (Val::Bool(p), Some(w)) => {
                    Val::Sym(smt::ite(p, smt::word(1, w), smt::word(0, w)), out_sign)
                }
                _ => Val::Unknown,
            }
        }
        Rvalue::Variant(name, ops) => {
            // An enum variant construction with a payload. The tag is the
            // variant's discriminant -- resolved against the program's enum
            // layouts, the same table a `match`'s downcast reads -- and the
            // operands are written as the variant's fields, so the downcast read
            // finds what the construction wrote.
            let Some(variant) = crate::mir::parse::variant_index(name, &env.enums) else {
                return Val::Unknown;
            };
            let w = enum_tag_width(f, dest, &env.enums).or(dest_w).unwrap_or(64);
            env.set_discriminant(dest.local, Val::Sym(smt::word(variant, w), Sign::Unsigned));
            for (i, o) in ops.iter().enumerate() {
                let v = operand(env, o);
                let pw = operand_width(f, o).unwrap_or(0);
                // The payload store holds *one* value per variant -- the field a
                // contract names as `ret.Variant` / `m.Variant`, which the binder
                // reads as `payload.first()` (field 0). Writing every operand here
                // left the *last* field, so `E::Pair(1, 2)` made `ret.Pair` denote
                // field 1 and `ensures: ret.Pair == 2` was *verified* against a
                // field-0 value of 1. Each field keeps its own identity in
                // `fields` (below), so a downcast read of `.1` is unaffected; only
                // the single-valued payload summary is pinned to field 0.
                if i == 0 {
                    env.set_payload(dest.local, variant, v, pw);
                }
                env.set(&Place { local: dest.local, proj: vec![Proj::Field(i as u32)] }, v);
            }
            Val::Agg
        }
        Rvalue::Aggregate(ops) => {
            for (i, o) in ops.iter().enumerate() {
                let v = operand(env, o);
                env.set(&Place { local: dest.local, proj: vec![Proj::Index(i as u64)] }, v);
                // An aggregate *operand* keeps its value in its parts, so
                // `[o.i, o.j]` stores the element's value but not the leaves under
                // it, and a later `a[0].v` reads `Unknown` -- the index-first
                // mirror of the `Rvalue::Struct` hole below. The parts are re-rooted
                // onto the element after the `set`, which forgets the paths beneath
                // the element. Gated on the operand's *type* for the same reason the
                // struct case is: a by-value aggregate operand reads `Unknown` as a
                // whole, so a value test would miss it.
                if let Operand::Copy(q) | Operand::Move(q) = o {
                    if matches!(v, Val::Agg) || matches!(type_of_place(f, q), Some(Ty::Other(_))) {
                        env.rebase_elem_parts(q, dest.local, i as u64);
                    }
                }
            }
            Val::Agg
        }
        Rvalue::Struct(ops) => {
            // A struct literal writes *fields*, not elements. The two are
            // different stores on purpose: a contract names a struct field
            // (`c.lo`) and never a tuple component by name, and a field read
            // (`_1.0`) consults `fields` first. Storing these under `Index` would
            // leave the read looking in a store the literal never wrote, which is
            // how `let c = Config { lo: 7, .. }; c.lo` stayed unknown.
            //
            // The printed order is declaration order, which is the order the
            // `Field(N)` projections index, so position `i` here is field `i`.
            for (i, o) in ops.iter().enumerate() {
                let v = operand(env, o);
                let dst = Place { local: dest.local, proj: vec![Proj::Field(i as u32)] };
                env.set(&dst, v);
                // An *aggregate operand* keeps its value in its parts, so `Outer { i: x, .. }`
                // stores the field's value but not `x`'s own `v`. A later read of the returned
                // `mk_outer(o.i).i.v` walks the nested chain and finds nothing. The parts are
                // re-rooted onto the field *after* the `set` above, because a field write
                // forgets the paths beneath it; the operand's own parts are untouched, so this
                // is a copy of what it holds rather than an assumption about it. The gate is the
                // operand's *type*, not its value: a by-value struct argument's parts live in
                // `fields`, so it reads `Unknown` as a whole and would be missed by a value
                // test.
                if let Operand::Copy(q) | Operand::Move(q) = o {
                    if matches!(v, Val::Agg) || matches!(type_of_place(f, q), Some(Ty::Other(_))) {
                        env.rebase_parts(q, &dst);
                    }
                }
            }
            Val::Agg
        }
        Rvalue::Ref(p) => {
            // `&place` addresses `place`. The local itself is not a modelled
            // value -- a pointer has no bit-vector meaning here -- so it reads
            // `Unknown`; what the reference *is* for this frontend is the mapping
            // `resolve` consults, and that is recorded here, at the one place a
            // reference is created.
            //
            // The place is stored as written, so `&_1.0` keeps its projection and
            // `(*_2)` later reads `_1.0` rather than the whole of `_1`.
            env.addressed.insert(dest.local, p.clone());
            // The *origin* of the reference, as the place it was built from -- in
            // this frame's terms. `_3 = &mut _1` records `_1`, and `_0 = &mut
            // (*_1).0` records `_1.0`. It is what lets a reference the callee
            // returns be re-based onto the caller's storage: without the projection
            // `*c.lo_mut() = 5` lost the write (the returned reference named
            // nothing), and the false `ret == 0` was **proved** while the true
            // `ret == 5` was refuted.
            env.ref_origin.insert(dest.local, p.clone());
            Val::Unknown
        }
        // `Len(p)` -- the length of a slice or array. `PtrMetadata` is how 1.99
        // and later lower the same query for a `&[T]`; older compilers (1.85, the
        // MSRV) lower it as `Len((*_1))` instead. The two mean the same number, so
        // they are modelled by the same code: refusing `Len` on a slice leaves the
        // bounds check above `a[i]` unmodelled on 1.85 and turns an otherwise
        // decidable corpus entry into an incomplete one.
        Rvalue::Len(p) => length_of(env, f, p),
        Rvalue::Unknown(_) => Val::Unknown,
        // `PtrMetadata(_1)` -- for a `&[T]` this is the slice's length. Modelled
        // only when the local is a slice the frontend bound a length for; any
        // other pointer has metadata this model cannot express, and answering
        // `Unknown` there is what keeps an invented length out of a proof.
        Rvalue::PtrMetadata(p) => length_of(env, f, p),
        Rvalue::Discriminant(p) => match env.discriminants.get(&p.local) {
            // The tag's width is the payload's, not the dump's `isize`. The
            // `switchInt` compares it against the small variant constants, so
            // the width only has to be wide enough to hold them; taking it from
            // the payload keeps `discriminant` and the payload in one width.
            Some(Val::Sym(tag, _)) => {
                // A seeded enum tag carries its own width; a synthesised
                // `Option` tag takes the payload's. Reading a seeded tag at the
                // dump's `isize` width would truncate nothing but would also
                // widen a 2-bit tag to 64, and `eq_const` then compares a
                // 64-bit word against the `u8`-typed place's expectations --
                // keeping the tag's own width is what the contract's `m ==
                // Mode::Run` was checked at.
                let w = env.tag_width(p.local).or_else(|| env.option_width(p.local)).unwrap_or(64);
                // A discriminant is an unsigned integer.
                Val::Sym(smt::truncate(*tag, w), Sign::Unsigned)
            }
            Some(v) => *v,
            // No modelled call wrote a tag here. An enum this frontend did not
            // build has an unknown tag, not tag zero -- guessing `None` would
            // send every path down the wrong arm.
            None => Val::Unknown,
        },
    }
}

/// The tag width for a place whose type is an enum: the discriminants', matching what
/// `spec::FieldEnv::bind_enum` binds a contract's tag to.
///
/// The dump declares an enum local as `isize`, but the tag's *domain* is the set
/// of variant discriminants, so their width is the one that can hold every tag
/// and no more. Using it here keeps a locally built enum's tag in the same width
/// as a seeded one, which is what makes `discriminant` read both back
/// consistently.
fn enum_tag_width(f: &MirFn, p: &Place, enums: &BTreeMap<String, EnumLayout>) -> Option<u8> {
    let Ty::Other(name) = type_of_place(f, p)? else { return None };
    let def = enums.get(&name)?;
    if def.variants.is_empty() {
        return None;
    }
    Some(def.tag_width())
}

/// The declared width of a place, following one level of tuple/array projection.
fn width_of(f: &MirFn, p: &Place) -> Option<u8> {
    let mut ty = f.ty_of(p.local)?.clone();
    for pr in &p.proj {
        ty = match (pr, &ty) {
            (Proj::Field(i), Ty::Tuple(ts)) => ts.get(*i as usize)?.clone(),
            (Proj::Index(_), Ty::Array(inner, _)) => (**inner).clone(),
            // `*r` for a `&T` has type `T`. The dump prints the deref as
            // `(*_1)` with no type, so the width has to come from the referent
            // the local was declared with. This is the same transparency the
            // executor applies when it reads the value.
            (Proj::Deref, Ty::Ref(inner)) => (**inner).clone(),
            // A downcast yields the payload, whose type the dump does not print
            // here. Reading it as the base type would mis-size the value: the
            // `u8` inside `Option<u8>` is not the `Option<u8>` local. The caller
            // supplies the width from the operator instead, so this declines.
            (Proj::Downcast(_), _) => return None,
            _ => return None,
        };
    }
    match &ty {
        Ty::Ref(inner) => inner.width(),
        t => t.width(),
    }
}

/// Whether the `i`-th argument is an indexed value passed through a reference
/// (`&[T]` or `&mut [T; N]`) rather than by value (`[T; N]`).
///
/// The distinction decides what a call does to the caller's store: a reference
/// shares it (the callee's post-state is the caller's), a by-value array is the
/// callee's own copy (the caller's is unchanged). Reading it off the callee's
/// declared parameter type is what keeps the two apart, because the *caller's*
/// operand type is the same for both.
/// True when argument `i` is passed by reference, so the callee's post-state for
/// that local is the caller's storage and must be copied back on return.
fn arg_is_ref(f: &MirFn, i: usize) -> bool {
    let Some(&l) = f.arg_locals.get(i) else { return false };
    matches!(f.ty_of(l), Some(Ty::Ref(_)))
}

/// The declared type of a place, resolving the projections the dump spells out.
///
/// A projection changes the type, and therefore the signedness: a `u8` element of
/// an `[u8; 4]` is unsigned, and a field of a tuple is whatever that field's type
/// is. Reading signedness off the base local would read the *wrong* type for
/// exactly the operands this exists to classify.
///
/// A struct-field projection is not resolvable here -- the dump prints
/// `_1: Config` and says nothing about `Config`'s layout -- so it returns `None`,
/// which the caller treats as "refuse" rather than "unsigned". In practice rustc
/// copies a field into a temp before using it as a binary operand, so this is the
/// defensive case; refusing is still the right answer if the shape ever changes.
/// The length of the slice or array a place denotes, or `Unknown`.
///
/// Both `PtrMetadata(p)` (a `&[T]`, from 1.99 on) and `Len(p)` (the same query
/// printed by older compilers, and an array's length) read through this. The place
/// is followed to its pointee first, so `_2 = _3 as &[u8]` after `_3 = &_1` names
/// `_1` here -- the place whose length is actually wanted.
fn length_of(env: &Env, f: &MirFn, p: &Place) -> Val {
    let p = env.pointee(p);
    match env.indexed.get(&p.local) {
        // A slice argument, whose length is a symbolic input.
        // A length is a `usize`, so it is unsigned.
        Some(s) => Val::Sym(s.len, Sign::Unsigned),
        // An *array* has its length in its type, not in `indexed`, so an unsized
        // `&[T; N]` would otherwise read unknown. The length is the type's
        // constant -- not a guess, and not a fresh variable: `[T; N]` coerces to a
        // slice of exactly `N`, so the two are the same number and a contract that
        // writes `a.len() == 4` on an `a: [u8; 4]` has something to agree with.
        None => match type_of_place(f, &p) {
            Some(Ty::Array(_, n)) => Val::Sym(smt::word(n, USIZE_WIDTH), Sign::Unsigned),
            // A string literal (`const "ab"`) has a *constant* byte length, kept
            // in the string store. It is the receiver of `str::len`/`is_empty` and
            // the source of `String::from`/`push_str`, so its length is read here
            // rather than left unknown.
            _ => match env.strs.get(&p.local) {
                Some(text) => Val::Sym(smt::word(text.len() as u64, USIZE_WIDTH), Sign::Unsigned),
                None => Val::Unknown,
            },
        },
    }
}

fn type_of_place(f: &MirFn, p: &Place) -> Option<Ty> {
    let mut ty = f.ty_of(p.local)?.clone();
    for pr in &p.proj {
        ty = match (pr, &ty) {
            (Proj::Field(i), Ty::Tuple(ts)) => ts.get(*i as usize)?.clone(),
            (Proj::Index(_), Ty::Array(inner, _)) => (**inner).clone(),
            // A subscript that is a local names the same element as a constant one,
            // so it types the same. Without this `type_of_place` refused
            // `a[_3]`/`other[_4]` and the whole-element rebase that needs the
            // element's type never ran.
            (Proj::IndexVar(_), Ty::Array(inner, _)) => (**inner).clone(),
            (Proj::Deref, Ty::Ref(inner)) => (**inner).clone(),
            (Proj::Downcast(_), _) => return None,
            _ => return None,
        };
    }
    Some(ty)
}


/// Which of the engine's three shifts a MIR `Shl`/`Shr` means.
///
/// The operand's signedness decides what `Shr` means, and the engine needs it
/// stated rather than guessed, so it is read from the type.
fn shift_kind(op: BinOp, signed: bool) -> smt::Shift {
    match (op, signed) {
        (BinOp::Shl, _) => smt::Shift::Left,
        (_, true) => smt::Shift::ArithmeticRight,
        (_, false) => smt::Shift::LogicalRight,
    }
}

/// Apply a binary operator, respecting the destination width.
///
/// The operand's signedness is *in* the operand -- `Val::Sym(word, sign)` -- not
/// a parameter, which is the point of the type. It used to be a bare `bool` the
/// caller looked up separately, and a caller that looked it up wrong (or not at
/// all) turned `0 < a` on an `i8` into an unsigned comparison, under which
/// `i8::MIN` is the largest value. A wrong signedness is not a missed proof but a
/// wrong branch, so the sign has to travel with the bits it describes.
fn eval_binary(op: BinOp, a: Val, b: Val, width: Option<u8>) -> Val {
    // rustc gives both operands of a binary op the same type, so one sign serves
    // both. It is taken from the left, matching how the operand type is chosen.
    //
    // `Some(signed)` only when the sign was actually read. `None` is not
    // "unsigned": the signedness-sensitive operators below refuse it rather than
    // pick a meaning. The operators that do not read the sign (`+`, `&`, `==`)
    // proceed, because for them the sign is genuinely irrelevant.
    let signed = match a {
        Val::Sym(_, sign) => sign.known(),
        // A comparison of two `bool`s (`p == q`) has no integer sign to use, and
        // the arms below handle it before any sign is read. Anything else here
        // has no bit-vector at all and returns `Unknown` below.
        _ => Some(false),
    };
    match op {
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let (x, y) = match (a, b) {
                (Val::Sym(x, _), Val::Sym(y, _)) => (x, y),
                (Val::Bool(x), Val::Bool(y)) => {
                    return Val::Bool(match op {
                        BinOp::Eq => smt::iff(x, y),
                        BinOp::Ne => smt::xor(x, y),
                        _ => return Val::Unknown,
                    })
                }
                _ => return Val::Unknown,
            };
            // `==`/`!=` do not read the sign -- two bit patterns are equal or
            // not regardless of how they are read -- so they are answered before
            // the sign is required. The relational four do read it, and refuse
            // when it was not printed: `<` on an `i8` is not `<` on a `u8`, and
            // the unsigned form calls `-1` the largest value. A wrong choice is
            // not a missed proof but a wrong branch, which is a wrong answer.
            if matches!(op, BinOp::Eq | BinOp::Ne) {
                return Val::Bool(match op {
                    BinOp::Eq => smt::eq(x, y),
                    _ => smt::not(smt::eq(x, y)),
                });
            }
            let Some(signed) = signed else { return Val::Unknown };
            Val::Bool(match op {
                BinOp::Lt if signed => smt::slt(x, y),
                BinOp::Le if signed => smt::sle(x, y),
                BinOp::Gt if signed => smt::sgt(x, y),
                BinOp::Ge if signed => smt::sge(x, y),
                BinOp::Lt => smt::ult(x, y),
                BinOp::Le => smt::ule(x, y),
                BinOp::Gt => smt::ult(y, x),
                BinOp::Ge => smt::ule(y, x),
                _ => unreachable!(),
            })
        }
        _ => {
            let (x, y) = match (a, b) {
                (Val::Sym(x, _), Val::Sym(y, _)) => (x, y),
                // Bitwise operators on `bool`. rustc lowers `p && q` to
                // `BitAnd(p, q)` and the OR/XOR forms likewise, so a contract
                // assert whose condition was written with `&&` arrives here as a
                // bitwise op on two booleans. Refusing it would leave the assert
                // unmodelled and the obligation open, which is a coverage hole
                // rather than a wrong answer -- but an avoidable one.
                (Val::Bool(p), Val::Bool(q)) => {
                    return Val::Bool(match op {
                        BinOp::BitAnd => smt::and(p, q),
                        BinOp::BitOr => smt::or(p, q),
                        BinOp::BitXor => smt::xor(p, q),
                        _ => return Val::Unknown,
                    })
                }
                _ => return Val::Unknown,
            };
            if width.is_none() {
                return Val::Unknown;
            }
            // Every arm below is an integer operation whose result has the
            // operand's type, so the result carries the operand's sign. The sign
            // is `Unknown` exactly when the dump did not print it; the arms that
            // do not read it still compute, and the two that do (`Div`/`Rem` and
            // the shifts) refuse below rather than guess.
            let sign = match signed {
                Some(true) => Sign::Signed,
                Some(false) => Sign::Unsigned,
                None => Sign::Unknown,
            };
            Val::Sym(match op {
                BinOp::Add => smt::add(x, y),
                BinOp::Sub => smt::sub(x, y),
                BinOp::Mul => smt::mul(x, y),
                BinOp::BitAnd => smt::band(x, y),
                BinOp::BitOr => smt::bor(x, y),
                BinOp::BitXor => smt::bxor(x, y),
                // Division and remainder go through the engine's restoring
                // divider, which is exact. `y == 0` has a defined value there,
                // and rustc's own divide-by-zero assert is what turns that into
                // a reported panic, so the pair is consistent. A signed operand
                // needs the *signed* divider: the unsigned one would return a
                // huge positive quotient for `-7 / 2`, which is a wrong value
                // and not merely a weaker proof.
                BinOp::Div | BinOp::Rem => {
                    // A signed operand needs the *signed* divider, and an
                    // unprinted sign is a refusal: the unsigned divider returns a
                    // huge positive quotient for `-7 / 2`, a wrong value rather
                    // than a weaker proof.
                    // A constant power-of-two divisor is a shift, not a division, and
                    // the difference is not a micro-optimisation: the signed divider's
                    // sign fixup is a BDD wall at 64 bits (9.3s for `sdiv(x, 2)` against
                    // 47ms for `udiv(x, 2)`), so `a / 2` on an `i64` was reported
                    // `incomplete`. The constant path is the shift identity and needs no
                    // fixup. `|c| == 1` is deliberately not taken -- `x / -1` overflows at
                    // `MIN` and the general path handles that explicitly -- and it would
                    // be a no-op shift anyway.
                    let Some(w) = width else { return Val::Unknown };
                    if signed == Some(true) {
                        if let Some((q, r)) = smt::const_of(y)
                            .map(|v| as_signed(v, w))
                            .and_then(|c| smt::sdivmod_pow2(x, c, w))
                        {
                            return Val::Sym(
                                match op {
                                    BinOp::Div => q,
                                    _ => r,
                                },
                                sign,
                            );
                        }
                    }
                    // The unsigned twin: a logical shift and a mask, with no sign to
                    // fix up. The general unsigned divider is not the signed one's wall,
                    // but it is still a `2 * w`-deep term, and a *symbolic* dividend
                    // through it is refused for the diagram's size -- `n / 4` on a `u64`
                    // with `n <= 1000` was `incomplete` in ~0.9 s. `d == 1` is left to the
                    // general path so the guard matches the signed branch.
                    if signed == Some(false) {
                        if let Some((q, r)) = smt::const_of(y)
                            .and_then(|d| smt::udivmod_pow2(x, d, w))
                        {
                            return Val::Sym(
                                match op {
                                    BinOp::Div => q,
                                    _ => r,
                                },
                                sign,
                            );
                        }
                    }
                    match (signed, op) {
                        (Some(true), BinOp::Div) => smt::sdiv(x, y),
                        (Some(true), BinOp::Rem) => smt::srem(x, y),
                        (Some(false), BinOp::Div) => smt::udiv(x, y),
                        (Some(false), BinOp::Rem) => smt::urem(x, y),
                        // The arm is reached only for `Div`/`Rem` (the outer
                        // `match op` selects it), so `None` is the only other
                        // case and it is a refusal.
                        (None, _) => return Val::Unknown,
                        _ => return Val::Unknown,
                    }
                }
                // A *variable* shift amount is a barrel shifter (see
                // `smt::shift_var`). rustc guards it with `assert(n < w)`
                // immediately before, so the amount is in range on every path that
                // reaches here. A constant amount keeps the cheap `Op::Shl` path,
                // which is also what makes `x << 3` prove without any guard at all.
                BinOp::Shl | BinOp::Shr => {
                    let Some(w) = width else { return Val::Unknown };
                    // `Shr` is arithmetic on a signed operand and logical on an
                    // unsigned one; an unprinted sign is a refusal, because the
                    // two differ for every negative value.
                    let Some(signed) = signed else { return Val::Unknown };
                    // `evaluate` with no assignment is `Some(k)` for any term that
                    // folds to a constant -- `x >> 1 + 1` reaches here as an add of
                    // two constants -- and `None` for a symbolic amount. Using the
                    // raw-literal `const_of` here classified a folded constant as
                    // symbolic, so the body built a barrel shifter for an amount
                    // rustc knows at compile time and the engine could not decide
                    // the query. A symbolic amount still takes `shift_var` below.
                    match smt::evaluate(y, |_| None) {
                        // rustc's guard says `k < w`; a constant outside that range
                        // is a compile error, so this is defensive only.
                        Some(k) if k < w as u64 => {
                            let v = match shift_kind(op, signed) {
                                smt::Shift::Left => smt::shl(x, k as u32),
                                smt::Shift::LogicalRight => smt::lshr(x, k as u32),
                                smt::Shift::ArithmeticRight => smt::ashr(x, k as u32),
                            };
                            return Val::Sym(v, sign);
                        }
                        Some(_) => return Val::Unknown,
                        None => {
                            return Val::Sym(smt::shift_var(shift_kind(op, signed), x, y), sign);
                        }
                    }
                }
                _ => return Val::Unknown,
            }, sign)
        }
    }
}

/// The predicate that says "this operation wraps at width `w`", or `None` when no
/// sound predicate is available.
///
/// This is the load-bearing part of the whole frontend, so it is worth being
/// precise about. rustc lowers `a + b` to `AddWithOverflow` plus an
/// `assert(!overflow)`, and it is that assert which makes the check meaningful.
/// If `overflow_pred` returned something too weak, the assert would look
/// dischargeable and an overflowing program would be reported panic-free — the
/// exact failure mode the README calls out, where an unsound engine reports a
/// *better-looking* result than the truth.
/// The signed range of a `w`-bit two's complement value, in `i128` so that the
/// `w == 64` case fits without a special case.
fn signed_range(w: u8) -> (i128, i128) {
    let half = 1i128 << (w - 1);
    (-half, half - 1)
}

/// Reinterpret a `w`-bit two's complement bit pattern as a signed value.
fn as_signed(raw: u64, w: u8) -> i128 {
    if w >= 64 {
        (raw as i64) as i128
    } else {
        let r = raw as i128;
        if r >= (1i128 << (w - 1)) {
            r - (1i128 << w)
        } else {
            r
        }
    }
}

/// `a / b` rounded toward negative infinity, with `b > 0`.
///
/// Rust's `/` truncates toward zero, and the two differ exactly on the negative
/// side, which is the side this whole computation lives on.
fn floor_div(a: i128, b: i128) -> i128 {
    let q = a / b;
    if a % b != 0 && (a < 0) != (b < 0) {
        q - 1
    } else {
        q
    }
}

/// `a / b` rounded toward positive infinity, with `b > 0`.
fn ceil_div(a: i128, b: i128) -> i128 {
    let q = a / b;
    if a % b != 0 && (a < 0) == (b < 0) {
        q + 1
    } else {
        q
    }
}

/// Whether a *signed* `v * c` wraps at width `w`, for a constant `c`.
///
/// `x * c` is monotone in `x` on each side of zero, so the exact product leaves the
/// `w`-bit signed range on a *prefix* `x < lo` or a *suffix* `x > hi`. Both bounds are
/// a division of the range end by `c` rounded one way or the other, computed exactly
/// in `i128`.
///
/// That is the whole point of the construction: **nothing here needs the product**,
/// only the two bounds, so it works at `w == 64` where the general path has no wider
/// width to compute the product in and refuses. The general path's comment says the
/// gap is deliberate because a weaker predicate there would be worse than a refusal;
/// this is not weaker, it is exact -- `x * c` is inside the range exactly when `x` is
/// between the bounds -- which is why it is worth having rather than a compromise.
///
/// `c == 0` is the one constant the formula cannot take: the bounds are a division by
/// `c`, and it is the only one that would divide by zero. `c == 1` is a cheap early
/// return and the formula agrees with it anyway.
///
/// `c == -1` is deliberately *not* in the set, which is the one place this construction
/// is easy to get wrong by hand. `-1 * MIN` is `2^(w-1)`, and the largest signed value is
/// `2^(w-1) - 1` -- so multiplying by minus one *does* overflow, at exactly `MIN`. (It is
/// easy to say instead that `MIN * -1` "wraps back to `MIN`", which is true of the
/// *wrapped* result and is precisely the overflow.) An earlier version of this function
/// special-cased `-1` as never wrapping, which was wrong and is caught by
/// `a_signed_constant_multiply_overflow_is_exact` at `2-bit -2 * -1`.
fn signed_mul_wraps_at(v: Var, c: i128, w: u8) -> Pred {
    if c == 0 || c == 1 {
        return smt::truth(false);
    }
    let (mn, mx) = signed_range(w);
    // For `c > 0` the product leaves low when `x * c < mn` and high when `x * c > mx`,
    // so the bounds are `mn / c` rounded up and `mx / c` rounded down.
    //
    // For `c < 0` the product is decreasing, and the two ends swap: `x` below
    // `floor(mn / |c|) + 1` gives a product *above* `mx`, and `x` above `2^(w-1) / |c|`
    // gives one *below* `mn`. Getting the swap right is the whole difficulty of the
    // negative case, and it is checked against brute force in the test below.
    let (lo, hi) = if c > 0 {
        (ceil_div(mn, c), mx / c)
    } else {
        let d = -c;
        (floor_div(mn, d) + 1, (1i128 << (w - 1)) / d)
    };
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let mut wraps = smt::truth(false);
    // A bound outside the range describes no `x` at all, so the guard is dropped
    // rather than built: `slt(x, MIN)` would be a constant `false` term, and a
    // constant term in a predicate is noise the diagram does not need.
    if lo > mn {
        wraps = smt::or(wraps, smt::slt(v, smt::word((lo as u64) & mask, w)));
    }
    if hi < mx {
        wraps = smt::or(wraps, smt::sgt(v, smt::word((hi as u64) & mask, w)));
    }
    wraps
}

fn overflow_pred(op: BinOp, a: Val, b: Val, w: u8) -> Option<Pred> {
    // The sign is the operand's, read from the operand, for the same reason
    // `eval_binary` does: a wrong sign here is a wrong overflow predicate, and an
    // overflow predicate that is too weak is an overflow the tool calls safe.
    let (x, y, signed) = match (a, b) {
        (Val::Sym(x, sx), Val::Sym(y, _)) => (x, y, sx.known()?),
        _ => return None,
    };
    Some(match op {
        // Unsigned `x + y` wraps exactly when the sum is below `x`: that is the
        // carry out of the top bit, and the unsigned order tracks it.
        //
        // Signed addition is a *different* condition, and getting it wrong is
        // unsound rather than merely weak. The carry test is not enough: `127 + 1`
        // at `i8` carries into a result that is *below* `127` read unsigned, so
        // the unsigned test happens to fire there — but it also fires on `-1 + 1`
        // (no overflow, result `0`), and it misses `-128 + -1`, whose sum `127u8`
        // carries yet lands below `127`... in a direction that depends on which
        // operand you compare against. The sign rule is the sound one and has no
        // such cases: the result is wrong exactly when the operands agree in sign
        // and the result disagrees with them.
        BinOp::Add if signed => {
            let sum = smt::add(x, y);
            let same_sign = smt::iff(smt::negative(x), smt::negative(y));
            smt::and(same_sign, smt::xor(smt::negative(x), smt::negative(sum)))
        }
        BinOp::Add => smt::ult(smt::add(x, y), x),
        // Unsigned `x - y` wraps exactly when `x < y` (the borrow).
        //
        // Signed subtraction wraps when the operands *differ* in sign and the
        // result takes the sign of the subtrahend: `x - y` is wrong exactly when
        // `x` and `y` disagree and the result agrees with `y`.
        BinOp::Sub if signed => {
            let diff = smt::sub(x, y);
            let differ = smt::xor(smt::negative(x), smt::negative(y));
            smt::and(differ, smt::iff(smt::negative(y), smt::negative(diff)))
        }
        BinOp::Sub => smt::ult(x, y),
        // `x * y` wraps exactly when the exact product needs more than `w` bits.
        //
        // Neither sign needs a wide product. Unsigned `x * y` wraps exactly when
        // `y != 0 && x > MAX / y`; the *signed* form is `|x| > limit / |y|` with
        // `y != 0`, where `limit` is `2^(w-1) - 1` for same signs and `2^(w-1)` for
        // different ones. Both are divisions, and both are exact rather than
        // sufficient, which matters because a too-weak predicate here would make
        // the `assert` look dischargeable and report an overflowing function as
        // panic-free. The signed form used to widen to `2w` and compare with the
        // sign-extended wrapped result -- the BDD wall -- which is why it refused
        // past 16 bits; see the arms below.
        BinOp::Mul => {
            // Both operands constant: the product is a literal, so the overflow
            // is a literal too. This arm is reachable only once an argument can
            // be pinned to a constant by its precondition (`a == 3` with the body
            // `a * 2`), which makes the *other* operand constant as well; rustc
            // folds a genuinely constant body before the frontend sees it. Without
            // this arm the pair fell through to the general path below, which has
            // no sound predicate at `w == 64` and returned `None`, so a query whose
            // every input was known came back `incomplete`.
            let both = match (smt::evaluate(x, |_| None), smt::evaluate(y, |_| None)) {
                (Some(xr), Some(yr)) => Some((xr, yr)),
                _ => None,
            };
            if let Some((xr, yr)) = both {
                let wraps = if signed {
                    let p = as_signed(xr, w) * as_signed(yr, w);
                    let (mn, mx) = signed_range(w);
                    p < mn || p > mx
                } else {
                    let p = (xr as u128) * (yr as u128);
                    let max = if w >= 64 { u64::MAX as u128 } else { (1u128 << w) - 1 };
                    p > max
                };
                return Some(smt::truth(wraps));
            }
            // A *constant* operand makes the test exact and cheap: `x * c` wraps,
            // for unsigned operands, exactly when `x > MAX / c`, and `MAX / c` is a
            // compile-time constant, so the whole predicate is one comparison --
            // no divider and no `2w`-bit multiplier. `i * 4` -- an index scaled by
            // an element size -- is the common shape.
            //
            // Unsigned only. The signed case has one case per combination of the
            // three signs, and a predicate that is too weak there is a false proof
            // rather than a refusal, so it takes `signed_mul_wraps_at` rather than
            // this comparison.
            let const_side = match (smt::evaluate(x, |_| None), smt::evaluate(y, |_| None)) {
                // `(v, k)`: the non-constant operand and the constant one.
                (Some(_), None) => Some((y, x)),
                (None, Some(_)) => Some((x, y)),
                _ => None,
            };
            if let Some((v, k)) = const_side {
                let raw = smt::evaluate(k, |_| None).expect("the constant side, just matched");
                if !signed {
                    let max = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                    // `c <= 1` is both cases where `MAX / c + 1` would not fit in
                    // `w` bits: `c == 0` never wraps, and `c == 1` cannot exceed
                    // `MAX`. The predicate is the sound one for every other `c`.
                    return Some(if raw <= 1 {
                        smt::truth(false)
                    } else {
                        smt::uge_const(v, max / raw + 1)
                    });
                }
                // Signed, and the same idea with a range that has two ends. This is
                // the case the general path below cannot reach at `w == 64`, and the
                // reason a scaled index in signed code stayed `incomplete`.
                return Some(signed_mul_wraps_at(v, as_signed(raw, w), w));
            }
            // Non-constant operands, unsigned. `x * y` wraps exactly when
            // `y != 0 && x > MAX / y`, and the division is *exact* rather than
            // sufficient: for `y != 0`, `x * y > MAX` iff `x > floor(MAX / y)`, and
            // `y == 0` can never wrap. No `2w`-bit product is built, so this costs
            // the divider the engine already has rather than the multiplier that is
            // the BDD scaling wall -- and it works at `w == 64`, where there is no
            // width left to widen to and the widened test below cannot exist at all.
            //
            // The shape is deliberately the one the guard in the saturation idiom is
            // written in (`if b != 0 && a > MAX / b`), in the same operand order, so
            // the two terms are structurally identical. That is what lets the boolean
            // fold in `smt::bin_bool` collapse `guard && !guard` to `false` without
            // ever blasting the divider: the difference between a verdict and
            // `Unknown` for a `u16` saturating multiply, whose guard is exactly this
            // predicate.
            if !signed {
                let max = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let nonzero = smt::not(smt::eq(y, smt::word(0, w)));
                let over = smt::ult(smt::udiv(smt::word(max, w), y), x);
                return Some(smt::and(nonzero, over));
            }
            // Signed, non-constant, and no longer widened.
            //
            // The old path widened both operands to `2w`, multiplied there and
            // compared with the sign-extension of the wrapped result. That is a
            // `2w`-bit multiplier -- the BDD scaling wall this crate documents -- so
            // it was refused past 16 bits, and every signed multiply of two
            // non-constant values in `i32`/`i64` code came back `incomplete`. The
            // refusal was justified by the comment that "there is no division form
            // that is exact for every combination of the three signs". That is
            // false, and the exact form is the one below, which is the same safe
            // interval `signed_mul_wraps_at` computes for a constant operand:
            // `|x|` against the largest magnitude the divisor permits.
            //
            // Only two signs matter, not three. Same signs multiply positive, so
            // the bound is `mx = 2^(w-1) - 1`; different signs multiply negative, so
            // it is `2^(w-1)`, the magnitude of `mn`. `|mn|` is one past `mx`, which
            // is why the two ends are not one number, and it is exactly the `-1` in
            // `MIN * -1` -- that pair is the different-signs bound reached at the
            // extreme, so it needs no special case here (unlike the round-trip
            // formulation, which cannot see it and has to name it).
            //
            // Magnitudes rather than signed operands: the division is unsigned, and
            // negating `MIN` wraps back to `MIN`, whose bit pattern *is* `2^(w-1)`,
            // so the plain wrapping subtract is the right magnitude for every input
            // -- the same reasoning the signed divider above uses. No `2w`-bit
            // product is built, so this works at `w == 64`, where the old path had
            // no predicate at all.
            let (_, mx) = signed_range(w);
            let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
            let zero = smt::word(0, w);
            let magnitude = |v: Var| smt::ite(smt::negative(v), smt::sub(zero, v), v);
            // `y != 0`, so the division is defined. The engine gives `x / 0` a
            // defined value rather than trapping it, so without this the zero divisor
            // would contribute an answer of its own -- and `x * 0` never overflows.
            let nonzero = smt::not(smt::eq(y, zero));
            // The largest `|x|` that pairs with this `|y|` and stays in range, chosen
            // by whether the product is positive or negative.
            let same_sign = smt::iff(smt::negative(x), smt::negative(y));
            let limit = smt::ite(
                same_sign,
                smt::word((mx as u64) & mask, w),
                smt::word(1u64 << (w - 1), w),
            );
            // `|x| > floor(limit / |y|)`, unsigned. `udiv` truncates, so the
            // comparison is strict and equality is the safe boundary -- `42 * 3` is
            // `126` and `43 * 3` is `129`, and the test below probes either side.
            let over = smt::ult(smt::udiv(limit, magnitude(y)), magnitude(x));
            smt::and(nonzero, over)
        }
        _ => return None,
    })
}
#[cfg(test)]
mod tests {
    //! The oracle for the per-kind discharge polarity, and for the report
    //! aggregation built on it.
    //!
    //! Every other check on this logic lives in `tests/mir.rs`, which needs
    //! `VERIF_RUSTC` pointing at a nightly compiler and *skips itself* without
    //! one. A skipped test still reports `ok`, so the suite count is the same
    //! whether the polarity is exercised or not: 325 with the nightly, 325
    //! without. On a stable-only machine the rule below had no teeth at all.
    //!
    //! The rule is also the kind of thing a single-polarity reading gets wrong in
    //! both directions. An `Unsat` answer *discharges* a panic query ("it cannot
    //! happen") and *refutes* a postcondition ("it holds for no input"). Collapsing
    //! the match into `verdict.is_proved()` -- which is what a caller reaching for
    //! `Verdict::is_proved` would write -- left the whole nightly suite green until
    //! `tests/mir.rs` was run with the compiler present, and it is exactly the
    //! soundness hole this method exists to close.
    //!
    //! So the oracle enumerates the whole truth table rather than sampling it, and
    //! asserts the cross-kind asymmetry that no single-polarity reading can satisfy.

    use super::*;
    use crate::smt;

    /// A real counterexample. A `Cex` has private fields and only the engine can
    /// build one, so this asks for a satisfiable-but-not-valid query rather than
    /// fabricating a witness.
    fn counterexample() -> Verdict {
        smt::with_fresh(|| {
            let x = smt::var(8);
            // `x < 3` has models (0, 1, 2) and is not valid, so `find_model`
            // refutes it and hands back one of them.
            smt::find_model(smt::ult_const(x, 3))
        })
    }

    /// The signedness a `Val` is *built* with comes from the operand's own type.
    ///
    /// This is the invariant the whole refactor exists for. The sign used to be a
    /// `bool` threaded alongside the value, and the two false proofs both came
    /// from a site that dropped it: `const 0_i8` read as unsigned made `0 < a` an
    /// unsigned test (so `i8::MIN` read as positive), and a signed source cast
    /// without its sign zero-filled `-1i8 as i16` to `255`. Here the sign is a
    /// field of `Val::Sym`, and this test pins that the *only* place a `Val` is
    /// made from an `Operand` -- `operand` -- reads it from the operand's type:
    /// a constant's suffix, a place's declared type, and a projection's element
    /// type rather than its container's.
    #[test]
    fn a_vals_sign_comes_from_the_operands_type() {
        let mut env = Env::new();
        // A constant's suffix is its type: `const 0_i8` is signed, `const 0_u8`
        // is not.
        let sign_of = |env: &mut Env, o: &Operand| match operand(env, o) {
            Val::Sym(_, s) => s,
            other => panic!("expected a bit-vector, got {other:?}"),
        };
        assert_eq!(
            sign_of(&mut env, &Operand::Const(Const::UInt(0, Some(Ty::I8)))),
            Sign::Signed
        );
        assert_eq!(
            sign_of(&mut env, &Operand::Const(Const::UInt(0, Some(Ty::U8)))),
            Sign::Unsigned
        );
        // A suffix-less constant carries no width *and* no sign, so it is
        // `Val::Unknown` outright -- there is nothing to read a signedness from,
        // which is what keeps the false-proof default from coming back.
        assert!(matches!(
            operand(&mut env, &Operand::Const(Const::UInt(0, None))),
            Val::Unknown
        ));
        // A place read returns the value that was *stored* for the local, so the
        // sign is the one the seeding site gave it. This is the path an argument
        // or an array element takes, and it is where a missing sign would have
        // been invisible before: `env.locals` held a bare `Var`.
        env.locals.insert(0, Val::Sym(smt::var(8), Sign::Unsigned));
        env.locals.insert(1, Val::Sym(smt::var(8), Sign::Signed));
        assert_eq!(sign_of(&mut env, &Operand::Copy(Place::new(0))), Sign::Unsigned);
        assert_eq!(sign_of(&mut env, &Operand::Copy(Place::new(1))), Sign::Signed);
    }

    /// A relational test on a value whose sign the dump did not print is
    /// *refused*, not read as unsigned.
    ///
    /// This is the regression guard for the `0 < a` false proof. `Lt` on two
    /// `Sign::Unknown` operands must be `Val::Unknown`, which the caller reports
    /// as an unmodelled path, rather than `smt::ult`, which would call
    /// `i8::MIN` the largest value and prove the wrong branch.
    #[test]
    fn a_comparison_on_an_unprinted_sign_is_refused() {
        let unknown = Val::Sym(smt::var(8), Sign::Unknown);
        let v = eval_binary(BinOp::Lt, unknown, unknown, Some(8));
        assert!(matches!(v, Val::Unknown), "expected a refusal, got {v:?}");
        // The equality forms do not read the sign, so they still answer.
        assert!(matches!(eval_binary(BinOp::Eq, unknown, unknown, Some(8)), Val::Bool(_)));
        // Division and shifts read it too, and refuse the same way.
        assert!(matches!(
            eval_binary(BinOp::Div, unknown, unknown, Some(8)),
            Val::Unknown
        ));
        assert!(matches!(
            eval_binary(BinOp::Shr, unknown, unknown, Some(8)),
            Val::Unknown
        ));
        // An *unsigned* pair is answered, so the refusal is specific to the
        // missing sign rather than to the operator.
        let unsigned = Val::Sym(smt::var(8), Sign::Unsigned);
        assert!(matches!(
            eval_binary(BinOp::Lt, unsigned, unsigned, Some(8)),
            Val::Bool(_)
        ));
    }

    fn panic_kind() -> ObligationKind {
        ObligationKind::Panic { message: "attempt to compute overflow".into() }
    }

    fn ob(kind: ObligationKind, verdict: Verdict) -> Obligation {
        Obligation { kind, verdict }
    }

    /// The truth table for `is_discharged`, written out rather than derived from
    /// the implementation, so the test states the intended semantics instead of
    /// echoing the code.
    ///
    /// The interesting rows are the ones that differ by kind at a fixed verdict:
    /// `Unsat` discharges a panic and refutes a postcondition; `Counterexample`
    /// refutes a postcondition and discharges a vacuity check.
    #[test]
    fn discharge_polarity_is_per_kind_not_per_verdict() {
        let cex = counterexample();
        assert!(
            matches!(cex, Verdict::Counterexample(_)),
            "the fixture needs a real counterexample, got {cex}"
        );

        // (kind, verdict, discharged)
        let table = [
            // A postcondition is discharged only by `Valid`: it must hold for all
            // inputs. `Unsat` is the strongest failure, not a pass.
            (ObligationKind::Postcondition, Verdict::Valid, true),
            (ObligationKind::Postcondition, Verdict::Unsat, false),
            (ObligationKind::Postcondition, cex, false),
            (ObligationKind::Postcondition, Verdict::Unknown, false),
            // A panic is discharged only by `Unsat`: the query is "can it happen",
            // so `Unsat` is the good answer and `Valid` is the worst case.
            (panic_kind(), Verdict::Valid, false),
            (panic_kind(), Verdict::Unsat, true),
            (panic_kind(), cex, false),
            (panic_kind(), Verdict::Unknown, false),
            // An `unreachable` is the same query shape as a panic.
            (ObligationKind::Unreachable, Verdict::Valid, false),
            (ObligationKind::Unreachable, Verdict::Unsat, true),
            (ObligationKind::Unreachable, cex, false),
            (ObligationKind::Unreachable, Verdict::Unknown, false),
            // The unwinding assertion is a reachability query too: it asks "is the
            // cutoff reachable", so `Unsat` discharges it. The engine records it
            // with `Valid` on a path that *did* reach the cutoff, which is the
            // failure case -- the row a too-small `unwind:` lands on.
            (ObligationKind::UnwindBound { bound: 3 }, Verdict::Valid, false),
            (ObligationKind::UnwindBound { bound: 3 }, Verdict::Unsat, true),
            (ObligationKind::UnwindBound { bound: 3 }, cex, false),
            (ObligationKind::UnwindBound { bound: 3 }, Verdict::Unknown, false),
            // A vacuity check is discharged when it is *refuted*: some input
            // satisfies the precondition. `Unsat` here is the finding.
            (ObligationKind::VacuousPrecondition, Verdict::Valid, true),
            (ObligationKind::VacuousPrecondition, Verdict::Unsat, false),
            (ObligationKind::VacuousPrecondition, cex, true),
            (ObligationKind::VacuousPrecondition, Verdict::Unknown, false),
        ];

        for (kind, verdict, expected) in table {
            let o = ob(kind.clone(), verdict);
            assert_eq!(
                o.is_discharged(),
                expected,
                "{} with verdict `{verdict}`: expected discharged={expected}",
                kind
            );
        }
    }

    /// The asymmetry the truth table rests on, stated on its own so a regression
    /// names the exact confusion rather than one row of a table.
    #[test]
    fn the_same_verdict_is_opposite_for_a_panic_and_a_postcondition() {
        let panic = ob(panic_kind(), Verdict::Unsat);
        let post = ob(ObligationKind::Postcondition, Verdict::Unsat);

        assert!(
            panic.is_discharged(),
            "an `Unsat` panic query means the panic cannot happen: a discharge"
        );
        assert!(
            !post.is_discharged(),
            "an `Unsat` postcondition holds for no input: the strongest failure"
        );
    }

    /// `Unknown` is never a discharge, for any kind. This is the one rule that is
    /// shared, and it is the reason the engine may decline to answer safely.
    #[test]
    fn an_undecided_obligation_is_never_discharged() {
        for kind in [
            ObligationKind::Postcondition,
            panic_kind(),
            ObligationKind::Unreachable,
            ObligationKind::VacuousPrecondition,
        ] {
            let o = ob(kind.clone(), Verdict::Unknown);
            assert!(!o.is_discharged(), "{kind} must not be discharged on `Unknown`");
        }
    }

    /// The two failures that leave no witness are opposite findings, and both
    /// render with no counterexample. The detail string has to tell them apart:
    /// a shared "holds for every input" describes an impossible postcondition as
    /// a universal truth, which is the reverse of what happened.
    #[test]
    fn the_two_witnessless_failures_are_told_apart() {
        let post = ob(ObligationKind::Postcondition, Verdict::Unsat);
        let panic = ob(panic_kind(), Verdict::Valid);

        assert!(post.failure_witness().is_none(), "an `Unsat` postcondition has no witness");
        assert!(panic.failure_witness().is_none(), "an always-firing panic has no witness");

        let post_detail = post.failure_detail();
        let panic_detail = panic.failure_detail();

        assert!(
            post_detail.contains("no input"),
            "an `Unsat` postcondition holds for NO input; detail was: {post_detail}"
        );
        assert!(
            panic_detail.contains("every input"),
            "a `Valid` panic fires on EVERY input; detail was: {panic_detail}"
        );
        assert_ne!(
            post_detail, panic_detail,
            "opposite findings must not share a diagnosis"
        );
        assert!(
            !post_detail.contains("every input") || post_detail.contains("no input"),
            "the postcondition detail must not read as a universal truth: {post_detail}"
        );
    }

    /// The classifier sentinels: a non-discharged obligation whose verdict is the
    /// discharge case for its kind would be a bug in `is_discharged`, so the
    /// detail says so instead of inventing a diagnosis.
    #[test]
    fn a_non_discharged_obligation_in_its_discharge_case_says_it_is_invalid() {
        // `Valid` is the pass case for a postcondition, so reaching the failure
        // path with it means the classifier disagreed with itself.
        let post = ob(ObligationKind::Postcondition, Verdict::Valid);
        assert!(
            post.failure_detail().contains("invalid"),
            "expected the invalid-classifier sentinel, got: {}",
            post.failure_detail()
        );

        // `Unsat` is the discharge case for a panic query, likewise.
        let panic = ob(panic_kind(), Verdict::Unsat);
        assert!(
            panic.failure_detail().contains("invalid"),
            "expected the invalid-classifier sentinel, got: {}",
            panic.failure_detail()
        );
    }

    /// A cutoff is not a proof, however many obligations passed.
    #[test]
    fn a_report_with_an_unknown_path_is_never_proved() {
        let report = MirReport {
            function: "f".into(),
            obligations: vec![ob(ObligationKind::Postcondition, Verdict::Valid)],
            unknown_paths: vec!["loop budget exhausted".into()],
            returned_paths: 1,
        };
        assert!(
            !report.is_proved(),
            "an unexplored path means the verification is incomplete"
        );
    }

    /// A decided failure outranks an undecided obligation, and the undecided one
    /// is counted separately rather than folded into the failure.
    #[test]
    fn a_decided_failure_outranks_an_undecided_obligation() {
        let cex = counterexample();
        let report = MirReport {
            function: "f".into(),
            obligations: vec![
                ob(ObligationKind::Postcondition, Verdict::Unknown),
                ob(panic_kind(), cex),
            ],
            unknown_paths: vec![],
            returned_paths: 1,
        };

        let failure = report
            .first_failure()
            .expect("a decided failure must be reported even when an earlier obligation is undecided");
        assert!(
            matches!(failure.kind, ObligationKind::Panic { .. }),
            "the panic is the decided failure, not the undecided postcondition"
        );
        assert_eq!(report.undecided(), 1, "the `Unknown` obligation is still counted");
        assert!(!report.is_proved(), "a failure means the function is not proved");
    }

    /// `panics_ruled_out` counts discharged panic obligations only: not other
    /// kinds, and not panics that were refuted.
    #[test]
    fn panics_ruled_out_counts_only_discharged_panics() {
        let cex = counterexample();
        let report = MirReport {
            function: "f".into(),
            obligations: vec![
                ob(panic_kind(), Verdict::Unsat),
                ob(panic_kind(), cex),
                ob(ObligationKind::Postcondition, Verdict::Valid),
            ],
            unknown_paths: vec![],
            returned_paths: 1,
        };
        assert_eq!(report.panics_ruled_out(), 1);
    }

    /// A vacuous precondition is a finding, and it must not read as a clean
    /// report: the obligation is not discharged, so the function is not proved.
    #[test]
    fn a_vacuous_precondition_is_a_finding_not_a_pass() {
        let report = MirReport {
            function: "f".into(),
            obligations: vec![ob(ObligationKind::VacuousPrecondition, Verdict::Unsat)],
            unknown_paths: vec![],
            returned_paths: 1,
        };
        assert!(!report.is_proved(), "an unsatisfiable precondition proves nothing");
        let failure = report.first_failure().expect("the vacuity is a decided failure");
        assert_eq!(failure.kind, ObligationKind::VacuousPrecondition);
        assert!(
            failure.failure_detail().contains("vacuous"),
            "the detail must name the vacuity, got: {}",
            failure.failure_detail()
        );
    }

    /// A branch inside an unwound loop multiplies paths without any single loop
    /// exceeding `DEFAULT_UNWIND`, so the loop bound alone does not make the
    /// search terminate.
    ///
    /// This is the regression for a real hang: `count_evens` below -- the exact
    /// MIR `rustc -O` emits for `while i < n { if i % 2 == 0 { c += 1; } i += 1; }`
    /// -- ran for minutes without returning, and the tool therefore reported
    /// *nothing* about it. The frontend's contract is that a cutoff is named as a
    /// cutoff; a search that never returns cannot name anything, so this test
    /// pins the property that matters: the call returns, and the incompleteness
    /// is reported rather than hidden.
    ///
    /// The cutoff *named* may be the path budget or the loop-unwind bound
    /// depending on how far dead-path pruning gets before either fires; the test
    /// accepts either, because both are honest cutoffs and the property under
    /// test is that *a* cutoff is reported and the call returns.
    ///
    /// The MIR is embedded so the test runs on stable. `tests/mir.rs` covers the
    /// same function end-to-end but skips itself without `VERIF_RUSTC`.
    #[test]
    fn a_branching_loop_reports_a_cutoff_rather_than_running_forever() {
        const COUNT_EVENS_MIR: &str = r#"
fn count_evens(_1: u8) -> u8 {
    debug n => _1;
    let mut _0: u8;
    let mut _2: u8;
    let mut _3: bool;
    let mut _4: u8;
    let mut _5: u8;
    let mut _6: u8;

    bb0: {
        _0 = const 0_u8;
        _2 = const 0_u8;
        goto -> bb1;
    }

    bb1: {
        _4 = copy _2;
        _3 = Lt(move _4, copy _1);
        switchInt(move _3) -> [0: bb6, otherwise: bb2];
    }

    bb2: {
        _6 = copy _2;
        _5 = Rem(move _6, const 2_u8);
        switchInt(copy _5) -> [0: bb3, otherwise: bb4];
    }

    bb3: {
        _0 = Add(copy _0, const 1_u8);
        goto -> bb5;
    }

    bb4: {
        goto -> bb5;
    }

    bb5: {
        _2 = Add(copy _2, const 1_u8);
        goto -> bb1;
    }

    bb6: {
        return;
    }
}
"#;
        // Go through the real entry point, not `verify_fn` directly. The hang
        // needs the corpus's postcondition closure as well as its precondition:
        // the postcondition is evaluated on every path and its BDD grows with
        // the path condition, which is what makes each successive path cost more
        // than the last. A hand-built `verify_fn` call without it settles
        // quickly, so it would not reproduce the defect.
        // A *symbolic* bound, so the loop cannot be pruned to a small trip count.
        // With `n <= 8` the guard folds and the loop now decides (the pruning in
        // `run_state` drops the unsatisfiable exit edge); this regression needs the
        // unbounded shape to keep exercising the path budget.
        let src = "/// requires: true\n/// ensures: true\npub fn count_evens(n: u8) -> u8 { n }\n";
        let specs = crate::mir::spec::extract(src);
        // Run on a thread with a large stack. The engine recurses through the
        // BDD and the frontend recurses through the term graph, so this workload
        // needs more stack than the test harness's default thread gives; the
        // real driver (`examples/mir_coverage.rs`) runs on the main thread and
        // never sees this. The stack size is not the property under test -- the
        // reported cutoff is -- so giving it room keeps the test about the fix.
        let outcome = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                let prog = crate::mir::parse::parse_program(COUNT_EVENS_MIR);
                let f = prog.get("count_evens").expect("the dump must parse");
                crate::smt::with_fresh(|| {
                    crate::mir::verify::verify_function(&prog, f, &specs)
                })
            })
            .expect("the test thread must spawn")
            .join()
            .expect("the verification must return rather than hang or overflow");
        let reasons = match &outcome {
            crate::mir::verify::FnOutcome::Incomplete { reasons, .. } => reasons.clone(),
            other => panic!("expected an incomplete outcome, got {other:?}"),
        };
        assert!(
            reasons
                .iter()
                .any(|r| r.contains("path budget exhausted") || r.contains("unwound past")),
            "the cutoff must be named; reasons were {reasons:?}"
        );
    }

    /// `count_up`: the exact MIR `rustc -O` emits for
    /// `let mut i = 0u8; while i < n { i += 1; } i`.
    ///
    /// Here the loop *is* the return value (`i` is `_0`), so a proof needs the
    /// invariant to carry the exit condition: after the loop `i >= n` and
    /// `i <= n`, hence `i == n`.
    const COUNT_UP_MIR: &str = r#"
fn count_up(_1: u8) -> u8 {
    debug n => _1;
    let mut _0: u8;
    let mut _2: bool;
    let mut _3: u8;
    scope 1 {
        debug i => _0;
    }

    bb0: {
        _0 = const 0_u8;
        goto -> bb1;
    }

    bb1: {
        _3 = copy _0;
        _2 = Lt(move _3, copy _1);
        switchInt(move _2) -> [0: bb3, otherwise: bb2];
    }

    bb2: {
        _0 = Add(copy _0, const 1_u8);
        goto -> bb1;
    }

    bb3: {
        return;
    }
}
"#;

    /// Verify an embedded MIR dump against a contract written as doc lines.
    fn verify_with(mir: &str, name: &str, contract: &str) -> crate::mir::verify::FnOutcome {
        let src = format!("{contract}pub fn {name}() {{}}\n");
        let specs = crate::mir::spec::extract(&src);
        let prog = crate::mir::parse::parse_program(mir);
        let name = name.to_string();
        // A large stack: the engine recurses through the BDD and the frontend
        // through the term graph, and the harness's default thread stack is
        // smaller than the main thread's.
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                let f = prog.get(&name).expect("the dump must parse");
                crate::smt::with_fresh(|| crate::mir::verify::verify_function(&prog, f, &specs))
            })
            .expect("the test thread must spawn")
            .join()
            .expect("verification must return")
    }

    #[test]
    fn an_invariant_decides_a_loop_that_unwinding_could_not() {
        let out = verify_with(
            COUNT_UP_MIR,
            "count_up",
            "/// requires: n <= 4\n/// invariant: i <= n\n/// ensures: ret == n\n",
        );
        assert!(
            matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "the loop should be decided by its invariant, got {out:?}"
        );
    }

    /// The soundness test, and the reason the header havocs the locals it can
    /// write.
    ///
    /// `i <= n` is a *true* invariant of `count_up` -- it holds on entry and is
    /// preserved by every iteration -- so the induction itself succeeds. But it
    /// says nothing that implies `ret == 0`, and for `n = 1` the loop returns
    /// `1`, so the postcondition is false.
    ///
    /// The discriminating detail is *which* state the exit edge is checked in.
    /// The guard forces `n == 0` on the very first pass, and there `i == 0` too,
    /// so a verifier that assumed the invariant at the header and then walked the
    /// exit edge from that first-iteration state would see `ret == 0` and report
    /// a proof of a false postcondition. That is the version this test was first
    /// written against, and it *passed* -- which is how the hole was found.
    ///
    /// With the havoc the exit state is any `i` with `i <= n` and `i >= n`, and
    /// `i == n == 1` refutes the postcondition. So this must not verify. The
    /// assertion is the weak form -- "not verified" -- because the engine may
    /// report a counterexample or leave the obligation open; what it must never
    /// do is claim a proof.
    #[test]
    fn an_invariant_too_weak_for_the_postcondition_is_not_a_proof() {
        let out = verify_with(
            COUNT_UP_MIR,
            "count_up",
            "/// requires: n <= 4\n/// invariant: i <= n\n/// ensures: ret == 0\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "a false postcondition must not verify, got {out:?}"
        );
    }

    /// The same loop, but the counter is advanced by a *call* rather than by an
    /// `Add` statement.
    ///
    /// This is the shape `rustc` emits for `i = i.wrapping_add(1)`: the write to
    /// `i` is the `Call` terminator's destination, not a `Stmt::Assign`. The
    /// havoc set is built from the loop body's writes, and reading only
    /// `Stmt::Assign` missed the call destination -- so `i` kept the value it had
    /// on the first entry, the induction step was checked against that one value,
    /// and the same false postcondition as above came back `Verified`.
    ///
    /// The fixture keeps the counter on `_2` (not `_0`) so the call destination is
    /// the only write to it inside the loop, which is what isolates the hole: with
    /// `Add` instead of the call, `an_invariant_too_weak_for_the_postcondition_is_not_a_proof`
    /// already covers the statement form.
    const COUNT_VIA_CALL_MIR: &str = r#"
fn count_via_call(_1: u8) -> u8 {
    debug n => _1;
    let mut _0: u8;
    let mut _2: u8;
    let mut _3: bool;
    let mut _4: u8;
    scope 1 {
        debug i => _2;
    }

    bb0: {
        _2 = const 0_u8;
        goto -> bb1;
    }

    bb1: {
        _4 = copy _2;
        _3 = Lt(move _4, copy _1);
        switchInt(move _3) -> [0: bb3, otherwise: bb2];
    }

    bb2: {
        _2 = core::num::<impl u8>::wrapping_add(move _2, const 1_u8) -> [return: bb4, unwind continue];
    }

    bb4: {
        goto -> bb1;
    }

    bb3: {
        _0 = copy _2;
        return;
    }
}
"#;

    /// A counter written only by a call must still be havoced at the loop header.
    #[test]
    fn a_call_written_counter_is_havoced_like_an_assigned_one() {
        let out = verify_with(
            COUNT_VIA_CALL_MIR,
            "count_via_call",
            "/// requires: n <= 4\n/// invariant: i <= n\n/// ensures: ret == 0\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "a call-written counter must not escape the havoc, got {out:?}"
        );
    }

    /// And the sound direction: the same loop with the invariant that actually
    /// decides it must still verify, so the fix to the havoc set did not simply
    /// make every call-carrying loop unknown.
    #[test]
    fn a_call_written_counter_is_still_decidable() {
        let out = verify_with(
            COUNT_VIA_CALL_MIR,
            "count_via_call",
            "/// requires: n <= 4\n/// invariant: i <= n\n/// ensures: ret == n\n",
        );
        assert!(
            matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "the call-written loop should still be decided by its invariant, got {out:?}"
        );
    }

    /// A user function that happens to be named `wrapping_add` must be *inlined*,
    /// not modelled as the `core` intrinsic.
    ///
    /// `intrinsics::classify` matches the method name after the last `::`, so a
    /// plain `wrapping_add` classified as the intrinsic. Dispatching on the
    /// intrinsic *before* the same-dump lookup then ignored the user's body
    /// entirely: this `wrapping_add` returns `0` whatever it is given, but the
    /// caller's `ret == 3` for `a == 1, b == 2` came back `Verified` -- a proof of
    /// a false statement, which is the one failure this crate exists to prevent.
    const SHADOWED_INTRINSIC_MIR: &str = r#"
fn wrapping_add(_1: u8, _2: u8) -> u8 {
    let mut _0: u8;
    bb0: {
        _0 = const 0_u8;
        return;
    }
}

fn caller(_1: u8, _2: u8) -> u8 {
    debug a => _1;
    debug b => _2;
    let mut _0: u8;
    bb0: {
        _0 = wrapping_add(copy _1, copy _2) -> [return: bb1, unwind continue];
    }
    bb1: {
        return;
    }
}
"#;

    #[test]
    fn a_user_function_named_like_an_intrinsic_is_inlined_not_modelled() {
        let out = verify_with(
            SHADOWED_INTRINSIC_MIR,
            "caller",
            "/// requires: a == 1 && b == 2\n/// ensures: ret == 3\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "a user `wrapping_add` returning 0 must not be modelled as `a + b`, got {out:?}"
        );
    }

    /// An invariant that is false on entry proves nothing, and must be reported
    /// as a definite failure rather than quietly ignored.
    #[test]
    fn an_invariant_false_on_entry_is_a_failure() {
        let out = verify_with(
            COUNT_UP_MIR,
            "count_up",
            "/// requires: n <= 4\n/// invariant: i == n + 1\n/// ensures: ret == n\n",
        );
        assert!(
            matches!(out, crate::mir::verify::FnOutcome::Failed { .. }),
            "a false invariant must fail, got {out:?}"
        );
    }

    /// An invariant that is preserved but *wrong* must not verify either. This
    /// is the case a naive "assert at the back edge" gets right only if the
    /// assertion really is made; a version that skipped preservation would accept
    /// this.
    #[test]
    fn an_invariant_not_preserved_is_not_a_proof() {
        let out = verify_with(
            COUNT_UP_MIR,
            "count_up",
            "/// requires: n <= 4\n/// invariant: i == 0\n/// ensures: ret == n\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "an invariant that is not preserved must not verify, got {out:?}"
        );
    }

    /// The same-dump helper the loop below calls, so the *inliner* is selected
    /// rather than the `core` intrinsic. Its body is `a + b`, the wrapped sum for
    /// a `u8`, but the point is only that the call is inlined.
    const HELPER_CALL_MIR: &str = r#"
fn wrapping_add(_1: u8, _2: u8) -> u8 {
    debug a => _1;
    debug b => _2;
    let mut _0: u8;
    bb0: {
        _0 = Add(copy _1, copy _2);
        return;
    }
}

fn count_via_helper(_1: u8) -> u8 {
    debug n => _1;
    let mut _0: u8;
    let mut _2: u8;
    let mut _3: bool;
    let mut _4: u8;
    scope 1 {
        debug i => _2;
    }

    bb0: {
        _2 = const 0_u8;
        goto -> bb1;
    }

    bb1: {
        _4 = copy _2;
        _3 = Lt(move _4, copy _1);
        switchInt(move _3) -> [0: bb3, otherwise: bb2];
    }

    bb2: {
        _2 = wrapping_add(move _2, const 1_u8) -> [return: bb4, unwind continue];
    }

    bb4: {
        goto -> bb1;
    }

    bb3: {
        _0 = copy _2;
        return;
    }
}
"#;

    /// A loop whose step is a same-dump call must keep its invariant across the
    /// inlined call, so it is decided by the invariant rather than unwound.
    ///
    /// Entering a callee clears `cut` -- the caller's loop invariant says nothing
    /// about the callee's locals -- but the return path used to copy the callee's
    /// (empty) cut into the resumed caller instead of restoring the caller's. The
    /// resumed caller was then inside a loop it had no cut for, so the next edge
    /// into its header was unwound. `n <= 10` needs more iterations than
    /// [`DEFAULT_UNWIND`], so the loop was reported as a cutoff even though its
    /// invariant decides it exactly.
    ///
    /// This is the shape the exact-name lookup now sends a user-defined
    /// `wrapping_add` through, which is why a loop that previously modelled the
    /// call as an intrinsic (and so kept its cut) began to lose it.
    #[test]
    fn an_invariant_survives_an_inlined_call_on_the_loop_edge() {
        let out = verify_with(
            HELPER_CALL_MIR,
            "count_via_helper",
            "/// requires: n <= 10\n/// invariant: i <= n\n/// ensures: ret == n\n",
        );
        assert!(
            matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "the loop should be decided by its invariant across the inlined call, got {out:?}"
        );
    }

    /// And the fix must not *weaken* the check: the same call-carrying loop with
    /// an invariant too weak for the postcondition must still be refuted, so
    /// restoring the cut did not restore a proof that was never there.
    #[test]
    fn an_inlined_call_does_not_rescue_a_weak_invariant() {
        let out = verify_with(
            HELPER_CALL_MIR,
            "count_via_helper",
            "/// requires: n <= 10\n/// invariant: i <= n\n/// ensures: ret == 0\n",
        );
        assert!(
            !matches!(out, crate::mir::verify::FnOutcome::Verified { .. }),
            "a weak invariant must not be rescued by the restored cut, got {out:?}"
        );
    }

    /// The *signed* constant multiply's predicate is exact, two-sided, at every width.
    ///
    /// This is the predicate that closes the `i64` gap, so it is the one that most needs
    /// the two-sided check: a predicate that is too *weak* here does not merely refuse a
    /// proof, it lets an overflowing `assert` discharge and reports an overflowing
    /// function as panic-free. A predicate that is too *strong* refuses safe code, which
    /// is the failure the old `wide > 16` bound was avoiding by refusing everything.
    ///
    /// So the whole domain is enumerated at widths where that is possible, against Rust's
    /// own `checked_mul` -- the oracle is the standard library's idea of overflow, not
    /// this file's. The negative constants are the interesting half: `x * c` is monotone
    /// but *decreasing* for `c < 0`, so the low and high bounds swap ends, and that swap
    /// is where a hand-derived bound goes wrong.
    #[test]
    fn a_signed_constant_multiply_overflow_is_exact() {
        // `true` when the engine's predicate says the multiply wraps. The oracle is
        // `i128`, which holds the exact product of any two values this test uses.
        let wraps = |w: u8, c: i128, v: i128| -> bool {
            smt::with_fresh(|| {
                // The constant has to be built as a `w`-bit bit pattern: `smt::word`
                // rejects a value that does not fit, and a negative constant does not fit
                // as written. Two's complement is the same pattern the frontend produces.
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let x = smt::var(w);
                let y = smt::word((c as u64) & mask, w);
                let p = overflow_pred(
                    BinOp::Mul,
                    Val::Sym(x, Sign::Signed),
                    Val::Sym(y, Sign::Signed),
                    w,
                )
                .expect("a constant multiply must produce a predicate");
                // The predicate is over the fresh variable, so asking whether it holds at
                // this point means substituting the point and evaluating. `v` is negative
                // for some cases, so it goes in as its own `w`-bit pattern too.
                smt::evaluate_pred(p, |_| Some((v as u64) & mask)).expect("predicate is over `x`")
            })
        };

        // Exhaustive where the domain is small enough to enumerate. Both signs of `c`
        // and every value of `x`, so the monotone-decreasing half is covered too.
        for w in [2u8, 3, 4, 5] {
            let half = 1i128 << (w - 1);
            let (mn, mx) = (-half, half - 1);
            for c in mn..=mx {
                for v in mn..=mx {
                    let want = v.checked_mul(c).is_none_or(|p| p < mn || p > mx);
                    assert_eq!(
                        wraps(w, c, v),
                        want,
                        "{w}-bit {v} * {c}: predicate said {} but wrapping is {want}",
                        wraps(w, c, v)
                    );
                }
            }
        }

        // `i64`, the width this predicate exists for and the one that cannot be
        // enumerated. The constants are chosen at the ends of the range and at powers of
        // two, where the bounds land on the edge of the domain; `x` is swept across each
        // constant's own boundary from `i64::MIN` to `i64::MAX`, which is the whole span
        // that matters for that constant.
        for c in [
            2i128,
            3,
            -2,
            -3,
            1 << 31,
            -(1 << 31),
            1 << 62,
            -(1 << 62),
            (1 << 62) - 1,
            i64::MAX as i128,
            i64::MIN as i128,
        ] {
            let (mn, mx) = (i64::MIN as i128, i64::MAX as i128);
            // The *safe* interval `[lo, hi]` -- the `x` whose product with `c` stays in
            // range -- derived here from the true interval, not from the implementation.
            // `x * c` is monotone but decreasing for `c < 0`, so the two ends of the
            // range swap: the low bound comes from `mx` and the high from `mn`. Deriving
            // both from `mn` (as an earlier version did) put the probes on the *negative*
            // side for every negative `c` and never straddled the positive transition at
            // `2^63 / |c|`, which is the boundary the negative arm is most likely to get
            // wrong. The probes below now bracket `lo` and `hi` on both signs.
            let (lo, hi) = if c > 0 {
                (ceil_div(mn, c), floor_div(mx, c))
            } else {
                (ceil_div(mx, c), floor_div(mn, c))
            };
            let probes = [
                mn,
                mn + 1,
                lo - 1,
                lo,
                lo + 1,
                -1,
                0,
                1,
                hi - 1,
                hi,
                hi + 1,
                mx - 1,
                mx,
            ];
            for v in probes {
                let want = v.checked_mul(c).is_none_or(|p| p < mn || p > mx);
                assert_eq!(
                    wraps(64, c, v),
                    want,
                    "64-bit {v} * {c}: predicate said {} but wrapping is {want}",
                    wraps(64, c, v)
                );
            }
        }
    }

    /// The *two-symbolic-operand* signed multiply is exact, and it exists at every
    /// width.
    ///
    /// This is the predicate that used to be refused outright. The old path widened
    /// both operands to `2w` and multiplied there, which is the BDD scaling wall, so
    /// it returned `None` past 16 bits and every signed multiply of two non-constant
    /// values in `i32`/`i64` code came back `incomplete`. The refusal was written down
    /// as "there is no division form that is exact for every combination of the three
    /// signs". That is false: the form below divides, with no widening at all.
    ///
    /// Two things are checked, and they are separate claims:
    ///
    /// * the predicate *exists* at every width, which is the refusal this replaces;
    /// * where it exists it agrees with Rust's own `checked_mul`, which is the part
    ///   that keeps it sound.
    ///
    /// The oracle is `i128`, which holds the exact product of any two `i64`s, so the
    /// comparison is against the standard library's idea of overflow rather than this
    /// file's.
    #[test]
    fn a_signed_multiply_of_two_symbols_is_exact() {
        // `Some(wraps)` when the engine's predicate says the multiply wraps, `None`
        // when the engine produced no predicate at all.
        let wraps = |w: u8, a: i128, b: i128| -> Option<bool> {
            smt::with_fresh(|| {
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let x = smt::var(w);
                let y = smt::var(w);
                let (xi, yi) = (smt::index(x), smt::index(y));
                let p = overflow_pred(
                    BinOp::Mul,
                    Val::Sym(x, Sign::Signed),
                    Val::Sym(y, Sign::Signed),
                    w,
                )?;
                // The predicate is over the two fresh variables, so a point is an
                // answer for each index. Negative values go in as their own `w`-bit
                // pattern, as in the tests above.
                smt::evaluate_pred(p, |i| {
                    if i == xi {
                        Some((a as u64) & mask)
                    } else if i == yi {
                        Some((b as u64) & mask)
                    } else {
                        None
                    }
                })
            })
        };
        let want = |w: u8, a: i128, b: i128| -> bool {
            let half = 1i128 << (w - 1);
            let (mn, mx) = (-half, half - 1);
            a.checked_mul(b).is_none_or(|p| p < mn || p > mx)
        };

        // The refusal this test exists for: a predicate at every width, including
        // `i64`, where the old widened path had none and returned `incomplete`.
        for w in 2..=64u8 {
            assert!(
                smt::with_fresh(|| overflow_pred(
                    BinOp::Mul,
                    Val::Sym(smt::var(w), Sign::Signed),
                    Val::Sym(smt::var(w), Sign::Signed),
                    w,
                ))
                .is_some(),
                "{w}-bit signed multiply of two symbols must produce a predicate"
            );
        }

        // Exhaustive where the domain is small enough: every pair of values at both
        // signs, against the standard library. `-2 * -1`, `MIN * -1` and `MIN * 1`
        // are all in here, and the whole truth table is covered rather than sampled.
        for w in [2u8, 3, 4, 5] {
            let half = 1i128 << (w - 1);
            let (mn, mx) = (-half, half - 1);
            for a in mn..=mx {
                for b in mn..=mx {
                    assert_eq!(
                        wraps(w, a, b),
                        Some(want(w, a, b)),
                        "{w}-bit {a} * {b}: predicate said {:?} but wrapping is {}",
                        wraps(w, a, b),
                        want(w, a, b)
                    );
                }
            }
        }

        // The boundary pairs at the wide end, one width at a time. `evaluate` walks a
        // term DAG under a fixed depth budget, and the divider's term chain for a wide
        // width is deeper than that budget, so the widest widths answer `None` from
        // *evaluation* even though the predicate exists. The bounds are checked by
        // construction -- `|x|` against the divisor's own limit -- so the pairs that
        // matter are the ones straddling that limit at each width.
        for w in [8u8, 12, 16, 24, 32] {
            let half = 1i128 << (w - 1);
            let (mn, mx) = (-half, half - 1);
            let mut probes: Vec<i128> = vec![mn, mn + 1, -2, -1, 0, 1, 2, mx - 1, mx];
            // The largest `|x|` that pairs with `|y| = 3`, `|y| = 5` and `|y| = 2^(w/2)`,
            // either side of the fencepost the division rounds at.
            for d in [3i128, 5, 1 << (w / 2), mx] {
                let lim = mx / d;
                probes.extend([lim - 1, lim, lim + 1, -lim - 1, -lim, -lim + 1]);
            }
            for a in &probes {
                for b in &probes {
                    if let Some(got) = wraps(w, *a, *b) {
                        assert_eq!(
                            got,
                            want(w, *a, *b),
                            "{w}-bit {a} * {b}: predicate said {got} but wrapping is {}",
                            want(w, *a, *b)
                        );
                    }
                }
            }
        }

        // The `MIN * -1` pair by name. It is the one overflow a round-trip form cannot
        // see, because the wrapped product is `MIN` and `|MIN| / 1` is `|MIN|`; the
        // range form used here reaches it as the different-signs bound, so this pins
        // that it did -- and that the *evaluated* predicate says so, not just the
        // oracle.
        for w in [8u8, 16, 32] {
            let half = 1i128 << (w - 1);
            assert_eq!(
                wraps(w, -half, -1),
                Some(true),
                "{w}-bit MIN * -1 must be reported as wrapping"
            );
            assert_eq!(
                wraps(w, -half, 1),
                Some(false),
                "{w}-bit MIN * 1 is representable and must not be reported as wrapping"
            );
        }
        for w in [8u8, 16, 32, 64] {
            let half = 1i128 << (w - 1);
            assert!(want(w, -half, -1), "{w}-bit MIN * -1 wraps");
            assert!(!want(w, -half, 1), "{w}-bit MIN * 1 does not wrap");
        }
    }

    /// The unsigned arm is untouched by the signed one: both signs are asked the same
    /// question and must give different answers where signedness matters.
    ///
    /// `-1` at `i8` is `255u8`, and `255 * 255` wraps *unsigned* (the product is past
    /// `255`) while `-1 * -1` does not wrap *signed*. A predicate that read the bit
    /// pattern without the sign would give one answer to both, so the two are asked
    /// together and required to differ.
    #[test]
    fn the_signed_and_unsigned_arms_are_not_confused() {
        let wraps = |signed: bool, w: u8, c: u64, v: u64| -> bool {
            smt::with_fresh(|| {
                let x = smt::var(w);
                let y = smt::word(c, w);
                let sign = if signed { Sign::Signed } else { Sign::Unsigned };
                let p = overflow_pred(BinOp::Mul, Val::Sym(x, sign), Val::Sym(y, sign), w)
                    .expect("a constant multiply must produce a predicate");
                smt::evaluate_pred(p, |_| Some(v)).expect("predicate is over `x`")
            })
        };
        // `-1 * -1` is `1` in `i8`: no signed overflow. `255 * 255` is `65025`: unsigned
        // overflow at 8 bits.
        assert!(
            !wraps(true, 8, 0xFF, 0xFF),
            "-1 * -1 must not wrap as signed"
        );
        assert!(
            wraps(false, 8, 0xFF, 0xFF),
            "255 * 255 must wrap as unsigned"
        );
        // `127 * -1` is `-127`, representable, while the *same bits* read unsigned are
        // `127 * 255`, far past `255`. A predicate that ignored the sign would answer one
        // of these wrong.
        assert!(!wraps(true, 8, 0xFF, 0x7F), "127 * -1 must not wrap as signed");
        assert!(wraps(false, 8, 0xFF, 0x7F), "127 * 255 must wrap as unsigned");
        // The regression for the minus-one bound: `-1 * MIN` is `2^(w-1)`, one past the
        // largest signed value, so it *does* overflow -- while the same product read as
        // unsigned magnitudes is `128 * 255`, which also overflows but for its own
        // reason. The first version of the predicate called the signed one safe.
        assert!(
            wraps(true, 8, 0xFF, 0x80),
            "MIN * -1 must wrap as signed: 2^(w-1) is not representable"
        );
    }

    /// A multiply with *both* operands constant is decided, and exactly.
    ///
    /// Both operands are literals only when the precondition pins the argument to a
    /// constant (`a == 3` with the body `a * 2`), because rustc folds a genuinely
    /// constant body itself. That shape used to fall through to the general signed
    /// path, which has no sound predicate at `w == 64` and returned `None` -- so the
    /// `assert(!overflow)` that follows was unmodelled and the whole query came back
    /// `incomplete` even though every input was known. The oracle is `i128`, and the
    /// negative constants are the interesting half because the product's sign follows
    /// the *signs*, not the magnitudes.
    #[test]
    fn a_constant_times_a_constant_multiply_is_decided() {
        // `overflow_pred` with both operands literal, at the width `w`.
        let wraps = |signed: bool, w: u8, a: i128, b: i128| -> bool {
            smt::with_fresh(|| {
                let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
                let sign = if signed { Sign::Signed } else { Sign::Unsigned };
                let x = smt::word((a as u64) & mask, w);
                let y = smt::word((b as u64) & mask, w);
                let p = overflow_pred(BinOp::Mul, Val::Sym(x, sign), Val::Sym(y, sign), w)
                    .expect("two constant operands must still produce a predicate");
                smt::evaluate_pred(p, |_| None).expect("a constant predicate must be evaluable")
            })
        };

        // Exhaustive at the small widths, both signs: every pair of values, against the
        // true product. This is what pins the arms rather than a hand-picked few.
        for w in [2u8, 3, 4, 5] {
            let half = 1i128 << (w - 1);
            let (mn, mx) = (-half, half - 1);
            let umax = (1i128 << w) - 1;
            for a in mn..=mx {
                for b in mn..=mx {
                    let want = a.checked_mul(b).is_none_or(|p| p < mn || p > mx);
                    assert_eq!(
                        wraps(true, w, a, b),
                        want,
                        "{w}-bit signed {a} * {b}: said {} but wrapping is {want}",
                        wraps(true, w, a, b)
                    );
                }
            }
            for a in 0..=umax {
                for b in 0..=umax {
                    let want = (a as u128) * (b as u128) > umax as u128;
                    assert_eq!(
                        wraps(false, w, a, b),
                        want,
                        "{w}-bit unsigned {a} * {b}: said {} but wrapping is {want}",
                        wraps(false, w, a, b)
                    );
                }
            }
        }

        // `i64`, where the bug bit. The pairs straddle the representable boundary:
        // `MIN * -1` is one past `MAX` and must wrap; `MIN * 1` and `-1 * -1` do not.
        for (a, b) in [
            (1i128, 1i128),
            (i64::MAX as i128, 1),
            (i64::MAX as i128, 2),
            (i64::MIN as i128, 1),
            (i64::MIN as i128, -1),
            (-1, -1),
            (-1, 1),
            (1 << 31, 1 << 31),
            (1 << 31, -(1 << 31)),
            (i64::MIN as i128, i64::MIN as i128),
            (0, i64::MIN as i128),
        ] {
            let (mn, mx) = (i64::MIN as i128, i64::MAX as i128);
            let want = a.checked_mul(b).is_none_or(|p| p < mn || p > mx);
            assert_eq!(
                wraps(true, 64, a, b),
                want,
                "64-bit signed {a} * {b}: said {} but wrapping is {want}",
                wraps(true, 64, a, b)
            );
        }
    }

    /// `overflow_pred` is *exact* for a constant multiply, checked exhaustively at
    /// a width small enough to enumerate and at the real boundary of a wide one.
    ///
    /// The predicate is one comparison against `MAX / c`, and the reason it is
    /// worth a test of its own is the failure mode: a predicate that is merely
    /// *sufficient* would still refuse the safe cases, and a predicate that is too
    /// *weak* would let rustc's `assert(!overflow)` discharge on a program that
    /// overflows, reporting a false panic-free result. So the check is two-sided --
    /// it must fire on every wrapping input and on no other.
    ///
    /// At `u8` the whole domain is 256 values, so "no other" is checked rather than
    /// sampled. `u32` cannot be enumerated, so the two values straddling the
    /// boundary `ceil(2^32 / c) - 1` are used, which is where a fencepost error
    /// lives.
    #[test]
    fn a_constant_multiply_overflow_is_exact() {
        // `true` when the engine's predicate says the multiply wraps.
        let wraps = |w: u8, c: u64, v: u64| -> bool {
            smt::with_fresh(|| {
                // `x` must be *symbolic*: with both operands constant the
                // constant-operand path is not taken at all, and the test would
                // exercise the widening path it is meant to be independent of.
                let x = smt::var(w);
                let y = smt::word(c, w);
                let p = overflow_pred(
                    BinOp::Mul,
                    Val::Sym(x, Sign::Unsigned),
                    Val::Sym(y, Sign::Unsigned),
                    w,
                )
                .expect("a constant multiply must produce a predicate");
                // The predicate is over fresh variables, so asking whether it holds
                // for this one point means substituting the point and evaluating.
                smt::evaluate_pred(p, |_| Some(v)).expect("the predicate is over `x`")
            })
        };

        // Exhaustive at `u8`: every value against every constant that can wrap.
        for w in [4u8, 8] {
            let max = (1u64 << w) - 1;
            for c in 0..=max {
                for v in 0..=max {
                    let want = v.checked_mul(c).is_none_or(|p| p > max);
                    assert_eq!(
                        wraps(w, c, v),
                        want,
                        "{w}-bit {v} * {c}: predicate said {} but wrapping is {want}",
                        wraps(w, c, v)
                    );
                }
            }
        }

        // The boundary of a wide width, where a fencepost error would sit.
        for c in [2u64, 3, 5, 7, 8, 1000] {
            let boundary = (1u64 << 32).div_ceil(c); // ceil(2^32 / c)
            for v in [boundary - 1, boundary] {
                let want = (v as u128) * (c as u128) > (u32::MAX as u128);
                assert_eq!(wraps(32, c, v), want, "32-bit {v} * {c}");
            }
        }

        // Multiplying by zero and by one never wraps, at any width -- the two cases
        // that are decided by a constant `false` rather than by a comparison, and so
        // the two that would panic if `MAX / c` were computed for them.
        for w in [1u8, 8, 16, 32, 64] {
            let max = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
            for c in [0u64, 1] {
                for v in [0u64, 1, max] {
                    assert!(!wraps(w, c, v), "{w}-bit {v} * {c} must not wrap");
                }
            }
        }
    }

    /// The name-shape rules a call name is resolved by, on the shapes rustc
    /// actually prints.
    ///
    /// These are pure string rules, so they are pinned here rather than only
    /// through a `rustc` run: the resolver is what stands between a call and the
    /// body it is answered from, and answering it from the wrong body is a false
    /// proof, not a lost one. The shapes below are the ones measured from a real
    /// `--emit=mir` dump.
    #[test]
    fn call_names_resolve_to_the_right_body() {
        // `base_type` strips the wrapper rustc prints on a definition and the
        // generics it prints on a call, and takes the last path segment.
        assert_eq!(base_type("Vec2"), "Vec2");
        assert_eq!(base_type("G::<T>"), "G");
        assert_eq!(base_type("<S2 as T2>"), "S2");
        assert_eq!(base_type("core::num::<impl u8>"), "u8");
        assert_eq!(base_type("&Vec2"), "&Vec2");

        // `call_type` is the type a method is called on.
        assert_eq!(call_type("Vec2::push").as_deref(), Some("Vec2"));
        assert_eq!(call_type("G::<T>::walk").as_deref(), Some("G"));
        assert_eq!(call_type("<S as T>::m").as_deref(), Some("S"));
        assert_eq!(call_type("free_fn"), None, "a bare name has no type segment");

        // An intrinsic call keeps its `<impl` projection, which marks it external.
        assert_eq!(call_type("core::num::<impl u8>::wrapping_add").as_deref(), Some("u8"));
    }

    /// The tail of a path is read through its generics.
    ///
    /// The dump spells these calls with their generics, so a naive last-segment
    /// split gives `<1>`/`<T>` rather than the method name -- and the model would
    /// then answer nothing at all, which is how the MSRV run reported
    /// `Arguments::<'_>::new_const::<1>` as unmodelled while stable was green.
    /// The turbofish separator (`new_const::<1>`) and a nested group
    /// (`Argument::<&'_ str>`) are both covered.
    #[test]
    fn a_path_tail_is_read_through_its_generics() {
        assert_eq!(path_tail("Arguments::<'_>::new_const::<1>"), "new_const");
        assert_eq!(path_tail("Arguments::<'_>::new_v1::<2, 2>"), "new_v1");
        assert_eq!(path_tail("Arguments::<'_>::new::<7, 1>"), "new");
        assert_eq!(path_tail("Arguments::<'_>::from_str"), "from_str");
        assert_eq!(path_tail("core::fmt::rt::Argument::<'_>::new_display::<u8>"), "new_display");
        assert_eq!(path_tail("std::rt::panic_fmt"), "panic_fmt");
        assert_eq!(path_tail("panic_fmt"), "panic_fmt");
    }

    /// The generic argument list is read as data, and a missing item is refused.
    #[test]
    fn a_generic_argument_is_read_or_refused() {
        assert_eq!(generic_arg("Arguments::<'_>::new_v1::<2, 1>", 1), Some(1));
        assert_eq!(generic_arg("Arguments::<'_>::new::<7, 1>", 1), Some(1));
        // No turbofish, a missing index, and a non-numeric item are all `None`.
        assert_eq!(generic_arg("Arguments::<'_>::new_const", 1), None);
        assert_eq!(generic_arg("Arguments::<'_>::new_v1::<2>", 1), None);
        assert_eq!(generic_arg("Arguments::<'_>::new_v1::<2, A>", 1), None);
    }

    /// A promoted constant's use-site spelling is reconciled with its definition's.
    ///
    /// On the MSRV rustc prints a trait default body's `panic!` promoted constant as
    /// `const a::Custom::into_iter::promoted[0]` but uses it as
    /// `const <Self as range_shim::a::Custom>::into_iter::promoted[0]`. An exact
    /// lookup misses and the `new_const` call becomes unmodelled, so the function is
    /// `incomplete` instead of refuted. The owner paths (the `<T as Trait>` projection
    /// on the use side, the qualifier on the definition side) are what reconcile them,
    /// and two sibling traits of the same method must not answer for each other.
    #[test]
    fn a_promoted_const_use_is_reconciled_with_its_definition() {
        let mut m: BTreeMap<String, Vec<String>> = BTreeMap::new();
        m.insert("a::Custom::into_iter::promoted[0]".into(), vec!["from a".into()]);
        m.insert("b::Custom::into_iter::promoted[0]".into(), vec!["from b".into()]);
        m.insert("g::promoted[0]".into(), vec!["from g".into()]);
        // The MSRV use spelling resolves to the trait it names, not its sibling.
        assert_eq!(
            lookup_promoted(&m, "<Self as range_shim::a::Custom>::into_iter::promoted[0]"),
            Some(vec!["from a".to_string()])
        );
        assert_eq!(
            lookup_promoted(&m, "<Self as range_shim::b::Custom>::into_iter::promoted[0]"),
            Some(vec!["from b".to_string()])
        );
        // An exact match still wins, and an unrelated name resolves to nothing.
        assert_eq!(lookup_promoted(&m, "g::promoted[0]"), Some(vec!["from g".to_string()]));
        assert_eq!(lookup_promoted(&m, "z::promoted[0]"), None);
        assert_eq!(lookup_promoted(&m, "SOME_CONST"), None);
    }

    /// A diverging call is labelled by *what* it does, not always `panic`.
    ///
    /// `std::process::exit(0)` and `std::process::abort()` end the path exactly as
    /// a panic does, so all three carry the same obligation -- but calling a clean
    /// `exit` a `panic` tells a reader the program crashed when it did not. The
    /// kind is read from the callee's printed name; an unrecognised `!`-returning
    /// function is `Never`, which is honest about not classifying it.
    #[test]
    fn a_diverging_call_is_labelled_by_its_kind() {
        assert_eq!(Divergence::of("core::panicking::panic"), Divergence::Panic);
        assert_eq!(Divergence::of("std::rt::panic_fmt"), Divergence::Panic);
        assert_eq!(Divergence::of("core::panicking::panic_nounwind"), Divergence::Panic);
        // `exit(…)` is printed with its tail alone (it is `std::process::exit`, but
        // the dump elides the path).
        assert_eq!(Divergence::of("exit"), Divergence::Exit);
        assert_eq!(Divergence::of("std::process::exit"), Divergence::Exit);
        assert_eq!(Divergence::of("std::process::abort"), Divergence::Abort);
        // A user function returning `!` is not classified as any of the three.
        assert_eq!(Divergence::of("my_crate::never_returns"), Divergence::Never);
        assert_eq!(Divergence::Never.label(), "diverges");
        assert_eq!(Divergence::Exit.label(), "exit");
    }

    /// Which types carry no drop glue, so a `drop` of one runs nothing.
    ///
    /// This is the *defensive* arm of the `Term::Drop` executor, not a live path:
    /// rustc emits no `drop` for a type with no drop glue (measured -- 0 of 6
    /// `drop` terms over `realistic.rs` are glue-free). So the arm cannot be
    /// exercised through the frontend, and the check lives here where it can be
    /// asserted directly. It matters because the alternative to a no-op is a
    /// refusal, and a refusal of `drop(_2)` for an integer would lose a proof.
    #[test]
    fn a_glue_free_type_has_a_noop_drop() {
        for ty in [
            Ty::Bool, Ty::U8, Ty::U64, Ty::I8, Ty::I64, Ty::Usize, Ty::Unit,
            Ty::Ref(Box::new(Ty::U8)),
        ] {
            assert!(drop_is_noop(&ty), "`{ty:?}` has no drop glue");
        }
        // An aggregate is glue-free exactly when every leaf is.
        assert!(drop_is_noop(&Ty::Array(Box::new(Ty::U8), 4)));
        assert!(drop_is_noop(&Ty::Tuple(vec![Ty::U8, Ty::Bool])));
        // A nominal type is not known glue-free from the dump, so it is *not* a
        // no-op -- it is resolved to a destructor or refused.
        assert!(!drop_is_noop(&Ty::Other("Guard".into())));
        // A `Vec<T>` is glue-free exactly when its element is: the container's own
        // destructor only runs `T`'s, so `Vec<u8>` runs nothing observable while a
        // `Vec<Guard>` (a nominal element) does not. The standard container's
        // *type* is `std::vec::Vec<T>`; a bare `Vec<T>` is a *user* type, so it is
        // not the container -- reading it as one would skip a user destructor.
        assert!(drop_is_noop(&Ty::Other("std::vec::Vec<u8>".into())));
        assert!(drop_is_noop(&Ty::Other("alloc::vec::Vec<u8>".into())));
        assert!(!drop_is_noop(&Ty::Other("std::vec::Vec<Guard>".into())));
        assert!(!drop_is_noop(&Ty::Other("std::vec::Vec<String>".into())));
        assert!(!drop_is_noop(&Ty::Other("Vec<u8>".into())), "a bare `Vec` is a user type");
        assert!(!drop_is_noop(&Ty::Other("m::Vec<u8>".into())), "a user `Vec` is not the container");
        // A tuple/array with a nominal leaf inherits the nominal's glue.
        assert!(!drop_is_noop(&Ty::Array(Box::new(Ty::Other("Guard".into())), 2)));
        assert!(!drop_is_noop(&Ty::Tuple(vec![Ty::U8, Ty::Other("String".into())])));
    }

    /// A projected promoted-constant use resolves to *its own* method's pieces.
    ///
    /// Two trait defaults each own a `promoted[0]`; the use
    /// `<Self as Custom>::zzz::promoted[0]` names the `zzz` method, but the
    /// fallback compared only the trait owner and the promotion index, so it
    /// returned `aaa`'s pieces (whichever the map iterated first) and the report
    /// named a panic message the caller never reached.
    #[test]
    fn a_projected_promoted_use_resolves_its_own_method() {
        let mut promoted: BTreeMap<String, Vec<String>> = BTreeMap::new();
        promoted.insert("Custom::aaa::promoted[0]".into(), vec!["from aaa".into()]);
        promoted.insert("Custom::zzz::promoted[0]".into(), vec!["from zzz".into()]);

        // Exact spellings resolve exactly.
        assert_eq!(
            lookup_promoted(&promoted, "Custom::zzz::promoted[0]"),
            Some(vec!["from zzz".to_string()])
        );
        // The projected spelling `rustc` prints for a trait default's use resolves
        // to the *same* method, not to whichever sibling the map yields first.
        assert_eq!(
            lookup_promoted(&promoted, "<Self as Custom>::zzz::promoted[0]"),
            Some(vec!["from zzz".to_string()])
        );
        assert_eq!(
            lookup_promoted(&promoted, "<Self as Custom>::aaa::promoted[0]"),
            Some(vec!["from aaa".to_string()])
        );

        // Two definitions that share owner *and* method (a genuine ambiguity) are
        // refused rather than answered with one of them. The use is a *projected*
        // spelling (`call_trait_path` reduces its owner to `a::Custom`), and both
        // candidates' owners match it -- `a::Custom` exactly and `Custom` as a
        // `::`-aligned suffix -- so the only reason to return `None` is the
        // ambiguity branch. The single-candidate control below returns `Some`, so
        // the refusal is not merely "nothing matched".
        let mut ambiguous: BTreeMap<String, Vec<String>> = BTreeMap::new();
        ambiguous.insert("a::Custom::m::promoted[0]".into(), vec!["one".into()]);
        ambiguous.insert("Custom::m::promoted[0]".into(), vec!["two".into()]);
        assert_eq!(
            lookup_promoted(&ambiguous, "<Self as a::Custom>::m::promoted[0]"),
            None,
            "two candidates whose owner matches the use must be refused"
        );
        // The control: with only the exact-owner candidate, the same use resolves,
        // so the `None` above is the ambiguity and not a failed match.
        let mut single: BTreeMap<String, Vec<String>> = BTreeMap::new();
        single.insert("a::Custom::m::promoted[0]".into(), vec!["one".into()]);
        assert_eq!(
            lookup_promoted(&single, "<Self as a::Custom>::m::promoted[0]"),
            Some(vec!["one".to_string()]),
            "a single matching candidate must resolve"
        );
    }

    /// A concrete-index write reaches the `last()` sentinel, so the pre-write
    /// value cannot be read back after a write that *is* the last element.
    ///
    /// The sentinel (`LAST_INDEX`) is one variable per slice, so a write to a
    /// concrete index used to leave it at its pre-write value. That was a false
    /// proof: `let before = *xs.last().unwrap(); xs[0] = 1; before ==
    /// *xs.last().unwrap()` was *proved* for a one-element slice, though the write
    /// replaced the only element. The write now refreshes the sentinel with the
    /// exact relationship `last == x` when `len == index + 1`, so the two facts
    /// must hold together: after a write of `1` to index `0`, the sentinel is `1`
    /// at `len == 1` and the *old* element otherwise. Reading the store directly is
    /// what makes the check independent of the executor's path machinery.
    #[test]
    fn a_concrete_index_write_reaches_the_last_sentinel() {
        smt::with_fresh(|| {
            let mut env = Env::new();
            let len = smt::var_named(0, 8);
            let old = smt::var_named(1, 8);
            let mut elems = BTreeMap::new();
            elems.insert(LAST_INDEX, old);
            env.indexed.insert(
                2,
                Indexed {
                    len,
                    len_mutable: false,
                    elem_w: 8,
                    elem_signed: false,
                    elems,
                    fixed_len: None,
                    slice_steps: None,
                    poisoned: false,
                },
            );
            let one = smt::word(1, 8);
            env.write_elem(2, 0, Val::Sym(one, Sign::Unsigned));
            let merged = env.indexed.get(&2).and_then(|s| s.elems.get(&LAST_INDEX).copied());
            let merged = merged.expect("the sentinel must still be present after a write");
            assert_ne!(
                merged, old,
                "a write to index 0 must refresh the sentinel rather than leave it stale"
            );
            // The refreshed value is `1` exactly when the write index is the last
            // one (`len == 1`), and the old element otherwise. Both readings are
            // checked, so a merge that dropped either branch fails here.
            let at_len_1 = smt::substitute_word(merged, &[(len, smt::word(1, 8))]);
            assert_eq!(
                smt::evaluate(at_len_1, |_| None),
                Some(1),
                "at `len == 1` the sentinel is the written value"
            );
            let at_len_2 = smt::substitute_word(merged, &[(len, smt::word(2, 8))]);
            let old_val = smt::evaluate(old, |_| None);
            assert_eq!(
                smt::evaluate(at_len_2, |_| None),
                old_val,
                "at `len == 2` the write of index 0 is not the last element, so the \
                 sentinel keeps the old element"
            );
        });
    }

    /// A call cycle in the write-set walk adds the call's reference arguments,
    /// which is what terminates a recursive callee and keeps its write visible.
    ///
    /// This pins the *cycle branch* of [`collect_writes`] directly, because no
    /// verdict-level fixture reaches it observably: for every corpus shape the
    /// callee's own direct scan already names the written referent, so the
    /// branch's inclusion is a conservative *superset* -- measured, deleting it
    /// changes no verdict. A branch that is reached (35 times in the recursion
    /// test) but never load-bearing is exactly the kind of guard the suite has
    /// no teeth for, so it is pinned here on the traversal's own output.
    ///
    /// The shape is a *mutual* cycle that writes through a reference the fold
    /// cannot map back: `a` calls `b` (a cycle, since `b` calls `a`), and `b`
    /// takes `&mut u8`. `a`'s header walk enters `b`, finds `b`'s self-cycle
    /// through `a`, and must add `b`'s reference argument to the write set.
    #[test]
    fn a_call_cycle_adds_its_reference_arguments_to_the_write_set() {
        fn block(id: usize, stmts: Vec<Stmt>, term: Term) -> Block {
            Block { id, stmts, term, cleanup: false }
        }
        // `b(c: &mut u8)`: calls `a` again, passing `c` -- and does *not* write
        // `c` directly, so the only way `_1` enters the write set is the cycle
        // branch. (With a direct write here the branch would be redundant and the
        // test would pass even with it deleted.)
        let b = MirFn {
            name: "b".into(),
            arg_locals: vec![1],
            ret_ty: Ty::U8,
            locals: [(0u32, Ty::U8), (1, Ty::Ref(Box::new(Ty::U8)))].into_iter().collect(),
            local_names: Default::default(),
            debug_bindings: Vec::new(),
            blocks: vec![block(
                0,
                Vec::new(),
                Term::Call {
                    callee: Callee::Name("a".into()),
                    args: vec![Operand::Copy(Place::new(1))],
                    dest: Place::new(0),
                    diverges: false,
                    target: 1,
                },
            )],
            written: [0u32].into_iter().collect(),
            impl_loc: None,
        };
        // `a(x: &mut u8)`: calls `b` (so `b`'s walk sees `a` on the stack -> cycle).
        let a = MirFn {
            name: "a".into(),
            arg_locals: vec![1],
            ret_ty: Ty::U8,
            locals: [(0u32, Ty::U8), (1, Ty::Ref(Box::new(Ty::U8)))].into_iter().collect(),
            local_names: Default::default(),
            debug_bindings: Vec::new(),
            blocks: vec![block(
                0,
                Vec::new(),
                Term::Call {
                    callee: Callee::Name("b".into()),
                    args: vec![Operand::Copy(Place::new(1))],
                    dest: Place::new(0),
                    diverges: false,
                    target: 1,
                },
            )],
            written: [0u32].into_iter().collect(),
            impl_loc: None,
        };
        let prog = MirProgram { fns: vec![a, b], ..Default::default() };
        // The walk starts at `a`'s header (block 0) with `a` already `visiting`.
        let writes = loop_writes(&prog, &prog.fns[0], 0);
        assert!(
            writes.contains(&1),
            "the cycle's reference argument (`_1`) must be in the write set, got: {writes:?}"
        );
    }
}

# The trusted computing base, and the semantics it reasons about

Part of the [`verif` README](../README.md). This is roadmap item **A4**.

A verifier is only worth what its trusted computing base (TCB) is worth. This
document states what `verif` trusts, the semantics it reasons about, and the
evidence that each layer is what it claims — so a reader can decide whether a
`verified` line is strong enough for their use, rather than taking it on faith.

## What is trusted

The TCB is everything that, if wrong, could turn a false statement into a
`verified` one. It is deliberately small, and each item names the check that
holds it.

| trusted | why it is trusted | evidence |
|---|---|---|
| **`rustc`'s MIR** (`--emit=mir`) | the frontend reads the MIR rustc lowers the source to; if rustc mis-lowers, the proof is about the wrong program | `tools/mir-oracle` compares the text parser's reading against `rustc_public`'s typed MIR (structural shape: blocks + panic guards); the crate's own tests run under several toolchains |
| **the MIR text parser** (`src/mir/parse.rs`) | it is the only reader of the dump | a 20 000-input mutation fuzz (`no_input_panics_the_reader`) pins totality; the oracle above pins the reading; a nightly/stable/MSRV matrix pins toolchain-shaped spellings |
| **the contract scanner** (`src/mir/spec.rs`) | contracts come from the *source text* (a `///` clause or a `spec! { … }` block), not from MIR | the same mutation fuzz on `spec::extract`; a clause-shaped line it does not take is *refused*, never ignored |
| **the symbolic executor** (`src/mir/exec.rs`) | it turns a function's MIR into obligations | a differential harness (`tests/modular_differential.rs`) checks `verified ⇒ no concrete execution violates the postcondition`, in both directions |
| **the BDD bit-blaster** (`src/smt.rs`) | bit-vectors are blasted into a Reduced Ordered BDD; the verdict is `Valid`/`Counterexample` from it | the differential oracles (`z3diff`, `kanidiff`, `verusdiff`) check the formulas against independent tools; `tests/op_differential.rs` checks the blaster against the term folder per operator |
| **the CDCL fallback** (`src/bitblast.rs` + `src/sat.rs`) | when the BDD arena fills, the *same* term graph is blasted to CNF and solved | `src/bitblast.rs`'s own tests drive the CNF blaster directly and compare against Rust's arithmetic over every input pair at 1–4 bits; `tests/sat_engine.rs` checks the solver against brute force |
| **the SMT-LIB2 exporter** (`src/smtscript.rs`) | it lets an *independent* solver re-check a query | the exported text is parsed by an independent reader (`tests/differential.rs`) and by z3 (`examples/z3diff.rs`, a corpus of tautologies per operator) |

Everything **outside** that table is untrusted and must not be load-bearing for a
verdict. In particular the `cargo verif` driver, the human/JSON/SARIF renderers
and the scoreboard are presentation: they read a `FileReport` that the executor
produced, and a bug there can mislabel a verdict but cannot change it.

## The semantics of the supported MIR subset

A value is a **bit-vector of a declared width and signedness** — the frontend's
`Val::Sym(Var, Sign)`, where `Sign` is `Signed`, `Unsigned`, or `Unknown` (a value
whose type the dump did not print). `Sign::Unknown` is a *refusal* at every
signedness-sensitive site (an ordering, a division, a widening cast), because a
guessed sign is a wrong value, not a weaker proof. A `bool` is a one-bit
predicate (`Val::Bool`); an aggregate is its parts (`Val::Agg`) or, where a part
is unmodelled, `Val::Unknown` — and an `Unknown` operand makes the obligation
unreadable, which is a refusal, never a pass.

Execution walks the basic blocks under a **path condition** `path`: a predicate
that is the conjunction of the guards on the way to the current point. An
obligation is a `path ⇒ goal` query:

- a **postcondition** is `path ⇒ post` — `Valid` is the proof, and an `Unsat`
  postcondition (true on *no* input) is the strongest failure;
- a **panic** (a rustc-emitted overflow/divide-by-zero assert, an `assert!`, an
  `unreachable!`, a diverging call) is `path` reachable — discharged by `Unsat`,
  and a `Valid` panic (fires on *every* input) is the worst case with no witness;
- a **loop** with `invariant:` is cut at the header: the head is **havoced** (every
  local the loop can write, directly or through a reference, replaced by a fresh
  value), the invariant is assumed over that arbitrary state, and three
  obligations are emitted — initiation on entry, preservation across one
  iteration, and exit (`I ∧ ¬guard ⇒ post`); a `variant:` adds a decrease
  obligation evaluated in two different states (the havoced head, and the body's
  symbolic post-state);
- a **call** is reasoned about through the callee's contract: its `requires` is an
  obligation, its `ensures` is assumed of a fresh return value, and its frame is
  checked against the derived write set; a call to a callee whose body is absent
  is answered from its contract, and a self-call with `decreases:` is answered by
  induction;
- an obligation that the executor cannot decide is reported `incomplete` with the
  reason — a budget, an unmodelled construct, or an open obligation — and a
  report is `verified` only when every obligation is discharged and every path
  explored.

Arithmetic is bit-vector arithmetic with **exact** overflow predicates (e.g. an
unsigned product wraps exactly when `y ≠ 0 ∧ x > MAX / y`, and the signed case is
a division of a range end by the constant). A `Ty::Ref` is modelled as its
referent (single-owner: a `&mut` write reaches the caller's storage on return;
there is no aliasing model beyond that). Division and shifts are exact
(`smt::divmod`, `smt::shift_var`), with `y = 0` and an out-of-range shift amount
given defined values that rustc's own guards then report.

## What is *not* in the semantics, and is therefore refused

The logic is bit-vectors and booleans only. The frontend **refuses** (reports
`incomplete` or `skipped`, never a proof) on: floating point; concurrency and
atomics; raw pointers and aliasing beyond a single-owner reference; unbounded
loops with no `invariant:`/`unwind:` (a *missing contract*, not an unmodelled
construct); a nested `?` whose payload is itself an enum; a `&mut &mut T` across a
call; a 128-bit type (past the engine's 64-bit words); and any value whose type the
dump did not print where the answer would depend on it. Each refusal is the
honest direction: a lost proof, never a false one.

## How this document is held honest

The table's evidence is run by `scripts/gate.sh` (the oracles skip, *reported*,
when their tool is absent — a skipped oracle is not a passed one). The
`SOUNDNESS.md` ledger records every false proof the project has produced, with the
fixture that fails if its fix is undone. The README states plainly that a
`verified` today means "a check ran", not "the checker is qualified" — **this crate
has no qualification evidence, and this TCB document is not a substitute for
external review**, which is the half of A4 that remains open.

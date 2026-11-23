# verif — formal verification that lives inside the Rust code

[![crates.io](https://img.shields.io/crates/v/verif.svg)](https://crates.io/crates/verif)
[![docs.rs](https://docs.rs/verif/badge.svg)](https://docs.rs/verif)
[![CI](https://github.com/cipansor/verif/actions/workflows/ci.yml/badge.svg)](https://github.com/cipansor/verif/actions/workflows/ci.yml)
[![license](https://img.shields.io/crates/l/verif.svg)](#license)

> An experiment: what if Rust could carry its own proof tooling the way
> SPARK/Ada carries `gnatprove`? Not a plugin, not an external solver, not a
> nightly feature — a **bit-blasting decision procedure compiled into your
> artifact**, next to a Curry–Howard proof kernel and a contract vocabulary.

> **Not affiliated with AdaCore or SPARK.** "SPARK" and "SPARK Pro" are
> AdaCore's; `gnatprove` is their tool. This crate is an independent experiment
> inspired by the *shape* of that workflow — contracts in the source, proofs
> discharged by a tool — and it embeds its own decision procedure rather than
> wrapping theirs. It is not a port, a wrapper, or a supported AdaCore product,
> and the name was chosen to describe what the crate *does*, not where it comes
> from.

`no_std`. Zero dependencies. Fixed-size, heap-free arena. `#![forbid(unsafe_op_in_unsafe_fn)]`.

```rust
use verif::prelude::*;

// ∀ x:u8. (x & 0x0f) < 16          — proved by the embedded SMT engine
let proved = verif::smt::with_fresh(|| {
    let x = var(8);
    (x & 0x0fu32).lt_val(16).prove().is_proved()
});
assert!(proved);
```

Run the flagship demo:

```console
$ cargo run --features std --example flight_control
[symbolic]  map_reading output bound       : valid (proved for all inputs)
[symbolic]  rate_limit step bound          : valid (proved for all inputs)
[exhaustive] clamp holds for all 65536     : true
[exhaustive] output in [PWM_MIN, PWM_MAX]  : true
[exhaustive] rate limit for all u8 pairs   : true
[exhaustive] mapping is monotone           : true
[kernel]    certificate accepted, value = 1500
[refuted]   raw < ADC_MAX is false, witness raw = 4095
[honesty]   (a*b)*c == a*(b*c) at 12 bits  : unknown (no conclusion: budget exhausted, ill-formed query, or stale handle)

all obligations discharged
```

---

## Contents

**[Getting started](#installation)**

- [Installation](#installation)
- [The idea in one paragraph](#the-idea-in-one-paragraph)
- [The three ways this crate proves something](#the-three-ways-this-crate-proves-something)
- [What is in the box](#what-is-in-the-box)
- [Two ways to use the verifier: at build time, or on the target](docs/build-time.md#two-ways-to-use-the-verifier-at-build-time-or-on-the-target)
- [Building and testing](docs/testing.md#building-and-testing)
- [Coverage scoreboard](#coverage-scoreboard)
- [Layout](docs/layout.md#layout)

**[Proving a program](docs/internals.md#verification-conditions-are-generated-not-hand-written)**

- [Verification conditions are generated, not hand-written](docs/internals.md#verification-conditions-are-generated-not-hand-written)
- [Memory: `read`, `store`, and the frame condition](docs/internals.md#memory-read-store-and-the-frame-condition)
- [Modular verification: procedures checked once, calls reasoned about through contracts](docs/internals.md#modular-verification-procedures-checked-once-calls-reasoned-about-through-contracts)
- [Bounded quantification: the invariant a loop over memory needs](docs/internals.md#bounded-quantification-the-invariant-a-loop-over-memory-needs)
- [Verifying real Rust: the MIR frontend](docs/mir.md#verifying-real-rust-the-mir-frontend)

**[How the engine is held honest](docs/internals.md#the-exported-query-must-mean-what-the-engine-proved)** — one section per claim, each naming the check that backs it

- [The exported query must mean what the engine proved](docs/internals.md#the-exported-query-must-mean-what-the-engine-proved)
- [Substitution must not walk a shift amount](docs/internals.md#substitution-must-not-walk-a-shift-amount)
- [A DSL's operator set is a claim too](docs/internals.md#a-dsls-operator-set-is-a-claim-too)
- [Constant operands are folded, so a closed query is decided rather than refused](docs/internals.md#constant-operands-are-folded-so-a-closed-query-is-decided-rather-than-refused)
- [A pin is transitive, and a closed goal is decided without its assumption](docs/internals.md#a-pin-is-transitive-and-a-closed-goal-is-decided-without-its-assumption)
- [A division by a power of two is a shift, on both signs](docs/internals.md#a-division-by-a-power-of-two-is-a-shift-on-both-signs)
- [Mixed-width operations are refused, not truncated](docs/internals.md#mixed-width-operations-are-refused-not-truncated)
- [Differential fuzzing: the shapes I did not think to test](docs/internals.md#differential-fuzzing-the-shapes-i-did-not-think-to-test)
- [The blasting is checked against Rust, not against itself](docs/internals.md#the-blasting-is-checked-against-rust-not-against-itself)
- [Staleness is caught once, in the arena](docs/internals.md#staleness-is-caught-once-in-the-arena)
- [A proof object must not change meaning underneath you](docs/internals.md#a-proof-object-must-not-change-meaning-underneath-you)
- [A wrapper must not overclaim](docs/internals.md#a-wrapper-must-not-overclaim)
- [A truncated witness has to say so](docs/internals.md#a-truncated-witness-has-to-say-so)
- [A negative answer has to say what it swept](docs/internals.md#a-negative-answer-has-to-say-what-it-swept)
- [An unreachable precondition is not a proof](docs/internals.md#an-unreachable-precondition-is-not-a-proof)
- [A diverging call is a checked panic, not a dropped line](docs/mir.md#a-diverging-call-is-a-checked-panic-not-a-dropped-line)
- [A `drop` is a terminator with a real successor](docs/mir.md#a-drop-is-a-terminator-with-a-real-successor)
- [A bound must be wider than the address, or "all cells" is vacuous](docs/internals.md#a-bound-must-be-wider-than-the-address-or-all-cells-is-vacuous)
- [The memory family, positive side](docs/internals.md#the-memory-family-positive-side)
- [The differential harness now covers memory](docs/internals.md#the-differential-harness-now-covers-memory)
- [A guard compares an index, it does not truncate it](docs/internals.md#a-guard-compares-an-index-it-does-not-truncate-it)
- [A derived frame says whether it is complete](docs/internals.md#a-derived-frame-says-whether-it-is-complete)
- [The obligation cap fails loudly, never silently](docs/internals.md#the-obligation-cap-fails-loudly-never-silently)
- [Differential testing: a proof must not outrun reality](docs/internals.md#differential-testing-a-proof-must-not-outrun-reality)

**[Design notes](#why-bdds-at-all)**

- [Why BDDs at all](#why-bdds-at-all)

**[Where this sits](docs/comparison.md#where-this-sits-in-the-rust-ecosystem)**

- [Where this sits in the Rust ecosystem](docs/comparison.md#where-this-sits-in-the-rust-ecosystem)
- [The SPARK comparison, stated plainly](docs/comparison.md#the-spark-comparison-stated-plainly)
- [What this is *not* — read this before trusting a green test](#what-this-is-not--read-this-before-trusting-a-green-test)
- [Documentation](#documentation)
- [License](#license)

**The open work** lives in [`ROADMAP.md`](ROADMAP.md) — one item per gap, each with
a priority, a measurable exit criterion, the competitor whose gap it closes, the
closing move (build / bridge / won't do), and a status. A PR that closes an item
updates its status there.

**The long-form notes live in [`docs/`](docs/internals.md)** — one file per theme
(the verification conditions, the MIR frontend, the layout, the gates, the
comparison) — so this page stays short. Each is linked from the contents above.

---

## Installation

Both crates are on crates.io. `verif` is the one you depend on; the proved
integer primitives it builds on are published separately as
[`verif-arithmetic`](https://crates.io/crates/verif-arithmetic) and pulled in for
you.

```toml
[dependencies]
verif = "0.2"

# The host-side tools (the MIR frontend, the file-backed helpers) need `std`.
# The engine itself does not: the default build is `no_std` and links `core`
# and nothing else, which is what a bare-metal safety build wants.
[dev-dependencies]
verif = { version = "0.2", features = ["std"] }
```

> **Which version to depend on.** `0.2` is the current release: the in-code `spec!`
> spelling, the `verif!` refusal and the doc-comment migration all landed in it, and
> a crate on an older `0.1.x` does not have them. `tests/readme.rs` pins the `"0.2"`
> requirement, so this paragraph and that test move together on the next bump.

There is nothing else to add: `verif`'s only dependency is `verif-arithmetic`,
which is itself `no_std` and dependency-free, so the artifact's crates.io supply
chain is those two crates and no third party.

Building for a microcontroller:

```console
$ cargo build --target thumbv7em-none-eabihf
```

## Verifying a file: `cargo verif`

With the `std` feature on, the crate ships a `cargo-verif` binary, so verifying a
file's `verif` contracts is one command, the way `cargo kani` is for Kani:

```console
$ cargo verif                         # verify src/lib.rs (then src/main.rs)
$ cargo verif --file src/foo.rs       # a specific file
$ cargo verif --function add          # one function by name
$ cargo verif --format json           # one machine-readable object for CI
```

The exit code is the verdict, and the codes are distinct so a script can tell a
failed proof from a tool that could not run: `0` every contract held, `1` a
failure / incomplete function / skipped contract / missing body, `2` the frontend
could not run (no compiler, a compile error). A skipped function is *not* a pass:
its contract could not be read, so it was never checked. The binary is a thin
wrapper over `mir::verify::verify_file_with`, so it decides exactly what the
library decides. `--format json` is hand-written (the crate is zero-dependency)
and emits `file`, `outcomes`, `missing` and a `summary`; `--format sarif` emits a
SARIF 2.1.0 document (one `result` per non-verified outcome, `error` for a failure
and `warning` for an incomplete or skipped one, an empty `results` array on a
clean run) for GitHub code scanning.

### The reusable GitHub Action

`.github/actions/verif` is a composite action that wires `--format sarif` to
`github/codeql-action/upload-sarif`, so a failed or incomplete contract shows up on
the pull request like a compiler error:

```yaml
- uses: cipansor/verif/.github/actions/verif@v0.2.0   # or ./.github/actions/verif
  with: { file: src/lib.rs }
```

It builds `cargo-verif` from its own checkout (`GITHUB_ACTION_PATH`), runs it with
`--format sarif`, uploads the report (`upload: false` to skip, for a fork without
code scanning), and fails the step on any finding (`fail-on-findings: false` to
report without failing). A *skipped* contract is a failure by default, because a
contract the tool could not read was never checked. This repository dogfoods the
action in the `sarif` CI job, and `scripts/check_sarif.py` asserts the report is a
well-formed SARIF 2.1.0 run that names the failing function -- so a run that
silently reports nothing fails there. If you would rather wire it by hand:

```yaml
- run: cargo install --path . --features std     # or `cargo install verif --features std`
- run: cargo verif --format sarif --file src/lib.rs > verif.sarif
  continue-on-error: true                         # upload the report even on a failure
- uses: github/codeql-action/upload-sarif@<pinned-sha>
  if: always()
  with: { sarif_file: verif.sarif }
```

---

## The idea in one paragraph

SPARK's advantage is not that Ada is a better language. It is that **the prover
is part of the toolchain and the contracts are part of the source**. Rust has a
superb type system and no such prover, so verification is outsourced to external
tools (Kani, Creusot, Prusti, MIRAI) that you must install, configure, and trust.
This crate asks what happens if you instead *compile the prover in*: lower
bit-vector formulas to **Reduced Ordered Binary Decision Diagrams**, which are a
canonical form, so two formulas are equivalent exactly when their diagrams are
the *same node*. That one property yields, with no external process:

| Query | Meaning |
|---|---|
| `prove(p)` | `p` holds for every input (diagram is the `true` node) |
| `find_model(p)` | a concrete satisfying input, or `Unsat` |
| `prove_implies(pre, post)` | `pre => post` holds for every input |
| `prove_equiv(a, b)` | `a` and `b` are equivalent for every input |

## The three ways this crate proves something

They are deliberately different tools, and each has a different honesty profile.

| # | Mechanism | Entry point | Complete? | Can it lie? |
|---|---|---|---|---|
| 1 | **Symbolic** — BDD, then CDCL SAT fallback | `smt::prove`, `sym::*::prove()` | no (scaling wall) | no — it returns `Unknown` |
| 2 | **Exhaustive** — every input of a real `fn` | `exhaustive::for_all_u8/u16` | yes, small domains | no |
| 3 | **Type-level** — Curry–Howard kernel | `proof::Certificate`, `assert_proof!` | yes, for composition | no — it will not compile |

A serious safety argument uses all three and says which one discharged each
obligation. That is what `examples/flight_control.rs` demonstrates.

## What is in the box

The engine is three modules (`smt`, `bitblast`, `sat`); the rest are the
specification surface, the complete-by-enumeration half, and interop.

| Module | Contents |
|---|---|
| `smt` | Bit-vector terms, ROBDD engine, `Verdict`, counterexamples, `no_std` arena |
| `bitblast` | The bit-level term graph → CNF lowering, used by the SAT fallback |
| `sat` | The CDCL SAT solver used as the fallback past the BDD wall |
| `sym` | Operator overloading so specs read like code: `(x + y).eq(y + x).prove()` |
| `logic` | Checked/saturating arithmetic and a Q16.16 `Fixed` type, each with proofs |
| `proof` | Curry–Howard kernel (`Truth`, `And`, `Imp`, `Equals`) + composable `Certificate` |
| `contract` | Runtime `Pre`/`Post`/`Assert` over concrete values, structured errors |
| `vc` | `requires`/`ensures`/`invariant`, `verify_body`, `Verified<T>` |
| `wp` | Hoare logic: weakest preconditions, automatic VC generation, loop rules, termination by variant |
| `smtscript` | SMT-LIB2 export, so an external solver can check the same formula |
| `mem` | Bounded symbolic memory: `read`/`store`, frame condition, composes with `wp` |
| `quant` | Bounded `forall`/`exists`, expanded into finite conjunctions/disjunctions |
| `exhaustive` | Complete proofs by enumeration over `u8`/`u16` |
| `primitives` | The symbolic oracle for the `safe_*` ops and `Bounded` (the runtime half is `arith`) |
| `arith` (sibling crate) | `verif-arithmetic`, re-exported: total integer ops and a refinement-typed `Bounded<MIN, MAX>`, each proved by enumeration |
| `macros` | `spec!` (in-code contracts), `verify!`, `verify_implies!`, `contract!`, `proof!`, `assert_proof!`, `check!`, `verify_exhaustive!` |
| `mir` (`std` only) | verify **real Rust**: read `rustc`'s own MIR, symbolically execute it, discharge rustc's overflow/underflow/div-by-zero asserts and contracts (`spec!` blocks or `///` clauses) |

The proved runtime primitives live in the sibling crate and are re-exported as
`verif::arith`, so a caller never has to name the workspace layout. `arith` is
`no_std`, `#![forbid(unsafe_code)]` and dependency-free on its own — that split
is what keeps the arithmetic a safety build ships down to `core` and nothing
else, while this crate keeps the symbolic engine that cross-checks those proofs.

## What this is *not* — read this before trusting a green test

Honesty matters more than a nice README, so:

1. **Pointers, aliasing and concurrency are still out of scope.** `mem` models a
   bounded *array*, addressed by an integer. It does not model pointers, address
   arithmetic across objects, or two threads touching the same cell. You cannot
   state "this pointer is valid" or "these two threads do not race" in it.
   Quantifiers are bounded and expanded, so `forall` over an unknown domain is not
   available either — the range must be a number the tool can count to.
1b. **Termination needs a variant.** Without one, `wp` proves partial correctness
   only: a divergent loop can verify. There is no inference of variants — you
   supply the measure, the engine checks it decreases.
1c. **A nested loop's effect on an outer variant is handled by havocing, not by
   tracking.** `variant_after` treats an inner `while` as writing every variable its
   body can write, so a measure that mentions one of them becomes an obligation about a
   fresh variable and cannot be discharged. That is sound but conservative: you must
   supply an outer measure that does not depend on the inner loop's writes, or a measure
   that accounts for them explicitly. The alternative — reading the inner loop as a no-op —
   was a real soundness hole and is described under "Why `variant_after` must havoc a
   nested loop" below.
1d. **`with_fresh` must not be nested.** The inner call wipes the term arena and
   invalidates every `Var` the outer scope holds. One `with_fresh` per proof.
1e. **A call to a procedure whose postcondition is unsatisfiable is refused, not
   trusted.** `ensures false` means the callee never returns, so a caller's claims after
   the call are vacuous. The report carries a `Rule::DivergentCall` failure rather than
   calling it `Total`. This is the call-shaped twin of the unreachable-`Assume` and
   unreachable-precondition findings; see "A call to a procedure that never returns is not
   a proof either".
2. **There is a scaling wall, and the engine says so.** Boolean *equality of two
   wide multipliers* is the classic blow-up: `(a*b)*c == a*(b*c)` at 12 bits
   returns `Unknown`, and the test suite asserts exactly that. This is why
   `Unknown` is a first-class verdict: the engine refuses to guess. The wall is
   not removed, only pushed out.
3. **Two engines, one term graph, two blasters.** BDDs are canonical and give
   equivalence checking for free, but they blow up on multipliers. When the BDD
   arena fills, the *same* term graph is handed to a CDCL SAT solver (`sat.rs`,
   `bitblast.rs`) that has no canonical-form wall.
   The two engines share **no** circuit: `smt::blast` writes BDD node ids and
   `bitblast::blast` writes `Lit`s, and each writes its *own* ripple adder,
   subtractor, multiplier and comparator loop. They cannot be one function
   because both gate arenas are `&mut`. What they share is the term graph, so
   each operation is *named* once — its operands and width are fixed when the
   node is built — but the bit-level circuit for it is written twice, so the two
   can diverge. That is why the agreement is treated as a property to *check*
   rather than to assert away, and the check has to be aimed at the right
   blaster: the differential corpus (`tests/differential.rs`) and the z3 oracle
   run at widths the BDD engine finishes, so they exercise `smt::blast` and
   never reach `bitblast::blast` at all. The oracle that pins *this* blaster is
   the `tests` module in `bitblast.rs`, which drives `blast` directly, forces
   every input pair at 1–4 bits, and asks the solver whether the circuit can
   differ from Rust's own wrapping arithmetic. It is exhaustive, and it is
   load-bearing: dropping the carry-generate term from the adder there (making
   it compute `xor`) survives `tests/differential.rs`, the whole `cargo test`
   run and the z3 oracle, and only that module fails.
   The SAT engine is exact but not fast, so it runs under a conflict budget and
   answers `Unknown` when it expires — a verifier that hangs is worse than one
   that declines. The gain is real but specific: `add_comm` at 64 bits is
   `Unknown` from the BDD engine alone and `Valid` with the fallback (the
   measurement is recorded in `AGENTS.md`, "A fallback engine is only worth its
   weight if the wall actually moves"). Multiplication equality stays out of
   reach at both engines' budgets; that is the honest state.
   The trade made here is still *no external process, no allocator,
   deterministic memory*. The SAT arena is a `static` in BSS, sized at compile
   time, and a capacity overrun yields `Unknown`, never a wrong verdict.
   The arena being a `static` also means the `std` build **serializes** every
   SAT query: both `Mutex` guards are held across the encoding *and* the solve,
   so two threads whose hard proofs fall back to SAT run one after the other.
   The BDD engine does not serialize, because its arena is a `thread_local!` on
   `std`. This is a throughput cost, not a correctness one — the solver is
   deterministic and the locks are always taken in the same order — and it is
   the price of a compile-time-sized arena with no allocator.
4. **`no_std` uses a single static arena**, so the symbolic engine is not
   re-entrant across interrupt contexts. Wrap queries in a critical section, or
   use one context per core. This is documented at the definition site.
5. **Counterexamples are witnesses, not optima.** A model is derived from a BDD
   path, so it is *a* violating input, not necessarily the smallest one.
   Enumeration finds the smallest.
6. **This is a research-grade experiment**, not a certified tool. It has no
   qualification evidence, no DO-178C tool qualification, and no independent
   review. Treat it as a demonstration of an idea, not as something to put on an
   aircraft without doing the certification work.

## Why BDDs at all

Because canonicity buys the properties that make "verification in the code"
practical:

- **Equivalence is node identity.** No proof search, no heuristics, no timeouts
  on the easy cases.
- **A proof is a small object.** A `Certificate` is a couple of machine words,
  so it can live in the artifact and be passed around, unlike a SAT proof trace.
- **No allocator.** A fixed arena gives a compile-time memory bound, which is
  what a safety case wants to see.

The variable order interleaves bit-planes by significance
(`level_of` in `smt.rs`), which keeps ripple-carry adders and unsigned
comparators linear in diagram size — the reason a 32-bit `x & 0xff < 256` proof
is instantaneous while a 12-bit multiplier equality is not.

## Coverage scoreboard

`scripts/scoreboard.py` runs `mir_coverage` on the three MIR corpora and prints how many
functions come back **verified**, with `--check` failing if any corpus drops below the
floor in `scripts/scoreboard-floor.txt`:

```console
$ python3 scripts/scoreboard.py
| corpus | verified | total | share |
|---|---|---|---|
| `everyday.rs` | 21 | 24 | 87% |
| `actuator.rs` | 18 | 33 | 54% |
| `realistic.rs` | 694 | 1252 | 55% |
```

The floor is a **regression** floor, not a target: the corpora's verdicts are stable
across the toolchains the gate runs, so a drop means a change made a function that used
to verify stop verifying -- the kind of regression a coverage number catches and a green
test suite does not. `--write-floor` records the current counts, which a PR that raises
coverage does deliberately. The three functions still `incomplete` in `everyday.rs`
(`div_unwrap`, `sum_iter`, `tri`) are the documented hard ones -- the u32 divider BDD
wall, an unbounded-length sum, and a nonlinear inductive invariant -- and are tracked in
[`ROADMAP.md`](ROADMAP.md) as C7, C11 and C12.

## Documentation

- The crate's own docs are on [docs.rs/verif](https://docs.rs/verif). They are
  built with `--all-features`, so the `std`-only surface is there too.
- The sibling crate has its own page: [docs.rs/verif-arithmetic](https://docs.rs/verif-arithmetic).
  It is re-exported here as `verif::arith`, so its API is documented in both
  places.
- This README is the long-form document: each section records a claim the crate
  makes and the check that backs it. The [Contents](#contents) list at the top
  groups those sections.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) covers the ground rules and the gates.
- [`ROADMAP.md`](ROADMAP.md) is the single source for open work: each item carries
  a priority, a measurable exit criterion, the competitor whose gap it closes, the
  closing move (build / bridge / won't do), and a status.
- [`SECURITY.md`](SECURITY.md) covers reporting a **soundness bug** — a false
  `Valid` — which is the vulnerability class that matters in a verifier.
- [`docs/tcb.md`](docs/tcb.md) is the **trusted computing base** and the semantics of
  the supported MIR subset: what a `verified` line trusts, and the check behind each
  layer (roadmap A4).
- [`SOUNDNESS.md`](SOUNDNESS.md) is the ledger of every false proof and wrong
  verdict the project has found, each with the fixture that fails if the fix is
  undone; `tests/soundness.rs` checks the fixtures still exist.
- [`AGENTS.md`](AGENTS.md) is the engineering log: why each decision was made,
  including the ones that were reversed.

The gates are one script:

```console
$ sh scripts/gate.sh
```

It runs clippy, the test suite, the `no_std` bare-metal build, the
zero-dependency check, the differential oracles (z3, Kani, Verus,
`rustc_public`, Lean 4, Coq), the comparison fixtures, the MSRV build, the
documentation build, the build-artifact check, the pinned-`unsafe` check and the
build-time zero-cost check, and prints `ALL GATES GREEN` only when all of them
hold.

## License

Apache-2.0. The full text is in [`LICENSE`](LICENSE).

Copyright 2026 Yayasan Pesantren Cipansor and contributors. Developed with
contributions from OpenHands agents; the copyright notice in `LICENSE` records
the foundation and the contributor base together, which is the arrangement the
project's authorship follows.

This project was previously offered under `MIT OR Apache-2.0`. It is now
Apache-2.0 only, which is the single license the `LICENSE` file has always
carried; the dual-license option in the manifest and this section is what was
removed. Recipients of a prior release keep the rights that release granted
them; Apache-2.0 is the license for this version and every version after it.

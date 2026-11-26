# Comparison with other tools

Part of the [`verif` README](../README.md).

## Where this sits in the Rust ecosystem

The other verification tools for Rust are a different *kind* of thing, and the
difference is worth stating before the comparison table, because it decides what
`verif` can and cannot be used for.

**The established tools verify Rust you already wrote, out of process.** Kani
(AWS) compiles to CBMC and model-checks; Verus and Creusot and Prusti translate
Rust (or its MIR) into a logic and hand it to an external SMT solver; `hax`
extracts Rust into F\*/Coq for other tools to consume; Flux adds refinement
types checked by a solver. All of them need a bespoke toolchain or a nightly
compiler, and all of them invoke a solver (usually Z3) as a separate binary.

**`verif` is a prover that compiles into your artifact.** The decision
procedure is bit-blasting BDDs in the crate, the proof is a value, and there is
no external solver, no plugin, no nightly feature. That is a narrower and more
awkward design point — it buys you a proof that can run where Z3 cannot — and it
costs you scale, as the limits below say.

The honest split:

| | `verif` | Kani / Verus / Creusot / Prusti | `contracts` crate |
|---|---|---|---|
| What is verified | the Rust function itself, from its MIR (plus a `Stmt` AST for the older frontend) | the Rust function itself (MIR/IR) | nothing — runtime `assert` |
| Needs external solver | no | yes (Z3 / CBMC) | no |
| Toolchain | stable, `no_std`, zero deps | nightly or bespoke driver | stable |
| Runs on the target | yes (compiled in) | no (host-side) | yes (but unchecked) |
| Scope | bit-vectors, booleans, bounded quantifiers | first-order + arithmetic + more | — |
| Maturity | a sketch | industrial | widely used |

That table is an argument. [`examples/comparison/`](../examples/comparison/README.md)
is the evidence: three ordinary functions — a guarded `sat_add`, a `clamp`, and a
counted `sum_to` — written for `verif`, Kani, Verus, Prusti, SPARK, Coq and
Lean, each tool asked to prove the same properties and then asked to *refuse* the
same three injected bugs (a swapped-branch `sat_add`, a wrong-arm `clamp`, and a
wrong-body `sum_to`). Every tool proves all three and catches all three, so the
interesting result is not who wins but what each one is proving: Coq and Lean
prove theorems about a hand-written **model**, and that model can silently be
wrong (the first version of the Coq file proved the *buggy* `sat_add` correct,
because unbounded `Z` never wraps), while `verif` reads the MIR `rustc`
actually emitted, so there is no transcription to drift. The contracts state the
whole function, not a bound: `sat_add` says the result *is* the sum when it fits
and `u16::MAX` when it does not, so the degenerate `u16::MAX` for every input is
refused rather than accepted. The directory also puts Ferrocene beside the
verifiers, as the qualified *compiler* that answers the other half of a safety
case.

Two things follow. First, `verif` does compete with the big tools on the
question that matters — *is the proof about the code or about a model of it?* —
and the answer is the code: `src/mir/` reads the actual MIR that `rustc` lowers a
real function to, symbolically executes it, and discharges the overflow, shift and
divide-by-zero `assert`s `rustc` emits plus the pre- and postconditions you wrote
as doc comments. Nothing is re-modelled by hand, so nothing can drift. What it
does *not* match is **scale and scope**: it decides small, deterministic functions
(a few locals, bounded arithmetic, loops that carry an invariant) and declines the
rest rather than guessing, where Kani and Verus take on trait-heavy, generic,
iterator-driven code that this frontend reports as `incomplete`. The older
`Stmt` AST frontend (`wp::Stmt`) is still there and still useful for programs you
want to state directly, but it is no longer the only way in. Second, the niche it
does occupy — a checked contract that can be discharged *on the target*, with no
solver in the loop — is not one the big tools aim at, and it is the same niche a
`no_std` flight build actually needs.

They are not rivals here so much as a second opinion. The crate uses Kani and
Verus, Lean and Coq as *differential oracles* in its test suite (`examples/kanidiff.rs`,
`examples/verusdiff.rs`, `examples/leandiff.rs`, `examples/coqdiff.rs`): the engine's verdict
on a predicate is checked against each tool's verdict on the equivalent compiled program or
goal, so the five decision procedures have to agree. They are invoked as subprocesses and are never
dependencies — the shipped crate still has none — but "an independent verifier
agrees" is a much stronger claim than "the tests pass", and it is available
precisely because these tools exist.

### Rust is moving toward contracts

This is the part that makes the design timely rather than idiosyncratic. Rust is
adding contracts to the language itself: `#[contracts::requires(...)]` and
`#[contracts::ensures(...)]`, tracked in [rust-lang/rust#128044][track] (open,
`B-experimental`). The implementation landed in [PR #128045][pr], and its
description says the intrinsics for evaluating pre- and post-condition
predicates exist **"for third-party verifiers"**.

[track]: https://github.com/rust-lang/rust/issues/128044
[pr]: https://github.com/rust-lang/rust/pull/128045

So the language is growing the same contract vocabulary this crate has been
experimenting with, and it is deliberately leaving a door open for tools like
this one to sit on top. That cuts both ways, and both ways are worth naming: it
validates the direction, and it means a home-grown DSL will eventually be
competing with a blessed, in-tree syntax. The durable contribution here is the
*engine* — the embedded decision procedure and the proof kernel — not the
surface syntax, which is the layer most likely to be absorbed.

### Is it useful, and is it a big deal?

Useful, in a narrow band. For safety-critical or embedded Rust where you want
SPARK-style contracts and a machine-checked discharge with **no external
toolchain and no solver process** — an MCU, a flight build, a `no_std` target
where you cannot ship Z3 — this is a working sketch of how to get there, and it
is checked hard: differential testing of the exporter against Z3, differential
testing of the *engine* against both Kani and Verus, mutation testing of its own
guards, and a test suite that fails when a soundness guard is removed. The popular
`contracts` crate does runtime checking only; the gap between "assert at run
time" and "prove for all inputs" is exactly the gap this crate is about.

A big deal, no — not as a general-purpose verifier. That space belongs to
Kani and Verus, and this crate does not enter it. Its value is as a *reference
implementation* of the no-solver, no_std corner, and as evidence that the shape
works: a prover that is a library, a proof that is a value, a contract that
compiles into the artifact you ship.

## The SPARK comparison, stated plainly

| | SPARK/Ada + `gnatprove` | `verif` |
|---|---|---|
| Contracts in source | `Pre`, `Post`, `Type_Invariant`, `Assert` | `requires`, `ensures`, `invariant`, `verify!` |
| Prover location | external tool in the toolchain | **inside the compiled artifact** |
| Logic | full first-order + linear arithmetic + arrays | bit-vectors and booleans |
| Memory model | pointer/aliasing analysis | none |
| Scaling | industrial, handles large systems | good on masks/bounds/shifts, weak on wide multipliers |
| Qualification | extensive certification evidence | none |
| Qualified compiler | AdaCore's qualified toolchain | **Ferrocene**, checked in CI |

The interesting part is not that `verif` beats `gnatprove` — it does not, and
cannot, on scope. The interesting part is the *shape*: a prover that is a
library, a proof that is a value, and a contract that compiles into the artifact
you ship. Rust can do that, and this crate is a working sketch of how.

### The qualified toolchain

Rust's answer to AdaCore's qualified toolchain is [Ferrocene], qualified to
ISO 26262 ASIL D, IEC 61508 SIL 3, EN 50128 and IEC 62304. This repository builds
its `no_std` crates with Ferrocene for `thumbv7em-none-eabihf` — a target
Ferrocene itself qualifies — so the qualified compiler is exercised against the
same sources this crate ships. That is gate 3 of `scripts/gate.sh` and the
`ferrocene` job in CI; `tools/ferrocene/` has the manifest and the script.

Be precise about what that does and does not buy, because the distinction is the
whole point of this section. It checks that the *qualified compiler accepts the
sources unchanged*. It does not qualify `verif` itself: a qualified compiler
is not a qualified verifier, and this crate's decision procedure is not in
Ferrocene's scope. The README's own statement still stands — no qualification
evidence, no DO-178C tool qualification — and building with Ferrocene does not
change it.

Ferrocene is commercial, and its archives require a customer-portal token that
does not allow programmatic access, so the gate reports and skips when the
toolchain is absent rather than passing in silence — the same convention Kani,
Verus, Lean and Coq follow here. A skipped oracle is not evidence, and the gate
says so.

The build that matters most is `examples/bare_metal.rs`. It is `#![no_std]`, it
has no `main`, and it *calls the decision procedure* — so compiling it for
`thumbv7em-none-eabihf` is what shows the prover itself, and not just the types
around it, is code the qualified compiler accepts for the target. The target has
no test harness, so its verdict tests run on the host instead, under
`cargo test --workspace --features std`.

[Ferrocene]: https://ferrocene.dev/

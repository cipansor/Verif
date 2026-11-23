# Repository layout

Part of the [`verif` README](../README.md).

## Layout

```
.
├── Cargo.toml          the crate manifest (`no_std`, zero dependencies)
├── build.rs            bakes VERIF_ENGINE_HASH (hash of src/ + Cargo.toml) for the proof cache
├── Cargo.lock          committed: two packages (this crate and its sibling), and no
│                       external dependency at all
├── README.md           the crate's page on crates.io
├── ROADMAP.md          the open work: one item per gap, with exit criteria
├── SOUNDNESS.md        the ledger of every false proof fixed, with its fixture
├── AGENTS.md           notes for agents, including the traps that cost the most time
├── CONTRIBUTING.md     how to build, test, and add a gate
├── SECURITY.md         how to report a vulnerability (GitHub private advisories)
├── LICENSE             Apache-2.0
├── NOTICE              third-party attribution (oracles and comparisons only)
├── .github/
│   ├── FUNDING.yml
│   └── workflows/
│       ├── ci.yml      the gates, plus Kani, Verus, Lean, Coq, the MIR oracle,
│       │               the comparison fixtures, packaging hygiene and the
│       │               publish dry-run as jobs
│       └── release.yml tag-driven release: one crate per tag, in dependency order
├── src/
│   ├── lib.rs          crate root: module map, prelude, the three proof routes
│   ├── smt.rs          the decision procedure (the heart of the crate)
│   ├── bitblast.rs     bit-level term graph -> CNF, for the SAT fallback
│   ├── sat.rs          CDCL SAT solver: the fallback when the BDD arena fills
│   ├── sym.rs          symbolic DSL via operator overloading
│   ├── logic.rs        verified arithmetic + Q16.16 fixed point
│   ├── proof.rs        Curry–Howard kernel + certificates
│   ├── vc.rs           requires/ensures/invariant, Verified<T>
│   ├── contract.rs     runtime predicate checking
│   ├── exhaustive.rs   complete proofs by enumeration
│   ├── primitives.rs   total ops, Bounded<MIN,MAX>
│   ├── macros.rs       verify!, contract!, proof!, ...
│   ├── wp.rs           Hoare logic + automatic VC generation
│   │                   (also carries Proc + Stmt::Call for modular verification)
│   ├── smtscript.rs    SMT-LIB2 export for independent checking
│   ├── mem.rs          bounded symbolic memory + frame condition
│   ├── quant.rs        bounded forall/exists, expanded to finite form
│   ├── bin/            the `cargo verif` and `verif-wrap` drivers
│   └── mir/            the real-Rust frontend (`std` only)
│       ├── parse.rs    rustc's textual MIR -> a small IR, failing closed
│       ├── exec.rs     symbolic execution of that IR, with a frame stack for calls
│       ├── intrinsics.rs  the `core` model: `checked_*`/`saturating_*`/`wrapping_*`,
│       │                  the bit counts, `Range`/`Iterator::next`, `?`, ...
│       ├── shape.rs    per-function summary the rustc_public oracle compares
│       ├── cache.rs    the proof cache: decided verdicts keyed on MIR+contracts+edition+engine
│       ├── spec.rs     contract scanner + the small contract-expression grammar
│       └── verify.rs   driver: emit MIR, extract contracts, discharge, report
├── verif-arithmetic/   the sibling crate, re-exported as `verif::arith` (its own
│   │                   `LICENSE`/`README`/`NOTICE`, because a `.crate` needs them)
│   ├── src/
│   │   ├── lib.rs      the module map and the `no_std`/no-`unsafe` claim
│   │   ├── checked.rs  checked/saturating/wrapping integer ops, proved by enumeration
│   │   ├── bounded.rs  `Bounded<MIN, MAX>`, a refinement type whose invariant holds
│   │   ├── fixed.rs    Q16.16 fixed point, with its truncate-toward-zero contract
│   │   └── prove.rs    the enumeration prover (`ENUM_BUDGET`) the proofs run under
│   └── tests/
│       ├── proofs.rs   the proofs, executed
│       └── readme.rs   the sibling README's example, pinned
├── tests/
│   ├── smoke.rs        the engine proves real identities
│   ├── kernel.rs       the proof kernel, including a compile-fail case
│   ├── sym.rs          the DSL operators, each against the primitive it wraps
│   ├── differential.rs symbolic prover vs brute-force execution
│   ├── sat_engine.rs   the SAT solver vs brute force on raw CNFs
│   ├── wp.rs           generated conditions checked against execution
│   ├── mem.rs          memory proofs checked against real Rust arrays
│   ├── quant.rs        fill and scan loops, both verified and executed
│   ├── call.rs         modular verification, every positive with its control
│   ├── loopdiff.rs     verifier vs exhaustive execution, loops and claims included
│   ├── modular_differential.rs  generated callers, verified then executed
│   ├── divmod.rs       the divider the MIR frontend needs, vs Rust's own `/` and `%`
│   ├── mul.rs          the constant-multiply arm, through `prove` not `evaluate`
│   ├── shift.rs        the barrel shifter, vs Rust's own `<<` and `>>`
│   ├── signed.rs       signed arithmetic: `slt`, `sdiv`, sign-extend, overflow
│   ├── op_differential.rs  `evaluate` vs `blast`, per operator, both operand shapes
│   ├── oracle.rs       the reference oracle (enumeration), checked before it is used
│   ├── bang_literal_signedness.rs  `!x` in a contract: value vs predicate reading
│   ├── mir.rs          real-Rust verification, with counterexamples replayed
│   │                   against the compiled functions
│   ├── readme.rs       the README's examples, pinned so they cannot rot
│   ├── cargo_verif.rs  the `cargo verif` binary, run end to end
│   └── soundness.rs    every fixture the SOUNDNESS.md ledger names must exist
├── examples/
│   ├── flight_control.rs  a realistic actuator path, all obligations discharged
│   ├── pipeline.rs        program -> conditions -> proofs -> SMT-LIB2
│   ├── memory.rs          read/store, the frame condition, and a fill loop
│   ├── contracts.rs       procedures verified once, calls reasoned about by contract
│   ├── report_probe.rs    a report's verdict must not depend on the arena it is read in
│   ├── z3diff.rs          differential harness: engine vs z3 on the exported text
│   │                      (needs z3-solver; a development tool, not a dependency)
│   ├── kanidiff.rs        differential harness: engine vs Kani on compiled Rust
│   │                      (needs `cargo kani`; a development tool, not a dependency)
│   ├── verusdiff.rs       differential harness: engine vs Verus on a spec fn
│   │                      (needs the Verus driver; a development tool, not a dependency)
│   ├── leandiff.rs        differential harness: engine vs Lean 4's `bv_decide`
│   │                      (needs Lean via elan; a development tool, not a dependency)
│   ├── coqdiff.rs         differential harness: engine vs Coq's kernel, by enumeration
│   │                      (needs `coqc`; a development tool, not a dependency)
│   ├── bare_metal.rs      the prover as `#![no_std]` code, built for the target by
│   │                      Ferrocene, the qualified toolchain (a `lib` example, no `main`)
│   ├── support/           the IR the engine harnesses share, so they check the
│   │                      same formulas rather than two drifting corpora
│   ├── mir_demo.rs        verifies real Rust read from MIR, end to end
│   ├── mir_coverage.rs    the coverage scoreboard: how much real Rust is decided
│   │                      (the number `ROADMAP.md` scores its corpora with)
│   ├── comparison_check.rs  gate 13's driver: asserts each comparison fixture's
│   │                      per-function outcome and obligation kind, not a count
│   ├── comparison/        the same three functions proved seven ways, plus
│   │                      Ferrocene as the qualified compiler (see its README)
│   └── mir_targets/
│       ├── actuator.rs    the Rust under verification; imports no `verif`
│       ├── realistic.rs   the large regression corpus (adversarial fixtures included)
│       └── everyday.rs    the independent corpus: ordinary Rust, not shaped for
│                          the tool; Phase 1 in `ROADMAP.md` is scored on it
├── tools/
│   ├── mir-oracle/     the `rustc_public` oracle: checks the text-MIR frontend
│   │                   against rustc's own typed MIR. Nightly + `rustc-dev`,
│   │                   its own workspace, and never a dependency of `verif`.
│   ├── comparison/     gate 13: re-runs the comparison fixtures -- the contracts,
│   │                   the teeth, and the degenerate-implementation check
│   ├── ferrocene/      gate 3: builds both crates with the qualified compiler for
│   │                   `thumbv7em-none-eabihf` (skipped, reported, if absent)
│   ├── build-verify/   gate 18: the Kani/Verus shape -- verify from `build.rs`
│   │                   and prove the artifact carries no prover (scratch crate)
│   ├── cost-bench/     the cross-tool cost table in "How the cost compares to
│   │                   other verifiers": `run.sh` measures `verif`, Kani, Verus,
│   │                   Coq and Lean on the same three functions (setup + per-
│   │                   verification; the artifact axis is `shape-bench/`)
│   ├── shape-bench/    the measured table in "Two ways to use the verifier":
│                       `run.sh` builds four crates (build-time vs on-target
│                       vs unused) on scratch copies, and `measurer.rs` is the
│                       native launcher that reads each process's own `VmHWM`
│                       rather than a `fork` harness's inflated `ru_maxrss`
│   └── external-demo/  C8: verifies a `no_std` crate that depends on
│                       `embedded-hal` end to end with `cargo verif` (a scratch
│                       crate; exit 2, reported, when there is no network)
└── scripts/
    ├── gate.sh              every gate in one command, failing loudly
    ├── test-count.sh        the exact passing-test count, only when all pass
    ├── check_package.sh     packaging hygiene: manifests, LICENSE/README/NOTICE
    ├── check_doc_links.py   every internal anchor and relative file link resolves
    ├── check_actions_pinned.py  every GitHub Action `uses:` is pinned to a SHA
    └── publish.py           publish order, dry-run, tag/checkout checks, notes
```

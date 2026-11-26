# Testing and the gates

Part of the [`verif` README](../README.md).

## Building and testing

```console
# Everything, in one command that fails loudly on the first gate that does not hold
scripts/gate.sh

# Host, with the thread-local arena and the full test suite.
# The `--features std` is required: the default feature set is empty (`no_std`),
# and the tests need the thread-local arena, so a plain `cargo test` does not
# compile the test harness.
cargo test --features std

# Lint both halves -- `--features std` alone never compiles the `no_std` items
cargo clippy --features std --all-targets
cargo clippy --no-default-features --lib

# Bare metal: no std, no allocator, no dependencies
rustup target add thumbv7em-none-eabihf
cargo build --no-default-features --target thumbv7em-none-eabihf
```

`scripts/gate.sh` runs clippy (with `-D warnings`, over both the `std` and the `no_std` half
of the crate), the test suite, the bare-metal
`no_std` build, a zero-dependency check, and the z3 differential oracle. It exists because
the gates were previously five separate commands quoted in prose, which is how a gate
quietly stops being run. It also refuses to report success when the z3 oracle is not
installed: an oracle that did not run is not evidence about the exporter. Five further gates
run the Kani, Verus, Lean and Coq differential oracles and the `rustc_public` MIR oracle when those
tools are present and *skip them loudly* when they are not, because all three are large
downloads (Kani: a pinned nightly plus CBMC; Verus: a self-contained bundle with its own z3;
the MIR oracle: a nightly with the `rustc-dev` and `llvm-tools-preview` components) that a normal local run should not
pay for; CI installs them and runs them as hard gates. One more gate holds the comparison
fixtures themselves — `tools/comparison/run.sh` re-runs `verif` on the positive fixture
and all three bug fixtures through `examples/comparison_check.rs`, which asserts each
fixture's per-function `FnOutcome` and the *expected obligation kind* rather than scraping
`mir_coverage`'s `decided N of M` line (that line counts only `Verified`, so a `Failed`,
`Incomplete` or `Skipped` fixture all read `decided 0 of 1`, and a contract that had become
unreadable would have been reported as a caught defect — a lost proof read as a refutation);
the positive fixture's three names are pinned in the driver rather than read back from the
contracts, and so is each function's whole contract (`requires:`, `ensures:`, `invariant:`)
clause for clause — a name survives a deleted contract and a count survives a weakened one, so
neither alone holds the claim; the
expected obligation kind is compared for equality, not by a `panic` prefix that any panic would
satisfy; and each scratch fixture gets a path unique per call, so two concurrent gates cannot
delete each other's file;
the same gate checks that the contracts refuse the degenerate implementations the bounds-only
versions accepted, and runs Coq and Lean on the positive fixture and both teeth, including
the mutation that shows each rejection is of the defect rather than of the script's shape.
Coq and Lean are both *required*: an absent prover is a reported skip (exit 2), never a
success for a proof suite that did not run. The last four gates hold the *tree*
rather than the logic: rustdoc must build both crates with `-D warnings` (the crate is
`#![deny(missing_docs)]`, but that says nothing about whether a doc link still *resolves*),
no compiled output may be tracked (`git ls-files` must not list a `.rlib` or a `target/`
path — a `git add -A` re-committed six stray `.rlib`s once, and a `.gitignore` does not
untrack a file that is already in the index), the `unsafe` surface must stay at the two
blocks `SECURITY.md` names, each with a `// SAFETY:` justification (a count in prose is a
claim like any other, and this one is security-relevant), and the build-time path must
verify at compile time while leaving the prover out of the artifact (see
[Two ways to use the verifier](build-time.md#two-ways-to-use-the-verifier-at-build-time-or-on-the-target) below).

### The third oracle: rustc's own MIR, against the parser

`z3diff` checks the exporter and `kanidiff`/`verusdiff` check the engine. The MIR frontend
has a third failure mode, and it is the one gap 2 below names: it reads rustc's *textual*
`--emit=mir` dump, so a rustc release that changes the pretty-printer can break the parser,
and the parser is the only thing that would notice. `tools/mir-oracle` closes part of that
loop. It asks `rustc_public` — the compiler's own public API, which needs a nightly with the
`rustc-dev` and `llvm-tools-preview` components — for the same programs' **typed** MIR, reduces each function to a
small comparable shape (how many basic blocks it lowered to, and which panic guards `rustc`
inserted and with what polarity, in block order), and fails if that disagrees with what the
frontend's parser read out of the text. The comparison is structural on purpose: the two
dumps are not byte-identical (the typed one omits `copy` qualifiers and nests `scope`
blocks), and comparing text would fail on cosmetics and prove nothing.

**What that shape can and cannot see is the honest limit of this gate**, and it is pinned in
both directions by `the_shape_sees_structure_and_guards_but_not_places` in
`src/mir/shape.rs`. It sees a change in *structure*: an extra basic block, a guard that moved
or was inserted, a guard whose polarity flipped. It does not see a change in *spelling*: a
place, a local index, a field projection, a type. Re-spelling `Len((*_1))` as
`PtrMetadata(copy _1)` — a real change in rustc 1.99 that cost four verdicts on the 1.85
floor — leaves the shape byte-identical, so gate 10 was silent across it; it was found by
running the suite under a second toolchain.

**Gate 14 is a sample of that coverage, not the whole of it.** It runs `tests/mir.rs` under
one older compiler (1.85) against the same suite on the current stable, and it *skipped
entirely* in a container without the 1.85 toolchain — reported, not passed, but a skip. Two
compilers catch a spelling change only where they differ; a printer change that lands in a
version *between* them, or after current stable, is not covered by either. The durable form of
the check is therefore a habit, not a gate: run the suite under a compiler you have not run
before when the toolchain moves. Measured for this paragraph, `tests/mir.rs` is 354/354 on
1.85.1, 1.100.0 and 1.102.0-nightly, and the two end spellings really do differ
(`Len((*_1))` on 1.85, `PtrMetadata(copy _1)` on stable). So gate 10 is evidence about the
parser's *reading of the control-flow skeleton*; gate 14 extends that evidence to one more
compiler's spellings; nothing here covers every token on every toolchain.

The oracle lives in
`tools/mir-oracle`, outside the workspace, so the nightly and the `rustc_private` feature
never touch a crate that must build on stable with zero dependencies; the dependency arrow
points one way, from the oracle to `verif`. Gate 10 of `scripts/gate.sh` runs it, and the
`mir-oracle` CI job makes it a hard gate.

### Four more oracles, for the engine instead of the exporter

`z3diff` checks the *exporter*: it prints a query and asks z3 to agree about that text.
`examples/kanidiff.rs`, `examples/verusdiff.rs`, `examples/leandiff.rs` and
`examples/coqdiff.rs` check the *engine*. Each takes predicates the engine proved, compiles
them into a real program or goal, and asks an independent verifier to establish the same
property:

* `kanidiff` compiles each case into a Rust function and asks **Kani** (AWS's model checker,
  over CBMC) to verify it.
* `verusdiff` compiles each case into a Verus `spec fn` and asks **Verus** (Viper plus SMT,
  with bit-vector reasoning) to verify it.
* `leandiff` compiles each case into a Lean 4 theorem and asks **`bv_decide`** to prove it.
  This is the strongest of the four, and for a structural reason: `bv_decide` bit-blasts the
  goal, runs a SAT solver, and then *replays the solver's refutation as a Lean proof term that
  the kernel type-checks*. The verdict is not "a solver said so", it is a machine-checked
  theorem about the same 8-bit words this crate blasts.
* `coqdiff` asks **Coq's kernel** to check a different thing from the other three: not "does
  the engine decide this formula the same way" but "does the engine's arithmetic, transcribed
  into `Z` with explicit masks, evaluate to the same truth value on every point of the 8-bit
  domain". Coq has no machine word in its standard library, so the generator spells every
  operator out over `Z` and the harness enumerates the domain with `vm_compute`. That makes it
  the only oracle that checks the *transcription* rather than the verdict, and it is the
  slowest by a wide margin (three variables is 16.7M evaluations), so it runs a selected
  subset of the corpus — see `SELECTED` in `examples/coqdiff.rs`.

No backend ever sees a symbolic term or an SMT-LIB string, and the four are built on
different foundations, so agreement is agreement between five independently built decision
procedures. A blasting bug now has to survive agreement with all four, which is a much
narrower coincidence than surviving one.

The design detail that matters is that the predicate and the generated program are *not*
produced independently. They are interpretations of one shared IR tree (`WExpr`/`PExpr`, in
`examples/support/mod.rs`), so "the same property" is structural rather than hoped for; and
the two harnesses share that module, so they are checking the same formulas rather than two
corpora that drift apart. Generating predicate and program separately would compare unrelated
formulas and every disagreement would be noise.

The harnesses have been checked for teeth by mutation, which is the only way to know they ask
a real question. Dropping the `+1` from the `Sub` blast (`borrow = TRUE` → `FALSE`) makes the
engine reject three true identities (`sub_self`, `add_sub_cancel`, `sub_zero`); changing the
`Eq` blast from `and` to `or` over the per-bit equalities makes it prove false ones. The
first of those is caught by `kanidiff` and `verusdiff`; the second by both as `MISMATCH
rand_N` on the random sweep. `leandiff` and `coqdiff` were checked against a mutation of
their own — the `Sub` blast wired to `Op::Add` instead, a blasting bug the engine then
*blesses* rather than rejects — and both catch it: the negative control flips from refuted to
proved (`control_ok=false`), and each reports `refuted_identity=2` plus three `MISMATCH`
lines naming `sub_self`, `add_sub_cancel` and the control. So every harness here has been
observed to fail on a broken engine, which is the only evidence that a green run means
anything.

Each harness also carries a negative control — `a - b == b - a`, false by construction — and
fails if either side *proves* it, so a run where "everything agreed" because nothing was
really asked cannot pass.

Eight divergences surfaced while building these, and all are worth stating because they are
where a plausible harness would have quietly lied:

1. **Arena sharing.** One engine arena for all cases exhausted the node budget after about a
   dozen queries, so later cases came back `Unknown` and the harness reported the engine as
   weak when the *harness* had run the arena dry. Each case now gets its own arena.
2. **Shift semantics.** The engine defines a shift by `k >= width` to be 0 (or the sign bit),
   the SMT-LIB rule, while Rust's `<<`/`>>` are an overflow error there. Emitting `x << k`
   would have compared a different function, so the generated programs spell the engine's rule
   out in `shl_eng`/`lshr_eng`/`ashr_eng`.
3. **The classification matrix.** The first version counted "engine refuted + backend proved"
   as agreement. A mutated engine then produced `mismatch=0` and was caught only by the
   curated corpus. Now only the engine's `Unknown` is "no claim"; every other engine verdict
   is a definite claim the backend must not contradict.
4. **Verus's arithmetic and its summary counts.** `#[verifier(bit_vector)]` rejects
   `wrapping_mul` when an operand is a literal, and a constant like `255u8 * 255u8` is a
   rustc const-eval overflow error that aborts the whole run, so the generated file routes
   arithmetic through spec helpers that wrap via `as u8`. And Verus's
   `verification results:: N verified, M errors` counts non-case items such as `main`, so the
   accounting check is on error *locations*, not on that sum.
5. **Lean's `setWidth` changes the type.** `setWidth 4` on a `BitVec 8` returns a `BitVec 4`,
   and `==` is homogeneous, so a bare truncation cannot be compared against a `BitVec 8` at
   all. The first `lean_word` emitted exactly that and every masked case came back as a
   `Type mismatch` rather than a verdict — a harness bug that would have read as "the engine
   and Lean disagree about masking" if the harness had counted non-verdicts as disagreement.
   Widening back with `.setWidth 8` is the engine's `truncate`-then-widen `Mask`.
6. **Lean diagnostics are multi-line, and the line number is the second-to-last field.**
   `bv_decide` and `native_decide` report a refutation in two different wordings
   ("The prover found a counterexample" vs "the proposition … is false"), and the second
   only appears on a continuation line — so the classifier has to collect the whole
   diagnostic block before it can judge it. Reading the first line alone called every
   `native_decide` refutation "hard", i.e. unverifiable. The line number itself is the field
   *before* the column, not the last one; taking the last one attributed every verdict to the
   wrong case and produced 47 spurious mismatches against a correct engine.
7. **`first | bv_decide | decide` does not work, and the failure is silent.** `first` commits
   to the first tactic that produces a proof *or an error*, and `bv_decide` reporting a
   counterexample counts as an error — so `decide` then runs on every refuted goal, including
   the wide arithmetic ones, where it exceeds the heartbeat limit. The case is then reported
   as undecidable rather than refuted, which is a *lost* verdict rather than a wrong one, but
   it makes the oracle look weaker than it is. `native_decide` compiles the decision instead
   of reducing in the kernel and finishes those in under a second. The trade is real and
   stated in the harness: `native_decide` is Lean's trusted-native escape hatch, so the
   fallback verdicts are trusted rather than kernel-checked, which is why `bv_decide` is tried
   first and applies to all but the out-of-fragment handful.
8. **Coq applies by juxtaposition, not by comma.** `add_eng(a, b)` is a type error —
   `add_eng` has type `Z -> Z -> Z` but is applied to a single argument — and every case
   failed to compile until the generator emitted `add_eng a b`. The harness refused to read
   the failed compile as a set of verdicts, which is the behaviour that made it visible.

Two corpus entries were also wrong — a bare `Not(And(..))` is not De Morgan, and
`guard <=> ite(guard,a,b)==a` fails at `a==b` — and the engine correctly refuted both. The
lesson that keeps recurring: when a harness disagrees, suspect the harness first, but *check*.

The engine's `Unknown` on `mul_comm` (an 8×8 multiplier) is the documented size wall, not a
disagreement: both backends prove the identity, so the engine is incomplete there, which the
harnesses count separately (`undecided_identity=1`) and do not fail on. A *refuted* identity
is a soundness failure and does fail the run. Note that the SAT fallback also tries this
identity and also declines it, which is the intended outcome: the fallback moves the wall, it
does not remove it, and an incomplete-but-honest answer is what keeps the differential
harness meaningful.

The `differential` test is the one that makes the approach trustworthy: for a
family of predicates it checks that the symbolic prover and brute-force
execution give the *same* answer, and that any symbolic counterexample really
does violate the property.

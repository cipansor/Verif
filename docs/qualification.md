# A qualification path (A5)

> **Draft.** `verif` is not qualified by any authority, and nothing in this document
> certifies it. It records the plan a qualification effort would follow, the
> requirements the tool would have to meet, and — for each — the check in this
> repository that already demonstrates it. The missing half is a *qualification kit*:
> the reviewed artifacts a certification body signs off. That is a human/process
> deliverable, not a code one, and this document is the starting point for it, not the
> result.

## Why a verifier is a tool that must itself be qualified

DO-330 (airborne) and ISO 26262-8 (automotive) treat a *verification* tool as one whose
**output is evidence**. A `verif` `verified` line is a claim about the program; if the
tool is wrong, the claim is wrong, and the failure is silent — a *false proof*, which is
the one outcome this crate exists to prevent. So the tool has to be trusted at the level
of the risk it removes.

DO-330 assigns a Tool Qualification Level (TQL-1 the strictest … TQL-5 the least) by how
much the tool's output can *mask* a failure:

- **TQL-5**: the tool's output is reviewed and can be independently checked. This is the
  *least* level, and it is not "no objectives": a TQL-5 tool still carries DO-330 tool
  *validation* objectives (requirements, a validation plan, evidence) — independent
  checking of the output is what makes TQL-5 the appropriate level, not what removes the
  objectives.
- **TQL-1..4**: the tool's output is relied on without review, so the tool must be
  qualified with requirements, design, verification, and so on.

`verif`'s realistic target is **TQL-5 with tool validation by differential testing**:
every verdict it produces can be re-checked by an independent oracle (a solver, a
model checker, a proof assistant, or `rustc` itself), and the repository already runs
those oracles as gates. Qualifying the *decision procedure* to TQL-2 — a formal
correctness argument for the BDD engine and the CDCL solver, reviewed by an assessor —
is a research programme, not a task in this repository, and this plan does not pretend
otherwise.

## Tool Operational Requirements (TOR)

Each requirement is a claim the tool must keep, and the column on the right is the check
in this repository that *already* demonstrates it — a gate, a differential oracle, or a
regression test. A TOR whose evidence column were empty would be an aspiration; the point
of listing the check is to make it a measurement.

| TOR | Requirement | Evidence |
|---|---|---|
| **TOR-1** | **Soundness.** Never report `verified` for a program with a violating run. | `SOUNDNESS.md` + `tests/soundness.rs`; the differential harnesses (`tests/modular_differential.rs`, `tests/op_differential.rs`, `tests/differential.rs`); the corpus sweep `no_cannot_prove_entry_is_ever_verified`; the four oracles (z3, Kani, Verus, `rustc_public`). |
| **TOR-2** | **Refusal over guessing.** An unmodelled construct is `incomplete` or `skipped`, never a verdict. | `Verdict::Unknown` as first-class; the refusal tests (e.g. `mir::parse::tests::no_input_panics_the_reader`, the intrinsic `is_modelled` refusals); the scoreboard's `decided N of M`. |
| **TOR-3** | **Determinism.** The same source and contracts yield the same verdict. | the parser determinism assertion in `no_input_panics_the_reader`; the scoreboard floor (`scripts/scoreboard-floor.txt`), which fails if a verdict moves. |
| **TOR-4** | **Bounded resources.** Never hang or crash; refuse on a budget. | the budget regression tests: `a_deep_term_walk_is_refused_not_allowed_to_overflow_the_stack`, `a_wide_constant_divisor_returns_a_verdict_instead_of_hanging`, `a_branching_loop_reports_a_path_budget_rather_than_running_forever`, `a_symbolic_pow_returns_a_verdict_instead_of_hanging`. |
| **TOR-5** | **No silent drops.** A contracted function absent from the report is `missing`, never passed. | `assert_not_dropped` (strict `verify_src`); `Specs::resolve` refusing an ambiguous suffix; the `missing` list in `FileReport`. |
| **TOR-6** | **Toolchain honesty.** The frontend reads `rustc`'s MIR; a printer change must be caught, not silently mis-parsed. | gate 9 (the `rustc_public` oracle), gate 14 (the MSRV run), and the two-toolchain `tests/mir.rs`. |
| **TOR-7** | **Reproducibility.** A proof's formula can be exported for an independent check. | `smtscript` (SMT-LIB2) + `examples/z3diff.rs`; the Coq/Lean/Kani/Verus comparison in `examples/comparison/`. |

The TCB these claims rest on — which component each trusts and the check behind it — is
written down in [`docs/tcb.md`](tcb.md). The ledger of every defect that broke a TOR, with
the fixture that would fail if the fix were reverted, is [`SOUNDNESS.md`](../SOUNDNESS.md).

## The qualification plan (DO-330 TQL-5 / ISO 26262 TCL3)

A qualification effort for `verif` would produce the following artifacts. The status
column is honest about what exists today.

| Activity (DO-330 §) | What it means here | Status |
|---|---|---|
| Tool requirements | the TOR table above | **drafted** (this document) |
| Tool design | the module map (`docs/internals.md`), the TCB (`docs/tcb.md`) | **drafted** |
| Tool verification | the differential oracles and the 18-gate `scripts/gate.sh` | **exists** |
| Configuration management | git, the SHA-pinned CI actions, `.github/workflows/release.yml` | **exists** |
| Problem reporting | `SECURITY.md` (soundness bugs are the vulnerability class) and `SOUNDNESS.md` | **exists** |
| Tool accomplishment summary | a report mapping each TOR to its evidence, signed off | **missing** |
| Independent assessment | a reviewer outside the project checks the TOR and the evidence | **missing** |
| Qualification kit | the reviewed, versioned artifacts a body signs | **missing** |

So the *technical* half — requirements backed by checks, a documented design, a defect
ledger, reproducible oracles — is in place. The *process* half — an independent
assessment and a signed tool accomplishment summary — is not, and cannot be produced by a
commit.

## What this buys, and what it does not

- **Ferrocene qualifies the compiler, not the verifier.** Gate 3 builds both crates with
  the TÜV SÜD-qualified toolchain for `thumbv7em-none-eabihf`, so the *sources* compile on
  a qualified compiler. `verif`'s decision procedure is outside Ferrocene's qualification
  scope; a qualified compiler is not a qualified verifier, and the README's "no
  qualification evidence" line stays true after that gate runs.
- **A TQL-5 plan plus the differential evidence is a credible starting point**, not a
  certificate. The gap to a real qualification is the independent assessment and the
  signed summary, both human actions.
- **The plan is versioned with the code.** If a gate named in the TOR table is removed or
  renamed, the claim behind its TOR weakens; the `docs/layout.md` and `SOUNDNESS.md`
  checks are what keep those references honest.

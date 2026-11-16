# Soundness ledger

A verifier's worst failure is a **false proof**: a `verified` verdict for a
program that does not satisfy its contract. It is worse than a crash, because a
crash reports nothing while a false proof is *trusted*. This file is the honest
record of every false proof this project has found and fixed, so that the rate is
a number rather than an impression.

It is the A1 item of [`ROADMAP.md`](ROADMAP.md): track the false-proof rate, and
pause feature work on any layer that produced one in the last two weeks.

## How to read a row

Each row is one defect that produced a **wrong verdict**. The classes are:

- **false proof** — a false contract reported `Verified`. The severe one.
- **false refutation** — a true contract reported `Failed`. Milder: it loses
  trust in the tool, not in the proof.
- **lost proof** — a function that should have been checked was refused or
  silently dropped (a dropped contract reports `Verified { obligations: 0 }`, so
  a drop is a false proof by another name — see the row that says so).
- **wrong verdict** — a definite answer (either way) read off a program that
  `rustc` rejects, or off the wrong value.

Every row names a **fixture**: a test that fails if the fix is undone. A row
without a fixture would be a claim, not evidence. The fixtures live in
`tests/mir.rs` unless the row says otherwise; the `src/mir/spec.rs` unit tests
are noted where the guard runs without a `rustc`.

## The MIR frontend

The frontend reads `rustc`'s textual MIR and turns contracts into queries. These
are the defects where it produced a wrong verdict.

| # | Symptom | Class | Fixture | Fixed |
|---|---|---|---|---|
| 1 | `0xFF` read as decimal `0`, so `requires: x == 0xFF` meant `x == 0` and a false postcondition was proved | false proof | `a_radix_literal_is_read_at_its_radix` | 2026-11-13 |
| 2 | `128` accepted for an `i8` (it fits eight *unsigned* bits), read as `-128`, so `x <= 128` admitted nothing | false proof | `an_out_of_range_literal_is_refused_not_wrapped` | 2026-11-13 |
| 3 | `200u8 + 100u8` folded mod width to `44`, so `x <= 200 + 100` *narrowed* the precondition and a false postcondition held | false proof | `an_overflowing_constant_expression_is_refused_not_wrapped` (spec unit test) | 2026-11-13 |
| 4 | A left-hand constant's signedness was dropped, so `0 < a` for an `i8` compared unsigned and `i8::MIN` read as the *largest* value | false proof | `a_constant_left_signed_compare_is_signed_not_unsigned` | 2026-11-13 |
| 5 | `-1i8 as i16` zero-filled to `255`, so `a as i16 == 255` was proved for a signed source | false proof | `a_widening_cast_respects_the_sources_signedness` | 2026-11-13 |
| 6 | A signed slice element was read as unsigned in a *contract*, so `xs[0] >= 0` over `&[i8]` was a tautology | false proof | `a_signed_element_is_read_as_signed_in_the_contract` | 2026-11-13 |
| 7 | A typed constant mask (`-1i8 & 1`, `1u8 & 1`) was marked untyped, so a pairing `rustc` rejects was decided | wrong verdict | `a_typed_constant_mask_keeps_its_type` | 2026-11-13 |
| 8 | A fixed-width constant (`1i8`) was resized to a partner of another width (`x as i16`), deciding an `E0308` program | wrong verdict | `a_fixed_width_constant_may_not_meet_a_partner_of_another_width` | 2026-11-13 |
| 9 | An untyped fold that overflows its operand width (`(!0 + 1) < 1u8`) was decided instead of refused | wrong verdict | `an_untyped_fold_that_overflows_the_operand_width_is_refused` (spec unit test) | 2026-11-13 |
| 10 | A function-local `const` was keyed by its bare name, so it was in scope in *every* function's contract | false proof | `a_local_const_is_not_in_scope_in_another_function` | 2026-11-13 |
| 11 | A contract on an inherent method was keyed by its bare name and dropped; a dropped contract is `Verified { obligations: 0 }` | false proof | `a_contract_on_an_inherent_method_is_resolved_and_checked` | 2026-11-13 |
| 12 | A branching `const` (`if false { 7 } else { 8 }`) folded to its first arm, so `K == 7` was proved while `K` is `8` | false proof | `a_branching_const_does_not_fold_to_its_first_arm` | 2026-11-13 |
| 13 | A local trait method sharing an intrinsic's name was answered by the intrinsic model, so a body that disagrees with `core` proved `core`'s value | false proof | `a_trait_method_sharing_an_intrinsic_name_is_answered_by_its_body` | 2026-11-13 |
| 14 | A field write through a `&mut` (`(*_1).0 = v`) was dropped, so a postcondition was checked against the stale seed | false proof | `a_field_write_through_a_mutable_reference_is_applied` | 2026-11-12 |
| 15 | Two same-named structs in different modules collided in the layout table, so drop glue read the wrong layout | false proof | `two_same_named_structs_do_not_share_a_layout` | 2026-11-16 |
| 16 | A diverging call in its cleanup form (`-> bbN` with a live `Drop` local) was dropped, so a reachable panic was never checked | false proof | `a_diverging_call_in_a_function_with_a_drop_local_is_checked` | 2026-11-13 |
| 17 | Drop glue of a struct whose field has its own destructor ran only the outer one, hiding a panicking field destructor | false proof | `a_destructor_body_is_executed_and_its_panic_is_an_obligation` | 2026-11-15 |
| 18 | The `unwind:` bound counted *block entries*, so a two-iteration loop verified under `unwind: 1` | false proof | `the_unwind_bound_counts_the_whole_loop_not_one_latch` | 2026-11-16 |
| 19 | `RangeInclusive::next` tested the *unsigned* successor-overflow flag, so a signed inclusive range never terminated and a true contract became a bound failure | false refutation | `a_signed_inclusive_range_stops_at_its_boundary` | 2026-11-16 |
| 20 | `next` advanced an empty range, so a second `next` returned an element Rust never yields | wrong verdict | `an_empty_inclusive_range_stays_empty` | 2026-11-16 |
| 21 | The edition was pinned to 2024, so valid 2021 code (`extern "C"`) was refused, and code that lowers differently was verified under an edition the crate does not build with | lost proof / wrong edition | the E4 matrix and the 2021 `extern "C"` fixture | 2026-11-13 |

The clusters are the lesson: rows 1–9 are all the *contract reader's* value and
width model; rows 10–13 are all *name resolution* (a name bound to the wrong
thing); rows 14–17 are all a *write or a path* that was dropped. A fix that
addresses one shape and not its siblings is the recurring cause — the reader had
three `align_widths` sites, four operator levels, five `push` sites, and each was
found one at a time.

## The engine and the imperative layer

These are documented in [`AGENTS.md`](AGENTS.md); they are listed here so the
ledger covers the whole stack rather than only the frontend.

- **A limit that truncates instead of reporting** (five instances). A bounded
  buffer or a width silently dropped evidence, so a summary outran the evidence:
  an under-declared call frame, a `Total` computed by counting instead of
  discharging, obligations dropped at `MAX_OBLIGATIONS`, a frame truncated at
  `MAX_WRITES`, an `exists_guarded` index truncated to the bound's width. Fixed by
  making the partiality part of the *type* (`Frame::complete`, `push_checked`,
  `Obligation::discharge`), not by a flag.
- **Vacuity** (four instances). A proof with no evidence: an unsatisfiable
  precondition, an unsatisfiable `Assume` in the body, a bound too narrow to name
  `len`, a call to `ensures false`. Reported as failures (`VacuousPrecondition`,
  `VacuousAssume`, `DivergentCall`) rather than proofs.
- **A proof object with no lifetime** (two instances). `Certificate` and
  `Report` stored term ids into a resettable arena, so a proof from one scope
  named a different formula in the next. Fixed by packing the arena generation
  into the id itself.
- **A kernel rule with no bounds** (`Imp<P, Q>` with no `Theorem` bound accepted
  `Truth => Falsity`). Fixed with the bounds and a `compile_fail` doctest.
- **A printer that is part of the proof** (three exporter bugs: polarity, sort,
  direction). Each made the external evidence not apply. Fixed with an independent
  SMT-LIB reader and a tautology corpus (`examples/z3diff.rs`).
- **A `to_int` that floored and a `from_int` that wrapped** in `Fixed` (Q16.16).
  Both total, so the proof layer could not see them; found by testing the *value*.

## The rate, and the exit criterion

The review's data (2025-11-04 … 2025-11-12) counted at least eleven false proofs;
the MIR-frontend table above records twenty-one wrong verdicts across
2026-11-12 … 2026-11-16, which is the same order of magnitude and the same
pattern — most found by a differential oracle or a hand probe, not by a unit test
written after the fact.

The roadmap's exit for a "beta" claim is **four consecutive weeks with no new
false proof while the independent corpus keeps growing**. That clock restarts on
each row above; the most recent is 2026-11-16. Until it clears, a `verified` is
evidence that a check *ran*, not yet that it is trustworthy on its own — which is
why every verdict the frontend reports carries the obligation it discharged, and
why `tests/mir.rs` replays each counterexample against the compiled function.

## Keeping this honest

- A new row is added in the commit that fixes the defect, with its fixture.
- A row's fixture must be confirmed to **fail** when the fix is reverted; a test
  that passes on the broken code is decoration.
- The classes are the point, not the count: when a row is added, check whether a
  sibling shape shares the cause, and add it in the same commit if so.

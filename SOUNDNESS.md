# Soundness ledger

A verifier's worst failure is a **false proof**: a `verified` verdict for a
program that does not satisfy its contract. It is worse than a crash, because a
crash reports nothing while a false proof is *trusted*. This file is the honest
record of every false proof this project has found and fixed, so that the rate is
a number rather than an impression.

It is the A1 item of [`ROADMAP.md`](ROADMAP.md): track the false-proof rate, and
pause feature work on any layer that produced one in the last two weeks. The
clock restarts on every row below, so the *date* and *commit* columns are what the
criterion is computed from, not decoration.

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
without a fixture would be a claim, not evidence. The fixture column is the
**fourth cell** of every table (after `#`, `Symptom`, `Class`), so a single
extractor reads both tables; a fixture cell may name more than one test, and may
name the file it lives in as `` `path/to/file.rs` ``, which pins the test to that
file. The fixtures live in `tests/mir.rs` unless the row says otherwise; the
`src/mir/spec.rs` unit tests are noted where the guard runs without a `rustc`.

The **commit** is the one that fixed the defect (and, where the two differ,
carried the fixture); `git show <commit>` reproduces the change. The commit for a
row whose defect predates the crate's move to the repository root (2026-10-27)
resolves only with `git log --all`, because the fixture file moved with the crate.

## The MIR frontend

The frontend reads `rustc`'s textual MIR and turns contracts into queries. These
are the defects where it produced a wrong verdict.

| # | Symptom | Class | Fixture | Commit | Fixed |
|---|---|---|---|---|---|
| 1 | `0xFF` read as decimal `0`, so `requires: x == 0xFF` meant `x == 0` and a false postcondition was proved | false proof | `a_radix_literal_is_read_at_its_radix` | `504484b` | 2026-10-30 |
| 2 | `128` accepted for an `i8` (it fits eight *unsigned* bits), read as `-128`, so `x <= 128` admitted nothing | false proof | `an_out_of_range_literal_is_refused_not_wrapped` | `6e5b299` | 2026-10-30 |
| 3 | `200u8 + 100u8` folded mod width to `44`, so `x <= 200 + 100` *narrowed* the precondition and a false postcondition held | false proof | `an_overflowing_constant_expression_is_refused_not_wrapped` (`src/mir/spec.rs`) | `3b8b610` | 2026-10-31 |
| 4 | A left-hand constant's signedness was dropped, so `0 < a` for an `i8` compared unsigned and `i8::MIN` read as the *largest* value | false proof | `a_constant_left_signed_compare_is_signed_not_unsigned` | `24bebe1` | 2026-10-29 |
| 5 | `-1i8 as i16` zero-filled to `255`, so `a as i16 == 255` was proved for a signed source | false proof | `a_widening_cast_respects_the_sources_signedness` | `d715d2a` | 2026-10-29 |
| 6 | A signed slice element was read as unsigned in a *contract*, so `xs[0] >= 0` over `&[i8]` was a tautology | false proof | `a_signed_element_is_read_as_signed_in_the_contract` | `b3dfe86` | 2026-11-01 |
| 7 | A typed constant mask (`-1i8 & 1`, `1u8 & 1`) was marked untyped, so a pairing `rustc` rejects was decided | wrong verdict | `a_typed_constant_mask_keeps_its_type` | `fd7591c` | 2026-11-02 |
| 8 | A fixed-width constant (`1i8`) was resized to a partner of another width (`x as i16`), deciding an `E0308` program | wrong verdict | `a_fixed_width_constant_may_not_meet_a_partner_of_another_width` | `745fa3e` | 2026-11-02 |
| 9 | An untyped fold that overflows its operand width (`(!0 + 1) < 1u8`) was decided instead of refused | wrong verdict | `an_untyped_fold_that_overflows_the_operand_width_is_refused` (`src/mir/spec.rs`) | `4ac7186` | 2026-11-02 |
| 10 | A function-local `const` was keyed by its bare name, so it was in scope in *every* function's contract | false proof | `a_local_const_is_not_in_scope_in_another_function` | `dd1ca69` | 2026-11-09 |
| 11 | A contract on an inherent method was keyed by its bare name and dropped; a dropped contract is `Verified { obligations: 0 }` | false proof | `a_contract_on_an_inherent_method_is_resolved_and_checked` | `f482de8` | 2026-11-09 |
| 12 | A branching `const` (`if false { 7 } else { 8 }`) folded to its first arm, so `K == 7` was proved while `K` is `8` | false proof | `a_branching_const_does_not_fold_to_its_first_arm` | `057bd20` | 2026-11-10 |
| 13 | A local trait method sharing an intrinsic's name was answered by the intrinsic model, so a body that disagrees with `core` proved `core`'s value | false proof | `a_trait_method_sharing_an_intrinsic_name_is_answered_by_its_body` | `d4c15af` | 2026-11-10 |
| 14 | A field write through a `&mut` (`(*_1).0 = v`) was dropped, so a postcondition was checked against the stale seed | false proof | `a_field_write_through_a_mutable_reference_is_applied` | `08a6065` | 2026-11-04 |
| 15 | Two same-named structs in different modules collided in the layout table, so drop glue read the wrong layout | false proof | `two_same_named_structs_do_not_share_a_layout` | `3bf73ea` | 2026-11-16 |
| 16 | A diverging call in its cleanup form (`-> bbN` with a live `Drop` local) was dropped, so a reachable panic was never checked | false proof | `a_diverging_call_in_a_function_with_a_drop_local_is_checked` | `451c73f` | 2026-11-13 |
| 17 | Drop glue of a struct whose field has its own destructor ran only the outer one, hiding a panicking field destructor | false proof | `a_destructor_body_is_executed_and_its_panic_is_an_obligation` | `f260560` | 2026-11-15 |
| 18 | The `unwind:` bound counted *block entries*, so a two-iteration loop verified under `unwind: 1` | false proof | `the_unwind_bound_counts_the_whole_loop_not_one_latch` | `3bf73ea` | 2026-11-16 |
| 19 | `RangeInclusive::next` tested the *unsigned* successor-overflow flag, so a signed inclusive range never terminated and a true contract became a bound failure | false refutation | `a_signed_inclusive_range_stops_at_its_boundary` | `3bf73ea` | 2026-11-16 |
| 20 | `next` advanced an empty range, so a second `next` returned an element Rust never yields | wrong verdict | `an_empty_inclusive_range_stays_empty` | `3bf73ea` | 2026-11-16 |
| 21 | The edition was pinned to 2024, so valid 2021 code (`extern "C"`) was refused, and code that lowers differently was verified under an edition the crate does not build with | lost proof / wrong edition | `a_2021_only_file_is_verified_under_its_own_edition`, `every_edition_compiles_the_corpus_to_the_same_verdicts` (`tests/mir.rs`) | `8ae3503` | 2026-11-13 |
| 22 | A returned reference to a whole array element (`elem_mut(&mut x.a)`) appended the argument's deref into the caller's place, so the write was dropped and a stale seed was proved | false proof | `a_returned_reference_to_an_element_reaches_the_caller` | `d6a4690` | 2026-11-07 |
| 23 | A returned reference to a symbolic element carried the callee's index local across the boundary, aiming the write at a caller local that merely shared its number | false proof | `a_returned_reference_to_an_element_reaches_the_caller` | `dd1ca69` | 2026-11-09 |
| 24 | A call to an intrinsic resolved to a local function sharing its name, so a measured self-recursion assumed its own postcondition (`ret == 0` for a body returning `n`) | false proof | `an_intrinsic_call_is_not_a_self_recursive_call` | `b7769c1` | 2026-11-09 |
| 25 | A local `impl From<u8> for u16` answered a real `<u16 as std::convert::From<u8>>::from` call (shared tail and owner), proving `ret == 7` | false proof | `a_local_trait_named_from_does_not_answer_the_std_trait` | `e4543d0` | 2026-11-11 |
| 26 | A bare crate-root trait call was answered by a same-named module trait's impl, and a local impl of an *imported* trait answered the library call | false proof | `a_bare_crate_root_trait_call_is_not_answered_by_the_model`, `a_local_impl_of_an_imported_trait_does_not_answer_the_model` | `496e416` | 2026-11-11 |
| 27 | An inherited trait contract bound parameters by *name*, so an impl naming them in the other order was checked against the wrong argument; a return type wrapped to the next line was read as unsigned | false proof | `an_inherited_contract_binds_parameters_by_position_not_by_name`, `a_return_type_on_one_line_is_read_and_refutes_the_false_claim` | `653a340` | 2026-11-12 |
| 28 | A `<Self as T>::m` call inside a trait *default* body resolved to the default method, so an impl's override was ignored and a caller's contract about its effect was proved against a no-op | false proof | `a_user_type_named_range_is_not_answered_by_the_range_model` (`tests/mir.rs`) | `9b13340` | 2026-11-16 |
| 29 | A `for` loop's iterator state is written *through `&mut`*, and the loop-header havoc replaced neither the referent nor the (widthless) aggregate's parts, so the exit guard folded to `false`, the exit edge was pruned, and a false postcondition was `Verified` | false proof | `the_for_loop_range_desugaring_is_modelled` (`tests/mir.rs`) | `118d42f` | 2026-11-13 |
| 30 | The loop-header havoc sized a local from its own `Ty::width()`, which is `None` for a `Ty::Ref`, so a `&mut u8` *argument* written inside the loop was skipped and its referent kept the entry value -- the exit guard folded and a false postcondition was `Verified` | false proof | `a_loop_havocs_what_it_writes_through` (`tests/mir.rs`) | `64cd6ba` | 2026-11-13 |
| 31 | The loop-header havoc collected a call's *destination* but not what the callee writes *through* a reference argument, so `while i < 3 { bump(x); i += 1 }` kept `x` at its entry value -- the exit guard folded and a false postcondition was `Verified` | false proof | `a_loop_havocs_what_it_writes_through` (`tests/mir.rs`) | `a5bd578` | 2026-11-13 |
| 32 | A projected promoted-constant use (`<Self as Custom>::zzz::promoted[0]`) was reconciled against its definition by trait owner and promotion index only, so two trait defaults that each own a `promoted[0]` collided and a call into one reported the *other* method's panic message | wrong verdict (misleading witness) | `a_projected_promoted_use_resolves_its_own_method` (`src/mir/exec.rs`) | `f5ad531` | 2026-11-13 |
| 33 | The interprocedural write-set walk allocated its block-visit set per function, so a loop calling a *self-recursive* callee followed the self-call forever and overflowed the stack -- a crash, not a refusal, and reachable with no reference argument | crash | `a_loop_that_calls_a_recursive_function_terminates_and_is_sound` (`tests/mir.rs`) | `5c49426` | 2026-11-13 |
| 34 | The `Vec` model matched the container by the bare last path segment, so a user `struct Vec<T>` with a panicking `Drop` was treated as glue-free and its destructor was skipped -- `Verified` for a body that always panics | false proof | `a_vec_length_model_does_not_leak_across_a_drop_havoc_or_move` (`tests/mir.rs`) | `8dd4d21` | 2026-11-17 |
| 35 | The loop-header havoc refreshed a local's fields but not its tracked `Vec` length, so the exit edge of an inductive loop read the entry length and `while i < 3 { v.push(1); i += 1 }` proved `ret == 0` for the real `ret == 3` | false proof | `a_vec_length_model_does_not_leak_across_a_drop_havoc_or_move` (`tests/mir.rs`) | `8dd4d21` | 2026-11-17 |
| 36 | A `Vec` move (`let w = v`) and a returned vector dropped the tracked length, so `w.len()`/`mk().len()` read a receiver with no modelled length -- the proof was lost, not invented | lost proof | `a_vec_length_model_does_not_leak_across_a_drop_havoc_or_move` (`tests/mir.rs`) | `8dd4d21` | 2026-11-17 |
| 37 | A slice's `last()` element is one fresh variable keyed by a sentinel, and a concrete-index write replaced only that index's entry -- so a `last()` read after a write that *is* the last element returned the pre-write value and `let b = *xs.last().unwrap(); xs[0] = 1; b == *xs.last().unwrap()` was proved for a one-element slice | false proof | `slice_last_is_an_element_and_array_last_is_exact` (`tests/mir.rs`) | `b48d7e6` | 2026-11-18 |
| 38 | `char::MAX`/`char::MIN` were derived from `Ty::width()` (32 bits), so `char::MAX` read as `2^32 - 1`: `c == char::MAX` compared against the wrong number, refuting the body and proving a claim that `char::MAX` is not the maximum | false proof | `char_literals_and_ascii_predicates_are_modelled` (`tests/mir.rs`) | `b48d7e6` | 2026-11-18 |
| 39 | A chain of `Option::or`/`and` recorded only its operands' *leaves*, so `a.first().or(b.first()).or(c.first())` lost the inner `or` and the outer combinator read the receiver's missing identity as permission to select the argument's element -- `ret == 9` was proved for the real `ret == a[0] == 5` | false proof | `option_or_and_are_total_and_select_the_right_operand` (`tests/mir.rs`) | `617a958` | 2026-11-17 |
| 40 | The conditional element identity a combinator folds was returned as `Sign::Unsigned`, so a signed slice element read through `or`/`and` compared unsigned -- `*a.first().or(b.first()).unwrap() < 0` for `a[0] == -1` is `false` under the unsigned reading, so `ret == false` was proved | false proof | `option_or_and_are_total_and_select_the_right_operand` (`tests/mir.rs`) | `617a958` | 2026-11-17 |
| 41 | `Result::unwrap_or_default` was excluded from the `unwrap_or` error-drop guard, so a `Result<u8, Boom>` whose `Boom::drop` panics was reported panic-free while the call unwinds on `Err` | false proof | `a_combinator_that_destroys_a_value_respects_its_drop_glue` (`tests/mir.rs`) | `27ba484` | 2026-11-17 |
| 42 | A **qualified** type name (`m::Outer`) fell back to a *bare* layout key, so with a crate-root `Outer { lo, hi }` and a one-line `pub mod m { pub struct Outer { hi, lo } }` both field projections read the crate-root fields and `requires: o.hi == 5; ensures: ret == 5` on a body returning `o.lo` was **verified** (rustc returns `7` for `{ hi: 5, lo: 7 }`) | false proof | `a_qualified_type_is_not_answered_by_a_bare_layout` (`tests/mir.rs`) | `a552c67` | 2026-11-18 |
| 43 | A comment between two tokens was **deleted** instead of replaced by a space, so `ensures: ret == n/**/as/**/u8` (the cast `n as u8`) was read as the identifier `nasu8`; a body returning an argument of that name **verified** a postcondition the source never states | false proof | `a_comment_and_a_non_ascii_name_cannot_smuggle_a_false_proof` (`tests/mir.rs`) | `2ab47cb` | 2026-11-19 |
| 44 | The clause scanner walked bytes and pushed `byte as char`, so a non-ASCII identifier `µ` (0xC2 0xB5) was read as `Âµ` -- a *different* name; a body returning an argument of the mangled spelling **verified** `ensures: ret == µ` | false proof | `a_comment_and_a_non_ascii_name_cannot_smuggle_a_false_proof` (`tests/mir.rs`) | `2ab47cb` | 2026-11-19 |
| 45 | `take_clause` matched the literal `requires:` (and each sibling keyword), so a comment before the colon -- valid Rust, whose matcher is `$clause:ident : $body:expr` -- became `requires : true` and the clause was **refused as unknown**, so the function was skipped | lost proof | `a_comment_before_a_clause_colon_is_whitespace_not_a_dropped_clause` (`tests/mir.rs`) | `808f33c` | 2026-11-19 |
| 46 | `extern_options` probed for an rlib with `VERIF_RUSTC` while the caller emitted MIR with `rustc`; under CI (nightly `VERIF_RUSTC`, stable build) the probe rejected the stable rlib, the extern was dropped, and `use verif::spec;` failed `E0432` -- the mismatch is now a **refused** probe/emit pair naming both compilers | wrong verdict | `a_probed_extern_set_is_refused_by_a_different_compiler` (`src/mir/verify.rs`) | `808f33c` | 2026-11-19 |
| 47 | `canonical_compiler` used `fs::canonicalize` only, which never searches `PATH`; a bare `rustc` (the rustup *shim*, a different file from the toolchain binary) therefore never equalled `rustup which`'s absolute path -- so the new probe/emit guard refused a legitimate pair, and the guard test passed **vacuously** because it canonicalised *both* operands with the same broken helper | lost proof (and a vacuous test) | `a_bare_compiler_name_and_its_absolute_path_are_one_identity` (`src/mir/verify.rs`) | `c46437a` | 2026-11-19 |

The clusters are the lesson: rows 1–9 are all the *contract reader's* value and
width model; rows 10–13 are all *name resolution* (a name bound to the wrong
thing); rows 14–17 are all a *write or a path* that was dropped; rows 22–28 are
the *call and trait resolution* family (a call answered by the wrong body); rows
39–41 are the `Option` combinator family (a selected element read from the wrong
operand, or with the wrong sign, and a destructor the combinator skips); row 42
returns to *name resolution* — a type name answered by another type's layout; and
rows 43–44 are the **lexical** reader — a comment deleted instead of replaced by a
space, and a UTF-8 identifier decoded a byte at a time. Both are the same mistake
one layer below the parser: the clause *text* was wrong before any expression was
parsed, so every rule downstream faithfully checked the wrong string. Row 45 is the
same layer's other half — a comment replaced by a space is *correct*, but the clause
matcher then demanded the colon be glued to the keyword, so the valid spelling
`requires : true` was refused; a separator fix and a matcher are two readers of one
line. Row 46 is not lexical at all: the *compiler* a probe asks is not the compiler
the emitter runs, and an rlib's metadata is toolchain-specific, so the two must be
one name — a build-time mismatch that only a second toolchain in CI could show.
A fix that addresses one shape and not its siblings is the recurring cause — the
reader had three `align_widths` sites, four operator levels, five `push` sites,
and each was found one at a time.

## The engine and the imperative layer

These are documented in [`AGENTS.md`](AGENTS.md). Each row here is one *instance*
of a class, with its own fixture and commit, so the two-week pause can be applied
to the engine and the imperative layer as well as to the frontend — a class
summary would leave their fix dates unfindable.

| # | Class | Symptom | Fixture | Commit | Fixed |
|---|---|---|---|---|---|
| 48 | false proof | An under-declared call frame let a caller prove a clobbered variable survived the call | `under_declaring_the_frame_is_rejected` (`tests/call.rs`) | `1b64205` | 2026-10-24 |
| 49 | false proof | A callee writing more than the cap made the caller's derived frame look complete, so a prefix of the truth passed | `a_call_to_an_over_cap_callee_makes_the_caller_frame_incomplete` (`tests/call.rs`) | `fd15f98` | 2026-10-27 |
| 50 | false proof | `Report::terminates` *counted* variant obligations instead of discharging them, so a non-decreasing measure read `Total` | `a_total_claim_is_not_made_for_a_divergent_loop` (`tests/modular_differential.rs`) | `fa178ef` | 2026-10-25 |
| 51 | false proof | `MAX_OBLIGATIONS` dropped obligations silently, so a failing `LoopExit` sat outside the buffer and the report said `verified` | `assertions_beyond_the_cap_are_reported_not_hidden` (`tests/wp.rs`) | `8d7120c` | 2026-10-27 |
| 52 | false proof | `exists_guarded` truncated the index to the bound's width, so a concrete index wrapped and was treated as inside | `the_guarded_quantifiers_do_not_truncate_their_index` (`tests/quant.rs`) | `40f94c0` | 2026-10-25 |
| 53 | vacuity | An unsatisfiable precondition made `pre => wp(body, post)` a theorem for any body | `an_unreachable_precondition_is_not_a_proof` (`tests/wp.rs`) | `8c812d8` | 2026-10-25 |
| 54 | vacuity | An unsatisfiable `Assume` inside the body made everything downstream vacuously true | `an_unreachable_assume_is_not_a_proof` (`tests/wp.rs`) | `779f1e9` | 2026-10-26 |
| 55 | vacuity | A bound exactly as wide as the address could not name `len`, so the standard postcondition was unsatisfiable | `a_bound_the_same_width_as_the_address_is_rejected` (`tests/mem.rs`) | `a85ebe6` | 2026-10-25 |
| 56 | vacuity | A call to `ensures false` never returns, so the post-call state was empty and the continuation vacuously true | `a_call_to_a_never_returning_proc_is_not_total` (`tests/call.rs`) | `3754e1d` | 2026-10-26 |
| 57 | false proof | `Certificate` stored a bare term id, so one from a reset scope named a different formula and certified a falsehood | `a_certificate_does_not_survive_an_arena_reset` (`tests/kernel.rs`) | `f9f6f4d` | 2026-10-25 |
| 58 | false proof | `Report` held term ids with no arena generation, so a report read after a reset answered `Unknown` for every obligation | `a_report_is_only_valid_in_the_arena_that_built_it` (`tests/wp.rs`) | `732aebf` | 2026-10-28 |
| 59 | false proof | The kernel's `Imp<P, Q>` had no `Theorem` bound, so `assert_proof!(Imp<Truth, Falsity>)` compiled | `the_imp_associated_proof_type_is_a_function_between_proofs` (`tests/kernel.rs`) | `4601e9d` | 2026-10-26 |
| 60 | false proof | The SMT-LIB printer's polarity, sort and direction bugs made the external evidence not apply (a solver proved a different formula) | `the_export_checker_rejects_what_the_old_exporter_printed` (`tests/differential.rs`) | `d687a45` | 2026-10-26 |
| 61 | wrong verdict | `Fixed::to_int` floored instead of truncating and `from_int` wrapped instead of saturating — both total, so the proof layer could not see them | `fixed_to_int_truncates_toward_zero`, `fixed_from_int_saturates_instead_of_wrapping` (`src/logic.rs`) | `c35b456` | 2026-10-26 |
| 62 | vacuity | The MIR frontend's twin of row 48: a call to a bodyless `ensures false` callee made every claim after it vacuously true, so the caller read `verified` | `a_call_to_a_callee_whose_postcondition_is_unsatisfiable_fails` (`tests/mir.rs`) | `c60ff40` | 2026-11-12 |
| 63 | false proof | `prove_implies` decided a closed true goal without reading the premise, so a `pre` saved from an earlier arena returned `Valid` for a premise that was not the one passed | `a_closed_goal_does_not_bypass_a_stale_premise` (`tests/sym.rs`) | `dd1ca69` | 2026-11-09 |

## Unavailable evidence

The rows above are complete: every one has a date, a commit and a fixture, and
the commit resolves in this repository. Three things about the record are worth
stating so a reader does not mistake a gap for completeness:

- **The pre-rename commits are found under `--all`.** The crate was `discharge`
  until 2026-10-30 and its directory was `discharge/` until the move to the
  repository root (`3797cf2`, 2026-10-27). A fixture whose commit predates the
  move is not reached by `git log -S` on the current path; `git log --all -S`
  is. Every engine row above was recovered that way.
- **The review's eleven earlier false proofs are rows 10, 14, 22–28 and 52 here,
  not a count.** The review named seven commits that fixed them (`08a6065`,
  `d6a4690`, `dd1ca69`, `b7769c1`, `e4543d0`, `496e416`, `653a340`); each false
  proof in those commits is its own dated row — nine in the MIR table and one
  in the engine table. "When did the engine last produce a false proof" is
  therefore answerable (2026-11-16, row 15) rather than hidden in a summary.
- **A defect with no surviving fixture is not recorded as a row.** The ledger is
  a list of *evidence*; a row that cannot point at a test that fails on the
  unfixed code would be a claim, which is the failure mode this file exists to
  avoid. If such a defect is found, it is fixed and given a fixture in the same
  commit, or it is noted here explicitly — none is outstanding.

## The rate, and the exit criterion

The review's data (2025-11-04 … 2025-11-12) counted at least eleven false proofs;
the tables above record fifty-nine wrong verdicts across 2026-10-24 … 2026-11-19,
which is the same order of magnitude and the same pattern — most found by a
differential oracle or a hand probe, not by a unit test written after the fact.
The densest cluster is the contract reader (rows 1–9, 2026-10-29 … 2026-11-02),
which is why the standing rule is to probe the *neighbours* of a fix.

The roadmap's exit for a "beta" claim is **four consecutive weeks with no new
false proof while the independent corpus keeps growing**. That clock restarts on
each row above; the most recent is **2026-11-19**. Until it clears, a `verified`
is evidence that a check *ran*, not yet that it is trustworthy on its own — which
is why every verdict the frontend reports carries the obligation it discharged,
and why `tests/mir.rs` replays each counterexample against the compiled function.

## Keeping this honest

- A new row is added in the commit that fixes the defect, with its fixture, its
  commit hash and its date.
- A row's fixture must be confirmed to **fail** when the fix is reverted; a test
  that passes on the broken code is decoration.
- The classes are the point, not the count: when a row is added, check whether a
  sibling shape shares the cause, and add it in the same commit if so.
- `tests/soundness.rs` checks all of the above mechanically: every fixture name
  must be a `#[test]` (not merely a same-named helper), in the file the cell
  names, and no row's date may be in the future.

# Roadmap

The single place open work lives. `AGENTS.md` records what was *learned*; this
file records what is *left*, in the order it blocks ordinary Rust. Every item has
five fields, so "is this done?" is a check rather than an opinion:

- **Priority** — P0 (blocks everyday code), P1 (needed to verify a real crate),
  P2 (parity with the high end).
- **Exit criterion** — a command whose output decides the item.
- **Competitor** — the tool whose gap the item closes.
- **Move** — **build** it, **bridge** to a tool that has it, or **won't do**.
- **Status** — done / in progress / todo / won't do.

A PR that closes an item updates its status here in the same PR.

The starting numbers, measured on the branch that created this file, are the
baseline every item is scored against:

| Corpus | Command | Verified / decided |
|---|---|---|
| `examples/mir_targets/actuator.rs` | `cargo run --features std --example mir_coverage -- examples/mir_targets/actuator.rs` | 18 / 33 |
| `examples/mir_targets/realistic.rs` | same, `realistic.rs` | 434 / 806 |
| `examples/mir_targets/everyday.rs` | same, `everyday.rs` | **16 / 21 (76%)** |

`everyday.rs` is the honest one: ordinary Rust written by an external reviewer,
not shaped for the tool. `realistic.rs` is a regression corpus (about a third of
it is adversarial fixtures), so its high percentage does not measure coverage of
ordinary code. Phase 1 is defined on `everyday.rs`.

---

## Phase 1 — everyday Rust (P0)

Exit: `everyday.rs` at least **80% decided** (17 of 21), and four weeks in a row
with no new false proof while the independent corpus keeps growing.

### The Rust edition (E items)

- **E1. Use the crate's own edition.** · P0 · done · Kani (whole-crate builds)
  - Gap: the frontend pinned `--edition=2024`, so a valid 2021 crate
    (`extern "C" { … }` must be `unsafe` from 2024) was refused, and code that
    lowers differently from the edition that ships could be verified as a program
    nobody built.
  - Exit: a 2021 `extern "C"` fixture produces MIR and verifies. ✅
  - Move: **build** (read `package.edition` from the nearest `Cargo.toml`,
    resolving `edition.workspace = true`). See `resolve_edition`.
- **E2. An explicit override, and no silent default.** · P0 · done · —
  - Exit: `MirOptions { edition }` and `VERIF_EDITION` override it; a loose file
    with neither is an error naming the missing edition. ✅
- **E3. Stamp the edition on every result.** · P0 · done · —
  - Exit: `FileReport.edition` is recorded and `mir_coverage` prints it. ✅
- **E4. An edition matrix in the gate.** · P1 · done · Kani
  - Gap: nothing ran the corpus under 2015/2018/2021/2024 and required identical
    verdicts, and no fixture pinned the per-edition lowering difference.
  - Exit: `tests/mir.rs` runs `actuator.rs` under all four editions and requires
    the *whole* outcome map to match (not just the decided count, so a
    `verified`↔`failed` swap is caught), plus a 2021-only `extern "C"` fixture
    that verifies under 2021 and is refused under 2024 — the evidence the edition
    is *used*, not pinned. ✅
  - Move: **build**.
- **E5. One source for the edition.** · P1 · done · —
  - Exit: `tools/mir-oracle` takes the edition from the frontend's resolver
    (`emit_mir_opts` returns it) rather than repeating a literal. ✅
- **E6. The misleading hint.** · P0 · done · —
  - Exit: `mir_coverage` prints the frontend's error (which names the compiler, the
    edition and the reason) instead of "set VERIF_RUSTC to a nightly". ✅

### Coverage (C items)

- **C1. `Drop` and cleanup edges.** · P0 · done · Kani, Prusti, Creusot,
  Verus, SPARK
  - Gap: `drop(_x) -> [return: bbN, unwind …]` is unmodelled, so any function with
    an RAII local (`Vec`, `String`, `Box`, a lock guard, a user `Drop`) is
    incomplete.
  - **C1b (done):** a diverging call in its *cleanup* form
    (`_4 = core::panicking::panic(…) -> bb4`, `bb4 (cleanup)`) was not recognised,
    so an `assert!` in any function with a live `Drop` local was a dropped path.
    Now read as a diverging call: `guard_misguarded` FAILED with a counterexample
    (`x = 224`). ✅
  - **`drop` (done):** `Term::Drop { place, target }` is parsed (its `drop(_2) ->
    [return: …]` line prints like a call, and since it has no ` = ` destination the
    call arm's fallback turned the whole line into `Unknown` — reported "unmodelled
    terminator" — so without its own arm the path was dropped) and executed. Three
    cases, and the middle one is the soundness boundary:
    - **No drop glue** — an integer, `bool`, `()`, a reference, or an aggregate of
      such (`[u8; N]`, a plain struct, a tuple). The terminator changes nothing, so
      it is a no-op and the path continues. This arm is *defensive*: rustc emits no
      `drop` at all for such a type (measured over `realistic.rs`: 0 of 6 `drop`
      terms are glue-free — the other six are a user `Drop` or a container), so the
      arm cannot be exercised through the frontend and its check lives in a unit
      test on `drop_is_noop`. It is kept because the alternative to a no-op is a
      refusal, and refusing a glue-free `drop` would lose a proof.
    - **A user `impl Drop`** — its body is in the dump, so it is executed through
      the same inliner a method call uses (`self` is `&mut T`, so the dropped place
      is the argument and the write-back carries the destructor's effects).
      `destructor_panic_cannot_prove_this` is refuted with a witness (`v = 16`) and
      its guarded twin verifies.
    - **An unmodellable container** — a `Vec`, `String`, `Box`, or a struct whose
      field has a user destructor. **Refused, not no-oped.** The MIR probe that
      decided this: `fn g(w: Wrapper)` with `struct Wrapper { v: Vec<u8> }` and
      `fn f()` with `struct Outer { i: Inner }` where `Inner: Drop` both lower to
      the *same* `drop(_2) -> [return: bb1, unwind continue]` line — the dump does
      not distinguish a container from a struct holding a user destructor. So the
      review's suggested "std container is a no-op that changes no scalar state" is
      unsound for the aggregate case (a `Vec<PanicOnDrop>`, or any struct wrapping
      one, panics in its destructor). The honest answer is a refusal: a lost proof,
      never a false one.
    - A *projected* place (`drop(_2.0)`) is refused for the same reason: the
      reference write-back is keyed on a whole local, so a projection would land
      the post-state on the wrong storage. rustc does not emit that shape for a
      glue-bearing place.
    - **R5 (done): the struct layout is keyed by its module path.** The layout
      table was keyed by the bare struct name, so `m::Outer` and `n::Outer` collided
      and the drop-glue check read whichever was recorded last — when that one is
      glue-free, a panicking field destructor vanishes and the function is a false
      `Verified`. Layouts are now keyed by the module-qualified path, with a bare
      key back-inserted only when the bare name is unique crate-wide; a shared name
      makes the bare lookup miss, so the glue check reports the shape unmodelled
      rather than reading the wrong layout (`two_same_named_structs_do_not_share_a_
      layout`).
    - **R6 (done): a unit struct is a zero-field layout.** `struct Guard;` was not
      read as a struct at all, so the drop-glue check saw an unknown type and
      refused the function. A unit struct now has an empty layout, so its `Drop`
      body is the only glue — and a panicking one is a real obligation
      (`a_unit_struct_runs_its_destructor`).
  - Exit (done): `guard_guarded` / `guard_is_dropped_cleanly` verified,
    `guard_misguarded` FAILED with a counterexample. ✅
  - Who has it: Kani, Prusti, Creusot, Verus, SPARK (finalization).
  - Move: **build**.
- **C2. `Option`/`Result` and `?`.** · P0 · in progress · Kani, Verus, Prusti, Creusot
  - Gap: `unwrap`, `unwrap_or`, `expect`, `ok_or`, `map`, `is_some` and `?` are
    unmodelled. Evidence: `checked_or_max`, `div_unwrap` incomplete.
  - Approach: the enum payload/discriminant model exists; add a **contract library
    for std/core** in the spirit of Prusti `#[extern_spec]` / Verus `vstd`, each
    spec differential-tested against the real implementation.
  - Exit: `checked_or_max` and `div_unwrap` verified; a misused `unwrap` refuted
    with a counterexample.
  - Move: **build**.
  - Progress: the `Option` and `Result` *methods* are modelled. `unwrap`,
    `unwrap_or`, `expect`, `is_some`/`is_none` and `is_ok`/`is_err` read the
    receiver's tag and payload from the executor's discriminant/payload stores —
    the first modelled calls whose input is an *enum* rather than a bit-vector
    operand. `unwrap`/`expect` report a **panic** on the failure variant (the same
    reachable-failure obligation `abs`/`clamp` carry), so
    `if x.is_some() { x.unwrap() }` verifies with the panic ruled out;
    `unwrap_or(default)` is total. `Option` and `Result` are one shape with the
    payload on the other discriminant (`Some` = tag 1, `Ok` = tag 0), so one
    executor arm answers both with the payload variant read off the method name.
    `checked_or_max` (`checked_add(..).unwrap_or(u32::MAX)`) now **verifies** —
    `everyday.rs` 14/21 -> **15/21**. `div_unwrap` is still incomplete, but the gap
    is the *divider* wall (`n / d <= n` at `u32`), not the `Option`; the same body
    decides at `u8`. Sixteen fixtures (true/tripwire/panic pairs, both families) in
    `realistic.rs` (**424 of 789**).
  - Remaining: `?` (the `Try` desugaring needs `From` on the error type), `ok_or`,
    `map`/`map_err`/`and_then` (closures), and the `Option`/`Result` *result* of a
    function whose contract names the payload (the `qmark_probe` gap: a contract
    reading `ret <= n` on an `Option<u32>` return is refused because the return has
    no single word).
- **C3. Ranges and `for` loops.** · P0 · done · Kani, Verus, Prusti
  - Gap: `RangeInclusive::new`, `Range`, `Iterator::next` unmodelled, so the
    commonest loop in Rust is out of reach. Evidence: `tri` incomplete.
  - Approach: model `Range`/`RangeInclusive` as structs, `next` as a modelled
    intrinsic, recognise the `for` desugaring, reuse the loop machinery.
  - Exit: `tri` verified with an `invariant:`; a missing invariant reported as *a
    missing invariant*, not "unmodelled". ✅
  - Move: **build**.
  - Progress: the desugaring is **built**. `RangeInclusive::new`/`Range::new`,
    `IntoIterator::into_iter` and `Iterator::next` are modelled
    (`intrinsics::Range`/`RangeMethod`, answered by `range_method` from the
    range's struct fields, with `core`'s `forward_overflowing` boundary
    reproduced exactly), and a `for` loop now decides through the existing
    machinery — `for i in 0..=n { s += i }` verifies with `unwind: 4` and with an
    `invariant: s <= 5050`, and its false twin is refuted
    (`the_for_loop_range_desugaring_is_modelled`).
  - The second exit half is met too: a loop with no `invariant:` or `unwind:` is
    reported as a *missing loop contract* naming the remedy, not as an unmodelled
    construct — `loop unwound past 9 at bb8 of tri; assuming it exited would be
    unsound -- this is a missing loop contract, not an unmodelled construct:
    declare `invariant:` or `unwind:` to decide it`
    (`a_loop_without_a_contract_names_the_missing_contract`).
  - A boundary that remains, and is *not* a gap in the desugaring: an invariant
    that *names* the loop element (`s <= i`) is refused as `unknown name i`. The
    element is a `debug` binding inside a nested `scope` block (`debug i => _9;`
    at `scope 3`) that is genuinely **not live at the loop header** — `next` has
    not returned on entry, so `_9` has no value there. Resolving the name would
    mean reading a variable the header state does not contain, which is a wrong
    value rather than a missing one, so the refusal is correct. A `for`-loop
    invariant is written over the loop's *carried* state (`s <= 5050`), which is
    exactly the state the header havocs and the invariant is quantified over.
    `tri` in `everyday.rs` declares no loop contract, so it stays `incomplete`
    with the honest missing-contract reason.
  - Boundary hardening from the PR #8 review round (R1, R4). Both are cases where
    the range model *decided*, so a wrong value was a wrong verdict, not a refusal:
    - **R1: the successor's overflow flag must test the *signed* `MIN`.** The flag
      was `succ == 0`, the unsigned rule. On a signed inclusive range it never
      fires, so `127i8..=127i8` kept yielding past `127` (into `-128`, `-127`, …)
      until the `unwind:` bound — a true contract became a bound failure. The flag
      is now `succ == (1 << (w-1))` for a signed range.
    - **R4: `next` leaves an empty range unchanged.** The advance was unguarded, so
      `255u8..=254u8` (empty) had its `start` wrapped to `0` and the *second* `next`
      returned `Some(0)` — an element Rust never yields. The advance is now guarded
      by `!empty`.
    - Validated by a differential oracle: 23 ranges at the `u8`/`i8` boundaries
      (every combination of `MIN`/`MAX`/`0`) counted against a compiled `rustc`
      execution, all agreeing (`a_signed_inclusive_range_stops_at_its_boundary`,
      `an_empty_inclusive_range_stays_empty`).
- **C4. Loops without path explosion.** · P0 · done · Kani (unwinding),
  Verus, Creusot, Prusti, SPARK (`Loop_Invariant`/`Loop_Variant`), Flux
  - Gap: a 4-iteration loop over an array exhausts the 64-path budget. Evidence:
    `max_of` was incomplete (`path budget exhausted after 64 paths`).
  - (a) `invariant:`/`variant:` clauses inside the MIR frontend — **built** (the
    `Cut` machinery, loop obligations, and the `an_invariant_decides_a_loop_that_
    unwinding_could_not` regression). (b) a bounded-unrolling mode whose bound is
    *reported*: `unwind:` raises the loop bound **and** the path budget (a
    declared bound means "unwind each loop N times", and a branching body yields
    a path per branch per iteration), and a *declared* bound that is too small is
    Kani's **unwinding assertion** — a `Failed` obligation
    (`ObligationKind::UnwindBound`), not an incompleteness, so a bound can never
    cut a path off silently. A loop with **no** `unwind:` still cuts off at
    `DEFAULT_UNWIND` and reports that honestly. (c) merge states at joins
    (ite-merging) instead of enumerating paths — not done.
  - Exit: **met** — `max_of` verified with `unwind: 5`, refuted with `unwind: 3`
    by the unwinding check (`max_of_verifies_with_a_sufficient_unwind_bound_and_
    fails_with_a_small_one`); the invariant half is pinned by
    `an_invariant_decides_a_loop_that_unwinding_could_not`. `everyday.rs` scores
    16 of 21 (up from 9).
  - **R2/R3 (done): the bound counts the *loop*, not one latch.** The counter was
    keyed by the source block holding the back edge, so a loop body that reaches
    its header from two latches (an `if` whose arms both loop, two `continue`s) had
    each counted separately and the combined trip count could exceed a declared
    `unwind:` while neither latch's own count did — a two-iteration loop verified
    under `unwind: 1`. A `switchInt` block additionally reset the count on every
    arm it took, which is where a `while` header hid the bug. The counter is now
    keyed by the loop *header* (merged latches), the switch reset is removed, and
    `unwind: N` means `N` iterations of the loop however the body reaches the back
    edge (`the_unwind_bound_counts_the_whole_loop_not_one_latch`).
  - Move: **build**.
  - Follow-up (not in the exit criterion): a *sufficient* invariant for `max_of`
    needs an implication in the contract language (`i > k => m >= a[k]`), which
    is C12 (a specification language that can say more). Until then the fixture
    proves a loop by unwinding.
- **C5. Enums with payloads and match guards.** · P0 · done · Kani
  - Gap: `match m { Run(n) if n < 10 => … }` gave "unmodelled switch
    discriminant". Evidence: `next_mode` was incomplete.
  - Cause: the guard reads the payload through a borrow of a downcast place,
    `_4 = &((_1 as Run).0: u8)`, and the rvalue contains the word ` as ` inside
    its parentheses. `parse_rvalue` checked for a cast *before* a reference, so it
    split the borrow at that ` as `, the address was lost, and the guard's
    `copy (*_4)` read `Unknown`. The reference arm now runs first, which a real
    cast cannot be mistaken for (`&…` is not a place).
  - Exit: `next_mode` decided (`verified`), plus the refuted fixture
    `guarded_match_tripwire` in `realistic.rs`.
  - Move: **built**.
- **C6. The everyday `core` surface.** · P0 · in progress · Kani, Verus (`vstd`)
  - Gap: `Ord::min/max/clamp`, `iN::abs`, `abs_diff`, `rotate_*`, `is_ascii_*`,
    `is_negative`/`is_positive`, `<[T]>::len/is_empty/first/get`. Evidence:
    `abs_small`, `clamp_builtin`, `digit`, `first_or` incomplete. All but
    `<[T]>::first/get` are now modelled (`min`/`max`, `From`/`Into`, `clamp`,
    `abs`, `abs_diff`, `rotate_*`, the `is_ascii_*` classes, the sign predicates,
    and `slice::len`/`is_empty`); the remaining `first`/`get` are blocked on
    monomorphisation.
  - Approach: the C2 contract library, plus a published list of the modelled
    `core` items with each item's oracle.
  - Exit: `abs_small`, `clamp_builtin`, `digit`, `first_or` verified; the list is
    in the docs.
  - Move: **build**.
  - Progress: `iN::abs` and `Ord::clamp` are modelled. They are the first modelled
    methods whose failure is a **panic**, so the model carries a value and a
    `fails` predicate, and the executor emits the predicate as a panic obligation
    (`abs` fails at `MIN`, `clamp` at `lo > hi`; an out-of-range `x` is clamped,
    not an error — the probe corpus caught the first version that got this wrong).
    `everyday.rs` moved 10/21 -> 12/21 (`abs_small`, `clamp_builtin` verified);
    `realistic.rs` 399/739 -> 402/746 with the true/tripwire/panic fixtures.
  - Progress (cont.): `is_ascii_*` are modelled. They are the first modelled
    methods whose receiver is `&self`, so the operand is the *referent* of a
    reference the body materialises (`_3 = &_1`); the executor follows the
    reference for them and only them. All ten classes are `core`'s own range
    tests (`is_ascii_digit` is `b'0'..=b'9'`, `is_ascii` is `b < 128`), checked
    exhaustively against Rust's own `u8` methods. `digit` in `everyday.rs` moved
    to verified (10/21 -> **13/21**), and six fixtures with their tripwires are in
    `realistic.rs` (**405 of 752**).
  - Progress (cont.): `abs_diff` and `rotate_left`/`rotate_right` are modelled.
    `abs_diff`'s result is the *unsigned* magnitude even on a signed type
    (`i8::abs_diff(-128, 127)` is `255u8`), so the model widens both operands by
    their own sign to `w + 1` bits, subtracts there, and takes the absolute value
    with a *signed* sign test (the `w + 1`-bit range is exactly a signed one). The
    rotations reduce the amount modulo the width the way `core` does — a rotation
    by the width is the identity and by `w + 1` is by `1` — and since a modelled
    width is a power of two the reduction is one `and`, not a divider. Both are
    total (no panic), so they are plain values. Checked exhaustively over `u8`/`i8`
    against Rust's own methods (`abs_diff_and_rotations_agree_with_rust`), with
    three verified fixtures and two tripwires in `realistic.rs` (**409 of 758**).
  - Progress (cont.): `is_negative`/`is_positive` are modelled. Both are `bool`
    predicates, and the model is `core`'s own definition — `x < 0` and `x > 0`
    read *signed*. The signedness is the whole content: `i8::MIN` (`0x80`) is the
    largest unsigned byte, so an unsigned reading of the top bit would call it
    positive. They exist only on the signed types, so an unsigned receiver is
    refused rather than read. Checked exhaustively over `i8`/`i16` against Rust's
    own methods (`the_sign_predicates_agree_with_rust`), with `i8::MIN` named as
    the point an unsigned reading gets wrong; six fixtures with their tripwires
    are in `realistic.rs` (**433 of 803**).
  - Remaining: `<[T]>::first/get` (and the generic `<[T]>::len/is_empty`) are
    blocked on *monomorphisation*: `first_or<T>` is generic, so its element type
    has no width and the slice length is never seeded (the frontend refuses a
    receiver whose length it does not hold, which is the honest answer, not a
    bug). `slice::len`/`is_empty` *are* classified now (by path, so a `Vec::len`
    is not mistaken for a slice length), so they decide the moment a contract
    binds the slice.
- **C7. Arithmetic scale and speed.** · P0 · in progress · Kani, Boolector,
  Bitwuzla
  - Gap: `u32::wrapping_mul` is past the 32-bit model; `clamp_std` takes 9.9 s.
    Evidence: `hash_step` incomplete; `clamp_std` verified in 9.89 s.
  - Approach: word-level preprocessing before bit-blasting (rewriting, constant
    propagation, lazy multiplication abstraction), a better SAT encoding for
    multipliers, and a per-function **time** budget beside the size budget so a
    slow shape is reported rather than waited out.
  - Exit: `hash_step` decided; `clamp_std` under 0.5 s.
  - Move: **build**.
  - Progress: the exit criterion is **half met**, and the two halves are now
    clearly separable.

    *The coverage half is done.* `u32::wrapping_mul` was past the model because
    `MUL_MAX_WIDTH` was 16, so `hash_step` — the flagship `u32` example — was
    `incomplete`. Raised to 32, and the two costs were measured apart: the
    *value* (`wrapping_*`, which builds no predicate) is a plain `w`-bit multiply
    and settles in milliseconds, so `hash_step` now **verifies in 0.00 s** and
    every `u32` value product (`x * y`, `(x*y)*z`, `x * x`) verifies in under
    50 ms; the *widened* `2w == 64` failure predicate is built only where a family
    needs it, where a constant multiplier folds it (`x.saturating_mul(3)` verifies
    in 0.01 s) and a fully symbolic one answers `Unknown` after ~5 s rather than
    hanging. The bound is 32 and not 64 because `2w == 128` cannot be held — a
    `u64` product's predicate is refused, and a `u64` `wrapping_mul` is past the
    BDD wall anyway. See [`MUL_MAX_WIDTH`] and the `u32` product fixtures in
    `examples/mir_targets/realistic.rs`.

    *The latency half is not.* Measured on the release build, `clamp_std`
    (`x.max(lo).min(hi)`) still verifies in **9.8 s** (the criterion is "under
    0.5 s") while `clamp_builtin_reads` — the same 32-bit three-operand `clamp`
    query — verifies in **0.74 s**. So the `u32` three-operand shape remains the
    workload to profile, and the item stays open on that half: the approach is the
    word-level preprocessing and a per-function *time* budget named above.

    The third exit criterion, **"`u32` multiply-overflow guards decided at full
    width"**, is likewise open but *bounded*: the saturation idiom
    (`if b != 0 && a > u32::MAX / b { u32::MAX } else { a * b }`) and a plain
    `a * b` under a guard both report `incomplete` after ~4 s — the plain-`*`
    path's exact-division form at `u32` is past the diagram budget — rather than
    hanging. A per-function time budget is what would turn that ~4 s into a
    reported `incomplete` the caller can act on.


### Trust tracking (A1, tracked from Phase 1)

- **A1. Track the false-proof rate.** · P0 · **done** · —
  - Data: at least 11 false proofs were fixed between 2025-11-04 and 2025-11-12.
    All were caught, but at that rate a `verified` is not yet evidence to rely on.
  - Approach: a `SOUNDNESS.md` listing every false proof with date, commit,
    root-cause class and fixture. Pause feature work on any layer that produced a
    false proof in the last two weeks.
  - Exit for "beta": four weeks in a row with no new false proof, while the
    independent corpus keeps growing.
  - Move: **build**. `SOUNDNESS.md` carries the ledger: 28 MIR-frontend rows and
    16 engine/imperative rows — 44 in all, so the review's "at least eleven
    earlier false proofs" is now that many *dated rows* rather than a count (the
    seven commits the review named each contribute their own row). Every row has a
    **commit**, a **date** and a fixture. `tests/soundness.rs` checks it
    mechanically — every fixture must be a `#[test]` (not a same-named helper), in
    the file the cell names, every row must carry a commit and a `YYYY-MM-DD`
    date, and no date may be in the future. The clock restarts on each row; the
    most recent is 2026-11-16.

---

## Phase 2 — real crates (P1)

Exit: one real `no_std` crate with a dependency verified end to end with
`cargo verif`; Kani agrees on every function both tools decide.

- **C8. Cargo, multi-module crates and dependencies.** · P1 · todo · Kani
  (`cargo kani`)
  - Gap: the frontend runs `rustc --crate-type=lib` on one file, without
    `--extern`, so a crate that `use`s another crate, or a file whose
    crate-relative paths only resolve inside the crate, cannot be verified.
  - Approach: a `cargo verif` subcommand through `cargo rustc`/`RUSTC_WRAPPER`,
    emitting MIR for the target crate with its real flags. Dependency calls are
    answered through contracts (C2), not bodies.
  - Exit: one function in a real `no_std` crate with at least one dependency
    (an `embedded-hal` driver, say) verified end to end with `cargo verif`.
  - Move: **build**.
- **C9. References and aliasing.** · P1 · **done** (scalar referents) · Prusti
    (ownership), Creusot (prophecies)
  - Gap: reference arguments are refused ("no aliasing model"), yet `&`/`&mut`
    are the norm. **Built:** `&T`/`&mut T` arguments, writes through them,
    returned references and two-reference targets are modelled (see the `AGENTS.md`
    sections on the call boundary). A **scalar referent named in a contract** is
    now modelled too: a `&mut u16` argument's name denotes the value it addresses,
    the postcondition's name is the *final* value, and `old(name)` / `old(*name)`
    reaches the entry value (`*c` and `c` are one binding). What remains is the
    *general* case the ownership model buys (a reference to an aggregate named as a
    whole, aliasing between two arguments that may point at one place).
  - Exit: `fn bump(c: &mut u16)` with `ensures: *c == old(*c) + 1` verified and
    its caller verified modularly. **Met** -- `bump_scalar_ref_star` and
    `a_scalar_ref_caller` in `examples/mir_targets/realistic.rs`, pinned by
    `a_scalar_reference_argument_is_named_in_a_contract`.
  - Move: **done**.
- **C10. Generics, traits, closures and `dyn`.** · P1 · in progress · Kani
  (monomorphised instances)
  - Gap: generics are partly supported; "indirect call not modelled" ends the
    path; closures are out of reach. Trait-method identity and contract
    inheritance have started.
  - Exit: a closure-taking function (`v.iter().map(|x| …).sum()`) decided for a
    monomorphised instance.
  - Move: **build**.
- **C11. Heap containers.** · P1 · todo · Kani, Verus (`Seq`), Creusot
  - Gap: `Vec`, `String`, `Box`, symbolic-length slices. Evidence: `make`
    incomplete.
  - Approach: a bounded *sequence* model (length plus element array, from `mem`),
    exposed through contracts for `Vec::{new, push, pop, len, get, index}`.
  - Exit: `make` verified.
  - Move: **build**.
- **C12. A specification language that can say more.** · P1 · in progress · Verus,
  Creusot, Prusti, SPARK
  - `old(x)` in contracts; quantifiers; mathematical integers (a spec must not
    overflow itself); pure spec functions; ghost code and lemmas; `modifies`/frame
    clauses; type invariants. **Partly built:** `old` via a caller snapshot and a
    `wp::unchanged` query (the wp layer), and now in the **MIR frontend** too:
    `old(name)` / `old(*name)` reads a reference argument's *entry* value while a
    bare name reads its *final* value, so a two-state spec over a `&mut` argument
    is expressible (see C9). Bounded quantifiers in `quant`, frames derived by
    `wp::writes`.
  - Exit: a contract with a `forall i < n: a[i] <= m` verified.
  - Move: **build** (the `old` sub-item is done).
- **C13. Rust's own contract attributes as input.** · P1 · todo · the `contracts`
    crate
  - Approach: read `#[core::contracts::requires/ensures]`
    (rust-lang/rust#128044) as well as doc comments, keeping doc comments as the
    stable fallback.
  - Exit: a function carrying the attribute instead of a doc comment is verified.
  - Move: **build**. Without it, a home-grown syntax risks being absorbed by the
    language's own — the risk the README already names.

### Usability (U items, Phase 2 subset)

- **U1. Publish to crates.io, or stop saying `cargo add verif`.** · P1 · in
  progress · —
  - Gap: the README's Installation section says `cargo add verif`, but the crates
    are not on crates.io (the API answers "does not exist"). The packaging work is
    done (`scripts/publish.py`, `scripts/check_package.sh`, a tag-driven
    `.github/workflows/release.yml`), so what remains is the human step: create the
    `CARGO_REGISTRY_TOKEN` secret and push a `verif-arithmetic-v0.1.0` tag, then
    `verif-v0.1.0`. Until then, either publish or change Installation to a git
    dependency.
  - Exit: `cargo add verif` works, or the README points at a git dependency.
  - Move: **build**.
- **U2. `cargo verif`.** · P1 · todo · Kani (`cargo kani`)
  - Exit: `cargo verif --format json|sarif` plus a GitHub Action that annotates a
    PR.
  - Move: **build**.
- **U3. A counterexample becomes a test.** · P1 · in progress · Kani (concrete
    playback)
  - Gap: the replay machinery exists in `tests/mir.rs`; make it a user feature
    that emits a `#[test]`.
  - Exit: a reported counterexample is emitted as a compiling, failing-then-fixed
    `#[test]`.
  - Move: **build**.
- **U4. Readable counterexamples.** · P1 · in progress · —
  - Gap: a report says `v1:u8 = 224`, not `x = 224`. The `debug x => _1` names
    exist; the stable text dump has no per-statement spans, so line numbers come
    from the source scanner or the `rustc_public` path.
  - Exit: `x = 224` in a report.
  - Move: **build**.
- **U5. A test harness that never passes vacuously.** · P0 · done · —
  - Gap: about 21 tests in `tests/mir.rs` use
    `let Some(report) = verify_all() else { return }`, so without `VERIF_RUSTC`
    they *passed while checking nothing* (a skipped test reports `ok`).
  - Fix: the `rustc()` helper falls back to the `rustc` on `PATH`, because
    `--emit=mir` is a *stable* flag; `VERIF_RUSTC` still wins when set, so CI
    keeps exercising a nightly's dump format. The skip is reserved for a machine
    with no compiler at all. Measured: `env -u VERIF_RUSTC cargo test --features
    std --test mir` is the same 289 passed as with the variable set, so the 21
    tests run either way. ✅
  - Exit: `cargo test --features std` never passes vacuously.
  - Move: **build**.
- **U6. Documentation size.** · P1 · todo · —
  - Gap: the README is ~166 KB and `AGENTS.md` ~586 KB. Split into a short README,
    a user guide, `ROADMAP.md` (this file), `SOUNDNESS.md`, and design notes.
  - Exit: a README under ~30 KB with links to the rest.
  - Move: **build**.
- **U7. Proof caching.** · P1 · todo · —
  - Exit: unchanged MIR plus unchanged contracts reuses the verdict across runs.
  - Move: **build**.
- **U8. A public scoreboard.** · P1 · todo · Kani
  - Exit: `everyday.rs`, an SV-COMP-style set, and `verify-rust-std` functions
    scored for verif **and** Kani on the same inputs, updated by CI.
  - Move: **build**.

---

## Phase 3 — trust (P0 for adoption)

Exit: every `Unsat` behind a `verified` carries a checked certificate; the public
scoreboard against Kani is live.

- **A2. A certificate for every `Unsat`.** · P0 · todo · Kani, Verus, Prusti,
    Creusot (all trust their solver)
  - Approach: emit LRAT/DRAT from the CDCL solver and check it with an independent
    checker (`drat-trim`, ideally the verified `cake_lpr`); in CI re-derive BDD
    verdicts through the certifying SAT path.
  - Exit: a `verified` verdict whose SAT certificate is re-checked by an external
    tool.
  - Move: **build**. This is a way to be *ahead* of the competition on trust, not
    just catch up.
- **A3. Re-check selected obligations in Coq or Lean.** · P1 · todo · Coq/Rocq,
    Lean
  - Approach: `examples/comparison` already has Coq and Lean files; make "export
    this obligation as a Lean/Coq goal" a user-facing option.
  - Exit: one obligation from `everyday.rs` re-checked by a kernel.
  - Move: **bridge**.
- **A4. A trusted computing base and a semantics.** · P1 · todo · —
  - Write down what is trusted (parser, MIR-printer stability, executor, blasters,
    solvers), a short formal semantics of the supported MIR subset, and back both
    with mutation testing (exists) and external review before any 1.0 claim.
  - Exit: a `SECURITY.md`-style TCB document and an external review.
  - Move: **build**.
- **A5. A qualification path.** · P2 · todo · SPARK (the only one with
    qualification kits)
  - Approach: draft Tool Operational Requirements and a DO-330 TQL-5 / ISO 26262
    TCL plan. Together with Ferrocene, this is the most credible embedded-safety
    differentiator.
  - Exit: a drafted TOR and qualification plan.
  - Move: **build** (long term).
- **A6. Kani as a standing oracle for the frontend.** · P1 · todo · Kani
  - Approach: run Kani on every function in `everyday.rs` and `realistic.rs` in
    CI and require agreement whenever both decide. The engine already has Kani and
    Verus oracles; extend to whole-function verdicts.
  - Exit: a CI job that fails on any disagreement.
  - Move: **build**.

---

## Phase 4 — the high end (P2)

Exit: float and ISR fixtures verified; TOR and a qualification plan drafted.

- **C14. Floating point.** · P2 · todo · Kani, SPARK
  - Approach: bit-blast IEEE-754 `+ - * / < ==` with round-to-nearest-even; check
    exhaustively on a small format first. Freedom from NaN/Inf becomes an
    obligation. Matters because the flagship example is *flight control*.
  - Exit: an `f32` fixture verified.
  - Move: **build**.
- **C15. Unbounded proofs.** · P2 · todo · Verus, Creusot, Coq
  - Approach: **pick one and write it here.** (a) a small embedded SMT core with
    linear integer arithmetic, arrays and uninterpreted functions, or (b) a
    **bridge** that sends the obligation to Z3/CVC5 (the SMT-LIB export exists) or
    to Lean/Coq as an optional host-side path.
  - Exit: a "for all n" obligation decided.
  - Move: **bridge** (b) is the honest choice for a bit-blasting engine; (a) is a
    research project.
- **C16. `unsafe` and raw pointers.** · P2 · todo · Kani, VeriFast, RefinedRust,
    Verus
  - Target: *bounded* reads and writes through raw pointers within one allocation,
    plus obligations that a contracted `unsafe fn`'s preconditions hold at each
    call site.
  - Exit: a bounded raw-pointer fixture verified.
  - Move: **build** (the bounded subset only; **won't do** the separation-logic
    general case).
- **C17. Concurrency and interrupts.** · P2 · todo · SPARK (Ravenscar/Jorvik),
    Verus
  - Target: for the `no_std`/MCU story, the *interrupt handler* with shared state
    behind `critical_section` or atomics, not threads. Start with "a
    read-modify-write on an `Atomic*` preserves invariant I when interleaved at ISR
    boundaries", for a bounded number of interleavings.
  - Exit: an ISR fixture verified.
  - Move: **build**.
- **C18. Flow analysis (SPARK's other half).** · P2 · todo · SPARK
  - Gap: `gnatprove` checks data/information flow (`Global`, `Depends`,
    initialisation) before any proof. `rustc` covers initialisation; `Depends`
    does not exist in Rust.
  - Approach: cheap on top of symbolic execution — check that an input the contract
    declares independent does not appear in the support of the output term.
  - Exit: a `Depends`-style contract checked.
  - Move: **build**.

---

## Won't do

Stated plainly so the boundary is a decision rather than an omission. These are
reproducible inside verif only by becoming a different tool.

- **Arbitrary mathematics and induction (Coq/Lean parity).** Bit-blasting cannot
  reach it. **Bridge** through A3/C15b instead.
- **A general separation-logic heap model (`unsafe` at large).** VeriFast and
  RefinedRust do it; verif's bounded `unsafe` subset (C16) is the target.
- **Thread concurrency as a general problem.** The embedded shape (C17) is the
  one that matters for a `no_std` verifier.
- **Qualification *evidence* without a plan.** A5 drafts the plan; shipping the
  evidence is a multi-year activity and is not claimed.

---

## Where this comes from

The items and their exit criteria are the review on PR #8
(`analisaperlengkapan`, 2026-11-13): editions (§2, E items), coverage in priority
order (§3, C items), trust (§4, A items), usability (§5, U items), the per-competitor
gap table (§6), and the phased exit criteria (§7). The comparison to Kani, Verus,
Prusti, Creusot, Coq/Rocq, Lean, SPARK, Flux, VeriFast/RefinedRust/ESBMC and the
`contracts` crate is in §6 of that review and is summarised in the **Competitor**
field of each item.

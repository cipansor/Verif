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

The corpus scoreboard, re-measured on this branch. Each row is a command whose
output decides the number, so the table is a measurement rather than a claim:

| Corpus | Command | Verified / total |
|---|---|---|
| `examples/mir_targets/actuator.rs` | `cargo run --features std --example mir_coverage -- examples/mir_targets/actuator.rs` | 18 / 33 |
| `examples/mir_targets/realistic.rs` | same, `realistic.rs` | 630 / 1148 |
| `examples/mir_targets/everyday.rs` | same, `everyday.rs` | **18 / 21 (86%)** |

This table is the *current* measurement and is the only number to quote. The
`N of M` figures inside the per-item progress notes below are the value *at the
moment that item landed* -- each was the running total when it was written, and
they are kept as a history of how the corpus grew rather than as the present
state. Re-run the command above rather than reading a note for the current
number.

`everyday.rs` is the honest one: ordinary Rust written by an external reviewer,
not shaped for the tool. `realistic.rs` is a regression corpus (about a third of
it is adversarial fixtures), so its high percentage does not measure coverage of
ordinary code. Phase 1 is defined on `everyday.rs`.

**The three functions that remain `incomplete`** are each blocked by a distinct,
confirmed-hard limitation — measured, not assumed. None is a bug, and none is a
small change:

- `div_unwrap` (`n.checked_div(d).unwrap()`, `ret <= n`) needs the **u32 divider**,
  whose BDD is exponential at 32 bits. The same query is still undecided after
  ~186 s with `MAX_APPLY_STEPS` raised 32× (to `1 << 24`) and after 5.7 s with the
  SAT conflict budget raised to 20 000 000 — so it is an engine wall (C7), not a
  budget knob. `n / d` at `u32` is equally undecided, which is the same fact.
- `sum_iter` (`v.iter().sum()`) is `incomplete` because its length is **unbounded**
  (`requires: true`). The `iter`/`sum` path is modelled now (C11 symbolic-length
  iteration), and a slice sum is unrolled to `MAX_SYMBOLIC_LEN` steps guarded by
  `k < len` — exact only when the precondition *proves* `len <= 8`. An unbounded
  length cannot be unrolled (a shorter unroll would silently miss elements, a wrong
  value), so `sum_iter` stays an honest refusal. A **guarded** sum decides:
  `symbolic_sum_no_overflow` (`len <= 4`, elements `<= 10`) **verifies** (the sum
  cannot overflow — a real panic-freedom proof over a runtime-length slice),
  `symbolic_sum_tripwire` (bounded length, unbounded elements) is **refuted** with
  an overflow witness, and `symbolic_sum_unbounded_refused` is the honest refusal.
  So the entry is decided *for the guarded shape*; `sum_iter` itself is a
  length-unbounded refusal, not an unmodelled `sum`.
- `tri` (`s += i` over `0..=n`, `n <= 100`, `ret <= 5050`) needs an **inductive**
  loop invariant, and the invariant that is inductive for a running sum is
  *nonlinear* (`s <= i(i+1)/2`). `s <= 5050` is not inductive (from `s == 5050`
  and `i == 100` the sum is `5150`), which is why the loop reports a spurious
  panic rather than a missing contract. This is C12 (the contract language's
  expressiveness), not a frontend gap.

---

## Phase 1 — everyday Rust (P0)

Exit: `everyday.rs` at least **80% decided** (17 of 21 — **met**, at 18 of 21),
and four weeks in a row with no new false proof while the independent corpus
keeps growing.

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
  - Gap: the *closure-taking* methods (`map`/`map_err`/`and_then`/`unwrap_or_else`)
    are unmodelled because a closure body is an indirect call the frontend does not
    inline -- that is C10 (closures), not this item. `?` is modelled
    (`TryBranch`/`FromResidual`); `unwrap`, `unwrap_or`, `unwrap_or_default`,
    `expect`, `ok_or`/`ok`/`err`, `is_some`,
    the enum-return discriminant methods and bare payload reads are modelled (see
    the progress notes). Evidence: `checked_or_max` verified, `div_unwrap`
    incomplete (the divider wall, not the `Option`).
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
  - Remaining: `map`/`map_err`/`and_then`/`unwrap_or_else` (closures). `ok_or`/`ok`/`err`
    are now modelled (see below), and the `?` operator is modelled (see the last
    progress note), so both are off this list.
  - Progress (the `?` operator): `expr?` is modelled. The desugaring is
    `<T as Try>::branch(expr)` producing a `ControlFlow<Residual, T>`, a
    `switchInt` on its discriminant, and — on the `Break` arm — a
    `FromResidual::from_residual` call that re-wraps the error as the function's
    return enum. Both calls are modelled (`Intrinsic::TryBranch` /
    `Intrinsic::FromResidual`, answered by the executor's `try_branch` /
    `from_residual` from the receiver's enum stores, exactly as the `Option`
    methods are). `branch` writes the `ControlFlow`'s tag — `Continue` iff the
    receiver is on its success variant (`Ok` = 0, `Some` = 1) — and both payloads
    (the success value, and the error value on the failure variant); the
    `(_2 as Continue).0` / `(_2 as Break).0` downcasts then resolve through
    `variant_index`'s `Continue`/`Break` numbering. The residual's own tag is fixed
    by the receiver type (`Err`/`None`), so it is not stored; `from_residual`
    re-numbers it for the *return* enum (read from the call's self type) and moves
    the error value onto the `Err` payload. A locally constructed `Ok`/`Err`/`None`
    receiver has a *known* tag, so the branch is decided statically (the
    `smt::evaluate` known-tag arm). Nineteen fixtures in `realistic.rs`
    (verify/tripwire pairs on both paths for both families, the three known-tag
    receivers, a chained pair, a two-branch pair and a cross-error-type pair),
    pinned by `the_try_operator_decides_on_both_paths`. `realistic.rs` **472 of
    881 -> 491 of 918**.
  - Progress (enum-return contract): a contract on an `Option`/`Result`-returning
    function can now name the **discriminant** methods — `ret.is_ok()`,
    `ret.is_some()`, `ret.is_err()`, `ret.is_none()`. A function returning an enum
    has no single return *word*, so a bare `ret <= n` is refused; the four methods
    read the return place's **tag**, which the executor now passes as the return
    word (`Env::tag_value(0)`), and the discriminants come from the type
    (`spec::enum_ret_discriminants`: `Ok` is 0 / `Err` is 1, `Some` is 1 / `None` is
    0, or a declared enum's own layout). They are *total* over the tag, so unlike
    `ret.Ok` — which names a payload that exists on only one variant, and so needs
    the postcondition guarded on the discriminant — they are admitted without a
    payload guard. A non-enum return refuses them (a skip, never a verdict against
    a fabricated tag). This also needed the parser to accept a variant name with a
    generic list containing a space (`Result::<u8, u8>::Ok`, which rustc prints with
    a space after the comma). The same four methods also read an enum-typed
    **argument** (`requires: r.is_ok()`), from the tag the binder records under
    `r__tag` and the discriminants it records as variant constants. Nineteen
    fixtures in `realistic.rs` (true/tripwire pairs on both tags for `ret` and for an
    argument, a pass-through, a `match`, and the non-enum refusal), pinned by
    `an_enum_return_contract_can_name_the_discriminant_methods` and by two
    toolchain-free `spec` unit tests. `realistic.rs` **439 of 813 -> 448 of 832**.
  - Progress (the `Option`↔`Result` conversions): `Option::ok_or`,
    `Result::ok` and `Result::err` are modelled. Each is *total* for a scalar
    payload and moves one payload across the tag: the result's tag is the
    receiver's reinterpreted (`Ok` and `Some` are discriminants 0 and 1, so
    `1 - tag` for `ok_or`/`ok`), while `err` *keeps* the tag (`Err` is already the
    payload-carrying variant of a `Result`, and the result is an `Option` whose
    `Some` is that discriminant). The moved payload is recorded under the
    discriminant the consuming `switchInt` selects -- `ok_or` writes *both*
    payloads, `Some`'s onto `Ok` and the error argument onto `Err`, because
    `ok_or` is the one conversion with two inputs. Each reads the type it *drops*
    (the `ok_or` argument, `ok`'s `Err` payload, `err`'s `Ok` payload) through the
    same `has_drop_glue` check `unwrap_or` uses, so a type with an unmodelled
    destructor is refused rather than assumed harmless. One parser-side finding:
    `ok_or` is printed with a *method* turbofish (`Option::<u8>::ok_or::<i32>`), so
    the classifier's last-segment read had to skip a `<…>` segment to find the
    method name -- without that the call was reported unmodelled, and the fix is
    strictly safer because a method name never begins with `<`. The first cut of
    the executor also stored the *error argument* as the `Ok` payload (it read the
    single "moved" operand), which made the payload's width 32 for a `u8` receiver
    and refuted every true payload contract; the fixtures' `_moves_the_payload`
    pairs are what caught it. Eighteen fixtures in `realistic.rs` (true/tripwire
    pairs on both tags for each of the three, and a payload round-trip through
    `unwrap` for each), pinned by
    `the_option_result_conversions_decide_and_move_the_payload` and by a
    toolchain-free `classify` unit test (including the turbofish).
    `realistic.rs` **448 of 832 -> 457 of 850**.
  - Progress (PR #8 review round: three findings). Each was reproduced against
    real rustc before being fixed, and each fix is pinned by a true/tripwire pair.
    - **A `&mut bool` postcondition lost its value.** A `bool` target is a
      `Val::Bool` *predicate*, not a `Val::Sym` word, and the reference-final
      collection kept only the `Sym` arm -- so `ensures: c == true` after
      `*c = true` was refused as an *unknown name*. The predicate is now widened to
      a one-bit word, exactly as a `bool` `ret` is. Three fixtures
      (`set_bool_ref`, `keep_bool_ref`, and the false `a_bool_ref_write_cannot_prove_this`),
      pinned by `a_mutable_bool_reference_postcondition_reads_its_final_value`.
    - **A conversion over a *constructed* variant was refused.** A locally
      constructed `None`/`Err`/`Ok` records only the payload that variant carries,
      so `None::<u8>.ok_or(e)` had no `Some` payload to move and the call was
      reported "on a receiver whose payload is not modelled". The inactive
      variant's payload is unreachable on such a path (the tag is a *known*
      discriminant), so it is now left *unbound* rather than refused -- the same
      treatment a `None` construction gets. A *symbolic* tag still refuses, so no
      fabricated value is bound on a path that could reach the payload. Eight
      fixtures (both constructed directions for each of the three, true and
      tripwire), pinned by
      `the_option_result_conversions_handle_constructed_variants_and_grouping`.
    - **Grouping and negation of an enum predicate was unreadable.** `(ret.is_ok())`
      and `!x.is_none()` carry no comparator, so `paren_is_predicate_from` and
      `bang_is_predicate` routed them into arithmetic and the contract was skipped.
      Both lookaheads now recognise the `base.method()` shape; whether the base
      really names an enum is still decided when the predicate is parsed. Eight
      fixtures plus a toolchain-free `spec` unit test
      (`a_grouped_or_negated_enum_method_is_a_predicate`).
    `realistic.rs` **457 of 850 -> 467 of 869** (11 verify, 11 refute).
  - Progress (a bare payload read on an enum return): `ret.Ok`, `ret.Some`,
    `ret.Err` and a *user* enum's variant (`ret.Data`) are modelled. A payload
    exists only on the variant's paths, so the clause naming it is **guarded on
    the discriminant** (`tag == disc => clause`): on the other variant's paths it is
    vacuously true, which is the only meaningful reading. Binding the payload with
    no guard would compare it on *every* path, against a value it does not have —
    a wrong value, not a weaker proof. The guard is applied per top-level `&&`
    conjunct (`Parser::guard_ret_payloads`), so `ret.Ok <= n && ret.Err <= m`
    checks each payload only on its own variant's paths. The payload variable is
    the executor's own (`ret_payloads`, collected from `payloads`/`fields` under
    local `_0` keyed by discriminant), so the contract's `ret.Ok` and the body's
    `((_0 as Ok).0)` are one value; the layout is one lookup
    (`spec::ret_enum_def`), shared with `ret.is_ok()` so the numbering and the
    payload width cannot drift. The *probe* binds only the variants a contract
    actually names (`names_ret_variant`), at a throwaway slot above the run's, so a
    contract that never mentions a payload pays nothing and a payload with no
    bit-vector width is refused only when it is asked for. Twelve fixtures in
    `realistic.rs` (true/tripwire pairs for `Ok`/`Some`/`Err`/a user enum, a
    branch-vacuity pair, and two refusals — a non-enum return and a unit variant),
    pinned by `an_enum_return_contract_can_name_a_payload`. This closes the last
    named C2 sub-item; `realistic.rs` **467 of 869 -> 472 of 881**.
  - Progress (`unwrap_or_default`): `Option::unwrap_or_default` and
    `Result::unwrap_or_default` are modelled. Both are `unwrap_or(T::default())`,
    so they reuse the `unwrap_or` arm with the default supplied by the model
    rather than by an argument: for every scalar payload the tool models,
    `T::default()` is the zero of the payload's own width (`0u8`, `0i32`,
    `false`), so the failure variant yields that word. A payload with no bit width
    (a struct) is refused rather than given a zero it may not have. Both are
    total -- no panic obligation -- and both are pinned by a `None`/`Err` true
    entry and a false twin (the `Some`/`Ok` path can carry any payload, so a fixed
    value is refuted). Four fixtures in `realistic.rs`, pinned by
    `option_unwrap_or_default_is_the_payload_or_zero`; the corpus carries the
    `Option` and `Result` directions.
  - Guard (`str` shadowing): a user type may shadow a primitive name, and rustc
    prints a crate-root type as the bare name, so `pub struct str { .. }` is
    spelled `&str` exactly as the primitive is. The primitive `str` length is
    therefore bound only when no declared layout names `str`
    (`struct_lookup(..).is_none()`); a user `str` reaches the struct branch and
    its fields bind. Pinned by `a_user_type_named_str_is_not_the_primitive_str`,
    which asserts both directions -- the user field resolves and refutes a fixed
    value, and the primitive length is still a symbolic input.
  - `Option::or`/`Option::and`: total, closure-free. Each returns one of its two
    `Option`s by the receiver's tag, so the result tag is an `ite` on it and both
    payloads are carried; `or` is the receiver on `Some` and the argument on
    `None`, `and` the mirror. The dropped operand's payload type drives the glue
    check (the argument for `or`, the receiver for `and`), so a `T` with an
    unmodelled destructor is refused. Eight fixtures (four true, four tripwires),
    pinned by `option_or_and_are_total_and_select_the_right_operand`.
  - **A chained `or`/`and` selected the wrong element (false proof, fixed).** The
    element-identity store was *flat* — a combinator recorded one leaf or a
    leaf-plus-condition — so `a.first().or(b.first()).or(c.first()).unwrap()` lost
    the inner `or` and the outer combinator read the missing receiver identity as
    permission to take the argument's element: with `a[0]==5`, `b[0]==7`, `c[0]==9`
    it **verified** `ret == 9`, which Rust never returns (it returns `a[0] == 5`).
    The identity is now a compositional tree (`ElemId::Leaf | Select`); a missing
    operand identity is substituted **only** when the receiver's tag proves that
    operand is not the selected one, so a symbolic tag with a missing identity
    leaves the deref unknown rather than wrong. The tree also carries the element's
    **sign**, so a conditional choice between `&[i8]` elements compares and divides
    signed (the old code hard-coded `Sign::Unsigned`). Fixtures `chained_or_selects_the_first`,
    `and_with_a_conditional_argument`, `signed_or_element_is_signed` and their
    `_cannot_prove_this` twins.
  - **`and` with a different-width argument (ill-formed query, fixed).** `Option<T>::and<U>`
    permits a different payload type and returns the *argument* on `Some`, so its result
    element is always the argument's. Building a `Select` over the receiver's (`u8`) and
    the argument's (`u16`) slice elements asked `smt::ite` for equal widths and marked the
    query ill-formed, so `*a.first().and(b.first()).unwrap()` was `incomplete` even with
    both slices nonempty. `and` now carries the argument's identity alone (exact and
    width-safe), which also fixes the scalar-receiver case (`Option<u8>.and(&[u8])`), where
    the old `(None, Some(a))` arm applied `or`'s "only when the tag proves it" rule to a
    combinator that selects the argument unconditionally. Fixtures
    `and_different_width_deref`, `and_scalar_receiver_ref_argument` and their twins.
  - Remaining: `map`/`map_err`/`and_then`/`unwrap_or_else` (closures). The `?`
    operator is modelled (see the `?` progress note above).
- **C3. Ranges and `for` loops.** · P0 · done · Kani, Verus, Prusti
  - Gap: `RangeInclusive::new`, `Range`, `Iterator::next` unmodelled, so the
    commonest loop in Rust is out of reach. Evidence: `tri` incomplete.
  - Approach: model `Range`/`RangeInclusive` as structs, `next` as a modelled
    intrinsic, recognise the `for` desugaring, reuse the loop machinery.
  - Exit: a `for` loop over a range verified with an `invariant:`; a missing
    invariant reported as *a missing invariant*, not "unmodelled". ✅ (The
    invariant must be inductive — see the progress note; `tri`'s own contract is
    not, so `tri` stays `incomplete` for that honest reason rather than for an
    unmodelled construct.)
  - Move: **build**.
  - Progress: the desugaring is **built**. `RangeInclusive::new`/`Range::new`,
    `IntoIterator::into_iter` and `Iterator::next` are modelled
    (`intrinsics::Range`/`RangeMethod`, answered by `range_method` from the
    range's struct fields, with `core`'s `forward_overflowing` boundary
    reproduced exactly), and a `for` loop now decides through the existing
    machinery — `for i in 0..=n { s += i }` verifies with `unwind: 4`, and a loop
    whose body is decided by an **inductive** invariant (`s = i.min(5050)`)
    verifies with `invariant: s <= 5050`, its false twin refuted
    (`the_for_loop_range_desugaring_is_modelled`).
  - The invariant has to be **inductive**, and `everyday.rs`'s `tri` is not.
    `invariant: s <= 5050` over a body doing `s += i` is not inductive (from
    `s == 5050` and `i == 100` the sum is `5150`), so a loop whose carried state is
    the *running sum* cannot be proved with a constant bound. The fixture that
    exercises the invariant path uses `s = i.min(5050)` (inductive); `tri` stays
    `incomplete` for the honest reason that no contract it declares is inductive.
    See `AGENTS.md` ("The `tri_invariant` fixture had been passing *because of*
    the bug") for why the first version of this note was wrong.
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
- **C6. The everyday `core` surface.** · P0 · **done** · Kani, Verus (`vstd`)
  - Gap: `Ord::min/max/clamp`, `PartialEq`/`PartialOrd` comparisons,
    `iN::abs`, `abs_diff`, `rotate_*`, `is_ascii_*`,
    `is_negative`/`is_positive`, `<[T]>::len/is_empty/first/get`. Evidence:
    `abs_small`, `clamp_builtin`, `digit`, `first_or` incomplete. All but
    `first_or` are now modelled (`min`/`max`, `From`/`Into`, `clamp`,
    `abs`, `abs_diff`, `rotate_*`, the `is_ascii_*` classes, the sign predicates,
    `slice::len`/`is_empty`, and `slice::first`/`get`). `first_or` now decides
    too: it is *generic* (`<T: Copy>`), and the earlier note that a generic slice
    needs monomorphisation was wrong for the *length* half — `v.len()`/`v.is_empty()`
    read only the length, which is a `usize` input whatever `T` is, so the length is
    bound even when the element width is unknown (the `0` sentinel in
    `exec::Indexed::elem_w`). Every *element* operation on a `&[T]` stays refused,
    which is the honest split; see the progress note below.
  - Also modelled since: `signum`, `div_euclid`/`rem_euclid`, `div_ceil`,
    `midpoint`, `next_multiple_of`, `ilog2`/`ilog10`, the `next_power_of_two`
    pair, and `str::len`/`str::is_empty` — see the progress notes below.
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
  - Progress (cont.): `<[T]>::first` and `<[T]>::get` are modelled for a
    *concrete* slice. They produce `Option<&T>`, so the payload is a reference,
    not a value: the model writes the `Option`'s tag as a *predicate* (`len == 0`
    for `first`, `k >= len` for `get(k)`, so `unwrap`'s panic obligation is real)
    and records the payload as the slice's *own* element variable — the same one
    `xs[k]` names — so `*xs.first().unwrap()` and `xs[0]` agree by construction.
    The reference's deref (`*_2`) resolves through a new `Env::slice_elem_ref`
    store; both `unwrap` and the `match` desugaring (which reads the payload
    through a downcast temp, `_4 = copy ((_2 as Some).0)`) carry the element to
    their destination, so the two spellings decide alike. `get`'s index must
    be a *constant* (a slice's length is symbolic, so a symbolic index has no
    finite domain and reading "some element" would be a wrong proof). `first_or`
    stays incomplete because it is *generic* (`<T: Copy>`) — that is C10, not this
    item — and the earlier note that `first`/`get` were "blocked on
    monomorphisation" was wrong for a concrete `&[u8]`. Seven fixtures (four true,
    two tripwires, one panic) plus three `match`-form fixtures are in
    `realistic.rs` (**496 of 927**), pinned by
    `slice_first_and_get_reach_the_slices_own_element` in `tests/mir.rs`.
  - Progress (cont.): the remaining total `core` value methods are modelled:
    `signum` (`-1`/`0`/`1`, signed-only — the signedness is the content, since
    `i8::MIN`'s `0x80` is the largest *unsigned* byte); `reverse_bits` (a shift-OR
    fold, both signednesses); `swap_bytes` (a rotation by `w/2` *bits*, which is
    the byte reversal — the first cut used `w/2 * 8` and the differential test
    caught it); `to_be`/`to_le` (a byte swap or the identity according to the
    *target's* endianness, read from `cfg!(target_endian)`; `core` has no `to_ne`
    *value* method, only `to_ne_bytes`, so only two variants exist); the ASCII case
    conversions `to_ascii_uppercase`/`to_ascii_lowercase` (`u8`-only, a range test,
    and `&self`, so the executor follows the reference as it does for `is_ascii_*`);
    and `is_multiple_of` (unsigned-only, `a % b == 0` with `b == 0` defined as `a ==
    0`, so both the `b != 0` guard and the `|| a == 0` disjunct carry — the engine's
    `urem(x, 0)` is a *defined* value, not a hole, so the guard is what makes the
    corner exact). The `_bytes` byte-order forms return an array, not an integer, so
    they stay unmodelled rather than written as a word. `div_euclid`/`rem_euclid`
    and `div_ceil` (unsigned) are the division shapes that are not the truncating
    `/`/`%`; each is a *value-and-panic* pair, because each panics on a zero
    divisor (`div_euclid`/`rem_euclid` also on `MIN / -1`), and modelling it as
    total would hide a panic. The Euclidean quotient adjusts the *other* way from
    the truncating one when the remainder is negative (`-7.div_euclid(3)` is `-3`),
    which the first cut got backwards and the differential test caught. On an
    *unsigned* receiver the remainder is never negative, so the Euclidean and
    truncating forms coincide and the model falls back to the plain unsigned
    divider — the sign is the whole difference, so the unsigned spelling is now
    modelled rather than refused. All are
    checked against Rust's own method over the whole `u8`/`i8` domain, with the
    panic predicate compared at *every* input. Twenty-six fixtures (fifteen true,
    eleven tripwires) are in `realistic.rs` (**553 of 1019**), pinned by
    `the_next_core_value_methods_are_modelled_with_their_tripwires` in
    `tests/mir.rs` and by `the_new_shapes_are_modelled_only_on_the_types_that_have_them`
    (the type-membership directions) in `src/mir/intrinsics.rs`.
  - Progress (cont.): `midpoint`, `next_multiple_of`, `ilog2` and `ilog10` are
    modelled. `midpoint` is total and computed *without* a sum at the operand
    width — unsigned `(a & b) + ((a ^ b) >> 1)`, and for the signed case that same
    form plus a `+1` correction when the result is negative and `(a ^ b)` is odd,
    which is the truncation toward zero Rust's `iN::midpoint` documents (the floor
    would give `-4` for `(-5).midpoint(-2)` where Rust gives `-3`). Checked
    exhaustively against `core` over all of `u8`/`i8`. `next_multiple_of` is
    unsigned-only (the signed spelling is unstable on this toolchain, so a signed
    receiver is refused) and is a *value-and-panic* pair: the value is
    `a + (b - a % b) % b` and the panic fires where `checked_next_multiple_of`
    returns `None` (a zero divisor, or an overflow), checked together over the
    whole `u8` domain. `ilog2`/`ilog10` exist on both signednesses and are
    value-and-panic too: the value is built at the operand width and zero-extended
    to the `u32` result, and the panic fires on a non-positive argument. The
    executor labels an `ilog` result *unsigned* — its type is `u32` whatever the
    operand's — and gives the panic a kind-specific message rather than calling a
    logarithm an "overflow". Twenty-six fixtures (sixteen true, seven tripwires,
    three panic) are in `realistic.rs` (**525 of 975**), pinned by
    `the_new_num_methods_verify_and_their_tripwires_refute` in `tests/mir.rs` and
    by `the_new_shapes_are_modelled_only_on_the_types_that_have_them` in
    `src/mir/intrinsics.rs`.
  - Progress (cont.): `next_power_of_two` and `checked_next_power_of_two` are
    modelled — the rounding sibling of the already-modelled `is_power_of_two`, and
    the second half of the `next_multiple_of` family. Both are unsigned-only (the
    signed types have no such method) and both are built by the classic
    smear-and-add: `p = x - 1` with the `x <= 1` case forced to `0` (core's own
    pre-step), `p |= p >> 1; p |= p >> 2; …` to smear the highest set bit down,
    then `p + 1`. The `- 1` is load-bearing — without it an *already*-power-of-two
    input would smear to `2^w - 1` and round to `0` instead of staying itself — and
    the `x <= 1` guard is what keeps `0.next_power_of_two()` at `1` rather than the
    all-ones wrap of an unguarded `x - 1`. `next_power_of_two` is a
    `ValueOrPanic` (the result does not fit for `x > 2^(w-1)`, so `129u8` panics in
    a checked build and wraps to `0` otherwise); `checked_next_power_of_two` is
    the `Option` counterpart, whose tag is a *term* (`1` where the value fits, `0`
    where it does not), so the `switchInt` consuming it takes the right arm on each
    path. The failure predicate is written as `value == 0` on the *computed value*,
    which is exact at the boundary (`x == 2^(w-1)` fits and yields `2^(w-1)`, not
    `0`). Checked exhaustively against Rust at 1/4/8/16 bits
    (`the_next_power_of_two_pair_agrees_with_rust`), with the oracle computed at
    the *model's* width (a `u8` oracle has a different overflow boundary from a
    four-bit model — the first cut used the host method and failed at 4 bits).
    Eleven fixtures (seven true, three tripwires, one panic) are in `realistic.rs`
    (**532 of 986**), pinned by `the_new_num_methods_verify_and_their_tripwires_refute`
    in `tests/mir.rs`.
  - Progress (cont.): `iN::unsigned_abs` is modelled — the same magnitude `abs`
    computes, read as the *unsigned* type (`i8::unsigned_abs(-128)` is `128u8`),
    and *total* where `abs` panics: at `MIN` the truncating `0 - x` is exactly the
    magnitude, the bit pattern the signed `abs` cannot represent. So it is a plain
    value with no failure predicate, labelled unsigned on the way out so `128` is
    not read back as `-128`; a model that gave it `abs`'s panic, or read the
    magnitude signed, fails at the `MIN` fixture. Checked exhaustively against
    Rust at 1/4/8/16 bits (`the_unsigned_abs_agrees_with_rust`), with five fixtures
    (three true, one tripwire, one `requires: true` panic-freedom control) in
    `realistic.rs` (**535 of 990**), pinned by
    `abs_and_clamp_are_modelled_with_their_panics` in `tests/mir.rs`.
  - Progress (cont.): `iN::checked_next_multiple_of` is modelled — the `Option`
    counterpart of the panicking `next_multiple_of`, with `None` exactly where the
    plain call would panic (a zero divisor, or an overflow), so its tag is the
    negation of the same failure predicate and no panic obligation is emitted. Four
    fixtures (three true, one tripwire) in `realistic.rs` (**538 of 994**), pinned
    by `the_new_num_methods_verify_and_their_tripwires_refute`; checked
    exhaustively against `core`'s own `checked_next_multiple_of` over the whole
    `u8` domain (`checked_next_multiple_of_agrees_with_rust`).
  - Progress (cont.): `iN::checked_ilog2`/`checked_ilog10` are modelled — the
    `Option` counterpart of the panicking logarithms, with `None` exactly where the
    plain call would panic (a non-positive argument), and the same `u32` payload as
    the plain form (so the payload is zero-extended to the destination's width, the
    one `checked_*` shape whose result width differs from the operand's). Seven
    fixtures (five true, two tripwires) in `realistic.rs` (**543 of 1001**), pinned
    by `the_new_num_methods_verify_and_their_tripwires_refute`; checked
    exhaustively against `core`'s own `checked_ilog2`/`checked_ilog10` over the
    whole `u8`/`i8` domain, tag and payload together
    (`the_checked_logs_agree_with_rust`).
  - Progress (cont.): `iN::cast_unsigned`/`uN::cast_signed` are modelled. The
    value is the operand unchanged — a same-width signedness cast is a
    re-interpretation, not a conversion — so the model carries only the *type*:
    it is the one shape whose result sign is the *opposite* of the operand's, and
    the executor reads it from the call's destination type rather than deriving it
    from the operand. Five fixtures (three true, two tripwires) in `realistic.rs`
    (**546 of 1006**), pinned by
    `the_next_core_value_methods_are_modelled_with_their_tripwires`; the value is
    checked exhaustively against Rust's own methods over the whole `u8`/`i8`
    domain (`the_signedness_casts_agree_with_rust`).
  - Progress (cont.): the inherent `iN::pow` is modelled as `Intrinsic::PowPanic`.
    The four *families* (`wrapping_pow`/`saturating_pow`/`checked_pow`/
    `overflowing_pow`) express overflow as a value, but the plain `pow` **panics**
    (`assert!` on overflow) and has no family-prefixed spelling to fall back on, so
    it is its own shape yielding a reachable-panic obligation. A model that wrapped
    or clamped would *hide the panic* — the one thing this frontend must never do —
    so the fixtures pin the polarity: two verify (in-range and exact boundary), two
    must fail on the `pow` overflow panic. Checked exhaustively against Rust's own
    `checked_pow` over the whole `u8`/`i8` base domain (`the_plain_pow_agrees_with_rust`),
    and pinned end to end by `the_plain_pow_panics_where_it_overflows`.
  - Progress (cont.): `iN::from_be`/`iN::from_le` are modelled — the associated
    functions that invert `to_be`/`to_le` on the same target, so they classify to
    the same byte-order shapes (`from_be` on a little-endian target is the same
    swap as `to_be`, and the `to_be`/`from_be` round trip is the identity). Six
    fixtures (three true, three tripwires) in `realistic.rs` (**551 of 1015**),
    pinned by `the_next_core_value_methods_are_modelled_with_their_tripwires`.
  - Progress (cont.): `PartialEq::eq`/`ne` and `PartialOrd::lt`/`le`/`gt`/`ge` are
    modelled — the six comparison operators in their *trait-method* spelling, the
    same shape of exception as `Ord::min`/`max`. The dump spells a call `<u8 as
    PartialOrd>::lt` (no `core::num::<impl …>` path), so the model is a *fallback*
    behind the same-dump lookup, admitted only when the trait path is the standard
    library's and the self type is a primitive; a local trait in a module
    (`cmp_shim::PartialOrd`) is refused by the path, and a crate-root trait that
    prints bare is answered by its own body first. Both operands are taken by
    reference (`&self`/`&other`), so the executor follows the references to their
    referents, the same step the `is_ascii_*` receivers already take. The value is
    exactly the comparison the operator builds, so a method call and its operator
    form cannot disagree; the ordering picks `slt`/`sle`/`sgt`/`sge` on a signed
    type and `ult`/`ule` on an unsigned one, with `i8::MIN` as the separating
    point. Checked exhaustively against the operators over all of `u8`/`i8`
    (`the_partial_cmp_methods_agree_with_the_operators`), with eight fixtures
    (five true, one local-trait pair, two tripwires) in `realistic.rs` (**559 of
    1027**), pinned by
    `partial_cmp_methods_are_modelled_and_a_local_trait_still_wins`.
  - Progress (cont.): `Ord::cmp` is modelled — the third method on the same
    `Ord` trait, admitted by the same narrow rule (`is_ord_callee`: the standard
    library's `Ord` path and a primitive self type), and the *first* modelled
    shape whose result is a three-variant enum rather than a value, an `Option` or
    a `(value, flag)` tuple. Its result is `core::cmp::Ordering`, whose
    discriminants are the *signed* `i8` values `Less` = -1, `Equal` = 0, `Greater`
    = 1, so the executor writes the destination's *discriminant* (the variants are
    unit, so there is no payload) and the `switchInt` on `discriminant(_)` decides.
    A three-way comparison is the sign of `x - y`, so the tag is
    `ite(slt(x, y), Less, ite(sgt(x, y), Greater, Equal))` — the two comparisons the
    `PartialOrd` operators already build, at the operands' common width and sign —
    and the tag is built from the *eight-bit two's-complement pattern* of the
    constants, because `smt::word` refuses the out-of-range `-1`. Both operands are
    `&Self`, so the executor follows both references to their referents, the same
    step the `PartialEq`/`PartialOrd` receivers take; an operand whose sign cannot
    be read is *refused*, because ordering `i8::MIN` unsigned places it above every
    other value (a wrong ordering, not a weaker proof). The tag width is
    `Ordering`'s own `i8` discriminant, not the destination local's declared width,
    so a locally built `Ordering` and a `switchInt` against rustc's `-1`/`0`/`1`
    arm constants agree. Six fixtures (five true, one tripwire) in `realistic.rs`
    (**564 of 1035**), pinned by `ord_cmp_returns_the_ordering_enum` in
    `tests/mir.rs`; the classify guard (the standard paths admitted, a foreign
    `m::Ord`/`MyOrd`/`ord_shim::Ord` refused, and `cmp` not mistaken for `min`) is
    pinned by `the_ord_names_classify_and_their_neighbours_do_not` in
    `src/mir/intrinsics.rs`.
  - Progress (cont.): a `PartialEq`/`PartialOrd` comparison against a *constant*
    operand is decided. The gap was not in the model but in the frontend: an
    unoptimised dump promotes a literal operand to its own item
    (`x.eq(&5)` lowers to `_3 = const F::promoted[0]; … Eq(copy _1, copy _3)`,
    where `const F::promoted[0]: &u8 = { _1 = const 5_u8; _0 = &_1; }`), and the
    parser recorded only the *string-array* promoted constants (`panic!` messages),
    never a scalar one. So the operand place named a constant the table did not
    hold, the reference's referent was unknown, and every comparison against a
    literal bound -- `x.ge(&0)`, `x.lt(&100)`, `x.eq(&i8::MIN)`, an everyday idiom
    -- came back `unmodelled argument to <u8 as PartialEq>::eq`. The parser now
    records a promoted body whose sole value statement is a scalar literal as a
    `const` (an array or struct-literal body still has no single word and is left
    to `promoted_strs`). The `&self`/`&other` reference-following was already
    there; only the value it reached was missing. Three fixtures (two true, one
    tripwire) in `realistic.rs` (**566 of 1036**, from 564 of 1033), pinned by
    `partial_cmp_methods_are_modelled_and_a_local_trait_still_wins` and by the
    parser unit test `a_scalar_promoted_constant_is_collected_as_a_const`. The
    exec arm that reads a *bare* `Const` operand is kept as a defensive path (no
    current dump prints it) with a comment saying so.
  - Remaining: the *element* half of a *generic* `<[T]>::first/get` needs a
    monomorphised element type, which is C10: `first_or<T>`'s element has no width,
    so `v[0]` stays refused. The *length* half does not need it, and now decides:
    `v.len()`/`v.is_empty()` read only the length, which is a `usize` input whatever
    `T` is, so a generic slice's length is bound even when the element width is
    unknown (`bind_indexed_len` accepts the `0` sentinel). `first_or` in `everyday.rs`
    verifies because its guard is `is_empty` — the bounds check on `v[0]` is
    discharged from the length — even though the `v[0]` arm itself is an unmodelled
    element read. A *locally constructed* `Ordering` (a `cmp` body that returns
    `Ordering::Greater`) is also still unmodelled — the executor resolves an
    enum-variant path constant through `variant_index`, which knows
    `Option`/`Result`/`ControlFlow` but not `Ordering` — so a local trait's `cmp`
    body is `incomplete` even though a `core` `Ord::cmp` call decides. That is a
    `variant_index` gap, not a `cmp` one, and is scheduled with the
    enum-construction work rather than here.
  - Progress (cont.): **the generic slice's length is modelled.** `first_or` in
    `everyday.rs` moved from `incomplete` to `verified`, taking the file to
    **17/21 (81%)** — Phase 1's 80% exit criterion is met. The change is the `0`
    sentinel in `exec::Indexed::elem_w` (the element width is *not modelled* for a
    `&[T]`), with `bind_indexed_len` accepting it and every element path
    (`index_elem`, `index_chain`, the slice intrinsic read) refusing it. The length
    functions (`len`, `is_empty`) and a length-guarded element read decide; a
    contract that *names* a generic element is a refusal, never a proof. Pinned by
    `a_generic_slices_length_is_modelled_but_its_element_is_not` and six corpus
    fixtures (three verify, one refutes, one skips on purpose, one refutes the
    element claim is not proved).
  - Progress (cont.): `iN::wrapping_shl`/`wrapping_shr` are modelled. `core`
    reduces the amount modulo the width (`1u8.wrapping_shl(8)` is `1`), which is
    exactly the reduction a rotation does — the low `log2(w)` bits, one `and` and
    no divider — so the two share the amount computation and the power-of-two
    width requirement. `wrapping_shl` fills with zeros; `wrapping_shr` is
    *arithmetic* on a signed receiver (`-8i8.wrapping_shr(1)` is `-4`) and
    *logical* on an unsigned one, so the sign decides the engine's shift kind.
    These are the *only* shift spellings the model takes: the plain families
    genuinely disagree (`checked_shl` returns `None` past the width,
    `overflowing_shl` reports a flag, and the engine's own variable shift
    saturates to zero), so `checked_shl`/`overflowing_shl`/`saturating_shl` stay
    refused rather than guessed at. Checked exhaustively against Rust's own
    methods over the whole `u8`/`i8` operand domain
    (`wrapping_shifts_agree_with_rust`). The corpus pairs are *discriminating*: the
    left-shift pair pins the amount reduction (the true entry claims `1`, its twin
    the saturated `0`, so only a reducing model proves one and refutes the other --
    a `ret <= 255` bound would satisfy both), the signed right-shift pair pins the
    shift kind (`-4` vs the logical `124`), and the unsigned right-shift entry pins
    both at once (`64`). Five fixtures (three true, two tripwires) in
    `realistic.rs` (**583 of 1065**), pinned by
    `wrapping_shifts_are_modelled_with_the_amount_reduced_modulo_the_width`; the
    no-reduction mutation flips both left-shift verdicts and fails that test.
  - Progress (cont.): `str::len`/`str::is_empty` are modelled. A `str` is unsized
    exactly as `[T]` is, so its length is the same kind of symbolic input and the
    *same two intrinsics* answer it — only the path differs
    (`core::str::<impl str>::len`). The `&str` argument's length is bound by the
    contract binder with the unmodelled-width sentinel (the same `bind_indexed_len`
    a generic `&[T]` uses), so `s.len()` in a contract and `PtrMetadata` in the
    body name one variable and a `requires: s.len() == 3` pins the body's read.
    `String` is deliberately not covered: it is a different type
    (`alloc::string::String`), so `String::len` stays an honest refusal rather than
    being answered with a length the model does not hold — a `String::len` call has
    no `str::<impl str>` in its path. Five fixtures in `realistic.rs` (three true,
    two tripwires), pinned by `a_str_length_is_a_symbolic_input`; reverting either
    the binding or the classifier fails that test. `realistic.rs`
    **583 of 1065 -> 586 of 1070**.
  - Progress (cont.): `Option<&T>::copied`/`cloned` are modelled — the everyday
    `v.first().copied().unwrap_or(0)` idiom, and the two closure-free methods that
    turn a `slice::first`/`get` result into the element's own value. The model
    stores a `&T` payload as the value it addresses (the single-owner reading every
    reference here takes), so the result's payload *is* the receiver's and only the
    tag passes through unchanged; the element identity is dropped, because the
    result is a value rather than a reference, so a later `*` on it is not a
    modelled read. A receiver with no payload on some path is refused (the rule
    `or`/`and` already apply), and `copied`/`cloned` share one arm because `Copy`
    and `Clone` both copy the referent. Six fixtures in `realistic.rs` (four true,
    two tripwires), pinned by
    `option_copied_and_cloned_copy_the_payload_with_the_tag`; the tag half is what
    the `copied_empty_is_none` fixture pins (a model that fixed the tag to `Some`
    would panic on `unwrap_or`), and the payload half is what the two tripwires
    pin (a claim about a different element refutes). `realistic.rs`
    **615 of 1125** (from **611 of 1119**; six new fixtures, four verified and two
    refuted).
  - Progress (cont.): `char` is modelled. A `char` is a 32-bit unsigned value, so
    `Ty::Char` parses to width 32 and `c as u8` truncates to the low byte. The
    `is_ascii_*` predicates (`is_ascii_digit`, `is_ascii_alphabetic`,
    `is_ascii_alphanumeric`, `is_ascii_whitespace`, `is_ascii_uppercase`,
    `is_ascii_lowercase`, `is_ascii_punctuation`, `is_ascii_hexdigit`, `is_ascii`)
    are exact at width 32, because every range they test lies inside `0..=0x7f`
    and a value at or above `0x100` is outside all of them — which is what
    `char::is_ascii_digit` means too (`'\u{130}'.is_ascii_digit()` is `false`,
    though its low byte is `'0'`). The `is_modelled` guard for the ASCII classes
    therefore drops its `w == 8` clause: a `char` receiver is the same byte test
    applied to the whole value, verified against `core` over the whole 32-bit
    domain. A `char` *literal* is read in a contract as its Unicode scalar value
    (`'0'` is `0x30`, `'\n'` is `0x0a`, `'\u{1F600}'` is `0x1F600`), and it is
    *typed*: `'0' == 0u8` is `E0308` in Rust, so `Sign::Unsigned` (which does not
    adapt) makes `align_widths` refuse the mismatch rather than resize the literal.
    Unicode methods (`is_alphanumeric`, `to_ascii_uppercase`, `to_lowercase`) are
    still refused — they are not ASCII byte tests. Eight fixtures in
    `realistic.rs` (six true, two tripwires), pinned by
    `char_literals_and_ascii_predicates_are_modelled` and the spec unit tests
    `a_char_literal_is_read_as_its_scalar_value_or_refused` /
    `a_char_literal_does_not_resize_to_a_narrower_operand` /
    `the_ascii_classes_agree_with_char_over_the_whole_domain`. `realistic.rs`
    **621 of 1133** (from **615 of 1125**; eight new fixtures, six verified and two
    refuted).
  - Progress (cont.): `slice::last` is modelled. A slice's length is symbolic, so
    `xs.last()` names no index the store can pin; the element is a *fresh* variable
    per slice (keyed by a sentinel index), which is the sound over-approximation —
    a contract true of every element holds of the last one, and a claim that the
    last element is a particular value is refuted, because a slice holding it can
    exist. An *array*'s length is its type's constant, so `a.last()` is the exact
    element `a[N-1]` and is modelled as that element, so a contract about `a[N-1]`
    decides. Four fixtures in `realistic.rs` (two true, two tripwires), pinned by
    `slice_last_is_an_element_and_array_last_is_exact`. `realistic.rs`
    **623 of 1137** (from **621 of 1133**; four new fixtures, two verified and two
    refuted).
  - Progress (cont.): `u8::from(bool)` (and the wider integer destinations) is
    modelled. A `bool` source has no integer width, so the integer-conversion model
    would refuse it; the conversion is the *zero-extension of the one-bit value*
    (`false` -> 0, `true` -> 1), the same step a `bool` `ret` takes, so the executor
    answers it directly. `u32::from(char)` stays a refusal -- a `char` conversion is
    not one of the integer widenings. Four fixtures in `realistic.rs` (three true,
    one tripwire), pinned by `a_bool_conversion_is_the_zero_extended_bit`.
    `realistic.rs` **626 of 1141** (from **623 of 1137**; four new fixtures, three
    verified and one refuted).
  - Progress (measured, done): the surface is complete for the *stable* integer
    API. Every method the three corpora call classifies; a sweep of ~30 standard
    methods (`checked_/saturating_/wrapping_/overflowing_`, the shifts, the counts,
    `abs`/`abs_diff`/`signum`, `min`/`max`/`clamp`/`cmp`, `rotate_*`, `pow`,
    `div_ceil`/`div_euclid`/`rem_euclid`, `midpoint`, `next_multiple_of`,
    `next_power_of_two`, `ilog*`, `to_be`/`to_le`, `is_ascii_*`, `is_multiple_of`,
    the `cast_signed`/`cast_unsigned` pair) is `classify`-able, and the only
    unmodelled call across `everyday.rs`/`actuator.rs`/`realistic.rs` is a
    *deliberate* refusal (`<Self as …>::set`, a `Self` receiver). `unwrap_or_default`
    on a `Result<u8, Boom>` where `Boom: Drop` is refused *because dropping `Boom`
    panics* -- a sound refusal, not a gap. The boundaries that remain are deliberate
    and named: `div_floor` is unstable (`int_roundings`) and cannot be
    differential-tested on the gate's toolchains, so it is refused; the `_bytes`
    forms return an array and are refused rather than modelled as a word. See
    `mir::intrinsics` tests `classify`/`the_new_shapes_are_modelled_only_on_the_types_that_have_them`.
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

    *The `u32` **divider** is a wall, not a budget knob* — the concrete blocker on
    `everyday.rs`'s `div_unwrap` (`n.checked_div(d).unwrap()`). Measured on the
    release build: `n / d` at `u32` is undecided after **~186 s** with
    `MAX_APPLY_STEPS` raised 32× (to `1 << 24`), and still undecided after 5.7 s
    with `MAX_CONFLICTS` raised to 20 000 000 (the SAT fallback cannot decide it
    either). So the restoring divider's BDD at 32 bits is exponential and no
    budget reaches it; `div_unwrap`, `plain_div` and a guarded `u32` `/` all fail
    identically. The `u8`/`u16` cases decide (`div_u8` verifies in 0.57 s,
    `div_u16` is undecided at 0.32 s and is the next width the diagram cannot
    hold). The fix is word-level preprocessing (the approach above), not a raised
    cap.


### Trust tracking (A1, tracked from Phase 1)

- **A1. Track the false-proof rate.** · P0 · **done** · —
  - Data: at least 11 false proofs were fixed between 2025-11-04 and 2025-11-12.
    All were caught, but at that rate a `verified` is not yet evidence to rely on.
  - Approach: a `SOUNDNESS.md` listing every false proof with date, commit,
    root-cause class and fixture. Pause feature work on any layer that produced a
    false proof in the last two weeks.
  - Exit for "beta": four weeks in a row with no new false proof, while the
    independent corpus keeps growing.
  - Move: **build**. `SOUNDNESS.md` carries the ledger: 41 MIR-frontend rows and
    16 engine/imperative rows — 57 in all, so the review's "at least eleven
    earlier false proofs" is now that many *dated rows* rather than a count (the
    seven commits the review named each contribute their own row). Every row has a
    **commit**, a **date** and a fixture. `tests/soundness.rs` checks it
    mechanically — every fixture must be a `#[test]` (not a same-named helper), in
    the file the cell names, every row must carry a commit and a `YYYY-MM-DD`
    date, and no date may be in the future. The clock restarts on each row; the
    most recent is 2026-11-18.

---

## Phase 2 — real crates (P1)

Exit: one real `no_std` crate with a dependency verified end to end with
`cargo verif`; Kani agrees on every function both tools decide.

- **C8. Cargo, multi-module crates and dependencies.** · P1 · **done** · Kani
  (`cargo kani`)
  - Gap: the frontend runs `rustc --crate-type=lib` on one file, without
    `--extern`, so a crate that `use`s another crate, or a file whose
    crate-relative paths only resolve inside the crate, cannot be verified.
  - Approach: a `cargo verif` subcommand through `cargo rustc`/`RUSTC_WRAPPER`,
    emitting MIR for the target crate with its real flags. Dependency calls are
    answered through contracts (C2), not bodies.
  - Progress (multi-module, done): `spec::extract_crate` inlines every external
    `mod name;` declaration (`name.rs` / `name/mod.rs`, recursively) before scanning,
    so a contract written in a *module file* is read and keyed by the `mod`-qualified
    path rustc prints for it (`a::clampish`). `cargo verif --file src/lib.rs` on a
    crate with `pub mod a;` now verifies `a`'s functions instead of reporting "all
    contracts held" over zero checked functions -- which was a silent pass, the worst
    direction. A module file that cannot be read stays a bare `mod name;`, so its
    functions are reported `missing`, never silently passed. Pinned by
    `extract_crate_reads_external_module_contracts` (the keying) and
    `a_multi_module_crate_is_verified_through_its_root` (a clean module exits 0, a
    false one exits 1, each naming the module function).
  - Progress (dependencies, done): `verify::crate_options` reads the crate's own
    `[dependencies]` table (`dependency_names`: `name = "1"`, `name = { … }`, and the
    `[dependencies.name]` sub-table; dev/build deps skipped) and, for each, finds its
    newest `lib<name>-*.rlib` under `target/<profile>/deps` *or* a
    `target/<profile>/build/<pkg>/<hash>/out` (the build-script layout this container's
    cargo uses for a path dependency), then *probes* the whole set with the emitting
    compiler (`extern_compiles`). `cargo-verif` passes the result as `--extern`/`-L`,
    so a file that `use`s another crate compiles and its contract is checked. A crate
    whose deps are not built, or whose rlibs are stale, falls back to
    `MirOptions::default()` and the honest `E0432`/`E0514` -- never a guessed path.
    Pinned by `dependency_names_reads_the_dependencies_table_only` (the parser) and
    `a_crate_with_a_dependency_is_verified` (a path-dep crate verifies; a false
    contract is still refuted, so the dependency did not hide the check).
  - Progress (RUSTC_WRAPPER, done): `src/bin/verif-wrap.rs` is a `RUSTC_WRAPPER`
    entry point. `RUSTC_WRAPPER=/path/to/verif-wrap cargo build` forwards every
    rustc call and, for the *primary* package (`CARGO_PRIMARY_PACKAGE=1`, which cargo
    sets for the crate under development and never for a dependency), also runs the
    frontend on the crate source, failing the build on a false contract. The source
    path is canonicalised first, because cargo passes it relative and `crate_options`
    walks up from it to find the manifest's `target/`. Pinned by
    `tests/rustc_wrapper.rs`: a true contract builds, a false one fails the build
    naming the obligation, and a *dependency's* false contract does not fail the
    build (the primary-package guard).
  - Progress (external crate, done): `tools/external-demo/run.sh` builds a throwaway
    `no_std` crate that depends on `embedded-hal = "=1.0.0"` and `use`s it, then runs
    `cargo verif` on it. Recorded output: `clamp_percent: verified (1 obligation(s))`
    and `all contracts held` (exit 0) for the true contract, `FAILED` (exit 1) for a
    false one. It found and fixed a real defect: a hyphenated manifest key
    (`embedded-hal`) was passed as `--extern embedded-hal=…`, which names nothing the
    source can `use`; `extern_name` now underscores it (`embedded_hal`), pinned by
    `a_hyphenated_dependency_name_is_an_underscored_extern`. The demo exits 2 (a
    reported skip, not a pass) when there is no network to fetch the crate.
  - Exit: one function in a real `no_std` crate with at least one dependency
    (an `embedded-hal` driver, say) verified end to end with `cargo verif`.
    **Met** -- `tools/external-demo/run.sh`.
  - Move: **done**.
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
  - Note on `everyday.rs`'s `sum_iter` (`v.iter().sum()`): modelling `iter`/`sum`
    would decide the *path*, but the entry would become `FAILED`, not `verified` —
    an unbounded slice sum can overflow, so the honest verdict for its total
    postcondition is a panic (a bare `a + b` under `requires: true` fails the same
    way). So `sum_iter` is not a target that moves the `everyday.rs` *score*; it is
    a shape whose modelling would show a real panic. Worth doing, but it is not a
    route to 21/21.
- **C11. Heap containers.** · P1 · in progress · Kani, Verus (`Seq`), Creusot
  - Gap: `Vec`, `String`, `Box`, symbolic-length slices. Evidence: `make`
    incomplete.
  - Approach: a bounded *sequence* model (length plus element array, from `mem`),
    exposed through contracts for `Vec::{new, push, pop, len, get, index}`.
  - Exit: `make` verified. **Met** — `make` verifies (18 of 21 in `everyday.rs`).
  - Done: the **length** half. `Vec::{new, push, len}` are modelled from a
    per-local length the executor tracks (now the `indexed` store's `len`, with
    `len_mutable` set for a `Vec`; it began as a separate `Env::vec_len` and was
    folded into `Indexed` when the element model landed), since a `Vec`'s fields
    (a heap pointer, a length, a capacity) are not printed by the dump. The
    length is `usize` and `push` is `+ 1`, which cannot overflow at 64 bits, so it
    is exact rather than saturating. `drop` of a `Vec<T>` is a no-op exactly when
    `T` is glue-free (`Vec<u8>` yes, `Vec<String>` no). The length crosses a call
    boundary in both directions (`&mut Vec<u8>` carry-in and write-back), so
    `push_helper` verifies and its false twin is refuted; a `Vec` *argument*'s
    length is never invented — `v.len()` on an unmodelled receiver is a refusal.
    A user type spelled `Vec` in a local module is not the standard one (the
    same-dump lookup answers its own body first, `classify` refuses `m::Vec`).
  - Three soundness holes in this model were found by review and fixed in
    `8dd4d21` (ledger rows 34–36): the container identity is the *full* path
    (`std::vec::Vec` / `alloc::vec::Vec`), so a user `struct Vec<T>` with a
    panicking `Drop` is no longer treated as glue-free; the loop-header havoc
    refreshes the tracked length to a fresh `usize`, so an inductive pushing loop
    no longer reads the entry length at the exit (`ret == 0` for `ret == 3`); and
    a `Vec` move (`let w = v`) and a returned vector transfer the length to the
    destination rather than dropping it.
  - Remaining: symbolic-length slices. (`Box<T>` and `String` are done — see the
    progress notes below. Iteration, `pop`, `is_empty` and the **element** model
    are done.)
  - Progress (`Box<T>`): `Box::<T>::new` + the deref `*b` are modelled. The dump
    never prints the allocation, so `Box::new` stores the boxed value and makes
    the pointer a large power-of-two token (nonzero, so the compiler's null check
    `Ne(SIZE, 0) && Eq(ptr, 0)` is discharged, and a multiple of every primitive
    alignment, so the `addr & (ALIGN-1) == 0` check is too); the deref
    `_5 = (_2.0) as *const u8; *_5` reads the stored value. Two parser fixes were
    needed and are general: a cast is now recognised *before* the copy/move-place
    attempt (a cast of an *annotated* place, `copy (_2.0: Unique<u8>) as *const u8`,
    was being swallowed as a bare place and the cast dropped), and a cast's
    trailing kind annotation (` (BoxDerefTransmute)`, ` (PtrToPtr)`) is stripped
    so `*const u8` is not truncated to `*const`. `SizedTypeProperties::{SIZE,
    ALIGN}` are modelled from the type in the constant's path. A `Box<T>`'s drop
    glue is `T`'s, so `drop_is_noop(Box<u8>)` is true while `Box<PanicOnDrop>` is
    not; the *bare* `Box<u8>` spelling an argument prints is treated as the
    standard one only when the crate declares no `struct Box` (a shadow would
    otherwise be read as glue-free and hide a panicking destructor). Fixtures:
    `box_new_reads_its_value`, `box_guarded_inc`, `box_u32_reads_its_value`,
    `owns_box_glue_free` and their two tripwires, pinned by
    `a_box_new_deref_decides`. An explicit `std::mem::drop(b)` call and a
    symbolic-length `sum` remain refusals (honest incompletenesses); `realistic.rs`
    656/1198 → 660/1204.
    - **MSRV fix.** On the 1.85 floor the deref lowers differently -- the pointer
      is reached by a *field chain* `_3 = copy (((_2.0).0).0)` (no cast) and an
      *alignment* assert is emitted (`AlignOf`/`BitAnd`/`Eq`) that current stable
      const-folds away. The `box_refs` link now records for either spelling (a
      cast of `_2.0` or an all-`Field` chain rooted at a boxed local) and is
      recorded *last* in the `Stmt::Assign` arm (`set`/`rebase_parts` clear it), and
      `parse_rvalue` reads `AlignOf(T)` as the alignment constant (a primitive's
      alignment is its byte size). Both box fixtures verify on 1.85 *and* stable;
      gate 14 (the suite on the MSRV) went red→green. See the AGENTS.md section.
  - Progress (**iterator method form** and **explicit drop**): `xs.iter()` on a
    `&[T; N]` now starts the same cursor the `for` desugaring does. The unsize
    coercion `xs as &[u8]` is a reference cast, and the cast arm carried the
    address only when the *source* was already `addressed`; a reference
    *argument* is modelled as its referent and is not, so the cast fell through
    and the `iter` receiver had no elements. The cast now falls back to
    `pointee(src)` (the referent), which is what a reference cast preserves. With
    that, `xs.iter().count()` and `xs.iter().copied().sum()` over a constant-length
    array decide (`sum` carries its real overflow obligation, so it verifies only
    under guards that rule the overflow out, and refutes otherwise). The
    `map`/`filter`/`fold` adapters are still unmodelled: their bodies live in
    `core`, not the dump, so they need closure execution the leaf intrinsic
    handlers cannot do. `std::mem::drop::<T>` is now modelled: a glue-free `T`
    (`Box<u8>`, `String`, `Vec<u8>`, a scalar) is a no-op, and a `T` with
    unrepresentable glue (`Rc<u8>`, a user `Drop`) is refused. Fixtures:
    `array_iter_count`, `array_iter_sum`, `explicit_drop_box`,
    `explicit_drop_string` and their two tripwires, pinned by
    `a_slice_iter_and_explicit_drop_decide`. The same fix unlocked the rest of
    the already-modelled `slice::Iter` surface on a constant-length array --
    `.max()`, `.min()`, `.last()`, `.nth(k)` (`array_iter_max`, `array_iter_min`,
    `array_iter_last`, `array_iter_nth` and three tripwires) -- and the total
    `clear` methods (`Vec::clear`, `String::clear`) are modelled as a length
    reset. `realistic.rs` 660/1204 → **670/1219**.
  - Progress (`pop`, `is_empty`): `Vec::is_empty` reads the tracked length;
    `Vec::pop` returns `None` iff the length is zero and decrements it on the
    non-empty path; on a constant-length vector the popped element is the payload.
    Fixtures `vec_is_empty_new`, `vec_not_empty_after_push`,
    `vec_pop_empty_then_len`, `vec_pop_one_is_some` and their twins.
  - Progress (the **element** model, C11's last hard half): a `Vec` is now an
    `Indexed` store exactly as a slice is — `len_mutable` distinguishes it from a
    slice/array, and `push` records the pushed value at the *current* length. The
    element is read back by `v[k]` (`<Vec as Index>::index`), `v.first()`/
    `v.get(k)` (`<Vec as Deref>::deref` and `as_slice`), and `pop`. A `Vec`
    *argument* binds a symbolic length (`v.len()` in a contract) and a distinct
    element per index, so `v[0]` in a contract agrees with the body's `v[0]`.
    Three soundness points pin it: `push` records an element only at a *constant*
    length (a symbolic one poisons the elements rather than pinning a wrong
    index), `v[k]` emits the `core` bounds panic as a reachable-failure obligation
    (`v[0]` on a vector the precondition proves empty is refuted as a *panic*,
    with the length in the witness), and the store crosses a call boundary and a
    loop havoc exactly as the length does. Fixtures: the `vec_index_reads_pushed`
    / `vec_first_reads_pushed` / `vec_get_reads_pushed` / `vec_pop_reads_pushed` /
    `vec_arg_{index,first}_matches_contract` families and their `_cannot_prove_this`
    twins, plus `vec_index_empty_is_a_panic`. `realistic.rs` **630/1148 →
    637/1163**; `tests/mir.rs` `a_vec_element_is_read_back_through_index_first_get_and_pop`
    pins every direction, and the `Vec` argument's length moving from a refusal to
    a symbolic input is pinned by `arg_len_reflexive` (verifies) against
    `arg_len_refused` (now a refutation, not a refusal).
  - Progress (**iteration**): `for x in xs` over a slice, a `&[T; N]`, a `[T; N]`
    (by value) and `xs.iter()` now decides. The desugaring is `IntoIterator::
    into_iter` + `Iterator::next`, so the model holds a *cursor* -- the base slice
    local and a **concrete** `u64` position -- that `next` advances. A concrete
    position makes each iteration name the element at a constant index, the same
    variable a contract's `xs[k]` names, so `for_slice_sum`'s `xs[0] + xs[1]`
    agrees with the body. `next`'s `None` guard is the slice's own length variable
    (`pos >= len`), so it cannot disagree with `len`/`is_empty`/`first`. A loop cut
    havocs the cursor (drops it), so a `for` loop with an `invariant:` -- where the
    position would be symbolic -- refuses `next` rather than reading an arbitrary
    element. A by-value `[T; N]` loop owns an `array::IntoIter`, whose drop is a
    no-op exactly when `T` is glue-free (the glue check reads `T` off the name).
    `classify` accepts the calls only for a `[T]`/`[T; N]`/`slice::Iter`/
    `array::IntoIter` head, so a user iterator is refused. `vec_iter_sum` and
    `for_over_slice` now **verify** (as do `make`, `for_array_sum`,
    `for_array_by_value_sum`, `for_slice_iter_sum`, `for_slice_count`,
    `for_slice_max`). `realistic.rs` **637/1163 → 643/1174**;
    `tests/mir.rs` `a_for_loop_over_a_slice_is_modelled` (five verified, three
    refuted) and `a_for_loop_with_an_invariant_refuses_the_iterator` pin both
    directions, and `slice_iteration_classifies_and_a_user_iterator_does_not`
    pins the path guard.
  - Progress (**iterator consumers**): `Iterator::{sum, count}` and the
    cursor-preserving `copied` adapter now decide on a slice/array cursor.
    `count` is `len - pos` on the slice's own length variable (exact even when the
    length is symbolic, since `pos <= len`). `sum::<T>` folds the remaining
    elements `s[pos] + ... + s[len-1]` with a **checked** `+`, so each partial sum
    raises a reachable-panic obligation -- an unguarded `xs.iter().sum()` over
    `u8`s is *refuted* as a panic (it overflows for `[200, 100]`), not proved; a
    contract that bounds the elements discharges the two additions and verifies.
    The number of addends is the length, so `sum` is modelled only when that length
    is a constant (an array's type length, or a slice the precondition pinned with
    `requires: xs.len() == N`); a symbolic length has no fixed addend count and is
    refused. `copied` is the identity on the cursor (a reference is modelled as its
    referent), and `next`/`sum`/`count`/`into_iter` accept an adapter over a
    slice/array iterator (`Copied<..>`, and the `Enumerate<..>` spelling is
    classified for `next` though the tuple payload is not yet modelled), so
    `xs.iter().copied().sum()` and `for x in xs.iter().copied()` decide. `classify`
    checks the receiver *type* (`slice::Iter`/`array::IntoIter`, or an adapter whose
    payload is one) and the `Iterator`/`IntoIterator` trait, so a user iterator is
    refused. `realistic.rs` **643/1174 → 647/1181**; `tests/mir.rs`
    `a_slice_iterator_sum_and_count_are_modelled` pins four verified, two
    postcondition refutations, the overflow *panic* refutation, and the
    symbolic-length refusal.
  - Progress (**extremes and offsets**): `Iterator::{last, nth, max, min}` now
    decide on the cursor. `last`/`nth` name the *exact* element when the length is
    known (an array's type length, or a slice the precondition pinned) -- the same
    variable a contract's `xs[len-1]`/`xs[pos+k]` names -- and fall back to the
    single fresh `LAST_INDEX` variable only for a symbolic-length slice, the same
    over-approximation `slice::last` uses. `nth(k)` needs a *constant* offset (a
    symbolic one names no single index) and advances the cursor past the returned
    element. `max`/`min` are folds of comparisons over the remaining elements, so
    (like `sum`) they need a constant length; the payload is the extreme *value*,
    and a reference payload (`Option<&T>`) also carries a `Select` tree over the
    same elements, so a deref reads the same value a direct `Option<T>` read does.
    The comparison is `slt`/`ult` by the element's sign -- `i8::MIN` is the
    smallest signed value but the largest unsigned byte, so an unsigned comparison
    would pick the wrong element. `realistic.rs` **647/1181 → 652/1190**;
    `tests/mir.rs` `a_slice_iterator_extremes_and_offsets_are_modelled` pins six
    verified (incl. signed `i8` and a reference payload), five postcondition
    refutations, and the symbolic-length refusal.
  - Progress (**`rev`**): `Iterator::rev` is a direction flag on the cursor
    (`IterState::rev`), carried like `copied`; `rev().rev()` toggles it back to the
    identity. Only the order-dependent terminals read it: `next` names base index
    `len-1-pos` (so a `for x in xs.iter().rev()` loop walks back-to-front), `last`
    names `s[pos]` (the first *remaining* element, so `rev().last()` is `xs[0]`),
    and `nth(k)` names `s[len-1-(pos+k)]`. `count`/`sum`/`max`/`min` are
    order-independent and unchanged. `rev` needs a *constant* length so the index
    is a constant (a symbolic-length reversed cursor is refused, the honest
    direction); `is_cursor_ty` accepts the `Rev` adapter, so the reversed cursor's
    terminals still classify. `tests/mir.rs::an_iterator_can_be_reversed` pins five
    verified (`last`/`nth`/
    `for`/`rev().rev()`/`count`) and one refuted tripwire, and
    `mir::intrinsics` pins the classification without a toolchain.

  - Progress (**`skip`/`step_by`**): `skip(n)` advances the cursor's position by
    `n`; `step_by(n)` sets its stride (`IterState::step`, composed as `step*n` when
    chained). The stride is read by every order/count-sensitive terminal: `next`
    advances `pos += step`, `nth(k)` names `pos + k*step`, `last` names the last
    strided index `pos + ((n-1-pos)/step)*step`, `count` is
    `(n-1-pos)/step + 1` (both need a *constant* length, which `skip` does not),
    and `sum`/`max`/`min` fold the strided positions. A zero step is a Rust panic
    and is refused. `is_cursor_ty` accepts the `Skip`/`StepBy` adapters.
    `tests/mir.rs::an_iterator_can_be_skipped_and_stepped` pins five verified
    (`skip`/`step_by` over `last`/`count`/`sum`) and one refuted tripwire, and
    `mir::intrinsics` pins the classification without a toolchain.

  - Progress (**`take`**): `take(n)` caps the cursor's effective end at
    `pos + n` (`IterState::end`, an absolute exclusive bound). It needs a *constant*
    length so the cap is constant; every terminal reads the capped end -- `next`
    stops at `min(len, end)`, `count` is `(hi-1-pos)/step + 1`, `last` names the
    last strided index below `hi`, `nth(k)` is valid iff `pos+k < hi`, and
    `sum`/`max`/`min` fold `pos..hi`. `is_cursor_ty` accepts the `Take` adapter.
    `tests/mir.rs::an_iterator_can_be_taken` pins five verified (incl. `take(10)`
    over four elements = all four) and one refuted tripwire, and `mir::intrinsics`
    pins the classification without a toolchain. Measured after all three adapter
    increments (rev, skip/step_by, take): `realistic.rs` **685 of 1237**.

  - Progress (**`fold` with a reducer closure**): `Iterator::fold(init, f)` folds a
    modelled reducer closure. A non-capturing closure prints as
    `const ZeroSized: {closure@FILE:L:C: L:C}`, so `closure_fn` resolves it to the
    `MirFn` whose first argument type is exactly that closure type (a function
    item is matched on its tail, and an ambiguous tail is refused). `closure_binop`
    reads the reducer shape `|acc, x| acc <op> x` -- a *checked* `Add`/`Sub`/`Mul`
    (with its overflow `assert`, so the fold raises a reachable-panic obligation
    per step, exactly as `sum` does for `+`) or a `wrapping_*` call (no
    obligation). Needs a constant length and a constant `init`. Anything else is
    refused, because a wrong reducer is a wrong value.
    `tests/mir.rs::an_iterator_can_be_folded_with_a_closure` pins three verified
    (checked sum, `wrapping_add`, a non-zero init) and one refuted tripwire (an
    unguarded fold overflows), and `mir::intrinsics` pins the classification.

  - Progress (**symbolic-length `sum`**): a slice whose length is a *symbolic*
    input (`v: &[T]`, `v.iter().sum()`) is summed by unrolling to
    `MAX_SYMBOLIC_LEN` (8) steps, each guarded by `k < len` (`ite(k < len, v[k],
    0)`), which is exact **iff** the precondition proves `len <= 8`; the handler
    proves `path => len <= 8` with `find_obligation` and **refuses** the shape
    otherwise (a shorter unroll would silently miss elements — a wrong value, so
    the direction is a refusal). The elements are created on demand
    (`index_elem`), so a guarded sum of small elements is a real panic-freedom
    proof over a runtime-length slice. `step_by`/`take` on a symbolic length are
    refused (they need a constant count). Pinned by
    `a_symbolic_length_sum_is_bounded_by_its_precondition` (verified / refuted /
    refused).

  - Progress (**`map`/`filter`**): `map(f)`/`filter(f)` are lazy: they set a
    transform/predicate on the cursor and carry it. `sum` applies the transform
    per element (with the transform's own overflow obligation, checked or
    `wrapping_*`), and `count` counts the elements the predicate accepts
    (`Σ ite(pred(x), 1, 0)`). The closure is resolved by `closure_fn`; the
    transform/predicate is read by `closure_map`/`closure_filter`, which follow
    the body's `_3 = copy (*_2)` copies (`resolve_operand`) to the element and a
    constant. Needs a constant length; anything else is refused.
    `tests/mir.rs::an_iterator_can_be_mapped_and_filtered` pins three verified
    (checked map, `wrapping_mul` map, filter-count) and one refuted tripwire (the
    filter accepts all four, so a count of two is refuted), and `mir::intrinsics`
    pins the classification.

  - Progress (**`all`/`any`**): `all(f)`/`any(f)` fold a predicate closure to a
    `bool` -- `all` is the conjunction of `pred(x)` over the elements, `any` the
    disjunction. Reuses the `filter` predicate reader (`closure_filter`); needs a
    constant length. `tests/mir.rs::an_iterator_can_be_tested_with_all_and_any`
    pins two verified and two refuted tripwires (all-true claimed false, and an
    unguarded `any` claimed true).

  - Progress (**`enumerate`**): `Iterator::enumerate` is a cursor identity whose
    `next` yields `Option<(usize, &T)>`. `next` writes the concrete index and the
    element into the tuple store and sets the payload to an aggregate, so the
    direct `((_2 as Some).0).0` / `.1` destructure reads the index and `xs[pos]`.
    Modelling it exposed a *parser* bug: a nested place whose group holds a
    downcast *and* a tail (`((_2 as Some).0).0`) was split on its last ` as ` and
    came back `None`, so the whole read was unknown. `parse_place` now splits a
    group only on a *top-level* ` as ` (`find_top_level_as`), so the inner
    `(_2 as Some).0` recurses to the real downcast. `realistic.rs` **652/1190 →
    654/1194**; `mir::parse::tests::a_nested_downcast_with_a_tail_parses_whole`
    pins the parse without a toolchain and
    `a_slice_iterator_enumerate_carries_the_index_and_element` pins the verdicts.
  - Progress (**`String`**, the length half): a `String` is a `Vec<u8>` underneath
    and its fields are not printed, so the model tracks its **length** only --
    `String::new` is `0`, `push_str` adds the appended `&str`'s byte length, the
    `<String as From<&str>>::from` constructor is that length, and `len`/`is_empty`
    read it. A `&str`'s byte length is a symbolic input for an argument (the same
    variable `str::len` reads) and a **constant** for a literal (`const "abc"` is
    `3`, kept in the string store and read back by `length_of`). A `String` drop is
    glue-free (like `Vec<u8>`), so a `String`-using function decides. The path is
    checked (`names_string_impl`, and the `String`/`&str` types in the conversion
    branch) so a user type spelled `String` is refused, and the same-dump lookup
    answers a real body first. The bytes are not modelled, so a method whose result
    depends on the *contents* stays refused. `realistic.rs` **654/1194 →
    656/1198**; `tests/mir.rs` `a_string_length_model_decides_new_from_push_len`
    pins eight verified (incl. a `&str`-argument reflexive length) and two
    refutations, so the model is exact rather than a constant the claim accepts.
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
  - The concrete blocker on `everyday.rs`'s `tri` (`s += i` over `0..=n`): the
    loop needs an **inductive** invariant, and the invariant that is inductive for
    a running sum is *nonlinear* (`s <= i(i+1)/2`), which the expression language
    has no multiplication in a loop-invariant position to express. The *linear*
    candidate that does exist — `s <= i` — is rejected (`unknown name i`: the
    `for`-loop element is a `debug` binding not live at the header, see C3), and
    the constant bound `s <= 5050` is not inductive, so the loop reports a spurious
    panic. Inferring the invariant is a separate, larger item than the language
    extension; both are recorded here rather than under C3.
- **C13. Rust's own contract attributes as input.** · P1 · todo · the `contracts`
    crate
  - Approach: read `#[core::contracts::requires/ensures]`
    (rust-lang/rust#128044) as well as doc comments, keeping doc comments as the
    stable fallback.
  - Exit: a function carrying the attribute instead of a doc comment is verified.
  - Move: **build**. Without it, a home-grown syntax risks being absorbed by the
    language's own — the risk the README already names.

### Usability (U items, Phase 2 subset)

- **U1. Publish to crates.io.** · P1 · done · —
  - Gap: the README's Installation section said `cargo add verif`, but the crates
    were not on crates.io. The packaging work (`scripts/publish.py`,
    `scripts/check_package.sh`, a tag-driven `.github/workflows/release.yml`) was
    already in place; what remained was the human step: create the
    `CARGO_REGISTRY_TOKEN` secret and push a `verif-arithmetic-v0.1.0` tag, then
    `verif-v0.1.0`. (That secret is no longer the mechanism: the repository is
    now registered as a crates.io **trusted publisher**, so `release.yml` mints a
    short-lived token through GitHub OIDC and no stored credential is needed.)
  - Fix: both crates are published (`verif-arithmetic` `0.1.0`, `verif` `0.1.1`),
    and the README's Installation section depends on the registry (`verif = "0.1"`)
    rather than on a git tag. The `0.1.1` patch is the qualified-layout soundness
    fix (`fix/qualified-type-layout`); `0.1.0` shipped with it, so the patch is
    what makes the published crate sound rather than merely buildable. The
    dependency snippets are pinned by `readme_install_uses_the_published_crate`
    in `tests/readme.rs`, so a regression back to a git source is a failing test
    rather than silent drift. (The current release is `verif` `0.2.0`, the minor
    bump that adds the in-code `spec!` macro, and the README snippet follows it
    at `verif = "0.2"`; `verif-arithmetic` stays at `0.1.0` because it did not
    change.)
  - Exit: `cargo add verif` works. ✅
  - Move: **build**.
- **U2. `cargo verif`.** · P1 · done · Kani (`cargo kani`)
  - Gap: there was no command-line entry point; a user had to write an example
    that called `verify_file_with`.
  - Progress: `src/bin/cargo-verif.rs` (a `[[bin]]` gated on `std`, so the
    bare-metal build is unaffected) is the entry point. `cargo verif [--file P]
    [--function N] [--format human|json]` verifies a file (default `src/lib.rs`)
    and maps the report to a distinct exit code: `0` clean, `1` a failure /
    incomplete / skipped / missing, `2` the tool could not run. `--format json`
    emits one machine-readable object (`file`, `outcomes`, `missing`, `summary`)
    with hand-written escaping (the crate is zero-dependency). Pinned end to end
    by `tests/cargo_verif.rs`, which runs the *built* binary (`CARGO_BIN_EXE_…`)
    on a throwaway crate: a true contract exits 0, a false one exits 1 and names
    the postcondition, a `--function` filter ignores a broken sibling, and the
    JSON carries the summary.
  - Progress (SARIF): `--format sarif` emits a SARIF 2.1.0 document -- one
    `result` per non-`verified` outcome, `error` for a failure and `warning` for
    an incomplete/skipped/missing function, each located at the file, and an empty
    `results` array on a clean run -- so `github/codeql-action/upload-sarif` can
    annotate a pull request. Pinned by
    `sarif_output_is_a_2_1_0_run_with_one_result_per_failure`.
  - Progress (the Action, done): the reusable composite action
    `.github/actions/verif/action.yml` wires `--format sarif` to
    `github/codeql-action/upload-sarif` (pinned to a commit SHA). It builds
    `cargo-verif` from its own checkout, runs it, uploads the report (skippable with
    `upload: false`), and fails the step on any finding (`fail-on-findings: false`
    to report without failing); a *skipped* contract is a failure by default. This
    repository dogfoods it in the `sarif` CI job, and `scripts/check_sarif.py`
    asserts the produced report is a well-formed SARIF 2.1.0 run naming the failing
    function, so a run that silently reports nothing fails there. The action's YAML
    is validated (composite, every `uses:` pinned) and `scripts/check_actions_pinned.py`
    scans it. The only piece not exercised in CI is the `upload-sarif` call itself
    (it needs code scanning enabled on the repo), which is why the dogfood runs with
    `upload: false` -- the report it would upload is what `check_sarif.py` checks.
  - Exit: `cargo verif --format json|sarif` plus a GitHub Action that annotates a
    PR.
  - Move: **build**.
- **U3. A counterexample becomes a test.** · P1 · **done** · Kani (concrete
    playback)
  - Gap: the replay machinery exists in `tests/mir.rs`; make it a user feature
    that emits a `#[test]`.
  - Progress (done): `cargo verif --emit-test <fn>` prints a `#[test]` that calls the
    refuted function at the counterexample's inputs (`mir::verify::emit_test_source`).
    The *values* come from the rendered counterexample (`n = 0`), the argument *order*
    from the source's parameter list (`mir::spec::function_params`), so the emitted
    call is the one the verifier refuted. It is deliberately scoped to a **panic**
    obligation with a concrete witness: a postcondition failure has no call to
    reproduce, and re-stating the postcondition in Rust is not modelled, so it is
    refused (exit 2) rather than guessed. A method, a non-scalar (reference)
    argument, or a counterexample that does not assign a parameter is refused too.
  - Exit: a reported counterexample is emitted as a compiling, failing-then-fixed
    `#[test]`. **Met** -- `tests/mir.rs::a_counterexample_becomes_a_failing_then_fixed_test`
    compiles the emitted test, runs it against the buggy body (it fails, the call
    panics) and against the fixed body (it passes).
  - Move: **done**.
- **U4. Readable counterexamples.** · P1 · in progress · —
  - Gap: a report says `v1:u8 = 224`, not `x = 224`. The `debug x => _1` names
    exist; the stable text dump has no per-statement spans, so line numbers come
    from the source scanner or the `rustc_public` path.
  - Exit: `x = 224` in a report. **Met** — the witness is rendered with the
    `debug` names (`a = 32768`, `n = 16`, `d = 0`), and a variable with no source
    name keeps its `v{index}:u{width}` spelling, so naming is a readability
    improvement and never a loss. See [`Cex::render_named`] and
    [`Obligation::failure_detail_named`]; pinned by
    `a_counterexample_is_rendered_with_source_names`. The README's `mir_demo`
    transcript is regenerated from the run.
  - Progress (lines): the source *line* of each function is now carried out of
    the scanner (`FileReport::lines`, from `FnContract::line`) and shown by
    `cargo verif` -- `wrong:3` in the human report and a SARIF
    `region.startLine` -- so a code-scanning annotation points at the function
    rather than at the file. The stable text dump has no per-statement spans, so
    this is the function's `fn` line, not the failing statement; that is the
    honest granularity the scanner can supply.
  - What remains: per-*statement* line numbers (a failing statement's line, not
    just the function's), which needs the `rustc_public` path.
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
- **U6. Documentation size.** · P1 · **done** · —
  - Gap: the README was ~166 KB and `AGENTS.md` ~586 KB. Split into a short README,
    a user guide, `ROADMAP.md` (this file), `SOUNDNESS.md`, and design notes.
  - Done: the README is now **25.7 KB** (under the ~30 KB exit). The long sections
    moved verbatim into `docs/` — `internals.md` (verification conditions + the
    engine-honesty war stories), `mir.md` (the MIR frontend), `layout.md`,
    `testing.md`, `comparison.md`, `build-time.md` — each linked from the README's
    contents, each headed with a back-link. `scripts/check_doc_links.py` was
    extended to check `docs/*.md` too, and its file-tree check now runs on
    `docs/layout.md` (where the tree moved) rather than only `README.md`; both
    were teeth-checked (a broken anchor and a bogus tree entry each fail). The
    `README.md`-anchored tests (`tests/readme.rs`) still read the sections that
    stayed (`Installation`).
  - `AGENTS.md` is deliberately **not** split: it is the agent-facing record, not a
    published page, and the exit names the README.
  - Move: **build**.
- **U7. Proof caching.** · P1 · **done** · —
  - Exit: unchanged MIR plus unchanged contracts reuses the verdict across runs.
  - Progress (done): `mir::cache` stores each file's *decided* outcomes
    (`Verified`/`Failed`) under a key that folds in the MIR text, the source text (the
    contracts), the edition **and the engine hash** — the last baked by `build.rs` from
    `src/**` + `Cargo.toml`. A change to any of the four is a *miss*, never a stale hit,
    which is what makes reuse sound: a cached `verified` cannot survive a change to the
    rule that produced it. Only `Verified`/`Failed` are stored (they carry no arena
    handles); `Incomplete`/`Skipped` are re-derived every run. Opt-in via
    `MirOptions.cache` / `cargo verif --cache <dir>`; a `--function` run merges rather
    than drops the other entries.
  - Exit met -- `tests/mir.rs::the_proof_cache_reuses_a_decided_verdict_and_a_change_is_a_miss`
    proves both halves: a *tampered* cache entry shows through (the cache is consulted),
    and a change to the source is a *miss* (the real verdict returns). `mir::cache`'s
    unit test pins that every key part changes the key, and that a tab/newline round-trips
    through the line format.
  - Move: **done**.
- **U8. A public scoreboard.** · P1 · in progress · Kani
  - Exit: `everyday.rs`, an SV-COMP-style set, and `verify-rust-std` functions
    scored for verif **and** Kani on the same inputs, updated by CI.
  - Progress (the verif half, done): `scripts/scoreboard.py` runs `mir_coverage` on
    the three MIR corpora and prints a markdown table of verified/total, with
    `--check` failing if a corpus drops below `scripts/scoreboard-floor.txt`
    (a *regression* floor: verdicts are stable across the gate's toolchains, so a
    drop means a change un-verified a function). `--write-floor` records a raised
    count. Current: everyday 21/24, actuator 18/33, realistic 694/1252. The
    everyday `div_unwrap`/`sum_iter`/`tri` are C7/C11/C12.
  - Progress (CI, done): `.github/workflows/ci.yml` has a `scoreboard` job that runs
    `python3 scripts/scoreboard.py --check`, so the regression floor is enforced on
    every push rather than only when someone remembers. It is a separate job, not a
    gate step, because it takes minutes; the action pins are checked by
    `scripts/check_actions_pinned.py` like every other `uses:`. Measured locally:
    `everyday 21/24, actuator 18/33, realistic 694/1252`, `every corpus is at or above
    its floor`, exit 0.
  - Remaining: the Kani column on the *same* inputs (Kani is already an oracle in
    `examples/kanidiff.rs`, but not a per-function coverage score), an SV-COMP-style
    set, and `verify-rust-std` functions.
  - Move: **build**.
- **U9. Contracts written in the code, not only in doc comments.** · P1 · done · —
  - Gap: a `///` clause is unchecked prose. A typo in a *keyword* is now refused
    (`ensuers:` is caught), but a typo in the *body* is a string the frontend
    parses leniently, and a contract above a struct could leak (fixed, but by a
    reset rather than by the syntax). A doc comment also cannot be reached by any
    of `rustc`'s own checks.
  - Fix: the `spec! { … }` macro, whose matcher is `$($clause:ident : $body:expr,)*`.
    `rustc` parses each body as a real expression, so `requires: n <=,` is
    `error: expected expression` at the contract line; the macro expands to
    nothing, so the artifact carries no byte and no symbol of it (measured: 4 660 B
    rlib, 0 `verif` symbols). Both spellings feed one clause parser, so they cannot
    disagree about what a clause means. A source that says `use verif::spec;` needs
    the frontend's `rustc` run to be told where the crate is, which is
    `mir::verify::extern_options` (it probes candidates and returns the first that
    compiles, so a stale rlib from another compiler is skipped rather than guessed).
  - Exit: an in-code block verifies at build time, a false one fails the build, a
    malformed clause is a compile error, and the artifact carries no prover symbol.
    ✅ Gate 18 check 4 (`tools/build-verify/run.sh`); pinned by
    `an_in_code_contract_can_name_verif_through_an_extern` (both directions: no
    extern is `E0432`, with one it verifies) and
    `an_unresolvable_import_names_the_missing_extern`.
  - Corpus migrated (0.2.0). Every example and corpus file now uses `spec!`:
    `actuator.rs`, `everyday.rs`, `realistic.rs`, the `comparison/` fixtures and
    the inline sources in `tests/mir.rs`. The migration was checked by comparing
    the *verdict table* before and after (`mir_coverage` on each file, diffed row
    by row) rather than by reading: `everyday.rs` 24 rows and `realistic.rs` 1151
    rows came out byte-identical, and the comparison fixtures kept their six
    claims. The doc-comment form survives only where importing `verif` is the thing
    being avoided and in the tests whose *subject* is that reader
    (`scanner_reads_contracts_and_ignores_inner_docs` and its siblings), plus
    `format!`-template fixtures whose braces are placeholders.
  - Migration found one real defect: `assert_not_dropped` tested `src.contains("///")`
    to decide whether a source had a contract, so a `spec!`-only source looked
    contract-free and a dropped function passed the guard. It now matches the
    clause keywords both spellings carry.
  - What remains: the macro is **not** a proc-macro, so it cannot resolve `ret` or
    check that a clause names a real argument — the frontend does that, and a name
    it cannot resolve is a `Skipped` function, not a compile error. Making it a
    proc-macro would need a dependency, which the crate does not take. Recorded,
    not planned.
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
- **A4. A trusted computing base and a semantics.** · P1 · in progress · —
  - Write down what is trusted (parser, MIR-printer stability, executor, blasters,
    solvers), a short formal semantics of the supported MIR subset, and back both
    with mutation testing (exists) and external review before any 1.0 claim.
  - Progress (the document, done): [`docs/tcb.md`](docs/tcb.md) enumerates the TCB
    (rustc's MIR, the text parser, the contract scanner, the executor, both
    blasters, the CDCL solver, the SMT-LIB2 exporter) with the check behind each,
    states the semantics of the supported MIR subset (bit-vector values with an
    explicit `Sign`, a path condition, and per-construct obligations), and lists
    what is refused. Linked from `README.md` and `SECURITY.md`.
  - Remaining: the **external review** the exit names. The document is not a
    substitute for it, and `docs/tcb.md` says so.
  - Move: **build**.
- **A5. A qualification path.** · P2 · **done** (draft) · SPARK (the only one with
    qualification kits)
  - Approach: draft Tool Operational Requirements and a DO-330 TQL-5 / ISO 26262
    TCL plan. Together with Ferrocene, this is the most credible embedded-safety
    differentiator.
  - Progress (draft, done): `docs/qualification.md` is the drafted TOR and plan. It
    states why a verifier is a tool that must itself be qualified, gives the TOR as a
    table whose every row names the gate or oracle that *already* demonstrates it
    (soundness -> `SOUNDNESS.md` + the differential oracles; refusal-over-guessing ->
    `Verdict::Unknown`; determinism -> the scoreboard floor; bounded resources -> the
    budget regression tests; no silent drops -> `assert_not_dropped`; toolchain honesty
    -> gates 9 and 14; reproducibility -> `smtscript` + the z3/Kani/Verus/Coq/Lean
    oracles), and lists what a real qualification still needs -- an independent
    assessment and a signed tool accomplishment summary, both human actions a commit
    cannot supply. It is explicit that `verif` is **not** qualified and that Ferrocene
    qualifies the compiler, not the verifier.
  - Exit: a drafted TOR and qualification plan. **Met** -- `docs/qualification.md`
    (draft).
  - Move: **done** (the draft; the independent assessment is the remaining human step,
    recorded in the doc rather than as a code task).
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

## Review findings (round 9): fixed and tracked

A soundness-focused review of the C8/U3/U7 work and the MIR frontend raised ~50 items.
The false-proof / false-pass ones and the cheap tooling ones are fixed with regressions;
the deep executor and multi-file ones are tracked here.

**Fixed (regression test named):**
- Cache keyed on the root source, not the inlined module text → a contract-only edit in
  a module reused a stale verdict. Now keyed on `Specs::snapshot`
  (`a_contract_only_edit_in_a_module_invalidates_the_cache`).
- Cache keyed by the report label, so two trait impls of one method shared a verdict.
  Now keyed by the MIR definition name
  (`two_trait_impls_of_one_method_get_distinct_cached_verdicts`).
- `verif-wrap` did not forward `--cfg`, so a feature-flipped `cfg!` could pass the build.
  `MirOptions.rustc_args` forwards `--cfg`/`--target`
  (`a_feature_that_flips_a_cfg_makes_the_contract_fail`).
- `--emit-test` replay used a comment declaration / swapped args, and emitted `0` for
  `false`, `255` for `-1i8`. `function_params` reads a real top-level `fn` (skips
  comments and methods) and `render_arg` types each value
  (`a_replay_call_uses_the_real_declaration_not_a_comment`,
  `function_params_ignores_a_comment_declaration`, `function_params_refuses_a_method`,
  `render_arg_types_a_counterexample_value`).
- `cargo verif --emit-test` requires a name, strips `verif` only as the subcommand, and
  requests verification of its target.
- `scoreboard.py --check --write-floor` checks before writing (no silent downgrade).
- `dependency_names` handles dotted keys and quoted sub-tables.
- `build.rs` includes `TARGET` in the engine hash (endianness-dependent `to_be`/`to_le`).
- external-demo always rebuilds, asserts `clamp_percent ... verified`, and gives each
  fixture an explicit target dir.
- The `everyday.rs` "wall" pin no longer rejects a *sound* `Verified` (the contracts are
  sound; only a false `Failed` is forbidden).

**Round 10 (also fixed):** `verif-wrap` refuses a cross target whose pointer width or
endianness the model does not represent; `function_params` is comment-aware across lines
(a `/* { */` no longer blocks replay); `extern_compiles` imports every `--extern`;
`dependency_names` splits before stripping quotes (`"dep".path`); `cargo-verif` errors on
an unmatched `--function`/`--emit-test`; the `everyday.rs` pin allows a panic finding for
`sum_iter`; the TCB path test skips inside a packaged crate; the action fails on exit 2
regardless of `fail-on-findings`; the SARIF smoke test requires an `error` level; docs
(build-time `verif-wrap`, CLI dependency resolution, TQL-5 objectives, TCB executor
evidence = panic replay, input-selection trust). Regressions:
`function_params_is_comment_aware_across_lines`,
`dependency_names_reads_dotted_and_quoted_keys`,
`a_32_bit_target_is_refused_and_the_host_is_not`.

**Round 11 (also fixed):** `--function`/`--emit-test` accepts a module function by its
short name (the unmatched-name guard tail-matches, like `select`); the action fails on any
exit other than 0/1 (a `cargo-verif`-not-on-PATH 101 is no longer a pass); `code_of_line`
tracks **nested** block comments (`/* /* */ */`); the extern probe is `#![no_std]` (a
panic-handler dependency no longer clashes with the probe's std); the `sum_iter` panic
exception is scoped to `sum_iter` alone (`tri`/`div_unwrap` are panic-free under their
preconditions); the TCB path check gates on `[workspace]` in the manifest, not a missing
directory; the README action ref is `@main`. Regressions:
`a_function_filter_accepts_a_module_function_by_its_short_name`,
`function_params_ignores_a_nested_block_comment`.

**Round 12 (also fixed):** the README action ref is a commit-SHA placeholder (no mutable
`@main`); the extern probe aliases each artifact with a synthetic name (`__verif_probe_N`),
so a dependency named `core`/`std` no longer redirects the probe's prelude; `verif-wrap`'s
`source_arg` finds a custom target path by `is_file()` (not a `.rs` suffix); `code_of_line`
carries string/char/raw-string state across lines, so a multiline literal containing `/*`
no longer leaves the scanner in a comment. Regression:
`function_params_tolerates_a_multiline_string_with_comment_tokens`.

**Round 13 (also fixed):** `verif-wrap`'s `source_arg` consumes option values, so a
`--crate-name <path>` whose value is an existing file is not mistaken for the input
(`source_arg_skips_a_crate_name_value_that_is_an_existing_file`); `code_of_line` masks
literal contents to spaces, so a `{` or a fake `fn bad(b, a)` inside a multiline string
neither unbalances the depth nor supplies a signature
(`function_params_masks_literal_braces_and_fake_signatures`); the README action ref is
already a commit-SHA placeholder. Regressions:
`source_arg_finds_a_custom_extension_path`.

**Round 14 (deep fixes):**
- `verif-wrap` now forwards the invocation's **own** `--extern`/`-L dependency=` to the
  MIR emit (Cargo's exact artifacts for this target/profile/feature set), instead of
  re-deriving from `[dependencies]` and ranking rlibs by mtime. This closes *wrapped builds
  lose resolved dependencies* (a binary's own library), *wrong dependency build*, *missing
  workspace/custom target artifacts* and *renamed dependencies* — the alias is the `--extern`
  name, not the artifact basename. Tests: `a_binary_that_imports_its_own_library_builds`.
- `verif-wrap` forwards a **build script** (`--crate-name build_script_build`) unchanged, so a
  `[build-dependencies]` script is not verified without its deps. Test:
  `a_build_script_with_a_build_only_dependency_is_forwarded`.
- Cached-build isolation is documented (a dedicated `CARGO_TARGET_DIR` per mode) and pinned by
  `enabling_verification_after_an_unwrapped_build_still_rejects_a_false_contract`.
- Executor fail-closed guards: `reject_adapters` (a terminal that reads base elements after a
  `map`/`filter` it does not apply is refused), `closure_op_count` (a closure with more than
  one operation is refused, so a compound `map` is not read as its first op), reversed checked
  reductions refused, and `Vec::clear` of an element that may have drop glue refused.
  `iterator_adapter_shortcuts_are_refused_not_mis_modelled` — `filter(..).next().is_some()` on a
  zeroed slice was a **false proof** (`Verified`, reporting `false` as `true`); it is now
  refused (teeth confirmed by disabling the guard). `clearing_a_vec_of_droppable_elements_is_not_proved_panic_free`.

**Round 15:**
- The emitted-test replay (`compile_emitted_test`) now compiles with
  `-C overflow-checks=on`, so a counterexample that is a subtraction underflow panics
  regardless of the test profile (a release `--test` without checks could otherwise pass
  before the function was fixed).
- `Env::set` gained a lone-`Deref`-of-a-box arm: a write through a `Box` pointer (`*b = v`)
  lands in the `boxed` store the read consults, so a later `*b` never returns the value the
  box held at `new`. The shape is currently refused before the write (an unmodelled
  null-deref assert), so the pinned invariant is the soundness one
  (`a_write_through_a_box_pointer_is_seen_by_a_later_read`).

**Round 16 — mutable-`Vec` postcondition length (was a known false proof; FIXED).**
`pub fn f(v: &mut Vec<u8>) { v.push(1); }` with `requires: v.len() == 0` /
`ensures: v.len() == 0` used to be **Verified** (the real length after `push` is 1) while the
true `ensures: v.len() == 1` was refuted: a `&mut Vec`'s contract length read the *entry* value.
The fix mirrors the scalar-ref `ref_final`: the executor now passes each `&Vec`/`&mut Vec`/`&[T]`
argument's *final* length in `ref_final`, and the `post` closure rebinds `{arg}__len` to it
(`spec::arg_name_any` supplies the widthless arg's source name, which `arg_name_of` omits). A
slice/array length cannot change, so the rebind is a no-op there; only a `&mut Vec`'s is the
pushed length. Pinned both ways by `a_mut_vec_postcondition_reads_the_final_length` (false `== 0`
refuted, true `== 1` verified).

**Round 17 — `enumerate` index counts from the enumerate's own start (FIXED).**
`skip(1).enumerate().next().0` reported the raw slice position (`1`) instead of the
enumerate index (`0`), and `rev().enumerate()` likewise. `IterState` gained `enum_start`
(set to `pos` when `enumerate` is applied, which rides the `SliceCopied` arm); the yielded
index is `pos - enum_start`. `enumerate().skip(1)` still yields `1` (skip advances `pos`
after the enumerate recorded its start). Pinned by
`an_enumerate_index_counts_from_the_enumerates_start` (skip/rev index 0, the old raw-position
value refuted, `enumerate().skip(1)` index 1).

**Fixed already (rounds 10–17):** compound-closure refusals, `Vec::clear` of droppable
elements, `*b = v` through a `Box`, mutable-`Vec` postcondition length (16), adapter-chain/
reversed-reduction refusals, `enumerate` index (17), wrapper `--extern`/`-L` forwarding +
build-script forwarding, custom source path, action ref, literal-masking replay lexer,
`source_arg` option-value parsing.

**Tracked (open):**
- Executor/iterator: `iterator_const_len` pin reuse, mapped sums including padded zeros,
  composed `rev`/`step_by`/`skip`/`take`/`nth` adapters. (`all`/`any` audited — they consume
  the iterator by removing the cursor, which is correct.)
- Spec multi-file: `#[path]`/nested external modules (silent skip); method matching after
  external declarations (synthetic line coordinates); `--emit-test` for module functions.
- `verif-wrap`: nested Cargo wrappers, cached-build invalidation (documented, not fixed),
  inactive `#[cfg]` contracts (audited — a `#[cfg]` line clears `pending`, so a disabled
  fn's contract does not leak onto the next function).
- CLI: `cargo verif` (non-wrapper) still uses mtime-ranked `crate_options`, so workspace/
  custom-target/renamed-dependency resolution is fixed only for the wrapper.
- Docs/tooling: SARIF module paths, iterator differential harness, `checked_ilog` base
  (audited — `checked_ilog(base)` is refused, not mis-modelled).

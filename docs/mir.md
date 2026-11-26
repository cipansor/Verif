# The MIR frontend

Part of the [`verif` README](../README.md).

## Verifying real Rust: the MIR frontend

Everything above has the same shape: you write a formula, or a `wp` program, and
the engine discharges it. The obligation is a *model* of the code, and a model can
drift from the code it describes. A human has to keep the two in step, and the
day they stop agreeing the proof is about the wrong program.

`verif::mir` removes that step. It reads the **actual MIR** that `rustc`
lowers a real Rust function to, symbolically executes it, and discharges the
obligations it finds — the overflow, underflow and divide-by-zero `assert`s that
`rustc` itself emits, plus the pre- and postconditions you wrote. Nothing is
re-modelled by hand, so there is nothing to keep in sync.

```console
$ cargo run --features std --example mir_demo
=== examples/mir_targets/actuator.rs ===
clamp            verified (3 obligation(s), 0 panic(s) ruled out)
rate_limit       verified (5 obligation(s), 2 panic(s) ruled out)
sat_add          verified (4 obligation(s), 2 panic(s) ruled out)
sat_sub          verified (1 obligation(s), 1 panic(s) ruled out)
shift_const      verified (1 obligation(s), 1 panic(s) ruled out)
shift_left       FAILED: panic: attempt to shift left by `{}`, which would overflow — n = 16
sat_shift        verified (1 obligation(s), 1 panic(s) ruled out)
sat_mul          verified (3 obligation(s), 3 panic(s) ruled out)
unchecked_add    FAILED: panic: attempt to compute `{} + {}`, which would overflow — a = 32768, b = 32768
unchecked_sub    FAILED: panic: attempt to compute `{} - {}`, which would overflow — a = 0, b = 32768
unchecked_div    FAILED: panic: attempt to divide `{}` by zero — d = 0
unchecked_mul    FAILED: panic: attempt to compute `{} * {}`, which would overflow — a = 128, b = 128
off_by_one_guard FAILED: postcondition — a = 32768, b = 32768
clamp_signed     verified (3 obligation(s), 0 panic(s) ruled out)
checked_div_signed verified (3 obligation(s), 2 panic(s) ruled out)
unchecked_div_signed FAILED: panic: attempt to divide `{}` by zero — b = 0
signed_add_misguarded FAILED: panic: attempt to compute `{} + {}`, which would overflow — a = 128, b = 128
signed_add_guarded verified (2 obligation(s), 1 panic(s) ruled out)
signed_mul_guarded verified (2 obligation(s), 1 panic(s) ruled out)
signed_mul_negative FAILED: panic: attempt to compute `{} * {}`, which would overflow — a = 128, b = 128
checked_neg      verified (2 obligation(s), 1 panic(s) ruled out)
assert_guarded   verified (1 obligation(s), 0 panic(s) ruled out)
assert_misguarded FAILED: panic: assertion failed: n <= 100 — n = 128
panic_guarded    verified (1 obligation(s), 0 panic(s) ruled out)

verified=14 failed=10 incomplete=0
All expectations met.
```

`unchecked_add` is `fn unchecked_add(a: u16, b: u16) -> u16 { a + b }` — ordinary
Rust with no annotations of any kind. The counterexample `32768 + 32768` is read
off the MIR, and `tests/mir.rs` feeds exactly that pair back into the compiled
function and requires the panic. That is the property worth having: the witness is
checked against `rustc`'s own code generator, not against another model.

The witness is rendered with the **source names** `rustc` recorded in its `debug`
bindings — `a = 32768`, `n = 16`, `d = 0` — rather than internal local indices. A
variable with no source name (a temporary, a promoted constant) keeps its
`v{index}:u{width}` spelling, so naming is a readability improvement and never a
loss.

### Contracts: one spelling, in the code it describes

The obvious syntax is an attribute:

```rust,ignore
#[requires(lo <= hi)]
pub fn clamp(x: u32, lo: u32, hi: u32) -> u32 { … }
```

That one still cannot be done. An unknown attribute on a function is not Rust; it
needs a proc-macro to consume it, and a proc-macro is a dependency, which would
break the zero-dependency gate that `scripts/gate.sh` enforces. So the contract is
a `spec!` block: a declarative macro that expands to nothing, placed directly
above the item it describes.

```rust,ignore
use verif::spec;

spec! {
    requires: lo <= hi,
    ensures: lo <= ret,
    ensures: ret <= hi,
}
pub fn clamp(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo { lo } else if x > hi { hi } else { x }
}
```

The specification and the code are one artifact: the same file is compiled,
executed and verified. There is no separate model to transcribe and no second file
to keep in step, which is the whole reason a proof here is about the program you
actually run. The macro expands to nothing, so it costs a deployed artifact zero
bytes and leaves no symbol behind.

The matcher is structured (`$clause:ident : $body:expr`), not a token soup, so
`rustc` parses each clause body as a real Rust expression: `requires: n <=,` is a
compile error *at the contract line*, and a misspelled `ensures` cannot silently
drop an obligation — the identifier is a token the macro matches, not prose it
ignores. It needs `use verif::spec;` to resolve, so `verif` must be an ordinary
dependency and the build script must tell the frontend where to find it; the
"Shape A" section below has the full recipe. A macro that expands to nothing is a
claim about the artifact, not about the verification, so `tools/build-verify/run.sh`
(gate 18) checks both the true and the false direction for this spelling.

**The doc-comment spelling still parses, and the corpus still exercises it.**
`/// requires:` / `/// ensures:` feed the *same* clause parser, so the two spellings
cannot disagree about what a clause means. It survives for two reasons: a source
that must not import `verif` at all (a corpus file a reviewer wants to paste into a
plain crate), and a `format!`-style fixture whose braces are placeholders. Every
example and every corpus file in this repository uses `spec!`; the doc-comment form
appears only where importing `verif` is the thing being avoided, and in the tests
whose subject *is* that reader.

#### What "fused with the code" looks like

The point of one spelling is that there is no second artifact. This is a whole
module — the code, its specification and its loop induction argument in the same
file, compiled by the same `rustc` and verified by the same build:

```rust,ignore
use verif::spec;

spec! {
    requires: total <= 10_000,
    requires: step >= 1 && step <= 1000,
    invariant: total <= 10_000,
    variant: 10_000 - total,
    ensures: ret <= 10_000,
}
pub fn accumulate(total: u32, step: u32) -> u32 {
    let mut total = total;
    while total < 10_000 {
        let next = total + step;
        total = if next > 10_000 { 10_000 } else { next };
    }
    total
}
```

There is no `accumulate.spec` beside it, no model to re-state, no generated proof
script to regenerate. The `invariant:` and `variant:` lines are the induction
argument, sitting next to the `while` they justify; delete the loop and the
clauses stop describing anything, which the verifier reports rather than ignores.
When a clause is wrong the build fails naming the obligation and a witness, the
same way a type error does — the specification is a checked part of the program,
not a comment about it.

This example is the one in the README, and it is not decorative: it was run
through `mir_coverage` while it was written. Two earlier drafts were *refuted* —
the first because `total` was unconstrained at entry (the invariant does not hold
for `u32::MAX`), the second because `saturating_add` clamps at `u32::MAX` and not
at `10_000`, so the invariant was not preserved. The version above reports
`verified`, 7 obligations discharged and 1 panic ruled out. A specification fused
with the code is only worth having if the tool will tell you when it is wrong,
which is exactly what those two refutations were.

The same holds for a shape the verifier cannot decide yet: it reports the
function as `Incomplete` with the reason, rather than quietly proving something
weaker. A specification that is *fused* with the code is only useful if the tool
is honest about the part it did not check.

A loop is proved by an `invariant:` clause rather than by unwinding. It is the
induction hypothesis: true on entry to the loop head, and left true by one
iteration. Naming it is what makes a loop with a symbolic trip count decidable
instead of cut off at an unwind bound:

```rust,ignore
spec! {
    requires: n <= 8,
    invariant: i <= n && s == i,
    ensures: ret <= 8,
}
pub fn sum_to(n: u8) -> u8 {
    let mut s = 0u8;
    let mut i = 0u8;
    while i < n { s += 1; i += 1; }
    s
}
```

An invariant may name any local, not just the parameters. It is checked twice —
once on entry to the head, once across an iteration — and at the head the locals
the loop can write are replaced by fresh values before the invariant is assumed,
so the state after the loop is *any* state satisfying the invariant and the exit
condition, not the state of the first pass. Omitting that step would prove false
postconditions; `AGENTS.md` records the measured case.

### Termination: a `variant:` measure

An invariant alone proves *partial* correctness: the loop is safe **if** it stops,
which a loop that never stops satisfies vacuously. A `variant:` line names the
quantity the loop counts down, and turns that into *total* correctness:

```rust,ignore
spec! {
    invariant: i <= n,
    variant: n - i,
    ensures: ret == n,
}
pub fn count_to(n: u8) -> u8 {
    let mut i = 0u8;
    while i < n { i += 1; }
    i
}
```

At the back edge the measure after one iteration is compared against the value at
the head, and the obligation is `I && guard => V' < V`. On a fixed bit width a
strictly decreasing sequence cannot be infinite, so no separate lower bound is
needed — and adding one would be wrong, because the measure is a machine word,
where "going negative" is just a smaller word, which is the descent that proves
termination. `while i < 5 { i += 0 }` is therefore reported as a failure on
`loop variant decreases` rather than as verified; before this clause existed it
came back `Verified`, which is the soundness hole the measure closes.

The measure is not inferred, for the same reason the invariant is not: a guessed
measure is a guessed proof. A loop with no `variant:` is still checked for partial
correctness, and no termination claim is made for it. A `variant:` with no
`invariant:` is refused, because the invariant is what locates the loop the measure
is about.

### Recursion: a `decreases:` measure

A recursive function is proved by *induction*, not by unrolling. Adding a
`decreases:` line names a measure — an expression in the arguments — that must be
non-negative at entry and strictly smaller at every self-call. The self-call is
then answered by the function's own contract instead of being inlined:

* the call's arguments must satisfy the `requires:`;
* the measure must strictly decrease (and stay non-negative, for a signed
  measure);
* the `ensures:` is *assumed* for the call's result, which is the induction
  hypothesis.

```rust,ignore
spec! {
    requires: true,
    decreases: n,
    ensures: ret == n,
}
pub fn count_down(n: u8) -> u8 {
    if n == 0 { 0 } else { count_down(n - 1) + 1 }
}
```

The measure is what makes the assumption an induction rather than a circular
argument: a strictly decreasing sequence in a well-founded order is finite, so
there is a base case, and nothing is assumed there — the body has to establish
the postcondition on its own. The base case is therefore still a proof
obligation, and a body that gets the base case wrong is refuted with a witness
(`a_recursive_lie_cannot_prove_this` in the corpus). A measure that does not
shrink, or a call that leaves its own precondition, is likewise a definite
failure rather than a silent pass. Without a `decreases:` line a self-call has no
induction principle, so it is inlined once and the result is reported
`Incomplete` at the depth bound — an honest "I could not decide", never a guess.

A contract may name a field of a struct argument, and a component of a tuple
return, by the same syntax the Rust body uses:

```rust,ignore
struct Bounds { lo: u8, hi: u8 }

spec! {
    requires: b.lo <= b.hi,
    ensures: ret >= b.lo && ret <= b.hi,
}
pub fn clamp_bounds(b: &Bounds, v: u8) -> u8 {
    if v < b.lo { b.lo } else if v > b.hi { b.hi } else { v }
}

spec! {
    requires: a <= b,
    ensures: ret.0 <= a,
}
pub fn split(a: u8, b: u8) -> (u8, u8) {
    if a <= b { (a, b) } else { (b, a) }
}
```

The MIR dump names the struct but never prints its layout — `_1: &Bounds` and
nothing more — so the field *indices and widths* are read from the source, the
same place the contract text comes from. That keeps the two consistent by
construction: a field the layout reader does not find cannot be named by a
contract that would otherwise be checked against it.

Each field is its own symbolic input. This is the honest model, not a
convenience: the frontend cannot see the caller's invariant relating two fields,
so assuming `lo <= hi` would be unsound. `examples/mir_targets/realistic.rs`
carries a `field_alias_tripwire` whose *failure* is the evidence that the two
fields are distinct variables rather than one aliased one; `tests/mir.rs`
requires that failure.

A projection that cannot be resolved is refused, never dropped. `c.lo` where `lo`
is not a field of `Bounds` is an error naming the field, and a projection on a
non-aggregate return is refused too — if the conjunct vanished instead, the
function would verify against a weaker contract than the source states.

A slice argument is named by its length and by its elements:

```rust,ignore
spec! {
    requires: xs.len() > 0,
    ensures: ret == xs[0],
}
pub fn first_of(xs: &[u8]) -> u8 {
    xs[0]
}
```

A slice has no length in its type, so `xs.len()` is a *symbolic input* — whatever
the caller passed — not a constant. The same variable is what the body's
`PtrMetadata(_1)` reads and what the `assert` before `(*_1)[_2]` checks, so the
bounds check is discharged from the precondition rather than assumed. Each element
is its own input per index: `xs[0]` and `xs[1]` are two variables, and a
`slice_alias_tripwire` in `examples/mir_targets/realistic.rs` fails precisely
because of it. Only a literal index is modelled; `xs[i]` with `i` a parameter is
refused rather than resolved to an arbitrary element.

A fixed-size array is named the same way, but its length is not an input:

```rust,ignore
spec! {
    requires: a[0] <= a[1],
    ensures: ret == a[1],
}
pub fn max_of_pair(a: [u8; 4]) -> u8 {
    if a[0] > a[1] { a[0] } else { a[1] }
}
```

An array's length is part of its type, so `a.len()` is the *constant* `4` and not a
fresh variable — binding it to an input would admit lengths the type excludes, so a
contract proved at length 4 would claim to hold at any length. The body's bounds
check is against that same literal (`Lt(_2, const 4_usize)`), so it is discharged
from the index being a literal. Elements are inputs per index exactly as a slice's
are, and `array_alias_tripwire` fails to show it. An index past the length is
refused rather than bound, since the element does not exist.

A literal in a contract takes its width from the operand it meets, not from the
widest name in scope:

```rust,ignore
spec! {
    requires: true,
    ensures: ret <= 255,
}
pub fn idx(a: [u8; 4]) -> u8 { a[0] }
```

Here `a` contributes a 64-bit length, but `ret` is 8 bits, so `255` has to be read
at 8 bits. Sizing it from the length instead made the comparison ill-formed, and an
ill-formed term makes *every* obligation in the run `Unknown` — so the function was
reported incomplete for a reason that had nothing to do with its body. A literal too
large for the operand's width is refused rather than truncated: `a <= 300` for a
`u8` must not become `a <= 44`.

The fit check is against the operand's *signed* range when the operand is signed,
not merely its bit width. `128` for an `i8` fits in eight bits, but those bits are
`0x80`, which is `-128` signed — so a check that only asked "does this fit in eight
unsigned bits?" accepted it and read `x <= 128` as `x <= -128`. rustc rejects
`x <= 128` for an `i8` ("literal out of range for `i8`"), and the wrong reading is a
false proof: `requires: x <= 128` with `ensures: ret != 127` *held*. The same holds
for a negation, where `-129` for an `i8` wraps to `127` at eight bits and `x >= -129`
became `x >= 127`. Both are refused now. The `i8::MIN` bound shares the bit pattern
`0x80` and still reads, which is why the fix distinguishes a non-negative literal
from a signed constant instead of refusing every `0x80`. The check runs even when
both operands are constants and no typed name is present: `128 <= i8::MAX` is a
`literal out of range` error, and reading `128` as `0x80` made it `-128 <= 127`,
always true — so it is refused, while `127 <= i8::MAX` and `i8::MIN <= i8::MAX` read.

A constant *arithmetic* expression is folded exactly, so one that overflows its
operand width is refused rather than wrapped. `200u8 + 100u8` is a rustc const-eval
error, but folding it mod 256 gave `44`, so `x <= 200 + 100` read as `x <= 44` — a
*stronger* precondition than the author wrote (`x <= 300`, which admits every `u8`)
— and `ensures: ret <= 44` was proved for a body that fails at `x == 100`: a false
proof. The same applies to `0 - 1` (underflow), `255 + 1`, `200 * 2`, and to a
constant `i8::MIN / -1` or `% -1`, which overflow the signed operand. The fold
widens past the operand width to keep the value exact, so the ordinary fit check
refuses the shape when the operand it meets is too narrow, while a sum whose overflow
is legal because a wider operand types it (`x as u16 <= 200 + 100` is `300`) still
reads. The widening is at the *expression's* signedness, so `i8::MAX + 1` is refused
too: `128` fits an unsigned byte but not a signed one, and an unsigned widening would
have left it at eight bits where it read as `-128` — a false proof in place of the one
being fixed.

A *signed* constant meeting an *unsigned* operand is refused, because Rust does not
type it either — at every level where two operands meet. A literal takes its type
from the operand it meets, so `x == -1` for a `u8` does not compile ("cannot apply
unary operator `-` to type `u8`"), and `x + -1`, `x - -1`, `x % -1`, `x * -1`,
`x & -1` and `x ^ -1` are the same shape. The reader carries the negation as a bit
pattern at the operand's width, so it read `x == -1` as `x == 255`, `x + -1 >= 0` as
`x + 255 >= 0`, and `x ^ -1 <= 255` as `x ^ 255 <= 255`. The first made
`ensures: ret == 255` *proved* for a body returning `x`; the second made
`requires: x + -1 >= 0` trivially true, so *any* postcondition was proved; the third
was always true. All false proofs, and the arithmetic and bitwise ones survive a
comparison-only check — the refusal has to sit at each operator, because that is
where the constant meets the name. Refusing the shape is the only sound answer: the
wrong reading is a proof, and a proof cannot be a warning. The refusal is narrow — a
bare literal is unsigned, so `0xFF` for a `u8` still reads as `255`, `x + 255 >= 0`
and `x & 255 == x` still read, and `x <= 127` for an `i8` is legal with the constant
on the unsigned side. Only a signed *constant* against an unsigned *name* (in either
order) triggers it, which is exactly the shape Rust rejects. The test that pins this
enumerates all sixteen operators (`== != < <= > >= + - * / % & | ^ << >>`) rather
than the levels a human remembered, because the hole was found one level at a time
and reasoning about the next level is what kept being wrong.

Two *names* of different signedness are refused for the same reason: `a > b` for an
`i8` and a `u8` is `E0308: mismatched types`, and the body reads each operand at its
own signedness, so a contract that picked one sign could disagree with the body about
what the operator means. Refusing keeps the answer "the tool could not run" rather
than a verdict on a program that does not compile. The refusal is narrow: two names of
the *same* signedness still compare, and a name against a literal of either value
still reads. A shift is exempt, because Rust lets the shift amount have its own type.

An *untyped* constant — the complement of a literal (`!0`), or a fold of untyped
operands — has no type of its own, and Rust types an untyped constant as `i32`, so
`!0` is `-1`. Where the signed and unsigned readings differ, the shape is refused
rather than guessed: at `>>`, `/`, `%`, an ordering comparison, a widening cast, and
at `==`/`!=` too. Equality is included because the two readings are different
*values*, not a different ordering of one — the reader built `255u8 == 255` from
`!0 == 255` and *verified* it, though Rust calls it false (a false proof). Any typed
operand fixes the reading, and two bare literals stay unambiguous.

Unary `-` on an unsigned operand is refused as well: `-x` for a `u8` is `E0600`, and
the reader's `0 - x` is a value Rust never produces. A signed name, and a bare literal
(Rust defaults it to a signed `i32`), still negate and read.

A constant widened to meet a wider operand fills from the value it **denotes**, not
blindly from the operand's sign. A bare literal is non-negative and zero-extends, so
`(x as i16) == 255` for a `u8` `x` is true — the same as Rust's `(255u8 as i16)`.
Filling from the signed operand instead sign-extended the `255` to `65535` and
*refuted* a postcondition Rust accepts (a false refutation). A typed signed constant
keeps sign-extending, so `-1 as i32` is still `-1`.

An *opaque* constant (`!0`, a fold of untyped operands) takes the operand's sign,
because that is the type Rust infers for it — but the reader holds a complement at the
*scope's* width, and no extension of that recovers the operand-width value (`!0` against
a `u16` is `65535`, not `255`). So an opaque widening is **refused** rather than guessed;
a *fold* is a value, not a bit pattern, and still widens exactly.

A numeric literal's **type suffix is kept**: `0u8` is unsigned, so `-1 <= 0u8` is an
error (a `u8` cannot be negated) and is refused rather than silently read as a signed
comparison. Dropping the suffix left `0u8` indistinguishable from a bare `0`, so a
mismatched constant pair was decided; the refusal now covers a signed constant meeting
an unsigned operand whether the other side is a name or another constant. Valid pairs
(`-1i8 <= 0i8`, `-1 <= 255`) still read.

A struct or enum whose body closes on its declaration line is read from that line,
not by opening a cursor. `pub struct B { pub lo: u8 }` used to leave a field cursor
open with no closing brace left to read, so every following line — the `///`
contracts and the `fn` items — was consumed as struct fields. Those functions then
had no contract at all and were neither verified nor reported as skipped: they
silently left the check set. A body that does not close on the line still opens a
cursor. The same distinction the enum reader already made for a refused one-line
body now applies to a readable one-line struct body.

A contract written above a struct or enum belongs to that item, not the next
function. The layout heads used to match and move on without clearing the pending
contract, so a doc comment above a struct carried over to the next `fn`. A leaked
`requires` is a false proof when it is satisfiable, because it narrows the inputs the
postcondition is checked for: `requires: x == 0` above a struct made
`ensures: ret == 0` for a body returning `x` verify. The contract now attaches only
to the item it was written above.

A slice or array element is read at the element type's signedness in the *contract*,
not only in the body. `bind_indexed_elem` recorded an `i8` element's sign for the
executor's seeds but not for the parser, so `xs[0] >= 0` over a `&[i8]` read as an
unsigned comparison — always true — and was *proved* for a body returning the element,
with `i8::MIN` as the counterexample. The symbolic-index chain (`a[i]` over `[i8; 4]`)
had the same hole. The existing `signed_slice_element_tripwire` did not catch it: its
body reads the element, and the body's own (correct) reading dominated the verdict, so
it was already FAILED for another reason. Both sign records are now made, and both
entries verify→refute when either is removed.

A literal is read at the radix it is written in. `0xFF` is `255`, `0b1010` is `10`
and `0o17` is `15`, in any width and with underscores or a type suffix (`0xFFu8`,
`0xFF_FF`). Reading every literal as decimal silently made `0xFF` equal `0` — the
digit run stopped at the `x` and the rest was skipped as a type suffix — and a wrong
value in a precondition is a *false proof*, not a refusal: `requires: x == 0xFF`
became `x == 0`, so `ensures: ret == 0` was proved for a function returning `255`. A
literal that is not an exact integer — a digit invalid for its radix (`0b12`, `0o9`),
no digits (`0xg`), an unknown suffix (`0xFFg`), or a value past `u64` — is refused,
so the fix does not trade one silent number for another.

The scanner is deliberately strict. A `requires:`, `ensures:` or `invariant:` that sits before a
`const`, a `struct` or a module comment is *not* attached to the next function, so
a misplaced contract is dropped rather than silently applied to the wrong item.
A contract expression outside the grammar — a function call, an unknown name, a
shift by a symbolic amount — is refused rather than approximated. An `invariant:`
clause carries no loop label, so a function may have at most one; a second is
refused rather than guessed at, since pairing the wrong text with the wrong loop
would check an obligation that does not mean what the source says.

The expression grammar is Rust's own subset, with Rust's precedence, so a contract
reads like the code it describes:

| Level (loosest first) | Operators |
|---|---|
| bitwise or | `\|` |
| bitwise xor | `^` |
| bitwise and | `&` |
| shift | `<<` `>>` |
| additive | `+` `-` |
| multiplicative | `*` `/` `%` |
| unary | `-` (negation) `!` (bitwise NOT on a value, negation on a predicate) |
| comparison | `==` `!=` `<` `<=` `>` `>=` |
| logical | `&&` `\|\|` |
| cast | `as u8` … `as u64` (an atom followed by one or more `as <type>`) |

`>>` is arithmetic on a signed operand and logical on an unsigned one, and `/`/`%`
take the signed quotient or remainder when either operand is signed — the same
choices the body makes. A *negated literal* is signed, so `-7 % 3` is `-1` (the sign
follows the dividend), `-7 / 2` is `-3` (truncated toward zero) and `-7 < 3` is
true — Rust does not compile `let x: u32 = -1;`, so a negation is its own evidence
of a signed type. A unary `-` binds *tighter* than `as` (`-x as u8` is
`(-x) as u8`, type `u8`). A unary `!` on a *value* is bitwise NOT and binds tighter
than `==`, so `!x == 5` is `(!x) == 5` (`x == 250` for a `u8`), not `!(x == 5)`; on a
parenthesized *predicate* it negates, so `!(x == 5)` is `x != 5`. A cast *extends*:
`-1i8 as i16` is `-1`, and `-1i8 as u16`
is `65535`, not `255`. A shift amount must be a *constant expression* — `x >> 1 + 1` is
`x >> 2` — and a *symbolic* amount is a barrel shifter in the body and is refused in a
contract rather than guessed at. A divisor of constant zero is refused however it is
spelled (`0`, `1 - 1`, `2 - 2`), matching rustc's `unconditional_panic` lint.

The engine's words are 64 bits, so a `u128`/`i128` type is refused rather than
mis-modelled: a function with a 128-bit argument, local or return, and a contract
casting *to* one, both report the function as skipped. This is a refusal, not a
crash — a width the engine cannot hold is decided before any width-taking
constructor runs.

### A diverging call is a checked panic, not a dropped line

`assert!`, `debug_assert!`, `panic!`, `unreachable!`, `todo!`, `unwrap`, and the
bounds and slice checks `rustc` inserts all lower the same way: a call into
`core::panicking` (or a user function returning `!`) with **no `[return: bbN]`
arm**, because the call never returns.

```rust,ignore
spec! {
    requires: x <= 200,
    ensures: ret == 1,
}
pub fn f(x: u8) -> u8 { assert!(x <= 200); 1 }
```

The parser recognised only the `[return:` shape, so this terminator came back
`Unknown("missing")`, the path was reported unmodelled, and the whole function was
`Incomplete`. The most ordinary safety guard in Rust was never checked at all —
`f` above was not proved, it was *skipped*, and a caller reading "incomplete" for
an `assert` would be right to distrust the tool.

The two call shapes are now read separately, and the diverging one becomes a
**panic obligation** rather than a silent drop:

* the obligation is `path`, "is this call reachable", discharged by `Unsat` — the
  same polarity as the `assert` terminator, and for the same reason. The `switchInt`
  that routes into the call already carries `!guard` in its path, so the query is
  really about the guard;
* the fall-through of a *non*-diverging `assert` terminator still assumes the
  guard, so code after an `assert!` may rely on it;
* the report names the failure from the string literal the dump passes, so an
  unproved `assert!(x <= 200)` reads `panic: assertion failed: x <= 200` with the
  counterexample that fires it, instead of a mangled callee path. Edition 2024 does
  not pass a literal for a *formatted* message — `panic!("bad {}", x)` builds an
  `Arguments` through `core::fmt` — so those pieces are recovered from that chain,
  with the placeholder count taken from the call's own argument count
  (`Arguments::new_v1::<P, A>`) rather than guessed from the pieces.

This is the sound direction, and it is the same shape as the `DivergentCall`
finding in `wp` — a construct that cuts a path off must be *recorded*, because
everything downstream of it is vacuously true. The teeth are a matched pair:
`an_assert_is_checked_and_discharged_under_its_precondition` pins the proof, and
`an_unproved_assert_is_refuted_with_a_counterexample` pins the refutation. A user
function returning `!` is treated the same way, so `if x == 0 { die(); }` is a
failure at `x == 0` and is proved unreachable under `requires: x != 0`.

`a_formatted_panic_message_is_recovered_from_the_fmt_chain` pins the message
recovery on whichever toolchain `VERIF_RUSTC` names — the `new_v1`/promoted-array
spelling on the MSRV and the `new::<LEN, A>` byte-template spelling on stable — and
`a_literal_panic_macro_names_its_message` pins that `unreachable!()` and `todo!()`,
which pass a literal, still name the text the programmer wrote. A name is never
reported as its type arguments: `panic!("{}", x)` has no literal piece at all, so it
falls back to the callee's name read through its generics (`panic_display`, not
`<u8>`).

### A `drop` is a terminator with a real successor

`drop(_x)` is the terminator `rustc` emits for a local whose type has drop glue, and
it prints with the same `-> [return: bbN, unwind continue]` shape as a call. So the
call arm claimed it, and because a `drop` line has no ` = ` destination,
`parse_call_head` returned `None` and the arm's fallback turned the whole line into
`Unknown` — reported as "unmodelled terminator", dropping the path. Every RAII local
lowers to a `drop`, so a function holding a `Vec`, a `String`, a lock guard or a user
`Drop` was `incomplete` for a reason that had nothing to do with its contract. It has
its own parser arm now, and `successors` knows the terminator has a normal successor,
so the path continues past it. (The old code had a `drop(` branch too, but it was
dead: the call arm above it matched first, because the line contains ` -> [return:`.)

Three cases, and the middle one is the soundness boundary:

* a type with **no drop glue** runs nothing, so the terminator is a no-op. rustc
  emits no `drop` for such a type, so this arm is *defensive* — measured over
  `realistic.rs`, 0 of 6 `drop` terms are glue-free — and its check lives in a unit
  test rather than in a corpus fixture that could not exercise it;
* a **user `impl Drop`** has a body in the dump, so it is executed through the same
  inliner a method call uses. The destructor's `self` is `&mut T`, so the dropped
  place is the argument and the `by_ref` copy-back carries the destructor's writes
  back to the caller. A destructor that panics is therefore a real obligation:
  `destructor_panic_cannot_prove_this` is refuted with the witness that fires the
  destructor's own `assert`, and its guarded twin verifies;
* **anything else** — a `Vec`, a `String`, a `Box`, a `MutexGuard`, or a generic `T`
  whose glue the dump does not spell — is **refused**, never assumed to be a no-op.
  This is the one place the review's first suggestion ("a std container is a no-op
  that changes no scalar state") was unsound: the dump cannot tell a `Vec` from a
  struct holding a user-`Drop` field, because both print the same `drop(_x)` line, so
  treating the container as a no-op would prove a function panic-free whose destructor
  panics. A refusal is a lost proof, never a false one.

The parser side is pinned by `parses_a_drop_terminator`; the executor's three cases by
the `tests/mir.rs` Drop tests and the `realistic.rs` fixtures; the no-op table by
`a_glue_free_type_has_a_noop_drop`, which needs no compiler. The `rustc_public` oracle
agrees on the parser's reading of the terminator's real shape.

### What is read from where, and why

| Part | Source | Reason |
|---|---|---|
| the body | `rustc --emit=mir` | the real lowering, including the checks `rustc` inserts |
| the contract | the source text | MIR carries no attributes or doc comments |
| the compiler | `VERIF_RUSTC`, else `rustc` | `--emit=mir` is stable, so the `rustc` on `PATH` is enough; the variable exists to point the frontend at a *different* compiler without disturbing cargo's own |
| the edition | `MirOptions::edition`, else `VERIF_EDITION`, else the nearest `Cargo.toml` | the edition changes the lowering, so a verdict is only meaningful under the edition the crate is built with |

The edition is resolved in that order, and it is never *guessed*: the first match
wins, and a value that is set but not one of `2015`/`2018`/`2021`/`2024` is an
error rather than a silent fallback. A file that lives in a crate takes the
edition from the nearest `Cargo.toml`'s `package.edition` (resolving
`edition.workspace = true` against the workspace root), and a `[package]` that
omits the key resolves to **2015**, which is Cargo's own default for a package
that does not state one. Only a *loose* file -- one with no manifest above it --
has no crate edition to infer, and it must be given one:

```bash
# A loose file has no Cargo.toml, so name the edition explicitly.
VERIF_EDITION=2021 VERIF_RUSTC="$(rustup which rustc)" \
  cargo run --features std --example mir_coverage -- /tmp/probe.rs
```

A program calls the frontend directly through `MirOptions { edition: Some(..) }`,
which takes precedence over both; the environment variable is for the examples and
the tests, which have no options struct to fill in.

**One boundary on the probe tools.** `mir_coverage` (and the other single-file
examples) runs `rustc` on one file with no Cargo graph behind it, so a source that
opens with `use verif::spec;` needs an `--extern` entry the example does not supply.
The corpora in this repository avoid that with a local no-op shim
(`macro_rules! spec { … }`, one line at the top of the file), which is why
`mir_coverage` decides them. A file you write for a real crate should import the
macro instead, and then it is the **build script** route that reads it — `build.rs`
locates the rlib it is already linked against with
`verify::extern_options_with` and passes the options to `verify_file_with_opts`,
which is the recipe in "The same function, two ways" above. If you do want
`mir_coverage` on a `use verif::spec;` file, add the shim or call the frontend from
a program that fills `MirOptions.externs` — the example deliberately does not guess
an rlib path, because a guessed one is either the wrong compiler's or the wrong
features' and surfaces as a compiler error about a program that is fine.

The five differential oracles (z3, Kani, Lean, Coq, Verus) all build their terms
with `smt::` calls, so they start *below* the contract reader. That left the reader
— the layer that turns contract text into terms — with no independent check, and
three parser bugs in a row (a negated literal read as unsigned, so `-7 % 3` was `0`;
a cast applied before a negation, so `-x as u8` had the wrong type) were found by
hand rather than by a gate. `the_contract_reader_agrees_with_rustc_on_a_grid` in
`tests/mir.rs` closes it against `rustc` itself: a *value* construction (the body is
the expression, so `ret == <expr>` is the agreement claim) and a *guard*
construction (`x == v && <expr> > t`, which is where a wrong *type* shows up, since
the value of `-x as u8` is the same under both readings but its type is not). The
oracle is itself checked by reverting each fix and confirming it fails.

### The edition and the minimum compiler

The crates are **edition 2024**, and `rust-version = "1.85"` in both manifests.
Edition 2024 is what the language is now: `gen` is reserved, `unsafe_op_in_unsafe_fn`
is on, and the pattern binding modes are the strict ones. Since 1.85 is exactly the
release that stabilised the edition, the floor and the edition are the same
decision — there is no version that takes one without the other.

The floor is a *lower* bound, not a pin. Everything here builds on current
stable (1.100 at the time of writing), and the MIR frontend runs on that same
stable `rustc`: `--emit=mir` is a stable flag, checked here down to 1.85, so no
part of the product needs a nightly. Only two *oracles* do — `tools/mir-oracle`
links `rustc_public` and the `rustc-dev` component, and Kani tracks a nightly —
and an oracle is a test tool that never enters the dependency tree. The
oracles' own toolchains move independently and are all newer: Verus pins the
compiler version its driver reports (CI installs exactly that toolchain), Kani
tracks a nightly, and Ferrocene — the qualified compiler, which is the one whose
ceiling could matter for a safety build — is currently downstream of Rust 1.96,
comfortably above 1.85. So no oracle forces the floor down, and none is held
back by it.

The MSRV is deliberately *not* raised to follow them. A `no_std` crate that ships
into a bare-metal safety build is the one place a high floor costs something real:
it locks out qualified and long-term-support toolchains that lag upstream. 1.85
buys the current edition at the oldest version that has it, and every later
compiler still works, so nothing is given up by staying there.

### The arithmetic, and one new primitive

MIR makes the checks explicit, so modelling them is most of the work. `a + b`
lowers to `AddWithOverflow` plus `assert(!(_3.1))`; the same for `SubWithOverflow`
and `MulWithOverflow`, and `/` comes with a `assert(!(_6))` for a zero divisor. The
`!` matters: rustc prints the failing polarity, and dropping it inverts every
check. `tests/mir.rs` and the parser's unit tests pin that.

Modelling overflow exactly needed a widened product for the *signed* case, which
exposed a fact worth writing down: **`smt::truncate` zero-extends when the target
is wider.** A signed `a * b` at `u16` is computed at 32 bits and compared with the
sign-extension of the wrapped result, so the predicate is exact rather than
approximate. The *unsigned* test is exact *without* widening, because
`x * y > MAX` iff `y != 0 && x > floor(MAX / y)`: the restoring divider decides it,
no `2w`-bit multiplier is built, and the form matches the guard a saturating
multiply is written with. That is what turned `sat_mul` from `incomplete` into
`verified` — the guard and the overflow test become structurally identical terms, so
the boolean fold collapses `guard && !guard` to `false` before the divider is ever
blasted (see the note on the multiply-overflow predicate below). Division needed
something the engine did not have, so `smt::divmod` builds a restoring divider out
of shifts, subtract, compare and select. It is exact — `tests/divmod.rs` checks it
against Rust's own `/` and `%` at every interesting boundary and proves
`(x / y) * y + x % y == x` and `x % y < y` symbolically. `y == 0` is given a
*defined* value (quotient all ones, remainder the dividend) rather than being left
as a hole, and rustc's own divide-by-zero assert is what turns that case into a
reported panic.

A *variable* shift amount needed two things that turned out to be one. The engine
gained `smt::shift_var`, a barrel shifter of `log2(w)` conditional stages, so
`x << n` is now in the vocabulary rather than refused. But the frontend also had to
start *assuming* an assert it had already checked: `Term::Assert` pushed the
fall-through block with the incoming path unchanged, so `assert(n < 16)` was proved
(a panic is reported when `n == 16`) and then discarded, and every obligation after
it was discharged as if `n` could still be 16. That is sound — the guard is checked
separately — but it is needlessly weak, and it is wrong for a guard the *caller*
wrote. The fall-through path now carries `satisfied`, which is what lets `sat_shift`
prove and what makes the modelled shift meaningful.

The shift is only half of it. rustc prints a cast constant as
`const 3_i32 as u32 (IntToInt)`, and `parse_rvalue` matched the `const ` prefix
*before* the ` as ` form, so the whole string went to `parse_const`, which read
`i32 as u32 (IntToInt)` as a type name and produced a constant with no width. Every
guard written against such a constant — `x << 3`, and the `assert(n < 16)` for a
`u16` shift — was then unmodelled, which is why a plain constant shift used to come
back `incomplete`. Checking the cast first fixes both. `tests/shift.rs` checks the
barrel shifter against Rust's own `<<` and `>>` at the interesting amounts, proves
it agrees with the constant path symbolically, and requires that a variable shift is
*not* the identity so a shifter that returned its input cannot pass.

### `core::num` is modelled rather than called

The `checked_*`, `saturating_*` and `wrapping_*` families are how real Rust writes
arithmetic that must not panic, and a call the frontend cannot model makes the
whole *path* unknown. So these are computed from their operands instead of being
refused. `src/mir/intrinsics.rs` holds the model:

- `wrapping_*` is the plain operator, because the plain operator already takes the
  result modulo `2^w`. The term is the *same term* `a + b` produces, not a second
  definition that could drift from it. A `wrapping_mul` needs no overflow test, so
  it is admitted up to `MUL_MAX_WIDTH` (`32`) rather than stopping where the widened
  product does; a `u32` `wrapping_mul` is a plain 32-bit multiply and settles in
  milliseconds.
- `saturating_*` is `ite(fails, bound, plain)`, where `fails` is the very predicate
  rustc's own `assert` reads and `bound` is the sign of the overflow. A function
  written with `saturating_add` and one written with a hand-rolled guard are decided
  by one rule.
- `checked_*` is an `Option<T>`: the tag is `1` where the operation is defined and
  `0` where it is not, and the payload is the result. The tag is a *term*, not a
  constant, so the `switchInt` on it takes the right arm on each path. rustc emits
  the downcast payload read only inside the `Some` arm, which is what makes
  recording the payload unconditionally sound.
- The unary `neg` and `abs` are `0 - x` and "negate if negative" in all four
  families, and the six bit counts (`count_ones`, `count_zeros`,
  `leading_zeros`, `leading_ones`, `trailing_zeros`, `trailing_ones`) are sums over
  the operand's bits. The three *complement* counts are not a second summation:
  each is `core`'s own definition, the corresponding positive count of `!x`, so
  `count_zeros` is `count_ones(!x)` and a fix to one half cannot leave the other
  behind. `!x` is spelled the way the executor spells it, so the model's `!x` and
  the body's `!x` are the same term.
- `is_power_of_two` is a modelled shape whose *return type* is `bool`, so it
  produces a predicate rather than a bit-vector. The executor writes it as a
  `bool`, which is what the `if` that consumes it branches on; a one-bit word
  there would leave the local readable only as a word. It is unsigned-only,
  matching `core`.
- `is_negative`/`is_positive` are `bool` predicates too, and the model is
  `core`'s own definition: `x < 0` and `x > 0` read *signed*. They exist only on
  the signed types, and the signedness is the whole content — `i8::MIN` (`0x80`)
  is the *largest* unsigned byte, so an unsigned reading of the top bit would call
  it positive. Each is checked exhaustively against Rust's own method over `i8`
  and `i16`, with `i8::MIN` named as the point an unsigned reading gets wrong.
- The ten `is_ascii_*` class tests (`is_ascii_digit`, `is_ascii_alphabetic`,
  `is_ascii_alphanumeric`, `is_ascii_uppercase`, `is_ascii_lowercase`,
  `is_ascii_hexdigit`, `is_ascii_whitespace`, `is_ascii_punctuation`,
  `is_ascii_control`, `is_ascii`) are `bool` predicates too, and each is `core`'s
  own range test on the byte (`is_ascii_digit` is `b'0'..=b'9'`, `is_ascii` is
  `b < 128`, whitespace is the five `core` names — vertical tab excluded). They
  are the first modelled methods whose receiver is `&self`, so the operand is the
  *referent* of a reference the body materialises (`_3 = &_1`): the executor
  follows the reference for these shapes and only these. Each is checked
  exhaustively against Rust's own `u8` method, so the boundaries cannot drift from
  the standard library's.
- `slice::len` and `slice::is_empty` are modelled from the slice's length
  variable — the same symbolic input the frontend already binds for the bounds
  checks — so a contract's `s.len()` and the body's `PtrMetadata(_1)` are one
  number. They are matched on the *path* (`core::slice::<impl [T]>::len`), so a
  `Vec::len` or `str::len` is not mistaken for a slice length; and the receiver's
  length has to be one the frontend holds, so a receiver it did not bind is
  refused rather than given an invented number.
- `slice::first` and `slice::get` are modelled for a *concrete* slice. They return
  `Option<&T>`, so the payload is a *place*, not a value, and the model writes the
  `Option`'s tag as a *predicate* — `len == 0` for `first`, `k >= len` for `get(k)`
  — which is what makes the `unwrap` that usually follows carry a real panic
  obligation rather than an assumed `Some`. The payload is the slice's *own*
  element variable, the same one `xs[k]` names, so `*xs.first().unwrap()` and
  `xs[0]` agree by construction; the returned reference's deref (`*_2`) reads
  through a dedicated `Env::slice_elem_ref` store, and both `unwrap` and the
  `match` desugaring (which reads the payload through a downcast temp) carry the
  element to their destination, so the two spellings decide alike. `get`'s index
  must be a *constant*: a slice's length is symbolic, so a symbolic index has no
  finite domain and reading "some element" would be a wrong proof, not a missing
  one. The *generic* `first_or<T>` is not this shape — it needs monomorphisation —
  so it stays refused.
- `Ord::min` and `Ord::max` are the two modelled *trait* methods, so a dump spells
  a call `<u8 as Ord>::min` (or `<i8 as std::cmp::Ord>::max` with `std` in scope)
  rather than a `core::num::<impl …>` inherent path. The model is one `ite` over
  the two operands, and the *sign* selects the ordering — `sle`/`sge` on a signed
  type, `ule`/`uge` on an unsigned one — so both signednesses are exact. The sign
  matters: `i8::MIN`'s bits (`0x80`) are the largest unsigned byte, so an unsigned
  ordering would return the wrong operand for every pair with a negative side. Only
  the standard library's `Ord` is accepted — the trait path must be exactly `Ord`,
  `core::cmp::Ord` or `std::cmp::Ord`, which a user cannot define — so a local
  trait's `min` is refused by name as well as by the same-dump lookup below.
- `From::from` and `Into::into` are the two *widening conversion* trait methods, so
  a dump spells a call `<u16 as From<u8>>::from` (or `<u8 as Into<u16>>::into`).
  They are the one modelled shape whose two operands have *different* types, so the
  model reads both types from the call's name and extends the source by its *own*
  signedness: `i8::MIN` widens to `i8::MIN` (a sign-extension), `255u8` to
  `255u16` (a zero-fill). The source's sign decides the extension, not the
  destination's, so `i16::from(255u8)` is `255` and not `-1`. A *strict widening*
  between modelled integers is accepted, which is exactly every widening `From`
  `core` implements, so a real call is never a guess. A *same-width* call is
  `core`'s reflexive `impl<T> From<T> for T`, whose result is the source
  unchanged, and is modelled as exactly that. Only a *narrowing*, or a source the
  engine does not hold (a `bool`, say), is refused and the path is reported
  unknown. The trait path must be exactly `From`/`Into`, `core::convert::…` or
  `std::convert::…` — none of which a user can define — so a local `From` in a
  module is refused by name.
- The inherent `iN::abs` and the trait `Ord::clamp` are the first modelled methods
  whose failure is a **panic**, so the model carries *two* channels — the value and
  a `fails` predicate — and the executor turns the predicate into a panic
  obligation beside the value. The value is defined at every input (the wrapped
  absolute value, the clamp expression), and the predicate is where `core`'s own
  `assert` fires: `abs` fails exactly at `MIN`, and `clamp` fails exactly at
  `lo > hi`. An out-of-range `x` is *not* a clamp panic — clamping it is the whole
  point — and reading it as one made a true corpus function fail until the probe
  corpus caught it. `abs` takes its sign from the operand (`Abs` joins the
  sign-reading arms), and `clamp`'s comparisons are the type's own, so a signed
  clamp reads `i8::MIN` as below `0`. Both are refused on a non-primitive self
  type, and `clamp` is admitted only under the standard library's `Ord` path, the
  same rule `min`/`max` follow.
- The inherent `iN::unsigned_abs` is the same magnitude as `abs` read as the
  *unsigned* type (`i8::unsigned_abs(-128)` is `128u8`), so it reuses the same
  `0 - x`/`x` `ite` — but it is *total* where `abs` panics: at `MIN` the
  truncating subtraction is exactly the magnitude, which is the very bit pattern
  the signed `abs` cannot represent. It is therefore a plain value with no
  failure predicate, labelled unsigned on the way out so `128` is not read back as
  `-128`. The pair is what makes `abs`'s panic meaningful: one call fails at `MIN`
  and its sibling does not.
- `iN::abs_diff` and `iN::rotate_left`/`rotate_right` are total, so they are plain
  values rather than a value-and-panic pair. `abs_diff`'s result is the *unsigned*
  magnitude even on a signed type — `i8::abs_diff(-128, 127)` is `255u8` — so the
  model widens both operands by their *own* sign to `w + 1` bits, subtracts there,
  and takes the absolute value with a *signed* sign test: the `w + 1`-bit range is
  exactly a signed one, so an unsigned difference `0 - 1` is read as `-1`, not as
  `255`. The rotations reduce the amount modulo the width the way `core` does — a
  rotation by the width is the identity and by `w + 1` is by `1` — and because a
  modelled width is a power of two the reduction is one `and` and no divider. Both
  are checked exhaustively over `u8`/`i8` against Rust's own methods, so the
  rotation's wrap cannot drift from the standard library's.
- The remaining total `core` value methods are modelled as plain values, each
  checked exhaustively against Rust's own method over the whole `u8`/`i8` domain:
  `signum` (`-1`/`0`/`1`, signed-only, so `i8::MIN`'s top bit is read as a sign
  rather than the largest unsigned byte); `cast_unsigned`/`cast_signed` (the
  same-width signedness re-interpretation: the value is the operand *unchanged*,
  and only the result *type* differs, so it is the one shape whose result sign is
  the opposite of the operand's — read from the call's destination type, not
  derived from the operand, which is what a later comparison or division then
  consults); `reverse_bits` (a shift-OR fold, both
  signednesses); `swap_bytes` (a rotation by `w/2` bits — the byte reversal, not a
  rotation by `w/2 * 8`); `to_be`/`to_le` (a byte swap or the identity according to
  the *target's* endianness, read from `cfg!(target_endian)` rather than guessed;
  `core` has no `to_ne` value method, only `to_ne_bytes`); the ASCII case
  conversions `to_ascii_uppercase`/`to_ascii_lowercase` (`u8`-only, a range test
  over `b'a'..=b'z'`/`b'A'..=b'Z'`); and `is_multiple_of` (unsigned-only, `a % b ==
  0` with `b == 0` defined as `a == 0`, so the `b != 0` guard and the `|| a == 0`
  disjunct both carry). The `_bytes` forms of the byte orders return an array, not
  an integer, so they are left unmodelled rather than written as a word.
- `iN::div_euclid`/`rem_euclid` and `uN::div_ceil` are the division shapes that are
  *not* the truncating `/`/`%`. Each has a value *and* a panic predicate, because
  each panics on a zero divisor (and `div_euclid`/`rem_euclid` also on `MIN / -1`,
  the same predicate `checked_div` reports) — modelling them as total would hide a
  panic. The Euclidean quotient is `a / b` adjusted *the other way* when the
  truncating remainder is negative (`q - 1` for a positive divisor, `q + 1` for a
  negative one; `-7.div_euclid(3)` is `-3`, not `-2`), the Euclidean remainder is
  `a % b + |b|` when negative, and `div_ceil` is `a / b` rounded up. They are
  signed-only (`div_euclid`/`rem_euclid`) or unsigned-only (`div_ceil`) and bounded
  at `DIV_MAX_WIDTH`, like every divider-backed model. Each is checked against
  Rust's own method at every input the call does not panic on, with the panic
  predicate compared at *every* input.
- `iN::midpoint`, `iN::next_multiple_of` (and its `checked_` counterpart),
  `iN::ilog2`/`ilog10` and the
  `next_power_of_two` pair are the rounding and magnitude helpers. `midpoint` is
  total and computed without a sum at the operand width — `(a & b) + ((a ^ b) >> 1)`,
  plus a `+1` correction for the signed case when the result is negative and
  `(a ^ b)` is odd, which is the truncation toward zero `core` documents (`-5` and
  `-2` mid at `-3`, not the floor `-4`). `next_multiple_of` is unsigned-only and
  value-and-panic (`a + (b - a % b) % b`, panicking on a zero divisor or an
  overflow), and `checked_next_multiple_of` is the same value and condition as an
  `Option` (`None` exactly where the plain call would panic, so its tag is a term
  and no panic obligation is emitted). `ilog2`/`ilog10` exist on both signednesses,
  are value-and-panic (a
  non-positive argument panics), and return a `u32` whatever the operand's type;
  `checked_ilog2`/`checked_ilog10` are the same value as an `Option`, `None` exactly
  where the plain form panics, with the same `u32` payload.
  `next_power_of_two` (unsigned-only) and its `checked_` counterpart are the
  rounding sibling of `is_power_of_two`: the classic smear-and-add (`p = x - 1`,
  forced to `0` for `x <= 1`; `p |= p >> 1; p |= p >> 2; …`; `p + 1`), which is
  total at `w` bits — the plain form panics where the result does not fit
  (`x > 2^(w-1)`) and the `checked_` form returns `None` there. Each is checked
  exhaustively against Rust's own method (the `next_power_of_two` pair at 1/4/8/16
  bits, with the oracle computed at the *model's* width).
- `Option`'s `unwrap`, `unwrap_or`, `expect`, `is_some` and `is_none`, and
  `Result`'s `is_ok`, `is_err`, `unwrap` and `unwrap_or`, are the first modelled
  calls that read an *enum* rather than a bit-vector operand: the receiver's tag
  and payload, which the model's own `checked_*` family writes (`checked_add` on a
  `u8` writes the tag and payload of an `Option<u8>`) and which a contract-bound
  `Option`/`Result` argument also fills. `unwrap`/`expect` return the payload and
  report a **panic** on the failure variant, the same reachable-failure obligation
  `abs` and `clamp` carry, so the idiom `if x.is_some() { x.unwrap() }` verifies
  with the panic ruled out; `unwrap_or(default)` is *total* — the payload on the
  success variant, the default on the failure one — and the predicates are the tag
  tested against the success/failure discriminant. The receiver is `self` for the
  value methods and `&self` for the predicates, so the executor follows the
  reference either way. The two families are one shape: `Option` puts the payload
  on `Some` (tag `1`) and `is_some` tests that tag, `Result` puts it on `Ok` (tag
  `0`) and `is_ok` tests *that* tag, so a single executor arm answers both with the
  payload variant read off the method name. They are matched on the
  `option::Option`/`result::Result` path rustc prints, so a user type spelled
  `Option`/`Result` is refused, and a same-dump body wins the lookup first. This
  closes the `checked_add(..).unwrap_or(u32::MAX)` and `checked_div(..).unwrap()`
  idioms, whose `Option` handling was the gap — the remaining `div_unwrap`
  incompleteness is the *divider* wall (`n / d <= n` at `u32`), not the `Option`,
  and the same body decides at `u8`.
- A *local* method that shares an intrinsic's name is answered by its own body,
  never by the model. rustc prints a trait impl's call as `<u8 as Trait>::m` but
  its definition as `<impl at …>::m`, so the names never match; the model is only
  consulted when no same-dump body exists and the call name carries the `<impl …>`
  projection that every real `core` method call has. Without both halves, a trait
  that disagrees with `core` would get a *false proof* from the model.
  `Ord::min`/`Ord::max` and the widening `From::from`/`Into::into` are the two
  exceptions to the projection rule — a trait call has no `<impl …>` — and each is
  admitted only under the standard library's trait path (and, for `Ord`, only for a
  *primitive* self type). A crate-root trait named `Ord` or `From` is the one
  spelling that prints its own call with a bare trait path too, so the same
  trait-path check separates it from the library trait — the local `From` is not a
  suffix of `std::convert::From`, and the model answers only the library spelling.
- The same-dump lookup is *trait-aware*, so a local impl on a primitive cannot
  answer a call the compiler resolved to a library trait. The hazard is concrete:
  a local `impl From<u8> for u16` returning `7` shares the method tail (`from`)
  *and* the owner (`u16`) with `core`'s `impl From<u8> for u16`, so matching on the
  owner alone answered `<u16 as std::convert::From<u8>>::from` from the local body
  — a false proof of a library call. A *trait* call (`<T as Trait<…>>::m`) is now
  admitted only when the call's trait path is a `::`-aligned suffix of the candidate
  impl's own trait path, which the source records (`impl_traits`): the local impl's
  bare `conv_shim::From` is not a suffix of `std::convert::From`, so it is refused,
  while the local trait's own call still reaches its body. A bare `Type::m` call
  carries no ` as ` projection — rustc prints an inherent method and an in-scope
  trait method that way — so it keeps the owner-type match alone, as before.
- A trait call's *instantiation* is part of its identity, not just its path and
  owner. `impl From<Local> for u16` returning `107` and `core`'s `impl From<u8> for
  u16` share the trait path, the owner and the method, so only the trait's
  *argument* separates them; a local `impl From<Local> for u16` once answered
  `<u16 as From<u8>>::from(7u8)` from its own body — a false proof. The argument is
  now read on *both* sides, with the same balanced reader
  (`spec::angle_inner`): `call_trait_args` from the call's name,
  `Specs::impl_trait_args` from the impl header. A nested argument
  (`impl Wrap<Option<u8>> for W`) is the case that keeps the reader honest — a
  "strip trailing `>`" reading on the call side cut *every* closing bracket
  (`Option<u8`), matched no impl, and turned a call with a real body into an
  unmodelled one — a lost proof. An unreadable side is refused, not waved through.
- The import scan reads the source's `use` items, because rustc prints an imported
  trait's call with the *imported* path (`use std::convert::From as Conv;` makes
  `impl Conv<Local> for u16` print `<u16 as std::convert::From<Local>>::from`).
  Imports are kept per module path, folded across the item's lines, and read
  through any visibility (`pub(crate)`, `pub(in …)`), so a lost import — which
  qualifies an impl with its own module and loses the call — is not the failure
  mode. A `#[cfg]`-conditional `use` is the exception to order-independence: it
  binds only when its condition holds, and rustc then binds nothing, so a
  conditional binding never displaces an unconditional one (a disabled
  `#[cfg(any())] use crate::Other as Conv;` once overwrote a live alias and lost
  the call). An attribute on the `use`'s own line is peeled first, so a live
  `#[cfg(all())] use …` is read rather than skipped, and the attribute block above
  the `use` is read as whole bracket-balanced items, so a condition that *spans*
  lines (`#[cfg(all(\n    any(),\n))]`) is found too. A delimiter inside quoted
  text is not a delimiter: `#[doc = "("]` carries an unmatched `(` in a string,
  and counting it would run the reader past the attribute's real end, so string
  and character literals are skipped (escapes honoured) while matching `#[…]`.
- `add_signed`/`add_unsigned` add a value to one of the *opposite* signedness
  (`u8::wrapping_add_signed` adds an `i8` to a `u8`), so the two operands are read
  at different signs. The value is the plain wrapped sum in both directions, since
  rustc reinterprets the addend and adds. The overflow flag is the addition's own
  overflow *adjusted by the addend's sign*, `carry XOR (addend < 0)` — not the
  ordinary signed-addition rule, which is wrong on half the domain. `250u8 +
  (-1i8)` carries but is in range, so the flag is `false`; `0i8 + 128u8` does not
  carry but runs off the top, so it is `true`. The saturating clamp follows the
  addend's end: `0` or `255` for an unsigned self, `127` for a signed one.

The refusals matter as much as the model, and each has a reason. Only `checked_div`
and `checked_rem` may model division: the `saturating_` and `wrapping_` forms *panic*
on a zero divisor, and modelling a panicking operation as total would hide a panic,
which is the one thing this frontend must never do. The shifts are refused because
the three families disagree about the amount — `wrapping_shl` reduces it modulo the
width, the engine's variable shift saturates to zero, and `checked_shl` returns
`None` past the width — and three behaviours under one name is not something to
guess at. `unchecked_*` is undefined behaviour, and a proof about UB is not a proof.
A name that is not in the table does not classify, and a name that classifies but
whose shape is past a width limit is refused by `eval`, which leaves the path
unknown rather than slow.

`src/mir/intrinsics.rs`'s unit tests are the oracle: every case is compared against
the real `core` call, over all of `u8` and all of `i8`, so the model is checked on
*every* input rather than on the ones that happened to be tried. That is what pins
the signed rules, which the unsigned tests cannot see — `-1 + 1` does not overflow,
but the unsigned carry test fires on it. The widths past the limits, the refused
names, and `i8::MIN / -1` are checked too.

### What it declines, and why that is the point

The frontend refuses far more than it accepts, and every refusal is reported:

- **MIR it cannot parse.** An unrecognized statement becomes `Unknown`, which
  makes the path "not modelled", never "proved".
- **A signed multiply whose overflow test needs a `2w`-bit product.** This is no
  longer a refusal. The predicate used to be written as a test on the sign-extended
  `2w`-bit product, which is the BDD scaling wall, so past 16 bits there was no
  predicate and the path was reported `incomplete`. The signed test is now the exact
  division form, in the same shape as the unsigned one: `|x| > limit / |y|` with
  `y != 0`, where `limit` is `2^(w-1) - 1` when the operands share a sign (the product
  is positive) and `2^(w-1)` when they differ (the product is negative). It needs no
  widening, so a predicate exists at `i64`, and it is exact for every combination of
  the two signs — the claim that no such form exists was wrong, and brute force over
  ~93M cases at widths 2..=14 found no counterexample. Whether the query is then
  *decided* still depends on the diagram budget, exactly as it does for the unsigned
  form: a guard written as this predicate cancels against the obligation's assert at
  every width, while a bare multiply the engine has to reason about from scratch can
  run out of budget and report `incomplete`.
- **A `core::num` product whose overflow test needs a widened `2w`-bit multiply past
  `u32`.** The `checked_*`/`saturating_*`/`overflowing_*` families need the exact
  product to test overflow, which is built by widening the operands to `2w` — the
  BDD scaling wall. `MUL_MAX_WIDTH` is `32`, so a `u32` product's predicate is built
  (a 64-bit multiply) while a `u64` one is refused (`2w == 128` cannot be held) and
  reported "past what the model covers". The *value* families (`wrapping_*`) need no
  widened product at all — they are a plain `w`-bit multiply — so they are admitted
  up to the same bound and a `u32` `wrapping_mul` (the shape `hash_step` uses) now
  decides, while a `u64` one is past the wall regardless. The refusal is the honest
  answer: the path stays unknown rather than being proved from a truncated product.
- **`core::num` operations other than the modelled families.** `checked_*`,
  `saturating_*` and `wrapping_*` for `add`/`sub`/`mul`/`div`/`rem` and the
  bitwise ops are computed from their operands (see below), as are the unary
  `neg`/`abs` in all four families, the six bit counts (`count_ones`,
  `count_zeros`, `leading_zeros`, `leading_ones`, `trailing_zeros`,
  `trailing_ones`), the `bool` predicates `is_power_of_two`,
  `is_negative`/`is_positive` and the ten
  `is_ascii_*` class tests, the `slice::len`/`is_empty` length queries, the
  `Ord::min`/`Ord::max`
  trait methods, the `abs_diff` and `rotate_left`/`rotate_right` methods, the
  widening `From::from`/`Into::into` conversions, the
  mixed-signedness
  additions (`wrapping_add_signed`, `saturating_add_signed`, `checked_add_signed`,
  `overflowing_add_signed` and their `_unsigned` counterparts) and the `pow`
  families. Every other intrinsic, and every other trait
  method, is still a call the frontend cannot model.
- **A symbolic index into a *slice*, or a mutable reference write.** An array
  subscripted by a parameter (`a[i]` on `[u8; 4]`) *is* modelled: the length is in
  the type, so `a[i]` is the exact ite chain over `0..N`, admitted only when the
  precondition establishes `i < N`. A slice has no such bound — its length is a
  symbolic input — so `xs[i]` is refused rather than resolved to an arbitrary
  element. `*r = v` is the aliasing model the crate does not claim. Fields and
  elements of by-value aggregates, and elements and lengths of slices and
  fixed-size arrays, *are* modelled — only the pointer arithmetic is not.

A subscript whose index is a *local* that aliases an argument is resolved to that
argument. `let k = i; a[k]` on a `Copy` index lowers to no local at all — the
body's `a[k]` really is `a[i]` — so the contract's `k` names the same index, and
`a[k]` builds the same ite chain `a[i]` would. The name resolves only when the
aliased local is an argument that the body never writes, so `let k = i; i = 2;`
does not alias `k` to the reassigned `i`; that subscript is refused instead.

### Signedness is a value question, not a display one

`i8`, `i16` and friends are bit patterns like any other, so every operation has one
bit-pattern answer — but signedness decides *which question a comparison asks*.
`-1 < 1` is `false` read unsigned and `true` read signed; `-7 / 2` is `-3` signed
and a huge positive number unsigned; and a signed add overflows where the unsigned
carry says nothing is wrong. The frontend reads the declared type and picks the
signed form (`slt`/`sle`/`sgt`/`sge`, `sdiv`/`srem`), and the contract evaluator
does the same, because a contract's `<` is the same comparison as the code's.

The overflow rules differ too. A signed add wraps exactly when the operands agree
in sign and the result disagrees; a signed multiply when the sign-extended product
is not the sign-extension of the wrapped result, which is `rustc`'s own test. This
matters in the direction that hides bugs: the unsigned carry test fires on
`127 + 1` but *also* on `-1 + 1`, which does not overflow, and `MIN` is the top bit
rather than zero. The demo's `signed_add_misguarded` is the case that pins it —
`requires: a <= 127 && b <= 1` reads like a safe guard and is not one.

`tests/signed.rs` checks the signed operators differentially against Rust's own on
the same two's-complement values, and `examples/z3diff.rs` carries signed
identities in its corpus. `MIN / -1` and a zero divisor are *defined* rather than
trapped, for the same reason the unsigned divider defines `y == 0`: a hole in the
model is a hole in the proof. `rustc`'s own `assert`s are what turn those inputs
into reported panics.

`FnOutcome::Incomplete` is not a pass. `FileReport::is_clean` is false whenever any
path was unmodelled or any contracted function is missing from the MIR, and a
missing contract is reported rather than quietly turning a function green. This is
the same discipline as `Verdict::Unknown` in the engine: a bounded checker that
says "I could not decide" is worth more than one that guesses.

### The known gaps, stated

1. **Calls are inlined one level, or answered by a contract.** A call to a
   function in the same file is symbolically executed; a call to a function whose
   body is *not* in the file but whose contract is -- an `extern` declaration, or
   any item the dump does not carry a body for -- is answered from that contract:
   its `requires:` is proved of the call's arguments, its `ensures:` is assumed of
   the result, and an unsatisfiable postcondition refuses the call as divergent.
   The precondition obligation is what makes the assumption sound; a call outside
   the callee's precondition fails rather than being trusted. A callee with no
   postcondition gives nothing to assume and stays incomplete. A *self-call* with
   a `decreases:` measure is answered by the same contract route with well-founded
   induction added, so a recursive function with a measure is decidable and one
   without it is reported incomplete at the depth bound. A callee whose parameter
   list the source scanner cannot read (a pattern parameter, a wrapped signature)
   is refused rather than bound positionally, and a reference argument is refused
   because there is no aliasing model to carry a write back to the caller.
2. **The dump is textual.** The frontend parses `--emit=mir` output rather than
   linking `rustc-dev`. That keeps the dependency count at zero and makes the
   input inspectable, but it means a rustc release that changes the pretty-printer
   can break the parser. It fails closed when that happens, and the
   `rustc_public` oracle in `tools/mir-oracle` (gate 10) catches one half of that
   risk: it compares each function's **basic-block count and the panic guards
   `rustc` inserted** (kind and polarity) between the text and typed MIR, so a
   printer change that alters the *structure* of a body fails CI. It does **not**
   compare places, types, locals or projections, so a change that only re-spells
   a place is invisible to it — `Len((*_1))` becoming `PtrMetadata(copy _1)` in
   1.99 was exactly that, and it was found by running the frontend's suite under a
   second toolchain, not by this gate — gate 10 was silent across it. `src/mir/shape.rs`'s
   `the_shape_sees_structure_and_guards_but_not_places` pins both directions of
   that boundary, so this paragraph cannot drift into claiming more than the code
   checks.
3. **Contracts are checked at entry and exit only.** A loop invariant written as a
   contract is not an invariant; it is an assertion at two points.
4. **The verifier is not inside the artifact.** `gnatprove` and this crate's own
   embedded engine are in-process; the MIR frontend shells out to `rustc` and lives
   behind the `std` feature. The engine it uses is the embedded one, but the
   frontend that feeds it is a development tool, not something that ships on a
   microcontroller.
5. **A `for` loop over a *range*, a *slice* or an *array* is modelled; an iterator
   chain is not.** `for i in 0..n` / `for i in 0..=n` desugars to
   `Range`/`RangeInclusive` construction, `IntoIterator::into_iter` and
   `Iterator::next(&mut range)`, and all of those *are* in the model (with `core`'s
   `forward_overflowing` boundary reproduced exactly), so the loop decides through the
   same machinery a `while` loop uses — `for i in 0..=n { s += i }` verifies under a
   `requires:` that bounds `n` (or an `unwind:` bound), and a body decided by an
   *inductive* `invariant:` verifies with one. `for x in xs` over a slice (`&[T]`), a
   `&[T; N]`, a `[T; N]` (by value) and `xs.iter()` is modelled too: `into_iter`/`iter`
   starts a *cursor* at a concrete position and `next` reads the element there, so each
   iteration names the same element variable a contract's `xs[k]` names — `for x in xs
   { s += x }` verifies against `requires: xs.len() == 2, ensures: s == xs[0] + xs[1]`,
   and the false twin is refuted. The **consumers** `sum`, `count` and the
   `copied` adapter are modelled on that cursor: `xs.iter().count()` is the length,
   `xs.iter().copied().sum()` reads the same elements, and `xs.iter().sum()` folds
   them with a *checked* `+` — so an unguarded `u8` sum is *refuted as a panic*
   (it overflows for `[200, 100]`), while a contract that bounds the elements
   discharges the additions and verifies. A `sum` over a *symbolic*-length slice is
   refused (there is no fixed number of addends to build a term from); an array's
   type length, or a slice the precondition pins (`requires: xs.len() == N`), is a
   constant and is summed. `last`, `nth(k)`, `max` and `min` ride the same cursor:
   `last`/`nth` name the exact element when the length is known (an array's type
   length, or a slice the precondition pinned) and fall back to a fresh variable for
   a symbolic-length slice, and `max`/`min` are folds of *signedness-aware*
   comparisons (so `i8::MIN` is the least, not the greatest), needing a constant
   length like `sum`. `enumerate()` is a cursor identity whose `next` yields
   `Option<(usize, &T)>`: the index is the cursor position and the element is
   `xs[pos]`, so `for (i, &x) in xs.iter().enumerate()` decides. What is *not*
   modelled is an iterator chain that must run a closure (`fold`, `map`, `filter`);
   those are reported `incomplete` with the unmodelled call named, so the gap is
   visible rather than silent. A `String` is modelled by its **length** (`new`,
   `push_str`, `from(&str)`, `len`, `is_empty`), with a `&str` literal's byte length
   a constant and an argument's a symbolic input; the bytes are not modelled, so a
   contents-dependent method stays refused, and a `String` drop is glue-free. A `Vec`'s *elements* are modelled — `v[k]`, `v.first()`,
   `v.get(k)` and `pop` read back what `push` wrote, and a `Vec` argument's
   `v.len()`/`v[k]` are symbolic inputs — and `v.iter()` derefs to a slice, so
   `for &x in v.iter()` decides like one over a slice. Two limits of the iteration model
   are worth knowing. A `for` loop carrying an `invariant:` is **refused** for a slice
   (`incomplete`): the loop cut havocs the cursor, so `next` finds none — the position
   would be symbolic, and reading "some element" would be a wrong value, so the honest
   answer is a refusal, and a `while` loop with an invariant (indexing `xs[i]`) is the
   way to state such an iteration. And an `invariant:` that *names* a range loop's element
   (`s <= i`) is refused as `unknown name i`, because the element is a `debug` binding
   that is genuinely not live at the loop header — write the invariant over the loop's
   *carried* state (`s <= 5050`), and it must be *inductive* (`s <= 5050` over a body
   doing `s += i` is not; `s = i.min(5050)` is). A `while` loop carrying an `invariant:`
   and a `variant:` remains the most precise way to state an iteration, because the
   measure gives total correctness, where an unwound `for` gives a bounded check.

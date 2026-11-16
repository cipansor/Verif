//! The `core::num` operations the frontend models instead of treating as unknown.
//!
//! A call the frontend cannot model makes the whole *path* unknown, and the
//! `checked_*`, `saturating_*` and `wrapping_*` families are how real Rust
//! writes arithmetic that must not panic. They are also the easiest calls to
//! model exactly: each is a pure function of its arguments with a definition
//! that fits in a line.
//!
//! The default everywhere else is to refuse an unmodelled call rather than
//! approximate it, and that stays true here -- a name not in the tables below is
//! not modelled, and a name that *is* listed but whose shape does not match is
//! also not modelled. What changes is that the three families below have a
//! definition, and the definition is used.
//!
//! # What is modelled, and why the result is not a guess
//!
//! * `wrapping_*` — the operation with the result taken modulo `2^w`. That is
//!   exactly what MIR's plain `Add`/`Sub`/`Mul`/`BitAnd`/… already compute, so
//!   the wrapping model is the *same term* a plain operator produces rather than
//!   a second definition that could drift from it.
//! * `saturating_*` — the operation, clamped. The clamp is `if it would overflow
//!   { bound } else { result }`, and the overflow test is the one rustc's own
//!   `assert` reads, so a function written with `saturating_add` and one written
//!   with a hand-rolled guard are decided by one rule.
//! * `checked_*` — an `Option<T>`. The tag is the *negation* of the overflow
//!   test and the payload is the result, so `Some` means exactly "defined".
//! * `overflowing_*` — a `(T, bool)`. The flag is the *same* predicate the other
//!   two families use, so the four cannot disagree about what "overflow" means.
//! * `wrapping_neg`, `checked_neg`, `saturating_neg`, `overflowing_neg` and the
//!   four `abs` spellings — the unary operators. They share the `0 - x` core,
//!   and `abs` is "negate if negative" on top of it, so there is one expression
//!   rather than four.
//! * `count_ones`, `count_zeros`, `leading_zeros`, `leading_ones`,
//!   `trailing_zeros`, `trailing_ones` — bit counts, built at the operand's width
//!   and zero-extended to the *return* type's. `u8::count_ones` returns `u32`, so
//!   this is the one shape whose result is wider than its operand; the extension is
//!   the promotion Rust performs. The three *complement* counts are `core`'s own
//!   definition — the corresponding positive count of `!x` — rather than a second
//!   summation.
//! * `is_power_of_two` — a `bool`, not a number: `x != 0 && x & (x - 1) == 0`.
//!   It is the one modelled shape whose *return type* is `bool`, so the model
//!   produces a [`Pred`] and the executor writes a `Val::Bool`, which is what the
//!   `if` that consumes it branches on. It is unsigned-only, because `core` has no
//!   such method on the signed types.
//! * `is_negative`/`is_positive` — also `bool`, and also `core`'s own definition:
//!   `x < 0` and `x > 0` read *signed*. They exist only on the signed types, and
//!   the signedness is the whole content -- `i8::MIN` (`0x80`) is the largest
//!   unsigned byte, so an unsigned reading of the top bit would call it positive.
//! * `Ord::min`/`Ord::max` — the two *trait* methods, so the dump spells a call
//!   `<u8 as Ord>::min` rather than a `core::num::<impl …>` path. The model is one
//!   `ite` whose ordering predicate the operand's sign selects (`sle`/`sge` for a
//!   signed type, `ule`/`uge` for an unsigned one), so both signednesses are exact
//!   and `i8::MIN` -- whose bits sort the other way unsigned -- is ordered
//!   correctly. Only the standard library's `Ord` path is accepted; see
//!   [`names_ord_trait`].
//! * `From::from`/`Into::into` — the two *widening conversion* trait methods,
//!   spelled `<u16 as From<u8>>::from` and `<u8 as Into<u16>>::into`. Unlike every
//!   other shape the two operand *types* differ, so the model reads both from the
//!   call's name and extends the source by its *own* signedness (`i8::MIN` widens
//!   to `i8::MIN`, `255u8` to `255u16`). Only a strict widening between modelled
//!   integers is accepted -- which is every integer `From` `core` implements, so a
//!   real call is never a guess; see [`Conversion`].
//! * `add_signed`/`add_unsigned` — an addition whose two operands have *opposite*
//!   signedness (`u8::wrapping_add_signed` adds an `i8` to a `u8`). The value is a
//!   plain addition of the two words, so it is the same term in both directions;
//!   the flag is the addition's own overflow *adjusted by the addend's sign*, which
//!   is what makes it exact rather than the ordinary signed-addition rule. See
//!   [`mixed_add_failure`] for why the adjustment is not optional.
//!
//! # What is not, and why refusing is the right answer
//!
//! * `wrapping_div`, `wrapping_rem`, `saturating_div`, `saturating_rem` **and
//!   `overflowing_div`/`overflowing_rem`** panic on a zero divisor. Modelling
//!   them as total would *hide a panic*, which is the one thing this frontend
//!   must never do. Only `checked_div`/`checked_rem` express the failure as a
//!   value -- `None` covers a zero divisor *and* `MIN / -1` -- so only they are
//!   modelled, and only up to [`DIV_MAX_WIDTH`]. The `overflowing_*` spelling is
//!   the trap here: it reports `MIN / -1` in its flag, which makes it look like a
//!   total form of division, but its flag is not the whole failure predicate and
//!   the zero divisor still panics.
//! * The shifts are refused because the families disagree: `wrapping_shl` takes
//!   the amount modulo the width, while the engine's variable shift saturates to
//!   zero, and `checked_shl` returns `None` past the width. Three behaviours
//!   under one name is not something to guess at.
//! * `unchecked_*` is undefined behaviour on overflow. There is no value to
//!   model, and a proof about UB is not a proof, so it is refused.
//! * `pow` is modelled as a fold over the exponent's bits (see [`POW_MAX_WIDTH`]).
//!   `div_floor` and the float ops remain absent, and an unmodelled name is
//!   refused rather than approximated.
//!
//! `abs_diff`, `rotate_left`/`rotate_right`, the ten `is_ascii_*` classes and the
//! sign predicates `is_negative`/`is_positive` are modelled, and this header said
//! otherwise for a while -- the list of what is modelled has to move with the
//! tables below it. The unit test `the_documented_modelled_set_matches_classify`
//! pins the spellings it names so a later removal cannot leave the prose behind
//! again.

use crate::mir::parse::{BinOp, Ty};
use crate::smt::{self, Pred, Var};

/// The widest bit-vector the divider is asked about.
///
/// The engine's divider is exact but large, and a quotient term at `u64` is past
/// what the BDD holds. Above this the model declines, which leaves the path
/// unknown rather than slow. Declining is the intended answer; a model that
/// hangs is worse than one that says "I could not decide".
pub const DIV_MAX_WIDTH: u8 = 32;

/// The widest operand whose *product* the intrinsics model will widen to test.
///
/// Overflow for a product needs the exact `2w`-bit result, and a `2w`-bit
/// multiplier is the scaling wall this crate documents. Past this the query is
/// not worth posing, so the model declines and the path stays unknown. The plain
/// `*` path reaches further -- it uses an exact division test rather than a
/// widened product, and `DIV_MAX_WIDTH` is its limit -- so this bound is the
/// intrinsics' own, stated here so the two cannot be confused.
///
/// The bound is measured rather than guessed. The widened product is what makes a
/// `u16` product decidable at all: with this bound at 8, every `u16`
/// `saturating_mul`/`checked_mul` reported "past what the model covers" and no
/// contract over one could be settled. At 16 a guarded `u16` product is
/// *verified* and a mis-guarded one is correctly *refuted*, both in under 200ms,
/// because the obligation's guard and the model's predicate are the same term and
/// the boolean fold settles them without blasting the multiplier.
///
/// **Raised to 32, and the two costs were measured apart.** What the wider bound
/// admits is the whole `u32` surface, and it pays off because the two shapes at
/// `u32` cost very different things:
///
/// * the *value* -- the `wrapping_*` family, which builds no predicate -- is a
///   plain `w`-bit multiply and settles in milliseconds: `x.wrapping_mul(31)`,
///   `x.wrapping_mul(y)`, `(x * y) * z` and `x * x` all verify in under 50ms, and
///   `hash_step` (`h.wrapping_mul(31).wrapping_add(b as u32)`) went from
///   `incomplete` to `verified` in 0.00s;
/// * the *widened* `2w`-bit product is built only when a family actually needs the
///   failure predicate. It is a 64-bit multiply, so it is not free: a constant
///   multiplier usually folds the obligation without blasting it
///   (`x.saturating_mul(2)` verifies in 0.00s), while a fully symbolic one can
///   answer `Unknown` after ~5s -- `x.saturating_mul(y)` at `u32` is undecided,
///   which is the honest answer, not a wrong one, and it is bounded by the
///   engine's own apply budget rather than hanging.
///
/// The bound is `32` and not `64` because `2w == 128` cannot be widened at all:
/// `mul_failure` clamps the widened width at 64, so a `u64` product's predicate is
/// refused (`wide == w`) and reported "past what the model covers". Raising this
/// constant to 64 would not help even for the *value*: a `u64` `wrapping_mul` is
/// already past the BDD wall and comes back `incomplete` in 0.01s. So 32 is where
/// the cheap shape reaches and the expensive one is merely declined.
///
/// It is *not* the division form the plain-`*` path uses. That form was measured
/// here and is strictly worse: a `u16` idiom that the widened test settles in
/// 180ms came back `Unknown` after 3.2s, because these idioms ask about the
/// *value* of a `core` call and carry no hand-written guard for a division to
/// cancel against. The two paths therefore share the overflow *rule* but not its
/// cheapest spelling.
pub const MUL_MAX_WIDTH: u8 = 32;

/// The widest base `pow` is modelled at.
///
/// Lower than [`MUL_MAX_WIDTH`], and deliberately so. `pow`'s fold is up to 64
/// `mul_failure` queries composed into one term -- a `mul` and a squaring per
/// exponent bit -- so it costs a large multiple of a single product rather than
/// the product itself. Raising this to the product bound buys nothing and costs
/// seconds: a `u16` `saturating_pow` with a symbolic exponent was still
/// `Unknown`, but only after twelve seconds of diagram work, where the same
/// refusal at 8 bits is immediate. An answer that cannot be reached is not worth
/// paying for, so the fold keeps the tighter bound.
pub const POW_MAX_WIDTH: u8 = 8;

/// The discriminant of the `Some` variant, where a modelled `Option` payload
/// lives. rustc numbers `None` 0 and `Some` 1.
pub const SOME_TAG: u64 = 1;

/// The discriminant of the `Ok` variant, where a modelled `Result` payload lives.
/// rustc numbers `Ok` 0 and `Err` 1 -- the opposite of `Option`'s numbering, which
/// is why the executor reads the payload variant off the method rather than
/// assuming [`SOME_TAG`].
pub const OK_TAG: u64 = 0;

/// The discriminant of `ControlFlow`'s `Continue` variant, which carries the
/// value a `?` *yields*. rustc numbers `Continue` 0 and `Break` 1, so `Break` --
/// the residual that `?` returns early -- is [`BREAK_TAG`].
pub const CONTINUE_TAG: u64 = 0;

/// The discriminant of `ControlFlow`'s `Break` variant, which carries the
/// residual (the error) a `?` propagates. See [`CONTINUE_TAG`].
pub const BREAK_TAG: u64 = 1;

/// What a modelled intrinsic computes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    /// The operation, result taken modulo `2^w`. Cannot fail.
    Wrapping(BinOp),
    /// The operation, clamped to the type's range. Cannot fail.
    Saturating(BinOp),
    /// The operation as `Option<T>`: `None` where it would overflow or divide by
    /// zero, `Some(result)` otherwise.
    Checked(BinOp),
    /// The operation as `(T, bool)`: the wrapped result and whether it overflowed.
    /// Cannot fail.
    ///
    /// The flag is the *same* predicate the `checked_` family negates and the
    /// `saturating_` family branches on, so the three families cannot disagree
    /// about what "overflow" means.
    Overflowing(BinOp),
    /// A unary operator (`neg`, `abs`) in one of the four families.
    ///
    /// `neg` and `abs` are not two-operand operators, so they do not fit the
    /// `BinOp` variants above; they are unary *shapes* that each family happens to
    /// define. The family is carried because the four disagree about the failure
    /// case -- `wrapping_neg` returns the wrapped value, `checked_neg` returns
    /// `None`, `saturating_neg` clamps, `overflowing_neg` reports the flag.
    Unary(Family, UnOp),
    /// A bit count: one of `count_ones`, `count_zeros`, `leading_zeros`,
    /// `leading_ones`, `trailing_zeros` or `trailing_ones`.
    ///
    /// Its result is wider than its operand (`u8::count_ones` returns `u32`), so
    /// unlike every other shape it is built at the operand's width and
    /// zero-extended to the destination's. It cannot fail.
    Bits(BitKind),
    /// `iN::ilog2`/`iN::ilog10`: the integer logarithm, floor.
    ///
    /// `ilog2` is the index of the highest set bit and `ilog10` the largest `k`
    /// with `10^k <= x`. Like a bit count the result is a `u32` regardless of the
    /// operand's type (`u8::ilog2` is `u32`), so it is built at the operand's
    /// width and zero-extended. Unlike a bit count it is *not* total: both panic
    /// on a non-positive argument (an operand `<= 0`, which for an unsigned type
    /// is `x == 0`), so the shape yields a [`Outcome::ValueOrPanic`] and the
    /// executor turns the failure predicate into a reachable-panic obligation --
    /// the same polarity as `iN::abs`'s overflow. `ilog2` exists on both
    /// signednesses; `ilog10` on both too.
    Ilog(LogKind),
    /// `iN::checked_ilog2`/`checked_ilog10`: the integer logarithm as an `Option`.
    ///
    /// The `Option` counterpart of [`Intrinsic::Ilog`]: `None` exactly where the
    /// plain call would panic (a non-positive argument), so the tag is the
    /// *negation* of the same failure predicate and no panic obligation is
    /// emitted. Its result is a `u32` whatever the operand's type, exactly as the
    /// plain form's is, so it is zero-extended to `result_w`. Exists on both
    /// signednesses.
    CheckedIlog(LogKind),
    /// `iN::next_multiple_of`: the smallest multiple of `b` that is `>= a`.
    ///
    /// A method that *panics*: on a zero divisor, and on an overflow (`u8::MAX`
    /// `next_multiple_of` `100` overflows and panics in a checked build). So it is
    /// a [`Outcome::ValueOrPanic`], and the executor reports both failures as one
    /// reachable-panic obligation. Unsigned-only -- the signed spelling is
    /// unstable on this toolchain -- so a signed receiver is refused rather than
    /// read. The value is `a + (b - a % b) % b`, which is `a` when `a % b == 0`.
    NextMultipleOf,
    /// `iN::checked_next_multiple_of`: the same value as
    /// [`Intrinsic::NextMultipleOf`], as an `Option`.
    ///
    /// The `Option` counterpart of the panicking plain method: `None` exactly
    /// where the plain call would panic (a zero divisor, or an overflow), so the
    /// tag is the *negation* of the same failure predicate and no panic obligation
    /// is emitted. Unsigned-only, like the plain method.
    CheckedNextMultipleOf,
    /// `iN::next_power_of_two`: the smallest power of two `>= x`.
    ///
    /// Unsigned-only (there is no such method on the signed types), and a
    /// *panicking* method: the result does not fit for `x > 2^(w-1)`, so
    /// `u8::MAX.next_power_of_two()` panics in a checked build and is `0` in a
    /// wrapping one. So it is a [`Outcome::ValueOrPanic`], and the failure
    /// predicate is exactly "the rounded value came out `0`" -- which is `false`
    /// at `x == 0` (the value is `1`, the one input where the wrap-around would
    /// otherwise look like a failure). The value is computed by the classic
    /// smear-and-add, which is total at `w` bits.
    NextPowerOfTwo,
    /// `iN::checked_next_power_of_two`: `Some(next_power_of_two)` where the plain
    /// method does not overflow, `None` where it does.
    ///
    /// The same value and the same condition as [`Intrinsic::NextPowerOfTwo`],
    /// packaged as an `Option` -- the `checked_*` counterpart, so a caller that
    /// guards on `is_some` proves its result is in range.
    CheckedNextPowerOfTwo,
    /// A `pow` in one of the four families: `wrapping_pow`, `saturating_pow`,
    /// `checked_pow` or `overflowing_pow`.
    ///
    /// Its *exponent* is a `u32` operand while its *base* has the method's own
    /// width, so unlike every other shape it reads two operands of different
    /// types. It also cannot be written as one `BinOp`: `pow` is a fold over the
    /// exponent's bits, so it is its own shape rather than a member of the
    /// `Wrapping`/`Saturating`/`Checked`/`Overflowing` operators. The family is
    /// carried for the same reason it is on `Unary`: the four disagree about the
    /// failure case, and `pow`'s failure is an *overflow*, not a zero divisor.
    Pow(Family),
    /// A mixed-signedness addition: `wrapping_add_signed`, `saturating_add_signed`,
    /// `checked_add_signed`, `overflowing_add_signed` and their `_unsigned`
    /// counterparts.
    ///
    /// Its two operands have *opposite* signedness -- `u8::wrapping_add_signed`
    /// adds an `i8` to a `u8` -- so it is its own shape rather than a `BinOp`,
    /// whose operands share a type. It is one variant and not two because the
    /// *value* is the same addition of two `w`-bit words either way: rustc
    /// reinterprets the operand of the opposite signedness and adds, which is one
    /// term whatever the direction. Only the failure predicate reads which side is
    /// signed, and that is already carried by the operand's sign -- the executor
    /// passes it as `signed` -- so the direction is not stored a second time here,
    /// where it could drift from the sign the model actually reads.
    MixedAdd(Family),
    /// A `bool`-valued predicate (`is_power_of_two`).
    ///
    /// Its *return type* is `bool`, not an integer, so unlike every other shape
    /// it produces a [`Pred`] rather than a [`Var`]. It is one bit by
    /// construction, so `result_w` is not read for it.
    Bool(BoolKind),
    /// `slice::len`: the number of elements, as a `usize`.
    ///
    /// A slice's length is a *symbolic input* the frontend already binds for the
    /// bounds checks (`PtrMetadata`), so the model is that same variable, not a
    /// fresh one -- otherwise `s.len()` in a contract and the body's `s.len()`
    /// would be two numbers. The executor reads it through `length_of`.
    SliceLen,
    /// `slice::is_empty`: `len == 0`, the same length variable compared to zero.
    ///
    /// The length is the one the *executor* holds, so the two shapes read the
    /// same number and `is_empty()` cannot disagree with `len() == 0`.
    SliceIsEmpty,
    /// `slice::first`: `Option<&T>` -- `Some(&s[0])` when the slice is non-empty,
    /// `None` otherwise.
    ///
    /// The element is the executor's own `s[0]` variable (the same one a
    /// `s[0]` read names), so the `Option`'s payload *is* that element rather than
    /// a fresh one. The length test is the executor's length variable compared to
    /// zero, so `first()` cannot disagree with `is_empty()`.
    SliceFirst,
    /// `slice::get`: `Option<&T>` -- `Some(&s[k])` when `k < len`, `None`
    /// otherwise.
    ///
    /// Unlike `first`, the index is an operand: `get(i)` is `Some(s[i])` under
    /// `i < len`, and the element is looked up by the index's *value*. A symbolic
    /// index on a slice has no finite domain, so the executor refuses it rather
    /// than reading an arbitrary element -- the same rule a `s[i]` subscript
    /// follows. A literal index (`get(0)`) is exact.
    SliceGet,
    /// `iN::abs_diff`: the absolute difference of two operands, as the type.
    ///
    /// Its result is *unsigned* even on a signed type -- `i8::abs_diff(-128, 127)`
    /// is `255`, which is why the result is a `u8` and not an `i8` -- so the model
    /// widens the operands to the sign, subtracts the smaller from the larger, and
    /// narrows back. It exists on both signednesses; on an unsigned type it is a
    /// plain `|x - y|`, which is the same expression.
    AbsDiff,
    /// `iN::rotate_left`/`rotate_right`: a rotation by a `u32` amount.
    ///
    /// The amount is a `u32` beside a value of the method's own width, and `core`
    /// reduces it modulo the width (`u8::rotate_left(x, 8)` is `x`), so the model
    /// is a barrel shifter in each direction OR-ed together, with the amount read
    /// modulo the width. It exists on both signednesses and is total.
    Rotate(RotateKind),
    /// `iN::signum`: `-1`, `0` or `1` according to the sign of the operand.
    ///
    /// It exists only on the *signed* types (`u32::signum` is not a method), so a
    /// signed operand is the method's own meaning and an unsigned one is refused
    /// rather than read. Total, and the result has the operand's own type and
    /// width: `slt(x, 0) ? -1 : (sgt(x, 0) ? 1 : 0)`.
    Signum,
    /// `iN::div_euclid`: Euclidean division, the quotient `q` with `a == q*b + r`
    /// and `0 <= r < |b|`.
    ///
    /// A *total* value method: `iN::div_euclid` panics on a zero divisor and on
    /// `MIN / -1`, and both of those are what the plain `/` already reports -- the
    /// executor emits the same divide-by-zero and overflow obligations for a
    /// `div_euclid` call as for a `/`, from the operands, so the model only has to
    /// supply the *value*. Signed-only (the unsigned spelling is the plain `/`),
    /// and the value is the truncating quotient adjusted *away* from the remainder
    /// when the remainder is negative: `r = a % b; r >= 0 ? q : (b > 0 ? q - 1 : q
    /// + 1)`. The direction is the part that is easy to get backwards -- `-7`
    /// `div_euclid` `3` is `-3`, not `-2`.
    DivEuclid,
    /// `iN::rem_euclid`: Euclidean remainder, `0 <= r < |b|`.
    ///
    /// The companion of [`Self::DivEuclid`], with the same totality: the panics are
    /// a zero divisor and `MIN / -1`, both reported by the plain `/` obligations.
    /// The value is `r = a % b; r >= 0 ? r : r + |b|`.
    RemEuclid,
    /// `iN::div_ceil`: division rounding toward positive infinity.
    ///
    /// A *total* value method on the unsigned types (`u32::div_ceil`); on the
    /// signed types it is unstable and refused, so only an unsigned operand is
    /// read. The panics are the plain `/` ones (a zero divisor). The value is
    /// `q = a / b` rounded up when the remainder is nonzero: `r != 0 ? q + 1 : q`.
    DivCeil,
    /// `iN::midpoint`: the midpoint `(a + b) / 2`, rounded toward zero, computed
    /// *without* the overflow a plain `a + b` would have.
    ///
    /// A *total* value method on both signednesses (`u8::midpoint` is `(a + b) / 2`
    /// with the sum taken at one bit of headroom). The result rounds toward zero,
    /// not toward negative infinity: `(-5).midpoint(-2)` is `-3`, where the floor
    /// would be `-4`. The model never forms `a + b` at the operand width -- that is
    /// the whole point of the method -- so it is written as the classic
    /// `(a & b) + ((a ^ b) >> 1)` with the sign and rounding corrections a
    /// fixed-width machine needs: see [`midpoint`].
    Midpoint,
    /// `iN::reverse_bits`: the operand's bits in reverse order.
    ///
    /// Total, and exists on both signednesses; the result has the operand's type
    /// and width. The model is a shift-OR fold over the bits, so it is a plain
    /// bit permutation rather than a table.
    BitReverse,
    /// `iN::swap_bytes`: the operand's bytes in reverse order, with an odd trailing
    /// byte kept in place (a `u16` swaps its two bytes; a `u8` is unchanged).
    ///
    /// Total, both signednesses, and the model is a byte-level rotation by half the
    /// width -- which is why it reuses [`rotate`]: the bytes reverse, so each byte
    /// travels half the *width*, i.e. `w/2` bits (a `u16` rotates by `8`, a `u32`
    /// by `16`).
    ByteSwap,
    /// `iN::to_be`/`to_le` and the associated `iN::from_be`/`iN::from_le`: a
    /// byte-order conversion.
    ///
    /// `to_be` on a little-endian target is `swap_bytes`, and on a big-endian one
    /// it is the identity; `to_le` is the reverse. The *target* endianness is not
    /// something the dump states, so the model reads it from the compilation and
    /// applies the matching of the two. `from_be`/`from_le` are the involutions of
    /// `to_be`/`to_le` on the same target -- a conversion *from* a byte order is
    /// the same permutation as a conversion *to* it -- so one model serves both.
    /// Total, both signednesses. The `_bytes` forms are not modelled (they return
    /// an array, not an integer).
    ByteOrder(ByteOrderKind),
    /// `iN::to_ascii_uppercase`/`to_ascii_lowercase`: the ASCII case of a `u8`.
    ///
    /// Total, `u8`-only: `b'a'..=b'z'` becomes `b'A'..=b'Z'` (and the reverse),
    /// every other byte unchanged. The model is one `ite` over the range, so the
    /// two cannot disagree about the boundaries.
    AsciiCase(AsciiCaseKind),
    /// `Ord::min` or `Ord::max`: the smaller or larger of two operands of one
    /// type.
    ///
    /// Unlike every other shape this is a *trait* method, so its dump spelling is
    /// `<u8 as Ord>::min` rather than a `core::num::<impl …>` path. The executor
    /// therefore lets a same-dump body win and consults this model only as a
    /// fallback, so a local trait method of the same shape is inlined rather than
    /// modelled. It is total and reads the sign to pick the ordering, so both
    /// signednesses are modelled.
    MinMax(MinMaxKind),
    /// A widening integer conversion: `From::from` or `Into::into`.
    ///
    /// Like [`Intrinsic::MinMax`] this is a *trait* method, so the dump spells a
    /// call `<u16 as From<u8>>::from` (or `<u8 as Into<u16>>::into`) rather than a
    /// `core::num::<impl …>` path, and the model is a fallback behind the same-dump
    /// lookup. Unlike every other shape the two operand *types* differ -- that is
    /// the whole content of the call -- so the source and destination signednesses
    /// are carried explicitly. Only a strictly *widening* conversion is modelled;
    /// see [`Conversion`].
    Conversion(Conversion),
    /// The inherent `abs` on a signed integer: `i32::abs`.
    ///
    /// It is its own shape rather than a member of the four families because its
    /// failure is a **panic**, not a value: `i32::MIN.abs()` overflows, and there
    /// is no `wrapping_abs`-style spelling of the plain call to fall back on. So
    /// unlike every other unary shape the model yields a
    /// [`Outcome::ValueOrPanic`], and the executor turns the failure predicate
    /// into a reachable-panic obligation -- the same polarity as a rustc-inserted
    /// `assert`. `abs` exists only on the signed types, so a signed operand is the
    /// method's own meaning and an unsigned one is not this method at all.
    Abs,
    /// The inherent `unsigned_abs` on a signed integer: `i32::unsigned_abs`.
    ///
    /// Its value is the same magnitude `abs` computes, read as the *unsigned*
    /// type (`i8::unsigned_abs(-128)` is `128u8`). The model is therefore the same
    /// `0 - x`/`x` `ite` the families' `abs` uses, and it needs no failure
    /// predicate: at `MIN` the truncating `0 - x` yields the correct magnitude
    /// (`0 - 0x80 == 0x80 == 128`), which is exactly the bit pattern the *signed*
    /// `abs` cannot represent -- so `unsigned_abs` is total where `abs` panics.
    /// Signed-only, like `abs`.
    UnsignedAbs,
    /// `iN::cast_unsigned` / `uN::cast_signed`: reinterpret the same `w` bits at
    /// the opposite signedness.
    ///
    /// The *value* is the operand unchanged -- a cast between same-width
    /// signednesses is a re-interpretation, not a conversion -- so the model
    /// carries only the resulting *type*, which is what a later comparison or
    /// division reads. It is the one shape whose result signedness is the
    /// *opposite* of the operand's, so it cannot be folded into the "result has
    /// the operand's sign" rule the rest of `eval` follows. Total, and the same
    /// width as the operand (`i32::cast_unsigned` is `u32`).
    SignednessCast,
    /// The inherent `pow`: `a.pow(b)`.
    ///
    /// Like [`Intrinsic::Abs`] its failure is a **panic** (`assert!` on overflow),
    /// not a value, and there is no family-prefixed spelling of the plain call to
    /// fall back on -- the four families' `wrapping_pow`/`checked_pow`/… are their
    /// own `Intrinsic::Pow` shapes. So it yields a [`Outcome::ValueOrPanic`], and
    /// the executor turns the failure predicate into a reachable-panic obligation,
    /// the same polarity as the families' `pow` (which the plain call's debug
    /// `assert!` mirrors). Total on both signednesses.
    PowPanic,
    /// The inherent `Ord::clamp`: `x.clamp(lo, hi)`.
    ///
    /// Three operands, so it does not fit `eval`'s two-operand signature and is
    /// evaluated by [`clamp`] instead. Like [`Intrinsic::Abs`] its failure is a
    /// **panic** -- `assert!(lo <= hi)`, the only panic in `core`'s body, since
    /// clamping an out-of-range `x` is the method's whole purpose -- so it yields
    /// a [`Outcome::ValueOrPanic`]. The dump spells it as the *trait* method
    /// `<u32 as Ord>::clamp`, so it is admitted by name like
    /// [`Intrinsic::MinMax`] and the same-dump lookup still answers a local trait
    /// first.
    Clamp,
    /// A standard-library enum method: `Option`'s `unwrap`, `unwrap_or`,
    /// `expect`, `is_some`, `is_none`, and `Result`'s `is_ok`, `is_err`,
    /// `unwrap`, `unwrap_or`.
    ///
    /// These read the receiver's *enum* state rather than a bit-vector operand, so
    /// they are answered by the executor from its discriminant/payload stores and
    /// `eval` returns `None` for them. They are modelled only on the standard
    /// library's `Option`/`Result` (see [`names_option_impl`] and
    /// [`names_result_impl`]); a same-dump body always wins the lookup first.
    OptionMethod(OptionMethod),
    /// A `for`-loop range: the `RangeInclusive`/`Range` shapes and the
    /// `IntoIterator`/`Iterator` methods the desugaring calls on them.
    ///
    /// These are the first modelled methods whose receiver is a *struct* rather
    /// than an integer, an enum or a slice, so they are answered by the executor
    /// from its field store: the `start`/`end`/`exhausted` words a `new` wrote and
    /// a `next` advances. `eval` returns `None` for all of them. The struct is the
    /// standard library's own, so the *type path* is checked (see [`names_range`]);
    /// a same-dump body always wins the lookup first.
    Range(RangeMethod),
    /// `Try::branch`, the `?` operator's first call.
    ///
    /// `expr?` lowers to `<T as Try>::branch(expr)` producing a
    /// `ControlFlow<Residual, T>`, whose `Continue` arm carries the success value
    /// and whose `Break` arm carries the residual (the error, wrapped). The
    /// executor answers it from the receiver's enum state and writes the
    /// `ControlFlow`'s tag and both payloads, so the `switchInt` on
    /// `discriminant(_)` and the `(_ as Continue).0` / `(_ as Break).0` downcasts
    /// that follow decide. Like [`Intrinsic::MinMax`] this is a *trait* method
    /// (`<Result<u8, u8> as Try>::branch`), so the model is a fallback behind the
    /// same-dump lookup. `eval` returns `None` for it.
    TryBranch,
    /// `FromResidual::from_residual`, the `?` operator's second call.
    ///
    /// On the `Break` arm `from_residual` converts the residual back into the
    /// function's return enum (`Result::Err(e)` / `Option::None`). It is the
    /// mirror of [`Intrinsic::TryBranch`]: the residual's failure tag and payload
    /// become the result enum's. `eval` returns `None` for it.
    FromResidual,
}

/// A method on a `for`-loop range.
///
/// The `for` desugaring lowers to a fixed set of calls, and this is exactly that
/// set: `RangeInclusive::new` / `Range::new` construct, `into_iter` is the
/// identity the desugaring wraps, and `next` yields the next element or `None`.
/// Modelling them makes the commonest loop in Rust reachable through the existing
/// loop machinery (an `invariant:` decides it; without one it is unwound like any
/// other loop).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeMethod {
    /// `RangeInclusive::new(start, end)` -> `RangeInclusive { start, end, exhausted: false }`.
    /// `Range::new(start, end)` -> `Range { start, end }`.
    New,
    /// `IntoIterator::into_iter(range)` -> the range itself. The desugaring calls
    /// this once before the loop; it copies the range and returns it unchanged.
    IntoIter,
    /// `Iterator::next(&mut range) -> Option<Idx>`.
    ///
    /// The exclusive `Range` yields `start` while `start < end` and then `None`.
    /// The inclusive `RangeInclusive` yields `start` while it is not exhausted and
    /// then `None`, marking itself exhausted once `start` reaches the end -- see
    /// [`RangeMethod::Next`]'s evaluator for the exact predicate, which has to
    /// reproduce `core`'s `forward_overflowing` at the type's boundary.
    Next,
}

/// Which family of a `core::num` method name a call belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Family {
    /// `wrapping_*`: the result modulo `2^w`.
    Wrapping,
    /// `saturating_*`: the result clamped to the type's range.
    Saturating,
    /// `checked_*`: `Option<T>`.
    Checked,
    /// `overflowing_*`: `(T, bool)`.
    Overflowing,
}

/// A unary operator that each family defines.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    /// Negation: `-x`.
    Neg,
    /// Absolute value: `|x|`.
    Abs,
}

/// A `bool`-valued predicate: a `core::num` method that answers a truth value
/// rather than a number.
///
/// These are the methods whose *return type* is `bool`, so unlike every other
/// shape the model produces a [`Pred`] rather than a [`Var`] and the executor
/// writes it with [`Env::set`] as a `Val::Bool`. The return width is one bit by
/// construction, which is why no `result_w` is read for them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoolKind {
    /// `is_power_of_two`: true exactly for `1 << k`, `k < w`.
    ///
    /// A *total* predicate, and unsigned-only: `is_power_of_two` is not a method
    /// on the signed types, so a dump that calls it is unsigned or is not a real
    /// dump. `0` is not a power of two (the zero bit pattern is `0` clear bits,
    /// not one), and the type's width is the highest exponent it can hold, so a
    /// signed reading would be wrong in both directions -- see [`is_modelled`].
    PowerOfTwo,
    /// The ASCII class tests on `u8`: `is_ascii_digit`, `is_ascii_alphabetic`,
    /// `is_ascii_alphanumeric`, `is_ascii_uppercase`, `is_ascii_lowercase`,
    /// `is_ascii_hexdigit`, `is_ascii_whitespace`, `is_ascii_punctuation`,
    /// `is_ascii_control` and `is_ascii`.
    ///
    /// `core` defines every one of these as a range test on the byte, so the model
    /// is one or more comparisons rather than a table: `is_ascii_digit` is
    /// `b >= b'0' && b <= b'9'`, `is_ascii` is `b < 128`, and so on. They are
    /// unsigned-only and exist only on `u8` -- `core` has no `is_ascii_digit` on
    /// `u32` -- so a signed or wider receiver is not this method.
    Ascii(AsciiKind),
    /// `is_negative`: the value is below zero, which is the top bit set on a
    /// signed type. The model is `slt(x, 0)`, and it exists only on the signed
    /// types, so an unsigned receiver is refused rather than read (the top bit of
    /// a `u8` is not a sign).
    Negative,
    /// `is_positive`: the value is above zero. The model is `sgt(x, 0)`, on the
    /// signed types only for the same reason as [`Self::Negative`].
    Positive,
    /// `is_multiple_of`: true exactly when `b != 0 && a % b == 0`.
    ///
    /// The `b != 0` half is what makes it total: `core` defines `is_multiple_of(0)`
    /// as `a == 0` (so `0.is_multiple_of(0)` is `true` and `5.is_multiple_of(0)` is
    /// `false`), which is the same predicate `a % b == 0 && b != 0 || a == 0`. It
    /// exists only on the *unsigned* types -- `i32::is_multiple_of` does not exist
    /// on this toolchain -- so a signed receiver is refused rather than read, and
    /// the model is `b != 0 && urem(a, b) == 0 || a == 0`.
    MultipleOf,
}

/// The ASCII class a `u8` byte belongs to, for [`BoolKind::Ascii`].
///
/// Each variant is one `core` method, and the model is the method's own range
/// test, so the two cannot disagree about the boundaries. A byte is a `u8`, so
/// every comparison here is unsigned and the constants are the ASCII code points
/// spelled as their character literals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AsciiKind {
    /// `is_ascii_digit`: `b'0'..=b'9'`.
    Digit,
    /// `is_ascii_alphabetic`: `b'a'..=b'z'` or `b'A'..=b'Z'`.
    Alphabetic,
    /// `is_ascii_alphanumeric`: digit or alphabetic.
    Alphanumeric,
    /// `is_ascii_uppercase`: `b'A'..=b'Z'`.
    Uppercase,
    /// `is_ascii_lowercase`: `b'a'..=b'z'`.
    Lowercase,
    /// `is_ascii_hexdigit`: digit, `b'A'..=b'F'` or `b'a'..=b'f'`.
    HexDigit,
    /// `is_ascii_whitespace`: space, tab, newline, form feed or carriage return.
    Whitespace,
    /// `is_ascii_punctuation`: the printable non-alphanumeric, non-space ASCII.
    Punctuation,
    /// `is_ascii_control`: the C0 controls and DEL, `0..=0x1f` or `0x7f`.
    Control,
    /// `is_ascii`: `b < 128`.
    Ascii,
}

/// `Ord::min` and `Ord::max`: the smaller or larger of two values of one type.
///
/// Unlike every other shape these are *trait* methods, not inherent ones, so the
/// dump spells a call `<u8 as Ord>::min` -- the `Ord` trait itself, with no
/// `core::num::<impl …>` path. That is why the model is a *fallback*: the executor
/// resolves a same-dump body first and reaches the model only when none claims the
/// name, so a local trait method of the same shape is inlined rather than
/// modelled. The trait path must also be the standard library's `Ord`, which is
/// what keeps a differently-qualified local trait out (see [`names_ord_trait`]).
/// The model itself is total and reads the sign to pick the comparison: `min`/`max`
/// are the same two-operand ite either way, only the ordering predicate differs, so
/// both signednesses are modelled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MinMaxKind {
    /// The smaller of the two operands: `a <= b ? a : b`.
    Min,
    /// The larger of the two operands: `a >= b ? a : b`.
    Max,
}

/// A byte-order conversion: `to_be` or `to_le`.
///
/// `core` has no `to_ne` *value* method (only `to_ne_bytes`), so there are two
/// variants, not three. Both depend on the *target's* endianness, which the dump
/// does not state; the model reads it from the compilation
/// (`cfg!(target_endian)`) so a big-endian target gets the identity for `to_be`
/// and the swap for `to_le`, and a little-endian target the reverse.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByteOrderKind {
    /// `to_be`: big-endian byte order.
    Be,
    /// `to_le`: little-endian byte order.
    Le,
}

/// `to_ascii_uppercase`/`to_ascii_lowercase` on a `u8`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AsciiCaseKind {
    /// `to_ascii_uppercase`: `b'a'..=b'z'` -> the matching uppercase letter.
    Upper,
    /// `to_ascii_lowercase`: `b'A'..=b'Z'` -> the matching lowercase letter.
    Lower,
}

/// A standard-library enum method the model knows: `Option`'s `unwrap`,
/// `unwrap_or`, `expect`, `is_some`, `is_none`, and `Result`'s `is_ok`, `is_err`,
/// `unwrap`, `unwrap_or`.
///
/// Unlike every other modelled shape these read the receiver's *enum* state -- the
/// tag and the payload -- rather than a bit-vector operand, so the model is not a
/// function of a value but a reader of the environment's discriminant/payload
/// stores. The executor is where they are answered (see `enum_method`), because
/// only it holds those stores; `eval` has no operand to compute them from and
/// returns `None` for them the way it does for `slice::len`.
///
/// The receiver is `self` for `unwrap`/`unwrap_or` and `&self` for the predicates,
/// so the dump prints `_0 = Option::<u32>::unwrap(move _3)` for the first group
/// and `_2 = &_1; _0 = Option::<u8>::is_some(move _2)` for the second. The
/// executor follows the reference, so both spellings reach the same enum local.
///
/// The variant a method reads is carried *in the method* rather than looked up per
/// enum: for `Option` the payload is on `Some` (tag [`SOME_TAG`]) and `is_some` is
/// that tag; for `Result` the payload is on `Ok` (tag 0) and `is_ok` is that tag.
/// One executor arm answers both families, because the two are the same shape with
/// the payload on the other discriminant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OptionMethod {
    /// `unwrap_or(default)`: the payload on the success variant, the default on
    /// the other. Total.
    UnwrapOr,
    /// `unwrap()`: the payload, and a **panic** on the failure variant. The one
    /// shape here whose failure is a panic, so it yields a reachable-panic
    /// obligation rather than a plain value.
    Unwrap,
    /// `expect(msg)`: the payload, and a **panic** on the failure variant with the
    /// given message. Identical to [`OptionMethod::Unwrap`] except that the message
    /// is carried rather than fixed, so the two share one model and differ only in
    /// the panic text.
    Expect,
    /// `is_some()` / `is_ok()`: the tag equals the *success* discriminant
    /// ([`SOME_TAG`] for `Option`, `0` for `Result`).
    IsSuccess,
    /// `is_none()` / `is_err()`: the tag equals the *failure* discriminant
    /// (`0` for `Option`, `1` for `Result`). `core` defines it as `!is_success()`,
    /// and the model tests the tag against the failure constant so the two cannot
    /// disagree.
    IsFailure,
    /// `Option::ok_or(err)`: `Ok(payload)` on `Some`, `Err(err)` on `None`. Total
    /// for a scalar payload and a scalar error. The error argument is moved into
    /// the result on the `None` path and dropped on the `Some` path, so its
    /// destructor is the reason this is not unconditionally total (see the
    /// executor's glue check).
    OkOr,
    /// `Result::ok()`: `Some(payload)` on `Ok`, `None` on `Err`. The `Err` payload
    /// is dropped, so its destructor is the glue the executor checks.
    Ok,
    /// `Result::err()`: `Some(payload)` on `Err`, `None` on `Ok`. The `Ok` payload
    /// is dropped, so its destructor is the glue the executor checks.
    Err,
}

/// A widening integer conversion: `u16::from(x)` where `x: u8`, `x.into()`.
///
/// The two operand types differ -- that is what the call *is* -- so unlike every
/// other shape the model reads two widths and two signednesses. The value is the
/// source widened to the destination's width, and the *source's* signedness picks
/// the extension: a signed source sign-extends (`-1i8` to `i16` is `-1`), an
/// unsigned one zero-fills (`255u8` to `u16` is `255`). The destination's
/// signedness only labels the result.
///
/// # Why only a *widening* conversion is modelled
///
/// `core` implements `From` for the integer types only where the source fits
/// entirely in the destination, and never across signedness: `u16::from(u8)`,
/// `i16::from(i8)` and `i16::from(u8)` exist, while `u16::from(i8)` and
/// `i8::from(u8)` do not (they would not be total, so `core` has no such `impl`).
/// So a real `<D as From<S>>::from` call with `S` and `D` both integer is
/// *necessarily* a widening or a same-width call, and both are exactly a zero- or
/// sign-extension of the source's `w` bits to the destination's width (a same-width
/// extension leaves the value unchanged, which is `core`'s reflexive `impl<T>
/// From<T> for T`). A model that saw only a *narrowing* call would have to guess at
/// a truncation `core` never performs; [`eval`] refuses those by name, and the
/// executor refuses a call whose types it cannot read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Conversion {
    /// `From::from`: `<D as From<S>>::from(x)`.
    From,
    /// `Into::into`: `<S as Into<D>>::into(x)`.
    Into,
}

/// The source and destination types of a conversion call, read from its name.
///
/// A conversion's two types are both in the name, and reading them there is what
/// keeps the model independent of how the executor happens to have typed the
/// argument: `From`'s spelling is `<DEST as From<SRC>>::from`, so the *self* type
/// is the destination and the type parameter is the source, while `Into`'s is
/// `<SRC as Into<DEST>>::into`, where they are the other way round. A name whose
/// self type or parameter does not parse as an integer is refused by the caller,
/// which reads the widths with [`int_width`] and requires the destination to be at
/// least as wide as the source -- a real integer `From` is always a widening.
pub fn conversion_types(name: &str, kind: Conversion) -> Option<(Ty, Ty)> {
    let (self_part, after_as) = name.rsplit_once(" as ")?;
    let self_ty = Ty::parse(self_part.trim_start_matches('<'));
    let open = after_as.find('<')?;
    let close = after_as.find(">::")?;
    if close <= open {
        return None;
    }
    // `after_as` is `TRAIT<PARAM>>::method`, so the slice up to `>::` carries the
    // trait's own closing `>`. An integer type never contains `>`, so dropping a
    // trailing one is exactly the type parameter and not a nested generic.
    let param = after_as[open + 1..close].trim_end_matches('>');
    let param_ty = Ty::parse(param);
    Some(match kind {
        Conversion::From => (param_ty, self_ty),
        Conversion::Into => (self_ty, param_ty),
    })
}

/// Whether a type is one of the integer types the model reads a width and a
/// signedness from.
///
/// `u128`/`i128` are excluded: the engine is 64 bits wide, so a conversion *into*
/// them has no term to build. `bool` and `char` are excluded too -- `u8::from(true)`
/// and `u32::from('a')` are real `From` impls, but their source is not an integer
/// whose bits the engine holds, so there is nothing to widen.
pub fn is_modelled_int(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::Usize | Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64
            | Ty::Isize
    )
}

/// The width of a modelled integer type, in bits.
pub fn int_width(ty: &Ty) -> Option<u8> {
    if !is_modelled_int(ty) {
        return None;
    }
    ty.width()
}

/// The bit-vector of a conversion's argument: the source widened to `dst_w`.
///
/// `x` is the source term at its own width, `src_signed` its signedness. A signed
/// source sign-extends and an unsigned one zero-fills, which is the *same* choice
/// the executor's `as`-cast makes (see the `Rvalue::Cast` arm); a conversion and a
/// cast of the same shape are the same term. When the destination is no wider than
/// the source -- which a real `From` never is, but a malformed dump could spell --
/// the value is truncated, so nothing here can build a term wider than `dst_w`.
pub fn convert_value(x: Var, src_signed: bool, dst_w: u8) -> Var {
    if src_signed {
        smt::sign_extend(x, dst_w)
    } else {
        smt::truncate(x, dst_w)
    }
}

/// A bit count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BitKind {
    /// The number of set bits: `count_ones`.
    Ones,
    /// The number of high zero bits, before the highest set bit: `leading_zeros`.
    LeadingZeros,
    /// The number of low zero bits, before the lowest set bit: `trailing_zeros`.
    TrailingZeros,
    /// The number of clear bits: `count_zeros`.
    ///
    /// `core` defines it as `count_ones(!x)`, and the model computes it that way
    /// rather than by a second summation, so the two cannot disagree.
    CountZeros,
    /// The number of high set bits, before the highest clear bit: `leading_ones`.
    ///
    /// `core` defines it as `leading_zeros(!x)`.
    LeadingOnes,
    /// The number of low set bits, before the lowest clear bit: `trailing_ones`.
    ///
    /// `core` defines it as `trailing_zeros(!x)`.
    TrailingOnes,
}

/// An integer logarithm: `ilog2` or `ilog10`.
///
/// Distinct from [`BitKind`] because a log is not a bit *count*: it is not a sum
/// over the operand's bits, and unlike a count it *panics* on a non-positive
/// argument. Keeping it a separate enum is what stops a log from being answered
/// by the count path, which is total.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogKind {
    /// `ilog2`: the index of the highest set bit, `w - 1 - leading_zeros(x)` for
    /// `x > 0`.
    Ilog2,
    /// `ilog10`: the largest `k` with `10^k <= x`.
    Ilog10,
}

/// Which way a rotation turns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RotateKind {
    /// Bits move toward the high end; the top bits wrap to the bottom.
    Left,
    /// Bits move toward the low end; the bottom bits wrap to the top.
    Right,
}

impl Intrinsic {
    /// True for the shapes that take one operand and no operator.
    ///
    /// `eval` and the executor both branch on this: a unary call has no second
    /// argument to read, so the two-operand path must not be entered for it.
    pub fn is_unary(self) -> bool {
        matches!(
            self,
            Intrinsic::Unary(..)
                | Intrinsic::Bits(_)
                | Intrinsic::Ilog(_)
                | Intrinsic::CheckedIlog(_)
                | Intrinsic::Bool(
                    BoolKind::PowerOfTwo
                        | BoolKind::Ascii(_)
                        | BoolKind::Negative
                        | BoolKind::Positive
                )
                | Intrinsic::Abs
                | Intrinsic::UnsignedAbs
                | Intrinsic::SignednessCast
                | Intrinsic::Signum
                | Intrinsic::NextPowerOfTwo
                | Intrinsic::CheckedNextPowerOfTwo
                | Intrinsic::BitReverse
                | Intrinsic::ByteSwap
                | Intrinsic::ByteOrder(_)
                | Intrinsic::AsciiCase(_)
                | Intrinsic::OptionMethod(
                    OptionMethod::Unwrap
                        | OptionMethod::Expect
                        | OptionMethod::IsSuccess
                        | OptionMethod::IsFailure
                )
        )
    }
}

/// What a modelled call produced.
#[derive(Clone, Copy, Debug)]
pub enum Outcome {
    /// A plain value, written to the destination local.
    Value(Var),
    /// An `Option`. The tag is a *term*, not a constant: it is `1` where the
    /// operation is defined and `0` where it is not, so the `switchInt` that
    /// consumes it takes the right arm on each path. The payload is the
    /// operation's result, and it is only ever read on a path whose condition
    /// already forces the tag to `Some` -- rustc emits the downcast projection
    /// only inside that arm, which is what makes an ungated payload sound.
    Option { tag: Var, payload: Var },
    /// A `(T, bool)` tuple: the wrapped value and the overflow flag, for the
    /// `overflowing_*` family. Field 0 is the value and field 1 is the flag,
    /// which is the order rustc's own `(result, overflowed)` tuple uses.
    ///
    /// Unlike the `Option` tag, the flag is written as a `bool` and not as a
    /// word: nothing compares it to a variant discriminant, so it is read by a
    /// `bool` consumer (`assert(!flag)`, or a `ret.1` in a contract).
    Tuple { value: Var, overflowed: Pred },
    /// A `bool`: the whole result of a predicate method (`is_power_of_two`).
    ///
    /// The destination local's type is `bool`, so the value is a `Pred` and not a
    /// `Var` -- writing a one-bit word into a `bool` local would leave the local
    /// readable only as a word, and the `if` that consumes it reads a predicate.
    Bool(Pred),
    /// A value plus a *reachable-panic* predicate: the shape for a method whose
    /// failure is a panic rather than a value (`iN::abs` at `MIN`, `Ord::clamp`
    /// with `lo > hi`).
    ///
    /// This is deliberately not the `Tuple` shape: a `Tuple` is the
    /// `overflowing_*` return, where the flag is a `bool` the program *reads*.
    /// Here the predicate is not part of any value -- it is the condition under
    /// which the call panics -- so the executor turns it into an obligation of
    /// the same polarity as a rustc-inserted `assert`: the call is safe exactly
    /// where `path ∧ fails` is unsatisfiable. Nothing assumes the predicate on
    /// the fall-through path; the panic is *checked* separately, and the result
    /// value is written unconditionally because a path where the predicate holds
    /// is already reported as a failure.
    ValueOrPanic {
        /// The value the call yields when it does not panic.
        value: Var,
        /// The condition under which the call panics.
        fails: Pred,
    },
}

/// The family a `core::num` method name belongs to, if any.
///
/// The name is matched after the last `::`, so both `core::num::<impl
/// u8>::checked_add` and a bare `checked_add` resolve. The whole suffix is
/// matched, not a prefix of it, so `wrapping_add_signed` and `saturating_pow`
/// are refused rather than read as `wrapping_add` and `saturating_add`.
///
/// The bit counts are matched before the prefix split: they have no
/// `wrapping_`/`saturating_`/`checked_`/`overflowing_` prefix, and reading them
/// through the split would look for an operator named `ones`, `zeros`,
/// `leading_zeros` or `trailing_ones` in the operator table. Matching them first
/// keeps the split honest -- it only ever sees a name it could actually have
/// prefixed.
pub fn classify(name: &str) -> Option<Intrinsic> {
    let short = name.rsplit("::").find(|s| !s.starts_with('<')).unwrap_or(name);
    match short {
        "count_ones" => return Some(Intrinsic::Bits(BitKind::Ones)),
        "count_zeros" => return Some(Intrinsic::Bits(BitKind::CountZeros)),
        "leading_zeros" => return Some(Intrinsic::Bits(BitKind::LeadingZeros)),
        "leading_ones" => return Some(Intrinsic::Bits(BitKind::LeadingOnes)),
        "trailing_zeros" => return Some(Intrinsic::Bits(BitKind::TrailingZeros)),
        "trailing_ones" => return Some(Intrinsic::Bits(BitKind::TrailingOnes)),
        _ => {}
    }
    // The `bool`-valued predicates. Like the bit counts they carry no family
    // prefix, so they are matched before the split for the same reason.
    if short == "is_power_of_two" {
        return Some(Intrinsic::Bool(BoolKind::PowerOfTwo));
    }
    // The sign predicates on the signed types. Matched by their exact names, and
    // only on a `core::num::<impl …>` path (see `is_modelled`), so a user method
    // spelled the same way is not read as one.
    if short == "is_negative" {
        return Some(Intrinsic::Bool(BoolKind::Negative));
    }
    if short == "is_positive" {
        return Some(Intrinsic::Bool(BoolKind::Positive));
    }
    // `is_multiple_of`, which like `is_power_of_two` has no family prefix. It is
    // unsigned-only (see `is_modelled`), so it is matched by its exact name and
    // read only on a `core::num::<impl …>` path.
    if short == "is_multiple_of" {
        return Some(Intrinsic::Bool(BoolKind::MultipleOf));
    }
    // The ASCII class tests on `u8`. Their receiver is `&u8`, not `u8` -- the dump
    // prints `_3 = &_1; is_ascii_digit(move _3)` -- but that is the *executor's*
    // concern, not the model's: the model sees the byte. Each is matched by its
    // exact name so no prefix split can mistake it for an operator.
    if let Some(kind) = ascii_kind(short) {
        return Some(Intrinsic::Bool(BoolKind::Ascii(kind)));
    }
    // `slice::len`/`is_empty`. `Vec`, `String` and `str` also spell `len`, and
    // their length is not the slice-length variable this model reads, so the
    // *path* is checked rather than the tail alone: only an inherent `[T]` slice
    // method is read as a slice length. Anything else falls through and stays
    // unmodelled, which is the honest answer for a length the frontend does not
    // hold.
    if names_slice_impl(name) {
        if short == "is_empty" {
            return Some(Intrinsic::SliceIsEmpty);
        }
        if short == "len" {
            return Some(Intrinsic::SliceLen);
        }
        if short == "first" {
            return Some(Intrinsic::SliceFirst);
        }
        // `get` is printed with its index type (`::<usize>`), so the tail is not
        // the bare name; match the head before any generic arguments.
        if short == "get" || short.starts_with("get::<") {
            return Some(Intrinsic::SliceGet);
        }
    }
    // The standard library's `Option`/`Result` methods. Like the slice shapes
    // these read the receiver's own state rather than a bit-vector operand -- the
    // tag and the payload -- so the executor answers them from its
    // discriminant/payload stores and `eval` returns `None` for them. The *path*
    // is checked (see `names_option_impl`/`names_result_impl`) so a user type
    // spelled `Option`/`Result` is refused, and the same-dump lookup still answers
    // a real body before the model.
    if names_option_impl(name) {
        match short {
            "unwrap_or" => return Some(Intrinsic::OptionMethod(OptionMethod::UnwrapOr)),
            "unwrap" => return Some(Intrinsic::OptionMethod(OptionMethod::Unwrap)),
            "expect" => return Some(Intrinsic::OptionMethod(OptionMethod::Expect)),
            "is_some" => return Some(Intrinsic::OptionMethod(OptionMethod::IsSuccess)),
            "is_none" => return Some(Intrinsic::OptionMethod(OptionMethod::IsFailure)),
            "ok_or" => return Some(Intrinsic::OptionMethod(OptionMethod::OkOr)),
            _ => {}
        }
    }
    if names_result_impl(name) {
        match short {
            "unwrap_or" => return Some(Intrinsic::OptionMethod(OptionMethod::UnwrapOr)),
            "unwrap" => return Some(Intrinsic::OptionMethod(OptionMethod::Unwrap)),
            "expect" => return Some(Intrinsic::OptionMethod(OptionMethod::Expect)),
            "is_ok" => return Some(Intrinsic::OptionMethod(OptionMethod::IsSuccess)),
            "is_err" => return Some(Intrinsic::OptionMethod(OptionMethod::IsFailure)),
            "ok" => return Some(Intrinsic::OptionMethod(OptionMethod::Ok)),
            "err" => return Some(Intrinsic::OptionMethod(OptionMethod::Err)),
            _ => {}
        }
    }
    // The `for`-loop ranges: `RangeInclusive`/`Range` and the `IntoIterator` /
    // `Iterator` methods the desugaring calls on them. Like the `Option` shapes
    // these are inherent/standard-library methods answered from the executor's
    // stores rather than from a bit-vector operand, and the *path* is checked
    // (see `names_range`) so a user type spelled `RangeInclusive` is refused. The
    // same-dump lookup still answers a real body first.
    if names_range(name) {
        match short {
            "new" => return Some(Intrinsic::Range(RangeMethod::New)),
            "into_iter" => return Some(Intrinsic::Range(RangeMethod::IntoIter)),
            "next" => return Some(Intrinsic::Range(RangeMethod::Next)),
            _ => {}
        }
    }
    // `Try::branch` and `FromResidual::from_residual`, the two calls the `?`
    // operator's desugaring makes. Both are *trait* methods -- the dump spells
    // them `<Result<u8, u8> as Try>::branch` and `<Result<u8, u8> as
    // FromResidual<Result<!, u8>>>::from_residual` -- so there is no
    // `core::num::<impl …>` path and they are admitted by name like `Ord::min`.
    // The trait path must be the standard library's `Try`/`FromResidual` (see
    // `names_try`/`names_from_residual`), so a module-qualified local `m::Try` is
    // refused, and the same-dump lookup answers a real body before the model.
    if short == "branch" {
        if !names_try(name) {
            return None;
        }
        return Some(Intrinsic::TryBranch);
    }
    if short == "from_residual" {
        if !names_from_residual(name) {
            return None;
        }
        return Some(Intrinsic::FromResidual);
    }
    // `Ord::min`/`Ord::max`. These are *trait* methods, so the name is matched on
    // the trait path rather than a `core::num::<impl …>` path: the dump spells the
    // call `<u8 as Ord>::min`, naming the trait itself. `min`/`max` are matched
    // only when that path is the standard library's `Ord` (see `names_ord_trait`),
    // so a same-named method on any other trait (or an inherent one) is not read as
    // `Ord`'s. That is a *narrower* match than the suffix match the other shapes
    // use, deliberately: the trait name is the only thing distinguishing this from
    // an unrelated `min`, and widening it would answer a call the model has no
    // definition for.
    if short == "min" || short == "max" {
        if !names_ord_trait(name) {
            return None;
        }
        let kind = if short == "min" { MinMaxKind::Min } else { MinMaxKind::Max };
        return Some(Intrinsic::MinMax(kind));
    }
    // `Ord::clamp`: the same trait-method spelling as `min`/`max`, and admitted
    // the same way for the same reason -- a three-operand method has no
    // `core::num::<impl …>` spelling, so refusing the name would make it
    // permanently unmodellable. The trait path must be the standard library's
    // `Ord`, so a module-qualified local `m::Ord` is refused, and the caller's
    // same-dump lookup answers a crate-root `Ord` before the model is consulted.
    if short == "clamp" {
        if !names_ord_trait(name) {
            return None;
        }
        return Some(Intrinsic::Clamp);
    }
    // `From::from`/`Into::into`. These are *trait* methods with a type parameter,
    // so the dump spells `<u16 as From<u8>>::from`: the trait path is read the same
    // way `Ord`'s is (see `trait_path`), which is what keeps a module-qualified
    // local trait (`m::From`) out. The two operand *types* are not in this name --
    // they are read from the call's arguments and destination by the executor --
    // so `classify` can only answer "this is a conversion"; whether it is one the
    // model covers is decided there, from the types.
    if short == "from" || short == "into" {
        if !names_conversion_trait(name) {
            return None;
        }
        let kind = if short == "from" { Conversion::From } else { Conversion::Into };
        return Some(Intrinsic::Conversion(kind));
    }
    // The inherent `iN::abs`. It is not one of the four families -- there is no
    // `wrapping_abs`-style spelling of the plain call, and its failure is a
    // *panic* (`abs(MIN)` overflows) rather than a value -- so it is matched here,
    // before the prefix split, which would otherwise see `abs` and look for an
    // operator of that name in the table below. It is the plain `abs` only: the
    // families' `wrapping_abs`/`checked_abs`/… are matched by the split below.
    if short == "abs" {
        return Some(Intrinsic::Abs);
    }
    // The inherent `unsigned_abs`: the same magnitude as `abs`, read as the
    // unsigned type. Its result type is the unsigned sibling of the receiver's
    // (`i32::unsigned_abs` is `u32`), so it is labelled unsigned on the way out.
    if short == "unsigned_abs" {
        return Some(Intrinsic::UnsignedAbs);
    }
    // The inherent `abs_diff`, `rotate_left` and `rotate_right`. Like `abs` they
    // are not family-prefixed, so they are matched before the split; unlike it
    // they are total (no panic), so they are plain values rather than a
    // `ValueOrPanic`. `abs_diff` exists on both signednesses; the rotations exist
    // on both too and reduce the amount modulo the width.
    if short == "abs_diff" {
        return Some(Intrinsic::AbsDiff);
    }
    if short == "rotate_left" {
        return Some(Intrinsic::Rotate(RotateKind::Left));
    }
    if short == "rotate_right" {
        return Some(Intrinsic::Rotate(RotateKind::Right));
    }
    // The remaining total, family-less value methods. Like `abs_diff` and the
    // rotations they are matched before the family split, which would otherwise
    // look for an operator of that name. `signum`, the Euclidean pair and
    // `div_ceil` are signed/unsigned-specific in different directions (see
    // `is_modelled`); the byte permutations and orderings exist on both
    // signednesses and are pure bit/byte moves.
    if short == "signum" {
        return Some(Intrinsic::Signum);
    }
    // The same-width signedness re-interpretation: `i32::cast_unsigned` is `u32`
    // and `u32::cast_signed` is `i32`. The value is the operand unchanged, so the
    // model only has to carry the *type*; matched by their exact names so no
    // prefix split can mistake them.
    if short == "cast_unsigned" || short == "cast_signed" {
        return Some(Intrinsic::SignednessCast);
    }
    if short == "div_euclid" {
        return Some(Intrinsic::DivEuclid);
    }
    if short == "rem_euclid" {
        return Some(Intrinsic::RemEuclid);
    }
    if short == "div_ceil" {
        return Some(Intrinsic::DivCeil);
    }
    if short == "midpoint" {
        return Some(Intrinsic::Midpoint);
    }
    if short == "next_multiple_of" {
        return Some(Intrinsic::NextMultipleOf);
    }
    // The `checked_` spelling: the same value and failure as the plain method, as
    // an `Option`. It is its own shape rather than a `Family` member because the
    // plain method is a `ValueOrPanic` (it panics), not a `Value`, so the family
    // split has nothing to attach to.
    if short == "checked_next_multiple_of" {
        return Some(Intrinsic::CheckedNextMultipleOf);
    }
    // The "round up to a power of two" pair, the sibling of `is_power_of_two`.
    // Unsigned-only (there is no such method on the signed types), and matched by
    // their exact names so no prefix split can mistake `next_power_of_two` for
    // `next_multiple_of` or an operator.
    if short == "next_power_of_two" {
        return Some(Intrinsic::NextPowerOfTwo);
    }
    if short == "checked_next_power_of_two" {
        return Some(Intrinsic::CheckedNextPowerOfTwo);
    }
    if short == "ilog2" {
        return Some(Intrinsic::Ilog(LogKind::Ilog2));
    }
    if short == "ilog10" {
        return Some(Intrinsic::Ilog(LogKind::Ilog10));
    }
    // The `checked_` spellings of the logs: the same value as an `Option`, `None`
    // exactly where the plain form panics. They are their own shape for the same
    // reason `checked_next_multiple_of` is -- the plain form is a `ValueOrPanic`.
    if short == "checked_ilog2" {
        return Some(Intrinsic::CheckedIlog(LogKind::Ilog2));
    }
    if short == "checked_ilog10" {
        return Some(Intrinsic::CheckedIlog(LogKind::Ilog10));
    }
    // The inherent `pow`: `a.pow(b)`. Matched by its exact name, before the
    // family split, so it is not read as a family-prefixed `pow` (there is no
    // such spelling) -- the plain call is its own shape because its failure is a
    // *panic*, not a value, exactly like `abs`.
    if short == "pow" {
        return Some(Intrinsic::PowPanic);
    }
    if short == "reverse_bits" {
        return Some(Intrinsic::BitReverse);
    }
    if short == "swap_bytes" {
        return Some(Intrinsic::ByteSwap);
    }
    if let Some(kind) = byte_order_kind(short) {
        return Some(Intrinsic::ByteOrder(kind));
    }
    if let Some(kind) = ascii_case_kind(short) {
        return Some(Intrinsic::AsciiCase(kind));
    }
    let (family, op) = if let Some(rest) = short.strip_prefix("wrapping_") {
        (Family::Wrapping, rest)
    } else if let Some(rest) = short.strip_prefix("saturating_") {
        (Family::Saturating, rest)
    } else if let Some(rest) = short.strip_prefix("overflowing_") {
        (Family::Overflowing, rest)
    } else {
        (Family::Checked, short.strip_prefix("checked_")?)
    };
    // `neg` and `abs` are unary, so they are their own shape rather than a
    // `BinOp`. Everything else in the families is a two-operand operator.
    match op {
        "neg" => return Some(Intrinsic::Unary(family, UnOp::Neg)),
        "abs" => return Some(Intrinsic::Unary(family, UnOp::Abs)),
        // The mixed-signedness additions: their two operands have opposite
        // signedness, so they are their own shape rather than a `BinOp`. The
        // whole suffix is matched, so `add_signed_thing` is refused rather than
        // read as `add_signed`.
        "add_signed" | "add_unsigned" => return Some(Intrinsic::MixedAdd(family)),
        // `pow` is a fold over the exponent's bits rather than one operator, so
        // it is its own shape too. It is matched here rather than falling into
        // the operator table below, which has no `pow` entry and would refuse it.
        "pow" => return Some(Intrinsic::Pow(family)),
        _ => {}
    }
    let op = match op {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        "and" => BinOp::BitAnd,
        "or" => BinOp::BitOr,
        "xor" => BinOp::BitXor,
        // Only `checked_div`/`checked_rem` are total; the others panic on a zero
        // divisor and are refused by `is_modelled`.
        "div" => BinOp::Div,
        "rem" => BinOp::Rem,
        _ => return None,
    };
    Some(match family {
        Family::Wrapping => Intrinsic::Wrapping(op),
        Family::Saturating => Intrinsic::Saturating(op),
        Family::Checked => Intrinsic::Checked(op),
        Family::Overflowing => Intrinsic::Overflowing(op),
    })
}

/// Whether a `min`/`max` name is `Ord`'s, and `Ord`'s alone.
///
/// The dump spells a trait call `<u8 as Ord>::min`, naming the trait between the
/// `as` and the `>`; a module-qualified trait spells `<u8 as m::Ord>::min`. The
/// trait path rustc prints for the prelude's own `Ord` is not always the bare
/// name: with `std` in scope a call is `<i8 as std::cmp::Ord>::max`, and against
/// `core` it is `<u8 as Ord>::min`. Both spellings are accepted, and so is
/// `core::cmp::Ord`.
///
/// The accepted set is exactly the standard library's `Ord` and nothing else, and
/// that is what makes the match sound: `std::cmp::Ord` and `core::cmp::Ord` cannot
/// name a user item, because a user cannot define items inside `std` or `core`. A
/// local trait is always qualified with *its own* module (`m::Ord`, `ord_shim::Ord`),
/// so it is refused. This is the narrow half of the guard in `try_intrinsic`: it
/// keeps the model from claiming a name that could be a local trait's, and the
/// caller's same-dump lookup is what answers the one spelling that could still
/// collide (a crate-root `Ord`, which the prelude also names `Ord`).
pub fn names_ord_trait(name: &str) -> bool {
    matches!(trait_path(name), Some("Ord" | "core::cmp::Ord" | "std::cmp::Ord"))
}

/// Whether a `branch` name is `Try`'s, and the standard library's alone.
///
/// The `?` desugaring spells the call `<Result<u8, u8> as Try>::branch` (or the
/// `std::ops::Try` spelling), naming the trait. A local trait in a module prints
/// `m::Try`, which is refused, and a crate-root `Try` -- which prints bare -- is
/// closed by the caller's same-dump lookup, exactly as for `Ord`. A user cannot
/// define items inside `core`/`std`, so the qualified set cannot name a local
/// item.
pub fn names_try(name: &str) -> bool {
    matches!(trait_path(name), Some("Try" | "core::ops::Try" | "std::ops::Try"))
}

/// Whether a `from_residual` name is `FromResidual`'s, and the standard library's
/// alone. The `Try` twin of [`names_try`]: the desugaring spells the call
/// `<Result<u8, u8> as FromResidual<Result<!, u8>>>::from_residual`.
pub fn names_from_residual(name: &str) -> bool {
    matches!(
        trait_path(name),
        Some("FromResidual" | "core::ops::FromResidual" | "std::ops::FromResidual")
    )
}

/// True when a call names an inherent method on a *slice* `[T]`.
///
/// `len` and `is_empty` are spelled the same on `Vec`, `String`, `str` and many
/// user types, and the model only knows the length of a `&[T]` the frontend
/// bound. The path is the only thing that separates them, so it is checked: the
/// dump prints a slice method as `core::slice::<impl [T]>::len`. A `Vec::len`
/// (`alloc::vec::Vec<T>::len` or `Vec::<u8>::len`) has no `slice::<impl [`, so it
/// is refused and stays unmodelled rather than answered with a slice length it
/// does not have.
pub fn names_slice_impl(name: &str) -> bool {
    name.contains("slice::<impl [")
}

/// True when a call names an inherent method on the standard library's `Option`.
///
/// `unwrap`, `unwrap_or`, `is_some` and `is_none` are spelled the same on a user
/// type that happens to be called `Option`, so the *path* is checked: rustc prints
/// an `Option` method as `core::option::Option::<u32>::unwrap` (or the
/// `std::option::…` spelling), naming the `option` module. A same-dump body is
/// always consulted first (the executor resolves it before the model), so this
/// predicate only has to keep the model from answering a *different* type's
/// method: a user `enum Option` in a local module is `m::Option::<u32>::unwrap`,
/// which has no `option::` segment, and is refused. The standard library's
/// `Option` is the only thing rustc prints with `option::Option`, because a user
/// cannot define items inside `core`/`std`.
pub fn names_option_impl(name: &str) -> bool {
    name.contains("option::Option") || name.starts_with("Option::")
}

/// Whether a name is a `Result` method call, and the standard library's alone.
///
/// The `Result` twin of [`names_option_impl`]: rustc prints the call as
/// `core::result::Result::<u8, u16>::is_ok` (or the `std::result::…` spelling),
/// naming the `result` module. A user `enum Result` in a local module is
/// `m::Result::<…>::is_ok`, which has no `result::` segment and is refused; a
/// same-dump body is answered by the executor before the model either way.
pub fn names_result_impl(name: &str) -> bool {
    name.contains("result::Result") || name.starts_with("Result::")
}

/// Whether a name is a `for`-loop range method, and the standard library's alone.
///
/// The desugaring spells the calls as `std::ops::RangeInclusive::<u32>::new`,
/// `<std::ops::RangeInclusive<u32> as IntoIterator>::into_iter` and
/// `<std::ops::RangeInclusive<u32> as Iterator>::next`, so the *type* segment is
/// `ops::RangeInclusive`/`ops::Range` (or the `core::ops` spelling). rustc 1.85 (the
/// MSRV) prints the same projection with the type *unqualified* -- `<RangeInclusive<u32>
/// as IntoIterator>::into_iter` -- which is also accepted, because an unqualified
/// `Range`/`RangeInclusive` is a name a user type can carry and the two spellings are
/// otherwise identical. A user type spelled `RangeInclusive` in a local module is
/// `m::RangeInclusive::<…>::new`, which has no `ops::` segment and is refused.
///
/// Because the unqualified spelling is one a user type can carry, the two `Iterator`
/// methods are additionally matched on the *trait* ([`names_std_range_trait`]): a user
/// `struct Range<T>` with a custom `into_iter` (`<Range<u8> as a::Custom>::into_iter`)
/// is refused rather than answered with the model's identity semantics, which would be
/// a false proof of a call the compiler resolved to the user's own method.
///
/// `Range::new` is the *exclusive* range's constructor; `Range` itself has no `next`
/// (only `RangeInclusive` does), but the desugaring never calls one, so the shared
/// `new` spelling is enough.
pub fn names_range(name: &str) -> bool {
    // The type segment, followed by a segment boundary, so `RangeFrom`/`RangeTo` --
    // which are not `Iterator`s and so never drive a `for` loop -- are not matched.
    // A path printed with generics puts a `<`, `>` or `::` right after the type
    // segment; a bare `Range::new` starts with the type name.
    let has_type = |seg: &str| {
        name.match_indices(seg).any(|(i, _)| {
            matches!(name[i + seg.len()..].chars().next(), None | Some(':') | Some('<') | Some('>'))
        })
    };
    let is_range = has_type("ops::RangeInclusive")
        || has_type("ops::Range")
        || name.starts_with("RangeInclusive::")
        || name.starts_with("Range::")
        // rustc 1.85 (the MSRV) prints the `as`-projection form with the type
        // *unqualified* -- `<RangeInclusive<u32> as IntoIterator>::into_iter`,
        // `<Range<u32> as Iterator>::next` -- where current stable qualifies it
        // (`<std::ops::RangeInclusive<u32> as …>`).
        || name.starts_with("<RangeInclusive<")
        || name.starts_with("<Range<");
    if !is_range {
        return false;
    }
    // The type name alone is not enough, because an *unqualified* `Range`/`RangeInclusive`
    // is a name a user type can carry, and rustc 1.85 prints the standard library's
    // projection unqualified. So the two `Iterator` methods are matched on the
    // *trait* as well as the type: `into_iter` only when the projection names the
    // standard library's `IntoIterator`, `next` only for `Iterator`. A user
    // `struct Range<T>` with a custom `into_iter` (`<Range<u8> as a::Custom>::into_iter`)
    // is therefore refused -- answering it with the range model's identity semantics
    // would be a false proof of a call the compiler resolved to the user's method.
    // `new` is inherent on the range type (it carries no trait), so it is matched on
    // the type alone; a user's inherent `new` has a body, and the same-dump lookup
    // answers it before the model is ever consulted.
    match name.rsplit("::").next() {
        Some("new") => true,
        Some("into_iter") => names_std_range_trait(name, "IntoIterator"),
        Some("next") => names_std_range_trait(name, "Iterator"),
        _ => false,
    }
}

/// Whether an `as`-projection names the standard library's `IntoIterator`/`Iterator`.
///
/// `<RangeInclusive<u32> as IntoIterator>::into_iter` and
/// `<std::ops::Range<u32> as Iterator>::next` carry the trait between ` as ` and the
/// `>` that closes the projection. The trait must be the bare standard-library name
/// (`IntoIterator`/`Iterator`), never a module-qualified one: `<Range<u8> as
/// a::Custom>::into_iter` and `<Range<u8> as m::IntoIterator>::into_iter` are both
/// refused, so a user type named `Range` cannot be answered by the range model. A
/// *crate-root* user trait named `IntoIterator` prints bare too; the caller's
/// declared-trait guard ([`crate::mir::exec`]'s `try_intrinsic`) refuses that case,
/// and a same-dump body always wins the lookup first.
fn names_std_range_trait(name: &str, want: &str) -> bool {
    let Some(after) = name.rsplit_once(" as ").map(|(_, a)| a) else {
        return false;
    };
    after.starts_with(&format!("{want}>")) || after.starts_with(&format!("{want}<"))
}

/// Whether a `from`/`into` name is `core`'s own `From`/`Into`, and theirs alone.
///
/// The dump spells the call `<u16 as From<u8>>::from` or `<u8 as Into<u16>>::into`,
/// so the trait is named between `as` and the `<` that opens its type parameter.
/// `core::convert::From` and `std::convert::From` are the same trait as the
/// prelude's `From`; rustc prints the bare name, but a program with a local trait
/// also called `From` in scope makes it print the qualified one to disambiguate
/// (the corpus does exactly this), so all three spellings are accepted.
///
/// The accepted set is exactly the standard library's `From` and `Into`: those
/// cannot name a user item, because a user cannot define items inside `core` or
/// `std`. A local trait is qualified with its own module (`m::From`), so it is
/// refused. The one spelling that can still collide is a *crate-root* trait named
/// `From`, which the dump also prints as the bare `From` -- the caller's same-dump
/// lookup is what answers that, and this predicate deliberately does not try to
/// tell it apart by name, because it cannot. See [`Intrinsic::Conversion`].
pub fn names_conversion_trait(name: &str) -> bool {
    matches!(
        trait_path(name),
        Some(
            "From"
                | "core::convert::From"
                | "std::convert::From"
                | "Into"
                | "core::convert::Into"
                | "std::convert::Into"
        )
    )
}

/// The trait a method call names, read out of a rustc-printed path.
///
/// A call is `<SELF as TRAIT<…>>::method`, so the trait is between the last ` as `
/// and the `<` that opens the trait's own type parameters. A name with no ` as `
/// is not a trait call at all -- a free function or an inherent method -- so it
/// names no trait here. A trait with no type parameters has no `<`, and is not one
/// of the shapes this reads, so it yields `None` rather than a truncated guess.
fn trait_path(name: &str) -> Option<&str> {
    let after_as = name.rsplit_once(" as ")?.1;
    // Cut the method off first (`From<i8>>::from` -> `From<i8>`), then drop the
    // trait's type parameters (`From<i8>` -> `From`). Doing it the other way round
    // would consume the `>::` that delimits the method.
    let (trait_ty, _) = after_as.split_once(">::")?;
    Some(trait_ty.split_once('<').map(|(t, _)| t).unwrap_or(trait_ty))
}

/// Whether the model has a definition for this operation at this width.
///
/// `w` is the *operand* width, not the return type's: `checked_add` on a `u8`
/// returns `Option<u8>` but overflows at 8 bits. `signed` decides what overflow
/// means, where the saturating bounds sit, and -- for the unary shapes -- whether
/// the method exists at all.
pub fn is_modelled(op: Intrinsic, w: u8, signed: bool) -> bool {
    if w == 0 || w > 64 {
        return false;
    }
    match op {
        // A bit count is a sum over the operand's bits, so it is exact at any
        // width the engine holds. Its *result* is wider than its operand, and
        // the model builds it at the operand's width and zero-extends.
        Intrinsic::Bits(_) => true,
        // A `bool` predicate. `is_power_of_two` exists only on the *unsigned*
        // types, so a signed operand is either a dump of something that is not
        // this method or a reading the model must not guess at: the signed
        // reading would accept `MIN` (its bits are a power of two but its value
        // is negative) and the model has no way to tell the two apart once it
        // has only the sign flag. It is total, so the only question is the width,
        // which is already bounded above.
        //
        // The ASCII classes are stricter still: they exist only on `u8`, so the
        // operand must be eight bits *and* unsigned. A wider or signed operand is
        // a different method (or not a method), and modelling it as the byte test
        // would answer a call `core` has no definition for.
        Intrinsic::Bool(BoolKind::Ascii(_)) => !signed && w == 8,
        Intrinsic::Bool(BoolKind::PowerOfTwo) => !signed,
        // `is_negative`/`is_positive` exist only on the *signed* types, so an
        // unsigned receiver is a different method (or not one), and reading the
        // top bit as a sign would answer a call `core` has no definition for.
        Intrinsic::Bool(BoolKind::Negative | BoolKind::Positive) => signed,
        // `is_multiple_of` exists only on the *unsigned* types (`i32::is_multiple_of`
        // does not exist on this toolchain), so a signed receiver is refused. It is
        // total -- `is_multiple_of(0)` is defined -- so the only question is the
        // width, already bounded above.
        Intrinsic::Bool(BoolKind::MultipleOf) => !signed,
        // The slice length, emptiness and element access. All read the executor's
        // own stores (the length variable, the element variable), so none reads the
        // operand width or sign -- they are answered from the executor's state, and
        // `eval` never sees them. Total here so that an `is_modelled` probe does not
        // report them unmodelled; the executor is what refuses a receiver whose
        // length (or index) it does not hold.
        Intrinsic::SliceLen
        | Intrinsic::SliceIsEmpty
        | Intrinsic::SliceFirst
        | Intrinsic::SliceGet => true,
        // The `Option` methods. They read the receiver's tag and payload, which
        // live in the executor's stores rather than in an operand term, so there is
        // no width or sign to check here -- `eval` never sees them and the
        // executor answers them from the stores (or refuses a receiver whose
        // `Option` state it does not hold). Total here so a probe does not report
        // them unmodelled.
        Intrinsic::OptionMethod(_) => true,
        // The `for`-loop range methods. Like the `Option` methods they read the
        // receiver's struct fields -- which live in the executor's store rather
        // than in an operand term -- so there is no width or sign to check here;
        // `eval` never sees them and the executor answers them from the fields (or
        // refuses a receiver whose range state it does not hold).
        Intrinsic::Range(_) => true,
        // The `?` operator's two calls. Like the `Option` methods they read the
        // receiver's enum state (or, for `from_residual`, the residual argument's)
        // rather than a bit-vector operand, so there is no width or sign to check
        // here; `eval` never sees them and the executor answers them from the
        // stores (or refuses a receiver whose enum state it does not hold).
        Intrinsic::TryBranch | Intrinsic::FromResidual => true,
        // `abs_diff` computes at one bit of headroom, so it needs a width below the
        // engine's 64. It exists on both signednesses -- on an unsigned type it is
        // a plain magnitude -- so there is no membership fact to check.
        Intrinsic::AbsDiff => (1..64).contains(&w),
        // The rotations exist on both signednesses and are total. The width must
        // be a *power of two*: the amount is reduced with the low `log2(w)` bits
        // (one `and`, no divider), which is exactly `n mod w` only when `w` is a
        // power of two. At `w == 12` the reduction is modulo 4, so
        // `rotate_left(1, 4)` would model as `1` where Rust gives `16`. Every real
        // integer type is a power-of-two width, so this costs no coverage; a
        // non-power-of-two width is refused rather than answered with the wrong
        // rotation.
        Intrinsic::Rotate(_) => (1..=64).contains(&w) && w.is_power_of_two(),
        // `signum` exists only on the *signed* types, so an unsigned receiver is
        // not this method. Total.
        Intrinsic::Signum => signed,
        // The Euclidean pair exist only on the *signed* types (the unsigned
        // spelling is the plain `/` and `%`), and their value is built from the
        // signed divider, so the width is bounded like `checked_div`'s. The panics
        // (a zero divisor, `MIN / -1`) are the plain `/` obligations the executor
        // already emits from the operands, not part of the value.
        Intrinsic::DivEuclid | Intrinsic::RemEuclid => signed && w <= DIV_MAX_WIDTH,
        // `div_ceil` is a *total* method on the unsigned types; the signed one is
        // unstable, so a signed receiver is refused. Bounded like a division.
        Intrinsic::DivCeil => !signed && w <= DIV_MAX_WIDTH,
        // `midpoint` exists on both signednesses and is total -- the whole point
        // of the method is that it does not overflow. Its value is built without a
        // sum at the operand width, so it needs no headroom and is modelled at any
        // width the engine holds.
        Intrinsic::Midpoint => true,
        // `next_multiple_of` is modelled on the *unsigned* types only: the signed
        // spelling is unstable on this toolchain, so a signed receiver is refused
        // rather than read. Its value is `a + (b - a % b) % b`, which needs no
        // headroom to *build* -- the overflow it may cause is the panic the
        // executor reports, not a value the model must represent -- but it does use
        // the unsigned divider, so it is bounded like a division.
        Intrinsic::NextMultipleOf => !signed && w <= DIV_MAX_WIDTH,
        // The `checked_` spelling has the same domain as the plain one.
        Intrinsic::CheckedNextMultipleOf => !signed && w <= DIV_MAX_WIDTH,
        // `ilog2`/`ilog10`. Both exist on both signednesses, and both panic on a
        // non-positive argument, which the executor reports. The value is built at
        // the operand width and zero-extended, so any width the engine holds is
        // fine.
        Intrinsic::Ilog(_) => true,
        // The `checked_` logarithms have the same domain as the plain ones.
        Intrinsic::CheckedIlog(_) => true,
        // `next_power_of_two`/`checked_next_power_of_two` are unsigned-only (the
        // signed types have no such method) and build no divider, so any width the
        // engine holds is fine.
        Intrinsic::NextPowerOfTwo | Intrinsic::CheckedNextPowerOfTwo => !signed,
        // The byte permutations and orderings are pure bit/byte moves, so they
        // exist on both signednesses and are total at any width the engine holds.
        Intrinsic::BitReverse | Intrinsic::ByteSwap | Intrinsic::ByteOrder(_) => true,
        // The ASCII case is `u8`-only, like the ASCII class tests: a wider or
        // signed operand is a different method (or not one).
        Intrinsic::AsciiCase(_) => !signed && w == 8,
        // The unary operators. Two membership facts decide whether a call can be
        // modelled at all, and both are about the *type*, not the width:
        //
        // * `abs` exists only on the signed types. `u8::wrapping_abs` is not a
        //   method, so a dump that calls it is either signed or not a real dump.
        // * `saturating_neg` exists only on the signed types too, while
        //   `wrapping_neg`, `checked_neg` and `overflowing_neg` exist on both.
        //   On an unsigned type negation is modular, and the failure case is
        //   `x != 0` -- which is exactly what the model computes once it reads
        //   the sign, so unsigned `neg` is modelled rather than refused.
        Intrinsic::Unary(family, un) => match un {
            UnOp::Abs => signed,
            UnOp::Neg => !(family == Family::Saturating && !signed),
        },
        // The inherent `abs`. Like the families' `abs` it exists only on the
        // signed types, so a signed operand is the method's own meaning and an
        // unsigned one is not this method at all. Unlike them it *panics* at
        // `MIN`, which is the whole reason it is a separate shape: the failure is
        // an obligation, not a value.
        Intrinsic::Abs => signed,
        // `unsigned_abs` is signed-only too (it is the unsigned reading of a
        // signed value), but unlike `abs` it is *total*: the magnitude at `MIN`
        // fits the unsigned result, so there is no failure predicate.
        Intrinsic::UnsignedAbs => signed,
        // The signedness re-interpretation exists on both signednesses (it is the
        // cast *between* them) and is total at any width the engine holds. A sign
        // that could not be read is refused like every other sign-reading shape.
        Intrinsic::SignednessCast => true,
        // `Ord::clamp`. It has a value at every input, and the one panic
        // (`lo > hi`) is a failure predicate the executor discharges. Modelled on
        // both signednesses: the comparisons are the type's own, which the model
        // reads from the sign.
        Intrinsic::Clamp => true,
        // The two-operand families.
        Intrinsic::Wrapping(bin)
        | Intrinsic::Saturating(bin)
        | Intrinsic::Checked(bin)
        | Intrinsic::Overflowing(bin) => match bin {
            // Division is modelled only for the family that can express *both*
            // failures as a value. `checked_div` returns `None`, which covers a
            // zero divisor as well as `MIN / -1`. Nothing else does:
            // `overflowing_div` reports `MIN / -1` in its flag but still *panics*
            // on a zero divisor -- its flag is not the whole failure predicate --
            // and `wrapping_div`/`saturating_div` panic on zero outright.
            // Modelling any of them as total would hide that panic, so only
            // `checked_*` is admitted.
            BinOp::Div | BinOp::Rem => {
                matches!(op, Intrinsic::Checked(_)) && w <= DIV_MAX_WIDTH
            }
            // A product needs the widened exact result to test, and to clamp.
            BinOp::Mul => w <= MUL_MAX_WIDTH,
            BinOp::Add | BinOp::Sub | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => true,
            BinOp::Shl | BinOp::Shr | BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt
            | BinOp::Ge => false,
        },
        // `pow`. Unlike the families above it reads a `u32` exponent beside a
        // base of the method's own width, so it is its own shape. It is modelled
        // only where a *product* is, and then only up to its own tighter bound:
        // the fold's every step is a `mul_failure` query, so its cost is a large
        // multiple of one product's rather than the product's own. See
        // [`POW_MAX_WIDTH`] for the measurement behind the difference.
        //
        // All four families are modelled, and `pow` is not the division trap: its
        // failure is an overflow, and an overflow is a *value* in every family --
        // `wrapping` wraps, `saturating` clamps, `checked` returns `None` and
        // `overflowing` sets the flag. Nothing here can panic, so there is no
        // panic to hide. The plain `pow`, which panics on overflow, is its own
        // shape (`Intrinsic::PowPanic`) and is admitted below.
        Intrinsic::Pow(_) => w <= POW_MAX_WIDTH,
        // The inherent `pow`. Its value and failure are the same fold the families'
        // `pow` uses, so it is admitted at the same bound; the difference is only
        // that its failure is a panic obligation rather than a value.
        Intrinsic::PowPanic => w <= POW_MAX_WIDTH,
        // The mixed-signedness additions. The operand of the method's own type
        // has the method's sign, and the other operand's sign is what tells the
        // model which one it is reading; the method itself exists on *both*
        // signednesses for the opposite operand's sign -- `u8::add_signed` takes
        // an `i8`, `i8::add_unsigned` takes a `u8` -- so there is no membership
        // fact to check, only the width. Nothing here can panic, so all four
        // families are modelled.
        Intrinsic::MixedAdd(_) => true,
        // `Ord::min`/`Ord::max`. Total, and modelled on both signednesses: the
        // model reads the sign to pick the ordering, so a signed operand is not a
        // guess but the method's own meaning. There is no membership fact to
        // check -- `Ord` is implemented for every integer -- only the width,
        // which is already bounded above.
        Intrinsic::MinMax(_) => true,
        // A widening conversion. The *value* is a plain extension, so it is total
        // and can fail only at a width the engine cannot hold -- which the guard
        // above already refused. Whether the call is a real integer widening at
        // all is a question about its two *types*, not this one operand width, so
        // it is decided by the executor (see `conversion_types`), which refuses a
        // non-integer or narrowing call rather than reaching here.
        Intrinsic::Conversion(_) => true,
    }
}

/// The value a modelled call yields.
///
/// A mismatch -- a width the engine cannot hold, a shape with no definition --
/// returns `None`, and the caller reports the path as unknown rather than
/// guessing.
///
/// `w` is the operand width. `result_w` is the destination type's width, which
/// differs from `w` for the bit counts (`u8::count_ones` returns `u32`) and for a
/// widening conversion (whose destination is wider than its source); for every
/// other shape the two are equal, and the caller passes `w` for both. The
/// result term is built at `result_w` so that it has the width of the local it is
/// written to -- a term narrower than its local would make the next read of that
/// local ill-formed.
pub fn eval(op: Intrinsic, x: Var, y: Var, w: u8, signed: bool, result_w: u8) -> Option<Outcome> {
    if !is_modelled(op, w, signed) {
        return None;
    }
    // The slice shapes are answered from the length variable the *executor*
    // holds, not from an operand term, so `eval` has nothing to compute for them.
    // Routing them here rather than at a match arm keeps the two-operand `eval`
    // from ever being asked about a shape with no operands.
    if matches!(
        op,
        Intrinsic::SliceLen
            | Intrinsic::SliceIsEmpty
            | Intrinsic::SliceFirst
            | Intrinsic::SliceGet
    ) {
        return None;
    }
    // The `Option` methods read the receiver's tag and payload from the executor's
    // stores, not from an operand term, so `eval` has nothing to compute for them
    // either. The executor answers them (see `enum_method`).
    if matches!(op, Intrinsic::OptionMethod(_)) {
        return None;
    }
    // The `for`-loop range methods read the receiver's struct fields from the
    // executor's store, not from an operand term, so `eval` has nothing to compute
    // for them either. The executor answers them (see `range_method`).
    if matches!(op, Intrinsic::Range(_)) {
        return None;
    }
    // The `?` operator's two calls read the receiver's (or residual's) enum state
    // from the executor's stores, not from an operand term, so `eval` has nothing
    // to compute for them either. The executor answers them (see `try_branch` /
    // `from_residual`).
    if matches!(op, Intrinsic::TryBranch | Intrinsic::FromResidual) {
        return None;
    }
    Some(match op {
        // Answered by `eval_slice` from the executor's length variable; the early
        // return above keeps them from reaching here.
        Intrinsic::SliceLen
        | Intrinsic::SliceIsEmpty
        | Intrinsic::SliceFirst
        | Intrinsic::SliceGet => {
            unreachable!("slice shapes are answered from the executor's stores")
        }
        // Answered by the executor's `enum_method` from the discriminant/payload
        // stores; the early return above keeps them from reaching here.
        Intrinsic::OptionMethod(_) => {
            unreachable!("Option methods are answered from the tag and payload stores")
        }
        // Answered by the executor's `range_method` from the struct field store;
        // the early return above keeps them from reaching here.
        Intrinsic::Range(_) => {
            unreachable!("range methods are answered from the struct field store")
        }
        // Answered by the executor's `try_branch`/`from_residual` from the enum
        // stores; the early return above keeps them from reaching here.
        Intrinsic::TryBranch | Intrinsic::FromResidual => {
            unreachable!("the `?` operator's calls are answered from the enum stores")
        }
        // The bit counts, each built at the operand's width and widened to the
        // result type. A count cannot exceed the operand width, so `w` bits hold
        // it; zero-extending to `result_w` is the promotion Rust performs (`u8`
        // -> `u32`). Building it wide here would add terms the extension throws
        // away, and for the fixed-width reading where `w == result_w` it is a
        // no-op.
        Intrinsic::Bits(kind) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            Outcome::Value(smt::truncate(bit_count(kind, x), result_w))
        }
        // A `bool` predicate. The result *is* the predicate, so there is no
        // `result_w` to read: a `bool` is one bit and the destination local's
        // type says so. The executor writes it as a `Val::Bool`, which is what
        // the `if` that consumes it reads.
        Intrinsic::Bool(kind) => Outcome::Bool(bool_pred(kind, x, y)),
        Intrinsic::Unary(family, un) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = unary_failure(un, x, w, signed)?;
            let plain = unary_result(un, x, w);
            match family {
                // The wrapped value: `0 - x` for `neg`, `if x < 0 { 0 - x } else
                // { x }` for `abs`. For `abs` the `0 - x` wraps at `MIN`, where
                // the magnitude is unrepresentable, and that wrap *is* the
                // method's answer -- so no separate `MIN` case is needed, and
                // stating one would be a second definition that could drift.
                Family::Wrapping => Outcome::Value(smt::truncate(plain, result_w)),
                // The clamp. The bound is the sign of the *overflow*, which for
                // both unary operators is the sign `-x` cannot reach: a negative
                // `x` overflowing `neg` or `abs` clamps to `MAX`, and `MIN`
                // itself is the only `x` that overflows while being negative.
                Family::Saturating => {
                    let (_, hi) = bounds(w, signed)?;
                    Outcome::Value(smt::truncate(smt::ite(fails, hi, plain), result_w))
                }
                // The `Option`: the tag is `1` exactly where the operation is
                // defined, so the `switchInt` on it takes the `Some` arm on those
                // paths and the `None` arm on the rest. It is a term, not a
                // constant, and it is what lets the payload be recorded
                // unconditionally: rustc only reads the payload inside the `Some`
                // arm, where this tag is `1`.
                Family::Checked => Outcome::Option {
                    tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                    payload: smt::truncate(plain, result_w),
                },
                // The `(value, flag)` tuple. The flag is the *same* predicate the
                // other two families use, so they cannot disagree about what
                // "overflow" means.
                Family::Overflowing => {
                    Outcome::Tuple { value: smt::truncate(plain, result_w), overflowed: fails }
                }
            }
        }
        Intrinsic::Wrapping(bin) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let plain = plain_result(bin, x, y, signed)?;
            Outcome::Value(smt::truncate(plain, result_w))
        }
        Intrinsic::Saturating(bin) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let plain = plain_result(bin, x, y, signed)?;
            let bound = saturation_bound(bin, x, y, w, signed)?;
            let fails = failure(bin, x, y, w, signed)?;
            Outcome::Value(smt::truncate(smt::ite(fails, bound, plain), result_w))
        }
        Intrinsic::Checked(bin) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let plain = plain_result(bin, x, y, signed)?;
            let fails = failure(bin, x, y, w, signed)?;
            Outcome::Option {
                tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                payload: smt::truncate(plain, result_w),
            }
        }
        Intrinsic::Overflowing(bin) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let plain = plain_result(bin, x, y, signed)?;
            let fails = failure(bin, x, y, w, signed)?;
            Outcome::Tuple { value: smt::truncate(plain, result_w), overflowed: fails }
        }
        // `pow`. `y` is the *exponent*, a `u32` operand, and `w` is the base's
        // width -- which is why `result_w` is not guarded here: the base and the
        // result share the method's width, so a `result_w` other than `w` would be
        // a different shape, not a wider one.
        Intrinsic::Pow(family) => {
            if result_w != w {
                return None;
            }
            let (value, fails) = pow_fold(x, y, w, signed)?;
            match family {
                Family::Wrapping => Outcome::Value(value),
                Family::Saturating => {
                    // `pow`'s magnitude is non-decreasing in the base, so an
                    // overflow can only push the result past a bound, never back
                    // inside one. `pow(0, 0)` is `1` in every family, which is why
                    // the `0^0` corner is not a failure.
                    Outcome::Value(smt::ite(fails, saturation_end(x, y, w, signed)?, value))
                }
                Family::Checked => Outcome::Option {
                    tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                    payload: value,
                },
                Family::Overflowing => Outcome::Tuple { value, overflowed: fails },
            }
        }
        // The inherent `pow`: the same fold as the families' `pow`, but the
        // failure is a **panic** rather than a value, so it yields a
        // [`Outcome::ValueOrPanic`] (the same shape `abs` and `clamp` use).
        Intrinsic::PowPanic => {
            if result_w != w {
                return None;
            }
            let (value, fails) = pow_fold(x, y, w, signed)?;
            Outcome::ValueOrPanic { value, fails }
        }
        // The mixed-signedness additions. `y` is the addend, whose signedness is
        // the *opposite* of the method's own, and `signed` is the method's own --
        // so the direction is not carried in the shape, only read here.
        //
        // The value is one term in both directions, so only the failure and the
        // clamp depend on the direction. The clamp is where the two directions
        // genuinely differ: `u8::saturating_add_signed` clamps to the *addend's*
        // end (`MAX` for a non-negative addend, `0` for a negative one), while
        // `i8::saturating_add_unsigned` adds a non-negative count and can only run
        // off the top, so it clamps to `MAX`. Both are the addend's sign read the
        // right way round -- a non-negative addend can only take an unsigned self
        // past `MAX`, and a negative one only below `0`.
        Intrinsic::MixedAdd(family) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let plain = mixed_add_result(x, y);
            let fails = mixed_add_failure(x, y, w, signed)?;
            match family {
                Family::Wrapping => Outcome::Value(smt::truncate(plain, result_w)),
                Family::Saturating => {
                    // The high bound is the *self type's* maximum: `127` for the
                    // signed direction, `255` for the unsigned one. Taking the
                    // unsigned maximum for a signed self would clamp `i8` to
                    // `0xff`, which reads back as `-1`.
                    let (_, hi) = bounds(w, signed)?;
                    let bound = if signed {
                        // The self operand is signed and the addend unsigned, so
                        // the only way past the top is up.
                        hi
                    } else {
                        // The self operand is unsigned: a non-negative addend
                        // takes it above `MAX`, a negative one below `0`.
                        smt::ite(smt::negative(y), smt::word(0, w), hi)
                    };
                    Outcome::Value(smt::truncate(smt::ite(fails, bound, plain), result_w))
                }
                Family::Checked => Outcome::Option {
                    tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                    payload: smt::truncate(plain, result_w),
                },
                Family::Overflowing => {
                    Outcome::Tuple { value: smt::truncate(plain, result_w), overflowed: fails }
                }
            }
        }
        // `Ord::min`/`Ord::max`: the smaller or larger operand, by the type's own
        // ordering. Total, so the result is a plain value and no failure term is
        // built. The sign selects the ordering -- `sle`/`sge` on a signed type,
        // `ule`/`uge` on an unsigned one -- and that is the *only* thing the sign
        // changes here: on a signed type `i8::MIN` is below `0`, so a `ule` would
        // return the wrong operand for every negative pair, which is a wrong value
        // rather than a weaker proof.
        Intrinsic::MinMax(kind) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            Outcome::Value(smt::truncate(min_max_result(kind, x, y, signed), result_w))
        }
        // A widening (or same-width) conversion. The operand *is* the source, so
        // its width and signedness are `w` and `signed`, and the destination is
        // `result_w`. The value is the source extended by its own signedness -- the
        // same rule the executor's `as`-cast uses, so a conversion and a cast of one
        // shape build one term. A destination narrower than the source is refused: a
        // real integer `From` never narrows, so a narrowing call is not the method
        // this model knows, and truncating it would be a guess at a conversion
        // `core` never performs. A same-width destination is `core`'s reflexive
        // `impl<T> From<T> for T`, and the extension leaves the source unchanged.
        Intrinsic::Conversion(_) => {
            if result_w < w {
                return None;
            }
            Outcome::Value(convert_value(x, signed, result_w))
        }
        // The inherent `abs`. The value is the same `unary_result` the families'
        // `abs` uses, and the failure is the same `MIN` predicate `unary_failure`
        // computes for them -- so the four spellings cannot disagree about what
        // `abs` is. The difference is only in what the failure *means*: here it
        // is a panic the executor must discharge, not a value or a flag.
        Intrinsic::Abs => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = unary_failure(UnOp::Abs, x, w, signed)?;
            Outcome::ValueOrPanic { value: smt::truncate(unary_result(UnOp::Abs, x, w), result_w), fails }
        }
        // The inherent `unsigned_abs`. Its value is the *same* `unary_result` the
        // families' `abs` uses -- `0 - x` where the operand is negative, `x`
        // otherwise -- but read as an unsigned value with no failure: the
        // truncating subtraction is exactly the magnitude even at `MIN` (where the
        // signed `abs` is the value that does not fit). It is a plain value, so the
        // executor labels the result unsigned.
        Intrinsic::UnsignedAbs => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            Outcome::Value(smt::truncate(unary_result(UnOp::Abs, x, w), result_w))
        }
        // The same-width signedness re-interpretation: the value is the operand
        // unchanged, and only the *result type* differs -- which the executor
        // reads from the call's destination type, not from this term. So the model
        // returns the operand at the destination width (a same-width cast is the
        // identity; `result_w == w` for every real call).
        Intrinsic::SignednessCast => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            Outcome::Value(smt::truncate(x, result_w))
        }
        // `abs_diff`: `|x - y|`, computed at one bit of headroom so the
        // subtraction cannot wrap, then narrowed back. The result is the *unsigned*
        // magnitude -- `i8::abs_diff(-128, 127)` is `255` -- so it is written as an
        // unsigned value whatever the operands' sign.
        Intrinsic::AbsDiff => {
            if w == 0 || w > 63 {
                return None;
            }
            // Both operands widen by their *own* sign to `w + 1` bits, which holds
            // the true difference: an unsigned `[0, 2^w)` and a signed
            // `[-2^(w-1), 2^(w-1))` both have a difference in `(-2^w, 2^w)`, and
            // that range is exactly a *signed* `w + 1`-bit value. So the sign test
            // is `slt` in both cases -- reading an unsigned difference as unsigned
            // would take the wrapped value for a negative one (`0 - 1` at eight
            // bits is `255`, not `-1`), which is the bug this comment prevents.
            let wide = w + 1;
            let diff = smt::sub(
                if signed { smt::sign_extend(x, wide) } else { smt::truncate(x, wide) },
                if signed { smt::sign_extend(y, wide) } else { smt::truncate(y, wide) },
            );
            let mag = smt::ite(
                smt::slt(diff, smt::word(0, wide)),
                smt::sub(smt::word(0, wide), diff),
                diff,
            );
            Outcome::Value(smt::truncate(mag, w))
        }
        // A rotation by a `u32` amount. `core` reduces the amount modulo the width,
        // so the model does the same: the two directions are each a shift by the
        // amount OR its complement shifted the other way, and the amount is masked
        // to `log2(w)` bits so `rotate_left(x, w)` is `x` rather than a shift by the
        // full width. The rotation is total, so there is no failure predicate.
        Intrinsic::Rotate(kind) => {
            if w == 0 || w > 64 {
                return None;
            }
            Outcome::Value(rotate(x, y, w, kind))
        }
        // `signum`: `-1`, `0` or `1`. The two comparisons are the engine's signed
        // ones, so `MIN` is below zero; `-1` is the all-ones pattern at `w` bits.
        Intrinsic::Signum => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let zero = smt::word(0, w);
            let minus_one = smt::all_ones(w);
            let one = smt::word(1, w);
            let v = smt::ite(smt::slt(x, zero), minus_one, smt::ite(smt::sgt(x, zero), one, zero));
            Outcome::Value(smt::truncate(v, result_w))
        }
        // `div_euclid`: `q = a / b`, adjusted up when the remainder is negative.
        // The *value* is built from the signed divider; the panics (`b == 0`,
        // `MIN / -1`) are exactly the plain `/` failure predicate, so they are
        // reported the same way `abs`'s overflow is -- a reachable-failure
        // obligation -- rather than silently assumed away.
        Intrinsic::DivEuclid => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = failure(BinOp::Div, x, y, w, signed)?;
            Outcome::ValueOrPanic { value: smt::truncate(div_euclid_value(x, y, w), result_w), fails }
        }
        // `rem_euclid`: `r = a % b`, adjusted by `+ |b|` when negative. Same
        // totality note as `div_euclid`.
        Intrinsic::RemEuclid => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = failure(BinOp::Rem, x, y, w, signed)?;
            Outcome::ValueOrPanic { value: smt::truncate(rem_euclid_value(x, y, w), result_w), fails }
        }
        // `div_ceil`: `q = a / b` rounded up when the remainder is nonzero.
        // Unsigned-only, so the plain unsigned divider is exact and the only panic
        // is a zero divisor.
        Intrinsic::DivCeil => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = failure(BinOp::Div, x, y, w, signed)?;
            Outcome::ValueOrPanic { value: smt::truncate(div_ceil_value(x, y, w), result_w), fails }
        }
        // `midpoint`: `(a + b) / 2` rounded toward zero, without the overflow the
        // sum would have. Total -- the whole point of the method -- so a plain
        // value, built by [`midpoint`] without ever forming `a + b` at `w` bits.
        Intrinsic::Midpoint => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            Outcome::Value(smt::truncate(midpoint(x, y, w, signed), result_w))
        }
        // `next_multiple_of`: the smallest multiple of `b` that is `>= a`. The
        // value is `a + (b - a % b) % b`; the *failure* is a zero divisor or an
        // overflow, both reported as a reachable-panic obligation. `a % b` and the
        // adjustment are built at `w` bits, and the addition is the wrapped one --
        // the wrap is exactly the overflow the panic predicate reports, so the
        // value the model carries on the failing path is the wrapped sum, which is
        // never read on a live path.
        Intrinsic::NextMultipleOf => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = next_multiple_fails(x, y);
            Outcome::ValueOrPanic {
                value: smt::truncate(next_multiple_value(x, y), result_w),
                fails,
            }
        }
        // `checked_next_multiple_of`: the same value and the same failure
        // condition as the plain method, as an `Option`. The tag is a *term* --
        // `1` where the value fits, `0` where the plain call would panic -- so the
        // `switchInt` that consumes it takes the right arm on each path, exactly
        // as the other `checked_*` tags do. The tag is built at the *operand*
        // width, not `result_w`, because the two-operand call path passes `result_w
        // == w` but the tag's own width must follow the operand regardless.
        Intrinsic::CheckedNextMultipleOf => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = next_multiple_fails(x, y);
            Outcome::Option {
                tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                payload: smt::truncate(next_multiple_value(x, y), result_w),
            }
        }
        // `ilog2`/`ilog10`: the integer logarithm. The value is built at `w` bits
        // and zero-extended to `result_w` (the method returns a `u32`). Both panic
        // on a non-positive argument, so the outcome is a value-or-panic.
        Intrinsic::Ilog(kind) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = ilog_fails(x, signed);
            Outcome::ValueOrPanic { value: smt::truncate(ilog_value(kind, x, w), result_w), fails }
        }
        // `checked_ilog2`/`checked_ilog10`: the same value and the same failure
        // condition as the plain logarithm, as an `Option`. The tag is a *term*
        // -- `1` where the operand is positive, `0` where the plain call would
        // panic -- built at the *operand* width, exactly as the other `checked_*`
        // tags are. The payload is the `u32` index, zero-extended to `result_w`
        // like the plain form's value.
        Intrinsic::CheckedIlog(kind) => {
            if result_w == 0 || result_w > 64 {
                return None;
            }
            let fails = ilog_fails(x, signed);
            Outcome::Option {
                tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                payload: smt::truncate(ilog_value(kind, x, w), result_w),
            }
        }
        // `next_power_of_two`: the smallest power of two `>= x`. Unsigned-only. The
        // value is the smear-and-add, which is total at `w` bits; the failure is a
        // rounding that wrapped to `0`, and `x == 0` is excluded because there the
        // value legitimately *is* the wrapped-looking `1` (the add carried, but the
        // answer fits). The result is the operand's own width, so `result_w` must
        // equal `w`.
        Intrinsic::NextPowerOfTwo => {
            if result_w != w {
                return None;
            }
            Outcome::ValueOrPanic { value: next_power_of_two_value(x, w), fails: next_power_of_two_fails(x, w) }
        }
        // `checked_next_power_of_two`: the same value and the same condition, as an
        // `Option`. The tag is a *term* -- `1` where the value fits, `0` where it
        // does not -- so the `switchInt` that consumes it takes the right arm on
        // each path, exactly as `checked_*`'s tag does.
        Intrinsic::CheckedNextPowerOfTwo => {
            if result_w != w {
                return None;
            }
            let fails = next_power_of_two_fails(x, w);
            Outcome::Option {
                tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                payload: next_power_of_two_value(x, w),
            }
        }
        // The byte permutations and orderings: pure moves, so the result has the
        // operand's own width and sign. Each is its own total expression.
        Intrinsic::BitReverse => Outcome::Value(smt::truncate(bit_reverse(x), result_w)),
        Intrinsic::ByteSwap => Outcome::Value(smt::truncate(byte_swap(x, w), result_w)),
        Intrinsic::ByteOrder(kind) => {
            Outcome::Value(smt::truncate(byte_order_value(x, w, kind), result_w))
        }
        Intrinsic::AsciiCase(kind) => {
            Outcome::Value(smt::truncate(ascii_case_value(x, kind), result_w))
        }
        // `Ord::clamp` is three-operand and is evaluated by [`clamp`] rather than
        // here, because `eval` reads exactly two operands. Reaching this arm means
        // a caller used `eval` for a shape it does not serve.
        Intrinsic::Clamp => return None,
    })
}

/// `x.rotate_left(n)` / `x.rotate_right(n)` at width `w`.
///
/// `n` is the amount as a term (a `u32` in the dump), read modulo `w` the way
/// `core` does: a rotation by the full width is the identity, and a rotation by
/// more than the width wraps. The amount is a symbolic barrel shift, so the two
/// half-shifts are `shift_var` calls rather than a loop over `w` cases; the
/// `and`/`or` combine them, and an amount of `0` leaves `x` unchanged.
pub fn rotate(x: Var, n: Var, w: u8, kind: RotateKind) -> Var {
    // `n` is a `u32` and `core` reduces it modulo `w`; `shift_var` saturates an
    // out-of-range amount to the defined out-of-range value (zero, or the sign
    // fill) rather than reducing it, so the *amount* is reduced here. A rotation
    // by the full width is the identity, and one by `w + k` is a rotation by `k`,
    // which is what a modulo does.
    //
    // `n % w` is the exact reduction, but `smt::urem` on a symbolic amount is a
    // divider -- the expensive circuit the engine already declines past a budget.
    // A modelled integer width is a power of two (`8/16/32/64`), so `n mod w` is
    // exactly the low `log2(w)` bits of `n`, which is one `and` and no divider.
    // That is the amount the two half-shifts use.
    let bits = (w as u32).trailing_zeros();
    let low_mask = if bits >= 32 { u32::MAX } else { (1u32 << bits) - 1 };
    let low = smt::band(n, smt::word(low_mask as u64, smt::bits(n)));
    match kind {
        // `(x << n) | (x >> (w - n))`, with the right shift logical so the bits
        // that wrap in are zeros, not the sign.
        RotateKind::Left => {
            let hi = smt::shift_var(smt::Shift::Left, x, low);
            let lo = smt::shift_var(smt::Shift::LogicalRight, x, smt::sub(smt::word(w as u64, smt::bits(n)), low));
            smt::bor(hi, lo)
        }
        // The mirror image: `(x >> n) | (x << (w - n))`.
        RotateKind::Right => {
            let lo = smt::shift_var(smt::Shift::LogicalRight, x, low);
            let hi = smt::shift_var(smt::Shift::Left, x, smt::sub(smt::word(w as u64, smt::bits(n)), low));
            smt::bor(lo, hi)
        }
    }
}

/// The value and panic condition of `Ord::clamp`: `x.clamp(lo, hi)`.
///
/// `core`'s body is one assert and the value: `assert!(lo <= hi)` (rustc's
/// "min > max" panic), then `if x < lo { lo } else if x > hi { hi } else { x }`.
/// The panic is therefore `lo > hi` and *only* that -- an `x` outside `[lo, hi]`
/// is the whole point of a clamp, not an error. (The first version of this model
/// treated an out-of-range `x` as a panic too, which made `clamp_builtin` in the
/// probe corpus `FAILED`; the corpus is what caught it.)
///
/// When `lo > hi` the clamp expression is still well-defined (it returns `lo`),
/// which is why the value needs no special case: a path where `lo > hi` is
/// already reported as a panic by the caller, so the value it carries is never
/// used on a live path.
///
/// The comparisons are the type's own, selected by `signed`, so a signed clamp
/// reads `i8::MIN` as below `0` -- an unsigned reading would return the wrong
/// operand for every negative pair, a wrong *value* rather than a weaker proof.
///
/// Returns `None` only for a width the engine cannot hold; the caller reports the
/// path as unknown rather than guessing.
pub fn clamp(x: Var, lo: Var, hi: Var, w: u8, signed: bool) -> Option<Outcome> {
    if !is_modelled(Intrinsic::Clamp, w, signed) {
        return None;
    }
    // `x > hi` is `hi < x`; there is no dedicated `ugt`, and writing the greater
    // comparison as the reversed lesser one keeps the sign selection in one place.
    let (below, above) = if signed {
        (smt::slt(x, lo), smt::slt(hi, x))
    } else {
        (smt::ult(x, lo), smt::ult(hi, x))
    };
    // The one panic: `assert!(lo <= hi)`, written as its negation.
    let too_high = if signed { smt::slt(hi, lo) } else { smt::ult(hi, lo) };
    let value = smt::ite(below, lo, smt::ite(above, hi, x));
    Some(Outcome::ValueOrPanic { value, fails: too_high })
}

/// The smaller or larger of two operands, under the type's ordering.
///
/// Both results are one ite over the same operands; only the comparison differs,
/// so the two cannot drift about which operand wins a tie (`min` returns the
/// first on `<=`, `max` the first on `>=`, and both are the value either way).
fn min_max_result(kind: MinMaxKind, x: Var, y: Var, signed: bool) -> Var {
    let take_x = match (kind, signed) {
        (MinMaxKind::Min, true) => smt::sle(x, y),
        (MinMaxKind::Min, false) => smt::ule(x, y),
        (MinMaxKind::Max, true) => smt::sge(x, y),
        (MinMaxKind::Max, false) => smt::ule(y, x),
    };
    smt::ite(take_x, x, y)
}

/// `iN::div_euclid`: the quotient `q` with `a == q*b + r` and `0 <= r < |b|`.
///
/// The Euclidean quotient is the truncating quotient `a / b` adjusted up by one
/// exactly when the truncating remainder is negative: `r = a % b; r >= 0 ? q :
/// (b > 0 ? q + 1 : q - 1)`. The adjustment is needed because the two operators
/// disagree about rounding direction only for a negative `a`, where the remainder
/// is negative.
///
/// The operands are read with the *signed* engine, which is the method's own
/// meaning (`div_euclid` is signed-only; see [`is_modelled`]). The panics (`b ==
/// 0`, `MIN / -1`) are not part of this value -- they are the plain `/` failure
/// predicate the caller reports separately.
fn div_euclid_value(x: Var, y: Var, w: u8) -> Var {
    let q = smt::sdiv(x, y);
    let r = smt::srem(x, y);
    let zero = smt::word(0, w);
    let one = smt::word(1, w);
    // A negative truncating remainder means `|b|` was added to `r`, and the
    // identity `a == q*b + r` then needs `q` moved the *other* way: `q - 1` for a
    // positive divisor, `q + 1` for a negative one. (`-128 div_euclid 3` is `-43`,
    // not `-41`: the truncating pair is `(-42, -2)`, and `-2 + 3 == 1` forces
    // `-43 * 3 + 1`.)
    let bump = smt::ite(smt::sgt(y, zero), smt::sub(q, one), smt::add(q, one));
    smt::ite(smt::slt(r, zero), bump, q)
}

/// `iN::rem_euclid`: the remainder `r` with `0 <= r < |b|`.
///
/// `r = a % b` adjusted by `+ |b|` when it is negative. `|b|` is `b` negated when
/// `b` is negative, which is the one place the sign of the *divisor* matters (the
/// remainder's own sign is what decides whether to adjust).
fn rem_euclid_value(x: Var, y: Var, w: u8) -> Var {
    let r = smt::srem(x, y);
    let zero = smt::word(0, w);
    let abs_y = smt::ite(smt::slt(y, zero), smt::sub(zero, y), y);
    smt::ite(smt::slt(r, zero), smt::add(r, abs_y), r)
}

/// `uN::div_ceil`: the quotient rounded toward positive infinity.
///
/// `q = a / b`, plus one when the remainder is nonzero. Unsigned-only, so the
/// plain unsigned divider is exact; the only panic is a zero divisor, reported
/// separately by the caller.
fn div_ceil_value(x: Var, y: Var, w: u8) -> Var {
    let q = smt::udiv(x, y);
    let r = smt::urem(x, y);
    let one = smt::word(1, w);
    smt::ite(smt::eq_const(r, 0), q, smt::add(q, one))
}

/// `iN::midpoint`: `(a + b) / 2`, rounded toward zero, without the overflow.
///
/// The method exists precisely so that `(a + b) / 2` does not overflow, so the
/// model must *not* form `a + b` at the operand width. The identity
/// `a + b == (a & b) * 2 + (a ^ b)` holds in unbounded arithmetic, so halving
/// gives `floor((a + b) / 2) == (a & b) + ((a ^ b) >> 1)` -- and that value always
/// fits in `w` bits (it is the true midpoint, which the method guarantees fits),
/// so the addition in the model cannot wrap either. The shift is arithmetic for a
/// signed operand, which is exactly `floor((a ^ b) / 2)` there.
///
/// `midpoint` truncates toward zero, and the floor and the truncation differ only
/// for a *negative odd* sum: the floor is then one below the truncation. Since
/// `a + b` and `a ^ b` have the same parity, the low bit of `a ^ b` is `1` exactly
/// when the sum is odd, so the correction is "add `(a ^ b) & 1` where the floor is
/// negative". The sign test is on the *floor* rather than on either operand, which
/// is the value the correction is applied to -- and `floor < 0` holds exactly when
/// `a + b < 0`, which is what makes the test the right one. An unsigned operand
/// never has a negative sum, so it takes no correction.
///
/// Both directions were checked exhaustively at `u8`/`i8` against `core`'s own
/// method in the unit tests below.
fn midpoint(x: Var, y: Var, w: u8, signed: bool) -> Var {
    let both = smt::band(x, y);
    let diff = smt::bxor(x, y);
    // The halving of `a ^ b` is a `>>` on the operand's own type: arithmetic when
    // signed (the top bit replicates, giving `floor` of a negative diff) and
    // logical when unsigned. The two are the same operation on a non-negative
    // value, which is why the unsigned case needs no sign care.
    let half = if signed { smt::ashr(diff, 1) } else { smt::lshr(diff, 1) };
    let floor = smt::add(both, half);
    if !signed {
        return floor;
    }
    let odd = smt::band(diff, smt::word(1, w));
    let correction = smt::ite(smt::slt(floor, smt::word(0, w)), odd, smt::word(0, w));
    smt::add(floor, correction)
}

/// `iN::next_multiple_of`: the smallest multiple of `b` that is `>= a`.
///
/// `a + (b - a % b) % b`. The inner `% b` matters: for `a % b == 0` the delta must
/// be `0`, not `b`, or the result would be the *next* multiple up. The addition is
/// the wrapping one; on the path where it overflows the value is never read (the
/// failure predicate is reported instead), so the wrap is not observable.
///
/// The result is unsigned (the method is modelled on the unsigned types only), so
/// the divider is the plain unsigned one.
fn next_multiple_value(x: Var, y: Var) -> Var {
    let r = smt::urem(x, y);
    let delta = smt::urem(smt::sub(y, r), y);
    smt::add(x, delta)
}

/// The failure predicate of `next_multiple_of`: a zero divisor, or an overflow of
/// the result.
///
/// The overflow is the same `Add` overflow the family predicates use -- the result
/// is `a + delta`, and `delta = (b - a % b) % b` -- so the flag is exact. A zero
/// divisor is a failure in its own right, which is why the predicate is
/// `b == 0 || add_overflows`. The two are a *disjunct*, not a guard: the delta term
/// is still built at `b == 0`, where `a % 0` is the engine's *defined* value rather
/// than a hole, but its value cannot change the answer because the `b == 0` disjunct
/// is already true there.
fn next_multiple_fails(x: Var, y: Var) -> Pred {
    let delta = smt::urem(smt::sub(y, smt::urem(x, y)), y);
    let sum = smt::add(x, delta);
    // `sum < x` is the unsigned-carry test: the wrapped sum is below an addend
    // exactly when the addition carried out of `w` bits. The same shape the
    // accumulator proof uses, and it needs no side condition.
    let overflow = smt::ult(sum, x);
    smt::or(smt::eq_const(y, 0), overflow)
}

/// `iN::ilog2`/`iN::ilog10`: the integer logarithm.
///
/// Both are built at the operand's width and the caller zero-extends to the
/// `u32` result. `ilog2` is `w - 1 - leading_zeros(x)`, which is the index of the
/// highest set bit; `ilog10` counts the `10^k` thresholds `x` reaches. The
/// argument is `x`'s *unsigned* reading for `ilog10` (`10^k <= x` is an unsigned
/// test even on a signed operand, because `core` panics on a negative argument
/// rather than comparing it). `ilog2` on a signed operand is the same: `core`
/// panics on a non-positive argument, so the operand is non-negative on the live
/// path and the unsigned bit index is the signed one.
fn ilog_value(kind: LogKind, x: Var, w: u8) -> Var {
    match kind {
        // The highest set bit index: `w - 1` minus the leading zeros. For `x == 0`
        // this is `-1` at `w` bits, but the failing path never reads it.
        LogKind::Ilog2 => {
            let lz = bit_count(BitKind::LeadingZeros, x);
            smt::sub(smt::word(u64::from(w) - 1, w), lz)
        }
        // The number of `10^k` thresholds `x` reaches: `sum_k [10^k <= x]`. The
        // thresholds are the powers of ten that fit `w` bits, taken from a table
        // rather than computed with a divider, so the model builds no circuit the
        // blaster has to hold. A value below `10` contributes nothing, which is
        // `ilog10(x) == 0`.
        LogKind::Ilog10 => {
            let one = smt::word(1, w);
            let mut acc = smt::word(0, w);
            for pow in POWERS_OF_TEN {
                if pow > max_of_width(w) {
                    break;
                }
                acc = smt::add(acc, smt::ite(smt::uge_const(x, pow), one, smt::word(0, w)));
            }
            acc
        }
    }
}

/// `10^1` through `10^19`, the powers of ten that fit in 64 bits.
///
/// A fixed table because every power the model can need is known up front: the
/// widest operand the engine holds is 64 bits and `10^19 < 2^64 < 10^20`, so no
/// operand can reach `10^20`.
const POWERS_OF_TEN: [u64; 19] = [
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
    10_000_000_000,
    100_000_000_000,
    1_000_000_000_000,
    10_000_000_000_000,
    100_000_000_000_000,
    1_000_000_000_000_000,
    10_000_000_000_000_000,
    100_000_000_000_000_000,
    1_000_000_000_000_000_000,
    10_000_000_000_000_000_000,
];

/// The largest value an unsigned `w`-bit word holds. `w >= 1`.
fn max_of_width(w: u8) -> u64 {
    if w >= 64 {
        u64::MAX
    } else {
        (1u64 << w) - 1
    }
}

/// The failure predicate of `ilog2`/`ilog10`: the argument is non-positive.
///
/// For an unsigned operand that is `x == 0`; for a signed one it is `x <= 0`,
/// which is `core`'s actual test ("argument of integer logarithm must be
/// positive"). The sign test is `sle(x, 0)` on a signed operand and `eq_const(x,
/// 0)` on an unsigned one, so a negative *signed* argument is a failure rather
/// than a huge positive index.
fn ilog_fails(x: Var, signed: bool) -> Pred {
    if signed {
        smt::sle(x, smt::word(0, smt::bits(x)))
    } else {
        smt::eq_const(x, 0)
    }
}

/// `iN::next_power_of_two`: the smallest power of two `>= x`, at `w` bits.
///
/// The classic smear-and-add, with the `- 1` that makes an *already*-power-of-two
/// input round to itself: subtract one, smear the highest set bit down into every
/// lower bit (`p |= p >> 1; p |= p >> 2; …`) so `p` becomes `2^k - 1`, and add one
/// to get `2^k`. Without the `- 1`, `128` would smear to `255` and round to `0`
/// instead of staying `128`.
///
/// `core` defines the pre-step as `x <= 1 => 0`, so the wrap of `x - 1` at `x == 0`
/// must be forced back to `0` -- otherwise `0.next_power_of_two` would smear the
/// all-ones `255` and give `0` where `core` gives `1`. The value is *total* at `w`
/// bits: when the true power of two does not fit (`x > 2^(w-1)`) the add wraps to
/// `0`, which is exactly the condition the failure predicate reports, so a live
/// path never reads it.
fn next_power_of_two_value(x: Var, w: u8) -> Var {
    let one = smt::word(1, w);
    // `p = x - 1`, with the `x <= 1` case forced to `0` (core's definition).
    let p = smt::ite(smt::ule_const(x, 1), smt::word(0, w), smt::sub(x, one));
    let mut acc = p;
    let mut shift = 1u32;
    while shift < u32::from(w) {
        acc = smt::bor(acc, smt::lshr(acc, shift));
        shift <<= 1;
    }
    smt::add(acc, one)
}

/// The failure predicate of `next_power_of_two`: the rounding does not fit `w` bits.
///
/// That is exactly "the rounded value came out `0`", because the smear-and-add
/// wraps to zero precisely when the true power of two is `2^w`. The one input
/// where the value is `0` without a wrap is `x == 0`, and there the value is `1`
/// (not `0`), so no extra guard is needed -- but the predicate is written as
/// `value == 0` on the *value* rather than on a bound, which is what makes it
/// exact at the boundary (`x == 2^(w-1)` fits and yields `2^(w-1)`, not `0`).
fn next_power_of_two_fails(x: Var, w: u8) -> Pred {
    smt::eq_const(next_power_of_two_value(x, w), 0)
}

/// `iN::reverse_bits`: the operand's bits in reversed order.
///
/// A shift-OR fold: bit `k` of the result is bit `w-1-k` of the operand, so the
/// result is the OR over `k` of `((x >> (w-1-k)) & 1) << k`. Written as the
/// *swaps* of a bit-reversal network it would be shorter, but the fold is the
/// direct statement of the definition, which is what makes it checkable against
/// `core`'s own method.
fn bit_reverse(x: Var) -> Var {
    let w = smt::bits(x);
    let mut acc = smt::word(0, w);
    for k in 0..w {
        let src = (w - 1 - k) as u32;
        let bit = smt::band(smt::lshr(x, src), smt::word(1, w));
        acc = smt::bor(acc, smt::shl(bit, k as u32));
    }
    acc
}

/// `iN::swap_bytes`: the operand's bytes in reversed order.
///
/// That is exactly a rotation by half the width in *bits* (`w/2 * 8`), because a
/// rotation moves each byte to the position the byte-swap would. A `u8` (one
/// byte) rotates by `4` bits, which is not the identity, so the rotation is only
/// taken when there is more than one byte; a single-byte type is unchanged.
fn byte_swap(x: Var, w: u8) -> Var {
    if w <= 8 {
        return x;
    }
    // Swapping the bytes of a `w`-bit value is a bit rotation by `w/2` bits: the
    // `w/8` bytes reverse, so each byte travels half the width. `rotate` takes the
    // amount as a term, and the amount is a constant here, so it is a word at the
    // operand's own width (a `u16` amount in an 8-bit field would be ill-formed).
    let half = smt::word(u64::from(w) / 2, w);
    // `rotate` reads the amount modulo the width; the amount is exact here, so
    // the low-bit reduction is the identity.
    rotate(x, half, w, RotateKind::Left)
}

/// `iN::to_be`/`to_le`/`to_ne`: a byte-order conversion.
///
/// `to_ne` is the identity. `to_be`/`to_le` depend on the *target's* endianness:
/// on a little-endian target `to_be` is a byte swap and `to_le` the identity, and
/// on a big-endian target the reverse. The endianness is read from the
/// compilation (`cfg!(target_endian = "big")`) rather than guessed, so the model
/// matches the target the MIR was produced for.
fn byte_order_value(x: Var, w: u8, kind: ByteOrderKind) -> Var {
    let big_endian = cfg!(target_endian = "big");
    let swap = match kind {
        ByteOrderKind::Be => !big_endian,
        ByteOrderKind::Le => big_endian,
    };
    if swap {
        byte_swap(x, w)
    } else {
        x
    }
}

/// `u8::to_ascii_uppercase`/`to_ascii_lowercase`.
///
/// `b'a'..=b'z'` becomes `b'A'..=b'Z'` by subtracting `32` (and the reverse by
/// adding it); every other byte is unchanged. The `ite` is over the method's own
/// range, so the boundaries cannot drift from `core`'s.
fn ascii_case_value(x: Var, kind: AsciiCaseKind) -> Var {
    let w = smt::bits(x);
    let (lo, hi, delta) = match kind {
        AsciiCaseKind::Upper => (b'a' as u64, b'z' as u64, -32i64),
        AsciiCaseKind::Lower => (b'A' as u64, b'Z' as u64, 32i64),
    };
    let in_range =
        smt::and(smt::ule_const(x, hi), smt::ule(smt::word(lo, w), x));
    let shifted = if delta < 0 {
        smt::sub(x, smt::word(delta.unsigned_abs(), w))
    } else {
        smt::add(x, smt::word(delta as u64, w))
    };
    smt::ite(in_range, shifted, x)
}

/// The wrapped result of a unary operator, before any family reads it.
///
/// Both operators share the `0 - x` core, and that is not a coincidence worth
/// hiding: `abs` *is* "negate if negative", so `neg` is the one expression the
/// other is built from. `wrapping_neg` at `MIN` therefore returns `MIN`, which
/// is what Rust does, and `wrapping_abs` at `MIN` returns `MIN` for the same
/// reason -- both are `0 - MIN` wrapping.
fn unary_result(un: UnOp, x: Var, w: u8) -> Var {
    match un {
        UnOp::Neg => smt::sub(smt::word(0, w), x),
        UnOp::Abs => smt::ite(smt::negative(x), smt::sub(smt::word(0, w), x), x),
    }
}

/// When a unary operator has no representable result.
///
/// For `neg` that is when `-x` leaves the range. On a *signed* type only `MIN`
/// is unrepresentable, because `-MIN` is one past `MAX`; on an *unsigned* type
/// the result must be `0` to be representable, so every `x != 0` fails. That
/// difference is the whole content of the function, and it is why the sign has
/// to be read from the type rather than assumed.
///
/// For `abs` the magnitude is what must fit, and it does not only at `MIN` on a
/// signed type -- which is also exactly where `abs` negates, so the same
/// predicate serves both operators once the sign is known.
fn unary_failure(un: UnOp, x: Var, w: u8, signed: bool) -> Option<Pred> {
    match un {
        // `abs` needs a sign bit to have a magnitude at all, so an unsigned call
        // is refused by `is_modelled` and never reaches here. Answering anyway
        // would be a guess about a method that does not exist.
        UnOp::Abs if !signed => None,
        UnOp::Abs | UnOp::Neg if !signed => Some(smt::not(smt::eq_const(x, 0))),
        UnOp::Abs => Some(smt::eq_const(x, min_value(w)?)),
        UnOp::Neg => Some(smt::eq_const(x, min_value(w)?)),
    }
}

/// The number of bits of the requested kind, as a term of the *operand's* width.
///
/// The three *positive* counts are built from the same primitive -- "is bit `k`
/// set" -- so they cannot disagree about which bit is which, and the three
/// *complement* counts are defined as the corresponding positive count of `!x`,
/// so there is one expression per pair rather than two that could drift.
fn bit_count(kind: BitKind, x: Var) -> Var {
    let w = smt::bits(x);
    let one = smt::word(1, w);
    let zero = smt::word(0, w);
    // `1` where bit `k` is set, `0` where it is not.
    let bit = |k: u8| smt::ite(smt::bit_set(x, u32::from(k)), one, zero);
    let mut acc = zero;
    match kind {
        // The set bits, summed.
        BitKind::Ones => {
            for k in 0..w {
                acc = smt::add(acc, bit(k));
            }
        }
        // The zero bits above the highest set bit. The `k`-th term is added only
        // while every bit above `k` is clear, which is `x < 2^k`. The sum runs
        // from `k == 0` and not from `k == 1`, and that is the whole subtlety:
        // `x < 2^0` is `x < 1`, which is `x == 0`, and a zero operand has *all*
        // `w` bits clear. Starting at `k == 1` omits that term and reports `w - 1`
        // for zero -- an off-by-one at exactly one input, which the exhaustive
        // walk against `core` is what caught.
        //
        // `k` runs to `w - 1`, so the host shift `1u64 << k` is at most `63` even
        // at `w == 64` and never overflows.
        BitKind::LeadingZeros => {
            for k in 0..w {
                acc = smt::add(acc, smt::ite(smt::ult_const(x, 1u64 << k), one, zero));
            }
        }
        // The zero bits below the lowest set bit: the `k`-th term is added while
        // the low `k` bits are all clear. Written as `x & (2^k - 1) == 0`, which
        // is one `and` and one compare per bit.
        //
        // The mask `2^k - 1` is built with a *host* shift, and `k` runs to `w`, so
        // at `w == 64` the last step would evaluate `1u64 << 64` -- which panics
        // under overflow checks and, without them, masks the shift amount to `0`
        // and yields an all-zero mask. An all-zero mask makes `x & mask == 0` true
        // for *every* operand, so the final term adds `1` unconditionally and
        // every `trailing_zeros`/`trailing_ones` at 64 bits is one too large --
        // `0u64.trailing_zeros()` would read `65`, not `64`. The last mask is
        // therefore `all_ones(w)`, which is the same low-bit mask without the
        // shift (`x & all_ones == x`, and `x == 0` iff all `w` low bits are clear).
        BitKind::TrailingZeros => {
            for k in 1..=w {
                let mask = if k == w {
                    smt::all_ones(w)
                } else {
                    smt::word((1u64 << k) - 1, w)
                };
                let low = smt::band(x, mask);
                acc = smt::add(acc, smt::ite(smt::eq_const(low, 0), one, zero));
            }
        }
        // The complements are *not* a second summation: each is `core`'s own
        // definition, the count of the bitwise complement. `count_zeros` is
        // `count_ones(!x)`, `leading_ones` is `leading_zeros(!x)` and
        // `trailing_ones` is `trailing_zeros(!x)`. Recursing keeps one expression
        // for each pair, so a fix to `leading_zeros` cannot leave `leading_ones`
        // behind. The recursion is one level deep -- `!x` is not a count.
        //
        // `!x` is spelled the way the executor spells it (`bxor` with `all_ones`),
        // not as a second complement primitive, so the model's `!x` is the *same
        // term* the body's `!x` produces rather than a definition that could drift
        // from it.
        BitKind::CountZeros => return bit_count(BitKind::Ones, not_bits(x)),
        BitKind::LeadingOnes => return bit_count(BitKind::LeadingZeros, not_bits(x)),
        BitKind::TrailingOnes => return bit_count(BitKind::TrailingZeros, not_bits(x)),
    }
    acc
}

/// `!x` at `x`'s own width.
///
/// The same term the executor builds for a `Not` rvalue, so a bit count of a
/// complement and a bit count of a written `!x` cannot disagree.
fn not_bits(x: Var) -> Var {
    let w = smt::bits(x);
    smt::bxor(x, smt::all_ones(w))
}

/// The ASCII class a method name denotes, for [`BoolKind::Ascii`].
///
/// The names are matched exactly -- not by prefix -- so `is_ascii_digit` cannot be
/// confused with `is_ascii_alphanumeric`, and a name this model does not know
/// returns `None` rather than the nearest class.
fn ascii_kind(short: &str) -> Option<AsciiKind> {
    Some(match short {
        "is_ascii_digit" => AsciiKind::Digit,
        "is_ascii_alphabetic" => AsciiKind::Alphabetic,
        "is_ascii_alphanumeric" => AsciiKind::Alphanumeric,
        "is_ascii_uppercase" => AsciiKind::Uppercase,
        "is_ascii_lowercase" => AsciiKind::Lowercase,
        "is_ascii_hexdigit" => AsciiKind::HexDigit,
        "is_ascii_whitespace" => AsciiKind::Whitespace,
        "is_ascii_punctuation" => AsciiKind::Punctuation,
        "is_ascii_control" => AsciiKind::Control,
        "is_ascii" => AsciiKind::Ascii,
        _ => return None,
    })
}

/// The byte-order method a name is, if any.
///
/// Only the *integer*-returning forms are matched: `to_be`, `to_le`, `from_be`
/// and `from_le`. Each is a byte permutation of the same width, and `from_be`/
/// `from_le` are the involutions of `to_be`/`to_le` -- a conversion from a byte
/// order on the same target endianness is the same swap -- so one model serves
/// both directions. The `_bytes` forms (`to_be_bytes`) return an *array*, not an
/// integer, so the model has no single word to produce for them; they are left
/// unclassified and stay unmodelled, which is the honest answer rather than
/// writing a word into an array local.
fn byte_order_kind(short: &str) -> Option<ByteOrderKind> {
    Some(match short {
        "to_be" | "from_be" => ByteOrderKind::Be,
        "to_le" | "from_le" => ByteOrderKind::Le,
        _ => return None,
    })
}

/// The ASCII case method a name is, if any.
fn ascii_case_kind(short: &str) -> Option<AsciiCaseKind> {
    Some(match short {
        "to_ascii_uppercase" => AsciiCaseKind::Upper,
        "to_ascii_lowercase" => AsciiCaseKind::Lower,
        _ => return None,
    })
}

/// The truth value of a `bool`-valued predicate.
///
/// `is_power_of_two` is `x != 0 && x & (x - 1) == 0`, which is the standard
/// trick: clearing the lowest set bit of a power of two leaves zero, and for
/// every other non-zero value it does not. `x != 0` is *not* redundant --
/// `0 & (0 - 1)` is `0 & all_ones`, which is `0`, so the mask test alone would
/// call zero a power of two. The mask test is spelled with the engine's own
/// `and`/`sub`/`eq_const`, so it is the same term a hand-written
/// `x & (x - 1) == 0` produces.
///
/// The ASCII classes are each `core`'s own range test, built from `ule`/`ult` on
/// the byte. `is_ascii` is the one that is a single comparison (`x < 128`); the
/// others are a disjunction of ranges, which is exactly how `core` writes them,
/// so the boundaries cannot drift from the standard library's.
fn bool_pred(kind: BoolKind, x: Var, y: Var) -> Pred {
    match kind {
        BoolKind::PowerOfTwo => {
            let w = smt::bits(x);
            let cleared = smt::band(x, smt::sub(x, smt::word(1, w)));
            smt::and(smt::not(smt::eq_const(x, 0)), smt::eq_const(cleared, 0))
        }
        BoolKind::Ascii(kind) => ascii_pred(kind, x),
        // `is_negative`/`is_positive` on a signed value: `x < 0` and `x > 0`. The
        // comparisons are the engine's *signed* ones, so `i8::MIN` (whose bits are
        // the largest unsigned byte) is below zero, which is what `core` means.
        // They exist only on the signed types -- see `is_modelled` -- so there is
        // no unsigned reading to fall back to.
        BoolKind::Negative => smt::slt(x, smt::word(0, smt::bits(x))),
        BoolKind::Positive => smt::sgt(x, smt::word(0, smt::bits(x))),
        // `is_multiple_of`: `a % b == 0`, with `b == 0` defined as `a == 0`.
        // `urem(x, 0)` is a *defined* value in the engine (the dividend), not a
        // hole, so the `b != 0` guard is what keeps `5.is_multiple_of(0)` from
        // reading as `5 % 0 == 0` (which would be `false` only by accident of that
        // defined value). The `|| x == 0` covers the `b == 0 && a == 0` case, which
        // `core` defines as `true`.
        BoolKind::MultipleOf => smt::or(
            smt::and(smt::not(smt::eq_const(y, 0)), smt::eq_const(smt::urem(x, y), 0)),
            smt::eq_const(x, 0),
        ),
    }
}

/// `core`'s range test for one ASCII class, on a `u8` operand.
///
/// Every comparison is unsigned -- a byte is a `u8` -- and the bounds are the
/// ASCII code points written as character literals, so the model is readable
/// against the standard library's definition. A range `lo..=hi` is
/// `ule(lo, x) && ule(x, hi)`; the multi-range classes are the disjunction of
/// their ranges, which is how `core` states them.
fn ascii_pred(kind: AsciiKind, x: Var) -> Pred {
    let in_range = |lo: u8, hi: u8| -> Pred {
        let w = smt::bits(x);
        let lo = smt::word(lo as u64, w);
        let hi = smt::word(hi as u64, w);
        smt::and(smt::ule(lo, x), smt::ule(x, hi))
    };
    match kind {
        AsciiKind::Digit => in_range(b'0', b'9'),
        AsciiKind::Uppercase => in_range(b'A', b'Z'),
        AsciiKind::Lowercase => in_range(b'a', b'z'),
        AsciiKind::Alphabetic => smt::or(in_range(b'A', b'Z'), in_range(b'a', b'z')),
        AsciiKind::Alphanumeric => smt::or(
            in_range(b'0', b'9'),
            smt::or(in_range(b'A', b'Z'), in_range(b'a', b'z')),
        ),
        AsciiKind::HexDigit => smt::or(
            in_range(b'0', b'9'),
            smt::or(in_range(b'A', b'F'), in_range(b'a', b'f')),
        ),
        // `core`'s list is space, tab, newline, form feed and carriage return --
        // not vertical tab (`0x0b`), which is why it is a disjunction of five
        // equalities rather than one range.
        AsciiKind::Whitespace => [0x20u64, 0x09, 0x0a, 0x0c, 0x0d]
            .into_iter()
            .map(|c| smt::eq_const(x, c))
            .reduce(smt::or)
            .unwrap_or_else(|| smt::truth(false)),
        // The printable non-alphanumeric, non-space ASCII: the four runs
        // `!` through `/`, `:` through `@`, `[` through backtick, and `{`
        // through `~`, which is how `core` states it.
        AsciiKind::Punctuation => smt::or(
            in_range(b'!', b'/'),
            smt::or(in_range(b':', b'@'), smt::or(in_range(b'[', b'`'), in_range(b'{', b'~'))),
        ),
        // The C0 controls and DEL: `0..=0x1f` or `0x7f`.
        AsciiKind::Control => smt::or(in_range(0, 0x1f), smt::eq_const(x, 0x7f)),
        AsciiKind::Ascii => {
            let w = smt::bits(x);
            smt::ult(x, smt::word(128, w))
        }
    }
}

/// The operation with the result taken modulo `2^w`.
///
/// For `+`, `-`, `*` and the bitwise ops this is MIR's plain operator, so the
/// term is the same one a hand-written `a + b` produces. Division and remainder
/// go through the engine's restoring divider, which is exact for a non-zero
/// divisor; the zero-divisor case is defined there too, and it is the failure
/// predicate that stops that value from ever being used as a result.
fn plain_result(op: BinOp, x: Var, y: Var, signed: bool) -> Option<Var> {
    Some(match op {
        BinOp::Add => smt::add(x, y),
        BinOp::Sub => smt::sub(x, y),
        BinOp::Mul => smt::mul(x, y),
        BinOp::BitAnd => smt::band(x, y),
        BinOp::BitOr => smt::bor(x, y),
        BinOp::BitXor => smt::bxor(x, y),
        // A signed operand needs the *signed* divider: the unsigned one returns
        // a huge positive quotient for `-7 / 2`, which is a wrong value and not
        // merely a weaker proof.
        BinOp::Div if signed => smt::sdiv(x, y),
        BinOp::Rem if signed => smt::srem(x, y),
        BinOp::Div => smt::udiv(x, y),
        BinOp::Rem => smt::urem(x, y),
        _ => return None,
    })
}

/// The condition under which the operation is not the plain result.
///
/// This is the predicate rustc's `assert` reads, which is what makes a
/// `saturating_*` and a hand-rolled overflow guard agree.
fn failure(op: BinOp, x: Var, y: Var, w: u8, signed: bool) -> Option<Pred> {
    Some(match op {
        // Unsigned addition wraps exactly when the sum is below `x` — the carry
        // out of the top bit, which the unsigned order tracks.
        //
        // Signed addition is a different condition, and getting it wrong is
        // unsound rather than merely weak: `-1 + 1` does not overflow but its sum
        // is below `127` read unsigned, so the unsigned test fires on it. The
        // sign rule has no such cases — the result is wrong exactly when the
        // operands agree in sign and the result disagrees with them.
        BinOp::Add if signed => {
            let sum = smt::add(x, y);
            smt::and(
                smt::iff(smt::negative(x), smt::negative(y)),
                smt::xor(smt::negative(x), smt::negative(sum)),
            )
        }
        BinOp::Add => smt::ult(smt::add(x, y), x),
        // Unsigned subtraction wraps exactly when `x < y` (the borrow).
        BinOp::Sub if signed => {
            let diff = smt::sub(x, y);
            smt::and(
                smt::xor(smt::negative(x), smt::negative(y)),
                smt::iff(smt::negative(y), smt::negative(diff)),
            )
        }
        BinOp::Sub => smt::ult(x, y),
        // A product wraps exactly when the exact result needs more than `w` bits.
        // The predicate is `mul_failure`'s, shared with `pow`, so a `saturating_mul`
        // and a `pow` step cannot disagree about what a product overflow is.
        BinOp::Mul => return mul_failure(x, y, w, signed),
        // Division and remainder fail on a zero divisor. The signed forms fail
        // on `MIN / -1` as well: the quotient is not representable, and
        // `checked_div` returns `None` there rather than wrapping.
        BinOp::Div | BinOp::Rem if signed => {
            let min = min_value(w)?;
            let zero_divisor = smt::eq_const(y, 0);
            let min_by_neg_one =
                smt::and(smt::eq_const(x, min), smt::eq_const(y, all_ones_value(w)));
            smt::or(zero_divisor, min_by_neg_one)
        }
        BinOp::Div | BinOp::Rem => smt::eq_const(y, 0),
        _ => return None,
    })
}

/// When a `w`-bit product has no representable result.
///
/// This is the `Mul` arm of [`failure`], lifted out because `pow` needs it for
/// every step of its fold: the two must agree on what a product overflow is, and
/// two copies of a widened multiply could drift. It is exact rather than
/// sufficient -- a too-weak predicate would make an overflowing function look
/// panic-free.
///
/// The exact result is built by widening: `truncate` zero-extends when the target
/// is wider, so the operands are widened to `2w` and multiplied exactly there.
/// Past `2w == 64` the widened multiply is the scaling wall this crate documents,
/// so the model declines and the caller reports the path unknown. The guard is the
/// *correctness* condition on the term this function builds -- a `2w`-bit product
/// the blaster cannot hold -- so it tracks [`MUL_MAX_WIDTH`]: every width that
/// bound admits (`w <= 32`, so `2w <= 64`) builds a predicate, and a `u64` product
/// (`2w == 128`, clamped to 64 and equal to `w`) is refused here.
fn mul_failure(x: Var, y: Var, w: u8, signed: bool) -> Option<Pred> {
    let wide = w.saturating_mul(2).min(64);
    if wide <= w || wide > 64 {
        return None;
    }
    Some(if signed {
        // The `2w`-bit product of two `w`-bit signed values always fits in `2w`
        // signed bits, so this multiply cannot itself wrap. The result is right
        // exactly when it equals the `w`-bit wrapped result sign-extended back to
        // `2w`; comparing a *zero*-extended result would fire on every negative
        // product.
        let exact = smt::mul(smt::sign_extend(x, wide), smt::sign_extend(y, wide));
        let want = smt::sign_extend(smt::mul(x, y), wide);
        smt::not(smt::eq(exact, want))
    } else {
        let exact = smt::mul(smt::truncate(x, wide), smt::truncate(y, wide));
        // 2^w, as a constant in the widened width.
        let limit = 1u64 << (w - 1);
        let limit = limit.saturating_mul(2);
        smt::uge_const(exact, limit)
    })
}

/// The wrapped value of a mixed-signedness addition.
///
/// The two operands have opposite signedness, but the value does not care: rustc
/// reinterprets the operand of the opposite signedness to the method's own type
/// and adds, which is a plain `w`-bit addition. So this is the *same term* the
/// body would build for `x.wrapping_add(r as _)`, and one expression serves both
/// directions.
fn mixed_add_result(x: Var, y: Var) -> Var {
    smt::add(x, y)
}

/// When a mixed-signedness addition has no representable result.
///
/// The model is the addition's top-bit carry adjusted by the *addend's* sign:
///
/// ```text
/// carry = overflow of x + y read at the method's own type
/// flag  = carry XOR sign_of_addend
/// ```
///
/// The carry is read at the method's own type -- the unsigned carry when that type
/// is unsigned, the signed overflow when it is signed -- which is exactly what
/// [`failure`] already computes for `Add`, so the mixed shapes reuse it rather than
/// stating a second carry rule that could drift from it. That is the `_3 = copy _2
/// as <self type>; AddWithOverflow(_1, _3)` rustc inlines: the addend is
/// reinterpreted to the self type and the addition's overflow is read there.
///
/// The adjustment is the whole subtlety, and getting it wrong is a wrong *flag*,
/// not a weaker proof. rustc inlines `flag = carry XOR (addend < 0)`, and the
/// addend's top bit is its sign in *either* reading, so the same term serves both
/// directions. Taking the bare carry as the flag is wrong in both directions. For
/// `u8::add_signed`, `250u8 + (-1i8)` is `249`, which is in range -- but the
/// addition carries, because `250 + 255` wraps to `249`, so the carry alone would
/// report an overflow that is not there. For `i8::add_unsigned`, `0i8 + 128u8` is
/// `-128`, which has run off the top -- but the addition does *not* carry, so the
/// carry alone would miss it. In each case the addend's sign is what corrects the
/// carry: a negative addend cancels a carry that is only a legitimate borrow, and
/// a top-bit-set unsigned addend (`128u8` read as `i8` is negative) is what makes
/// a carry-less addition an overflow. Both directions were walked over the whole
/// `u8`/`i8` domain (65536 pairs each) and this predicate matched `core` on every
/// one; the carry alone missed half of them.
fn mixed_add_failure(x: Var, y: Var, w: u8, signed: bool) -> Option<Pred> {
    let carry = failure(BinOp::Add, x, y, w, signed)?;
    // `y` is the addend -- the operand whose signedness is the opposite of the
    // method's own -- and it is its top bit that the carry is adjusted by.
    Some(smt::xor(carry, smt::negative(y)))
}

/// The wrapped value and the overflow flag of `base.pow(exp)`, by squaring.
///
/// `exp` is the *exponent* operand, a `u32`; `w` is the base's width. The fold is
/// the right-to-left binary exponentiation Rust itself performs, unrolled one step
/// per exponent bit rather than run as a loop, because the model is a term and not
/// a program:
///
/// ```text
/// result = 1; base = x
/// for k in 0..32:
///     result = if bit_k(exp) { result * base } else { result }
///     base   = if any bit above k of exp is set { base * base } else { base }
/// ```
///
/// Every step is a `w`-bit multiply, and the flag is the `or` of the *product*
/// overflow of the steps that actually ran. That is the whole subtlety: a squaring
/// the fold discards must not contribute its overflow, so both the value and the
/// flag are gated on the same condition. Ungating the flag made `pow` report an
/// overflow for a `2` that never had one -- and it is the same gate, not two that
/// could drift, because the value and the flag are read from the one step.
///
/// `result` and `base` start at `1` and `x`, so `exp == 0` yields `1` and no step
/// runs -- which is `pow(x, 0) == 1` for every `x`, `0` included.
///
/// The base has the operand's sign and the exponent does not: the exponent is a
/// `u32` count, and a signed reading of its bits would make `exp == 0x8000_0000`
/// a negative number and the fold a different function.
fn pow_fold(x: Var, exp: Var, w: u8, signed: bool) -> Option<(Var, Pred)> {
    // A constant exponent is the common case in a specification (`x.pow(3)`), and
    // it is also the case the general fold cannot carry: the 32-step fold below
    // builds a fan-out DAG whose *unrolled* size is exponential in the number of
    // steps, and the bit-blaster walks a DAG once per path to a shared node. That
    // is a hang, not a slow answer. A literal exponent is known before the fold
    // starts, so the steps that cannot run are skipped here rather than built and
    // then multiplied by a zero gate.
    //
    // The two paths must agree. The general fold computes `x^e` by binary
    // exponentiation over the exponent's bits, and the fast path is the same
    // recurrence with the bits read from a `u64` -- so a mismatch would be a bug
    // in this branch, which the differential test sweeps.
    if let Some(e) = smt::const_of(exp) {
        let e = e & 0xFFFF_FFFF;
        let mut result = smt::word(1, w);
        let mut base = x;
        let mut flag = smt::truth(false);
        let mut k = 0u32;
        while k < 32 {
            if (e >> k) & 1 == 1 {
                let (product, product_overflows) = mul_step(result, base, w, signed)?;
                result = product;
                flag = smt::or(flag, product_overflows);
            }
            k += 1;
            // Only square while a higher exponent bit remains. A squaring whose
            // result no later step reads is dead, and at the BDD wall a dead
            // subterm is not free: it is still a term in the arena and still
            // walked if anything reaches it.
            if k < 32 && (e >> k) != 0 {
                let (square, square_overflows) = mul_step(base, base, w, signed)?;
                base = square;
                flag = smt::or(flag, square_overflows);
            }
        }
        return Some((result, flag));
    }
    let one = smt::word(1, w);
    let mut result = one;
    let mut base = x;
    // The overflow of the steps that ran. `or`-ing in the overflow of a step that
    // did not run would report an overflow that never happened.
    let mut flag = smt::truth(false);
    for k in 0..32 {
        let bit = smt::bit_set(exp, k);
        let (product, product_overflows) = mul_step(result, base, w, signed)?;
        result = smt::ite(bit, product, result);
        flag = smt::or(flag, smt::and(bit, product_overflows));
        if k + 1 < 32 {
            // A squaring is only needed while a higher exponent bit remains. The
            // gate is a test on the exponent's *bits*, which are unsigned, so
            // `uge_const` is the right order here and a signed compare would be
            // wrong for a top bit set.
            let higher = smt::uge_const(exp, 1u64 << (k + 1));
            let (square, square_overflows) = mul_step(base, base, w, signed)?;
            base = smt::ite(higher, square, base);
            flag = smt::or(flag, smt::and(higher, square_overflows));
        }
    }
    Some((result, flag))
}

/// One `w`-bit multiply: its wrapped value and whether it overflowed.
///
/// The value is MIR's plain `*`, the same term a hand-written `a * b` produces, so
/// the fold's steps cannot disagree with a plain multiply about what wrapping is.
fn mul_step(a: Var, b: Var, w: u8, signed: bool) -> Option<(Var, Pred)> {
    Some((smt::mul(a, b), mul_failure(a, b, w, signed)?))
}

/// The bound `saturating_pow` takes when the result overflows.
///
/// The direction is the sign of the *true* result, and `pow` is simpler than the
/// two-operand `saturating_*` here: the magnitude only ever grows with the base, so
/// the result is negative exactly when the base is negative and the exponent is
/// odd. Every other overflowing case is above `MAX`.
fn saturation_end(x: Var, exp: Var, w: u8, signed: bool) -> Option<Var> {
    let (lo, hi) = bounds(w, signed)?;
    if !signed {
        return Some(hi);
    }
    Some(smt::ite(smt::and(smt::negative(x), smt::bit_set(exp, 0)), lo, hi))
}

/// Whether every exponent the model can represent is covered by the fold.
///
/// The fold runs 32 steps, so it is exact for a `u32` exponent and would silently
/// truncate a wider one. The caller reads the exponent's width from the dump, so
/// this is a check rather than an assumption -- and a wider exponent is refused
/// rather than folded with its top bits dropped.
pub fn pow_exponent_fits(exp_w: u8) -> bool {
    exp_w <= 32
}

/// The value a saturating operation takes when it would overflow.
///
/// The direction is the sign of the *overflow*, not of the operator, and that
/// distinction is the whole content of the function. An unsigned `a - b` with
/// `a < b` saturates to zero, while a signed `a - b` with `a >= 0, b < 0`
/// saturates to the maximum: same operator, opposite ends.
fn saturation_bound(op: BinOp, x: Var, y: Var, w: u8, signed: bool) -> Option<Var> {
    let (lo, hi) = bounds(w, signed)?;
    Some(match op {
        // Unsigned addition and multiplication only ever overflow upward.
        BinOp::Add | BinOp::Mul if !signed => hi,
        // Unsigned subtraction only ever borrows downward.
        BinOp::Sub if !signed => lo,
        // Signed addition overflows only when the operands agree in sign, and
        // then the true sum takes that sign -- so the operand's sign is the
        // direction.
        BinOp::Add => smt::ite(smt::negative(x), lo, hi),
        // Signed subtraction overflows only when the operands differ, and then
        // the true difference takes the sign of `x`, not of `y`.
        BinOp::Sub => smt::ite(smt::negative(x), lo, hi),
        // Signed multiplication overflows upward when the operands agree in sign
        // and downward when they differ.
        BinOp::Mul => smt::ite(smt::xor(smt::negative(x), smt::negative(y)), lo, hi),
        _ => return None,
    })
}

/// The minimum and maximum of a `w`-bit integer, as constants.
fn bounds(w: u8, signed: bool) -> Option<(Var, Var)> {
    let max = max_value(w)?;
    if signed {
        Some((smt::word(min_value(w)?, w), smt::word(max >> 1, w)))
    } else {
        Some((smt::word(0, w), smt::word(max, w)))
    }
}

/// `2^w - 1`, the unsigned maximum.
fn max_value(w: u8) -> Option<u64> {
    if w == 0 || w > 64 {
        return None;
    }
    Some(if w == 64 { u64::MAX } else { (1u64 << w) - 1 })
}

/// `-2^(w-1)`, the signed minimum, as its two's-complement bit pattern.
fn min_value(w: u8) -> Option<u64> {
    if w == 0 || w > 64 {
        return None;
    }
    Some(1u64 << (w - 1))
}

/// `-1` as a `w`-bit two's-complement word.
fn all_ones_value(w: u8) -> u64 {
    max_value(w).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    //! Differential test: the model against `core`'s own arithmetic.
    //!
    //! The model here is only useful if it agrees with the real `checked_*`,
    //! `saturating_*` and `wrapping_*` on *every* input, not on the inputs that
    //! happened to be tried. So each case is compared against the `core` call
    //! itself, over all of `u8` and all of `i8` -- small enough to enumerate in
    //! full, and the widths where every sign and boundary rule bites.
    //!
    //! This lives as a unit test rather than under `tests/` because the model is
    //! crate-internal, which is the same reason the IR checks live beside the IR.
    //!
    //! Each operation's term is built once and evaluated per input pair, so the
    //! full cross product is a walk over a fixed term rather than an arena reset
    //! per pair.

    use super::*;

    /// Walk every pair of `w`-bit inputs, calling `f(x, y)` for each.
    fn each_pair(w: u8, mut f: impl FnMut(u64, u64)) {
        let n = 1u64 << w;
        for x in 0..n {
            for y in 0..n {
                f(x, y);
            }
        }
    }

    /// The concrete meaning of an outcome under one input pair.
    ///
    /// The outcome holds *terms*; `smt::evaluate` turns "the model computed
    /// this" into "the model computed this value", which is what can be compared
    /// against Rust.
    fn read(outcome: Outcome, ai: u32, bi: u32, x: u64, y: u64) -> (Option<bool>, Option<u64>) {
        let env = |i: u32| {
            if i == ai {
                Some(x)
            } else if i == bi {
                Some(y)
            } else {
                None
            }
        };
        match outcome {
            Outcome::Value(v) => (None, smt::evaluate(v, env)),
            Outcome::Option { tag, payload } => {
                (smt::evaluate(tag, env).map(|t| t != 0), smt::evaluate(payload, env))
            }
            // A `(T, bool)`: the value is read like a plain one, and the flag is
            // reported through the same `Option<bool>` channel the `Option` tag
            // uses. The two are distinguishable by the caller because a `Tuple`
            // never has a `None` flag -- it is always `Some` -- while an `Option`
            // outcome's tag can be `0`. `check_tuple` reads it that way.
            Outcome::Tuple { value, overflowed } => {
                (smt::evaluate_pred(overflowed, env), smt::evaluate(value, env))
            }
            // A `bool`: there is no value channel, so it is reported through the
            // `Option<bool>` channel the tag uses. `check_bool` reads it that way.
            Outcome::Bool(p) => (smt::evaluate_pred(p, env), None),
            // A value-or-panic outcome is the unary `abs` or the three-operand
            // `clamp`, neither of which is served by this two-channel reader.
            Outcome::ValueOrPanic { .. } => {
                unreachable!("a value-or-panic outcome is read by its own helper")
            }
        }
    }

    /// Build `op`'s term once, then check every input pair against `rust`.
    ///
    /// `rust` answers with the `core` result for a pair: `Some(v)` when the
    /// operation is defined, `None` when `checked_*` would return `None`. A
    /// saturating or wrapping operation always answers `Some`, which is the point
    /// -- those never fail. `from_bits`/`to_bits` reinterpret the bit pattern as
    /// the signed type for the oracle and back.
    fn check(
        op: Intrinsic,
        w: u8,
        signed: bool,
        from_bits: impl Fn(u64) -> i64,
        to_bits: impl Fn(i64) -> u64,
        rust: impl Fn(i64, i64) -> Option<i64>,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let b = smt::var(w);
            let outcome = eval(op, a, b, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(w, |xb, yb| {
                let (x, y) = (from_bits(xb), from_bits(yb));
                let want = rust(x, y);
                let (got_some, got_val) = read(outcome, ai, bi, xb, yb);
                match (got_some, want) {
                    // An `Option` outcome, checked against a `checked_*`.
                    (Some(true), Some(r)) => assert_eq!(
                        got_val,
                        Some(to_bits(r)),
                        "{label} at ({x}, {y}): the model says {got_val:?}, Rust says {r}"
                    ),
                    (Some(true), None) => panic!(
                        "{label} at ({x}, {y}): the model says `Some`, Rust says `None`"
                    ),
                    (Some(false), Some(r)) => panic!(
                        "{label} at ({x}, {y}): the model says `None`, Rust says `{r}`"
                    ),
                    (Some(false), None) => {}
                    // A plain value, checked against a total operation.
                    (None, Some(r)) => assert_eq!(
                        got_val,
                        Some(to_bits(r)),
                        "{label} at ({x}, {y}): the model says {got_val:?}, Rust says {r}"
                    ),
                    (None, None) => panic!("{label}: a plain outcome cannot match a failing oracle"),
                }
            });
        });
    }

    /// The unsigned reinterpretations: a bit pattern is the value, both ways.
    fn ident(v: i64) -> u64 {
        v as u64
    }

    fn unident(bits: u64) -> i64 {
        bits as i64
    }

    /// Check a two-operand `(T, bool)` model against `rust` over every input pair.
    ///
    /// The generic [`check`] cannot serve here. It reads a `Tuple`'s flag through
    /// the same `Option<bool>` channel an `Option` tag uses, and its arms treat
    /// `false` as "the operation is undefined" -- which is right for a `checked_*`
    /// but wrong for an `overflowing_*`, whose value is defined everywhere and
    /// whose flag is a *result*, not a definedness bit. So the flag is compared on
    /// its own, at every pair, as the pair `overflowing_*` actually returns.
    fn check_tuple(
        op: Intrinsic,
        w: u8,
        signed: bool,
        from_bits: impl Fn(u64) -> i64,
        to_bits: impl Fn(i64) -> u64,
        rust: impl Fn(i64, i64) -> (i64, bool),
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let b = smt::var(w);
            let outcome = eval(op, a, b, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let Outcome::Tuple { value, overflowed } = outcome else {
                panic!("{label} must produce a tuple");
            };
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(w, |xb, yb| {
                let (x, y) = (from_bits(xb), from_bits(yb));
                let (want_val, want_flag) = rust(x, y);
                let env = |i: u32| {
                    if i == ai {
                        Some(xb)
                    } else if i == bi {
                        Some(yb)
                    } else {
                        None
                    }
                };
                assert_eq!(
                    smt::evaluate(value, env),
                    Some(to_bits(want_val)),
                    "{label} at ({x}, {y}): value mismatch"
                );
                assert_eq!(
                    smt::evaluate_pred(overflowed, env),
                    Some(want_flag),
                    "{label} at ({x}, {y}): overflow flag mismatch"
                );
            });
        });
    }

    /// The exponents a `pow` walk sweeps.
    ///
    /// `pow`'s exponent is a `u32`, so the full cross product is `2^32` per base
    /// and cannot be walked. The sweep is instead the range where the fold's
    /// *control flow* can differ -- every exponent up to 256 covers all values
    /// whose low eight bits vary -- plus the boundaries where a step's gating
    /// changes: `2^k - 1`, `2^k`, `2^k + 1` for every `k` in the fold, and the
    /// extremes. Between them those exercise every branch of the unrolled fold,
    /// including the "no higher bit remains" cut at each position.
    fn pow_exponents() -> Vec<u32> {
        let mut e: Vec<u32> = (0..=256).collect();
        // The `2^k +/- 1` boundaries only matter where the *gate* flips, and the
        // low 17 positions are where a `u8`/`i8` base can still be in range; past
        // that every exponent overflows every base, and the extremes below pin the
        // high gates.
        for k in 0..=16u32 {
            let p = 1u32 << k;
            e.push(p.wrapping_sub(1));
            e.push(p);
            e.push(p.wrapping_add(1));
        }
        e.extend([
            u32::MAX,
            u32::MAX - 1,
            u32::MAX / 2,
            u32::MAX / 2 + 1,
            1 << 30,
            (1 << 24) + 1,
        ]);
        e.sort_unstable();
        e.dedup();
        e
    }

    /// Check a `pow` family against `core` over every base and the exponent set.
    ///
    /// One helper for all four families, because they share the fold: a
    /// `wrapping_pow` and an `overflowing_pow` that disagreed about the wrapped
    /// value would be two definitions of `pow`, and checking them through one
    /// walk is what stops that. `oracle` returns the expected `(value, flag)`,
    /// or `None` for the `checked_pow` case where `core` returns `None`, and it
    /// calls the real `core` method so the expectation is never a copy of the
    /// model.
    fn check_pow(
        op: Intrinsic,
        w: u8,
        signed: bool,
        base_from: impl Fn(u64) -> i64,
        base_to: impl Fn(i64) -> u64,
        oracle: impl Fn(i64, u32) -> Option<(i64, bool)>,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let base = smt::var(w);
            let exp = smt::var(32);
            let outcome = eval(op, base, exp, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let (bi, ei) = (smt::index(base), smt::index(exp));
            let n = 1u64 << w;
            for xb in 0..n {
                let x = base_from(xb);
                for e in pow_exponents() {
                    let env = |i: u32| {
                        if i == bi {
                            Some(xb)
                        } else if i == ei {
                            Some(u64::from(e))
                        } else {
                            None
                        }
                    };
                    let (got_some, got_val, got_flag) = match outcome {
                        Outcome::Value(v) => (None, smt::evaluate(v, env), None),
                        Outcome::Option { tag, payload } => (
                            smt::evaluate(tag, env).map(|t| t != 0),
                            smt::evaluate(payload, env),
                            None,
                        ),
                        Outcome::Tuple { value, overflowed } => (
                            smt::evaluate_pred(overflowed, env),
                            smt::evaluate(value, env),
                            smt::evaluate_pred(overflowed, env),
                        ),
                        // `pow` is never a `bool`, so this arm is unreachable in
                        // this helper; it exists only to keep the match total.
                        Outcome::Bool(_) => unreachable!("`pow` is not a bool"),
                        // `pow` is never a value-or-panic shape either.
                        Outcome::ValueOrPanic { .. } => {
                            unreachable!("`pow` is not a value-or-panic shape")
                        }
                    };
                    let want = oracle(x, e);
                    let Some((wv, wf)) = want else {
                        assert_eq!(
                            got_some,
                            Some(false),
                            "{label} at ({x}, {e}): the model says `Some`, Rust says `None`"
                        );
                        continue;
                    };
                    assert_eq!(
                        got_val,
                        Some(base_to(wv)),
                        "{label} at ({x}, {e}): value mismatch"
                    );
                    // An `Option` outcome carries the flag in its tag, a `Tuple`
                    // in field 1; both are read above, so one assertion covers
                    // whichever shape this family produced.
                    if let Some(gf) = got_flag {
                        assert_eq!(gf, wf, "{label} at ({x}, {e}): overflow flag mismatch");
                    }
                }
            }
        });
    }

    /// `wrapping_pow` and `overflowing_pow` against `core`, over all of `u8`/`i8`
    /// and the exponent sweep.
    ///
    /// The two families are checked together because they must agree on the
    /// *wrapped* value while disagreeing on nothing else: `wrapping_pow` is
    /// `overflowing_pow` with the flag dropped. `checked_pow` is here too, so the
    /// `None` boundary is pinned to the same flag -- if the fold reported an
    /// overflow the other two did not, one of the three would fail.
    #[test]
    fn the_pow_families_agree_with_rust() {
        // `wrapping_pow`: the flag is discarded, so the oracle returns the value
        // with a flag that is never read.
        check_pow(
            Intrinsic::Pow(Family::Wrapping),
            8,
            false,
            unident,
            ident,
            |x, e| Some((u8::wrapping_pow(x as u8, e) as i64, false)),
            "wrapping_pow u8",
        );
        check_pow(
            Intrinsic::Pow(Family::Wrapping),
            8,
            true,
            to_i8,
            i8_bits,
            |x, e| Some((i8::wrapping_pow(x as i8, e) as i64, false)),
            "wrapping_pow i8",
        );
        // `overflowing_pow`: the flag is the shared overflow predicate.
        check_pow(
            Intrinsic::Pow(Family::Overflowing),
            8,
            false,
            unident,
            ident,
            |x, e| {
                let (v, o) = u8::overflowing_pow(x as u8, e);
                Some((v as i64, o))
            },
            "overflowing_pow u8",
        );
        check_pow(
            Intrinsic::Pow(Family::Overflowing),
            8,
            true,
            to_i8,
            i8_bits,
            |x, e| {
                let (v, o) = i8::overflowing_pow(x as i8, e);
                Some((v as i64, o))
            },
            "overflowing_pow i8",
        );
        // `checked_pow`: `None` exactly where the flag is set.
        check_pow(
            Intrinsic::Pow(Family::Checked),
            8,
            false,
            unident,
            ident,
            |x, e| u8::checked_pow(x as u8, e).map(|v| (v as i64, false)),
            "checked_pow u8",
        );
        check_pow(
            Intrinsic::Pow(Family::Checked),
            8,
            true,
            to_i8,
            i8_bits,
            |x, e| i8::checked_pow(x as i8, e).map(|v| (v as i64, false)),
            "checked_pow i8",
        );
    }

    /// `saturating_pow` against `core`, over all of `u8`/`i8`.
    ///
    /// This is the one family whose result is a *clamp*, so the value at an
    /// overflow is the interesting part: it has to land on the right bound, and
    /// the signed case picks between `MIN` and `MAX` by the sign of the true
    /// result. A model that clamped both signs to `MAX` would agree with `core`
    /// for every non-negative base and fail on the negative ones -- which is what
    /// the `i8` walk covers.
    #[test]
    fn saturating_pow_agrees_with_rust() {
        check_pow(
            Intrinsic::Pow(Family::Saturating),
            8,
            false,
            unident,
            ident,
            |x, e| Some((u8::saturating_pow(x as u8, e) as i64, false)),
            "saturating_pow u8",
        );
        check_pow(
            Intrinsic::Pow(Family::Saturating),
            8,
            true,
            to_i8,
            i8_bits,
            |x, e| Some((i8::saturating_pow(x as i8, e) as i64, false)),
            "saturating_pow i8",
        );
    }

    /// A constant exponent takes a different path through the fold than a symbolic
    /// one, and the two must agree.
    ///
    /// `pow_fold` fast-paths a literal exponent: it reads the exponent's bits from
    /// a `u64` and builds only the steps that run, because the general fold's
    /// `ite`-gated fan-out is exponential in the unrolled size and the bit-blaster
    /// cannot carry it (the query hangs rather than answering `Unknown`). The
    /// fast path is the same binary-exponentiation recurrence, so it is the same
    /// function -- but "same recurrence" is an argument, not a measurement. This
    /// pins it: for every exponent in the sweep, the constant `e` term and the
    /// symbolic term bound to `e` are *evaluated* and compared bit for bit, at
    /// every base of a `u8`.
    ///
    /// Both sides go through `smt::evaluate`, so this is the model's arithmetic
    /// and not the blaster's -- which is the point. The blaster is what the fast
    /// path exists to spare, so a test that needed it could not check the branch
    /// that removes the load.
    #[test]
    fn a_constant_exponent_agrees_with_a_symbolic_one() {
        for family in [Family::Wrapping, Family::Checked, Family::Saturating, Family::Overflowing] {
            for signed in [false, true] {
                let (w, to_signed, to_bits) = if signed {
                    (8u8, to_i8 as fn(u64) -> i64, i8_bits as fn(i64) -> u64)
                } else {
                    (8u8, unident as fn(u64) -> i64, ident as fn(i64) -> u64)
                };
                smt::with_fresh(|| {
                    let base = smt::var(w);
                    let sym = smt::var(32);
                    let bi = smt::index(base);
                    let si = smt::index(sym);
                    for e in pow_exponents() {
                        let env = |i: u32| {
                            if i == bi {
                                None
                            } else if i == si {
                                Some(u64::from(e))
                            } else {
                                None
                            }
                        };
                        let constant = smt::word(u64::from(e), 32);
                        for xb in 0..(1u64 << w) {
                            let read = |outcome: Outcome| match outcome {
                                Outcome::Value(v) => (smt::evaluate(v, |i| {
                                    if i == bi { Some(xb) } else { env(i) }
                                }), None, None),
                                Outcome::Option { tag, payload } => (
                                    smt::evaluate(payload, |i| if i == bi { Some(xb) } else { env(i) }),
                                    smt::evaluate(tag, |i| if i == bi { Some(xb) } else { env(i) }),
                                    None,
                                ),
                                Outcome::Tuple { value, overflowed } => (
                                    smt::evaluate(value, |i| if i == bi { Some(xb) } else { env(i) }),
                                    None,
                                    smt::evaluate_pred(overflowed, |i| if i == bi { Some(xb) } else { env(i) }),
                                ),
                                // `pow` is never a `bool`; the arm keeps the
                                // match total.
                                Outcome::Bool(_) => unreachable!("`pow` is not a bool"),
                                Outcome::ValueOrPanic { .. } => {
                                    unreachable!("`pow` is not a value-or-panic shape")
                                }
                            };
                            let from_const = eval(Intrinsic::Pow(family), base, constant, w, signed, w)
                                .unwrap_or_else(|| panic!("{family:?} const must be modelled"));
                            let from_sym = eval(Intrinsic::Pow(family), base, sym, w, signed, w)
                                .unwrap_or_else(|| panic!("{family:?} symbolic must be modelled"));
                            assert_eq!(
                                read(from_const),
                                read(from_sym),
                                "{family:?} signed={signed} base={} exp={e}: the constant-exponent \
                                 fast path and the symbolic fold disagree",
                                to_bits(to_signed(xb))
                            );
                        }
                    }
                });
            }
        }
    }

    /// `pow` is modelled only where a product is, and only up to its own bound.
    ///
    /// The bound is deliberately *below* the product bound, because the fold
    /// composes many products: this pins the separation, so a later change that
    /// collapses the two constants has to delete an assertion rather than quietly
    /// make every symbolic `pow` slow.
    #[test]
    fn pow_is_modelled_only_where_a_product_is() {
        // A `u32` read makes the comparison opaque to clippy's constant check while
        // still being a compile-time fact; the point is that a later change to the
        // constants cannot silently pass.
        assert!(
            u32::from(POW_MAX_WIDTH) < u32::from(MUL_MAX_WIDTH),
            "pow's fold must keep the tighter bound"
        );
        assert!(is_modelled(Intrinsic::Pow(Family::Wrapping), POW_MAX_WIDTH, false));
        assert!(!is_modelled(Intrinsic::Pow(Family::Wrapping), POW_MAX_WIDTH + 1, false));
        // A width a two-operand product admits is still refused for `pow`.
        assert!(!is_modelled(Intrinsic::Pow(Family::Wrapping), MUL_MAX_WIDTH, false));
        assert!(eval(
            Intrinsic::Pow(Family::Overflowing),
            smt::var(POW_MAX_WIDTH),
            smt::var(32),
            POW_MAX_WIDTH,
            false,
            POW_MAX_WIDTH
        )
        .is_some());
        assert!(eval(
            Intrinsic::Pow(Family::Overflowing),
            smt::var(POW_MAX_WIDTH + 1),
            smt::var(32),
            POW_MAX_WIDTH + 1,
            false,
            POW_MAX_WIDTH + 1
        )
        .is_none());
        // The fold runs 32 steps, so a `u32` exponent is the whole domain and a
        // wider one would be silently truncated.
        assert!(pow_exponent_fits(32));
        assert!(!pow_exponent_fits(33));
        assert!(!pow_exponent_fits(64));
    }

    /// A *symbolic* `pow` must return a verdict instead of hanging the blaster.
    ///
    /// `pow` is a 32-step fold, and its term is a DAG with heavy sharing: a shared subterm
    /// sits on many paths, so a walk that does not memoise re-visits it once per path --
    /// 2^32 visits for a 32-step fold. The arena does not fill on the way, so the old
    /// overflow guard never fired, and `prove` simply never returned. This is the shape
    /// that regressed: a `pow` whose *exponent* is a variable, which is the only way the
    /// fold's control flow is symbolic at all. A concrete exponent is unrolled to one path
    /// and never showed the blow-up.
    ///
    /// The assertion is deliberately weak -- any verdict is accepted, `Unknown` included.
    /// The property being pinned is termination, not the answer: before the fix the call
    /// did not return, so reaching the assertion at all is the whole test. Demanding
    /// `Valid` here would fail on the widths where the honest answer *is* `Unknown`.
    #[test]
    fn a_symbolic_pow_returns_a_verdict_instead_of_hanging() {
        for w in [4u8, 6, 8] {
            smt::with_fresh(|| {
                let base = smt::var(w);
                let exp = smt::var(32);
                let outcome = eval(Intrinsic::Pow(Family::Wrapping), base, exp, w, false, w)
                    .expect("`wrapping_pow` at a small width must be modelled");
                let Outcome::Value(value) = outcome else {
                    panic!("`wrapping_pow` yields a value, not an option or a tuple");
                };
                // `x^e == x^e` is a tautology, so the only sound outcomes are `Valid` and
                // `Unknown`. A `Counterexample` or an `Unsat` here would be a *wrong*
                // answer, and one that a step budget could in principle manufacture if it
                // let a truncated encoding through as a complete one -- so this pins both
                // that the call returns and that the budget did not corrupt the verdict.
                let verdict = smt::prove(smt::eq(value, value));
                assert!(
                    matches!(verdict, crate::smt::Verdict::Valid | crate::smt::Verdict::Unknown),
                    "a symbolic `pow` on a tautology must be `Valid` or `Unknown`, got {verdict:?}"
                );
            });
        }
    }

    /// The `pow` names classify into the four families, and their neighbours do
    /// not.
    ///
    /// `pow` is matched before the operator table, so the thing to pin is that
    /// the family prefix is read and that a name *containing* `pow` -- or the
    /// panic-on-overflow `pow` itself -- does not silently become a modelled call.
    #[test]
    fn the_pow_names_classify_and_their_neighbours_do_not() {
        assert_eq!(classify("wrapping_pow"), Some(Intrinsic::Pow(Family::Wrapping)));
        assert_eq!(classify("saturating_pow"), Some(Intrinsic::Pow(Family::Saturating)));
        assert_eq!(classify("checked_pow"), Some(Intrinsic::Pow(Family::Checked)));
        assert_eq!(classify("overflowing_pow"), Some(Intrinsic::Pow(Family::Overflowing)));
        // The qualified path rustc prints resolves to the same item.
        assert_eq!(
            classify("core::num::<impl u8>::wrapping_pow"),
            Some(Intrinsic::Pow(Family::Wrapping))
        );
        // The plain `pow` panics on overflow and has no family prefix, so it is its
        // own shape (`Intrinsic::PowPanic`) rather than a family member -- the
        // prefix split below must not see it, and `pow` under a prefix that is not
        // one of the four is refused.
        assert_eq!(classify("pow"), Some(Intrinsic::PowPanic));
        assert_eq!(classify("core::num::<impl u8>::pow"), Some(Intrinsic::PowPanic));
        assert_eq!(classify("unchecked_pow"), None);
        assert_eq!(classify("powf"), None);
        // `next_power_of_two` is modelled now, but the prefix split must not read
        // it as a `pow`: it is its own shape, not `Intrinsic::Pow`.
        assert_eq!(classify("next_power_of_two"), Some(Intrinsic::NextPowerOfTwo));
        assert_eq!(
            classify("checked_next_power_of_two"),
            Some(Intrinsic::CheckedNextPowerOfTwo)
        );
    }

    /// The `Option`/`Result` method names classify, and a *user* type spelled
    /// `Option`/`Result` does not.
    ///
    /// `names_option_impl`/`names_result_impl` key on the `option::Option` /
    /// `result::Result` path rustc prints for the standard library's types, so the
    /// interesting cases are the ones that must be refused: a local `Option` in a
    /// module (`m::Option`) and a bare `Option::unwrap` that names neither. A
    /// same-dump body is answered by the executor before the model, so these
    /// predicates only have to keep the model from claiming a different type's
    /// method. The success/failure variants are checked too, because `Result` puts
    /// the payload on the *other* discriminant from `Option`.
    #[test]
    fn the_option_and_result_method_names_classify_and_a_local_type_does_not() {
        assert_eq!(
            classify("core::option::Option::<u32>::unwrap_or"),
            Some(Intrinsic::OptionMethod(OptionMethod::UnwrapOr))
        );
        assert_eq!(
            classify("std::option::Option::<u8>::unwrap"),
            Some(Intrinsic::OptionMethod(OptionMethod::Unwrap))
        );
        assert_eq!(
            classify("Option::<u32>::expect"),
            Some(Intrinsic::OptionMethod(OptionMethod::Expect))
        );
        assert_eq!(
            classify("core::option::Option::<u8>::is_some"),
            Some(Intrinsic::OptionMethod(OptionMethod::IsSuccess))
        );
        assert_eq!(
            classify("core::option::Option::<u8>::is_none"),
            Some(Intrinsic::OptionMethod(OptionMethod::IsFailure))
        );
        // The `Result` family: `is_ok` is the success variant (`Ok`), `is_err` the
        // failure one.
        assert_eq!(
            classify("core::result::Result::<u8, u16>::is_ok"),
            Some(Intrinsic::OptionMethod(OptionMethod::IsSuccess))
        );
        assert_eq!(
            classify("std::result::Result::<u8, u16>::is_err"),
            Some(Intrinsic::OptionMethod(OptionMethod::IsFailure))
        );
        assert_eq!(
            classify("Result::<u8, u16>::unwrap"),
            Some(Intrinsic::OptionMethod(OptionMethod::Unwrap))
        );
        assert_eq!(
            classify("core::result::Result::<u8, u16>::unwrap_or"),
            Some(Intrinsic::OptionMethod(OptionMethod::UnwrapOr))
        );
        // The `Option`↔`Result` conversions: `ok_or` on `Option`, `ok`/`err` on
        // `Result`. `ok_or` is printed with a *method* turbofish
        // (`Option::<u8>::ok_or::<i32>`), so the classifier's last-segment read has
        // to skip a `<…>` segment to find `ok_or`.
        assert_eq!(
            classify("core::option::Option::<u8>::ok_or::<i32>"),
            Some(Intrinsic::OptionMethod(OptionMethod::OkOr))
        );
        assert_eq!(
            classify("Option::<u32>::ok_or::<u32>"),
            Some(Intrinsic::OptionMethod(OptionMethod::OkOr))
        );
        assert_eq!(
            classify("core::result::Result::<u8, u16>::ok"),
            Some(Intrinsic::OptionMethod(OptionMethod::Ok))
        );
        assert_eq!(
            classify("core::result::Result::<u8, u16>::err"),
            Some(Intrinsic::OptionMethod(OptionMethod::Err))
        );
        // A local type spelled `Option`/`Result` in a module is not the standard
        // library's.
        assert_eq!(classify("m::Option::<u8>::unwrap"), None);
        assert_eq!(classify("m::Result::<u8, u16>::is_ok"), None);
        assert_eq!(classify("m::Option::<u8>::ok_or::<u8>"), None);
        // A different method the model does not know stays unmodelled.
        assert_eq!(classify("core::option::Option::<u8>::map"), None);
        assert_eq!(classify("core::result::Result::<u8, u16>::map"), None);
    }

    /// A *method* turbofish puts a `<…>` segment where the method name would be,
    /// so the classifier's last-segment read must skip it -- or `ok_or` is never
    /// classified and the call is reported unmodelled. A plain path segment that
    /// merely contains a `<` (a generic type) is skipped too, and a method name
    /// never begins with `<`.
    #[test]
    fn a_method_turbofish_does_not_hide_the_method_name() {
        assert_eq!(
            classify("Option::<u8>::ok_or::<i32>"),
            Some(Intrinsic::OptionMethod(OptionMethod::OkOr))
        );
        // The ordinary spelling (no method turbofish) still classifies.
        assert_eq!(
            classify("core::option::Option::<u8>::is_some"),
            Some(Intrinsic::OptionMethod(OptionMethod::IsSuccess))
        );
        // A generic *argument* segment is skipped for an inherent method too.
        assert_eq!(
            classify("core::num::<impl u8>::wrapping_add"),
            Some(Intrinsic::Wrapping(BinOp::Add))
        );
    }

    /// The `for`-loop range names classify, in the spelling every toolchain prints.
    ///
    /// This is an MSRV defect, not a hypothetical: rustc **1.85** prints the
    /// `as`-projection form with the type *unqualified*
    /// (`<RangeInclusive<u32> as IntoIterator>::into_iter`) where current stable
    /// qualifies it (`<std::ops::RangeInclusive<u32> as IntoIterator>::into_iter`).
    /// `names_range` required an `ops::` segment, so every `for` loop was
    /// `incomplete: call to unmodelled function` on the compiler the manifest
    /// promises to support -- and green on 1.99, which is why only gate 14 (the
    /// MSRV run) caught it. Both spellings must classify, and a user type named
    /// `RangeInclusive` in a module (`m::RangeInclusive`) must not.
    #[test]
    fn the_for_loop_range_names_classify_in_both_toolchain_spellings() {
        // The qualified form current stable prints.
        assert_eq!(
            classify("std::ops::RangeInclusive::<u32>::new"),
            Some(Intrinsic::Range(RangeMethod::New))
        );
        assert_eq!(
            classify("<std::ops::RangeInclusive<u32> as IntoIterator>::into_iter"),
            Some(Intrinsic::Range(RangeMethod::IntoIter))
        );
        assert_eq!(
            classify("<std::ops::RangeInclusive<u32> as Iterator>::next"),
            Some(Intrinsic::Range(RangeMethod::Next))
        );
        // The unqualified form rustc 1.85 (the MSRV) prints.
        assert_eq!(
            classify("<RangeInclusive<u32> as IntoIterator>::into_iter"),
            Some(Intrinsic::Range(RangeMethod::IntoIter))
        );
        assert_eq!(
            classify("<RangeInclusive<i8> as IntoIterator>::into_iter"),
            Some(Intrinsic::Range(RangeMethod::IntoIter))
        );
        assert_eq!(
            classify("<RangeInclusive<u32> as Iterator>::next"),
            Some(Intrinsic::Range(RangeMethod::Next))
        );
        assert_eq!(
            classify("RangeInclusive::<u32>::new"),
            Some(Intrinsic::Range(RangeMethod::New))
        );
        // The exclusive range's two spellings.
        assert_eq!(
            classify("std::ops::Range::<u32>::new"),
            Some(Intrinsic::Range(RangeMethod::New))
        );
        assert_eq!(
            classify("<Range<u32> as IntoIterator>::into_iter"),
            Some(Intrinsic::Range(RangeMethod::IntoIter))
        );
        assert_eq!(
            classify("<Range<u32> as Iterator>::next"),
            Some(Intrinsic::Range(RangeMethod::Next))
        );
        // A user type spelled `RangeInclusive`/`Range` in a module is not the
        // standard library's: `m::RangeInclusive` has no `ops::` segment and does
        // not start with `<Range…`, so it is refused. (A same-dump body is answered
        // by the executor before the model in any case.)
        assert_eq!(classify("m::RangeInclusive::<u32>::new"), None);
        assert_eq!(classify("m::Range::<u32>::new"), None);
        // The neighbouring range types are not `Iterator`s and never drive a `for`
        // loop, so they are refused.
        assert_eq!(classify("std::ops::RangeFrom::<u32>::new"), None);
        assert_eq!(classify("std::ops::RangeTo::<u32>::new"), None);
        // The `Iterator` methods are matched on the *trait* as well as the type, so a
        // user type named `Range` with a custom `into_iter` is refused -- answering it
        // with the model's identity semantics would be a false proof of a call the
        // compiler resolved to the user's own method. This is the hole an unqualified
        // `Range` (which rustc 1.85 prints for the standard library) would otherwise
        // open, because a user can name a type `Range` too.
        assert_eq!(classify("<Range<u8> as a::Custom>::into_iter"), None);
        assert_eq!(classify("<Range<u8> as a::Custom>::next"), None);
        assert_eq!(classify("<RangeInclusive<u8> as m::IntoIterator>::into_iter"), None);
        assert_eq!(classify("<Range<u8> as m::Iterator>::next"), None);
        // An `as`-projection whose type is the standard library's but whose trait is a
        // user's is still refused (the trait, not the type, is what a user can spoof).
        assert_eq!(classify("<Range<u8> as core::ops::RangeBounds<u8>>::into_iter"), None);
    }

    /// The `overflowing_*` family, two-operand, against `core` over all of `u8`
    /// and `i8`.
    ///
    /// This is the family whose flag is the shared overflow predicate read
    /// directly. The value is the wrapped one and is defined at *every* input,
    /// which the exhaustive walk checks rather than assumes; the flag is checked
    /// at every input too, so a predicate that happened to agree on the boundary
    /// but not in the interior would be caught.
    #[test]
    fn the_overflowing_family_agrees_with_rust() {
        check_tuple(
            Intrinsic::Overflowing(BinOp::Add),
            8,
            false,
            unident,
            ident,
            |x, y| {
                let (v, o) = u8::overflowing_add(x as u8, y as u8);
                (v as i64, o)
            },
            "overflowing_add u8",
        );
        check_tuple(
            Intrinsic::Overflowing(BinOp::Sub),
            8,
            false,
            unident,
            ident,
            |x, y| {
                let (v, o) = u8::overflowing_sub(x as u8, y as u8);
                (v as i64, o)
            },
            "overflowing_sub u8",
        );
        check_tuple(
            Intrinsic::Overflowing(BinOp::Mul),
            8,
            false,
            unident,
            ident,
            |x, y| {
                let (v, o) = u8::overflowing_mul(x as u8, y as u8);
                (v as i64, o)
            },
            "overflowing_mul u8",
        );
        check_tuple(
            Intrinsic::Overflowing(BinOp::Add),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| {
                let (v, o) = i8::overflowing_add(x as i8, y as i8);
                (v as i64, o)
            },
            "overflowing_add i8",
        );
        check_tuple(
            Intrinsic::Overflowing(BinOp::Sub),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| {
                let (v, o) = i8::overflowing_sub(x as i8, y as i8);
                (v as i64, o)
            },
            "overflowing_sub i8",
        );
        check_tuple(
            Intrinsic::Overflowing(BinOp::Mul),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| {
                let (v, o) = i8::overflowing_mul(x as i8, y as i8);
                (v as i64, o)
            },
            "overflowing_mul i8",
        );
    }

    /// `overflowing_div`/`overflowing_rem` are refused, like the rest of the
    /// division families except `checked_*`.
    ///
    /// This looks like a form of division that can report its failure as a value,
    /// and the flag *does* report `MIN / -1`. But a zero divisor still panics --
    /// the flag is not the whole failure predicate -- so modelling it as total
    /// would hide a panic. The differential test against `core` is what exposed
    /// this: `7u8.overflowing_div(0)` unwinds, it does not return `(_, true)`.
    #[test]
    fn overflowing_division_is_refused_like_the_other_panicking_families() {
        for w in [8u8, 16, 32] {
            for signed in [false, true] {
                assert!(
                    !is_modelled(Intrinsic::Overflowing(BinOp::Div), w, signed),
                    "overflowing_div must be refused at {w} bits (signed={signed})"
                );
                assert!(
                    !is_modelled(Intrinsic::Overflowing(BinOp::Rem), w, signed),
                    "overflowing_rem must be refused at {w} bits (signed={signed})"
                );
            }
        }
        // `checked_*` is still the one division family that is modelled, which is
        // what makes the refusal above a *narrowing* and not an accident.
        assert!(is_modelled(Intrinsic::Checked(BinOp::Div), 8, false));
        assert!(is_modelled(Intrinsic::Checked(BinOp::Rem), 8, false));
    }

    #[test]
    fn checked_u8_agrees_with_rust() {
        check(
            Intrinsic::Checked(BinOp::Add),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_add(x as u8, y as u8).map(|v| v as i64),
            "checked_add u8",
        );
        check(
            Intrinsic::Checked(BinOp::Sub),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_sub(x as u8, y as u8).map(|v| v as i64),
            "checked_sub u8",
        );
        check(
            Intrinsic::Checked(BinOp::Mul),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_mul(x as u8, y as u8).map(|v| v as i64),
            "checked_mul u8",
        );
    }

    #[test]
    fn saturating_u8_agrees_with_rust() {
        check(
            Intrinsic::Saturating(BinOp::Add),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::saturating_add(x as u8, y as u8) as i64),
            "saturating_add u8",
        );
        check(
            Intrinsic::Saturating(BinOp::Sub),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::saturating_sub(x as u8, y as u8) as i64),
            "saturating_sub u8",
        );
        check(
            Intrinsic::Saturating(BinOp::Mul),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::saturating_mul(x as u8, y as u8) as i64),
            "saturating_mul u8",
        );
    }

    #[test]
    fn wrapping_u8_agrees_with_rust() {
        check(
            Intrinsic::Wrapping(BinOp::Add),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::wrapping_add(x as u8, y as u8) as i64),
            "wrapping_add u8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Sub),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::wrapping_sub(x as u8, y as u8) as i64),
            "wrapping_sub u8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Mul),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::wrapping_mul(x as u8, y as u8) as i64),
            "wrapping_mul u8",
        );
    }

    #[test]
    fn checked_div_and_rem_agree_with_rust() {
        check(
            Intrinsic::Checked(BinOp::Div),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_div(x as u8, y as u8).map(|v| v as i64),
            "checked_div u8",
        );
        check(
            Intrinsic::Checked(BinOp::Rem),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_rem(x as u8, y as u8).map(|v| v as i64),
            "checked_rem u8",
        );
    }

    /// Reinterpret a two's-complement bit pattern as `i8`, for the signed oracle.
    fn to_i8(bits: u64) -> i64 {
        (bits as u8) as i8 as i64
    }

    /// The inverse, for comparing an `i8` result against the model's bits.
    fn i8_bits(v: i64) -> u64 {
        (v as i8) as u8 as u64
    }

    #[test]
    fn checked_i8_agrees_with_rust() {
        check(
            Intrinsic::Checked(BinOp::Add),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_add(x as i8, y as i8).map(|v| v as i64),
            "checked_add i8",
        );
        check(
            Intrinsic::Checked(BinOp::Sub),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_sub(x as i8, y as i8).map(|v| v as i64),
            "checked_sub i8",
        );
        check(
            Intrinsic::Checked(BinOp::Mul),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_mul(x as i8, y as i8).map(|v| v as i64),
            "checked_mul i8",
        );
        check(
            Intrinsic::Checked(BinOp::Div),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_div(x as i8, y as i8).map(|v| v as i64),
            "checked_div i8",
        );
        check(
            Intrinsic::Checked(BinOp::Rem),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_rem(x as i8, y as i8).map(|v| v as i64),
            "checked_rem i8",
        );
    }

    #[test]
    fn saturating_and_wrapping_i8_agree_with_rust() {
        check(
            Intrinsic::Saturating(BinOp::Add),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::saturating_add(x as i8, y as i8) as i64),
            "saturating_add i8",
        );
        check(
            Intrinsic::Saturating(BinOp::Sub),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::saturating_sub(x as i8, y as i8) as i64),
            "saturating_sub i8",
        );
        check(
            Intrinsic::Saturating(BinOp::Mul),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::saturating_mul(x as i8, y as i8) as i64),
            "saturating_mul i8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Add),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::wrapping_add(x as i8, y as i8) as i64),
            "wrapping_add i8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Sub),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::wrapping_sub(x as i8, y as i8) as i64),
            "wrapping_sub i8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Mul),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::wrapping_mul(x as i8, y as i8) as i64),
            "wrapping_mul i8",
        );
    }

    /// `u16`, so the width-dependence of the overflow test is exercised at a
    /// second width rather than only at 8 bits. The full `u16` cross product is
    /// 2^32, so this samples the boundaries plus a spread of interior values.
    #[test]
    fn saturating_u16_agrees_with_rust_at_the_boundaries() {
        let vals: [u16; 12] = [0, 1, 2, 15, 100, 255, 256, 32767, 32768, 65534, 65535, 12345];
        smt::with_fresh(|| {
            let a = smt::var(16);
            let b = smt::var(16);
            let op = Intrinsic::Saturating(BinOp::Add);
            let outcome = eval(op, a, b, 16, false, 16).expect("u16 is modelled");
            let (ai, bi) = (smt::index(a), smt::index(b));
            for &x in &vals {
                for &y in &vals {
                    let (_, got) = read(outcome, ai, bi, x as u64, y as u64);
                    assert_eq!(
                        got,
                        Some(u16::saturating_add(x, y) as u64),
                        "saturating_add u16 at ({x}, {y})"
                    );
                }
            }
        });
    }

    /// The signed division trap: `i8::MIN / -1` has no representable quotient, and
    /// the model must say `None` rather than hand back the wrapped value.
    #[test]
    fn signed_division_refuses_min_by_neg_one() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            let op = Intrinsic::Checked(BinOp::Div);
            let outcome = eval(op, a, b, 8, true, 8).expect("i8 is modelled");
            let (ai, bi) = (smt::index(a), smt::index(b));
            let (got_some, _) = read(outcome, ai, bi, i8_bits(i8::MIN as i64), i8_bits(-1));
            assert_eq!(
                got_some,
                Some(false),
                "the model must not produce a quotient for i8::MIN / -1"
            );
            assert_eq!(i8::checked_div(i8::MIN, -1), None, "the oracle must agree");
        });
    }

    /// A name the model does not cover must be refused, not approximated. This is
    /// what keeps an unmodelled call from becoming a *silently weaker* proof.
    ///
    /// Refusal happens at two layers, and the distinction matters. A name whose
    /// *family and operator* are unknown does not classify at all. A name that
    /// classifies but whose shape cannot be modelled -- `saturating_div` panics on
    /// a zero divisor, so treating it as total would hide a panic -- is refused by
    /// `is_modelled`/`eval`. Both must refuse; neither may approximate.
    #[test]
    fn unmodelled_names_are_refused() {
        // Unknown operator: `shl` is not in the operator table, so the whole
        // suffix fails to match. (`pow` *is* modelled now -- it is its own shape,
        // not an operator -- so it is no longer an example here.)
        assert!(classify("wrapping_shl").is_none());
        assert!(classify("checked_shl").is_none());
        assert!(classify("unchecked_add").is_none());
        // The suffix is matched whole, so a near miss is not read as a modelled
        // shape. `add_signed` *is* modelled now, but only the exact spelling: a
        // trailing word does not classify.
        assert!(classify("wrapping_add_signed_thing").is_none());
        assert!(classify("add_signed").is_none());

        // A *known* operator that only some families can model. `saturating_div`
        // classifies as a name, and is then refused by the model: only the
        // `checked_` family may model division, because the others panic on zero.
        let sat_div = classify("core::num::<impl u8>::saturating_div")
            .expect("the name is recognised, so it classifies");
        assert_eq!(sat_div, Intrinsic::Saturating(BinOp::Div));
        assert!(
            eval(sat_div, smt::var(8), smt::var(8), 8, false, 8).is_none(),
            "saturating_div must not be modelled: it panics on a zero divisor"
        );
        assert!(!is_modelled(sat_div, 8, false));

        // And the names that *are* covered classify, under both spellings.
        assert!(classify("core::num::<impl u8>::checked_add").is_some());
        assert!(classify("saturating_sub").is_some());
    }

    /// A `u16` product is now inside the bound, and the widened test is still exact
    /// there -- the width that used to be refused outright.
    ///
    /// The oracle is `core`'s own `checked_mul`/`saturating_mul`, so this is not a
    /// second copy of the model. The sweep is the boundary neighbourhood plus a few
    /// strides: `2^16` pairs is too many to enumerate, and the cases a wrong bound
    /// gets wrong are the ones where the product lands exactly on `MAX`, one past
    /// it, or in the high half.
    #[test]
    fn a_u16_product_is_modelled_and_exact() {
        let vals: [u16; 16] = [
            0, 1, 2, 3, 255, 256, 257, 32767, 32768, 32769, 43690, 65534, 65535, 12345, 40000, 513,
        ];
        smt::with_fresh(|| {
            let a = smt::var(16);
            let b = smt::var(16);
            let (ai, bi) = (smt::index(a), smt::index(b));
            let checked = eval(Intrinsic::Checked(BinOp::Mul), a, b, 16, false, 16)
                .expect("checked_mul u16 must be modelled");
            let sat = eval(Intrinsic::Saturating(BinOp::Mul), a, b, 16, false, 16)
                .expect("saturating_mul u16 must be modelled");
            for &x in &vals {
                for &y in &vals {
                    let (got_some, got_val) = read(checked, ai, bi, x as u64, y as u64);
                    assert_eq!(
                        got_some,
                        Some(u16::checked_mul(x, y).is_some()),
                        "checked_mul u16 at ({x}, {y}): the tag must match `core`"
                    );
                    if let Some(want) = u16::checked_mul(x, y) {
                        assert_eq!(
                            got_val,
                            Some(want as u64),
                            "checked_mul u16 at ({x}, {y}): the payload must match `core`"
                        );
                    }
                    // The clamp is the predicate's other use, so a wrong `failure`
                    // would show here as a value rather than only a tag.
                    let (_, sat_val) = read(sat, ai, bi, x as u64, y as u64);
                    assert_eq!(
                        sat_val,
                        Some(u16::saturating_mul(x, y) as u64),
                        "saturating_mul u16 at ({x}, {y})"
                    );
                }
            }
        });
    }

    /// A `u32` product is modelled and exact, and a `u64` one is still refused.
    ///
    /// The bound is 32, so the widened test builds a 64-bit multiply here. The
    /// chosen values straddle the `u32` `MAX` boundary -- `65536` squares to
    /// exactly `2^32`, one past `MAX`, and `65535 * 65537` is one below it -- so a
    /// predicate that is off by one at the fencepost fails.
    #[test]
    fn a_u32_product_is_modelled_and_exact() {
        let vals: [u32; 14] = [
            0,
            1,
            2,
            255,
            65535,
            65536,
            65537,
            46341,
            0x8000_0000,
            0xffff_fffe,
            0xffff_ffff,
            12345,
            1_000_000,
            65_537,
        ];
        smt::with_fresh(|| {
            let a = smt::var(32);
            let b = smt::var(32);
            let (ai, bi) = (smt::index(a), smt::index(b));
            let checked = eval(Intrinsic::Checked(BinOp::Mul), a, b, 32, false, 32)
                .expect("checked_mul u32 must be modelled");
            let sat = eval(Intrinsic::Saturating(BinOp::Mul), a, b, 32, false, 32)
                .expect("saturating_mul u32 must be modelled");
            for &x in &vals {
                for &y in &vals {
                    let (got_some, got_val) = read(checked, ai, bi, x as u64, y as u64);
                    assert_eq!(
                        got_some,
                        Some(u32::checked_mul(x, y).is_some()),
                        "checked_mul u32 at ({x}, {y}): the tag must match `core`"
                    );
                    if let Some(want) = u32::checked_mul(x, y) {
                        assert_eq!(
                            got_val,
                            Some(want as u64),
                            "checked_mul u32 at ({x}, {y}): the payload must match `core`"
                        );
                    }
                    let (_, sat_val) = read(sat, ai, bi, x as u64, y as u64);
                    assert_eq!(
                        sat_val,
                        Some(u32::saturating_mul(x, y) as u64),
                        "saturating_mul u32 at ({x}, {y})"
                    );
                }
            }
        });
        // A `u64` product is past the widened test (`2w == 128` cannot be held), so
        // the model declines rather than building a term the blaster cannot take.
        assert!(eval(Intrinsic::Saturating(BinOp::Mul), smt::var(64), smt::var(64), 64, false, 64).is_none());
        assert!(!is_modelled(Intrinsic::Saturating(BinOp::Mul), 64, false));
    }

    /// Above the documented width limits the model declines rather than guessing.
    /// A declined model leaves the path unknown, which is the safe answer.
    #[test]
    fn past_the_width_limits_the_model_declines() {
        // Multiplication needs a `2w`-bit product; past `MUL_MAX_WIDTH` it declines.
        let mw = MUL_MAX_WIDTH + 1;
        assert!(eval(Intrinsic::Saturating(BinOp::Mul), smt::var(mw), smt::var(mw), mw, false, mw).is_none());
        // Division past `DIV_MAX_WIDTH` declines too.
        let dw = DIV_MAX_WIDTH + 1;
        assert!(eval(Intrinsic::Checked(BinOp::Div), smt::var(dw), smt::var(dw), dw, false, dw).is_none());
        // And the limits themselves are still modelled.
        assert!(eval(
            Intrinsic::Saturating(BinOp::Mul),
            smt::var(MUL_MAX_WIDTH),
            smt::var(MUL_MAX_WIDTH),
            MUL_MAX_WIDTH,
            false,
            MUL_MAX_WIDTH
        )
        .is_some());
        assert!(eval(
            Intrinsic::Checked(BinOp::Div),
            smt::var(DIV_MAX_WIDTH),
            smt::var(DIV_MAX_WIDTH),
            DIV_MAX_WIDTH,
            false,
            DIV_MAX_WIDTH
        )
        .is_some());
    }

    /// Walk every `w`-bit value and compare a unary model against Rust.
    ///
    /// The unary analogue of [`check`]: one operand, so one variable, and the
    /// result width is given separately because a bit count widens. `oracle`
    /// takes the operand's bit pattern and returns the expected result's bit
    /// pattern, calling the real `core` method so the expectation is not a second
    /// copy of the model.
    fn check_unary(
        op: Intrinsic,
        w: u8,
        result_w: u8,
        signed: bool,
        oracle: impl Fn(u64) -> u64,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let outcome = eval(op, a, a, w, signed, result_w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let ai = smt::index(a);
            for xb in 0..(1u64 << w) {
                let want = oracle(xb);
                let Outcome::Value(v) = outcome else {
                    panic!("{label} must produce a plain value");
                };
                let got = smt::evaluate(v, |i| if i == ai { Some(xb) } else { None });
                assert_eq!(
                    got,
                    Some(want),
                    "{label} at bits {xb}: the model says {got:?}, Rust says {want}"
                );
            }
        });
    }

    /// Walk every `w`-bit value and compare a unary `Option` model against Rust.
    ///
    /// `oracle` answers `Some(bits)` when the operation is defined and `None` when
    /// it is not, which is the shape a `checked_*` has. The tag is the model's
    /// "defined" bit and must agree with the oracle at every input -- a tag that
    /// says `Some` where Rust says `None` would let the `switchInt` take the wrong
    /// arm, and one that says `None` where Rust says `Some` would make a
    /// dischargeable obligation look unknown.
    fn check_unary_option(
        op: Intrinsic,
        w: u8,
        signed: bool,
        oracle: impl Fn(u64) -> Option<u64>,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let outcome = eval(op, a, a, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let ai = smt::index(a);
            for xb in 0..(1u64 << w) {
                let want = oracle(xb);
                let Outcome::Option { tag, payload } = outcome else {
                    panic!("{label} must produce an `Option`");
                };
                let got_tag = smt::evaluate(tag, |i| if i == ai { Some(xb) } else { None });
                let got_val = smt::evaluate(payload, |i| if i == ai { Some(xb) } else { None });
                match want {
                    Some(v) => {
                        assert_eq!(
                            got_tag,
                            Some(1),
                            "{label} at bits {xb}: Rust says `Some`, model says {got_tag:?}"
                        );
                        assert_eq!(
                            got_val,
                            Some(v),
                            "{label} at bits {xb}: the model says {got_val:?}, Rust says {v}"
                        );
                    }
                    None => {
                        assert_eq!(
                            got_tag,
                            Some(0),
                            "{label} at bits {xb}: Rust says `None`, model says {got_tag:?}"
                        );
                    }
                }
            }
        });
    }

    /// Walk every `w`-bit value and compare a unary `(T, bool)` model against Rust.
    ///
    /// `oracle` answers with the wrapped value and the flag, which is the pair
    /// `overflowing_*` returns. The value is checked at *every* input, not only
    /// where the flag is clear, because the wrapped value is defined everywhere --
    /// that is what "wrapping" means.
    fn check_unary_tuple(
        op: Intrinsic,
        w: u8,
        signed: bool,
        oracle: impl Fn(u64) -> (u64, bool),
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let outcome = eval(op, a, a, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let ai = smt::index(a);
            for xb in 0..(1u64 << w) {
                let (want_val, want_flag) = oracle(xb);
                let Outcome::Tuple { value, overflowed } = outcome else {
                    panic!("{label} must produce a tuple");
                };
                let env = |i: u32| if i == ai { Some(xb) } else { None };
                assert_eq!(
                    smt::evaluate(value, env),
                    Some(want_val),
                    "{label} at bits {xb}: value mismatch"
                );
                assert_eq!(
                    smt::evaluate_pred(overflowed, env),
                    Some(want_flag),
                    "{label} at bits {xb}: overflow flag mismatch"
                );
            }
        });
    }

    /// The bit counts agree with Rust at every width, `count_ones` included.
    ///
    /// The result type is wider than the operand (`u8` -> `u32`), which is the
    /// case the model has to widen; the same test at `result_w == w` covers the
    /// fixed-width reading. The exhaustive walk is what makes it a proof rather
    /// than a sample: every operand value is visited.
    #[test]
    fn the_bit_counts_agree_with_rust() {
        // The oracle is `core`'s own method, read at the *operand's* width rather
        // than at `u32`. A count is a function of the bits of the type, and the
        // width is part of the answer: `0u8.leading_zeros()` is `8` and
        // `0u32.leading_zeros()` is `32`, while a one-bit zero has `1` of each.
        // Both counts are therefore taken at 32 bits and then adjusted, and
        // `trailing_zeros` gets a sentinel bit above the operand so that an
        // all-zero operand counts its own width instead of running into the
        // sentinel.
        fn oracle(kind: BitKind, w: u8, b: u64) -> u64 {
            let mask = (1u32 << w) - 1;
            let v = (b as u32) & mask;
            // `core` defines each complement as the count of `!x`, so the oracle is
            // the same method on the complement. The complement must be taken *at
            // the operand's width* -- `!v` on a `u32` sets the bits above `w`, and
            // counting those would be counting bits the operand does not have.
            let c = !v & mask;
            match kind {
                BitKind::Ones => u64::from(v.count_ones()),
                BitKind::LeadingZeros => u64::from(v.leading_zeros() - (32 - u32::from(w))),
                BitKind::TrailingZeros => u64::from((v | (1u32 << w)).trailing_zeros()),
                BitKind::CountZeros => u64::from(c.count_ones()),
                BitKind::LeadingOnes => u64::from(c.leading_zeros() - (32 - u32::from(w))),
                BitKind::TrailingOnes => u64::from((c | (1u32 << w)).trailing_zeros()),
            }
        }
        for w in [1u8, 4, 8] {
            for (kind, name) in [
                (BitKind::Ones, "count_ones"),
                (BitKind::LeadingZeros, "leading_zeros"),
                (BitKind::TrailingZeros, "trailing_zeros"),
                (BitKind::CountZeros, "count_zeros"),
                (BitKind::LeadingOnes, "leading_ones"),
                (BitKind::TrailingOnes, "trailing_ones"),
            ] {
                let f = move |b: u64| oracle(kind, w, b);
                check_unary(
                    Intrinsic::Bits(kind),
                    w,
                    32,
                    false,
                    f,
                    &format!("{name} (widened to u32)"),
                );
                check_unary(
                    Intrinsic::Bits(kind),
                    w,
                    w,
                    false,
                    f,
                    &format!("{name} (at operand width)"),
                );
            }
        }
    }

    /// The 64-bit bit counts, checked at chosen operands rather than by walking.
    ///
    /// `the_bit_counts_agree_with_rust` walks the whole domain, which is only
    /// possible up to 32 bits (`0..(1u64 << w)`). 64 bits is exactly where the
    /// mask construction is delicate: `trailing_zeros` builds `2^k - 1` with a
    /// *host* shift, and its last step is `k == w`, so at 64 bits that step is
    /// `1u64 << 64` -- a panic under overflow checks and, without them, an
    /// all-zero mask that makes `x & mask == 0` true for every operand, so every
    /// count comes back one too large (`0u64.trailing_zeros()` would read `65`,
    /// not `64`). The mask is now `all_ones(w)` at that step, and this pins the
    /// shape at the one width the exhaustive walk cannot reach.
    ///
    /// The operands are the ones that separate the answers: `0` (every bit of the
    /// operand is the counted kind), all ones (none is), `1` and `1 << 63` (one
    /// bit of each kind at each end), and a mixed pattern.
    #[test]
    fn the_64_bit_counts_agree_with_rust() {
        let operands = [
            0u64,
            u64::MAX,
            1,
            1u64 << 63,
            0x8000_0000_0000_0001,
            0x0000_ffff_ffff_0000,
        ];
        let check = |kind: BitKind, name: &str, oracle: fn(u64) -> u64| {
            smt::with_fresh(|| {
                let a = smt::var(64);
                let ai = smt::index(a);
                let outcome = eval(Intrinsic::Bits(kind), a, a, 64, false, 64)
                    .unwrap_or_else(|| panic!("{name} at 64 bits must be modelled"));
                let Outcome::Value(v) = outcome else {
                    panic!("{name} must produce a plain value");
                };
                for xb in operands {
                    let want = oracle(xb);
                    let got = smt::evaluate(v, |i| if i == ai { Some(xb) } else { None });
                    assert_eq!(
                        got,
                        Some(want),
                        "{name} at bits {xb:#x}: the model says {got:?}, Rust says {want}"
                    );
                }
            });
        };
        check(BitKind::Ones, "count_ones", |v| u64::from(v.count_ones()));
        check(BitKind::CountZeros, "count_zeros", |v| u64::from(v.count_zeros()));
        check(BitKind::LeadingZeros, "leading_zeros", |v| u64::from(v.leading_zeros()));
        check(BitKind::LeadingOnes, "leading_ones", |v| u64::from(v.leading_ones()));
        check(BitKind::TrailingZeros, "trailing_zeros", |v| u64::from(v.trailing_zeros()));
        check(BitKind::TrailingOnes, "trailing_ones", |v| u64::from(v.trailing_ones()));
    }

    /// Walk every `w`-bit value and compare a `bool`-valued model against Rust.
    ///
    /// The oracle answers with `core`'s own `bool`, so the expectation is never a
    /// copy of the model. This is the sharpest of the three channels: a
    /// `count_zeros` read as `count_ones` is a *wrong number*, but an
    /// `is_power_of_two` read as its negation, or with the `x != 0` conjunct
    /// dropped, is a wrong *branch* -- the `if` that consumes it takes the other
    /// arm, and a proof built on it is a proof about the wrong program.
    fn check_bool(
        op: Intrinsic,
        w: u8,
        signed: bool,
        oracle: impl Fn(u64) -> bool,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let outcome = eval(op, a, a, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let ai = smt::index(a);
            for xb in 0..(1u64 << w) {
                let want = oracle(xb);
                let Outcome::Bool(p) = outcome else {
                    panic!("{label} must produce a `bool`");
                };
                let got = smt::evaluate_pred(p, |i| if i == ai { Some(xb) } else { None });
                assert_eq!(
                    got,
                    Some(want),
                    "{label} at bits {xb}: the model says {got:?}, Rust says {want}"
                );
            }
        });
    }

    /// `is_power_of_two` agrees with Rust over whole `u8` and `u16` domains.
    ///
    /// The oracle is `core`'s own method rather than the mask trick the model
    /// uses, so a mistake in the trick is visible instead of being reproduced.
    /// The interesting inputs are named rather than only swept: `0` is not a
    /// power of two (the one value the bare `x & (x - 1)` test would accept),
    /// `1` is (`1 << 0`), the top bit is, and `127` and `255` are not.
    #[test]
    fn is_power_of_two_agrees_with_rust() {
        for w in [8u8, 16] {
            let oracle = move |b: u64| match w {
                8 => u8::try_from(b).unwrap().is_power_of_two(),
                16 => u16::try_from(b).unwrap().is_power_of_two(),
                _ => unreachable!("the test walks 8 and 16 bits"),
            };
            check_bool(Intrinsic::Bool(BoolKind::PowerOfTwo), w, false, oracle, "is_power_of_two");
        }
        // The named points, at 8 bits, so a failure names the value that broke
        // rather than only the width.
        let p = |b: u64| {
            smt::with_fresh(|| {
                let a = smt::var(8);
                let Outcome::Bool(p) =
                    eval(Intrinsic::Bool(BoolKind::PowerOfTwo), a, a, 8, false, 8)
                        .expect("is_power_of_two at 8 bits must be modelled")
                else {
                    panic!("is_power_of_two must produce a `bool`");
                };
                let ai = smt::index(a);
                smt::evaluate_pred(p, |i| if i == ai { Some(b) } else { None })
            })
        };
        for (b, want, why) in [
            (0u64, false, "zero is not a power of two"),
            (1, true, "one is 1 << 0"),
            (2, true, "two is 1 << 1"),
            (127, false, "seven set bits"),
            (128, true, "the top bit is 1 << 7"),
            (255, false, "eight set bits"),
        ] {
            assert_eq!(p(b), Some(want), "{why} (at bits {b})");
        }
    }

    /// `is_negative`/`is_positive` agree with Rust over whole `i8`/`i16` domains.
    ///
    /// The oracle is `core`'s own method. The named points are the ones a wrong
    /// reading gets wrong: `i8::MIN` (`0x80`) is *negative* though its bits are the
    /// largest unsigned byte, so an unsigned model would call it positive; `0` is
    /// neither; and `i8::MAX` is positive. A signedness check is what the sweep is
    /// for -- an unsigned reading is caught at `0x80`.
    #[test]
    fn the_sign_predicates_agree_with_rust() {
        for w in [8u8, 16] {
            let neg = move |b: u64| match w {
                8 => (b as u8 as i8).is_negative(),
                16 => (b as u16 as i16).is_negative(),
                _ => unreachable!("the test walks 8 and 16 bits"),
            };
            let pos = move |b: u64| match w {
                8 => (b as u8 as i8).is_positive(),
                16 => (b as u16 as i16).is_positive(),
                _ => unreachable!("the test walks 8 and 16 bits"),
            };
            check_bool(Intrinsic::Bool(BoolKind::Negative), w, true, neg, "is_negative");
            check_bool(Intrinsic::Bool(BoolKind::Positive), w, true, pos, "is_positive");
        }
        // The named points at 8 bits, so a failure names the value that broke.
        let ev = |kind: BoolKind, b: u64| {
            smt::with_fresh(|| {
                let a = smt::var(8);
                let Outcome::Bool(p) = eval(Intrinsic::Bool(kind), a, a, 8, true, 8)
                    .expect("a sign predicate at 8 bits must be modelled")
                else {
                    panic!("a sign predicate must produce a `bool`");
                };
                let ai = smt::index(a);
                smt::evaluate_pred(p, |i| if i == ai { Some(b) } else { None })
            })
        };
        for (bits, neg, pos, why) in [
            (0u64, false, false, "zero is neither negative nor positive"),
            (1, false, true, "one is positive"),
            (0x7f, false, true, "i8::MAX is positive"),
            (0x80, true, false, "i8::MIN is negative -- an unsigned read would call it positive"),
            (0xff, true, false, "-1 is negative"),
        ] {
            assert_eq!(
                ev(BoolKind::Negative, bits),
                Some(neg),
                "is_negative {why} (at bits {bits:#x})"
            );
            assert_eq!(
                ev(BoolKind::Positive, bits),
                Some(pos),
                "is_positive {why} (at bits {bits:#x})"
            );
        }
    }

    /// Every ASCII class agrees with Rust's own `u8` method over the whole byte
    /// range.
    ///
    /// The oracle is `core` itself, walked exhaustively over `0..=255`, so the
    /// model's range boundaries are checked against the standard library's rather
    /// than against the same constants written twice. Each class has its own
    /// method, and the two that are easy to get wrong are named in the list: the
    /// whitespace set excludes vertical tab, and punctuation excludes the space.
    #[test]
    fn the_ascii_classes_agree_with_rust() {
        type Case = (AsciiKind, fn(u8) -> bool, &'static str);
        let classes: [Case; 10] = [
            (AsciiKind::Digit, |b| b.is_ascii_digit(), "is_ascii_digit"),
            (AsciiKind::Alphabetic, |b| b.is_ascii_alphabetic(), "is_ascii_alphabetic"),
            (AsciiKind::Alphanumeric, |b| b.is_ascii_alphanumeric(), "is_ascii_alphanumeric"),
            (AsciiKind::Uppercase, |b| b.is_ascii_uppercase(), "is_ascii_uppercase"),
            (AsciiKind::Lowercase, |b| b.is_ascii_lowercase(), "is_ascii_lowercase"),
            (AsciiKind::HexDigit, |b| b.is_ascii_hexdigit(), "is_ascii_hexdigit"),
            (AsciiKind::Whitespace, |b| b.is_ascii_whitespace(), "is_ascii_whitespace"),
            (AsciiKind::Punctuation, |b| b.is_ascii_punctuation(), "is_ascii_punctuation"),
            (AsciiKind::Control, |b| b.is_ascii_control(), "is_ascii_control"),
            (AsciiKind::Ascii, |b| b.is_ascii(), "is_ascii"),
        ];
        for (kind, oracle, label) in classes {
            check_bool(
                Intrinsic::Bool(BoolKind::Ascii(kind)),
                8,
                false,
                |b: u64| oracle(b as u8),
                label,
            );
        }
        // The two boundaries a copied constant list gets wrong, pinned by value so
        // a failure names the byte rather than only the class.
        let p = |kind: AsciiKind, b: u64| {
            smt::with_fresh(|| {
                let a = smt::var(8);
                let Outcome::Bool(p) = eval(Intrinsic::Bool(BoolKind::Ascii(kind)), a, a, 8, false, 8)
                    .expect("an ASCII class at 8 bits must be modelled")
                else {
                    panic!("an ASCII class must produce a `bool`");
                };
                let ai = smt::index(a);
                smt::evaluate_pred(p, |i| if i == ai { Some(b) } else { None })
            })
        };
        for (kind, b, want, why) in [
            (AsciiKind::Whitespace, 0x0b, false, "vertical tab is not ASCII whitespace"),
            (AsciiKind::Whitespace, b' ' as u64, true, "space is whitespace"),
            (AsciiKind::Punctuation, b' ' as u64, false, "space is not punctuation"),
            (AsciiKind::Punctuation, b'!' as u64, true, "`!` is punctuation"),
            (AsciiKind::Control, 0x1f, true, "the last C0 control"),
            (AsciiKind::Control, 0x20, false, "space is the first printable"),
            (AsciiKind::Control, 0x7f, true, "DEL is a control"),
            (AsciiKind::Control, 0x80, false, "0x80 is not a control"),
            (AsciiKind::Ascii, 0x7f, true, "DEL is ASCII"),
            (AsciiKind::Ascii, 0x80, false, "0x80 is not ASCII"),
        ] {
            assert_eq!(p(kind, b), Some(want), "{why} (0x{b:02x})");
        }
    }

    /// The ASCII classes are refused on a signed or wider operand, where `core`
    /// has no such method.
    ///
    /// They exist only on `u8`, so an `i8` or `u16` receiver is a different method
    /// (or not a method), and modelling it as the byte test would answer a call
    /// `core` does not define.
    #[test]
    fn the_ascii_classes_are_refused_off_u8() {
        let digit = Intrinsic::Bool(BoolKind::Ascii(AsciiKind::Digit));
        assert!(is_modelled(digit, 8, false));
        assert!(!is_modelled(digit, 8, true));
        assert!(!is_modelled(digit, 16, false));
        assert!(eval(digit, smt::var(8), smt::var(8), 8, true, 8).is_none());
        assert!(eval(digit, smt::var(16), smt::var(16), 16, false, 16).is_none());
    }

    /// `is_power_of_two` is refused on a signed operand, where `core` has no such
    /// method.
    ///
    /// The refusal is the sound answer: read at the *bits*, `i8::MIN` is `1 << 7`
    /// and would be accepted, but its value is negative, and once only the sign
    /// flag survives there is no way to tell it from an unsigned `128`. Refusing
    /// rather than guessing is what keeps the model from proving a signed reading
    /// that `core` does not define.
    #[test]
    fn is_power_of_two_is_refused_when_signed() {
        assert!(is_modelled(Intrinsic::Bool(BoolKind::PowerOfTwo), 8, false));
        assert!(!is_modelled(Intrinsic::Bool(BoolKind::PowerOfTwo), 8, true));
        assert!(eval(Intrinsic::Bool(BoolKind::PowerOfTwo), smt::var(8), smt::var(8), 8, true, 8)
            .is_none());
    }

    /// Every unary operator in every family agrees with Rust over a whole `i8`.
    ///
    /// `MIN` is the interesting point for all of them: its magnitude is not
    /// representable, so `neg` has no result, `abs` has no result, `saturating`
    /// clamps to `MAX`, `wrapping` returns `MIN`, `checked` returns `None` and
    /// `overflowing` reports the flag. One exhaustive walk per method is what
    /// proves the four families agree with `core` at that point *and* everywhere
    /// else, rather than only at the point that was reasoned about.
    #[test]
    fn the_signed_unary_families_agree_with_rust() {
        let x = |b: u64| i8::from_ne_bytes([b as u8]);
        let bits = |v: i8| v as u8 as u64;
        check_unary(
            Intrinsic::Unary(Family::Wrapping, UnOp::Neg),
            8,
            8,
            true,
            |b| bits(x(b).wrapping_neg()),
            "wrapping_neg i8",
        );
        check_unary(
            Intrinsic::Unary(Family::Saturating, UnOp::Neg),
            8,
            8,
            true,
            |b| bits(x(b).saturating_neg()),
            "saturating_neg i8",
        );
        check_unary_option(
            Intrinsic::Unary(Family::Checked, UnOp::Neg),
            8,
            true,
            |b| x(b).checked_neg().map(bits),
            "checked_neg i8",
        );
        check_unary_tuple(
            Intrinsic::Unary(Family::Overflowing, UnOp::Neg),
            8,
            true,
            |b| {
                let (v, o) = x(b).overflowing_neg();
                (bits(v), o)
            },
            "overflowing_neg i8",
        );
        check_unary(
            Intrinsic::Unary(Family::Wrapping, UnOp::Abs),
            8,
            8,
            true,
            |b| bits(x(b).wrapping_abs()),
            "wrapping_abs i8",
        );
        check_unary(
            Intrinsic::Unary(Family::Saturating, UnOp::Abs),
            8,
            8,
            true,
            |b| bits(x(b).saturating_abs()),
            "saturating_abs i8",
        );
        check_unary_option(
            Intrinsic::Unary(Family::Checked, UnOp::Abs),
            8,
            true,
            |b| x(b).checked_abs().map(bits),
            "checked_abs i8",
        );
        check_unary_tuple(
            Intrinsic::Unary(Family::Overflowing, UnOp::Abs),
            8,
            true,
            |b| {
                let (v, o) = x(b).overflowing_abs();
                (bits(v), o)
            },
            "overflowing_abs i8",
        );
    }

    /// Unsigned negation is modelled, and its failure case is `x != 0`.
    ///
    /// This is the case a "neg is signed" assumption would have refused
    /// outright. `u8::wrapping_neg` is the modular negation, `checked_neg` is
    /// `None` for every `x != 0`, and `overflowing_neg` reports the flag for the
    /// same set. `saturating_neg` does *not* exist unsigned, so `is_modelled`
    /// refuses it -- the one asymmetry between the families, and the reason the
    /// model reads the sign rather than assuming one.
    #[test]
    fn unsigned_negation_is_modelled_except_where_the_method_does_not_exist() {
        let bits = |v: u8| u64::from(v);
        check_unary(
            Intrinsic::Unary(Family::Wrapping, UnOp::Neg),
            8,
            8,
            false,
            |b| bits((b as u8).wrapping_neg()),
            "wrapping_neg u8",
        );
        check_unary_option(
            Intrinsic::Unary(Family::Checked, UnOp::Neg),
            8,
            false,
            |b| (b as u8).checked_neg().map(bits),
            "checked_neg u8",
        );
        check_unary_tuple(
            Intrinsic::Unary(Family::Overflowing, UnOp::Neg),
            8,
            false,
            |b| {
                let (v, o) = (b as u8).overflowing_neg();
                (bits(v), o)
            },
            "overflowing_neg u8",
        );
        // The members that do not exist on an unsigned type are refused.
        assert!(!is_modelled(Intrinsic::Unary(Family::Saturating, UnOp::Neg), 8, false));
        assert!(!is_modelled(Intrinsic::Unary(Family::Wrapping, UnOp::Abs), 8, false));
        assert!(!is_modelled(Intrinsic::Unary(Family::Checked, UnOp::Abs), 8, false));
        assert!(!is_modelled(Intrinsic::Unary(Family::Overflowing, UnOp::Abs), 8, false));
        // And they *are* modelled on a signed type.
        assert!(is_modelled(Intrinsic::Unary(Family::Saturating, UnOp::Neg), 8, true));
        assert!(is_modelled(Intrinsic::Unary(Family::Wrapping, UnOp::Abs), 8, true));
    }

    /// The unary shapes classify, and the names that only *look* like them do not.
    ///
    /// The family split must produce a `Unary` for `neg`/`abs` and a `BinOp` for
    /// everything else, so the near misses are the ones that would be read as the
    /// wrong shape: `neg_signed` is not an operator, `abs` without a prefix is not
    /// a method, and `pow` has no model yet.
    #[test]
    fn the_unary_names_classify_and_their_neighbours_do_not() {
        assert_eq!(
            classify("core::num::<impl i8>::wrapping_neg"),
            Some(Intrinsic::Unary(Family::Wrapping, UnOp::Neg))
        );
        assert_eq!(classify("wrapping_abs"), Some(Intrinsic::Unary(Family::Wrapping, UnOp::Abs)));
        assert_eq!(
            classify("core::num::<impl u8>::overflowing_neg"),
            Some(Intrinsic::Unary(Family::Overflowing, UnOp::Neg))
        );
        assert_eq!(
            classify("saturating_abs"),
            Some(Intrinsic::Unary(Family::Saturating, UnOp::Abs))
        );
        // `neg`/`abs` are *not* read as a `BinOp` operator.
        assert_eq!(classify("checked_neg"), Some(Intrinsic::Unary(Family::Checked, UnOp::Neg)));
        assert_ne!(classify("checked_neg"), Some(Intrinsic::Checked(BinOp::Add)));
        // The plain `abs` is now its own shape (it panics at `MIN`), so it is
        // matched before the prefix split; the families' `wrapping_abs` etc. are
        // still read by the split. The plain `neg` stays unmodelled: `neg` is
        // only a family member, never an inherent method.
        assert_eq!(classify("abs"), Some(Intrinsic::Abs));
        assert!(classify("neg").is_none());
        assert!(classify("wrapping_neg_signed").is_none());
        assert!(classify("checked_abs_signed").is_none());
        // `pow` classifies now (as `Intrinsic::Pow`, its own shape), so the
        // unmodelled examples here are the names that stay unmodelled.
        assert!(classify("powf").is_none());
        assert!(classify("count_ones_signed").is_none());
        // `count_zeros` is modelled now; the near miss that stays unmodelled is
        // the signed spelling, which is not a real method name.
        assert_eq!(classify("count_zeros"), Some(Intrinsic::Bits(BitKind::CountZeros)));
        assert!(classify("count_zeros_signed").is_none());
    }

    /// The bit-count names classify as counts and not as anything else.
    #[test]
    fn the_bit_count_names_classify() {
        assert_eq!(classify("core::num::<impl u8>::count_ones"), Some(Intrinsic::Bits(BitKind::Ones)));
        assert_eq!(classify("count_ones"), Some(Intrinsic::Bits(BitKind::Ones)));
        assert_eq!(classify("leading_zeros"), Some(Intrinsic::Bits(BitKind::LeadingZeros)));
        assert_eq!(classify("trailing_zeros"), Some(Intrinsic::Bits(BitKind::TrailingZeros)));
        assert_eq!(classify("count_zeros"), Some(Intrinsic::Bits(BitKind::CountZeros)));
        assert_eq!(classify("leading_ones"), Some(Intrinsic::Bits(BitKind::LeadingOnes)));
        assert_eq!(classify("trailing_ones"), Some(Intrinsic::Bits(BitKind::TrailingOnes)));
        // The six are distinct: a `count_zeros` read as `count_ones` would be the
        // *complement* of the right answer, which is a wrong value rather than a
        // refusal.
        assert_ne!(classify("count_zeros"), Some(Intrinsic::Bits(BitKind::Ones)));
        assert_ne!(classify("leading_ones"), Some(Intrinsic::Bits(BitKind::LeadingZeros)));
        assert_ne!(classify("trailing_ones"), Some(Intrinsic::Bits(BitKind::TrailingZeros)));
        // A near miss that is still refused: the `_signed` spellings are not
        // `core` methods.
        assert!(classify("leading_ones_signed").is_none());
    }

    /// `is_power_of_two` classifies as a `bool` predicate, and only that name does.
    #[test]
    fn the_bool_predicate_names_classify() {
        assert_eq!(
            classify("core::num::<impl u32>::is_power_of_two"),
            Some(Intrinsic::Bool(BoolKind::PowerOfTwo))
        );
        assert_eq!(classify("is_power_of_two"), Some(Intrinsic::Bool(BoolKind::PowerOfTwo)));
        // Distinct from the numeric shapes: a `bool` read as a value would write
        // a one-bit word into a `bool` local, which no `if` could read.
        assert_ne!(classify("is_power_of_two"), Some(Intrinsic::Bits(BitKind::Ones)));
        // The ASCII classes are `Bool` too, and each maps to its own variant --
        // a name matched by prefix would confuse `is_ascii` with `is_ascii_digit`.
        assert_eq!(
            classify("core::num::<impl u8>::is_ascii_digit"),
            Some(Intrinsic::Bool(BoolKind::Ascii(AsciiKind::Digit)))
        );
        assert_eq!(
            classify("core::num::<impl u8>::is_ascii_alphanumeric"),
            Some(Intrinsic::Bool(BoolKind::Ascii(AsciiKind::Alphanumeric)))
        );
        assert_eq!(
            classify("core::num::<impl u8>::is_ascii"),
            Some(Intrinsic::Bool(BoolKind::Ascii(AsciiKind::Ascii)))
        );
        assert_ne!(
            classify("is_ascii"),
            Some(Intrinsic::Bool(BoolKind::Ascii(AsciiKind::Digit)))
        );
        // Near misses that stay refused. `is_power_of_two` on the signed types is
        // not a `core` method; the other `is_*` predicates are not modelled. The
        // sign predicates *are* modelled now (see `the_sign_predicates_agree_with_rust`),
        // so they are checked as present rather than as near misses.
        assert!(classify("is_power_of_two_signed").is_none());
        assert_eq!(classify("is_negative"), Some(Intrinsic::Bool(BoolKind::Negative)));
        assert_eq!(classify("is_positive"), Some(Intrinsic::Bool(BoolKind::Positive)));
        // The slice shapes are matched on the *path*, so a `Vec`'s `len` is not
        // read as a slice length.
        assert_eq!(classify("core::slice::<impl [u8]>::len"), Some(Intrinsic::SliceLen));
        assert_eq!(classify("core::slice::<impl [u8]>::is_empty"), Some(Intrinsic::SliceIsEmpty));
        assert!(classify("alloc::vec::Vec<u8>::len").is_none());
        assert!(classify("Vec::<u8>::len").is_none());
        assert!(classify("str::len").is_none());
        // `abs_diff` and the rotations are matched by their exact tail, so a
        // longer name that merely starts the same way is refused rather than read
        // as the shorter one.
        assert_eq!(classify("core::num::<impl u8>::abs_diff"), Some(Intrinsic::AbsDiff));
        assert_eq!(
            classify("core::num::<impl u8>::rotate_left"),
            Some(Intrinsic::Rotate(RotateKind::Left))
        );
        assert_eq!(
            classify("core::num::<impl i32>::rotate_right"),
            Some(Intrinsic::Rotate(RotateKind::Right))
        );
        assert!(classify("rotate_left_signed").is_none());
        assert!(classify("abs_diff_thing").is_none());
    }
    /// The module header's "what is modelled" list must match the tables below it.
    ///
    /// The header claimed `abs_diff`, `rotate_*` and `is_ascii_*` "remain absent"
    /// while all four were modelled -- a doc claim that drifted from the code, the
    /// class of defect the README warns about. This pins the four spellings, so a
    /// later removal cannot leave the prose behind again.
    #[test]
    fn the_documented_modelled_set_matches_classify() {
        assert_eq!(classify("core::num::<impl u8>::abs_diff"), Some(Intrinsic::AbsDiff));
        assert_eq!(
            classify("core::num::<impl u8>::rotate_left"),
            Some(Intrinsic::Rotate(RotateKind::Left))
        );
        assert_eq!(
            classify("core::num::<impl u8>::rotate_right"),
            Some(Intrinsic::Rotate(RotateKind::Right))
        );
        // All ten ASCII classes, so "the ten `is_ascii_*` classes" is a count a
        // reader can check rather than a number to trust.
        for name in [
            "is_ascii_digit",
            "is_ascii_alphabetic",
            "is_ascii_alphanumeric",
            "is_ascii_uppercase",
            "is_ascii_lowercase",
            "is_ascii_hexdigit",
            "is_ascii_whitespace",
            "is_ascii_punctuation",
            "is_ascii_control",
            "is_ascii",
        ] {
            assert!(
                classify(&format!("core::num::<impl u8>::{name}")).is_some(),
                "the header says `{name}` is modelled, so it must classify"
            );
        }
        // The sign predicates the header names alongside the ASCII classes.
        assert_eq!(
            classify("core::num::<impl i8>::is_negative"),
            Some(Intrinsic::Bool(BoolKind::Negative))
        );
        assert_eq!(
            classify("core::num::<impl i8>::is_positive"),
            Some(Intrinsic::Bool(BoolKind::Positive))
        );
        // The inherent `abs`/`unsigned_abs`: the same magnitude, one panicking at
        // `MIN` and one total, so they are distinct shapes rather than one.
        assert_eq!(classify("core::num::<impl i32>::abs"), Some(Intrinsic::Abs));
        assert_eq!(
            classify("core::num::<impl i32>::unsigned_abs"),
            Some(Intrinsic::UnsignedAbs)
        );
    }

    /// The unary shapes are `is_unary`; the two-operand families are not.
    ///
    /// The executor branches on this to decide whether to read a second operand,
    /// so a family wrongly reported unary would read one argument and mis-shape
    /// every call, and a unary shape wrongly reported binary would refuse every
    /// call for missing its second argument.
    #[test]
    fn only_the_unary_shapes_are_unary() {
        assert!(Intrinsic::Bits(BitKind::Ones).is_unary());
        assert!(Intrinsic::Bool(BoolKind::PowerOfTwo).is_unary());
        assert!(Intrinsic::Unary(Family::Wrapping, UnOp::Neg).is_unary());
        assert!(Intrinsic::Unary(Family::Checked, UnOp::Abs).is_unary());
        assert!(!Intrinsic::Wrapping(BinOp::Add).is_unary());
        assert!(!Intrinsic::Saturating(BinOp::Sub).is_unary());
        assert!(!Intrinsic::Checked(BinOp::Mul).is_unary());
        assert!(!Intrinsic::Overflowing(BinOp::Add).is_unary());
        // A mixed-signedness addition takes two operands, so it must *not* be
        // reported unary: the executor would read one argument and mis-shape it.
        assert!(!Intrinsic::MixedAdd(Family::Wrapping).is_unary());
    }

    /// The `add_signed`/`add_unsigned` names classify into the four families, and
    /// no other spelling does.
    #[test]
    fn the_mixed_add_names_classify() {
        assert_eq!(
            classify("core::num::<impl u8>::wrapping_add_signed"),
            Some(Intrinsic::MixedAdd(Family::Wrapping))
        );
        assert_eq!(
            classify("saturating_add_signed"),
            Some(Intrinsic::MixedAdd(Family::Saturating))
        );
        assert_eq!(classify("checked_add_signed"), Some(Intrinsic::MixedAdd(Family::Checked)));
        assert_eq!(
            classify("overflowing_add_signed"),
            Some(Intrinsic::MixedAdd(Family::Overflowing))
        );
        // The `_unsigned` spelling is the same shape: the direction is read from
        // the operands, not from the name.
        assert_eq!(
            classify("core::num::<impl i8>::wrapping_add_unsigned"),
            Some(Intrinsic::MixedAdd(Family::Wrapping))
        );
        assert_eq!(
            classify("overflowing_add_unsigned"),
            Some(Intrinsic::MixedAdd(Family::Overflowing))
        );
        // The bare `add_signed` is not a `core` name -- every method carries a
        // family prefix -- so it does not classify.
        assert!(classify("add_signed").is_none());
        assert!(classify("add_unsigned").is_none());
    }

    /// Walk every `u8`/`i8` pair of a mixed-signedness addition against `core`.
    ///
    /// The two operands have opposite signedness, so the generic [`check`] and
    /// [`check_tuple`] helpers do not fit: they read both operands at the same
    /// width *and* the same signedness. Here the first operand is read at the
    /// method's own sign and the second at the opposite, and `core`'s own method
    /// is the oracle in both directions.
    ///
    /// `self_is_unsigned` says which direction is under test, and it must agree
    /// with the `signed` flag handed to `eval`: the flag is the sign of the
    /// operand with the method's own type, so `u8::add_signed` passes `false` and
    /// `i8::add_unsigned` passes `true`. Passing the other one is the bug the
    /// whole `signed_operand` selection exists to prevent, so it is what the two
    /// calls below vary.
    fn check_mixed(
        op: Intrinsic,
        self_is_unsigned: bool,
        rust: impl Fn(u64, u64) -> (Option<bool>, Option<u64>),
        label: &str,
    ) {
        let w = 8u8;
        smt::with_fresh(|| {
            let a = smt::var(w);
            let b = smt::var(w);
            // `signed` is the *self* operand's sign, which is the opposite of the
            // addend's.
            let signed = !self_is_unsigned;
            let outcome = eval(op, a, b, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(w, |xb, yb| {
                let (want_tag, want_val) = rust(xb, yb);
                let (got_tag, got_val) = read(outcome, ai, bi, xb, yb);
                assert_eq!(
                    (got_tag, got_val),
                    (want_tag, want_val),
                    "{label} at (self={xb}, addend={yb}): the model says \
                     ({got_tag:?}, {got_val:?}), Rust says ({want_tag:?}, {want_val:?})"
                );
            });
        });
    }

    /// `u8::wrapping_add_signed` and `i8::wrapping_add_unsigned` agree with `core`.
    #[test]
    fn the_wrapping_mixed_adds_agree_with_rust() {
        // `u8` self, `i8` addend: the addend's bits are its two's-complement
        // image, and the value is the plain wrapped sum.
        check_mixed(
            Intrinsic::MixedAdd(Family::Wrapping),
            true,
            |xb, yb| {
                let (x, r) = (xb as u8, yb as u8 as i8);
                (None, Some(u64::from(x.wrapping_add_signed(r))))
            },
            "wrapping_add_signed u8",
        );
        // `i8` self, `u8` addend.
        check_mixed(
            Intrinsic::MixedAdd(Family::Wrapping),
            false,
            |xb, yb| {
                let (x, r) = (xb as u8 as i8, yb as u8);
                (None, Some(x.wrapping_add_unsigned(r) as u8 as u64))
            },
            "wrapping_add_unsigned i8",
        );
    }

    /// The `overflowing` mixed additions agree with `core` on *both* the value and
    /// the flag, over the whole `u8`/`i8` domain.
    ///
    /// The flag is the sharp part: it is not the ordinary signed-addition rule, so
    /// a model that reached for that rule would agree on the value everywhere and
    /// disagree on the flag for half the domain. The oracle is `core`'s own
    /// `overflowing_*`, so the expectation is never a copy of the model.
    #[test]
    fn the_overflowing_mixed_adds_agree_with_rust() {
        check_mixed(
            Intrinsic::MixedAdd(Family::Overflowing),
            true,
            |xb, yb| {
                let (x, r) = (xb as u8, yb as u8 as i8);
                let (v, o) = x.overflowing_add_signed(r);
                (Some(o), Some(u64::from(v)))
            },
            "overflowing_add_signed u8",
        );
        check_mixed(
            Intrinsic::MixedAdd(Family::Overflowing),
            false,
            |xb, yb| {
                let (x, r) = (xb as u8 as i8, yb as u8);
                let (v, o) = x.overflowing_add_unsigned(r);
                (Some(o), Some(v as u8 as u64))
            },
            "overflowing_add_unsigned i8",
        );
    }

    /// The `checked` mixed additions agree with `core`'s `Option`, so `None` is
    /// exactly where the operation is undefined.
    #[test]
    fn the_checked_mixed_adds_agree_with_rust() {
        check_mixed(
            Intrinsic::MixedAdd(Family::Checked),
            true,
            |xb, yb| {
                let (x, r) = (xb as u8, yb as u8 as i8);
                match x.checked_add_signed(r) {
                    Some(v) => (Some(true), Some(u64::from(v))),
                    None => (Some(false), Some(u64::from(x.wrapping_add_signed(r)))),
                }
            },
            "checked_add_signed u8",
        );
        check_mixed(
            Intrinsic::MixedAdd(Family::Checked),
            false,
            |xb, yb| {
                let (x, r) = (xb as u8 as i8, yb as u8);
                match x.checked_add_unsigned(r) {
                    Some(v) => (Some(true), Some(v as u8 as u64)),
                    None => (Some(false), Some(x.wrapping_add_unsigned(r) as u8 as u64)),
                }
            },
            "checked_add_unsigned i8",
        );
    }

    /// The `saturating` mixed additions agree with `core`, including the two
    /// *different* clamps the two directions use.
    #[test]
    fn the_saturating_mixed_adds_agree_with_rust() {
        // `u8` self: clamps to `0` for a negative addend and `MAX` for a
        // non-negative one, so both ends are exercised by the sweep.
        check_mixed(
            Intrinsic::MixedAdd(Family::Saturating),
            true,
            |xb, yb| {
                let (x, r) = (xb as u8, yb as u8 as i8);
                (None, Some(u64::from(x.saturating_add_signed(r))))
            },
            "saturating_add_signed u8",
        );
        // `i8` self: the addend is unsigned, so it can only run off the top and
        // the clamp is always `MAX`. A model that reused the `u8` clamp would
        // return `0` on the wrap and disagree here.
        check_mixed(
            Intrinsic::MixedAdd(Family::Saturating),
            false,
            |xb, yb| {
                let (x, r) = (xb as u8 as i8, yb as u8);
                (None, Some(x.saturating_add_unsigned(r) as u8 as u64))
            },
            "saturating_add_unsigned i8",
        );
    }

    /// `Ord::min`/`Ord::max` classify only under the standard library's `Ord`.
    #[test]
    fn the_ord_names_classify_and_their_neighbours_do_not() {
        assert_eq!(classify("<u8 as Ord>::min"), Some(Intrinsic::MinMax(MinMaxKind::Min)));
        assert_eq!(classify("<u8 as Ord>::max"), Some(Intrinsic::MinMax(MinMaxKind::Max)));
        assert_eq!(classify("<i8 as Ord>::min"), Some(Intrinsic::MinMax(MinMaxKind::Min)));
        assert_eq!(classify("<i8 as Ord>::max"), Some(Intrinsic::MinMax(MinMaxKind::Max)));
        // `min` and `max` are distinct shapes: reading `max` as `min` returns the
        // other operand, a wrong value rather than a refusal.
        assert_ne!(classify("<u8 as Ord>::max"), Some(Intrinsic::MinMax(MinMaxKind::Min)));
        // A different trait's `min` is refused. The trait path is the only thing
        // distinguishing `Ord`'s from another trait's, and a local trait in a
        // module spells its call `<u8 as m::Ord>::min` -- a path that is not `Ord`.
        assert!(classify("<u8 as m::Ord>::min").is_none());
        assert!(classify("<u8 as MyOrd>::min").is_none());
        assert!(classify("<u8 as ord_shim::Ord>::min").is_none());
        // `Ord::clamp` is the same trait's three-operand method, so it is admitted
        // on the same trait path and refused for the same foreign ones.
        assert_eq!(classify("<u8 as Ord>::clamp"), Some(Intrinsic::Clamp));
        assert!(classify("<u8 as m::Ord>::clamp").is_none());
        // The `std`/`core`-qualified spelling the prelude's own `Ord` prints with.
        assert_eq!(
            classify("<i8 as std::cmp::Ord>::max"),
            Some(Intrinsic::MinMax(MinMaxKind::Max))
        );
        assert_eq!(
            classify("<u8 as core::cmp::Ord>::min"),
            Some(Intrinsic::MinMax(MinMaxKind::Min))
        );
        // The `_signed` near misses stay refused.
        assert!(classify("<u8 as Ord>::min_signed").is_none());
    }

    /// `Ord::min`/`Ord::max` agree with `core` over a whole `u8` and `i8`.
    ///
    /// The signed walk is what pins the ordering choice: a model that used `ule`
    /// for a signed type would return the wrong operand for every pair with a
    /// negative side, and `i8::MIN` (`0x80`) is the one value whose bits sort the
    /// other way. `core`'s own `min`/`max` are the oracle, so the model's `ite` is
    /// compared against the method rather than against a second copy of itself.
    #[test]
    fn the_ord_min_max_agree_with_rust() {
        check(
            Intrinsic::MinMax(MinMaxKind::Min),
            8,
            false,
            unident,
            ident,
            |x, y| Some(i64::from((x as u8).min(y as u8))),
            "u8::min",
        );
        check(
            Intrinsic::MinMax(MinMaxKind::Max),
            8,
            false,
            unident,
            ident,
            |x, y| Some(i64::from((x as u8).max(y as u8))),
            "u8::max",
        );
        check(
            Intrinsic::MinMax(MinMaxKind::Min),
            8,
            true,
            |b| i8::from_ne_bytes([b as u8]) as i64,
            |v| v as u8 as u64,
            |x, y| Some(i64::from((x as i8).min(y as i8))),
            "i8::min",
        );
        check(
            Intrinsic::MinMax(MinMaxKind::Max),
            8,
            true,
            |b| i8::from_ne_bytes([b as u8]) as i64,
            |v| v as u8 as u64,
            |x, y| Some(i64::from((x as i8).max(y as i8))),
            "i8::max",
        );
        // The named points, so a failure names the pair that broke. `i8::MIN` is
        // the value that separates the signed and unsigned orderings.
        let ord = |kind: MinMaxKind, signed: bool, xb: u64, yb: u64| {
            smt::with_fresh(|| {
                let (a, b) = (smt::var(8), smt::var(8));
                let Outcome::Value(v) =
                    eval(Intrinsic::MinMax(kind), a, b, 8, signed, 8).expect("min/max at 8 bits")
                else {
                    panic!("min/max must produce a plain value");
                };
                let (ai, bi) = (smt::index(a), smt::index(b));
                smt::evaluate(v, |i| {
                    if i == ai {
                        Some(xb)
                    } else if i == bi {
                        Some(yb)
                    } else {
                        None
                    }
                })
            })
        };
        for (kind, signed, xb, yb, want, why) in [
            (MinMaxKind::Min, false, 3, 7, 3u64, "unsigned min takes the smaller"),
            (MinMaxKind::Max, false, 3, 7, 7, "unsigned max takes the larger"),
            (MinMaxKind::Min, true, 0x80, 1, 0x80, "i8::MIN is the smallest signed value"),
            (MinMaxKind::Max, true, 0x80, 1, 1, "i8::MIN is not the largest"),
            (MinMaxKind::Min, true, 0xff, 0xfe, 0xfe, "0xfe is -2, below -1"),
            (MinMaxKind::Max, true, 0xff, 0xfe, 0xff, "0xff is -1, above -2"),
        ] {
            assert_eq!(ord(kind, signed, xb, yb), Some(want), "{why} ({xb:#x}, {yb:#x})");
        }
    }

    /// `abs_diff` and the rotations agree with Rust over every `u8`/`i8` pair.
    ///
    /// The oracle is Rust's own method, so the model cannot drift from the
    /// definition. `abs_diff`'s result is the *unsigned* magnitude even on a
    /// signed type, so it is checked against `i8::abs_diff` (which returns a `u8`)
    /// and the sign of the model's value is asserted to be unsigned; the
    /// rotations are checked against `u8::rotate_left`/`rotate_right` and their
    /// `i8` counterparts, whose amount is a `u32` reduced modulo the width.
    #[test]
    fn abs_diff_and_rotations_agree_with_rust() {
        // `abs_diff` on both signednesses. The oracle reads the operands as their
        // own type and returns the `uN` magnitude.
        check(
            Intrinsic::AbsDiff,
            8,
            false,
            unident,
            ident,
            |x, y| Some(i64::from((x as u8).abs_diff(y as u8))),
            "u8::abs_diff",
        );
        check(
            Intrinsic::AbsDiff,
            8,
            true,
            |b| i8::from_ne_bytes([b as u8]) as i64,
            |v| v as u8 as u64,
            |x, y| Some(i64::from((x as i8).abs_diff(y as i8))),
            "i8::abs_diff",
        );
        // The rotations, at the width the amount reduces modulo. `i8`'s rotation
        // operates on the bits, so the oracle reinterprets through `u8`.
        for (kind, label_l, label_r) in [
            (RotateKind::Left, "u8::rotate_left", "i8::rotate_left"),
            (RotateKind::Right, "u8::rotate_right", "i8::rotate_right"),
        ] {
            // The amount is a `u32` in the dump; `check` passes a second operand of
            // the *value's* width, so the oracle is given the same bits. The
            // reduction modulo the width means the low `log2(w)` bits are all that
            // matter, which is exactly what a value at the value's own width gives.
            let (left, _right) = match kind {
                RotateKind::Left => (true, false),
                RotateKind::Right => (false, true),
            };
            check(
                Intrinsic::Rotate(kind),
                8,
                false,
                unident,
                ident,
                move |x, y| {
                    let (x, n) = (x as u8, y as u32);
                    Some(i64::from(if left { x.rotate_left(n) } else { x.rotate_right(n) }))
                },
                label_l,
            );
            check(
                Intrinsic::Rotate(kind),
                8,
                true,
                |b| i8::from_ne_bytes([b as u8]) as i64,
                |v| v as u8 as u64,
                move |x, y| {
                    let (x, n) = (x as i8, y as u32);
                    Some(i64::from(if left { x.rotate_left(n) } else { x.rotate_right(n) } as u8))
                },
                label_r,
            );
        }
        // The named boundaries, so a failure names the input that broke. A rotation
        // by the full width is the identity; a rotation by `w + k` is one by `k`.
        for (kind, x, n, want, why) in [
            (RotateKind::Left, 0x81u8, 8u32, 0x81u8, "rotate_left by the width is the identity"),
            (RotateKind::Left, 0x81, 9, 0x03, "rotate_left by w+1 is by 1"),
            (RotateKind::Right, 0x81, 0, 0x81, "rotate_right by 0 is the identity"),
            (RotateKind::Right, 0x81, 7, 0x03, "rotate_right by w-1"),
        ] {
            let got = smt::with_fresh(|| {
                let (a, b) = (smt::var(8), smt::var(32));
                let Outcome::Value(v) = eval(Intrinsic::Rotate(kind), a, b, 8, false, 8)
                    .expect("a rotation is modelled")
                else {
                    panic!("a rotation must produce a plain value");
                };
                let (ai, bi) = (smt::index(a), smt::index(b));
                smt::evaluate(v, |i| {
                    if i == ai {
                        Some(x as u64)
                    } else if i == bi {
                        Some(n as u64)
                    } else {
                        None
                    }
                })
            });
            assert_eq!(got, Some(want as u64), "{why} ({x:#x}, {n})");
        }
    }

    /// Check a two-operand value-or-panic model against Rust.
    ///
    /// The *value* is compared only where the call does **not** panic -- a path
    /// where it panics is reported by the predicate, and the value it carries
    /// there is never used on a live path, so pinning it would pin an arbitrary
    /// choice. The *predicate* is compared at every input, which is the half that
    /// matters: a predicate that is false where Rust panics would hide a panic.
    fn check_value_or_panic_binary(
        op: Intrinsic,
        w: u8,
        signed: bool,
        from_bits: impl Fn(u64) -> i64,
        rust: impl Fn(i64, i64) -> i64,
        panics: impl Fn(i64, i64) -> bool,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let b = smt::var(w);
            let outcome = eval(op, a, b, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let Outcome::ValueOrPanic { value, fails } = outcome else {
                panic!("{label} must produce a value-or-panic outcome");
            };
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(w, |xb, yb| {
                let (x, y) = (from_bits(xb), from_bits(yb));
                let env = |i: u32| {
                    if i == ai {
                        Some(xb)
                    } else if i == bi {
                        Some(yb)
                    } else {
                        None
                    }
                };
                let p = panics(x, y);
                assert_eq!(
                    smt::evaluate_pred(fails, env),
                    Some(p),
                    "{label} panic predicate at ({x}, {y})"
                );
                if !p {
                    let got = smt::evaluate(value, env);
                    let want = rust(x, y) as u64 & mask_of(w);
                    assert_eq!(got, Some(want), "{label} value at ({x}, {y})");
                }
            });
        });
    }

    /// Check a two-operand `bool` predicate against Rust over every input pair.
    fn check_bool_binary(
        op: Intrinsic,
        w: u8,
        signed: bool,
        from_bits: impl Fn(u64) -> i64,
        oracle: impl Fn(i64, i64) -> bool,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let b = smt::var(w);
            let outcome = eval(op, a, b, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let Outcome::Bool(p) = outcome else {
                panic!("{label} must produce a `bool`");
            };
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(w, |xb, yb| {
                let (x, y) = (from_bits(xb), from_bits(yb));
                let env = |i: u32| {
                    if i == ai {
                        Some(xb)
                    } else if i == bi {
                        Some(yb)
                    } else {
                        None
                    }
                };
                assert_eq!(
                    smt::evaluate_pred(p, env),
                    Some(oracle(x, y)),
                    "{label} at ({x}, {y})"
                );
            });
        });
    }

    /// `is_multiple_of` agrees with Rust over the whole `u8` domain, including the
    /// `b == 0` corner (`core` defines `a.is_multiple_of(0)` as `a == 0`).
    #[test]
    fn is_multiple_of_agrees_with_rust() {
        check_bool_binary(
            Intrinsic::Bool(BoolKind::MultipleOf),
            8,
            false,
            unident,
            |x, y| (x as u8).is_multiple_of(y as u8),
            "u8::is_multiple_of",
        );
    }

    /// `signum` agrees with Rust over the whole `i8` domain.
    #[test]
    fn signum_agrees_with_rust() {
        check_unary(
            Intrinsic::Signum,
            8,
            8,
            true,
            |xb| signed_of(xb, 8).signum() as u64 & 0xff,
            "i8::signum",
        );
    }

    /// `cast_unsigned`/`cast_signed` agree with Rust over the whole `i8`/`u8`
    /// domain.
    ///
    /// The value is the operand unchanged -- the cast is a *re-interpretation*, not
    /// a conversion -- so the oracle is Rust's own method, and a model that
    /// sign-extended, zero-extended or negated would disagree at the boundary
    /// values (`-1` and `MIN`) this walk reaches.
    #[test]
    fn the_signedness_casts_agree_with_rust() {
        // `i8::cast_unsigned` reinterprets the same bits as `u8`.
        check_unary(
            Intrinsic::SignednessCast,
            8,
            8,
            true,
            |xb| u64::from(signed_of(xb, 8).cast_unsigned() as u8),
            "i8::cast_unsigned",
        );
        // `u8::cast_signed` reinterprets the same bits as `i8`.
        check_unary(
            Intrinsic::SignednessCast,
            8,
            8,
            false,
            |xb| (u8::try_from(xb).unwrap().cast_signed() as u8) as u64,
            "u8::cast_signed",
        );
    }

    /// The plain inherent `pow` agrees with Rust, panic included, over the whole
    /// `u8`/`i8` base domain.
    ///
    /// `pow`'s exponent is a `u32` in `core`, but the model folds over the
    /// exponent's *value*, so an eight-bit exponent exercises the same fold for
    /// every exponent a `u8` can hold. The oracle is Rust's own `checked_pow`: the
    /// value where it is `Some`, and a panic exactly where it is `None` -- so a
    /// model that wrapped instead of panicking fails at the first overflowing pair.
    #[test]
    fn the_plain_pow_agrees_with_rust() {
        check_value_or_panic_binary(
            Intrinsic::PowPanic,
            8,
            false,
            |xb| xb as i64,
            |x, y| i64::from((x as u8).pow(y as u32)),
            |x, y| (x as u8).checked_pow(y as u32).is_none(),
            "u8::pow",
        );
        check_value_or_panic_binary(
            Intrinsic::PowPanic,
            8,
            true,
            |xb| signed_of(xb, 8),
            |x, y| i64::from((x as i8).pow(y as u32)),
            |x, y| (x as i8).checked_pow(y as u32).is_none(),
            "i8::pow",
        );
    }

    /// The Euclidean pair and `div_ceil` agree with Rust's value everywhere the
    /// call is defined, and their panic predicate fires exactly where it panics.
    ///
    /// `div_euclid`/`rem_euclid` panic on a zero divisor and on `MIN / -1`;
    /// `div_ceil` (unsigned) panics only on a zero divisor. The oracle calls the
    /// real method only on the non-panicking inputs, so it cannot itself panic.
    #[test]
    fn the_euclidean_pair_and_div_ceil_agree_with_rust() {
        let i8_min = i8::MIN as i64;
        check_value_or_panic_binary(
            Intrinsic::DivEuclid,
            8,
            true,
            |b| i8::from_ne_bytes([b as u8]) as i64,
            |x, y| i64::from((x as i8).div_euclid(y as i8)),
            |x, y| y == 0 || (x == i8_min && y == -1),
            "i8::div_euclid",
        );
        check_value_or_panic_binary(
            Intrinsic::RemEuclid,
            8,
            true,
            |b| i8::from_ne_bytes([b as u8]) as i64,
            |x, y| i64::from((x as i8).rem_euclid(y as i8)),
            |x, y| y == 0 || (x == i8_min && y == -1),
            "i8::rem_euclid",
        );
        check_value_or_panic_binary(
            Intrinsic::DivCeil,
            8,
            false,
            unident,
            |x, y| i64::from((x as u8).div_ceil(y as u8)),
            |_, y| y == 0,
            "u8::div_ceil",
        );
    }

    /// `midpoint` agrees with Rust's own method over the whole domain, on both
    /// signednesses, including the overflowing sums a plain `(a + b) / 2` would
    /// wrap.
    ///
    /// `midpoint` is *total* -- it exists so the sum never overflows -- so the
    /// oracle is a plain value comparison and the exhaustive walk covers the
    /// boundary cases (`MIN`, `MAX`, `MAX + MAX`) that a sampling test would miss.
    #[test]
    fn midpoint_agrees_with_rust() {
        check_unary_binary_value(
            Intrinsic::Midpoint,
            8,
            false,
            unident,
            |x, y| i64::from((x as u8).midpoint(y as u8)),
            "u8::midpoint",
        );
        check_unary_binary_value(
            Intrinsic::Midpoint,
            8,
            true,
            |b| i8::from_ne_bytes([b as u8]) as i64,
            |x, y| i64::from((x as i8).midpoint(y as i8)),
            "i8::midpoint",
        );
    }

    /// `next_multiple_of` agrees with Rust's value and its panic predicate over the
    /// whole `u8` domain.
    ///
    /// The oracle uses `checked_next_multiple_of`, which returns `None` exactly
    /// where the method panics (a zero divisor, or an overflow), so the two are
    /// checked together: a value mismatch, a predicate that fires where Rust
    /// returns `Some`, and a predicate that stays silent where Rust returns `None`
    /// are all caught.
    #[test]
    fn next_multiple_of_agrees_with_rust() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            let outcome = eval(Intrinsic::NextMultipleOf, a, b, 8, false, 8)
                .expect("next_multiple_of must be modelled at u8");
            let Outcome::ValueOrPanic { value, fails } = outcome else {
                panic!("next_multiple_of must produce a value-or-panic outcome");
            };
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(8, |xb, yb| {
                let (x, y) = (xb as u8, yb as u8);
                let env = |i: u32| {
                    if i == ai {
                        Some(xb)
                    } else if i == bi {
                        Some(yb)
                    } else {
                        None
                    }
                };
                let want = x.checked_next_multiple_of(y);
                assert_eq!(
                    smt::evaluate_pred(fails, env),
                    Some(want.is_none()),
                    "next_multiple_of panic predicate at ({x}, {y})"
                );
                if let Some(v) = want {
                    assert_eq!(
                        smt::evaluate(value, env),
                        Some(u64::from(v)),
                        "next_multiple_of value at ({x}, {y})"
                    );
                }
            });
        });
    }

    /// `checked_next_multiple_of` agrees with Rust's `Option` over the whole `u8`
    /// domain, tag and payload together.
    ///
    /// The `Option` counterpart of `next_multiple_of`: the oracle is `core`'s own
    /// `checked_next_multiple_of`, so the tag is checked against `Some`/`None`
    /// exactly, and the payload against the value the plain method returns. A
    /// model that swapped the tag (a `None` where Rust returns `Some`), or that
    /// carried the payload on the `None` path, is caught here rather than at a
    /// corpus fixture.
    #[test]
    fn checked_next_multiple_of_agrees_with_rust() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            let outcome = eval(Intrinsic::CheckedNextMultipleOf, a, b, 8, false, 8)
                .expect("checked_next_multiple_of must be modelled at u8");
            let Outcome::Option { tag, payload } = outcome else {
                panic!("checked_next_multiple_of must produce an `Option` outcome");
            };
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(8, |xb, yb| {
                let (x, y) = (xb as u8, yb as u8);
                let env = |i: u32| {
                    if i == ai {
                        Some(xb)
                    } else if i == bi {
                        Some(yb)
                    } else {
                        None
                    }
                };
                let want = x.checked_next_multiple_of(y);
                assert_eq!(
                    smt::evaluate(tag, env),
                    Some(if want.is_some() { 1 } else { 0 }),
                    "checked_next_multiple_of tag at ({x}, {y})"
                );
                if let Some(v) = want {
                    assert_eq!(
                        smt::evaluate(payload, env),
                        Some(u64::from(v)),
                        "checked_next_multiple_of payload at ({x}, {y})"
                    );
                }
            });
        });
    }

    /// `ilog2`/`ilog10` agree with Rust over the whole `u8`/`i8` domain, value and
    /// panic predicate together.
    ///
    /// `core` panics on a non-positive argument, so the oracle calls the real
    /// method only where it is defined (`x > 0`) and expects the failure predicate
    /// elsewhere. The result is a `u32`, so `result_w` is `32` and the value is
    /// zero-extended -- the walk checks the widened term, which is what a caller
    /// reads.
    #[test]
    fn the_integer_logs_agree_with_rust() {
        for (kind, oracle_u, oracle_i, label) in [
            (
                LogKind::Ilog2,
                (|x: u8| u64::from(x.ilog2())) as fn(u8) -> u64,
                (|x: i8| u64::from(x.ilog2())) as fn(i8) -> u64,
                "ilog2",
            ),
            (
                LogKind::Ilog10,
                (|x: u8| u64::from(x.ilog10())) as fn(u8) -> u64,
                (|x: i8| u64::from(x.ilog10())) as fn(i8) -> u64,
                "ilog10",
            ),
        ] {
            for xb in 0..=u8::MAX {
                let x = xb;
                check_log(
                    Intrinsic::Ilog(kind),
                    8,
                    false,
                    xb as u64,
                    x > 0,
                    || oracle_u(x),
                    &format!("u8::{label} at {x}"),
                );
            }
            for xb in 0..=u8::MAX {
                let x = i8::from_ne_bytes([xb]);
                check_log(
                    Intrinsic::Ilog(kind),
                    8,
                    true,
                    xb as u64,
                    x > 0,
                    || oracle_i(x),
                    &format!("i8::{label} at {x}"),
                );
            }
        }
    }

    /// Evaluate a `uN`/`iN` log model at one input and compare value and panic.
    ///
    /// `want` is a closure because `core`'s method *panics* where the model's
    /// failure predicate fires, so the expectation cannot be computed eagerly for
    /// every input.
    fn check_log(
        op: Intrinsic,
        w: u8,
        signed: bool,
        bits: u64,
        defined: bool,
        want: impl Fn() -> u64,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let outcome = eval(op, a, a, w, signed, 32)
                .unwrap_or_else(|| panic!("{label} must be modelled"));
            let Outcome::ValueOrPanic { value, fails } = outcome else {
                panic!("{label} must produce a value-or-panic outcome");
            };
            let ai = smt::index(a);
            let env = |i: u32| if i == ai { Some(bits) } else { None };
            assert_eq!(
                smt::evaluate_pred(fails, env),
                Some(!defined),
                "{label}: panic predicate"
            );
            if defined {
                assert_eq!(smt::evaluate(value, env), Some(want()), "{label}: value");
            }
        });
    }

    /// `checked_ilog2`/`checked_ilog10` agree with Rust over the whole `u8`/`i8`
    /// domain, tag and payload together.
    ///
    /// The tag is the point: `Some` exactly where the plain logarithm is defined
    /// (`x > 0`) and `None` where it would panic, so a model that wrote the tag
    /// the wrong way round -- or built it at the wrong width -- is caught here
    /// rather than only at a corpus fixture. The payload is a `u32`, so
    /// `result_w` is `32` and the walk checks the widened term, which is what a
    /// caller reads.
    #[test]
    fn the_checked_logs_agree_with_rust() {
        for (kind, oracle_u, oracle_i, label) in [
            (
                LogKind::Ilog2,
                (|x: u8| x.checked_ilog2().map(u64::from)) as fn(u8) -> Option<u64>,
                (|x: i8| x.checked_ilog2().map(u64::from)) as fn(i8) -> Option<u64>,
                "checked_ilog2",
            ),
            (
                LogKind::Ilog10,
                (|x: u8| x.checked_ilog10().map(u64::from)) as fn(u8) -> Option<u64>,
                (|x: i8| x.checked_ilog10().map(u64::from)) as fn(i8) -> Option<u64>,
                "checked_ilog10",
            ),
        ] {
            for xb in 0..=u8::MAX {
                let x = xb;
                check_checked_log(
                    Intrinsic::CheckedIlog(kind),
                    false,
                    xb as u64,
                    oracle_u(x),
                    &format!("u8::{label} at {x}"),
                );
            }
            for xb in 0..=u8::MAX {
                let x = i8::from_ne_bytes([xb]);
                check_checked_log(
                    Intrinsic::CheckedIlog(kind),
                    true,
                    xb as u64,
                    oracle_i(x),
                    &format!("i8::{label} at {x}"),
                );
            }
        }
    }

    /// Evaluate a `checked_ilog*` model at one input and compare tag and payload.
    ///
    /// The payload is compared only where Rust returns `Some`; where it returns
    /// `None` the model's payload is unconstrained (a path that takes the `None`
    /// arm never reads it), so asserting it would be asserting something the
    /// model does not claim.
    fn check_checked_log(
        op: Intrinsic,
        signed: bool,
        bits: u64,
        want: Option<u64>,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let outcome = eval(op, a, a, 8, signed, 32)
                .unwrap_or_else(|| panic!("{label} must be modelled"));
            let Outcome::Option { tag, payload } = outcome else {
                panic!("{label} must produce an `Option` outcome");
            };
            let ai = smt::index(a);
            let env = |i: u32| if i == ai { Some(bits) } else { None };
            assert_eq!(
                smt::evaluate(tag, env),
                Some(if want.is_some() { 1 } else { 0 }),
                "{label}: tag"
            );
            if let Some(v) = want {
                assert_eq!(smt::evaluate(payload, env), Some(v), "{label}: payload");
            }
        });
    }

    /// The width-aware oracle for `next_power_of_two`: `Some(2^ceil(log2 x))`
    /// when that fits `w` bits, `None` when it does not.
    ///
    /// Written from the definition rather than by calling a host method, because
    /// the model is parameterised by a width the host types do not share: at four
    /// bits the overflow boundary is `8`, not the `u8`'s `128`. `0` and `1` both
    /// round to `1`; otherwise the result is the smallest power of two `>= x`,
    /// which is `None` exactly when it is `2^w`.
    fn next_power_of_two_oracle(xb: u64, w: u8) -> Option<u64> {
        let x = xb & mask_of(w);
        if x <= 1 {
            return Some(1);
        }
        let k = 64 - (x - 1).leading_zeros();
        if k >= u32::from(w) {
            None
        } else {
            Some(1u64 << k)
        }
    }

    /// `next_power_of_two` and its `checked_` counterpart agree with Rust
    /// everywhere, value and failure condition together.
    ///
    /// The whole `u8`/`u16` domain is walked. The oracle is `checked_next_power_of_two`,
    /// which returns `None` exactly where the plain method panics (the result does
    /// not fit), so a value mismatch, a predicate that fires where Rust returns
    /// `Some`, and a predicate that stays silent where Rust returns `None` are all
    /// caught -- and the `x == 0` case (value `1`, no failure) is the input an
    /// off-by-one in the `x <= 1` pre-step would get wrong.
    #[test]
    fn the_next_power_of_two_pair_agrees_with_rust() {
        for w in [1u8, 4, 8, 16] {
            for (op, is_checked) in
                [(Intrinsic::NextPowerOfTwo, false), (Intrinsic::CheckedNextPowerOfTwo, true)]
            {
                smt::with_fresh(|| {
                    let a = smt::var(w);
                    let outcome = eval(op, a, a, w, false, w).expect("modelled");
                    let ai = smt::index(a);
                    for xb in 0..(1u64 << w) {
                        // The oracle is computed at the *model's* width, not the
                        // host's: `checked_next_power_of_two` on a `u8` has a
                        // different overflow boundary from the four-bit model, so
                        // the width has to be part of the oracle.
                        let want = next_power_of_two_oracle(xb, w);
                        let env = |i: u32| if i == ai { Some(xb) } else { None };
                        match &outcome {
                            Outcome::ValueOrPanic { value, fails } => {
                                assert!(!is_checked);
                                assert_eq!(
                                    smt::evaluate_pred(*fails, env),
                                    Some(want.is_none()),
                                    "next_power_of_two panic at {w} bits, {xb:#x}"
                                );
                                if let Some(v) = want {
                                    assert_eq!(
                                        smt::evaluate(*value, env),
                                        Some(v),
                                        "next_power_of_two value at {w} bits, {xb:#x}"
                                    );
                                }
                            }
                            Outcome::Option { tag, payload } => {
                                assert!(is_checked);
                                let want_tag = if want.is_some() { 1 } else { 0 };
                                assert_eq!(
                                    smt::evaluate(*tag, env),
                                    Some(want_tag),
                                    "checked_next_power_of_two tag at {w} bits, {xb:#x}"
                                );
                                if let Some(v) = want {
                                    assert_eq!(
                                        smt::evaluate(*payload, env),
                                        Some(v),
                                        "checked_next_power_of_two payload at {w} bits, {xb:#x}"
                                    );
                                }
                            }
                            _ => panic!("next_power_of_two must be a value-or-panic or an Option"),
                        }
                    }
                });
            }
        }
    }

    /// Compare a two-operand *total* model against Rust over every input pair.
    ///
    /// The total counterpart of [`check_value_or_panic_binary`]: no failure
    /// predicate, so the oracle is called at every input.
    fn check_unary_binary_value(
        op: Intrinsic,
        w: u8,
        signed: bool,
        from_bits: impl Fn(u64) -> i64,
        rust: impl Fn(i64, i64) -> i64,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let b = smt::var(w);
            let outcome = eval(op, a, b, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let Outcome::Value(value) = outcome else {
                panic!("{label} must produce a plain value");
            };
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(w, |xb, yb| {
                let (x, y) = (from_bits(xb), from_bits(yb));
                let env = |i: u32| {
                    if i == ai {
                        Some(xb)
                    } else if i == bi {
                        Some(yb)
                    } else {
                        None
                    }
                };
                let want = rust(x, y) as u64 & mask_of(w);
                assert_eq!(smt::evaluate(value, env), Some(want), "{label} at ({x}, {y})");
            });
        });
    }

    /// The byte permutations and orderings agree with Rust over the whole domain.
    ///
    /// `reverse_bits` and `swap_bytes` are bit/byte moves, checked on both
    /// signednesses (the result is the operand's type, so a signed oracle reads it
    /// back through `u8`). `to_be`/`to_le`/`to_ne` depend on the *target's*
    /// endianness, so the oracle is Rust's own method, which agrees with the model
    /// by construction only if both read the same target -- which they do, since
    /// the model uses `cfg!(target_endian)`.
    #[test]
    fn the_byte_permutations_and_orderings_agree_with_rust() {
        for w in [8u8, 16] {
            check_unary(
                Intrinsic::BitReverse,
                w,
                w,
                false,
                move |xb| match w {
                    8 => u8::try_from(xb).unwrap().reverse_bits() as u64,
                    16 => u16::try_from(xb).unwrap().reverse_bits() as u64,
                    _ => unreachable!(),
                },
                "reverse_bits",
            );
            check_unary(
                Intrinsic::ByteSwap,
                w,
                w,
                false,
                move |xb| match w {
                    8 => u8::try_from(xb).unwrap().swap_bytes() as u64,
                    16 => u16::try_from(xb).unwrap().swap_bytes() as u64,
                    _ => unreachable!(),
                },
                "swap_bytes",
            );
            for (kind, label) in
                [(ByteOrderKind::Be, "to_be"), (ByteOrderKind::Le, "to_le")]
            {
                check_unary(
                    Intrinsic::ByteOrder(kind),
                    w,
                    w,
                    false,
                    move |xb| match w {
                        8 => {
                            let x = u8::try_from(xb).unwrap();
                            match kind {
                                ByteOrderKind::Be => x.to_be() as u64,
                                ByteOrderKind::Le => x.to_le() as u64,
                            }
                        }
                        16 => {
                            let x = u16::try_from(xb).unwrap();
                            match kind {
                                ByteOrderKind::Be => x.to_be() as u64,
                                ByteOrderKind::Le => x.to_le() as u64,
                            }
                        }
                        _ => unreachable!(),
                    },
                    label,
                );
            }
        }
    }

    /// The ASCII case conversions agree with Rust over the whole `u8` domain.
    #[test]
    fn the_ascii_case_conversions_agree_with_rust() {
        check_unary(
            Intrinsic::AsciiCase(AsciiCaseKind::Upper),
            8,
            8,
            false,
            |xb| u8::try_from(xb).unwrap().to_ascii_uppercase() as u64,
            "u8::to_ascii_uppercase",
        );
        check_unary(
            Intrinsic::AsciiCase(AsciiCaseKind::Lower),
            8,
            8,
            false,
            |xb| u8::try_from(xb).unwrap().to_ascii_lowercase() as u64,
            "u8::to_ascii_lowercase",
        );
    }

    /// The new names classify, and the neighbours that only *look* like them do
    /// not.
    #[test]
    fn the_new_value_names_classify_and_their_neighbours_do_not() {
        assert_eq!(classify("core::num::<impl i32>::signum"), Some(Intrinsic::Signum));
        assert_eq!(
            classify("core::num::<impl i32>::cast_unsigned"),
            Some(Intrinsic::SignednessCast)
        );
        assert_eq!(
            classify("core::num::<impl u32>::cast_signed"),
            Some(Intrinsic::SignednessCast)
        );
        assert_eq!(classify("core::num::<impl i32>::div_euclid"), Some(Intrinsic::DivEuclid));
        assert_eq!(classify("core::num::<impl i32>::rem_euclid"), Some(Intrinsic::RemEuclid));
        assert_eq!(classify("core::num::<impl u32>::div_ceil"), Some(Intrinsic::DivCeil));
        assert_eq!(classify("core::num::<impl u8>::reverse_bits"), Some(Intrinsic::BitReverse));
        assert_eq!(classify("core::num::<impl u16>::swap_bytes"), Some(Intrinsic::ByteSwap));
        assert_eq!(classify("core::num::<impl u32>::to_be"), Some(Intrinsic::ByteOrder(ByteOrderKind::Be)));
        assert_eq!(classify("core::num::<impl u32>::to_le"), Some(Intrinsic::ByteOrder(ByteOrderKind::Le)));
        // `from_be`/`from_le` are the *associated functions* (`u16::from_be(x)`)
        // that invert `to_be`/`to_le` on the same target, so they classify to the
        // same byte-order shapes rather than being refused.
        assert_eq!(classify("core::num::<impl u32>::from_be"), Some(Intrinsic::ByteOrder(ByteOrderKind::Be)));
        assert_eq!(classify("core::num::<impl u32>::from_le"), Some(Intrinsic::ByteOrder(ByteOrderKind::Le)));
        assert_eq!(classify("core::num::<impl u8>::to_ascii_uppercase"), Some(Intrinsic::AsciiCase(AsciiCaseKind::Upper)));
        assert_eq!(classify("core::num::<impl u8>::to_ascii_lowercase"), Some(Intrinsic::AsciiCase(AsciiCaseKind::Lower)));
        assert_eq!(classify("core::num::<impl u32>::is_multiple_of"), Some(Intrinsic::Bool(BoolKind::MultipleOf)));
        assert_eq!(classify("core::num::<impl u32>::midpoint"), Some(Intrinsic::Midpoint));
        assert_eq!(classify("core::num::<impl i32>::midpoint"), Some(Intrinsic::Midpoint));
        assert_eq!(classify("core::num::<impl u32>::next_multiple_of"), Some(Intrinsic::NextMultipleOf));
        assert_eq!(
            classify("core::num::<impl u32>::checked_next_multiple_of"),
            Some(Intrinsic::CheckedNextMultipleOf)
        );
        assert_eq!(classify("core::num::<impl u32>::ilog2"), Some(Intrinsic::Ilog(LogKind::Ilog2)));
        assert_eq!(classify("core::num::<impl i32>::ilog2"), Some(Intrinsic::Ilog(LogKind::Ilog2)));
        assert_eq!(classify("core::num::<impl u32>::ilog10"), Some(Intrinsic::Ilog(LogKind::Ilog10)));
        assert_eq!(
            classify("core::num::<impl u32>::checked_ilog2"),
            Some(Intrinsic::CheckedIlog(LogKind::Ilog2))
        );
        assert_eq!(
            classify("core::num::<impl i32>::checked_ilog10"),
            Some(Intrinsic::CheckedIlog(LogKind::Ilog10))
        );
        assert_eq!(classify("core::num::<impl i32>::ilog10"), Some(Intrinsic::Ilog(LogKind::Ilog10)));
        // The `_bytes` forms return an array, so they are left unclassified rather
        // than modelled as a word.
        assert_eq!(classify("core::num::<impl u32>::to_be_bytes"), None);
        assert_eq!(classify("core::num::<impl u32>::to_le_bytes"), None);
        // Names that merely end in a modelled name are not the method.
        assert_eq!(classify("core::num::<impl u32>::signum_thing"), None);
        assert_eq!(classify("core::num::<impl u32>::no_div_ceil"), None);
        assert_eq!(classify("core::num::<impl u8>::to_ascii_uppercase_thing"), None);
    }

    /// The type-specific membership of the new shapes: `signum` and the Euclidean
    /// pair are signed-only, `div_ceil` and `is_multiple_of` are unsigned-only, and
    /// the ASCII case conversions are `u8`-only. A wrong direction here would read
    /// a method `core` does not define on that type.
    #[test]
    fn the_new_shapes_are_modelled_only_on_the_types_that_have_them() {
        for w in [8u8, 16, 32] {
            assert!(is_modelled(Intrinsic::Signum, w, true), "iN::signum exists");
            assert!(!is_modelled(Intrinsic::Signum, w, false), "uN::signum does not exist");
            assert!(is_modelled(Intrinsic::DivEuclid, w, true));
            assert!(!is_modelled(Intrinsic::DivEuclid, w, false));
            assert!(is_modelled(Intrinsic::RemEuclid, w, true));
            assert!(!is_modelled(Intrinsic::RemEuclid, w, false));
            assert!(is_modelled(Intrinsic::DivCeil, w, false));
            assert!(!is_modelled(Intrinsic::DivCeil, w, true));
            assert!(is_modelled(Intrinsic::Bool(BoolKind::MultipleOf), w, false));
            assert!(!is_modelled(Intrinsic::Bool(BoolKind::MultipleOf), w, true));
            // `midpoint` and the logs exist on both signednesses and are total
            // (the logs' panic is a *reported* obligation, not a missing model).
            assert!(is_modelled(Intrinsic::Midpoint, w, true));
            assert!(is_modelled(Intrinsic::Midpoint, w, false));
            assert!(is_modelled(Intrinsic::Ilog(LogKind::Ilog2), w, true));
            assert!(is_modelled(Intrinsic::Ilog(LogKind::Ilog2), w, false));
            assert!(is_modelled(Intrinsic::Ilog(LogKind::Ilog10), w, true));
            assert!(is_modelled(Intrinsic::Ilog(LogKind::Ilog10), w, false));
            // `next_multiple_of` is unsigned-only on this toolchain: the signed
            // spelling is unstable, so a signed receiver must be refused rather
            // than read.
            assert!(is_modelled(Intrinsic::NextMultipleOf, w, false));
            assert!(!is_modelled(Intrinsic::NextMultipleOf, w, true));
            // `next_power_of_two` and its `checked_` counterpart are unsigned-only
            // too: `core` has no such method on the signed types, so a signed
            // receiver must be refused rather than read.
            assert!(is_modelled(Intrinsic::NextPowerOfTwo, w, false));
            assert!(!is_modelled(Intrinsic::NextPowerOfTwo, w, true));
            assert!(is_modelled(Intrinsic::CheckedNextPowerOfTwo, w, false));
            assert!(!is_modelled(Intrinsic::CheckedNextPowerOfTwo, w, true));
            // The byte permutations and orders exist on both signednesses.
            assert!(is_modelled(Intrinsic::BitReverse, w, true));
            assert!(is_modelled(Intrinsic::BitReverse, w, false));
            assert!(is_modelled(Intrinsic::ByteSwap, w, true));
            assert!(is_modelled(Intrinsic::ByteOrder(ByteOrderKind::Be), w, false));
        }
        // `signum`, the permutations and the orders are total at 64 bits too, but
        // the divider-backed shapes are not -- they are bounded at `DIV_MAX_WIDTH`.
        for op in [
            Intrinsic::BitReverse,
            Intrinsic::ByteSwap,
            Intrinsic::ByteOrder(ByteOrderKind::Le),
        ] {
            assert!(is_modelled(op, 64, true));
            assert!(is_modelled(op, 64, false));
        }
        assert!(is_modelled(Intrinsic::Signum, 64, true));
        // The ASCII case is `u8`-only.
        assert!(is_modelled(Intrinsic::AsciiCase(AsciiCaseKind::Upper), 8, false));
        assert!(!is_modelled(Intrinsic::AsciiCase(AsciiCaseKind::Upper), 16, false));
        assert!(!is_modelled(Intrinsic::AsciiCase(AsciiCaseKind::Upper), 8, true));
        // The division shapes are bounded at `DIV_MAX_WIDTH`, like the other
        // divider-backed models.
        assert!(!is_modelled(Intrinsic::DivEuclid, 64, true));
        assert!(!is_modelled(Intrinsic::DivCeil, 64, false));
    }

    /// The inherent `abs` value and panic predicate agree with Rust everywhere.
    ///
    /// The value is the same `unary_result` the families' `abs` uses, so it is
    /// checked against `iN::abs` at *every* input -- the wrapped value is defined
    /// everywhere, and only the predicate says where Rust panics. The predicate
    /// must be true exactly at `MIN`, which is where `iN::abs` overflows.
    #[test]
    fn the_abs_value_and_panic_predicate_agree_with_rust() {
        for w in [1u8, 4, 8] {
            smt::with_fresh(|| {
                let a = smt::var(w);
                let outcome = eval(Intrinsic::Abs, a, a, w, true, w).expect("abs is modelled");
                let Outcome::ValueOrPanic { value, fails } = outcome else {
                    panic!("abs must produce a value-or-panic outcome");
                };
                let ai = smt::index(a);
                for xb in 0..(1u64 << w) {
                    let x = signed_of(xb, w);
                    let env = |i: u32| if i == ai { Some(xb) } else { None };
                    let got = smt::evaluate(value, env);
                    let want = x.wrapping_abs() as u64 & mask_of(w);
                    assert_eq!(
                        got,
                        Some(want),
                        "abs at {w} bits, bits {xb:#x}: the model says {got:?}, Rust says {want:#x}"
                    );
                    let want_fails = x == i64::MIN >> (64 - w);
                    assert_eq!(
                        smt::evaluate_pred(fails, env),
                        Some(want_fails),
                        "abs panic at {w} bits, bits {xb:#x}: want {want_fails}"
                    );
                }
            });
        }
    }

    /// The inherent `unsigned_abs` agrees with Rust everywhere, and never fails.
    ///
    /// Its value is the same `unary_result` the families' `abs` uses, read as an
    /// *unsigned* magnitude: `i8::unsigned_abs(-128)` is `128u8`, which is the
    /// input the signed `abs` cannot represent. So the value is checked against
    /// `iN::unsigned_abs` at every input, and the outcome is asserted to be a
    /// plain `Value` -- there is no failure predicate, because the magnitude
    /// always fits the unsigned result. The `MIN` input is named explicitly, so a
    /// model that reused the signed `abs`'s failure (or truncated the magnitude to
    /// a signed read) fails the test rather than passing at the easy inputs.
    #[test]
    fn the_unsigned_abs_agrees_with_rust() {
        for w in [1u8, 4, 8, 16] {
            smt::with_fresh(|| {
                let a = smt::var(w);
                let outcome =
                    eval(Intrinsic::UnsignedAbs, a, a, w, true, w).expect("unsigned_abs is modelled");
                let Outcome::Value(value) = outcome else {
                    panic!("unsigned_abs is total, so it must be a plain value, got a failure");
                };
                let ai = smt::index(a);
                for xb in 0..(1u64 << w) {
                    let x = signed_of(xb, w);
                    let env = |i: u32| if i == ai { Some(xb) } else { None };
                    let got = smt::evaluate(value, env);
                    let want = x.unsigned_abs() & mask_of(w);
                    assert_eq!(
                        got,
                        Some(want),
                        "unsigned_abs at {w} bits, bits {xb:#x}: the model says {got:?}, Rust says {want:#x}"
                    );
                }
            });
        }
    }

    /// `Ord::clamp`'s value and panic predicate agree with Rust everywhere.
    ///
    /// Every `(x, lo, hi)` triple at four bits is walked. The value is the
    /// clamped `x`; the predicate is true exactly where `core`'s two asserts
    /// would fire -- `lo > hi` or `x` outside `[lo, hi]`. This is the whole
    /// contract of the shape: a value wrong anywhere is a wrong proof, and a
    /// predicate that misses an out-of-range triple would let a panicking call be
    /// reported safe.
    #[test]
    fn the_clamp_value_and_panic_predicate_agree_with_rust() {
        for signed in [false, true] {
            let w = 4u8;
            smt::with_fresh(|| {
                let (a, l, h) = (smt::var(w), smt::var(w), smt::var(w));
                let outcome = clamp(a, l, h, w, signed).expect("clamp is modelled");
                let Outcome::ValueOrPanic { value, fails } = outcome else {
                    panic!("clamp must produce a value-or-panic outcome");
                };
                let (ai, li, hi_i) = (smt::index(a), smt::index(l), smt::index(h));
                for xb in 0..(1u64 << w) {
                    for lob in 0..(1u64 << w) {
                        for hib in 0..(1u64 << w) {
                            let (x, lo, hi) = if signed {
                                (signed_of(xb, w), signed_of(lob, w), signed_of(hib, w))
                            } else {
                                (xb as i64, lob as i64, hib as i64)
                            };
                            let env = |i: u32| {
                                if i == ai {
                                    Some(xb)
                                } else if i == li {
                                    Some(lob)
                                } else if i == hi_i {
                                    Some(hib)
                                } else {
                                    None
                                }
                            };
                            // The oracle is the clamp *expression*, not
                            // `iN::clamp`, because `core`'s method panics on
                            // `lo > hi` and there is no value to compare there.
                            // The expression is exactly what the model builds
                            // (`if x < lo { lo } else if x > hi { hi } else { x }`),
                            // and it agrees with `core`'s value wherever `core`
                            // returns one.
                            let want = (if x < lo {
                                lo
                            } else if x > hi {
                                hi
                            } else {
                                x
                            }) as u64
                                & mask_of(w);
                            let got = smt::evaluate(value, env);
                            assert_eq!(
                                got,
                                Some(want),
                                "clamp(signed={signed}) ({x}, {lo}, {hi}): model {got:?}, Rust {want}"
                            );
                            // The only panic is `assert!(lo <= hi)`: an
                            // out-of-range `x` is clamped, not an error.
                            let want_fails = lo > hi;
                            assert_eq!(
                                smt::evaluate_pred(fails, env),
                                Some(want_fails),
                                "clamp panic(signed={signed}) ({x}, {lo}, {hi}): want {want_fails}"
                            );
                        }
                    }
                }
            });
        }
    }

    /// `abs` and `clamp` classify, and the neighbours that only *look* like them
    /// do not.
    #[test]
    fn the_abs_and_clamp_names_classify_and_their_neighbours_do_not() {
        assert_eq!(classify("core::num::<impl i32>::abs"), Some(Intrinsic::Abs));
        assert_eq!(classify("abs"), Some(Intrinsic::Abs));
        // `clamp` is `Ord`'s, so only the standard library's trait path is
        // accepted -- a module-qualified local trait is refused.
        assert_eq!(classify("<u32 as Ord>::clamp"), Some(Intrinsic::Clamp));
        assert_eq!(classify("<i8 as std::cmp::Ord>::clamp"), Some(Intrinsic::Clamp));
        assert_eq!(classify("<i8 as core::cmp::Ord>::clamp"), Some(Intrinsic::Clamp));
        assert_eq!(classify("<MyT as m::Ord>::clamp"), None);
        assert_eq!(classify("<MyT as MyOrd>::clamp"), None);
        assert_eq!(classify("clamp"), None);
        // The families' own `abs` names are still matched by the prefix split, not
        // by the inherent `abs` arm.
        assert_eq!(
            classify("core::num::<impl i8>::wrapping_abs"),
            Some(Intrinsic::Unary(Family::Wrapping, UnOp::Abs))
        );
        assert_eq!(classify("core::num::<impl i8>::checked_abs"),
            Some(Intrinsic::Unary(Family::Checked, UnOp::Abs)));
        // A name that merely ends in `abs` is not the method.
        assert_eq!(classify("core::num::<impl i8>::no_abs"), None);
    }

    /// The bit mask of a `w`-bit value, as a `u64`.
    fn mask_of(w: u8) -> u64 {
        if w >= 64 {
            u64::MAX
        } else {
            (1u64 << w) - 1
        }
    }

    /// Reinterpret a `w`-bit pattern as the signed value it denotes.
    fn signed_of(bits: u64, w: u8) -> i64 {
        let shift = 64 - u32::from(w);
        ((bits << shift) as i64) >> shift
    }

    /// The `from`/`into` names classify, and the neighbours that only *look* like
    /// them do not.
    #[test]
    fn the_conversion_names_classify_and_their_neighbours_do_not() {
        // Both spellings of both directions, bare and fully qualified.
        for name in [
            "<u16 as From<u8>>::from",
            "<u16 as core::convert::From<u8>>::from",
            "<u16 as std::convert::From<u8>>::from",
            "<i8 as Into<i32>>::into",
            "<i8 as core::convert::Into<i32>>::into",
            "<i8 as std::convert::Into<i32>>::into",
        ] {
            assert!(classify(name).is_some(), "`{name}` must classify as a conversion");
        }
        assert_eq!(
            classify("<u16 as From<u8>>::from"),
            Some(Intrinsic::Conversion(Conversion::From))
        );
        assert_eq!(
            classify("<u8 as Into<u16>>::into"),
            Some(Intrinsic::Conversion(Conversion::Into))
        );
        // A module-qualified local trait is a different path, and is refused: the
        // same-dump lookup answers it, and the model must not.
        assert_eq!(classify("<MyT as m::From<u8>>::from"), None);
        assert_eq!(classify("<MyT as m::Into<u16>>::into"), None);
        assert_eq!(classify("<MyT as MyFrom<u8>>::from"), None);
        // An inherent method of the same name is not a trait call, so it names no
        // `From`/`Into` and is not modelled.
        assert_eq!(classify("core::num::<impl u8>::from"), None);
        assert_eq!(classify("from"), None);
        assert_eq!(classify("into"), None);
        // The `From`-like names that are not `From`.
        assert_eq!(classify("<u8 as TryFrom<u16>>::try_from"), None);
        assert_eq!(classify("<u16 as FromIterator<u8>>::from_iter"), None);
    }

    /// The two types a conversion reads out of its own name.
    #[test]
    fn a_conversion_reads_its_source_and_destination_from_the_name() {
        // `From`: the self type is the destination, the parameter the source.
        assert_eq!(
            conversion_types("<u16 as From<u8>>::from", Conversion::From),
            Some((Ty::U8, Ty::U16))
        );
        // `Into`: they are the other way round.
        assert_eq!(
            conversion_types("<u8 as Into<u16>>::into", Conversion::Into),
            Some((Ty::U8, Ty::U16))
        );
        assert_eq!(
            conversion_types("<i8 as Into<i64>>::into", Conversion::Into),
            Some((Ty::I8, Ty::I64))
        );
        // A signedness change is a widening too: `i16::from(u8)`.
        assert_eq!(
            conversion_types("<i16 as From<u8>>::from", Conversion::From),
            Some((Ty::U8, Ty::I16))
        );
        // A non-integer operand (the `bool`/`char` `From` impls) parses, but
        // `int_width` refuses it, so the caller reports the path unknown rather
        // than guessing a width.
        let (src, dst) = conversion_types("<u8 as From<bool>>::from", Conversion::From).unwrap();
        assert_eq!(src, Ty::Bool);
        assert_eq!(int_width(&src), None);
        assert_eq!(int_width(&dst), Some(8));
    }

    /// A widening conversion agrees with Rust's own `From`/`Into`, over every
    /// input of the source type.
    #[test]
    fn the_conversion_agrees_with_rust() {
        // `rust` is the language's own conversion, taken as a pair of functions
        // over the *bit pattern*: `bits` at the source width in, `bits` at the
        // destination width out. The oracle is the real `From` impl, so it cannot
        // drift from the model the way a second hand-written rule could.
        let check = |src_w: u8,
                     dst_w: u8,
                     src_signed: bool,
                     src_ty: Ty,
                     dst_ty: Ty,
                     rust: &dyn Fn(u64) -> u64,
                     label: &str| {
            smt::with_fresh(|| {
                let x = smt::var(src_w);
                let xi = smt::index(x);
                let Outcome::Value(v) = eval(
                    Intrinsic::Conversion(Conversion::From),
                    x,
                    x,
                    src_w,
                    src_signed,
                    dst_w,
                )
                .unwrap_or_else(|| panic!("{label}: must be modelled")) else {
                    panic!("{label}: a conversion produces a plain value");
                };
                for bits in 0..(1u64 << src_w) {
                    let got = smt::evaluate(v, |i| if i == xi { Some(bits) } else { None });
                    let want = rust(bits);
                    assert_eq!(
                        got,
                        Some(want),
                        "{label} at {bits:#x}: the model says {got:?}, Rust says {want:#x}"
                    );
                }
                // The name reads the same two types the case claims.
                assert_eq!(src_ty.is_signed(), src_signed, "{label}: source signedness");
                assert_eq!(int_width(&src_ty), Some(src_w), "{label}: source width");
                assert_eq!(int_width(&dst_ty), Some(dst_w), "{label}: destination width");
            });
        };

        let u8_to_u16 = |bits: u64| u64::from(u16::from(bits as u8));
        check(8, 16, false, Ty::U8, Ty::U16, &u8_to_u16, "u16::from(u8)");

        let i8_to_i16 = |bits: u64| u64::from(i16::from(i8::from_ne_bytes([bits as u8])) as u16);
        check(8, 16, true, Ty::I8, Ty::I16, &i8_to_i16, "i16::from(i8)");

        // A signedness *change* on a widening: `u8` -> `i16` zero-fills, so `255`
        // stays `255` and never becomes `-1`.
        let u8_to_i16 = |bits: u64| u64::from(i16::from(bits as u8) as u16);
        check(8, 16, false, Ty::U8, Ty::I16, &u8_to_i16, "i16::from(u8)");

        let i8_to_i64 = |bits: u64| i64::from(i8::from_ne_bytes([bits as u8])) as u64;
        check(8, 64, true, Ty::I8, Ty::I64, &i8_to_i64, "i64::from(i8)");

        let u8_to_u32 = |bits: u64| u64::from(u32::from(bits as u8));
        check(8, 32, false, Ty::U8, Ty::U32, &u8_to_u32, "u32::from(u8)");

        let i16_to_i32 =
            |bits: u64| u64::from(i32::from(i16::from_ne_bytes((bits as u16).to_ne_bytes())) as u32);
        check(16, 32, true, Ty::I16, Ty::I32, &i16_to_i32, "i32::from(i16)");

        // The named points, so a failure names the value that broke. `-1` is the
        // one that separates sign-extension from zero-filling, and `0xff`/`0x80`
        // are the extremes of the source type.
        let widen = |src_w: u8, dst_w: u8, src_signed: bool, bits: u64| {
            smt::with_fresh(|| {
                let x = smt::var(src_w);
                let xi = smt::index(x);
                let Outcome::Value(v) = eval(
                    Intrinsic::Conversion(Conversion::From),
                    x,
                    x,
                    src_w,
                    src_signed,
                    dst_w,
                )
                .expect("a widening conversion is modelled") else {
                    panic!("a conversion produces a plain value");
                };
                smt::evaluate(v, |i| if i == xi { Some(bits) } else { None })
            })
        };
        for (src_w, dst_w, signed, bits, want, why) in [
            (8u8, 16u8, false, 0xff, 0xffu64, "unsigned widens by zero-fill"),
            (8, 16, true, 0xff, 0xffff, "-1i8 widens to -1i16, not 255"),
            (8, 16, true, 0x80, 0xff80, "i8::MIN widens to i16::MIN"),
            (8, 64, true, 0x80, 0xffff_ffff_ffff_ff80, "i8::MIN widens to i64::MIN"),
            (8, 16, false, 0x80, 0x80, "u8::128 stays 128 in a wider unsigned"),
            (16, 32, true, 0x8000, 0xffff_8000, "i16::MIN widens to i32::MIN"),
        ] {
            assert_eq!(
                widen(src_w, dst_w, signed, bits),
                Some(want),
                "{why} ({bits:#x})"
            );
        }

        // A narrowing conversion is refused, so a call `core` does not implement is
        // never read as one it does. (A same-width call *is* `core`'s reflexive
        // `impl<T> From<T> for T` and is modelled, so it is not refused here.)
        smt::with_fresh(|| {
            let x = smt::var(16);
            assert!(
                eval(Intrinsic::Conversion(Conversion::From), x, x, 16, false, 8).is_none(),
                "a narrowing conversion must be refused"
            );
        });
        // A same-width call *is* `core`'s reflexive `impl<T> From<T> for T`, so it
        // must be modelled rather than refused. (Its identity semantics are pinned
        // end to end in the corpus; here it is enough that it is not a refusal.)
        smt::with_fresh(|| {
            let x = smt::var(16);
            assert!(
                eval(Intrinsic::Conversion(Conversion::From), x, x, 16, false, 16).is_some(),
                "a same-width conversion is the identity `core` implements, not a refusal"
            );
        });
    }

    /// F9: a rotation is modelled only at a power-of-two width.
    ///
    /// The amount is reduced with the low `log2(w)` bits (one `and`, no divider),
    /// which is `n mod w` only when `w` is a power of two. At `w == 12` the
    /// reduction is modulo 4, so `rotate_left(1, 4)` would model as `1` where Rust
    /// gives `16` -- a wrong value, not a weaker proof. Every real integer type is
    /// a power-of-two width, so the restriction costs no coverage.
    #[test]
    fn a_rotation_needs_a_power_of_two_width() {
        let rot = Intrinsic::Rotate(RotateKind::Left);
        for w in [8u8, 16, 32, 64] {
            assert!(is_modelled(rot, w, false), "a rotation at width {w} must be modelled");
        }
        for w in [12u8, 24, 48] {
            assert!(
                !is_modelled(rot, w, false),
                "a rotation at the non-power-of-two width {w} must be refused"
            );
        }
        // The engine's own width bound is unchanged.
        for w in [0u8, 65] {
            assert!(!is_modelled(Intrinsic::Rotate(RotateKind::Right), w, false));
        }
    }
}

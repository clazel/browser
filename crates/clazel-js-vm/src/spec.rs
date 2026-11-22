//! The bytecode's semantics (phase-7.md item 7.4): NaN-boxed values, the
//! abstract machine, and `spec fn step`.
//!
//! Sources:
//! - ECMA-262, 17th edition (ES2026), `tc39/ecma262` commit
//!   `0248456c758431e4bb8e5d26333ff1865123c9cd` (see
//!   `crates/clazel-js-lexer/SPEC-PIN.md`). Section numbers below are the
//!   numbers of that commit's `spec.html`, which does not print them: they
//!   are computed from the nesting of its `emu-clause` elements, and each
//!   cited clause is named by its anchor (`#sec-...`) in the doc comment of
//!   the function that implements it.
//! - phase-7.md "Shapes fixed here for the JIT" and 7.4; jit.md J.1, J.5, J.10.
//!
//! Nothing here runs. This file defines what the interpreter's handlers and
//! the JIT's lowerings must refine; the part a reviewer reads is this file,
//! and [`crate::ops`] for the op list.
//!
//! # Structure
//!
//! 1. Values: the NaN-boxing (`enc_*`, `decode`).
//! 2. Numbers: ECMA-262's Number operations on IEEE 754 bit patterns.
//! 3. The machine: frames in the value-stack region, the heap, the code.
//! 4. `fast_path`, `fast_step`, `handler` and `step`.
//!
//! # Modelling choices
//!
//! Each is a deliberate difference in form from the standard or from phase-7.md,
//! with the argument that the meaning is unchanged, or the stated extension.
//!
//! - **A Number is its IEEE 754 binary64 bit pattern, a `u64`.** Verus has no
//!   floating-point arithmetic in specs, and a bit pattern is what the
//!   region holds. Everything the standard says about a Number
//!   (`NaN`, `+0`, `-0`, `+∞`, finite) is a predicate on the bits
//!   (`is_nan`, `is_pos_zero`, ...). `x is y` in the standard, for non-NaN
//!   Numbers, is bit equality. `ℝ(x) < ℝ(y)` for finite Numbers is
//!   `f64_key(x) < f64_key(y)`, which is correct because IEEE 754's
//!   sign-magnitude layout orders finite and infinite values as integers,
//!   with `-0` and `+0` both mapping to key 0 (`lemma_number_equal_key`, `lemma_less_than_asymmetric`).
//! - **The rounding of an exact real result is uninterpreted.**
//!   `𝔽(ℝ(x) + ℝ(y))` (and the same for `×`, `/`, and the remainder's
//!   `r`) is `f64_add_finite`, `f64_mul_finite`, `f64_div_finite`,
//!   `f64_rem_finite`: `spec fn`s without bodies. The standard defines the
//!   function ("the Number value for", §6.1.6.1, roundTiesToEven) but it is
//!   a statement about real numbers, which Verus cannot compute here. The
//!   special cases around it (`NaN`, infinities, zeros: steps 1 to 7 of each
//!   Number method) *are* transcribed. The assumption made, and listed for
//!   VERIFICATION.md's TCB when the JIT's back end uses it, is that the
//!   target's `addsd`/`mulsd`/`divsd` (x86-64) and `fadd`/`fmul`/`fdiv`
//!   (A64) in the default rounding mode agree with those four functions on
//!   finite arguments, and `f64_rem_finite` is C's `fmod`
//!   ("the result of a floating-point remainder ... is analogous to ...
//!   fmod", the standard's note on Number::remainder).
//! - **int32 and double encodings of one Number are both Numbers.** The
//!   standard has one Number type; the machine has two encodings, `Int32(i)`
//!   and `Double(bits)`, and `num_bits` maps each to the double that
//!   represents the same Number. An arithmetic op chooses the encoding of
//!   its result by a fixed rule (`arith_add`, ...: int32 when both operands
//!   are int32 and the exact result is an int32 and not `-0`, a double
//!   otherwise). The rule is pinned here, not left free, because the JIT's
//!   proof refines `step` exactly, and a lowering that narrowed a double to
//!   an int32 would be a different result. Whether to narrow is then an
//!   explicit, provable change to this file.
//! - **Fast paths are conditions on the whole state, not on types.** A
//!   guarded op's `fast_path` is what the JIT tests inline: operand tags,
//!   shape ids, bounds. `step` is `fast_step` when it holds and `handler`
//!   when it does not. Nothing else is interpreted: whether the handler
//!   allocates, throws or calls JS is the handler's business.
//! - **A handler is one uninterpreted function of the whole state.**
//!   `handler(h, s, op)` returns the next state, including `pc`. It has no
//!   body and no axioms, so nothing is proven about it here. Test262 is the
//!   evidence for each handler (phase-7.md 7.4, 7.8). The properties the JIT
//!   needs of handlers (they touch only the region window of the current
//!   call chain, they preserve heap well-formedness) will be stated as the
//!   handlers' contracts in 7.8, not assumed here.
//! - **Exceptions are handler results.** Throwing and unwinding set
//!   `exception`, restore `fp`, and move `pc` to a catch handler (or leave
//!   the frame), all inside `handler`. The exception table is a handler
//!   input, so it is not in this state's `Code`.
//! - **The heap is an abstract map** from arena index (`u32`) to `Cell`,
//!   where a cell has the `u16` generation the arena would hold. A reference
//!   is *live* (`live_cell`) when the index is in the map and the
//!   generations agree. A stale reference is therefore never an alias: it is
//!   not live, so no fast path accepts it and the handler reports the
//!   defined error (phase-7.md 7.0(f)). Free-list order, string contents,
//!   BigInt limbs and so on are the heap crate's (7.5); here a cell only
//!   says what a fast path reads: its shape id, its slot values, its dense
//!   elements, and for functions and environments their code and parent.
//! - **Shapes are ids, and a shape determines slot count only through the
//!   inline cache.** An inline-cache entry is `(shape, slot)`. A hit
//!   re-checks `slot < slots.len()` so `step` is total; the JIT may drop that
//!   test if it proves the invariant `ic_wf` ("any object with the cached
//!   shape has the slot"), which the heap maintains (7.5). Shape id `0` is
//!   never an object's shape in a cache, so an empty entry never hits.
//!   Inline caches here are own-property caches. A prototype-chain hit (a
//!   method on a class) misses and goes to the handler, until the cache
//!   gains a holder and a validity cell.
//! - **The return address is a RAW value** (`TAG_RAW`): bits 24 to 47 hold
//!   the caller's frame base and bits 0 to 23 the caller's `pc`, so that
//!   every slot of a frame, including the header, is a well-formed
//!   `u64`-boxed value and the collector scans a frame without a layout
//!   table (phase-7.md 7.0(f): the value stack is a root). This limits a
//!   region to `2^24 - 1` slots and a function to `2^24 - 1` ops; the
//!   fast paths that build or read an address check the limit, so a larger
//!   frame goes to a handler (which can fall back to an out-of-line address).
//!   The return address does not name the caller's destination register: it
//!   is read from the call op at the saved `pc` (`call_dst`).
//! - **The argument-count slot carries the frame kind.** The header slot
//!   "argument count" holds an int32 `argc | kind << 28` (kind 0: plain
//!   call, 1: construct call, 2: generator or async frame). A plain return
//!   is fast; the other two kinds return through a handler, because a
//!   construct call substitutes `this` for a non-object result ([[Construct]],
//!   §10.2.2) and a generator's return allocates an iterator result
//!   (§27.5.3.3 GeneratorResume).
//! - **A call passes arguments by copy.** The arguments are `argc` consecutive
//!   caller registers (`Call::args`). The callee frame is pushed at the first
//!   slot after the caller's frame and arguments are copied into it, missing
//!   parameters filled with `undefined`. Calls with more arguments than
//!   parameters, any sloppy-mode `this` coercion, any `arguments` object and
//!   every non-ordinary callee (bound, native, class constructor, generator,
//!   async, Proxy) are not fast (`FnInfo::fast_callable`), so go to the call
//!   handler, which pushes the same frame layout.
//! - **The termination flag** (phase-7.md, "Limits and stopping") is a read-only
//!   state field, `terminate`. A `Loop` back-edge and a `Call` are guarded on it
//!   being clear; when it is set the handler ends the evaluation with the
//!   uncatchable `Terminated` error. Setting it is another thread's act, so
//!   `step` never changes it.
//! - **Counters** for tiering (function entries, back-edges) are not in the
//!   state: they are not observable by JS.
//! - **Op operands are `nat`s and the ops are an enum**, not a bit
//!   encoding. `op_wf` is the check a compiler's output must pass.
//! - **A value of tag `0xFFFC` (RAW) and the hole** are internal values: they
//!   never reach a JS-visible register except through the TDZ and array-hole
//!   uses documented on `Op::LoadHole`.
//!
//! # Errata
//!
//! Number::multiply (§6.1.6.1.4) as written returns `+0` for `+0 × -5`
//! (step 6, `𝔽(ℝ(x) × ℝ(y))`, with `ℝ(+0) × ℝ(-5) = 0` and §6.1.6.1's "Number
//! value for", which gives `-0` only for a negative real). Every engine
//! and IEEE 754 give `-0`. `number_multiply` implements the evident intent
//! (a zero result has the sign of the product of the operand signs) in an
//! added step 5a, and `docs/ERRATA.md` has the entry.

#[allow(unused_imports)]
use vstd::prelude::*;

pub use crate::ops::*;

verus! {

// =====================================================================
// 1. Values (phase-7.md "Shapes fixed here for the JIT")
// =====================================================================
//
// A value is a `u64`.
//
// - A double is itself, with every NaN replaced by the canonical NaN
//   `0x7FF8_0000_0000_0000`. Then the top 16 bits of a double are at most
//   `0xFFF8`, and `0xFFF8_0000_0000_0000` (the negative quiet NaN) is the
//   only double-range pattern that is *not* a value.
// - Everything else is a NaN-space pattern with a 16-bit tag in bits 48..63:
//     0xFFF9  int32: bits 32..47 zero, the int32 in bits 0..31
//     0xFFFA  special: bits 0..47 are 0 undefined, 1 null, 2 false, 3 true,
//             4 hole
//     0xFFFB  heap reference: generation (u16) in bits 32..47, arena
//             index (u32) in bits 0..31
//     0xFFFC  raw: a 48-bit payload (header slots: return address)
//   Tags 0xFFFD..0xFFFF are reserved and not values.

/// `undefined`.
pub const UNDEFINED: u64 = 0xFFFA_0000_0000_0000;
/// `null`.
pub const NULL: u64 = 0xFFFA_0000_0000_0001;
/// `false`.
pub const FALSE: u64 = 0xFFFA_0000_0000_0002;
/// `true`.
pub const TRUE: u64 = 0xFFFA_0000_0000_0003;
/// The hole: an uninitialized binding or an absent array element.
pub const HOLE: u64 = 0xFFFA_0000_0000_0004;
/// The canonical NaN, the only NaN a value may be.
pub const CANON_NAN: u64 = 0x7FF8_0000_0000_0000;
/// The return-address payload of the outermost frame: no caller.
pub const RET_NONE: u64 = 0xFFFF_FFFF_FFFF;

/// A decoded value.
pub enum Val {
    /// A double (not an int32), by its canonical bits.
    Double(u64),
    /// An int32.
    Int32(i32),
    /// `undefined`.
    Undefined,
    /// `null`.
    Null,
    /// A boolean.
    Bool(bool),
    /// The hole.
    Hole,
    /// A heap reference: arena index and generation.
    Ref(u32, u16),
    /// A raw 48-bit payload.
    Raw(u64),
    /// A bit pattern that is not a value.
    Invalid,
}

/// IEEE 754 exponent field of a double's bits.
pub open spec fn f64_exp(b: u64) -> u64 {
    (b >> 52) & 0x7FF
}

/// IEEE 754 fraction field of a double's bits.
pub open spec fn f64_frac(b: u64) -> u64 {
    b & 0xF_FFFF_FFFF_FFFF
}

/// IEEE 754 sign bit of a double's bits (1 for negative).
pub open spec fn f64_sign(b: u64) -> u64 {
    b >> 63
}

/// The Number is `NaN`.
pub open spec fn is_nan(b: u64) -> bool {
    f64_exp(b) == 0x7FF && f64_frac(b) != 0
}

/// The Number is `+∞`.
pub open spec fn is_pos_inf(b: u64) -> bool {
    b == 0x7FF0_0000_0000_0000
}

/// The Number is `-∞`.
pub open spec fn is_neg_inf(b: u64) -> bool {
    b == 0xFFF0_0000_0000_0000
}

/// The Number is `+∞` or `-∞`.
pub open spec fn is_inf(b: u64) -> bool {
    is_pos_inf(b) || is_neg_inf(b)
}

/// The Number is `+0`.
pub open spec fn is_pos_zero(b: u64) -> bool {
    b == 0
}

/// The Number is `-0`.
pub open spec fn is_neg_zero(b: u64) -> bool {
    b == 0x8000_0000_0000_0000
}

/// The Number is `+0` or `-0`.
pub open spec fn is_zero(b: u64) -> bool {
    is_pos_zero(b) || is_neg_zero(b)
}

/// The Number is finite (not `NaN`, not an infinity).
pub open spec fn is_finite(b: u64) -> bool {
    f64_exp(b) != 0x7FF
}

/// The bits are a double *value*: in the double range, and no NaN but the
/// canonical one.
pub open spec fn is_double(v: u64) -> bool {
    (v >> 48) < 0xFFF9 && (is_nan(v) ==> v == CANON_NAN)
}

/// Encode a double: canonicalize NaN, keep every other pattern.
pub open spec fn enc_double(bits: u64) -> u64 {
    if is_nan(bits) { CANON_NAN } else { bits }
}

/// Encode an int32: tag `0xFFF9`, bits 32..47 zero.
pub open spec fn enc_int32(i: i32) -> u64 {
    0xFFF9_0000_0000_0000u64 | (((i as u32) as u64) & 0xFFFF_FFFF)
}

/// Encode a heap reference: tag `0xFFFB`, generation, arena index.
pub open spec fn enc_ref(index: u32, generation: u16) -> u64 {
    0xFFFB_0000_0000_0000u64 | ((generation as u64) << 32) | (index as u64)
}

/// Encode a raw payload (low 48 bits).
pub open spec fn enc_raw(p: u64) -> u64 {
    0xFFFC_0000_0000_0000u64 | (p & 0xFFFF_FFFF_FFFF)
}

/// Encode a boolean.
pub open spec fn enc_bool(b: bool) -> u64 {
    if b { TRUE } else { FALSE }
}

/// Decode a value (total: a pattern that is not a value gives `Invalid`).
pub open spec fn decode(v: u64) -> Val {
    let tag = v >> 48;
    if tag < 0xFFF9 {
        if is_double(v) { Val::Double(v) } else { Val::Invalid }
    } else if tag == 0xFFF9 {
        if (v >> 32) & 0xFFFF == 0 {
            Val::Int32(((v & 0xFFFF_FFFF) as u32) as i32)
        } else {
            Val::Invalid
        }
    } else if tag == 0xFFFA {
        let k = v & 0xFFFF_FFFF_FFFF;
        if k == 0 { Val::Undefined }
        else if k == 1 { Val::Null }
        else if k == 2 { Val::Bool(false) }
        else if k == 3 { Val::Bool(true) }
        else if k == 4 { Val::Hole }
        else { Val::Invalid }
    } else if tag == 0xFFFB {
        Val::Ref((v & 0xFFFF_FFFF) as u32, ((v >> 32) & 0xFFFF) as u16)
    } else if tag == 0xFFFC {
        Val::Raw(v & 0xFFFF_FFFF_FFFF)
    } else {
        Val::Invalid
    }
}

/// Encode a decoded value (the inverse of `decode`, `lemma_encode_decode`).
/// `Invalid` has no encoding; `0` is arbitrary.
pub open spec fn encode(x: Val) -> u64 {
    match x {
        Val::Double(b) => enc_double(b),
        Val::Int32(i) => enc_int32(i),
        Val::Undefined => UNDEFINED,
        Val::Null => NULL,
        Val::Bool(b) => enc_bool(b),
        Val::Hole => HOLE,
        Val::Ref(i, g) => enc_ref(i, g),
        Val::Raw(p) => enc_raw(p),
        Val::Invalid => 0,
    }
}

/// The bits are a well-formed value.
pub open spec fn value_wf(v: u64) -> bool {
    !(decode(v) is Invalid)
}

/// The value is an int32.
pub open spec fn is_int32(v: u64) -> bool {
    decode(v) is Int32
}

/// The int32 payload of an int32 value (0 for any other value).
pub open spec fn int32_of(v: u64) -> i32 {
    match decode(v) {
        Val::Int32(i) => i,
        _ => 0,
    }
}

/// The value is a Number: an int32 or a double.
pub open spec fn is_number(v: u64) -> bool {
    decode(v) is Int32 || decode(v) is Double
}

/// The value is a heap reference.
pub open spec fn is_ref(v: u64) -> bool {
    decode(v) is Ref
}

// =====================================================================
// 2. Numbers (ECMA-262 §6.1.6.1 and §7.1)
// =====================================================================

/// An int32 fits.
pub open spec fn fits_i32(n: int) -> bool {
    -2147483648 <= n && n <= 2147483647
}

/// `floor(log2(n))` for `n >= 1` (0 for 0 and 1).
pub open spec fn ilog2(n: nat) -> nat
    decreases n,
{
    if n <= 1 { 0 } else { 1 + ilog2((n / 2) as nat) }
}

/// The double that represents the integer `n`, exactly, for `|n| < 2^53`
/// (every int32 and uint32 qualify). `+0` for 0 (the integer 0 is `+0`).
pub open spec fn f64_of_int(n: int) -> u64
    recommends -9007199254740992 < n < 9007199254740992,
{
    if n == 0 {
        0
    } else {
        let neg = n < 0;
        let mag: nat = (if neg { -n } else { n }) as nat;
        let k = ilog2(mag);
        let frac: int = mag * vstd::arithmetic::power2::pow2((52 - k) as nat) - vstd::arithmetic::power2::pow2(52);
        let exp: int = (k + 1023) as int;
        ((if neg { 0x8000_0000_0000_0000int } else { 0int }) + exp * 4503599627370496int + frac) as u64
    }
}

/// The double that represents an int32.
pub open spec fn i32_to_f64(i: i32) -> u64 {
    f64_of_int(i as int)
}

/// The double that represents the Number a value holds: an int32's integer,
/// or a double itself. (A non-Number gives itself, unused.)
pub open spec fn num_bits(v: u64) -> u64 {
    match decode(v) {
        Val::Int32(i) => i32_to_f64(i),
        _ => v,
    }
}

/// The value for an integer result: an int32 when it fits, else the double
/// that represents it (for `|n| < 2^53`).
pub open spec fn enc_number_int(n: int) -> u64 {
    if fits_i32(n) { enc_int32(n as i32) } else { enc_double(f64_of_int(n)) }
}

/// `x > +0` for a non-NaN Number: positive and not a zero.
pub open spec fn gt_pos_zero(x: u64) -> bool {
    f64_sign(x) == 0 && !is_zero(x)
}

/// `x < -0` for a non-NaN Number: negative and not a zero.
pub open spec fn lt_neg_zero(x: u64) -> bool {
    f64_sign(x) == 1 && !is_zero(x)
}

/// The rounded sum of two finite Numbers: `𝔽(ℝ(x) + ℝ(y))`, with the
/// rounding of §6.1.6.1 ("the Number value for"). Uninterpreted, see the
/// modelling choices.
pub uninterp spec fn f64_add_finite(x: u64, y: u64) -> u64;

/// `𝔽(ℝ(x) × ℝ(y))` for finite non-zero `x`, `y`. Uninterpreted.
pub uninterp spec fn f64_mul_finite(x: u64, y: u64) -> u64;

/// `𝔽(ℝ(x) / ℝ(y))` for finite non-zero `x`, `y`. Uninterpreted.
pub uninterp spec fn f64_div_finite(x: u64, y: u64) -> u64;

/// `𝔽(r)` of Number::remainder step 11, for finite non-zero `n`, `d`:
/// `r = ℝ(n) - ℝ(d) × truncate(ℝ(n) / ℝ(d))`, with `-0` when `r = 0` and
/// `n < -0` (steps 10 and 11 together). Uninterpreted.
pub uninterp spec fn f64_rem_finite(n: u64, d: u64) -> u64;

/// Number::unaryMinus, §6.1.6.1.1
/// (`#sec-numeric-types-number-unaryMinus`).
pub open spec fn number_unary_minus(x: u64) -> u64 {
    if is_nan(x) {
        CANON_NAN // 1. "If x is NaN, return NaN."
    } else {
        x ^ 0x8000_0000_0000_0000 // 2. "Return the negation of x"
    }
}

/// Number::add, §6.1.6.1.7 (`#sec-numeric-types-number-add`).
pub open spec fn number_add(x: u64, y: u64) -> u64 {
    if is_nan(x) || is_nan(y) {
        CANON_NAN // 1.
    } else if is_pos_inf(x) && is_neg_inf(y) {
        CANON_NAN // 2.
    } else if is_neg_inf(x) && is_pos_inf(y) {
        CANON_NAN // 3.
    } else if is_inf(x) {
        x // 4.
    } else if is_inf(y) {
        y // 5.
    }
    // 6. "Assert: x and y are both finite."
    else if is_neg_zero(x) && is_neg_zero(y) {
        x // 7. "return -0"
    } else {
        f64_add_finite(x, y) // 8. "Return 𝔽(ℝ(x) + ℝ(y))."
    }
}

/// Number::subtract, §6.1.6.1.8 (`#sec-numeric-types-number-subtract`).
pub open spec fn number_subtract(x: u64, y: u64) -> u64 {
    number_add(x, number_unary_minus(y)) // 1.
}

/// Number::multiply, §6.1.6.1.4 (`#sec-numeric-types-number-multiply`).
/// Step 5a is the erratum (docs/ERRATA.md): see the file header.
pub open spec fn number_multiply(x: u64, y: u64) -> u64 {
    if is_nan(x) || is_nan(y) {
        CANON_NAN // 1.
    } else if is_inf(x) {
        // 2.
        if is_zero(y) { CANON_NAN } // 2.a.
        else if gt_pos_zero(y) { x } // 2.b.
        else { number_unary_minus(x) } // 2.c.
    } else if is_inf(y) {
        // 3.
        if is_zero(x) { CANON_NAN } // 3.a.
        else if gt_pos_zero(x) { y } // 3.b.
        else { number_unary_minus(y) } // 3.c.
    } else if is_neg_zero(x) {
        // 4.
        if is_neg_zero(y) || lt_neg_zero(y) { 0 } // 4.a. "return +0"
        else { 0x8000_0000_0000_0000 } // 4.b. "Return -0"
    } else if is_neg_zero(y) {
        // 5.
        if lt_neg_zero(x) { 0 } // 5.a. "return +0"
        else { 0x8000_0000_0000_0000 } // 5.b. "Return -0"
    } else if is_pos_zero(x) || is_pos_zero(y) {
        // 5a (erratum): the other operand is finite and not NaN; the result is
        // a zero whose sign is the exclusive or of the operand signs.
        (f64_sign(x) ^ f64_sign(y)) << 63
    } else {
        f64_mul_finite(x, y) // 6. "Return 𝔽(ℝ(x) × ℝ(y))."
    }
}

/// Number::divide, §6.1.6.1.5 (`#sec-numeric-types-number-divide`).
pub open spec fn number_divide(x: u64, y: u64) -> u64 {
    if is_nan(x) || is_nan(y) {
        CANON_NAN // 1.
    } else if is_inf(x) {
        // 2.
        if is_inf(y) { CANON_NAN } // 2.a.
        else if is_pos_zero(y) || gt_pos_zero(y) { x } // 2.b.
        else { number_unary_minus(x) } // 2.c.
    } else if is_pos_inf(y) {
        // 3.
        if is_pos_zero(x) || gt_pos_zero(x) { 0 } // 3.a. "return +0"
        else { 0x8000_0000_0000_0000 } // 3.b. "Return -0"
    } else if is_neg_inf(y) {
        // 4.
        if is_pos_zero(x) || gt_pos_zero(x) { 0x8000_0000_0000_0000 } // 4.a.
        else { 0 } // 4.b.
    } else if is_zero(x) {
        // 5.
        if is_zero(y) { CANON_NAN } // 5.a.
        else if gt_pos_zero(y) { x } // 5.b.
        else { number_unary_minus(x) } // 5.c.
    } else if is_pos_zero(y) {
        // 6.
        if gt_pos_zero(x) { 0x7FF0_0000_0000_0000 } // 6.a. "return +∞"
        else { 0xFFF0_0000_0000_0000 } // 6.b. "Return -∞"
    } else if is_neg_zero(y) {
        // 7.
        if gt_pos_zero(x) { 0xFFF0_0000_0000_0000 } // 7.a. "return -∞"
        else { 0x7FF0_0000_0000_0000 } // 7.b. "Return +∞"
    } else {
        f64_div_finite(x, y) // 8. "Return 𝔽(ℝ(x) / ℝ(y))."
    }
}

/// Number::remainder, §6.1.6.1.6 (`#sec-numeric-types-number-remainder`).
pub open spec fn number_remainder(n: u64, d: u64) -> u64 {
    if is_nan(n) || is_nan(d) {
        CANON_NAN // 1.
    } else if is_inf(n) {
        CANON_NAN // 2.
    } else if is_inf(d) {
        n // 3.
    } else if is_zero(d) {
        CANON_NAN // 4.
    } else if is_zero(n) {
        n // 5.
    } else {
        // 6. "Assert: n and d are finite and non-zero."
        // 7. to 11. quotient, q, r, the -0 case, 𝔽(r): f64_rem_finite.
        f64_rem_finite(n, d)
    }
}

/// The integer ordering key of a non-NaN Number: sign-magnitude as an
/// integer. `-0` and `+0` are both 0.
pub open spec fn f64_key(b: u64) -> int {
    let m = (b & 0x7FFF_FFFF_FFFF_FFFF) as int;
    if f64_sign(b) == 1 { -m } else { m }
}

/// Number::lessThan, §6.1.6.1.12 (`#sec-numeric-types-number-lessThan`).
/// `None` is `undefined`.
pub open spec fn number_less_than(x: u64, y: u64) -> Option<bool> {
    if is_nan(x) {
        None // 1.
    } else if is_nan(y) {
        None // 2.
    } else if x == y {
        Some(false) // 3. "If x is y, return false."
    } else if is_pos_zero(x) && is_neg_zero(y) {
        Some(false) // 4.
    } else if is_neg_zero(x) && is_pos_zero(y) {
        Some(false) // 5.
    } else if is_pos_inf(x) {
        Some(false) // 6.
    } else if is_pos_inf(y) {
        Some(true) // 7.
    } else if is_neg_inf(y) {
        Some(false) // 8.
    } else if is_neg_inf(x) {
        Some(true) // 9.
    }
    // 10. "Assert: x and y are finite."
    else {
        Some(f64_key(x) < f64_key(y)) // 11. and 12. ℝ(x) < ℝ(y)
    }
}

/// Number::equal, §6.1.6.1.13 (`#sec-numeric-types-number-equal`).
pub open spec fn number_equal(x: u64, y: u64) -> bool {
    if is_nan(x) {
        false // 1.
    } else if is_nan(y) {
        false // 2.
    } else if x == y {
        true // 3. "If x is y, return true."
    } else if is_pos_zero(x) && is_neg_zero(y) {
        true // 4.
    } else if is_neg_zero(x) && is_pos_zero(y) {
        true // 5.
    } else {
        false // 6.
    }
}

/// `truncate(|ℝ(b)|)` for a finite Number: the integer part of the
/// magnitude. A finite double is `m × 2^k` with `m = 2^52 + frac` and
/// `k = exponent - 1075` (a zero exponent field is a subnormal or zero, of
/// magnitude below 1).
pub open spec fn f64_trunc_abs(b: u64) -> nat {
    let e: int = f64_exp(b) as int;
    if e == 0 {
        0
    } else {
        let m: int = vstd::arithmetic::power2::pow2(52) + f64_frac(b) as int;
        let k: int = e - 1075;
        if k >= 0 { (m * vstd::arithmetic::power2::pow2(k as nat)) as nat } else { (m / (vstd::arithmetic::power2::pow2((-k) as nat) as int)) as nat }
    }
}

/// `int modulo 2^32` of ToInt32 and ToUint32, step 4: `truncate(ℝ(number))`
/// reduced into `[0, 2^32)`.
pub open spec fn f64_int32bit(b: u64) -> nat {
    let t: int = f64_trunc_abs(b) as int;
    let i: int = if f64_sign(b) == 1 { -t } else { t };
    (i % 4294967296int) as nat
}

/// ToInt32, §7.1.6 (`#sec-toint32`), on a Number (step 1's ToNumber is the
/// identity on a Number).
pub open spec fn to_int32(b: u64) -> i32 {
    // 2. "If number is not finite or number is either +0 or -0, return +0."
    if !is_finite(b) || is_zero(b) {
        0
    } else {
        let int32bit: int = f64_int32bit(b) as int; // 3. and 4.
        if int32bit >= 2147483648int {
            (int32bit - 4294967296int) as i32 // 5.
        } else {
            int32bit as i32 // 6.
        }
    }
}

/// ToUint32, §7.1.7 (`#sec-touint32`), on a Number.
pub open spec fn to_uint32(b: u64) -> u32 {
    // 2.
    if !is_finite(b) || is_zero(b) {
        0
    } else {
        f64_int32bit(b) as u32 // 3. to 5.
    }
}

/// `n` reduced into the int32 range, two's complement ("exactly representable
/// as a 32-bit two's complement bit string" in §6.1.6.1.9 and .10).
pub open spec fn wrap_i32(n: int) -> i32 {
    let m: int = n % 4294967296int;
    if m >= 2147483648int { (m - 4294967296int) as i32 } else { m as i32 }
}

/// Number::bitwiseNOT, §6.1.6.1.2, on the Number's bits.
pub open spec fn number_bitwise_not(x: u64) -> i32 {
    let old_value = to_int32(x); // 1.
    (-1 - old_value as int) as i32 // 2. "bitwise complement of oldValue"
}

/// Number::leftShift, §6.1.6.1.9, giving the int32 result.
pub open spec fn number_left_shift(x: u64, y: u64) -> i32 {
    let l_num = to_int32(x); // 1.
    let r_num = to_uint32(y); // 2.
    let shift_count: nat = (r_num as nat) % 32; // 3.
    wrap_i32(l_num as int * vstd::arithmetic::power2::pow2(shift_count) as int) // 4.
}

/// Number::signedRightShift, §6.1.6.1.10, giving the int32 result.
pub open spec fn number_signed_right_shift(x: u64, y: u64) -> i32 {
    let l_num = to_int32(x); // 1.
    let r_num = to_uint32(y); // 2.
    let shift_count: nat = (r_num as nat) % 32; // 3.
    // 4. Sign-extending shift: floor division by 2^shiftCount.
    (l_num as int / vstd::arithmetic::power2::pow2(shift_count) as int) as i32
}

/// Number::unsignedRightShift, §6.1.6.1.11, giving the uint32 result as an
/// integer.
pub open spec fn number_unsigned_right_shift(x: u64, y: u64) -> nat {
    let l_num = to_uint32(x); // 1.
    let r_num = to_uint32(y); // 2.
    let shift_count: nat = (r_num as nat) % 32; // 3.
    (l_num as nat) / vstd::arithmetic::power2::pow2(shift_count) // 4. Zero-filling shift.
}

/// Number::bitwiseAND, §6.1.6.1.17 (the shared helper of §6.1.6.1.16
/// NumberBitwiseOp: both operands through ToInt32, the operation on the
/// 32-bit strings, the result as an int32).
pub open spec fn number_bitwise_and(x: u64, y: u64) -> i32 {
    to_int32(x) & to_int32(y)
}

/// Number::bitwiseOR, §6.1.6.1.19.
pub open spec fn number_bitwise_or(x: u64, y: u64) -> i32 {
    to_int32(x) | to_int32(y)
}

/// Number::bitwiseXOR, §6.1.6.1.18.
pub open spec fn number_bitwise_xor(x: u64, y: u64) -> i32 {
    to_int32(x) ^ to_int32(y)
}

/// ToBoolean, §7.1.2 (`#sec-toboolean`), on the values that need no heap:
/// `None` for a heap reference (a String or BigInt needs its length, an
/// object may be IsHTMLDDA) and for internal values.
pub open spec fn to_boolean_fast(v: u64) -> Option<bool> {
    match decode(v) {
        Val::Undefined => Some(false), // 3. "If argument is undefined, null, false, +0, -0, NaN, 0n, or the empty String, return false."
        Val::Null => Some(false),
        Val::Bool(b) => Some(b), // 1. "If argument is a Boolean, return argument."
        Val::Int32(i) => Some(i != 0),
        Val::Double(b) => Some(!(is_zero(b) || is_nan(b))),
        _ => None,
    }
}

/// IsStrictlyEqual, §7.2.14 (`#sec-isstrictlyequal`), where it needs no heap
/// contents: `None` when two distinct heap references might be equal Strings
/// or BigInts (the handler compares contents).
pub open spec fn strict_eq_fast(a: u64, b: u64) -> Option<bool> {
    if !value_wf(a) || !value_wf(b) || decode(a) is Hole || decode(b) is Hole
        || decode(a) is Raw || decode(b) is Raw {
        None
    } else if is_number(a) && is_number(b) {
        Some(number_equal(num_bits(a), num_bits(b))) // 2. "If x is a Number, return Number::equal(x, y)."
    } else if is_ref(a) && is_ref(b) {
        if a == b { Some(true) } else { None } // 3. SameValueNonNumber, equal cells
    } else if is_ref(a) || is_ref(b) {
        Some(false) // 1. "If SameType(x, y) is false, return false."
    } else {
        Some(a == b) // 1., 3.: undefined, null and booleans
    }
}

/// The relational operators' result on Numbers, §13.10.1: `lt` is
/// `IsLessThan` §7.2.12 steps for two Numbers
/// ("If nx is a Number, return Number::lessThan(nx, ny)") with the
/// operand order and `undefined` handling of each operator.
pub open spec fn rel_lt(x: u64, y: u64) -> bool {
    match number_less_than(x, y) { Some(r) => r, None => false } // `<`: "If r is undefined, return false."
}

/// `x > y`: `IsLessThan(y, x, false)`.
pub open spec fn rel_gt(x: u64, y: u64) -> bool {
    match number_less_than(y, x) { Some(r) => r, None => false }
}

/// `x <= y`: `IsLessThan(y, x, false)`; "If r is either true or undefined,
/// return false. Return true."
pub open spec fn rel_le(x: u64, y: u64) -> bool {
    match number_less_than(y, x) { Some(r) => !r, None => false }
}

/// `x >= y`: `IsLessThan(x, y, true)`; "If r is either true or undefined,
/// return false. Return true."
pub open spec fn rel_ge(x: u64, y: u64) -> bool {
    match number_less_than(x, y) { Some(r) => !r, None => false }
}

// ---- The result of each guarded arithmetic op on two Numbers ----------

/// `a + b` on two Number values, with the encoding rule of the modelling
/// choices. Number::add §6.1.6.1.7.
pub open spec fn arith_add(a: u64, b: u64) -> u64 {
    if is_int32(a) && is_int32(b) && fits_i32(int32_of(a) as int + int32_of(b) as int) {
        enc_int32((int32_of(a) as int + int32_of(b) as int) as i32)
    } else {
        enc_double(number_add(num_bits(a), num_bits(b)))
    }
}

/// `a - b` on two Number values. Number::subtract §6.1.6.1.8.
pub open spec fn arith_sub(a: u64, b: u64) -> u64 {
    if is_int32(a) && is_int32(b) && fits_i32(int32_of(a) as int - int32_of(b) as int) {
        enc_int32((int32_of(a) as int - int32_of(b) as int) as i32)
    } else {
        enc_double(number_subtract(num_bits(a), num_bits(b)))
    }
}

/// `a * b` on two Number values. Number::multiply §6.1.6.1.4. An exact zero
/// product with a negative operand is `-0`, which no int32 is.
pub open spec fn arith_mul(a: u64, b: u64) -> u64 {
    if is_int32(a) && is_int32(b) && fits_i32(int32_of(a) as int * int32_of(b) as int)
        && !(int32_of(a) as int * int32_of(b) as int == 0 && (int32_of(a) < 0 || int32_of(b) < 0)) {
        enc_int32((int32_of(a) as int * int32_of(b) as int) as i32)
    } else {
        enc_double(number_multiply(num_bits(a), num_bits(b)))
    }
}

/// `a / b` on two Number values: always a double. Number::divide §6.1.6.1.5.
pub open spec fn arith_div(a: u64, b: u64) -> u64 {
    enc_double(number_divide(num_bits(a), num_bits(b)))
}

/// The truncated remainder of two integers (sign of the dividend), `d != 0`.
pub open spec fn int_rem_trunc(n: int, d: int) -> int {
    let m: int = (if n < 0 { -n } else { n }) % (if d < 0 { -d } else { d });
    if n < 0 { -m } else { m }
}

/// `a % b` on two Number values. Number::remainder §6.1.6.1.6. The int32
/// result is the remainder unless it is a zero from a negative dividend,
/// which is `-0`.
pub open spec fn arith_mod(a: u64, b: u64) -> u64 {
    if is_int32(a) && is_int32(b) && int32_of(b) != 0
        && !(int_rem_trunc(int32_of(a) as int, int32_of(b) as int) == 0 && int32_of(a) < 0) {
        enc_int32(int_rem_trunc(int32_of(a) as int, int32_of(b) as int) as i32)
    } else {
        enc_double(number_remainder(num_bits(a), num_bits(b)))
    }
}

/// `-a` on a Number value. Number::unaryMinus §6.1.6.1.1. `-0` is not an
/// int32, and `-(-2^31)` does not fit.
pub open spec fn arith_neg(a: u64) -> u64 {
    if is_int32(a) && int32_of(a) != 0 && int32_of(a) != -2147483648 {
        enc_int32((-(int32_of(a) as int)) as i32)
    } else {
        enc_double(number_unary_minus(num_bits(a)))
    }
}

/// `a + 1` (§13.4.2.1 and §13.4.4.1: `Number::add(oldValue, 1𝔽)`).
pub open spec fn arith_inc(a: u64) -> u64 {
    arith_add(a, enc_int32(1))
}

/// `a - 1` (§13.4.3.1 and §13.4.5.1: `Number::subtract(oldValue, 1𝔽)`).
pub open spec fn arith_dec(a: u64) -> u64 {
    arith_sub(a, enc_int32(1))
}

// =====================================================================
// 3. The machine
// =====================================================================

/// The number of header slots in a frame: callee, `this`, argument count,
/// return address (phase-7.md "Shapes fixed here").
pub open spec fn hdr_slots() -> nat {
    4
}

/// Slot of the callee in a frame (offset from the frame base).
pub open spec fn hdr_callee() -> nat {
    0
}

/// Slot of `this`.
pub open spec fn hdr_this() -> nat {
    1
}

/// Slot of the argument count and frame kind.
pub open spec fn hdr_argc() -> nat {
    2
}

/// Slot of the return address.
pub open spec fn hdr_ret() -> nat {
    3
}

/// A plain call's frame kind.
pub open spec fn kind_plain() -> nat {
    0
}

/// A construct call's frame kind.
pub open spec fn kind_construct() -> nat {
    1
}

/// A generator or async frame's kind.
pub open spec fn kind_suspendable() -> nat {
    2
}

/// The int32 stored in a frame's argument-count slot.
pub open spec fn enc_argc(argc: nat, kind: nat) -> u64 {
    enc_int32((argc + kind * 268435456) as i32)
}

/// The argument count in an argument-count slot.
pub open spec fn argc_of(v: u64) -> nat {
    ((int32_of(v) as int) % 268435456) as nat
}

/// The frame kind in an argument-count slot.
pub open spec fn kind_of(v: u64) -> nat {
    ((int32_of(v) as int) / 268435456) as nat
}

/// The return-address payload for a caller with frame base `base` at `pc`.
pub open spec fn pack_ret(base: nat, pc: nat) -> u64 {
    (((base as u64) << 24) | (pc as u64)) & 0xFFFF_FFFF_FFFF
}

/// The return address packs a frame base and a `pc`, each below this.
pub open spec fn ret_limit() -> nat {
    0xFF_FFFF
}

/// What a cell is, for the fast paths.
pub enum Class {
    /// An ordinary object.
    Plain,
    /// An Array exotic object (§10.4.2), dense.
    Array,
    /// A function object.
    Function(FnInfo),
    /// A declarative environment (§9.1.1.1): its slots are the bindings.
    Env {
        /// The enclosing environment: a heap reference, or `undefined` for the outermost.
        parent: u64,
    },
    /// A string, symbol, BigInt, or any cell the fast paths do not touch.
    Other,
}

/// What a fast call needs to know of a function object.
pub struct FnInfo {
    /// The function's code, an index into `State::codes`.
    pub code: nat,
    /// The captured environment: a heap reference, or `undefined`.
    pub env: u64,
    /// The function is ordinary for the fast call: [[Call]] is
    /// OrdinaryCallEvaluateBody (§10.2.1.4) with no `this` coercion, no
    /// `arguments` object, not a class constructor, generator or async.
    /// Decided by the heap (7.5) when the function is created.
    pub fast_callable: bool,
}

/// A heap cell, as far as the fast paths see it.
pub struct Cell {
    /// The generation (phase-7.md 7.0(f): bumped when the slot is reused).
    pub generation: u16,
    /// The shape id; 0 for cells with no properties.
    pub shape: nat,
    /// What the cell is.
    pub class: Class,
    /// Property slots, by the shape's layout.
    pub slots: Seq<u64>,
    /// Dense elements; the hole marks an absent one.
    pub elements: Seq<u64>,
    /// Every element is an ordinary writable, configurable, enumerable data
    /// property of an extensible object (not frozen, sealed, or an accessor).
    pub elements_plain: bool,
}

/// The heap: live cells by arena index.
pub struct Heap {
    /// Live cells.
    pub cells: Map<u32, Cell>,
}

/// One inline-cache entry: a shape and the slot index it gives.
pub struct IcEntry {
    /// The shape id; 0 means empty and never hits.
    pub shape: nat,
    /// The property's slot.
    pub slot: nat,
}

/// A function's code.
pub struct Code {
    /// The ops.
    pub ops: Seq<Op>,
    /// The constant pool (values).
    pub consts: Seq<u64>,
    /// The number of parameters.
    pub nparams: nat,
    /// The number of registers after the parameters.
    pub nregs: nat,
    /// The size of the inline-cache table.
    pub nics: nat,
}

/// The abstract machine state.
pub struct State {
    /// The value-stack region: every frame is a window of it.
    pub region: Seq<u64>,
    /// The base slot of the current frame.
    pub fp: nat,
    /// The index of the next op of the current function.
    pub pc: nat,
    /// The heap.
    pub heap: Heap,
    /// All code, by id. Immutable while running.
    pub codes: Seq<Code>,
    /// Inline-cache tables, by code id then ic index. Handlers install entries.
    pub ics: Seq<Seq<IcEntry>>,
    /// The thrown value, set by unwinding and read by `GetException`.
    pub exception: u64,
    /// The termination flag. Set from outside; `step` never changes it.
    pub terminate: bool,
}

/// The number of slots of a frame of `code`: header, parameters, registers.
pub open spec fn frame_size(c: Code) -> nat {
    hdr_slots() + c.nparams + c.nregs
}

/// The slot of register `r` in the frame at `fp`: arguments first (registers
/// `0..nparams`), then locals.
pub open spec fn reg_slot(fp: nat, r: nat) -> nat {
    fp + hdr_slots() + r
}

/// The live cell a value refers to, if it is a live heap reference.
pub open spec fn live_cell(h: Heap, v: u64) -> Option<Cell> {
    match decode(v) {
        Val::Ref(i, g) => {
            if h.cells.dom().contains(i) && h.cells[i].generation == g {
                Some(h.cells[i])
            } else {
                None
            }
        }
        _ => None,
    }
}

/// The arena index of a heap reference (0 for anything else).
pub open spec fn ref_index(v: u64) -> u32 {
    match decode(v) {
        Val::Ref(i, _) => i,
        _ => 0,
    }
}

/// The value of register `r` of the current frame.
pub open spec fn reg(s: State, r: nat) -> u64
    recommends reg_slot(s.fp, r) < s.region.len(),
{
    s.region[reg_slot(s.fp, r) as int]
}

/// `s` with register `r` of the current frame set to `v`.
pub open spec fn set_reg(s: State, r: nat, v: u64) -> State
    recommends reg_slot(s.fp, r) < s.region.len(),
{
    State { region: s.region.update(reg_slot(s.fp, r) as int, v), ..s }
}

/// `s` at the next op.
pub open spec fn next(s: State) -> State {
    State { pc: s.pc + 1, ..s }
}

/// `s` at op `target`.
pub open spec fn jump(s: State, target: nat) -> State {
    State { pc: target, ..s }
}

/// The code id of the function a frame at `fp` is running, from the callee
/// slot of its header (0 if the slot is not a live function).
pub open spec fn frame_code_id(s: State, fp: nat) -> nat
    recommends fp < s.region.len(),
{
    match live_cell(s.heap, s.region[(fp + hdr_callee()) as int]) {
        Some(c) => match c.class {
            Class::Function(f) => f.code,
            _ => 0,
        },
        None => 0,
    }
}

/// The code of the current frame.
pub open spec fn cur_code(s: State) -> Code
    recommends s.fp < s.region.len(), frame_code_id(s, s.fp) < s.codes.len(),
{
    s.codes[frame_code_id(s, s.fp) as int]
}

/// The op at `pc` in the current function.
pub open spec fn fetch(s: State) -> Op
    recommends s.pc < cur_code(s).ops.len(),
{
    cur_code(s).ops[s.pc as int]
}

/// One step of the machine: fetch and run.
pub open spec fn step_fetch(s: State) -> State {
    step(s, fetch(s))
}

/// An operand register is inside the frame of `c`.
pub open spec fn reg_ok(c: Code, r: nat) -> bool {
    r < c.nparams + c.nregs
}

/// `n` registers from `r` are inside the frame of `c`.
pub open spec fn regs_ok(c: Code, r: nat, n: nat) -> bool {
    r + n <= c.nparams + c.nregs
}

/// An op's operands are in range for the function `c` with `nops` ops: every
/// register inside the frame, every constant, target and cache index in its
/// table. A compiler's output must satisfy it (7.7).
pub open spec fn op_wf(c: Code, op: Op) -> bool {
    let nops = c.ops.len();
    match op {
        Op::Nop => true,
        Op::Move { dst, src } => reg_ok(c, dst) && reg_ok(c, src),
        Op::LoadConst { dst, k } => reg_ok(c, dst) && k < c.consts.len() && value_wf(c.consts[k as int]),
        Op::LoadInt { dst, .. } => reg_ok(c, dst),
        Op::LoadUndefined { dst } => reg_ok(c, dst),
        Op::LoadNull { dst } => reg_ok(c, dst),
        Op::LoadBool { dst, .. } => reg_ok(c, dst),
        Op::LoadHole { dst } => reg_ok(c, dst),
        Op::GetThis { dst } => reg_ok(c, dst),
        Op::GetCallee { dst } => reg_ok(c, dst),
        Op::GetArgc { dst } => reg_ok(c, dst),
        Op::GetException { dst } => reg_ok(c, dst),
        Op::Jump { target } => target < nops,
        Op::JumpIfUndefined { src, target } => reg_ok(c, src) && target < nops,
        Op::JumpIfNotUndefined { src, target } => reg_ok(c, src) && target < nops,
        Op::JumpIfNullish { src, target } => reg_ok(c, src) && target < nops,
        Op::JumpIfNotNullish { src, target } => reg_ok(c, src) && target < nops,
        Op::Add { dst, a, b } | Op::Sub { dst, a, b } | Op::Mul { dst, a, b }
        | Op::Div { dst, a, b } | Op::Mod { dst, a, b } | Op::BitAnd { dst, a, b }
        | Op::BitOr { dst, a, b } | Op::BitXor { dst, a, b } | Op::Shl { dst, a, b }
        | Op::Shr { dst, a, b } | Op::UShr { dst, a, b } | Op::Lt { dst, a, b }
        | Op::Le { dst, a, b } | Op::Gt { dst, a, b } | Op::Ge { dst, a, b }
        | Op::StrictEq { dst, a, b } | Op::StrictNe { dst, a, b } | Op::Exp { dst, a, b }
        | Op::LooseEq { dst, a, b } | Op::LooseNe { dst, a, b }
        | Op::InstanceOf { dst, a, b } | Op::HasProperty { dst, a, b } =>
            reg_ok(c, dst) && reg_ok(c, a) && reg_ok(c, b),
        Op::Neg { dst, src } | Op::Inc { dst, src } | Op::Dec { dst, src }
        | Op::BitNot { dst, src } | Op::Not { dst, src } | Op::ToNumeric { dst, src }
        | Op::ToNumber { dst, src } | Op::TypeOf { dst, src } | Op::GetIterator { dst, src } =>
            reg_ok(c, dst) && reg_ok(c, src),
        Op::JumpIfTrue { cond, target } | Op::JumpIfFalse { cond, target } =>
            reg_ok(c, cond) && target < nops,
        Op::Loop { target } => target < nops,
        Op::ThrowIfHole { src } => reg_ok(c, src),
        Op::GetProp { dst, obj, key, ic } =>
            reg_ok(c, dst) && reg_ok(c, obj) && key < c.consts.len() && ic < c.nics,
        Op::SetProp { obj, key, val, ic } =>
            reg_ok(c, obj) && key < c.consts.len() && reg_ok(c, val) && ic < c.nics,
        Op::GetElem { dst, obj, idx } => reg_ok(c, dst) && reg_ok(c, obj) && reg_ok(c, idx),
        Op::SetElem { obj, idx, val } => reg_ok(c, obj) && reg_ok(c, idx) && reg_ok(c, val),
        Op::Call { dst, callee, this, args, argc } =>
            reg_ok(c, dst) && reg_ok(c, callee) && reg_ok(c, this) && regs_ok(c, args, argc),
        Op::Return { src } => reg_ok(c, src),
        Op::GetEnvSlot { dst, env, .. } => reg_ok(c, dst) && reg_ok(c, env),
        Op::SetEnvSlot { env, src, .. } => reg_ok(c, env) && reg_ok(c, src),
        Op::GetEnvParent { dst, env } => reg_ok(c, dst) && reg_ok(c, env),
        Op::GetCalleeEnv { dst } => reg_ok(c, dst),
        Op::DeleteProp { dst, obj, idx } => reg_ok(c, dst) && reg_ok(c, obj) && reg_ok(c, idx),
        Op::GetGlobal { dst, key, ic } => reg_ok(c, dst) && key < c.consts.len() && ic < c.nics,
        Op::SetGlobal { key, src, ic } => key < c.consts.len() && reg_ok(c, src) && ic < c.nics,
        Op::GetGlobalOrUndefined { dst, key } => reg_ok(c, dst) && key < c.consts.len(),
        Op::DeclareGlobals { k } => k < c.consts.len() && value_wf(c.consts[k as int]),
        Op::DefineProp { obj, key, val } => reg_ok(c, obj) && key < c.consts.len() && reg_ok(c, val),
        Op::DefineElem { obj, idx, val } => reg_ok(c, obj) && reg_ok(c, idx) && reg_ok(c, val),
        Op::SetLiteralProto { obj, val } => reg_ok(c, obj) && reg_ok(c, val),
        Op::NewObject { dst } => reg_ok(c, dst),
        Op::NewArray { dst, .. } => reg_ok(c, dst),
        Op::NewEnv { dst, parent, .. } => reg_ok(c, dst) && reg_ok(c, parent),
        Op::NewClosure { dst, env, .. } => reg_ok(c, dst) && reg_ok(c, env),
        Op::New { dst, callee, args, argc } =>
            reg_ok(c, dst) && reg_ok(c, callee) && regs_ok(c, args, argc),
        Op::CallSpread { dst, callee, this, args } =>
            reg_ok(c, dst) && reg_ok(c, callee) && reg_ok(c, this) && reg_ok(c, args),
        Op::IterNext { value, done, iter } =>
            reg_ok(c, value) && reg_ok(c, done) && reg_ok(c, iter),
        Op::IterClose { iter } => reg_ok(c, iter),
        Op::Yield { src, value, mode } | Op::Await { src, value, mode } =>
            reg_ok(c, src) && reg_ok(c, value) && reg_ok(c, mode),
        Op::Throw { src } => reg_ok(c, src),
        Op::ThrowError { msg, .. } => msg < c.consts.len(),
        Op::InitGlobalLexical { key, src, .. } => key < c.consts.len() && reg_ok(c, src),
        Op::ToPropertyKey { dst, src, .. } => reg_ok(c, dst) && reg_ok(c, src),
        Op::ToString { dst, src, .. } => reg_ok(c, dst) && reg_ok(c, src),
        Op::CopyDataProperties { obj, src, excl, nexcl, .. } => reg_ok(c, obj) && reg_ok(c, src) && regs_ok(c, excl, nexcl),
        Op::GetTemplateObject { dst, k, .. } => reg_ok(c, dst) && k < c.consts.len() && value_wf(c.consts[k as int]),
        Op::NewSpread { dst, callee, args, .. } => reg_ok(c, dst) && reg_ok(c, callee) && reg_ok(c, args),
        Op::SuperCall { dst, func, newtarget, this, args, argc, .. } => reg_ok(c, dst) && reg_ok(c, func) && reg_ok(c, newtarget) && reg_ok(c, this) && regs_ok(c, args, argc),
        Op::SuperCallSpread { dst, func, newtarget, this, args, .. } => reg_ok(c, dst) && reg_ok(c, func) && reg_ok(c, newtarget) && reg_ok(c, this) && reg_ok(c, args),
        Op::InitInstance { obj, func, .. } => reg_ok(c, obj) && reg_ok(c, func),
        Op::ClassSetup { ctor, proto, heritage, .. } => reg_ok(c, ctor) && reg_ok(c, proto) && reg_ok(c, heritage),
        Op::DefineMethod { obj, key, func, form, .. } => reg_ok(c, obj) && reg_ok(c, key) && reg_ok(c, func) && form < 3,
        Op::SetHomeObject { func, obj, .. } => reg_ok(c, func) && reg_ok(c, obj),
        Op::SetInstanceInit { ctor, init, .. } => reg_ok(c, ctor) && reg_ok(c, init),
        Op::NewPrivateName { dst, k, .. } => reg_ok(c, dst) && k < c.consts.len(),
        Op::GetPrivate { dst, obj, name, .. } => reg_ok(c, dst) && reg_ok(c, obj) && reg_ok(c, name),
        Op::SetPrivate { obj, name, val, .. } => reg_ok(c, obj) && reg_ok(c, name) && reg_ok(c, val),
        Op::DefinePrivate { obj, name, val, form, .. } => reg_ok(c, obj) && reg_ok(c, name) && reg_ok(c, val) && form < 4,
        Op::HasPrivate { dst, name, obj, .. } => reg_ok(c, dst) && reg_ok(c, name) && reg_ok(c, obj),
        Op::GetSuperBase { dst, func, .. } => reg_ok(c, dst) && reg_ok(c, func),
        Op::GetSuper { dst, base, key, this, .. } => reg_ok(c, dst) && reg_ok(c, base) && reg_ok(c, key) && reg_ok(c, this),
        Op::SetSuper { base, key, val, this, .. } => reg_ok(c, base) && reg_ok(c, key) && reg_ok(c, val) && reg_ok(c, this),
        Op::GetNewTarget { dst, .. } => reg_ok(c, dst),
        Op::ConstructResult { dst, val, this, .. } => reg_ok(c, dst) && reg_ok(c, val) && reg_ok(c, this),
        Op::CreateUnmappedArguments { dst, .. } => reg_ok(c, dst),
        Op::CreateMappedArguments { dst, env, k, .. } => reg_ok(c, dst) && reg_ok(c, env) && k < c.consts.len() && value_wf(c.consts[k as int]),
        Op::CreateRestArray { dst, .. } => reg_ok(c, dst),
        Op::ForInIterator { dst, src, .. } => reg_ok(c, dst) && reg_ok(c, src),
    }
}

/// The op can continue at the next op (every op but the unconditional
/// transfers of control and the throws).
pub open spec fn falls_through(op: Op) -> bool {
    match op {
        Op::Jump { .. } | Op::Loop { .. } | Op::Return { .. } | Op::Throw { .. }
        | Op::ThrowError { .. } => false,
        _ => true,
    }
}

/// Every op of the function is well-formed, an op that can continue is not
/// the last (so `pc` never leaves the function), and the function fits the
/// return-address limit.
pub open spec fn code_wf(c: Code) -> bool {
    &&& c.ops.len() < ret_limit()
    &&& forall|i: int| 0 <= i < c.ops.len() ==> op_wf(c, #[trigger] c.ops[i])
    &&& forall|i: int| 0 <= i < c.ops.len() && falls_through(#[trigger] c.ops[i]) ==> i + 1 < c.ops.len()
}

/// The frame at `fp` is well-formed: its callee is a live function whose code
/// exists, and the whole window is inside the region.
pub open spec fn frame_wf(s: State, fp: nat) -> bool {
    &&& fp + hdr_slots() <= s.region.len()
    &&& match live_cell(s.heap, s.region[(fp + hdr_callee()) as int]) {
            Some(c) => match c.class {
                Class::Function(f) => f.code < s.codes.len()
                    && fp + frame_size(s.codes[f.code as int]) <= s.region.len(),
                _ => false,
            },
            None => false,
        }
}

/// The machine's invariant, which the handlers preserve (their contract, 7.8)
/// and `step` preserves for core ops (`lemma_core_step_wf`): the current
/// frame is well-formed, `pc` is inside the function, the code and the
/// tables are consistent, and the region is within the return-address limit.
pub open spec fn state_wf(s: State) -> bool {
    &&& s.region.len() < ret_limit()
    &&& s.ics.len() == s.codes.len()
    &&& forall|i: int| 0 <= i < s.codes.len() ==> code_wf(#[trigger] s.codes[i])
    &&& forall|i: int| 0 <= i < s.codes.len() ==> s.ics[i].len() == (#[trigger] s.codes[i]).nics
    &&& frame_wf(s, s.fp)
    &&& s.pc < cur_code(s).ops.len()
}

/// An inline-cache entry hits a cell: the entry is not empty, the shapes
/// agree, and the slot is there.
pub open spec fn ic_hit(c: Cell, e: IcEntry) -> bool {
    e.shape != 0 && c.shape == e.shape && e.slot < c.slots.len()
}

/// The cell is an ordinary property holder that a cache may name.
pub open spec fn is_prop_holder(c: Cell) -> bool {
    match c.class {
        Class::Plain => true,
        Class::Array => true,
        Class::Function(_) => true,
        _ => false,
    }
}

/// The inline-cache invariant of phase-7.md "Inline caches are data": an
/// entry's shape implies the slot exists in every live cell of that shape.
pub open spec fn ic_wf(s: State) -> bool {
    forall|ci: int, ii: int, h: u32| #![trigger s.ics[ci][ii], s.heap.cells[h]]
        0 <= ci < s.ics.len() && 0 <= ii < s.ics[ci].len() && s.heap.cells.dom().contains(h)
        && s.ics[ci][ii].shape != 0 && s.heap.cells[h].shape == s.ics[ci][ii].shape
        && is_prop_holder(s.heap.cells[h])
        ==> s.ics[ci][ii].slot < s.heap.cells[h].slots.len()
}

/// The caller a plain `Return` goes back to.
pub struct RetTarget {
    /// The caller's frame base.
    pub base: nat,
    /// The `pc` of the caller's call op.
    pub pc: nat,
    /// The register that receives the value.
    pub dst: nat,
}

/// The caller named by the current frame's return address, if it is a
/// well-formed one: a RAW address that is not `RET_NONE`, naming a frame
/// whose callee is a live function, whose op at `pc` is a call, with its
/// destination register in the region.
pub open spec fn ret_target(s: State) -> Option<RetTarget> {
    match decode(s.region[(s.fp + hdr_ret()) as int]) {
        Val::Raw(p) => {
            if p == RET_NONE {
                None
            } else {
                let base: nat = (p >> 24) as nat;
                let pc: nat = (p & 0xFF_FFFF) as nat;
                if base + hdr_slots() > s.region.len() {
                    None
                } else {
                    match live_cell(s.heap, s.region[(base + hdr_callee()) as int]) {
                        Some(c) => match c.class {
                            Class::Function(f) => {
                                if f.code < s.codes.len() && pc < s.codes[f.code as int].ops.len() {
                                    match call_dst(s.codes[f.code as int].ops[pc as int]) {
                                        Some(dst) => {
                                            if reg_slot(base, dst) < s.region.len() {
                                                Some(RetTarget { base: base, pc: pc, dst: dst })
                                            } else {
                                                None
                                            }
                                        }
                                        None => None,
                                    }
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        },
                        None => None,
                    }
                }
            }
        }
        _ => None,
    }
}

/// The function a `Call` would enter on its callee operand, if the callee is
/// a live function the fast call accepts.
pub open spec fn call_target(s: State, callee: u64) -> Option<FnInfo> {
    match live_cell(s.heap, callee) {
        Some(c) => match c.class {
            Class::Function(f) => if f.fast_callable { Some(f) } else { None },
            _ => None,
        },
        None => None,
    }
}

/// The region after pushing a frame at `nb` for the function `f` (code `cc`):
/// header, the first `argc` arguments copied from the caller's registers
/// `args..`, `undefined` in the missing parameters and in every local.
pub open spec fn pushed_region(s: State, nb: nat, callee: u64, this_v: u64, args: nat, argc: nat, cc: Code, ret: u64) -> Seq<u64> {
    Seq::new(s.region.len(), |i: int|
        if i == nb + hdr_callee() { callee }
        else if i == nb + hdr_this() { this_v }
        else if i == nb + hdr_argc() { enc_argc(argc, kind_plain()) }
        else if i == nb + hdr_ret() { ret }
        else if nb + hdr_slots() <= i && i < nb + hdr_slots() + argc {
            s.region[reg_slot(s.fp, args + (i - nb - hdr_slots()) as nat) as int]
        }
        else if nb + hdr_slots() + argc <= i && i < nb + frame_size(cc) { UNDEFINED }
        else { s.region[i] })
}

// =====================================================================
// 4. fast_path, fast_step, handler, step
// =====================================================================

/// The uninterpreted handler: the next state after calling handler `h` for
/// `op` in state `s`, including `pc`. Test262 is the evidence for each
/// handler (phase-7.md 7.4); its contract is written with the handler, 7.8.
pub uninterp spec fn handler(h: HandlerId, s: State, op: Op) -> State;

/// The condition under which `op` takes its fast path (`fast_step`) in `s`.
/// True for every core op, false for every handler op, and for a guarded op
/// the condition the JIT tests inline.
pub open spec fn fast_path(s: State, op: Op) -> bool {
    match op {
        // --- Core ---
        Op::Nop | Op::Move { .. } | Op::LoadConst { .. } | Op::LoadInt { .. }
        | Op::LoadUndefined { .. } | Op::LoadNull { .. } | Op::LoadBool { .. }
        | Op::LoadHole { .. } | Op::GetThis { .. } | Op::GetCallee { .. }
        | Op::GetArgc { .. } | Op::GetException { .. } | Op::Jump { .. }
        | Op::JumpIfUndefined { .. } | Op::JumpIfNotUndefined { .. }
        | Op::JumpIfNullish { .. } | Op::JumpIfNotNullish { .. } => true,
        // --- Guarded: numbers ---
        Op::Add { a, b, .. } | Op::Sub { a, b, .. } | Op::Mul { a, b, .. }
        | Op::Div { a, b, .. } | Op::Mod { a, b, .. } | Op::BitAnd { a, b, .. }
        | Op::BitOr { a, b, .. } | Op::BitXor { a, b, .. } | Op::Shl { a, b, .. }
        | Op::Shr { a, b, .. } | Op::UShr { a, b, .. } | Op::Lt { a, b, .. }
        | Op::Le { a, b, .. } | Op::Gt { a, b, .. } | Op::Ge { a, b, .. } =>
            is_number(reg(s, a)) && is_number(reg(s, b)),
        Op::Neg { src, .. } | Op::Inc { src, .. } | Op::Dec { src, .. }
        | Op::BitNot { src, .. } | Op::ToNumeric { src, .. } => is_number(reg(s, src)),
        // ToNumber §7.1.4† step 1: a Number is returned as it is; everything else is the handler's.
        Op::ToNumber { src, .. } => is_number(reg(s, src)),
        Op::StrictEq { a, b, .. } | Op::StrictNe { a, b, .. } =>
            strict_eq_fast(reg(s, a), reg(s, b)) is Some,
        Op::Not { src, .. } => to_boolean_fast(reg(s, src)) is Some,
        Op::JumpIfTrue { cond, .. } | Op::JumpIfFalse { cond, .. } =>
            to_boolean_fast(reg(s, cond)) is Some,
        Op::Loop { .. } => !s.terminate,
        Op::ThrowIfHole { src } => reg(s, src) != HOLE,
        // --- Guarded: properties ---
        Op::GetProp { obj, ic, .. } | Op::SetProp { obj, ic, .. } => {
            match live_cell(s.heap, reg(s, obj)) {
                Some(c) => is_prop_holder(c) && ic_hit(c, s.ics[frame_code_id(s, s.fp) as int][ic as int]),
                None => false,
            }
        }
        Op::GetElem { obj, idx, .. } | Op::SetElem { obj, idx, .. } => {
            match live_cell(s.heap, reg(s, obj)) {
                Some(c) => (c.class is Plain || c.class is Array) && c.elements_plain
                    && is_int32(reg(s, idx)) && 0 <= int32_of(reg(s, idx))
                    && int32_of(reg(s, idx)) < c.elements.len()
                    && c.elements[int32_of(reg(s, idx)) as int] != HOLE,
                None => false,
            }
        }
        // --- Guarded: calls ---
        Op::Call { callee, args, argc, .. } => {
            match call_target(s, reg(s, callee)) {
                Some(f) => {
                    &&& !s.terminate
                    &&& f.code < s.codes.len()
                    &&& argc <= s.codes[f.code as int].nparams
                    &&& s.fp < ret_limit() && s.pc < ret_limit()
                    &&& s.fp + frame_size(cur_code(s)) + frame_size(s.codes[f.code as int]) <= s.region.len()
                }
                None => false,
            }
        }
        Op::Return { .. } => {
            &&& kind_of(s.region[(s.fp + hdr_argc()) as int]) == kind_plain()
            &&& ret_target(s) is Some
        }
        // --- Guarded: environments ---
        Op::GetEnvSlot { env, idx, .. } | Op::SetEnvSlot { env, idx, .. } => {
            match live_cell(s.heap, reg(s, env)) {
                Some(c) => (c.class is Env) && idx < c.slots.len(),
                None => false,
            }
        }
        Op::GetEnvParent { env, .. } => {
            match live_cell(s.heap, reg(s, env)) {
                Some(c) => c.class is Env,
                None => false,
            }
        }
        Op::GetCalleeEnv { .. } => {
            match live_cell(s.heap, s.region[(s.fp + hdr_callee()) as int]) {
                Some(c) => c.class is Function,
                None => false,
            }
        }
        // --- Handler ops: never fast ---
        _ => false,
    }
}

/// The result of a core op, or of a guarded op when `fast_path` holds.
/// Defined for every op so it is a total function; for a handler op the value
/// is `s` and never used (`step` does not reach it).
pub open spec fn fast_step(s: State, op: Op) -> State {
    match op {
        Op::Nop => next(s),
        Op::Move { dst, src } => next(set_reg(s, dst, reg(s, src))),
        Op::LoadConst { dst, k } => next(set_reg(s, dst, cur_code(s).consts[k as int])),
        Op::LoadInt { dst, imm } => next(set_reg(s, dst, enc_int32(imm))),
        Op::LoadUndefined { dst } => next(set_reg(s, dst, UNDEFINED)),
        Op::LoadNull { dst } => next(set_reg(s, dst, NULL)),
        Op::LoadBool { dst, flag } => next(set_reg(s, dst, enc_bool(flag))),
        Op::LoadHole { dst } => next(set_reg(s, dst, HOLE)),
        Op::GetThis { dst } => next(set_reg(s, dst, s.region[(s.fp + hdr_this()) as int])),
        Op::GetCallee { dst } => next(set_reg(s, dst, s.region[(s.fp + hdr_callee()) as int])),
        Op::GetArgc { dst } => next(set_reg(s, dst,
            enc_int32(argc_of(s.region[(s.fp + hdr_argc()) as int]) as i32))),
        Op::GetException { dst } => next(set_reg(s, dst, s.exception)),
        Op::Jump { target } => jump(s, target),
        Op::JumpIfUndefined { src, target } =>
            if reg(s, src) == UNDEFINED { jump(s, target) } else { next(s) },
        Op::JumpIfNotUndefined { src, target } =>
            if reg(s, src) != UNDEFINED { jump(s, target) } else { next(s) },
        Op::JumpIfNullish { src, target } =>
            if reg(s, src) == UNDEFINED || reg(s, src) == NULL { jump(s, target) } else { next(s) },
        Op::JumpIfNotNullish { src, target } =>
            if reg(s, src) != UNDEFINED && reg(s, src) != NULL { jump(s, target) } else { next(s) },

        Op::Add { dst, a, b } => next(set_reg(s, dst, arith_add(reg(s, a), reg(s, b)))),
        Op::Sub { dst, a, b } => next(set_reg(s, dst, arith_sub(reg(s, a), reg(s, b)))),
        Op::Mul { dst, a, b } => next(set_reg(s, dst, arith_mul(reg(s, a), reg(s, b)))),
        Op::Div { dst, a, b } => next(set_reg(s, dst, arith_div(reg(s, a), reg(s, b)))),
        Op::Mod { dst, a, b } => next(set_reg(s, dst, arith_mod(reg(s, a), reg(s, b)))),
        Op::Neg { dst, src } => next(set_reg(s, dst, arith_neg(reg(s, src)))),
        Op::Inc { dst, src } => next(set_reg(s, dst, arith_inc(reg(s, src)))),
        Op::Dec { dst, src } => next(set_reg(s, dst, arith_dec(reg(s, src)))),
        Op::BitAnd { dst, a, b } => next(set_reg(s, dst,
            enc_int32(number_bitwise_and(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::BitOr { dst, a, b } => next(set_reg(s, dst,
            enc_int32(number_bitwise_or(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::BitXor { dst, a, b } => next(set_reg(s, dst,
            enc_int32(number_bitwise_xor(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::Shl { dst, a, b } => next(set_reg(s, dst,
            enc_int32(number_left_shift(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::Shr { dst, a, b } => next(set_reg(s, dst,
            enc_int32(number_signed_right_shift(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::UShr { dst, a, b } => next(set_reg(s, dst,
            enc_number_int(number_unsigned_right_shift(num_bits(reg(s, a)), num_bits(reg(s, b))) as int))),
        Op::BitNot { dst, src } => next(set_reg(s, dst,
            enc_int32(number_bitwise_not(num_bits(reg(s, src)))))),
        Op::Lt { dst, a, b } => next(set_reg(s, dst,
            enc_bool(rel_lt(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::Le { dst, a, b } => next(set_reg(s, dst,
            enc_bool(rel_le(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::Gt { dst, a, b } => next(set_reg(s, dst,
            enc_bool(rel_gt(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::Ge { dst, a, b } => next(set_reg(s, dst,
            enc_bool(rel_ge(num_bits(reg(s, a)), num_bits(reg(s, b)))))),
        Op::StrictEq { dst, a, b } => next(set_reg(s, dst,
            enc_bool(match strict_eq_fast(reg(s, a), reg(s, b)) { Some(r) => r, None => false }))),
        Op::StrictNe { dst, a, b } => next(set_reg(s, dst,
            enc_bool(match strict_eq_fast(reg(s, a), reg(s, b)) { Some(r) => !r, None => false }))),
        Op::Not { dst, src } => next(set_reg(s, dst,
            enc_bool(match to_boolean_fast(reg(s, src)) { Some(r) => !r, None => false }))),
        Op::ToNumeric { dst, src } => next(set_reg(s, dst, reg(s, src))),
        // ToNumber §7.1.4† step 1: "If argument is a Number, return argument."
        Op::ToNumber { dst, src } => next(set_reg(s, dst, reg(s, src))),
        Op::JumpIfTrue { cond, target } =>
            if to_boolean_fast(reg(s, cond)) == Some(true) { jump(s, target) } else { next(s) },
        Op::JumpIfFalse { cond, target } =>
            if to_boolean_fast(reg(s, cond)) == Some(false) { jump(s, target) } else { next(s) },
        Op::Loop { target } => jump(s, target),
        Op::ThrowIfHole { src } => next(s),

        Op::GetProp { dst, obj, key, ic } => {
            let c = live_cell(s.heap, reg(s, obj))->Some_0;
            let e = s.ics[frame_code_id(s, s.fp) as int][ic as int];
            next(set_reg(s, dst, c.slots[e.slot as int]))
        }
        Op::SetProp { obj, key, val, ic } => {
            let c = live_cell(s.heap, reg(s, obj))->Some_0;
            let e = s.ics[frame_code_id(s, s.fp) as int][ic as int];
            let c2 = Cell { slots: c.slots.update(e.slot as int, reg(s, val)), ..c };
            next(State {
                heap: Heap { cells: s.heap.cells.insert(ref_index(reg(s, obj)), c2) },
                ..s
            })
        }
        Op::GetElem { dst, obj, idx } => {
            let c = live_cell(s.heap, reg(s, obj))->Some_0;
            next(set_reg(s, dst, c.elements[int32_of(reg(s, idx)) as int]))
        }
        Op::SetElem { obj, idx, val } => {
            let c = live_cell(s.heap, reg(s, obj))->Some_0;
            let c2 = Cell { elements: c.elements.update(int32_of(reg(s, idx)) as int, reg(s, val)), ..c };
            next(State {
                heap: Heap { cells: s.heap.cells.insert(ref_index(reg(s, obj)), c2) },
                ..s
            })
        }
        Op::Call { dst, callee, this, args, argc } => {
            // Push a frame after the caller's (see `pushed_region`).
            let f = call_target(s, reg(s, callee))->Some_0;
            let nb: nat = s.fp + frame_size(cur_code(s));
            let cc = s.codes[f.code as int];
            State {
                region: pushed_region(s, nb, reg(s, callee), reg(s, this), args, argc, cc,
                    enc_raw(pack_ret(s.fp, s.pc))),
                fp: nb,
                pc: 0,
                ..s
            }
        }
        Op::Return { src } => {
            // Pop the frame: the value goes to the call op's destination.
            let t = ret_target(s)->Some_0;
            State {
                region: s.region.update(reg_slot(t.base, t.dst) as int, reg(s, src)),
                fp: t.base,
                pc: t.pc + 1,
                ..s
            }
        }
        Op::GetEnvSlot { dst, env, idx } => {
            let c = live_cell(s.heap, reg(s, env))->Some_0;
            next(set_reg(s, dst, c.slots[idx as int]))
        }
        Op::SetEnvSlot { env, idx, src } => {
            let c = live_cell(s.heap, reg(s, env))->Some_0;
            let c2 = Cell { slots: c.slots.update(idx as int, reg(s, src)), ..c };
            next(State {
                heap: Heap { cells: s.heap.cells.insert(ref_index(reg(s, env)), c2) },
                ..s
            })
        }
        Op::GetEnvParent { dst, env } => {
            let c = live_cell(s.heap, reg(s, env))->Some_0;
            next(set_reg(s, dst, match c.class { Class::Env { parent } => parent, _ => UNDEFINED }))
        }
        Op::GetCalleeEnv { dst } => {
            let c = live_cell(s.heap, s.region[(s.fp + hdr_callee()) as int])->Some_0;
            next(set_reg(s, dst, match c.class { Class::Function(f) => f.env, _ => UNDEFINED }))
        }
        _ => s,
    }
}

/// The semantics of one op: the fast result when the op is core or its fast
/// path holds, and the handler's result otherwise. This is what jit.md's
/// front-end proofs (J.10) refine: per op, the lowered LIR computes
/// `fast_step` when `fast_path` holds, and exits to `op_handler(op)`
/// otherwise.
pub open spec fn step(s: State, op: Op) -> State {
    if fast_path(s, op) { fast_step(s, op) } else { handler(op_handler(op), s, op) }
}

} // verus!

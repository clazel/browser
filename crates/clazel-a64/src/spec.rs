//! The **primary** specification of the A64 subset the JIT emits (jit.md item
//! J.4): the machine state, the semantics of every instruction, and the
//! canonical encoding. Nothing here runs; it defines what "correct" means.
//!
//! # Source
//!
//! Transcribed from the Sail model of Armv9.4-A, rems-project/sail-arm commit
//! `5416ef6b43e9527c38dc71fb752259c1d01a47e1`, `arm-v9.4-a/`, vendored under
//! `tests/data/sail-arm/` (`SOURCE.md`). The Sail is a mechanical translation
//! of Arm's ASL (2023-03), so this is a transcription of the ASL too. Each
//! function cites the Sail file and function it transcribes, as
//! `// sail-arm src/file.sail, FunctionName` (CLAUDE.md rule 5, adapted: the
//! pseudocode has no step numbers; the structure and the names of Sail's
//! functions and variables are kept instead).
//!
//! An instruction is the pair of a `decode_*` function (the encoding and its
//! fields, in `src/instrs64.sail`) and the `execute_aarch64_instrs_*`
//! function it calls (in the same file); the shared pseudocode (`X_read`,
//! `AddWithCarry`, `FPAdd` ...) is in `src/v8_base.sail`, and the fetch,
//! execute and PC update loop is `__InstructionExecute` in `src/fetch.sail`.
//!
//! **Sail's standard library is not vendored.** `src/prelude.sail` includes
//! `<arith.sail>`, `<vector_dec.sail>` and `<real.sail>` from the Sail
//! distribution (rems-project/sail, `lib/`), which define the primitive
//! operations: `UInt`, `SInt`, `ZeroExtend`, `SignExtend`, slicing,
//! `sail_shiftleft`/`sail_shiftright`/`sail_arith_shiftright` (which `LSL`,
//! `LSR`, `ASR` overload), `and_vec`/`or_vec`/`xor_vec`/`not_vec`, and on
//! `real`: `to_real` (`Real`), `floor` (`RoundDown`), `ceil` (`RoundUp`),
//! `sqrt`, `pow_real` (`^`). They are used here with their standard
//! mathematical meaning (bit vectors are unsigned integers below `2^N`;
//! `real` is the real numbers). A reader who wants their text must fetch
//! them from the Sail repository.
//!
//! The Arm Architecture Reference Manual was **not** read: the independent
//! transcription (jit.md, the note under J.4) is made from it by another
//! session. Nor was any other description of the semantics.
//!
//! # What is covered
//!
//! Each in its 64-bit (`sf = 1`, X registers) and 32-bit (`sf = 0`, W
//! registers) form unless it says otherwise:
//!
//! - **Arithmetic:** `ADD`, `ADDS`, `SUB`, `SUBS` (shifted register, and
//!   immediate); `CMP`, `CMN`, `NEG`, `MOV` to or from `SP` are their aliases.
//!   `MADD`, `MSUB` (`MUL`, `MNEG` are aliases), `SDIV`, `UDIV`.
//! - **Logic:** `AND`, `ANDS`, `ORR`, `EOR` (shifted register); `TST`,
//!   `MOV` (register) are aliases.
//! - **Shifts and bit fields:** `LSLV`, `LSRV`, `ASRV`; `SBFM`, `UBFM` (whose
//!   aliases include `LSL`, `LSR`, `ASR` by an immediate, `SXTW`, `UXTW`,
//!   `SBFX`, `UBFX`).
//! - **Constants:** `MOVZ`, `MOVK`. (J.4's list names no way to make a
//!   constant; the JIT needs one, and these are the two that need no
//!   canonical-form rules beyond one, see [`valid_instr`].)
//! - **Conditional select:** `CSEL`, `CSINC`, `CSINV`, `CSNEG` (`CSET`,
//!   `CSETM`, `CINC`, `CNEG` are aliases).
//! - **Loads and stores:** `LDR`, `STR` of a W or X register, and of a D
//!   (double) register, with a register base and either an unsigned scaled
//!   12-bit immediate offset or a register offset (`LSL` by 0 or by the
//!   access size).
//! - **Branches:** `B`, `B.cond`, `CBZ`, `CBNZ`, `RET` (through `X30`).
//! - **Scalar double floating point:** `FADD`, `FSUB`, `FMUL`, `FDIV`,
//!   `FSQRT`, `FMOV`/`FABS`/`FNEG` (register), `FCMP` (register), `FMOV`
//!   between an X register and a D register, `SCVTF` and `FCVTZS` between a W
//!   or X register and a D register.
//!
//! # What is left out
//!
//! - The logical **immediate** forms (`AND`/`ORR`/`EOR` with a bitmask
//!   immediate) and `MOVN`: `MOVN` and `MOVZ` both make `0xFFFF0000` in a W
//!   register, so the subset would need a rule for which one is canonical.
//!   Either is a small addition.
//! - `BIC`, `ORN`, `EON`, `BICS` (the `N` bit of the logical shifted-register
//!   forms), `RORV`, `BFM`, `ADC`, `SBC`, the extended-register `ADD`/`SUB`,
//!   `CCMP`/`CCMN`, `SMULH`/`UMULH`/`SMADDL` and the other widening
//!   multiplies, `CLZ`, `RBIT`, `REV`, `EXTR`: J.4 does not list them.
//! - Byte and halfword loads and stores, sign-extending loads, pre- and
//!   post-indexed addressing, the unscaled (`LDUR`) forms, pairs (`LDP`),
//!   extended register offsets (`UXTW`, `SXTW`, `SXTX`), and loads and
//!   stores whose base is `SP` (register 31): see "SP" below.
//! - `BL`, `BLR`, `BR`, `RET` through any register but `X30`, the
//!   pointer-authenticated forms, `TBZ`/`TBNZ`, `BC.cond`.
//! - Single and half precision, `FMADD` and the other fused forms,
//!   `FNMUL`, `FCMPE`, `FCMP` with zero, `FCCMP`, `FCSEL`, `FMIN`/`FMAX`,
//!   `FRINT*`, `FCVT` between precisions, `UCVTF`/`FCVTZU`, the other
//!   rounding conversions (`FCVTNS` ...), `FJCVTZS`, `FMOV` with an
//!   immediate, and every Advanced SIMD (vector) instruction.
//! - Any state the subset does not read or write: the exception levels, the
//!   system registers, `FPSR` (see below), SVE and SME state, the exclusive
//!   monitors, `PSTATE` other than `N Z C V`.
//!
//! # Modelling choices
//!
//! Each is a difference in form that does not change the meaning, or a
//! restriction of the machine the subset runs on, stated so the validator's
//! theorem (J.6) can assume it.
//!
//! - **The machine runs at EL0 in AArch64** (`PSTATE.nRW = 0`,
//!   `PSTATE.EL = EL0`, `PSTATE.SP = 0`, so `SP_read`/`SP_set` are
//!   `SP_EL0`). Every `UsingAArch32()` branch of the pseudocode is dropped.
//! - **One step of one instruction is a pure function** [`step`] from a
//!   [`State`] and an [`Instr`] to `Option<State>`. Sail fetches the word at
//!   the PC and decodes it in `__InstructionExecute`; here decoding is the
//!   relation of [`encode`], and [`fetch_ok`] says the word at the PC is the
//!   instruction's encoding.
//! - **A fault is `None`.** Sail takes an exception (`AArch64_Abort`,
//!   `AArch64_PCAlignmentFault`, an undefined-instruction exception) and
//!   continues in the kernel; the program sees none of that. Here every
//!   exception is `None`, with no state. The only one the subset can raise
//!   is a data abort: a load or store touching an unmapped byte. (Fetch
//!   faults and PC alignment are [`fetch_ok`]'s.)
//! - **Memory is a partial map** from 64-bit virtual address to byte
//!   ([`State::mem`]); its domain is the set of addresses the process may
//!   read and write. Sail's `Mem_read`/`Mem_set` go through
//!   `AArch64_MemSingle_read`/`_write`, address translation, permission
//!   checks, the memory-tagging check, and the memory model; all of that
//!   is collapsed into "mapped or not". The validator (J.6) reasons about
//!   which addresses are touched, so this is the part it needs. Byte `i` of
//!   an access at `address` is at `address + i` modulo `2^64`, as in
//!   `Mem_read__2`'s byte-by-byte branch.
//! - **Top-byte-ignore is not modelled.** With `TCR_EL1.TBI0 = 1` (Linux)
//!   a data address's top byte is ignored by translation, so two addresses
//!   that differ only there name the same byte. A map cannot say that, so
//!   [`wf`] requires every mapped address to have a zero top byte: an access
//!   with a nonzero top byte faults here, where the hardware might not. The
//!   model is therefore stricter than the hardware for tagged addresses,
//!   which the JIT never forms. For branch targets, `AArch64_BranchAddr`
//!   is taken with `AddrTop = 63` (`EffectiveTBI` is 0 for instruction
//!   addresses): the target is the 64-bit sum, unchanged.
//! - **Little-endian, no alignment checking.** `SCTLR_EL1.E0E = 0`, so
//!   `BigEndian` is false and the bytes are little-endian. `SCTLR_EL1.A =
//!   0` and the memory is Normal, so `AArch64_UnalignedAccessFaults` is
//!   false: an unaligned access is done byte by byte and never faults for
//!   alignment. Sail's single-copy atomicity is irrelevant to one thread.
//! - **SP as a load/store base is left out** (`n = 31` is not a
//!   [`valid_instr`] load or store): Sail calls `CheckSPAlignment`, which
//!   depends on `SCTLR_EL1.SA0`, and the subset does not need it. `SP` is in
//!   the state because `ADD`/`SUB` (immediate) name it with register 31.
//! - **FPCR is the constant 0**: `RMode = 00` (round to nearest, ties to
//!   even), `FZ = 0` (no flush to zero), `DN = 0` (NaNs propagate), `AH = 0`
//!   and `FIZ = 0` (the alternate floating-point behaviour of `FEAT_AFP` is
//!   off), `NEP = 0` (scalar results are not merged), `FZ16 = AHP = 0`, and
//!   every trap enable (`IOE` ... `IDE`) clear. That is the reset value an
//!   EL0 process starts with on Linux and macOS; the subset has no `MSR
//!   FPCR`, so nothing in a blob can change it; the enter stub (J.7) must
//!   keep it and J.6's theorem assumes it. Every branch that depends on
//!   another value is the one the constant selects, commented where it would
//!   have been. With `AH = 0` and `NEP = 0`, `HaveAltFP()` makes no
//!   difference, so the model holds with and without `FEAT_AFP`.
//! - **FPSR is not modelled.** `FPProcessException` with every trap enable
//!   clear only sets a cumulative flag in `FPSR`, which no instruction of the
//!   subset reads; so the calls are dropped, and commented.
//! - **Floating point is enabled and not in streaming mode.**
//!   `CheckFPEnabled64` does not trap (`CPACR_EL1.FPEN`; an OS that traps
//!   lazily restores the state and retries, which the program cannot see),
//!   and `PSTATE.SM = 0`.
//! - **Vector registers are 128 bits** ([`State::vreg`], the low 128 bits of
//!   Sail's `_Z`). `V_set` writes `ZeroExtend(value, vlen)` with
//!   `vlen = 128` when SVE is not enabled; with SVE enabled it also clears
//!   the bits above 128, which this model does not have. No instruction of
//!   the subset reads them.
//! - **Undefined values never arise.** Every `undefined` in the transcribed
//!   pseudocode is overwritten before it is read, and the
//!   `CONSTRAINED UNPREDICTABLE` cases (`Unpredictable_WBOVERLAPLD` ...)
//!   need writeback, which the subset does not have. So, unlike the x86-64
//!   spec, [`step`] takes no source of unknown values.
//! - **Reals.** Sail's `real` is the real numbers; the arithmetic of the
//!   subset needs only rationals and the square roots of rationals. A
//!   rational is [`Rat`] (as in the x86-64 spec); a [`Real`] is a rational or
//!   the square root of a nonnegative rational. `FPRoundBase` uses its
//!   operand only through comparisons, scaling by a power of two and
//!   `RoundDown` ([`real_cmp`], [`real_mul_p2`], [`real_round_down`]), and
//!   those are exact for both forms, so `FPSqrt` is transcribed exactly
//!   rather than through a round-to-odd approximation. The exponent found by
//!   `FPRoundBase`'s two `while` loops is [`real_expo`], the unique `e` with
//!   `2^e <= |op| < 2^(e+1)`, which is where the loops stop.
//! - **The PC is a `u64`**, and so are the registers; the flags are
//!   `bool`s (Sail's `bits(1)`).
//! - **Branch-target identification is not modelled**: no page is guarded
//!   (`InGuardedPage` is false), so `BTypeNext` and `PSTATE.BTYPE` have no
//!   effect. Nor are the statistical profiling, branch record and PMU hooks
//!   (`SPEBranch`, `BRBEBranch`, `PMUEvent` ...), which change no
//!   architectural state the program can read.
//! - **Field names are Sail's** (`d`, `n`, `m`, `a`, `t` for the register
//!   numbers `UInt(Rd)` ..., `datasize`, `sub_op`, `setflags`,
//!   `shift_type`, `shift_amount` ...), so each [`Instr`] variant is the
//!   argument list of the `execute_*` function it stands for, restricted to
//!   the forms the subset has.
//! - **The canonical encoding is part of this file** ([`encode`]), because
//!   the validator accepts only these words. A64 words have a fixed size, so
//!   the encoding is fixed by the fields; the choice is which field values are
//!   in the subset when two mean the same, listed at [`valid_instr`].
//!
//! # Things in the Sail model worth a reviewer's eye
//!
//! 1. `FPToFixed` gives a NaN the value 0.0 (`FPUnpack` sets `value_name =
//!    0.0` for a NaN), so `FCVTZS` of a NaN is 0, and an infinity the value
//!    `2.0 ^ 1000000`, so it saturates. Both are as Sail has them; the
//!    hardware differential tests check them.
//! 2. `decode_ldr_imm_gen_..._immediate_unsigned` (and the SIMD&FP one) call
//!    `execute_..._immediate_signed_post_idx`, not the
//!    `execute_..._immediate_unsigned` function that also exists. The two
//!    bodies are the same text; the one actually called is cited.
//! 3. `FDIV` reads `FPCR_read()` twice (once into `fpcr`, once in the call
//!    to `FPDiv`). With FPCR constant it makes no difference.
//! 4. `SDIV`/`UDIV` compute `RoundTowardsZero(Real(a) / Real(b))` through the
//!    reals; it is the integer quotient rounded toward zero, written here
//!    with integers ([`round_towards_zero_div`]). Division by zero gives 0
//!    and does not trap.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: bits
// ============================================================================
//
// Bit-vector operations of Sail's standard library (not vendored, see the
// header) on unsigned integers. A `bits(N)` value is an `int` in
// `0 .. 2^N`.

/// `2^n` as an integer (Sail `pow2(n)`, `2 ^ n`).
pub open spec fn p2(n: nat) -> int {
    vstd::arithmetic::power2::pow2(n) as int
}

/// The low `n` bits of `x`: Sail's `x[n - 1 .. 0]`, `integer_subrange`, and
/// the truncation `ZeroExtend`/assignment to `bits(n)` do. Negative `x`
/// wraps (two's complement).
pub open spec fn trunc(n: nat, x: int) -> int {
    x % p2(n)
}

/// `SInt(x)` for `x : bits(n)`: the low `n` bits read as two's complement.
pub open spec fn sint(n: nat, x: int) -> int {
    let l = trunc(n, x);
    if l >= p2((n - 1) as nat) {
        l - p2(n)
    } else {
        l
    }
}

/// Bit `k` of `x` (`x[k]`), as 0 or 1.
pub open spec fn bit(x: int, k: nat) -> int {
    (x / p2(k)) % 2
}

/// `Ones(n)`.
pub open spec fn ones(n: nat) -> int {
    p2(n) - 1
}

/// `not_vec(x)` for `x : bits(n)`.
pub open spec fn not_vec(n: nat, x: int) -> int {
    ones(n) - trunc(n, x)
}

/// `x & y` (`and_vec`) for bit vectors of at most 64 bits.
pub open spec fn and_vec(x: int, y: int) -> int {
    ((x as u64) & (y as u64)) as int
}

/// `x | y` (`or_vec`) for bit vectors of at most 64 bits.
pub open spec fn or_vec(x: int, y: int) -> int {
    ((x as u64) | (y as u64)) as int
}

/// `EOR(x, y)` (`xor_vec`) for bit vectors of at most 64 bits.
pub open spec fn eor_vec(x: int, y: int) -> int {
    ((x as u64) ^ (y as u64)) as int
}

/// `LSL(x, shift)` (`sail_shiftleft`) on `bits(n)`.
pub open spec fn lsl(n: nat, x: int, shift: nat) -> int {
    trunc(n, x * p2(shift))
}

/// `LSR(x, shift)` (`sail_shiftright`) on `bits(n)`.
pub open spec fn lsr(n: nat, x: int, shift: nat) -> int {
    trunc(n, x) / p2(shift)
}

/// `ASR(x, shift)` (`sail_arith_shiftright`) on `bits(n)`: `SInt(x)`
/// divided by `2^shift`, rounded down (Verus's `/` on `int` rounds down for
/// a positive divisor), truncated to `n` bits.
pub open spec fn asr(n: nat, x: int, shift: nat) -> int {
    trunc(n, sint(n, x) / p2(shift))
}

// sail-arm src/builtins.sail, ROR
/// `ROR(x, shift)` on `bits(n)`, `n > 0`.
pub open spec fn ror(n: nat, x: int, shift: nat) -> int {
    if shift == 0 {
        x
    } else {
        // let 'm = MOD(shift, 'N) in LSR(x, m) | LSL(x, 'N - m)
        let m = shift % n;
        or_vec(lsr(n, x, m), lsl(n, x, (n - m) as nat))
    }
}

// sail-arm src/builtins.sail, HighestSetBit
/// `HighestSetBit(x)` for `x : bits(n)`: the index of the highest set bit,
/// or -1. The `foreach` from `n - 1` down to 0 is a recursion on `n`.
pub open spec fn highest_set_bit(n: nat, x: int) -> int
    decreases n,
{
    if n == 0 {
        -1
    } else if bit(x, (n - 1) as nat) == 1 {
        n - 1
    } else {
        highest_set_bit((n - 1) as nat, x)
    }
}

/// `Replicate([b], n)` for one bit `b`: all ones or all zeros.
pub open spec fn replicate_bit(n: nat, b: int) -> int {
    if b == 1 {
        ones(n)
    } else {
        0
    }
}

// ============================================================================
// Section: real numbers
// ============================================================================
//
// Sail's `real`, for the values the subset computes: rationals, and the
// square roots of nonnegative rationals (see the header).

/// The rational `n / d` (`d` is always positive).
pub struct Rat {
    /// Numerator.
    pub n: int,
    /// Denominator, positive.
    pub d: int,
}

/// An integer as a rational (`Real(i)`, `to_real`).
pub open spec fn rat(n: int) -> Rat {
    Rat { n, d: 1 }
}

/// `2.0 ^ e` for any integer `e`.
pub open spec fn rat_p2(e: int) -> Rat {
    if e >= 0 {
        Rat { n: p2(e as nat), d: 1 }
    } else {
        Rat { n: 1, d: p2((-e) as nat) }
    }
}

/// `a + b`.
pub open spec fn rat_add(a: Rat, b: Rat) -> Rat {
    Rat { n: a.n * b.d + b.n * a.d, d: a.d * b.d }
}

/// `a - b`.
pub open spec fn rat_sub(a: Rat, b: Rat) -> Rat {
    Rat { n: a.n * b.d - b.n * a.d, d: a.d * b.d }
}

/// `a * b`.
pub open spec fn rat_mul(a: Rat, b: Rat) -> Rat {
    Rat { n: a.n * b.n, d: a.d * b.d }
}

/// `a / b` for a nonzero `b` (0 when `b` is zero; no caller divides by
/// zero).
pub open spec fn rat_div(a: Rat, b: Rat) -> Rat {
    if b.n > 0 {
        Rat { n: a.n * b.d, d: a.d * b.n }
    } else if b.n < 0 {
        Rat { n: -(a.n * b.d), d: a.d * (-b.n) }
    } else {
        rat(0)
    }
}

/// `-a` (`neg_real`).
pub open spec fn rat_neg(a: Rat) -> Rat {
    Rat { n: -a.n, d: a.d }
}

/// The sign of `a - b`: -1, 0 or 1.
pub open spec fn rat_cmp(a: Rat, b: Rat) -> int {
    if a.n * b.d < b.n * a.d {
        -1
    } else if a.n * b.d == b.n * a.d {
        0
    } else {
        1
    }
}

/// `RoundDown(a)` (`floor`): the greatest integer not above `a`. Verus's
/// `/` on `int` rounds down for a positive divisor.
pub open spec fn rat_floor(a: Rat) -> int {
    a.n / a.d
}

/// `m` is the integer square root of `x`: `0 <= m` and
/// `m * m <= x < (m + 1) * (m + 1)`.
pub open spec fn is_isqrt(x: int, m: int) -> bool {
    0 <= m && m * m <= x && x < (m + 1) * (m + 1)
}

/// The integer square root of a natural number (see [`is_isqrt`]).
pub open spec fn isqrt(x: int) -> int {
    choose|m: int| #[trigger] is_isqrt(x, m)
}

/// A real number of the subset: a rational, or the square root of a
/// nonnegative rational (what `sqrt` returns in `FPSqrt`).
pub enum Real {
    /// The rational itself.
    Rat(Rat),
    /// The nonnegative square root of the rational, which is nonnegative.
    Sqrt(Rat),
}

/// The sign of `x - r`: -1, 0 or 1. Exact: for `Sqrt(q)` with `q >= 0`,
/// `sqrt(q)` is below a negative `r` never, and otherwise compares with `r`
/// as `q` compares with `r * r`.
pub open spec fn real_cmp(x: Real, r: Rat) -> int {
    match x {
        Real::Rat(a) => rat_cmp(a, r),
        Real::Sqrt(q) => if r.n < 0 {
            1
        } else {
            rat_cmp(q, rat_mul(r, r))
        },
    }
}

/// `abs(x)`: for a rational its absolute value; a square root is already
/// nonnegative.
pub open spec fn real_abs(x: Real) -> Real {
    match x {
        Real::Rat(a) => if a.n < 0 {
            Real::Rat(rat_neg(a))
        } else {
            Real::Rat(a)
        },
        Real::Sqrt(q) => Real::Sqrt(q),
    }
}

/// `x * 2.0 ^ k` (also `x / 2.0 ^ (-k)`). For a square root,
/// `sqrt(q) * 2^k = sqrt(q * 2^(2k))`.
pub open spec fn real_mul_p2(x: Real, k: int) -> Real {
    match x {
        Real::Rat(a) => Real::Rat(rat_mul(a, rat_p2(k))),
        Real::Sqrt(q) => Real::Sqrt(rat_mul(q, rat_p2(2 * k))),
    }
}

/// `RoundDown(x)` (`floor`) for a nonnegative `x`. For a square root,
/// `floor(sqrt(q)) = isqrt(floor(q))`.
pub open spec fn real_round_down(x: Real) -> int {
    match x {
        Real::Rat(a) => rat_floor(a),
        Real::Sqrt(q) => isqrt(rat_floor(q)),
    }
}

/// The exponent `FPRoundBase`'s two `while` loops compute for a positive
/// `x`: the `e` with `2^e <= x < 2^(e + 1)`. The loops double or halve
/// `mantissa` (starting at `x`) and count until `1.0 <= mantissa < 2.0`,
/// which is when `mantissa = x / 2^e` for this `e`.
pub open spec fn real_expo(x: Real) -> int {
    choose|e: int| #[trigger] is_real_expo(x, e)
}

/// `2^e <= x < 2^(e + 1)`.
pub open spec fn is_real_expo(x: Real, e: int) -> bool {
    real_cmp(x, rat_p2(e)) >= 0 && real_cmp(x, rat_p2(e + 1)) < 0
}

// ============================================================================
// Section: floating point
// ============================================================================
//
// The IEEE 754 binary64 operations of the subset, transcribed from
// sail-arm src/v8_base.sail with `N = 64` (`E = 11`, `F = 52`) and
// FPCR = 0 (see the header). A double is its bit pattern, a `u64`.

/// `FPType` (src/v8_base.sail).
pub enum FPType {
    /// `FPType_Zero`
    Zero,
    /// `FPType_Denormal`
    Denormal,
    /// `FPType_Nonzero`
    Nonzero,
    /// `FPType_Infinity`
    Infinity,
    /// `FPType_QNaN`
    QNaN,
    /// `FPType_SNaN`
    SNaN,
}

/// `FPRounding` (src/v8_base.sail).
pub enum FPRounding {
    /// `FPRounding_TIEEVEN`
    TieEven,
    /// `FPRounding_POSINF`
    PosInf,
    /// `FPRounding_NEGINF`
    NegInf,
    /// `FPRounding_ZERO`
    Zero,
    /// `FPRounding_TIEAWAY`
    TieAway,
    /// `FPRounding_ODD`
    Odd,
}

/// What `FPUnpack` returns: `(fptype, sign, value_name)`.
pub struct Unpacked {
    /// The kind of value.
    pub fptype: FPType,
    /// The sign bit, 0 or 1.
    pub sign: int,
    /// The value (0 for a NaN, `2.0 ^ 1000000` with the sign for an
    /// infinity, as Sail has it).
    pub value: Rat,
}

// sail-arm src/v8_base.sail, FPRoundingMode, FPDecodeRounding
/// `FPRoundingMode(fpcr)`: `FPDecodeRounding(fpcr[RMode])` with
/// `RMode = 0b00`.
pub open spec fn fp_rounding_mode() -> FPRounding {
    FPRounding::TieEven
}

// sail-arm src/v8_base.sail, FPUnpackBase__1 (via FPUnpack, FPUnpack__1)
/// `FPUnpack(fpval, fpcr)` for `N = 64`. FPCR = 0, so `fz` and `fiz` are
/// false and a denormal is not flushed; `isbfloat16` is false.
pub open spec fn fp_unpack(fpval: u64) -> Unpacked {
    let x = fpval as int;
    // sign = [fpval[63]]; exp64 = fpval[62 .. 52]; frac64 = fpval[51 .. 0]
    let sign = bit(x, 63);
    let exp64 = (x / p2(52)) % p2(11);
    let frac64 = x % p2(52);
    let (fptype, value) = if exp64 == 0 {
        if frac64 == 0 {
            (FPType::Zero, rat(0))
        } else {
            // else if fz | fiz: not taken (FPCR.FZ = 0, FIZ = 0)
            // value_name = 2.0 ^ negate(1022) * (Real(UInt(frac64)) * 2.0 ^ negate(52))
            (FPType::Denormal, rat_mul(rat_p2(-1022), rat_mul(rat(frac64), rat_p2(-52))))
        }
    } else if exp64 == ones(11) {
        if frac64 == 0 {
            // value_name = 2.0 ^ 1000000
            (FPType::Infinity, rat_p2(1000000))
        } else {
            // fptype = if [frac64[51]] == 0b1 then FPType_QNaN else FPType_SNaN
            (if bit(frac64, 51) == 1 {
                FPType::QNaN
            } else {
                FPType::SNaN
            }, rat(0))
        }
    } else {
        // value_name = 2.0 ^ (UInt(exp64) - 1023) * (1.0 + Real(UInt(frac64)) * 2.0 ^ negate(52))
        (
            FPType::Nonzero,
            rat_mul(rat_p2(exp64 - 1023), rat_add(rat(1), rat_mul(rat(frac64), rat_p2(-52)))),
        )
    };
    // if sign == 0b1 then value_name = neg_real(value_name)
    let value = if sign == 1 {
        rat_neg(value)
    } else {
        value
    };
    Unpacked { fptype, sign, value }
}

/// Whether an `FPType` is a NaN.
pub open spec fn is_nan_type(t: FPType) -> bool {
    t is QNaN || t is SNaN
}

// sail-arm src/v8_base.sail, FPZero
/// `FPZero(sign, 64)`.
pub open spec fn fp_zero(sign: int) -> u64 {
    (sign * p2(63)) as u64
}

// sail-arm src/v8_base.sail, FPInfinity
/// `FPInfinity(sign, 64)`: exponent all ones, fraction zero.
pub open spec fn fp_infinity(sign: int) -> u64 {
    (sign * p2(63) + ones(11) * p2(52)) as u64
}

// sail-arm src/v8_base.sail, FPMaxNormal
/// `FPMaxNormal(sign, 64)`: exponent `Ones(10) @ 0b0`, fraction all ones.
pub open spec fn fp_max_normal(sign: int) -> u64 {
    (sign * p2(63) + (ones(11) - 1) * p2(52) + ones(52)) as u64
}

// sail-arm src/v8_base.sail, FPDefaultNaN__1
/// `FPDefaultNaN(64)`: the sign is `fpcr[AH]` = 0 (or 0 without
/// `FEAT_AFP`), the exponent all ones, the fraction `0b1 @ Zeros(51)`:
/// `0x7FF8000000000000`.
pub open spec fn fp_default_nan() -> u64 {
    (ones(11) * p2(52) + p2(51)) as u64
}

// sail-arm src/v8_base.sail, FPProcessNaN__1 (via FPProcessNaN)
/// `FPProcessNaN(fptype, op, fpcr)` for `N = 64` (`topfrac = 51`): a
/// signalling NaN is quietened by setting bit 51. `FPProcessException
/// (FPExc_InvalidOp)` only sets FPSR (not modelled); `fpcr[DN] = 0`, so the
/// result is not replaced by the default NaN.
pub open spec fn fp_process_nan(fptype: FPType, op: u64) -> u64 {
    if fptype is SNaN {
        // result[topfrac] = Bit(0b1)
        (op as int - bit(op as int, 51) * p2(51) + p2(51)) as u64
    } else {
        op
    }
}

// sail-arm src/v8_base.sail, FPProcessNaNs__1 (via FPProcessNaNs)
/// `FPProcessNaNs(type1, type2, op1, op2, fpcr)`: `Some(result)` when `done`
/// is true, `None` otherwise. `altfp` is false (`fpcr[AH] = 0`), so the
/// first branch is not taken.
pub open spec fn fp_process_nans(type1: FPType, type2: FPType, op1: u64, op2: u64) -> Option<u64> {
    // if (altfp & op1_nan) & op2_nan: not taken
    if type1 is SNaN {
        Some(fp_process_nan(type1, op1))
    } else if type2 is SNaN {
        Some(fp_process_nan(type2, op2))
    } else if type1 is QNaN {
        Some(fp_process_nan(type1, op1))
    } else if type2 is QNaN {
        Some(fp_process_nan(type2, op2))
    } else {
        None
    }
}

// sail-arm src/v8_base.sail, FPRoundBase__1 (via FPRound, FPRound__1, FPRound__2)
/// `FPRoundBase(op, fpcr, rounding, isbfloat16 = false, fpexc, 64)` for a
/// nonzero `op`. `altfp` is false (`fpcr[AH] = 0`) and `fpcr[FZ] = 0`, so
/// the flush-to-zero return and the whole `altfp` branch (with
/// `error_unconstrained`, `int_mant_unconstrained`,
/// `biased_exp_unconstrained`, which only it reads) are not taken. The
/// `FPProcessException` calls only set FPSR (not modelled). `N != 16`, so
/// `fpcr[AHP]` is not read.
///
/// `error = mantissa * 2.0 ^ F - Real(int_mant)` is not formed as a real:
/// each test on it (`error > 0.5`, `error == 0.5`, `error != 0.0`) is the
/// same comparison of `mantissa * 2.0 ^ F` with `int_mant + 0.5` or
/// `int_mant`.
pub open spec fn fp_round_base(op: Real, rounding: FPRounding) -> u64 {
    // N == 64: minimum_exp = negate(1022); E = 11; F = 52
    let minimum_exp: int = -1022;
    let e: nat = 11;
    let f: nat = 52;
    // if op < 0.0 then { sign = 0b1; mantissa = neg_real(op) } else { sign = 0b0; mantissa = op }
    let sign: int = if real_cmp(op, rat(0)) < 0 {
        1
    } else {
        0
    };
    let mantissa0 = real_abs(op);
    // the two while loops: 1.0 <= mantissa < 2.0 with mantissa = |op| / 2^exponent
    let exponent = real_expo(mantissa0);
    let mantissa1 = real_mul_p2(mantissa0, -exponent);
    // if (not(altfp) & fpcr[FZ] == 0b1 ...) & exponent < minimum_exp: not taken (FZ = 0)
    // biased_exp : int = Max(exponent - minimum_exp + 1, 0)
    let biased_exp0: int = if exponent - minimum_exp + 1 > 0 {
        exponent - minimum_exp + 1
    } else {
        0
    };
    // if biased_exp == 0 then mantissa = mantissa / 2.0 ^ (minimum_exp - exponent)
    let mantissa = if biased_exp0 == 0 {
        real_mul_p2(mantissa1, -(minimum_exp - exponent))
    } else {
        mantissa1
    };
    // int_mant : int = RoundDown(mantissa * 2.0 ^ F)
    let scaled = real_mul_p2(mantissa, f as int);
    let int_mant0 = real_round_down(scaled);
    // error : real = mantissa * 2.0 ^ F - Real(int_mant)
    let error_vs_half = real_cmp(scaled, rat_add(rat(int_mant0), Rat { n: 1, d: 2 }));
    let error_nonzero = real_cmp(scaled, rat(int_mant0)) != 0;
    // (the underflow exception only sets FPSR)
    // not(altfp): match rounding { ... }
    let (round_up, overflow_to_inf) = match rounding {
        // round_up = error > 0.5 | error == 0.5 & [int_mant[0]] == 0b1; overflow_to_inf = true
        FPRounding::TieEven => (
            error_vs_half > 0 || (error_vs_half == 0 && int_mant0 % 2 == 1),
            true,
        ),
        // round_up = error != 0.0 & sign == 0b0; overflow_to_inf = sign == 0b0
        FPRounding::PosInf => (error_nonzero && sign == 0, sign == 0),
        // round_up = error != 0.0 & sign == 0b1; overflow_to_inf = sign == 0b1
        FPRounding::NegInf => (error_nonzero && sign == 1, sign == 1),
        // round_up = false; overflow_to_inf = false
        FPRounding::Zero => (false, false),
        FPRounding::Odd => (false, false),
        // _ => (): FPRoundBase asserts rounding != FPRounding_TIEAWAY
        FPRounding::TieAway => (false, false),
    };
    // if round_up then { int_mant = int_mant + 1;
    //   if int_mant == pow2(F) then biased_exp = 1;
    //   if int_mant == pow2(F + 1) then { biased_exp = biased_exp + 1; int_mant = DIV(int_mant, 2) } }
    let int_mant1 = if round_up {
        int_mant0 + 1
    } else {
        int_mant0
    };
    let biased_exp1 = if round_up && int_mant1 == p2(f) {
        1
    } else {
        biased_exp0
    };
    let (biased_exp, int_mant2) = if round_up && int_mant1 == p2(f + 1) {
        (biased_exp1 + 1, int_mant1 / 2)
    } else {
        (biased_exp1, int_mant1)
    };
    // if error != 0.0 & rounding == FPRounding_ODD then int_mant = [int_mant with 0 .. 0 = 0b1]
    let int_mant = if error_nonzero && rounding is Odd {
        int_mant2 - int_mant2 % 2 + 1
    } else {
        int_mant2
    };
    // N != 16:
    if biased_exp >= p2(e) - 1 {
        // result = if overflow_to_inf then FPInfinity(sign, N) else FPMaxNormal(sign, N)
        if overflow_to_inf {
            fp_infinity(sign)
        } else {
            fp_max_normal(sign)
        }
    } else {
        // result = ((sign @ biased_exp[E - 1 .. 0]) @ int_mant[F - 1 .. 0])
        (sign * p2(63) + trunc(e, biased_exp) * p2(f) + trunc(f, int_mant)) as u64
    }
}

// sail-arm src/v8_base.sail, FPRound, FPRound__1, FPRound__2
/// `FPRound(op, fpcr, rounding, 64)`: `fpcr[AHP]` is cleared and
/// `FPRoundBase` called with `isbfloat16 = false`.
pub open spec fn fp_round(op: Real, rounding: FPRounding) -> u64 {
    fp_round_base(op, rounding)
}

// sail-arm src/v8_base.sail, FPAdd__1 (via FPAdd)
/// `FPAdd(op1, op2, fpcr)` for `N = 64`. `FPProcessDenorms` only raises an
/// exception with `altfp`, so it is dropped.
pub open spec fn fp_add(op1: u64, op2: u64) -> u64 {
    let rounding = fp_rounding_mode();
    let u1 = fp_unpack(op1);
    let u2 = fp_unpack(op2);
    match fp_process_nans(u1.fptype, u2.fptype, op1, op2) {
        Some(result) => result,
        None => {
            let inf1 = u1.fptype is Infinity;
            let inf2 = u2.fptype is Infinity;
            let zero1 = u1.fptype is Zero;
            let zero2 = u2.fptype is Zero;
            if inf1 && inf2 && u1.sign == 1 - u2.sign {
                // result = FPDefaultNaN; FPProcessException(FPExc_InvalidOp)
                fp_default_nan()
            } else if (inf1 && u1.sign == 0) || (inf2 && u2.sign == 0) {
                fp_infinity(0)
            } else if (inf1 && u1.sign == 1) || (inf2 && u2.sign == 1) {
                fp_infinity(1)
            } else if zero1 && zero2 && u1.sign == u2.sign {
                fp_zero(u1.sign)
            } else {
                let result_value = rat_add(u1.value, u2.value);
                if result_value.n == 0 {
                    // result_sign = if rounding == FPRounding_NEGINF then 0b1 else 0b0
                    fp_zero(
                        if rounding is NegInf {
                            1
                        } else {
                            0
                        },
                    )
                } else {
                    fp_round(Real::Rat(result_value), rounding)
                }
            }
        },
    }
}

// sail-arm src/v8_base.sail, FPSub__1 (via FPSub)
/// `FPSub(op1, op2, fpcr)` for `N = 64`.
pub open spec fn fp_sub(op1: u64, op2: u64) -> u64 {
    let rounding = fp_rounding_mode();
    let u1 = fp_unpack(op1);
    let u2 = fp_unpack(op2);
    match fp_process_nans(u1.fptype, u2.fptype, op1, op2) {
        Some(result) => result,
        None => {
            let inf1 = u1.fptype is Infinity;
            let inf2 = u2.fptype is Infinity;
            let zero1 = u1.fptype is Zero;
            let zero2 = u2.fptype is Zero;
            if inf1 && inf2 && u1.sign == u2.sign {
                fp_default_nan()
            } else if (inf1 && u1.sign == 0) || (inf2 && u2.sign == 1) {
                fp_infinity(0)
            } else if (inf1 && u1.sign == 1) || (inf2 && u2.sign == 0) {
                fp_infinity(1)
            } else if zero1 && zero2 && u1.sign == 1 - u2.sign {
                fp_zero(u1.sign)
            } else {
                let result_value = rat_sub(u1.value, u2.value);
                if result_value.n == 0 {
                    fp_zero(
                        if rounding is NegInf {
                            1
                        } else {
                            0
                        },
                    )
                } else {
                    fp_round(Real::Rat(result_value), rounding)
                }
            }
        },
    }
}

// sail-arm src/v8_base.sail, FPMul
/// `FPMul(op1, op2, fpcr)` for `N = 64`.
pub open spec fn fp_mul(op1: u64, op2: u64) -> u64 {
    let u1 = fp_unpack(op1);
    let u2 = fp_unpack(op2);
    match fp_process_nans(u1.fptype, u2.fptype, op1, op2) {
        Some(result) => result,
        None => {
            let inf1 = u1.fptype is Infinity;
            let inf2 = u2.fptype is Infinity;
            let zero1 = u1.fptype is Zero;
            let zero2 = u2.fptype is Zero;
            if (inf1 && zero2) || (zero1 && inf2) {
                fp_default_nan()
            } else if inf1 || inf2 {
                // FPInfinity(EOR(sign1, sign2), 'N)
                fp_infinity(eor_vec(u1.sign, u2.sign))
            } else if zero1 || zero2 {
                fp_zero(eor_vec(u1.sign, u2.sign))
            } else {
                // FPRound(value1_name * value2_name, fpcr, 'N)
                fp_round(Real::Rat(rat_mul(u1.value, u2.value)), fp_rounding_mode())
            }
        },
    }
}

// sail-arm src/v8_base.sail, FPDiv
/// `FPDiv(op1, op2, fpcr)` for `N = 64`. The divide-by-zero exception only
/// sets FPSR.
pub open spec fn fp_div(op1: u64, op2: u64) -> u64 {
    let u1 = fp_unpack(op1);
    let u2 = fp_unpack(op2);
    match fp_process_nans(u1.fptype, u2.fptype, op1, op2) {
        Some(result) => result,
        None => {
            let inf1 = u1.fptype is Infinity;
            let inf2 = u2.fptype is Infinity;
            let zero1 = u1.fptype is Zero;
            let zero2 = u2.fptype is Zero;
            if (inf1 && inf2) || (zero1 && zero2) {
                fp_default_nan()
            } else if inf1 || zero2 {
                fp_infinity(eor_vec(u1.sign, u2.sign))
            } else if zero1 || inf2 {
                fp_zero(eor_vec(u1.sign, u2.sign))
            } else {
                // FPRound(value1_name / value2_name, fpcr, 'N)
                fp_round(Real::Rat(rat_div(u1.value, u2.value)), fp_rounding_mode())
            }
        },
    }
}

// sail-arm src/v8_base.sail, FPSqrt
/// `FPSqrt(op, fpcr)` for `N = 64`. `sqrt(value_name)` is
/// `Real::Sqrt(value_name)` (the value is positive there).
pub open spec fn fp_sqrt(op: u64) -> u64 {
    let u = fp_unpack(op);
    if is_nan_type(u.fptype) {
        fp_process_nan(u.fptype, op)
    } else if u.fptype is Zero {
        fp_zero(u.sign)
    } else if u.fptype is Infinity && u.sign == 0 {
        fp_infinity(u.sign)
    } else if u.sign == 1 {
        fp_default_nan()
    } else {
        // result = FPRound(sqrt(value_name), fpcr, 'N); FPProcessDenorm: altfp only
        fp_round(Real::Sqrt(u.value), fp_rounding_mode())
    }
}

// sail-arm src/v8_base.sail, FPAbs
/// `FPAbs(op)`: `0b0 @ op['N - 2 .. 0]` (the `fpcr[AH] == 0b1` branch is not
/// taken).
pub open spec fn fp_abs(op: u64) -> u64 {
    (op as int - bit(op as int, 63) * p2(63)) as u64
}

// sail-arm src/v8_base.sail, FPNeg
/// `FPNeg(op)`: `not_vec([op['N - 1]]) @ op['N - 2 .. 0]` (the
/// `fpcr[AH] == 0b1` branch is not taken).
pub open spec fn fp_neg(op: u64) -> u64 {
    (op as int - bit(op as int, 63) * p2(63) + (1 - bit(op as int, 63)) * p2(63)) as u64
}

// sail-arm src/v8_base.sail, FPCompare
/// `FPCompare(op1, op2, signal_nans, fpcr)` for `N = 64`: the `NZCV` bits,
/// `0b0011` unordered, `0b0110` equal, `0b1000` less, `0b0010` greater. The
/// invalid-operation exception only sets FPSR, so `signal_nans` changes
/// nothing here.
pub open spec fn fp_compare(op1: u64, op2: u64) -> int {
    let u1 = fp_unpack(op1);
    let u2 = fp_unpack(op2);
    if is_nan_type(u1.fptype) || is_nan_type(u2.fptype) {
        0b0011
    } else {
        let c = rat_cmp(u1.value, u2.value);
        if c == 0 {
            0b0110
        } else if c < 0 {
            0b1000
        } else {
            0b0010
        }
    }
}

// sail-arm src/v8_base.sail, SignedSatQ, UnsignedSatQ, SatQ
/// `SatQ(i, N, is_unsigned)`, the result bits only (the saturation flag
/// only decides an FPSR exception).
pub open spec fn sat_q(i: int, n: nat, is_unsigned: bool) -> int {
    let result = if is_unsigned {
        // UnsignedSatQ
        if i > p2(n) - 1 {
            p2(n) - 1
        } else if i < 0 {
            0
        } else {
            i
        }
    } else {
        // SignedSatQ
        if i > p2((n - 1) as nat) - 1 {
            p2((n - 1) as nat) - 1
        } else if i < -p2((n - 1) as nat) {
            -p2((n - 1) as nat)
        } else {
            i
        }
    };
    // result[N - 1 .. 0]
    trunc(n, result)
}

// sail-arm src/v8_base.sail, FPToFixed
/// `FPToFixed(op, fbits, is_unsigned, fpcr, rounding, M)` for `N = 64`: the
/// `M`-bit result. A NaN unpacks to the value 0.0 and an infinity to
/// `2.0 ^ 1000000` (see [`fp_unpack`]), so they convert to 0 and saturate.
pub open spec fn fp_to_fixed(op: u64, fbits: nat, is_unsigned: bool, rounding: FPRounding, m: nat) -> int {
    let u = fp_unpack(op);
    // if fptype is a NaN: FPProcessException(FPExc_InvalidOp) only
    // value_name = value_name * 2.0 ^ fbits
    let value = rat_mul(u.value, rat_p2(fbits as int));
    // int_result : int = RoundDown(value_name); error = value_name - Real(int_result)
    let int_result0 = rat_floor(value);
    let error = rat_sub(value, rat(int_result0));
    let half = Rat { n: 1, d: 2 };
    let round_up = match rounding {
        // error > 0.5 | error == 0.5 & [int_result[0]] == 0b1
        FPRounding::TieEven => rat_cmp(error, half) > 0 || (rat_cmp(error, half) == 0
            && int_result0 % 2 == 1),
        // error != 0.0
        FPRounding::PosInf => error.n != 0,
        // false
        FPRounding::NegInf => false,
        // error != 0.0 & int_result < 0
        FPRounding::Zero => error.n != 0 && int_result0 < 0,
        // error > 0.5 | error == 0.5 & int_result >= 0
        FPRounding::TieAway => rat_cmp(error, half) > 0 || (rat_cmp(error, half) == 0
            && int_result0 >= 0),
        // _ => (): FPToFixed asserts rounding != FPRounding_ODD
        FPRounding::Odd => false,
    };
    let int_result = if round_up {
        int_result0 + 1
    } else {
        int_result0
    };
    // (result, overflow) = SatQ(int_result, M, is_unsigned)
    sat_q(int_result, m, is_unsigned)
}

// sail-arm src/v8_base.sail, FixedToFP
/// `FixedToFP(op, fbits, is_unsigned, fpcr, rounding, N)` for `N = 64` and
/// `op : bits(m)`.
pub open spec fn fixed_to_fp(op: int, m: nat, fbits: nat, is_unsigned: bool, rounding: FPRounding) -> u64 {
    // int_operand = asl_Int(op, is_unsigned)
    let int_operand = if is_unsigned {
        trunc(m, op)
    } else {
        sint(m, op)
    };
    // real_operand : real = Real(int_operand) / 2.0 ^ fbits
    let real_operand = rat_mul(rat(int_operand), rat_p2(-(fbits as int)));
    if real_operand.n == 0 {
        fp_zero(0)
    } else {
        // FPRound__1(real_operand, fpcr, rounding, N)
        fp_round(Real::Rat(real_operand), rounding)
    }
}

// ============================================================================
// Section: syntax
// ============================================================================
//
// The abstract syntax of the subset: one variant per `execute_*` function
// (with the parameters the subset fixes left out), and the predicate saying
// which values are in the subset.

/// `datasize` (also `intsize`, `regsize`, `destsize`): `sf = 0` gives 32,
/// `sf = 1` gives 64.
pub enum Width {
    /// `sf = 0`: W registers.
    W32,
    /// `sf = 1`: X registers.
    W64,
}

/// `datasize` in bits.
pub open spec fn datasize(sf: Width) -> nat {
    match sf {
        Width::W32 => 32,
        Width::W64 => 64,
    }
}

/// The `sf` bit.
pub open spec fn sf_bit(sf: Width) -> int {
    match sf {
        Width::W32 => 0,
        Width::W64 => 1,
    }
}

/// `ShiftType` (`DecodeShift`: `0b00` LSL, `0b01` LSR, `0b10` ASR, `0b11`
/// ROR).
pub enum ShiftType {
    /// `ShiftType_LSL`
    Lsl,
    /// `ShiftType_LSR`
    Lsr,
    /// `ShiftType_ASR`
    Asr,
    /// `ShiftType_ROR`
    Ror,
}

/// The encoding of a `ShiftType` (`DecodeShift`'s argument).
pub open spec fn shift_field(s: ShiftType) -> int {
    match s {
        ShiftType::Lsl => 0,
        ShiftType::Lsr => 1,
        ShiftType::Asr => 2,
        ShiftType::Ror => 3,
    }
}

/// The `opc` field of the logical shifted-register instructions, which
/// gives `op` and `setflags` (`decode_and_log_shift_...`): `0b00` AND,
/// `0b01` ORR, `0b10` EOR, `0b11` ANDS.
pub enum LogicalOpc {
    /// `AND`: `LogicalOp_AND`, no flags.
    And,
    /// `ORR`: `LogicalOp_ORR`, no flags.
    Orr,
    /// `EOR`: `LogicalOp_EOR`, no flags.
    Eor,
    /// `ANDS`: `LogicalOp_AND`, `setflags`.
    Ands,
}

/// `MoveWideOp` for the forms of the subset.
pub enum MoveWideOp {
    /// `MoveWideOp_Z` (`MOVZ`, `opc = 0b10`).
    Z,
    /// `MoveWideOp_K` (`MOVK`, `opc = 0b11`).
    K,
}

/// `FPUnaryOp` (the `opc` field of the one-source FP instructions).
pub enum FPUnaryOp {
    /// `FPUnaryOp_MOV` (`FMOV` register, `opc = 0b00`).
    Mov,
    /// `FPUnaryOp_ABS` (`FABS`, `0b01`).
    Abs,
    /// `FPUnaryOp_NEG` (`FNEG`, `0b10`).
    Neg,
    /// `FPUnaryOp_SQRT` (`FSQRT`, `0b11`).
    Sqrt,
}

/// One instruction of the subset. Register numbers are `0 ..= 31`; what 31
/// means (the zero register or `SP`) is the instruction's, as in Sail. A
/// condition `cond` is the 4-bit field `ConditionHolds` reads. A branch
/// offset is the signed immediate field (`imm26`, `imm19`), counted in
/// instructions: the byte offset is four times it.
pub enum Instr {
    // ---- integer arithmetic ----
    /// `ADD`, `ADDS`, `SUB`, `SUBS` (shifted register):
    /// `decode_add_addsub_shift_...` and the `adds`, `sub`, `subs` ones,
    /// `execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg`.
    AddSubShiftedReg {
        /// The operand size.
        sf: Width,
        /// `SUB`/`SUBS` (`op = 1`).
        sub_op: bool,
        /// `ADDS`/`SUBS` (`S = 1`).
        setflags: bool,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
        /// `shift`.
        shift_type: ShiftType,
        /// `imm6`.
        shift_amount: u8,
    },
    /// `ADD`, `ADDS`, `SUB`, `SUBS` (immediate):
    /// `decode_add_addsub_imm_...` and the others,
    /// `execute_aarch64_instrs_integer_arithmetic_add_sub_immediate`.
    /// Register 31 is `SP` as `n`, and as `d` when `setflags` is false.
    AddSubImm {
        /// The operand size.
        sf: Width,
        /// `SUB`/`SUBS`.
        sub_op: bool,
        /// `ADDS`/`SUBS`.
        setflags: bool,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `imm12`.
        imm12: u16,
        /// `sh`: the immediate is shifted left by 12.
        sh: bool,
    },
    /// `MADD`, `MSUB`: `decode_madd_...`, `decode_msub_...`,
    /// `execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub`.
    MulAddSub {
        /// The operand size.
        sf: Width,
        /// `MSUB` (`o0 = 1`).
        sub_op: bool,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
        /// `Ra`.
        a: u8,
    },
    /// `SDIV`, `UDIV`: `decode_sdiv_...`, `decode_udiv_...`,
    /// `execute_aarch64_instrs_integer_arithmetic_div`.
    Div {
        /// The operand size.
        sf: Width,
        /// `UDIV` (`o1 = 0`).
        is_unsigned: bool,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
    },
    // ---- logic, shifts, bit fields, constants ----
    /// `AND`, `ORR`, `EOR`, `ANDS` (shifted register, `N = 0`):
    /// `decode_and_log_shift_...` and the others,
    /// `execute_aarch64_instrs_integer_logical_shiftedreg`.
    LogicalShiftedReg {
        /// The operand size.
        sf: Width,
        /// `opc`.
        opc: LogicalOpc,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
        /// `shift`.
        shift_type: ShiftType,
        /// `imm6`.
        shift_amount: u8,
    },
    /// `LSLV`, `LSRV`, `ASRV`: `decode_lslv_...` and the others,
    /// `execute_aarch64_instrs_integer_shift_variable`.
    ShiftVariable {
        /// The operand size.
        sf: Width,
        /// `op2` (`DecodeShift`); not `Ror`.
        shift_type: ShiftType,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
    },
    /// `SBFM`, `UBFM` with `N = sf`: `decode_sbfm_...`, `decode_ubfm_...`,
    /// `execute_aarch64_instrs_integer_bitfield`.
    Bitfield {
        /// The operand size.
        sf: Width,
        /// `SBFM` (`opc = 0b00`: `inzero`, `extend`) rather than `UBFM`
        /// (`opc = 0b10`: `inzero`, not `extend`).
        signed: bool,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `immr`.
        immr: u8,
        /// `imms`.
        imms: u8,
    },
    /// `MOVZ`, `MOVK`: `decode_movz_...`, `decode_movk_...`,
    /// `execute_aarch64_instrs_integer_ins_ext_insert_movewide`.
    MoveWide {
        /// The operand size.
        sf: Width,
        /// `opc`.
        opcode: MoveWideOp,
        /// `Rd`.
        d: u8,
        /// `imm16`.
        imm16: u16,
        /// `hw`: `pos = hw * 16`.
        hw: u8,
    },
    // ---- conditional select ----
    /// `CSEL`, `CSINC`, `CSINV`, `CSNEG`: `decode_csel_...` and the others,
    /// `execute_aarch64_instrs_integer_conditional_select`.
    CondSelect {
        /// The operand size.
        sf: Width,
        /// `CSINV`/`CSNEG` (`op = 1`).
        else_inv: bool,
        /// `CSINC`/`CSNEG` (`o2 = 1`).
        else_inc: bool,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
        /// `cond`.
        cond: u8,
    },
    // ---- loads and stores ----
    /// `LDR`, `STR` (immediate, unsigned offset) of a W (`size = 0b10`) or
    /// X (`0b11`) register: `decode_ldr_imm_gen_..._immediate_unsigned`,
    /// `decode_str_imm_gen_..._immediate_unsigned`,
    /// `execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx`
    /// (with `postindex` and `wback` false).
    LoadStoreImm {
        /// The access and register size (`regsize = datasize`).
        sf: Width,
        /// `LDR` (`opc = 0b01`) rather than `STR` (`0b00`).
        load: bool,
        /// `Rt`.
        t: u8,
        /// `Rn` (not 31).
        n: u8,
        /// `imm12`: the offset is `imm12 << scale`.
        imm12: u16,
    },
    /// `LDR`, `STR` (register) of a W or X register, `option = 0b011`
    /// (`UXTX`, written `LSL`): `decode_ldr_reg_gen_...`,
    /// `decode_str_reg_gen_...`,
    /// `execute_aarch64_instrs_memory_single_general_register`.
    LoadStoreReg {
        /// The access and register size.
        sf: Width,
        /// `LDR` rather than `STR`.
        load: bool,
        /// `Rt`.
        t: u8,
        /// `Rn` (not 31).
        n: u8,
        /// `Rm`.
        m: u8,
        /// `S`: the offset register is shifted left by `scale`.
        s: bool,
    },
    /// `LDR`, `STR` (immediate, SIMD&FP, unsigned offset) of a D register
    /// (`size = 0b11`, `opc = 0b0x`):
    /// `decode_ldr_imm_fpsimd_..._immediate_unsigned`,
    /// `decode_str_imm_fpsimd_..._immediate_unsigned`,
    /// `execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx`.
    FpLoadStoreImm {
        /// `LDR` rather than `STR`.
        load: bool,
        /// `Rt` (a vector register).
        t: u8,
        /// `Rn` (not 31).
        n: u8,
        /// `imm12`: the offset is `imm12 << 3`.
        imm12: u16,
    },
    /// `LDR`, `STR` (register, SIMD&FP) of a D register, `option = 0b011`:
    /// `decode_ldr_reg_fpsimd_...`, `decode_str_reg_fpsimd_...`,
    /// `execute_aarch64_instrs_memory_single_simdfp_register`.
    FpLoadStoreReg {
        /// `LDR` rather than `STR`.
        load: bool,
        /// `Rt` (a vector register).
        t: u8,
        /// `Rn` (not 31).
        n: u8,
        /// `Rm`.
        m: u8,
        /// `S`: the offset register is shifted left by 3.
        s: bool,
    },
    // ---- branches ----
    /// `B`: `decode_b_uncond_...`,
    /// `execute_aarch64_instrs_branch_unconditional_immediate` with
    /// `BranchType_DIR`.
    B {
        /// `imm26`, signed: the offset is `imm26 * 4`.
        imm26: i32,
    },
    /// `B.cond`: `decode_b_cond_...`,
    /// `execute_aarch64_instrs_branch_conditional_cond`.
    BCond {
        /// `cond`.
        cond: u8,
        /// `imm19`, signed.
        imm19: i32,
    },
    /// `CBZ`, `CBNZ`: `decode_cbz_...`, `decode_cbnz_...`,
    /// `execute_aarch64_instrs_branch_conditional_compare`.
    CompareBranch {
        /// The operand size.
        sf: Width,
        /// `CBZ` (`op = 0`) rather than `CBNZ`.
        iszero: bool,
        /// `Rt`.
        t: u8,
        /// `imm19`, signed.
        imm19: i32,
    },
    /// `RET` (through `X30`): `decode_ret_...`,
    /// `execute_aarch64_instrs_branch_unconditional_register` with
    /// `BranchType_RET`, `n = 30`, no `pac`.
    Ret,
    // ---- scalar double floating point (ftype = 0b01) ----
    /// `FADD`, `FSUB` (scalar): `decode_fadd_float_...`,
    /// `decode_fsub_float_...`,
    /// `execute_aarch64_instrs_float_arithmetic_add_sub`.
    FAddSub {
        /// `FSUB` (`op = 1`).
        sub_op: bool,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
    },
    /// `FMUL` (scalar): `decode_fmul_float_...`,
    /// `execute_aarch64_instrs_float_arithmetic_mul_product` with `negated`
    /// false.
    FMul {
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
    },
    /// `FDIV` (scalar): `decode_fdiv_float_...`,
    /// `execute_aarch64_instrs_float_arithmetic_div`.
    FDiv {
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
    },
    /// `FMOV`, `FABS`, `FNEG`, `FSQRT` (scalar, register):
    /// `decode_fmov_float_...` and the others,
    /// `execute_aarch64_instrs_float_arithmetic_unary`.
    FUnary {
        /// `opc`.
        fpop: FPUnaryOp,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
    },
    /// `FCMP Dn, Dm` (`opc = 0b00`): `decode_fcmp_float_...`,
    /// `execute_aarch64_instrs_float_compare_uncond` with `cmp_with_zero`
    /// and `signal_all_nans` false.
    FCmp {
        /// `Rn`.
        n: u8,
        /// `Rm`.
        m: u8,
    },
    /// `FMOV Xd, Dn` (`to_fp` false, `opcode = 0b110`) or `FMOV Dd, Xn`
    /// (`to_fp`, `0b111`), `sf = 1`, `rmode = 0b00`:
    /// `decode_fmov_float_gen_...`,
    /// `execute_aarch64_instrs_float_convert_int` with
    /// `FPConvOp_MOV_FtoI`/`FPConvOp_MOV_ItoF`, `part = 0`.
    FMovGen {
        /// General to FP register.
        to_fp: bool,
        /// `Rd`.
        d: u8,
        /// `Rn`.
        n: u8,
    },
    /// `SCVTF Dd, Wn/Xn` (`rmode = 0b00`, `opcode = 0b010`):
    /// `decode_scvtf_float_int_...`,
    /// `execute_aarch64_instrs_float_convert_int` with `FPConvOp_CVT_ItoF`.
    Scvtf {
        /// `intsize`.
        sf: Width,
        /// `Rd` (a vector register).
        d: u8,
        /// `Rn`.
        n: u8,
    },
    /// `FCVTZS Wd/Xd, Dn` (`rmode = 0b11`, `opcode = 0b000`):
    /// `decode_fcvtzs_float_int_...`,
    /// `execute_aarch64_instrs_float_convert_int` with `FPConvOp_CVT_FtoI`
    /// and `FPRounding_ZERO`.
    Fcvtzs {
        /// `intsize`.
        sf: Width,
        /// `Rd`.
        d: u8,
        /// `Rn` (a vector register).
        n: u8,
    },
}

/// A 5-bit register field.
pub open spec fn reg_ok(r: u8) -> bool {
    r < 32
}

/// A signed field of `bits` bits: `-2^(bits-1) <= v < 2^(bits-1)`.
pub open spec fn signed_fits(v: int, bits: nat) -> bool {
    -p2((bits - 1) as nat) <= v && v < p2((bits - 1) as nat)
}

/// A shifted-register operand: the amount is below `datasize` (Sail
/// throws `Error_Undefined` for `sf = 0` and `imm6[5] = 1`), and, as the
/// subset's choice, an amount of 0 is written `LSL` (`LSR #0`, `ASR #0` and
/// `ROR #0` mean the same as `LSL #0`).
pub open spec fn shifted_reg_ok(sf: Width, shift_type: ShiftType, shift_amount: u8) -> bool {
    (shift_amount as int) < datasize(sf) && (shift_amount == 0 ==> shift_type is Lsl)
}

/// Whether `i` is an instruction of the subset: its fields are in range,
/// Sail's decoder does not throw `Error_Undefined` for it, and it is the
/// canonical one of the field values that mean the same. The canonical
/// choices (the subset's, not Sail's) are:
///
/// - a shift by 0 in a shifted-register operand is `LSL` ([`shifted_reg_ok`]);
/// - an immediate of 0 in `ADD`/`SUB` (immediate) has `sh = 0`;
/// - a `MOVZ` of 0 has `hw = 0`;
/// - a condition is never `0b1110` (AL) or `0b1111` (NV), which mean
///   "always" (`ConditionHolds`): an unconditional branch is `B`, and a
///   select that always picks `n` is not in the subset;
/// - the register offset of a load or store is `UXTX` (`option = 0b011`,
///   written `LSL`), not `SXTX` (`0b111`), which means the same for a 64-bit
///   register;
/// - `RET` is through `X30`.
///
/// Sail's own rejections that the fields could otherwise express: `shift =
/// 0b11` (ROR) in `ADD`/`SUB`; `imm6[5]`, `immr[5]` or `imms[5]` set with
/// `sf = 0`; `hw[1]` set with `sf = 0`. A base of 31 (`SP`) in a load or
/// store is the subset's exclusion (see the header).
pub open spec fn valid_instr(i: Instr) -> bool {
    match i {
        Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount } =>
            reg_ok(d) && reg_ok(n) && reg_ok(m) && !(shift_type is Ror) && shifted_reg_ok(
            sf,
            shift_type,
            shift_amount,
        ),
        Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh } => reg_ok(d) && reg_ok(n)
            && imm12 < 4096 && (sh ==> imm12 != 0),
        Instr::MulAddSub { sf, sub_op, d, n, m, a } => reg_ok(d) && reg_ok(n) && reg_ok(m)
            && reg_ok(a),
        Instr::Div { sf, is_unsigned, d, n, m } => reg_ok(d) && reg_ok(n) && reg_ok(m),
        Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount } => reg_ok(d)
            && reg_ok(n) && reg_ok(m) && shifted_reg_ok(sf, shift_type, shift_amount),
        Instr::ShiftVariable { sf, shift_type, d, n, m } => reg_ok(d) && reg_ok(n) && reg_ok(m)
            && !(shift_type is Ror),
        Instr::Bitfield { sf, signed, d, n, immr, imms } => reg_ok(d) && reg_ok(n) && (immr as int)
            < datasize(sf) && (imms as int) < datasize(sf),
        Instr::MoveWide { sf, opcode, d, imm16, hw } => reg_ok(d) && (hw as int) * 16 < datasize(
            sf,
        ) && (opcode is Z && imm16 == 0 ==> hw == 0),
        Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond } => reg_ok(d) && reg_ok(n)
            && reg_ok(m) && cond < 14,
        Instr::LoadStoreImm { sf, load, t, n, imm12 } => reg_ok(t) && reg_ok(n) && n != 31
            && imm12 < 4096,
        Instr::LoadStoreReg { sf, load, t, n, m, s } => reg_ok(t) && reg_ok(n) && n != 31
            && reg_ok(m),
        Instr::FpLoadStoreImm { load, t, n, imm12 } => reg_ok(t) && reg_ok(n) && n != 31 && imm12
            < 4096,
        Instr::FpLoadStoreReg { load, t, n, m, s } => reg_ok(t) && reg_ok(n) && n != 31 && reg_ok(
            m,
        ),
        Instr::B { imm26 } => signed_fits(imm26 as int, 26),
        Instr::BCond { cond, imm19 } => cond < 14 && signed_fits(imm19 as int, 19),
        Instr::CompareBranch { sf, iszero, t, imm19 } => reg_ok(t) && signed_fits(imm19 as int, 19),
        Instr::Ret => true,
        Instr::FAddSub { sub_op, d, n, m } => reg_ok(d) && reg_ok(n) && reg_ok(m),
        Instr::FMul { d, n, m } => reg_ok(d) && reg_ok(n) && reg_ok(m),
        Instr::FDiv { d, n, m } => reg_ok(d) && reg_ok(n) && reg_ok(m),
        Instr::FUnary { fpop, d, n } => reg_ok(d) && reg_ok(n),
        Instr::FCmp { n, m } => reg_ok(n) && reg_ok(m),
        Instr::FMovGen { to_fp, d, n } => reg_ok(d) && reg_ok(n),
        Instr::Scvtf { sf, d, n } => reg_ok(d) && reg_ok(n),
        Instr::Fcvtzs { sf, d, n } => reg_ok(d) && reg_ok(n),
    }
}

// ============================================================================
// Section: encoding
// ============================================================================
//
// The canonical encoding: the 32-bit word of each instruction of the subset.
// Each is the bit pattern of the `__DecodeA64_*` clause that calls the
// instruction's `decode_*` function (src/instrs64.sail; the clause lists the
// bits from bit 31 down to bit 0, `_` for a field bit), with the fields at
// the positions its `Slice(__opcode, lsb, width)` calls name. The constant
// part of each word is written in hexadecimal; the fields are added at their
// positions (multiplication by `2^lsb`). Sail's decoder reads every
// encoding; what makes these words the subset's is only [`valid_instr`].
//
// Instructions are fetched little-endian (`__FetchInstr` reads with
// `AArch64_MemSingle_read`, which does not apply `BigEndian`): the word's
// bytes in memory are [`word_bytes`].

/// A 0/1 field from a `bool`.
pub open spec fn b(x: bool) -> int {
    if x {
        1
    } else {
        0
    }
}

/// The `shift` field value of a shifted-register form.
pub open spec fn enc_shifted_reg(
    sf: Width,
    d: u8,
    n: u8,
    m: u8,
    shift_type: ShiftType,
    shift_amount: u8,
) -> int {
    // sf @ 31, shift @ 22, Rm @ 16, imm6 @ 10, Rn @ 5, Rd @ 0
    sf_bit(sf) * 0x8000_0000 + shift_field(shift_type) * 0x40_0000 + (m as int) * 0x1_0000 + (
    shift_amount as int) * 0x400 + (n as int) * 0x20 + (d as int)
}

/// The `opc` field of a [`LogicalOpc`].
pub open spec fn logical_opc_field(opc: LogicalOpc) -> int {
    match opc {
        LogicalOpc::And => 0,
        LogicalOpc::Orr => 1,
        LogicalOpc::Eor => 2,
        LogicalOpc::Ands => 3,
    }
}

/// The `opc` field of an [`FPUnaryOp`].
pub open spec fn fp_unary_opc_field(op: FPUnaryOp) -> int {
    match op {
        FPUnaryOp::Mov => 0,
        FPUnaryOp::Abs => 1,
        FPUnaryOp::Neg => 2,
        FPUnaryOp::Sqrt => 3,
    }
}

/// The canonical encoding of an instruction, as an integer (a 32-bit word
/// for a [`valid_instr`]; any other value is not in the subset).
pub open spec fn encode(i: Instr) -> int {
    match i {
        // decode_add_addsub_shift_... `.0001011 ..0..... ........ ........`
        // (sub: op @ 30; adds/subs: S @ 29)
        Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount } =>
            0x0B00_0000 + b(sub_op) * 0x4000_0000 + b(setflags) * 0x2000_0000 + enc_shifted_reg(
            sf,
            d,
            n,
            m,
            shift_type,
            shift_amount,
        ),
        // decode_add_addsub_imm_... `.0010001 0....... ........ ........`:
        // sf @ 31, op @ 30, S @ 29, sh @ 22, imm12 @ 10, Rn @ 5, Rd @ 0
        Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh } => 0x1100_0000 + sf_bit(sf)
            * 0x8000_0000 + b(sub_op) * 0x4000_0000 + b(setflags) * 0x2000_0000 + b(sh) * 0x40_0000
            + (imm12 as int) * 0x400 + (n as int) * 0x20 + (d as int),
        // decode_madd_... `.0011011 000..... 0....... ........`:
        // sf @ 31, Rm @ 16, o0 @ 15, Ra @ 10, Rn @ 5, Rd @ 0
        Instr::MulAddSub { sf, sub_op, d, n, m, a } => 0x1B00_0000 + sf_bit(sf) * 0x8000_0000 + (
        m as int) * 0x1_0000 + b(sub_op) * 0x8000 + (a as int) * 0x400 + (n as int) * 0x20 + (
        d as int),
        // decode_udiv_... `.0011010 110..... 000010.. ........` (sdiv: o1 @ 10)
        Instr::Div { sf, is_unsigned, d, n, m } => 0x1AC0_0800 + sf_bit(sf) * 0x8000_0000 + (
        m as int) * 0x1_0000 + b(!is_unsigned) * 0x400 + (n as int) * 0x20 + (d as int),
        // decode_and_log_shift_... `.0001010 ..0..... ........ ........`:
        // opc @ 29, N @ 21 = 0
        Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount } => 0x0A00_0000
            + logical_opc_field(opc) * 0x2000_0000 + enc_shifted_reg(
            sf,
            d,
            n,
            m,
            shift_type,
            shift_amount,
        ),
        // decode_lslv_... `.0011010 110..... 001000.. ........`: op2 @ 10
        Instr::ShiftVariable { sf, shift_type, d, n, m } => 0x1AC0_2000 + sf_bit(sf) * 0x8000_0000
            + (m as int) * 0x1_0000 + shift_field(shift_type) * 0x400 + (n as int) * 0x20 + (
        d as int),
        // decode_sbfm_... `.0010011 0....... ........ ........` (ubfm: opc =
        // 0b10 @ 29): N @ 22 (= sf), immr @ 16, imms @ 10
        Instr::Bitfield { sf, signed, d, n, immr, imms } => 0x1300_0000 + sf_bit(sf) * 0x8000_0000
            + b(!signed) * 0x4000_0000 + sf_bit(sf) * 0x40_0000 + (immr as int) * 0x1_0000 + (
        imms as int) * 0x400 + (n as int) * 0x20 + (d as int),
        // decode_movz_... `.1010010 1....... ........ ........` (movk: opc =
        // 0b11 @ 29): hw @ 21, imm16 @ 5
        Instr::MoveWide { sf, opcode, d, imm16, hw } => 0x5280_0000 + sf_bit(sf) * 0x8000_0000 + b(
            opcode is K,
        ) * 0x2000_0000 + (hw as int) * 0x20_0000 + (imm16 as int) * 0x20 + (d as int),
        // decode_csel_... `.0011010 100..... ....00.. ........`:
        // op @ 30, Rm @ 16, cond @ 12, o2 @ 10
        Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond } => 0x1A80_0000 + sf_bit(sf)
            * 0x8000_0000 + b(else_inv) * 0x4000_0000 + (m as int) * 0x1_0000 + (cond as int)
            * 0x1000 + b(else_inc) * 0x400 + (n as int) * 0x20 + (d as int),
        // decode_ldr_imm_gen_..._unsigned `1.111001 01...... ........ ........`
        // (str: opc = 0b00): size @ 30, opc @ 22, imm12 @ 10, Rn @ 5, Rt @ 0
        Instr::LoadStoreImm { sf, load, t, n, imm12 } => 0xB900_0000 + sf_bit(sf) * 0x4000_0000
            + b(load) * 0x40_0000 + (imm12 as int) * 0x400 + (n as int) * 0x20 + (t as int),
        // decode_ldr_reg_gen_... `1.111000 011..... ....10.. ........` (str:
        // opc = 0b00): Rm @ 16, option @ 13 = 0b011, S @ 12
        Instr::LoadStoreReg { sf, load, t, n, m, s } => 0xB820_6800 + sf_bit(sf) * 0x4000_0000 + b(
            load,
        ) * 0x40_0000 + (m as int) * 0x1_0000 + b(s) * 0x1000 + (n as int) * 0x20 + (t as int),
        // decode_ldr_imm_fpsimd_..._unsigned `..111101 .1...... ........ ........`
        // with size = 0b11, opc = 0b01 (str: 0b00)
        Instr::FpLoadStoreImm { load, t, n, imm12 } => 0xFD00_0000 + b(load) * 0x40_0000 + (
        imm12 as int) * 0x400 + (n as int) * 0x20 + (t as int),
        // decode_ldr_reg_fpsimd_... `..111100 .11..... ....10.. ........` with
        // size = 0b11, opc = 0b01 (str: 0b00), option = 0b011
        Instr::FpLoadStoreReg { load, t, n, m, s } => 0xFC20_6800 + b(load) * 0x40_0000 + (
        m as int) * 0x1_0000 + b(s) * 0x1000 + (n as int) * 0x20 + (t as int),
        // decode_b_uncond_... `000101.. ........ ........ ........`: imm26 @ 0
        Instr::B { imm26 } => 0x1400_0000 + (imm26 as int) % 0x400_0000,
        // decode_b_cond_... `01010100 ........ ........ ...0....`:
        // imm19 @ 5, cond @ 0
        Instr::BCond { cond, imm19 } => 0x5400_0000 + ((imm19 as int) % 0x8_0000) * 0x20 + (
        cond as int),
        // decode_cbz_... `.0110100 ........ ........ ........` (cbnz: op @ 24):
        // sf @ 31, imm19 @ 5, Rt @ 0
        Instr::CompareBranch { sf, iszero, t, imm19 } => 0x3400_0000 + sf_bit(sf) * 0x8000_0000
            + b(!iszero) * 0x100_0000 + ((imm19 as int) % 0x8_0000) * 0x20 + (t as int),
        // decode_ret_... `11010110 01011111 000000.. ...00000` with Rn = 30
        Instr::Ret => 0xD65F_03C0,
        // decode_fadd_float_... `00011110 ..1..... 001010.. ........` with
        // ftype = 0b01 @ 22 (fsub: op @ 12)
        Instr::FAddSub { sub_op, d, n, m } => 0x1E60_2800 + (m as int) * 0x1_0000 + b(sub_op)
            * 0x1000 + (n as int) * 0x20 + (d as int),
        // decode_fmul_float_... `00011110 ..1..... 000010.. ........`, ftype = 0b01
        Instr::FMul { d, n, m } => 0x1E60_0800 + (m as int) * 0x1_0000 + (n as int) * 0x20 + (
        d as int),
        // decode_fdiv_float_... `00011110 ..1..... 000110.. ........`, ftype = 0b01
        Instr::FDiv { d, n, m } => 0x1E60_1800 + (m as int) * 0x1_0000 + (n as int) * 0x20 + (
        d as int),
        // decode_fmov_float_... `00011110 ..100000 010000.. ........` and the
        // fabs, fneg, fsqrt ones: ftype = 0b01, opc @ 15
        Instr::FUnary { fpop, d, n } => 0x1E60_4000 + fp_unary_opc_field(fpop) * 0x8000 + (
        n as int) * 0x20 + (d as int),
        // decode_fcmp_float_... `00011110 ..1..... 001000.. ...0.000`,
        // ftype = 0b01, opc = 0b00
        Instr::FCmp { n, m } => 0x1E60_2000 + (m as int) * 0x1_0000 + (n as int) * 0x20,
        // decode_fmov_float_gen_... `.0011110 ..10.11. 000000.. ........`:
        // sf = 1, ftype = 0b01, rmode = 0b00, opcode = 0b110 / 0b111 @ 16
        Instr::FMovGen { to_fp, d, n } => 0x9E66_0000 + b(to_fp) * 0x1_0000 + (n as int) * 0x20 + (
        d as int),
        // decode_scvtf_float_int_... `.0011110 ..100010 000000.. ........`, ftype = 0b01
        Instr::Scvtf { sf, d, n } => 0x1E62_0000 + sf_bit(sf) * 0x8000_0000 + (n as int) * 0x20 + (
        d as int),
        // decode_fcvtzs_float_int_... `.0011110 ..111000 000000.. ........`, ftype = 0b01
        Instr::Fcvtzs { sf, d, n } => 0x1E78_0000 + sf_bit(sf) * 0x8000_0000 + (n as int) * 0x20
            + (d as int),
    }
}

/// The four bytes of a word in memory, least significant first.
pub open spec fn word_bytes(w: int) -> Seq<u8> {
    seq![(w % 0x100) as u8, ((w / 0x100) % 0x100) as u8, ((w / 0x1_0000) % 0x100) as u8, ((w / 0x100_0000) % 0x100) as u8]
}

/// `w` is the canonical encoding of `i`, and `i` is in the subset: the only
/// words the validator accepts for an instruction.
pub open spec fn is_canonical_encoding(w: u32, i: Instr) -> bool {
    valid_instr(i) && w as int == encode(i)
}

// ============================================================================
// Section: state
// ============================================================================
//
// The machine state and its accessors (src/v8_base.sail: `X_read`, `X_set`,
// `SP_read`, `SP_set`, `V_read`, `V_set`, `Mem_read`, `Mem_set`,
// `ConditionHolds`, `BranchTo`).

/// The state the subset reads and writes.
pub struct State {
    /// `_R(0)` to `_R(30)`, the general-purpose registers (register 31 is
    /// not one: it is the zero register or `SP`).
    pub r: Seq<u64>,
    /// `SP_EL0`, which `SP_read` and `SP_set` use at EL0.
    pub sp: u64,
    /// `_PC`.
    pub pc: u64,
    /// `PSTATE.N`.
    pub flag_n: bool,
    /// `PSTATE.Z`.
    pub flag_z: bool,
    /// `PSTATE.C`.
    pub flag_c: bool,
    /// `PSTATE.V`.
    pub flag_v: bool,
    /// `_Z[0]` to `_Z[31]`, bits 127 .. 0 (the V registers).
    pub vreg: Seq<u128>,
    /// Memory: a partial map from virtual address (`0 .. 2^64`) to byte; an
    /// address outside the domain is unmapped, and an access to it faults.
    pub mem: Map<int, u8>,
}

/// A well-formed state: 31 general registers, 32 vector registers, and only
/// addresses with a zero top byte mapped (see the header on TBI).
pub open spec fn wf(s: State) -> bool {
    s.r.len() == 31 && s.vreg.len() == 32 && (forall|a: int|
        s.mem.dom().contains(a) ==> 0 <= a < 0x100_0000_0000_0000)
}

// sail-arm src/v8_base.sail, X_read
/// `X_read(n, width)`: the low `width` bits of `_R(n)`, or zero for
/// `n = 31`.
pub open spec fn x_read(s: State, n: u8, width: nat) -> int {
    if n != 31 {
        trunc(width, s.r[n as int] as int)
    } else {
        0
    }
}

// sail-arm src/v8_base.sail, X_set
/// `X_set(n, width) = value`: `_R(n) = ZeroExtend(value, 64)`, nothing for
/// `n = 31`.
pub open spec fn x_set(s: State, n: u8, width: nat, value: int) -> State {
    if n != 31 {
        State { r: s.r.update(n as int, trunc(width, value) as u64), ..s }
    } else {
        s
    }
}

// sail-arm src/v8_base.sail, SP_read
/// `SP_read()`: `SP_EL0` (`PSTATE.SP = 0`).
pub open spec fn sp_read(s: State) -> int {
    s.sp as int
}

// sail-arm src/v8_base.sail, SP_set
/// `SP_set() = value`.
pub open spec fn sp_set(s: State, value: int) -> State {
    State { sp: trunc(64, value) as u64, ..s }
}

// sail-arm src/v8_base.sail, V_read
/// `V_read(n, width)`: `_Z[n][width - 1 .. 0]`.
pub open spec fn v_read(s: State, n: u8, width: nat) -> int {
    trunc(width, s.vreg[n as int] as int)
}

// sail-arm src/v8_base.sail, V_set
/// `V_set(n, width) = value`: `_Z[n][vlen - 1 .. 0] = ZeroExtend(value,
/// vlen)` with `vlen = 128` (see the header on SVE).
pub open spec fn v_set(s: State, n: u8, width: nat, value: int) -> State {
    State { vreg: s.vreg.update(n as int, trunc(width, value) as u128), ..s }
}

/// `(PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv`.
pub open spec fn set_nzcv(s: State, nzcv: int) -> State {
    State {
        flag_n: bit(nzcv, 3) == 1,
        flag_z: bit(nzcv, 2) == 1,
        flag_c: bit(nzcv, 1) == 1,
        flag_v: bit(nzcv, 0) == 1,
        ..s
    }
}

// sail-arm src/v8_base.sail, ConditionHolds
/// `ConditionHolds(cond)`.
pub open spec fn condition_holds(s: State, cond: u8) -> bool {
    let c = cond as int;
    // match cond[3 .. 1]
    let base = match cond / 2 {
        0u8 => s.flag_z,
        1u8 => s.flag_c,
        2u8 => s.flag_n,
        3u8 => s.flag_v,
        4u8 => s.flag_c && !s.flag_z,
        5u8 => s.flag_n == s.flag_v,
        6u8 => s.flag_n == s.flag_v && !s.flag_z,
        _ => true,
    };
    // if [cond[0]] == 0b1 & cond != 0b1111 then result = not_bool(result)
    if c % 2 == 1 && c != 15 {
        !base
    } else {
        base
    }
}

// sail-arm src/v8_base.sail, Mem_read, Mem_read__2
/// `Mem_read(address, size, accdesc)`: `size` bytes, little-endian, byte `i`
/// at `address + i` (modulo `2^64`); `None` (a data abort) if any of them is
/// not mapped.
pub open spec fn mem_read(m: Map<int, u8>, address: int, size: nat) -> Option<int>
    decreases size,
{
    if size == 0 {
        Some(0)
    } else if !m.dom().contains(trunc(64, address)) {
        None
    } else {
        match mem_read(m, address + 1, (size - 1) as nat) {
            None => None,
            Some(rest) => Some(m[trunc(64, address)] as int + 256 * rest),
        }
    }
}

// sail-arm src/v8_base.sail, Mem_set, Mem_set__2
/// `Mem_set(address, size, accdesc) = value`: `size` bytes of `value`,
/// little-endian; `None` (a data abort) if any of them is not mapped.
pub open spec fn mem_set(m: Map<int, u8>, address: int, size: nat, value: int) -> Option<Map<int, u8>>
    decreases size,
{
    if size == 0 {
        Some(m)
    } else if !m.dom().contains(trunc(64, address)) {
        None
    } else {
        match mem_set(m, address + 1, (size - 1) as nat, value / 256) {
            None => None,
            Some(m2) => Some(m2.insert(trunc(64, address), (value % 256) as u8)),
        }
    }
}

// ============================================================================
// Section: semantics
// ============================================================================
//
// What one instruction does to the [`State`]. Each `execute_*` function is
// transcribed as a function from the state to the state, or to
// `Option<State>` when it can fault.

// sail-arm src/v8_base.sail, AddWithCarry
/// `AddWithCarry(x, y, carry_in)` on `bits(n)`: the result and `nzcv`.
pub open spec fn add_with_carry(n: nat, x: int, y: int, carry_in: int) -> (int, int) {
    let unsigned_sum = trunc(n, x) + trunc(n, y) + carry_in;
    let signed_sum = sint(n, x) + sint(n, y) + carry_in;
    let result = trunc(n, unsigned_sum);
    let flag_n = bit(result, (n - 1) as nat);
    let flag_z = if result == 0 {
        1int
    } else {
        0
    };
    let flag_c = if result == unsigned_sum {
        0int
    } else {
        1
    };
    let flag_v = if sint(n, result) == signed_sum {
        0int
    } else {
        1
    };
    (result, flag_n * 8 + flag_z * 4 + flag_c * 2 + flag_v)
}

// sail-arm src/v8_base.sail, ShiftReg
/// `ShiftReg(reg, shiftype, amount, N)`.
pub open spec fn shift_reg(s: State, reg: u8, shiftype: ShiftType, amount: nat, n: nat) -> int {
    let result = x_read(s, reg, n);
    match shiftype {
        ShiftType::Lsl => lsl(n, result, amount),
        ShiftType::Lsr => lsr(n, result, amount),
        ShiftType::Asr => asr(n, result, amount),
        ShiftType::Ror => ror(n, result, amount),
    }
}

// sail-arm src/v8_base.sail, ExtendReg
/// `ExtendReg(reg, ExtendType_UXTX, shift, 64)`: `is_unsigned`, `len =
/// Min(64, 64 - shift)`, `ZeroExtend(val_name[len - 1 .. 0] @ Zeros(shift),
/// 64)`.
pub open spec fn extend_reg_uxtx(s: State, reg: u8, shift: nat) -> int {
    let val_name = x_read(s, reg, 64);
    let len = (64 - shift) as nat;
    trunc(len, val_name) * p2(shift)
}

// sail-arm src/v8_base.sail, DecodeBitMasks
/// `DecodeBitMasks(immN, imms, immr, immediate = false, M)`: `(wmask,
/// tmask)`. For the encodings the subset admits (`immN = sf`; with
/// `sf = 0`, `imms < 32`), `len = HighestSetBit(immN @ not_vec(imms))` is 6
/// or 5, so `esize = 1 << len` is `M` and `Replicate(_, DIV(M, esize))` is
/// the identity; `immediate` is false, so it never throws.
pub open spec fn decode_bit_masks(imm_n: int, imms: int, immr: int, m: nat) -> (int, int) {
    // len = HighestSetBit(immN @ not_vec(imms))
    let len = highest_set_bit(7, imm_n * 64 + not_vec(6, imms));
    let levels = ones(len as nat);
    let s = and_vec(imms, levels);
    let r = and_vec(immr, levels);
    let diff = s - r;
    let esize = p2(len as nat);
    let d = trunc(len as nat, diff);
    // welem = ZeroExtend(Ones(s + 1), esize); telem = ZeroExtend(Ones(d + 1), esize)
    let welem = ones((s + 1) as nat);
    let telem = ones((d + 1) as nat);
    // wmask = Replicate(ROR(welem, r), DIV(M, esize)); tmask = Replicate(telem, ...)
    (ror(esize as nat, welem, r as nat), telem)
}

/// `RoundTowardsZero(Real(a) / Real(b))` for `b != 0`: the quotient rounded
/// toward zero (`src/prelude.sail`, `RoundTowardsZero`: `RoundUp` of a
/// negative real, `RoundDown` otherwise).
pub open spec fn round_towards_zero_div(a: int, b: int) -> int {
    let q = rat_div(rat(a), rat(b));
    if q.n < 0 {
        // RoundUp
        -rat_floor(rat_neg(q))
    } else {
        rat_floor(q)
    }
}

/// The value of a `ShiftType` field written as a `nat` amount.
pub open spec fn nat_of(x: u8) -> nat {
    x as nat
}

/// The register, flag and memory effects of an instruction that is not a
/// branch; `None` is a fault (a data abort). Branches have none here: their
/// effect is the PC, in [`step`].
pub open spec fn execute(s: State, i: Instr) -> Option<State> {
    match i {
        // execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
        Instr::AddSubShiftedReg { sf, sub_op, setflags, d, n, m, shift_type, shift_amount } => {
            let datasize = datasize(sf);
            let operand1 = x_read(s, n, datasize);
            let operand2_0 = shift_reg(s, m, shift_type, nat_of(shift_amount), datasize);
            // if sub_op then { operand2 = not_vec(operand2); carry_in = 0b1 } else carry_in = 0b0
            let (operand2, carry_in) = if sub_op {
                (not_vec(datasize, operand2_0), 1int)
            } else {
                (operand2_0, 0int)
            };
            let (result, nzcv) = add_with_carry(datasize, operand1, operand2, carry_in);
            let s1 = if setflags {
                set_nzcv(s, nzcv)
            } else {
                s
            };
            Some(x_set(s1, d, datasize, result))
        },
        // execute_aarch64_instrs_integer_arithmetic_add_sub_immediate, with
        // imm = ZeroExtend(imm12, datasize) or ZeroExtend(imm12 @ Zeros(12),
        // datasize) from the decode function.
        Instr::AddSubImm { sf, sub_op, setflags, d, n, imm12, sh } => {
            let datasize = datasize(sf);
            let imm = if sh {
                (imm12 as int) * 0x1000
            } else {
                imm12 as int
            };
            // operand1 = if n == 31 then SP_read()[datasize - 1 .. 0] else X_read(n, datasize)
            let operand1 = if n == 31 {
                trunc(datasize, sp_read(s))
            } else {
                x_read(s, n, datasize)
            };
            let (operand2, carry_in) = if sub_op {
                (not_vec(datasize, imm), 1int)
            } else {
                (imm, 0int)
            };
            let (result, nzcv) = add_with_carry(datasize, operand1, operand2, carry_in);
            let s1 = if setflags {
                set_nzcv(s, nzcv)
            } else {
                s
            };
            // if d == 31 & not_bool(setflags) then SP_set() = ZeroExtend(result, 64)
            if d == 31 && !setflags {
                Some(sp_set(s1, result))
            } else {
                Some(x_set(s1, d, datasize, result))
            }
        },
        // execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub
        // (destsize = datasize)
        Instr::MulAddSub { sf, sub_op, d, n, m, a } => {
            let datasize = datasize(sf);
            let operand1 = x_read(s, n, datasize);
            let operand2 = x_read(s, m, datasize);
            let operand3 = x_read(s, a, datasize);
            let result = if sub_op {
                operand3 - operand1 * operand2
            } else {
                operand3 + operand1 * operand2
            };
            // X_set(d, destsize) = result[destsize - 1 .. 0]
            Some(x_set(s, d, datasize, trunc(datasize, result)))
        },
        // execute_aarch64_instrs_integer_arithmetic_div
        Instr::Div { sf, is_unsigned, d, n, m } => {
            let datasize = datasize(sf);
            let operand1 = x_read(s, n, datasize);
            let operand2 = x_read(s, m, datasize);
            let result = if operand2 == 0 {
                0
            } else {
                // asl_Int(operand, is_unsigned)
                let a = if is_unsigned {
                    operand1
                } else {
                    sint(datasize, operand1)
                };
                let b = if is_unsigned {
                    operand2
                } else {
                    sint(datasize, operand2)
                };
                round_towards_zero_div(a, b)
            };
            Some(x_set(s, d, datasize, trunc(datasize, result)))
        },
        // execute_aarch64_instrs_integer_logical_shiftedreg (invert false)
        Instr::LogicalShiftedReg { sf, opc, d, n, m, shift_type, shift_amount } => {
            let datasize = datasize(sf);
            let operand1 = x_read(s, n, datasize);
            let operand2 = shift_reg(s, m, shift_type, nat_of(shift_amount), datasize);
            let result = match opc {
                LogicalOpc::And => and_vec(operand1, operand2),
                LogicalOpc::Ands => and_vec(operand1, operand2),
                LogicalOpc::Orr => or_vec(operand1, operand2),
                LogicalOpc::Eor => eor_vec(operand1, operand2),
            };
            // if setflags: nzcv = [result[datasize - 1]] @ IsZeroBit(result) @ 0b00
            let s1 = if opc is Ands {
                set_nzcv(
                    s,
                    bit(result, (datasize - 1) as nat) * 8 + (if result == 0 {
                        1int
                    } else {
                        0
                    }) * 4,
                )
            } else {
                s
            };
            Some(x_set(s1, d, datasize, result))
        },
        // execute_aarch64_instrs_integer_shift_variable
        Instr::ShiftVariable { sf, shift_type, d, n, m } => {
            let datasize = datasize(sf);
            let operand2 = x_read(s, m, datasize);
            // ShiftReg(n, shift_type, MOD(UInt(operand2), datasize), datasize)
            let result = shift_reg(s, n, shift_type, (operand2 % (datasize as int)) as nat, datasize);
            Some(x_set(s, d, datasize, result))
        },
        // execute_aarch64_instrs_integer_bitfield, with decode_sbfm_... /
        // decode_ubfm_...: SBFM inzero = extend = true; UBFM inzero = true,
        // extend = false.
        Instr::Bitfield { sf, signed, d, n, immr, imms } => {
            let datasize = datasize(sf);
            let r = immr as int;
            let s_ = imms as int;
            let (wmask, tmask) = decode_bit_masks(sf_bit(sf), imms as int, immr as int, datasize);
            // dst = if inzero then Zeros(datasize) else X_read(d, datasize)
            let dst = 0int;
            let src = x_read(s, n, datasize);
            // bot = dst & not_vec(wmask) | ROR(src, r) & wmask
            let bot = or_vec(and_vec(dst, not_vec(datasize, wmask)), and_vec(ror(datasize, src, r as nat), wmask));
            // top = if extend then Replicate([src[s]], datasize) else dst
            let top = if signed {
                replicate_bit(datasize, bit(src, s_ as nat))
            } else {
                dst
            };
            // X_set(d, datasize) = top & not_vec(tmask) | bot & tmask
            Some(x_set(s, d, datasize, or_vec(and_vec(top, not_vec(datasize, tmask)), and_vec(bot, tmask))))
        },
        // execute_aarch64_instrs_integer_ins_ext_insert_movewide
        Instr::MoveWide { sf, opcode, d, imm16, hw } => {
            let datasize = datasize(sf);
            let pos = (hw as nat) * 16;
            // result = if opcode == MoveWideOp_K then X_read(d, datasize) else Zeros(datasize)
            let result0 = if opcode is K {
                x_read(s, d, datasize)
            } else {
                0
            };
            // result[pos + 15 .. pos] = imm
            let result = result0 - (result0 / p2(pos)) % 0x1_0000 * p2(pos) + (imm16 as int) * p2(
                pos,
            );
            // (opcode == MoveWideOp_N: not in the subset)
            Some(x_set(s, d, datasize, result))
        },
        // execute_aarch64_instrs_integer_conditional_select
        Instr::CondSelect { sf, else_inv, else_inc, d, n, m, cond } => {
            let datasize = datasize(sf);
            let result = if condition_holds(s, cond) {
                x_read(s, n, datasize)
            } else {
                let r0 = x_read(s, m, datasize);
                let r1 = if else_inv {
                    not_vec(datasize, r0)
                } else {
                    r0
                };
                // result = result + 1 (bits(datasize) arithmetic)
                if else_inc {
                    trunc(datasize, r1 + 1)
                } else {
                    r1
                }
            };
            Some(x_set(s, d, datasize, result))
        },
        // execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx,
        // from decode_ldr_imm_gen_..._unsigned / decode_str_imm_gen_..._unsigned:
        // scale = UInt(size), offset = LSL(ZeroExtend(imm12, 64), scale),
        // datasize = regsize, postindex = wback = false, n != 31.
        Instr::LoadStoreImm { sf, load, t, n, imm12 } => {
            let datasize = datasize(sf);
            let offset = (imm12 as int) * (datasize as int / 8);
            let address = trunc(64, x_read(s, n, 64) + offset);
            load_store_gpr(s, load, t, datasize, address)
        },
        // execute_aarch64_instrs_memory_single_general_register, from
        // decode_ldr_reg_gen_... / decode_str_reg_gen_...: extend_type =
        // DecodeRegExtend(0b011) = UXTX, shift = if S then scale else 0.
        Instr::LoadStoreReg { sf, load, t, n, m, s: s_bit } => {
            let datasize = datasize(sf);
            let scale: nat = if sf is W64 {
                3
            } else {
                2
            };
            let shift: nat = if s_bit {
                scale
            } else {
                0
            };
            let offset = extend_reg_uxtx(s, m, shift);
            let address = trunc(64, x_read(s, n, 64) + offset);
            load_store_gpr(s, load, t, datasize, address)
        },
        // execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx,
        // from decode_ldr_imm_fpsimd_..._unsigned: scale = UInt(opc[1] @ size) = 3,
        // datasize = 64.
        Instr::FpLoadStoreImm { load, t, n, imm12 } => {
            let offset = (imm12 as int) * 8;
            let address = trunc(64, x_read(s, n, 64) + offset);
            load_store_fp(s, load, t, address)
        },
        // execute_aarch64_instrs_memory_single_simdfp_register, from
        // decode_ldr_reg_fpsimd_...: shift = if S then 3 else 0.
        Instr::FpLoadStoreReg { load, t, n, m, s: s_bit } => {
            let shift: nat = if s_bit {
                3
            } else {
                0
            };
            let offset = extend_reg_uxtx(s, m, shift);
            let address = trunc(64, x_read(s, n, 64) + offset);
            load_store_fp(s, load, t, address)
        },
        // execute_aarch64_instrs_float_arithmetic_add_sub (esize = 64; merge
        // is false, so result starts as Zeros(128))
        Instr::FAddSub { sub_op, d, n, m } => {
            let operand1 = v_read(s, n, 64) as u64;
            let operand2 = v_read(s, m, 64) as u64;
            let r = if sub_op {
                fp_sub(operand1, operand2)
            } else {
                fp_add(operand1, operand2)
            };
            Some(v_set(s, d, 128, r as int))
        },
        // execute_aarch64_instrs_float_arithmetic_mul_product (negated false)
        Instr::FMul { d, n, m } => {
            let operand1 = v_read(s, n, 64) as u64;
            let operand2 = v_read(s, m, 64) as u64;
            Some(v_set(s, d, 128, fp_mul(operand1, operand2) as int))
        },
        // execute_aarch64_instrs_float_arithmetic_div
        Instr::FDiv { d, n, m } => {
            let operand1 = v_read(s, n, 64) as u64;
            let operand2 = v_read(s, m, 64) as u64;
            Some(v_set(s, d, 128, fp_div(operand1, operand2) as int))
        },
        // execute_aarch64_instrs_float_arithmetic_unary (merge is false:
        // result starts as 0[127 .. 0])
        Instr::FUnary { fpop, d, n } => {
            let operand = v_read(s, n, 64) as u64;
            let r = match fpop {
                FPUnaryOp::Mov => operand,
                FPUnaryOp::Abs => fp_abs(operand),
                FPUnaryOp::Neg => fp_neg(operand),
                FPUnaryOp::Sqrt => fp_sqrt(operand),
            };
            Some(v_set(s, d, 128, r as int))
        },
        // execute_aarch64_instrs_float_compare_uncond (cmp_with_zero false)
        Instr::FCmp { n, m } => {
            let operand1 = v_read(s, n, 64) as u64;
            let operand2 = v_read(s, m, 64) as u64;
            Some(set_nzcv(s, fp_compare(operand1, operand2)))
        },
        // execute_aarch64_instrs_float_convert_int, FPConvOp_MOV_ItoF /
        // FPConvOp_MOV_FtoI, part = 0, fsize = fltsize = intsize = 64
        Instr::FMovGen { to_fp, d, n } => if to_fp {
            // intval = X_read(n, intsize); Vpart_set(d, 0, fsize) = intval[63 .. 0]
            Some(v_set(s, d, 64, x_read(s, n, 64)))
        } else {
            // fltval = Vpart_read(n, 0, fsize); X_set(d, intsize) = ZeroExtend(fltval, intsize)
            Some(x_set(s, d, 64, v_read(s, n, 64)))
        },
        // execute_aarch64_instrs_float_convert_int, FPConvOp_CVT_ItoF, merge
        // false: fltval = Zeros(64); rounding = FPRoundingMode(FPCR) (decode)
        Instr::Scvtf { sf, d, n } => {
            let intsize = datasize(sf);
            let intval = x_read(s, n, intsize);
            let fltval = fixed_to_fp(intval, intsize, 0, false, fp_rounding_mode());
            Some(v_set(s, d, 64, fltval as int))
        },
        // execute_aarch64_instrs_float_convert_int, FPConvOp_CVT_FtoI,
        // rounding = FPDecodeRounding(0b11) = FPRounding_ZERO, is_unsigned false
        Instr::Fcvtzs { sf, d, n } => {
            let intsize = datasize(sf);
            let fltval = v_read(s, n, 64) as u64;
            let intval = fp_to_fixed(fltval, 0, false, FPRounding::Zero, intsize);
            Some(x_set(s, d, intsize, intval))
        },
        // Branches have no effect but on the PC (see step).
        Instr::B { imm26 } => Some(s),
        Instr::BCond { cond, imm19 } => Some(s),
        Instr::CompareBranch { sf, iszero, t, imm19 } => Some(s),
        Instr::Ret => Some(s),
    }
}

/// The `match memop` of the general-register load/store execute functions
/// (`regsize = datasize`, `is_signed` false, `rt_unknown` false): a load is
/// `X_set(t, regsize) = ZeroExtend(Mem_read(address, datasize / 8))`, a
/// store `Mem_set(address, datasize / 8) = X_read(t, datasize)`.
pub open spec fn load_store_gpr(s: State, load: bool, t: u8, datasize: nat, address: int) -> Option<State> {
    if load {
        match mem_read(s.mem, address, datasize / 8) {
            Some(data) => Some(x_set(s, t, datasize, data)),
            None => None,
        }
    } else {
        let data = x_read(s, t, datasize);
        match mem_set(s.mem, address, datasize / 8, data) {
            Some(mem) => Some(State { mem, ..s }),
            None => None,
        }
    }
}

/// The `match memop` of the SIMD&FP load/store execute functions with
/// `datasize = 64`: a load is `V_set(t, 64) = Mem_read(address, 8)`, a store
/// `Mem_set(address, 8) = V_read(t, 64)`.
pub open spec fn load_store_fp(s: State, load: bool, t: u8, address: int) -> Option<State> {
    if load {
        match mem_read(s.mem, address, 8) {
            Some(data) => Some(v_set(s, t, 64, data)),
            None => None,
        }
    } else {
        let data = v_read(s, t, 64);
        match mem_set(s.mem, address, 8, data) {
            Some(mem) => Some(State { mem, ..s }),
            None => None,
        }
    }
}

// sail-arm src/v8_base.sail, BranchTo (with AArch64_BranchAddr, AddrTop = 63)
/// `BranchTo(target, branch_type, branch_conditional)`: `_PC = target`.
pub open spec fn branch_to(s: State, target: int) -> State {
    State { pc: trunc(64, target) as u64, ..s }
}

/// One step of the machine: executes `i`, which is at `s.pc`, and returns
/// the next state, or `None` for a fault.
///
/// `__InstructionExecute` (src/fetch.sail) clears `__BranchTaken`, executes,
/// and then, if no branch was taken, sets `_PC = _PC + 4` (modulo `2^64`).
/// A branch sets `_PC` through `BranchTo` and `__BranchTaken`.
///
/// - `B` (`execute_..._branch_unconditional_immediate`, `BranchType_DIR`):
///   `BranchTo(PC_read() + offset)`.
/// - `B.cond` (`execute_..._branch_conditional_cond`) and `CBZ`/`CBNZ`
///   (`execute_..._branch_conditional_compare`): `BranchTo` when the
///   condition holds, else `BranchNotTaken`, which changes nothing.
/// - `RET` (`execute_..._branch_unconditional_register`): `target =
///   X_read(30, 64)`, then `BranchTo(target)` (no `pac`, and GCS is not
///   enabled at EL0, so the target is not checked).
///
/// The instruction's word is not read here: `i` is the decoded instruction.
/// That the word at the PC is its canonical encoding is [`fetch_ok`].
pub open spec fn step(s: State, i: Instr) -> Option<State> {
    let pc = s.pc as int;
    match i {
        Instr::B { imm26 } => Some(branch_to(s, pc + (imm26 as int) * 4)),
        Instr::BCond { cond, imm19 } => if condition_holds(s, cond) {
            Some(branch_to(s, pc + (imm19 as int) * 4))
        } else {
            Some(branch_to(s, pc + 4))
        },
        Instr::CompareBranch { sf, iszero, t, imm19 } => {
            // operand1 = X_read(t, datasize); if IsZero(operand1) == iszero then BranchTo
            let operand1 = x_read(s, t, datasize(sf));
            if (operand1 == 0) == iszero {
                Some(branch_to(s, pc + (imm19 as int) * 4))
            } else {
                Some(branch_to(s, pc + 4))
            }
        },
        Instr::Ret => Some(branch_to(s, x_read(s, 30, 64))),
        _ => match execute(s, i) {
            Some(s1) => Some(branch_to(s1, pc + 4)),
            None => None,
        },
    }
}

/// The word at the PC is the canonical encoding of `i`, and the fetch does
/// not fault: the PC is a multiple of 4 (`AArch64_CheckPCAlignment`), and
/// the four bytes at it are mapped and hold [`word_bytes`] of the encoding
/// (`__FetchInstr`). (Which memory is executable is the validator's concern;
/// this model has no execute permission.)
pub open spec fn fetch_ok(s: State, i: Instr) -> bool {
    valid_instr(i) && (s.pc as int) % 4 == 0 && forall|k: int|
        0 <= k < 4 ==> #[trigger] s.mem.dom().contains(s.pc as int + k) && s.mem[s.pc as int + k]
            == word_bytes(encode(i))[k]
}

} // verus!

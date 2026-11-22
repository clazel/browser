//! The **primary** specification of the x86-64 subset the JIT emits (jit.md
//! item J.3): the machine state, the semantics of every instruction, and the
//! canonical encoding. Nothing here runs; it defines what "correct" means.
//!
//! # Source
//!
//! Transcribed from the ACL2 `x86isa` model, acl2/acl2 commit
//! `33b05575eaf9f54734bf36e6f4bd8ee094ff2ee1`, `books/projects/x86isa`,
//! vendored under `tests/data/acl2-x86isa/` (`SOURCE.md`). Each function
//! cites the book and the ACL2 function it transcribes, as
//! `file.lisp: function-name` (CLAUDE.md rule 5, adapted: ACL2 has no step
//! numbers; the structure of ACL2's functions is kept instead).
//!
//! **Two kinds of source lie outside `tests/data/`.** The J.2 vendoring did
//! not copy them, so a reader must fetch them from the commit above:
//!
//! - `books/projects/x86isa/machine/instructions/fp/logical.lisp`, which holds
//!   the `UCOMISD` instruction (`x86-comis?/ucomis?-Op/En-RM`). The vendored
//!   `fp/cmp-spec.lisp` has only the comparison function it calls.
//! - `books/rtl/rel11/lib/{defs,reps,round,excps}.lisp`, Russinoff's RTL
//!   library, in which ACL2's `addsd`, `subsd`, `mulsd`, `divsd` and `sqrtsd`
//!   are defined (`rtl::sse-binary-spec`, `rtl::sse-sqrt-spec`, with `rnd`,
//!   `drnd`, `qsqrt`, `nencode`, `dencode`). x86isa's own books
//!   (`fp/add-mul-spec.lisp`, `fp/sqrt-spec.lisp`, vendored) only call them.
//!
//! The Sail translation (`tests/data/sail-x86-from-acl2/`) was used only to
//! check the reading of ACL2 (it has no SSE2). It is a mechanical translation
//! of ACL2, not an independent source, and nothing here is transcribed from
//! it. The Intel SDM was **not** read: the independent transcription (jit.md,
//! the note under J.3) is made from it by another session.
//!
//! # What is covered
//!
//! - 64- and 32-bit operand size: `mov` (register, load, store, `imm32`,
//!   sign-extended `imm32`, `imm64`); `add or and sub xor cmp` (register,
//!   load, `imm32`); `test` (register, `imm32`); `neg`, `not`; `shl shr sar`
//!   (by `imm8` and by `cl`); `imul` (two- and three-operand); `jcc rel32`,
//!   `jmp rel32`, `ret`; `cmovcc`, `setcc`.
//! - SSE2 scalar double: `addsd subsd mulsd divsd sqrtsd` (register or
//!   memory), `ucomisd`, `cvtsi2sd`, `cvttsd2si`, `cvtsd2si`, `movq` between a
//!   general register and an XMM register, `movsd` load and store.
//!
//! # What is left out
//!
//! - **Memory destinations of the arithmetic, logic, shift, `neg`, `not` and
//!   `setcc` instructions** (read-modify-write), `inc`, `dec`, `adc`, `sbb`,
//!   `lea`, `movzx`, `movsx`, `movsxd`, `push`, `pop`, `call`, `mul`, `idiv`
//!   and `div`, rotates, `bt*`, `xchg`: jit.md J.3 does not list them. A
//!   JIT that needs one asks for it by an addition to this file.
//! - `movsd` and `movq` between two XMM registers, `movaps`, `cvtsd2ss`,
//!   `cvtss2sd`, `xorpd`/`andpd` (for negation and `abs`), `roundsd`,
//!   `minsd`, `maxsd`: J.3's list has `movq` between *general and XMM*
//!   registers only. An XMM-to-XMM copy and `xorpd` are the likely first
//!   additions.
//! - Anything with a segment override, a RIP-relative or absolute address, an
//!   address-size override, a `lock` or `rep` prefix, `VEX` or `EVEX`.
//! - Any state the subset does not read or write: segment registers, control
//!   registers, MSRs, the x87 and MMX state, MXCSR (see below), `AC`
//!   alignment checking, paging, the TLB, the instruction cache.
//!
//! # Modelling choices
//!
//! Each is a difference in form that does not change the meaning, or a
//! restriction of the machine the subset runs on, stated so the validator's
//! theorem (J.6) can assume it.
//!
//! - **Process mode.** 64-bit mode only. ACL2's `proc-mode` parameter is
//!   fixed to `#.*64-bit-mode*`: ACL2's `case proc-mode` branches for the
//!   other modes are dropped, and the 64-bit branch is kept.
//! - **One step of one instruction is a pure function** [`step`]
//!   from a [`State`] and an [`Instr`] to
//!   `Option<State>`. ACL2 fetches and decodes the bytes at RIP in the same
//!   function; here decoding is the relation of [`encoding`], and
//!   [`fetch_ok`] says the bytes at RIP are the encoding. The
//!   length of the instruction ACL2 learns by decoding (`temp-rip`,
//!   `increment-RIP-by`) is [`instr_len`].
//! - **A fault is `None`.** ACL2 records a fault (`!!fault-fresh`: `#GP`,
//!   `#SS`, `#PF`, `#AC`) or a model stop (`!!ms-fresh`: an unsupported or
//!   non-canonical case) in the state and promises nothing about the state
//!   after it. Here every one of them is `None`, with no state. The cases
//!   that can arise in the subset: an access to an unmapped byte, a
//!   non-canonical new RIP, a non-canonical new RSP (`ret`).
//! - **Memory is a partial map** from signed linear address to byte
//!   ([`State::mem`]); the domain is the set of addresses the
//!   process may access, and must hold only canonical addresses
//!   ([`wf`]). ACL2's linear memory is built on paging
//!   (`machine/linear-memory.lisp`, `machine/physical-memory.lisp`:
//!   `rml-size`/`wml-size` translate, check permissions and canonicity, and
//!   read bytes); the subset's validator (J.6) reasons about which linear
//!   addresses are touched, so paging, `CR0.WP`, `SMEP`, page permissions,
//!   and the user/supervisor bit are all collapsed into "mapped or not". A
//!   read of `n` bytes at `a` needs `a, a+1 .. a+n-1` (as integers, no
//!   wrap-around) mapped, little-endian.
//! - **Alignment checking is off** (`alignment-checking-enabled-p` is
//!   false: `CR0.AM`, `RFLAGS.AC` and CPL are not modelled). The instructions
//!   of the subset need no alignment (`movsd`, `movq`, `addsd` with a memory
//!   operand are the unaligned forms).
//! - **Segmentation is flat.** Every segment base is 0 and every limit is
//!   ignored in 64-bit mode (no `FS`/`GS` override is in the subset), so a
//!   linear address is the effective address and `select-segment-register` is
//!   dropped.
//! - **Undefined flags** use ACL2's own mechanism: the state has a seed
//!   ([`State::undef`]), and each undefined flag takes
//!   `(n01 (create-undef seed))` and increments the seed
//!   ([`write_user_rflags`]). `create-undef` is ACL2's unspecified
//!   function; here it is a parameter `create_undef: spec_fn(nat) -> nat`
//!   of [`step`], so every statement about `step` holds for every
//!   such function. The flags an instruction leaves undefined are listed by
//!   its `*_spec` function exactly as ACL2 lists them.
//! - **MXCSR is the constant `0x1F80`** (round to nearest even, all
//!   exceptions masked, DAZ = FTZ = 0). The subset cannot change it. See
//!   [`fp`]. The sticky exception flags are not modelled.
//! - **Instruction-length checks** (`check-instruction-length`, at most 15
//!   bytes: a `#GP`) are dropped: no instruction of the subset is longer
//!   than 10 bytes.
//! - **Operand sizes** are the two of the subset ([`Size`]). ACL2
//!   generates one function per size by macro (`gpr-add-spec-1`, `-2`, `-4`,
//!   `-8`, the same for every flag function); here one function takes the
//!   width `n` in bits (32 or 64) and applies the same formula, so
//!   `gpr-add-spec-4` is `gpr_add_spec(32, ..)` and `gpr-add-spec-8` is
//!   `gpr_add_spec(64, ..)`. The 8- and 16-bit instances are not transcribed.
//! - **Registers are unsigned.** ACL2 stores the GPRs signed (`rgfi`) and
//!   converts at each use (`n64-to-i64`); here they are unsigned and the
//!   conversions are [`logext`]. `rr08`/`wr08` are used only for
//!   `setcc` and `cl`, and the byte-register quirk of `wr08` (registers 4 to
//!   7 without a `REX` byte name `ah`..`bh`) does not arise, because the
//!   canonical encoding has a `REX` byte whenever it matters
//!   ([`encoding`], rule 2).
//! - **`rflags`** is the 32-bit `rflagsBits` with the same bit positions
//!   (`utils/structures.lisp: rflagsBits`); only the six user flags are
//!   ever written.
//! - **XMM registers** are 128 bits ([`State::xmm`]); ACL2 keeps the
//!   whole `zmm` (512 bits) and has the legacy-SSE write preserve the upper
//!   bits. None of the subset's instructions touches or reads bits 128 and
//!   above, so they are not modelled.
//! - **The canonical encoding is part of this file**, as spec functions
//!   ([`encoding`]), because the semantics needs `instr_len`, and because the
//!   validator accepts only these bytes. It is a *choice* (one of the byte
//!   strings x86-64 allows for each instruction), not a transcription: ACL2
//!   decodes all of them. Its rules are in the header of [`encoding`].
//! - **`ucomisd`'s flags** are set directly with `!flgi` in ACL2
//!   (`x86-comis?/ucomis?-Op/En-RM`), not through `write-user-rflags`, and
//!   leave nothing undefined.
//! - **A step does not model the instruction fetch faulting.** [`step`]
//!   is given the instruction; that its bytes are mapped and are the canonical
//!   encoding is [`fetch_ok`].
//!
//! # Things in the ACL2 model worth a reviewer's eye
//!
//! 1. ACL2's `addsd`, `subsd`, `mulsd`, `divsd` and `sqrtsd` delegate the
//!    arithmetic to Russinoff's RTL library, which is not part of x86isa and
//!    is not in `tests/data/`. The transcription of [`fp`] is of those RTL
//!    functions, not of x86isa's books. Hardware differential tests (J.3's
//!    last bullet) are the independent check of this part.
//! 2. `UCOMISD` is in `fp/logical.lisp`, not vendored (see above).
//! 3. ACL2's `x86-ret` checks that `rsp + 8` is canonical, and
//!    `x86-near-jmp-Op/En-D` checks the address of the next instruction as
//!    well as the target. Whether hardware does either is for the hardware
//!    differential tests to say; both make the model fault in more cases than
//!    a laxer reading would, and are kept as ACL2 has them.
//! 4. ACL2's `x86-cmovcc` reads the source operand whether or not the
//!    condition holds, and with a 32-bit operand rewrites the destination
//!    zero-extended when it does not. Kept as is; the differential tests
//!    check it.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: bits
// ============================================================================
//
// Integer and bit helpers the transcription uses, named after the ACL2
// functions they stand for (`loghead`, `logbitp`, `logext`, `n64-to-i64`,
// `logcount`). All of them work on mathematical integers (`int`); the
// fixed-width ACL2 types (`(unsigned-byte n)`, `(signed-byte n)`) are
// predicates over them.
//
// ACL2 sources: the ACL2 system books `ihs/logops-definitions` (`loghead`,
// `logext`, `logbitp`, `logcount`) and `centaur/bitops`, which are not
// vendored; the definitions here are the standard ones. The model's own
// `n-size`/`n32`/`n64`/`n64-to-i64` are in
// `tests/data/acl2-x86isa/utils/utilities.lisp` and `structures.lisp`.


/// `2^n` as an integer (ACL2 `(expt 2 n)`).
pub open spec fn p2(n: nat) -> int {
    vstd::arithmetic::power2::pow2(n) as int
}

/// `(loghead n x)`, also `(n-size n x)`, `(n32 x)`, `(n64 x)`: the low `n`
/// bits of `x`, as a natural number. Negative `x` wraps (two's complement).
pub open spec fn loghead(n: nat, x: int) -> int {
    x % p2(n)
}

/// `(logbitp k x)` as a bit: bit `k` of `x`.
pub open spec fn bit(x: int, k: nat) -> int {
    (x / p2(k)) % 2
}

/// `(unsigned-byte-p n x)`.
pub open spec fn unsigned_byte_p(n: nat, x: int) -> bool {
    0 <= x && x < p2(n)
}

/// `(signed-byte-p n x)`.
pub open spec fn signed_byte_p(n: nat, x: int) -> bool {
    -p2((n - 1) as nat) <= x && x < p2((n - 1) as nat)
}

/// `(logext n x)`, `(n64-to-i64 x)` and the other `nXX-to-iXX`: the low `n`
/// bits of `x` read as a two's complement integer.
pub open spec fn logext(n: nat, x: int) -> int {
    let l = loghead(n, x);
    if l >= p2((n - 1) as nat) {
        l - p2(n)
    } else {
        l
    }
}

/// `(bool->bit b)`.
pub open spec fn bool_to_bit(b: bool) -> int {
    if b {
        1
    } else {
        0
    }
}

/// `(logcount x)` for a natural `x`, written as ACL2's `bitcount8`
/// (rflags-spec.lisp) does: the number of one bits.
pub open spec fn logcount(x: nat) -> nat
    decreases x,
{
    if x == 0 {
        0
    } else {
        ((x % 2) + logcount((x / 2) as nat)) as nat
    }
}

/// Replaces bit `k` of the 32-bit word `w` with `v` (0 or 1). The `change-rflagsBits`
/// and `!rflagsBits->xx` field updates are this on the flag's bit position.
pub open spec fn set_bit32(w: u32, k: nat, v: int) -> u32 {
    let cleared = (w as int) - bit(w as int, k) * p2(k);
    (cleared + (v % 2) * p2(k)) as u32
}


// ============================================================================
// Section: fp
// ============================================================================
//
// The IEEE-754 binary64 operations of the subset, as bit-level spec
// functions over exact rationals.
//
// Verus has no usable floating-point semantics, and the ACL2 model does not
// use ACL2's own either: it keeps the arithmetic as integers and rationals.
// This file is therefore the model's own, in the model's structure.
//
// # Sources
//
// - **Vendored** (`tests/data/acl2-x86isa/machine/instructions/fp/`):
//   `base.lisp` (`fp-decode`, `fp-to-rat`, `make-special-bp`),
//   `cmp-spec.lisp` (`sse-cmp`, `sse-cmp-special`), `cvt-spec.lisp`
//   (`sse-cvt-fp-to-int`, `sse-cvt-int-to-fp`, `rat-round-to-int*`).
// - **Not vendored, read at the same upstream commit** (acl2/acl2
//   `33b05575eaf9f54734bf36e6f4bd8ee094ff2ee1`): the ACL2 model's addition,
//   subtraction, multiplication, division and square root do not appear in
//   x86isa at all. `add-mul-spec.lisp` and `sqrt-spec.lisp` call
//   `rtl::sse-binary-spec` and `rtl::sse-sqrt-spec`, which are Russinoff's
//   RTL library, `books/rtl/rel11/lib/excps.lisp` (and its `rnd`, `drnd`,
//   `qsqrt`, `nencode`, `dencode` ... in `defs.lisp`/`reps.lisp`/`round.lisp`).
//   Those definitions are transcribed here, from those files. **They are
//   outside `tests/data/`**: a reviewer needs them fetched from the pinned
//   commit. The same holds for the `UCOMISD` instruction body
//   (`machine/instructions/fp/logical.lisp`, `x86-comis?/ucomis?-Op/En-RM`),
//   which the J.2 vendoring left out; see `semantics.rs`.
//
// # Modelling choices
//
// - **MXCSR is the constant `0x1F80`** (the reset value): round to nearest
//   even, every exception masked, DAZ and FTZ clear. The subset has no
//   `ldmxcsr`, `fxrstor` or `vldmxcsr`, so nothing in a blob can change it;
//   the enter stub (J.7) must set it, and J.6's validator theorem assumes
//   it. Every ACL2 branch that depends on an unmasked exception, on the
//   rounding-control field, on DAZ or on FTZ is therefore the branch that
//   the constant selects, and is commented where it would have been. The
//   sticky exception flags (`mxcsr` bits 0 to 5, the `flags` results of
//   `rtl::sse-post-comp`) are not modelled: no instruction of the subset
//   reads them, so they cannot affect any other state.
// - **A rational is a pair** `n/d` with `d > 0` ([`Rat`]); ACL2 uses
//   its built-in rationals. `expo`, `sig`, `fl` are RTL's (`expo x` is the
//   `e` with `2^e <= |x| < 2^(e+1)`).
// - **A double is a `u64`** (the "encoding" of RTL's `dp` format
//   `(nil 53 11)`: no explicit integer bit, 53-bit precision, 11-bit
//   exponent).
// - `qsqrt` is transcribed as written (`rtz-sqrt` by recursion on the bit
//   count), not replaced by an integer square root.


// ---------------------------------------------------------------------------
// Exact rationals
// ---------------------------------------------------------------------------

/// The rational `n / d` (`d` is always positive).
pub struct Rat {
    /// Numerator.
    pub n: int,
    /// Denominator, positive.
    pub d: int,
}

/// An integer as a rational.
pub open spec fn rat(n: int) -> Rat {
    Rat { n, d: 1 }
}

/// `2^e` for any integer `e`.
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

/// `a / b` (zero when `b` is zero; RTL's `binary-eval` is never called with
/// a zero divisor, its guard says so).
pub open spec fn rat_div(a: Rat, b: Rat) -> Rat {
    if b.n > 0 {
        Rat { n: a.n * b.d, d: a.d * b.n }
    } else if b.n < 0 {
        Rat { n: -(a.n * b.d), d: a.d * (-b.n) }
    } else {
        rat(0)
    }
}

/// `a < b`.
pub open spec fn rat_lt(a: Rat, b: Rat) -> bool {
    a.n * b.d < b.n * a.d
}

/// `a <= b`.
pub open spec fn rat_le(a: Rat, b: Rat) -> bool {
    a.n * b.d <= b.n * a.d
}

/// `a = b` as rationals.
pub open spec fn rat_eq(a: Rat, b: Rat) -> bool {
    a.n * b.d == b.n * a.d
}

/// `|a|`.
pub open spec fn rat_abs(a: Rat) -> Rat {
    if a.n < 0 {
        Rat { n: -a.n, d: a.d }
    } else {
        a
    }
}

/// RTL `(sgn x)`: -1, 0 or 1.
pub open spec fn rat_sgn(a: Rat) -> int {
    if a.n > 0 {
        1
    } else if a.n < 0 {
        -1
    } else {
        0
    }
}

/// RTL `(expo x)` for nonzero `x`: the integer `e` with `2^e <= |x| < 2^(e+1)`.
pub open spec fn expo(x: Rat) -> int {
    choose|e: int| rat_le(rat_p2(e), rat_abs(x)) && rat_lt(rat_abs(x), rat_p2(e + 1))
}

/// RTL `(fl x)`: the greatest integer not above `x`.
pub open spec fn fl(x: Rat) -> int {
    x.n / x.d
}

/// RTL `(cg x)`: the least integer not below `x`.
pub open spec fn cg(x: Rat) -> int {
    if x.n % x.d == 0 {
        x.n / x.d
    } else {
        x.n / x.d + 1
    }
}

// ---------------------------------------------------------------------------
// Rounding: RTL `rtz`, `raz`, `rne`, `rnd` (round.lisp, defs.lisp), `drnd`
// ---------------------------------------------------------------------------

/// `|x| * 2^(n-1-expo x)`: RTL's `(* (expt 2 (1- n)) (sig x))`.
pub open spec fn scaled_sig(x: Rat, n: int) -> Rat {
    rat_mul(rat_abs(x), rat_p2(n - 1 - expo(x)))
}

/// RTL `(rtz x n)`: truncate to `n` significant bits.
pub open spec fn rtz(x: Rat, n: int) -> Rat {
    if x.n == 0 {
        rat(0)
    } else {
        rat_mul(rat(rat_sgn(x) * fl(scaled_sig(x, n))), rat_p2(expo(x) + 1 - n))
    }
}

/// RTL `(raz x n)`: round away from zero to `n` significant bits.
pub open spec fn raz(x: Rat, n: int) -> Rat {
    if x.n == 0 {
        rat(0)
    } else {
        rat_mul(rat(rat_sgn(x) * cg(scaled_sig(x, n))), rat_p2(expo(x) + 1 - n))
    }
}

/// RTL `(rne x n)`: round to nearest even to `n` significant bits.
pub open spec fn rne(x: Rat, n: int) -> Rat {
    if x.n == 0 {
        rat(0)
    } else {
        let s = scaled_sig(x, n);
        let z = fl(s);
        // f = (re (* (expt 2 (1- n)) (sig x))), compared with 1/2.
        let twice_f = 2 * (s.n - z * s.d);
        if twice_f < s.d {
            rtz(x, n)
        } else if twice_f > s.d {
            raz(x, n)
        } else if z % 2 == 0 {
            rtz(x, n)
        } else {
            raz(x, n)
        }
    }
}

/// RTL `(drnd x rne f)` for `f = (dp)`: round to nearest even to the
/// precision a denormal at `x`'s exponent has,
/// `(rnd x mode (+ (prec f) (expo x) (- (expo (spn f)))))` with
/// `prec = 53` and `expo (spn f) = -1022`.
pub open spec fn drnd(x: Rat) -> Rat {
    rne(x, 53 + expo(x) + 1022)
}

// ---------------------------------------------------------------------------
// The binary64 format ((dp) = (nil 53 11)): defs.lisp, reps.lisp
// ---------------------------------------------------------------------------

/// `(prec f)`.
pub open spec fn prec() -> int {
    53
}

/// `(bias f) = 1023`.
pub open spec fn bias() -> int {
    1023
}

/// `(sgnf x f)`.
pub open spec fn sgnf(x: u64) -> int {
    bit(x as int, 63)
}

/// `(expf x f)`: the 11 exponent bits.
pub open spec fn expf(x: u64) -> int {
    (x as int / p2(52)) % p2(11)
}

/// `(sigf x f)` and `(manf x f)`: the 52 fraction bits (`dp` has no
/// explicit integer bit, so they coincide).
pub open spec fn sigf(x: u64) -> int {
    (x as int) % p2(52)
}

/// `(zerp x f)`.
pub open spec fn zerp(x: u64) -> bool {
    expf(x) == 0 && sigf(x) == 0
}

/// `(denormp x f)`.
pub open spec fn denormp(x: u64) -> bool {
    expf(x) == 0 && sigf(x) != 0
}

/// `(infp x f)`.
pub open spec fn infp(x: u64) -> bool {
    expf(x) == 2047 && sigf(x) == 0
}

/// `(nanp x f)`.
pub open spec fn nanp(x: u64) -> bool {
    expf(x) == 2047 && sigf(x) != 0
}

/// `(snanp x f)`: a NaN whose top fraction bit (bit `prec - 2 = 51`) is clear.
pub open spec fn snanp(x: u64) -> bool {
    nanp(x) && bit(x as int, 51) == 0
}

/// `(qnanize x f)`: set bit 51.
pub open spec fn qnanize(x: u64) -> u64 {
    (x as int - bit(x as int, 51) * p2(51) + p2(51)) as u64
}

/// `(indef f)`: sign 1, exponent all ones, fraction `100...0`: the default
/// QNaN `0xFFF8000000000000`.
pub open spec fn indef() -> u64 {
    0xFFF8_0000_0000_0000u64
}

/// `(zencode sgn f)`.
pub open spec fn zencode(sgn: int) -> u64 {
    (sgn * p2(63)) as u64
}

/// `(iencode sgn f)`.
pub open spec fn iencode(sgn: int) -> u64 {
    (sgn * p2(63) + 2047 * p2(52)) as u64
}

/// `(ddecode x f)`: `+- sigf * 2^(2 - bias - prec)`.
pub open spec fn ddecode(x: u64) -> Rat {
    rat_mul(rat((1 - 2 * sgnf(x)) * sigf(x)), rat_p2(2 - bias() - prec()))
}

/// `(ndecode x f)`: `+- 2^(expf - bias) * (1 + manf * 2^(1 - prec))`.
pub open spec fn ndecode(x: u64) -> Rat {
    rat_mul(
        rat((1 - 2 * sgnf(x)) * (p2(52) + sigf(x))),
        rat_p2(expf(x) - bias() - 52),
    )
}

/// `(decode x f)` (`rtl_decode`).
pub open spec fn rtl_decode(x: u64) -> Rat {
    if expf(x) == 0 {
        ddecode(x)
    } else {
        ndecode(x)
    }
}

/// `(spn f)`: the smallest positive normal, `2^(1 - bias)`.
pub open spec fn spn() -> Rat {
    rat_p2(1 - bias())
}

/// `(lpn f)`: the largest positive normal,
/// `2^(2^expw - (2 + bias)) * (2 - 2^(1 - prec))`.
pub open spec fn lpn() -> Rat {
    rat_mul(rat_p2(2048 - (2 + bias())), rat_sub(rat(2), rat_p2(1 - prec())))
}

/// `(nencode x f)` for a nonzero `x` with at most 53 significant bits and
/// `expo x + bias` in `1..=2046`: sign, exponent `expo x + bias`, fraction
/// `sig x * 2^52` (low 52 bits).
pub open spec fn nencode(x: Rat) -> u64 {
    let e = expo(x);
    let m = fl(rat_mul(rat_abs(x), rat_p2(52 - e)));
    (bool_to_bit(x.n < 0) * p2(63) + (e + bias()) * p2(52) + (m - p2(52))) as u64
}

/// `(dencode x f)` for a nonzero denormal `x`: sign, exponent 0, fraction
/// `|x| * 2^1074`.
pub open spec fn dencode(x: Rat) -> u64 {
    let m = fl(rat_mul(rat_abs(x), rat_p2(1074)));
    (bool_to_bit(x.n < 0) * p2(63) + m) as u64
}

// ---------------------------------------------------------------------------
// excps.lisp: sse-post-comp, sse-binary-spec, sse-sqrt-spec
// ---------------------------------------------------------------------------

/// The operations of `rtl::sse-binary-spec`: `add sub mul div`.
pub enum BinOp {
    /// `add`
    Add,
    /// `sub`
    Sub,
    /// `mul`
    Mul,
    /// `div`
    Div,
}

/// RTL `sse-post-comp` (excps.lisp), the part that makes the result:
/// `u` is the exact nonzero result. MXCSR is `0x1F80` (see the header): the
/// rounding mode is `rne`, overflow is masked (so `rne` gives infinity),
/// underflow is masked, FTZ is clear. The `flags` result is not modelled.
pub open spec fn sse_post_comp(u: Rat) -> u64 {
    // (r (rnd u rmode (prec f)))
    let r = rne(u, prec());
    let rsgn = if r.n < 0 {
        1int
    } else {
        0int
    };
    if rat_lt(lpn(), rat_abs(r)) {
        // (> (abs r) (lpn f)), omsk = 1: rmode is rne, so (iencode rsgn f).
        iencode(rsgn)
    } else if rat_lt(rat_abs(r), spn()) {
        // (< (abs r) (spn f)), umsk = 1, ftz = 0:
        let d = drnd(u);
        if rat_eq(d, u) {
            dencode(d)
        } else if d.n == 0 {
            zencode(rsgn)
        } else if rat_eq(rat_abs(d), spn()) {
            nencode(d)
        } else {
            dencode(d)
        }
    } else {
        nencode(r)
    }
}

/// RTL `binary-undefined-p` (excps.lisp).
pub open spec fn binary_undefined_p(op: BinOp, a: u64, b: u64) -> bool {
    match op {
        BinOp::Add => infp(a) && infp(b) && sgnf(a) != sgnf(b),
        BinOp::Sub => infp(a) && infp(b) && sgnf(a) == sgnf(b),
        BinOp::Mul => (infp(a) || infp(b)) && (zerp(a) || zerp(b)),
        BinOp::Div => (infp(a) && infp(b)) || (zerp(a) && zerp(b)),
    }
}

/// RTL `sse-binary-pre-comp-val` (excps.lisp), with `dazify` the identity
/// (DAZ clear): `Some(result)` when a NaN operand or an invalid operation
/// decides the result, `None` otherwise.
pub open spec fn sse_binary_pre_comp_val(op: BinOp, a: u64, b: u64) -> Option<u64> {
    if nanp(a) {
        Some(qnanize(a))
    } else if nanp(b) {
        Some(qnanize(b))
    } else if binary_undefined_p(op, a, b) {
        Some(indef())
    } else {
        None
    }
}

/// RTL `binary-inf-sgn` (excps.lisp).
pub open spec fn binary_inf_sgn(op: BinOp, a: u64, b: u64) -> int {
    match op {
        BinOp::Add => if infp(a) {
            sgnf(a)
        } else {
            sgnf(b)
        },
        BinOp::Sub => if infp(a) {
            sgnf(a)
        } else if sgnf(b) == 0 {
            1
        } else {
            0
        },
        BinOp::Mul | BinOp::Div => if sgnf(a) == sgnf(b) {
            0
        } else {
            1
        },
    }
}

/// RTL `binary-zero-sgn` (excps.lisp) for `rmode = rne` (only `rdn` differs).
pub open spec fn binary_zero_sgn(op: BinOp, asgn: int, bsgn: int) -> int {
    match op {
        BinOp::Add => if asgn == bsgn {
            asgn
        } else {
            0
        },
        BinOp::Sub => if asgn != bsgn {
            asgn
        } else {
            0
        },
        BinOp::Mul | BinOp::Div => if asgn == bsgn {
            0
        } else {
            1
        },
    }
}

/// RTL `binary-eval` (excps.lisp).
pub open spec fn binary_eval(op: BinOp, aval: Rat, bval: Rat) -> Rat {
    match op {
        BinOp::Add => rat_add(aval, bval),
        BinOp::Sub => rat_sub(aval, bval),
        BinOp::Mul => rat_mul(aval, bval),
        BinOp::Div => rat_div(aval, bval),
    }
}

/// RTL `sse-binary-comp` (excps.lisp), result only.
pub open spec fn sse_binary_comp(op: BinOp, a: u64, b: u64) -> u64 {
    if infp(a) || (if op is Div {
        zerp(b)
    } else {
        infp(b)
    }) {
        iencode(binary_inf_sgn(op, a, b))
    } else {
        let asgn = sgnf(a);
        let bsgn = sgnf(b);
        let aval = rtl_decode(a);
        let bval = rtl_decode(b);
        let u = binary_eval(op, aval, bval);
        if (op is Div && infp(b)) || u.n == 0 {
            zencode(binary_zero_sgn(op, asgn, bsgn))
        } else {
            sse_post_comp(u)
        }
    }
}

/// RTL `sse-binary-spec` (excps.lisp), result only, via x86isa's
/// `dp-sse-add/sub/mul/div` (add-mul-spec.lisp): the result of `addsd`,
/// `subsd`, `mulsd` or `divsd` on the operands `a` (destination) and `b`.
/// The pre-computation's exception flags (step "unmasked-excp-p") never
/// stop the computation, because every mask is set.
pub open spec fn dp_sse_add_sub_mul_div(op: BinOp, a: u64, b: u64) -> u64 {
    match sse_binary_pre_comp_val(op, a, b) {
        Some(v) => v,
        None => sse_binary_comp(op, a, b),
    }
}

/// RTL `rtz-sqrt` (defs.lisp): the `n`-bit truncated square root.
pub open spec fn rtz_sqrt(x: Rat, n: nat) -> Rat
    decreases n,
{
    if n == 0 {
        rat(0)
    } else {
        let lower = rtz_sqrt(x, (n - 1) as nat);
        let upper = rat_add(lower, rat_p2(-(n as int)));
        if rat_le(rat_mul(upper, upper), x) {
            upper
        } else {
            lower
        }
    }
}

/// RTL `rto-sqrt` (defs.lisp).
pub open spec fn rto_sqrt(x: Rat, n: nat) -> Rat {
    let trunc = rtz_sqrt(x, (n - 1) as nat);
    if rat_lt(rat_mul(trunc, trunc), x) {
        rat_add(trunc, rat_p2(-(n as int)))
    } else {
        trunc
    }
}

/// RTL `qsqrt` (defs.lisp): `x` positive.
pub open spec fn qsqrt(x: Rat, n: nat) -> Rat {
    let e = 1 + expo(x) / 2;
    rat_mul(rat_p2(e), rto_sqrt(rat_mul(x, rat_p2(-(2 * e))), n))
}

/// RTL `sse-sqrt-spec` (excps.lisp), result only, via x86isa's `dp-sse-sqrt`
/// (sqrt-spec.lisp): the result of `sqrtsd` on `a`.
pub open spec fn dp_sse_sqrt(a: u64) -> u64 {
    // sse-sqrt-pre-comp-val (dazify is the identity)
    if nanp(a) {
        qnanize(a)
    } else if !zerp(a) && sgnf(a) == 1 {
        indef()
    } else {
        // sse-sqrt-comp
        if infp(a) || zerp(a) {
            a
        } else {
            sse_post_comp(qsqrt(rtl_decode(a), (prec() + 2) as nat))
        }
    }
}

// ---------------------------------------------------------------------------
// base.lisp (vendored): fp-decode, fp-to-rat
// ---------------------------------------------------------------------------

/// The kinds `fp-decode` returns (base.lisp).
pub enum Kind {
    /// `'indef`
    Indef,
    /// `'qnan`
    Qnan,
    /// `'snan`
    Snan,
    /// `'inf`
    Inf,
    /// `'zero`
    Zero,
    /// `'denormal`
    Denormal,
    /// `'normal`
    Normal,
}

/// `fp-decode` (base.lisp) for `exp-width = 11`, `frac-width = 52`: the kind
/// of the double `x`. (The sign, exponent and fraction it also returns are
/// [`sgnf`], [`expf`] and [`sigf`].)
pub open spec fn fp_decode_kind(x: u64) -> Kind {
    if expf(x) == 0 {
        if sigf(x) != 0 {
            Kind::Denormal
        } else {
            Kind::Zero
        }
    } else if expf(x) == 2047 {
        if sigf(x) == 0 {
            Kind::Inf
        } else if bit(sigf(x), 51) == 1 {
            if sgnf(x) == 1 && sigf(x) == p2(51) {
                Kind::Indef
            } else {
                Kind::Qnan
            }
        } else {
            Kind::Snan
        }
    } else {
        Kind::Normal
    }
}

/// `fp-to-rat` (base.lisp): the value of a zero, denormal or normal double
/// (0 for anything else).
pub open spec fn fp_to_rat(x: u64) -> Rat {
    let sign = sgnf(x);
    let exp = expf(x);
    let frac = sigf(x);
    if exp == 0 && frac == 0 {
        rat(0)
    } else if exp == 0 {
        // man = frac * 2^-frac-width; (* sign man (expt 2 (- 1 bias)))
        rat_mul(rat((1 - 2 * sign) * frac), rat_p2(-52 + (1 - bias())))
    } else if 0 < exp && exp <= 2046 {
        rat_mul(rat((1 - 2 * sign) * (p2(52) + frac)), rat_p2(-52 + (exp - bias())))
    } else {
        rat(0)
    }
}

// ---------------------------------------------------------------------------
// cmp-spec.lisp (vendored): sse-cmp for UCOMI
// ---------------------------------------------------------------------------

/// Whether `k` is `snan`, `qnan` or `indef`.
pub open spec fn kind_is_nan(k: Kind) -> bool {
    k is Snan || k is Qnan || k is Indef
}

/// `sse-cmp` (cmp-spec.lisp) with `operation = *OP-UCOMI*`, through
/// `dp-sse-cmp`: 0 for "greater", 1 for "less", 4 for "equal", 7 for
/// "unordered". `daz` is clear and every mask is set, so the
/// `invalid-operand-exception-is-not-masked` and
/// `denormal-operand-exception-is-not-masked` returns are never taken.
pub open spec fn dp_sse_cmp_ucomi(op1: u64, op2: u64) -> int {
    let kind1 = fp_decode_kind(op1);
    let kind2 = fp_decode_kind(op2);
    // sse-cmp-special
    if kind_is_nan(kind1) || kind_is_nan(kind2) {
        // (or (int= operation *OP-COMI*) (int= operation *OP-UCOMI*)) => 7
        7
    } else if kind1 is Inf || kind2 is Inf {
        let rat1 = if kind1 is Inf {
            if sgnf(op1) == 0 {
                1int
            } else {
                -1int
            }
        } else {
            0int
        };
        let rat2 = if kind2 is Inf {
            if sgnf(op2) == 0 {
                1int
            } else {
                -1int
            }
        } else {
            0int
        };
        if rat1 > rat2 {
            0
        } else if rat1 < rat2 {
            1
        } else {
            4
        }
    } else {
        let rat1 = fp_to_rat(op1);
        let rat2 = fp_to_rat(op2);
        if rat_lt(rat2, rat1) {
            0
        } else if rat_lt(rat1, rat2) {
            1
        } else {
            4
        }
    }
}

// ---------------------------------------------------------------------------
// cvt-spec.lisp (vendored): conversions to and from integers
// ---------------------------------------------------------------------------

/// `rat-round-to-int-rn` (cvt-spec.lisp): ACL2 `(round rat 1)`, the nearest
/// integer, ties to even.
pub open spec fn rat_round_to_int_rn(r: Rat) -> int {
    let f = fl(r);
    let twice_rem = 2 * (r.n - f * r.d);
    if twice_rem < r.d {
        f
    } else if twice_rem > r.d {
        f + 1
    } else if f % 2 == 0 {
        f
    } else {
        f + 1
    }
}

/// `rat-round-to-int-rz` (cvt-spec.lisp): ACL2 `(truncate rat 1)`.
pub open spec fn rat_round_to_int_rz(r: Rat) -> int {
    if r.n >= 0 {
        fl(r)
    } else {
        cg(r)
    }
}

/// `sse-cvt-fp-to-int` (cvt-spec.lisp) through `dp-sse-cvt-fp-to-int`: the
/// bit pattern of the `nbytes`-byte result of `cvtsd2si` (`trunc` false) or
/// `cvttsd2si` (`trunc` true) on the double `op`. `nbytes` is 4 or 8. The
/// rounding-control field of MXCSR is 0 (`*RC-RN*`).
pub open spec fn dp_sse_cvt_fp_to_int(nbytes: nat, op: u64, trunc: bool) -> int {
    let nbits = nbytes * 8;
    let kind = fp_decode_kind(op);
    // sse-cvt-fp-to-int-special: NaN or infinity gives the integer indefinite
    if kind is Snan || kind is Qnan || kind is Indef || kind is Inf {
        p2((nbits - 1) as nat)
    } else {
        let rat = fp_to_rat(op);
        // (rc (if trunc #b11 rc)): rz when trunc, rn otherwise.
        let rat_to_int = if trunc {
            rat_round_to_int_rz(rat)
        } else {
            rat_round_to_int_rn(rat)
        };
        let min_signed_int = -p2((nbits - 1) as nat);
        let max_signed_int = p2((nbits - 1) as nat) - 1;
        if rat_to_int < min_signed_int || rat_to_int > max_signed_int {
            // out-of-range, masked: the integer indefinite
            p2((nbits - 1) as nat)
        } else {
            // (trunc nbytes result)
            loghead(nbits, rat_to_int)
        }
    }
}

/// `sse-cvt-int-to-fp` (cvt-spec.lisp) through `dp-sse-cvt-int-to-fp`: the
/// double `cvtsi2sd` makes of the signed integer `op`. `rat-round` is
/// `(rnd x rne 53)` for an integer (an integer's `expo` is at least 0, above
/// `-bias`); `rat-to-fp` of zero is `+0` (the sign is 0 for `rc = rn`), and
/// of any other integer is its `nencode`.
pub open spec fn dp_sse_cvt_int_to_fp(op: int) -> u64 {
    let int_to_rat = rne(rat(op), prec());
    if int_to_rat.n == 0 {
        // (rat-to-fp 0 sign ...) => (fp-encode-integer sign 0 0 ...), sign 0.
        zencode(0)
    } else {
        nencode(int_to_rat)
    }
}


// ============================================================================
// Section: syntax
// ============================================================================
//
// The abstract syntax of the subset: one enum value per instruction (jit.md
// item J.3), and the predicate saying which values are in the subset.
//
// This is not a decoding of ACL2's `prefixes`/`rex`/`modr/m`/`sib` structures
// (`utils/structures.lisp`, `machine/prefix-modrm-sib-decoding.lisp`); it is
// what those fields mean once decoded, for the forms the JIT emits, with the
// ACL2 names for the fields: [`Size`] is `operand-size`, a register index is
// the 4-bit result of `reg-index`, [`Mem`] is the effective address
// `base + (index << scale) + disp32` of `x86-effective-addr-32/64`
// (`machine/decoding-and-spec-utils.lisp`) with `mod = 2` (disp32) and a SIB
// byte (`x86-effective-addr-from-sib`).


/// The operand size of an integer instruction (ACL2 `operand-size`): 4 bytes
/// (a write to a register zero-extends to 64 bits) or 8.
pub enum Size {
    /// `operand-size = 4`
    W32,
    /// `operand-size = 8` (`REX.W`)
    W64,
}

/// `operand-size` in bytes.
pub open spec fn nbytes(sz: Size) -> nat {
    match sz {
        Size::W32 => 4,
        Size::W64 => 8,
    }
}

/// `operand-size` in bits.
pub open spec fn nbits(sz: Size) -> nat {
    nbytes(sz) * 8
}

/// A scaled index register: `reg << scale`. `scale` is the SIB `scale` field
/// (0 to 3, so the factor is 1, 2, 4 or 8).
pub struct Index {
    /// The register number (0 to 15, but not 4: `rsp` cannot be an index).
    pub reg: u8,
    /// The SIB `scale` field.
    pub scale: u8,
}

/// A memory operand `base + (index << scale) + disp`: a base register, an
/// optional scaled index, and a 32-bit displacement (sign-extended). No
/// RIP-relative form, no absolute form, no segment override, no address-size
/// override.
pub struct Mem {
    /// The base register number (0 to 15).
    pub base: u8,
    /// The index, or `None` ("no index register" in Intel Table 2-3).
    pub index: Option<Index>,
    /// The displacement.
    pub disp: i32,
}

/// The two-operand arithmetic and logic operations of group 1 that the
/// subset has (ACL2 `*OP-ADD*`, `*OP-OR*`, `*OP-AND*`, `*OP-SUB*`, `*OP-XOR*`
/// and `*OP-CMP*`; the subset has no `adc` or `sbb`). `Cmp` only sets flags.
pub enum AluOp {
    /// `add`
    Add,
    /// `or`
    Or,
    /// `and`
    And,
    /// `sub`
    Sub,
    /// `xor`
    Xor,
    /// `cmp`
    Cmp,
}

/// The shifts of the subset (ModR/M `reg` 4, 5 and 7 of group 2).
pub enum ShiftOp {
    /// `shl` (also `sal`)
    Shl,
    /// `shr`
    Shr,
    /// `sar`
    Sar,
}

/// The source of an SSE scalar double operation: an XMM register or 8 bytes
/// of memory (`xmm2/m64`).
pub enum XmmSrc {
    /// An XMM register, 0 to 15.
    Reg(u8),
    /// Memory.
    Mem(Mem),
}

/// One instruction of the subset. A condition code `cc` is the low nibble of
/// the opcode (`jcc/cmovcc/setcc-spec`, conditional.lisp): 0 `o`, 1 `no`, 2
/// `b`, 3 `ae`, 4 `e`, 5 `ne`, 6 `be`, 7 `a`, 8 `s`, 9 `ns`, 10 `p`, 11 `np`,
/// 12 `l`, 13 `ge`, 14 `le`, 15 `g`. A relative displacement is relative to
/// the address of the next instruction.
pub enum Instr {
    // ---- moves, loads, stores ----
    /// `mov r, r` (`x86-mov-Op/En-MR`, opcode 89): `dst := src`.
    MovRR {
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `mov r, [mem]` (`x86-mov-Op/En-RM`, opcode 8B).
    MovLoad {
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The memory operand.
        mem: Mem,
    },
    /// `mov [mem], r` (`x86-mov-Op/En-MR`, opcode 89).
    MovStore {
        /// The operand size.
        sz: Size,
        /// The memory operand.
        mem: Mem,
        /// The source register.
        src: u8,
    },
    /// `mov r32, imm32` (`x86-mov-Op/En-OI`, opcode B8+r, operand size 4: the
    /// result is zero-extended).
    MovImm32 {
        /// The destination register.
        dst: u8,
        /// The immediate.
        imm_u32: u32,
    },
    /// `mov r64, imm32` (`x86-mov-Op/En-MI`, opcode C7 /0 with `REX.W`: the
    /// immediate is sign-extended).
    MovImm32S {
        /// The destination register.
        dst: u8,
        /// The immediate.
        imm: i32,
    },
    /// `mov r64, imm64` (`x86-mov-Op/En-OI`, opcode B8+r with `REX.W`).
    MovImm64 {
        /// The destination register.
        dst: u8,
        /// The immediate.
        imm_u64: u64,
    },
    // ---- integer arithmetic and logic ----
    /// `op r, r` (`x86-add/xadd/adc/sub/sbb/or/and/xor/cmp/test-E-G`):
    /// `dst := dst op src` (`Cmp` only sets the flags).
    AluRR {
        /// The operation.
        alu: AluOp,
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `op r, [mem]` (`x86-add/adc/sub/sbb/or/and/xor/cmp-G-E`).
    AluRM {
        /// The operation.
        alu: AluOp,
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The memory operand.
        mem: Mem,
    },
    /// `op r, imm32` (`x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I`, opcode
    /// 81): the immediate is sign-extended to the operand size.
    AluRI {
        /// The operation.
        alu: AluOp,
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The immediate.
        imm: i32,
    },
    /// `test r, r` (`x86-add/xadd/adc/sub/sbb/or/and/xor/cmp/test-E-G`,
    /// opcode 85, `*OP-TEST*`): `a & b` sets the flags.
    TestRR {
        /// The operand size.
        sz: Size,
        /// The a operand.
        a: u8,
        /// The b operand.
        b: u8,
    },
    /// `test r, imm32` (`x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I`, opcode
    /// F7 /0).
    TestRI {
        /// The operand size.
        sz: Size,
        /// The a operand.
        a: u8,
        /// The immediate.
        imm: i32,
    },
    /// `neg r` (`x86-not/neg-F6-F7`, F7 /3).
    Neg {
        /// The operand size.
        sz: Size,
        /// The r operand.
        r: u8,
    },
    /// `not r` (`x86-not/neg-F6-F7`, F7 /2).
    Not {
        /// The operand size.
        sz: Size,
        /// The r operand.
        r: u8,
    },
    /// `shl/shr/sar r, imm8` (`x86-sal/sar/shl/shr/rcl/rcr/rol/ror`, opcode
    /// C1). The count is 1 up to one less than the operand size in bits.
    ShiftImm {
        /// The operation.
        shift: ShiftOp,
        /// The operand size.
        sz: Size,
        /// The r operand.
        r: u8,
        /// The shift count.
        count: u8,
    },
    /// `shl/shr/sar r, cl` (same, opcode D3).
    ShiftCl {
        /// The operation.
        shift: ShiftOp,
        /// The operand size.
        sz: Size,
        /// The r operand.
        r: u8,
    },
    /// `imul r, r` (`x86-imul-Op/En-RM`, opcode 0F AF): `dst := dst * src`.
    ImulRR {
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `imul r, r, imm32` (`x86-imul-Op/En-RMI`, opcode 69): `dst := src * imm`.
    ImulRRI {
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
        /// The immediate.
        imm: i32,
    },
    // ---- control flow ----
    /// `jcc rel32` (`x86-two-byte-jcc`, opcode 0F 80+cc).
    Jcc {
        /// The condition code.
        cc: u8,
        /// The relative displacement.
        rel: i32,
    },
    /// `jmp rel32` (`x86-near-jmp-Op/En-D`, opcode E9).
    Jmp {
        /// The relative displacement.
        rel: i32,
    },
    /// `ret` (`x86-ret`, opcode C3).
    Ret,
    /// `cmovcc r, r` (`x86-cmovcc`, opcode 0F 40+cc).
    Cmovcc {
        /// The condition code.
        cc: u8,
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `setcc r8` (`x86-setcc`, opcode 0F 90+cc): writes the low byte of the
    /// register.
    Setcc {
        /// The condition code.
        cc: u8,
        /// The destination register.
        dst: u8,
    },
    // ---- SSE2 scalar double ----
    /// `addsd/subsd/mulsd/divsd xmm, xmm/m64`
    /// (`x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM`, F2 0F 58/5C/59/5E).
    FpArith {
        /// The operation.
        fop: BinOp,
        /// The destination register.
        dst: u8,
        /// The XMM or memory source.
        xsrc: XmmSrc,
    },
    /// `sqrtsd xmm, xmm/m64` (`x86-sqrts?-Op/En-RM`, F2 0F 51).
    Sqrtsd {
        /// The destination register.
        dst: u8,
        /// The XMM or memory source.
        xsrc: XmmSrc,
    },
    /// `ucomisd xmm, xmm/m64` (`x86-comis?/ucomis?-Op/En-RM`, 66 0F 2E).
    Ucomisd {
        /// The a operand.
        a: u8,
        /// The XMM or memory source.
        xsrc: XmmSrc,
    },
    /// `cvtsi2sd xmm, r32/r64` (`x86-cvtsi2s?-Op/En-RM`, F2 [REX.W] 0F 2A).
    Cvtsi2sd {
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `cvttsd2si r32/r64, xmm` (`x86-cvts?2si/cvtts?2si-Op/En-RM`, F2
    /// [REX.W] 0F 2C): truncating.
    Cvttsd2si {
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `cvtsd2si r32/r64, xmm` (same function, F2 [REX.W] 0F 2D): rounds as
    /// MXCSR says (to nearest even).
    Cvtsd2si {
        /// The operand size.
        sz: Size,
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `movq xmm, r64` (`x86-movd/movq-to-xmm`, 66 REX.W 0F 6E): the upper 64
    /// bits of the XMM register become zero.
    MovqToXmm {
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `movq r64, xmm` (`x86-movd/movq-from-xmm`, 66 REX.W 0F 7E).
    MovqFromXmm {
        /// The destination register.
        dst: u8,
        /// The source register.
        src: u8,
    },
    /// `movsd xmm, m64` (`x86-movss/movsd-Op/En-RM`, F2 0F 10): the upper 64
    /// bits become zero.
    MovsdLoad {
        /// The destination register.
        dst: u8,
        /// The memory operand.
        mem: Mem,
    },
    /// `movsd m64, xmm` (`x86-movss/movsd-Op/En-MR`, F2 0F 11).
    MovsdStore {
        /// The memory operand.
        mem: Mem,
        /// The source register.
        src: u8,
    },
}

/// A register number of the 16 general-purpose or XMM registers.
pub open spec fn reg_ok(r: u8) -> bool {
    r < 16
}

/// A valid memory operand: base below 16; an index below 16 and not 4
/// (`rsp`; index field 100 with `REX.X` clear means no index) with `scale`
/// below 4.
pub open spec fn mem_ok(m: Mem) -> bool {
    reg_ok(m.base) && match m.index {
        None => true,
        Some(ix) => reg_ok(ix.reg) && ix.reg != 4 && ix.scale < 4,
    }
}

/// A valid XMM source.
pub open spec fn xmm_src_ok(s: XmmSrc) -> bool {
    match s {
        XmmSrc::Reg(r) => reg_ok(r),
        XmmSrc::Mem(m) => mem_ok(m),
    }
}

/// The largest count a shift by an immediate may name: the operand size in
/// bits minus one (a count is masked to 5 or 6 bits, `countMask` in
/// `x86-sal/sar/shl/shr/rcl/rcr/rol/ror`; 0 is a no-op and is not the
/// canonical form).
pub open spec fn max_shift(sz: Size) -> int {
    nbits(sz) as int - 1
}

/// Whether `i` is an instruction of the subset: every register number is in
/// range, every memory operand is a valid one, a condition code is below 16,
/// and a shift count is in range.
pub open spec fn valid_instr(i: Instr) -> bool {
    match i {
        Instr::MovRR { sz, dst, src } => reg_ok(dst) && reg_ok(src),
        Instr::MovLoad { sz, dst, mem } => reg_ok(dst) && mem_ok(mem),
        Instr::MovStore { sz, mem, src } => mem_ok(mem) && reg_ok(src),
        Instr::MovImm32 { dst, imm_u32: imm } => reg_ok(dst),
        Instr::MovImm32S { dst, imm } => reg_ok(dst),
        Instr::MovImm64 { dst, imm_u64: imm } => reg_ok(dst),
        Instr::AluRR { alu: op, sz, dst, src } => reg_ok(dst) && reg_ok(src),
        Instr::AluRM { alu: op, sz, dst, mem } => reg_ok(dst) && mem_ok(mem),
        Instr::AluRI { alu: op, sz, dst, imm } => reg_ok(dst),
        Instr::TestRR { sz, a, b } => reg_ok(a) && reg_ok(b),
        Instr::TestRI { sz, a, imm } => reg_ok(a),
        Instr::Neg { sz, r } => reg_ok(r),
        Instr::Not { sz, r } => reg_ok(r),
        Instr::ShiftImm { shift: op, sz, r, count } => reg_ok(r) && 1 <= count && count as int
            <= max_shift(sz),
        Instr::ShiftCl { shift: op, sz, r } => reg_ok(r),
        Instr::ImulRR { sz, dst, src } => reg_ok(dst) && reg_ok(src),
        Instr::ImulRRI { sz, dst, src, imm } => reg_ok(dst) && reg_ok(src),
        Instr::Jcc { cc, rel } => cc < 16,
        Instr::Jmp { rel } => true,
        Instr::Ret => true,
        Instr::Cmovcc { cc, sz, dst, src } => cc < 16 && reg_ok(dst) && reg_ok(src),
        Instr::Setcc { cc, dst } => cc < 16 && reg_ok(dst),
        Instr::FpArith { fop: op, dst, xsrc: src } => reg_ok(dst) && xmm_src_ok(src),
        Instr::Sqrtsd { dst, xsrc: src } => reg_ok(dst) && xmm_src_ok(src),
        Instr::Ucomisd { a, xsrc: src } => reg_ok(a) && xmm_src_ok(src),
        Instr::Cvtsi2sd { sz, dst, src } => reg_ok(dst) && reg_ok(src),
        Instr::Cvttsd2si { sz, dst, src } => reg_ok(dst) && reg_ok(src),
        Instr::Cvtsd2si { sz, dst, src } => reg_ok(dst) && reg_ok(src),
        Instr::MovqToXmm { dst, src } => reg_ok(dst) && reg_ok(src),
        Instr::MovqFromXmm { dst, src } => reg_ok(dst) && reg_ok(src),
        Instr::MovsdLoad { dst, mem } => reg_ok(dst) && mem_ok(mem),
        Instr::MovsdStore { mem, src } => mem_ok(mem) && reg_ok(src),
    }
}


// ============================================================================
// Section: encoding
// ============================================================================
//
// The canonical encoding: one fixed byte string per instruction of the
// subset (jit.md item J.3).
//
// The encoder emits only these bytes, and the validator (J.6) accepts only
// them. Everything x86-64 allows beyond them is refused: redundant prefixes,
// a `REX` byte that sets no bit, the alternative ModR/M forms (`mod` 0 and 1,
// no-SIB forms, the `rm` operand written in the `reg` direction), the
// sign-extended 8-bit immediates, the `D1`/`C0`/`D0`/`D2` shift forms, and
// every prefix the subset does not name (segment, address-size, `lock`,
// `rep`, the operand-size prefix on an integer instruction, `VEX`, `EVEX`).
//
// The rules (each instruction's bytes are in [`encode`]):
//
// 1. **Prefix order:** the mandatory prefix of an SSE instruction (`66` or
//    `F2`), then `REX`, then the opcode, then ModR/M, SIB, displacement,
//    immediate.
// 2. **`REX`** is present exactly when it sets a bit: `W` for 64-bit
//    operand size (and always for `movq`, `mov r64, imm32` and
//    `mov r64, imm64`), `R` for a `reg` operand numbered 8 or more, `X` for
//    an index register of 8 or more, `B` for an `rm` or base register of 8
//    or more. The one other case is `setcc` on `spl`, `bpl`, `sil` or `dil`
//    (registers 4 to 7), which needs a `REX` byte (here `0x40`) to name them
//    rather than `ah`, `ch`, `dh`, `bh` (the `rr08`/`wr08` rule in
//    `machine/register-readers-and-writers.lisp`).
// 3. **Register operands use `mod = 11`.** The operand in the `rm` field is
//    the destination of an `op r, r`, the register of `neg`, `not`, a shift,
//    `test`, the source of `cmovcc`, `imul`, a conversion; the `reg` field
//    holds the other operand. The direction is fixed per instruction, below.
// 4. **Memory operands use `mod = 10`, `rm = 100` (a SIB byte) and a
//    four-byte displacement**, always. The SIB byte holds `scale`, `index`
//    and `base`; with no index, `index = 100`, `REX.X = 0` and `scale = 0`.
//    `mod = 10` has no special case for a base of `rbp` or `r13`, and the SIB
//    byte makes a base of `rsp` or `r12` expressible, so any base works.
// 5. **Immediates** are little-endian, always four bytes (`imm32`, or
//    `imm64` for `movabs`), never the 8-bit sign-extended forms.
// 6. **One opcode per operation:** `op r/m, r` (opcode `op*8+1`) for
//    register-register, `op r, r/m` (`op*8+3`) for loads, `81 /n` for
//    immediates, `89` for a register-to-register `mov` and for a store, `8B`
//    for a load, `85` for `test r, r`, `F7 /0` for `test r, imm32`, `C1`
//    for an immediate shift (also by 1), `D3` for a shift by `cl`.
//
// This is a choice of the subset, not something ACL2 states: ACL2 decodes
// every encoding, so what ties these bytes to the semantics is only that
// ACL2's decoder (`machine/prefix-modrm-sib-decoding.lisp`,
// `machine/inst-listing.lisp`) reads these bytes as the instruction
// [`Instr`] names. Opcodes are those of `inst-listing.lisp`, which also
// lists the `reg` extensions of the groups.


/// The `n` low bytes of `v`, least significant first (two's complement for a
/// negative `v`).
pub open spec fn le_bytes(v: int, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        seq![(v % 256) as u8] + le_bytes(v / 256, (n - 1) as nat)
    }
}

/// The `REX` prefix (`0100WRXB`) when it must be present: when any of `w`,
/// `r`, `x`, `b` is set, or when `force` (a byte register 4 to 7).
pub open spec fn rex_seq(w: bool, r: bool, x: bool, b: bool, force: bool) -> Seq<u8> {
    if w || r || x || b || force {
        seq![(0x40 + 8 * bool_to_bit(w) + 4 * bool_to_bit(r) + 2 * bool_to_bit(x) + bool_to_bit(
            b,
        )) as u8]
    } else {
        Seq::empty()
    }
}

/// A ModR/M byte from `mod`, `reg` and `rm` (the last two reduced to three
/// bits: the fourth bit is in `REX`).
pub open spec fn modrm(m: int, reg: int, rm: int) -> u8 {
    (m * 64 + (reg % 8) * 8 + (rm % 8)) as u8
}

/// A register-direct instruction: `prefix`, `REX`, `opcode`, ModR/M with
/// `mod = 11`, `reg` in the `reg` field and `rm` in the `rm` field.
pub open spec fn enc_rr(
    prefix: Seq<u8>,
    w: bool,
    reg: u8,
    rm: u8,
    opcode: Seq<u8>,
    force_rex: bool,
) -> Seq<u8> {
    prefix + rex_seq(w, reg >= 8, false, rm >= 8, force_rex) + opcode + seq![
        modrm(3, reg as int, rm as int),
    ]
}

/// The SIB `index` field of a memory operand (100 for "none").
pub open spec fn sib_index_reg(m: Mem) -> int {
    match m.index {
        None => 4,
        Some(ix) => ix.reg as int,
    }
}

/// The SIB `scale` field of a memory operand (0 for "no index").
pub open spec fn sib_scale(m: Mem) -> int {
    match m.index {
        None => 0,
        Some(ix) => ix.scale as int,
    }
}

/// A memory instruction: `prefix`, `REX`, `opcode`, ModR/M with `mod = 10`
/// and `rm = 100`, SIB, a four-byte displacement.
pub open spec fn enc_rm_mem(prefix: Seq<u8>, w: bool, reg: u8, m: Mem, opcode: Seq<u8>) -> Seq<u8> {
    let ix = sib_index_reg(m);
    prefix + rex_seq(w, reg >= 8, ix >= 8, m.base >= 8, false) + opcode + seq![
        modrm(2, reg as int, 4),
        (sib_scale(m) * 64 + (ix % 8) * 8 + (m.base as int) % 8) as u8,
    ] + le_bytes(m.disp as int, 4)
}

/// An XMM source operand in the `rm` position.
pub open spec fn enc_xmm_src(
    prefix: Seq<u8>,
    w: bool,
    reg: u8,
    src: XmmSrc,
    opcode: Seq<u8>,
) -> Seq<u8> {
    match src {
        XmmSrc::Reg(r) => enc_rr(prefix, w, reg, r, opcode, false),
        XmmSrc::Mem(m) => enc_rm_mem(prefix, w, reg, m, opcode),
    }
}

/// `REX.W` for an operand size.
pub open spec fn is64(sz: Size) -> bool {
    sz is W64
}

/// The opcode base of a group-1 operation in the `op r/m, r` row
/// (`add` 00, `or` 08, `and` 20, `sub` 28, `xor` 30, `cmp` 38).
pub open spec fn alu_base(op: AluOp) -> int {
    match op {
        AluOp::Add => 0x00,
        AluOp::Or => 0x08,
        AluOp::And => 0x20,
        AluOp::Sub => 0x28,
        AluOp::Xor => 0x30,
        AluOp::Cmp => 0x38,
    }
}

/// The ModR/M `reg` extension of a group-1 operation (`81 /n`).
pub open spec fn alu_ext(op: AluOp) -> int {
    match op {
        AluOp::Add => 0,
        AluOp::Or => 1,
        AluOp::And => 4,
        AluOp::Sub => 5,
        AluOp::Xor => 6,
        AluOp::Cmp => 7,
    }
}

/// The ModR/M `reg` extension of a shift (`C1 /n`, `D3 /n`).
pub open spec fn shift_ext(op: ShiftOp) -> int {
    match op {
        ShiftOp::Shl => 4,
        ShiftOp::Shr => 5,
        ShiftOp::Sar => 7,
    }
}

/// The second opcode byte of `addsd`, `subsd`, `mulsd`, `divsd` (`0F xx`).
pub open spec fn fp_opcode(op: BinOp) -> int {
    match op {
        BinOp::Add => 0x58,
        BinOp::Mul => 0x59,
        BinOp::Sub => 0x5C,
        BinOp::Div => 0x5E,
    }
}

/// The canonical encoding of an instruction. Meaningful for a
/// [`valid_instr`] (any other value gets some byte string, and is not in the
/// subset: see [`is_canonical_encoding`]).
pub open spec fn encode(i: Instr) -> Seq<u8> {
    match i {
        Instr::MovRR { sz, dst, src } => enc_rr(Seq::empty(), is64(sz), src, dst, seq![0x89u8], false),
        Instr::MovLoad { sz, dst, mem } => enc_rm_mem(Seq::empty(), is64(sz), dst, mem, seq![0x8Bu8]),
        Instr::MovStore { sz, mem, src } => enc_rm_mem(Seq::empty(), is64(sz), src, mem, seq![0x89u8]),
        Instr::MovImm32 { dst, imm_u32: imm } => rex_seq(false, false, false, dst >= 8, false) + seq![
            (0xB8 + (dst as int) % 8) as u8,
        ] + le_bytes(imm as int, 4),
        Instr::MovImm32S { dst, imm } => enc_rr(Seq::empty(), true, 0, dst, seq![0xC7u8], false)
            + le_bytes(imm as int, 4),
        Instr::MovImm64 { dst, imm_u64: imm } => rex_seq(true, false, false, dst >= 8, false) + seq![
            (0xB8 + (dst as int) % 8) as u8,
        ] + le_bytes(imm as int, 8),
        Instr::AluRR { alu: op, sz, dst, src } => enc_rr(
            Seq::empty(),
            is64(sz),
            src,
            dst,
            seq![(alu_base(op) + 1) as u8],
            false,
        ),
        Instr::AluRM { alu: op, sz, dst, mem } => enc_rm_mem(
            Seq::empty(),
            is64(sz),
            dst,
            mem,
            seq![(alu_base(op) + 3) as u8],
        ),
        Instr::AluRI { alu: op, sz, dst, imm } => enc_rr(
            Seq::empty(),
            is64(sz),
            alu_ext(op) as u8,
            dst,
            seq![0x81u8],
            false,
        ) + le_bytes(imm as int, 4),
        Instr::TestRR { sz, a, b } => enc_rr(Seq::empty(), is64(sz), b, a, seq![0x85u8], false),
        Instr::TestRI { sz, a, imm } => enc_rr(Seq::empty(), is64(sz), 0, a, seq![0xF7u8], false)
            + le_bytes(imm as int, 4),
        Instr::Neg { sz, r } => enc_rr(Seq::empty(), is64(sz), 3, r, seq![0xF7u8], false),
        Instr::Not { sz, r } => enc_rr(Seq::empty(), is64(sz), 2, r, seq![0xF7u8], false),
        Instr::ShiftImm { shift: op, sz, r, count } => enc_rr(
            Seq::empty(),
            is64(sz),
            shift_ext(op) as u8,
            r,
            seq![0xC1u8],
            false,
        ) + seq![count],
        Instr::ShiftCl { shift: op, sz, r } => enc_rr(
            Seq::empty(),
            is64(sz),
            shift_ext(op) as u8,
            r,
            seq![0xD3u8],
            false,
        ),
        Instr::ImulRR { sz, dst, src } => enc_rr(
            Seq::empty(),
            is64(sz),
            dst,
            src,
            seq![0x0Fu8, 0xAFu8],
            false,
        ),
        Instr::ImulRRI { sz, dst, src, imm } => enc_rr(
            Seq::empty(),
            is64(sz),
            dst,
            src,
            seq![0x69u8],
            false,
        ) + le_bytes(imm as int, 4),
        Instr::Jcc { cc, rel } => seq![0x0Fu8, (0x80 + cc as int) as u8] + le_bytes(rel as int, 4),
        Instr::Jmp { rel } => seq![0xE9u8] + le_bytes(rel as int, 4),
        Instr::Ret => seq![0xC3u8],
        Instr::Cmovcc { cc, sz, dst, src } => enc_rr(
            Seq::empty(),
            is64(sz),
            dst,
            src,
            seq![0x0Fu8, (0x40 + cc as int) as u8],
            false,
        ),
        Instr::Setcc { cc, dst } => enc_rr(
            Seq::empty(),
            false,
            0,
            dst,
            seq![0x0Fu8, (0x90 + cc as int) as u8],
            4 <= dst && dst < 8,
        ),
        Instr::FpArith { fop: op, dst, xsrc: src } => enc_xmm_src(
            seq![0xF2u8],
            false,
            dst,
            src,
            seq![0x0Fu8, fp_opcode(op) as u8],
        ),
        Instr::Sqrtsd { dst, xsrc: src } => enc_xmm_src(
            seq![0xF2u8],
            false,
            dst,
            src,
            seq![0x0Fu8, 0x51u8],
        ),
        Instr::Ucomisd { a, xsrc: src } => enc_xmm_src(
            seq![0x66u8],
            false,
            a,
            src,
            seq![0x0Fu8, 0x2Eu8],
        ),
        Instr::Cvtsi2sd { sz, dst, src } => enc_rr(
            seq![0xF2u8],
            is64(sz),
            dst,
            src,
            seq![0x0Fu8, 0x2Au8],
            false,
        ),
        Instr::Cvttsd2si { sz, dst, src } => enc_rr(
            seq![0xF2u8],
            is64(sz),
            dst,
            src,
            seq![0x0Fu8, 0x2Cu8],
            false,
        ),
        Instr::Cvtsd2si { sz, dst, src } => enc_rr(
            seq![0xF2u8],
            is64(sz),
            dst,
            src,
            seq![0x0Fu8, 0x2Du8],
            false,
        ),
        Instr::MovqToXmm { dst, src } => enc_rr(
            seq![0x66u8],
            true,
            dst,
            src,
            seq![0x0Fu8, 0x6Eu8],
            false,
        ),
        Instr::MovqFromXmm { dst, src } => enc_rr(
            seq![0x66u8],
            true,
            src,
            dst,
            seq![0x0Fu8, 0x7Eu8],
            false,
        ),
        Instr::MovsdLoad { dst, mem } => enc_rm_mem(
            seq![0xF2u8],
            false,
            dst,
            mem,
            seq![0x0Fu8, 0x10u8],
        ),
        Instr::MovsdStore { mem, src } => enc_rm_mem(
            seq![0xF2u8],
            false,
            src,
            mem,
            seq![0x0Fu8, 0x11u8],
        ),
    }
}

/// The length in bytes of the canonical encoding of `i`.
pub open spec fn instr_len(i: Instr) -> nat {
    encode(i).len()
}

/// `bytes` is the canonical encoding of `i`, and `i` is in the subset: the
/// only byte strings the validator accepts for one instruction.
pub open spec fn is_canonical_encoding(bytes: Seq<u8>, i: Instr) -> bool {
    valid_instr(i) && bytes == encode(i)
}

/// `bytes` begins with the canonical encoding of `i`.
pub open spec fn starts_with_encoding(bytes: Seq<u8>, i: Instr) -> bool {
    valid_instr(i) && encode(i).len() <= bytes.len() && bytes.subrange(0, encode(i).len() as int)
        == encode(i)
}


// ============================================================================
// Section: state
// ============================================================================
//
// The machine state and its accessors: registers, flags, RIP, XMM
// registers, memory.
//
// ACL2 sources (`tests/data/acl2-x86isa/`): `machine/state.lisp` and
// `machine/x86.lisp` for the state, `machine/register-readers-and-writers.lisp`
// for `rgfi`, `rr08`/`rr32`/`rr64`, `wr08`/`wr32`/`wr64`, `rgfi-size`,
// `!rgfi-size`, `xmmi-size`, `!xmmi-size`, `undef-flg`, `!flgi-undefined`
// and `write-user-rflags`, `machine/decoding-and-spec-utils.lisp` for
// `add-to-*ip`, `write-*ip` and the effective address, and
// `machine/linear-memory.lisp` for `rml-size` and `wml-size`.


/// The state the subset reads and writes.
pub struct State {
    /// The 16 general-purpose registers (`rgf`), `rax` to `r15` in the
    /// order of the instruction encoding (`rax rcx rdx rbx rsp rbp rsi rdi
    /// r8 ... r15`), each as an unsigned 64-bit value. (ACL2 stores them
    /// signed; `rr64` and `n64-to-i64` convert.)
    pub rgf: Seq<u64>,
    /// RIP. ACL2 keeps it as a signed 48-bit integer (`i48p`): only
    /// canonical addresses are ever stored.
    pub rip: int,
    /// RFLAGS (`rflags`, 32 bits). Only the bits `cf pf af zf sf of` are
    /// ever changed by the subset; the others (the always-one bit 1, `tf`,
    /// `if`, `df` ...) are carried through untouched.
    pub rflags: u32,
    /// ACL2's `undef` field: the seed of the next unknown value, consumed
    /// by `undef-read` each time an instruction leaves a flag undefined.
    pub undef: nat,
    /// The 16 XMM registers (`xmm`), low 128 bits of the vector registers.
    pub xmm: Seq<u128>,
    /// Memory: a partial map from linear address to byte. The addresses are
    /// signed integers, as in ACL2 (`(signed-byte 64)`); an address outside
    /// the domain is unmapped and any access to it faults.
    pub mem: Map<int, u8>,
}

/// `(canonical-address-p a)` in 64-bit mode: a signed 48-bit integer.
pub open spec fn canonical(a: int) -> bool {
    -p2(47) <= a && a < p2(47)
}

/// A well-formed state: 16 GPRs, 16 XMM registers, a canonical RIP, and
/// only canonical addresses mapped.
pub open spec fn wf(s: State) -> bool {
    s.rgf.len() == 16 && s.xmm.len() == 16 && canonical(s.rip) && (forall|a: int|
        s.mem.dom().contains(a) ==> #[trigger] canonical(a))
}

// ---------------------------------------------------------------------------
// General-purpose registers (register-readers-and-writers.lisp)
// ---------------------------------------------------------------------------

/// `(rr64 reg x86)`: the whole register, as an unsigned value.
pub open spec fn rr64(s: State, r: u8) -> int {
    s.rgf[r as int] as int
}

/// `(rr32 reg x86)`: `(n32 (rgfi reg x86))`.
pub open spec fn rr32(s: State, r: u8) -> int {
    loghead(32, rr64(s, r))
}

/// `(wr64 reg val x86)`.
pub open spec fn wr64(s: State, r: u8, v: int) -> State {
    State { rgf: s.rgf.update(r as int, loghead(64, v) as u64), ..s }
}

/// `(wr32 reg val x86)`: 32-bit operands generate a 32-bit result,
/// zero-extended to 64 bits.
pub open spec fn wr32(s: State, r: u8, v: int) -> State {
    wr64(s, r, loghead(32, v))
}

/// `(wr08 reg rex val x86)` as the subset uses it: the low byte of the
/// register is replaced and the other 56 bits are kept. (`wr08` writes `ah`
/// to `bh` for registers 4 to 7 when there is no `REX` byte; the canonical
/// encoding of `setcc` always has one for those registers, see
/// `encoding.rs`.)
pub open spec fn wr08(s: State, r: u8, v: int) -> State {
    let old = rr64(s, r);
    wr64(s, r, old - old % 256 + loghead(8, v))
}

/// `(rgfi-size nbytes reg rex x86)` for `nbytes` 4 or 8.
pub open spec fn rgfi_size(s: State, sz: Size, r: u8) -> int {
    match sz {
        Size::W32 => rr32(s, r),
        Size::W64 => rr64(s, r),
    }
}

/// `(!rgfi-size nbytes reg val rex x86)` for `nbytes` 4 or 8.
pub open spec fn set_rgfi_size(s: State, sz: Size, r: u8, v: int) -> State {
    match sz {
        Size::W32 => wr32(s, r, v),
        Size::W64 => wr64(s, r, v),
    }
}

// ---------------------------------------------------------------------------
// XMM registers
// ---------------------------------------------------------------------------

/// `(xmmi-size 8 index x86)`: the low 64 bits.
pub open spec fn xmmi_size8(s: State, x: u8) -> int {
    loghead(64, s.xmm[x as int] as int)
}

/// `(!xmmi-size 8 index val x86)`: the low 64 bits are replaced, the rest of
/// the register is kept.
pub open spec fn set_xmmi_size8(s: State, x: u8, v: int) -> State {
    let old = s.xmm[x as int] as int;
    State { xmm: s.xmm.update(x as int, (old - old % p2(64) + loghead(64, v)) as u128), ..s }
}

/// `(!xmmi-size 16 index val x86)`: the whole 128-bit register.
pub open spec fn set_xmmi_size16(s: State, x: u8, v: int) -> State {
    State { xmm: s.xmm.update(x as int, loghead(128, v) as u128), ..s }
}

// ---------------------------------------------------------------------------
// Flags
// ---------------------------------------------------------------------------

/// The position of `cf` in `rflagsBits` (utils/structures.lisp).
pub open spec fn cf_bit() -> nat {
    0
}

/// The position of `pf`.
pub open spec fn pf_bit() -> nat {
    2
}

/// The position of `af`.
pub open spec fn af_bit() -> nat {
    4
}

/// The position of `zf`.
pub open spec fn zf_bit() -> nat {
    6
}

/// The position of `sf`.
pub open spec fn sf_bit() -> nat {
    7
}

/// The position of `of`.
pub open spec fn of_bit() -> nat {
    11
}

/// `(flgi :xx x86)`.
pub open spec fn flgi(s: State, k: nat) -> int {
    bit(s.rflags as int, k)
}

/// `(!flgi :xx val x86)`.
pub open spec fn set_flgi(s: State, k: nat, v: int) -> State {
    State { rflags: set_bit32(s.rflags, k, v), ..s }
}

/// One step of `write-user-rflags`: the flag at position `k` is taken from
/// `user_flags_vector`, or, when `undefined_mask` marks it, is
/// `(!flgi-undefined)`: `(n01 (create-undef undef))` and `undef` advances.
/// `create_undef` is ACL2's `create-undef`, an unspecified function from
/// seed to value: the semantics holds for every such function.
pub open spec fn write_flag_or_undefined(
    create_undef: spec_fn(nat) -> nat,
    s: State,
    k: nat,
    user_flags_vector: u32,
    undefined_mask: u32,
) -> State {
    if bit(undefined_mask as int, k) == 1 {
        State {
            rflags: set_bit32(s.rflags, k, (create_undef(s.undef) % 2) as int),
            undef: s.undef + 1,
            ..s
        }
    } else {
        set_flgi(s, k, bit(user_flags_vector as int, k))
    }
}

/// `(write-user-rflags user-flags-vector undefined-mask x86)`: the six user
/// flags, in the order `cf pf af zf sf of`.
pub open spec fn write_user_rflags(
    create_undef: spec_fn(nat) -> nat,
    s: State,
    user_flags_vector: u32,
    undefined_mask: u32,
) -> State {
    let s1 = write_flag_or_undefined(create_undef, s, cf_bit(), user_flags_vector, undefined_mask);
    let s2 = write_flag_or_undefined(create_undef, s1, pf_bit(), user_flags_vector, undefined_mask);
    let s3 = write_flag_or_undefined(create_undef, s2, af_bit(), user_flags_vector, undefined_mask);
    let s4 = write_flag_or_undefined(create_undef, s3, zf_bit(), user_flags_vector, undefined_mask);
    let s5 = write_flag_or_undefined(create_undef, s4, sf_bit(), user_flags_vector, undefined_mask);
    write_flag_or_undefined(create_undef, s5, of_bit(), user_flags_vector, undefined_mask)
}

// ---------------------------------------------------------------------------
// RIP
// ---------------------------------------------------------------------------

/// `(add-to-*ip proc-mode *ip delta x86)` in 64-bit mode: the sum, or `None`
/// (ACL2's error flag, which stops the model) when it is not canonical.
pub open spec fn add_to_ip(ip: int, delta: int) -> Option<int> {
    if canonical(ip + delta) {
        Some(ip + delta)
    } else {
        None
    }
}

/// `(write-*ip proc-mode *ip x86)` in 64-bit mode.
pub open spec fn write_ip(s: State, ip: int) -> State {
    State { rip: ip, ..s }
}

// ---------------------------------------------------------------------------
// Memory (linear-memory.lisp: rml-size, wml-size)
// ---------------------------------------------------------------------------

/// The effective address of a memory operand, `x86-effective-addr-32/64` with
/// `mod = 2` and a SIB byte (`x86-effective-addr-from-sib`): base, plus the
/// index shifted left by `scale`, plus the displacement, taken modulo 2^64
/// and read as a signed 64-bit address (`(n64-to-i64 (n64 dst-base))`).
pub open spec fn eff_addr(s: State, m: Mem) -> int {
    let base = rr64(s, m.base);
    let scaled_index = match m.index {
        None => 0,
        Some(ix) => rr64(s, ix.reg) * p2(ix.scale as nat),
    };
    logext(64, base + scaled_index + m.disp as int)
}

/// Reads `n` bytes at `addr`, little-endian (`rml-size`, `combine-bytes`):
/// `None` if any of the bytes is not mapped (a fault).
pub open spec fn read_mem(m: Map<int, u8>, addr: int, n: nat) -> Option<int>
    decreases n,
{
    if n == 0 {
        Some(0)
    } else if !m.dom().contains(addr) {
        None
    } else {
        match read_mem(m, addr + 1, (n - 1) as nat) {
            None => None,
            Some(rest) => Some(m[addr] as int + 256 * rest),
        }
    }
}

/// Writes the low `n` bytes of `v` at `addr`, little-endian (`wml-size`):
/// `None` if any of the bytes is not mapped (a fault).
pub open spec fn write_mem(m: Map<int, u8>, addr: int, n: nat, v: int) -> Option<Map<int, u8>>
    decreases n,
{
    if n == 0 {
        Some(m)
    } else if !m.dom().contains(addr) {
        None
    } else {
        match write_mem(m, addr + 1, (n - 1) as nat, v / 256) {
            None => None,
            Some(m2) => Some(m2.insert(addr, (v % 256) as u8)),
        }
    }
}


// ============================================================================
// Section: semantics
// ============================================================================
//
// The semantics of each instruction of the subset: what one instruction does
// to the [`State`].
//
// Transcribed from the ACL2 `x86isa` model (`tests/data/acl2-x86isa/`). Each
// function cites the ACL2 book and function it comes from, as
// `file.lisp: function-name`; paths are relative to `machine/` and
// `machine/instructions/`. Where ACL2 splits an instruction into an
// operand-fetching `def-inst` and a `*-spec` function that computes the
// result and the flags, so do we: the `def-inst` is [`effect`] (and
// [`step`]), the `*-spec` functions are the `gpr_*_spec`, `*_spec`
// functions below.


// ===========================================================================
// rflags-spec.lisp: the flag functions
// ===========================================================================

/// `cf-spec8/16/32/64`: carry out of the top bit of an `n`-bit addition
/// (`general-cf-spec-fn`).
pub open spec fn cf_spec(n: nat, raw_result: int) -> int {
    bool_to_bit(!unsigned_byte_p(n, raw_result))
}

/// `of-spec8/16/32/64`: the signed result does not fit in `n` bits.
pub open spec fn of_spec(n: nat, signed_raw_result: int) -> int {
    bool_to_bit(!signed_byte_p(n, signed_raw_result))
}

/// `zf-spec`.
pub open spec fn zf_spec(result: int) -> int {
    if result == 0 {
        1
    } else {
        0
    }
}

/// `pf-spec8/16/32/64`: 1 when the low byte of the result has an even number
/// of one bits.
pub open spec fn pf_spec(result: int) -> int {
    bool_to_bit(logcount(loghead(8, result) as nat) % 2 == 0)
}

/// `sf-spec8/16/32/64`: the top bit of the `n`-bit result.
pub open spec fn sf_spec(n: nat, result: int) -> int {
    bit(result, (n - 1) as nat)
}

/// `add-af-spec8/16/32/64`: carry out of bit 3.
pub open spec fn add_af_spec(dst: int, src: int) -> int {
    bool_to_bit(dst % 16 + src % 16 > 15)
}

/// `sub-af-spec8/16/32/64`: borrow from bit 4.
pub open spec fn sub_af_spec(dst: int, src: int) -> int {
    bool_to_bit(dst % 16 - src % 16 < 0)
}

/// The fields a `change-rflagsBits` names: `None` leaves the flag as it was.
pub struct FlagUpd {
    /// `:cf`
    pub cf: Option<int>,
    /// `:pf`
    pub pf: Option<int>,
    /// `:af`
    pub af: Option<int>,
    /// `:zf`
    pub zf: Option<int>,
    /// `:sf`
    pub sf: Option<int>,
    /// `:of`
    pub of: Option<int>,
}

/// Sets bit `k` to `v` when there is one.
pub open spec fn opt_set_bit(w: u32, k: nat, v: Option<int>) -> u32 {
    match v {
        Some(x) => set_bit32(w, k, x),
        None => w,
    }
}

/// `(change-rflagsBits input-rflags :cf cf ...)`.
pub open spec fn change_rflags(input_rflags: u32, f: FlagUpd) -> u32 {
    let w1 = opt_set_bit(input_rflags, cf_bit(), f.cf);
    let w2 = opt_set_bit(w1, pf_bit(), f.pf);
    let w3 = opt_set_bit(w2, af_bit(), f.af);
    let w4 = opt_set_bit(w3, zf_bit(), f.zf);
    let w5 = opt_set_bit(w4, sf_bit(), f.sf);
    opt_set_bit(w5, of_bit(), f.of)
}

/// The three results of a `*-spec` function: `(mv result output-rflags
/// undefined-flags)`. `undef` is a mask of the flags that are undefined
/// (`(!rflagsBits->af 1 0)` and so on).
pub struct SpecOut {
    /// The result, an unsigned `n`-bit integer.
    pub result: int,
    /// The output rflags.
    pub rflags: u32,
    /// The undefined-flags mask.
    pub undef: u32,
}

/// `(!rflagsBits->cf 1 0)`.
pub open spec fn mask_cf() -> u32 {
    0x1
}

/// `(!rflagsBits->af 1 0)`.
pub open spec fn mask_af() -> u32 {
    0x10
}

/// `(!rflagsBits->of 1 0)`.
pub open spec fn mask_of() -> u32 {
    0x800
}

/// `(!rflagsBits->pf 1 0)`.
pub open spec fn mask_pf() -> u32 {
    0x4
}

/// `(!rflagsBits->zf 1 0)`.
pub open spec fn mask_zf() -> u32 {
    0x40
}

/// `(!rflagsBits->sf 1 0)`.
pub open spec fn mask_sf() -> u32 {
    0x80
}

// ===========================================================================
// add-spec.lisp, sub-spec.lisp, and-spec.lisp, or-spec.lisp, xor-spec.lisp
// ===========================================================================

/// `gpr-add-spec-4`, `gpr-add-spec-8` (add-spec.lisp: `gpr-add-spec-gen-fn`)
/// for `n = 32` or `64`.
pub open spec fn gpr_add_spec(n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    let dst = loghead(n, dst);
    let src = loghead(n, src);
    let raw_result = dst + src;
    let signed_raw_result = logext(n, dst) + logext(n, src);
    let result = loghead(n, raw_result);
    let cf = cf_spec(n, raw_result);
    let pf = pf_spec(result);
    let af = add_af_spec(dst, src);
    let zf = zf_spec(result);
    let sf = sf_spec(n, result);
    let of = of_spec(n, signed_raw_result);
    SpecOut {
        result,
        rflags: change_rflags(
            input_rflags,
            FlagUpd {
                cf: Some(cf),
                pf: Some(pf),
                af: Some(af),
                zf: Some(zf),
                sf: Some(sf),
                of: Some(of),
            },
        ),
        // No undefined flags.
        undef: 0,
    }
}

/// `gpr-sub-spec-4`, `gpr-sub-spec-8` (sub-spec.lisp: `gpr-sub-spec-gen-fn`).
pub open spec fn gpr_sub_spec(n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    let dst = loghead(n, dst);
    let src = loghead(n, src);
    let signed_raw_result = logext(n, dst) - logext(n, src);
    let result = loghead(n, signed_raw_result);
    let cf = bool_to_bit(dst < src);
    let pf = pf_spec(result);
    let af = sub_af_spec(dst, src);
    let zf = zf_spec(result);
    let sf = sf_spec(n, result);
    let of = of_spec(n, signed_raw_result);
    SpecOut {
        result,
        rflags: change_rflags(
            input_rflags,
            FlagUpd {
                cf: Some(cf),
                pf: Some(pf),
                af: Some(af),
                zf: Some(zf),
                sf: Some(sf),
                of: Some(of),
            },
        ),
        undef: 0,
    }
}

/// The flags of `and`, `or`, `xor`: `cf` and `of` cleared, `pf zf sf` of the
/// result, `af` undefined (and-spec.lisp, or-spec.lisp, xor-spec.lisp:
/// `(undefined-flags (!rflagsBits->af 1 0))`).
pub open spec fn logic_flags(n: nat, result: int, input_rflags: u32) -> SpecOut {
    SpecOut {
        result,
        rflags: change_rflags(
            input_rflags,
            FlagUpd {
                cf: Some(0),
                pf: Some(pf_spec(result)),
                af: None,
                zf: Some(zf_spec(result)),
                sf: Some(sf_spec(n, result)),
                of: Some(0),
            },
        ),
        undef: mask_af(),
    }
}

/// `gpr-and-spec-4`, `gpr-and-spec-8` (and-spec.lisp).
pub open spec fn gpr_and_spec(n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    let dst = loghead(n, dst);
    let src = loghead(n, src);
    logic_flags(n, ((dst as u64) & (src as u64)) as int, input_rflags)
}

/// `gpr-or-spec-4`, `gpr-or-spec-8` (or-spec.lisp).
pub open spec fn gpr_or_spec(n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    let dst = loghead(n, dst);
    let src = loghead(n, src);
    logic_flags(n, ((dst as u64) | (src as u64)) as int, input_rflags)
}

/// `gpr-xor-spec-4`, `gpr-xor-spec-8` (xor-spec.lisp).
pub open spec fn gpr_xor_spec(n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    let dst = loghead(n, dst);
    let src = loghead(n, src);
    logic_flags(n, ((dst as u64) ^ (src as u64)) as int, input_rflags)
}

/// `gpr-arith/logic-spec-4`, `gpr-arith/logic-spec-8`
/// (arith-and-logic-spec.lisp), for the operations of the subset. `test` is
/// `and` and `cmp` is `sub`, as there.
pub open spec fn gpr_arith_logic_spec(
    n: nat,
    op: AluOp,
    dst: int,
    src: int,
    input_rflags: u32,
) -> SpecOut {
    match op {
        AluOp::Add => gpr_add_spec(n, dst, src, input_rflags),
        AluOp::Or => gpr_or_spec(n, dst, src, input_rflags),
        AluOp::And => gpr_and_spec(n, dst, src, input_rflags),
        AluOp::Sub => gpr_sub_spec(n, dst, src, input_rflags),
        AluOp::Xor => gpr_xor_spec(n, dst, src, input_rflags),
        // We will re-use the SUB specification here.
        AluOp::Cmp => gpr_sub_spec(n, dst, src, input_rflags),
    }
}

// ===========================================================================
// shifts-spec.lisp: sal/shl-spec, shr-spec, sar-spec
// ===========================================================================

/// The flags every non-trivial shift sets from its result: `pf zf sf`.
pub open spec fn shift_pzs(n: nat, result: int) -> FlagUpd {
    FlagUpd {
        cf: None,
        pf: Some(pf_spec(result)),
        af: None,
        zf: Some(zf_spec(result)),
        sf: Some(sf_spec(n, result)),
        of: None,
    }
}

/// `sal/shl-spec-32`, `sal/shl-spec-64` (shifts-spec.lisp:
/// `sal/shl-spec-gen`). `src` is the count, already masked by the caller.
pub open spec fn sal_shl_spec(n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    let dst = loghead(n, dst);
    let src = loghead(6, src);
    let raw_result = dst * p2(src as nat);
    let result = loghead(n, raw_result);
    if src == 0 {
        SpecOut { result, rflags: input_rflags, undef: 0 }
    } else if src == 1 {
        let cf = bit(dst, (n - 1) as nat);
        let of = (cf + bit(result, (n - 1) as nat)) % 2;
        SpecOut {
            result,
            rflags: change_rflags(
                input_rflags,
                FlagUpd { cf: Some(cf), of: Some(of), ..shift_pzs(n, result) },
            ),
            undef: mask_af(),
        }
    } else if n <= src {
        // CF is undefined.
        SpecOut {
            result,
            rflags: change_rflags(input_rflags, shift_pzs(n, result)),
            undef: mask_cf() | mask_af() | mask_of(),
        }
    } else {
        let cf = bit(dst, (n - src) as nat);
        SpecOut {
            result,
            rflags: change_rflags(
                input_rflags,
                FlagUpd { cf: Some(cf), ..shift_pzs(n, result) },
            ),
            undef: mask_af() | mask_of(),
        }
    }
}

/// `shr-spec-32`, `shr-spec-64` (shifts-spec.lisp: `shr-spec-gen`).
pub open spec fn shr_spec(n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    let dst = loghead(n, dst);
    let src = loghead(6, src);
    let result = loghead(n, dst / p2(src as nat));
    if src == 0 {
        SpecOut { result, rflags: input_rflags, undef: 0 }
    } else if src == 1 {
        let cf = bit(dst, 0);
        let of = bit(dst, (n - 1) as nat);
        SpecOut {
            result,
            rflags: change_rflags(
                input_rflags,
                FlagUpd { cf: Some(cf), of: Some(of), ..shift_pzs(n, result) },
            ),
            undef: mask_af(),
        }
    } else if n <= src {
        SpecOut {
            result,
            rflags: change_rflags(input_rflags, shift_pzs(n, result)),
            undef: mask_cf() | mask_af() | mask_of(),
        }
    } else {
        let cf = bit(dst, (src - 1) as nat);
        SpecOut {
            result,
            rflags: change_rflags(
                input_rflags,
                FlagUpd { cf: Some(cf), ..shift_pzs(n, result) },
            ),
            undef: mask_af() | mask_of(),
        }
    }
}

/// `sar-spec-32`, `sar-spec-64` (shifts-spec.lisp: `sar-spec-gen`).
pub open spec fn sar_spec(n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    let dst = loghead(n, dst);
    let src = loghead(6, src);
    // raw-result: the logical shift, or, when the sign bit is set, the
    // arithmetic one: (loghead n (ash (logext n dst) (- src))).
    let raw_result = if bit(dst, (n - 1) as nat) == 1 {
        loghead(n, logext(n, dst) / p2(src as nat))
    } else {
        dst / p2(src as nat)
    };
    let result = loghead(n, raw_result);
    if src == 0 {
        SpecOut { result, rflags: input_rflags, undef: 0 }
    } else if src == 1 {
        let cf = bit(dst, 0);
        SpecOut {
            result,
            rflags: change_rflags(
                input_rflags,
                FlagUpd { cf: Some(cf), of: Some(0), ..shift_pzs(n, result) },
            ),
            undef: mask_af(),
        }
    } else {
        let cf = if n <= src {
            bit(dst, (n - 1) as nat)
        } else {
            bit(dst, (src - 1) as nat)
        };
        SpecOut {
            result,
            rflags: change_rflags(
                input_rflags,
                FlagUpd { cf: Some(cf), ..shift_pzs(n, result) },
            ),
            undef: mask_af() | mask_of(),
        }
    }
}

/// `sal/shl-spec`, `shr-spec`, `sar-spec` (the dispatchers on the size).
pub open spec fn shift_spec(op: ShiftOp, n: nat, dst: int, src: int, input_rflags: u32) -> SpecOut {
    match op {
        ShiftOp::Shl => sal_shl_spec(n, dst, src, input_rflags),
        ShiftOp::Shr => shr_spec(n, dst, src, input_rflags),
        ShiftOp::Sar => sar_spec(n, dst, src, input_rflags),
    }
}

// ===========================================================================
// multiply-spec.lisp: imul-spec
// ===========================================================================

/// `imul-spec-32`, `imul-spec-64` (multiply-spec.lisp: `imul-spec-gen`):
/// `(mv product-high product-low product cf-and-of)`; only the low half and
/// the flag are used by the subset.
pub open spec fn imul_spec(n: nat, dst: int, src: int) -> (int, int) {
    let dst_int = logext(n, dst);
    let src_int = logext(n, src);
    let product_int = dst_int * src_int;
    let product = loghead(2 * n, product_int);
    let product_low = loghead(n, product);
    let product_low_int = logext(n, product_low);
    let cf_and_of = bool_to_bit(product_low_int != product_int);
    (product_low, cf_and_of)
}

// ===========================================================================
// conditional.lisp: jcc/cmovcc/setcc-spec
// ===========================================================================

/// `jcc/cmovcc/setcc-spec`: whether the condition `cc` (the low nibble of
/// the opcode) holds.
pub open spec fn jcc_cmovcc_setcc_spec(s: State, cc: u8) -> bool {
    match cc {
        0x0 => flgi(s, of_bit()) == 1,
        0x1 => flgi(s, of_bit()) == 0,
        0x2 => flgi(s, cf_bit()) == 1,
        0x3 => flgi(s, cf_bit()) == 0,
        0x4 => flgi(s, zf_bit()) == 1,
        0x5 => flgi(s, zf_bit()) == 0,
        0x6 => flgi(s, cf_bit()) == 1 || flgi(s, zf_bit()) == 1,
        0x7 => flgi(s, cf_bit()) == 0 && flgi(s, zf_bit()) == 0,
        0x8 => flgi(s, sf_bit()) == 1,
        0x9 => flgi(s, sf_bit()) == 0,
        0xA => flgi(s, pf_bit()) == 1,
        0xB => flgi(s, pf_bit()) == 0,
        0xC => flgi(s, sf_bit()) != flgi(s, of_bit()),
        0xD => flgi(s, sf_bit()) == flgi(s, of_bit()),
        0xE => flgi(s, zf_bit()) == 1 || flgi(s, sf_bit()) != flgi(s, of_bit()),
        _ => flgi(s, zf_bit()) == 0 && flgi(s, sf_bit()) == flgi(s, of_bit()),
    }
}

// ===========================================================================
// The instructions
// ===========================================================================

/// Read the memory operand `m` (`x86-operand-from-modr/m-and-sib-bytes`
/// with `mod = 2`): `None` on a fault.
pub open spec fn read_operand_mem(s: State, sz: Size, m: Mem) -> Option<int> {
    read_mem(s.mem, eff_addr(s, m), nbytes(sz))
}

/// `x86-operand-from-modr/m-and-sib-bytes` with `*xmm-access*` and
/// `operand-size` 8 for `xmm2/m64`.
pub open spec fn read_xmm_src(s: State, src: XmmSrc) -> Option<int> {
    match src {
        XmmSrc::Reg(r) => Some(xmmi_size8(s, r)),
        XmmSrc::Mem(m) => read_mem(s.mem, eff_addr(s, m), 8),
    }
}

/// `x86-operand-to-reg/mem` for a memory destination: the new memory, or
/// `None` on a fault.
pub open spec fn store_mem(s: State, m: Mem, sz: Size, v: int) -> Option<State> {
    match write_mem(s.mem, eff_addr(s, m), nbytes(sz), v) {
        Some(mem2) => Some(State { mem: mem2, ..s }),
        None => None,
    }
}

/// The part of an instruction's semantics that is not the RIP update: the
/// register, flag and memory effects, for every instruction but `jcc`, `jmp`
/// and `ret`. `None` is a fault (an unmapped access): ACL2 stops with a
/// `fault` or `ms` value and promises nothing about the state after it.
/// `create_undef` is ACL2's `create-undef` (see [`State::undef`]).
pub open spec fn effect(create_undef: spec_fn(nat) -> nat, s: State, i: Instr) -> Option<State> {
    match i {
        // x86-mov-Op/En-MR (move.lisp), opcode 89, register direct
        Instr::MovRR { sz, dst, src } => Some(
            set_rgfi_size(s, sz, dst, rgfi_size(s, sz, src)),
        ),
        // x86-mov-Op/En-RM (move.lisp), opcode 8B
        Instr::MovLoad { sz, dst, mem } => match read_operand_mem(s, sz, mem) {
            Some(v) => Some(set_rgfi_size(s, sz, dst, v)),
            None => None,
        },
        // x86-mov-Op/En-MR (move.lisp), opcode 89, memory destination
        Instr::MovStore { sz, mem, src } => store_mem(s, mem, sz, rgfi_size(s, sz, src)),
        // x86-mov-Op/En-OI (move.lisp), opcode B8+r, operand-size 4
        Instr::MovImm32 { dst, imm_u32: imm } => Some(wr32(s, dst, imm as int)),
        // x86-mov-Op/En-MI (move.lisp), opcode C7, reg/mem-size 8:
        // (n64 (n32-to-i32 imm))
        Instr::MovImm32S { dst, imm } => Some(wr64(s, dst, imm as int)),
        // x86-mov-Op/En-OI (move.lisp), opcode B8+r, operand-size 8
        Instr::MovImm64 { dst, imm_u64: imm } => Some(wr64(s, dst, imm as int)),
        // x86-add/xadd/adc/sub/sbb/or/and/xor/cmp/test-E-G
        // (arith-and-logic.lisp), mod = 3: E is dst, G is src.
        Instr::AluRR { alu: op, sz, dst, src } => {
            let r = gpr_arith_logic_spec(
                nbits(sz),
                op,
                rgfi_size(s, sz, dst),
                rgfi_size(s, sz, src),
                s.rflags,
            );
            let s1 = if op is Cmp {
                s
            } else {
                set_rgfi_size(s, sz, dst, r.result)
            };
            Some(write_user_rflags(create_undef, s1, r.rflags, r.undef))
        },
        // x86-add/adc/sub/sbb/or/and/xor/cmp-G-E (arith-and-logic.lisp):
        // G is dst, E is the memory operand.
        Instr::AluRM { alu: op, sz, dst, mem } => match read_operand_mem(s, sz, mem) {
            Some(e) => {
                let r = gpr_arith_logic_spec(
                    nbits(sz),
                    op,
                    rgfi_size(s, sz, dst),
                    e,
                    s.rflags,
                );
                let s1 = if op is Cmp {
                    s
                } else {
                    set_rgfi_size(s, sz, dst, r.result)
                };
                Some(write_user_rflags(create_undef, s1, r.rflags, r.undef))
            },
            None => None,
        },
        // x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I (arith-and-logic.lisp),
        // mod = 3, imm-size 4: imm is (loghead (ash E-size 3) (logext 32 imm)).
        Instr::AluRI { alu: op, sz, dst, imm } => {
            let r = gpr_arith_logic_spec(
                nbits(sz),
                op,
                rgfi_size(s, sz, dst),
                loghead(nbits(sz), imm as int),
                s.rflags,
            );
            let s1 = if op is Cmp {
                s
            } else {
                set_rgfi_size(s, sz, dst, r.result)
            };
            Some(write_user_rflags(create_undef, s1, r.rflags, r.undef))
        },
        // x86-add/xadd/adc/sub/sbb/or/and/xor/cmp/test-E-G, opcode 85,
        // *OP-TEST*: gpr-arith/logic-spec with E, G; no result is written.
        Instr::TestRR { sz, a, b } => {
            let r = gpr_and_spec(nbits(sz), rgfi_size(s, sz, a), rgfi_size(s, sz, b), s.rflags);
            Some(write_user_rflags(create_undef, s, r.rflags, r.undef))
        },
        // x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I, opcode F7 /0
        Instr::TestRI { sz, a, imm } => {
            let r = gpr_and_spec(
                nbits(sz),
                rgfi_size(s, sz, a),
                loghead(nbits(sz), imm as int),
                s.rflags,
            );
            Some(write_user_rflags(create_undef, s, r.rflags, r.undef))
        },
        // x86-not/neg-F6-F7 (arith-and-logic.lisp), reg 3: the flags of
        // (gpr-arith/logic-spec size *OP-SUB* 0 r/mem), with CF special.
        Instr::Neg { sz, r } => {
            let v = rgfi_size(s, sz, r);
            let o = gpr_sub_spec(nbits(sz), 0, v, s.rflags);
            // (cf (if (equal 0 r/mem) 0 1))
            let flags = set_bit32(o.rflags, cf_bit(), if v == 0 {
                0
            } else {
                1
            });
            let s1 = write_user_rflags(create_undef, s, flags, o.undef);
            Some(set_rgfi_size(s1, sz, r, o.result))
        },
        // x86-not/neg-F6-F7, reg 2: (trunc r/mem-size (lognot r/mem)); the
        // flags are not written.
        Instr::Not { sz, r } => {
            let v = rgfi_size(s, sz, r);
            Some(set_rgfi_size(s, sz, r, p2(nbits(sz)) - 1 - v))
        },
        // x86-sal/sar/shl/shr/rcl/rcr/rol/ror (rotate-and-shift.lisp),
        // opcode C1: shift/rotate-by is the immediate byte masked with
        // countMask (#x3F for REX.W, #x1F otherwise).
        Instr::ShiftImm { shift: op, sz, r, count } => {
            let cnt = shift_count(sz, count as int);
            let o = shift_spec(op, nbits(sz), rgfi_size(s, sz, r), cnt, s.rflags);
            let s1 = write_user_rflags(create_undef, s, o.rflags, o.undef);
            Some(set_rgfi_size(s1, sz, r, o.result))
        },
        // same, opcode D3: shift/rotate-by is (rr08 *rcx* rex-byte x86)
        Instr::ShiftCl { shift: op, sz, r } => {
            let cnt = shift_count(sz, loghead(8, rr64(s, 1)));
            let o = shift_spec(op, nbits(sz), rgfi_size(s, sz, r), cnt, s.rflags);
            let s1 = write_user_rflags(create_undef, s, o.rflags, o.undef);
            Some(set_rgfi_size(s1, sz, r, o.result))
        },
        // x86-imul-Op/En-RM (multiply.lisp), opcode 0F AF
        Instr::ImulRR { sz, dst, src } => {
            let (low, cf_and_of) = imul_spec(nbits(sz), rgfi_size(s, sz, src), rgfi_size(s, sz, dst));
            Some(imul_flags(create_undef, set_rgfi_size(s, sz, dst, low), cf_and_of))
        },
        // x86-imul-Op/En-RMI (multiply.lisp), opcode 69:
        // (loghead (* 8 reg/mem-size) (logext (* 8 imm-size) imm))
        Instr::ImulRRI { sz, dst, src, imm } => {
            let (low, cf_and_of) = imul_spec(
                nbits(sz),
                rgfi_size(s, sz, src),
                loghead(nbits(sz), imm as int),
            );
            Some(imul_flags(create_undef, set_rgfi_size(s, sz, dst, low), cf_and_of))
        },
        // x86-cmovcc (conditional.lisp): the source is read (and may fault)
        // whether or not the condition holds; with a 32-bit operand the
        // destination is zero-extended in either case.
        Instr::Cmovcc { cc, sz, dst, src } => {
            let v = rgfi_size(s, sz, src);
            if jcc_cmovcc_setcc_spec(s, cc) {
                Some(set_rgfi_size(s, sz, dst, v))
            } else if sz is W32 {
                Some(set_rgfi_size(s, sz, dst, rgfi_size(s, sz, dst)))
            } else {
                Some(s)
            }
        },
        // x86-setcc (conditional.lisp): (x86-operand-to-reg/mem ... 1 val ...)
        Instr::Setcc { cc, dst } => Some(
            wr08(s, dst, if jcc_cmovcc_setcc_spec(s, cc) {
                1
            } else {
                0
            }),
        ),
        // x86-adds?/subs?/muls?/divs?/maxs?/mins?-Op/En-RM
        // (fp/arithmetic.lisp), sp/dp = *OP-DP*: the result is written to
        // the low 8 bytes (!xmmi-size 8 ...).
        Instr::FpArith { fop: op, dst, xsrc: src } => match read_xmm_src(s, src) {
            Some(b) => Some(
                set_xmmi_size8(
                    s,
                    dst,
                    dp_sse_add_sub_mul_div(op, xmmi_size8(s, dst) as u64, b as u64) as int,
                ),
            ),
            None => None,
        },
        // x86-sqrts?-Op/En-RM (fp/arithmetic.lisp)
        Instr::Sqrtsd { dst, xsrc: src } => match read_xmm_src(s, src) {
            Some(b) => Some(set_xmmi_size8(s, dst, dp_sse_sqrt(b as u64) as int)),
            None => None,
        },
        // x86-comis?/ucomis?-Op/En-RM (fp/logical.lisp, not vendored):
        // result 0, 1, 7 or 4 sets cf, pf, zf, and clears af, sf, of.
        Instr::Ucomisd { a, xsrc: src } => match read_xmm_src(s, src) {
            Some(b) => {
                let result = dp_sse_cmp_ucomi(xmmi_size8(s, a) as u64, b as u64);
                Some(ucomi_flags(s, result))
            },
            None => None,
        },
        // x86-cvtsi2s?-Op/En-RM (fp/convert.lisp): the integer is
        // (n32-to-i32 reg/mem) or (n64-to-i64 reg/mem).
        Instr::Cvtsi2sd { sz, dst, src } => {
            let v = logext(nbits(sz), rgfi_size(s, sz, src));
            Some(set_xmmi_size8(s, dst, dp_sse_cvt_int_to_fp(v) as int))
        },
        // x86-cvts?2si/cvtts?2si-Op/En-RM (fp/convert.lisp), trunc = t
        Instr::Cvttsd2si { sz, dst, src } => Some(
            set_rgfi_size(s, sz, dst, dp_sse_cvt_fp_to_int(nbytes(sz), xmmi_size8(s, src) as u64, true)),
        ),
        // same, trunc = nil
        Instr::Cvtsd2si { sz, dst, src } => Some(
            set_rgfi_size(s, sz, dst, dp_sse_cvt_fp_to_int(nbytes(sz), xmmi_size8(s, src) as u64, false)),
        ),
        // x86-movd/movq-to-xmm (move-sse.lisp), operand-size 8:
        // (!xmmi-size 16 ...)
        Instr::MovqToXmm { dst, src } => Some(set_xmmi_size16(s, dst, rr64(s, src))),
        // x86-movd/movq-from-xmm (move-sse.lisp), operand-size 8
        Instr::MovqFromXmm { dst, src } => Some(wr64(s, dst, xmmi_size8(s, src))),
        // x86-movss/movsd-Op/En-RM (move-sse.lisp), memory source:
        // operand-size 16 for the write (zero-extending)
        Instr::MovsdLoad { dst, mem } => match read_mem(s.mem, eff_addr(s, mem), 8) {
            Some(v) => Some(set_xmmi_size16(s, dst, v)),
            None => None,
        },
        // x86-movss/movsd-Op/En-MR (move-sse.lisp), memory destination
        Instr::MovsdStore { mem, src } => store_mem(s, mem, Size::W64, xmmi_size8(s, src)),
        // jcc, jmp, ret have no register or memory effect of this kind.
        Instr::Jcc { cc, rel } => Some(s),
        Instr::Jmp { rel } => Some(s),
        Instr::Ret => Some(s),
    }
}

/// `countMask` of `x86-sal/sar/shl/shr/rcl/rcr/rol/ror`: `#x3F` if the
/// operand size is 8 (REX.W), `#x1F` otherwise.
pub open spec fn shift_count(sz: Size, raw: int) -> int {
    match sz {
        Size::W64 => loghead(6, raw),
        Size::W32 => loghead(5, raw),
    }
}

/// The flags of `imul` (`x86-imul-Op/En-RM`, `-RMI`): `cf` and `of` take
/// `cf-and-of`, `pf af zf sf` are undefined (`!flgi-undefined`, in that
/// order).
pub open spec fn imul_flags(
    create_undef: spec_fn(nat) -> nat,
    s: State,
    cf_and_of: int,
) -> State {
    let flags = change_rflags(
        s.rflags,
        FlagUpd { cf: Some(cf_and_of), pf: None, af: None, zf: None, sf: None, of: Some(cf_and_of) },
    );
    write_user_rflags(create_undef, s, flags, mask_pf() | mask_af() | mask_zf() | mask_sf())
}

/// The flags of `ucomisd` from `dp-sse-cmp`'s result (fp/logical.lisp,
/// `x86-comis?/ucomis?-Op/En-RM`): 0 clears `cf pf zf`, 1 sets `cf`, 7 sets
/// all three, 4 sets `zf`; `af`, `sf` and `of` are cleared in every case.
pub open spec fn ucomi_flags(s: State, result: int) -> State {
    let cf = if result == 1 || result == 7 {
        1int
    } else {
        0int
    };
    let pf = if result == 7 {
        1int
    } else {
        0int
    };
    let zf = if result == 7 || result == 4 {
        1int
    } else {
        0int
    };
    State {
        rflags: change_rflags(
            s.rflags,
            FlagUpd {
                cf: Some(cf),
                pf: Some(pf),
                af: Some(0),
                zf: Some(zf),
                sf: Some(0),
                of: Some(0),
            },
        ),
        ..s
    }
}

/// One step of the machine: executes the instruction `i`, which is at
/// `s.rip`, and returns the next state, or `None` for a fault.
///
/// The RIP rules are ACL2's: `temp-rip` is the address after the opcode
/// bytes already consumed, and `add-to-*ip` fails (stops the model) if the
/// sum is not canonical.
///
/// - **Straight-line instructions** (`x86-mov-Op/En-MR` and the rest): the
///   next RIP is the address after the instruction, which must be
///   canonical.
/// - **`jcc` (`x86-two-byte-jcc`):** when the condition holds, RIP becomes
///   `temp-rip + 4 + rel`, which must be canonical; when it does not, RIP
///   becomes `temp-rip + 4`, which must be canonical.
/// - **`jmp` (`x86-near-jmp-Op/En-D`):** the next-instruction address
///   `temp-rip + 4` must be canonical, and so must the target.
/// - **`ret` (`x86-ret`):** reads the return address at `rsp`; `rsp + 8` and
///   the return address must be canonical; `rsp` and RIP are written.
///
/// The instruction's bytes are not read here: `i` is the decoded
/// instruction. That the bytes at RIP are the canonical encoding of `i` is
/// [`fetch_ok`].
pub open spec fn step(create_undef: spec_fn(nat) -> nat, s: State, i: Instr) -> Option<State> {
    let end = s.rip + instr_len(i) as int;
    match i {
        Instr::Jcc { cc, rel } => {
            let target = if jcc_cmovcc_setcc_spec(s, cc) {
                end + rel as int
            } else {
                end
            };
            match add_to_ip(target, 0) {
                Some(ip) => Some(write_ip(s, ip)),
                None => None,
            }
        },
        Instr::Jmp { rel } => match add_to_ip(end, 0) {
            Some(next_rip) => match add_to_ip(next_rip, rel as int) {
                Some(ip) => Some(write_ip(s, ip)),
                None => None,
            },
            None => None,
        },
        Instr::Ret => {
            let rsp = logext(64, rr64(s, 4));
            let new_rsp = logext(64, rsp + 8);
            match read_mem(s.mem, rsp, 8) {
                Some(raw) => {
                    let tos = logext(64, raw);
                    if canonical(new_rsp) && canonical(tos) {
                        Some(write_ip(wr64(s, 4, new_rsp), tos))
                    } else {
                        None
                    }
                },
                None => None,
            }
        },
        _ => match add_to_ip(end, 0) {
            Some(ip) => match effect(create_undef, s, i) {
                Some(s1) => Some(write_ip(s1, ip)),
                None => None,
            },
            None => None,
        },
    }
}

/// The bytes at RIP are the canonical encoding of `i`: every byte of
/// `encode(i)` is mapped at `rip + k` with that value. (Which memory is
/// executable is the validator's concern, not the machine's: the ACL2 model
/// has no execute permission in this flat model.)
pub open spec fn fetch_ok(s: State, i: Instr) -> bool {
    valid_instr(i) && forall|k: int|
        0 <= k < instr_len(i) ==> #[trigger] s.mem.dom().contains(s.rip + k) && s.mem[s.rip
            + k] == encode(i)[k]
}


} // verus!

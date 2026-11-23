//! The specification of the **A64 validator** (jit.md item J.6): which blobs of
//! machine code are *accepted*, written as spec functions over the
//! instruction subset of `clazel-a64`. Nothing here runs. It is the A64
//! counterpart of [`crate::spec`] (the x86-64 one) and follows its design;
//! this header says where the two differ.
//!
//! # Source
//!
//! There is no standard to transcribe. The sources are:
//!
//! - **jit.md, "J.6 `clazel-codecheck`: the validators"**, which lists the
//!   checks, its "Design choices that keep WebAssembly in mind" (regions, a
//!   context register, no indirect branches, exits, immutable code), and the
//!   J.0 decisions (the enter stub is the only code that meets the platform
//!   ABI; AAPCS64 on A64). Each rule below names the bullet it implements, as
//!   `J.6/<bullet>`.
//! - **`clazel-a64`'s `spec`**: the instruction subset ([`Instr`]), its
//!   canonical encoding ([`encode`], [`word_bytes`]) and its semantics
//!   ([`step`]). *What the bytes mean* is that crate's business; this crate
//!   says which sequences of its instructions may be run. The Arm
//!   Architecture Reference Manual is not read here. The one fact about
//!   semantics used is how a branch computes its target (`BranchTo(PC +
//!   offset)`, `sail-arm src/instrs64.sail`, `execute_aarch64_instrs_branch_*`),
//!   as `clazel-a64`'s [`step`] has it.
//!
//! # What the validator accepts, in one paragraph
//!
//! A blob is **accepted** when it is exactly the canonical encodings of a
//! sequence of instructions of the subset, one 4-byte word after the other
//! ([`decodes_to`]), and that sequence passes [`policy`]. The policy groups
//! the instructions into **units** (an exit sequence of 3, a bounds-check
//! sequence of 7, or any other single instruction) with one left-to-right
//! scan ([`scan`]) that tracks what is known about each register, and:
//!
//! 1. every load and store is either to the **context** (through the
//!    context register `x28`, at a fixed immediate offset) or to a **region**,
//!    through a base register loaded from the context's region table and an
//!    index register that a bounds-check unit checked and masked, with no
//!    other change to it since (`J.6/every load and store ...`);
//! 2. the context register `x28`, the link register `x30` and the stack
//!    pointer are never written (`J.6/reserved registers ...`);
//! 3. every `b`, `b.cond` and `cbz`/`cbnz` target, and every entry, is the
//!    first word of a unit, so inside the blob and on a word boundary
//!    (`J.6/every direct target ...`), and what is known about registers is
//!    forgotten at each such place;
//! 4. `ret` occurs only as the last instruction of an **exit sequence**
//!    (`J.6/no indirect branch except the exit sequence`);
//! 5. the last instruction is `ret` or `b`, so control never runs past the
//!    end (`J.6/every path ends in the exit sequence or a branch`);
//! 6. there is no system instruction (`J.6/no system instruction`): the
//!    subset has none, and decoding accepts only subset encodings.
//!
//! # Modelling choices
//!
//! The form choices are those of [`crate::spec`] (decoding is a relation;
//! positions are byte offsets; "earlier in the same basic block" is a scan
//! with forgetting; targets are computed first from all instructions; a
//! recognized sequence is a unit and no target may land inside one). Where
//! A64 differs:
//!
//! - **Decoding needs no prefix lemma.** A64 words have a fixed size, so the
//!   blob has exactly `4 * len` bytes and word `j` is the 4 bytes at `4j`
//!   ([`decodes_to`]). `clazel-a64` proves its encoding injective
//!   (`canonical_injective`), so the instruction sequence of a blob is
//!   unique, and the validator is complete without any assumption
//!   ([`crate::a64::contract::validate_ensures`] is an equivalence).
//! - **A branch is relative to its own address.** A64's `b`, `b.cond`,
//!   `cbz` and `cbnz` take `PC + 4 * imm`, where `PC` is the address of the
//!   branch (x86-64's is the end of the instruction); [`jump_targets`]
//!   computes it so. A `b.cond` or `cbz` that is not taken goes to the next
//!   word, so it is not a block end; `b` is.
//! - **Register 31 is the zero register** in every operand of the subset
//!   except as the base or destination of `ADD`/`SUB` (immediate), where it
//!   is `SP`. So a write to register 31 is a write to `SP` only for `ADD`/`SUB`
//!   (immediate) without flags ([`writes_sp`]); elsewhere it is discarded, and
//!   it is how `cmp` (`SUBS xzr, ...`) and the mask (`csel ..., xzr, ...`) are
//!   written. A load or store with base 31 is not in the subset.
//!
//! ABI (jit.md leaves these open; see [`abi`]). The back end (J.9) must emit
//! exactly these. They are the A64 counterparts of the x86-64 choices, and are
//! collected in [`abi`] so one place changes if they change.
//!
//! - **Reserved registers: `x28` (the context), `x30` (the link register,
//!   holding the enter stub's return address) and `SP`.** The blob never
//!   writes them. The enter stub (J.7) sets `x28` and `x30` and does all
//!   AAPCS64 work (saving callee-saved registers, setting the frame), so, as
//!   on x86-64, the "fixed prologue and epilogue" of J.6 and exit criterion 2
//!   are **empty in v1**: the blob has no prologue, and its epilogue is the
//!   exit sequence, whose `ret` returns through `x30`. All other registers
//!   `x0` to `x27`, `x29` and `v0` to `v31` are the blob's.
//! - **The context** is a 512-byte block, reached only through `x28`
//!   ([`abi::ctx_reg`]): a table of 16 regions, `base` at offset `16k` and
//!   `bound` at `16k + 8`, in bytes `0..256`, which the code may read but never
//!   write, then an exit area of bytes `256..512` (the exit code at 256, the
//!   operands after it), which the code may read and write. It is the same
//!   layout as the x86-64 ABI. A context access is `ldr`/`str` (unsigned
//!   immediate) of a W, X or D register with base `x28`, the immediate being
//!   the whole offset; a register offset with base `x28` is refused.
//! - **A region access** is `ldr`/`str` (register) of a W, X or D register,
//!   `[base, index]` with no shift (`S = 0`: the index is a byte index, as on
//!   x86-64's scale 1), a size of at most 8 bytes. The base register was loaded
//!   with a 64-bit `ldr` of `[x28, #16k]` ([`Fact::Base`]); the index register
//!   holds an `i` with `i + n <= bound(k)` ([`Fact::Idx`]), established by the
//!   **bounds-check sequence** ([`check_instr`]) of 7 instructions, which
//!   also masks. A region access with an immediate offset is not accepted.
//! - **The bounds-check sequence** is, with `i` the index, `t` and `b`
//!   scratch, `n` the size, `K` the region:
//!
//!   ```text
//!   0  ldr  b, [x28, #(16K + 8)]   ; b := bound(K)
//!   1  adds t, i, #n               ; t := i + n, C set if it wrapped
//!   2  b.hs exit1                  ; wrapped: leave
//!   3  cmp  t, b                   ; (subs xzr, t, b)
//!   4  b.hi exit2                  ; i + n > bound: leave
//!   5  cmp  i, b
//!   6  csel i, i, xzr, lo          ; i := 0 if i >= bound (never, after 1-4)
//!   ```
//!
//!   It is the A64 form of the x86-64 sequence (jit.md: "Indexes are masked
//!   after the check", LIR's `masked(bound, i)`); the bound is loaded into a
//!   scratch register rather than compared in memory, and `xzr` needs no zero
//!   register. Falling through, `i + n <= bound(K)` with no wrap-around.
//! - **The exit sequence** is `movz t, #code` (a 16-bit exit code, `hw = 0`),
//!   `str t, [x28, #256]` (64-bit store), `ret`. The operands were stored
//!   before by ordinary stores to the exit area. The enter stub (J.7) is the
//!   code that `ret` returns to. The validator accepts a `ret` in no other
//!   place.
//! - **Entries** are given to the validator as byte offsets, each a unit start
//!   (so a multiple of 4).
//! - **Calls are not in the subset** (`bl`, `blr`, `br` are left out by
//!   `clazel-a64`), and nothing in the subset reads or writes `SP` except
//!   `ADD`/`SUB` (immediate), whose writes to `SP` are refused, so the native
//!   stack depth of an entry is constant.
//! - **A blob is at most 2^31 - 1 bytes** (a `requires` of the validator).
//!
//! # What is not here
//!
//! - **The safety theorem of jit.md exit criterion 2** (every execution of an
//!   accepted blob stays in its regions, leaves through the exit, and so on)
//!   is *not stated or proven here*. It needs the machine-level invariant over
//!   `clazel_a64::spec::step` and the region layout; this file defines
//!   *acceptance* only, so that the theorem has something to be about.
//! - **Termination.** A blob may loop for ever (a backward `b`).
//! - **The second validator** (a dataflow analysis, jit.md J.6) for A64.

/// The instruction subset's vocabulary, re-exported so that this module (and
/// its users) read one namespace: [`Instr`], [`encode`], [`valid_instr`] and
/// the rest are `clazel-a64`'s.
pub use clazel_a64::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: abi
// ============================================================================

/// The ABI constants. Spec functions, so a witness may evaluate them.
pub mod abi {
    #[allow(unused_imports)]
    use vstd::prelude::*;

    /// The context register: `x28`. Reserved: never written.
    pub open spec fn ctx_reg() -> u8 {
        28
    }

    /// The link register: `x30`, which the exit sequence's `ret` returns
    /// through. Reserved: never written.
    pub open spec fn link_reg() -> u8 {
        30
    }

    /// Register number 31, which names `SP` in `ADD`/`SUB` (immediate), and the
    /// zero register elsewhere.
    pub open spec fn sp_reg() -> u8 {
        31
    }

    /// A general register the code may not write.
    pub open spec fn reserved(r: u8) -> bool {
        r == ctx_reg() || r == link_reg()
    }

    /// The number of regions in the context's table.
    pub open spec fn num_regions() -> int {
        16
    }

    /// The offset in the context of region `k`'s base address (8 bytes).
    pub open spec fn base_off(k: int) -> int {
        16 * k
    }

    /// The offset in the context of region `k`'s bound in bytes (8 bytes).
    pub open spec fn bound_off(k: int) -> int {
        16 * k + 8
    }

    /// The first byte after the region table, where the exit area starts.
    pub open spec fn table_end() -> int {
        16 * num_regions()
    }

    /// The offset of the exit code, the first word of the exit area.
    pub open spec fn exit_code_off() -> int {
        table_end()
    }

    /// The size of the context in bytes: the table, then the exit area.
    pub open spec fn ctx_size() -> int {
        2 * table_end()
    }

    /// The most bytes one load or store touches: an X or D register.
    pub open spec fn max_access() -> int {
        8
    }
}

// ============================================================================
// Section: decoding
// ============================================================================
//
// jit.md J.6, "every instruction is in the subset, in canonical encoding".

/// Every instruction is in the subset ([`valid_instr`]).
pub open spec fn all_valid(ins: Seq<Instr>) -> bool {
    forall|j: int| 0 <= j < ins.len() ==> valid_instr(#[trigger] ins[j])
}

/// `blob` is exactly the canonical encodings of the instructions `ins`, in the
/// subset: word `j` is the 4 bytes at `4j`, [`word_bytes`] of the canonical
/// encoding of `ins[j]`. No byte is left over, and none is unread.
pub open spec fn decodes_to(blob: Seq<u8>, ins: Seq<Instr>) -> bool {
    all_valid(ins) && blob.len() == 4 * ins.len() && forall|j: int|
        0 <= j < ins.len() ==> blob.subrange(4 * j, 4 * j + 4) == word_bytes(
            encode(#[trigger] ins[j]),
        )
}

/// The byte offset at which instruction `j` begins: every instruction has 4
/// bytes (`start_of(ins, ins.len())` is the length of the blob).
pub open spec fn start_of(ins: Seq<Instr>, j: int) -> int {
    4 * j
}

// ============================================================================
// Section: registers and what is known about them
// ============================================================================

/// What the scan knows about the value of one general register.
pub enum Fact {
    /// Nothing.
    Unknown,
    /// The register holds the base address of region `k`: it was loaded
    /// from `[x28, #16k]` (64-bit), and the table is never written.
    Base(int),
    /// The register holds an `i` with `i + n <= bound(k)` (no wrap-around),
    /// so an `n`-byte access at `base(k) + i` lies inside region `k`. A
    /// bounds-check sequence established it.
    Idx(int, int),
}

/// One entry of the fact list: the register `reg` has the fact `fact`.
pub struct Binding {
    /// The register number.
    pub reg: u8,
    /// What is known of it from here on.
    pub fact: Fact,
}

/// What is known about every register: a list of bindings, the *last* one
/// for a register being current (a register with none is [`Fact::Unknown`]).
pub type Facts = Seq<Binding>;

/// Nothing is known about any register.
pub open spec fn no_facts() -> Facts {
    Seq::empty()
}

/// What is known about register `r`: its latest binding.
pub open spec fn fact_of(fs: Facts, r: u8) -> Fact
    decreases fs.len(),
{
    if fs.len() == 0 {
        Fact::Unknown
    } else if fs.last().reg == r {
        fs.last().fact
    } else {
        fact_of(fs.drop_last(), r)
    }
}

/// `fs` with `r` now known as `f`.
pub open spec fn set_fact(fs: Facts, r: u8, f: Fact) -> Facts {
    fs.push(Binding { reg: r, fact: f })
}

// ============================================================================
// Section: what an instruction writes and touches
// ============================================================================

/// The general register an instruction writes, if any: its destination
/// (`J.6/reserved registers ...`). `cmp` is `SUBS` into register 31, the zero
/// register, so it names register 31 and writes nothing (see [`writes_sp`]).
/// The stores, branches and the floating-point instructions that write only a
/// vector register write none; the ones that return an integer (`FMOV Xd,
/// Dn`, `FCVTZS`) name `d`.
pub open spec fn written_gpr(i: Instr) -> Option<u8> {
    match i {
        Instr::AddSubShiftedReg { d, .. } => Some(d),
        Instr::AddSubImm { d, .. } => Some(d),
        Instr::MulAddSub { d, .. } => Some(d),
        Instr::Div { d, .. } => Some(d),
        Instr::LogicalShiftedReg { d, .. } => Some(d),
        Instr::ShiftVariable { d, .. } => Some(d),
        Instr::Bitfield { d, .. } => Some(d),
        Instr::MoveWide { d, .. } => Some(d),
        Instr::CondSelect { d, .. } => Some(d),
        Instr::LoadStoreImm { load, t, .. } => if load {
            Some(t)
        } else {
            None
        },
        Instr::LoadStoreReg { load, t, .. } => if load {
            Some(t)
        } else {
            None
        },
        Instr::FpLoadStoreImm { .. } => None,
        Instr::FpLoadStoreReg { .. } => None,
        Instr::B { .. } => None,
        Instr::BCond { .. } => None,
        Instr::CompareBranch { .. } => None,
        Instr::Ret => None,
        Instr::FAddSub { .. } => None,
        Instr::FMul { .. } => None,
        Instr::FDiv { .. } => None,
        Instr::FUnary { .. } => None,
        Instr::FCmp { .. } => None,
        Instr::FMovGen { to_fp, d, .. } => if to_fp {
            None
        } else {
            Some(d)
        },
        Instr::Scvtf { .. } => None,
        Instr::Fcvtzs { d, .. } => Some(d),
    }
}

/// The instruction writes the stack pointer: `ADD`/`SUB` (immediate) without
/// flags and with destination 31 (with flags, register 31 is the zero
/// register). It is the only instruction of the subset whose register 31 is
/// `SP` as a destination.
pub open spec fn writes_sp(i: Instr) -> bool {
    match i {
        Instr::AddSubImm { setflags, d, .. } => !setflags && d == abi::sp_reg(),
        _ => false,
    }
}

/// The instruction writes the context register, the link register or the
/// stack pointer.
pub open spec fn writes_reserved(i: Instr) -> bool {
    writes_sp(i) || match written_gpr(i) {
        Some(d) => abi::reserved(d),
        None => false,
    }
}

/// One memory access of an instruction: the base register, the index register
/// (for the register-offset forms) and whether it is shifted, the immediate
/// byte offset (for the immediate forms), how many bytes are touched, and
/// whether it is a store. Every instruction of the subset touches memory in at
/// most one place and does not touch the stack (`ret` reads no memory).
pub struct Access {
    /// The base register `Rn` (never 31 in the subset).
    pub base: u8,
    /// The offset register `Rm`, if the form has one.
    pub index: Option<u8>,
    /// The `S` bit: the offset register is shifted left by `log2(size)`.
    pub scaled: bool,
    /// The immediate byte offset (`imm12 << scale`); 0 for a register offset.
    pub off: int,
    /// The number of bytes read or written.
    pub size: int,
    /// A store (else a load).
    pub store: bool,
}

/// The bytes of a W or X register access.
pub open spec fn nbytes(sf: Width) -> int {
    match sf {
        Width::W32 => 4,
        Width::W64 => 8,
    }
}

/// The memory access of an instruction, if it makes one.
pub open spec fn mem_access(i: Instr) -> Option<Access> {
    match i {
        Instr::LoadStoreImm { sf, load, n, imm12, .. } => Some(
            Access {
                base: n,
                index: None,
                scaled: false,
                off: imm12 as int * nbytes(sf),
                size: nbytes(sf),
                store: !load,
            },
        ),
        Instr::LoadStoreReg { sf, load, n, m, s, .. } => Some(
            Access {
                base: n,
                index: Some(m),
                scaled: s,
                off: 0,
                size: nbytes(sf),
                store: !load,
            },
        ),
        Instr::FpLoadStoreImm { load, n, imm12, .. } => Some(
            Access {
                base: n,
                index: None,
                scaled: false,
                off: imm12 as int * 8,
                size: 8,
                store: !load,
            },
        ),
        Instr::FpLoadStoreReg { load, n, m, s, .. } => Some(
            Access { base: n, index: Some(m), scaled: s, off: 0, size: 8, store: !load },
        ),
        _ => None,
    }
}

/// The access is permitted, given what is known of the registers
/// (`J.6/every load and store ...`).
///
/// 1. **To the context:** base `x28`, an immediate offset, and the `size`
///    bytes at `off` inside the context. A store must also lie in the exit
///    area, so the region table is never written.
/// 2. **To a region:** base a register known to hold region `k`'s base, an
///    index register known to be checked for at least `size` bytes of the
///    same region, no shift and no immediate offset.
///
/// Anything else (another base, an unchecked index, a wider access than was
/// checked, a shifted index, an offset) is refused.
pub open spec fn access_ok(fs: Facts, a: Access) -> bool {
    if a.base == abi::ctx_reg() {
        a.index is None && 0 <= a.off && a.off + a.size <= abi::ctx_size() && (!a.store
            || abi::exit_code_off() <= a.off)
    } else {
        match a.index {
            None => false,
            Some(m) => !a.scaled && a.off == 0 && match (
                fact_of(fs, a.base),
                fact_of(fs, m),
            ) {
                (Fact::Base(k), Fact::Idx(k2, n)) => k == k2 && a.size <= n,
                _ => false,
            },
        }
    }
}

/// The instruction is a 64-bit load of the base of a region from the
/// context's table into a register (not the zero register), `ldr xt, [x28,
/// #16k]`: the region `k`.
pub open spec fn base_load_region(i: Instr) -> Option<int> {
    match i {
        Instr::LoadStoreImm { sf, load, t, n, imm12 } => if sf is W64 && load && n == abi::ctx_reg()
            && t != abi::sp_reg() && imm12 as int * 8 < abi::table_end() && (imm12 as int * 8) % 16
            == 0 {
            Some(imm12 as int * 8 / 16)
        } else {
            None
        },
        _ => None,
    }
}

// ============================================================================
// Section: units
// ============================================================================
//
// jit.md J.6: "a fixed recognizable sequence". A unit is one or more
// instructions that the scan takes together.

/// What a unit does to the scan: how many instructions it covers and what is
/// known after it.
pub struct Unit {
    /// The number of instructions.
    pub len: int,
    /// What is known about the registers after the unit.
    pub facts: Facts,
}

/// A single instruction that is not part of a recognized sequence, and what is
/// known after it, if it is permitted (`J.6/reserved registers ...`, `J.6/every
/// load and store ...`, `J.6/no indirect branch ...`).
///
/// - `ret` is refused: it is only in the exit sequence.
/// - A write to the context register, the link register or the stack pointer
///   is refused.
/// - A memory access must pass [`access_ok`].
/// - `b` ends a block, so nothing is known after it; `b.cond`, `cbz` and
///   `cbnz` do not.
/// - Writing a register ends what is known about it; loading `[x28, #16k]` in
///   64 bits makes it region `k`'s base.
pub open spec fn plain_ok(fs: Facts, i: Instr) -> Option<Facts> {
    if i is Ret {
        None
    } else if writes_reserved(i) {
        None
    } else if match mem_access(i) {
        Some(a) => !access_ok(fs, a),
        None => false,
    } {
        None
    } else if i is B {
        Some(no_facts())
    } else {
        match written_gpr(i) {
            None => Some(fs),
            Some(d) => match base_load_region(i) {
                Some(k) => Some(set_fact(fs, d, Fact::Base(k))),
                None => Some(set_fact(fs, d, Fact::Unknown)),
            },
        }
    }
}

/// The parameters of a bounds check, read off the first instructions of a
/// candidate sequence.
pub struct Chk {
    /// The region (0 to 15).
    pub k: int,
    /// The number of bytes the check admits (1 to 8).
    pub n: int,
    /// The index register, checked and masked in place.
    pub i: u8,
    /// A scratch register for `i + n`.
    pub t: u8,
    /// A scratch register for the bound.
    pub bnd: u8,
    /// The offset (in words) of the first conditional branch (the carry exit).
    pub r1: i32,
    /// The offset of the second (the bound exit).
    pub r2: i32,
}

/// Instruction `m` (0 to 6) of the **bounds-check sequence** for `c`; see the
/// header for the listing. Falling through, `i + n <= bound(K)` with no
/// wrap-around, so `base(K) + i .. + n` is inside the region ([`Fact::Idx`]),
/// and the mask in 5 and 6 is the identity architecturally (it is what LIR's
/// `bounds_check` does, and it bounds the index under speculation). The two
/// branches may go anywhere the targets rule allows.
pub open spec fn check_instr(m: int, c: Chk) -> Instr {
    if m == 0 {
        Instr::LoadStoreImm {
            sf: Width::W64,
            load: true,
            t: c.bnd,
            n: abi::ctx_reg(),
            imm12: (abi::bound_off(c.k) / 8) as u16,
        }
    } else if m == 1 {
        Instr::AddSubImm {
            sf: Width::W64,
            sub_op: false,
            setflags: true,
            d: c.t,
            n: c.i,
            imm12: c.n as u16,
            sh: false,
        }
    } else if m == 2 {
        Instr::BCond { cond: 2, imm19: c.r1 }
    } else if m == 3 {
        Instr::AddSubShiftedReg {
            sf: Width::W64,
            sub_op: true,
            setflags: true,
            d: abi::sp_reg(),
            n: c.t,
            m: c.bnd,
            shift_type: ShiftType::Lsl,
            shift_amount: 0,
        }
    } else if m == 4 {
        Instr::BCond { cond: 8, imm19: c.r2 }
    } else if m == 5 {
        Instr::AddSubShiftedReg {
            sf: Width::W64,
            sub_op: true,
            setflags: true,
            d: abi::sp_reg(),
            n: c.i,
            m: c.bnd,
            shift_type: ShiftType::Lsl,
            shift_amount: 0,
        }
    } else {
        Instr::CondSelect {
            sf: Width::W64,
            else_inv: false,
            else_inc: false,
            d: c.i,
            n: c.i,
            m: abi::sp_reg(),
            cond: 3,
        }
    }
}

/// The whole bounds-check sequence for `c`, seven instructions.
pub open spec fn check_seq(c: Chk) -> Seq<Instr> {
    seq![
        check_instr(0, c),
        check_instr(1, c),
        check_instr(2, c),
        check_instr(3, c),
        check_instr(4, c),
        check_instr(5, c),
        check_instr(6, c),
    ]
}

/// The parameters a bounds-check sequence at `j` would have, read from the
/// instructions that carry them; `None` if there is no room for 7
/// instructions or those do not have the right shapes. The match against
/// [`check_instr`] is [`check_unit_at`]'s.
pub open spec fn check_params(ins: Seq<Instr>, j: int) -> Option<Chk> {
    if j < 0 || j + 7 > ins.len() {
        None
    } else {
        match (ins[j], ins[j + 1], ins[j + 2], ins[j + 4]) {
            (
                Instr::LoadStoreImm { t: b, imm12: o, .. },
                Instr::AddSubImm { d: t, n: i, imm12: n, .. },
                Instr::BCond { imm19: r1, .. },
                Instr::BCond { imm19: r2, .. },
            ) => Some(
                Chk {
                    k: ((o as int) * 8 - 8) / 16,
                    n: n as int,
                    i: i,
                    t: t,
                    bnd: b,
                    r1: r1,
                    r2: r2,
                },
            ),
            _ => None,
        }
    }
}

/// The parameters are the ones the sequence admits: a region in the table, a
/// size of 1 to 8 bytes, three distinct registers, none of them reserved or
/// the zero register.
pub open spec fn check_ok(c: Chk) -> bool {
    0 <= c.k < abi::num_regions() && 1 <= c.n <= abi::max_access() && c.i != c.t && c.i != c.bnd
        && c.t != c.bnd && c.i < abi::sp_reg() && c.t < abi::sp_reg() && c.bnd < abi::sp_reg()
        && !abi::reserved(c.i) && !abi::reserved(c.t) && !abi::reserved(c.bnd)
}

/// A bounds-check sequence begins at instruction `j`: seven instructions equal
/// to [`check_instr`] for some admitted parameters.
pub open spec fn check_unit_at(ins: Seq<Instr>, j: int) -> bool {
    match check_params(ins, j) {
        None => false,
        Some(c) => check_ok(c) && ins[j] == check_instr(0, c) && ins[j + 1] == check_instr(1, c)
            && ins[j + 2] == check_instr(2, c) && ins[j + 3] == check_instr(3, c) && ins[j + 4]
            == check_instr(4, c) && ins[j + 5] == check_instr(5, c) && ins[j + 6] == check_instr(
            6,
            c,
        ),
    }
}

/// What is known after the bounds-check sequence at `j` (assumed present):
/// the scratch registers are unknown, and the index register is checked for
/// `n` bytes of region `k`.
pub open spec fn check_facts(fs: Facts, ins: Seq<Instr>, j: int) -> Facts {
    match check_params(ins, j) {
        None => fs,
        Some(c) => set_fact(
            set_fact(set_fact(fs, c.t, Fact::Unknown), c.bnd, Fact::Unknown),
            c.i,
            Fact::Idx(c.k, c.n),
        ),
    }
}

/// An **exit sequence** begins at instruction `j` (`J.6/no indirect branch
/// except the exit sequence`, `J.6/every path ends in the exit sequence or a
/// branch`): `movz wt, #code`; `str xt, [x28, #exit_code_off]`; `ret`, with
/// `t` not reserved and not the zero register.
pub open spec fn exit_unit_at(ins: Seq<Instr>, j: int) -> bool {
    0 <= j && j + 3 <= ins.len() && match (ins[j], ins[j + 1], ins[j + 2]) {
        (
            Instr::MoveWide { sf: Width::W32, opcode: MoveWideOp::Z, d: t, hw: 0, .. },
            Instr::LoadStoreImm { sf: Width::W64, load: false, t: src, n, imm12 },
            Instr::Ret,
        ) => t < abi::sp_reg() && !abi::reserved(t) && src == t && n == abi::ctx_reg() && (
        imm12 as int) * 8 == abi::exit_code_off(),
        _ => false,
    }
}

/// The unit that begins at instruction `j`, given what is known there: the
/// exit sequence, else the bounds-check sequence, else one permitted
/// instruction. `None` if the instruction at `j` is not permitted.
pub open spec fn unit_at(ins: Seq<Instr>, j: int, fs: Facts) -> Option<Unit> {
    if exit_unit_at(ins, j) {
        Some(Unit { len: 3, facts: no_facts() })
    } else if check_unit_at(ins, j) {
        Some(Unit { len: 7, facts: check_facts(fs, ins, j) })
    } else if 0 <= j && j < ins.len() {
        match plain_ok(fs, ins[j]) {
            Some(f) => Some(Unit { len: 1, facts: f }),
            None => None,
        }
    } else {
        None
    }
}

// ============================================================================
// Section: targets
// ============================================================================
//
// `J.6/every direct target is a decoded boundary inside the blob`.

/// The displacement in bytes of a direct branch: four times the immediate
/// (`b`, `b.cond`, `cbz`, `cbnz`).
pub open spec fn jump_rel(i: Instr) -> Option<int> {
    match i {
        Instr::B { imm26 } => Some(imm26 as int * 4),
        Instr::BCond { imm19, .. } => Some(imm19 as int * 4),
        Instr::CompareBranch { imm19, .. } => Some(imm19 as int * 4),
        _ => None,
    }
}

/// The byte offsets that instructions `j` and after branch to: the offset of
/// the branch itself plus the displacement (`BranchTo(PC + offset)`, as in
/// `clazel-a64`'s `step`; `PC` is the address of the branch).
pub open spec fn jump_targets(ins: Seq<Instr>, j: int) -> Seq<int>
    decreases ins.len() - j,
{
    if j < 0 || j >= ins.len() {
        Seq::empty()
    } else {
        let here: Seq<int> = match jump_rel(ins[j]) {
            Some(r) => seq![start_of(ins, j) + r],
            None => Seq::empty(),
        };
        here + jump_targets(ins, j + 1)
    }
}

/// `x` is an element of `s`.
pub open spec fn seq_has(s: Seq<int>, x: int) -> bool
    decreases s.len(),
{
    if s.len() == 0 {
        false
    } else {
        s.last() == x || seq_has(s.drop_last(), x)
    }
}

/// Every element of `a` is an element of `b`.
pub open spec fn subset_of(a: Seq<int>, b: Seq<int>) -> bool
    decreases a.len(),
{
    if a.len() == 0 {
        true
    } else {
        seq_has(b, a.last()) && subset_of(a.drop_last(), b)
    }
}

// ============================================================================
// Section: the scan and the policy
// ============================================================================

/// The one linear pass (`J.6`: "Checks, in one linear decode"). From
/// instruction `j`, knowing `fs`: forget everything if this offset is a
/// target; take the unit that begins here; continue after it. The result is
/// the offsets at which units begin (from `j` on), or `None` if any unit is
/// refused.
pub open spec fn scan(ins: Seq<Instr>, tg: Seq<int>, j: int, fs: Facts) -> Option<Seq<int>>
    decreases ins.len() - j,
{
    if j < 0 || j >= ins.len() {
        Some(Seq::empty())
    } else {
        let here = start_of(ins, j);
        let fs0 = if seq_has(tg, here) {
            no_facts()
        } else {
            fs
        };
        match unit_at(ins, j, fs0) {
            None => None,
            Some(u) => if u.len >= 1 && j + u.len <= ins.len() {
                match scan(ins, tg, j + u.len, u.facts) {
                    None => None,
                    Some(rest) => Some(seq![here] + rest),
                }
            } else {
                None
            },
        }
    }
}

/// Every offset the blob can be entered at or jumped to: the entries and the
/// jump targets.
pub open spec fn all_targets(ins: Seq<Instr>, entries: Seq<int>) -> Seq<int> {
    entries + jump_targets(ins, 0)
}

/// The instructions `ins`, entered at the byte offsets `entries`, pass the
/// validator's checks:
///
/// - there is an instruction, and the last is `ret` or `b`
///   (`J.6/every path ends in the exit sequence or a branch`; with `ret`
///   accepted only in the exit sequence, this is "ends in an exit sequence or
///   an unconditional branch");
/// - the scan refuses no unit;
/// - every entry and every branch target is the offset of a unit's first
///   instruction (`J.6/every direct target ...`).
pub open spec fn policy(ins: Seq<Instr>, entries: Seq<int>) -> bool {
    0 < ins.len() && (ins.last() is Ret || ins.last() is B) && match scan(
        ins,
        all_targets(ins, entries),
        0,
        no_facts(),
    ) {
        None => false,
        Some(starts) => subset_of(all_targets(ins, entries), starts),
    }
}

/// `blob`, entered at the byte offsets `entries`, is **accepted**: it is the
/// canonical encoding of some sequence of instructions of the subset that
/// passes the [`policy`].
pub open spec fn accepted(blob: Seq<u8>, entries: Seq<int>) -> bool {
    exists|ins: Seq<Instr>| decodes_to(blob, ins) && policy(ins, entries)
}

} // verus!

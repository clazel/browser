//! The specification of the **x86-64 validator** (jit.md item J.6): which
//! blobs of machine code are *accepted*, written as spec functions over the
//! instruction subset of `clazel-x64`. Nothing here runs.
//!
//! # Source
//!
//! There is no standard to transcribe. The sources are:
//!
//! - **jit.md, "J.6 `clazel-codecheck`: the validators"**, which lists the
//!   checks, and its "Design choices that keep WebAssembly in mind" (regions,
//!   a context register, no indirect branches, exits, immutable code). Each
//!   rule below names the bullet it implements, as `J.6/<bullet>`.
//! - **`clazel-x64`'s `spec`**: the instruction subset ([`Instr`]), its
//!   canonical encoding ([`encode`]) and its semantics ([`step`]). *What the
//!   bytes mean* is that crate's business; this crate says which sequences of
//!   its instructions may be run. The Intel SDM is not read here: x86-64
//!   encoding is not re-specified, it is `clazel-x64`'s `encode`.
//!
//! # What the validator accepts, in one paragraph
//!
//! A blob is **accepted** when it is exactly the canonical encodings of a
//! sequence of instructions of the subset, one after the other
//! ([`decodes_to`]), and that sequence passes [`policy`]. The policy groups
//! the instructions into **units** (an exit sequence of 3, a bounds-check
//! sequence of 8, or any other single instruction) with one left-to-right
//! scan ([`scan`]) that tracks what is known about each register, and:
//!
//! 1. every load and store is either to the **context** (through the
//!    context register, at a fixed offset) or to a **region**, through a base
//!    register loaded from the context's region table and an index register
//!    that a bounds-check unit checked and masked, with no other change to it
//!    since (`J.6/every load and store ...`);
//! 2. the context register and the stack pointer are never written
//!    (`J.6/reserved registers ...`);
//! 3. every `jcc` and `jmp` target, and every entry, is the first byte of a
//!    unit, so inside the blob and on an instruction boundary (`J.6/every
//!    direct target ...`), and what is known about registers is forgotten at
//!    each such place;
//! 4. `ret` occurs only as the last instruction of an **exit sequence**
//!    (`J.6/no indirect branch except the exit sequence`);
//! 5. the last instruction is `ret` or `jmp`, so control never runs past the
//!    end (`J.6/every path ends in the exit sequence or a branch`);
//! 6. there is no system instruction (`J.6/no system instruction`): the
//!    subset has none, and decoding accepts only subset encodings.
//!
//! # Modelling choices
//!
//! Each is a difference of form that does not change the meaning, or a
//! decision jit.md leaves open and this file makes. The ABI choices (the
//! second group) are *ours*: jit.md says "a context register" and "fixed
//! recognizable sequences" without fixing them, so the back end (J.9) must
//! emit exactly these. They are collected in [`abi`], so one place changes if
//! they change.
//!
//! Form:
//!
//! - **Decoding is a relation, not a function.** [`decodes_to`] says the
//!   blob is the concatenation of canonical encodings; [`accepted`]
//!   quantifies over the instruction sequence. `clazel-x64`'s
//!   `canonical_prefix_free` (stated there, to be proven) says there is at
//!   most one such sequence, which makes a decoder deterministic. This crate
//!   does not rely on it for *soundness* (a blob is accepted if *some*
//!   decoding passes the policy), only for the validator being *complete*
//!   ([`crate::contract::validate_ensures`]).
//! - **Positions are byte offsets** from the start of the blob, as `int`s.
//!   A `jcc`/`jmp` target is the offset of the next instruction plus the
//!   signed displacement (Intel SDM vol. 2, `Jcc`: "relative to the end of
//!   the instruction"), which is how [`jump_targets`] computes it.
//! - **"Earlier in the same basic block" is a scan with forgetting.** The
//!   register facts ([`Fact`]) hold from the instruction that establishes
//!   them until the register is written, and are dropped at every unit
//!   start that is a jump target or an entry, and after `jmp` and `ret`.
//!   That is conservative: a fact is kept only where every way of arriving
//!   has it, because arriving by a jump or an entry is the only way not to
//!   arrive by falling through from the previous unit.
//! - **The targets are computed first, from all instructions**, and the scan
//!   uses them; then every target must be a unit start. (Whether a unit starts
//!   at a position depends on the scan, and the scan on the targets; the
//!   order here is a fixpoint-free reading: targets are a function of the
//!   instruction list only.)
//! - **A recognized sequence is a unit.** The 3-instruction exit sequence and
//!   the 8-instruction bounds check are matched wherever they occur
//!   ([`exit_unit_at`], [`check_unit_at`]). A position strictly inside a unit
//!   is not a unit start, so no jump or entry may land there: a jump into the
//!   middle of a check would skip it, and the targets rule refuses it. The
//!   same bytes that begin a check are always taken as one.
//!
//! ABI (jit.md leaves these open; see [`abi`]):
//!
//! - **The context** is a 512-byte block, reached only through `r15`
//!   ([`abi::ctx_reg`]): a table of 16 regions, `base` at offset `16k` and
//!   `bound` at `16k + 8`, in bytes `0..256`, which the code may read but
//!   never write, then an exit area of bytes `256..512` (the exit code at
//!   256, the operands after it), which the code may read and write.
//!   jit.md: "a context register pointing at a fixed table of (base, bound)
//!   pairs", and an exit "stores an exit code and its operands in the
//!   context".
//! - **A region access** is `[base + index]` (scale 1, displacement 0, a
//!   size of at most 8 bytes). The base register was loaded with a 64-bit
//!   load of `[r15 + 16k]` ([`Fact::Base`]); the index register holds an `i`
//!   with `i + n <= bound(k)` ([`Fact::Idx`]), established by the **bounds
//!   check sequence** ([`check_instr`]) of 8 instructions, which also masks
//!   (`J.6/... compared against that region's bound, and masked`; jit.md:
//!   "Indexes are masked after the check"; LIR's `masked(bound, i)`). The
//!   addition is checked for carry, so `i + n` cannot wrap.
//! - **The exit sequence** is `mov t, code` (32-bit immediate), `mov
//!   [r15 + 256], t` (64-bit store), `ret`. The code is the exit code; the
//!   operands were stored before by ordinary stores to the exit area. The
//!   enter stub (`clazel-sys`, J.7) is the code that `ret` returns to. The
//!   validator accepts a `ret` in no other place, so there is no prologue or
//!   epilogue: the blob never touches `rsp`, and the stub does all the ABI
//!   work (jit.md: "the enter stub is the only code that meets the platform
//!   ABI"), so the plan's "fixed prologue and epilogue" is empty in v1.
//! - **Entries** are given to the validator as byte offsets (jit.md J.1:
//!   re-entry "at a recorded resume point"), each a unit start. A blob with
//!   one entry at 0 is the common case.
//! - **Calls, pushes and pops are not in the subset**, so the native stack
//!   depth of an entry is constant (jit.md: "the native stack depth of an
//!   entry is a constant the validator checks"): it is 0 beyond what the stub
//!   pushed, because nothing in the subset reads or writes `rsp`.
//! - **A blob is at most 2^31 - 1 bytes** (a `requires` of the validator): a
//!   `rel32` cannot reach further, and the code cache is bounded far below.
//!
//! # What is not here
//!
//! - **The safety theorem of jit.md exit criterion 2** (every execution of an
//!   accepted blob stays in its regions, leaves through the exit, and so on)
//!   is *not stated or proven here*. It needs the machine-level invariant over
//!   `clazel_x64::spec::step` and the region layout; this file defines
//!   *acceptance* only, so that the theorem has something to be about.
//! - **Termination.** A blob may loop for ever (a backward `jmp` is a direct
//!   branch to a unit start). jit.md names no preemption mechanism (see the
//!   report in the pull request); nothing here rules a loop out.
//! - **The second validator** (a dataflow analysis, jit.md J.6) and the
//!   A64 validator.

/// The instruction subset's vocabulary, re-exported so that this crate's
/// modules (and its users) read one namespace: [`Instr`], [`encode`],
/// [`valid_instr`] and the rest are `clazel-x64`'s.
pub use clazel_x64::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: abi
// ============================================================================
//
// The fixed choices: which register is the context, where things are in it.
// (Modelling choices, second group, above.)

/// The ABI constants. Spec functions, so a witness may evaluate them.
pub mod abi {
    #[allow(unused_imports)]
    use vstd::prelude::*;

    /// The context register: `r15`, number 15. Reserved: never written.
    pub open spec fn ctx_reg() -> u8 {
        15
    }

    /// The stack pointer: `rsp`, number 4. Reserved: never written.
    pub open spec fn sp_reg() -> u8 {
        4
    }

    /// A register the code may not write.
    pub open spec fn reserved(r: u8) -> bool {
        r == ctx_reg() || r == sp_reg()
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

    /// The most bytes one load or store touches: `mov r64` or `movsd`.
    pub open spec fn max_access() -> int {
        8
    }
}

// ============================================================================
// Section: decoding
// ============================================================================
//
// jit.md J.6, "every instruction is in the subset, in canonical encoding".

/// The bytes of `ins` one after the other, each the canonical encoding of
/// its instruction.
pub open spec fn enc_all(ins: Seq<Instr>) -> Seq<u8>
    decreases ins.len(),
{
    if ins.len() == 0 {
        Seq::empty()
    } else {
        enc_all(ins.drop_last()) + encode(ins.last())
    }
}

/// Every instruction is in the subset ([`valid_instr`]): a register number
/// of 16 or more, an index of `rsp` or a shift count of 0 is not.
pub open spec fn all_valid(ins: Seq<Instr>) -> bool {
    forall|j: int| 0 <= j < ins.len() ==> valid_instr(#[trigger] ins[j])
}

/// `blob` is exactly the canonical encodings of the instructions `ins`, in
/// the subset. No byte is left over, and none is unread.
pub open spec fn decodes_to(blob: Seq<u8>, ins: Seq<Instr>) -> bool {
    all_valid(ins) && blob == enc_all(ins)
}

/// The byte offset at which instruction `j` begins (`start_of(ins, 0) == 0`;
/// `start_of(ins, ins.len())` is the length of the blob).
pub open spec fn start_of(ins: Seq<Instr>, j: int) -> int
    decreases j,
{
    if j <= 0 {
        0
    } else {
        start_of(ins, j - 1) + instr_len(ins[j - 1]) as int
    }
}

// ============================================================================
// Section: registers and what is known about them
// ============================================================================

/// What the scan knows about the value of one general register.
pub enum Fact {
    /// Nothing.
    Unknown,
    /// The register holds the base address of region `k`: it was loaded
    /// from `[r15 + 16k]` (64-bit), and the table is never written.
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

/// The general-purpose register an instruction writes, if any: its
/// destination (`J.6/reserved registers ...`). `cmp`, `test` and the stores
/// write none; the SSE instructions write only XMM registers, except the
/// ones that return an integer (`cvttsd2si`, `cvtsd2si`, `movq r, xmm`).
pub open spec fn written_gpr(i: Instr) -> Option<u8> {
    match i {
        Instr::MovRR { dst, .. } => Some(dst),
        Instr::MovLoad { dst, .. } => Some(dst),
        Instr::MovStore { .. } => None,
        Instr::MovImm32 { dst, .. } => Some(dst),
        Instr::MovImm32S { dst, .. } => Some(dst),
        Instr::MovImm64 { dst, .. } => Some(dst),
        Instr::AluRR { alu, dst, .. } => if alu is Cmp {
            None
        } else {
            Some(dst)
        },
        Instr::AluRM { alu, dst, .. } => if alu is Cmp {
            None
        } else {
            Some(dst)
        },
        Instr::AluRI { alu, dst, .. } => if alu is Cmp {
            None
        } else {
            Some(dst)
        },
        Instr::TestRR { .. } => None,
        Instr::TestRI { .. } => None,
        Instr::Neg { r, .. } => Some(r),
        Instr::Not { r, .. } => Some(r),
        Instr::ShiftImm { r, .. } => Some(r),
        Instr::ShiftCl { r, .. } => Some(r),
        Instr::ImulRR { dst, .. } => Some(dst),
        Instr::ImulRRI { dst, .. } => Some(dst),
        Instr::Jcc { .. } => None,
        Instr::Jmp { .. } => None,
        Instr::Ret => None,
        Instr::Cmovcc { dst, .. } => Some(dst),
        Instr::Setcc { dst, .. } => Some(dst),
        Instr::FpArith { .. } => None,
        Instr::Sqrtsd { .. } => None,
        Instr::Ucomisd { .. } => None,
        Instr::Cvtsi2sd { .. } => None,
        Instr::Cvttsd2si { dst, .. } => Some(dst),
        Instr::Cvtsd2si { dst, .. } => Some(dst),
        Instr::MovqToXmm { .. } => None,
        Instr::MovqFromXmm { dst, .. } => Some(dst),
        Instr::MovsdLoad { .. } => None,
        Instr::MovsdStore { .. } => None,
    }
}

/// The instruction writes the context register or the stack pointer.
pub open spec fn writes_reserved(i: Instr) -> bool {
    match written_gpr(i) {
        Some(d) => abi::reserved(d),
        None => false,
    }
}

/// One memory access of an instruction: the operand, how many bytes are
/// touched, and whether it is a store. Every instruction of the subset
/// touches memory in at most one place and does not touch the stack
/// (`ret` reads `[rsp]`; it is accepted only in the exit sequence, where the
/// enter stub put the return address).
pub struct Access {
    /// The memory operand.
    pub mem: Mem,
    /// The number of bytes read or written.
    pub size: int,
    /// A store (else a load).
    pub store: bool,
}

/// The memory access of an instruction, if it makes one.
pub open spec fn mem_access(i: Instr) -> Option<Access> {
    match i {
        Instr::MovLoad { sz, mem, .. } => Some(
            Access { mem: mem, size: nbytes(sz) as int, store: false },
        ),
        Instr::MovStore { sz, mem, .. } => Some(
            Access { mem: mem, size: nbytes(sz) as int, store: true },
        ),
        Instr::AluRM { sz, mem, .. } => Some(
            Access { mem: mem, size: nbytes(sz) as int, store: false },
        ),
        Instr::FpArith { xsrc: XmmSrc::Mem(m), .. } => Some(
            Access { mem: m, size: 8, store: false },
        ),
        Instr::Sqrtsd { xsrc: XmmSrc::Mem(m), .. } => Some(
            Access { mem: m, size: 8, store: false },
        ),
        Instr::Ucomisd { xsrc: XmmSrc::Mem(m), .. } => Some(
            Access { mem: m, size: 8, store: false },
        ),
        Instr::MovsdLoad { mem, .. } => Some(Access { mem: mem, size: 8, store: false }),
        Instr::MovsdStore { mem, .. } => Some(Access { mem: mem, size: 8, store: true }),
        _ => None,
    }
}

/// The access is permitted, given what is known of the registers
/// (`J.6/every load and store ...`).
///
/// 1. **To the context:** base `r15`, no index, and the `size` bytes at
///    `disp` inside the context. A store must also lie in the exit area, so
///    the region table is never written.
/// 2. **To a region:** base a register known to hold region `k`'s base, an
///    index register known to be checked for at least `size` bytes of the
///    same region, scale 1 and displacement 0.
///
/// Anything else (another base, an unchecked index, a wider access than was
/// checked, a displacement) is refused.
pub open spec fn access_ok(fs: Facts, a: Access) -> bool {
    if a.mem.base == abi::ctx_reg() {
        a.mem.index is None && 0 <= a.mem.disp && a.mem.disp + a.size <= abi::ctx_size() && (
        !a.store || abi::exit_code_off() <= a.mem.disp)
    } else {
        match a.mem.index {
            None => false,
            Some(ix) => ix.scale == 0 && a.mem.disp == 0 && match (
                fact_of(fs, a.mem.base),
                fact_of(fs, ix.reg),
            ) {
                (Fact::Base(k), Fact::Idx(k2, n)) => k == k2 && a.size <= n,
                _ => false,
            },
        }
    }
}

/// The instruction is a 64-bit load of the base of a region from the
/// context's table, `mov r, [r15 + 16k]`: the region `k`.
pub open spec fn base_load_region(i: Instr) -> Option<int> {
    match i {
        Instr::MovLoad { sz, mem, .. } => if sz is W64 && mem.base == abi::ctx_reg() && mem.index
            is None && 0 <= mem.disp && mem.disp < abi::table_end() && mem.disp % 16 == 0 {
            Some(mem.disp as int / 16)
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

/// A single instruction that is not part of a recognized sequence, and what
/// is known after it, if it is permitted (`J.6/reserved registers ...`, `J.6/
/// every load and store ...`, `J.6/no indirect branch ...`).
///
/// - `ret` is refused: it is only in the exit sequence.
/// - A write to the context register or the stack pointer is refused.
/// - A memory access must pass [`access_ok`].
/// - `jmp` and `ret` end a block, so nothing is known after them; `jcc` does
///   not.
/// - Writing a register ends what is known about it; loading `[r15 + 16k]`
///   in 64 bits makes it region `k`'s base.
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
    } else if i is Jmp {
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
    /// A scratch register holding zero, for the mask.
    pub z: u8,
    /// The displacement of the first conditional jump (the carry exit).
    pub r1: i32,
    /// The displacement of the second (the bound exit).
    pub r2: i32,
}

/// The context memory operand holding region `k`'s bound.
pub open spec fn bound_mem(k: int) -> Mem {
    Mem { base: abi::ctx_reg(), index: None, disp: abi::bound_off(k) as i32 }
}

/// Instruction `m` (0 to 7) of the **bounds-check sequence** for `c`. With
/// `i` the index, `t` and `z` scratch, `n` the size, `K` the region:
///
/// ```text
/// 0  mov  t, i             ; t := i
/// 1  add  t, n             ; t := i + n, CF set if it wrapped
/// 2  jb   exit1            ; wrapped: refuse         (cc 2, "b")
/// 3  cmp  t, [r15 + bound(K)]
/// 4  ja   exit2            ; i + n > bound: refuse   (cc 7, "a")
/// 5  mov  z, 0
/// 6  cmp  i, [r15 + bound(K)]
/// 7  cmovae i, z           ; i := 0 if i >= bound (never, after 1-4)
/// ```
///
/// Falling through, `i + n <= bound(K)` with no wrap-around, so
/// `base(K) + i .. + n` is inside the region ([`Fact::Idx`]), and the mask in
/// 5 to 7 is the identity architecturally (it is what LIR's `bounds_check`
/// does, and it bounds the index under speculation). The two jumps may go
/// anywhere the targets rule allows.
pub open spec fn check_instr(m: int, c: Chk) -> Instr {
    if m == 0 {
        Instr::MovRR { sz: Size::W64, dst: c.t, src: c.i }
    } else if m == 1 {
        Instr::AluRI { alu: AluOp::Add, sz: Size::W64, dst: c.t, imm: c.n as i32 }
    } else if m == 2 {
        Instr::Jcc { cc: 2, rel: c.r1 }
    } else if m == 3 {
        Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst: c.t, mem: bound_mem(c.k) }
    } else if m == 4 {
        Instr::Jcc { cc: 7, rel: c.r2 }
    } else if m == 5 {
        Instr::MovImm32 { dst: c.z, imm_u32: 0 }
    } else if m == 6 {
        Instr::AluRM { alu: AluOp::Cmp, sz: Size::W64, dst: c.i, mem: bound_mem(c.k) }
    } else {
        Instr::Cmovcc { cc: 3, sz: Size::W64, dst: c.i, src: c.z }
    }
}

/// The whole bounds-check sequence for `c`, eight instructions.
pub open spec fn check_seq(c: Chk) -> Seq<Instr> {
    seq![
        check_instr(0, c),
        check_instr(1, c),
        check_instr(2, c),
        check_instr(3, c),
        check_instr(4, c),
        check_instr(5, c),
        check_instr(6, c),
        check_instr(7, c),
    ]
}

/// The parameters a bounds-check sequence at `j` would have, read from the
/// instructions that carry them; `None` if there is no room for 8
/// instructions or those do not have the right shapes. The match against
/// [`check_instr`] is [`check_unit_at`]'s.
pub open spec fn check_params(ins: Seq<Instr>, j: int) -> Option<Chk> {
    if j < 0 || j + 8 > ins.len() {
        None
    } else {
        match (ins[j], ins[j + 1], ins[j + 2], ins[j + 3], ins[j + 4], ins[j + 5]) {
            (
                Instr::MovRR { dst: t, src: i, .. },
                Instr::AluRI { imm: n, .. },
                Instr::Jcc { rel: r1, .. },
                Instr::AluRM { mem: m, .. },
                Instr::Jcc { rel: r2, .. },
                Instr::MovImm32 { dst: z, .. },
            ) => Some(
                Chk { k: (m.disp as int - 8) / 16, n: n as int, i: i, t: t, z: z, r1: r1, r2: r2 },
            ),
            _ => None,
        }
    }
}

/// The parameters are the ones the sequence admits: a region in the table, a
/// size of 1 to 8 bytes, three distinct registers, none of them reserved.
pub open spec fn check_ok(c: Chk) -> bool {
    0 <= c.k < abi::num_regions() && 1 <= c.n <= abi::max_access() && c.i != c.t && c.i != c.z
        && c.t != c.z && !abi::reserved(c.i) && !abi::reserved(c.t) && !abi::reserved(c.z)
}

/// A bounds-check sequence begins at instruction `j`: eight instructions
/// equal to [`check_instr`] for some admitted parameters.
pub open spec fn check_unit_at(ins: Seq<Instr>, j: int) -> bool {
    match check_params(ins, j) {
        None => false,
        Some(c) => check_ok(c) && ins[j] == check_instr(0, c) && ins[j + 1] == check_instr(1, c)
            && ins[j + 2] == check_instr(2, c) && ins[j + 3] == check_instr(3, c) && ins[j + 4]
            == check_instr(4, c) && ins[j + 5] == check_instr(5, c) && ins[j + 6] == check_instr(
            6,
            c,
        ) && ins[j + 7] == check_instr(7, c),
    }
}

/// What is known after the bounds-check sequence at `j` (assumed present):
/// the scratch registers are unknown, and the index register is checked for
/// `n` bytes of region `k`.
pub open spec fn check_facts(fs: Facts, ins: Seq<Instr>, j: int) -> Facts {
    match check_params(ins, j) {
        None => fs,
        Some(c) => set_fact(
            set_fact(set_fact(fs, c.t, Fact::Unknown), c.z, Fact::Unknown),
            c.i,
            Fact::Idx(c.k, c.n),
        ),
    }
}

/// An **exit sequence** begins at instruction `j` (`J.6/no indirect branch
/// except the exit sequence`, `J.6/every path ends in the exit sequence or a
/// branch`): `mov t, code`; `mov [r15 + exit_code_off], t` (64-bit);
/// `ret`, with `t` not reserved.
pub open spec fn exit_unit_at(ins: Seq<Instr>, j: int) -> bool {
    0 <= j && j + 3 <= ins.len() && match (ins[j], ins[j + 1], ins[j + 2]) {
        (Instr::MovImm32 { dst: t, .. }, Instr::MovStore { sz, mem, src }, Instr::Ret) => !abi::reserved(
            t,
        ) && sz is W64 && mem.base == abi::ctx_reg() && mem.index is None && mem.disp
            == abi::exit_code_off() && src == t,
        _ => false,
    }
}

/// The unit that begins at instruction `j`, given what is known there:
/// the exit sequence, else the bounds-check sequence, else one permitted
/// instruction. `None` if the instruction at `j` is not permitted.
pub open spec fn unit_at(ins: Seq<Instr>, j: int, fs: Facts) -> Option<Unit> {
    if exit_unit_at(ins, j) {
        Some(Unit { len: 3, facts: no_facts() })
    } else if check_unit_at(ins, j) {
        Some(Unit { len: 8, facts: check_facts(fs, ins, j) })
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

/// The displacement of a direct jump (`jcc rel32`, `jmp rel32`).
pub open spec fn jump_rel(i: Instr) -> Option<int> {
    match i {
        Instr::Jcc { rel, .. } => Some(rel as int),
        Instr::Jmp { rel } => Some(rel as int),
        _ => None,
    }
}

/// The byte offsets that instructions `j` and after jump to: the offset of
/// the next instruction plus the displacement (Intel SDM vol. 2, `Jcc` and
/// `JMP`: "relative to the end of the instruction").
pub open spec fn jump_targets(ins: Seq<Instr>, j: int) -> Seq<int>
    decreases ins.len() - j,
{
    if j < 0 || j >= ins.len() {
        Seq::empty()
    } else {
        let here: Seq<int> = match jump_rel(ins[j]) {
            Some(r) => seq![start_of(ins, j + 1) + r],
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
/// - there is an instruction, and the last is `ret` or `jmp`
///   (`J.6/every path ends in the exit sequence or a branch`; with `ret`
///   accepted only in the exit sequence, this is "ends in an exit sequence or
///   an unconditional jump");
/// - the scan refuses no unit;
/// - every entry and every jump target is the offset of a unit's first
///   instruction (`J.6/every direct target ...`).
pub open spec fn policy(ins: Seq<Instr>, entries: Seq<int>) -> bool {
    0 < ins.len() && (ins.last() is Ret || ins.last() is Jmp) && match scan(
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

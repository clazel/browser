//! What the LIR → A64 back end is *about* (jit.md item J.9): the state
//! relation between a LIR state and an A64 machine state, the shape of the
//! frame, and the small definitions the refinement statements of
//! [`crate::a64::contract`] are written in. Nothing here runs and nothing is
//! proven. It is the A64 counterpart of [`crate::spec`] and follows its design;
//! this header says where the two differ. Read that header for the choices
//! the two share (the frame is a slot per local and per operand-stack
//! element, a value is a 64-bit word, no register is live between two LIR
//! instructions, memory is related and not yet touched).
//!
//! # Source
//!
//! There is no standard to transcribe. The sources are:
//!
//! - **jit.md, "J.9 Back ends"**: "No register allocation: every LIR local is
//!   a frame slot, and each LIR instruction is a fixed template over scratch
//!   registers, so each template's proof is local."
//! - **`clazel-lir`'s `spec`** ([`lir::eval`]): the meaning of the source.
//! - **`clazel-a64`'s `spec`** ([`isa::step`]): the meaning of the target.
//! - **`clazel-codecheck`'s `a64::spec::abi`**: the context register `x28`,
//!   the reserved registers (`x28`, `x30`, `SP`), the region table, which
//!   context bytes the code may write, and the exit sequence (`movz`; `str
//!   [x28, #256]`; `ret`). The templates follow it so that what they emit is
//!   accepted (the test in `tests/validator_a64.rs`; the validator's own spec
//!   is not re-stated here).
//!
//! # Where A64 differs from the x86-64 back end
//!
//! 1. **The frame** is the same bytes: the context's exit area after the exit
//!    code, slot `j` at `[x28 + 264 + 8 j]`, `j < 31`. A64's `LDR`/`STR`
//!    (unsigned immediate) of an X register takes the whole offset as `imm12 *
//!    8`, so slot `j` is `imm12 = 33 + j` ([`slot_imm`]); the validator accepts
//!    a store only at an offset of 256 or more and an access that ends by 512
//!    ([`abi::ctx_size`]), which is exactly the frame ([`max_slots`]). The two
//!    ABIs agree on these numbers; the proof module of the next commit shows it
//!    against [`crate::spec`]'s.
//! 2. **The scratch registers** are `x0`, `x1` and `x2` ([`x0`], [`x1`],
//!    [`x2`]), and so are the temporaries of the templates' middles: no
//!    register is live between two LIR instructions, so the relation does not
//!    mention them. `x28` (the context), `x30` (the link register) and `SP` are
//!    never written ([`preserved`]). The flags `NZCV` are not mentioned either.
//! 3. **There is no undefined-value source.** `clazel-a64`'s [`isa::step`] takes
//!    none (its header explains why), so the statements have no `create_undef`
//!    parameter.
//! 4. **Instructions are four bytes.** [`code_len`] is `4 * code.len()`, and
//!    `pc` advances by 4 per instruction. The end of the code must not wrap the
//!    64-bit address space (a `requires` of each refinement; x86-64's is "the
//!    end address is canonical"). That the bytes at `pc` are the canonical
//!    encodings ([`isa::fetch_ok`]) is not part of the statement, as for
//!    x86-64: [`preserved`] says the code writes only the exit area, so code
//!    placed outside it stays what it was, and the bytes are the emitter's
//!    contract.
//! 5. **User-space addresses.** The context lies below `2^47` ([`ctx_ok`]), so
//!    every address a template forms is far below `2^56`, the bound
//!    [`isa::wf`] puts on mapped addresses (no top-byte-ignore subtlety, no
//!    wrap-around).
//! 6. **The exit code is 16 bits.** The validator's exit sequence is `movz
//!    wt, #code` with `hw = 0`, so the code is a `u16` ([`exit_seq`]);
//!    x86-64's `mov eax, imm32` allows 32.
//! 7. **The exit sequence returns through `x30`** and reads no memory: `ret`
//!    sets `pc` to `x30` ([`isa::step`]), so there is no stack-pointer
//!    precondition ([`crate::spec::stack_ok`]) and `SP` is untouched.
//!
//! # What is not here
//!
//! The memory instructions, structured control flow, `exit` with operands,
//! `f64` arithmetic, comparisons and conversions (LIR's `f64` operators are
//! uninterpreted functions), and rotates (`clazel-a64`'s subset has no `RORV`).

/// The source subset's instruction type, shared with the x86-64 back end:
/// [`Op`] and its stack effect ([`crate::spec`]) are target-independent.
pub use crate::spec::Op;
/// `clazel-a64`'s semantics (the A64 subset), re-exported so that this crate's
/// modules read one namespace.
pub use clazel_a64::spec as isa;
/// The validator's A64 ABI, re-exported likewise.
pub use clazel_codecheck::a64::spec::abi;
/// LIR's semantics, re-exported likewise.
pub use clazel_lir::spec as lir;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: the source subset
// ============================================================================

/// The program as one LIR instruction ([`crate::spec::prog_instr`]).
#[verifier::inline]
pub open spec fn prog_instr(ops: Seq<Op>) -> lir::Instr {
    crate::spec::prog_instr(ops)
}

/// The stack height after the program `ops`, started at height `h`
/// ([`crate::spec::height_after`]).
#[verifier::inline]
pub open spec fn height_after(ops: Seq<Op>, h: nat) -> nat {
    crate::spec::height_after(ops, h)
}

/// The value in slot `j` of the LIR state `a` ([`crate::spec::slot_val`]).
#[verifier::inline]
pub open spec fn slot_val(a: lir::St, nl: nat, j: nat) -> lir::Val {
    crate::spec::slot_val(a, nl, j)
}

/// `a` is an address inside some region of `lay` ([`crate::spec::in_regions`]).
#[verifier::inline]
pub open spec fn in_regions(lay: lir::Layout, a: nat) -> bool {
    crate::spec::in_regions(lay, a)
}

/// LIR's memory and the machine's agree on every byte of every region
/// ([`crate::spec::mem_rel`]).
#[verifier::inline]
pub open spec fn mem_rel(lay: lir::Layout, lm: lir::Mem, mm: Map<int, u8>) -> bool {
    crate::spec::mem_rel(lay, lm, mm)
}

/// The instruction has a template, and is well formed at a stack of height
/// `h` with `nl` locals: the frame holds the stack as it is (`nl + h` slots)
/// and as it will be, its operands exist, its local index is in range, and so
/// everything it reads or writes is one of the 31 frame slots. As
/// [`crate::spec::op_ok`], with this module's [`max_slots`].
pub open spec fn op_ok(op: Op, nl: nat, h: nat) -> bool {
    nl + h <= max_slots() && crate::spec::pops(op) <= h && nl + crate::spec::height_after_op(op, h)
        <= max_slots() && match op {
        Op::LocalGet(x) => x < nl,
        Op::LocalSet(x) => x < nl,
        Op::LocalTee(x) => x < nl,
        Op::Bin(b) => crate::spec::bin_supported(b),
        Op::Un(u) => crate::spec::un_supported(u),
        _ => true,
    }
}

/// Every instruction of `ops` has a template at its place in the program, for
/// `nl` locals and a stack that starts at height `h`, and the starting frame
/// fits.
pub open spec fn prog_ok(ops: Seq<Op>, nl: nat, h: nat) -> bool
    decreases ops.len(),
{
    if ops.len() == 0 {
        nl + h <= max_slots()
    } else {
        prog_ok(ops.drop_last(), nl, h) && op_ok(ops.last(), nl, height_after(ops.drop_last(), h))
    }
}

// ============================================================================
// Section: the frame
// ============================================================================

/// `x0`, the first scratch register.
pub open spec fn x0() -> u8 {
    0
}

/// `x1`, the second scratch register.
pub open spec fn x1() -> u8 {
    1
}

/// `x2`, the third scratch register.
pub open spec fn x2() -> u8 {
    2
}

/// The offset from the context register of frame slot 0: the first word
/// after the exit code.
pub open spec fn frame_off() -> int {
    abi::exit_code_off() + 8
}

/// The number of frame slots: the words of the context after the exit code.
pub open spec fn max_slots() -> nat {
    ((abi::ctx_size() - frame_off()) / 8) as nat
}

/// The displacement of frame slot `j` from the context register.
pub open spec fn slot_disp(j: nat) -> int {
    frame_off() + 8 * j
}

/// The `imm12` of the `LDR`/`STR` (unsigned immediate, X register) of frame
/// slot `j`: the displacement divided by the access size.
pub open spec fn slot_imm(j: nat) -> u16 {
    (slot_disp(j) / 8) as u16
}

/// The value of the context register in `m`, as an address.
pub open spec fn ctx_of(m: isa::State) -> int {
    m.r[abi::ctx_reg() as int] as int
}

/// The context lies in user space: the 512 bytes from the context register
/// are all below `2^47` (modelling choice 5).
pub open spec fn ctx_ok(m: isa::State) -> bool {
    m.r.len() == 31 && 0 <= ctx_of(m) && ctx_of(m) + abi::ctx_size() <= isa::p2(47)
}

/// `a` is a byte of the context's exit area (what [`abi`] lets code write).
pub open spec fn in_exit_area(ctxb: int, a: int) -> bool {
    ctxb + abi::exit_code_off() <= a && a < ctxb + abi::ctx_size()
}

/// Every byte of the exit area is mapped.
pub open spec fn exit_area_mapped(mm: Map<int, u8>, ctxb: int) -> bool {
    forall|a: int| #[trigger] in_exit_area(ctxb, a) ==> mm.dom().contains(a)
}

/// The 8 bytes at the address of slot `j` read as the word `v`.
pub open spec fn slot_holds(mm: Map<int, u8>, ctxb: int, j: nat, v: nat) -> bool {
    isa::mem_read(mm, ctxb + slot_disp(j), 8) == Some(v as int)
}

// ============================================================================
// Section: the state relation
// ============================================================================

/// No region overlaps the context's exit area, which holds the frame: the
/// frame is the only machine memory the templates write, and it is nobody's
/// region.
pub open spec fn regions_clear_of_exit_area(lay: lir::Layout, ctxb: int) -> bool {
    forall|a: nat| #[trigger] in_regions(lay, a) ==> !in_exit_area(ctxb, a as int)
}

/// **The state relation.** The LIR state `a`, with `nl` locals, is
/// represented by the machine state `m`:
///
/// 1. `m` is a well-formed machine state ([`isa::wf`]), with the context in
///    user space ([`ctx_ok`]) and the layout well formed and clear of the
///    exit area;
/// 2. the frame fits: `a` has `nl` locals and `nl + height` is at most 31;
/// 3. the exit area is mapped, so a store to a slot does not fault;
/// 4. every local, and every operand-stack element, is in its slot, as the
///    64-bit word [`lir::val_bits`] of its value;
/// 5. memory is related ([`mem_rel`]).
///
/// The scratch registers, the flags and `pc` are not constrained; the
/// refinement statements say where `pc` is.
pub open spec fn rel(lay: lir::Layout, a: lir::St, m: isa::State, nl: nat) -> bool {
    isa::wf(m) && ctx_ok(m) && lir::layout_wf(lay) && regions_clear_of_exit_area(lay, ctx_of(m))
        && a.locals.len() == nl && nl + a.stack.len() <= max_slots() && exit_area_mapped(
        m.mem,
        ctx_of(m),
    ) && (forall|j: nat|
        j < nl + a.stack.len() ==> #[trigger] slot_holds(
            m.mem,
            ctx_of(m),
            j,
            lir::val_bits(slot_val(a, nl, j)),
        )) && mem_rel(lay, a.mem, m.mem)
}

/// What a template leaves alone in memory: the context register keeps its
/// value, the set of mapped addresses is the same, and every byte outside the
/// exit area keeps its value. So the code (which lives outside the exit
/// area) and every region are as they were.
pub open spec fn preserved_mem(m: isa::State, m2: isa::State) -> bool {
    m.r.len() == 31 && m2.r.len() == 31 && m2.r[abi::ctx_reg() as int] == m.r[abi::ctx_reg() as int]
        && m2.mem.dom() == m.mem.dom() && (forall|a: int|
        #[trigger] m.mem.dom().contains(a) && !in_exit_area(ctx_of(m), a) ==> m2.mem[a]
            == m.mem[a])
}

/// [`preserved_mem`], and the link register and the stack pointer keep their
/// values too: the validator forbids writing them, and the exit sequence's
/// `ret` returns through the link register.
pub open spec fn preserved(m: isa::State, m2: isa::State) -> bool {
    preserved_mem(m, m2) && m2.r[abi::link_reg() as int] == m.r[abi::link_reg() as int] && m2.sp
        == m.sp
}

// ============================================================================
// Section: running code
// ============================================================================

/// Run the instructions of `code` one after the other from `s`, each by
/// [`isa::step`], stopping at a fault (`None`). `pc` advances by 4 per
/// instruction (and, for a branch, goes to its target; the straight-line
/// templates have none).
pub open spec fn run_seq(s: isa::State, code: Seq<isa::Instr>) -> Option<isa::State>
    decreases code.len(),
{
    if code.len() == 0 {
        Some(s)
    } else {
        match isa::step(s, code[0]) {
            Some(s1) => run_seq(s1, code.skip(1)),
            None => None,
        }
    }
}

/// The exit sequence for `c`, as the validator recognizes it
/// (`clazel_codecheck::a64::spec::exit_unit_at`): `movz w0, #c`, `str x0,
/// [x28, #256]`, `ret`. It is LIR's `exit` with no operands (a function that
/// falls off its end exits with code `c`).
pub open spec fn exit_seq(c: u16) -> Seq<isa::Instr> {
    seq![
        isa::Instr::MoveWide {
            sf: isa::Width::W32,
            opcode: isa::MoveWideOp::Z,
            d: x0(),
            imm16: c,
            hw: 0,
        },
        isa::Instr::LoadStoreImm {
            sf: isa::Width::W64,
            load: false,
            t: x0(),
            n: abi::ctx_reg(),
            imm12: (abi::exit_code_off() / 8) as u16,
        },
        isa::Instr::Ret,
    ]
}

/// The length in bytes of the canonical encodings of `code`: 4 per
/// instruction.
pub open spec fn code_len(code: Seq<isa::Instr>) -> nat {
    4 * code.len()
}

} // verus!

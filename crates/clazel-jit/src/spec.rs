//! What the LIR → x86-64 back end is *about* (jit.md item J.9): the state
//! relation between a LIR state and an x86-64 machine state, the shape of a
//! template, and the small definitions the refinement statements of
//! [`crate::contract`] are written in. Nothing here runs and nothing is
//! proven; the templates are in `templates` and their proofs in the modules
//! after it.
//!
//! # Source
//!
//! There is no standard to transcribe. The sources are:
//!
//! - **jit.md, "J.9 Back ends"**: "No register allocation: every LIR local is
//!   a frame slot, and each LIR instruction is a fixed template over scratch
//!   registers, so each template's proof is local. Per-template refinement of
//!   LIR semantics, then composition over structured control flow."
//! - **`clazel-lir`'s `spec`** ([`lir::eval`]): the meaning of the source.
//! - **`clazel-x64`'s `spec`** ([`x64::step`]): the meaning of the target.
//! - **`clazel-codecheck`'s `spec::abi`**: the context register, the region
//!   table, and which context bytes the code may write. The templates follow
//!   it, so that what they emit is accepted (the test in
//!   `tests/validator.rs`; the validator's own spec is not re-stated here).
//!
//! # Modelling choices
//!
//! These are *ours*: jit.md fixes "a frame slot per local" but not where the
//! frame is, or what happens to LIR's operand stack.
//!
//! 1. **The frame is the context's writable area.** The only memory the
//!    validator lets code write without a bounds-check sequence is the exit
//!    area of the context, bytes `256..512` from `r15`
//!    ([`abi::exit_code_off`], [`abi::ctx_size`]). The frame is the part of it
//!    after the exit code: slot `j` is the 8 bytes at `r15 + 264 + 8 j`
//!    ([`slot_disp`]), for `j < 31` ([`max_slots`]). A function whose locals
//!    and operand stack need more than 31 slots is refused ([`prog_ok`]). A
//!    larger frame is a region (jit.md J.0: the interpreter's value stack),
//!    reached through the 8-instruction bounds-check sequence on every
//!    access; that needs the memory templates and is future work. **The exit
//!    code word (offset 256) is not a slot**, so an exit sequence does not
//!    overwrite a local.
//! 2. **LIR's operand stack is in the frame too.** LIR is a stack machine (it
//!    mirrors WebAssembly), and "every local is a slot" needs a home for the
//!    stack. Locals are slots `0 .. nl`; the operand stack's element `k`
//!    (bottom first) is slot `nl + k`. The height of the stack at each
//!    instruction is a static fact of well-typed straight-line code, so a
//!    template is a function of `(op, nl, h)` ([`templates::tmpl`]).
//! 3. **A value is a 64-bit word.** An `i64` and an `f64` (its bit pattern)
//!    are stored as they are, and an `i32` zero-extended
//!    ([`lir::val_bits`], which is below `2^32` for an `i32`). The type is
//!    not stored: it is static.
//! 4. **No register is live between two LIR instructions.** The scratch
//!    registers `rax`, `rcx` and `rdx` ([`rax`], [`rcx`], [`rdx`]) and the
//!    flags are dead at each template's start and end, so the relation does
//!    not mention them. `r15` (the context) and `rsp` are never written.
//! 5. **Running code is [`run_seq`]**: [`x64::step`] on each instruction of a
//!    `Seq<x64::Instr>` in turn. That the bytes at `rip` are the canonical
//!    encoding of the instruction ([`x64::fetch_ok`]) is not part of it:
//!    instead [`preserved`] says the code writes nothing but the exit area,
//!    so code placed outside the exit area stays what it was, and the bytes
//!    are `enc_all` of the instruction list (the emitter's contract).
//! 6. **Addresses are user-space addresses.** The context lies below
//!    `2^47` ([`ctx_ok`]), so every address a template forms is canonical and
//!    equals the effective address (no wrap-around), and the code's end
//!    address is canonical (a `requires` of each refinement).
//! 7. **LIR memory is related, not yet touched.** [`mem_rel`] relates each
//!    region byte of LIR's memory to the machine's, and every template in
//!    this slice leaves both unchanged. The memory templates (`bounds_check`,
//!    `load`, `store`) are not here.
//!
//! # What is not here
//!
//! The memory instructions, structured control flow (`block`, `loop`, `if`,
//! `br`, `br_if`, `br_table`), `exit` with operands, `f64` arithmetic,
//! comparisons and conversions (LIR's `f64` operators are uninterpreted
//! functions, so a refinement to SSE needs an axiom this crate does not
//! add), rotates, and the A64 back end.

/// The validator's ABI, re-exported so that this crate's modules read one namespace.
pub use clazel_codecheck::spec::abi;
/// LIR's semantics, re-exported likewise.
pub use clazel_lir::spec as lir;
/// The x86-64 subset's semantics, re-exported likewise.
pub use clazel_x64::spec as x64;

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: the source subset
// ============================================================================

/// A LIR instruction of the first slice, in a form executable code can build:
/// `clazel-lir`'s own `Instr` holds `nat`s and `Seq`s, which exist only in
/// proofs. [`View`] is the LIR instruction it stands for.
pub enum Op {
    /// `nop`.
    Nop,
    /// `t.const v`.
    Const(lir::Val),
    /// `local.get x`.
    LocalGet(usize),
    /// `local.set x`.
    LocalSet(usize),
    /// `local.tee x`.
    LocalTee(usize),
    /// `drop`.
    Drop,
    /// `select`.
    Select,
    /// A binary numeric instruction.
    Bin(lir::BinOp),
    /// A unary numeric instruction.
    Un(lir::UnOp),
}

impl vstd::view::View for Op {
    type V = lir::Instr;

    open spec fn view(&self) -> lir::Instr {
        match *self {
            Op::Nop => lir::Instr::Nop,
            Op::Const(v) => lir::Instr::Const(v),
            Op::LocalGet(x) => lir::Instr::LocalGet(x as nat),
            Op::LocalSet(x) => lir::Instr::LocalSet(x as nat),
            Op::LocalTee(x) => lir::Instr::LocalTee(x as nat),
            Op::Drop => lir::Instr::Drop,
            Op::Select => lir::Instr::Select,
            Op::Bin(b) => lir::Instr::Bin(b),
            Op::Un(u) => lir::Instr::Un(u),
        }
    }
}

/// A straight-line program as one LIR instruction: `((nop; op_0); op_1); ...`,
/// the left-nested `then` chain, so that the program minus its last
/// instruction is the first operand of the outermost `then`.
pub open spec fn prog_instr(ops: Seq<Op>) -> lir::Instr
    decreases ops.len(),
{
    if ops.len() == 0 {
        lir::Instr::Nop
    } else {
        lir::Instr::Then(Box::new(prog_instr(ops.drop_last())), Box::new(ops.last()@))
    }
}

/// How many operand-stack values the instruction takes.
pub open spec fn pops(op: Op) -> nat {
    match op {
        Op::Nop => 0,
        Op::Const(_) => 0,
        Op::LocalGet(_) => 0,
        Op::LocalSet(_) => 1,
        Op::LocalTee(_) => 1,
        Op::Drop => 1,
        Op::Select => 3,
        Op::Bin(_) => 2,
        Op::Un(_) => 1,
    }
}

/// How many operand-stack values the instruction leaves.
pub open spec fn pushes(op: Op) -> nat {
    match op {
        Op::Nop => 0,
        Op::Const(_) => 1,
        Op::LocalGet(_) => 1,
        Op::LocalSet(_) => 0,
        Op::LocalTee(_) => 1,
        Op::Drop => 0,
        Op::Select => 1,
        Op::Bin(_) => 1,
        Op::Un(_) => 1,
    }
}

/// The stack height after `op` at height `h`.
pub open spec fn height_after_op(op: Op, h: nat) -> nat {
    (h - pops(op) + pushes(op)) as nat
}

/// The integer binary operators this slice has templates for: everything but
/// `rotl` and `rotr`, which the x86-64 subset has no instruction for.
pub open spec fn ibin_supported(o: lir::IBin) -> bool {
    match o {
        lir::IBin::Rotl => false,
        lir::IBin::Rotr => false,
        _ => true,
    }
}

/// The binary instructions of this slice: integer arithmetic and logic, and
/// integer comparisons. Not the `f64` ones (see the header).
pub open spec fn bin_supported(b: lir::BinOp) -> bool {
    match b {
        lir::BinOp::I32(o) => ibin_supported(o),
        lir::BinOp::I64(o) => ibin_supported(o),
        lir::BinOp::I32Cmp(_) => true,
        lir::BinOp::I64Cmp(_) => true,
        lir::BinOp::F64(_) => false,
        lir::BinOp::F64Cmp(_) => false,
    }
}

/// The unary instructions of this slice: the integer tests and conversions,
/// and the `f64` instructions that are bit operations (`neg`, `abs`,
/// `reinterpret`). Not `sqrt` or the integer-to-`f64` conversions.
pub open spec fn un_supported(u: lir::UnOp) -> bool {
    match u {
        lir::UnOp::I32Eqz => true,
        lir::UnOp::I64Eqz => true,
        lir::UnOp::F64Neg => true,
        lir::UnOp::F64Abs => true,
        lir::UnOp::F64Sqrt => false,
        lir::UnOp::I32WrapI64 => true,
        lir::UnOp::I64ExtendI32S => true,
        lir::UnOp::I64ExtendI32U => true,
        lir::UnOp::F64ConvertI32S => false,
        lir::UnOp::F64ConvertI32U => false,
        lir::UnOp::F64ConvertI64S => false,
        lir::UnOp::F64ConvertI64U => false,
        lir::UnOp::F64ReinterpretI64 => true,
        lir::UnOp::I64ReinterpretF64 => true,
    }
}

/// The instruction has a template, and is well formed at a stack of height
/// `h` with `nl` locals: the frame holds the stack as it is (`nl + h` slots)
/// and as it will be, its operands exist, its local index is in range, and so
/// everything it reads or writes is one of the 31 frame slots.
pub open spec fn op_ok(op: Op, nl: nat, h: nat) -> bool {
    nl + h <= max_slots() && pops(op) <= h && nl + height_after_op(op, h) <= max_slots() && match op {
        Op::LocalGet(x) => x < nl,
        Op::LocalSet(x) => x < nl,
        Op::LocalTee(x) => x < nl,
        Op::Bin(b) => bin_supported(b),
        Op::Un(u) => un_supported(u),
        _ => true,
    }
}

/// The stack height after the program `ops`, started at height `h`.
pub open spec fn height_after(ops: Seq<Op>, h: nat) -> nat
    decreases ops.len(),
{
    if ops.len() == 0 {
        h
    } else {
        height_after_op(ops.last(), height_after(ops.drop_last(), h))
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

/// `rax`, the first scratch register.
pub open spec fn rax() -> u8 {
    0
}

/// `rcx`, the second scratch register (and the shift count: `shl r, cl`).
pub open spec fn rcx() -> u8 {
    1
}

/// `rdx`, the third scratch register.
pub open spec fn rdx() -> u8 {
    2
}

/// The offset from the context register of frame slot 0: the first word
/// after the exit code (modelling choice 1).
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

/// The memory operand of frame slot `j`: `[r15 + 264 + 8 j]`.
pub open spec fn slot_mem(j: nat) -> x64::Mem {
    x64::Mem { base: abi::ctx_reg(), index: None, disp: slot_disp(j) as i32 }
}

/// The value of the context register in `m`, as an address.
pub open spec fn ctx_of(m: x64::State) -> int {
    m.rgf[abi::ctx_reg() as int] as int
}

/// The context lies in user space: the 512 bytes from the context register
/// are all below `2^47` (modelling choice 6).
pub open spec fn ctx_ok(m: x64::State) -> bool {
    m.rgf.len() == 16 && 0 <= ctx_of(m) && ctx_of(m) + abi::ctx_size() <= x64::p2(47)
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
    x64::read_mem(mm, ctxb + slot_disp(j), 8) == Some(v as int)
}

// ============================================================================
// Section: the state relation
// ============================================================================

/// The value in slot `j` of the LIR state `a`, which has `nl` locals: a local
/// for `j < nl`, else the operand stack's element `j - nl`.
pub open spec fn slot_val(a: lir::St, nl: nat, j: nat) -> lir::Val {
    if j < nl {
        a.locals[j as int]
    } else {
        a.stack[(j - nl) as int]
    }
}

/// The addresses of the regions of `lay` are the addresses of its bytes: `a`
/// is inside some region.
pub open spec fn in_regions(lay: lir::Layout, a: nat) -> bool {
    exists|r: int|
        #![trigger lay[r]]
        0 <= r < lay.len() && lay[r].base <= a && a < lay[r].base + lay[r].bound
}

/// LIR's memory and the machine's agree on every byte of every region: the
/// machine maps it, and holds the byte LIR's memory reads (absent bytes read
/// 0, `lir::byte_at`).
pub open spec fn mem_rel(lay: lir::Layout, lm: lir::Mem, mm: Map<int, u8>) -> bool {
    forall|a: nat| #[trigger] in_regions(lay, a) ==> mm.dom().contains(a as int) && mm[a as int]
        == lir::byte_at(lm, a)
}

/// No region overlaps the context's exit area, which holds the frame: the
/// frame is the only machine memory the templates write, and it is nobody's
/// region.
pub open spec fn regions_clear_of_exit_area(lay: lir::Layout, ctxb: int) -> bool {
    forall|a: nat| #[trigger] in_regions(lay, a) ==> !in_exit_area(ctxb, a as int)
}

/// **The state relation.** The LIR state `a`, with `nl` locals, is
/// represented by the machine state `m`:
///
/// 1. `m` is a well-formed machine state ([`x64::wf`]), with the context in
///    user space ([`ctx_ok`]) and the layout well formed and clear of the
///    exit area;
/// 2. the frame fits: `a` has `nl` locals and `nl + height` is at most 31;
/// 3. the exit area is mapped, so a store to a slot does not fault;
/// 4. every local, and every operand-stack element, is in its slot, as the
///    64-bit word [`lir::val_bits`] of its value;
/// 5. memory is related ([`mem_rel`]).
///
/// The scratch registers, the flags, `rip` and the XMM registers are not
/// constrained (modelling choice 4); the refinement statements say where
/// `rip` is.
pub open spec fn rel(lay: lir::Layout, a: lir::St, m: x64::State, nl: nat) -> bool {
    x64::wf(m) && ctx_ok(m) && lir::layout_wf(lay) && regions_clear_of_exit_area(lay, ctx_of(m))
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
pub open spec fn preserved_mem(m: x64::State, m2: x64::State) -> bool {
    m.rgf.len() == 16 && m2.rgf.len() == 16 && m2.rgf[abi::ctx_reg() as int]
        == m.rgf[abi::ctx_reg() as int] && m2.mem.dom() == m.mem.dom() && (forall|a: int|
        #[trigger] m.mem.dom().contains(a) && !in_exit_area(ctx_of(m), a) ==> m2.mem[a]
            == m.mem[a])
}

/// [`preserved_mem`], and the stack pointer keeps its value too (no
/// template but the exit sequence's `ret` touches it, and the validator
/// forbids writing it).
pub open spec fn preserved(m: x64::State, m2: x64::State) -> bool {
    preserved_mem(m, m2) && m2.rgf[abi::sp_reg() as int] == m.rgf[abi::sp_reg() as int]
}

// ============================================================================
// Section: running code
// ============================================================================

/// Run the instructions of `code` one after the other from `s`, each by
/// [`x64::step`], stopping at a fault (`None`). `rip` advances by each
/// instruction's length (and, for a jump, goes to its target; the straight-line
/// templates have none).
pub open spec fn run_seq(
    cu: spec_fn(nat) -> nat,
    s: x64::State,
    code: Seq<x64::Instr>,
) -> Option<x64::State>
    decreases code.len(),
{
    if code.len() == 0 {
        Some(s)
    } else {
        match x64::step(cu, s, code[0]) {
            Some(s1) => run_seq(cu, s1, code.skip(1)),
            None => None,
        }
    }
}

/// The exit sequence for `c`, as the validator recognizes it
/// (`clazel_codecheck::spec::exit_unit_at`): `mov rax, c`, `mov [r15 + 256],
/// rax`, `ret`. It is LIR's `exit` with no operands (a function that falls
/// off its end exits with code `c`).
pub open spec fn exit_seq(c: u32) -> Seq<x64::Instr> {
    seq![
        x64::Instr::MovImm32 { dst: rax(), imm_u32: c },
        x64::Instr::MovStore {
            sz: x64::Size::W64,
            mem: x64::Mem { base: abi::ctx_reg(), index: None, disp: abi::exit_code_off() as i32 },
            src: rax(),
        },
        x64::Instr::Ret,
    ]
}

/// The machine's stack is as the enter stub leaves it for the `ret` of an
/// exit sequence: `rsp` points at 8 mapped bytes holding a canonical return
/// address, `rsp + 8` is canonical, and the stack word is not in the context
/// (so the exit code's store cannot change it).
pub open spec fn stack_ok(m: x64::State) -> bool {
    m.rgf.len() == 16 && {
        let rsp = x64::logext(64, m.rgf[abi::sp_reg() as int] as int);
        match x64::read_mem(m.mem, rsp, 8) {
            Some(raw) => x64::canonical(x64::logext(64, rsp + 8)) && x64::canonical(
                x64::logext(64, raw),
            ) && (rsp + 8 <= ctx_of(m) + abi::exit_code_off() || ctx_of(m) + abi::ctx_size()
                <= rsp),
            None => false,
        }
    }
}

/// The length in bytes of the canonical encodings of `code`, one after the
/// other.
pub open spec fn code_len(code: Seq<x64::Instr>) -> nat
    decreases code.len(),
{
    if code.len() == 0 {
        0
    } else {
        x64::instr_len(code[0]) + code_len(code.skip(1))
    }
}

} // verus!

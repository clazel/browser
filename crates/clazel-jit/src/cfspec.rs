//! What the x86-64 back end's **structured control flow and memory
//! instructions** are about (jit.md item J.9, second slice): the source
//! language that has them ([`Node`]), which programs have a translation
//! ([`cf_flow`]), the state relation that includes the region table
//! ([`rel_base`]), and the machine's running of code with jumps ([`steps`],
//! [`reaches`]). Nothing here runs and nothing is proven; the statements are
//! in [`crate::cfcontract`], the templates and proofs come after them.
//!
//! # Source
//!
//! As in [`crate::spec`]: jit.md "J.9 Back ends", `clazel-lir`'s `eval`
//! (the meaning of the source: `block`, `loop`, `if`, `br`, `br_if`,
//! `br_table`, `bounds_check`, `load`, `store`, `exit`), `clazel-x64`'s `step`
//! (the target), and `clazel-codecheck`'s `spec` (the ABI, and the
//! bounds-check sequence [`clazel_codecheck::spec::check_seq`] that every
//! region access must be preceded by in its basic block).
//!
//! # Modelling choices
//!
//! These add to the list in [`crate::spec`] (choices 1 to 7 there still hold,
//! except 7: memory is now touched).
//!
//! 8. **Blocks have no parameters and no results.** `block`, `loop` and `if`
//!    are *void*: a branch carries no values, so a branch is a `jmp`, with no
//!    moves between frame slots. LIR's typed blocks (jit.md: Wasm's
//!    `blocktype`) are not translated: [`Node`] has no block type, and
//!    [`View`] gives every block the empty one. The operand stack *below* a
//!    block is untouched by it (a branch to a block's label leaves the stack
//!    the block was entered with, as LIR's `finish_label` does for arity 0),
//!    which is why a branch needs no code beyond the jump.
//! 9. **Heights are static.** Like a straight-line template, a template is a
//!    function of the operand-stack height `h` at that point, found by
//!    [`cf_flow`], which is the typing LIR's soundness proves: a block's
//!    body must leave the height it entered with, or end in a branch or exit
//!    (the stack is then unconstrained). Code after such an instruction in the
//!    same sequence is dead and refused ([`cf_flow`], `Then`), so no template
//!    is chosen for a height that is never reached.
//! 10. **Labels are offsets.** The label `l` of the node being translated is
//!     a byte offset `offs[l]` from the node's first byte (negative for a
//!     `loop`'s label, past the code for a `block`'s). A `jmp` or `jcc` to it
//!     is `rel32` with the displacement from the end of the jump, so the code
//!     does not depend on where it is placed. `br_table` is a chain of
//!     compare and `je`, since the subset has no indirect branch (jit.md: no
//!     indirect branch except the exit sequence).
//! 11. **Bounds checks.** A `load` or `store` is its own bounds-check
//!     sequence (the 8 instructions of `check_seq`) and the access, with the
//!     check's two exits going to an exit stub after the access, so that the
//!     validator sees check and access in one basic block. That check can
//!     only fail where LIR's `load` is `Stuck` (typing rules it out), so its
//!     exit code is [`trap_code`] and nothing is claimed about it. A
//!     `bounds_check` instruction is the same check without the access, with
//!     its own exit code, and *is* claimed about: LIR's `Exit`.
//! 12. **The region table is related, not assumed.** [`table_ok`] says the
//!     context's table holds LIR's layout (`base` at `16 k`, `bound` at `16 k
//!     + 8`). The table is outside the exit area, so no template writes it
//!     and [`preserved_mem_r`] carries it. [`rel`] is unchanged.
//! 13. **The fresh stack of a block is a `base`.** LIR runs a block's body
//!     on a fresh stack, with the stack below set aside; the machine has all
//!     of it in the frame. [`rel_base`]`(lay, base, a, m, nl)` says the
//!     machine represents the LIR state `a` *on top of* the values `base`, in
//!     slot order: statements about a body are statements about `a`, with the
//!     enclosing stacks as `base`. A `Branch` or `Exit` outcome may have been
//!     reached in a nested body, so its state is related on top of `base`
//!     *and some `extra`* values the nested bodies' bases added.
//! 14. **Running with jumps.** [`steps`] fetches the instruction at `rip`
//!     from a list placed at a base address (the bytes are not modelled, as
//!     in [`crate::spec`] choice 5), steps it, and goes on. It fails (`None`)
//!     at a `rip` that is not an instruction boundary of the list, so a
//!     claim that code `reaches` a state includes that the code never leaves
//!     the list except by the step that ends the run. [`reaches`] is
//!     existential in the number of steps: LIR's evaluation is fuelled, the
//!     machine's is not.
//! 15. **Regions are not code, not the stack.** A region store changes bytes
//!     outside the exit area, so the statements use [`preserved_mem_r`]:
//!     everything outside the exit area *and every region* is as it was.
//!     That the code's bytes and the native stack are outside every region
//!     is a precondition ([`stack_ok_r`] for the stack; the placement of the
//!     code is the caller's, as before).
//!
//! # What is not here
//!
//! Typed blocks (choice 8), `f64` arithmetic, rotates, frames beyond 31
//! slots, and the A64 back end.

use crate::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ============================================================================
// Section: the source subset with control flow
// ============================================================================

/// `rsi`, a fourth scratch register: a region's base, in an access.
pub open spec fn rsi() -> u8 {
    6
}

/// `rdi`, a fifth scratch register: the value a `store` writes.
pub open spec fn rdi() -> u8 {
    7
}

/// The exit code of a bounds check inside a `load` or `store` (choice 11).
pub open spec fn trap_code() -> u32 {
    0xFFFF_FFFF
}

/// The value types of a `load` or `store`: the ones with a size.
pub enum MTy {
    /// `i32`: 4 bytes.
    I32,
    /// `i64`: 8 bytes.
    I64,
    /// `f64`: 8 bytes (its bits).
    F64,
}

impl MTy {
    /// The LIR type.
    pub open spec fn lir_ty(self) -> lir::Ty {
        match self {
            MTy::I32 => lir::Ty::I32,
            MTy::I64 => lir::Ty::I64,
            MTy::F64 => lir::Ty::F64,
        }
    }

    /// The access size in bytes.
    pub open spec fn size(self) -> nat {
        match self {
            MTy::I32 => 4,
            MTy::I64 => 8,
            MTy::F64 => 8,
        }
    }
}

/// The memory instructions of LIR.
pub enum MemOp {
    /// `bounds_check region size code`: the index on top of the stack; exit
    /// with `code` unless `index + size <= bound(region)`.
    BoundsCheck {
        /// The region (0 to 15).
        region: usize,
        /// The number of bytes the access that follows touches.
        size: usize,
        /// The exit code if the check fails.
        code: u32,
    },
    /// `t.load region`: pop the index, push the value in the region.
    Load {
        /// The region (0 to 15).
        region: usize,
        /// The type loaded.
        ty: MTy,
    },
    /// `t.store region`: pop the value, pop the index, write the value.
    Store {
        /// The region (0 to 15).
        region: usize,
        /// The type stored.
        ty: MTy,
    },
}

impl vstd::view::View for MemOp {
    type V = lir::Instr;

    open spec fn view(&self) -> lir::Instr {
        match *self {
            MemOp::BoundsCheck { region, size, code } => lir::Instr::BoundsCheck {
                region: region as nat,
                size: size as nat,
                code: code as nat,
            },
            MemOp::Load { region, ty } => lir::Instr::Load {
                region: region as nat,
                ty: ty.lir_ty(),
            },
            MemOp::Store { region, ty } => lir::Instr::Store {
                region: region as nat,
                ty: ty.lir_ty(),
            },
        }
    }
}

/// A LIR instruction with structured control flow, in a form executable code
/// can build (choice 8: every block is void). [`View`] is the LIR instruction
/// it stands for.
pub enum Node {
    /// A straight-line instruction ([`Op`]).
    Op(Op),
    /// A memory instruction.
    Mem(MemOp),
    /// The first, then the second, unless the first branched or exited.
    Then(Box<Node>, Box<Node>),
    /// `block` with no parameters and no results.
    Block(Box<Node>),
    /// `loop` with no parameters and no results.
    Loop(Box<Node>),
    /// `if` with no parameters and no results: the condition is popped from
    /// the enclosing body's stack.
    If(Box<Node>, Box<Node>),
    /// `br l`.
    Br(usize),
    /// `br_if l`.
    BrIf(usize),
    /// `br_table ls d`.
    BrTable(Vec<usize>, usize),
    /// `exit code` with `k` operands (the top `k` values of the stack).
    Exit(u32, usize),
}

/// The empty block type: no parameters, no results.
pub open spec fn void_bt() -> lir::BlockType {
    lir::BlockType { params: seq![], results: seq![] }
}

/// LIR's `exit c` with `k` operands (their types are not used by `eval`).
pub open spec fn exit_instr(c: nat, k: nat) -> lir::Instr {
    lir::Instr::Exit(c, Seq::new(k, |i: int| lir::Ty::I64))
}

impl vstd::view::View for Node {
    type V = lir::Instr;

    open spec fn view(&self) -> lir::Instr
        decreases *self,
    {
        match *self {
            Node::Op(o) => o@,
            Node::Mem(m) => m@,
            Node::Then(a, b) => lir::Instr::Then(Box::new((*a)@), Box::new((*b)@)),
            Node::Block(b) => lir::Instr::Block(void_bt(), Box::new((*b)@)),
            Node::Loop(b) => lir::Instr::Loop(void_bt(), Box::new((*b)@)),
            Node::If(t, e) => lir::Instr::If(
                void_bt(),
                Box::new((*t)@),
                Box::new((*e)@),
            ),
            Node::Br(l) => lir::Instr::Br(l as nat),
            Node::BrIf(l) => lir::Instr::BrIf(l as nat),
            Node::BrTable(ls, d) => lir::Instr::BrTable(
                ls@.map_values(|x: usize| x as nat),
                d as nat,
            ),
            Node::Exit(c, k) => exit_instr(c as nat, k as nat),
        }
    }
}

// ============================================================================
// Section: which programs have a translation
// ============================================================================

/// What the static analysis says about the end of an instruction.
pub enum Flow {
    /// It can fall through, leaving the operand stack at this height.
    Falls(nat),
    /// It always branches or exits: nothing follows in its sequence.
    Dead,
}

/// The analysis of `n`, entered at stack height `h` with `nl` locals and
/// `depth` labels in scope (the outermost is the function's return): `None`
/// if it has no translation. This is LIR's typing for the void subset, plus
/// the frame limit.
///
/// - A straight-line instruction: [`op_ok`].
/// - A memory instruction: the frame holds the stack, its operands exist, the
///   region is in the table (16 regions), and a `bounds_check` size is 1 to 8.
/// - `then`: the second runs at the height the first leaves. After a first
///   that is [`Flow::Dead`] only `nop` may follow (choice 9).
/// - `block`, `loop`: the body, one label deeper, leaves the height it
///   entered with or is dead.
/// - `if`: needs the condition; each arm is a body at the height below it.
/// - `br l`, `br_if l`, `br_table`: every label is in scope; `br_if` needs
///   its condition.
/// - `exit` needs its `k` operands and a code below `2^32` (a `u32`).
pub open spec fn cf_flow(n: Node, nl: nat, h: nat, depth: nat) -> Option<Flow>
    decreases n,
{
    match n {
        Node::Op(o) => if op_ok(o, nl, h) {
            Some(Flow::Falls(height_after_op(o, h)))
        } else {
            None
        },
        Node::Mem(m) => match m {
            MemOp::BoundsCheck { region, size, code } => if nl + h <= max_slots() && 1 <= h
                && region < 16 && 1 <= size <= 8 {
                Some(Flow::Falls(h))
            } else {
                None
            },
            MemOp::Load { region, ty } => if nl + h <= max_slots() && 1 <= h && region < 16 {
                Some(Flow::Falls(h))
            } else {
                None
            },
            MemOp::Store { region, ty } => if nl + h <= max_slots() && 2 <= h && region < 16 {
                Some(Flow::Falls((h - 2) as nat))
            } else {
                None
            },
        },
        Node::Then(a, b) => match cf_flow(*a, nl, h, depth) {
            None => None,
            Some(Flow::Falls(h1)) => cf_flow(*b, nl, h1, depth),
            Some(Flow::Dead) => match *b {
                Node::Op(Op::Nop) => Some(Flow::Dead),
                _ => None,
            },
        },
        Node::Block(b) => match cf_flow(*b, nl, h, depth + 1) {
            Some(Flow::Falls(h1)) => if h1 == h {
                Some(Flow::Falls(h))
            } else {
                None
            },
            Some(Flow::Dead) => Some(Flow::Falls(h)),
            None => None,
        },
        Node::Loop(b) => match cf_flow(*b, nl, h, depth + 1) {
            Some(Flow::Falls(h1)) => if h1 == h {
                Some(Flow::Falls(h))
            } else {
                None
            },
            Some(Flow::Dead) => Some(Flow::Falls(h)),
            None => None,
        },
        Node::If(t, e) => if 1 <= h && nl + h <= max_slots() {
            match (cf_flow(*t, nl, (h - 1) as nat, depth + 1), cf_flow(*e, nl, (h - 1) as nat, depth + 1)) {
                (Some(ft), Some(fe)) => if flow_fits(ft, (h - 1) as nat) && flow_fits(
                    fe,
                    (h - 1) as nat,
                ) {
                    Some(Flow::Falls((h - 1) as nat))
                } else {
                    None
                },
                _ => None,
            }
        } else {
            None
        },
        Node::Br(l) => if l < depth {
            Some(Flow::Dead)
        } else {
            None
        },
        Node::BrIf(l) => if l < depth && 1 <= h && nl + h <= max_slots() {
            Some(Flow::Falls((h - 1) as nat))
        } else {
            None
        },
        Node::BrTable(ls, d) => if d < depth && 1 <= h && nl + h <= max_slots() && (forall|i: int|
            0 <= i < ls@.len() ==> #[trigger] ls@[i] < depth) {
            Some(Flow::Dead)
        } else {
            None
        },
        Node::Exit(c, k) => if k <= h && nl + h <= max_slots() {
            Some(Flow::Dead)
        } else {
            None
        },
    }
}

/// A block's body ends as it must: dead, or at height `h`.
pub open spec fn flow_fits(f: Flow, h: nat) -> bool {
    match f {
        Flow::Falls(h1) => h1 == h,
        Flow::Dead => true,
    }
}

/// The node has a template in this slice. **Not** the memory instructions
/// (`bounds_check`, `load`, `store`) or `br_table`, which are in [`Node`]
/// and [`cf_flow`] (the statement is made for them) but have no proven
/// template yet; everything else has one.
pub open spec fn templated(n: Node) -> bool
    decreases n,
{
    match n {
        Node::Op(_) => true,
        Node::Mem(_) => false,
        Node::Then(a, b) => templated(*a) && templated(*b),
        Node::Block(b) => templated(*b),
        Node::Loop(b) => templated(*b),
        Node::If(t, e) => templated(*t) && templated(*e),
        Node::Br(_) => true,
        Node::BrIf(_) => true,
        Node::BrTable(_, _) => false,
        Node::Exit(_, _) => true,
    }
}

// ============================================================================
// Section: the state relation with a base, and the region table
// ============================================================================

/// The context's region table holds LIR's layout: at most 16 regions, and for
/// each, `base` at `r15 + 16 k` and `bound` at `r15 + 16 k + 8`, as 64-bit
/// words (choice 12). No region overlaps the table, so a store to a region
/// never changes it (the exit area is already clear: [`rel`]).
pub open spec fn table_ok(lay: lir::Layout, m: x64::State) -> bool {
    lay.len() <= abi::num_regions() && (forall|k: int|
        0 <= k < lay.len() ==> {
            &&& x64::read_mem(m.mem, ctx_of(m) + abi::base_off(k), 8) == Some(
                (#[trigger] lay[k]).base as int,
            )
            &&& x64::read_mem(m.mem, ctx_of(m) + abi::bound_off(k), 8) == Some(lay[k].bound as int)
        }) && forall|b: int|
        ctx_of(m) <= b < ctx_of(m) + abi::table_end() ==> !#[trigger] in_regions_i(lay, b)
}

/// The machine `m` represents the LIR state `a` on top of the values `base`
/// (choice 13), and the region table is as LIR's layout.
#[verifier::opaque]
pub open spec fn rel_base(
    lay: lir::Layout,
    base: Seq<lir::Val>,
    a: lir::St,
    m: x64::State,
    nl: nat,
) -> bool {
    rel(lay, a.with_stack(base + a.stack), m, nl) && table_ok(lay, m)
}

/// `a` is a byte of some region, `a` an `int`.
pub open spec fn in_regions_i(lay: lir::Layout, a: int) -> bool {
    0 <= a && in_regions(lay, a as nat)
}

/// What a template leaves alone in memory, now that a store may write a
/// region: the context register keeps its value, the mapped addresses are the
/// same, and every byte outside the exit area **and outside every region**
/// keeps its value (choice 15).
pub open spec fn preserved_mem_r(lay: lir::Layout, m: x64::State, m2: x64::State) -> bool {
    m.rgf.len() == 16 && m2.rgf.len() == 16 && m2.rgf[abi::ctx_reg() as int]
        == m.rgf[abi::ctx_reg() as int] && m2.mem.dom() == m.mem.dom() && (forall|a: int|
        #[trigger] m.mem.dom().contains(a) && !in_exit_area(ctx_of(m), a) && !in_regions_i(lay, a)
            ==> m2.mem[a] == m.mem[a])
}

/// [`preserved_mem_r`], and the stack pointer keeps its value too.
pub open spec fn preserved_r(lay: lir::Layout, m: x64::State, m2: x64::State) -> bool {
    preserved_mem_r(lay, m, m2) && m2.rgf[abi::sp_reg() as int] == m.rgf[abi::sp_reg() as int]
}

/// [`stack_ok`], and the stack word the `ret` of an exit sequence reads is in
/// no region (so no store to a region changes it).
pub open spec fn stack_ok_r(lay: lir::Layout, m: x64::State) -> bool {
    stack_ok(m) && forall|b: int|
        x64::logext(64, m.rgf[abi::sp_reg() as int] as int) <= b < x64::logext(
            64,
            m.rgf[abi::sp_reg() as int] as int,
        ) + 8 ==> !#[trigger] in_regions_i(lay, b)
}

// ============================================================================
// Section: running code with jumps
// ============================================================================

/// The instruction of `code` that begins `off` bytes after the first byte:
/// `None` if no instruction begins there (past the end, or inside one).
pub open spec fn fetch(code: Seq<x64::Instr>, off: int) -> Option<x64::Instr>
    decreases code.len(),
{
    if code.len() == 0 || off < 0 {
        None
    } else if off == 0 {
        Some(code[0])
    } else if off < x64::instr_len(code[0]) as int {
        None
    } else {
        fetch(code.skip(1), off - x64::instr_len(code[0]) as int)
    }
}

/// `n` steps of the machine from `s`, the code `code` being placed at address
/// `base` (choice 14): each fetches the instruction at `rip` and steps it. A
/// fault, or a `rip` with no instruction of `code`, is `None`.
pub open spec fn steps(
    cu: spec_fn(nat) -> nat,
    code: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    n: nat,
) -> Option<x64::State>
    decreases n,
{
    if n == 0 {
        Some(s)
    } else {
        match fetch(code, s.rip - base) {
            Some(i) => match x64::step(cu, s, i) {
                Some(s1) => steps(cu, code, base, s1, (n - 1) as nat),
                None => None,
            },
            None => None,
        }
    }
}

/// Running `code` (placed at `base`) from `s` reaches `s2` after some number
/// of steps, none of which faults.
pub open spec fn reaches(
    cu: spec_fn(nat) -> nat,
    code: Seq<x64::Instr>,
    base: int,
    s: x64::State,
    s2: x64::State,
) -> bool {
    exists|n: nat| steps(cu, code, base, s, n) == Some(s2)
}

} // verus!

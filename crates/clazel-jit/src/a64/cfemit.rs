//! The executable back end for **structured control flow, memory
//! instructions and `br_table`** (A64): [`emit_cf_blob`], **proven equal to the
//! templates**. The A64 counterpart of [`crate::cfemit`]; read that header for
//! the design, which is the same (an analysis [`analyze`] that equals `cf_flow`
//! and `csize`, then an emission [`emit_node`] that appends exactly
//! [`ctmpl`], leaf by leaf).
//!
//! [`emit_cf_blob`]'s postcondition is
//! [`super::cfcontract::emit_cf_blob_ensures`]: the bytes it returns are the
//! canonical encodings of [`super::cftemplates::ctmpl`] (the body, with the
//! return label at its end) followed by the exit sequence, and it answers
//! `None` exactly when [`super::cftemplates::cf_prog_ok`] refuses. Together
//! with [`super::cfproofs::lemma_ctmpl_refines`] that makes every emitted blob
//! a refinement of its program ([`lemma_emitted_refines`]).
//!
//! # Where it differs from x86-64's
//!
//! - **Positions are words.** Every instruction is 4 bytes, so a position is
//!   a `usize` count of words below [`MAX_WORDS`] (the spec's `max_size` is
//!   `4 * MAX_WORDS` bytes), and the spec's byte offsets of the labels in scope
//!   are `4 * (position - start)` ([`offs_of`]).
//! - **Displacements are in words** from the branch itself, so a displacement
//!   is `target - position of the branch` ([`relw`]). They fit `imm26` and
//!   `imm19` because every position is below [`MAX_WORDS`], which is why the
//!   size bound (`2^19` bytes) is what it is. Negative ones are formed, as in
//!   x86-64's emitter, without signed arithmetic: `!(pos - target - 1)` on a
//!   `u32` ([`lemma_not_neg`]).
//! - **Exit codes** are checked to be 16 bits first ([`codes_ok_exec`]), then
//!   assumed by [`analyze`] and the emission.

#[cfg(verus_only)]
use super::cfbrt::*;
#[cfg(verus_only)]
use super::cfcompose::lemma_shift_index;
#[cfg(verus_only)]
use super::cfcontract::*;
#[cfg(verus_only)]
use super::cffit::*;
#[cfg(verus_only)]
use super::cflens::*;
#[cfg(verus_only)]
use super::cfproofs::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[cfg(verus_only)]
use super::contract::*;
use super::emit::{emit_exit, emit_op, ex_load, ex_store, op_ok_exec, pops_exec, pushes_exec};
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::templates::*;
use crate::cfspec::{MTy, MemOp, Node};
use clazel_a64::encoder::encode_instr;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The largest body this emitter translates, in words (the spec's
/// `cftemplates::max_size`, `2^19` bytes).
pub const MAX_WORDS: usize = 0x2_0000;

/// The most targets of a `br_table` (the spec's `max_targets`).
pub const MAX_TARGETS: usize = 0x10000;

/// The emitter's limits are the spec's.
pub proof fn lemma_emitter_limits()
    ensures
        4 * MAX_WORDS as nat == max_size(),
        MAX_TARGETS as nat == max_targets(),
{
}

// ----------------------------------------------------------------------------
// Arithmetic (the workspace denies the unchecked operators)
// ----------------------------------------------------------------------------

/// `a + b`, when it does not overflow.
fn add_u(a: usize, b: usize) -> (r: usize)
    requires
        a + b <= usize::MAX,
    ensures
        r == a + b,
{
    a.saturating_add(b)
}

/// `a - b`, when it does not underflow.
fn sub_u(a: usize, b: usize) -> (r: usize)
    requires
        b <= a,
    ensures
        r == a - b,
{
    a.saturating_sub(b)
}

/// `a * b`, when it does not overflow.
fn mul_u(a: usize, b: usize) -> (r: usize)
    requires
        a * b <= usize::MAX,
    ensures
        r == a * b,
{
    a.saturating_mul(b)
}

/// The bit-complement of a small `u32`, read as an `i32`, is `-x - 1`.
proof fn lemma_not_neg(x: u32)
    requires
        x < 0x4000_0000,
    ensures
        (!x) as i32 as int == -(x as int) - 1,
{
    assert((!x) as i32 == -(x as i32) - 1) by (bit_vector)
        requires
            x < 0x4000_0000,
    ;
    assert((x as i32) as int == x as int);
}

/// The displacement in words from a branch at word `pos` to word `target`.
/// Both are at most [`MAX_WORDS`], so it fits an `i32`; a negative one is the
/// two's complement `!(pos - target - 1)`.
fn relw(target: usize, pos: usize) -> (r: i32)
    requires
        target <= MAX_WORDS,
        pos <= MAX_WORDS,
    ensures
        r as int == target as int - pos as int,
{
    if target >= pos {
        let d = sub_u(target, pos);
        d as i32
    } else {
        let d1 = sub_u(sub_u(pos, target), 1);
        let x = d1 as u32;
        let y = !x;
        proof {
            lemma_not_neg(x);
        }
        y as i32
    }
}

/// Every exit code in the node is 16 bits (the spec's [`codes_ok`]).
fn codes_ok_exec(n: &Node) -> (r: bool)
    ensures
        r == codes_ok(*n),
    decreases *n,
{
    match n {
        Node::Op(_) => true,
        Node::Mem(m) => match m {
            MemOp::BoundsCheck { code, .. } => *code < 0x1_0000,
            _ => true,
        },
        Node::Then(a, b) => codes_ok_exec(a) && codes_ok_exec(b),
        Node::Block(b) => codes_ok_exec(b),
        Node::Loop(b) => codes_ok_exec(b),
        Node::If(t, e) => codes_ok_exec(t) && codes_ok_exec(e),
        Node::Br(_) => true,
        Node::BrIf(_) => true,
        Node::BrTable(_, _) => true,
        Node::Exit(c, _) => *c < 0x1_0000,
    }
}

// ----------------------------------------------------------------------------
// Labels
// ----------------------------------------------------------------------------

/// The spec's label offsets (bytes) for a node that starts at word `start`,
/// when the labels are at the absolute word positions `labs`.
pub open spec fn offs_of(labs: Seq<usize>, start: int) -> Seq<int> {
    Seq::new(labs.len(), |i: int| 4 * (labs[i] as int - start))
}

/// Moving the start on by `d` words is [`shift`] by `4 d` bytes.
proof fn lemma_offs_shift(labs: Seq<usize>, start: int, d: int)
    ensures
        offs_of(labs, start + d) =~= shift(offs_of(labs, start), 4 * d),
{
    let o = offs_of(labs, start);
    assert forall|i: int| 0 <= i < labs.len() implies #[trigger] offs_of(labs, start + d)[i]
        == shift(o, 4 * d)[i] by {
        lemma_shift_index(o, 4 * d, i);
    }
}

/// A new label in front, at the absolute word `new`.
proof fn lemma_offs_push(labs: Seq<usize>, new: usize, start: int)
    ensures
        offs_of(seq![new] + labs, start) =~= seq![4 * (new as int - start)] + offs_of(labs, start),
{
    let l = seq![new] + labs;
    let r = seq![4 * (new as int - start)] + offs_of(labs, start);
    assert(l.len() == r.len());
    assert forall|i: int| 0 <= i < l.len() implies #[trigger] offs_of(l, start)[i] == r[i] by {
        if i > 0 {
            assert(l[i] == labs[i - 1]);
        }
    }
}

/// `new` followed by `labs`.
fn push_label(new: usize, labs: &[usize]) -> (v: Vec<usize>)
    ensures
        v@ == seq![new] + labs@,
{
    let mut v: Vec<usize> = Vec::new();
    v.push(new);
    v.extend_from_slice(labs);
    proof {
        assert(v@ =~= seq![new] + labs@);
    }
    v
}

// ----------------------------------------------------------------------------
// Leaves
// ----------------------------------------------------------------------------

/// The flow of an analysis, as the spec's [`Flow`]: `Some(h)` falls through at
/// height `h`, `None` is dead.
pub open spec fn fl_spec(f: Option<usize>) -> Flow {
    match f {
        Some(x) => Flow::Falls(x as nat),
        None => Flow::Dead,
    }
}

/// `ldr x0, [top of stack]; cbz/cbnz w0, rel` with `rel` words from the
/// branch.
fn cond_pre_exec(nl: usize, h: usize, iszero: bool, rel: i32, v: &mut Vec<isa::Instr>)
    requires
        1 <= h,
        nl + h <= 31,
    ensures
        final(v)@ == old(v)@ + cond_pre(nl as nat, h as nat, iszero, 4 * (rel as int)),
{
    let ghost ov = v@;
    let top = sub_u(add_u(nl, h), 1);
    v.push(ex_load(0, top));
    v.push(isa::Instr::CompareBranch { sf: isa::Width::W32, iszero, t: 0, imm19: rel });
    proof {
        assert((4 * (rel as int)) / 4 == rel as int);
        assert(v@ =~= ov + cond_pre(nl as nat, h as nat, iszero, 4 * (rel as int)));
    }
}

/// The access width of a type.
fn mty_sf_exec(ty: &MTy) -> (s: isa::Width)
    ensures
        s == mty_sf(*ty),
{
    match ty {
        MTy::I32 => isa::Width::W32,
        MTy::I64 => isa::Width::W64,
        MTy::F64 => isa::Width::W64,
    }
}

/// The number of bytes of an access.
fn mty_size_exec(ty: &MTy) -> (n: usize)
    ensures
        n as nat == ty.size(),
{
    match ty {
        MTy::I32 => 4,
        MTy::I64 => 8,
        MTy::F64 => 8,
    }
}

/// `ldr x3, [x28, #16 k]`: region `k`'s base.
fn base_ld_exec(k: usize) -> (i: isa::Instr)
    requires
        k < 16,
    ensures
        i == base_ld(k as nat),
{
    proof {
        super::steps::lemma_abi_consts();
    }
    let d = mul_u(k, 2);
    isa::Instr::LoadStoreImm { sf: isa::Width::W64, load: true, t: 3, n: 28, imm12: d as u16 }
}

/// The lengths of a memory instruction's parts.
proof fn lemma_mem_lens(m: MemOp, nl: nat, h: nat)
    ensures
        match m {
            MemOp::BoundsCheck { .. } => mem_pre(m, nl, h).len() == 1 && mem_tail(m, nl, h).len()
                == 0,
            MemOp::Load { .. } => mem_pre(m, nl, h).len() == 2 && mem_tail(m, nl, h).len() == 2,
            MemOp::Store { .. } => mem_pre(m, nl, h).len() == 3 && mem_tail(m, nl, h).len() == 1,
        },
        mem_check(m, nl, h).len() == 7,
        mem_code(m, nl, h).len() == mem_pre(m, nl, h).len() + 7 + mem_tail(m, nl, h).len() + 4,
{
}

/// The facts a memory instruction's parts need.
proof fn lemma_mem_facts(m: MemOp, nl: nat, h: nat)
    requires
        cf_flow(Node::Mem(m), nl, h, 0) is Some,
    ensures
        nl + h <= 31,
        1 <= h,
        mem_region(m) < 16,
        m is Store ==> 2 <= h,
{
    super::tlemmas::lemma_abi_consts_t();
}

/// What a memory instruction does before its check.
fn mem_pre_exec(m: &MemOp, nl: usize, h: usize, v: &mut Vec<isa::Instr>)
    requires
        cf_flow(Node::Mem(*m), nl as nat, h as nat, 0) is Some,
    ensures
        final(v)@ == old(v)@ + mem_pre(*m, nl as nat, h as nat),
{
    let ghost ov = v@;
    proof {
        lemma_mem_facts(*m, nl as nat, h as nat);
    }
    let top = sub_u(add_u(nl, h), 1);
    match m {
        MemOp::BoundsCheck { .. } => {
            v.push(ex_load(1, top));
        },
        MemOp::Load { region, .. } => {
            v.push(ex_load(1, top));
            v.push(base_ld_exec(*region));
        },
        MemOp::Store { region, .. } => {
            v.push(ex_load(4, top));
            v.push(ex_load(1, sub_u(top, 1)));
            v.push(base_ld_exec(*region));
        },
    }
    proof {
        assert(v@ =~= ov + mem_pre(*m, nl as nat, h as nat));
    }
}

/// What a memory instruction does after its check.
fn mem_tail_exec(m: &MemOp, nl: usize, h: usize, v: &mut Vec<isa::Instr>)
    requires
        cf_flow(Node::Mem(*m), nl as nat, h as nat, 0) is Some,
    ensures
        final(v)@ == old(v)@ + mem_tail(*m, nl as nat, h as nat),
{
    let ghost ov = v@;
    proof {
        lemma_mem_facts(*m, nl as nat, h as nat);
    }
    let top = sub_u(add_u(nl, h), 1);
    match m {
        MemOp::BoundsCheck { .. } => {},
        MemOp::Load { ty, .. } => {
            v.push(
                isa::Instr::LoadStoreReg {
                    sf: mty_sf_exec(ty),
                    load: true,
                    t: 0,
                    n: 3,
                    m: 1,
                    s: false,
                },
            );
            v.push(ex_store(top, 0));
        },
        MemOp::Store { ty, .. } => {
            v.push(
                isa::Instr::LoadStoreReg {
                    sf: mty_sf_exec(ty),
                    load: false,
                    t: 4,
                    n: 3,
                    m: 1,
                    s: false,
                },
            );
        },
    }
    proof {
        assert(v@ =~= ov + mem_tail(*m, nl as nat, h as nat));
    }
}

/// Append the code of a memory instruction (`mem_code`): the operands, the
/// validator's bounds check, the access, a `b` over the stub, the stub.
fn mem_code_exec(m: &MemOp, nl: usize, h: usize, out: &mut Vec<isa::Instr>)
    requires
        cf_flow(Node::Mem(*m), nl as nat, h as nat, 0) is Some,
        codes_ok(Node::Mem(*m)),
    ensures
        final(out)@ == old(out)@ + mem_code(*m, nl as nat, h as nat),
{
    proof {
        lemma_mem_facts(*m, nl as nat, h as nat);
        lemma_mem_lens(*m, nl as nat, h as nat);
        super::steps::lemma_abi_consts();
    }
    let ghost old_out = out@;
    let (region, n, exit_code, tl): (usize, usize, u16, usize) = match m {
        MemOp::BoundsCheck { region, size, code } => (*region, *size, *code as u16, 0),
        MemOp::Load { region, ty } => (*region, mty_size_exec(ty), 0xFFFF, 2),
        MemOp::Store { region, ty } => (*region, mty_size_exec(ty), 0xFFFF, 1),
    };
    proof {
        match m {
            MemOp::BoundsCheck { .. } => {},
            MemOp::Load { ty, .. } => {
                assert(mem_n(*m) == ty.size());
            },
            MemOp::Store { ty, .. } => {
                assert(mem_n(*m) == ty.size());
            },
        }
        assert(n as nat == mem_n(*m));
        assert(region as nat == mem_region(*m));
        assert(exit_code == mem_exit_code(*m));
        assert(tl as nat == mem_tail(*m, nl as nat, h as nat).len());
        assert(n <= 8);
    }
    mem_pre_exec(m, nl, h, out);
    let r1 = add_u(6, tl) as i32;
    let r2 = add_u(4, tl) as i32;
    let bd = add_u(mul_u(region, 2), 1) as u16;
    out.push(
        isa::Instr::LoadStoreImm { sf: isa::Width::W64, load: true, t: 2, n: 28, imm12: bd },
    );
    out.push(
        isa::Instr::AddSubImm {
            sf: isa::Width::W64,
            sub_op: false,
            setflags: true,
            d: 0,
            n: 1,
            imm12: n as u16,
            sh: false,
        },
    );
    out.push(isa::Instr::BCond { cond: 2, imm19: r1 });
    out.push(
        isa::Instr::AddSubShiftedReg {
            sf: isa::Width::W64,
            sub_op: true,
            setflags: true,
            d: 31,
            n: 0,
            m: 2,
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
    );
    out.push(isa::Instr::BCond { cond: 8, imm19: r2 });
    out.push(
        isa::Instr::AddSubShiftedReg {
            sf: isa::Width::W64,
            sub_op: true,
            setflags: true,
            d: 31,
            n: 1,
            m: 2,
            shift_type: isa::ShiftType::Lsl,
            shift_amount: 0,
        },
    );
    out.push(
        isa::Instr::CondSelect {
            sf: isa::Width::W64,
            else_inv: false,
            else_inc: false,
            d: 1,
            n: 1,
            m: 31,
            cond: 3,
        },
    );
    mem_tail_exec(m, nl, h, out);
    out.push(isa::Instr::B { imm26: 4 });
    emit_exit(out, exit_code);
    proof {
        let c = mem_chk(
            mem_region(*m),
            mem_n(*m),
            mem_r1(*m, nl as nat, h as nat),
            mem_r2(*m, nl as nat, h as nat),
        );
        let cs = clazel_codecheck::a64::spec::check_seq(c);
        assert(r1 as int == mem_r1(*m, nl as nat, h as nat));
        assert(r2 as int == mem_r2(*m, nl as nat, h as nat));
        assert(abi::bound_off(mem_region(*m) as int) / 8 == bd as int);
        assert(code_len(exit_seq(mem_exit_code(*m))) == 12);
        assert(cs =~= seq![
            isa::Instr::LoadStoreImm { sf: isa::Width::W64, load: true, t: 2, n: 28, imm12: bd },
            isa::Instr::AddSubImm {
                sf: isa::Width::W64,
                sub_op: false,
                setflags: true,
                d: 0,
                n: 1,
                imm12: n as u16,
                sh: false,
            },
            isa::Instr::BCond { cond: 2, imm19: r1 },
            isa::Instr::AddSubShiftedReg {
                sf: isa::Width::W64,
                sub_op: true,
                setflags: true,
                d: 31,
                n: 0,
                m: 2,
                shift_type: isa::ShiftType::Lsl,
                shift_amount: 0,
            },
            isa::Instr::BCond { cond: 8, imm19: r2 },
            isa::Instr::AddSubShiftedReg {
                sf: isa::Width::W64,
                sub_op: true,
                setflags: true,
                d: 31,
                n: 1,
                m: 2,
                shift_type: isa::ShiftType::Lsl,
                shift_amount: 0,
            },
            isa::Instr::CondSelect {
                sf: isa::Width::W64,
                else_inv: false,
                else_inc: false,
                d: 1,
                n: 1,
                m: 31,
                cond: 3,
            },
        ]);
        assert(b_i(code_len(exit_seq(mem_exit_code(*m))) as int + 4) == isa::Instr::B { imm26: 4 });
        assert(out@ =~= old_out + mem_code(*m, nl as nat, h as nat));
    }
}

/// Spec of the chain's entries `0..i`.
pub open spec fn brt_upto(ls: Seq<usize>, offs: Seq<int>, i: nat) -> Seq<isa::Instr>
    decreases i,
{
    if i == 0 {
        seq![]
    } else {
        brt_upto(ls, offs, (i - 1) as nat) + brt_entry(
            (i - 1) as nat,
            brt_rel(offs, ls[i - 1], (4 + (i - 1) * 12 + 8) as int),
        )
    }
}

/// The entries `0..i` then the entries from `i` are all of them.
proof fn lemma_brt_upto(ls: Seq<usize>, offs: Seq<int>, i: nat)
    requires
        i <= ls.len(),
    ensures
        brt_upto(ls, offs, i) + brt_entries(ls, offs, 4, i) =~= brt_entries(ls, offs, 4, 0),
    decreases i,
{
    assert(brt_e() == 12);
    if i > 0 {
        lemma_brt_upto(ls, offs, (i - 1) as nat);
        let k = (i - 1) as nat;
        assert(brt_entries(ls, offs, 4, k) == brt_entry(
            k,
            brt_rel(offs, ls[k as int], 4 + k * brt_e() + 8),
        ) + brt_entries(ls, offs, 4, i));
        assert((brt_upto(ls, offs, k) + brt_entry(
            k,
            brt_rel(offs, ls[k as int], (4 + k * 12 + 8) as int),
        )) + brt_entries(ls, offs, 4, i) =~= brt_upto(ls, offs, k) + brt_entries(
            ls,
            offs,
            4,
            k,
        ));
    }
}

/// Append the code of `br_table ls d` at the absolute word `start`.
fn brt_exec(
    ls: &[usize],
    d: usize,
    nl: usize,
    h: usize,
    start: usize,
    labs: &[usize],
    out: &mut Vec<isa::Instr>,
)
    requires
        1 <= h,
        nl + h <= 31,
        ls@.len() <= 0x10000,
        d < labs@.len(),
        forall|i: int| 0 <= i < ls@.len() ==> #[trigger] ls@[i] < labs@.len(),
        forall|i: int| 0 <= i < labs@.len() ==> #[trigger] labs@[i] <= MAX_WORDS,
        start + 2 + 3 * ls@.len() <= MAX_WORDS,
    ensures
        final(out)@ == old(out)@ + brt_code(
            ls@,
            d,
            nl as nat,
            h as nat,
            offs_of(labs@, start as int),
        ),
{
    let ghost old_out = out@;
    let ghost offs = offs_of(labs@, start as int);
    proof {
        assert(brt_p0(nl as nat, h as nat) == 4);
        assert(brt_e() == 12);
    }
    let top = sub_u(add_u(nl, h), 1);
    out.push(ex_load(0, top));
    let mut i: usize = 0;
    while i < ls.len()
        invariant
            i <= ls.len(),
            1 <= h,
            nl + h <= 31,
            ls@.len() <= 0x10000,
            forall|j: int| 0 <= j < ls@.len() ==> #[trigger] ls@[j] < labs@.len(),
            forall|j: int| 0 <= j < labs@.len() ==> #[trigger] labs@[j] <= MAX_WORDS,
            start + 2 + 3 * ls@.len() <= MAX_WORDS,
            offs == offs_of(labs@, start as int),
            out@ == old_out + seq![load_slot(x0(), (nl + h - 1) as nat)] + brt_upto(
                ls@,
                offs,
                i as nat,
            ),
        decreases ls.len() - i,
    {
        let l = match ls.get(i) {
            Some(l) => *l,
            None => {
                proof {
                    assert(false);
                }
                return ;
            },
        };
        let tgt = match labs.get(l) {
            Some(t) => *t,
            None => {
                proof {
                    assert(false);
                }
                return ;
            },
        };
        // the `b.eq` is word `start + 3 + 3 i`
        let pos = add_u(add_u(start, 3), mul_u(3, i));
        let rel = relw(tgt, pos);
        out.push(
            isa::Instr::MoveWide {
                sf: isa::Width::W32,
                opcode: isa::MoveWideOp::Z,
                d: 1,
                imm16: i as u16,
                hw: 0,
            },
        );
        out.push(
            isa::Instr::AddSubShiftedReg {
                sf: isa::Width::W32,
                sub_op: true,
                setflags: true,
                d: 31,
                n: 0,
                m: 1,
                shift_type: isa::ShiftType::Lsl,
                shift_amount: 0,
            },
        );
        out.push(isa::Instr::BCond { cond: 0, imm19: rel });
        proof {
            let ii = (i + 1) as nat;
            let r = brt_rel(offs, ls@[i as int], (4 + i * 12 + 8) as int);
            assert(r == 4 * (tgt as int - pos as int));
            assert(r / 4 == rel as int);
            assert(brt_upto(ls@, offs, ii) == brt_upto(ls@, offs, i as nat) + brt_entry(
                i as nat,
                r,
            ));
            assert(brt_entry(i as nat, r) =~= seq![
                isa::Instr::MoveWide {
                    sf: isa::Width::W32,
                    opcode: isa::MoveWideOp::Z,
                    d: 1,
                    imm16: i as u16,
                    hw: 0,
                },
                isa::Instr::AddSubShiftedReg {
                    sf: isa::Width::W32,
                    sub_op: true,
                    setflags: true,
                    d: 31,
                    n: 0,
                    m: 1,
                    shift_type: isa::ShiftType::Lsl,
                    shift_amount: 0,
                },
                isa::Instr::BCond { cond: 0, imm19: rel },
            ]);
            assert(out@ =~= old_out + seq![load_slot(x0(), (nl + h - 1) as nat)] + brt_upto(
                ls@,
                offs,
                ii,
            ));
        }
        i = add_u(i, 1);
    }
    let tgt = match labs.get(d) {
        Some(t) => *t,
        None => {
            proof {
                assert(false);
            }
            return ;
        },
    };
    let pos = add_u(add_u(start, 1), mul_u(3, ls.len()));
    let rl = relw(tgt, pos);
    out.push(isa::Instr::B { imm26: rl });
    proof {
        lemma_brt_upto(ls@, offs, ls@.len());
        assert(brt_entries(ls@, offs, 4, ls@.len() as nat) =~= Seq::<isa::Instr>::empty());
        assert(brt_p0(nl as nat, h as nat) == 4);
        assert(brt_e() == 12);
        assert(brt_upto(ls@, offs, ls@.len()) =~= brt_entries(ls@, offs, 4, 0));
        let r = brt_rel(offs, d, (4 + ls@.len() * 12) as int);
        assert(r == 4 * (tgt as int - pos as int));
        assert(r / 4 == rl as int);
        assert(out@ =~= old_out + brt_code(ls@, d, nl as nat, h as nat, offs));
    }
}

// ----------------------------------------------------------------------------
// The analysis
// ----------------------------------------------------------------------------

/// Every node is templated in this slice.
proof fn lemma_templated_all(n: Node)
    ensures
        templated(n),
    decreases n,
{
    match n {
        Node::Then(a, b) => {
            lemma_templated_all(*a);
            lemma_templated_all(*b);
        },
        Node::Block(b) => {
            lemma_templated_all(*b);
        },
        Node::Loop(b) => {
            lemma_templated_all(*b);
        },
        Node::If(t, e) => {
            lemma_templated_all(*t);
            lemma_templated_all(*e);
        },
        _ => {},
    }
}

/// The analysis of `n` (the spec's `cf_flow`), entered at height `h` with `nl`
/// locals and `labs.len()` labels in scope, and the size of its code in words
/// (a quarter of the spec's `csize`). `None` only if it has no translation, or
/// its code is larger than `max_size`.
#[verifier::spinoff_prover]
#[verifier::rlimit(1500)]
fn analyze(n: &Node, nl: usize, h: usize, labs: &[usize]) -> (r: Option<(Option<usize>, usize)>)
    requires
        nl <= 31,
        h <= 31,
        codes_ok(*n),
    ensures
        match r {
            Some((f, s)) => {
                &&& cf_flow(*n, nl as nat, h as nat, labs@.len()) == Some(fl_spec(f))
                &&& 4 * s == csize(*n, nl as nat, h as nat, labs@.len())
                &&& s <= MAX_WORDS
                &&& match f {
                    Some(x) => x <= 31,
                    None => true,
                }
            },
            None => cf_flow(*n, nl as nat, h as nat, labs@.len()) is None || csize(
                *n,
                nl as nat,
                h as nat,
                labs@.len(),
            ) > max_size(),
        },
    decreases *n,
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
    }
    let depth = labs.len();
    let room = add_u(nl, h) <= 31;
    match n {
        Node::Op(o) => {
            let ok = op_ok_exec(o, nl, h);
            if !ok {
                return None;
            }
            let mut v: Vec<isa::Instr> = Vec::new();
            emit_op(o, nl, h, &mut v);
            proof {
                assert(v@ =~= tmpl(*o, nl as nat, h as nat));
                assert(csize(*n, nl as nat, h as nat, depth as nat) == code_len(v@));
            }
            let sz = v.len();
            if sz > MAX_WORDS {
                return None;
            }
            let h2 = add_u(sub_u(h, pops_exec(o)), pushes_exec(o));
            Some((Some(h2), sz))
        },
        Node::Mem(m) => {
            let ok = room && match m {
                MemOp::BoundsCheck { region, size, .. } => h >= 1 && *region < 16 && 1 <= *size
                    && *size <= 8,
                MemOp::Load { region, .. } => h >= 1 && *region < 16,
                MemOp::Store { region, .. } => h >= 2 && *region < 16,
            };
            if !ok {
                return None;
            }
            let h2 = match m {
                MemOp::Store { .. } => sub_u(h, 2),
                _ => h,
            };
            proof {
                assert(cf_flow(*n, nl as nat, h as nat, depth as nat) is Some);
            }
            let mut v: Vec<isa::Instr> = Vec::new();
            mem_code_exec(m, nl, h, &mut v);
            proof {
                assert(v@ =~= mem_code(*m, nl as nat, h as nat));
                assert(csize(*n, nl as nat, h as nat, depth as nat) == code_len(v@));
            }
            let sz = v.len();
            if sz > MAX_WORDS {
                return None;
            }
            Some((Some(h2), sz))
        },
        Node::Then(a, b) => {
            proof {
                lemma_csize_then(**a, **b, nl as nat, h as nat, depth as nat);
            }
            let (fa, sa) = match analyze(a, nl, h, labs) {
                Some(x) => x,
                None => {
                    return None;
                },
            };
            match fa {
                Some(h1) => {
                    let (fb, sb) = match analyze(b, nl, h1, labs) {
                        Some(x) => x,
                        None => {
                            return None;
                        },
                    };
                    let s = add_u(sa, sb);
                    if s > MAX_WORDS {
                        return None;
                    }
                    Some((fb, s))
                },
                None => {
                    if matches!(&**b, Node::Op(crate::spec::Op::Nop)) {
                        proof {
                            assert(csize(**b, nl as nat, h as nat, depth as nat) == 0) by {
                                assert(ctmpl(**b, nl as nat, h as nat, zeros(depth as nat))
                                    =~= Seq::<isa::Instr>::empty());
                            }
                        }
                        Some((None, sa))
                    } else {
                        None
                    }
                },
            }
        },
        Node::Block(b) | Node::Loop(b) => {
            proof {
                if n is Block {
                    lemma_csize_block(**b, nl as nat, h as nat, depth as nat);
                } else {
                    lemma_csize_loop(**b, nl as nat, h as nat, depth as nat);
                }
            }
            let l0 = push_label(0, labs);
            let (fb, sb) = match analyze(b, nl, h, l0.as_slice()) {
                Some(x) => x,
                None => {
                    return None;
                },
            };
            let bad = match fb {
                Some(h1) => h1 != h,
                None => false,
            };
            if bad {
                return None;
            }
            Some((Some(h), sb))
        },
        Node::If(t, e) => {
            if h < 1 || !room {
                return None;
            }
            let h1 = sub_u(h, 1);
            proof {
                lemma_csize_if(**t, **e, nl as nat, h as nat, depth as nat);
            }
            let l0 = push_label(0, labs);
            let (ft, st) = match analyze(t, nl, h1, l0.as_slice()) {
                Some(x) => x,
                None => {
                    return None;
                },
            };
            let (fe, se) = match analyze(e, nl, h1, l0.as_slice()) {
                Some(x) => x,
                None => {
                    return None;
                },
            };
            let fits_t = match ft {
                Some(x) => x == h1,
                None => true,
            };
            let fits_e = match fe {
                Some(x) => x == h1,
                None => true,
            };
            if !fits_t || !fits_e {
                return None;
            }
            let s = add_u(add_u(add_u(2, st), 1), se);
            if s > MAX_WORDS {
                return None;
            }
            Some((Some(h1), s))
        },
        Node::Br(l) => {
            proof {
                lemma_csize_br(*l, nl as nat, h as nat, depth as nat);
            }
            if *l < depth {
                Some((None, 1))
            } else {
                None
            }
        },
        Node::BrIf(l) => {
            proof {
                lemma_csize_brif(*l, nl as nat, h as nat, depth as nat);
            }
            if *l < depth && h >= 1 && room {
                Some((Some(sub_u(h, 1)), 2))
            } else {
                None
            }
        },
        Node::BrTable(ls, d) => {
            if !(*d < depth && h >= 1 && room && ls.len() <= MAX_TARGETS) {
                return None;
            }
            let mut i: usize = 0;
            while i < ls.len()
                invariant
                    i <= ls.len(),
                    depth == labs@.len(),
                    *n == Node::BrTable(*ls, *d),
                    *d < depth,
                    1 <= h,
                    nl + h <= 31,
                    ls@.len() <= 0x10000,
                    forall|j: int| 0 <= j < i ==> #[trigger] ls@[j] < depth,
                decreases ls.len() - i,
            {
                let l = match ls.get(i) {
                    Some(l) => *l,
                    None => {
                        proof {
                            assert(false);
                        }
                        return None;
                    },
                };
                if l >= depth {
                    proof {
                        assert(ls@[i as int] >= depth);
                    }
                    return None;
                }
                i = add_u(i, 1);
            }
            proof {
                lemma_brt_len(ls@, *d, nl as nat, h as nat, zeros(depth as nat));
                assert(csize(*n, nl as nat, h as nat, depth as nat) == 8 + 12 * ls@.len());
            }
            let s = add_u(2, mul_u(3, ls.len()));
            if s > MAX_WORDS {
                return None;
            }
            Some((None, s))
        },
        Node::Exit(_, k) => {
            proof {
                assert(csize(*n, nl as nat, h as nat, depth as nat) == 12);
            }
            if *k <= h && room {
                Some((None, 3))
            } else {
                None
            }
        },
    }
}

// ----------------------------------------------------------------------------
// The emission
// ----------------------------------------------------------------------------

/// The facts every emission function needs of its node.
pub open spec fn emit_pre(n: Node, nl: usize, h: usize, start: usize, labs: Seq<usize>) -> bool {
    nl <= 31 && h <= 31 && cf_flow(n, nl as nat, h as nat, labs.len()) is Some && codes_ok(n)
        && start + csize(n, nl as nat, h as nat, labs.len()) / 4 <= MAX_WORDS && forall|i: int|
        0 <= i < labs.len() ==> #[trigger] labs[i] <= MAX_WORDS
}

/// `then a b`.
fn emit_then(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<isa::Instr>)
    requires
        n is Then,
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, offs_of(labs@, start as int)),
    decreases *n, 0nat,
{
    let ghost old_out = out@;
    let ghost offs = offs_of(labs@, start as int);
    if let Node::Then(a, b) = n {
        {
            proof {
                super::tlemmas::lemma_abi_consts_t();
                lemma_csize_then(**a, **b, nl as nat, h as nat, labs@.len());
            }
            let (fa, sa) = emit_node(a, nl, h, start, labs, out);
            if let Some(h1) = fa {
                proof {
                    lemma_offs_shift(labs@, start as int, sa as int);
                }
                emit_node(b, nl, h1, add_u(start, sa), labs, out);
                proof {
                    assert(flow_h(**a, nl as nat, h as nat, labs@.len()) == h1 as nat);
                    assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
                }
            } else {
                proof {
                    lemma_offs_shift(labs@, start as int, sa as int);
                    assert(ctmpl(**b, nl as nat, h as nat, shift(offs, 4 * sa as int))
                        =~= Seq::<isa::Instr>::empty());
                    assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
                }
            }
        }
    }
}

/// `block b`.
fn emit_block(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<isa::Instr>)
    requires
        n is Block,
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, offs_of(labs@, start as int)),
    decreases *n, 0nat,
{
    let ghost offs = offs_of(labs@, start as int);
    if let Node::Block(b) = n {
        {
            proof {
                super::tlemmas::lemma_abi_consts_t();
                lemma_csize_block(**b, nl as nat, h as nat, labs@.len());
            }
            let l0 = push_label(0, labs);
            let sb = match analyze(b, nl, h, l0.as_slice()) {
                Some(x) => x.1,
                None => {
                    proof {
                        assert(false);
                    }
                    return ;
                },
            };
            let l = push_label(add_u(start, sb), labs);
            proof {
                lemma_offs_push(labs@, (start + sb) as usize, start as int);
                assert(offs_of(l@, start as int) =~= seq![4 * sb as int] + offs);
            }
            emit_node(b, nl, h, start, l.as_slice(), out);
        }
    }
}

/// `loop b`.
fn emit_loop(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<isa::Instr>)
    requires
        n is Loop,
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, offs_of(labs@, start as int)),
    decreases *n, 0nat,
{
    let ghost offs = offs_of(labs@, start as int);
    if let Node::Loop(b) = n {
        {
            proof {
                super::tlemmas::lemma_abi_consts_t();
                lemma_csize_loop(**b, nl as nat, h as nat, labs@.len());
            }
            let l = push_label(start, labs);
            proof {
                lemma_offs_push(labs@, start, start as int);
                assert(offs_of(l@, start as int) =~= seq![0int] + offs);
            }
            emit_node(b, nl, h, start, l.as_slice(), out);
        }
    }
}

/// `if t e`.
fn emit_if(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<isa::Instr>)
    requires
        n is If,
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, offs_of(labs@, start as int)),
    decreases *n, 0nat,
{
    let ghost old_out = out@;
    let ghost offs = offs_of(labs@, start as int);
    if let Node::If(t, e) = n {
        {
            proof {
                super::tlemmas::lemma_abi_consts_t();
            }
            let h1 = sub_u(h, 1);
            proof {
                lemma_csize_if(**t, **e, nl as nat, h as nat, labs@.len());
            }
            let l0 = push_label(0, labs);
            let st = match analyze(t, nl, h1, l0.as_slice()) {
                Some(x) => x.1,
                None => {
                    proof {
                        assert(false);
                    }
                    return ;
                },
            };
            let se = match analyze(e, nl, h1, l0.as_slice()) {
                Some(x) => x.1,
                None => {
                    proof {
                        assert(false);
                    }
                    return ;
                },
            };
            let end = add_u(add_u(add_u(add_u(start, 2), st), 1), se);
            let l = push_label(end, labs);
            let skip = add_u(st, 2) as i32;
            cond_pre_exec(nl, h, true, skip, out);
            let tstart = add_u(start, 2);
            proof {
                lemma_offs_push(labs@, end, tstart as int);
                lemma_offs_shift(labs@, start as int, 2);
                assert(offs_of(l@, tstart as int) =~= seq![4 * st as int + 4 + 4 * se as int]
                    + shift(offs, 8));
            }
            emit_node(t, nl, h1, tstart, l.as_slice(), out);
            out.push(isa::Instr::B { imm26: add_u(se, 1) as i32 });
            let estart = add_u(tstart, add_u(st, 1));
            proof {
                lemma_offs_push(labs@, end, estart as int);
                lemma_offs_shift(labs@, start as int, 2 + st as int + 1);
                assert(offs_of(l@, estart as int) =~= seq![4 * se as int] + shift(
                    offs,
                    12 + 4 * st as int,
                ));
                assert(b_i(4 * se as int + 4) == isa::Instr::B { imm26: (se + 1) as i32 });
            }
            emit_node(e, nl, h1, estart, l.as_slice(), out);
            proof {
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
            }
        }
    }
}

/// `br l` and `br_if l`.
fn emit_br(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<isa::Instr>)
    requires
        n is Br || n is BrIf,
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, offs_of(labs@, start as int)),
{
    let ghost old_out = out@;
    let ghost offs = offs_of(labs@, start as int);
    proof {
        super::tlemmas::lemma_abi_consts_t();
    }
    match n {
        Node::Br(l) => {
            proof {
                lemma_csize_br(*l, nl as nat, h as nat, labs@.len());
            }
            let tgt = match labs.get(*l) {
                Some(t) => *t,
                None => {
                    proof {
                        assert(false);
                    }
                    return ;
                },
            };
            let r = relw(tgt, start);
            out.push(isa::Instr::B { imm26: r });
            proof {
                assert(offs[*l as int] == 4 * (tgt as int - start as int));
                assert((4 * (tgt as int - start as int)) / 4 == r as int);
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
            }
        },
        Node::BrIf(l) => {
            proof {
                lemma_csize_brif(*l, nl as nat, h as nat, labs@.len());
            }
            let tgt = match labs.get(*l) {
                Some(t) => *t,
                None => {
                    proof {
                        assert(false);
                    }
                    return ;
                },
            };
            let rel = relw(tgt, add_u(start, 1));
            cond_pre_exec(nl, h, false, rel, out);
            proof {
                assert(offs[*l as int] == 4 * (tgt as int - start as int));
                assert(offs[*l as int] - 4 == 4 * (rel as int));
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
            }
        },
        _ => {},
    }
}

/// `br_table`, `exit`, memory and straight-line instructions.
fn emit_leaf(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<isa::Instr>)
    requires
        n is BrTable || n is Exit || n is Mem || n is Op,
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, offs_of(labs@, start as int)),
{
    let ghost old_out = out@;
    let ghost offs = offs_of(labs@, start as int);
    proof {
        super::tlemmas::lemma_abi_consts_t();
    }
    match n {
        Node::Op(o) => {
            emit_op(o, nl, h, out);
            proof {
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
            }
        },
        Node::Mem(m) => {
            mem_code_exec(m, nl, h, out);
        },
        Node::BrTable(ls, d) => {
            proof {
                lemma_brt_len(ls@, *d, nl as nat, h as nat, zeros(labs@.len()));
            }
            brt_exec(ls.as_slice(), *d, nl, h, start, labs, out);
        },
        Node::Exit(c, _) => {
            emit_exit(out, *c as u16);
        },
        _ => {},
    }
}

/// Append the code of `n` at the absolute word `start`, with the labels in
/// scope at the absolute words `labs`: exactly [`ctmpl`]. Returns the flow and
/// the size in words, as [`analyze`] does.
fn emit_node(
    n: &Node,
    nl: usize,
    h: usize,
    start: usize,
    labs: &[usize],
    out: &mut Vec<isa::Instr>,
) -> (r: (Option<usize>, usize))
    requires
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(
            *n,
            nl as nat,
            h as nat,
            offs_of(labs@, start as int),
        ),
        cf_flow(*n, nl as nat, h as nat, labs@.len()) == Some(fl_spec(r.0)),
        4 * r.1 == csize(*n, nl as nat, h as nat, labs@.len()),
        match r.0 {
            Some(x) => x <= 31,
            None => true,
        },
    decreases *n, 1nat,
{
    let (flow, size) = match analyze(n, nl, h, labs) {
        Some(x) => x,
        None => {
            proof {
                assert(false);
            }
            return (None, 0);
        },
    };
    match n {
        Node::Then(..) => emit_then(n, nl, h, start, labs, out),
        Node::Block(..) => emit_block(n, nl, h, start, labs, out),
        Node::Loop(..) => emit_loop(n, nl, h, start, labs, out),
        Node::If(..) => emit_if(n, nl, h, start, labs, out),
        Node::Br(..) => emit_br(n, nl, h, start, labs, out),
        Node::BrIf(..) => emit_br(n, nl, h, start, labs, out),
        _ => emit_leaf(n, nl, h, start, labs, out),
    }
    (flow, size)
}

/// Encode `code` to bytes: the canonical word of each instruction.
fn encode_code(code: &[isa::Instr]) -> (bytes: Vec<u8>)
    requires
        all_valid_instrs(code@),
    ensures
        clazel_codecheck::a64::spec::decodes_to(bytes@, code@),
{
    let mut bytes: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < code.len()
        invariant
            k <= code.len(),
            bytes@.len() == 4 * k,
            forall|j: int|
                0 <= j < k ==> #[trigger] bytes@.subrange(4 * j, 4 * j + 4) == isa::word_bytes(
                    isa::encode(code@[j]),
                ),
            all_valid_instrs(code@),
        decreases code.len() - k,
    {
        let ins = match code.get(k) {
            Some(ins) => ins,
            None => {
                proof {
                    assert(false);
                }
                return bytes;
            },
        };
        let w = encode_instr(ins);
        let ghost old_bytes = bytes@;
        bytes.push((w % 256) as u8);
        bytes.push(((w / 0x100) % 256) as u8);
        bytes.push(((w / 0x1_0000) % 256) as u8);
        bytes.push((w / 0x100_0000) as u8);
        proof {
            assert(ins == &code@[k as int]);
            assert(w as int == isa::encode(code@[k as int]));
            assert(w as int / 0x100_0000 < 0x100);
            let b = isa::word_bytes(isa::encode(code@[k as int]));
            assert(bytes@ =~= old_bytes + b);
            assert forall|j: int| 0 <= j < k + 1 implies #[trigger] bytes@.subrange(4 * j, 4 * j + 4)
                == isa::word_bytes(isa::encode(code@[j])) by {
                if j < k {
                    assert(bytes@.subrange(4 * j, 4 * j + 4) =~= old_bytes.subrange(
                        4 * j,
                        4 * j + 4,
                    ));
                } else {
                    assert(bytes@.subrange(4 * j, 4 * j + 4) =~= b);
                }
            }
        }
        k = add_u(k, 1);
    }
    proof {
        assert(clazel_codecheck::a64::spec::decodes_to(bytes@, code@)) by {
            assert(bytes@.len() == 4 * code@.len());
        }
    }
    bytes
}

/// **Every emitted blob refines its program.** If the emitter answers with
/// `bytes`, the encoded body is [`ctmpl`] of the program with the return label
/// at its end, which refines it.
pub proof fn lemma_emitted_refines(n: Node, nl: usize, exit_code: u16, bytes: Seq<u8>)
    requires
        emit_cf_blob_ensures(n, nl, exit_code, Some(bytes)),
    ensures
        cf_prog_ok(n, nl as nat),
        exists|body: Seq<isa::Instr>|
            #![trigger all_valid_instrs(body)]
            all_valid_instrs(body) && cf_refines(
                n@,
                nl as nat,
                0,
                seq![code_len(body) as int],
                body,
            ) && clazel_codecheck::a64::spec::decodes_to(bytes, body + exit_seq(exit_code)),
{
}

/// Emit the body of the function `n` with `nl` locals as encoded bytes,
/// followed by the exit sequence for `exit_code`. The function's return label
/// (a `br` to it, and falling off the end) is the exit sequence. `None` if the
/// program has no translation.
///
/// **Proven**: [`super::cfcontract::emit_cf_blob_ensures`].
#[verifier::rlimit(500)]
pub fn emit_cf_blob(n: &Node, nl: usize, exit_code: u16) -> (r: Option<Vec<u8>>)
    ensures
        emit_cf_blob_ensures(*n, nl, exit_code, match r {
            Some(v) => Some(v@),
            None => None,
        }),
{
    proof {
        super::tlemmas::lemma_abi_consts_t();
        lemma_templated_all(*n);
    }
    if nl > 31 {
        return None;
    }
    if !codes_ok_exec(n) {
        return None;
    }
    let l1: Vec<usize> = push_label(0, &[]);
    let size = match analyze(n, nl, 0, l1.as_slice()) {
        Some((_, s)) => s,
        None => {
            return None;
        },
    };
    let labs: Vec<usize> = push_label(size, &[]);
    let mut body: Vec<isa::Instr> = Vec::new();
    proof {
        assert(4 * size == csize(*n, nl as nat, 0, 1));
    }
    emit_node(n, nl, 0, 0, labs.as_slice(), &mut body);
    let ghost body_seq = body@;
    emit_exit(&mut body, exit_code);
    proof {
        let offs = offs_of(labs@, 0);
        assert(offs =~= seq![4 * size as int]);
        lemma_ctmpl_len(*n, nl as nat, 0, offs);
        assert(labels_fit(offs, 4 * size as nat));
        lemma_ctmpl_refines(*n, nl as nat, 0, offs);
        super::tlemmas::lemma_exit_valid(exit_code);
        assert(Seq::<isa::Instr>::empty() + body_seq =~= body_seq);
        assert(all_valid_instrs(body@)) by {
            assert forall|k: int| 0 <= k < body@.len() implies isa::valid_instr(
                #[trigger] body@[k],
            ) by {
                if k < body_seq.len() {
                    assert(body@[k] == body_seq[k]);
                } else {
                    assert(body@[k] == exit_seq(exit_code)[k - body_seq.len()]);
                }
            }
        }
    }
    let bytes = encode_code(body.as_slice());
    Some(bytes)
}

} // verus!

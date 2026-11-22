//! The executable back end for **structured control flow, memory
//! instructions and `br_table`** (x86-64): [`emit_cf_blob`], **proven equal
//! to the templates**.
//!
//! [`emit_cf_blob`]'s postcondition is
//! [`crate::cfcontract::emit_cf_blob_ensures`]: the bytes it returns are the
//! encoding of [`crate::cftemplates::ctmpl`] (the body, with the return label
//! at its end) followed by the exit sequence, and it answers `None` exactly
//! when [`crate::cftemplates::cf_prog_ok`] refuses. Together with
//! [`crate::cfproofs::lemma_ctmpl_refines`] that makes every emitted blob a
//! refinement of its program ([`lemma_emitted_refines`]).
//!
//! # How it is proven
//!
//! - **Labels** are absolute byte positions in the body (`labs`, label 0
//!   first); the spec's `offs` of a node that starts at `start` are
//!   [`offs_of`]`(labs, start)` (position minus start). `then`, `block`,
//!   `loop` and `if` change `labs` and `start` exactly as `ctmpl` changes
//!   `offs` ([`lemma_offs_shift`], [`lemma_offs_push`]).
//! - **No signed arithmetic.** Verus's `vstd` specifies `checked_*` and
//!   `saturating_*` for unsigned types only, and `i32::try_from(i64)` has no
//!   spec. Every position is a `usize` below [`MAX_SIZE`] (the spec's
//!   `max_size`), and a displacement is `target - end` when the target is
//!   not before the end, else the two's complement of `end - target`, formed
//!   as `!(end - target - 1)` on a `u32` ([`rel32`], [`lemma_not_neg`]), so
//!   the workspace's `arithmetic_side_effects` lint holds with no `#[allow]`
//!   and nothing is trusted.
//! - **The size analysis** [`analyze`] equals `cf_flow` and `csize`: it
//!   returns the flow and the size when the node has a translation of at most
//!   [`MAX_SIZE`] bytes, and refuses (`None`) only if `cf_flow` does or the
//!   size exceeds `max_size` (a node's size is at most that of the nodes
//!   around it, `cflens`). Overflow is excluded: a size is summed only after
//!   each part is at most [`MAX_SIZE`], and the label count is the length of
//!   a `Vec`.
//! - **The emission** [`emit_node`] appends exactly `ctmpl`, by induction on
//!   the node, each leaf by its own function ([`mem_code_exec`],
//!   [`brt_exec`], `emit_op` from the first slice, ...).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfcompose::lemma_shift_index;
#[cfg(verus_only)]
use crate::cfblobacc::{emit_cf_blob_accepted_ensures, emitted_bytes, lemma_emitter_accepted};
#[cfg(verus_only)]
use crate::cfcontract::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfmemvalid::lemma_mem_valid;
#[cfg(verus_only)]
use crate::cfproofs::*;
#[cfg(verus_only)]
use crate::cfspec::*;
use crate::cfspec::{MTy, MemOp, Node};
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::cfvalid::lemma_ctmpl_valid;
#[cfg(verus_only)]
use crate::contract::*;
use crate::emit::{emit_exit, emit_op, ex_load, ex_store, op_ok_exec, pops_exec, pushes_exec};
#[cfg(verus_only)]
use crate::templates::*;
use clazel_x64::encoder::encode_exec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The largest body this emitter translates, in bytes (the spec's
/// `cftemplates::max_size`).
pub const MAX_SIZE: usize = 0x2000_0000;

/// The most targets of a `br_table` (the spec's `max_targets`).
pub const MAX_TARGETS: usize = 0x10000;

/// The emitter's limits are the spec's: a larger body, or a `br_table` with
/// more targets, is refused exactly where `cf_prog_ok` and `cf_flow` refuse it.
pub proof fn lemma_emitter_limits()
    ensures
        MAX_SIZE as nat == max_size(),
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

/// The displacement from a jump that ends at `end` to `target`. Both are at
/// most [`MAX_SIZE`], so it fits an `i32`; a negative one is the two's
/// complement `!(end - target - 1)`.
fn rel32(target: usize, end: usize) -> (r: i32)
    requires
        target <= MAX_SIZE,
        end <= MAX_SIZE,
    ensures
        r as int == target as int - end as int,
{
    if target >= end {
        let d = sub_u(target, end);
        d as i32
    } else {
        let d1 = sub_u(sub_u(end, target), 1);
        let x = d1 as u32;
        let y = !x;
        proof {
            lemma_not_neg(x);
        }
        y as i32
    }
}

/// The length in bytes of the encodings of `code`, or `None` if it does not
/// fit a `usize`.
fn code_bytes(code: &[x64::Instr])  -> (r: Option<usize>)
    requires
        all_valid_instrs(code@),
    ensures
        match r {
            Some(n) => n == code_len(code@),
            None => code_len(code@) > usize::MAX,
        },
{
    let mut acc: usize = 0;
    let mut k: usize = 0;
    proof {
        assert(code@.take(0) =~= Seq::<x64::Instr>::empty());
    }
    while k < code.len()
        invariant
            k <= code.len(),
            acc == code_len(code@.take(k as int)),
            all_valid_instrs(code@),
        decreases code.len() - k,
    {
        let ins = match code.get(k) {
            Some(ins) => ins,
            None => {
                proof {
                    assert(false);
                }
                return None;
            },
        };
        let e = encode_exec(ins);
        let l = e.len();
        proof {
            assert(e@ =~= x64::encode(code@[k as int]));
            let t = code@.take(k as int + 1);
            assert(t =~= code@.take(k as int) + seq![code@[k as int]]);
            crate::runseq::lemma_code_len_append(code@.take(k as int), seq![code@[k as int]]);
            crate::runseq::lemma_code_len_one(code@[k as int]);
            assert(code@ =~= t + code@.skip(k as int + 1));
            crate::runseq::lemma_code_len_append(t, code@.skip(k as int + 1));
        }
        match acc.checked_add(l) {
            Some(a) => {
                acc = a;
            },
            None => {
                return None;
            },
        }
        k = add_u(k, 1);
        proof {
            assert(k == code@.take(k as int).len() || true);
        }
    }
    proof {
        assert(code@.take(code.len() as int) =~= code@);
    }
    Some(acc)
}

// ----------------------------------------------------------------------------
// Labels
// ----------------------------------------------------------------------------

/// The spec's label offsets for a node that starts at `start`, when the labels
/// are at the absolute positions `labs`.
pub open spec fn offs_of(labs: Seq<usize>, start: int) -> Seq<int> {
    Seq::new(labs.len(), |i: int| labs[i] as int - start)
}

/// Moving the start on by `d` is [`shift`].
proof fn lemma_offs_shift(labs: Seq<usize>, start: int, d: int)
    ensures
        offs_of(labs, start + d) =~= shift(offs_of(labs, start), d),
{
    let o = offs_of(labs, start);
    assert forall|i: int| 0 <= i < labs.len() implies #[trigger] offs_of(labs, start + d)[i]
        == shift(o, d)[i] by {
        lemma_shift_index(o, d, i);
    }
}

/// A new label in front, at the absolute position `new`.
proof fn lemma_offs_push(labs: Seq<usize>, new: usize, start: int)
    ensures
        offs_of(seq![new] + labs, start) =~= seq![new as int - start] + offs_of(labs, start),
{
    let l = seq![new] + labs;
    let r = seq![new as int - start] + offs_of(labs, start);
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

/// The condition test is 16 bytes (8, 2, 6).
proof fn lemma_cond_len_16(nl: nat, h: nat)
    ensures
        cond_len(nl, h) == 16,
{
    let a = load_slot(rax(), (nl + h - 1) as nat);
    let b = x64::Instr::TestRR { sz: x64::Size::W32, a: rax(), b: rax() };
    crate::cfmemlens::lemma_mem_instr_lens((nl + h - 1) as nat, 0);
    lemma_jcc_len(0, 0);
    assert(x64::encode(b).len() == 2);
    crate::runseq::lemma_len3(a, b, jcc_i(0, 0));
    crate::runseq::lemma_len1(a);
}

/// `mov rax, [r15 + 264 + 8 (nl + h - 1)]; test eax, eax; jcc cc rel`.
fn cond_pre_exec(nl: usize, h: usize, cc: u8, rel: i32, v: &mut Vec<x64::Instr>)
    requires
        1 <= h,
        nl + h <= 31,
    ensures
        final(v)@ == old(v)@ + cond_pre(nl as nat, h as nat, cc, rel as int),
{
    let ghost ov = v@;
    let top = sub_u(add_u(nl, h), 1);
    v.push(ex_load(0, top));
    v.push(x64::Instr::TestRR { sz: x64::Size::W32, a: 0, b: 0 });
    v.push(x64::Instr::Jcc { cc, rel });
    proof {
        assert(v@ =~= ov + cond_pre(nl as nat, h as nat, cc, rel as int));
    }
}

/// The operand size of an access.
fn mty_sz_exec(ty: &MTy) -> (s: x64::Size)
    ensures
        s == mty_sz(*ty),
{
    match ty {
        MTy::I32 => x64::Size::W32,
        MTy::I64 => x64::Size::W64,
        MTy::F64 => x64::Size::W64,
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

/// `[rsi + rcx]`.
fn ix_mem_exec() -> (m: x64::Mem)
    ensures
        m == ix_mem(),
{
    x64::Mem { base: 6, index: Some(x64::Index { reg: 1, scale: 0 }), disp: 0 }
}

/// `[r15 + 16 k]`: region `k`'s base.
fn base_mem_exec(k: usize) -> (m: x64::Mem)
    requires
        k < 16,
    ensures
        m == base_mem(k as nat),
{
    proof {
        crate::steps::lemma_abi_consts();
    }
    let d = mul_u(k, 16);
    x64::Mem { base: 15, index: None, disp: d as i32 }
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
    crate::tlemmas::lemma_abi_consts_t();
}

/// What a memory instruction does before its check.
fn mem_pre_exec(m: &MemOp, nl: usize, h: usize, v: &mut Vec<x64::Instr>)
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
            v.push(x64::Instr::MovLoad { sz: x64::Size::W64, dst: 6, mem: base_mem_exec(*region) });
        },
        MemOp::Store { region, .. } => {
            v.push(ex_load(7, top));
            v.push(ex_load(1, sub_u(top, 1)));
            v.push(x64::Instr::MovLoad { sz: x64::Size::W64, dst: 6, mem: base_mem_exec(*region) });
        },
    }
    proof {
        assert(v@ =~= ov + mem_pre(*m, nl as nat, h as nat));
    }
}

/// What a memory instruction does after its check.
fn mem_tail_exec(m: &MemOp, nl: usize, h: usize, v: &mut Vec<x64::Instr>)
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
            v.push(x64::Instr::MovLoad { sz: mty_sz_exec(ty), dst: 0, mem: ix_mem_exec() });
            v.push(ex_store(top, 0));
        },
        MemOp::Store { ty, .. } => {
            v.push(x64::Instr::MovStore { sz: mty_sz_exec(ty), mem: ix_mem_exec(), src: 7 });
        },
    }
    proof {
        assert(v@ =~= ov + mem_tail(*m, nl as nat, h as nat));
    }
}

/// Append the code of a memory instruction (`mem_code`): the operands, the
/// validator's bounds check, the access, a `jmp` over the stub, the stub.
fn mem_code_exec(m: &MemOp, nl: usize, h: usize, out: &mut Vec<x64::Instr>)
    requires
        cf_flow(Node::Mem(*m), nl as nat, h as nat, 0) is Some,
    ensures
        final(out)@ == old(out)@ + mem_code(*m, nl as nat, h as nat),
{
    proof {
        lemma_mem_facts(*m, nl as nat, h as nat);
        lemma_mem_parts_len(*m, nl as nat, h as nat);
        crate::steps::lemma_abi_consts();
    }
    let ghost old_out = out@;
    let (region, n, exit_code, tl): (usize, usize, u32, usize) = match m {
        MemOp::BoundsCheck { region, size, code } => (*region, *size, *code, 0),
        MemOp::Load { region, ty } => (*region, mty_size_exec(ty), 0xFFFF_FFFF, match ty {
            MTy::I32 => 15,
            _ => 16,
        }),
        MemOp::Store { region, ty } => (*region, mty_size_exec(ty), 0xFFFF_FFFF, match ty {
            MTy::I32 => 7,
            _ => 8,
        }),
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
        assert(tl as nat == code_len(mem_tail(*m, nl as nat, h as nat)));
        assert(n <= 8);
    }
    mem_pre_exec(m, nl, h, out);
    let r1 = add_u(36, tl) as i32;
    let r2 = add_u(22, tl) as i32;
    let bd = add_u(mul_u(region, 16), 8) as i32;
    out.push(x64::Instr::MovRR { sz: x64::Size::W64, dst: 2, src: 1 });
    out.push(x64::Instr::AluRI { alu: x64::AluOp::Add, sz: x64::Size::W64, dst: 2, imm: n as i32 });
    out.push(x64::Instr::Jcc { cc: 2, rel: r1 });
    out.push(
        x64::Instr::AluRM {
            alu: x64::AluOp::Cmp,
            sz: x64::Size::W64,
            dst: 2,
            mem: x64::Mem { base: 15, index: None, disp: bd },
        },
    );
    out.push(x64::Instr::Jcc { cc: 7, rel: r2 });
    out.push(x64::Instr::MovImm32 { dst: 0, imm_u32: 0 });
    out.push(
        x64::Instr::AluRM {
            alu: x64::AluOp::Cmp,
            sz: x64::Size::W64,
            dst: 1,
            mem: x64::Mem { base: 15, index: None, disp: bd },
        },
    );
    out.push(x64::Instr::Cmovcc { cc: 3, sz: x64::Size::W64, dst: 1, src: 0 });
    mem_tail_exec(m, nl, h, out);
    out.push(x64::Instr::Jmp { rel: 14 });
    let ghost before_stub = out@;
    emit_exit(out, exit_code);
    proof {
        let c = mem_chk(mem_region(*m), mem_n(*m), mem_r1(*m, nl as nat, h as nat), mem_r2(
            *m,
            nl as nat,
            h as nat,
        ));
        let cs = clazel_codecheck::spec::check_seq(c);
        assert(r1 as int == mem_r1(*m, nl as nat, h as nat));
        assert(r2 as int == mem_r2(*m, nl as nat, h as nat));
        assert(bd as int == abi::bound_off(mem_region(*m) as int));
        crate::cfmemlens::lemma_exit_seq_len(mem_exit_code(*m));
        assert(cs =~= seq![
            x64::Instr::MovRR { sz: x64::Size::W64, dst: 2, src: 1 },
            x64::Instr::AluRI { alu: x64::AluOp::Add, sz: x64::Size::W64, dst: 2, imm: n as i32 },
            x64::Instr::Jcc { cc: 2, rel: r1 },
            x64::Instr::AluRM {
                alu: x64::AluOp::Cmp,
                sz: x64::Size::W64,
                dst: 2,
                mem: x64::Mem { base: 15, index: None, disp: bd },
            },
            x64::Instr::Jcc { cc: 7, rel: r2 },
            x64::Instr::MovImm32 { dst: 0, imm_u32: 0 },
            x64::Instr::AluRM {
                alu: x64::AluOp::Cmp,
                sz: x64::Size::W64,
                dst: 1,
                mem: x64::Mem { base: 15, index: None, disp: bd },
            },
            x64::Instr::Cmovcc { cc: 3, sz: x64::Size::W64, dst: 1, src: 0 },
        ]);
        assert(out@ =~= old_out + mem_code(*m, nl as nat, h as nat));
    }
}

/// Spec of the chain's entries `0..i`.
pub open spec fn brt_upto(ls: Seq<usize>, offs: Seq<int>, i: nat) -> Seq<x64::Instr>
    decreases i,
{
    if i == 0 {
        seq![]
    } else {
        brt_upto(ls, offs, (i - 1) as nat) + brt_entry(
            (i - 1) as nat,
            brt_rel(offs, ls[i - 1], (8 + i * 13) as int),
        )
    }
}

/// The entries `0..i` then the entries from `i` are all of them.
proof fn lemma_brt_upto(ls: Seq<usize>, offs: Seq<int>, i: nat)
    requires
        i <= ls.len(),
    ensures
        brt_upto(ls, offs, i) + brt_entries(ls, offs, 8, i) =~= brt_entries(ls, offs, 8, 0),
    decreases i,
{
    crate::cfmemlens::lemma_brt_entry_len(0, 0);
    if i > 0 {
        lemma_brt_upto(ls, offs, (i - 1) as nat);
        let k = (i - 1) as nat;
        assert(brt_entries(ls, offs, 8, k) == brt_entry(
            k,
            brt_rel(offs, ls[k as int], 8 + (k + 1) * brt_e()),
        ) + brt_entries(ls, offs, 8, i));
        assert((brt_upto(ls, offs, k) + brt_entry(k, brt_rel(offs, ls[k as int], (8 + i * 13) as int)))
            + brt_entries(ls, offs, 8, i) =~= brt_upto(ls, offs, k) + brt_entries(
            ls,
            offs,
            8,
            k,
        ));
    }
}

/// Append the code of `br_table ls d` at the absolute position `start`.
fn brt_exec(
    ls: &[usize],
    d: usize,
    nl: usize,
    h: usize,
    start: usize,
    labs: &[usize],
    out: &mut Vec<x64::Instr>,
)
    requires
        1 <= h,
        nl + h <= 31,
        ls@.len() <= 0x10000,
        d < labs@.len(),
        forall|i: int| 0 <= i < ls@.len() ==> #[trigger] ls@[i] < labs@.len(),
        forall|i: int| 0 <= i < labs@.len() ==> #[trigger] labs@[i] <= MAX_SIZE,
        start + 13 + 13 * ls@.len() <= MAX_SIZE,
    ensures
        final(out)@ == old(out)@ + brt_code(
            ls@,
            d,
            nl as nat,
            h as nat,
            offs_of(labs@, start as int),
        ),
{
    proof {
        crate::cfbrt::lemma_brt_p0(nl as nat, h as nat);
        crate::cfmemlens::lemma_brt_entry_len(0, 0);
    }
    let ghost old_out = out@;
    let ghost offs = offs_of(labs@, start as int);
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
            forall|j: int| 0 <= j < labs@.len() ==> #[trigger] labs@[j] <= MAX_SIZE,
            start + 13 + 13 * ls@.len() <= MAX_SIZE,
            offs == offs_of(labs@, start as int),
            out@ == old_out + seq![load_slot(rax(), (nl + h - 1) as nat)] + brt_upto(
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
                return;
            },
        };
        let tgt = match labs.get(l) {
            Some(t) => *t,
            None => {
                proof {
                    assert(false);
                }
                return;
            },
        };
        let end = add_u(add_u(start, 8), mul_u(13, add_u(i, 1)));
        let rel = rel32(tgt, end);
        out.push(x64::Instr::MovImm32 { dst: 2, imm_u32: i as u32 });
        out.push(x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: x64::Size::W32, dst: 0, src: 2 });
        out.push(x64::Instr::Jcc { cc: 4, rel });
        proof {
            let ii = (i + 1) as nat;
            assert(brt_rel(offs, ls@[i as int], (8 + ii * 13) as int) == tgt as int - end as int);
            assert(brt_upto(ls@, offs, ii) == brt_upto(ls@, offs, i as nat) + brt_entry(
                i as nat,
                brt_rel(offs, ls@[i as int], (8 + ii * 13) as int),
            ));
            assert(brt_entry(i as nat, tgt as int - end as int) =~= seq![
                x64::Instr::MovImm32 { dst: 2, imm_u32: i as u32 },
                x64::Instr::AluRR {
                    alu: x64::AluOp::Cmp,
                    sz: x64::Size::W32,
                    dst: 0,
                    src: 2,
                },
                x64::Instr::Jcc { cc: 4, rel },
            ]);
            assert(out@ =~= old_out + seq![load_slot(rax(), (nl + h - 1) as nat)] + brt_upto(
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
            return;
        },
    };
    let end = add_u(add_u(start, add_u(8, mul_u(13, ls.len()))), 5);
    out.push(x64::Instr::Jmp { rel: rel32(tgt, end) });
    proof {
        lemma_brt_upto(ls@, offs, ls@.len());
        assert(brt_entries(ls@, offs, 8, ls@.len() as nat) =~= Seq::<x64::Instr>::empty());
        assert(brt_p0(nl as nat, h as nat) == 8);
        assert(brt_e() == 13);
        assert(brt_upto(ls@, offs, ls@.len()) =~= brt_entries(ls@, offs, 8, 0));
        assert(out@ =~= old_out + brt_code(ls@, d, nl as nat, h as nat, offs));
    }
}

// ----------------------------------------------------------------------------
// The analysis
// ----------------------------------------------------------------------------

/// The code of a node is valid instructions (the analysis encodes it to
/// measure it).
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

/// The analysis of `n` (the spec's `cf_flow`), entered at height `h` with
/// `nl` locals and `labs.len()` labels in scope, and the size of its code in
/// bytes (the spec's `csize`). `None` only if it has no translation, or its
/// code is larger than `max_size`.
#[verifier::spinoff_prover]
#[verifier::rlimit(1500)]
fn analyze(n: &Node, nl: usize, h: usize, labs: &[usize]) -> (r: Option<(Option<usize>, usize)>)
    requires
        nl <= 31,
        h <= 31,
    ensures
        match r {
            Some((f, s)) => {
                &&& cf_flow(*n, nl as nat, h as nat, labs@.len()) == Some(fl_spec(f))
                &&& s == csize(*n, nl as nat, h as nat, labs@.len())
                &&& s <= MAX_SIZE
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
        crate::tlemmas::lemma_abi_consts_t();
    }
    let depth = labs.len();
    let room = add_u(nl, h) <= 31;
    match n {
        Node::Op(o) => {
            let ok = op_ok_exec(o, nl, h);
            if !ok {
                return None;
            }
            let mut v: Vec<x64::Instr> = Vec::new();
            emit_op(o, nl, h, &mut v);
            proof {
                crate::tlemmas::lemma_tmpl_valid(*o, nl as nat, h as nat);
                assert(v@ =~= tmpl(*o, nl as nat, h as nat));
                assert(all_valid_instrs(v@));
                assert(csize(*n, nl as nat, h as nat, depth as nat) == code_len(v@));
            }
            let sz = match code_bytes(v.as_slice()) {
                Some(s) => s,
                None => {
                    return None;
                },
            };
            if sz > MAX_SIZE {
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
            let mut v: Vec<x64::Instr> = Vec::new();
            mem_code_exec(m, nl, h, &mut v);
            proof {
                lemma_mem_valid(*m, nl as nat, h as nat);
                assert(v@ =~= mem_code(*m, nl as nat, h as nat));
                assert(csize(*n, nl as nat, h as nat, depth as nat) == code_len(v@));
            }
            let sz = match code_bytes(v.as_slice()) {
                Some(s) => s,
                None => {
                    return None;
                },
            };
            if sz > MAX_SIZE {
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
                    if s > MAX_SIZE {
                        return None;
                    }
                    Some((fb, s))
                },
                None => {
                    if matches!(&**b, Node::Op(crate::spec::Op::Nop)) {
                        proof {
                            assert(csize(**b, nl as nat, h as nat, depth as nat) == 0) by {
                                assert(ctmpl(**b, nl as nat, h as nat, zeros(depth as nat))
                                    =~= Seq::<x64::Instr>::empty());
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
                lemma_cond_len_16(nl as nat, h as nat);
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
            let s = add_u(add_u(add_u(16, st), 5), se);
            if s > MAX_SIZE {
                return None;
            }
            Some((Some(h1), s))
        },
        Node::Br(l) => {
            proof {
                lemma_csize_br(*l, nl as nat, h as nat, depth as nat);
            }
            if *l < depth {
                Some((None, 5))
            } else {
                None
            }
        },
        Node::BrIf(l) => {
            proof {
                lemma_csize_brif(*l, nl as nat, h as nat, depth as nat);
                lemma_cond_len_16(nl as nat, h as nat);
            }
            if *l < depth && h >= 1 && room {
                Some((Some(sub_u(h, 1)), 16))
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
                crate::cfbrt::lemma_brt_fetch_jmp(
                    ls@,
                    *d,
                    nl as nat,
                    h as nat,
                    zeros(depth as nat),
                );
                assert(csize(*n, nl as nat, h as nat, depth as nat) == 13 + 13 * ls@.len());
            }
            Some((None, add_u(13, mul_u(13, ls.len()))))
        },
        Node::Exit(c, k) => {
            let _ = c;
            proof {
                crate::cfmemlens::lemma_exit_seq_len(*c);
                assert(csize(*n, nl as nat, h as nat, depth as nat) == 14);
            }
            if *k <= h && room {
                Some((None, 14))
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
    nl <= 31 && h <= 31 && cf_flow(n, nl as nat, h as nat, labs.len()) is Some && start + csize(
        n,
        nl as nat,
        h as nat,
        labs.len(),
    ) <= MAX_SIZE && forall|i: int| 0 <= i < labs.len() ==> #[trigger] labs[i] <= MAX_SIZE
}

/// `then a b`.
fn emit_then(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<x64::Instr>)
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
                crate::tlemmas::lemma_abi_consts_t();
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
                    assert(ctmpl(**b, nl as nat, h as nat, shift(offs, sa as int))
                        =~= Seq::<x64::Instr>::empty());
                    assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
                }
            }
        }
    }
}

/// `block b`.
fn emit_block(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<x64::Instr>)
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
                crate::tlemmas::lemma_abi_consts_t();
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
                assert(offs_of(l@, start as int) =~= seq![sb as int] + offs);
            }
            emit_node(b, nl, h, start, l.as_slice(), out);
        }
    }
}

/// `loop b`.
fn emit_loop(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<x64::Instr>)
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
                crate::tlemmas::lemma_abi_consts_t();
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
fn emit_if(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<x64::Instr>)
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
                crate::tlemmas::lemma_abi_consts_t();
            }
            let h1 = sub_u(h, 1);
            proof {
                lemma_csize_if(**t, **e, nl as nat, h as nat, labs@.len());
                lemma_cond_len_16(nl as nat, h as nat);
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
            let end = add_u(add_u(add_u(add_u(start, 16), st), 5), se);
            let l = push_label(end, labs);
            let skip = add_u(st, 5) as i32;
            cond_pre_exec(nl, h, 4, skip, out);
            let tstart = add_u(start, 16);
            proof {
                lemma_offs_push(labs@, end, tstart as int);
                lemma_offs_shift(labs@, start as int, 16);
                assert(offs_of(l@, tstart as int) =~= seq![st as int + 5 + se as int] + shift(
                    offs,
                    16,
                ));
            }
            emit_node(t, nl, h1, tstart, l.as_slice(), out);
            out.push(x64::Instr::Jmp { rel: se as i32 });
            let estart = add_u(tstart, add_u(st, 5));
            proof {
                lemma_offs_push(labs@, end, estart as int);
                lemma_offs_shift(labs@, start as int, 16 + st as int + 5);
                assert(offs_of(l@, estart as int) =~= seq![se as int] + shift(
                    offs,
                    16 + st as int + 5,
                ));
            }
            emit_node(e, nl, h1, estart, l.as_slice(), out);
            proof {
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
            }
        }
    }
}

/// `br l` and `br_if l`.
fn emit_br(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<x64::Instr>)
    requires
        n is Br || n is BrIf,
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, offs_of(labs@, start as int)),
{
    let ghost old_out = out@;
    let ghost offs = offs_of(labs@, start as int);
    proof {
        crate::tlemmas::lemma_abi_consts_t();
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
            out.push(x64::Instr::Jmp { rel: rel32(tgt, add_u(start, 5)) });
            proof {
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
            }
        },
        Node::BrIf(l) => {
            proof {
                lemma_csize_brif(*l, nl as nat, h as nat, labs@.len());
                lemma_cond_len_16(nl as nat, h as nat);
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
            let rel = rel32(tgt, add_u(start, 16));
            cond_pre_exec(nl, h, 5, rel, out);
            proof {
                assert(out@ =~= old_out + ctmpl(*n, nl as nat, h as nat, offs));
            }
        },
        _ => {},
    }
}

/// `br_table`, `exit`, memory and straight-line instructions.
fn emit_leaf(n: &Node, nl: usize, h: usize, start: usize, labs: &[usize], out: &mut Vec<x64::Instr>)
    requires
        n is BrTable || n is Exit || n is Mem || n is Op,
        emit_pre(*n, nl, h, start, labs@),
    ensures
        final(out)@ == old(out)@ + ctmpl(*n, nl as nat, h as nat, offs_of(labs@, start as int)),
{
    let ghost old_out = out@;
    let ghost offs = offs_of(labs@, start as int);
    proof {
        crate::tlemmas::lemma_abi_consts_t();
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
                crate::cfbrt::lemma_brt_fetch_jmp(
                    ls@,
                    *d,
                    nl as nat,
                    h as nat,
                    zeros(labs@.len()),
                );
            }
            brt_exec(ls.as_slice(), *d, nl, h, start, labs, out);
        },
        Node::Exit(c, _) => {
            emit_exit(out, *c);
        },
        _ => {},
    }
}

/// Append the code of `n` at the absolute position `start`, with the labels in
/// scope at the absolute positions `labs`: exactly [`ctmpl`]. Returns the
/// flow and the size, as [`analyze`] does.
fn emit_node(
    n: &Node,
    nl: usize,
    h: usize,
    start: usize,
    labs: &[usize],
    out: &mut Vec<x64::Instr>,
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
        r.1 == csize(*n, nl as nat, h as nat, labs@.len()),
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

/// Encode `code` to bytes.
fn encode_code(code: &[x64::Instr]) -> (bytes: Vec<u8>)
    requires
        all_valid_instrs(code@),
    ensures
        bytes@ == clazel_codecheck::spec::enc_all(code@),
{
    let mut bytes: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    proof {
        assert(code@.take(0) =~= Seq::<x64::Instr>::empty());
    }
    while k < code.len()
        invariant
            k <= code.len(),
            bytes@ == clazel_codecheck::spec::enc_all(code@.take(k as int)),
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
        let e = encode_exec(ins);
        bytes.extend_from_slice(e.as_slice());
        proof {
            let t = code@.take(k as int + 1);
            assert(t.drop_last() =~= code@.take(k as int));
            assert(t.last() == code@[k as int]);
            assert(e@ =~= x64::encode(code@[k as int]));
        }
        k = add_u(k, 1);
    }
    proof {
        assert(code@.take(code@.len() as int) =~= code@);
    }
    bytes
}

/// **Every emitted blob refines its program.** If the emitter answers with
/// `bytes`, the encoded body is [`ctmpl`] of the program with the return
/// label at its end, which refines it.
pub proof fn lemma_emitted_refines(n: Node, nl: usize, exit_code: u32, bytes: Seq<u8>)
    requires
        emit_cf_blob_ensures(n, nl, exit_code, Some(bytes)),
    ensures
        cf_prog_ok(n, nl as nat),
        exists|body: Seq<x64::Instr>|
            #![trigger all_valid_instrs(body)]
            all_valid_instrs(body) && cf_refines(
                n@,
                nl as nat,
                0,
                seq![code_len(body) as int],
                body,
            ) && bytes == clazel_codecheck::spec::enc_all(body + exit_seq(exit_code)),
{
}

/// Emit the body of the function `n` with `nl` locals as encoded bytes,
/// followed by the exit sequence for `exit_code`. The function's return label
/// (a `br` to it, and falling off the end) is the exit sequence. `None` if the
/// program has no translation.
///
/// **Proven**: [`crate::cfcontract::emit_cf_blob_ensures`].
#[verifier::rlimit(500)]
pub fn emit_cf_blob(n: &Node, nl: usize, exit_code: u32) -> (r: Option<Vec<u8>>)
    ensures
        emit_cf_blob_ensures(*n, nl, exit_code, match r {
            Some(v) => Some(v@),
            None => None,
        }),
        // **Exactly** the template bytes: `crate::cfblobacc::emitted_bytes`
        // (an addition to the contract, which says only that some body
        // refines; the validator-acceptance theorem is about these bytes).
        match r {
            Some(v) => v@ == emitted_bytes(*n, nl as nat, exit_code),
            None => true,
        },
        // **The validator accepts it** (J.9): `crate::cfblobacc::theorem_blob_accepted`.
        emit_cf_blob_accepted_ensures(*n, nl, exit_code, match r {
            Some(v) => Some(v@),
            None => None,
        }),
{
    proof {
        crate::tlemmas::lemma_abi_consts_t();
        lemma_templated_all(*n);
    }
    if nl > 31 {
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
    let mut body: Vec<x64::Instr> = Vec::new();
    proof {
        assert(csize(*n, nl as nat, 0, 1) == size);
    }
    emit_node(n, nl, 0, 0, labs.as_slice(), &mut body);
    let ghost body_seq = body@;
    emit_exit(&mut body, exit_code);
    proof {
        let offs = offs_of(labs@, 0);
        assert(offs =~= seq![size as int]);
        lemma_ctmpl_valid(*n, nl as nat, 0, offs);
        lemma_ctmpl_len(*n, nl as nat, 0, offs);
        assert(labels_fit(offs, size as nat));
        lemma_ctmpl_refines(*n, nl as nat, 0, offs);
        crate::tlemmas::lemma_exit_valid(exit_code);
        assert(Seq::<x64::Instr>::empty() + body_seq =~= body_seq);
        assert(all_valid_instrs(body@)) by {
            assert forall|k: int| 0 <= k < body@.len() implies x64::valid_instr(
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
    proof {
        let offs = offs_of(labs@, 0);
        assert(offs =~= seq![size as int]);
        assert(csize(*n, nl as nat, 0, 1) == size);
        assert(body_seq =~= ctmpl(*n, nl as nat, 0, offs)) by {
            assert(Seq::<x64::Instr>::empty() + ctmpl(*n, nl as nat, 0, offs) =~= ctmpl(
                *n,
                nl as nat,
                0,
                offs,
            ));
        }
        assert(body@ =~= body_seq + exit_seq(exit_code));
        assert(bytes@ == emitted_bytes(*n, nl as nat, exit_code));
        assert(emit_cf_blob_ensures(*n, nl, exit_code, Some(bytes@)));
        lemma_emitter_accepted(*n, nl, exit_code, bytes@);
    }
    Some(bytes)
}

} // verus!

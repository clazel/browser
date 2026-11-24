//! One `x64::step` of each instruction form the memory templates and the
//! `br_table` chain add to the first slice's: a register move, `add` with an
//! immediate (its carry), `cmp` with a memory operand, and a load or store
//! through any memory operand.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `mov dst, src` (64-bit).
pub proof fn lemma_step_mov_rr64(cu: spec_fn(nat) -> nat, m: x64::State, dst: u8, src: u8)
    requires
        x64::wf(m),
        dst < 16,
        src < 16,
        x64::canonical(
            m.rip + x64::instr_len(x64::Instr::MovRR { sz: x64::Size::W64, dst: dst, src: src }),
        ),
    ensures
        x64::step(cu, m, x64::Instr::MovRR { sz: x64::Size::W64, dst: dst, src: src }) == Some(
            x64::State {
                rgf: m.rgf.update(dst as int, m.rgf[src as int]),
                rip: m.rip + x64::instr_len(
                    x64::Instr::MovRR { sz: x64::Size::W64, dst: dst, src: src },
                ),
                ..m
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    let v = m.rgf[src as int] as int;
    assert(x64::loghead(64, v) == v);
}

/// `add dst, imm` (64-bit, `imm >= 0`): the sum modulo `2^64`, and the carry
/// flag says the sum did not fit.
pub proof fn lemma_step_add_ri64(cu: spec_fn(nat) -> nat, m: x64::State, dst: u8, imm: i32)
    requires
        x64::wf(m),
        dst < 16,
        0 <= imm,
        x64::canonical(
            m.rip + x64::instr_len(
                x64::Instr::AluRI { alu: x64::AluOp::Add, sz: x64::Size::W64, dst: dst, imm: imm },
            ),
        ),
    ensures
        x64::step(
            cu,
            m,
            x64::Instr::AluRI { alu: x64::AluOp::Add, sz: x64::Size::W64, dst: dst, imm: imm },
        ) is Some,
        ({
            let m1 = x64::step(
                cu,
                m,
                x64::Instr::AluRI { alu: x64::AluOp::Add, sz: x64::Size::W64, dst: dst, imm: imm },
            ).unwrap();
            let sum = m.rgf[dst as int] as int + imm as int;
            &&& m1.rgf == m.rgf.update(dst as int, (sum % 0x1_0000_0000_0000_0000) as u64)
            &&& m1.mem == m.mem && m1.xmm == m.xmm
            &&& m1.rip == m.rip + x64::instr_len(
                x64::Instr::AluRI { alu: x64::AluOp::Add, sz: x64::Size::W64, dst: dst, imm: imm },
            )
            &&& x64::flgi(m1, x64::cf_bit()) == x64::bool_to_bit(sum >= 0x1_0000_0000_0000_0000)
        }),
{
    super::memlemmas::lemma_p2_consts();
    let x = m.rgf[dst as int] as int;
    let y = imm as int;
    assert(0 <= x && x < 0x1_0000_0000_0000_0000);
    assert(x64::loghead(64, y) == y);
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, 0x1_0000_0000_0000_0000nat);
    assert(x64::loghead(64, x) == x);
    let r = x64::gpr_add_spec(64, x, y, m.rflags);
    let s1 = x64::wr64(m, dst, r.result);
    super::alu::lemma_wur_frame(cu, s1, r.rflags, r.undef);
    assert(r.undef == 0);
    assert(x64::bit(0, 0) == 0) by {
        vstd::arithmetic::power2::lemma2_to64();
        assert(x64::p2(0) == 1);
    }
    super::flags::lemma_wur_flag(cu, s1, r.rflags, r.undef, 0);
    let sum = x + y;
    let f = x64::FlagUpd {
        cf: Some(x64::cf_spec(64, sum)),
        pf: Some(x64::pf_spec(x64::loghead(64, sum))),
        af: Some(x64::add_af_spec(x, y)),
        zf: Some(x64::zf_spec(x64::loghead(64, sum))),
        sf: Some(x64::sf_spec(64, x64::loghead(64, sum))),
        of: Some(x64::of_spec(64, x64::logext(64, x) + x64::logext(64, y))),
    };
    assert(r.rflags == x64::change_rflags(m.rflags, f));
    super::flags::lemma_change_rflags_bit(m.rflags, f, 0);
    assert(x64::loghead(64, sum) == sum % 0x1_0000_0000_0000_0000);
    assert(x64::cf_spec(64, sum) == x64::bool_to_bit(sum >= 0x1_0000_0000_0000_0000));
    assert(x64::cf_spec(64, sum) % 2 == x64::cf_spec(64, sum));
}

/// `cmp dst, [mem]` (64-bit) with the memory operand reading the word `e`:
/// the registers and memory are unchanged, and the flags are those of
/// `dst - e`.
pub proof fn lemma_step_cmp_rm64_flags(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    a: u8,
    mem: x64::Mem,
    e: int,
)
    requires
        x64::wf(m),
        a < 16,
        x64::read_mem(m.mem, x64::eff_addr(m, mem), 8) == Some(e),
        0 <= e < 0x1_0000_0000_0000_0000,
        x64::canonical(
            m.rip + x64::instr_len(
                x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem },
            ),
        ),
    ensures
        x64::step(
            cu,
            m,
            x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem },
        ) is Some,
        ({
            let m1 = x64::step(
                cu,
                m,
                x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem },
            ).unwrap();
            let lx = m.rgf[a as int] as int;
            let sraw = x64::logext(64, lx) - x64::logext(64, e);
            let res = x64::loghead(64, sraw);
            &&& m1.rgf == m.rgf && m1.mem == m.mem && m1.xmm == m.xmm
            &&& m1.rip == m.rip + x64::instr_len(
                x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem },
            )
            &&& x64::flgi(m1, x64::cf_bit()) == x64::bool_to_bit(lx < e)
            &&& x64::flgi(m1, x64::zf_bit()) == x64::zf_spec(res)
            &&& x64::flgi(m1, x64::sf_bit()) == x64::sf_spec(64, res) % 2
            &&& x64::flgi(m1, x64::of_bit()) == x64::of_spec(64, sraw)
        }),
{
    super::memlemmas::lemma_p2_consts();
    let n: nat = 64;
    let x = x64::rgfi_size(m, x64::Size::W64, a);
    assert(x == m.rgf[a as int] as int);
    assert(0 <= x < 0x1_0000_0000_0000_0000);
    let r = x64::gpr_sub_spec(n, x, e, m.rflags);
    assert(x64::gpr_arith_logic_spec(n, x64::AluOp::Cmp, x, e, m.rflags) == r);
    super::alu::lemma_wur_frame(cu, m, r.rflags, r.undef);
    assert(r.undef == 0);
    assert(x64::bit(0, 0) == 0 && x64::bit(0, 6) == 0 && x64::bit(0, 7) == 0 && x64::bit(0, 11)
        == 0) by {
        vstd::arithmetic::power2::lemma2_to64();
        assert(x64::p2(0) == 1 && x64::p2(6) == 64 && x64::p2(7) == 128 && x64::p2(11) == 2048);
    }
    super::flags::lemma_wur_flag(cu, m, r.rflags, r.undef, 0);
    super::flags::lemma_wur_flag(cu, m, r.rflags, r.undef, 6);
    super::flags::lemma_wur_flag(cu, m, r.rflags, r.undef, 7);
    super::flags::lemma_wur_flag(cu, m, r.rflags, r.undef, 11);
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, 0x1_0000_0000_0000_0000nat);
    vstd::arithmetic::div_mod::lemma_small_mod(e as nat, 0x1_0000_0000_0000_0000nat);
    let lx = x64::loghead(n, x);
    let ly = x64::loghead(n, e);
    assert(lx == x && ly == e);
    let sraw = x64::logext(n, lx) - x64::logext(n, ly);
    let res = x64::loghead(n, sraw);
    let f = x64::FlagUpd {
        cf: Some(x64::bool_to_bit(lx < ly)),
        pf: Some(x64::pf_spec(res)),
        af: Some(x64::sub_af_spec(lx, ly)),
        zf: Some(x64::zf_spec(res)),
        sf: Some(x64::sf_spec(n, res)),
        of: Some(x64::of_spec(n, sraw)),
    };
    assert(r.rflags == x64::change_rflags(m.rflags, f));
    super::flags::lemma_change_rflags_bit(m.rflags, f, 0);
    super::flags::lemma_change_rflags_bit(m.rflags, f, 6);
    super::flags::lemma_change_rflags_bit(m.rflags, f, 7);
    super::flags::lemma_change_rflags_bit(m.rflags, f, 11);
}

/// [`lemma_step_cmp_rm64_flags`], and what the three condition codes of the
/// bounds check read from those flags (`b`, `ae`, `a`).
pub proof fn lemma_step_cmp_rm64(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    a: u8,
    mem: x64::Mem,
    e: int,
)
    requires
        x64::wf(m),
        a < 16,
        x64::read_mem(m.mem, x64::eff_addr(m, mem), 8) == Some(e),
        0 <= e < 0x1_0000_0000_0000_0000,
        x64::canonical(
            m.rip + x64::instr_len(
                x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem },
            ),
        ),
    ensures
        x64::step(
            cu,
            m,
            x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem },
        ) is Some,
        ({
            let m1 = x64::step(
                cu,
                m,
                x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem },
            ).unwrap();
            let lx = m.rgf[a as int] as int;
            &&& m1.rgf == m.rgf && m1.mem == m.mem && m1.xmm == m.xmm
            &&& m1.rip == m.rip + x64::instr_len(
                x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem },
            )
            &&& x64::jcc_cmovcc_setcc_spec(m1, 2) == (lx < e)
            &&& x64::jcc_cmovcc_setcc_spec(m1, 3) == (lx >= e)
            &&& x64::jcc_cmovcc_setcc_spec(m1, 7) == (lx > e)
        }),
{
    lemma_step_cmp_rm64_flags(cu, m, a, mem, e);
    let i = x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: a, mem: mem };
    let m1 = x64::step(cu, m, i).unwrap();
    let lx = m.rgf[a as int] as int;
    super::memlemmas::lemma_p2_consts();
    assert(0 <= lx < 0x1_0000_0000_0000_0000);
    assert(x64::p2(64) == 0x1_0000_0000_0000_0000);
    super::flags::lemma_cc_icmp(m1, lir::ICmp::LtU, 64, lx, e);
    super::flags::lemma_cc_icmp(m1, lir::ICmp::GeU, 64, lx, e);
    super::flags::lemma_cc_icmp(m1, lir::ICmp::GtU, 64, lx, e);
    assert(super::templates::cc_of(lir::ICmp::LtU) == 2 && super::templates::cc_of(lir::ICmp::GeU)
        == 3 && super::templates::cc_of(lir::ICmp::GtU) == 7);
}

/// `mov dst, [mem]` of either size, when the read gives `v`.
pub proof fn lemma_step_movload(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    sz: x64::Size,
    dst: u8,
    mem: x64::Mem,
    v: int,
)
    requires
        x64::wf(m),
        dst < 16,
        x64::read_mem(m.mem, x64::eff_addr(m, mem), x64::nbytes(sz)) == Some(v),
        x64::canonical(
            m.rip + x64::instr_len(x64::Instr::MovLoad { sz: sz, dst: dst, mem: mem }),
        ),
    ensures
        x64::step(cu, m, x64::Instr::MovLoad { sz: sz, dst: dst, mem: mem }) == Some(
            x64::State {
                rgf: x64::set_rgfi_size(m, sz, dst, v).rgf,
                rip: m.rip + x64::instr_len(x64::Instr::MovLoad { sz: sz, dst: dst, mem: mem }),
                ..m
            },
        ),
{
}

/// `mov [mem], src` of either size, when the write succeeds.
pub proof fn lemma_step_movstore(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    sz: x64::Size,
    mem: x64::Mem,
    src: u8,
    mem2: Map<int, u8>,
)
    requires
        x64::wf(m),
        src < 16,
        x64::write_mem(m.mem, x64::eff_addr(m, mem), x64::nbytes(sz), x64::rgfi_size(m, sz, src))
            == Some(mem2),
        x64::canonical(
            m.rip + x64::instr_len(x64::Instr::MovStore { sz: sz, mem: mem, src: src }),
        ),
    ensures
        x64::step(cu, m, x64::Instr::MovStore { sz: sz, mem: mem, src: src }) == Some(
            x64::State {
                mem: mem2,
                rip: m.rip + x64::instr_len(x64::Instr::MovStore { sz: sz, mem: mem, src: src }),
                ..m
            },
        ),
{
}

} // verus!

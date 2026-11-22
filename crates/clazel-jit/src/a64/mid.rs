//! The register-only middle of each template computes LIR's result: from a
//! state whose scratch registers hold the loaded operands, the middle does not
//! fault and leaves the result word in `x0`, changing only scratch registers,
//! the flags and `pc`. The A64 counterpart of [`crate::mid`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What every middle establishes: register `rd` holds `w`; the register file
/// has its 31 registers; the context register, the link register, `SP`, the
/// vector registers and memory are as they were; `pc` advanced by `len`.
pub open spec fn mid_post(m: isa::State, m1: isa::State, rd: u8, w: nat, len: nat) -> bool {
    m1.r.len() == 31 && m1.vreg == m.vreg && m1.r[rd as int] as nat == w && m1.r[abi::ctx_reg() as int]
        == m.r[abi::ctx_reg() as int] && m1.r[abi::link_reg() as int] == m.r[abi::link_reg() as int]
        && m1.sp == m.sp && m1.mem == m.mem && m1.pc as int == m.pc as int + len
}

/// A step that sets only the flags and `pc` keeps the state well formed, and
/// every register.
pub proof fn lemma_wf_flags(s: isa::State, s1: isa::State)
    requires
        isa::wf(s),
        s1.r == s.r,
        s1.vreg == s.vreg,
        s1.mem == s.mem,
        s1.sp == s.sp,
    ensures
        isa::wf(s1),
{
}

/// `wrote_x0` establishes [`mid_post`] for a value below `2^n`.
pub proof fn lemma_wrote_post(s: isa::State, v: int, n: nat)
    requires
        isa::wf(s),
        n == 32 || n == 64,
        0 <= v < isa::p2(n),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::wf(super::alu::wrote_x0(s, v, n)),
        mid_post(s, super::alu::wrote_x0(s, v, n), 0, v as nat, 4),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_trunc_small(n, v);
    super::alu::lemma_pc4(s.pc);
    assert(v < 0x1_0000_0000_0000_0000);
    let s1 = super::alu::wrote_x0(s, v, n);
    assert(s1.r[0] == v as u64);
}

/// **`op x0, x0, x1`** computes LIR's integer binary operator.
pub proof fn lemma_mid_int(s: isa::State, sf: isa::Width, o: lir::IBin, x: u64, y: u64)
    requires
        isa::wf(s),
        crate::spec::ibin_supported(o),
        s.r[0] == x,
        s.r[1] == y,
        x < isa::p2(super::alu::bits(sf)),
        y < isa::p2(super::alu::bits(sf)),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, seq![super::templates::int_op_instr(o, sf)]) is Some,
        mid_post(
            s,
            run_seq(s, seq![super::templates::int_op_instr(o, sf)]).unwrap(),
            0,
            super::intops::ibin_w(o, sf, x, y) as nat,
            4,
        ),
{
    super::alu::lemma_bits(sf);
    super::intops::lemma_step_int_op(s, sf, o, x, y);
    super::intops::lemma_ibin_w_bound(o, sf, x, y);
    super::runseq::lemma_run_seq_one(s, super::templates::int_op_instr(o, sf));
    lemma_wrote_post(s, super::intops::ibin_w(o, sf, x, y), super::alu::bits(sf));
}

/// **`cmp x0, x1; cset w0, cc`** computes LIR's integer comparison.
#[verifier::rlimit(300)]
pub proof fn lemma_mid_cmp(s: isa::State, c: lir::ICmp, sf: isa::Width, x: u64, y: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        s.r[1] == y,
        x < isa::p2(super::alu::bits(sf)),
        y < isa::p2(super::alu::bits(sf)),
        s.pc as int + 8 < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, super::templates::cmp_mid(c, sf)) is Some,
        mid_post(
            s,
            run_seq(s, super::templates::cmp_mid(c, sf)).unwrap(),
            0,
            lir::bool_i32(lir::icmp(c, super::alu::bits(sf), x as int, y as int)) as nat,
            8,
        ),
{
    let n = super::alu::bits(sf);
    super::alu::lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    let i1 = super::templates::cmp_rr(sf, 0, 1);
    let i2 = super::templates::cset0(super::templates::cset_cond(c));
    assert(super::templates::cmp_mid(c, sf) == seq![i1, i2]);
    super::flags::lemma_step_cmp(s, sf, x, y);
    let t = isa::set_nzcv(s, super::flags::cmp_nzcv(n, x as int, y as int));
    let s1 = isa::State { pc: (s.pc + 4) as u64, ..t };
    assert(isa::step(s, i1) == Some(s1));
    lemma_wf_flags(s, s1);
    assert(s1.r[0] == x && s1.r[1] == y);
    assert(super::templates::cset_cond(c) < 14);
    super::alu::lemma_pc4(s.pc);
    super::flags::lemma_step_cset(s1, super::templates::cset_cond(c));
    super::flags::lemma_cc_icmp(s, c, n, x as int, y as int);
    // the condition reads only the flags, which `t` and `s1` share
    assert(isa::condition_holds(s1, super::templates::cset_cond(c)) == isa::condition_holds(
        t,
        super::templates::cset_cond(c),
    ));
    let holds = isa::condition_holds(s1, super::templates::cset_cond(c));
    let s2 = super::alu::wrote_x0(s1, if holds {
        0int
    } else {
        1int
    }, 32);
    super::runseq::run2(s, i1, i2, s1, s2);
    lemma_wrote_post(s1, if holds {
        0int
    } else {
        1int
    }, 32);
    assert(s2.mem == s.mem && s2.sp == s.sp);
    assert(s2.vreg == s.vreg);
    assert(mid_post(s, s2, 0, lir::bool_i32(lir::icmp(c, n, x as int, y as int)) as nat, 8));
}

/// **`cmp x0, #0; cset w0, eq`** computes LIR's `eqz`.
#[verifier::rlimit(300)]
pub proof fn lemma_mid_eqz(s: isa::State, sf: isa::Width, x: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        x < isa::p2(super::alu::bits(sf)),
        s.pc as int + 8 < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, super::templates::eqz_mid(sf)) is Some,
        mid_post(
            s,
            run_seq(s, super::templates::eqz_mid(sf)).unwrap(),
            0,
            lir::bool_i32(x == 0) as nat,
            8,
        ),
{
    let n = super::alu::bits(sf);
    super::alu::lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    let i1 = super::templates::cmp_zero(sf, 0);
    let i2 = super::templates::cset0(1);
    assert(super::templates::eqz_mid(sf) == seq![i1, i2]);
    super::flags::lemma_step_cmp_zero(s, sf, 0, x);
    let t = isa::set_nzcv(s, super::flags::cmp_nzcv(n, x as int, 0));
    let s1 = isa::State { pc: (s.pc + 4) as u64, ..t };
    assert(isa::step(s, i1) == Some(s1));
    lemma_wf_flags(s, s1);
    super::alu::lemma_pc4(s.pc);
    super::flags::lemma_step_cset(s1, 1);
    // `eq` compare against zero: the condition `ne` (the csinc's) fails iff x == 0
    super::memlemmas::lemma_p2_consts();
    assert(0 < isa::p2(n));
    super::flags::lemma_cc_icmp(s, lir::ICmp::Eq, n, x as int, 0);
    assert(super::templates::cset_cond(lir::ICmp::Eq) == 1);
    assert(isa::condition_holds(s1, 1) == isa::condition_holds(t, 1));
    let holds = isa::condition_holds(s1, 1);
    let s2 = super::alu::wrote_x0(s1, if holds {
        0int
    } else {
        1int
    }, 32);
    super::runseq::run2(s, i1, i2, s1, s2);
    lemma_wrote_post(s1, if holds {
        0int
    } else {
        1int
    }, 32);
    assert(lir::icmp(lir::ICmp::Eq, n, x as int, 0) == (x == 0));
    assert(s2.mem == s.mem && s2.sp == s.sp);
    assert(s2.vreg == s.vreg);
}

/// **`cmp w2, #0; csel x0, x0, x1, ne`** computes LIR's `select`.
#[verifier::rlimit(300)]
pub proof fn lemma_mid_select(s: isa::State, v1: u64, v2: u64, c: u32)
    requires
        isa::wf(s),
        s.r[0] == v1,
        s.r[1] == v2,
        s.r[2] == c as u64,
        s.pc as int + 8 < 0x1_0000_0000_0000_0000,
    ensures
        run_seq(s, super::templates::select_mid()) is Some,
        mid_post(
            s,
            run_seq(s, super::templates::select_mid()).unwrap(),
            0,
            (if c != 0 {
                v1
            } else {
                v2
            }) as nat,
            8,
        ),
{
    super::memlemmas::lemma_p2_consts();
    let i1 = super::templates::cmp_zero(isa::Width::W32, 2);
    let i2 = super::templates::select_mid()[1];
    assert(super::templates::select_mid() == seq![i1, i2]);
    assert(super::alu::bits(isa::Width::W32) == 32);
    assert((c as u64) < isa::p2(32));
    super::flags::lemma_step_cmp_zero(s, isa::Width::W32, 2, c as u64);
    let t = isa::set_nzcv(s, super::flags::cmp_nzcv(32, c as int, 0));
    let s1 = isa::State { pc: (s.pc + 4) as u64, ..t };
    assert(isa::step(s, i1) == Some(s1));
    lemma_wf_flags(s, s1);
    super::alu::lemma_pc4(s.pc);
    // the Z flag is "c == 0"
    super::flags::lemma_cmp_arith(32, c as int, 0);
    assert(0 <= isa::bit(super::flags::cmp_nzcv(32, c as int, 0), 2)) by {
        vstd::arithmetic::power2::lemma2_to64();
    }
    assert(s1.flag_z == (c == 0));
    super::flags::lemma_step_csel_ne(s1, v1, v2);
    let s2 = super::alu::wrote_x0(s1, if !s1.flag_z {
        v1 as int
    } else {
        v2 as int
    }, 64);
    super::runseq::run2(s, i1, i2, s1, s2);
    assert(isa::step(s1, i2) == Some(s2));
    let w = if c != 0 {
        v1 as int
    } else {
        v2 as int
    };
    assert(0 <= w < isa::p2(64));
    lemma_wrote_post(s1, w, 64);
    assert(s2.mem == s.mem && s2.sp == s.sp);
    assert(s2.vreg == s.vreg);
}

} // verus!

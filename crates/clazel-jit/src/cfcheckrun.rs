//! [`lemma_check_run`]: the run of the bounds-check sequence, in three
//! pieces (steps 0 to 2, 3 and 4, 5 to 7).

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfcheck::*;
#[cfg(verus_only)]
use crate::cfleaf::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfmemsteps::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cfsteps::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The sequence's instructions are where the offsets say.
pub proof fn lemma_check_fetch(c: clazel_codecheck::spec::Chk)
    requires
        c.i == rcx() && c.t == rdx() && c.z == rax() && 0 <= c.k < 16,
    ensures
        ({
            let cs = clazel_codecheck::spec::check_seq(c);
            &&& fetch(cs, 0) == Some(clazel_codecheck::spec::check_instr(0, c))
            &&& fetch(cs, 3) == Some(clazel_codecheck::spec::check_instr(1, c))
            &&& fetch(cs, 10) == Some(clazel_codecheck::spec::check_instr(2, c))
            &&& fetch(cs, 16) == Some(clazel_codecheck::spec::check_instr(3, c))
            &&& fetch(cs, 24) == Some(clazel_codecheck::spec::check_instr(4, c))
            &&& fetch(cs, 30) == Some(clazel_codecheck::spec::check_instr(5, c))
            &&& fetch(cs, 35) == Some(clazel_codecheck::spec::check_instr(6, c))
            &&& fetch(cs, 43) == Some(clazel_codecheck::spec::check_instr(7, c))
        }),
{
    let cs = clazel_codecheck::spec::check_seq(c);
    lemma_check_offsets(c);
    assert(cs[0] == clazel_codecheck::spec::check_instr(0, c));
    assert(cs[1] == clazel_codecheck::spec::check_instr(1, c));
    assert(cs[2] == clazel_codecheck::spec::check_instr(2, c));
    assert(cs[3] == clazel_codecheck::spec::check_instr(3, c));
    assert(cs[4] == clazel_codecheck::spec::check_instr(4, c));
    assert(cs[5] == clazel_codecheck::spec::check_instr(5, c));
    assert(cs[6] == clazel_codecheck::spec::check_instr(6, c));
    assert(cs[7] == clazel_codecheck::spec::check_instr(7, c));
    lemma_fetch_idx(cs, 0);
    lemma_fetch_idx(cs, 1);
    lemma_fetch_idx(cs, 2);
    lemma_fetch_idx(cs, 3);
    lemma_fetch_idx(cs, 4);
    lemma_fetch_idx(cs, 5);
    lemma_fetch_idx(cs, 6);
    lemma_fetch_idx(cs, 7);
}

/// Steps 0 to 2: `mov rdx, rcx; add rdx, n; jb`. The run reaches `s3`, with
/// `rdx` the sum, and `rip` at the first exit on a carry, else after the `jb`.
#[verifier::rlimit(400)]
pub proof fn lemma_chk_head(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    c: clazel_codecheck::spec::Chk,
)
    requires
        x64::wf(m),
        c.i == rcx() && c.t == rdx() && c.z == rax() && 0 <= c.k < 16,
        1 <= c.n <= 8,
        -0x8000_0000 <= c.r1 < 0x8000_0000,
        x64::canonical(m.rip + 47),
        x64::canonical(m.rip + 16 + c.r1),
    ensures
        ({
            let cs = clazel_codecheck::spec::check_seq(c);
            let sum = m.rgf[1] as int + c.n;
            exists|s3: x64::State|
                #![trigger reaches(cu, cs, m.rip, m, s3)]
                reaches(cu, cs, m.rip, m, s3) && x64::wf(s3) && s3.mem == m.mem && s3.xmm
                    == m.xmm && s3.rgf == m.rgf.update(
                    2,
                    (sum % 0x1_0000_0000_0000_0000) as u64,
                ) && s3.rip == (if sum >= 0x1_0000_0000_0000_0000 {
                    m.rip + 16 + c.r1
                } else {
                    m.rip + 16
                })
        }),
{
    super::memlemmas::lemma_p2_consts();
    let cs = clazel_codecheck::spec::check_seq(c);
    lemma_check_fetch(c);
    lemma_check_instr_lens(c);
    let ix = m.rgf[1] as int;
    assert(0 <= ix < 0x1_0000_0000_0000_0000);
    let rip0 = m.rip;
    super::runseq::lemma_canonical_between(rip0, rip0 + 3, rip0 + 47);
    super::runseq::lemma_canonical_between(rip0, rip0 + 10, rip0 + 47);
    super::runseq::lemma_canonical_between(rip0, rip0 + 16, rip0 + 47);
    let i0 = clazel_codecheck::spec::check_instr(0, c);
    let i1 = clazel_codecheck::spec::check_instr(1, c);
    let i2 = clazel_codecheck::spec::check_instr(2, c);
    assert(i0 == x64::Instr::MovRR { sz: x64::Size::W64, dst: 2, src: 1 });
    lemma_step_mov_rr64(cu, m, 2, 1);
    let s1 = x64::step(cu, m, i0).unwrap();
    lemma_wf_like(m, s1);
    assert(reaches(cu, cs, rip0, m, m)) by {
        assert(steps(cu, cs, rip0, m, 0) == Some(m));
    }
    lemma_reach_step(cu, cs, rip0, m, m, i0, s1);
    assert(i1 == x64::Instr::AluRI {
        alu: x64::AluOp::Add,
        sz: x64::Size::W64,
        dst: 2,
        imm: c.n as i32,
    });
    lemma_step_add_ri64(cu, s1, 2, c.n as i32);
    let s2 = x64::step(cu, s1, i1).unwrap();
    assert(s1.rgf[2] as int == ix);
    let sum = ix + c.n;
    lemma_wf_like(m, s2);
    lemma_reach_step(cu, cs, rip0, m, s1, i1, s2);
    assert(i2 == jcc_i(2, c.r1 as int));
    lemma_step_jcc(cu, s2, 2, c.r1 as int);
    let s3 = x64::step(cu, s2, i2).unwrap();
    assert(x64::cf_bit() == 0);
    assert((c.r1 as i32) as int == c.r1);
    assert(x64::jcc_cmovcc_setcc_spec(s2, 2) == (sum >= 0x1_0000_0000_0000_0000));
    lemma_wf_like(m, s3);
    lemma_reach_step(cu, cs, rip0, m, s2, i2, s3);
}

/// Steps 3 and 4: `cmp rdx, [bound]; ja`, from after the `jb` with no carry.
/// The run reaches `s5`, at the second exit exactly when `sum > bound`, else
/// after the `ja`, registers as they were.
#[verifier::rlimit(400)]
pub proof fn lemma_chk_mid(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    m: x64::State,
    s3: x64::State,
    c: clazel_codecheck::spec::Chk,
)
    requires
        x64::wf(m),
        ctx_ok(m),
        table_ok(lay, m),
        c.i == rcx() && c.t == rdx() && c.z == rax() && 0 <= c.k < 16,
        c.k < lay.len(),
        1 <= c.n <= 8,
        -0x8000_0000 <= c.r2 < 0x8000_0000,
        x64::canonical(m.rip + 47),
        x64::canonical(m.rip + 30 + c.r2),
        x64::wf(s3),
        s3.mem == m.mem,
        s3.xmm == m.xmm,
        s3.rgf.len() == 16,
        s3.rgf[15] == m.rgf[15],
        s3.rgf[2] as int == m.rgf[1] as int + c.n,
        s3.rip == m.rip + 16,
        reaches(cu, clazel_codecheck::spec::check_seq(c), m.rip, m, s3),
    ensures
        ({
            let cs = clazel_codecheck::spec::check_seq(c);
            let sum = m.rgf[1] as int + c.n;
            let bound = lay[c.k].bound as int;
            exists|s5: x64::State|
                #![trigger reaches(cu, cs, m.rip, m, s5)]
                reaches(cu, cs, m.rip, m, s5) && x64::wf(s5) && s5.mem == m.mem && s5.xmm
                    == m.xmm && s5.rgf == s3.rgf && s5.rip == (if sum > bound {
                    m.rip + 30 + c.r2
                } else {
                    m.rip + 30
                })
        }),
{
    super::memlemmas::lemma_p2_consts();
    let cs = clazel_codecheck::spec::check_seq(c);
    lemma_check_fetch(c);
    lemma_check_instr_lens(c);
    lemma_table_words(lay, m, c.k as nat);
    let rip0 = m.rip;
    let ix = m.rgf[1] as int;
    let sum = ix + c.n;
    let bound = lay[c.k].bound as int;
    super::runseq::lemma_canonical_between(rip0, rip0 + 24, rip0 + 47);
    super::runseq::lemma_canonical_between(rip0, rip0 + 30, rip0 + 47);
    let bm = clazel_codecheck::spec::bound_mem(c.k);
    let i3 = clazel_codecheck::spec::check_instr(3, c);
    let i4 = clazel_codecheck::spec::check_instr(4, c);
    assert(i3 == x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: 2, mem: bm });
    assert(x64::eff_addr(s3, bm) == x64::eff_addr(m, bm));
    assert(sum < 0x1_0000_0000_0000_0000);
    lemma_step_cmp_rm64(cu, s3, 2, bm, bound);
    let s4 = x64::step(cu, s3, i3).unwrap();
    lemma_wf_like(m, s4);
    lemma_reach_step(cu, cs, rip0, m, s3, i3, s4);
    assert(i4 == jcc_i(7, c.r2 as int));
    assert(x64::jcc_cmovcc_setcc_spec(s4, 7) == (sum > bound));
    lemma_step_jcc(cu, s4, 7, c.r2 as int);
    let s5 = x64::step(cu, s4, i4).unwrap();
    assert((c.r2 as i32) as int == c.r2);
    lemma_wf_like(m, s5);
    lemma_reach_step(cu, cs, rip0, m, s4, i4, s5);
}

/// Steps 5 to 7: `mov eax, 0; cmp rcx, [bound]; cmovae rcx, rax`, from after
/// the `ja` with `ix < bound`: nothing but `rax` and the flags change.
#[verifier::rlimit(400)]
pub proof fn lemma_chk_tail(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    m: x64::State,
    s5: x64::State,
    c: clazel_codecheck::spec::Chk,
)
    requires
        x64::wf(m),
        ctx_ok(m),
        table_ok(lay, m),
        c.i == rcx() && c.t == rdx() && c.z == rax() && 0 <= c.k < 16,
        c.k < lay.len(),
        1 <= c.n <= 8,
        m.rgf[1] as int + c.n <= lay[c.k].bound as int,
        x64::canonical(m.rip + 47),
        x64::wf(s5),
        s5.mem == m.mem,
        s5.xmm == m.xmm,
        s5.rgf.len() == 16,
        s5.rgf[15] == m.rgf[15],
        s5.rgf[1] == m.rgf[1],
        s5.rip == m.rip + 30,
        reaches(cu, clazel_codecheck::spec::check_seq(c), m.rip, m, s5),
    ensures
        ({
            let cs = clazel_codecheck::spec::check_seq(c);
            exists|s8: x64::State|
                #![trigger reaches(cu, cs, m.rip, m, s8)]
                reaches(cu, cs, m.rip, m, s8) && x64::wf(s8) && s8.mem == m.mem && s8.xmm == m.xmm
                    && s8.rgf == s5.rgf.update(0, 0u64) && s8.rip == m.rip + 47
        }),
{
    super::memlemmas::lemma_p2_consts();
    let cs = clazel_codecheck::spec::check_seq(c);
    lemma_check_fetch(c);
    lemma_check_instr_lens(c);
    lemma_table_words(lay, m, c.k as nat);
    let rip0 = m.rip;
    let ix = m.rgf[1] as int;
    let bound = lay[c.k].bound as int;
    super::runseq::lemma_canonical_between(rip0, rip0 + 35, rip0 + 47);
    super::runseq::lemma_canonical_between(rip0, rip0 + 43, rip0 + 47);
    let bm = clazel_codecheck::spec::bound_mem(c.k);
    let i5 = clazel_codecheck::spec::check_instr(5, c);
    let i6 = clazel_codecheck::spec::check_instr(6, c);
    let i7 = clazel_codecheck::spec::check_instr(7, c);
    assert(i5 == x64::Instr::MovImm32 { dst: 0, imm_u32: 0 });
    super::steps::lemma_step_imm(cu, s5, i5);
    let s6 = x64::step(cu, s5, i5).unwrap();
    lemma_wf_like(m, s6);
    lemma_reach_step(cu, cs, rip0, m, s5, i5, s6);
    assert(i6 == x64::Instr::AluRM { alu: x64::AluOp::Cmp, sz: x64::Size::W64, dst: 1, mem: bm });
    assert(x64::eff_addr(s6, bm) == x64::eff_addr(m, bm));
    assert(s6.rgf[1] == m.rgf[1]);
    lemma_step_cmp_rm64(cu, s6, 1, bm, bound);
    let s7 = x64::step(cu, s6, i6).unwrap();
    lemma_wf_like(m, s7);
    lemma_reach_step(cu, cs, rip0, m, s6, i6, s7);
    assert(i7 == x64::Instr::Cmovcc { cc: 3, sz: x64::Size::W64, dst: 1, src: 0 });
    assert(x64::jcc_cmovcc_setcc_spec(s7, 3) == (ix >= bound));
    super::flags::lemma_step_cmov64(cu, s7, 3, 1, 0);
    let s8 = x64::step(cu, s7, i7).unwrap();
    lemma_wf_like(m, s8);
    lemma_reach_step(cu, cs, rip0, m, s7, i7, s8);
    assert(s8.rgf == s7.rgf);
}

/// **The bounds check, run.** From a state with the index `ix` in `rcx`: if
/// `ix + n <= bound` the check falls through to its end (47 bytes on), else it
/// leaves by the first exit (a carry) or the second (`ix + n > bound`).
#[verifier::rlimit(2000)]
pub proof fn lemma_check_run(
    cu: spec_fn(nat) -> nat,
    lay: lir::Layout,
    m: x64::State,
    k: nat,
    n: nat,
    r1: int,
    r2: int,
)
    requires
        x64::wf(m),
        ctx_ok(m),
        table_ok(lay, m),
        k < lay.len(),
        1 <= n <= 8,
        -0x8000_0000 <= r1 < 0x8000_0000,
        -0x8000_0000 <= r2 < 0x8000_0000,
        x64::canonical(m.rip + 47),
        x64::canonical(m.rip + 16 + r1),
        x64::canonical(m.rip + 30 + r2),
    ensures
        ({
            let cs = clazel_codecheck::spec::check_seq(mem_chk(k, n, r1, r2));
            let ix = m.rgf[1] as int;
            let bound = lay[k as int].bound as int;
            &&& (ix + n <= bound ==> exists|m2: x64::State|
                #![trigger reaches(cu, cs, m.rip, m, m2)]
                reaches(cu, cs, m.rip, m, m2) && m2.rip == m.rip + 47 && keeps(m, m2)
                    && m2.rgf[1] == m.rgf[1])
            &&& (ix + n > bound ==> exists|m2: x64::State|
                #![trigger reaches(cu, cs, m.rip, m, m2)]
                reaches(cu, cs, m.rip, m, m2) && (m2.rip == m.rip + 16 + r1 || m2.rip == m.rip + 30
                    + r2) && keeps(m, m2) && m2.rgf[1] == m.rgf[1])
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let c = mem_chk(k, n, r1, r2);
    assert(c.n == n as int && c.r1 == r1 as i32 && c.r2 == r2 as i32);
    assert(c.r1 as int == r1 && c.r2 as int == r2);
    lemma_table_words(lay, m, k);
    let ix = m.rgf[1] as int;
    let bound = lay[k as int].bound as int;
    lemma_chk_head(cu, m, c);
    let s3 = choose|s3: x64::State|
        reaches(cu, clazel_codecheck::spec::check_seq(c), m.rip, m, s3) && x64::wf(s3) && s3.mem
            == m.mem && s3.xmm == m.xmm && s3.rgf == m.rgf.update(
            2,
            ((ix + n) % 0x1_0000_0000_0000_0000) as u64,
        ) && s3.rip == (if ix + n >= 0x1_0000_0000_0000_0000 {
            m.rip + 16 + r1
        } else {
            m.rip + 16
        });
    assert(s3.rgf.len() == 16);
    if ix + n >= 0x1_0000_0000_0000_0000 {
        assert(ix + n > bound);
        assert(keeps(m, s3));
    } else {
        assert(s3.rgf[2] as int == ix + n);
        lemma_chk_mid(cu, lay, m, s3, c);
        let s5 = choose|s5: x64::State|
            reaches(cu, clazel_codecheck::spec::check_seq(c), m.rip, m, s5) && x64::wf(s5)
                && s5.mem == m.mem && s5.xmm == m.xmm && s5.rgf == s3.rgf && s5.rip == (if ix + n
                > bound {
                m.rip + 30 + r2
            } else {
                m.rip + 30
            });
        if ix + n > bound {
            assert(keeps(m, s5));
        } else {
            lemma_chk_tail(cu, lay, m, s5, c);
            let s8 = choose|s8: x64::State|
                reaches(cu, clazel_codecheck::spec::check_seq(c), m.rip, m, s8) && x64::wf(s8)
                    && s8.mem == m.mem && s8.xmm == m.xmm && s8.rgf == s5.rgf.update(0, 0u64)
                    && s8.rip == m.rip + 47;
            assert(keeps(m, s8));
        }
    }
}

} // verus!

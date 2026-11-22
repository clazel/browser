//! **The run of the validator's bounds-check sequence** (jit.md J.6; the
//! sequence is `clazel_codecheck::a64::spec::check_seq`): from the state at
//! its first instruction, in a list of code that contains it, the machine
//! reaches the stub both its exits go to when `i + n > bound`, and falls
//! through to the instruction after it, with the index unchanged (`csel i, i,
//! xzr, lo` is the identity after the check), when `i + n <= bound`. The A64
//! counterpart of [`crate::cfcheckrun`]. Only registers `x0` to `x2` and the
//! flags change.

#[cfg(verus_only)]
use super::cfleaf::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cfsteps::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use clazel_codecheck::a64::spec::{Chk, check_instr};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the check leaves alone: the memory, `SP`, the vector registers, and
/// every general register but `x0`, `x1` and `x2` (the flags are not
/// mentioned).
pub open spec fn chk_frame(s: isa::State, s2: isa::State) -> bool {
    s2.r.len() == 31 && s.r.len() == 31 && s2.vreg == s.vreg && s2.mem == s.mem && s2.sp == s.sp
        && forall|k: int|
        0 <= k < 31 && k != 0 && k != 1 && k != 2 ==> #[trigger] s2.r[k] == s.r[k]
}

/// [`chk_frame`] is transitive.
pub proof fn lemma_chk_frame_trans(s: isa::State, s1: isa::State, s2: isa::State)
    requires
        chk_frame(s, s1),
        chk_frame(s1, s2),
    ensures
        chk_frame(s, s2),
{
}

/// One step at index `idx` of `code`, placed at `b0`, is a run of the code.
pub proof fn lemma_reach_step(
    code: Seq<isa::Instr>,
    b0: int,
    s: isa::State,
    idx: int,
    s1: isa::State,
)
    requires
        0 <= idx < code.len(),
        s.pc as int == b0 + 4 * idx,
        isa::step(s, code[idx]) == Some(s1),
    ensures
        reaches(code, b0, s, s1),
{
    assert(fetch(code, s.pc as int - b0) == Some(code[idx]));
    lemma_steps_one(code, b0, s, code[idx], s1);
}

/// `ldr xr, [x28, #(8 imm12)]` loads the word at that offset of the context
/// into `xr`.
pub proof fn lemma_step_ctx_ld(m: isa::State, r: u8, imm12: u16, v: nat)
    requires
        isa::wf(m),
        ctx_ok(m),
        r < 31,
        imm12 as int * 8 + 8 <= abi::ctx_size(),
        isa::mem_read(m.mem, ctx_of(m) + imm12 as int * 8, 8) == Some(v as int),
        v < 0x1_0000_0000_0000_0000,
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(
            m,
            isa::Instr::LoadStoreImm {
                sf: isa::Width::W64,
                load: true,
                t: r,
                n: abi::ctx_reg(),
                imm12,
            },
        ) == Some(isa::State { r: m.r.update(r as int, v as u64), pc: (m.pc + 4) as u64, ..m }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    super::steps::lemma_x_read64(m, 28);
    super::memlemmas::lemma_trunc64(v as int);
    super::memlemmas::lemma_trunc64(m.pc as int + 4);
    super::memlemmas::lemma_trunc64(ctx_of(m) + imm12 as int * 8);
    let i = isa::Instr::LoadStoreImm {
        sf: isa::Width::W64,
        load: true,
        t: r,
        n: abi::ctx_reg(),
        imm12,
    };
    assert(isa::x_read(m, 28, 64) == ctx_of(m));
    assert(isa::datasize(isa::Width::W64) == 64);
    assert(isa::execute(m, i) == Some(isa::x_set(m, r, 64, v as int)));
    assert(isa::x_set(m, r, 64, v as int) == isa::State { r: m.r.update(r as int, v as u64), ..m });
}

#[verifier::rlimit(2000)]
/// `adds xd, xn, #imm` (64 bits): `xd` gets the sum modulo `2^64`, and the
/// carry flag says it wrapped.
pub proof fn lemma_step_adds_imm(s: isa::State, d: u8, n: u8, imm: u16, x: u64)
    requires
        isa::wf(s),
        d < 31,
        n < 31,
        s.r[n as int] == x,
        imm < 4096,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let i = isa::Instr::AddSubImm {
                sf: isa::Width::W64,
                sub_op: false,
                setflags: true,
                d,
                n,
                imm12: imm,
                sh: false,
            };
            &&& isa::step(s, i) is Some
            &&& ({
                let s1 = isa::step(s, i).unwrap();
                &&& s1.pc as int == s.pc as int + 4
                &&& s1.r == s.r.update(
                    d as int,
                    ((x as int + imm as int) % 0x1_0000_0000_0000_0000) as u64,
                )
                &&& s1.mem == s.mem
                &&& s1.sp == s.sp
                &&& s1.vreg == s.vreg
                &&& s1.flag_c == (x as int + imm as int >= 0x1_0000_0000_0000_0000)
            })
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    let p: int = 0x1_0000_0000_0000_0000;
    let h: int = 0x8000_0000_0000_0000;
    let xi = x as int;
    let yi = imm as int;
    super::alu::lemma_trunc_small(64, xi);
    super::alu::lemma_trunc_small(64, yi);
    let us = xi + yi;
    let res = us % p;
    assert(isa::trunc(64, us) == res);
    let sx = if xi >= h { xi - p } else { xi };
    let sy = yi;
    assert(isa::sint(64, xi) == sx && isa::sint(64, yi) == sy);
    let ss = sx + sy;
    let fn_ = (res / h) % 2;
    let fz = if res == 0 {
        1int
    } else {
        0
    };
    let fc = if res == us {
        0int
    } else {
        1
    };
    let sres = if res >= h {
        res - p
    } else {
        res
    };
    assert(isa::sint(64, res) == sres);
    let fv = if sres == ss {
        0int
    } else {
        1
    };
    assert(isa::bit(res, 63) == fn_);
    assert(isa::add_with_carry(64, xi, yi, 0) == (res, fn_ * 8 + fz * 4 + fc * 2 + fv));
    assert(0 <= fn_ <= 1 && 0 <= res < p);
    super::flags::lemma_nzcv_bits(fn_, fz, fc, fv);
    let i = isa::Instr::AddSubImm {
        sf: isa::Width::W64,
        sub_op: false,
        setflags: true,
        d,
        n,
        imm12: imm,
        sh: false,
    };
    assert(isa::x_read(s, n, 64) == xi);
    let s0 = isa::set_nzcv(s, fn_ * 8 + fz * 4 + fc * 2 + fv);
    assert(s0.flag_c == (fc == 1));
    assert(isa::execute(s, i) == Some(isa::x_set(s0, d, 64, res)));
}

/// `cmp xn, xm` (64 bits, `subs xzr, xn, xm`) sets the flags of `x - y`.
pub proof fn lemma_step_cmp_rr(s: isa::State, n: u8, m: u8, x: u64, y: u64)
    requires
        isa::wf(s),
        n < 31,
        m < 31,
        s.r[n as int] == x,
        s.r[m as int] == y,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::cmp_rr(isa::Width::W64, n, m)) == Some(
            isa::State {
                pc: (s.pc + 4) as u64,
                ..isa::set_nzcv(s, super::flags::cmp_nzcv(64, x as int, y as int))
            },
        ),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    super::alu::lemma_trunc_small(64, x as int);
    super::alu::lemma_trunc_small(64, y as int);
    assert(isa::lsl(64, y as int, 0) == y as int) by {
        assert(isa::p2(0) == 1);
    }
}

/// The flags of `cmp x, y`: `hi` (condition 8) holds exactly when `x > y`, and
/// `lo` (3) exactly when `x < y`.
pub proof fn lemma_cmp_hi_lo(s: isa::State, x: int, y: int)
    requires
        0 <= x < 0x1_0000_0000_0000_0000,
        0 <= y < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let t = isa::set_nzcv(s, super::flags::cmp_nzcv(64, x, y));
            &&& isa::condition_holds(t, 8) == (x > y)
            &&& isa::condition_holds(t, 3) == (x < y)
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::flags::lemma_cmp_arith64(x, y);
    let nzcv = super::flags::cmp_nzcv(64, x, y);
    let t = isa::set_nzcv(s, nzcv);
    assert(0 <= isa::bit(nzcv, 1) <= 1 && 0 <= isa::bit(nzcv, 2) <= 1);
    assert(t.flag_c == (isa::bit(nzcv, 1) == 1));
    assert(t.flag_z == (isa::bit(nzcv, 2) == 1));
}

/// `csel xd, xn, xzr, lo` (64 bits): `xd` is `xn` when the carry is clear and
/// zero when it is set.
pub proof fn lemma_step_csel_lo(s: isa::State, d: u8, n: u8, x: u64)
    requires
        isa::wf(s),
        d < 31,
        n < 31,
        s.r[n as int] == x,
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let i = isa::Instr::CondSelect {
                sf: isa::Width::W64,
                else_inv: false,
                else_inc: false,
                d,
                n,
                m: 31,
                cond: 3,
            };
            &&& isa::step(s, i) == Some(
                isa::State {
                    r: s.r.update(d as int, if isa::condition_holds(s, 3) {
                        x
                    } else {
                        0u64
                    }),
                    pc: (s.pc + 4) as u64,
                    ..s
                },
            )
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::alu::lemma_pc4(s.pc);
    super::alu::lemma_trunc_small(64, x as int);
    let i = isa::Instr::CondSelect {
        sf: isa::Width::W64,
        else_inv: false,
        else_inc: false,
        d,
        n,
        m: 31,
        cond: 3,
    };
    assert(isa::x_read(s, 31, 64) == 0int);
    assert(isa::trunc(64, 0int) == 0int) by {
        super::alu::lemma_trunc_small(64, 0int);
    }
}

/// Word `j` of the check in `code` (starting at word `st`, both exits to word
/// `sx`) is the validator's instruction `j` for region `k`, `n` bytes.
pub open spec fn chk_at(code: Seq<isa::Instr>, st: int, sx: int, k: nat, n: nat, j: int) -> bool {
    0 <= st + j < code.len() && code[st + j] == check_instr(
        j,
        mem_chk(k, n, sx - (st + 2), sx - (st + 4)),
    )
}

/// **The first three instructions of the check**: the bound into `x2`, `adds`,
/// and the branch on the carry. If the sum wrapped the machine is at the stub;
/// if not, at the fourth instruction, with `x0` the sum.
#[verifier::rlimit(400)]
pub proof fn lemma_chk_head(
    code: Seq<isa::Instr>,
    b0: int,
    st: int,
    sx: int,
    k: nat,
    n: nat,
    s: isa::State,
    ix: u64,
    bnd: u64,
)
    requires
        0 <= st,
        st + 7 <= sx,
        sx < st + 0x1_0000,
        0 <= b0,
        b0 + 4 * sx + 4 < 0x1_0000_0000_0000_0000,
        chk_at(code, st, sx, k, n, 0),
        chk_at(code, st, sx, k, n, 1),
        chk_at(code, st, sx, k, n, 2),
        s.pc as int == b0 + 4 * st,
        isa::wf(s),
        ctx_ok(s),
        k < 16,
        1 <= n <= 8,
        s.r[1] == ix,
        isa::mem_read(s.mem, ctx_of(s) + abi::bound_off(k as int), 8) == Some(bnd as int),
    ensures
        exists|s3: isa::State|
            #![trigger reaches(code, b0, s, s3)]
            reaches(code, b0, s, s3) && chk_frame(s, s3) && isa::wf(s3) && ctx_ok(s3)
                && s3.r[1] == ix && s3.r[2] == bnd && (ix as int + n >= 0x1_0000_0000_0000_0000
                ==> s3.pc as int == b0 + 4 * sx) && (ix as int + n < 0x1_0000_0000_0000_0000
                ==> s3.pc as int == b0 + 4 * (st + 3) && s3.r[0] as int == ix as int + n),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    let p: int = 0x1_0000_0000_0000_0000;
    let c = mem_chk(k, n, sx - (st + 2), sx - (st + 4));
    let r1 = sx - (st + 2);
    let xi = ix as int;
    let ni = n as int;
    let i0 = check_instr(0, c);
    assert(i0 == isa::Instr::LoadStoreImm {
        sf: isa::Width::W64,
        load: true,
        t: 2,
        n: abi::ctx_reg(),
        imm12: (abi::bound_off(k as int) / 8) as u16,
    });
    assert((abi::bound_off(k as int) / 8) as u16 as int * 8 == abi::bound_off(k as int));
    lemma_step_ctx_ld(s, 2, (abi::bound_off(k as int) / 8) as u16, bnd as nat);
    let s1 = isa::step(s, i0).unwrap();
    lemma_reach_step(code, b0, s, st, s1);
    assert(s1.r[1] == ix && s1.r[2] == bnd);
    let i1 = check_instr(1, c);
    lemma_step_adds_imm(s1, 0, 1, n as u16, ix);
    let s2 = isa::step(s1, i1).unwrap();
    lemma_reach_step(code, b0, s1, st + 1, s2);
    assert(s2.flag_c == (xi + ni >= p));
    assert(s2.r[1] == ix && s2.r[2] == bnd);
    let i2 = check_instr(2, c);
    assert(i2 == bcond_i(2, 4 * r1)) by {
        assert((4 * r1) / 4 == r1);
        assert(c.r1 == r1 as i32);
    }
    assert(isa::condition_holds(s2, 2) == s2.flag_c);
    assert(0 <= s2.pc as int + 4 * r1 < p);
    lemma_step_bcond(s2, 2, 4 * r1);
    let s3 = isa::step(s2, i2).unwrap();
    lemma_reach_step(code, b0, s2, st + 2, s3);
    lemma_chk_frame_trans(s, s1, s2);
    lemma_chk_frame_trans(s, s2, s3);
    lemma_reaches_trans(code, b0, s, s1, s2);
    lemma_reaches_trans(code, b0, s, s2, s3);
    assert(s3.r[1] == ix && s3.r[2] == bnd);
    assert(isa::wf(s3) && ctx_ok(s3));
    if xi + ni < p {
        assert((xi + ni) % p == xi + ni) by {
            vstd::arithmetic::div_mod::lemma_small_mod((xi + ni) as nat, p as nat);
        }
    }
}

/// **The compare and `b.hi`**: from the fourth instruction, with `x0` the sum
/// `sum` (no wrap) and `x2` the bound, the machine reaches the stub if `sum >
/// bnd` and the sixth instruction if not.
#[verifier::rlimit(400)]
pub proof fn lemma_chk_mid(
    code: Seq<isa::Instr>,
    b0: int,
    st: int,
    sx: int,
    k: nat,
    n: nat,
    s: isa::State,
    sum: int,
    bnd: u64,
)
    requires
        0 <= st,
        st + 7 <= sx,
        sx < st + 0x1_0000,
        0 <= b0,
        b0 + 4 * sx + 4 < 0x1_0000_0000_0000_0000,
        chk_at(code, st, sx, k, n, 3),
        chk_at(code, st, sx, k, n, 4),
        s.pc as int == b0 + 4 * (st + 3),
        isa::wf(s),
        0 <= sum < 0x1_0000_0000_0000_0000,
        s.r[0] as int == sum,
        s.r[2] == bnd,
    ensures
        exists|s5: isa::State|
            #![trigger reaches(code, b0, s, s5)]
            reaches(code, b0, s, s5) && chk_frame(s, s5) && s5.r[1] == s.r[1] && s5.r[2] == bnd
                && (sum > bnd as int ==> s5.pc as int == b0 + 4 * sx) && (sum <= bnd as int
                ==> s5.pc as int == b0 + 4 * (st + 5)),
{
    super::memlemmas::lemma_p2_consts();
    let p: int = 0x1_0000_0000_0000_0000;
    let c = mem_chk(k, n, sx - (st + 2), sx - (st + 4));
    let r2 = sx - (st + 4);
    let bi = bnd as int;
    let i3 = check_instr(3, c);
    assert(i3 == super::templates::cmp_rr(isa::Width::W64, 0, 2));
    lemma_step_cmp_rr(s, 0, 2, s.r[0], bnd);
    let s4 = isa::step(s, i3).unwrap();
    lemma_reach_step(code, b0, s, st + 3, s4);
    lemma_cmp_hi_lo(s, sum, bi);
    assert(isa::condition_holds(s4, 8) == (sum > bi)) by {
        assert(s4 == isa::State {
            pc: (s.pc + 4) as u64,
            ..isa::set_nzcv(s, super::flags::cmp_nzcv(64, sum, bi))
        });
    }
    let i4 = check_instr(4, c);
    assert(i4 == bcond_i(8, 4 * r2)) by {
        assert((4 * r2) / 4 == r2);
        assert(c.r2 == r2 as i32);
    }
    assert(0 <= s4.pc as int + 4 * r2 < p);
    lemma_step_bcond(s4, 8, 4 * r2);
    let s5 = isa::step(s4, i4).unwrap();
    lemma_reach_step(code, b0, s4, st + 4, s5);
    lemma_chk_frame_trans(s, s4, s5);
    lemma_reaches_trans(code, b0, s, s4, s5);
}

/// **The last compare and the mask**: from the sixth instruction, with `x1` the
/// index `ix` below the bound `bnd` in `x2`, the machine reaches the word after
/// the check with `x1` still `ix`.
#[verifier::rlimit(400)]
pub proof fn lemma_chk_tail(
    code: Seq<isa::Instr>,
    b0: int,
    st: int,
    sx: int,
    k: nat,
    n: nat,
    s: isa::State,
    ix: u64,
    bnd: u64,
)
    requires
        0 <= st,
        0 <= b0,
        b0 + 4 * (st + 7) < 0x1_0000_0000_0000_0000,
        chk_at(code, st, sx, k, n, 5),
        chk_at(code, st, sx, k, n, 6),
        s.pc as int == b0 + 4 * (st + 5),
        isa::wf(s),
        s.r[1] == ix,
        s.r[2] == bnd,
        ix < bnd,
    ensures
        exists|s7: isa::State|
            #![trigger reaches(code, b0, s, s7)]
            reaches(code, b0, s, s7) && chk_frame(s, s7) && s7.r[1] == ix && s7.pc as int == b0 + 4
                * (st + 7),
{
    super::memlemmas::lemma_p2_consts();
    let c = mem_chk(k, n, sx - (st + 2), sx - (st + 4));
    let xi = ix as int;
    let bi = bnd as int;
    let i5 = check_instr(5, c);
    assert(i5 == super::templates::cmp_rr(isa::Width::W64, 1, 2));
    lemma_step_cmp_rr(s, 1, 2, ix, bnd);
    let s6 = isa::step(s, i5).unwrap();
    lemma_reach_step(code, b0, s, st + 5, s6);
    lemma_cmp_hi_lo(s, xi, bi);
    assert(isa::condition_holds(s6, 3)) by {
        assert(s6 == isa::State {
            pc: (s.pc + 4) as u64,
            ..isa::set_nzcv(s, super::flags::cmp_nzcv(64, xi, bi))
        });
    }
    let i6 = check_instr(6, c);
    lemma_step_csel_lo(s6, 1, 1, ix);
    let s7 = isa::step(s6, i6).unwrap();
    lemma_reach_step(code, b0, s6, st + 6, s7);
    lemma_chk_frame_trans(s, s6, s7);
    lemma_reaches_trans(code, b0, s, s6, s7);
}

/// **The run of the bounds check.** `code` is placed at `b0`; its words `st` to
/// `st + 6` are the check for region `k`, `n` bytes, with both exits going to
/// word `sx`; the machine is at its first word with the index `ix` in `x1` and
/// the region's bound `bnd` in the context table. If `ix + n > bnd` the check
/// reaches `sx`; if not, the word after the check, with `x1` still `ix`.
pub proof fn lemma_check_run(
    code: Seq<isa::Instr>,
    b0: int,
    st: int,
    sx: int,
    k: nat,
    n: nat,
    s: isa::State,
    ix: u64,
    bnd: u64,
)
    requires
        0 <= st,
        st + 7 <= sx,
        sx < st + 0x1_0000,
        0 <= b0,
        b0 + 4 * sx + 4 < 0x1_0000_0000_0000_0000,
        b0 + 4 * (st + 7) < 0x1_0000_0000_0000_0000,
        forall|j: int| 0 <= j < 7 ==> #[trigger] chk_at(code, st, sx, k, n, j),
        s.pc as int == b0 + 4 * st,
        isa::wf(s),
        ctx_ok(s),
        k < 16,
        1 <= n <= 8,
        s.r[1] == ix,
        isa::mem_read(s.mem, ctx_of(s) + abi::bound_off(k as int), 8) == Some(bnd as int),
    ensures
        ix as int + n > bnd as int ==> exists|s2: isa::State|
            #![trigger reaches(code, b0, s, s2)]
            reaches(code, b0, s, s2) && s2.pc as int == b0 + 4 * sx && chk_frame(s, s2),
        ix as int + n <= bnd as int ==> exists|s2: isa::State|
            #![trigger reaches(code, b0, s, s2)]
            reaches(code, b0, s, s2) && s2.pc as int == b0 + 4 * (st + 7) && chk_frame(s, s2)
                && s2.r[1] == ix,
{
    super::memlemmas::lemma_p2_consts();
    let p: int = 0x1_0000_0000_0000_0000;
    assert(chk_at(code, st, sx, k, n, 0));
    assert(chk_at(code, st, sx, k, n, 1));
    assert(chk_at(code, st, sx, k, n, 2));
    assert(chk_at(code, st, sx, k, n, 3));
    assert(chk_at(code, st, sx, k, n, 4));
    assert(chk_at(code, st, sx, k, n, 5));
    assert(chk_at(code, st, sx, k, n, 6));
    lemma_chk_head(code, b0, st, sx, k, n, s, ix, bnd);
    let s3 = choose|s3: isa::State|
        reaches(code, b0, s, s3) && chk_frame(s, s3) && isa::wf(s3) && ctx_ok(s3) && s3.r[1] == ix
            && s3.r[2] == bnd && (ix as int + n >= p ==> s3.pc as int == b0 + 4 * sx) && (ix as int
            + n < p ==> s3.pc as int == b0 + 4 * (st + 3) && s3.r[0] as int == ix as int + n);
    if ix as int + n < p {
        let sum = ix as int + n as int;
        lemma_chk_mid(code, b0, st, sx, k, n, s3, sum, bnd);
        let s5 = choose|s5: isa::State|
            reaches(code, b0, s3, s5) && chk_frame(s3, s5) && s5.r[1] == s3.r[1] && s5.r[2] == bnd
                && (sum > bnd as int ==> s5.pc as int == b0 + 4 * sx) && (sum <= bnd as int
                ==> s5.pc as int == b0 + 4 * (st + 5));
        lemma_reaches_trans(code, b0, s, s3, s5);
        lemma_chk_frame_trans(s, s3, s5);
        if sum <= bnd as int {
            assert(isa::wf(s5));
            lemma_chk_tail(code, b0, st, sx, k, n, s5, ix, bnd);
            let s7 = choose|s7: isa::State|
                reaches(code, b0, s5, s7) && chk_frame(s5, s7) && s7.r[1] == ix && s7.pc as int == b0
                    + 4 * (st + 7);
            lemma_reaches_trans(code, b0, s, s5, s7);
            lemma_chk_frame_trans(s, s5, s7);
        }
    }
}

} // verus!

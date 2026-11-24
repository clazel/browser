//! The register-only middle of each template: from a machine state whose
//! scratch registers hold the operands, running the template's computation
//! leaves the LIR result in `rax` ([`mid_post`]). One lemma per shape, each a
//! chain of the single-step lemmas of [`crate::steps`], [`crate::alu`] and
//! [`crate::flags`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The integer operators with a one-instruction middle.
pub open spec fn int_op_ok(o: lir::IBin) -> bool {
    ibin_supported(o)
}

/// Writing a register with a 32-bit result leaves the zero-extended word, and
/// changes that register only.
pub proof fn lemma_set_rgfi(m: x64::State, sz: x64::Size, dst: u8, v: int)
    requires
        m.rgf.len() == 16,
        dst < 16,
        0 <= v,
        sz is W32 ==> v < 0x1_0000_0000,
        v < 0x1_0000_0000_0000_0000,
    ensures
        x64::set_rgfi_size(m, sz, dst, v).rgf == m.rgf.update(dst as int, v as u64),
{
    super::memlemmas::lemma_p2_consts();
    assert(x64::loghead(32, v) == v || sz is W64);
    assert(x64::loghead(64, v) == v);
}

/// `op rax, rcx` for the integer operators of the first slice, 32-bit: leaves
/// LIR's result (`ibin32`) in `rax`.
#[verifier::rlimit(1000)]
pub proof fn lemma_mid_int32(cu: spec_fn(nat) -> nat, s: x64::State, o: lir::IBin, x: u32, y: u32)
    requires
        x64::wf(s),
        int_op_ok(o),
        s.rgf[0] == x as u64,
        s.rgf[1] == y as u64,
        x64::canonical(s.rip + x64::instr_len(super::templates::int_op_instr(o, x64::Size::W32))),
    ensures
        run_seq(cu, s, seq![super::templates::int_op_instr(o, x64::Size::W32)]) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, seq![super::templates::int_op_instr(o, x64::Size::W32)]).unwrap(),
            rax(),
            lir::ibin32(o, x, y) as nat,
            code_len(seq![super::templates::int_op_instr(o, x64::Size::W32)]),
        ),
{
    super::memlemmas::lemma_p2_consts();
    let i = super::templates::int_op_instr(o, x64::Size::W32);
    super::runseq::lemma_run_seq_one(cu, s, i);
    super::runseq::lemma_code_len_one(i);
    assert(x64::rgfi_size(s, x64::Size::W32, 0) == x as int);
    assert(x64::rgfi_size(s, x64::Size::W32, 1) == y as int);
    let m1 = x64::step(cu, s, i).unwrap();
    if super::templates::alu_of(o) is Some {
        let alu = super::templates::alu_of(o).unwrap();
        super::alu::lemma_step_alu_rr(cu, s, alu, x64::Size::W32, 0, 1);
        super::alu::lemma_val32_alu(o, x, y, s.rflags);
        let r = x64::gpr_arith_logic_spec(32, alu, x as int, y as int, s.rflags);
        lemma_set_rgfi(s, x64::Size::W32, 0, r.result);
    } else if super::templates::shift_of(o) is Some {
        let sh = super::templates::shift_of(o).unwrap();
        super::alu::lemma_step_shift_cl(cu, s, sh, x64::Size::W32, 0);
        super::alu::lemma_val32_shift(o, x, y, s.rflags);
        assert(x64::rr64(s, 1) == y as int);
        let cnt = x64::shift_count(x64::Size::W32, x64::loghead(8, y as int));
        let res = x64::shift_spec(sh, 32, x as int, cnt, s.rflags).result;
        lemma_set_rgfi(s, x64::Size::W32, 0, res);
    } else {
        assert(o == lir::IBin::Mul);
        super::alu::lemma_step_imul_rr(cu, s, x64::Size::W32, 0, 1);
        super::alu::lemma_val32_mul(x, y);
        let (low, cf) = x64::imul_spec(32, y as int, x as int);
        lemma_set_rgfi(s, x64::Size::W32, 0, low);
    }
}

/// `op rax, rcx` for the integer operators of the first slice, 64-bit.
#[verifier::rlimit(1000)]
pub proof fn lemma_mid_int64(cu: spec_fn(nat) -> nat, s: x64::State, o: lir::IBin, x: u64, y: u64)
    requires
        x64::wf(s),
        int_op_ok(o),
        s.rgf[0] == x,
        s.rgf[1] == y,
        x64::canonical(s.rip + x64::instr_len(super::templates::int_op_instr(o, x64::Size::W64))),
    ensures
        run_seq(cu, s, seq![super::templates::int_op_instr(o, x64::Size::W64)]) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, seq![super::templates::int_op_instr(o, x64::Size::W64)]).unwrap(),
            rax(),
            lir::ibin64(o, x, y) as nat,
            code_len(seq![super::templates::int_op_instr(o, x64::Size::W64)]),
        ),
{
    super::memlemmas::lemma_p2_consts();
    let i = super::templates::int_op_instr(o, x64::Size::W64);
    super::runseq::lemma_run_seq_one(cu, s, i);
    super::runseq::lemma_code_len_one(i);
    assert(x64::rgfi_size(s, x64::Size::W64, 0) == x as int);
    assert(x64::rgfi_size(s, x64::Size::W64, 1) == y as int);
    let m1 = x64::step(cu, s, i).unwrap();
    if super::templates::alu_of(o) is Some {
        let alu = super::templates::alu_of(o).unwrap();
        super::alu::lemma_step_alu_rr(cu, s, alu, x64::Size::W64, 0, 1);
        super::alu::lemma_val64_alu(o, x, y, s.rflags);
        let r = x64::gpr_arith_logic_spec(64, alu, x as int, y as int, s.rflags);
        lemma_set_rgfi(s, x64::Size::W64, 0, r.result);
    } else if super::templates::shift_of(o) is Some {
        let sh = super::templates::shift_of(o).unwrap();
        super::alu::lemma_step_shift_cl(cu, s, sh, x64::Size::W64, 0);
        super::alu::lemma_val64_shift(o, x, y, s.rflags);
        assert(x64::rr64(s, 1) == y as int);
        let cnt = x64::shift_count(x64::Size::W64, x64::loghead(8, y as int));
        let res = x64::shift_spec(sh, 64, x as int, cnt, s.rflags).result;
        lemma_set_rgfi(s, x64::Size::W64, 0, res);
    } else {
        assert(o == lir::IBin::Mul);
        super::alu::lemma_step_imul_rr(cu, s, x64::Size::W64, 0, 1);
        super::alu::lemma_val64_mul(x, y);
        let (low, cf) = x64::imul_spec(64, y as int, x as int);
        lemma_set_rgfi(s, x64::Size::W64, 0, low);
    }
}

/// A state with the same memory as a well-formed one, 16 registers of each
/// kind and a canonical `rip` is well formed.
pub proof fn lemma_wf_from(s: x64::State, s2: x64::State)
    requires
        x64::wf(s),
        s2.rgf.len() == 16,
        s2.xmm.len() == 16,
        s2.mem == s.mem,
        x64::canonical(s2.rip),
    ensures
        x64::wf(s2),
{
}

/// The `rip` after some of a run's instructions is canonical, when the end of
/// the whole run is.
pub proof fn lemma_rip_between(s: x64::State, ip: int, end: int)
    requires
        x64::wf(s),
        x64::canonical(end),
        s.rip <= ip <= end,
    ensures
        x64::canonical(ip),
{
}

/// `mov eax, 0; cmp rcx, rdx; setcc al` leaves 0 or 1 in `rax`: LIR's
/// comparison result.
#[verifier::rlimit(400)]
pub proof fn lemma_mid_cmp(
    cu: spec_fn(nat) -> nat,
    s: x64::State,
    op: lir::ICmp,
    sz: x64::Size,
    x: u64,
    y: u64,
)
    requires
        x64::wf(s),
        s.rgf[1] == x,
        s.rgf[2] == y,
        sz is W32 ==> x < 0x1_0000_0000 && y < 0x1_0000_0000,
        x64::canonical(s.rip + code_len(super::templates::cmp_mid(op, sz))),
    ensures
        run_seq(cu, s, super::templates::cmp_mid(op, sz)) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, super::templates::cmp_mid(op, sz)).unwrap(),
            rax(),
            lir::bool_i32(lir::icmp(op, x64::nbits(sz), x as int, y as int)) as nat,
            code_len(super::templates::cmp_mid(op, sz)),
        ),
{
    super::memlemmas::lemma_p2_consts();
    let n = x64::nbits(sz);
    let i1 = x64::Instr::MovImm32 { dst: rax(), imm_u32: 0 };
    let i2 = x64::Instr::AluRR { alu: x64::AluOp::Cmp, sz: sz, dst: rcx(), src: rdx() };
    let i3 = x64::Instr::Setcc { cc: super::templates::cc_of(op), dst: rax() };
    super::runseq::lemma_len3(i1, i2, i3);
    let total = code_len(super::templates::cmp_mid(op, sz));
    assert(super::templates::cmp_mid(op, sz) == seq![i1, i2, i3]);
    // 1. mov eax, 0
    super::steps::lemma_step_imm(cu, s, i1);
    let s1 = x64::State {
        rgf: s.rgf.update(0, 0u32 as u64),
        rip: s.rip + x64::instr_len(i1),
        ..s
    };
    assert(x64::step(cu, s, i1) == Some(s1));
    assert(x64::canonical(s1.rip));
    lemma_wf_from(s, s1);
    // 2. cmp rcx, rdx
    super::flags::lemma_step_cmp(cu, s1, sz, 1, 2);
    let s2 = x64::step(cu, s1, i2).unwrap();
    assert(x64::canonical(s2.rip));
    lemma_wf_from(s, s2);
    assert(s1.rgf[1] == x && s1.rgf[2] == y);
    assert(x64::rgfi_size(s1, sz, 1) == x as int);
    assert(x64::rgfi_size(s1, sz, 2) == y as int);
    assert(x64::loghead(n, x as int) == x as int);
    assert(x64::loghead(n, y as int) == y as int);
    super::flags::lemma_cc_icmp(s2, op, n, x as int, y as int);
    // 3. setcc al
    super::flags::lemma_step_setcc(cu, s2, super::templates::cc_of(op), 0);
    let s3 = x64::step(cu, s2, i3).unwrap();
    assert(s2.rgf[0] == 0);
    let f = super::runseq::stepper(cu);
    super::runseq::lemma_gen3(f, s, i1, i2, i3, s1, s2, s3);
    super::runseq::lemma_run_seq_is_gen(cu, s, seq![i1, i2, i3]);
    assert(s3.rgf[0] as nat == lir::bool_i32(lir::icmp(op, n, x as int, y as int)) as nat);
}

/// `mov eax, 0; test rcx, rcx; sete al` leaves `x == 0` in `rax`.
#[verifier::rlimit(100)]
pub proof fn lemma_mid_eqz(cu: spec_fn(nat) -> nat, s: x64::State, sz: x64::Size, x: u64)
    requires
        x64::wf(s),
        s.rgf[1] == x,
        sz is W32 ==> x < 0x1_0000_0000,
        x64::canonical(s.rip + code_len(super::templates::eqz_mid(sz))),
    ensures
        run_seq(cu, s, super::templates::eqz_mid(sz)) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, super::templates::eqz_mid(sz)).unwrap(),
            rax(),
            lir::bool_i32(x == 0) as nat,
            code_len(super::templates::eqz_mid(sz)),
        ),
{
    super::memlemmas::lemma_p2_consts();
    let n = x64::nbits(sz);
    let i1 = x64::Instr::MovImm32 { dst: rax(), imm_u32: 0 };
    let i2 = x64::Instr::TestRR { sz: sz, a: rcx(), b: rcx() };
    let i3 = x64::Instr::Setcc { cc: 4, dst: rax() };
    super::runseq::lemma_len3(i1, i2, i3);
    assert(super::templates::eqz_mid(sz) == seq![i1, i2, i3]);
    super::steps::lemma_step_imm(cu, s, i1);
    let s1 = x64::State {
        rgf: s.rgf.update(0, 0u32 as u64),
        rip: s.rip + x64::instr_len(i1),
        ..s
    };
    assert(x64::canonical(s1.rip));
    lemma_wf_from(s, s1);
    super::flags::lemma_step_test(cu, s1, sz, 1, 1);
    let s2 = x64::step(cu, s1, i2).unwrap();
    assert(x64::canonical(s2.rip));
    lemma_wf_from(s, s2);
    assert(x64::rgfi_size(s1, sz, 1) == x as int);
    assert(x64::loghead(n, x as int) == x as int);
    assert((x & x) == x) by (bit_vector);
    assert(((x as u64) & (x as u64)) as int == x as int);
    super::flags::lemma_step_setcc(cu, s2, 4, 0);
    let s3 = x64::step(cu, s2, i3).unwrap();
    assert(s2.rgf[0] == 0);
    assert(x64::zf_bit() == 6);
    let f = super::runseq::stepper(cu);
    super::runseq::lemma_gen3(f, s, i1, i2, i3, s1, s2, s3);
    super::runseq::lemma_run_seq_is_gen(cu, s, seq![i1, i2, i3]);
}

/// `mov rcx, mask; xor/and rax, rcx` leaves `x ^ mask` or `x & mask` in `rax`.
#[verifier::rlimit(100)]
pub proof fn lemma_mid_mask(
    cu: spec_fn(nat) -> nat,
    s: x64::State,
    alu: x64::AluOp,
    mask: u64,
    x: u64,
)
    requires
        x64::wf(s),
        alu is Xor || alu is And,
        s.rgf[0] == x,
        x64::canonical(s.rip + code_len(super::templates::mask_mid(alu, mask))),
    ensures
        run_seq(cu, s, super::templates::mask_mid(alu, mask)) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, super::templates::mask_mid(alu, mask)).unwrap(),
            rax(),
            (if alu is Xor {
                x ^ mask
            } else {
                x & mask
            }) as nat,
            code_len(super::templates::mask_mid(alu, mask)),
        ),
{
    super::memlemmas::lemma_p2_consts();
    let i1 = x64::Instr::MovImm64 { dst: rcx(), imm_u64: mask };
    let i2 = x64::Instr::AluRR { alu: alu, sz: x64::Size::W64, dst: rax(), src: rcx() };
    super::runseq::lemma_len2(i1, i2);
    assert(super::templates::mask_mid(alu, mask) == seq![i1, i2]);
    super::steps::lemma_step_imm(cu, s, i1);
    let s1 = x64::State {
        rgf: s.rgf.update(1, mask),
        rip: s.rip + x64::instr_len(i1),
        ..s
    };
    assert(x64::canonical(s1.rip));
    lemma_wf_from(s, s1);
    super::alu::lemma_step_alu_rr(cu, s1, alu, x64::Size::W64, 0, 1);
    let s2 = x64::step(cu, s1, i2).unwrap();
    assert(x64::rgfi_size(s1, x64::Size::W64, 0) == x as int);
    assert(x64::rgfi_size(s1, x64::Size::W64, 1) == mask as int);
    assert(x64::loghead(64, x as int) == x as int);
    assert(x64::loghead(64, mask as int) == mask as int);
    let r = x64::gpr_arith_logic_spec(64, alu, x as int, mask as int, s1.rflags);
    if alu is Xor {
        assert(r.result == ((x as u64) ^ (mask as u64)) as int);
    } else {
        assert(r.result == ((x as u64) & (mask as u64)) as int);
    }
    lemma_set_rgfi(s1, x64::Size::W64, 0, r.result);
    let f = super::runseq::stepper(cu);
    super::runseq::lemma_gen2(f, s, i1, i2, s1, s2);
    super::runseq::lemma_run_seq_is_gen(cu, s, seq![i1, i2]);
}

/// `mov ecx, 0x80000000; xor rax, rcx; sub rax, rcx` sign-extends the low 32
/// bits of `rax` to 64: LIR's `i64.extend_i32_s`.
#[verifier::rlimit(100)]
pub proof fn lemma_mid_exts(cu: spec_fn(nat) -> nat, s: x64::State, x: u32)
    requires
        x64::wf(s),
        s.rgf[0] == x as u64,
        x64::canonical(s.rip + code_len(super::templates::exts_mid())),
    ensures
        run_seq(cu, s, super::templates::exts_mid()) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, super::templates::exts_mid()).unwrap(),
            rax(),
            lir::wrap(64, lir::signed_of(32, x as int)) as u64 as nat,
            code_len(super::templates::exts_mid()),
        ),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    let i1 = x64::Instr::MovImm32 { dst: rcx(), imm_u32: 0x8000_0000 };
    let i2 = x64::Instr::AluRR {
        alu: x64::AluOp::Xor,
        sz: x64::Size::W64,
        dst: rax(),
        src: rcx(),
    };
    let i3 = x64::Instr::AluRR {
        alu: x64::AluOp::Sub,
        sz: x64::Size::W64,
        dst: rax(),
        src: rcx(),
    };
    super::runseq::lemma_len3(i1, i2, i3);
    assert(super::templates::exts_mid() == seq![i1, i2, i3]);
    super::steps::lemma_step_imm(cu, s, i1);
    let s1 = x64::State {
        rgf: s.rgf.update(1, 0x8000_0000u32 as u64),
        rip: s.rip + x64::instr_len(i1),
        ..s
    };
    assert(x64::canonical(s1.rip));
    lemma_wf_from(s, s1);
    // xor
    super::alu::lemma_step_alu_rr(cu, s1, x64::AluOp::Xor, x64::Size::W64, 0, 1);
    let s2 = x64::step(cu, s1, i2).unwrap();
    assert(x64::rgfi_size(s1, x64::Size::W64, 0) == x as int);
    assert(x64::rgfi_size(s1, x64::Size::W64, 1) == 0x8000_0000);
    assert(x64::loghead(64, x as int) == x as int);
    assert(x64::loghead(64, 0x8000_0000) == 0x8000_0000);
    let rx = x64::gpr_arith_logic_spec(64, x64::AluOp::Xor, x as int, 0x8000_0000, s1.rflags);
    assert(rx.result == ((x as u64) ^ 0x8000_0000u64) as int);
    let v: u64 = (x as u64) ^ 0x8000_0000u64;
    assert(((x as u64) ^ 0x8000_0000u64) == if x < 0x8000_0000 {
        (x as u64) + 0x8000_0000
    } else {
        (x as u64) - 0x8000_0000
    }) by (bit_vector);
    assert(v == if x < 0x8000_0000 {
        (x as u64) + 0x8000_0000
    } else {
        (x as u64) - 0x8000_0000
    });
    lemma_set_rgfi(s1, x64::Size::W64, 0, rx.result);
    assert(s2.rgf[0] == v);
    assert(s2.rgf[1] == 0x8000_0000u64);
    lemma_wf_from(s, s2);
    // sub
    super::alu::lemma_step_alu_rr(cu, s2, x64::AluOp::Sub, x64::Size::W64, 0, 1);
    let s3 = x64::step(cu, s2, i3).unwrap();
    assert(x64::rgfi_size(s2, x64::Size::W64, 0) == v as int);
    assert(x64::rgfi_size(s2, x64::Size::W64, 1) == 0x8000_0000);
    let rs = x64::gpr_sub_spec(64, v as int, 0x8000_0000, s2.rflags);
    assert(x64::loghead(64, v as int) == v as int);
    assert(x64::loghead(64, 0x8000_0000) == 0x8000_0000);
    assert(v < 0x1_0000_0000);
    assert(x64::logext(64, v as int) == v as int);
    assert(x64::logext(64, 0x8000_0000) == 0x8000_0000);
    assert(rs.result == (v as int - 0x8000_0000) % 0x1_0000_0000_0000_0000);
    assert(x64::gpr_arith_logic_spec(64, x64::AluOp::Sub, v as int, 0x8000_0000, s2.rflags)
        == rs);
    let sg = lir::signed_of(32, x as int);
    assert(lir::pow2(32) == 0x1_0000_0000);
    assert(lir::pow2(32) / 2 == 0x8000_0000);
    assert(sg == if x < 0x8000_0000 {
        x as int
    } else {
        x as int - 0x1_0000_0000
    });
    assert(lir::pow2(64) == 0x1_0000_0000_0000_0000);
    assert(rs.result == lir::wrap(64, sg));
    lemma_set_rgfi(s2, x64::Size::W64, 0, rs.result);
    let f = super::runseq::stepper(cu);
    super::runseq::lemma_gen3(f, s, i1, i2, i3, s1, s2, s3);
    super::runseq::lemma_run_seq_is_gen(cu, s, seq![i1, i2, i3]);
}

/// `mov eax, eax` leaves the low 32 bits of `rax`: LIR's `i32.wrap_i64`.
#[verifier::rlimit(100)]
pub proof fn lemma_mid_wrap(cu: spec_fn(nat) -> nat, s: x64::State, x: u64)
    requires
        x64::wf(s),
        s.rgf[0] == x,
        x64::canonical(s.rip + code_len(super::templates::wrap_mid())),
    ensures
        run_seq(cu, s, super::templates::wrap_mid()) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, super::templates::wrap_mid()).unwrap(),
            rax(),
            ((x & 0xFFFF_FFFF) as u32) as nat,
            code_len(super::templates::wrap_mid()),
        ),
{
    super::memlemmas::lemma_p2_consts();
    let i = x64::Instr::MovRR { sz: x64::Size::W32, dst: rax(), src: rax() };
    assert(super::templates::wrap_mid() == seq![i]);
    super::runseq::lemma_run_seq_one(cu, s, i);
    super::runseq::lemma_code_len_one(i);
    super::steps::lemma_step_mov_rr32(cu, s, 0, 0);
    assert((x & 0xFFFF_FFFFu64) as u32 as u64 == x % 0x1_0000_0000u64) by (bit_vector);
}

/// `test edx, edx; cmove rax, rcx` leaves the first value if the condition is
/// nonzero, else the second: LIR's `select`.
#[verifier::rlimit(100)]
pub proof fn lemma_mid_select(
    cu: spec_fn(nat) -> nat,
    s: x64::State,
    v1: u64,
    v2: u64,
    c: u32,
)
    requires
        x64::wf(s),
        s.rgf[0] == v1,
        s.rgf[1] == v2,
        s.rgf[2] == c as u64,
        x64::canonical(s.rip + code_len(super::templates::select_mid())),
    ensures
        run_seq(cu, s, super::templates::select_mid()) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, super::templates::select_mid()).unwrap(),
            rax(),
            (if c != 0 {
                v1
            } else {
                v2
            }) as nat,
            code_len(super::templates::select_mid()),
        ),
{
    super::memlemmas::lemma_p2_consts();
    let i1 = x64::Instr::TestRR { sz: x64::Size::W32, a: rdx(), b: rdx() };
    let i2 = x64::Instr::Cmovcc { cc: 4, sz: x64::Size::W64, dst: rax(), src: rcx() };
    super::runseq::lemma_len2(i1, i2);
    assert(super::templates::select_mid() == seq![i1, i2]);
    super::flags::lemma_step_test(cu, s, x64::Size::W32, 2, 2);
    let s1 = x64::step(cu, s, i1).unwrap();
    assert(x64::canonical(s1.rip));
    lemma_wf_from(s, s1);
    assert(x64::rgfi_size(s, x64::Size::W32, 2) == c as int);
    assert(x64::loghead(32, c as int) == c as int);
    assert((c & c) == c) by (bit_vector);
    assert(((c as u64) & (c as u64)) as int == c as int);
    assert(x64::zf_bit() == 6);
    super::flags::lemma_step_cmov64(cu, s1, 4, 0, 1);
    let s2 = x64::step(cu, s1, i2).unwrap();
    let f = super::runseq::stepper(cu);
    super::runseq::lemma_gen2(f, s, i1, i2, s1, s2);
    super::runseq::lemma_run_seq_is_gen(cu, s, seq![i1, i2]);
}

/// A constant's load puts its word in `rax`.
pub proof fn lemma_mid_const(cu: spec_fn(nat) -> nat, s: x64::State, v: lir::Val)
    requires
        x64::wf(s),
        x64::canonical(s.rip + code_len(seq![super::templates::const_instr(v)])),
    ensures
        run_seq(cu, s, seq![super::templates::const_instr(v)]) is Some,
        super::alu::mid_post(
            s,
            run_seq(cu, s, seq![super::templates::const_instr(v)]).unwrap(),
            rax(),
            lir::val_bits(v),
            code_len(seq![super::templates::const_instr(v)]),
        ),
{
    let i = super::templates::const_instr(v);
    super::runseq::lemma_run_seq_one(cu, s, i);
    super::runseq::lemma_code_len_one(i);
    super::steps::lemma_step_imm(cu, s, i);
}

} // verus!

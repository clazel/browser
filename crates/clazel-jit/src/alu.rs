//! The arithmetic, logic, shift and multiply instructions of the integer
//! templates: what `x64::step` does to the register file, and that the word
//! it leaves in `rax` is the result LIR's operator defines
//! (`lir::ibin32`, `lir::ibin64`).
//!
//! The results are statements about *values*: the 32-bit forms are given
//! zero-extended words (`x as u64`), and they leave a zero-extended word.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What a register-only stretch of a template does, as far as the template's
/// other steps are concerned: `m1` is `m` with scratch registers changed
/// (`rd` now holds the word `w`), the same memory, the context register and
/// stack pointer as they were, `rip` moved on by `len`, and still a state
/// with 16 general and 16 XMM registers.
pub open spec fn mid_post(m: x64::State, m1: x64::State, rd: u8, w: nat, len: nat) -> bool {
    m1.rgf.len() == 16 && m1.xmm.len() == 16 && m1.rgf[rd as int] as nat == w && m1.rgf[15]
        == m.rgf[15] && m1.rgf[4] == m.rgf[4] && m1.mem == m.mem && m1.rip == m.rip + len
}

/// `write_user_rflags` changes only the flags and the undefined-value seed.
pub proof fn lemma_wur_frame(cu: spec_fn(nat) -> nat, s: x64::State, vec: u32, mask: u32)
    ensures
        ({
            let t = x64::write_user_rflags(cu, s, vec, mask);
            t.rgf == s.rgf && t.mem == s.mem && t.xmm == s.xmm && t.rip == s.rip
        }),
{
}

/// A two-operand arithmetic or logic instruction (not `cmp`) writes the
/// destination register with the result of the operation, changes the flags,
/// and nothing else.
pub proof fn lemma_step_alu_rr(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    alu: x64::AluOp,
    sz: x64::Size,
    dst: u8,
    src: u8,
)
    requires
        x64::wf(m),
        dst < 16,
        src < 16,
        !(alu is Cmp),
        x64::canonical(
            m.rip + x64::instr_len(x64::Instr::AluRR { alu: alu, sz: sz, dst: dst, src: src }),
        ),
    ensures
        x64::step(cu, m, x64::Instr::AluRR { alu: alu, sz: sz, dst: dst, src: src }) is Some,
        ({
            let m1 = x64::step(
                cu,
                m,
                x64::Instr::AluRR { alu: alu, sz: sz, dst: dst, src: src },
            ).unwrap();
            let r = x64::gpr_arith_logic_spec(
                x64::nbits(sz),
                alu,
                x64::rgfi_size(m, sz, dst),
                x64::rgfi_size(m, sz, src),
                m.rflags,
            );
            m1.rgf == x64::set_rgfi_size(m, sz, dst, r.result).rgf && m1.mem == m.mem && m1.xmm
                == m.xmm && m1.rip == m.rip + x64::instr_len(
                x64::Instr::AluRR { alu: alu, sz: sz, dst: dst, src: src },
            )
        }),
{
    let i = x64::Instr::AluRR { alu: alu, sz: sz, dst: dst, src: src };
    let r = x64::gpr_arith_logic_spec(
        x64::nbits(sz),
        alu,
        x64::rgfi_size(m, sz, dst),
        x64::rgfi_size(m, sz, src),
        m.rflags,
    );
    let s1 = x64::set_rgfi_size(m, sz, dst, r.result);
    lemma_wur_frame(cu, s1, r.rflags, r.undef);
}

/// `imul dst, src` writes the destination register and the flags.
pub proof fn lemma_step_imul_rr(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    sz: x64::Size,
    dst: u8,
    src: u8,
)
    requires
        x64::wf(m),
        dst < 16,
        src < 16,
        x64::canonical(
            m.rip + x64::instr_len(x64::Instr::ImulRR { sz: sz, dst: dst, src: src }),
        ),
    ensures
        x64::step(cu, m, x64::Instr::ImulRR { sz: sz, dst: dst, src: src }) is Some,
        ({
            let m1 = x64::step(cu, m, x64::Instr::ImulRR { sz: sz, dst: dst, src: src }).unwrap();
            let (low, cf) = x64::imul_spec(
                x64::nbits(sz),
                x64::rgfi_size(m, sz, src),
                x64::rgfi_size(m, sz, dst),
            );
            m1.rgf == x64::set_rgfi_size(m, sz, dst, low).rgf && m1.mem == m.mem && m1.xmm
                == m.xmm && m1.rip == m.rip + x64::instr_len(
                x64::Instr::ImulRR { sz: sz, dst: dst, src: src },
            )
        }),
{
    let (low, cf) = x64::imul_spec(
        x64::nbits(sz),
        x64::rgfi_size(m, sz, src),
        x64::rgfi_size(m, sz, dst),
    );
    let s1 = x64::set_rgfi_size(m, sz, dst, low);
    // imul_flags is write_user_rflags on s1
    lemma_wur_frame(
        cu,
        s1,
        x64::change_rflags(
            m.rflags,
            x64::FlagUpd {
                cf: Some(cf),
                pf: None,
                af: None,
                zf: None,
                sf: None,
                of: Some(cf),
            },
        ),
        x64::mask_pf() | x64::mask_af() | x64::mask_zf() | x64::mask_sf(),
    );
}

/// `shl/shr/sar r, cl` writes the register and the flags.
pub proof fn lemma_step_shift_cl(
    cu: spec_fn(nat) -> nat,
    m: x64::State,
    sh: x64::ShiftOp,
    sz: x64::Size,
    r: u8,
)
    requires
        x64::wf(m),
        r < 16,
        x64::canonical(m.rip + x64::instr_len(x64::Instr::ShiftCl { shift: sh, sz: sz, r: r })),
    ensures
        x64::step(cu, m, x64::Instr::ShiftCl { shift: sh, sz: sz, r: r }) is Some,
        ({
            let m1 = x64::step(cu, m, x64::Instr::ShiftCl { shift: sh, sz: sz, r: r }).unwrap();
            let cnt = x64::shift_count(sz, x64::loghead(8, x64::rr64(m, 1)));
            let o = x64::shift_spec(sh, x64::nbits(sz), x64::rgfi_size(m, sz, r), cnt, m.rflags);
            m1.rgf == x64::set_rgfi_size(m, sz, r, o.result).rgf && m1.mem == m.mem && m1.xmm
                == m.xmm && m1.rip == m.rip + x64::instr_len(
                x64::Instr::ShiftCl { shift: sh, sz: sz, r: r },
            )
        }),
{
    let cnt = x64::shift_count(sz, x64::loghead(8, x64::rr64(m, 1)));
    let o = x64::shift_spec(sh, x64::nbits(sz), x64::rgfi_size(m, sz, r), cnt, m.rflags);
    let s1 = x64::write_user_rflags(cu, m, o.rflags, o.undef);
    lemma_wur_frame(cu, m, o.rflags, o.undef);
    let s2 = x64::set_rgfi_size(s1, sz, r, o.result);
    assert(s1.rgf == m.rgf);
    assert(x64::set_rgfi_size(s1, sz, r, o.result).rgf == x64::set_rgfi_size(
        m,
        sz,
        r,
        o.result,
    ).rgf);
}

// ----------------------------------------------------------------------------
// Values: 32-bit
// ----------------------------------------------------------------------------

/// `add`, `sub`, `and`, `or`, `xor` on 32-bit operands compute LIR's result.
pub proof fn lemma_val32_alu(o: lir::IBin, x: u32, y: u32, fl: u32)
    requires
        super::templates::alu_of(o) is Some,
    ensures
        x64::gpr_arith_logic_spec(32, super::templates::alu_of(o).unwrap(), x as int, y as int, fl).result
            == lir::ibin32(o, x, y) as int,
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    assert(x64::loghead(32, x as int) == x as int);
    assert(x64::loghead(32, y as int) == y as int);
    match o {
        lir::IBin::Add => {
            assert(lir::ibin32(o, x, y) as int == (x as int + y as int) % 0x1_0000_0000);
        },
        lir::IBin::Sub => {
            assert(lir::ibin32(o, x, y) as int == (x as int - y as int) % 0x1_0000_0000);
            let a = x64::logext(32, x as int);
            let b = x64::logext(32, y as int);
            assert((a - b) % 0x1_0000_0000 == (x as int - y as int) % 0x1_0000_0000);
        },
        lir::IBin::And => {
            assert((x as u64) & (y as u64) == (x & y) as u64) by (bit_vector);
        },
        lir::IBin::Or => {
            assert((x as u64) | (y as u64) == (x | y) as u64) by (bit_vector);
        },
        lir::IBin::Xor => {
            assert((x as u64) ^ (y as u64) == (x ^ y) as u64) by (bit_vector);
        },
        _ => {},
    }
}

/// `add`, `sub`, `and`, `or`, `xor` on 64-bit operands compute LIR's result.
pub proof fn lemma_val64_alu(o: lir::IBin, x: u64, y: u64, fl: u32)
    requires
        super::templates::alu_of(o) is Some,
    ensures
        x64::gpr_arith_logic_spec(64, super::templates::alu_of(o).unwrap(), x as int, y as int, fl).result
            == lir::ibin64(o, x, y) as int,
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    assert(x64::loghead(64, x as int) == x as int);
    assert(x64::loghead(64, y as int) == y as int);
    match o {
        lir::IBin::Add => {
            assert(lir::ibin64(o, x, y) as int == (x as int + y as int) % 0x1_0000_0000_0000_0000);
        },
        lir::IBin::Sub => {
            assert(lir::ibin64(o, x, y) as int == (x as int - y as int)
                % 0x1_0000_0000_0000_0000);
            let a = x64::logext(64, x as int);
            let b = x64::logext(64, y as int);
            assert((a - b) % 0x1_0000_0000_0000_0000 == (x as int - y as int)
                % 0x1_0000_0000_0000_0000);
        },
        lir::IBin::And => {
            assert((x as u64) & (y as u64) == (x & y) as u64) by (bit_vector);
        },
        lir::IBin::Or => {
            assert((x as u64) | (y as u64) == (x | y) as u64) by (bit_vector);
        },
        lir::IBin::Xor => {
            assert((x as u64) ^ (y as u64) == (x ^ y) as u64) by (bit_vector);
        },
        _ => {},
    }
}

/// `imul` on 32-bit operands is LIR's `mul`: the low 32 bits of the product.
pub proof fn lemma_val32_mul(x: u32, y: u32)
    ensures
        x64::imul_spec(32, y as int, x as int).0 == lir::ibin32(lir::IBin::Mul, x, y) as int,
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    let m: int = 0x1_0000_0000;
    let a = x64::logext(32, x as int);
    let b = x64::logext(32, y as int);
    assert(x64::loghead(32, x as int) == x as int);
    assert(x64::loghead(32, y as int) == y as int);
    assert(a % m == x as int % m);
    assert(b % m == y as int % m);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop(a, b, m);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop(x as int, y as int, m);
    vstd::arithmetic::div_mod::lemma_mod_mod(a * b, m, m);
    assert(x64::p2(64) == m * m);
    assert(lir::ibin32(lir::IBin::Mul, x, y) as int == (x as int * y as int) % m);
}

/// `imul` on 64-bit operands is LIR's `mul`: the low 64 bits of the product.
pub proof fn lemma_val64_mul(x: u64, y: u64)
    ensures
        x64::imul_spec(64, y as int, x as int).0 == lir::ibin64(lir::IBin::Mul, x, y) as int,
{
    super::memlemmas::lemma_p2_consts();
    let m: int = 0x1_0000_0000_0000_0000;
    let a = x64::logext(64, x as int);
    let b = x64::logext(64, y as int);
    assert(x64::loghead(64, x as int) == x as int);
    assert(x64::loghead(64, y as int) == y as int);
    assert(a % m == x as int % m);
    assert(b % m == y as int % m);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop(a, b, m);
    vstd::arithmetic::div_mod::lemma_mul_mod_noop(x as int, y as int, m);
    vstd::arithmetic::power2::lemma_pow2_adds(64, 64);
    vstd::arithmetic::power2::lemma2_to64();
    assert(x64::p2(128) == m * m);
    vstd::arithmetic::div_mod::lemma_mod_mod(a * b, m, m);
    assert(lir::ibin64(lir::IBin::Mul, x, y) as int == (x as int * y as int) % m);
}

/// `shl`, `shr` and `sar` by `cl` on 32-bit operands compute LIR's shift: the
/// count is the low bits of `cl`, which is the count modulo the width.
pub proof fn lemma_val32_shift(o: lir::IBin, x: u32, y: u32, fl: u32)
    requires
        super::templates::shift_of(o) is Some,
    ensures
        ({
            let cnt = x64::shift_count(
                x64::Size::W32,
                x64::loghead(8, y as int),
            );
            x64::shift_spec(super::templates::shift_of(o).unwrap(), 32, x as int, cnt, fl).result == lir::ibin32(o, x, y) as int
        }),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    assert(x64::p2(5) == 32 && x64::p2(6) == 64 && x64::p2(8) == 256);
    let yi = y as int;
    let cnt = x64::shift_count(x64::Size::W32, x64::loghead(8, yi));
    let k: nat = (yi % 32) as nat;
    assert(cnt == yi % 32);
    assert(x64::loghead(32, x as int) == x as int);
    assert(x64::loghead(6, cnt) == cnt);
    assert(cnt == k as int);
    let p = x64::p2(k);
    vstd::arithmetic::power2::lemma_pow2_pos(k);
    assert(p == lir::pow2(k) as int);
    assert(p > 0);
    match o {
        lir::IBin::Shl => {
            assert(lir::ibin32(o, x, y) as int == (x as int * p) % 0x1_0000_0000);
        },
        lir::IBin::ShrU => {
            assert(x as int / p <= x as int) by (nonlinear_arith)
                requires
                    p >= 1,
                    x as int >= 0,
            ;
            assert(0 <= x as int / p) by (nonlinear_arith)
                requires
                    p >= 1,
                    x as int >= 0,
            ;
            assert(lir::ibin32(o, x, y) as int == x as int / p);
        },
        lir::IBin::ShrS => {
            let sg = lir::signed_of(32, x as int);
            assert(x64::bit(x as int, 31) == (x as int / 0x8000_0000) % 2);
            if x as int >= 0x8000_0000 {
                assert(x64::logext(32, x as int) == x as int - 0x1_0000_0000);
                assert(sg == x as int - 0x1_0000_0000);
            } else {
                assert(x64::logext(32, x as int) == x as int);
                assert(sg == x as int);
                assert(x as int / p <= x as int) by (nonlinear_arith)
                    requires
                        p >= 1,
                        x as int >= 0,
                ;
                assert(0 <= x as int / p) by (nonlinear_arith)
                    requires
                        p >= 1,
                        x as int >= 0,
                ;
            }
            assert(lir::ibin32(o, x, y) as int == (sg / p) % 0x1_0000_0000);
        },
        _ => {},
    }
}

/// `shl`, `shr` and `sar` by `cl` on 64-bit operands compute LIR's shift: the
/// count is the low bits of `cl`, which is the count modulo the width.
#[verifier::rlimit(100)]
pub proof fn lemma_val64_shift(o: lir::IBin, x: u64, y: u64, fl: u32)
    requires
        super::templates::shift_of(o) is Some,
    ensures
        ({
            let cnt = x64::shift_count(
                x64::Size::W64,
                x64::loghead(8, y as int),
            );
            x64::shift_spec(super::templates::shift_of(o).unwrap(), 64, x as int, cnt, fl).result == lir::ibin64(o, x, y) as int
        }),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::power2::lemma2_to64();
    assert(x64::p2(5) == 32 && x64::p2(6) == 64 && x64::p2(8) == 256);
    let yi = y as int;
    let cnt = x64::shift_count(x64::Size::W64, x64::loghead(8, yi));
    let k: nat = (yi % 64) as nat;
    assert(cnt == yi % 64);
    assert(x64::loghead(64, x as int) == x as int);
    assert(x64::loghead(6, cnt) == cnt);
    assert(cnt == k as int);
    let p = x64::p2(k);
    vstd::arithmetic::power2::lemma_pow2_pos(k);
    assert(p == lir::pow2(k) as int);
    assert(p > 0);
    match o {
        lir::IBin::Shl => {
            assert(lir::ibin64(o, x, y) as int == (x as int * p) % 0x1_0000_0000_0000_0000);
        },
        lir::IBin::ShrU => {
            assert(x as int / p <= x as int) by (nonlinear_arith)
                requires
                    p >= 1,
                    x as int >= 0,
            ;
            assert(0 <= x as int / p) by (nonlinear_arith)
                requires
                    p >= 1,
                    x as int >= 0,
            ;
            assert(lir::ibin64(o, x, y) as int == x as int / p);
        },
        lir::IBin::ShrS => {
            let sg = lir::signed_of(64, x as int);
            assert(x64::bit(x as int, 63) == (x as int / 0x8000_0000_0000_0000) % 2);
            if x as int >= 0x8000_0000_0000_0000 {
                assert(x64::logext(64, x as int) == x as int - 0x1_0000_0000_0000_0000);
                assert(sg == x as int - 0x1_0000_0000_0000_0000);
            } else {
                assert(x64::logext(64, x as int) == x as int);
                assert(sg == x as int);
                assert(x as int / p <= x as int) by (nonlinear_arith)
                    requires
                        p >= 1,
                        x as int >= 0,
                ;
                assert(0 <= x as int / p) by (nonlinear_arith)
                    requires
                        p >= 1,
                        x as int >= 0,
                ;
            }
            assert(lir::ibin64(o, x, y) as int == (sg / p) % 0x1_0000_0000_0000_0000);
        },
        _ => {},
    }
}

} // verus!

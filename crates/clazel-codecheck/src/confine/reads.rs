//! **Reads are confined**: the part of the x86-64 confinement proof that says
//! a step's outcome depends only on the bytes of the read area. `effect`
//! reads memory only through [`read_mem`] at the operand's address (or
//! decides a fault by whether the bytes of a store are mapped); the lemmas
//! below, one per instruction, show that two memories that agree on those
//! bytes give the same outcome. [`lemma_reads_confined`] puts them together
//! with the access facts of the invariant.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A write is possible in `m2` if and only if it is in `m`, if they agree on
/// which of its bytes are mapped.
pub proof fn lemma_write_mem_some_same(m: Map<int, u8>, m2: Map<int, u8>, a: int, n: nat, v: int)
    requires
        same_on(m, m2, a, n as int),
    ensures
        write_mem(m2, a, n, v) is Some == write_mem(m, a, n, v) is Some,
    decreases n,
{
    if n > 0 {
        assert(a <= a < a + n);
        assert forall|x: int| a + 1 <= x < a + 1 + (n - 1) implies (#[trigger] m2.dom().contains(x)
            == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
            assert(a <= x < a + n);
        }
        lemma_write_mem_some_same(m, m2, a + 1, (n - 1) as nat, v / 256);
    }
}

/// The claim about one instruction's `effect`: from a memory `m2` that agrees
/// with the state's on the bytes of its access, the outcome is the same apart
/// from memory.
pub open spec fn read_claim(cu: spec_fn(nat) -> nat, s: State, i: Instr, m2: Map<int, u8>) -> bool {
    (match mem_access(i) {
        Some(a) => same_on(s.mem, m2, eff_addr(s, a.mem), a.size),
        None => true,
    }) ==> same_outcome(effect(cu, s, i), effect(cu, State { mem: m2, ..s }, i))
}

/// `effect` of `MovRR` obeys [`read_claim`].
pub proof fn lemma_er_mov_r_r(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::MovRR { sz, dst, src }, m2),
{
}

/// `effect` of `MovLoad` obeys [`read_claim`].
pub proof fn lemma_er_mov_load(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, dst: u8, mem: Mem)
    ensures
        read_claim(cu, s, Instr::MovLoad { sz, dst, mem }, m2),
{
    let a = eff_addr(s, mem);
    assert(eff_addr(State { mem: m2, ..s }, mem) == a);
    if same_on(s.mem, m2, a, nbytes(sz) as int) {
        lemma_read_mem_same(s.mem, m2, a, nbytes(sz));
    }
}

/// `effect` of `MovStore` obeys [`read_claim`].
pub proof fn lemma_er_mov_store(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, mem: Mem, src: u8)
    ensures
        read_claim(cu, s, Instr::MovStore { sz, mem, src }, m2),
{
    let a = eff_addr(s, mem);
    assert(eff_addr(State { mem: m2, ..s }, mem) == a);
    if same_on(s.mem, m2, a, nbytes(sz) as int) {
        lemma_write_mem_some_same(s.mem, m2, a, nbytes(sz), rgfi_size(s, sz, src));
    }
}

/// `effect` of `MovImm32` obeys [`read_claim`].
pub proof fn lemma_er_mov_imm32(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, dst: u8, imm_u32: u32)
    ensures
        read_claim(cu, s, Instr::MovImm32 { dst, imm_u32 }, m2),
{
}

/// `effect` of `MovImm32S` obeys [`read_claim`].
pub proof fn lemma_er_mov_imm32_s(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, dst: u8, imm: i32)
    ensures
        read_claim(cu, s, Instr::MovImm32S { dst, imm }, m2),
{
}

/// `effect` of `MovImm64` obeys [`read_claim`].
pub proof fn lemma_er_mov_imm64(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, dst: u8, imm_u64: u64)
    ensures
        read_claim(cu, s, Instr::MovImm64 { dst, imm_u64 }, m2),
{
}

/// `effect` of `AluRR` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_alu_r_r(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, alu: AluOp, sz: Size, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::AluRR { alu, sz, dst, src }, m2),
{
    let s2 = State { mem: m2, ..s };
    assert(rgfi_size(s2, sz, dst) == rgfi_size(s, sz, dst));
    assert(rgfi_size(s2, sz, src) == rgfi_size(s, sz, src));
    assert(s2.rflags == s.rflags);
}

/// `effect` of `AluRM` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_alu_r_m(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, alu: AluOp, sz: Size, dst: u8, mem: Mem)
    ensures
        read_claim(cu, s, Instr::AluRM { alu, sz, dst, mem }, m2),
{
    let s2 = State { mem: m2, ..s };
    assert(rgfi_size(s2, sz, dst) == rgfi_size(s, sz, dst));
    assert(s2.rflags == s.rflags);
    let a = eff_addr(s, mem);
    assert(eff_addr(State { mem: m2, ..s }, mem) == a);
    if same_on(s.mem, m2, a, nbytes(sz) as int) {
        lemma_read_mem_same(s.mem, m2, a, nbytes(sz));
    }
}

/// `effect` of `AluRI` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_alu_r_i(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, alu: AluOp, sz: Size, dst: u8, imm: i32)
    ensures
        read_claim(cu, s, Instr::AluRI { alu, sz, dst, imm }, m2),
{
    let s2 = State { mem: m2, ..s };
    assert(rgfi_size(s2, sz, dst) == rgfi_size(s, sz, dst));
    assert(s2.rflags == s.rflags);
}

/// `effect` of `TestRR` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_test_r_r(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, a: u8, b: u8)
    ensures
        read_claim(cu, s, Instr::TestRR { sz, a, b }, m2),
{
    let s2 = State { mem: m2, ..s };
    assert(rgfi_size(s2, sz, a) == rgfi_size(s, sz, a));
    assert(rgfi_size(s2, sz, b) == rgfi_size(s, sz, b));
    assert(s2.rflags == s.rflags);
}

/// `effect` of `TestRI` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_test_r_i(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, a: u8, imm: i32)
    ensures
        read_claim(cu, s, Instr::TestRI { sz, a, imm }, m2),
{
}

/// `effect` of `Neg` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_neg(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, r: u8)
    ensures
        read_claim(cu, s, Instr::Neg { sz, r }, m2),
{
}

/// `effect` of `Not` obeys [`read_claim`].
pub proof fn lemma_er_not(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, r: u8)
    ensures
        read_claim(cu, s, Instr::Not { sz, r }, m2),
{
}

/// `effect` of `ShiftImm` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_shift_imm(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, shift: ShiftOp, sz: Size, r: u8, count: u8)
    ensures
        read_claim(cu, s, Instr::ShiftImm { shift, sz, r, count }, m2),
{
}

/// `effect` of `ShiftCl` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_shift_cl(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, shift: ShiftOp, sz: Size, r: u8)
    ensures
        read_claim(cu, s, Instr::ShiftCl { shift, sz, r }, m2),
{
}

/// `effect` of `ImulRR` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_imul_r_r(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::ImulRR { sz, dst, src }, m2),
{
}

/// `effect` of `ImulRRI` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_imul_r_r_i(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, dst: u8, src: u8, imm: i32)
    ensures
        read_claim(cu, s, Instr::ImulRRI { sz, dst, src, imm }, m2),
{
}

/// `effect` of `Jcc` obeys [`read_claim`].
pub proof fn lemma_er_jcc(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, cc: u8, rel: i32)
    ensures
        read_claim(cu, s, Instr::Jcc { cc, rel }, m2),
{
}

/// `effect` of `Jmp` obeys [`read_claim`].
pub proof fn lemma_er_jmp(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, rel: i32)
    ensures
        read_claim(cu, s, Instr::Jmp { rel }, m2),
{
}

/// `effect` of `Ret` obeys [`read_claim`].
pub proof fn lemma_er_ret(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>)
    ensures
        read_claim(cu, s, Instr::Ret, m2),
{
}

/// `effect` of `Cmovcc` obeys [`read_claim`].
pub proof fn lemma_er_cmovcc(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, cc: u8, sz: Size, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::Cmovcc { cc, sz, dst, src }, m2),
{
}

/// `effect` of `Setcc` obeys [`read_claim`].
pub proof fn lemma_er_setcc(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, cc: u8, dst: u8)
    ensures
        read_claim(cu, s, Instr::Setcc { cc, dst }, m2),
{
}

/// `effect` of `FpArith` obeys [`read_claim`].
pub proof fn lemma_er_fp_arith(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, fop: BinOp, dst: u8, xsrc: XmmSrc)
    ensures
        read_claim(cu, s, Instr::FpArith { fop, dst, xsrc }, m2),
{
    match xsrc {
        XmmSrc::Mem(mm) => {
            let a = eff_addr(s, mm);
            assert(eff_addr(State { mem: m2, ..s }, mm) == a);
            if same_on(s.mem, m2, a, 8) {
                lemma_read_mem_same(s.mem, m2, a, 8);
            }
        },
        XmmSrc::Reg(_) => {},
    }
}

/// `effect` of `Sqrtsd` obeys [`read_claim`].
pub proof fn lemma_er_sqrtsd(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, dst: u8, xsrc: XmmSrc)
    ensures
        read_claim(cu, s, Instr::Sqrtsd { dst, xsrc }, m2),
{
    match xsrc {
        XmmSrc::Mem(mm) => {
            let a = eff_addr(s, mm);
            assert(eff_addr(State { mem: m2, ..s }, mm) == a);
            if same_on(s.mem, m2, a, 8) {
                lemma_read_mem_same(s.mem, m2, a, 8);
            }
        },
        XmmSrc::Reg(_) => {},
    }
}

/// `effect` of `Ucomisd` obeys [`read_claim`].
#[verifier::rlimit(2000)]
pub proof fn lemma_er_ucomisd(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, a: u8, xsrc: XmmSrc)
    ensures
        read_claim(cu, s, Instr::Ucomisd { a, xsrc }, m2),
{
    match xsrc {
        XmmSrc::Mem(mm) => {
            let a = eff_addr(s, mm);
            assert(eff_addr(State { mem: m2, ..s }, mm) == a);
            if same_on(s.mem, m2, a, 8) {
                lemma_read_mem_same(s.mem, m2, a, 8);
            }
        },
        XmmSrc::Reg(_) => {},
    }
}

/// `effect` of `Cvtsi2sd` obeys [`read_claim`].
pub proof fn lemma_er_cvtsi2sd(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::Cvtsi2sd { sz, dst, src }, m2),
{
}

/// `effect` of `Cvttsd2si` obeys [`read_claim`].
pub proof fn lemma_er_cvttsd2si(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::Cvttsd2si { sz, dst, src }, m2),
{
}

/// `effect` of `Cvtsd2si` obeys [`read_claim`].
pub proof fn lemma_er_cvtsd2si(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, sz: Size, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::Cvtsd2si { sz, dst, src }, m2),
{
}

/// `effect` of `MovqToXmm` obeys [`read_claim`].
pub proof fn lemma_er_movq_to_xmm(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::MovqToXmm { dst, src }, m2),
{
}

/// `effect` of `MovqFromXmm` obeys [`read_claim`].
pub proof fn lemma_er_movq_from_xmm(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, dst: u8, src: u8)
    ensures
        read_claim(cu, s, Instr::MovqFromXmm { dst, src }, m2),
{
}

/// `effect` of `MovsdLoad` obeys [`read_claim`].
pub proof fn lemma_er_movsd_load(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, dst: u8, mem: Mem)
    ensures
        read_claim(cu, s, Instr::MovsdLoad { dst, mem }, m2),
{
    let a = eff_addr(s, mem);
    assert(eff_addr(State { mem: m2, ..s }, mem) == a);
    if same_on(s.mem, m2, a, 8) {
        lemma_read_mem_same(s.mem, m2, a, 8);
    }
}

/// `effect` of `MovsdStore` obeys [`read_claim`].
pub proof fn lemma_er_movsd_store(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, mem: Mem, src: u8)
    ensures
        read_claim(cu, s, Instr::MovsdStore { mem, src }, m2),
{
    let a = eff_addr(s, mem);
    assert(eff_addr(State { mem: m2, ..s }, mem) == a);
    if same_on(s.mem, m2, a, 8) {
        lemma_write_mem_some_same(s.mem, m2, a, 8, xmmi_size8(s, src));
    }
}

/// **`effect` reads only the bytes of its access.**
pub proof fn lemma_effect_reads(cu: spec_fn(nat) -> nat, s: State, m2: Map<int, u8>, i: Instr)
    ensures
        read_claim(cu, s, i, m2),
{
    match i {
        Instr::MovRR { sz, dst, src } => lemma_er_mov_r_r(cu, s, m2, sz, dst, src),
        Instr::MovLoad { sz, dst, mem } => lemma_er_mov_load(cu, s, m2, sz, dst, mem),
        Instr::MovStore { sz, mem, src } => lemma_er_mov_store(cu, s, m2, sz, mem, src),
        Instr::MovImm32 { dst, imm_u32 } => lemma_er_mov_imm32(cu, s, m2, dst, imm_u32),
        Instr::MovImm32S { dst, imm } => lemma_er_mov_imm32_s(cu, s, m2, dst, imm),
        Instr::MovImm64 { dst, imm_u64 } => lemma_er_mov_imm64(cu, s, m2, dst, imm_u64),
        Instr::AluRR { alu, sz, dst, src } => lemma_er_alu_r_r(cu, s, m2, alu, sz, dst, src),
        Instr::AluRM { alu, sz, dst, mem } => lemma_er_alu_r_m(cu, s, m2, alu, sz, dst, mem),
        Instr::AluRI { alu, sz, dst, imm } => lemma_er_alu_r_i(cu, s, m2, alu, sz, dst, imm),
        Instr::TestRR { sz, a, b } => lemma_er_test_r_r(cu, s, m2, sz, a, b),
        Instr::TestRI { sz, a, imm } => lemma_er_test_r_i(cu, s, m2, sz, a, imm),
        Instr::Neg { sz, r } => lemma_er_neg(cu, s, m2, sz, r),
        Instr::Not { sz, r } => lemma_er_not(cu, s, m2, sz, r),
        Instr::ShiftImm { shift, sz, r, count } => lemma_er_shift_imm(cu, s, m2, shift, sz, r, count),
        Instr::ShiftCl { shift, sz, r } => lemma_er_shift_cl(cu, s, m2, shift, sz, r),
        Instr::ImulRR { sz, dst, src } => lemma_er_imul_r_r(cu, s, m2, sz, dst, src),
        Instr::ImulRRI { sz, dst, src, imm } => lemma_er_imul_r_r_i(cu, s, m2, sz, dst, src, imm),
        Instr::Jcc { cc, rel } => lemma_er_jcc(cu, s, m2, cc, rel),
        Instr::Jmp { rel } => lemma_er_jmp(cu, s, m2, rel),
        Instr::Ret => lemma_er_ret(cu, s, m2),
        Instr::Cmovcc { cc, sz, dst, src } => lemma_er_cmovcc(cu, s, m2, cc, sz, dst, src),
        Instr::Setcc { cc, dst } => lemma_er_setcc(cu, s, m2, cc, dst),
        Instr::FpArith { fop, dst, xsrc } => lemma_er_fp_arith(cu, s, m2, fop, dst, xsrc),
        Instr::Sqrtsd { dst, xsrc } => lemma_er_sqrtsd(cu, s, m2, dst, xsrc),
        Instr::Ucomisd { a, xsrc } => lemma_er_ucomisd(cu, s, m2, a, xsrc),
        Instr::Cvtsi2sd { sz, dst, src } => lemma_er_cvtsi2sd(cu, s, m2, sz, dst, src),
        Instr::Cvttsd2si { sz, dst, src } => lemma_er_cvttsd2si(cu, s, m2, sz, dst, src),
        Instr::Cvtsd2si { sz, dst, src } => lemma_er_cvtsd2si(cu, s, m2, sz, dst, src),
        Instr::MovqToXmm { dst, src } => lemma_er_movq_to_xmm(cu, s, m2, dst, src),
        Instr::MovqFromXmm { dst, src } => lemma_er_movq_from_xmm(cu, s, m2, dst, src),
        Instr::MovsdLoad { dst, mem } => lemma_er_movsd_load(cu, s, m2, dst, mem),
        Instr::MovsdStore { mem, src } => lemma_er_movsd_store(cu, s, m2, mem, src),
    }
}

/// Agreement on the read area, at one byte of it.
pub proof fn lemma_agree_at(c: Cfg, m: Map<int, u8>, m2: Map<int, u8>, x: int)
    requires
        agree_on_read_area(c, m, m2),
        read_area(c, x),
    ensures
        m2.dom().contains(x) == m.dom().contains(x),
        m.dom().contains(x) ==> m2[x] == m[x],
{
    assert(read_area(c, x) ==> (m2.dom().contains(x) == m.dom().contains(x) && (m.dom().contains(
        x,
    ) ==> m2[x] == m[x])));
}

/// Bytes of a readable range are in the read area, so memories that agree on
/// the read area agree on the range.
pub proof fn lemma_range_agree(c: Cfg, m: Map<int, u8>, m2: Map<int, u8>, addr: int, size: int)
    requires
        agree_on_read_area(c, m, m2),
        readable(c, addr, size),
    ensures
        same_on(m, m2, addr, size),
{
    assert forall|x: int| addr <= x < addr + size implies (#[trigger] m2.dom().contains(x)
        == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
        assert(readable(c, x, 1)) by {
            if c.ctx <= addr && addr + size <= c.ctx + abi::ctx_size() {
            } else {
                assert(in_region(c, addr, size));
                let k = choose|k: int|
                    0 <= k < abi::num_regions() && c.bases[k] <= addr && addr + size
                        <= c.bases[k] + c.bounds[k];
                assert(0 <= k < abi::num_regions() && c.bases[k] <= x && x + 1 <= c.bases[k]
                    + c.bounds[k]);
            }
        }
        assert(read_area(c, x));
        lemma_agree_at(c, m, m2, x);
    }
}

/// A writable range is readable.
pub proof fn lemma_writable_readable(c: Cfg, addr: int, size: int)
    requires
        writable(c, addr, size),
    ensures
        readable(c, addr, size),
{
}

/// **The step of `i` has the same outcome from every memory that agrees on the
/// read area** (given the access facts of the invariant).
pub proof fn lemma_step_reads(
    c: Cfg,
    cu: spec_fn(nat) -> nat,
    s: State,
    i: Instr,
    m2: Map<int, u8>,
)
    requires
        cfg_ok(c),
        base_inv(c, s),
        acc_ok(c, s, i),
        agree_on_read_area(c, s.mem, m2),
    ensures
        same_outcome(step(cu, s, i), step(cu, State { mem: m2, ..s }, i)),
{
    lemma_base_inv_split(c, s);
    let s2 = State { mem: m2, ..s };
    match mem_access(i) {
        Some(a) => {
            let addr = eff_addr(s, a.mem);
            if a.store {
                lemma_writable_readable(c, addr, a.size);
            }
            lemma_range_agree(c, s.mem, m2, addr, a.size);
        },
        None => {},
    }
    lemma_effect_reads(cu, s, m2, i);
    match i {
        Instr::Jcc { cc, rel } => {},
        Instr::Jmp { rel } => {},
        Instr::Ret => {
            lemma_p2();
            lemma_logext64_id(c.sp);
            assert(logext(64, rr64(s, 4)) == c.sp);
            assert(forall|x: int| c.sp <= x < c.sp + 8 ==> read_area(c, x));
            assert(same_on(s.mem, m2, c.sp, 8)) by {
                assert forall|x: int| c.sp <= x < c.sp + 8 implies (#[trigger] m2.dom().contains(x)
                    == s.mem.dom().contains(x) && (s.mem.dom().contains(x) ==> m2[x] == s.mem[x])) by {
                    assert(read_area(c, x));
                    lemma_agree_at(c, s.mem, m2, x);
                }
            }
            lemma_read_mem_same(s.mem, m2, c.sp, 8);
        },
        _ => {},
    }
}

/// **Reads are confined** ([`reads_confined`]) at a state with the invariant.
pub proof fn lemma_reads_confined(c: Cfg, cu: spec_fn(nat) -> nat, s: State, i: Instr)
    requires
        cfg_ok(c),
        base_inv(c, s),
        acc_ok(c, s, i),
    ensures
        reads_confined(c, cu, s, i),
{
    assert forall|m2: Map<int, u8>| agree_on_read_area(c, s.mem, m2) implies #[trigger] same_outcome(
        step(cu, s, i),
        step(cu, State { mem: m2, ..s }, i),
    ) by {
        lemma_step_reads(c, cu, s, i, m2);
    }
}

} // verus!

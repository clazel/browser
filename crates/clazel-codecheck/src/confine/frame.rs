//! **Frame lemmas of the x86-64 semantics** the confinement proof rests on:
//! what `clazel_x64::spec::effect` and `step` leave alone. A write changes
//! memory only at the bytes of its access (and never the set of mapped
//! bytes); an instruction changes no general register but its destination
//! ([`crate::spec::written_gpr`]); `effect` never moves RIP.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Bytes `[p, p + q)` of `m2` are as in `m`, mapped or not.
pub open spec fn same_on(m: Map<int, u8>, m2: Map<int, u8>, p: int, q: int) -> bool {
    forall|x: int|
        p <= x < p + q ==> (#[trigger] m2.dom().contains(x) == m.dom().contains(x) && (
        m.dom().contains(x) ==> m2[x] == m[x]))
}

/// A successful write maps the same bytes as before, changes only the bytes it
/// writes, and the bytes it writes were mapped.
pub proof fn lemma_write_mem_frame(m: Map<int, u8>, a: int, n: nat, v: int)
    requires
        write_mem(m, a, n, v) is Some,
    ensures
        write_mem(m, a, n, v)->Some_0.dom() =~= m.dom(),
        forall|x: int|
            (x < a || x >= a + n) && m.dom().contains(x) ==> #[trigger] write_mem(
                m,
                a,
                n,
                v,
            )->Some_0[x] == m[x],
        forall|x: int| a <= x < a + n ==> #[trigger] m.dom().contains(x),
    decreases n,
{
    if n > 0 {
        lemma_write_mem_frame(m, a + 1, (n - 1) as nat, v / 256);
        let m1 = write_mem(m, a + 1, (n - 1) as nat, v / 256)->Some_0;
        assert(write_mem(m, a, n, v)->Some_0 == m1.insert(a, (v % 256) as u8));
        assert(m.dom().contains(a));
    }
}

/// A read sees the same if the bytes it reads are the same.
pub proof fn lemma_read_mem_same(m: Map<int, u8>, m2: Map<int, u8>, p: int, q: nat)
    requires
        same_on(m, m2, p, q as int),
    ensures
        read_mem(m2, p, q) == read_mem(m, p, q),
    decreases q,
{
    if q > 0 {
        assert(p <= p < p + q);
        assert(m2.dom().contains(p) == m.dom().contains(p));
        assert forall|x: int| p + 1 <= x < p + 1 + (q - 1) implies (#[trigger] m2.dom().contains(
            x,
        ) == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
            assert(p <= x < p + q);
        }
        lemma_read_mem_same(m, m2, p + 1, (q - 1) as nat);
    }
}

/// A read that succeeds read mapped bytes.
pub proof fn lemma_read_mem_mapped(m: Map<int, u8>, p: int, q: nat)
    requires
        read_mem(m, p, q) is Some,
    ensures
        forall|x: int| p <= x < p + q ==> #[trigger] m.dom().contains(x),
    decreases q,
{
    if q > 0 {
        lemma_read_mem_mapped(m, p + 1, (q - 1) as nat);
    }
}

/// A write to bytes `[a, a + n)` leaves a read of `[p, p + q)` alone if the
/// two ranges do not overlap.
pub proof fn lemma_write_read_disjoint(
    m: Map<int, u8>,
    a: int,
    n: nat,
    v: int,
    p: int,
    q: nat,
)
    requires
        write_mem(m, a, n, v) is Some,
        a + n <= p || p + q <= a,
    ensures
        read_mem(write_mem(m, a, n, v)->Some_0, p, q) == read_mem(m, p, q),
{
    lemma_write_mem_frame(m, a, n, v);
    let m2 = write_mem(m, a, n, v)->Some_0;
    assert forall|x: int| p <= x < p + q implies (#[trigger] m2.dom().contains(x)
        == m.dom().contains(x) && (m.dom().contains(x) ==> m2[x] == m[x])) by {
        assert(x < a || x >= a + n);
    }
    lemma_read_mem_same(m, m2, p, q);
}

/// What `effect` does to the state, other than memory: it writes only the
/// destination general register (if any), never moves RIP, and keeps the
/// register files' lengths.
pub open spec fn effect_regs_frame(s: State, s1: State, d: Option<u8>) -> bool {
    s1.rgf.len() == s.rgf.len() && s1.xmm.len() == s.xmm.len() && s1.rip == s.rip && forall|
        r: int,
    |
        0 <= r < s.rgf.len() && d != Some(r as u8) ==> #[trigger] s1.rgf[r] == s.rgf[r]
}

/// The memory of `s1` after a store of `size` bytes at `addr` is the memory of
/// `s` except at those bytes, and the same bytes are mapped.
pub open spec fn store_frame(s: State, s1: State, addr: int, size: int) -> bool {
    s1.mem.dom() =~= s.mem.dom() && forall|x: int|
        (x < addr || x >= addr + size) && s.mem.dom().contains(x) ==> #[trigger] s1.mem[x]
            == s.mem[x]
}

/// `write_user_rflags` changes only the flags and the undefined seed.
pub proof fn lemma_wur_frame(
    cu: spec_fn(nat) -> nat,
    s: State,
    u: u32,
    mask: u32,
)
    ensures
        ({
            let t = write_user_rflags(cu, s, u, mask);
            t.rgf == s.rgf && t.mem == s.mem && t.xmm == s.xmm && t.rip == s.rip
        }),
{
}

/// The claim [`lemma_effect_frame`] makes about one instruction: if `effect`
/// succeeds, it writes only its destination register (if any), never moves
/// RIP, and leaves memory alone except for the bytes of a store (whose set of
/// mapped bytes is unchanged).
pub open spec fn frame_claim(cu: spec_fn(nat) -> nat, s: State, i: Instr) -> bool {
    effect(cu, s, i) is Some ==> {
        let s1 = effect(cu, s, i)->Some_0;
        effect_regs_frame(s, s1, written_gpr(i)) && match mem_access(i) {
            Some(a) => if a.store {
                store_frame(s, s1, eff_addr(s, a.mem), a.size)
            } else {
                s1.mem == s.mem
            },
            None => s1.mem == s.mem,
        }
    }
}

/// `effect` of `MovRR` obeys [`frame_claim`].
pub proof fn lemma_ef_mov_r_r(cu: spec_fn(nat) -> nat, s: State, sz: Size, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::MovRR { sz, dst, src }),
{
}

/// `effect` of `MovLoad` obeys [`frame_claim`].
pub proof fn lemma_ef_mov_load(cu: spec_fn(nat) -> nat, s: State, sz: Size, dst: u8, mem: Mem)
    ensures
        frame_claim(cu, s, Instr::MovLoad { sz, dst, mem }),
{
}

/// `effect` of `MovStore` obeys [`frame_claim`].
pub proof fn lemma_ef_mov_store(cu: spec_fn(nat) -> nat, s: State, sz: Size, mem: Mem, src: u8)
    ensures
        frame_claim(cu, s, Instr::MovStore { sz, mem, src }),
{
    if write_mem(s.mem, eff_addr(s, mem), nbytes(sz), rgfi_size(s, sz, src)) is Some {
        lemma_write_mem_frame(s.mem, eff_addr(s, mem), nbytes(sz), rgfi_size(s, sz, src));
    }
}

/// `effect` of `MovImm32` obeys [`frame_claim`].
pub proof fn lemma_ef_mov_imm32(cu: spec_fn(nat) -> nat, s: State, dst: u8, imm_u32: u32)
    ensures
        frame_claim(cu, s, Instr::MovImm32 { dst, imm_u32 }),
{
}

/// `effect` of `MovImm32S` obeys [`frame_claim`].
pub proof fn lemma_ef_mov_imm32_s(cu: spec_fn(nat) -> nat, s: State, dst: u8, imm: i32)
    ensures
        frame_claim(cu, s, Instr::MovImm32S { dst, imm }),
{
}

/// `effect` of `MovImm64` obeys [`frame_claim`].
pub proof fn lemma_ef_mov_imm64(cu: spec_fn(nat) -> nat, s: State, dst: u8, imm_u64: u64)
    ensures
        frame_claim(cu, s, Instr::MovImm64 { dst, imm_u64 }),
{
}

/// `effect` of `AluRR` obeys [`frame_claim`].
pub proof fn lemma_ef_alu_r_r(cu: spec_fn(nat) -> nat, s: State, alu: AluOp, sz: Size, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::AluRR { alu, sz, dst, src }),
{
    let r = gpr_arith_logic_spec(
        nbits(sz),
        alu,
        rgfi_size(s, sz, dst),
        rgfi_size(s, sz, src),
        s.rflags,
    );
    let s1 = if alu is Cmp { s } else { set_rgfi_size(s, sz, dst, r.result) };
    lemma_wur_frame(cu, s1, r.rflags, r.undef);
}

/// `effect` of `AluRM` obeys [`frame_claim`].
pub proof fn lemma_ef_alu_r_m(cu: spec_fn(nat) -> nat, s: State, alu: AluOp, sz: Size, dst: u8, mem: Mem)
    ensures
        frame_claim(cu, s, Instr::AluRM { alu, sz, dst, mem }),
{
    let e = read_operand_mem(s, sz, mem)->Some_0;
    let r = gpr_arith_logic_spec(nbits(sz), alu, rgfi_size(s, sz, dst), e, s.rflags);
    let s1 = if alu is Cmp { s } else { set_rgfi_size(s, sz, dst, r.result) };
    lemma_wur_frame(cu, s1, r.rflags, r.undef);
}

/// `effect` of `AluRI` obeys [`frame_claim`].
pub proof fn lemma_ef_alu_r_i(cu: spec_fn(nat) -> nat, s: State, alu: AluOp, sz: Size, dst: u8, imm: i32)
    ensures
        frame_claim(cu, s, Instr::AluRI { alu, sz, dst, imm }),
{
    let r = gpr_arith_logic_spec(
        nbits(sz),
        alu,
        rgfi_size(s, sz, dst),
        loghead(nbits(sz), imm as int),
        s.rflags,
    );
    let s1 = if alu is Cmp { s } else { set_rgfi_size(s, sz, dst, r.result) };
    lemma_wur_frame(cu, s1, r.rflags, r.undef);
}

/// `effect` of `TestRR` obeys [`frame_claim`].
pub proof fn lemma_ef_test_r_r(cu: spec_fn(nat) -> nat, s: State, sz: Size, a: u8, b: u8)
    ensures
        frame_claim(cu, s, Instr::TestRR { sz, a, b }),
{
    let r = gpr_and_spec(nbits(sz), rgfi_size(s, sz, a), rgfi_size(s, sz, b), s.rflags);
    lemma_wur_frame(cu, s, r.rflags, r.undef);
}

/// `effect` of `TestRI` obeys [`frame_claim`].
pub proof fn lemma_ef_test_r_i(cu: spec_fn(nat) -> nat, s: State, sz: Size, a: u8, imm: i32)
    ensures
        frame_claim(cu, s, Instr::TestRI { sz, a, imm }),
{
    let r = gpr_and_spec(
        nbits(sz),
        rgfi_size(s, sz, a),
        loghead(nbits(sz), imm as int),
        s.rflags,
    );
    lemma_wur_frame(cu, s, r.rflags, r.undef);
}

/// `effect` of `Neg` obeys [`frame_claim`].
pub proof fn lemma_ef_neg(cu: spec_fn(nat) -> nat, s: State, sz: Size, r: u8)
    ensures
        frame_claim(cu, s, Instr::Neg { sz, r }),
{
    let v = rgfi_size(s, sz, r);
    let o = gpr_sub_spec(nbits(sz), 0, v, s.rflags);
    let flags = set_bit32(o.rflags, cf_bit(), if v == 0 { 0 } else { 1 });
    lemma_wur_frame(cu, s, flags, o.undef);
}

/// `effect` of `Not` obeys [`frame_claim`].
pub proof fn lemma_ef_not(cu: spec_fn(nat) -> nat, s: State, sz: Size, r: u8)
    ensures
        frame_claim(cu, s, Instr::Not { sz, r }),
{
}

/// `effect` of `ShiftImm` obeys [`frame_claim`].
pub proof fn lemma_ef_shift_imm(cu: spec_fn(nat) -> nat, s: State, shift: ShiftOp, sz: Size, r: u8, count: u8)
    ensures
        frame_claim(cu, s, Instr::ShiftImm { shift, sz, r, count }),
{
    let cnt = shift_count(sz, count as int);
    let o = shift_spec(shift, nbits(sz), rgfi_size(s, sz, r), cnt, s.rflags);
    lemma_wur_frame(cu, s, o.rflags, o.undef);
}

/// `effect` of `ShiftCl` obeys [`frame_claim`].
pub proof fn lemma_ef_shift_cl(cu: spec_fn(nat) -> nat, s: State, shift: ShiftOp, sz: Size, r: u8)
    ensures
        frame_claim(cu, s, Instr::ShiftCl { shift, sz, r }),
{
    let cnt = shift_count(sz, loghead(8, rr64(s, 1)));
    let o = shift_spec(shift, nbits(sz), rgfi_size(s, sz, r), cnt, s.rflags);
    lemma_wur_frame(cu, s, o.rflags, o.undef);
}

/// `effect` of `ImulRR` obeys [`frame_claim`].
pub proof fn lemma_ef_imul_r_r(cu: spec_fn(nat) -> nat, s: State, sz: Size, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::ImulRR { sz, dst, src }),
{
    let (low, cf_and_of) = imul_spec(nbits(sz), rgfi_size(s, sz, src), rgfi_size(s, sz, dst));
    lemma_imul_flags_frame(cu, set_rgfi_size(s, sz, dst, low), cf_and_of);
}

/// `effect` of `ImulRRI` obeys [`frame_claim`].
pub proof fn lemma_ef_imul_r_r_i(cu: spec_fn(nat) -> nat, s: State, sz: Size, dst: u8, src: u8, imm: i32)
    ensures
        frame_claim(cu, s, Instr::ImulRRI { sz, dst, src, imm }),
{
    let (low, cf_and_of) = imul_spec(
        nbits(sz),
        rgfi_size(s, sz, src),
        loghead(nbits(sz), imm as int),
    );
    lemma_imul_flags_frame(cu, set_rgfi_size(s, sz, dst, low), cf_and_of);
}

/// `effect` of `Jcc` obeys [`frame_claim`].
pub proof fn lemma_ef_jcc(cu: spec_fn(nat) -> nat, s: State, cc: u8, rel: i32)
    ensures
        frame_claim(cu, s, Instr::Jcc { cc, rel }),
{
}

/// `effect` of `Jmp` obeys [`frame_claim`].
pub proof fn lemma_ef_jmp(cu: spec_fn(nat) -> nat, s: State, rel: i32)
    ensures
        frame_claim(cu, s, Instr::Jmp { rel }),
{
}

/// `effect` of `Ret` obeys [`frame_claim`].
pub proof fn lemma_ef_ret(cu: spec_fn(nat) -> nat, s: State)
    ensures
        frame_claim(cu, s, Instr::Ret),
{
}

/// `effect` of `Cmovcc` obeys [`frame_claim`].
pub proof fn lemma_ef_cmovcc(cu: spec_fn(nat) -> nat, s: State, cc: u8, sz: Size, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::Cmovcc { cc, sz, dst, src }),
{
}

/// `effect` of `Setcc` obeys [`frame_claim`].
pub proof fn lemma_ef_setcc(cu: spec_fn(nat) -> nat, s: State, cc: u8, dst: u8)
    ensures
        frame_claim(cu, s, Instr::Setcc { cc, dst }),
{
}

/// `effect` of `FpArith` obeys [`frame_claim`].
pub proof fn lemma_ef_fp_arith(cu: spec_fn(nat) -> nat, s: State, fop: BinOp, dst: u8, xsrc: XmmSrc)
    ensures
        frame_claim(cu, s, Instr::FpArith { fop, dst, xsrc }),
{
}

/// `effect` of `Sqrtsd` obeys [`frame_claim`].
pub proof fn lemma_ef_sqrtsd(cu: spec_fn(nat) -> nat, s: State, dst: u8, xsrc: XmmSrc)
    ensures
        frame_claim(cu, s, Instr::Sqrtsd { dst, xsrc }),
{
}

/// `effect` of `Ucomisd` obeys [`frame_claim`].
pub proof fn lemma_ef_ucomisd(cu: spec_fn(nat) -> nat, s: State, a: u8, xsrc: XmmSrc)
    ensures
        frame_claim(cu, s, Instr::Ucomisd { a, xsrc }),
{
    let b = read_xmm_src(s, xsrc)->Some_0;
    let result = dp_sse_cmp_ucomi(xmmi_size8(s, a) as u64, b as u64);
    lemma_ucomi_flags_frame(s, result);
}

/// `effect` of `Cvtsi2sd` obeys [`frame_claim`].
pub proof fn lemma_ef_cvtsi2sd(cu: spec_fn(nat) -> nat, s: State, sz: Size, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::Cvtsi2sd { sz, dst, src }),
{
}

/// `effect` of `Cvttsd2si` obeys [`frame_claim`].
pub proof fn lemma_ef_cvttsd2si(cu: spec_fn(nat) -> nat, s: State, sz: Size, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::Cvttsd2si { sz, dst, src }),
{
}

/// `effect` of `Cvtsd2si` obeys [`frame_claim`].
pub proof fn lemma_ef_cvtsd2si(cu: spec_fn(nat) -> nat, s: State, sz: Size, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::Cvtsd2si { sz, dst, src }),
{
}

/// `effect` of `MovqToXmm` obeys [`frame_claim`].
pub proof fn lemma_ef_movq_to_xmm(cu: spec_fn(nat) -> nat, s: State, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::MovqToXmm { dst, src }),
{
}

/// `effect` of `MovqFromXmm` obeys [`frame_claim`].
pub proof fn lemma_ef_movq_from_xmm(cu: spec_fn(nat) -> nat, s: State, dst: u8, src: u8)
    ensures
        frame_claim(cu, s, Instr::MovqFromXmm { dst, src }),
{
}

/// `effect` of `MovsdLoad` obeys [`frame_claim`].
pub proof fn lemma_ef_movsd_load(cu: spec_fn(nat) -> nat, s: State, dst: u8, mem: Mem)
    ensures
        frame_claim(cu, s, Instr::MovsdLoad { dst, mem }),
{
}

/// `effect` of `MovsdStore` obeys [`frame_claim`].
pub proof fn lemma_ef_movsd_store(cu: spec_fn(nat) -> nat, s: State, mem: Mem, src: u8)
    ensures
        frame_claim(cu, s, Instr::MovsdStore { mem, src }),
{
    if write_mem(s.mem, eff_addr(s, mem), nbytes(Size::W64), xmmi_size8(s, src)) is Some {
        lemma_write_mem_frame(s.mem, eff_addr(s, mem), nbytes(Size::W64), xmmi_size8(s, src));
    }
}

/// **`effect` writes only its destination register and the memory its access
/// names**: see [`frame_claim`].
pub proof fn lemma_effect_frame(cu: spec_fn(nat) -> nat, s: State, i: Instr)
    ensures
        frame_claim(cu, s, i),
{
    match i {
        Instr::MovRR { sz, dst, src } => lemma_ef_mov_r_r(cu, s, sz, dst, src),
        Instr::MovLoad { sz, dst, mem } => lemma_ef_mov_load(cu, s, sz, dst, mem),
        Instr::MovStore { sz, mem, src } => lemma_ef_mov_store(cu, s, sz, mem, src),
        Instr::MovImm32 { dst, imm_u32 } => lemma_ef_mov_imm32(cu, s, dst, imm_u32),
        Instr::MovImm32S { dst, imm } => lemma_ef_mov_imm32_s(cu, s, dst, imm),
        Instr::MovImm64 { dst, imm_u64 } => lemma_ef_mov_imm64(cu, s, dst, imm_u64),
        Instr::AluRR { alu, sz, dst, src } => lemma_ef_alu_r_r(cu, s, alu, sz, dst, src),
        Instr::AluRM { alu, sz, dst, mem } => lemma_ef_alu_r_m(cu, s, alu, sz, dst, mem),
        Instr::AluRI { alu, sz, dst, imm } => lemma_ef_alu_r_i(cu, s, alu, sz, dst, imm),
        Instr::TestRR { sz, a, b } => lemma_ef_test_r_r(cu, s, sz, a, b),
        Instr::TestRI { sz, a, imm } => lemma_ef_test_r_i(cu, s, sz, a, imm),
        Instr::Neg { sz, r } => lemma_ef_neg(cu, s, sz, r),
        Instr::Not { sz, r } => lemma_ef_not(cu, s, sz, r),
        Instr::ShiftImm { shift, sz, r, count } => lemma_ef_shift_imm(cu, s, shift, sz, r, count),
        Instr::ShiftCl { shift, sz, r } => lemma_ef_shift_cl(cu, s, shift, sz, r),
        Instr::ImulRR { sz, dst, src } => lemma_ef_imul_r_r(cu, s, sz, dst, src),
        Instr::ImulRRI { sz, dst, src, imm } => lemma_ef_imul_r_r_i(cu, s, sz, dst, src, imm),
        Instr::Jcc { cc, rel } => lemma_ef_jcc(cu, s, cc, rel),
        Instr::Jmp { rel } => lemma_ef_jmp(cu, s, rel),
        Instr::Ret => lemma_ef_ret(cu, s),
        Instr::Cmovcc { cc, sz, dst, src } => lemma_ef_cmovcc(cu, s, cc, sz, dst, src),
        Instr::Setcc { cc, dst } => lemma_ef_setcc(cu, s, cc, dst),
        Instr::FpArith { fop, dst, xsrc } => lemma_ef_fp_arith(cu, s, fop, dst, xsrc),
        Instr::Sqrtsd { dst, xsrc } => lemma_ef_sqrtsd(cu, s, dst, xsrc),
        Instr::Ucomisd { a, xsrc } => lemma_ef_ucomisd(cu, s, a, xsrc),
        Instr::Cvtsi2sd { sz, dst, src } => lemma_ef_cvtsi2sd(cu, s, sz, dst, src),
        Instr::Cvttsd2si { sz, dst, src } => lemma_ef_cvttsd2si(cu, s, sz, dst, src),
        Instr::Cvtsd2si { sz, dst, src } => lemma_ef_cvtsd2si(cu, s, sz, dst, src),
        Instr::MovqToXmm { dst, src } => lemma_ef_movq_to_xmm(cu, s, dst, src),
        Instr::MovqFromXmm { dst, src } => lemma_ef_movq_from_xmm(cu, s, dst, src),
        Instr::MovsdLoad { dst, mem } => lemma_ef_movsd_load(cu, s, dst, mem),
        Instr::MovsdStore { mem, src } => lemma_ef_movsd_store(cu, s, mem, src),
    }
}

/// `imul_flags` changes only the flags.
pub proof fn lemma_imul_flags_frame(cu: spec_fn(nat) -> nat, s: State, cf_and_of: int)
    ensures
        ({
            let t = imul_flags(cu, s, cf_and_of);
            t.rgf == s.rgf && t.mem == s.mem && t.xmm == s.xmm && t.rip == s.rip
        }),
{
}

/// `ucomi_flags` changes only the flags.
pub proof fn lemma_ucomi_flags_frame(s: State, result: int)
    ensures
        ({
            let t = ucomi_flags(s, result);
            t.rgf == s.rgf && t.mem == s.mem && t.xmm == s.xmm && t.rip == s.rip
        }),
{
}

} // verus!

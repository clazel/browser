//! Frame lemmas for `clazel_x64::spec::step`, used by the safety theorem
//! ([`super::safety`]): what one instruction can change. They say nothing
//! about the validator; they are facts about the machine model.
//!
//! - which general registers a step may write (only [`written_gpr`], and `rsp`
//!   for `ret`);
//! - which memory bytes a step may write (only those of a store's access);
//! - where `rip` goes.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The general registers of `s2` are those of `s`, except possibly `d`.
pub open spec fn gpr_kept(s: State, s2: State, d: Option<u8>) -> bool {
    &&& s2.rgf.len() == s.rgf.len()
    &&& forall|r: u8| r < 16 && s.rgf.len() == 16 && d != Some(r) ==> s2.rgf[r as int] == s.rgf[r as int]
}

/// `s2` differs from `s` at most in the flags (and the undefined-flag seed).
pub open spec fn only_flags(s: State, s2: State) -> bool {
    s2.rgf == s.rgf && s2.mem == s.mem && s2.rip == s.rip && s2.xmm == s.xmm
}

/// The bytes of `m2` are those of `m` outside `[lo, lo + n)`, and the mapped
/// addresses are the same.
pub open spec fn mem_frame(m: Map<int, u8>, m2: Map<int, u8>, lo: int, n: int) -> bool {
    &&& m2.dom() == m.dom()
    &&& forall|a: int|
        #![trigger m2[a]]
        m.dom().contains(a) && !(lo <= a < lo + n) ==> m2[a] == m[a]
}

/// A store changes only the bytes it writes.
pub proof fn lemma_write_mem_frame(m: Map<int, u8>, addr: int, n: nat, v: int, m2: Map<int, u8>)
    requires
        write_mem(m, addr, n, v) == Some(m2),
    ensures
        mem_frame(m, m2, addr, n as int),
    decreases n,
{
    if n > 0 {
        let m3 = write_mem(m, addr + 1, (n - 1) as nat, v / 256)->Some_0;
        lemma_write_mem_frame(m, addr + 1, (n - 1) as nat, v / 256, m3);
        assert(m2 == m3.insert(addr, (v % 256) as u8));
        assert(m2.dom() =~= m.dom());
    } else {
        assert(m2 == m);
    }
}

/// Reading bytes that were not changed gives the same value.
pub proof fn lemma_read_mem_frame(m: Map<int, u8>, m2: Map<int, u8>, a: int, n: nat)
    requires
        forall|i: int| #![trigger m2.dom().contains(a + i)]
            0 <= i < n ==> (m.dom().contains(a + i) == m2.dom().contains(a + i)) && (m.dom().contains(
                a + i,
            ) ==> m2[a + i] == m[a + i]),
    ensures
        read_mem(m2, a, n) == read_mem(m, a, n),
    decreases n,
{
    if n > 0 {
        assert(m.dom().contains(a + 0) == m2.dom().contains(a + 0));
        assert forall|i: int| #![trigger m2.dom().contains(a + 1 + i)]
            0 <= i < n - 1 implies (m.dom().contains(a + 1 + i) == m2.dom().contains(a + 1 + i)) && (
        m.dom().contains(a + 1 + i) ==> m2[a + 1 + i] == m[a + 1 + i]) by {
            assert(0 <= i + 1 < n);
            assert(a + (i + 1) == a + 1 + i);
        }
        lemma_read_mem_frame(m, m2, a + 1, (n - 1) as nat);
    }
}

// ---- Building blocks ----

/// The values of the powers of two up to 2^64.
pub proof fn lemma_p2_vals()
    ensures
        p2(0) == 1,
        p2(8) == 256,
        p2(32) == 0x1_0000_0000,
        p2(63) == 0x8000_0000_0000_0000,
        p2(64) == 0x1_0000_0000_0000_0000,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
}

pub proof fn lemma_wr64(s: State, r: u8, v: int)
    requires
        s.rgf.len() == 16,
        r < 16,
    ensures
        gpr_kept(s, wr64(s, r, v), Some(r)),
        wr64(s, r, v).mem == s.mem,
        wr64(s, r, v).rip == s.rip,
        wr64(s, r, v).rgf[r as int] as int == loghead(64, v),
{
    lemma_p2_vals();
    assert(0 <= loghead(64, v) < p2(64));
}

pub proof fn lemma_set_rgfi(s: State, sz: Size, r: u8, v: int)
    requires
        s.rgf.len() == 16,
        r < 16,
    ensures
        gpr_kept(s, set_rgfi_size(s, sz, r, v), Some(r)),
        set_rgfi_size(s, sz, r, v).mem == s.mem,
        set_rgfi_size(s, sz, r, v).rip == s.rip,
        sz is W64 ==> set_rgfi_size(s, sz, r, v).rgf[r as int] as int == loghead(64, v),
{
    lemma_wr64(s, r, if sz is W32 { loghead(32, v) } else { v });
}

pub proof fn lemma_wr08(s: State, r: u8, v: int)
    requires
        s.rgf.len() == 16,
        r < 16,
    ensures
        gpr_kept(s, wr08(s, r, v), Some(r)),
        wr08(s, r, v).mem == s.mem,
        wr08(s, r, v).rip == s.rip,
{
    lemma_wr64(s, r, rr64(s, r) - rr64(s, r) % 256 + loghead(8, v));
}

/// `write_user_rflags` changes only flags.
pub proof fn lemma_wur(u: spec_fn(nat) -> nat, s: State, a: u32, b: u32)
    ensures
        only_flags(s, write_user_rflags(u, s, a, b)),
{
}

proof fn lemma_xmm8(s: State, x: u8, v: int)
    ensures
        s.rgf == set_xmmi_size8(s, x, v).rgf,
        s.mem == set_xmmi_size8(s, x, v).mem,
        s.rip == set_xmmi_size8(s, x, v).rip,
{
}

proof fn lemma_xmm16(s: State, x: u8, v: int)
    ensures
        s.rgf == set_xmmi_size16(s, x, v).rgf,
        s.mem == set_xmmi_size16(s, x, v).mem,
        s.rip == set_xmmi_size16(s, x, v).rip,
{
}

/// What a store (`store_mem`) does: a `write_mem` at the effective address.
proof fn lemma_store_mem(s: State, m: Mem, sz: Size, v: int, s2: State)
    requires
        store_mem(s, m, sz, v) == Some(s2),
    ensures
        s2.rgf == s.rgf,
        s2.rip == s.rip,
        mem_frame(s.mem, s2.mem, eff_addr(s, m), nbytes(sz) as int),
{
    let m2 = write_mem(s.mem, eff_addr(s, m), nbytes(sz), v)->Some_0;
    lemma_write_mem_frame(s.mem, eff_addr(s, m), nbytes(sz), v, m2);
}

/// **What `effect` can change**: only the register `written_gpr` names, the
/// bytes of a store's access, and nothing of `rip`.
#[verifier::rlimit(400)]
#[verifier::spinoff_prover]
pub proof fn lemma_effect_frame(u: spec_fn(nat) -> nat, s: State, i: Instr, s1: State)
    requires
        valid_instr(i),
        s.rgf.len() == 16,
        effect(u, s, i) == Some(s1),
    ensures
        gpr_kept(s, s1, written_gpr(i)),
        s1.rip == s.rip,
        match mem_access(i) {
            Some(a) => if a.store {
                mem_frame(s.mem, s1.mem, eff_addr(s, a.mem), a.size)
            } else {
                s1.mem == s.mem
            },
            None => s1.mem == s.mem,
        },
{
    match i {
        Instr::MovRR { sz, dst, src } => {
            lemma_set_rgfi(s, sz, dst, rgfi_size(s, sz, src));
        },
        Instr::MovLoad { sz, dst, mem } => {
            let v = read_operand_mem(s, sz, mem)->Some_0;
            lemma_set_rgfi(s, sz, dst, v);
        },
        Instr::MovStore { sz, mem, src } => {
            lemma_store_mem(s, mem, sz, rgfi_size(s, sz, src), s1);
        },
        Instr::MovImm32 { dst, imm_u32 } => {
            lemma_wr64(s, dst, loghead(32, imm_u32 as int));
        },
        Instr::MovImm32S { dst, imm } => {
            lemma_wr64(s, dst, imm as int);
        },
        Instr::MovImm64 { dst, imm_u64 } => {
            lemma_wr64(s, dst, imm_u64 as int);
        },
        Instr::AluRR { alu, sz, dst, src } => {
            let r = gpr_arith_logic_spec(
                nbits(sz),
                alu,
                rgfi_size(s, sz, dst),
                rgfi_size(s, sz, src),
                s.rflags,
            );
            let s0 = if alu is Cmp {
                s
            } else {
                set_rgfi_size(s, sz, dst, r.result)
            };
            if !(alu is Cmp) {
                lemma_set_rgfi(s, sz, dst, r.result);
            }
            lemma_wur(u, s0, r.rflags, r.undef);
        },
        Instr::AluRM { alu, sz, dst, mem } => {
            let e = read_operand_mem(s, sz, mem)->Some_0;
            let r = gpr_arith_logic_spec(nbits(sz), alu, rgfi_size(s, sz, dst), e, s.rflags);
            let s0 = if alu is Cmp {
                s
            } else {
                set_rgfi_size(s, sz, dst, r.result)
            };
            if !(alu is Cmp) {
                lemma_set_rgfi(s, sz, dst, r.result);
            }
            lemma_wur(u, s0, r.rflags, r.undef);
        },
        Instr::AluRI { alu, sz, dst, imm } => {
            let r = gpr_arith_logic_spec(
                nbits(sz),
                alu,
                rgfi_size(s, sz, dst),
                loghead(nbits(sz), imm as int),
                s.rflags,
            );
            let s0 = if alu is Cmp {
                s
            } else {
                set_rgfi_size(s, sz, dst, r.result)
            };
            if !(alu is Cmp) {
                lemma_set_rgfi(s, sz, dst, r.result);
            }
            lemma_wur(u, s0, r.rflags, r.undef);
        },
        Instr::TestRR { sz, a, b } => {
            let r = gpr_and_spec(nbits(sz), rgfi_size(s, sz, a), rgfi_size(s, sz, b), s.rflags);
            lemma_wur(u, s, r.rflags, r.undef);
        },
        Instr::TestRI { sz, a, imm } => {
            let r = gpr_and_spec(
                nbits(sz),
                rgfi_size(s, sz, a),
                loghead(nbits(sz), imm as int),
                s.rflags,
            );
            lemma_wur(u, s, r.rflags, r.undef);
        },
        Instr::Neg { sz, r } => {
            let v = rgfi_size(s, sz, r);
            let o = gpr_sub_spec(nbits(sz), 0, v, s.rflags);
            let flags = set_bit32(o.rflags, cf_bit(), if v == 0 {
                0
            } else {
                1
            });
            let s1 = write_user_rflags(u, s, flags, o.undef);
            lemma_wur(u, s, flags, o.undef);
            lemma_set_rgfi(s1, sz, r, o.result);
        },
        Instr::Not { sz, r } => {
            lemma_set_rgfi(s, sz, r, p2(nbits(sz)) - 1 - rgfi_size(s, sz, r));
        },
        Instr::ShiftImm { shift, sz, r, count } => {
            let cnt = shift_count(sz, count as int);
            let o = shift_spec(shift, nbits(sz), rgfi_size(s, sz, r), cnt, s.rflags);
            let s2 = write_user_rflags(u, s, o.rflags, o.undef);
            lemma_wur(u, s, o.rflags, o.undef);
            lemma_set_rgfi(s2, sz, r, o.result);
        },
        Instr::ShiftCl { shift, sz, r } => {
            let cnt = shift_count(sz, loghead(8, rr64(s, 1)));
            let o = shift_spec(shift, nbits(sz), rgfi_size(s, sz, r), cnt, s.rflags);
            let s2 = write_user_rflags(u, s, o.rflags, o.undef);
            lemma_wur(u, s, o.rflags, o.undef);
            lemma_set_rgfi(s2, sz, r, o.result);
        },
        Instr::ImulRR { sz, dst, src } => {
            let (low, cfo) = imul_spec(nbits(sz), rgfi_size(s, sz, src), rgfi_size(s, sz, dst));
            let s0 = set_rgfi_size(s, sz, dst, low);
            lemma_set_rgfi(s, sz, dst, low);
            let flags = change_rflags(
                s0.rflags,
                FlagUpd {
                    cf: Some(cfo),
                    pf: None,
                    af: None,
                    zf: None,
                    sf: None,
                    of: Some(cfo),
                },
            );
            lemma_wur(u, s0, flags, mask_pf() | mask_af() | mask_zf() | mask_sf());
        },
        Instr::ImulRRI { sz, dst, src, imm } => {
            let (low, cfo) = imul_spec(
                nbits(sz),
                rgfi_size(s, sz, src),
                loghead(nbits(sz), imm as int),
            );
            let s0 = set_rgfi_size(s, sz, dst, low);
            lemma_set_rgfi(s, sz, dst, low);
            let flags = change_rflags(
                s0.rflags,
                FlagUpd {
                    cf: Some(cfo),
                    pf: None,
                    af: None,
                    zf: None,
                    sf: None,
                    of: Some(cfo),
                },
            );
            lemma_wur(u, s0, flags, mask_pf() | mask_af() | mask_zf() | mask_sf());
        },
        Instr::Cmovcc { cc, sz, dst, src } => {
            lemma_set_rgfi(s, sz, dst, rgfi_size(s, sz, src));
            lemma_set_rgfi(s, sz, dst, rgfi_size(s, sz, dst));
        },
        Instr::Setcc { cc, dst } => {
            lemma_wr08(s, dst, if jcc_cmovcc_setcc_spec(s, cc) {
                1
            } else {
                0
            });
        },
        Instr::FpArith { fop, dst, xsrc } => {
            let b = read_xmm_src(s, xsrc)->Some_0;
            lemma_xmm8(
                s,
                dst,
                dp_sse_add_sub_mul_div(fop, xmmi_size8(s, dst) as u64, b as u64) as int,
            );
        },
        Instr::Sqrtsd { dst, xsrc } => {
            let b = read_xmm_src(s, xsrc)->Some_0;
            lemma_xmm8(s, dst, dp_sse_sqrt(b as u64) as int);
        },
        Instr::Ucomisd { a, xsrc } => {
        },
        Instr::Cvtsi2sd { sz, dst, src } => {
            lemma_xmm8(
                s,
                dst,
                dp_sse_cvt_int_to_fp(logext(nbits(sz), rgfi_size(s, sz, src))) as int,
            );
        },
        Instr::Cvttsd2si { sz, dst, src } => {
            lemma_set_rgfi(
                s,
                sz,
                dst,
                dp_sse_cvt_fp_to_int(nbytes(sz), xmmi_size8(s, src) as u64, true),
            );
        },
        Instr::Cvtsd2si { sz, dst, src } => {
            lemma_set_rgfi(
                s,
                sz,
                dst,
                dp_sse_cvt_fp_to_int(nbytes(sz), xmmi_size8(s, src) as u64, false),
            );
        },
        Instr::MovqToXmm { dst, src } => {
            lemma_xmm16(s, dst, rr64(s, src));
        },
        Instr::MovqFromXmm { dst, src } => {
            lemma_wr64(s, dst, xmmi_size8(s, src));
        },
        Instr::MovsdLoad { dst, mem } => {
            let v = read_mem(s.mem, eff_addr(s, mem), 8)->Some_0;
            lemma_xmm16(s, dst, v);
        },
        Instr::MovsdStore { mem, src } => {
            lemma_store_mem(s, mem, Size::W64, xmmi_size8(s, src), s1);
        },
        Instr::Jcc { cc, rel } => {},
        Instr::Jmp { rel } => {},
        Instr::Ret => {},
    }
}

/// **What `step` can change.** A step writes only `written_gpr` (and `rsp`
/// for `ret`), the bytes of a store's access, and `rip`.
pub proof fn lemma_step_frame(u: spec_fn(nat) -> nat, s: State, i: Instr, s2: State)
    requires
        valid_instr(i),
        s.rgf.len() == 16,
        step(u, s, i) == Some(s2),
    ensures
        gpr_kept(s, s2, if i is Ret { Some(4u8) } else { written_gpr(i) }),
        match mem_access(i) {
            Some(a) => if a.store {
                mem_frame(s.mem, s2.mem, eff_addr(s, a.mem), a.size)
            } else {
                s2.mem == s.mem
            },
            None => s2.mem == s.mem,
        },
        !(i is Jcc) && !(i is Jmp) && !(i is Ret) ==> s2.rip == s.rip + instr_len(i),
        i is Jmp ==> s2.rip == s.rip + instr_len(i) + i->Jmp_rel,
        i is Jcc ==> s2.rip == if jcc_cmovcc_setcc_spec(s, i->Jcc_cc) {
            s.rip + instr_len(i) + i->Jcc_rel
        } else {
            s.rip + instr_len(i)
        },
{
    match i {
        Instr::Jcc { cc, rel } => {},
        Instr::Jmp { rel } => {},
        Instr::Ret => {
            let rsp = logext(64, rr64(s, 4));
            let new_rsp = logext(64, rsp + 8);
            lemma_wr64(s, 4, new_rsp);
        },
        _ => {
            let s1 = effect(u, s, i)->Some_0;
            lemma_effect_frame(u, s, i, s1);
        },
    }
}

} // verus!

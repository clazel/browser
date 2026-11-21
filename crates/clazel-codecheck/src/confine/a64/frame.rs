//! **What a step of `clazel-a64` leaves alone**: the frame lemmas of the A64
//! confinement proof. `execute` writes the destination register of
//! [`written_gpr`], `SP` only for [`writes_sp`], and memory only in a store's
//! bytes ([`mem_set`]); a step then moves the program counter. Also the facts
//! about [`mem_read`] and [`mem_set`] the proof uses: a store changes only the
//! bytes it names, and a load or a store's fault depends only on the bytes it
//! touches.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The values of `2^k` the proof uses.
pub proof fn lemma_p2()
    ensures
        p2(0) == 1,
        p2(1) == 2,
        p2(2) == 4,
        p2(3) == 8,
        p2(64) == 18446744073709551616,
        p2(32) == 4294967296,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
}

/// Truncating to 64 bits is the identity on a value in range.
pub proof fn lemma_trunc64_id(x: int)
    requires
        0 <= x < p2(64),
    ensures
        trunc(64, x) == x,
{
    lemma_p2();
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, p2(64) as nat);
}

/// A truncation to 64 bits is in range.
pub proof fn lemma_trunc64_range(x: int)
    ensures
        0 <= trunc(64, x) < p2(64),
{
    lemma_p2();
    vstd::arithmetic::div_mod::lemma_mod_bound(x, p2(64));
}

/// Reading a general register of a well-formed state in 64 bits.
pub proof fn lemma_xr(s: State, r: u8)
    requires
        s.r.len() == 31,
        r < 31,
    ensures
        x_read(s, r, 64) == s.r[r as int] as int,
        0 <= x_read(s, r, 64) < p2(64),
{
    lemma_p2();
    let v = s.r[r as int] as int;
    assert(0 <= v < 18446744073709551616);
    lemma_trunc64_id(v);
}

/// Reading register 31 gives zero.
pub proof fn lemma_xr31(s: State)
    ensures
        x_read(s, 31, 64) == 0,
{
}

/// The memory part of a store: the domain is unchanged and every byte outside
/// `[addr, addr + size)` is unchanged.
pub open spec fn store_frame(s: State, s2: State, addr: int, size: int) -> bool {
    s2.mem.dom() =~= s.mem.dom() && forall|x: int|
        (x < addr || x >= addr + size) && s.mem.dom().contains(x) ==> #[trigger] s2.mem[x]
            == s.mem[x]
}

/// An instruction is a store.
pub open spec fn is_store(i: Instr) -> bool {
    match mem_access(i) {
        Some(a) => a.store,
        None => false,
    }
}

/// A successful [`mem_set`] changes only the bytes it names, and keeps the
/// domain, if the bytes do not wrap around `2^64`.
pub proof fn lemma_mem_set_frame(m: Map<int, u8>, a: int, n: nat, v: int, m2: Map<int, u8>)
    requires
        mem_set(m, a, n, v) == Some(m2),
        0 <= a,
        a + n <= p2(64),
    ensures
        m2.dom() =~= m.dom(),
        forall|x: int| (x < a || x >= a + n) && m.dom().contains(x) ==> #[trigger] m2[x] == m[x],
    decreases n,
{
    lemma_p2();
    if n == 0 {
    } else {
        lemma_trunc64_id(a);
        assert(m.dom().contains(a));
        let m3 = mem_set(m, a + 1, (n - 1) as nat, v / 256)->Some_0;
        assert(mem_set(m, a + 1, (n - 1) as nat, v / 256) == Some(m3));
        lemma_mem_set_frame(m, a + 1, (n - 1) as nat, v / 256, m3);
        assert(m2 == m3.insert(a, (v % 256) as u8));
        assert(m2.dom() =~= m.dom());
        assert forall|x: int| (x < a || x >= a + n) && m.dom().contains(x) implies #[trigger] m2[x]
            == m[x] by {
            assert(x != a);
            assert(x < a + 1 || x >= a + 1 + (n - 1));
        }
    }
}

/// A store faults in `m2` if and only if in `m`, if they agree on which of
/// its bytes are mapped.
pub proof fn lemma_mem_set_some_same(m: Map<int, u8>, m2: Map<int, u8>, a: int, n: nat, v: int)
    requires
        0 <= a,
        a + n <= p2(64),
        forall|x: int| a <= x < a + n ==> #[trigger] m2.dom().contains(x) == m.dom().contains(x),
    ensures
        mem_set(m2, a, n, v) is Some == mem_set(m, a, n, v) is Some,
    decreases n,
{
    lemma_p2();
    if n > 0 {
        lemma_trunc64_id(a);
        assert(m2.dom().contains(a) == m.dom().contains(a));
        lemma_mem_set_some_same(m, m2, a + 1, (n - 1) as nat, v / 256);
    }
}

/// A load gives the same in `m2` as in `m`, if they agree on its bytes.
pub proof fn lemma_mem_read_same(m: Map<int, u8>, m2: Map<int, u8>, a: int, n: nat)
    requires
        0 <= a,
        a + n <= p2(64),
        forall|x: int|
            a <= x < a + n ==> (#[trigger] m2.dom().contains(x) == m.dom().contains(x) && (
            m.dom().contains(x) ==> m2[x] == m[x])),
    ensures
        mem_read(m2, a, n) == mem_read(m, a, n),
    decreases n,
{
    lemma_p2();
    if n > 0 {
        lemma_trunc64_id(a);
        lemma_mem_read_same(m, m2, a + 1, (n - 1) as nat);
    }
}

/// The frame of one instruction's `execute`: the program counter, the lengths,
/// the registers other than the destination, `SP` unless written, memory
/// unless a store.
pub open spec fn exec_frame(s: State, s1: State, i: Instr) -> bool {
    s1.r.len() == 31 && s1.vreg.len() == 32 && s1.pc == s.pc && (forall|r: int|
        0 <= r < 31 && written_gpr(i) != Some(r as u8) ==> #[trigger] s1.r[r] == s.r[r]) && (
    !writes_sp(i) ==> s1.sp == s.sp) && (!is_store(i) ==> s1.mem == s.mem)
}

/// **The frame of `execute`**, for every instruction of the subset: it
/// writes the destination register (and `SP` for `ADD`/`SUB` into 31), the
/// flags and the vector registers, and, for a store, exactly the bytes
/// [`mem_set`] writes at the address [`eff_addr`] computes.
pub proof fn lemma_execute_frame(s: State, i: Instr, s1: State)
    requires
        s.r.len() == 31,
        s.vreg.len() == 32,
        valid_instr(i),
        execute(s, i) == Some(s1),
    ensures
        exec_frame(s, s1, i),
        is_store(i) ==> exists|data: int|
            #[trigger] mem_set(
                s.mem,
                eff_addr(s, mem_access(i)->Some_0),
                mem_access(i)->Some_0.size as nat,
                data,
            ) == Some(s1.mem),
{
    lemma_p2();
    match i {
        Instr::AddSubShiftedReg { .. } => {},
        Instr::AddSubImm { .. } => {},
        Instr::MulAddSub { .. } => {},
        Instr::Div { .. } => {},
        Instr::LogicalShiftedReg { .. } => {},
        Instr::ShiftVariable { .. } => {},
        Instr::Bitfield { .. } => {},
        Instr::MoveWide { .. } => {},
        Instr::CondSelect { .. } => {},
        Instr::LoadStoreImm { sf, load, t, n, imm12 } => {
            let datasize = datasize(sf);
            let a = mem_access(i)->Some_0;
            assert(eff_addr(s, a) == trunc(64, x_read(s, n, 64) + imm12 as int * nbytes(sf)));
            if !load {
                let data = x_read(s, t, datasize);
                assert(mem_set(s.mem, eff_addr(s, a), a.size as nat, data) == Some(s1.mem));
            }
        },
        Instr::LoadStoreReg { sf, load, t, n, m, s: sbit } => {
            let datasize = datasize(sf);
            let a = mem_access(i)->Some_0;
            if !load {
                let data = x_read(s, t, datasize);
                assert(mem_set(s.mem, eff_addr(s, a), a.size as nat, data) == Some(s1.mem));
            }
        },
        Instr::FpLoadStoreImm { load, t, n, imm12 } => {
            let a = mem_access(i)->Some_0;
            if !load {
                let data = v_read(s, t, 64);
                assert(mem_set(s.mem, eff_addr(s, a), a.size as nat, data) == Some(s1.mem));
            }
        },
        Instr::FpLoadStoreReg { load, t, n, m, s: sbit } => {
            let a = mem_access(i)->Some_0;
            if !load {
                let data = v_read(s, t, 64);
                assert(mem_set(s.mem, eff_addr(s, a), a.size as nat, data) == Some(s1.mem));
            }
        },
        Instr::B { .. } => {},
        Instr::BCond { .. } => {},
        Instr::CompareBranch { .. } => {},
        Instr::Ret => {},
        Instr::FAddSub { .. } => {},
        Instr::FMul { .. } => {},
        Instr::FDiv { .. } => {},
        Instr::FUnary { .. } => {},
        Instr::FCmp { .. } => {},
        Instr::FMovGen { .. } => {},
        Instr::Scvtf { .. } => {},
        Instr::Fcvtzs { .. } => {},
    }
}

/// The frame of a successful `step` of an instruction that is not a branch:
/// as [`exec_frame`], and the program counter has moved to the next word.
pub proof fn lemma_step_straight(s: State, i: Instr, s2: State)
    requires
        s.r.len() == 31,
        s.vreg.len() == 32,
        valid_instr(i),
        !(i is B),
        !(i is BCond),
        !(i is CompareBranch),
        !(i is Ret),
        step(s, i) == Some(s2),
    ensures
        execute(s, i) is Some,
        ({
            let s1 = execute(s, i)->Some_0;
            exec_frame(s, s1, i) && s2 == State { pc: trunc(64, s.pc as int + 4) as u64, ..s1 }
        }),
        s2.r.len() == 31,
        s2.vreg.len() == 32,
        s2.pc as int == trunc(64, s.pc as int + 4),
        forall|r: int|
            0 <= r < 31 && written_gpr(i) != Some(r as u8) ==> #[trigger] s2.r[r] == s.r[r],
        !writes_sp(i) ==> s2.sp == s.sp,
        !is_store(i) ==> s2.mem == s.mem,
        is_store(i) ==> exists|data: int|
            #[trigger] mem_set(
                s.mem,
                eff_addr(s, mem_access(i)->Some_0),
                mem_access(i)->Some_0.size as nat,
                data,
            ) == Some(s2.mem),
{
    let s1 = execute(s, i)->Some_0;
    lemma_execute_frame(s, i, s1);
    lemma_trunc64_range(s.pc as int + 4);
    assert(s2 == branch_to(s1, s.pc as int + 4));
    let v = trunc(64, s.pc as int + 4);
    assert(0 <= v < 18446744073709551616) by {
        lemma_p2();
    }
    assert(s2.pc == v as u64);
    assert(v as u64 as int == v);
}

} // verus!

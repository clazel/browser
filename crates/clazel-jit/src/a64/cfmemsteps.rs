//! One step of the two region-access instruction forms the memory templates
//! use: `ldr`/`str` (register offset, `UXTX`, no shift) of a W or X register,
//! `[xn, xm]`. The A64 counterpart of [`crate::cfmemsteps`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bytes an access of width `sf` touches.
pub open spec fn sf_bytes(sf: isa::Width) -> nat {
    match sf {
        isa::Width::W32 => 4,
        isa::Width::W64 => 8,
    }
}

/// `ldr wt/xt, [xn, xm]` loads the `sf_bytes` bytes at `xn + xm` (zero-extended)
/// into `xt`, advances `pc` by 4, and changes nothing else.
pub proof fn lemma_step_ld_reg(m: isa::State, sf: isa::Width, t: u8, n: u8, mr: u8, v: nat)
    requires
        isa::wf(m),
        t < 31,
        n < 31,
        mr < 31,
        0 <= m.r[n as int] as int + m.r[mr as int] as int,
        m.r[n as int] as int + m.r[mr as int] as int + sf_bytes(sf) < 0x1_0000_0000_0000_0000,
        isa::mem_read(
            m.mem,
            m.r[n as int] as int + m.r[mr as int] as int,
            sf_bytes(sf),
        ) == Some(v as int),
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(
            m,
            isa::Instr::LoadStoreReg { sf, load: true, t, n, m: mr, s: false },
        ) == Some(isa::State { r: m.r.update(t as int, v as u64), pc: (m.pc + 4) as u64, ..m }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_x_read64(m, n);
    super::steps::lemma_x_read64(m, mr);
    let addr = m.r[n as int] as int + m.r[mr as int] as int;
    super::memlemmas::lemma_trunc64(addr);
    super::memlemmas::lemma_trunc64(m.pc as int + 4);
    super::memlemmas::lemma_trunc64(m.r[mr as int] as int);
    let i = isa::Instr::LoadStoreReg { sf, load: true, t, n, m: mr, s: false };
    let ds = isa::datasize(sf);
    assert(ds / 8 == sf_bytes(sf));
    assert(isa::extend_reg_uxtx(m, mr, 0) == m.r[mr as int] as int) by {
        assert(isa::p2(0) == 1);
        assert(isa::trunc(64, m.r[mr as int] as int) == m.r[mr as int] as int);
    }
    super::cfmemrel::lemma_read_mem_range(m.mem, addr, sf_bytes(sf), v as int);
    assert(isa::trunc(ds, v as int) == v as int) by {
        vstd::arithmetic::power2::lemma2_to64();
        assert(isa::p2(ds) == vstd::arithmetic::power2::pow2(8 * sf_bytes(sf)) as int);
        vstd::arithmetic::div_mod::lemma_small_mod(v, isa::p2(ds) as nat);
    }
    assert(isa::execute(m, i) == Some(isa::x_set(m, t, ds, v as int)));
    assert(isa::x_set(m, t, ds, v as int) == isa::State { r: m.r.update(t as int, v as u64), ..m });
}

/// `str wt/xt, [xn, xm]` writes the low `sf_bytes` bytes of `xt` at `xn + xm`
/// (the bytes are mapped), advances `pc` by 4, and changes nothing but that
/// memory.
pub proof fn lemma_step_st_reg(m: isa::State, sf: isa::Width, t: u8, n: u8, mr: u8)
    requires
        isa::wf(m),
        t < 31,
        n < 31,
        mr < 31,
        0 <= m.r[n as int] as int + m.r[mr as int] as int,
        m.r[n as int] as int + m.r[mr as int] as int + sf_bytes(sf) < 0x1_0000_0000_0000_0000,
        forall|i: int|
            0 <= i < sf_bytes(sf) ==> m.mem.dom().contains(
                #[trigger] (m.r[n as int] as int + m.r[mr as int] as int + i),
            ),
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let addr = m.r[n as int] as int + m.r[mr as int] as int;
            let w = isa::trunc(isa::datasize(sf), m.r[t as int] as int);
            &&& isa::mem_set(m.mem, addr, sf_bytes(sf), w) is Some
            &&& isa::step(m, isa::Instr::LoadStoreReg { sf, load: false, t, n, m: mr, s: false })
                == Some(
                isa::State {
                    mem: isa::mem_set(m.mem, addr, sf_bytes(sf), w).unwrap(),
                    pc: (m.pc + 4) as u64,
                    ..m
                },
            )
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_x_read64(m, n);
    super::steps::lemma_x_read64(m, mr);
    let addr = m.r[n as int] as int + m.r[mr as int] as int;
    super::memlemmas::lemma_trunc64(addr);
    super::memlemmas::lemma_trunc64(m.pc as int + 4);
    super::memlemmas::lemma_trunc64(m.r[mr as int] as int);
    let i = isa::Instr::LoadStoreReg { sf, load: false, t, n, m: mr, s: false };
    let ds = isa::datasize(sf);
    assert(ds / 8 == sf_bytes(sf));
    assert(isa::extend_reg_uxtx(m, mr, 0) == m.r[mr as int] as int) by {
        assert(isa::p2(0) == 1);
        assert(isa::trunc(64, m.r[mr as int] as int) == m.r[mr as int] as int);
    }
    let w = isa::trunc(ds, m.r[t as int] as int);
    assert(isa::x_read(m, t, ds) == w);
    super::memlemmas::lemma_mem_set_some(m.mem, addr, sf_bytes(sf), w);
}

} // verus!

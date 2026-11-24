//! The exit sequence refines LIR's `exit c` with no operands
//! ([`lemma_exit_refines`]): `movz w0, #c; str x0, [x28, #256]; ret`. The A64
//! counterpart of [`crate::exit`]; `ret` reads no memory, so unlike x86-64 there
//! is no stack to describe.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `str xr, [x28, #256]`: the store of the exit code.
pub open spec fn store_exit(src: u8) -> isa::Instr {
    isa::Instr::LoadStoreImm {
        sf: isa::Width::W64,
        load: false,
        t: src,
        n: abi::ctx_reg(),
        imm12: (abi::exit_code_off() / 8) as u16,
    }
}

/// `str xr, [x28, #256]` writes `xr` to the exit-code word and changes nothing
/// else.
pub proof fn lemma_step_store_exit(m: isa::State, src: u8)
    requires
        isa::wf(m),
        ctx_ok(m),
        src < 31,
        exit_area_mapped(m.mem, ctx_of(m)),
        m.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(m, store_exit(src)) is Some,
        ({
            let m1 = isa::step(m, store_exit(src)).unwrap();
            &&& m1 == isa::State { mem: m1.mem, pc: (m.pc + 4) as u64, ..m }
            &&& isa::mem_read(m1.mem, ctx_of(m) + abi::exit_code_off(), 8) == Some(
                m.r[src as int] as int,
            )
            &&& m1.mem.dom() =~= m.mem.dom()
            &&& forall|b: int|
                #![trigger m1.mem.dom().contains(b)]
                m.mem.dom().contains(b) && (b < ctx_of(m) + abi::exit_code_off() || ctx_of(m)
                    + abi::exit_code_off() + 8 <= b) ==> m1.mem[b] == m.mem[b]
        }),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    super::alu::lemma_pc4(m.pc);
    super::steps::lemma_x_read64(m, 28);
    super::steps::lemma_x_read64(m, src);
    let ctxb = ctx_of(m);
    let addr = ctxb + 256;
    let w = m.r[src as int] as int;
    super::memlemmas::lemma_trunc64(addr);
    super::memlemmas::lemma_trunc64(256);
    assert(isa::x_read(m, 28, 64) == ctxb);
    assert(((abi::exit_code_off() / 8) as u16) as int == 32);
    assert(isa::trunc(64, ctxb + 32 * (isa::datasize(isa::Width::W64) as int / 8)) == addr);
    assert forall|i: int| 0 <= i < 8 implies m.mem.dom().contains(#[trigger] (addr + i)) by {
        assert(in_exit_area(ctxb, addr + i));
    }
    super::memlemmas::lemma_mem_set_some(m.mem, addr, 8, w);
    let m2 = isa::mem_set(m.mem, addr, 8, w).unwrap();
    super::memlemmas::lemma_mem_set_frame(m.mem, addr, 8, w, m2);
    assert(0 <= w < vstd::arithmetic::power2::pow2(8 * 8) as int) by {
        vstd::arithmetic::power2::lemma2_to64_rest();
    }
    super::memlemmas::lemma_read_after_write_same(m.mem, addr, 8, w, m2);
    assert(isa::execute(m, store_exit(src)) == Some(isa::State { mem: m2, ..m }));
}

/// **The exit sequence refines `exit c`.**
#[verifier::rlimit(500)]
pub proof fn lemma_exit_refines(c: u16, nl: nat)
    ensures
        super::contract::exit_refines(c, nl),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    assert forall|lay: lir::Layout, a: lir::St, m: isa::State, fuel: nat|
        #![trigger lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, fuel), run_seq(m, exit_seq(c))]
        rel(lay, a, m, nl) && (m.pc as int) + code_len(exit_seq(c)) < isa::p2(64) implies match lir::eval(
        lay,
        lir::Instr::Exit(c as nat, seq![]),
        a,
        fuel,
    ) {
        lir::Outcome::Exit(code, _, a2) => match run_seq(m, exit_seq(c)) {
            Some(m2) => rel(lay, a2, m2, nl) && preserved(m, m2) && isa::mem_read(
                m2.mem,
                ctx_of(m) + abi::exit_code_off(),
                8,
            ) == Some(code as int) && m2.pc == m.r[abi::link_reg() as int],
            None => false,
        },
        _ => true,
    } by {
        match lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, fuel) {
            lir::Outcome::Exit(code, vals, a2) => {
                assert(fuel > 0);
                assert(code == c as nat);
                assert(a2.stack =~= a.stack);
                assert(a2.locals == a.locals && a2.mem == a.mem);
                let i1 = isa::Instr::MoveWide {
                    sf: isa::Width::W32,
                    opcode: isa::MoveWideOp::Z,
                    d: 0,
                    imm16: c,
                    hw: 0,
                };
                let i2 = store_exit(0);
                let i3 = isa::Instr::Ret;
                assert(exit_seq(c) == seq![i1, i2, i3]);
                assert(isa::wf(m));
                let ctxb = ctx_of(m);
                // 1. movz w0, #c
                assert(super::alu::bits(isa::Width::W32) == 32);
                super::bitmid::lemma_step_movz(m, isa::Width::W32, 0, c, 0);
                assert(super::bitmid::chunk_val(c, 0) == c as int);
                let s1 = isa::State { r: m.r.update(0, c as u64), pc: (m.pc + 4) as u64, ..m };
                assert(isa::step(m, i1) == Some(s1));
                super::alu::lemma_pc4(m.pc);
                assert(rel(lay, a, s1, nl)) by {
                    super::rel::lemma_rel_regs(lay, a, m, s1, nl);
                }
                // 2. str x0, [x28, #256]
                lemma_step_store_exit(s1, 0);
                let s2 = isa::step(s1, i2).unwrap();
                assert(s1.r[0] == c as u64);
                assert(isa::wf(s2)) by {
                    assert(s2.mem.dom() =~= m.mem.dom());
                }
                // the frame's slots survive the store to the exit-code word
                assert forall|j: nat| j < nl + a.stack.len() implies #[trigger] slot_holds(
                    s2.mem,
                    ctxb,
                    j,
                    lir::val_bits(slot_val(a, nl, j)),
                ) by {
                    assert(slot_holds(m.mem, ctxb, j, lir::val_bits(slot_val(a, nl, j))));
                    assert(j < max_slots());
                    super::steps::lemma_slot_addr(m, j);
                    assert forall|i: int| 0 <= i < 8 implies (m.mem.dom().contains(
                        #[trigger] (ctxb + slot_disp(j) + i),
                    ) == s2.mem.dom().contains(ctxb + slot_disp(j) + i)) && (m.mem.dom().contains(
                        ctxb + slot_disp(j) + i,
                    ) ==> m.mem[ctxb + slot_disp(j) + i] == s2.mem[ctxb + slot_disp(j) + i]) by {
                        assert(s2.mem.dom().contains(ctxb + slot_disp(j) + i) == m.mem.dom().contains(
                            ctxb + slot_disp(j) + i,
                        ));
                    }
                    super::memlemmas::lemma_mem_read_congr(m.mem, s2.mem, ctxb + slot_disp(j), 8);
                }
                assert(mem_rel(lay, a.mem, s2.mem)) by {
                    assert forall|b: nat| #[trigger] in_regions(lay, b) implies s2.mem.dom().contains(
                        b as int,
                    ) && s2.mem[b as int] == lir::byte_at(a.mem, b) by {
                        assert(!in_exit_area(ctxb, b as int));
                        assert(m.mem.dom().contains(b as int));
                    }
                }
                assert(rel(lay, a2, s2, nl)) by {
                    assert(isa::wf(s2) && ctx_ok(s2));
                    assert(ctx_of(s2) == ctxb);
                    assert(exit_area_mapped(s2.mem, ctxb));
                }
                // 3. ret
                super::steps::lemma_x_read64(s2, 30);
                let target = s2.r[30] as int;
                assert(isa::x_read(s2, 30, 64) == target);
                super::memlemmas::lemma_trunc64(target);
                let s3 = isa::State { pc: s2.r[30], ..s2 };
                assert(isa::step(s2, i3) == Some(s3));
                super::runseq::run3(m, i1, i2, i3, s1, s2, s3);
                assert(s3.r == s2.r && s3.mem == s2.mem);
                assert(rel(lay, a2, s3, nl)) by {
                    super::rel::lemma_rel_regs(lay, a2, s2, s3, nl);
                }
                assert(s3.r[30] == m.r[30]);
                assert(preserved_mem(m, s3));
            },
            _ => {},
        }
    }
}

} // verus!

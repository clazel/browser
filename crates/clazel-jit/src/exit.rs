//! The exit sequence's refinement ([`exit_refines`]): `mov eax, c; mov [r15 +
//! 256], rax; ret`, for LIR's `exit c` with no operands. The first two
//! instructions put the code in the context's exit-code word; the `ret` pops
//! the return address the enter stub pushed. The frame, the regions and the
//! code are untouched.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The memory operand of the exit-code word: `[r15 + 256]`.
pub open spec fn exit_mem() -> x64::Mem {
    x64::Mem { base: abi::ctx_reg(), index: None, disp: abi::exit_code_off() as i32 }
}

/// `mov [r15 + 256], src` writes the exit-code word: it reads back as `src`'s
/// value, every byte outside those 8 is as it was, and the registers and
/// flags are unchanged.
pub proof fn lemma_step_store_exit(cu: spec_fn(nat) -> nat, m: x64::State, src: u8)
    requires
        x64::wf(m),
        ctx_ok(m),
        src < 16,
        exit_area_mapped(m.mem, ctx_of(m)),
        x64::canonical(
            m.rip + x64::instr_len(
                x64::Instr::MovStore { sz: x64::Size::W64, mem: exit_mem(), src: src },
            ),
        ),
    ensures
        x64::step(
            cu,
            m,
            x64::Instr::MovStore { sz: x64::Size::W64, mem: exit_mem(), src: src },
        ) is Some,
        ({
            let m1 = x64::step(
                cu,
                m,
                x64::Instr::MovStore { sz: x64::Size::W64, mem: exit_mem(), src: src },
            ).unwrap();
            &&& m1 == x64::State {
                mem: m1.mem,
                rip: m.rip + x64::instr_len(
                    x64::Instr::MovStore { sz: x64::Size::W64, mem: exit_mem(), src: src },
                ),
                ..m
            }
            &&& x64::read_mem(m1.mem, ctx_of(m) + abi::exit_code_off(), 8) == Some(
                m.rgf[src as int] as int,
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
    let ctxb = ctx_of(m);
    let addr = ctxb + 256;
    assert((256int as i32) as int == 256);
    assert(x64::eff_addr(m, exit_mem()) == addr) by {
        assert(0 <= addr && addr < 0x8000_0000_0000 + 512);
        assert(x64::loghead(64, addr) == addr);
        assert(x64::logext(64, addr) == addr);
    }
    let w = m.rgf[src as int] as int;
    assert(x64::rgfi_size(m, x64::Size::W64, src) == w);
    assert forall|i: int| 0 <= i < 8 implies m.mem.dom().contains(#[trigger] (addr + i)) by {
        assert(in_exit_area(ctxb, addr + i));
    }
    super::memlemmas::lemma_write_mem_some(m.mem, addr, 8, w);
    let m2 = x64::write_mem(m.mem, addr, 8, w).unwrap();
    super::memlemmas::lemma_write_mem_frame(m.mem, addr, 8, w, m2);
    assert(0 <= w < vstd::arithmetic::power2::pow2(8 * 8) as int) by {
        assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000);
    }
    super::memlemmas::lemma_read_after_write_same(m.mem, addr, 8, w, m2);
    assert(x64::store_mem(m, exit_mem(), x64::Size::W64, w) == Some(x64::State { mem: m2, ..m }));
}

/// **The exit sequence refines `exit c`.**
#[verifier::rlimit(500)]
pub proof fn lemma_exit_refines(c: u32, nl: nat)
    ensures
        super::contract::exit_refines(c, nl),
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    assert forall|
        lay: lir::Layout,
        cu: spec_fn(nat) -> nat,
        a: lir::St,
        m: x64::State,
        fuel: nat,
    |
        #![trigger lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, fuel), run_seq(cu, m, exit_seq(c))]
        rel(lay, a, m, nl) && stack_ok(m) && x64::canonical(m.rip + code_len(exit_seq(c)))
            implies match lir::eval(lay, lir::Instr::Exit(c as nat, seq![]), a, fuel) {
        lir::Outcome::Exit(code, _, a2) => match run_seq(cu, m, exit_seq(c)) {
            Some(m2) => {
                let rsp = x64::logext(64, m.rgf[abi::sp_reg() as int] as int);
                rel(lay, a2, m2, nl) && preserved_mem(m, m2) && x64::read_mem(
                    m2.mem,
                    ctx_of(m) + abi::exit_code_off(),
                    8,
                ) == Some(code as int) && m2.rgf[abi::sp_reg() as int] as int == x64::loghead(
                    64,
                    rsp + 8,
                ) && match x64::read_mem(m.mem, rsp, 8) {
                    Some(raw) => m2.rip == x64::logext(64, raw),
                    None => false,
                }
            },
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
                let i1 = x64::Instr::MovImm32 { dst: rax(), imm_u32: c };
                let i2 = x64::Instr::MovStore { sz: x64::Size::W64, mem: exit_mem(), src: rax() };
                let i3 = x64::Instr::Ret;
                assert(exit_seq(c) == seq![i1, i2, i3]);
                super::runseq::lemma_len3(i1, i2, i3);
                assert(x64::wf(m));
                let ctxb = ctx_of(m);
                // 1. mov eax, c
                super::steps::lemma_step_imm(cu, m, i1);
                let s1 = x64::State {
                    rgf: m.rgf.update(0, c as u64),
                    rip: m.rip + x64::instr_len(i1),
                    ..m
                };
                assert(x64::canonical(s1.rip));
                assert(rel(lay, a, s1, nl)) by {
                    super::rel::lemma_rel_regs(lay, a, m, s1, nl);
                }
                // 2. mov [r15 + 256], rax
                lemma_step_store_exit(cu, s1, 0);
                let s2 = x64::step(cu, s1, i2).unwrap();
                assert(s1.rgf[0] == c as u64);
                assert(x64::canonical(s2.rip));
                assert(x64::wf(s2)) by {
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
                    super::memlemmas::lemma_read_mem_congr(m.mem, s2.mem, ctxb + slot_disp(j), 8);
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
                    assert(x64::wf(s2) && ctx_ok(s2));
                    assert(ctx_of(s2) == ctxb);
                    assert(exit_area_mapped(s2.mem, ctxb));
                }
                // 3. ret
                let rsp = x64::logext(64, m.rgf[4] as int);
                assert(s2.rgf[4] == m.rgf[4]);
                assert(rsp + 8 <= ctxb + 256 || ctxb + 512 <= rsp);
                match x64::read_mem(m.mem, rsp, 8) {
                    Some(raw) => {
                        super::memlemmas::lemma_read_mem_congr(m.mem, s2.mem, rsp, 8);
                        assert(x64::read_mem(s2.mem, rsp, 8) == Some(raw));
                        let new_rsp = x64::logext(64, rsp + 8);
                        let tos = x64::logext(64, raw);
                        assert(x64::canonical(new_rsp) && x64::canonical(tos));
                        let s3 = x64::step(cu, s2, i3).unwrap();
                        assert(x64::step(cu, s2, i3) == Some(
                            x64::write_ip(x64::wr64(s2, 4, new_rsp), tos),
                        ));
                        let f = super::runseq::stepper(cu);
                        super::runseq::lemma_gen3(f, m, i1, i2, i3, s1, s2, s3);
                        super::runseq::lemma_run_seq_is_gen(cu, m, seq![i1, i2, i3]);
                        assert(s3.rgf.len() == 16);
                        assert(s3.rgf[15] == m.rgf[15]);
                        assert(s3.mem == s2.mem);
                        assert(x64::wf(s3));
                        assert(rel(lay, a2, s3, nl)) by {
                            super::rel::lemma_rel_regs(lay, a2, s2, s3, nl);
                        }
                        assert(preserved_mem(m, s3));
                        assert(x64::loghead(64, new_rsp) == x64::loghead(64, rsp + 8));
                    },
                    None => {
                        assert(false);
                    },
                }
            },
            _ => {},
        }
    }
}

} // verus!

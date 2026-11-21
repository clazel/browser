//! What one [`isa::step`] does for the arithmetic, logic, shift and multiply
//! forms the templates use (`x0 := x0 op x1`), as numbers: the result word in
//! `x0` is LIR's result. The A64 counterpart of [`crate::alu`], which has the
//! same job for x86-64. Each lemma takes the operands as the values of `x0`
//! and `x1` below `2^n` for the instruction's width `n`, and says what the
//! state after the step is.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bit width of an operand size, as the `nat` the spec's arithmetic takes.
pub open spec fn bits(sf: isa::Width) -> nat {
    isa::datasize(sf)
}

/// The step of a register-writing instruction that does not touch the flags,
/// memory or the stack pointer: `x0` is set to `v`, `pc` advances by 4.
pub open spec fn wrote_x0(s: isa::State, v: int, n: nat) -> isa::State {
    isa::State { r: s.r.update(0, isa::trunc(n, v) as u64), pc: (s.pc + 4) as u64, ..s }
}

/// `pc + 4` does not wrap, so the program counter after a step is the address
/// after the instruction.
pub proof fn lemma_pc4(pc: u64)
    requires
        pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::trunc(64, pc as int + 4) == pc as int + 4,
{
    super::memlemmas::lemma_trunc64(pc as int + 4);
}

/// A number below `2^n` is its own low `n` bits.
pub proof fn lemma_trunc_small(n: nat, x: int)
    requires
        n == 32 || n == 64,
        0 <= x < isa::p2(n),
    ensures
        isa::trunc(n, x) == x,
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::div_mod::lemma_small_mod(x as nat, isa::p2(n) as nat);
}

/// A number's low `n` bits are below `2^n`.
pub proof fn lemma_trunc_bound(n: nat, x: int)
    requires
        n == 32 || n == 64,
    ensures
        0 <= isa::trunc(n, x) < isa::p2(n),
{
    super::memlemmas::lemma_p2_consts();
    vstd::arithmetic::div_mod::lemma_mod_bound(x, isa::p2(n));
}

/// `add x0, x0, x1` and `sub x0, x0, x1` (no flags) at width `sf`: `x0` gets
/// `x + y` or `x - y` modulo `2^n`.
#[verifier::rlimit(200)]
pub proof fn lemma_step_addsub(s: isa::State, sf: isa::Width, sub: bool, x: u64, y: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        s.r[1] == y,
        x < isa::p2(bits(sf)),
        y < isa::p2(bits(sf)),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::int_op_instr(if sub {
            lir::IBin::Sub
        } else {
            lir::IBin::Add
        }, sf)) == Some(
            wrote_x0(
                s,
                if sub {
                    (x as int - y as int) % isa::p2(bits(sf))
                } else {
                    (x as int + y as int) % isa::p2(bits(sf))
                },
                bits(sf),
            ),
        ),
{
    let n = bits(sf);
    let ni = n as int;
    assert(n == 32 || n == 64);
    super::memlemmas::lemma_p2_consts();
    lemma_pc4(s.pc);
    let p = isa::p2(n);
    lemma_trunc_small(n, x as int);
    lemma_trunc_small(n, y as int);
    // operand2 after the shift by 0
    assert(isa::lsl(n, y as int, 0) == y as int) by {
        assert(isa::p2(0) == 1);
    }
    if sub {
        // not_vec = ones - y = p - 1 - y
        assert(isa::not_vec(n, y as int) == p - 1 - y);
        assert(isa::trunc(n, p - 1 - y) == p - 1 - y) by {
            lemma_trunc_small(n, p - 1 - y);
        }
        assert(isa::trunc(n, x as int + (p - 1 - y) + 1) == (x as int - y as int) % p) by {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(x as int - y as int, p);
        }
    } else {
        assert(isa::trunc(n, x as int + y as int + 0) == (x as int + y as int) % p);
    }
}

/// The width of `sf` is 32 or 64.
pub proof fn lemma_bits(sf: isa::Width)
    ensures
        bits(sf) == 32 || bits(sf) == 64,
        (sf is W32) <==> bits(sf) == 32,
{
}

/// The bitwise operation of `and`, `or`, `xor` on two words.
pub open spec fn logic_val(o: lir::IBin, x: u64, y: u64) -> u64 {
    match o {
        lir::IBin::And => x & y,
        lir::IBin::Or => x | y,
        _ => x ^ y,
    }
}

/// `and`, `orr`, `eor` (shifted register, no shift) on `x0` and `x1` at width
/// `sf`: the bitwise operation on the operands.
#[verifier::rlimit(200)]
pub proof fn lemma_step_logic(s: isa::State, sf: isa::Width, o: lir::IBin, x: u64, y: u64)
    requires
        isa::wf(s),
        super::templates::logic_of(o) is Some,
        s.r[0] == x,
        s.r[1] == y,
        x < isa::p2(bits(sf)),
        y < isa::p2(bits(sf)),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::int_op_instr(o, sf)) == Some(
            wrote_x0(s, logic_val(o, x, y) as int, bits(sf)),
        ),
        logic_val(o, x, y) < isa::p2(bits(sf)),
{
    let n = bits(sf);
    lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    lemma_pc4(s.pc);
    lemma_trunc_small(n, x as int);
    lemma_trunc_small(n, y as int);
    assert(isa::lsl(n, y as int, 0) == y as int) by {
        assert(isa::p2(0) == 1);
    }
    assert(isa::lsl(n, x as int, 0) == x as int);
    // the result is below 2^n
    if n == 32 {
        assert((x & y) < 0x1_0000_0000u64) by (bit_vector)
            requires
                x < 0x1_0000_0000u64,
                y < 0x1_0000_0000u64,
        ;
        assert((x | y) < 0x1_0000_0000u64) by (bit_vector)
            requires
                x < 0x1_0000_0000u64,
                y < 0x1_0000_0000u64,
        ;
        assert((x ^ y) < 0x1_0000_0000u64) by (bit_vector)
            requires
                x < 0x1_0000_0000u64,
                y < 0x1_0000_0000u64,
        ;
    }
    assert(isa::and_vec(x as int, y as int) == (x & y) as int);
    assert(isa::or_vec(x as int, y as int) == (x | y) as int);
    assert(isa::eor_vec(x as int, y as int) == (x ^ y) as int);
    lemma_trunc_small(n, logic_val(o, x, y) as int);
}

/// `mul x0, x0, x1` (`madd x0, x0, x1, xzr`) at width `sf`: the low `n` bits
/// of the product.
#[verifier::rlimit(200)]
pub proof fn lemma_step_mul(s: isa::State, sf: isa::Width, x: u64, y: u64)
    requires
        isa::wf(s),
        s.r[0] == x,
        s.r[1] == y,
        x < isa::p2(bits(sf)),
        y < isa::p2(bits(sf)),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        isa::step(s, super::templates::int_op_instr(lir::IBin::Mul, sf)) == Some(
            wrote_x0(s, (x as int * y as int) % isa::p2(bits(sf)), bits(sf)),
        ),
{
    let n = bits(sf);
    lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    lemma_pc4(s.pc);
    lemma_trunc_small(n, x as int);
    lemma_trunc_small(n, y as int);
    let p = isa::p2(n);
    // x_set truncates the already truncated product
    assert(isa::trunc(n, 0 + x as int * y as int) == (x as int * y as int) % p);
    vstd::arithmetic::div_mod::lemma_mod_bound(x as int * y as int, p);
    lemma_trunc_small(n, (x as int * y as int) % p);
}

/// `lslv`, `lsrv`, `asrv` of `x0` by `x1` at width `sf`: the count is `x1`
/// modulo the width, and the result is the shift of `x0`.
#[verifier::rlimit(300)]
pub proof fn lemma_step_shift(s: isa::State, sf: isa::Width, o: lir::IBin, x: u64, y: u64)
    requires
        isa::wf(s),
        super::templates::shift_of(o) is Some,
        s.r[0] == x,
        s.r[1] == y,
        x < isa::p2(bits(sf)),
        y < isa::p2(bits(sf)),
        s.pc as int + 4 < 0x1_0000_0000_0000_0000,
    ensures
        ({
            let k = (y as int % bits(sf) as int) as nat;
            isa::step(s, super::templates::int_op_instr(o, sf)) == Some(
                wrote_x0(
                    s,
                    match o {
                        lir::IBin::Shl => (x as int * isa::p2(k)) % isa::p2(bits(sf)),
                        lir::IBin::ShrU => x as int / isa::p2(k),
                        _ => isa::trunc(bits(sf), isa::sint(bits(sf), x as int) / isa::p2(k)),
                    },
                    bits(sf),
                ),
            )
        }),
{
    let n = bits(sf);
    lemma_bits(sf);
    super::memlemmas::lemma_p2_consts();
    lemma_pc4(s.pc);
    lemma_trunc_small(n, x as int);
    lemma_trunc_small(n, y as int);
    let k = (y as int % n as int) as nat;
    let p = isa::p2(n);
    assert(isa::trunc(n, x as int * isa::p2(k)) == (x as int * isa::p2(k)) % p);
    // the shifted value of a logical shift right is at most x, so below 2^n
    if o is ShrU {
        vstd::arithmetic::power2::lemma_pow2_pos(k);
        assert(isa::p2(k) >= 1);
        assert(x as int / isa::p2(k) <= x as int) by (nonlinear_arith)
            requires
                isa::p2(k) >= 1,
                x as int >= 0,
        ;
        assert(0 <= x as int / isa::p2(k)) by (nonlinear_arith)
            requires
                isa::p2(k) >= 1,
                x as int >= 0,
        ;
    }
}

} // verus!

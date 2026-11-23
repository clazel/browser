//! **The validator's bounds-check sequence, run** (`clazel_codecheck::spec::
//! check_seq`, with the index in `rcx`, `rdx` and `rax` as scratch): from a
//! state with the index in `rcx`, it falls through to its end exactly when
//! `index + n <= bound`, and otherwise leaves through one of its two exits.
//! Either way registers other than the scratch ones, and memory, are as they
//! were.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cfalg::*;
#[cfg(verus_only)]
use crate::cfleaf::*;
#[cfg(verus_only)]
use crate::cfmemlens::*;
#[cfg(verus_only)]
use crate::cfmemrel::*;
#[cfg(verus_only)]
use crate::cfmemsteps::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cfsteps::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What a stretch of code keeps of the machine: the memory, the context
/// register, the stack pointer, `rsi` and `rdi`, and being a well-formed
/// state.
pub open spec fn keeps(m: x64::State, m2: x64::State) -> bool {
    m2.mem == m.mem && x64::wf(m2) && m2.rgf[15] == m.rgf[15] && m2.rgf[4] == m.rgf[4]
        && m2.rgf[6] == m.rgf[6] && m2.rgf[7] == m.rgf[7]
}

/// The instruction at index `j` of `code` is what `fetch` finds at the
/// offset of the bytes before it.
pub proof fn lemma_fetch_idx(code: Seq<x64::Instr>, j: int)
    requires
        0 <= j < code.len(),
    ensures
        fetch(code, code_len(code.take(j)) as int) == Some(code[j]),
{
    let pre = code.take(j);
    let post = seq![code[j]] + code.skip(j + 1);
    assert(code =~= pre + post);
    assert(code.skip(j) =~= post);
    super::cfsteps::lemma_fetch_append_r(pre, post, code_len(pre) as int);
    assert(fetch(post, 0) == Some(code[j]));
}

/// The bytes before instruction `j + 1` are those before `j` and `j`.
pub proof fn lemma_take_len(code: Seq<x64::Instr>, j: int)
    requires
        0 <= j < code.len(),
    ensures
        code_len(code.take(j + 1)) == code_len(code.take(j)) + x64::instr_len(code[j]),
{
    assert(code.take(j + 1) =~= code.take(j) + seq![code[j]]);
    super::runseq::lemma_code_len_append(code.take(j), seq![code[j]]);
    super::runseq::lemma_code_len_one(code[j]);
}

/// One more step of a run: if `s` is reached, the instruction at `rip` is
/// `i`, and it steps to `s1`, then `s1` is reached.
pub proof fn lemma_reach_step(
    cu: spec_fn(nat) -> nat,
    code: Seq<x64::Instr>,
    base: int,
    s0: x64::State,
    s: x64::State,
    i: x64::Instr,
    s1: x64::State,
)
    requires
        reaches(cu, code, base, s0, s),
        fetch(code, s.rip - base) == Some(i),
        x64::step(cu, s, i) == Some(s1),
    ensures
        reaches(cu, code, base, s0, s1),
{
    let n = choose|n: nat| steps(cu, code, base, s0, n) == Some(s);
    reveal_with_fuel(steps, 2);
    assert(steps(cu, code, base, s, 1) == Some(s1));
    lemma_steps_trans(cu, code, base, s0, s, s1, n, 1);
}

/// A read through the context register at an offset below the context's
/// size, with no wrap-around.
pub proof fn lemma_ctx_ea(m: x64::State, off: int)
    requires
        ctx_ok(m),
        0 <= off < 512,
    ensures
        x64::eff_addr(
            m,
            x64::Mem { base: abi::ctx_reg(), index: None, disp: off as i32 },
        ) == ctx_of(m) + off,
{
    super::memlemmas::lemma_p2_consts();
    super::steps::lemma_abi_consts();
    assert((off as i32) as int == off);
    let x = ctx_of(m) + off;
    assert(0 <= x && x < 0x8000_0000_0000 + 512);
    assert(x64::loghead(64, x) == x);
    assert(x64::logext(64, x) == x);
}

/// What the region table gives for region `k`: the base and the bound, as
/// words below `2^64`, readable through the context register.
pub proof fn lemma_table_words(lay: lir::Layout, m: x64::State, k: nat)
    requires
        x64::wf(m),
        ctx_ok(m),
        table_ok(lay, m),
        k < lay.len(),
    ensures
        x64::read_mem(m.mem, x64::eff_addr(m, base_mem(k)), 8) == Some(lay[k as int].base as int),
        x64::read_mem(m.mem, x64::eff_addr(m, clazel_codecheck::spec::bound_mem(k as int)), 8)
            == Some(lay[k as int].bound as int),
        lay[k as int].base < 0x1_0000_0000_0000_0000,
        lay[k as int].bound < 0x1_0000_0000_0000_0000,
{
    super::steps::lemma_abi_consts();
    assert(abi::base_off(k as int) == 16 * k && abi::bound_off(k as int) == 16 * k + 8);
    assert(k < 16);
    lemma_ctx_ea(m, abi::base_off(k as int));
    lemma_ctx_ea(m, abi::bound_off(k as int));
    assert(base_mem(k).disp as int == 16 * k) by {
        assert((abi::base_off(k as int) as i32) as int == abi::base_off(k as int));
    }
    assert(clazel_codecheck::spec::bound_mem(k as int).disp as int == 16 * k + 8) by {
        assert((abi::bound_off(k as int) as i32) as int == abi::bound_off(k as int));
    }
    assert(x64::eff_addr(m, base_mem(k)) == ctx_of(m) + abi::base_off(k as int));
    assert(x64::eff_addr(m, clazel_codecheck::spec::bound_mem(k as int)) == ctx_of(m)
        + abi::bound_off(k as int));
    let lk = lay[k as int];
    assert(x64::read_mem(m.mem, ctx_of(m) + abi::base_off(k as int), 8) == Some(lk.base as int));
    assert(x64::read_mem(m.mem, ctx_of(m) + abi::bound_off(k as int), 8) == Some(lk.bound as int));
    lemma_read_mem_range(m.mem, ctx_of(m) + abi::base_off(k as int), 8, lk.base as int);
    lemma_read_mem_range(m.mem, ctx_of(m) + abi::bound_off(k as int), 8, lk.bound as int);
    super::memlemmas::lemma_p2_consts();
    assert(vstd::arithmetic::power2::pow2(64) == 0x1_0000_0000_0000_0000);
}

/// A state with the memory and `rip`'s canonicity of a well-formed one, 16
/// general and 16 XMM registers, is well formed.
pub proof fn lemma_wf_like(m: x64::State, s: x64::State)
    requires
        x64::wf(m),
        s.mem == m.mem,
        s.rgf.len() == 16,
        s.xmm.len() == 16,
        x64::canonical(s.rip),
    ensures
        x64::wf(s),
{
}

/// The offsets of the bounds-check sequence's instructions: they begin 0, 3,
/// 10, 16, 24, 30, 35 and 43 bytes in, and it is 47 bytes long; the part from
/// the fourth instruction on is 31, from the sixth 17.
pub proof fn lemma_check_offsets(c: clazel_codecheck::spec::Chk)
    requires
        c.i == rcx() && c.t == rdx() && c.z == rax() && 0 <= c.k < 16,
    ensures
        ({
            let cs = clazel_codecheck::spec::check_seq(c);
            &&& cs.len() == 8
            &&& code_len(cs.take(0)) == 0
            &&& code_len(cs.take(1)) == 3
            &&& code_len(cs.take(2)) == 10
            &&& code_len(cs.take(3)) == 16
            &&& code_len(cs.take(4)) == 24
            &&& code_len(cs.take(5)) == 30
            &&& code_len(cs.take(6)) == 35
            &&& code_len(cs.take(7)) == 43
            &&& code_len(cs) == 47
            &&& code_len(cs.skip(3)) == 31
            &&& code_len(cs.skip(5)) == 17
        }),
{
    let cs = clazel_codecheck::spec::check_seq(c);
    lemma_check_instr_lens(c);
    assert(cs.len() == 8);
    assert(cs.take(0) =~= Seq::<x64::Instr>::empty());
    assert(code_len(Seq::<x64::Instr>::empty()) == 0);
    assert(cs[0] == clazel_codecheck::spec::check_instr(0, c));
    assert(cs[1] == clazel_codecheck::spec::check_instr(1, c));
    assert(cs[2] == clazel_codecheck::spec::check_instr(2, c));
    assert(cs[3] == clazel_codecheck::spec::check_instr(3, c));
    assert(cs[4] == clazel_codecheck::spec::check_instr(4, c));
    assert(cs[5] == clazel_codecheck::spec::check_instr(5, c));
    assert(cs[6] == clazel_codecheck::spec::check_instr(6, c));
    assert(cs[7] == clazel_codecheck::spec::check_instr(7, c));
    lemma_take_len(cs, 0);
    lemma_take_len(cs, 1);
    lemma_take_len(cs, 2);
    lemma_take_len(cs, 3);
    lemma_take_len(cs, 4);
    lemma_take_len(cs, 5);
    lemma_take_len(cs, 6);
    lemma_take_len(cs, 7);
    assert(cs.take(8) =~= cs);
    assert(cs =~= cs.take(3) + cs.skip(3));
    assert(cs =~= cs.take(5) + cs.skip(5));
    super::runseq::lemma_code_len_append(cs.take(3), cs.skip(3));
    super::runseq::lemma_code_len_append(cs.take(5), cs.skip(5));
}

} // verus!

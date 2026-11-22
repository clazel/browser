//! The lengths of the memory and `br_table` templates: each instruction's
//! length is a number, so the displacements of the check's exits and of the
//! `br_table` chain are, and fit a `rel32`.

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use crate::cflens::*;
#[cfg(verus_only)]
use crate::cfspec::*;
#[cfg(verus_only)]
use crate::cftemplates::*;
#[cfg(verus_only)]
use crate::templates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A memory instruction with a 64-bit operand size and a 32-bit displacement
/// is 8 bytes (`REX`, opcode, ModR/M, SIB, displacement).
pub proof fn lemma_len_rm64(i: x64::Instr)
    requires
        (i is MovLoad && i->MovLoad_sz is W64) || (i is MovStore && i->MovStore_sz is W64),
    ensures
        x64::instr_len(i) == 8,
{
    lemma_le_bytes_len(match i {
        x64::Instr::MovLoad { mem, .. } => mem.disp as int,
        x64::Instr::MovStore { mem, .. } => mem.disp as int,
        _ => 0,
    }, 4);
}

/// The lengths of the instructions the memory templates use.
pub proof fn lemma_mem_instr_lens(j: nat, k: nat)
    ensures
        x64::instr_len(load_slot(rcx(), j)) == 8,
        x64::instr_len(load_slot(rdi(), j)) == 8,
        x64::instr_len(load_slot(rax(), j)) == 8,
        x64::instr_len(store_slot(j, rax())) == 8,
        x64::instr_len(
            x64::Instr::MovLoad { sz: x64::Size::W64, dst: rsi(), mem: base_mem(k) },
        ) == 8,
        x64::instr_len(
            x64::Instr::MovLoad { sz: x64::Size::W64, dst: rax(), mem: ix_mem() },
        ) == 8,
        x64::instr_len(
            x64::Instr::MovLoad { sz: x64::Size::W32, dst: rax(), mem: ix_mem() },
        ) == 7,
        x64::instr_len(
            x64::Instr::MovStore { sz: x64::Size::W64, mem: ix_mem(), src: rdi() },
        ) == 8,
        x64::instr_len(
            x64::Instr::MovStore { sz: x64::Size::W32, mem: ix_mem(), src: rdi() },
        ) == 7,
{
    lemma_len_rm64(load_slot(rcx(), j));
    lemma_len_rm64(load_slot(rdi(), j));
    lemma_len_rm64(load_slot(rax(), j));
    lemma_len_rm64(store_slot(j, rax()));
    lemma_len_rm64(x64::Instr::MovLoad { sz: x64::Size::W64, dst: rsi(), mem: base_mem(k) });
    lemma_len_rm64(x64::Instr::MovLoad { sz: x64::Size::W64, dst: rax(), mem: ix_mem() });
    lemma_len_rm64(x64::Instr::MovStore { sz: x64::Size::W64, mem: ix_mem(), src: rdi() });
    lemma_le_bytes_len(0, 4);
    assert(x64::encode(x64::Instr::MovLoad { sz: x64::Size::W32, dst: rax(), mem: ix_mem() }).len()
        == 7);
    assert(x64::encode(x64::Instr::MovStore { sz: x64::Size::W32, mem: ix_mem(), src: rdi() }).len()
        == 7);
}

/// The lengths of the instructions of the bounds-check sequence (`rcx`,
/// `rdx`, `rax`, region `k`): 3, 7, 6, 8, 6, 5, 8, 4 bytes.
pub proof fn lemma_check_instr_lens(c: clazel_codecheck::spec::Chk)
    requires
        c.i == rcx() && c.t == rdx() && c.z == rax() && 0 <= c.k < 16,
    ensures
        x64::instr_len(clazel_codecheck::spec::check_instr(0, c)) == 3,
        x64::instr_len(clazel_codecheck::spec::check_instr(1, c)) == 7,
        x64::instr_len(clazel_codecheck::spec::check_instr(2, c)) == 6,
        x64::instr_len(clazel_codecheck::spec::check_instr(3, c)) == 8,
        x64::instr_len(clazel_codecheck::spec::check_instr(4, c)) == 6,
        x64::instr_len(clazel_codecheck::spec::check_instr(5, c)) == 5,
        x64::instr_len(clazel_codecheck::spec::check_instr(6, c)) == 8,
        x64::instr_len(clazel_codecheck::spec::check_instr(7, c)) == 4,
{
    lemma_le_bytes_len(c.n as i32 as int, 4);
    lemma_jcc_len(2, c.r1 as int);
    lemma_jcc_len(7, c.r2 as int);
    lemma_le_bytes_len(clazel_codecheck::spec::bound_mem(c.k).disp as int, 4);
    lemma_le_bytes_len(0, 4);
    let i3 = clazel_codecheck::spec::check_instr(3, c);
    let i6 = clazel_codecheck::spec::check_instr(6, c);
    assert(x64::encode(i3).len() == 8);
    assert(x64::encode(i6).len() == 8);
    assert(x64::encode(clazel_codecheck::spec::check_instr(0, c)).len() == 3);
    assert(x64::encode(clazel_codecheck::spec::check_instr(1, c)).len() == 7);
    assert(x64::encode(clazel_codecheck::spec::check_instr(5, c)).len() == 5);
    assert(x64::encode(clazel_codecheck::spec::check_instr(7, c)).len() == 4);
}

/// The exit sequence is 14 bytes (5, 8, 1).
pub proof fn lemma_exit_seq_len(c: u32)
    ensures
        code_len(exit_seq(c)) == 14,
{
    lemma_le_bytes_len(c as int, 4);
    lemma_le_bytes_len(abi::exit_code_off(), 4);
    let i0 = x64::Instr::MovImm32 { dst: rax(), imm_u32: c };
    let i1 = x64::Instr::MovStore {
        sz: x64::Size::W64,
        mem: x64::Mem { base: abi::ctx_reg(), index: None, disp: abi::exit_code_off() as i32 },
        src: rax(),
    };
    lemma_len_rm64(i1);
    assert(x64::encode(i0).len() == 5);
    assert(x64::encode(x64::Instr::Ret).len() == 1);
    super::runseq::lemma_len3(i0, i1, x64::Instr::Ret);
    assert(exit_seq(c) =~= seq![i0, i1, x64::Instr::Ret]);
}

} // verus!

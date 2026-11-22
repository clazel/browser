//! Small facts about the memory and branch templates that the validator and
//! LIR's semantics need, each a proven theorem about a concrete input, so that
//! a mutation of the template that breaks it has a **certificate**
//! (`mutations.json`, `xtask/src/mutate.rs`): the validator's access rule
//! admits the access a memory instruction makes after its check, an access
//! moves as many bytes as its type has, a failing `bounds_check` exits with its
//! own code, a `br_table` entry branches on equal, a branch's displacement is in
//! words, and `br_if` branches on a nonzero condition. The A64 counterpart of
//! [`crate::cfmemvalid`].

#[allow(unused_imports)]
use super::spec::*;
#[cfg(verus_only)]
use super::cfmemsteps::*;
#[cfg(verus_only)]
use super::cfspec::*;
#[cfg(verus_only)]
use super::cftemplates::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What the validator knows after `ldr x3, [x28, #16 k]` and the bounds check
/// of `n` bytes on `x1` (`clazel_codecheck::a64::spec::check_facts`): `x3` is
/// region `k`'s base, `x0` and `x2` are unknown, `x1` is checked for `n` bytes.
pub open spec fn after_check(k: int, n: int) -> Seq<clazel_codecheck::a64::spec::Binding> {
    seq![
        clazel_codecheck::a64::spec::Binding {
            reg: 3,
            fact: clazel_codecheck::a64::spec::Fact::Base(k),
        },
        clazel_codecheck::a64::spec::Binding {
            reg: 2,
            fact: clazel_codecheck::a64::spec::Fact::Unknown,
        },
        clazel_codecheck::a64::spec::Binding {
            reg: 0,
            fact: clazel_codecheck::a64::spec::Fact::Unknown,
        },
        clazel_codecheck::a64::spec::Binding {
            reg: 1,
            fact: clazel_codecheck::a64::spec::Fact::Idx(k, n),
        },
    ]
}

/// **The validator accepts a load's access**: the facts after the check admit the
/// template's `ldr x0, [x3, x1]` of 8 bytes in region 0.
pub proof fn lemma_load_access_accepted()
    ensures
        clazel_codecheck::a64::spec::access_ok(
            after_check(0, 8),
            clazel_codecheck::a64::spec::mem_access(
                mem_tail(MemOp::Load { region: 0, ty: MTy::I64 }, 0, 1)[0],
            )->Some_0,
        ),
{
    reveal_with_fuel(clazel_codecheck::a64::spec::fact_of, 6);
}

/// **The validator accepts a store's access**: the same for `str x4, [x3, x1]`.
pub proof fn lemma_store_access_accepted()
    ensures
        clazel_codecheck::a64::spec::access_ok(
            after_check(0, 8),
            clazel_codecheck::a64::spec::mem_access(
                mem_tail(MemOp::Store { region: 0, ty: MTy::I64 }, 0, 2)[0],
            )->Some_0,
        ),
{
    reveal_with_fuel(clazel_codecheck::a64::spec::fact_of, 6);
}

/// An access of a type's width moves as many bytes as the type has (so it is
/// within the `n` bytes the check admitted).
pub proof fn lemma_mty_sf_bytes(ty: MTy)
    ensures
        sf_bytes(mty_sf(ty)) == ty.size(),
{
}

/// The access size of a type is LIR's.
pub proof fn lemma_mty_size_is_lir(ty: MTy)
    ensures
        lir::ty_size(ty.lir_ty()) == ty.size(),
{
}

/// A `bounds_check`'s stub exits with the instruction's own code.
pub proof fn lemma_bc_exit_code(region: usize, size: usize, code: u32)
    requires
        code < 0x1_0000,
    ensures
        mem_exit_code(MemOp::BoundsCheck { region, size, code }) as u32 == code,
{
}

/// The chain's entry branches on equal (`b.eq`: condition 0).
pub proof fn lemma_brt_cond(i: nat, rel: int)
    ensures
        brt_entry(i, rel)[2]->BCond_cond == 0,
{
}

/// A branch's displacement is in words: `b` 8 bytes on has `imm26` 2.
pub proof fn lemma_b_words()
    ensures
        b_i(8)->B_imm26 == 2,
{
}

/// `br_if` branches on a nonzero condition (`cbnz`).
pub proof fn lemma_brif_branches_on_nonzero()
    ensures
        ctmpl(Node::BrIf(0), 0, 1, seq![8int])[1]->CompareBranch_iszero == false,
{
}

} // verus!

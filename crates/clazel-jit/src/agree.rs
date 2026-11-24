//! How the LIR states before and after an instruction relate slot by slot
//! ([`slots_agree_except`], [`slots_agree`]), for each way an instruction
//! changes the locals and the operand stack: push a value, replace the top
//! `k` values by one, drop the top, set a local. They are what the template
//! proofs feed to the skeleton.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Pushing `v`: the new top slot (`nl + h`) is the only slot that changes, and
/// it holds `v`'s word.
pub proof fn lemma_agree_push(a: lir::St, a2: lir::St, nl: nat, h: nat, v: lir::Val)
    requires
        a.stack.len() == h,
        a.locals.len() == nl,
        nl + h + 1 <= max_slots(),
        a2 == a.with_stack(a.stack.push(v)),
    ensures
        super::rel::slots_agree_except(a, a2, nl, nl + h),
        lir::val_bits(slot_val(a2, nl, nl + h)) == lir::val_bits(v),
{
    assert(a2.stack.len() == h + 1);
    assert forall|j: nat| j < nl + a2.stack.len() && j != nl + h implies j < nl + a.stack.len()
        && lir::val_bits(#[trigger] slot_val(a2, nl, j)) == lir::val_bits(slot_val(a, nl, j)) by {
        if j >= nl {
            assert(a2.stack[(j - nl) as int] == a.stack[(j - nl) as int]);
        }
    }
    assert(a2.stack[h as int] == v);
}

/// Replacing the top `k` values by one value `v`: the slot `nl + h - k` is the
/// only one that changes, and it holds `v`'s word.
pub proof fn lemma_agree_replace(
    a: lir::St,
    a2: lir::St,
    nl: nat,
    h: nat,
    k: nat,
    v: lir::Val,
)
    requires
        a.stack.len() == h,
        a.locals.len() == nl,
        1 <= k <= h,
        nl + (h - k) + 1 <= max_slots(),
        a2 == a.with_stack(lir::below(a.stack, k).push(v)),
    ensures
        super::rel::slots_agree_except(a, a2, nl, (nl + h - k) as nat),
        lir::val_bits(slot_val(a2, nl, (nl + h - k) as nat)) == lir::val_bits(v),
{
    let hk = (h - k) as nat;
    assert(a2.stack.len() == hk + 1);
    assert(lir::below(a.stack, k) =~= a.stack.take(hk as int));
    assert forall|j: nat|
        j < nl + a2.stack.len() && j != (nl + h - k) as nat implies j < nl + a.stack.len()
        && lir::val_bits(#[trigger] slot_val(a2, nl, j)) == lir::val_bits(slot_val(a, nl, j)) by {
        if j >= nl {
            assert(a2.stack[(j - nl) as int] == a.stack[(j - nl) as int]);
        }
    }
    assert(a2.stack[hk as int] == v);
}

/// Dropping the top value, or any change to the stack that keeps a prefix:
/// every slot of `a2` is a slot of `a`.
pub proof fn lemma_agree_drop(a: lir::St, a2: lir::St, nl: nat, h: nat)
    requires
        a.stack.len() == h,
        a.locals.len() == nl,
        1 <= h,
        nl + h <= max_slots(),
        a2 == a.with_stack(a.stack.drop_last()),
    ensures
        super::rel::slots_agree(a, a2, nl),
{
    assert forall|j: nat| j < nl + a2.stack.len() implies j < nl + a.stack.len() && lir::val_bits(
        #[trigger] slot_val(a2, nl, j),
    ) == lir::val_bits(slot_val(a, nl, j)) by {
        if j >= nl {
            assert(a2.stack[(j - nl) as int] == a.stack[(j - nl) as int]);
        }
    }
}

/// `local.set x`: the stack loses its top, local `x` takes its value. The only
/// slot that changes is `x`.
pub proof fn lemma_agree_set(a: lir::St, a2: lir::St, nl: nat, h: nat, x: nat)
    requires
        a.stack.len() == h,
        a.locals.len() == nl,
        1 <= h,
        x < nl,
        nl + h <= max_slots(),
        a2 == (lir::St {
            stack: a.stack.drop_last(),
            locals: a.locals.update(x as int, a.stack.last()),
            mem: a.mem,
        }),
    ensures
        super::rel::slots_agree_except(a, a2, nl, x),
        lir::val_bits(slot_val(a2, nl, x)) == lir::val_bits(slot_val(a, nl, (nl + h - 1) as nat)),
{
    assert forall|j: nat| j < nl + a2.stack.len() && j != x implies j < nl + a.stack.len()
        && lir::val_bits(#[trigger] slot_val(a2, nl, j)) == lir::val_bits(slot_val(a, nl, j)) by {
        if j >= nl {
            assert(a2.stack[(j - nl) as int] == a.stack[(j - nl) as int]);
        } else {
            assert(a2.locals[j as int] == a.locals[j as int]);
        }
    }
    assert(a.stack.last() == a.stack[h - 1]);
}

/// `local.tee x`: the stack is unchanged, local `x` takes the top's value.
pub proof fn lemma_agree_tee(a: lir::St, a2: lir::St, nl: nat, h: nat, x: nat)
    requires
        a.stack.len() == h,
        a.locals.len() == nl,
        1 <= h,
        x < nl,
        nl + h <= max_slots(),
        a2 == a.with_locals(a.locals.update(x as int, a.stack.last())),
    ensures
        super::rel::slots_agree_except(a, a2, nl, x),
        lir::val_bits(slot_val(a2, nl, x)) == lir::val_bits(slot_val(a, nl, (nl + h - 1) as nat)),
{
    assert forall|j: nat| j < nl + a2.stack.len() && j != x implies j < nl + a.stack.len()
        && lir::val_bits(#[trigger] slot_val(a2, nl, j)) == lir::val_bits(slot_val(a, nl, j)) by {
        if j < nl {
            assert(a2.locals[j as int] == a.locals[j as int]);
        }
    }
    assert(a.stack.last() == a.stack[h - 1]);
}

/// Replacing the top by a value with the same word changes no slot's word.
pub proof fn lemma_agree_same_word(a: lir::St, a2: lir::St, nl: nat, h: nat, v: lir::Val)
    requires
        a.stack.len() == h,
        a.locals.len() == nl,
        1 <= h,
        nl + h <= max_slots(),
        lir::val_bits(v) == lir::val_bits(a.stack.last()),
        a2 == a.with_stack(lir::below(a.stack, 1).push(v)),
    ensures
        super::rel::slots_agree(a, a2, nl),
{
    assert(lir::below(a.stack, 1) =~= a.stack.take((h - 1) as int));
    assert(a2.stack.len() == h);
    assert forall|j: nat| j < nl + a2.stack.len() implies j < nl + a.stack.len() && lir::val_bits(
        #[trigger] slot_val(a2, nl, j),
    ) == lir::val_bits(slot_val(a, nl, j)) by {
        if j >= nl {
            if j - nl == h - 1 {
                assert(a2.stack[(h - 1) as int] == v);
                assert(a.stack.last() == a.stack[(h - 1) as int]);
            } else {
                assert(a2.stack[(j - nl) as int] == a.stack[(j - nl) as int]);
            }
        }
    }
}

/// A state is related to itself, to the same machine state: no change.
pub proof fn lemma_agree_refl(a: lir::St, nl: nat)
    requires
        a.locals.len() == nl,
        nl + a.stack.len() <= max_slots(),
    ensures
        super::rel::slots_agree(a, a, nl),
{
}

/// `preserved` holds between a machine state and itself.
pub proof fn lemma_preserved_refl(m: x64::State)
    requires
        m.rgf.len() == 16,
    ensures
        preserved(m, m),
{
}

} // verus!

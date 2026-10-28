//! Facts about `value` and `limb_pow` that the loop invariants of the
//! arithmetic use.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `base^i` is positive.
pub proof fn lemma_limb_pow_pos(i: nat)
    ensures
        limb_pow(i) > 0,
    decreases i,
{
    if i > 0 {
        lemma_limb_pow_pos((i - 1) as nat);
        assert(limb_pow(i) == limb_pow((i - 1) as nat) * base());
        assert(limb_pow((i - 1) as nat) * base() > 0) by (nonlinear_arith)
            requires
                limb_pow((i - 1) as nat) > 0,
                base() > 0,
        ;
    }
}

/// `base^(i + 1) = base^i * base`.
pub proof fn lemma_limb_pow_succ(i: nat)
    ensures
        limb_pow(i + 1) == limb_pow(i) * base(),
{
}

/// A sequence of `n` limbs is below `base^n`.
pub proof fn lemma_value_bound(s: Seq<u64>)
    ensures
        value(s) < limb_pow(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_value_bound(d);
        let p = limb_pow(d.len());
        let l = s.last() as nat;
        assert(limb_pow(s.len()) == p * base());
        assert(value(s) == value(d) + l * p);
        assert(value(s) < p * base()) by (nonlinear_arith)
            requires
                value(d) < p,
                l < base(),
                value(s) == value(d) + l * p,
        ;
    }
}

/// Appending a limb adds it at the next weight.
pub proof fn lemma_value_push(s: Seq<u64>, x: u64)
    ensures
        value(s.push(x)) == value(s) + (x as nat) * limb_pow(s.len()),
{
    assert(s.push(x).drop_last() =~= s);
}

/// The first `i + 1` limbs are the first `i` plus limb `i` at weight
/// `base^i`.
pub proof fn lemma_value_take_succ(s: Seq<u64>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        value(s.take(i + 1)) == value(s.take(i)) + (s[i] as nat) * limb_pow(i as nat),
{
    let t = s.take(i + 1);
    assert(t.drop_last() =~= s.take(i));
    assert(t.last() == s[i]);
}

/// A whole sequence is its own `take`.
pub proof fn lemma_take_all(s: Seq<u64>)
    ensures
        s.take(s.len() as int) =~= s,
{
}

/// `value` of the empty sequence is zero.
pub proof fn lemma_value_empty()
    ensures
        value(Seq::<u64>::empty()) == 0,
{
}

/// The number of `k` zero limbs is zero.
pub proof fn lemma_value_zeros(s: Seq<u64>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] == 0,
    ensures
        value(s) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert(forall|i: int| 0 <= i < d.len() ==> d[i] == 0);
        lemma_value_zeros(d);
    }
}

} // verus!

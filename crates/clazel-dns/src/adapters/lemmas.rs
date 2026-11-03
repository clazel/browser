//! Facts the executable adapter-buffer reader needs about the spec: how
//! large a little-endian field can be.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `n` octets spell a number below 256^n, little-endian too.
pub proof fn lemma_le_value_bound(s: Seq<u8>)
    ensures
        le_value(s) < crate::lemmas::pow256(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_le_value_bound(s.drop_first());
        assert(le_value(s) == le_value(s.drop_first()) * 256 + s[0] as nat);
        assert(crate::lemmas::pow256(s.len()) == 256 * crate::lemmas::pow256((s.len() - 1) as nat));
    }
}

/// Eight octets hold exactly the values of a `u64`.
pub proof fn lemma_pow256_8()
    ensures
        crate::lemmas::pow256(8) == 0x1_0000_0000_0000_0000,
{
    assert(crate::lemmas::pow256(8) == 0x1_0000_0000_0000_0000) by (compute_only);
}

/// Up to eight octets fit in a `u64`.
pub proof fn lemma_pow256_up_to_8(n: nat)
    requires
        n <= 8,
    ensures
        crate::lemmas::pow256(n) <= 0x1_0000_0000_0000_0000,
    decreases 8 - n,
{
    if n < 8 {
        lemma_pow256_up_to_8(n + 1);
        assert(crate::lemmas::pow256(n + 1) == 256 * crate::lemmas::pow256(n));
        assert(crate::lemmas::pow256(n) >= 1) by {
            crate::lemmas::lemma_pow256_positive(n);
        }
    } else {
        lemma_pow256_8();
    }
}

} // verus!

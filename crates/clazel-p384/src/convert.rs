//! Small conversions the point and scalar code needs: an octet as a
//! residue, and an octet string reduced modulo p or n (Horner's rule over
//! the field operations). Both are proven against [`crate::spec::os2ip`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

use crate::field::Fe;

/// The residue `b`, for an octet `b` (both moduli exceed 255).
pub fn fe_of_byte(w: crate::field::spec::Which, b: u8) -> (r: Fe)
    ensures
        r.which() == w,
        r.val() == b as nat,
{
    let mut o = [0u8;48];
    o[47] = b;
    proof {
        crate::lemmas::lemma_os2ip_last(o@);
        crate::lemmas::lemma_modulus_gt_256(w);
    }
    match Fe::from_octets(w, &o) {
        Some(f) => f,
        // Unreachable: os2ip(o) = b < 256 < modulus.
        None => {
            proof {
                assert(false);
            }
            Fe::one(w)
        },
    }
}

/// The residue 256.
fn fe_256(w: crate::field::spec::Which) -> (r: Fe)
    ensures
        r.which() == w,
        r.val() == 256,
{
    let a = fe_of_byte(w, 255);
    let one = Fe::one(w);
    proof {
        crate::lemmas::lemma_modulus_gt_256(w);
        vstd::arithmetic::div_mod::lemma_small_mod(256nat, crate::field::spec::modulus(w));
    }
    a.add(&one)
}

/// The octets `o[0..k]`, big-endian, as an integer reduced modulo the
/// modulus of `w`: `os2ip(o[0..k]) mod m`. Horner's rule in the field, so
/// that no integer ever exceeds the modulus; this is how a value that may be
/// at least the modulus (the digest `e` against n, `x_R` against n) is
/// reduced.
pub fn reduce_prefix(w: crate::field::spec::Which, o: &[u8], k: usize) -> (r: Fe)
    requires
        k <= o.len(),
    ensures
        r.which() == w,
        r.val() == os2ip(o@.subrange(0, k as int)) % crate::field::spec::modulus(w),
{
    let c256 = fe_256(w);
    let mut acc = fe_of_byte(w, 0);
    let mut i: usize = 0;
    proof {
        assert(o@.subrange(0, 0) =~= Seq::<u8>::empty());
        crate::lemmas::lemma_modulus_gt_256(w);
        vstd::arithmetic::div_mod::lemma_small_mod(0nat, crate::field::spec::modulus(w));
    }
    while i < k
        invariant
            i <= k,
            k <= o.len(),
            acc.which() == w,
            c256.which() == w,
            c256.val() == 256,
            acc.val() == os2ip(o@.subrange(0, i as int)) % crate::field::spec::modulus(w),
        decreases k - i,
    {
        let byte: u8 = match o.get(i) {
            Some(b) => *b,
            None => 0,
        };
        let b = fe_of_byte(w, byte);
        let shifted = acc.mul(&c256);
        let next = shifted.add(&b);
        proof {
            let pre = o@.subrange(0, i as int);
            crate::field::lemmas::lemma_os2ip_push(pre, byte);
            assert(o@.subrange(0, i as int + 1) =~= pre.push(byte));
            crate::lemmas::lemma_modulus_gt_256(w);
            crate::lemmas::lemma_horner_mod(os2ip(pre), byte as nat, crate::field::spec::modulus(w));
        }
        acc = next;
        i = i.saturating_add(1);
    }
    acc
}

} // verus!

//! Adler-32 (RFC 1950 §8.2, and §2.2's "ADLER32" paragraph), proven equal to
//! the fold of [`super::contract::adler_fold`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The modulus: "the largest prime smaller than 65536".
pub const BASE: u32 = 65521;

/// The running sums `(s1, s2)` after `data`, from `(s1, s2)`: "s1 is the sum
/// of all bytes, s2 is the sum of all s1 values. Both sums are done modulo
/// 65521." Both sums start (and stay) below 65521.
pub fn update(s1: u32, s2: u32, data: &[u8]) -> (r: (u32, u32))
    requires
        s1 < 65521,
        s2 < 65521,
    ensures
        r.0 < 65521,
        r.1 < 65521,
        super::contract::adler_update_ensures(s1, s2, data@, r),
{
    let mut a = s1;
    let mut b = s2;
    let mut i: usize = 0;
    proof {
        assert(data@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while i < data.len()
        invariant
            i <= data.len(),
            a < 65521,
            b < 65521,
            (a as nat, b as nat) == super::contract::adler_fold((s1 as nat, s2 as nat), data@.subrange(0, i as int)),
        decreases data.len() - i,
    {
        let byte = match data.get(i) {
            Some(&x) => x,
            None => 0,
        };
        proof {
            let prefix = data@.subrange(0, i as int);
            assert(data@.subrange(0, i as int + 1) =~= prefix.push(data@[i as int]));
            super::adler_proofs::lemma_fold_push((s1 as nat, s2 as nat), prefix, data@[i as int]);
        }
        // Never saturates: a < 65521 and byte < 256.
        a = a.saturating_add(byte as u32) % BASE;
        // Never saturates: b < 65521 and a < 65521.
        b = b.saturating_add(a) % BASE;
        // Never saturates: i < data.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(data@.subrange(0, data.len() as int) =~= data@);
    }
    (a, b)
}

/// The checksum of `data`: "s2*65536 + s1", with "s1 initialized to 1, s2 to
/// zero".
pub fn adler32(data: &[u8]) -> (sum: u32)
    ensures
        super::contract::adler32_ensures(data@, sum),
{
    let (a, b) = update(1, 0, data);
    proof {
        super::adler_proofs::lemma_sums_fold(data@);
    }
    // b < 65521 < 2^16, so the shift loses nothing.
    let r = (b << 16) | a;
    proof {
        assert(r == b * 65536 + a) by (bit_vector)
            requires
                r == (b << 16) | a,
                a < 65521u32,
                b < 65521u32,
            ;
    }
    r
}

} // verus!

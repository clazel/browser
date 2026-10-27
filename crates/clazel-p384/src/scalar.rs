//! The scalar product `[k] P` and the reduction of the digest, executable
//! and proven against [`crate::spec`]. `[k] P` is MSB-first double-and-add
//! over [`crate::point::ec_add`], one bit at a time, exactly the recursion of
//! [`crate::spec::scalar_mul`] (`[2q + b] P = ([q] P + [q] P) + b P`), so the
//! invariant of the loop is that after the top `i` bits the accumulator is
//! the spec's product by the integer those bits make, and nothing about the
//! group law beyond its own definition is used. Every input is public, so
//! the loop branches on the bits.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

use crate::field::Fe;
use crate::point::{ec_add, Point};

/// A bit as a number.
spec fn bit_nat(b: bool) -> nat {
    if b {
        1
    } else {
        0
    }
}

/// The spec's recursion for `[2q + b] P`, in terms of `[q] P`: a doubling,
/// then the addition of `P` if the bit is set.
pub open spec fn mul_step_spec(h: Option<crate::spec::Point>, pt: crate::spec::Point, bit: bool) -> Option<
    crate::spec::Point,
> {
    match h {
        None => None,
        Some(h) => match crate::spec::ec_add(p384(), h, h) {
            None => None,
            Some(twice) => if bit {
                crate::spec::ec_add(p384(), twice, pt)
            } else {
                Some(twice)
            },
        },
    }
}

/// `[2q + b] P` is one step from `[q] P`: the definition of `scalar_mul`,
/// including for `q = 0` and `b = 0`, where both sides are `O` (`O + O = O`).
proof fn lemma_mul_step(q: nat, bit: bool, pt: crate::spec::Point)
    ensures
        crate::spec::scalar_mul(p384(), 2 * q + bit_nat(bit), pt) == mul_step_spec(
            crate::spec::scalar_mul(p384(), q, pt),
            pt,
            bit,
        ),
{
    let k = 2 * q + bit_nat(bit);
    if k == 0 {
        assert(q == 0 && !bit);
        assert(crate::spec::scalar_mul(p384(), 0, pt) == Some(crate::spec::Point::Infinity));
    } else {
        assert(k / 2 == q);
        assert(k % 2 == bit_nat(bit));
    }
}

/// Take the bit worth `t` off `rem`: whether `rem >= t`, and `rem` without it.
fn split_bit(rem: u8, t: u8) -> (r: (bool, u8))
    ensures
        r.0 == (rem >= t),
        rem as nat == r.1 as nat + (if r.0 {
            t as nat
        } else {
            0nat
        }),
        r.1 <= rem,
{
    if rem >= t {
        (true, rem.wrapping_sub(t))
    } else {
        (false, rem)
    }
}

/// One bit: the accumulator `[q] P` becomes `[2q + bit] P`.
fn mul_step(acc: Option<Point>, pt: &Point, bit: bool, Ghost(q): Ghost<nat>) -> (r: Option<Point>)
    requires
        pt.wf(),
        crate::point::opt_wf(&acc),
        crate::point::opt_view(&acc) == crate::spec::scalar_mul(p384(), q, pt@),
    ensures
        crate::point::opt_wf(&r),
        crate::point::opt_view(&r) == crate::spec::scalar_mul(p384(), 2 * q + bit_nat(bit), pt@),
{
    proof {
        lemma_mul_step(q, bit, pt@);
    }
    match acc {
        None => None,
        Some(h) => match ec_add(&h, &h) {
            None => None,
            Some(twice) => if bit {
                ec_add(&twice, pt)
            } else {
                Some(twice)
            },
        },
    }
}

/// Eight bits, most significant first: `[256 q + byte] P` from `[q] P`.
fn mul_byte(acc: Option<Point>, pt: &Point, byte: u8, Ghost(q): Ghost<nat>) -> (r: Option<Point>)
    requires
        pt.wf(),
        crate::point::opt_wf(&acc),
        crate::point::opt_view(&acc) == crate::spec::scalar_mul(p384(), q, pt@),
    ensures
        crate::point::opt_wf(&r),
        crate::point::opt_view(&r) == crate::spec::scalar_mul(p384(), q * 256 + byte as nat, pt@),
{
    let (b7, rem) = split_bit(byte, 128);
    let acc = mul_step(acc, pt, b7, Ghost(q));
    let ghost q1: nat = 2 * q + bit_nat(b7);
    let (b6, rem) = split_bit(rem, 64);
    let acc = mul_step(acc, pt, b6, Ghost(q1));
    let ghost q2: nat = 2 * q1 + bit_nat(b6);
    let (b5, rem) = split_bit(rem, 32);
    let acc = mul_step(acc, pt, b5, Ghost(q2));
    let ghost q3: nat = 2 * q2 + bit_nat(b5);
    let (b4, rem) = split_bit(rem, 16);
    let acc = mul_step(acc, pt, b4, Ghost(q3));
    let ghost q4: nat = 2 * q3 + bit_nat(b4);
    let (b3, rem) = split_bit(rem, 8);
    let acc = mul_step(acc, pt, b3, Ghost(q4));
    let ghost q5: nat = 2 * q4 + bit_nat(b3);
    let (b2, rem) = split_bit(rem, 4);
    let acc = mul_step(acc, pt, b2, Ghost(q5));
    let ghost q6: nat = 2 * q5 + bit_nat(b2);
    let (b1, rem) = split_bit(rem, 2);
    let acc = mul_step(acc, pt, b1, Ghost(q6));
    let ghost q7: nat = 2 * q6 + bit_nat(b1);
    let last = split_bit(rem, 1);
    let b0 = last.0;
    let acc = mul_step(acc, pt, b0, Ghost(q7));
    proof {
        // rem is now 0, and byte = 128 b7 + 64 b6 + ... + b0.
        assert(last.1 == 0);
        assert(2 * q7 + bit_nat(b0) == q * 256 + byte as nat);
    }
    acc
}

/// `[k] pt`, `k` the integer of the 48 big-endian octets: MSB-first
/// double-and-add, [`crate::spec::scalar_mul`].
pub fn scalar_mul(k: &[u8; 48], pt: &Point) -> (r: Option<Point>)
    requires
        pt.wf(),
    ensures
        crate::point::opt_wf(&r),
        crate::point_contract::scalar_mul_ensures(k@, pt@, crate::point::opt_view(&r)),
{
    let mut acc: Option<Point> = Some(Point::Infinity);
    let mut i: usize = 0;
    let ghost mut q: nat = 0;
    proof {
        assert(k@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(crate::spec::scalar_mul(p384(), 0, pt@) == Some(crate::spec::Point::Infinity));
    }
    while i < 48
        invariant
            i <= 48,
            pt.wf(),
            crate::point::opt_wf(&acc),
            q == os2ip(k@.subrange(0, i as int)),
            crate::point::opt_view(&acc) == crate::spec::scalar_mul(p384(), q, pt@),
        decreases 48 - i,
    {
        let byte: u8 = match k.get(i) {
            Some(b) => *b,
            None => 0,
        };
        let next = mul_byte(acc, pt, byte, Ghost(q));
        proof {
            let pre = k@.subrange(0, i as int);
            crate::field::lemmas::lemma_os2ip_push(pre, byte);
            assert(k@.subrange(0, i as int + 1) =~= pre.push(byte));
            q = q * 256 + byte as nat;
        }
        acc = next;
        i = i.saturating_add(1);
    }
    proof {
        assert(k@.subrange(0, 48) =~= k@);
    }
    acc
}

/// FIPS 186-5 §6.4.2 step 3, with the reduction modulo n that step 5 applies:
/// the integer `e` of [`crate::spec::derive_e`] (the leftmost
/// `min(|H|, 384)` bits of the digest, read as an integer, so below 2^384 and
/// possibly at least n) as a residue modulo n.
pub fn derive_e(digest: &[u8]) -> (r: Fe)
    ensures
        r.which() == crate::field::spec::Which::N,
        crate::point_contract::derive_e_ensures(digest@, r.val()),
{
    let k = if digest.len() <= 48 {
        digest.len()
    } else {
        48
    };
    proof {
        crate::lemmas::lemma_derive_e(digest@);
    }
    crate::convert::reduce_prefix(crate::field::spec::Which::N, digest, k)
}

} // verus!

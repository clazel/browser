//! What each executable function above the field is proven to satisfy: the
//! group law, the scalar product, the key decoding and the digest's
//! reduction. As in [`crate::field::contract`], the arguments are the
//! mathematical values the executable objects stand for, so reviewing these
//! predicates and [`crate::spec`] is enough to know what the code
//! guarantees. The statement for `verify` itself is
//! [`crate::contract::verify_ensures`].
//!
//! The executable point [`Point`](crate::point::Point) is either the point at
//! infinity or an affine pair of [`Fe`](crate::field::Fe)s modulo p; its
//! view `a@` is the spec's [`Point`](crate::spec::Point) with those
//! residues as coordinates. `r@` for an `Option<Point>` is the option of the
//! views. A point is *well formed* (`wf`) when its coordinates are residues
//! modulo p (not modulo n); every function below that takes a point requires
//! this and every point it returns is well formed.
//!
//! ```text
//! point::ec_add(&Point, &Point) -> Option<Point>
//!     requires a.wf(), b.wf()
//!     ensures  r.wf(), ec_add_ensures(a@, b@, r@)
//! scalar::scalar_mul(&[u8; 48], &Point) -> Option<Point>
//!     requires pt.wf()
//!     ensures  r.wf(), scalar_mul_ensures(k@, pt@, r@)
//! point::decode_public_key(&[u8]) -> Option<Point>
//!     ensures  r.wf(), decode_public_key_ensures(q@, r@)
//! scalar::derive_e(&[u8]) -> Fe            // e mod n, as a residue mod n
//!     requires digest.len() <= 64
//!     ensures  r.which() == Which::N, derive_e_ensures(digest@, r.val())
//! verify::verify(&[u8], &[u8; 48], &[u8; 48], &[u8]) -> bool
//!     requires verify_requires(digest@)
//!     ensures  verify_ensures(digest@, r@, s@, point@, ok)
//! ```

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `a + b` on P-384: [`crate::spec::ec_add`], SEC 1 §2.2.1, with `None`
/// exactly when the spec's is `None` (an inversion failed).
pub open spec fn ec_add_ensures(a: Point, b: Point, r: Option<Point>) -> bool {
    r == ec_add(p384(), a, b)
}

/// `[k] pt` where `k` is the big-endian octets of the scalar:
/// [`crate::spec::scalar_mul`] of its integer (`os2ip`), MSB-first
/// double-and-add, with `None` exactly when the spec's is `None`.
pub open spec fn scalar_mul_ensures(k: Seq<u8>, pt: Point, r: Option<Point>) -> bool {
    r == scalar_mul(p384(), os2ip(k), pt)
}

/// The key `q` (an ECPoint, SEC 1 §2.3.4) decoded and validated:
/// [`crate::spec::decode_public_key`]. `None` for anything that function
/// refuses (compressed, hybrid, infinity, wrong length, a coordinate at
/// least p, a point off the curve).
pub open spec fn decode_public_key_ensures(q: Seq<u8>, r: Option<Point>) -> bool {
    r == decode_public_key(p384(), q)
}

/// FIPS 186-5 §6.4.2 step 3 followed by the reduction of step 5: the
/// residue modulo n of [`crate::spec::derive_e`]. (`derive_e` itself may be
/// at least n, up to 2^384 - 1, which is more than one residue modulo n; step
/// 5 reduces it, and the code returns the reduced value, which is all step 5
/// uses.)
pub open spec fn derive_e_ensures(h: Seq<u8>, r: nat) -> bool {
    r == derive_e(p384(), h) % p384().n
}

} // verus!

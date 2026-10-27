//! ECDSA signature verification over NIST P-384, FIPS 186-5 §6.4.2, proven
//! to meet [`crate::contract::verify_ensures`], that is [`crate::spec`]'s
//! `ecdsa_verify`, over the six axioms of [`crate::axioms`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

use crate::convert::{fe_of_byte, reduce_prefix};
use crate::field::Fe;
use crate::point::Point;

/// `verify(digest, r, s, point)`: FIPS 186-5 §6.4.2 for P-384.
///
/// `digest` is the hash `H` of step 2 (0 to 64 octets), `r` and `s` are the
/// big-endian octets of the signature integers, and `point` is the key's
/// ECPoint `04 || X || Y`. Returns whether the signature is valid; a key
/// that does not decode (or is not on the curve) is invalid.
pub fn verify(digest: &[u8], r: &[u8; 48], s: &[u8; 48], point: &[u8]) -> (ok: bool)
    requires
        crate::contract::verify_requires(digest@),
    ensures
        crate::contract::verify_ensures(digest@, r@, s@, point@, ok),
{
    // The public key, decoded and validated first (modelling choice 8).
    let q = match crate::point::decode_public_key(point) {
        None => return false,
        Some(q) => q,
    };
    // Step 1: r and s are integers in [1, n - 1]. `from_octets` refuses an
    // integer that is at least n; zero is refused below.
    let r_fe = match Fe::from_octets(crate::field::spec::Which::N, r) {
        None => return false,
        Some(f) => f,
    };
    let s_fe = match Fe::from_octets(crate::field::spec::Which::N, s) {
        None => return false,
        Some(f) => f,
    };
    let zero = fe_of_byte(crate::field::spec::Which::N, 0);
    if r_fe.equals(&zero) || s_fe.equals(&zero) {
        return false;
    }
    // Step 3: e, reduced modulo n (step 5 reduces it).
    let e = crate::scalar::derive_e(digest);
    // Step 4: w = s^-1 mod n.
    let w = match s_fe.inv() {
        None => return false,
        Some(w) => w,
    };
    // Step 5: u = e w mod n and v = r w mod n.
    let u = e.mul(&w);
    let v = r_fe.mul(&w);
    proof {
        crate::field::lemmas::lemma_modulus(crate::field::spec::Which::N);
        crate::lemmas::lemma_mul_reduced(derive_e(p384(), digest@), w.val(), p384().n);
    }
    // Step 6: R1 = [u]G + [v]Q, two separate products.
    let uo = u.to_octets();
    let vo = v.to_octets();
    let g = crate::point::base();
    let ug = crate::scalar::scalar_mul(&uo, &g);
    let vq = crate::scalar::scalar_mul(&vo, &q);
    let r1 = match (ug, vq) {
        (Some(a), Some(b)) => crate::point::ec_add(&a, &b),
        _ => None,
    };
    match r1 {
        // Step 6: the identity, or a failed operation, rejects.
        None => false,
        Some(Point::Infinity) => false,
        // Step 7: x_R. Step 8: its integer is itself (F.1).
        Some(Point::Affine { x, y: _ }) => {
            // Step 9: r = x_R mod n. x_R < p may exceed n, so reduce it.
            let xo = x.to_octets();
            let xr = reduce_prefix(crate::field::spec::Which::N, &xo, 48);
            proof {
                assert(xo@.subrange(0, 48) =~= xo@);
            }
            xr.equals(&r_fe)
        },
    }
}

} // verus!

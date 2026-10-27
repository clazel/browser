//! What each executable field function is proven to satisfy. The arguments
//! are the residues the field elements stand for (`Fe::val`, in `[0,
//! modulus(w))`, by `Fe`'s type invariant) and octet strings, so these
//! predicates mention neither limbs nor Montgomery form: reviewing them and
//! [`crate::spec`] is enough to know what the field code guarantees. The
//! shapes (a predicate per function, named `<fn>_ensures`) are those of
//! `clazel-pkcs1`'s `contract.rs`.
//!
//! ```text
//! Fe::add(&self, &Fe) -> (r: Fe)   ensures add_ensures(w, a.val(), b.val(), r.val())
//! Fe::sub(&self, &Fe) -> (r: Fe)   ensures sub_ensures(w, a.val(), b.val(), r.val())
//! Fe::mul(&self, &Fe) -> (r: Fe)   ensures mul_ensures(w, a.val(), b.val(), r.val())
//! Fe::one(w)          -> (r: Fe)   ensures one_ensures(r.val())
//! Fe::equals(&self, &Fe) -> (r: bool) ensures eq_ensures(a.val(), b.val(), r)
//! Fe::from_octets(w, &[u8; 48]) -> Option<Fe>
//!                                  ensures from_octets_ensures(w, o@, r.map(val))
//! Fe::to_octets(&self) -> [u8; 48] ensures to_octets_ensures(a.val(), r@)
//! Fe::pow(&self, &[u8; 48]) -> Fe  ensures pow_ensures(w, a.val(), e@, r.val())
//! Fe::inv(&self) -> Option<Fe>     ensures inv_ensures(w, a.val(), r.map(val))
//! ```
//!
//! `w` is the modulus selector of both operands (`requires a.which() ==
//! b.which()` where there are two).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `a + b` in GF(m): the residue of the sum. Fiat's `add`, "(eval a + eval b)
/// mod m", seen through the abstraction of [`super::spec`].
pub open spec fn add_ensures(w: Which, a: nat, b: nat, r: nat) -> bool {
    r == (a + b) % modulus(w)
}

/// `a - b` in GF(m): [`crate::spec::fe_sub`], the spec's subtraction.
pub open spec fn sub_ensures(w: Which, a: nat, b: nat, r: nat) -> bool {
    r == crate::spec::fe_sub(modulus(w), a, b)
}

/// `a b` in GF(m): the residue of the product.
pub open spec fn mul_ensures(w: Which, a: nat, b: nat, r: nat) -> bool {
    r == a * b % modulus(w)
}

/// The element 1.
pub open spec fn one_ensures(r: nat) -> bool {
    r == 1
}

/// Equality of residues. Two field elements are equal exactly when the
/// residues they stand for are.
pub open spec fn eq_ensures(a: nat, b: nat, r: bool) -> bool {
    r == (a == b)
}

/// SEC 1 §2.3.6 for a 48-octet string, and for either modulus: the octets
/// are read big-endian ([`crate::spec::os2ip`]) and the result is the
/// integer if it lies in `[0, m)`, and none otherwise. For `Which::P` this
/// is [`crate::spec::os2fe`] of `p384()` (`lemmas.rs`, `lemma_from_octets_os2fe`).
pub open spec fn from_octets_ensures(w: Which, o: Seq<u8>, r: Option<nat>) -> bool {
    match r {
        Some(x) => crate::spec::os2ip(o) < modulus(w) && x == crate::spec::os2ip(o),
        None => crate::spec::os2ip(o) >= modulus(w),
    }
}

/// The 48 octets of the residue, big-endian: SEC 1 §2.3.5 (a field element
/// to an octet string, through the integer of §2.3.9 and the octet string of
/// §2.3.7), whose inverse is [`crate::spec::os2ip`], SEC 1 §2.3.8.
pub open spec fn to_octets_ensures(a: nat, out: Seq<u8>) -> bool {
    out.len() == 48 && crate::spec::os2ip(out) == a
}

/// `a^e mod m`, `e` the big-endian octets of the exponent: the spec's
/// [`crate::spec::pow_mod`].
pub open spec fn pow_ensures(w: Which, a: nat, e: Seq<u8>, r: nat) -> bool {
    r == crate::spec::pow_mod(a, crate::spec::os2ip(e), modulus(w))
}

/// `a⁻¹` in GF(m) is the spec's [`crate::spec::inv`]: `Some(w)` exactly when
/// `inv(m, a)` is, with the same `w`, and none exactly when it is none. In
/// particular `Some(w)` implies `a w ≡ 1`, and (FIPS 186-5 step 4, choice 3
/// of `spec.rs`) none is returned for `a ≡ 0`.
pub open spec fn inv_ensures(w: Which, a: nat, r: Option<nat>) -> bool {
    match r {
        Some(x) => crate::spec::inv(modulus(w), a) == Some(x),
        None => crate::spec::inv(modulus(w), a) is None,
    }
}

} // verus!

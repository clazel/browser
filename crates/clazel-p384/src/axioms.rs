//! The trust boundary of the field: every call into fiat-crypto, each one
//! axiom. Six in all, `mul`, `add` and `sub` for each of `p384_64` (mod p)
//! and `p384_scalar_64` (mod n).
//!
//! Each wrapper is `external_body`. Verus takes its `ensures` on trust, and
//! the body is one call to one fiat function and nothing else: it wraps the
//! limb arrays in fiat's tuple structs, calls, and unwraps. The `ensures`
//! copies the postcondition that fiat prints above that function, in the
//! terms of `crate::field::spec`, and the `requires` copies the printed
//! precondition (inputs below `m`; the "unique saturated representation" is
//! the `[u64; 6]` type). That fiat-crypto's code meets its printed
//! postcondition is the Coq proof of `word_by_word_montgomery`, recorded in
//! the TCB (docs/VERIFICATION.md), and nothing else about fiat is assumed.
//!
//! **No wrapper checks its inputs at run time.** The precondition is a
//! `requires`, so Verus proves it at every call site; `field/fe.rs`'s
//! `Fe` type invariant (`value(limbs) < modulus`) is what discharges it. No
//! wrapper can be called with an argument whose precondition is not proven.
//!
//! There is no axiom for conversion into or out of the Montgomery domain,
//! for byte conversion, for `nonzero` or for `to_bytes`/`from_bytes`: the
//! first two are `mul` by R^2 and by 1 (`field/fe.rs`), and the octet
//! conversions are our own proven code. Inversion is `pow` over `mul`.
//!
//! These axioms are counted in the README table. A session other than the
//! one that wrote them reviews every change to this file
//! (docs/phases/phase-3.md 3.5f).

#[allow(unused_imports)]
use vstd::prelude::*;

use fiat_crypto::p384_64 as fiat_p;
use fiat_crypto::p384_scalar_64 as fiat_n;

verus! {

/// Multiplication modulo p on Montgomery-domain limbs.
///
/// Fiat's printed conditions (`p384_64.rs`, above `fiat_p384_mul`):
///
/// ```text
/// Preconditions:
///   0 ≤ eval arg1 < m
///   0 ≤ eval arg2 < m
/// Postconditions:
///   eval (from_montgomery out1) mod m = (eval (from_montgomery arg1) * eval (from_montgomery arg2)) mod m
///   0 ≤ eval out1 < m
/// ```
///
/// Here `m` is `modulus(Which::P)`, `eval` is `value` and `eval
/// (from_montgomery z)` is `from_montgomery(Which::P, z)` (docs of
/// `crate::field::spec`, choices 1 to 3). Every limb is below 2^64 by its
/// type, which is fiat's "unique saturated representation".
// AXIOM: fiat-crypto =0.3.0 `p384_64::fiat_p384_mul` satisfies the Postconditions printed above it,
// given its Preconditions (Coq-proven word-by-word Montgomery code; see docs/VERIFICATION.md).
#[verifier::external_body]
pub fn p_mul(a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        crate::field::spec::value(a@) < crate::field::spec::modulus(crate::field::spec::Which::P),
        crate::field::spec::value(b@) < crate::field::spec::modulus(crate::field::spec::Which::P),
    ensures
        crate::field::spec::from_montgomery(crate::field::spec::Which::P, out@)
            % crate::field::spec::modulus(crate::field::spec::Which::P)
            == (crate::field::spec::from_montgomery(crate::field::spec::Which::P, a@)
            * crate::field::spec::from_montgomery(crate::field::spec::Which::P, b@))
            % crate::field::spec::modulus(crate::field::spec::Which::P),
        crate::field::spec::value(out@) < crate::field::spec::modulus(crate::field::spec::Which::P),
{
    let mut out = fiat_p::fiat_p384_montgomery_domain_field_element([0; 6]);
    let a = fiat_p::fiat_p384_montgomery_domain_field_element(*a);
    let b = fiat_p::fiat_p384_montgomery_domain_field_element(*b);
    fiat_p::fiat_p384_mul(&mut out, &a, &b);
    out.0
}

/// Addition modulo p on Montgomery-domain limbs.
///
/// Fiat's printed conditions (`p384_64.rs`, above `fiat_p384_add`):
///
/// ```text
/// Preconditions:
///   0 ≤ eval arg1 < m
///   0 ≤ eval arg2 < m
/// Postconditions:
///   eval (from_montgomery out1) mod m = (eval (from_montgomery arg1) + eval (from_montgomery arg2)) mod m
///   0 ≤ eval out1 < m
/// ```
///
/// Here `m` is `modulus(Which::P)`, `eval` is `value` and `eval
/// (from_montgomery z)` is `from_montgomery(Which::P, z)` (docs of
/// `crate::field::spec`, choices 1 to 3). Every limb is below 2^64 by its
/// type, which is fiat's "unique saturated representation".
// AXIOM: fiat-crypto =0.3.0 `p384_64::fiat_p384_add` satisfies the Postconditions printed above it,
// given its Preconditions (Coq-proven word-by-word Montgomery code; see docs/VERIFICATION.md).
#[verifier::external_body]
pub fn p_add(a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        crate::field::spec::value(a@) < crate::field::spec::modulus(crate::field::spec::Which::P),
        crate::field::spec::value(b@) < crate::field::spec::modulus(crate::field::spec::Which::P),
    ensures
        crate::field::spec::from_montgomery(crate::field::spec::Which::P, out@)
            % crate::field::spec::modulus(crate::field::spec::Which::P)
            == (crate::field::spec::from_montgomery(crate::field::spec::Which::P, a@)
            + crate::field::spec::from_montgomery(crate::field::spec::Which::P, b@))
            % crate::field::spec::modulus(crate::field::spec::Which::P),
        crate::field::spec::value(out@) < crate::field::spec::modulus(crate::field::spec::Which::P),
{
    let mut out = fiat_p::fiat_p384_montgomery_domain_field_element([0; 6]);
    let a = fiat_p::fiat_p384_montgomery_domain_field_element(*a);
    let b = fiat_p::fiat_p384_montgomery_domain_field_element(*b);
    fiat_p::fiat_p384_add(&mut out, &a, &b);
    out.0
}

/// Subtraction modulo p on Montgomery-domain limbs.
///
/// Fiat's printed conditions (`p384_64.rs`, above `fiat_p384_sub`):
///
/// ```text
/// Preconditions:
///   0 ≤ eval arg1 < m
///   0 ≤ eval arg2 < m
/// Postconditions:
///   eval (from_montgomery out1) mod m = (eval (from_montgomery arg1) - eval (from_montgomery arg2)) mod m
///   0 ≤ eval out1 < m
/// ```
///
/// Here `m` is `modulus(Which::P)`, `eval` is `value` and `eval
/// (from_montgomery z)` is `from_montgomery(Which::P, z)` (docs of
/// `crate::field::spec`, choices 1 to 3). Every limb is below 2^64 by its
/// type, which is fiat's "unique saturated representation".
// AXIOM: fiat-crypto =0.3.0 `p384_64::fiat_p384_sub` satisfies the Postconditions printed above it,
// given its Preconditions (Coq-proven word-by-word Montgomery code; see docs/VERIFICATION.md).
#[verifier::external_body]
pub fn p_sub(a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        crate::field::spec::value(a@) < crate::field::spec::modulus(crate::field::spec::Which::P),
        crate::field::spec::value(b@) < crate::field::spec::modulus(crate::field::spec::Which::P),
    ensures
        (crate::field::spec::from_montgomery(crate::field::spec::Which::P, out@) as int)
            % (crate::field::spec::modulus(crate::field::spec::Which::P) as int)
            == ((crate::field::spec::from_montgomery(crate::field::spec::Which::P, a@) as int)
            - (crate::field::spec::from_montgomery(crate::field::spec::Which::P, b@) as int))
            % (crate::field::spec::modulus(crate::field::spec::Which::P) as int),
        crate::field::spec::value(out@) < crate::field::spec::modulus(crate::field::spec::Which::P),
{
    let mut out = fiat_p::fiat_p384_montgomery_domain_field_element([0; 6]);
    let a = fiat_p::fiat_p384_montgomery_domain_field_element(*a);
    let b = fiat_p::fiat_p384_montgomery_domain_field_element(*b);
    fiat_p::fiat_p384_sub(&mut out, &a, &b);
    out.0
}

/// Multiplication modulo n on Montgomery-domain limbs.
///
/// Fiat's printed conditions (`p384_scalar_64.rs`, above `fiat_p384_scalar_mul`):
///
/// ```text
/// Preconditions:
///   0 ≤ eval arg1 < m
///   0 ≤ eval arg2 < m
/// Postconditions:
///   eval (from_montgomery out1) mod m = (eval (from_montgomery arg1) * eval (from_montgomery arg2)) mod m
///   0 ≤ eval out1 < m
/// ```
///
/// Here `m` is `modulus(Which::N)`, `eval` is `value` and `eval
/// (from_montgomery z)` is `from_montgomery(Which::N, z)` (docs of
/// `crate::field::spec`, choices 1 to 3). Every limb is below 2^64 by its
/// type, which is fiat's "unique saturated representation".
// AXIOM: fiat-crypto =0.3.0 `p384_scalar_64::fiat_p384_scalar_mul` satisfies the Postconditions printed above it,
// given its Preconditions (Coq-proven word-by-word Montgomery code; see docs/VERIFICATION.md).
#[verifier::external_body]
pub fn n_mul(a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        crate::field::spec::value(a@) < crate::field::spec::modulus(crate::field::spec::Which::N),
        crate::field::spec::value(b@) < crate::field::spec::modulus(crate::field::spec::Which::N),
    ensures
        crate::field::spec::from_montgomery(crate::field::spec::Which::N, out@)
            % crate::field::spec::modulus(crate::field::spec::Which::N)
            == (crate::field::spec::from_montgomery(crate::field::spec::Which::N, a@)
            * crate::field::spec::from_montgomery(crate::field::spec::Which::N, b@))
            % crate::field::spec::modulus(crate::field::spec::Which::N),
        crate::field::spec::value(out@) < crate::field::spec::modulus(crate::field::spec::Which::N),
{
    let mut out = fiat_n::fiat_p384_scalar_montgomery_domain_field_element([0; 6]);
    let a = fiat_n::fiat_p384_scalar_montgomery_domain_field_element(*a);
    let b = fiat_n::fiat_p384_scalar_montgomery_domain_field_element(*b);
    fiat_n::fiat_p384_scalar_mul(&mut out, &a, &b);
    out.0
}

/// Addition modulo n on Montgomery-domain limbs.
///
/// Fiat's printed conditions (`p384_scalar_64.rs`, above `fiat_p384_scalar_add`):
///
/// ```text
/// Preconditions:
///   0 ≤ eval arg1 < m
///   0 ≤ eval arg2 < m
/// Postconditions:
///   eval (from_montgomery out1) mod m = (eval (from_montgomery arg1) + eval (from_montgomery arg2)) mod m
///   0 ≤ eval out1 < m
/// ```
///
/// Here `m` is `modulus(Which::N)`, `eval` is `value` and `eval
/// (from_montgomery z)` is `from_montgomery(Which::N, z)` (docs of
/// `crate::field::spec`, choices 1 to 3). Every limb is below 2^64 by its
/// type, which is fiat's "unique saturated representation".
// AXIOM: fiat-crypto =0.3.0 `p384_scalar_64::fiat_p384_scalar_add` satisfies the Postconditions printed above it,
// given its Preconditions (Coq-proven word-by-word Montgomery code; see docs/VERIFICATION.md).
#[verifier::external_body]
pub fn n_add(a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        crate::field::spec::value(a@) < crate::field::spec::modulus(crate::field::spec::Which::N),
        crate::field::spec::value(b@) < crate::field::spec::modulus(crate::field::spec::Which::N),
    ensures
        crate::field::spec::from_montgomery(crate::field::spec::Which::N, out@)
            % crate::field::spec::modulus(crate::field::spec::Which::N)
            == (crate::field::spec::from_montgomery(crate::field::spec::Which::N, a@)
            + crate::field::spec::from_montgomery(crate::field::spec::Which::N, b@))
            % crate::field::spec::modulus(crate::field::spec::Which::N),
        crate::field::spec::value(out@) < crate::field::spec::modulus(crate::field::spec::Which::N),
{
    let mut out = fiat_n::fiat_p384_scalar_montgomery_domain_field_element([0; 6]);
    let a = fiat_n::fiat_p384_scalar_montgomery_domain_field_element(*a);
    let b = fiat_n::fiat_p384_scalar_montgomery_domain_field_element(*b);
    fiat_n::fiat_p384_scalar_add(&mut out, &a, &b);
    out.0
}

/// Subtraction modulo n on Montgomery-domain limbs.
///
/// Fiat's printed conditions (`p384_scalar_64.rs`, above `fiat_p384_scalar_sub`):
///
/// ```text
/// Preconditions:
///   0 ≤ eval arg1 < m
///   0 ≤ eval arg2 < m
/// Postconditions:
///   eval (from_montgomery out1) mod m = (eval (from_montgomery arg1) - eval (from_montgomery arg2)) mod m
///   0 ≤ eval out1 < m
/// ```
///
/// Here `m` is `modulus(Which::N)`, `eval` is `value` and `eval
/// (from_montgomery z)` is `from_montgomery(Which::N, z)` (docs of
/// `crate::field::spec`, choices 1 to 3). Every limb is below 2^64 by its
/// type, which is fiat's "unique saturated representation".
// AXIOM: fiat-crypto =0.3.0 `p384_scalar_64::fiat_p384_scalar_sub` satisfies the Postconditions printed above it,
// given its Preconditions (Coq-proven word-by-word Montgomery code; see docs/VERIFICATION.md).
#[verifier::external_body]
pub fn n_sub(a: &[u64; 6], b: &[u64; 6]) -> (out: [u64; 6])
    requires
        crate::field::spec::value(a@) < crate::field::spec::modulus(crate::field::spec::Which::N),
        crate::field::spec::value(b@) < crate::field::spec::modulus(crate::field::spec::Which::N),
    ensures
        (crate::field::spec::from_montgomery(crate::field::spec::Which::N, out@) as int)
            % (crate::field::spec::modulus(crate::field::spec::Which::N) as int)
            == ((crate::field::spec::from_montgomery(crate::field::spec::Which::N, a@) as int)
            - (crate::field::spec::from_montgomery(crate::field::spec::Which::N, b@) as int))
            % (crate::field::spec::modulus(crate::field::spec::Which::N) as int),
        crate::field::spec::value(out@) < crate::field::spec::modulus(crate::field::spec::Which::N),
{
    let mut out = fiat_n::fiat_p384_scalar_montgomery_domain_field_element([0; 6]);
    let a = fiat_n::fiat_p384_scalar_montgomery_domain_field_element(*a);
    let b = fiat_n::fiat_p384_scalar_montgomery_domain_field_element(*b);
    fiat_n::fiat_p384_scalar_sub(&mut out, &a, &b);
    out.0
}

} // verus!

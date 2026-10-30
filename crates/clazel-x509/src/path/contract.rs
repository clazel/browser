//! Contracts for the executable path validation P8 and P9 write: one
//! predicate per executable function, in terms of `spec.rs`, `profile.rs`
//! and `verifier.rs`, and the two parameters' executable traits. Nothing
//! here is implemented yet.
//!
//! - **The parameters.** `LinkVerifier` is design §3.3's trait: its
//!   executable `verify` returns exactly what its spec function `link` says
//!   of the same `SignedData`; P11 implements it in `clazel-crypto`.
//!   `RevocationOracle` is the same shape for §6.1.3 (a)(3); its production
//!   instance answers `false` and its spec function is `|_| false`.
//! - **The fold.** P8's `process` is a loop over the certificates. Its
//!   invariant is `state_before`: the state §6.1.3 finds for certificate i+1
//!   (`certs[i]`), defined here as the prefix of the spec's fold. P8 proves
//!   that the spec's `process_from` from that state is `process`
//!   (`process_from_state_before` states it).
//! - **The bound.** The name-constraint comparison bound is part of the spec
//!   (`verifier::candidate_verdict`), so the executable candidate verdict
//!   equals the spec's exactly; nothing here is weaker than the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The parameters
// ---------------------------------------------------------------------------

/// §6.1.3 (a)(1), design §3.3: link signature verification.
pub trait LinkVerifier {
    /// The verification this instance performs, as a spec function.
    spec fn link(&self) -> LinkFn;

    /// Verify `signature` over `tbs_der` with `algorithm` under the issuer's
    /// SubjectPublicKeyInfo `issuer_spki`.
    fn verify(
        &self, issuer_spki: &[u8], algorithm: &crate::certificate::exec::AlgorithmIdentifier<'_>,
        tbs_der: &[u8], signature: &[u8],
    ) -> (out: bool)
        ensures out == (self.link())(SignedData {
            issuer_spki: issuer_spki@,
            algorithm: crate::certificate::contract::view_algorithm_identifier(algorithm),
            tbs_der: tbs_der@,
            signature: signature@,
        });
}

/// §6.1.3 (a)(3): revocation (production: nothing is revoked).
pub trait RevocationOracle {
    /// The revocation status this instance reports, as a spec function.
    spec fn revoked(&self) -> RevokedFn;

    /// Whether `cert` is revoked at the current time.
    fn is_revoked(&self, cert: &super::parsed::exec::PathCert<'_>) -> (out: bool)
        ensures out == (self.revoked())(super::parsed::exec::view_path_cert(cert));
}

// ---------------------------------------------------------------------------
// §6.1, step by step (P8)
// ---------------------------------------------------------------------------

/// §6.1.2 `initialization`.
pub open spec fn initialization_ensures(anchor: super::parsed::spec::Anchor, n: nat, out: Result<State, PathError>) -> bool {
    out == initialization(anchor, n)
}

/// §6.1.3 `basic_certificate_processing`.
pub open spec fn basic_certificate_processing_ensures(
    link: LinkFn, revoked: RevokedFn, state: State, cert: super::parsed::spec::PathCert,
    now: crate::time::spec::CertificateTime, out: Result<(), PathError>,
) -> bool {
    out == basic_certificate_processing(link, revoked, state, cert, now)
}

/// §6.1.4 `preparation_for_next`.
pub open spec fn preparation_for_next_ensures(
    state: State, cert: super::parsed::spec::PathCert, out: Result<State, PathError>,
) -> bool {
    out == preparation_for_next(state, cert)
}

/// §6.1.5 `wrap_up`.
pub open spec fn wrap_up_ensures(state: State, cert: super::parsed::spec::PathCert, out: Result<Seq<u8>, PathError>) -> bool {
    out == wrap_up(state, cert)
}

/// The state §6.1.3 finds for `certs[i]` (the RFC's certificate i+1): the
/// first `i` rounds of Figure 2 from `initialization`, or the error one of
/// them returned. P8's loop invariant.
pub open spec fn state_before(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, i: int,
) -> Result<State, PathError>
    decreases i
{
    if i <= 0 { initialization(anchor, certs.len()) }
    else { match state_before(link, revoked, anchor, certs, now, i - 1) {
        Err(e) => Err(e),
        Ok(state) => match basic_certificate_processing(link, revoked, state, certs[i - 1], now) {
            Err(e) => Err(e),
            Ok(()) => preparation_for_next(state, certs[i - 1]),
        },
    }}
}

/// What P8 proves of the fold: for every `i` before the last certificate, a
/// path whose first `i` rounds succeed continues as `process_from` from
/// `state_before`. (A statement, not yet proven.)
pub open spec fn process_from_state_before(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime, i: int,
) -> bool {
    (certs.len() > 0 && certificates_distinct_from(certs, 0) && 0 <= i < certs.len()) ==>
        match state_before(link, revoked, anchor, certs, now, i) {
            Ok(state) => process(link, revoked, anchor, certs, now) == process_from(link, revoked, certs, i, now, state),
            Err(e) => process(link, revoked, anchor, certs, now) == Err::<Seq<u8>, PathError>(e),
        }
}

/// §6.1 `process`.
pub open spec fn process_ensures(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
    out: Result<Seq<u8>, PathError>,
) -> bool {
    out == process(link, revoked, anchor, certs, now)
}

// ---------------------------------------------------------------------------
// The profile and one candidate (P8)
// ---------------------------------------------------------------------------

/// `profile::path_profile`.
pub open spec fn path_profile_ensures(
    anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>,
    reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
    out: Result<(), PathError>,
) -> bool {
    out == super::profile::path_profile(anchor, certs, reference, now)
}

/// `verifier::path_within_budget`, the design §1.12 comparison bound.
pub open spec fn path_within_budget_ensures(
    anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>, out: bool,
) -> bool {
    out == super::verifier::path_within_budget(anchor, certs)
}

/// `verifier::candidate_verdict`: the whole verdict on one candidate.
pub open spec fn candidate_verdict_ensures(
    environment: super::verifier::Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    candidate: super::verifier::Candidate, reference: crate::spec::ReferenceIdentity,
    now: crate::time::spec::CertificateTime, out: Result<Seq<u8>, PathError>,
) -> bool {
    out == super::verifier::candidate_verdict(environment, anchors, pool, leaf, candidate, reference, now)
}

// ---------------------------------------------------------------------------
// The chain (P9)
// ---------------------------------------------------------------------------

/// `verifier::chain_inputs`: the bound on presented certificates, the leaf,
/// the pool and the time.
pub open spec fn chain_inputs_ensures(
    presented: Seq<Seq<u8>>, now: u64, out: Result<super::verifier::ChainInputs, PathError>,
) -> bool {
    out == super::verifier::chain_inputs(presented, now)
}

/// The top-level verifier: `verifier::verify_server_chain_ensures`, which
/// fixes soundness and completeness; `order` is the step sequence P9's
/// search examines, on which the 200,000-step budget is judged.
pub open spec fn verify_server_chain_contract(
    environment: super::verifier::Environment, anchors: Seq<super::parsed::spec::Anchor>,
    presented: Seq<Seq<u8>>, reference: crate::spec::ReferenceIdentity, now: u64,
    order: Seq<super::verifier::IssuerStep>, out: Result<super::verifier::Validated, PathError>,
) -> bool {
    super::verifier::verify_server_chain_ensures(environment, anchors, presented, reference, now, order, out)
}

} // verus!

//! The verdict on a presented TLS server chain: RFC 5280 §6.1 (`spec.rs`)
//! and the browser profile (`profile.rs`) on one candidate path, the bounds
//! of the design's §1.12, and the contract the top-level verifier meets
//! (design §2.6, §3.5).
//!
//! Sources: as `spec.rs` and `profile.rs`; RFC 8446 §4.4.2 ("The sender's
//! certificate MUST come in the first CertificateEntry in the list. Each
//! following certificate SHOULD directly certify the one immediately
//! preceding it" and "clients SHOULD be prepared to handle potentially
//! extraneous certificates and arbitrary orderings from any TLS version"),
//! <https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2>; RFC 4158 (path
//! building, guidance only).
//!
//! What is here and what is not:
//! - **One candidate path** is an anchor index and a sequence of pool
//!   indices (`Candidate`, design §2.6). `candidate_verdict` is the whole
//!   verdict on it: well-formedness, `profile::path_profile`, `spec::process`
//!   and the name-constraint comparison bound.
//! - **The chain** is accepted when *some* candidate is valid
//!   (`some_candidate_valid`). Which candidate the verifier returns, the
//!   bounded depth-first enumeration that finds it (anchors first, K = 16
//!   candidates) and the theorems about that enumeration are P9's (`build.rs`,
//!   `chain.rs`). `verify_server_chain_ensures` is the contract P9's executable
//!   verifier must meet whatever enumeration it uses: an `Ok` is a valid
//!   candidate, and any error but `TooManyCandidates` means none is valid.
//!
//! Modelling choices:
//! - **The reference identity is typed** (design Q2, decided 2026-10-29): a
//!   `crate::spec::ReferenceIdentity`, DNS or IP, as the URL layer produces
//!   it. IP references match only iPAddress subjectAltName entries and DNS
//!   references only dNSName entries (`crate::spec::service_identity_match`).
//!   No host bytes are re-parsed here.
//! - **The clock** is Unix seconds (`now: u64`, as `clazel-tls`'s
//!   `ChainValidation` passes it), converted by
//!   `time::spec::from_unix_seconds`; a time past the year 9999 refuses
//!   (`Malformed`).
//! - **The presented chain** is the TLS Certificate message's certificates
//!   in order, `presented[0]` the server's own (RFC 8446 §4.4.2). The others
//!   are a pool, used in any order (design Q3). **(I)** A pool certificate
//!   that `parse_path_cert` refuses is dropped from the pool rather than
//!   refusing the chain (design §2.6 step 3); a path simply cannot use it.
//!   A first certificate that does not parse refuses (`Malformed`).
//! - **Trust anchors** are a parameter, `anchors`; the production value is
//!   every `roots::ROOTS` entry for which `parsed::spec::anchor_from_root` is
//!   `Some`.
//! - **Revocation and signatures** are the parameters of `spec.rs`, in
//!   `Environment`. **(I)** Certificate Transparency is not checked (design
//!   Q4: Phase 8).
//! - **Bounds** (design §1.12, Q13). Each refuses beyond, with its own error:
//!   - at most 16 presented certificates (`TooManyCertificates`);
//!   - at most `max_intermediates` intermediates in a candidate, 6 in
//!     production (webpki's `MAX_SUB_CA_COUNT`; limbo's `max_chain_depth`
//!     sets it per test case). A longer candidate is not a candidate;
//!   - at most 4,096 name-constraint comparisons per path, counted as P5's
//!     contract counts them (`within_budget`, below) (`TooManyNameComparisons`);
//!   - at most K = 16 candidates examined (`TooManyCandidates`): P9's
//!     enumeration bound. Here it appears only in what that error may mean.
//!
//! For P16, the intended `clazel-tls` join (not changed here). `auth::spec`'s
//! `ChainValidation` becomes
//! `spec_fn(crate::spec::ReferenceIdentity, u64, Seq<u8>) -> Result<Seq<u8>, CertificateError>`:
//! the typed reference identity, the clock and the Certificate message body.
//! Its instance (in `clazel-crypto`, design §3.1) parses the body's
//! CertificateEntry list with `clazel_tls::spec`, takes each entry's
//! `cert_data` in order as `presented`, and returns the `Ok` value's
//! `leaf_spki` of a verifier meeting `verify_server_chain_ensures` with the
//! production anchors, `max_intermediates` 6, P11's `link` and `revoked` =
//! nothing. `auth::spec::Config.host` and `hello::client_spec::Config` carry
//! the typed host. The intended mapping of errors to the `CertificateError`
//! alerts: `Expired` and `AnchorExpired` to `Expired` (45);
//! `UnsupportedAlgorithm` to `Unsupported` (43); `UnknownIssuer`,
//! `BadSignature`, `NameChaining`, `Distrusted`, `Revoked` and
//! `TooManyCandidates` to `UnknownCa` (48); every other error to
//! `BadCertificate` (42).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Parameters and results
// ---------------------------------------------------------------------------

/// The verifier's parameters that are not data from the peer.
pub struct Environment {
    /// §6.1.3 (a)(1): link signature verification (P11's instance).
    pub link: super::spec::LinkFn,
    /// §6.1.3 (a)(3): revocation (production: nothing is revoked).
    pub revoked: super::spec::RevokedFn,
    /// Design §1.12: the most intermediates a candidate may have (6).
    pub max_intermediates: nat,
}

/// A candidate path (design §2.6): `anchors[anchor]`, then the pool
/// certificates `path[0]`, ..., `path[len-1]` (the anchor's child first),
/// then the presented leaf.
pub struct Candidate {
    /// Index into the anchors.
    pub anchor: nat,
    /// Indices into the pool (`presented[1..]`), the anchor's child first.
    pub path: Seq<nat>,
}

/// An accepted chain (design §2.6).
pub struct Validated {
    /// Index of the anchor the path reaches.
    pub anchor: nat,
    /// The pool indices of the intermediates, the anchor's child first.
    pub path: Seq<nat>,
    /// The target's complete SubjectPublicKeyInfo DER (§6.1.6's
    /// working_public_key), the key `ChainValidation` returns.
    pub leaf_spki: Seq<u8>,
}

// ---------------------------------------------------------------------------
// Bounds (design §1.12)
// ---------------------------------------------------------------------------

/// At most this many certificates in one Certificate message.
pub open spec fn max_presented_certificates() -> nat { 16 }

/// The production `max_intermediates` (webpki `MAX_SUB_CA_COUNT`).
pub open spec fn default_max_intermediates() -> nat { 6 }

/// At most this many candidate paths are examined (P9's K).
pub open spec fn max_candidates() -> nat { 16 }

/// At most this many subjectAltName-entry by subtree comparisons per path.
/// The definitions down to `within_budget` are those of P5's contract
/// (`name_constraints/matching/contract.rs` on PR #40, not yet on this
/// branch), restated so the bound is part of the spec; once #40 is merged
/// they should be replaced by P5's, which are the same text.
pub open spec fn comparison_bound() -> nat { 4096 }

/// The subtrees one NameConstraints value holds, in both lists.
pub open spec fn subtrees_in(value: crate::name_constraints::spec::NameConstraints) -> nat {
    (match value.permitted_subtrees { Some(items) => items.len(), None => 0 })
        + (match value.excluded_subtrees { Some(items) => items.len(), None => 0 })
}

/// The subtrees of every set in the state.
pub open spec fn subtree_count(state: Seq<crate::name_constraints::spec::NameConstraints>) -> nat
    decreases state.len()
{
    if state.len() == 0 { 0 } else { subtrees_in(state.last()) + subtree_count(state.drop_last()) }
}

/// The comparisons one certificate costs: every subjectAltName entry, and the
/// subject, against every subtree of the state.
pub open spec fn comparisons(entries: nat, subtrees: nat) -> nat {
    (entries + 1) * subtrees
}

/// Every certificate of `path[i..]` stays within the bound, `spent` being the
/// comparisons of `path[..i]`, with the state evolution of P4's
/// `names_constrained_from`.
pub open spec fn within_budget_from(
    path: Seq<crate::name_constraints::matching::spec::NcCertificate>, i: int,
    state: Seq<crate::name_constraints::spec::NameConstraints>, spent: nat,
) -> bool
    decreases path.len() - i
{
    if i < 0 || i >= path.len() { true }
    else {
        let certificate = path[i];
        let total = spent + comparisons(certificate.subject_alt_names.len(), subtree_count(state));
        &&& total <= comparison_bound()
        &&& i == path.len() - 1 || match crate::name_constraints::matching::spec::prepare_name_constraints(
            state, certificate.name_constraints) {
            Some(next) => within_budget_from(path, i + 1, next, total),
            None => true,
        }
    }
}

/// The whole path within the bound, from `initial`.
pub open spec fn within_budget(
    path: Seq<crate::name_constraints::matching::spec::NcCertificate>,
    initial: Seq<crate::name_constraints::spec::NameConstraints>,
) -> bool {
    within_budget_from(path, 0, initial, 0)
}

/// What P4 reads from each certificate of a path, in order.
pub open spec fn nc_path(certs: Seq<super::parsed::spec::PathCert>)
    -> Seq<crate::name_constraints::matching::spec::NcCertificate>
    decreases certs.len()
{
    if certs.len() == 0 { seq![] }
    else { nc_path(certs.drop_last()).push(super::spec::nc_certificate(certs.last())) }
}

/// The name-constraint state the anchor starts a path with (RFC 5937 §3.2
/// bullets 2 and 3), or `None` when it is unsupported (`spec::initialization`
/// then refuses).
pub open spec fn anchor_subtrees(anchor: super::parsed::spec::Anchor)
    -> Option<Seq<crate::name_constraints::spec::NameConstraints>>
{
    crate::name_constraints::matching::spec::prepare_name_constraints(
        crate::name_constraints::matching::spec::initial_state(), anchor.name_constraints)
}

/// A path within the comparison bound (vacuous when the anchor's constraints
/// are unsupported, which `spec::process` refuses anyway).
pub open spec fn path_within_budget(anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>) -> bool {
    match anchor_subtrees(anchor) {
        Some(initial) => within_budget(nc_path(certs), initial),
        None => true,
    }
}

// ---------------------------------------------------------------------------
// One candidate
// ---------------------------------------------------------------------------

/// `index` is not among `path[from..]`.
pub open spec fn index_absent_from(path: Seq<nat>, index: nat, from: int) -> bool
    decreases path.len() - from
{
    if from < 0 || from >= path.len() { true }
    else { path[from] != index && index_absent_from(path, index, from + 1) }
}

/// No index of `path[from..]` repeats.
pub open spec fn indices_distinct_from(path: Seq<nat>, from: int) -> bool
    decreases path.len() - from
{
    if from < 0 || from >= path.len() { true }
    else { index_absent_from(path, path[from], from + 1) && indices_distinct_from(path, from + 1) }
}

/// Every index of `path[from..]` names a pool certificate that parsed.
pub open spec fn indices_usable_from(pool: Seq<Option<super::parsed::spec::PathCert>>, path: Seq<nat>, from: int) -> bool
    decreases path.len() - from
{
    if from < 0 || from >= path.len() { true }
    else { path[from] < pool.len() && pool[path[from] as int] is Some && indices_usable_from(pool, path, from + 1) }
}

/// A candidate names an anchor, at most `max_intermediates` usable pool
/// certificates, and none twice (design §2.6).
pub open spec fn candidate_well_formed(
    anchors: Seq<super::parsed::spec::Anchor>, pool: Seq<Option<super::parsed::spec::PathCert>>,
    candidate: Candidate, max_intermediates: nat,
) -> bool {
    &&& candidate.anchor < anchors.len()
    &&& candidate.path.len() <= max_intermediates
    &&& indices_usable_from(pool, candidate.path, 0)
    &&& indices_distinct_from(candidate.path, 0)
}

/// The intermediates a candidate names, the anchor's child first.
pub open spec fn intermediates_of(pool: Seq<Option<super::parsed::spec::PathCert>>, path: Seq<nat>)
    -> Seq<super::parsed::spec::PathCert>
    decreases path.len()
{
    if path.len() == 0 { seq![] }
    else {
        let index = path.last();
        let cert = if index < pool.len() { match pool[index as int] { Some(c) => c, None => arbitrary() } }
            else { arbitrary() };
        intermediates_of(pool, path.drop_last()).push(cert)
    }
}

/// §6.1.1 (a): the prospective path of a candidate, certificate 1 first and
/// the leaf last.
pub open spec fn candidate_certificates(
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert, candidate: Candidate,
) -> Seq<super::parsed::spec::PathCert> {
    intermediates_of(pool, candidate.path).push(leaf)
}

/// The verdict on one candidate: well-formed, then the profile, then §6.1,
/// then the comparison bound. `Ok` carries the target's key.
pub open spec fn candidate_verdict(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    candidate: Candidate, reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> Result<Seq<u8>, super::spec::PathError> {
    if !candidate_well_formed(anchors, pool, candidate, environment.max_intermediates) {
        // A path longer than the bound, or through an unusable certificate,
        // is not a candidate.
        if candidate.path.len() > environment.max_intermediates { Err(super::spec::PathError::TooManyIntermediates) }
        else { Err(super::spec::PathError::UnknownIssuer) }
    } else {
        let anchor = anchors[candidate.anchor as int];
        let certs = candidate_certificates(pool, leaf, candidate);
        match super::profile::path_profile(anchor, certs, reference, now) {
            Err(e) => Err(e),
            Ok(()) => match super::spec::process(environment.link, environment.revoked, anchor, certs, now) {
                Err(e) => Err(e),
                Ok(key) => if !path_within_budget(anchor, certs) { Err(super::spec::PathError::TooManyNameComparisons) }
                    else { Ok(key) },
            },
        }
    }
}

/// A candidate on which the verdict is `Ok`.
pub open spec fn candidate_valid(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert,
    candidate: Candidate, reference: crate::spec::ReferenceIdentity, now: crate::time::spec::CertificateTime,
) -> bool {
    candidate_verdict(environment, anchors, pool, leaf, candidate, reference, now) is Ok
}

// ---------------------------------------------------------------------------
// The presented chain
// ---------------------------------------------------------------------------

/// The pool: every presented certificate after the first, parsed; `None`
/// where it does not parse (dropped, (I)).
pub open spec fn parsed_pool(presented: Seq<Seq<u8>>) -> Seq<Option<super::parsed::spec::PathCert>>
    decreases presented.len()
{
    if presented.len() <= 1 { seq![] }
    else { parsed_pool(presented.drop_last()).push(super::parsed::spec::parse_path_cert(presented.last())) }
}

/// What the verdict starts from: the bound on presented certificates, the
/// leaf, the pool and the time.
pub struct ChainInputs {
    /// `presented[0]`, parsed.
    pub leaf: super::parsed::spec::PathCert,
    /// `presented[1..]`, parsed.
    pub pool: Seq<Option<super::parsed::spec::PathCert>>,
    /// `now`, as a certificate time.
    pub now: crate::time::spec::CertificateTime,
}

/// The inputs, or the error that refuses the chain before any path is tried.
pub open spec fn chain_inputs(presented: Seq<Seq<u8>>, now: u64) -> Result<ChainInputs, super::spec::PathError> {
    // 1. Design §1.12: at most 16 presented certificates.
    if presented.len() > max_presented_certificates() { Err(super::spec::PathError::TooManyCertificates) }
    // 2. RFC 8446 §4.4.2: the server's own certificate comes first.
    else if presented.len() == 0 { Err(super::spec::PathError::Malformed) }
    else { match (super::parsed::spec::parse_path_cert(presented[0]), crate::time::spec::from_unix_seconds(now as nat)) {
        // 3. The leaf parses, and the time is one a certificate can name.
        (Some(leaf), Some(time)) => Ok(ChainInputs { leaf, pool: parsed_pool(presented), now: time }),
        _ => Err(super::spec::PathError::Malformed),
    }}
}

/// The chain is acceptable: some candidate path is valid.
pub open spec fn some_candidate_valid(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>,
    reference: crate::spec::ReferenceIdentity, now: u64,
) -> bool {
    match chain_inputs(presented, now) {
        Err(_) => false,
        Ok(inputs) => exists|candidate: Candidate|
            candidate_valid(environment, anchors, inputs.pool, inputs.leaf, candidate, reference, inputs.now),
    }
}

/// The issuer and subject names of a candidate chain, as the builder follows
/// them (design §2.6: names only, no other check): certificate 1's issuer is
/// the anchor's subject, and each certificate's issuer is the previous one's
/// subject (§6.1 conditions (a) and (b)).
pub open spec fn names_chain_from(
    anchor: super::parsed::spec::Anchor, certs: Seq<super::parsed::spec::PathCert>, i: int,
) -> bool
    decreases certs.len() - i
{
    if i < 0 || i >= certs.len() { true }
    else {
        let expected = if i == 0 { anchor.subject_der } else { certs[i - 1].tbs.subject_der };
        certs[i].tbs.issuer_der == expected && names_chain_from(anchor, certs, i + 1)
    }
}

/// A well-formed candidate whose names chain: what P9's enumeration lists.
pub open spec fn candidate_name_chained(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>,
    pool: Seq<Option<super::parsed::spec::PathCert>>, leaf: super::parsed::spec::PathCert, candidate: Candidate,
) -> bool {
    &&& candidate_well_formed(anchors, pool, candidate, environment.max_intermediates)
    &&& names_chain_from(anchors[candidate.anchor as int], candidate_certificates(pool, leaf, candidate), 0)
}

/// `TooManyCandidates` is justified: more than K distinct name-chained
/// candidates exist.
pub open spec fn too_many_candidates(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>, now: u64,
) -> bool {
    match chain_inputs(presented, now) {
        Err(_) => false,
        Ok(inputs) => exists|listed: Seq<Candidate>| {
            &&& listed.len() > max_candidates()
            &&& forall|a: int, b: int| 0 <= a < b < listed.len() ==> listed[a] != listed[b]
            &&& forall|a: int| 0 <= a < listed.len() ==>
                candidate_name_chained(environment, anchors, inputs.pool, inputs.leaf, #[trigger] listed[a])
        },
    }
}

/// The top-level verifier's contract (design §2.6, §3.5), for P9's
/// executable `verify_server_chain` whatever its enumeration:
/// - `Ok(v)`: the chain's inputs are acceptable, and the candidate
///   `(v.anchor, v.path)` is valid with `v.leaf_spki` its key (soundness);
/// - `Err(TooManyCandidates)`: more than K name-chained candidates exist;
/// - any other `Err`: no candidate is valid (completeness, within the bounds).
pub open spec fn verify_server_chain_ensures(
    environment: Environment, anchors: Seq<super::parsed::spec::Anchor>, presented: Seq<Seq<u8>>,
    reference: crate::spec::ReferenceIdentity, now: u64, out: Result<Validated, super::spec::PathError>,
) -> bool {
    match out {
        Ok(v) => match chain_inputs(presented, now) {
            Err(_) => false,
            Ok(inputs) => candidate_verdict(environment, anchors, inputs.pool, inputs.leaf,
                Candidate { anchor: v.anchor, path: v.path }, reference, inputs.now) == Ok::<Seq<u8>, super::spec::PathError>(v.leaf_spki),
        },
        Err(super::spec::PathError::TooManyCandidates) => too_many_candidates(environment, anchors, presented, now),
        Err(_) => !some_candidate_valid(environment, anchors, presented, reference, now),
    }
}

} // verus!

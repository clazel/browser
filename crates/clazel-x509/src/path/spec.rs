//! RFC 5280 §6.1 Basic Path Validation, §6.1.1 to §6.1.5, over a candidate
//! path of decoded certificates (`PathCert`) issued below a trust anchor
//! (`Anchor`), with RFC 5937 §3.2's trust-anchor initialization.
//!
//! Sources, pinned:
//! - RFC 5280, May 2008, <https://www.rfc-editor.org/rfc/rfc5280.txt>,
//!   SHA-256 `a2f2628c0a83b873fc4786abd921f9b2c02395954b655d190bf16b831633345d`
//!   (downloaded 2026-10-29). §6.1 (the conditions (a) to (d) and the
//!   self-issued definition), §6.1.1 (a) to (i), §6.1.2 (a) to (k), §6.1.3
//!   (a)(1) to (f), §6.1.4 (a) to (o), §6.1.5 (a) to (g), §6.1.6.
//! - RFC 5937, August 2010, <https://www.rfc-editor.org/rfc/rfc5937.txt>,
//!   SHA-256 `6424a9b13e2ea7accfed71e0adef806309851909775aea74471187910f861f01`.
//!   §3.2, bullets counted from 1 as in `parsed/spec.rs`: (2)
//!   initial-permitted-subtrees, (3) initial-excluded-subtrees, (8)
//!   pathLenConstraint.
//! - The path-validation design (`.claude/plans/path-validation.md`, not in
//!   the repository): §1 (scope and profile), §2.2 to §2.5 (the steps) and
//!   questions Q2 to Q13 as decided on 2026-10-29.
//!
//! This file is the RFC transcription only. The CA/Browser Forum and browser
//! checks layered on it are in `profile.rs`, and the verdict on a presented
//! chain is in `verifier.rs`. Indices are from 0: `certs[i]` is the RFC's
//! certificate i+1, so `certs[0]` is certificate 1 (issued by the trust
//! anchor) and `certs[n-1]` is certificate n, the target. Every comment that
//! names an RFC step quotes the RFC's 1-based i.
//!
//! Modelling choices. **(R)** marks a refusal RFC 5280 does not require, **(I)**
//! something RFC 5280 asks for that is ignored, and **(=)** a change of form
//! whose outcome is the RFC's.
//! - **(=) §6.1.1 inputs.** (a) is `certs`, a non-empty sequence; (b) the
//!   current date/time is `now`, already a `CertificateTime`; (c)
//!   user-initial-policy-set is {any-policy}; (d) is `anchor` (built by
//!   `parsed::spec::anchor_from_root`); (e), (f) and (g) are all FALSE; (h)
//!   initial-permitted-subtrees is every name of every type and (i)
//!   initial-excluded-subtrees is empty, before RFC 5937 adds the anchor's
//!   constraints. None of these is a parameter, because the browser's values
//!   never change (design §1.1).
//! - **(=) "A certificate MUST NOT appear more than once in a prospective
//!   certification path"** (§6.1) is checked on the input: two equal DER
//!   encodings refuse the path. The builder (P9) never proposes one; the
//!   check makes the statement hold for every path.
//! - **The signature of each link is a parameter** (`link`, design §3.3),
//!   since `clazel-x509` cannot call `clazel-crypto`. §6.1.3 (a)(1) is
//!   "`link` holds of `SignedData` built from the working key and the
//!   certificate". Its production instance is P11's. **(R)** A certificate
//!   whose signature algorithm `signature_algorithm::spec::classify` calls
//!   `Unsupported` (RSASSA-PSS, Ed25519, SHA-1, ...) refuses the path before
//!   `link` is asked (design §1.11), so that refusal does not depend on the
//!   instance.
//! - **(=) §6.1.2 (g), (h) and (i) are one field**, `working_public_key`,
//!   holding the complete SubjectPublicKeyInfo DER: algorithm, parameters and
//!   key together. §6.1.4 (d), (e), (f) and §6.1.5 (c), (d), (e) assign it
//!   whole. `link` receives it whole, so splitting it adds nothing.
//!   **(R)** Parameters are never inherited: §6.1.4 (e)'s inheritance applies
//!   only to an algorithm whose key needs parameters absent from the
//!   certificate (DSA), and the link instance refuses such a key.
//! - **(I) Revocation, §6.1.3 (a)(3), is a parameter** (`revoked`), so the
//!   step stays a numbered line. The production instance is "nothing is
//!   revoked" (design §1.3, Q4: browsers no longer do online OCSP for DV
//!   certificates; a pushed revocation set is Phase 8). Stapled OCSP is not
//!   read.
//! - **The policy tree is not modelled** (design §1.2, Q5). §6.1.2 (a),
//!   (e), (f); §6.1.3 (d), (e); §6.1.4 (b), (h)(2), (h)(3), (i)(2), (j); and
//!   §6.1.5 (g)'s intersection are comments at their places, not code. Only
//!   `explicit_policy` is kept, transcribed exactly ((d), (h)(1), (i)(1),
//!   §6.1.5 (a), (b)). **(R)** Where the RFC accepts when "either
//!   explicit_policy is greater than 0 or the valid_policy_tree is not equal
//!   to NULL" (§6.1.3 (f), §6.1.5's last paragraph), this accepts only when
//!   explicit_policy is greater than 0. Since nothing else reads the tree,
//!   every path accepted here is accepted by the RFC for every value the tree
//!   could have (`theorems::policy_free_sound`, design `lemma_policy_free_sound`).
//!   Non-critical certificatePolicies and inhibitAnyPolicy are therefore
//!   ignored without changing the outcome; critical ones are refused at
//!   §6.1.4 (o) and §6.1.5 (f) as unrecognized **(R)**.
//! - **(R) policyMappings refuses an intermediate** at §6.1.4 (a) whether or
//!   not it is critical, instead of decoding it and checking only for
//!   anyPolicy (design Q8). `PathCert` records only its presence.
//! - **(R) Name comparison is byte equality** of the complete DER Name TLVs,
//!   in §6.1.3 (a)(4) and in "self-issued" (design §1.10, Q10), not §7.1's
//!   comparison. Every effect is a refusal: names that §7.1 would equate
//!   fail to chain, and a certificate §7.1 would call self-issued counts as
//!   not self-issued, which only lowers `max_path_length` and
//!   `explicit_policy` sooner. CA/B BR §7.1.2.7 asks the same of issuers:
//!   "`issuer` MUST be byte-for-byte identical to the `subject` field of the
//!   Issuing CA".
//! - **Name constraints are P4's** (`name_constraints::matching::spec`).
//!   §6.1.2 (b) and (c) are one field, `subtrees`, P4's sequence of the
//!   NameConstraints values in force; its denotation is the RFC's
//!   permitted_subtrees and excluded_subtrees (P4's
//!   `within_permitted_subtrees`, `within_excluded_subtrees`). §6.1.3 (b) and
//!   (c) are `certificate_acceptable`, and §6.1.4 (g) is
//!   `prepare_name_constraints`, which refuses unsupported bases. Every **(R)**
//!   of P4's header applies, among them: **(R)** self-issued intermediates are
//!   checked too (the "skip this step" sentence of (b) and (c) is not
//!   followed: Firefox; Chrome and the RFC skip them).
//! - **(=) RFC 5937 §3.2 bullets 2 and 3**: the anchor's nameConstraints, if
//!   any, is the first set of `subtrees`, through the same
//!   `prepare_name_constraints` (an unsupported base refuses the path). The
//!   user-provided initial sets are "every name" and "none", so the
//!   intersection and union of bullets 2 and 3 are the anchor's sets.
//! - **(=) RFC 5937 §3.2 bullet 8**: an anchor pathLenConstraint p makes
//!   `max_path_length` p instead of n. The RFC places this step "prior to"
//!   §6.1.2, whose (k) would then overwrite it with n; this follows the
//!   evident intent (docs/ERRATA.md, "RFC 5937 §3.2 ... max_path_length").
//! - **(=) §6.1.4 (k)**: "Conforming implementations may choose to reject all
//!   version 1 and version 2 intermediate certificates", and this does: no
//!   out-of-band means is offered.
//! - **pathLenConstraint and requireExplicitPolicy are numbers**
//!   (`parsed::spec::skip_certs_value`, big-endian), unbounded. A value of at
//!   least n has no effect, so no size cap is needed here.
//! - **The critical extensions recognized** (§6.1.4 (o), §6.1.5 (f), design
//!   §1.6): on an intermediate, basicConstraints, keyUsage, extKeyUsage,
//!   nameConstraints, subjectAltName and policyConstraints; on the target,
//!   `leaf::spec::supported_critical_extensions`' set (subjectAltName,
//!   basicConstraints, keyUsage, extKeyUsage). Any other critical extension
//!   refuses the path, as §6.1 requires ("clients MUST reject the certificate
//!   if it contains an unsupported critical extension"). That includes a
//!   critical nameConstraints on the target, which RFC 5280 §4.2.1.10 allows
//!   only in a CA certificate (`profile.rs` refuses a non-critical one too,
//!   **(R)**). extKeyUsage on intermediates is processed by `profile.rs`.
//! - **The order of failure.** Each of §6.1.3, §6.1.4 and §6.1.5 returns the
//!   error of the first failing check in step-letter order. The RFC returns
//!   "a failure indication and an appropriate reason" without ordering them;
//!   the ordering only chooses which reason is reported.
//! - **Out of §6.1, and not here:** the target's identity, its key usage and
//!   role, every CA/B Forum rule, the anchor's validity and distrust-after,
//!   and the bounds of design §1.12 (`profile.rs`, `verifier.rs`).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Inputs and parameters
// ---------------------------------------------------------------------------

/// What §6.1.3 (a)(1) verifies: the signature on one certificate under the
/// working public key (design §3.3).
pub struct SignedData {
    /// `working_public_key`: the issuer's complete SubjectPublicKeyInfo DER.
    pub issuer_spki: Seq<u8>,
    /// The certificate's signature AlgorithmIdentifier (the TBS copy, which
    /// `prepare_signature` has checked equal to the outer one).
    pub algorithm: crate::certificate::spec::AlgorithmIdentifier,
    /// The exact TBSCertificate DER the signature covers.
    pub tbs_der: Seq<u8>,
    /// The signature BIT STRING's octets (unused bits are 0 for every
    /// supported algorithm).
    pub signature: Seq<u8>,
}

/// §6.1.3 (a)(1) as a parameter: whether the signature verifies.
pub type LinkFn = spec_fn(SignedData) -> bool;

/// §6.1.3 (a)(3) as a parameter: whether a certificate is revoked at the
/// current time (production: never; design §1.3).
pub type RevokedFn = spec_fn(super::parsed::spec::PathCert) -> bool;

/// Why a path is refused. Each variant names the step that refuses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathError {
    /// §6.1.1 (a): the path is empty.
    EmptyPath,
    /// §6.1: "A certificate MUST NOT appear more than once".
    RepeatedCertificate,
    /// §6.1.3 (a)(1), (R): the signature algorithm is not supported.
    UnsupportedAlgorithm,
    /// §6.1.3 (a)(1): the signature does not verify.
    BadSignature,
    /// §6.1.3 (a)(2): the time is outside the validity period (also when
    /// it is before notBefore).
    Expired,
    /// §6.1.3 (a)(3): the certificate is revoked.
    Revoked,
    /// §6.1.3 (a)(4): the issuer name is not working_issuer_name.
    NameChaining,
    /// §6.1.3 (b), (c): a name is outside permitted_subtrees or within
    /// excluded_subtrees.
    NameConstraint,
    /// §6.1.4 (g) and RFC 5937 §3.2: a NameConstraints this verifier does
    /// not support (malformed bases, excluded directoryName; P4).
    NameConstraintUnsupported,
    /// §6.1.3 (f) and §6.1.5 (g), (R): explicit_policy is 0.
    PolicyRequired,
    /// §6.1.4 (a), (R): a policyMappings extension.
    PolicyMappings,
    /// §6.1.4 (k): not a v3 certificate with basicConstraints cA TRUE.
    NotCa,
    /// §6.1.4 (l): max_path_length is 0.
    PathLen,
    /// §6.1.4 (n): keyUsage without keyCertSign (and, in `profile.rs`, no
    /// keyUsage at all).
    KeyUsage,
    /// §6.1.4 (o), §6.1.5 (f): an unrecognized critical extension.
    UnknownCriticalExtension,
    /// `profile.rs`: an extKeyUsage that does not allow serverAuth, or none
    /// on the target.
    ExtendedKeyUsage,
    /// `profile.rs`: the target fails the leaf checks (identity, key usage,
    /// role, validity; `leaf::spec::check_extensions`).
    Leaf,
    /// `profile.rs`, (R): the target carries nameConstraints.
    LeafNameConstraints,
    /// `profile.rs`, (R): the anchor certificate is outside its validity.
    AnchorExpired,
    /// `profile.rs`, (R): the target was issued after the anchor's
    /// `server_distrust_after`.
    Distrusted,
    /// `verifier.rs`: the presented chain is empty, its first certificate
    /// does not parse, or `now` has no `CertificateTime`.
    Malformed,
    /// `verifier.rs`, design §1.12: more intermediates than allowed.
    TooManyIntermediates,
    /// `verifier.rs`, design §1.12: more name-constraint comparisons than allowed.
    TooManyNameComparisons,
    /// `verifier.rs`: no candidate path reaches a trust anchor.
    UnknownIssuer,
    /// `verifier.rs`, design §1.12: the path search examined more candidate
    /// issuers than its budget allows (mozilla::pkix `buildForwardCallBudget`).
    BuildBudgetExhausted,
}

// ---------------------------------------------------------------------------
// §6.1: definitions used by several steps
// ---------------------------------------------------------------------------

/// §6.1: "A certificate is self-issued if the same DN appears in the subject
/// and issuer fields". (R) The DNs are compared byte for byte, not by §7.1.
pub open spec fn self_issued(cert: super::parsed::spec::PathCert) -> bool {
    cert.tbs.issuer_der == cert.tbs.subject_der
}

/// No certificate of `certs[from..]` has the DER `der`.
pub open spec fn der_absent_from(certs: Seq<super::parsed::spec::PathCert>, der: Seq<u8>, from: int) -> bool
    decreases certs.len() - from
{
    if from < 0 || from >= certs.len() { true }
    else { certs[from].der != der && der_absent_from(certs, der, from + 1) }
}

/// §6.1: "A certificate MUST NOT appear more than once in a prospective
/// certification path", for `certs[from..]`: no two DER encodings are equal.
pub open spec fn certificates_distinct_from(certs: Seq<super::parsed::spec::PathCert>, from: int) -> bool
    decreases certs.len() - from
{
    if from < 0 || from >= certs.len() { true }
    else { der_absent_from(certs, certs[from].der, from + 1) && certificates_distinct_from(certs, from + 1) }
}

/// What P4's §6.1.3 (b), (c) and §6.1.4 (g) read from a certificate: the
/// subject, the subjectAltName entries ("critical or non-critical"; none when
/// the extension is absent) and the nameConstraints extension.
pub open spec fn nc_certificate(cert: super::parsed::spec::PathCert)
    -> crate::name_constraints::matching::spec::NcCertificate
{
    crate::name_constraints::matching::spec::NcCertificate {
        subject: cert.tbs.subject_der,
        subject_alt_names: match cert.san { Some(san) => san.names, None => seq![] },
        name_constraints: cert.name_constraints,
    }
}

/// The validity period of a certificate (§4.1.2.5, inclusive).
pub open spec fn validity(cert: super::parsed::spec::PathCert) -> crate::time::spec::Validity {
    crate::time::spec::Validity { not_before: cert.tbs.not_before, not_after: cert.tbs.not_after }
}

/// The SignedData §6.1.3 (a)(1) asks `link` about.
pub open spec fn signed_data(working_public_key: Seq<u8>, cert: super::parsed::spec::PathCert) -> SignedData {
    SignedData {
        issuer_spki: working_public_key,
        algorithm: cert.signature.tbs_algorithm,
        tbs_der: cert.signature.tbs_der,
        signature: cert.signature.signature_bits,
    }
}

/// §6.1.4 (o), design §1.6: the critical extensions an intermediate may carry
/// (basicConstraints, keyUsage, extKeyUsage, nameConstraints,
/// subjectAltName, policyConstraints), for `extensions[index..]`.
pub open spec fn intermediate_critical_supported(
    extensions: Seq<crate::extensions::spec::Extension>, index: int,
) -> bool
    recommends 0 <= index <= extensions.len()
    decreases extensions.len() - index
{
    if index < 0 || index >= extensions.len() { true }
    else {
        let extension = extensions[index];
        (!extension.critical
            || extension.oid =~= crate::leaf::spec::basic_constraints_oid()
            || extension.oid =~= crate::leaf::spec::key_usage_oid()
            || extension.oid =~= crate::leaf::spec::extended_key_usage_extension_oid()
            || extension.oid =~= crate::name_constraints::spec::name_constraints_oid()
            || extension.oid =~= crate::extensions::spec::subject_alt_name_oid()
            || extension.oid =~= crate::policy_constraints::spec::policy_constraints_oid())
            && intermediate_critical_supported(extensions, index + 1)
    }
}

// ---------------------------------------------------------------------------
// §6.1.2 Initialization
// ---------------------------------------------------------------------------

/// The §6.1.2 state variables that this transcription keeps. The others are
/// noted where the RFC defines them.
pub struct State {
    // (a) valid_policy_tree: not modelled (modelling choices; design §1.2).
    /// (b) permitted_subtrees and (c) excluded_subtrees, as P4's sequence of
    /// the NameConstraints in force.
    pub subtrees: Seq<crate::name_constraints::spec::NameConstraints>,
    /// (d) explicit_policy.
    pub explicit_policy: nat,
    // (e) inhibit_anyPolicy and (f) policy_mapping: not modelled; only the
    //     policy tree reads them.
    /// (g) working_public_key_algorithm, (h) working_public_key and (i)
    /// working_public_key_parameters, together: a complete
    /// SubjectPublicKeyInfo DER.
    pub working_public_key: Seq<u8>,
    /// (j) working_issuer_name: a complete Name DER.
    pub working_issuer_name: Seq<u8>,
    /// (k) max_path_length.
    pub max_path_length: nat,
}

/// §6.1.2 "This initialization phase establishes eleven state variables
/// based upon the nine inputs", after RFC 5937 §3.2. `n` is the path length.
pub open spec fn initialization(anchor: super::parsed::spec::Anchor, n: nat) -> Result<State, PathError> {
    // RFC 5937 §3.2 bullets 2 and 3, then §6.1.2 (b) and (c): "the initial
    // value is initial-permitted-subtrees" / "initial-excluded-subtrees".
    // §6.1.1 (h), (i) give every name and no name, so the anchor's sets, if
    // any, are the whole initial state.
    match crate::name_constraints::matching::spec::prepare_name_constraints(
        crate::name_constraints::matching::spec::initial_state(), anchor.name_constraints,
    ) {
        None => Err(PathError::NameConstraintUnsupported),
        Some(subtrees) => Ok(State {
            // (a) valid_policy_tree: "a single node with valid_policy
            //     anyPolicy": not modelled.
            // (b), (c): above.
            subtrees,
            // (d) "If initial-explicit-policy is set, then the initial value
            //     is 0, otherwise the initial value is n+1." It is not set
            //     (§6.1.1 (f); RFC 5937 bullet 6 cannot set it, because
            //     `anchor_from_root` refuses an anchor with policyConstraints).
            explicit_policy: n + 1,
            // (e) inhibit_anyPolicy = n+1 and (f) policy_mapping = n+1: not
            //     modelled.
            // (g), (h), (i): "initialized from the trusted public key
            //     algorithm", "the trusted public key", "the trusted public
            //     key parameters": the anchor's SubjectPublicKeyInfo.
            working_public_key: anchor.spki_der,
            // (j) "initialized to the trusted issuer name": the anchor's subject.
            working_issuer_name: anchor.subject_der,
            // (k) "this integer is initialized to n"; RFC 5937 §3.2 bullet 8:
            //     "If a basic constraints extension is associated with the
            //     trust anchor and contains a pathLenConstraint value, set the
            //     max_path_length state variable equal to the pathLenConstraint
            //     value". RFC 5937 orders bullet 8 before (k), which would
            //     overwrite it; the evident intent is that the anchor's value
            //     wins (docs/ERRATA.md).
            max_path_length: match anchor.path_len { Some(p) => p, None => n },
        }),
    }
}

// ---------------------------------------------------------------------------
// §6.1.3 Basic Certificate Processing
// ---------------------------------------------------------------------------

/// §6.1.3: "The basic path processing actions to be performed for
/// certificate i (for all i in [1..n])". `cert` is the RFC's certificate i.
pub open spec fn basic_certificate_processing(
    link: LinkFn, revoked: RevokedFn, state: State,
    cert: super::parsed::spec::PathCert, now: crate::time::spec::CertificateTime,
) -> Result<(), PathError> {
    // (a) "Verify the basic certificate information. The certificate MUST
    //     satisfy each of the following:"
    // (a)(1) "The signature on the certificate can be verified using
    //     working_public_key_algorithm, the working_public_key, and the
    //     working_public_key_parameters." (R) Unsupported algorithms first.
    if cert.signature.class is Unsupported { Err(PathError::UnsupportedAlgorithm) }
    else if !link(signed_data(state.working_public_key, cert)) { Err(PathError::BadSignature) }
    // (a)(2) "The certificate validity period includes the current time."
    else if !crate::time::spec::validity_contains(validity(cert), now) { Err(PathError::Expired) }
    // (a)(3) "At the current time, the certificate is not revoked."
    else if revoked(cert) { Err(PathError::Revoked) }
    // (a)(4) "The certificate issuer name is the working_issuer_name."
    //     (R) byte equality.
    else if cert.tbs.issuer_der != state.working_issuer_name { Err(PathError::NameChaining) }
    // (b) "If certificate i is self-issued and it is not the final
    //     certificate in the path, skip this step for certificate i.
    //     Otherwise, verify that the subject name is within one of the
    //     permitted_subtrees for X.500 distinguished names, and verify that
    //     each of the alternative names in the subjectAltName extension
    //     (critical or non-critical) is within one of the permitted_subtrees
    //     for that name type."
    // (c) The same "is not within any of the excluded_subtrees".
    //     Both are P4's `certificate_acceptable`. (R) The self-issued skip is
    //     not taken: every certificate is checked (Firefox).
    else if !crate::name_constraints::matching::spec::certificate_acceptable(state.subtrees, nc_certificate(cert)) {
        Err(PathError::NameConstraint)
    }
    // (d) certificate policies processing and (e) "If the certificate
    //     policies extension is not present, set the valid_policy_tree to
    //     NULL": not modelled (the tree).
    // (f) "Verify that either explicit_policy is greater than 0 or the
    //     valid_policy_tree is not equal to NULL". (R) Without the tree,
    //     explicit_policy must be greater than 0.
    else if state.explicit_policy == 0 { Err(PathError::PolicyRequired) }
    // "If any of steps (a), (b), (c), or (f) fails, the procedure
    //  terminates"; otherwise continue with §6.1.4 or §6.1.5 (`process_from`).
    else { Ok(()) }
}

// ---------------------------------------------------------------------------
// §6.1.4 Preparation for Certificate i+1
// ---------------------------------------------------------------------------

/// §6.1.4 (h)(1): "If explicit_policy is not 0, decrement explicit_policy by
/// 1", applied only "If certificate i is not self-issued".
pub open spec fn explicit_policy_after_h(state: State, cert: super::parsed::spec::PathCert) -> nat {
    if !self_issued(cert) && state.explicit_policy != 0 { (state.explicit_policy - 1) as nat }
    else { state.explicit_policy }
}

/// §6.1.4 (i)(1): "If requireExplicitPolicy is present and is less than
/// explicit_policy, set explicit_policy to the value of
/// requireExplicitPolicy."
pub open spec fn explicit_policy_after_i(explicit_policy: nat, cert: super::parsed::spec::PathCert) -> nat {
    match cert.require_explicit_policy {
        Some(r) => if r < explicit_policy { r } else { explicit_policy },
        None => explicit_policy,
    }
}

/// §6.1.4 (m): "If pathLenConstraint is present in the certificate and is
/// less than max_path_length, set max_path_length to the value of
/// pathLenConstraint." (basicConstraints is present: (k) has checked it.)
pub open spec fn max_path_length_after_m(max_path_length: nat, cert: super::parsed::spec::PathCert) -> nat {
    match cert.basic {
        Some(basic) => match basic.path_len_constraint {
            Some(octets) => {
                let p = super::parsed::spec::skip_certs_value(octets);
                if p < max_path_length { p } else { max_path_length }
            },
            None => max_path_length,
        },
        None => max_path_length,
    }
}

/// §6.1.4: "To prepare for processing of certificate i+1, perform the
/// following steps for certificate i". `cert` is the RFC's certificate i,
/// never the final one. The checks the RFC lists as failures are "(a), (k),
/// (l), (n), or (o)"; (g) also fails for an unsupported NameConstraints.
pub open spec fn preparation_for_next(state: State, cert: super::parsed::spec::PathCert) -> Result<State, PathError> {
    // (a) "If a policy mappings extension is present, verify that the special
    //     value anyPolicy does not appear as an issuerDomainPolicy or a
    //     subjectDomainPolicy." (R) Any policyMappings refuses (design Q8).
    if cert.has_policy_mappings { Err(PathError::PolicyMappings) }
    // (b) the policy mappings' effect on the tree: not modelled.
    // (g) "If a name constraints extension is included in the certificate,
    //     modify the permitted_subtrees and excluded_subtrees state variables":
    //     (1) intersection and (2) union, P4's `prepare_name_constraints`;
    //     an unsupported NameConstraints refuses.
    else { match crate::name_constraints::matching::spec::prepare_name_constraints(state.subtrees, cert.name_constraints) {
        None => Err(PathError::NameConstraintUnsupported),
        Some(subtrees) => {
            // (c) "Assign the certificate subject name to working_issuer_name."
            let working_issuer_name = cert.tbs.subject_der;
            // (d) "Assign the certificate subjectPublicKey to
            //     working_public_key", (e) its parameters, (f) its algorithm:
            //     the SubjectPublicKeyInfo, whole. Parameters are never
            //     inherited (modelling choices).
            let working_public_key = cert.tbs.subject_public_key_info_der;
            // (h) "If certificate i is not self-issued: (1) If
            //     explicit_policy is not 0, decrement explicit_policy by 1."
            //     (2) policy_mapping and (3) inhibit_anyPolicy: not modelled.
            let explicit_policy = explicit_policy_after_h(state, cert);
            // (i) "If a policy constraints extension is included in the
            //     certificate": (1) requireExplicitPolicy. (2)
            //     inhibitPolicyMapping: not modelled.
            let explicit_policy = explicit_policy_after_i(explicit_policy, cert);
            // (j) inhibitAnyPolicy: not modelled (a critical one is refused by (o)).
            // (k) "If certificate i is a version 3 certificate, verify that
            //     the basicConstraints extension is present and that cA is set
            //     to TRUE." Version 1 and 2 intermediates are rejected, which
            //     "Conforming implementations may choose".
            if !(cert.tbs.version == 2 && match cert.basic { Some(basic) => basic.ca, None => false }) {
                Err(PathError::NotCa)
            }
            // (l) "If the certificate was not self-issued, verify that
            //     max_path_length is greater than zero and decrement
            //     max_path_length by 1."
            else if !self_issued(cert) && state.max_path_length == 0 { Err(PathError::PathLen) }
            else {
                let max_path_length = if !self_issued(cert) { (state.max_path_length - 1) as nat }
                    else { state.max_path_length };
                // (m) pathLenConstraint.
                let max_path_length = max_path_length_after_m(max_path_length, cert);
                // (n) "If a key usage extension is present, verify that the
                //     keyCertSign bit is set." (Present-at-all is `profile.rs`.)
                if match cert.key_usage {
                    Some(usage) => !crate::constraints::spec::key_usage_has(
                        usage, crate::constraints::spec::KeyUsageBit::KeyCertSign),
                    None => false,
                } { Err(PathError::KeyUsage) }
                // (o) "Recognize and process any other critical extension
                //     present in the certificate."
                else if !intermediate_critical_supported(cert.extensions, 0) {
                    Err(PathError::UnknownCriticalExtension)
                }
                // "If (a), (k), (l), (n), and (o) have completed successfully,
                //  increment i and perform the basic certificate processing".
                else { Ok(State { subtrees, explicit_policy, working_public_key, working_issuer_name, max_path_length }) }
            }
        },
    }}
}

// ---------------------------------------------------------------------------
// §6.1.5 Wrap-Up Procedure
// ---------------------------------------------------------------------------

/// §6.1.5 (a) and (b): explicit_policy after the wrap-up's policy steps.
pub open spec fn explicit_policy_wrapped(state: State, cert: super::parsed::spec::PathCert) -> nat {
    // (a) "If explicit_policy is not 0, decrement explicit_policy by 1."
    let explicit_policy = if state.explicit_policy != 0 { (state.explicit_policy - 1) as nat }
        else { state.explicit_policy };
    // (b) "If a policy constraints extension is included in the certificate
    //     and requireExplicitPolicy is present and has a value of 0, set the
    //     explicit_policy state variable to 0."
    if cert.require_explicit_policy == Some(0nat) { 0 } else { explicit_policy }
}

/// §6.1.5: "To complete the processing of the target certificate, perform
/// the following steps for certificate n". The result is §6.1.6's
/// working_public_key: the target's complete SubjectPublicKeyInfo DER.
pub open spec fn wrap_up(state: State, cert: super::parsed::spec::PathCert) -> Result<Seq<u8>, PathError> {
    // (a), (b): explicit_policy.
    let explicit_policy = explicit_policy_wrapped(state, cert);
    // (c) "Assign the certificate subjectPublicKey to working_public_key",
    // (d) its parameters, (e) its algorithm: the SubjectPublicKeyInfo, whole.
    let working_public_key = cert.tbs.subject_public_key_info_der;
    // (f) "Recognize and process any other critical extension present in the
    //     certificate n": the leaf set (subjectAltName, basicConstraints,
    //     keyUsage, extKeyUsage).
    if !crate::leaf::spec::supported_critical_extensions(cert.extensions, 0) {
        Err(PathError::UnknownCriticalExtension)
    }
    // (g) the intersection of the valid_policy_tree and the
    //     user-initial-policy-set: not modelled; with user-initial-policy-set
    //     any-policy, (g)(ii) makes it the whole tree.
    // "If either (1) the value of explicit_policy variable is greater than
    //  zero or (2) the valid_policy_tree is not NULL, then path processing has
    //  succeeded." (R) Without the tree, (1) only.
    else if explicit_policy == 0 { Err(PathError::PolicyRequired) }
    // §6.1.6 "returning a success indication together with ... the
    //  working_public_key" (the tree and the algorithm are inside it).
    else { Ok(working_public_key) }
}

// ---------------------------------------------------------------------------
// §6.1 The procedure: Figure 2
// ---------------------------------------------------------------------------

/// Figure 2 from certificate `certs[i]` (the RFC's certificate i+1) on, with
/// `state` as §6.1.3 finds it: "Process Cert", then "Wrap up" if it is the
/// last certificate in the path, else "Prepare for Next Cert" and repeat.
pub open spec fn process_from(
    link: LinkFn, revoked: RevokedFn, certs: Seq<super::parsed::spec::PathCert>, i: int,
    now: crate::time::spec::CertificateTime, state: State,
) -> Result<Seq<u8>, PathError>
    decreases certs.len() - i
{
    if i < 0 || i >= certs.len() { Err(PathError::EmptyPath) }
    else {
        // §6.1.3 for certificate i+1.
        match basic_certificate_processing(link, revoked, state, certs[i], now) {
            Err(e) => Err(e),
            Ok(()) =>
                // "If i is equal to n, perform the wrap-up steps listed in
                //  Section 6.1.5."
                if i == certs.len() - 1 { wrap_up(state, certs[i]) }
                // "If i is not equal to n, continue by performing the
                //  preparatory steps listed in Section 6.1.4."
                else { match preparation_for_next(state, certs[i]) {
                    Err(e) => Err(e),
                    Ok(next) => process_from(link, revoked, certs, i + 1, now, next),
                }},
        }
    }
}

/// RFC 5280 §6.1 Basic Path Validation of `certs` (certificates 1 to n)
/// under `anchor` at `now`. `Ok` carries §6.1.6's working_public_key.
pub open spec fn process(
    link: LinkFn, revoked: RevokedFn, anchor: super::parsed::spec::Anchor,
    certs: Seq<super::parsed::spec::PathCert>, now: crate::time::spec::CertificateTime,
) -> Result<Seq<u8>, PathError> {
    // §6.1.1 (a) "a prospective certification path of length n".
    if certs.len() == 0 { Err(PathError::EmptyPath) }
    // §6.1 "A certificate MUST NOT appear more than once in a prospective
    //  certification path."
    else if !certificates_distinct_from(certs, 0) { Err(PathError::RepeatedCertificate) }
    // §6.1.2, then §6.1.3 for certificate 1.
    else { match initialization(anchor, certs.len()) {
        Err(e) => Err(e),
        Ok(state) => process_from(link, revoked, certs, 0, now, state),
    }}
}

} // verus!

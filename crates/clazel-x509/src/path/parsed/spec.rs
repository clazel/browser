//! The parsed form of a certificate in a path (`PathCert`) and of a trust
//! anchor (`Anchor`): RFC 5280 §6.1.1 (d), RFC 5937 §2 and §3.2.
//!
//! Sources, pinned:
//! - RFC 5280, May 2008, <https://www.rfc-editor.org/rfc/rfc5280.txt>,
//!   SHA-256 `a2f2628c0a83b873fc4786abd921f9b2c02395954b655d190bf16b831633345d`
//!   (downloaded 2026-10-29). §4.1, §4.1.1.2, §4.2, §4.2.1.9 to §4.2.1.12,
//!   §6.1.1 (d).
//! - RFC 5937, August 2010, <https://www.rfc-editor.org/rfc/rfc5937.txt>,
//!   SHA-256 `6424a9b13e2ea7accfed71e0adef806309851909775aea74471187910f861f01`
//!   (downloaded 2026-10-29). §2 and §3.2. The RFC's rules are bullets, not
//!   numbered steps, so a citation such as "§3.2 bullet 2" counts the
//!   bullets of §3.2 from 1: (1) the subject name, (2) initial-permitted-
//!   subtrees, (3) initial-excluded-subtrees, (4) certificate policies,
//!   (5) inhibit any policy, (6) require explicit policy, (7) inhibit policy
//!   mapping, (8) basic constraints pathLenConstraint.
//! - The path-validation design (`.claude/plans/path-validation.md`, not in
//!   the repository): §1.4 (trust anchors), §1.6 (unknown critical
//!   extensions), §1.7, §2.1 (the `PathCert` notation), §3.2 and question
//!   Q9, all as accepted.
//!
//! This file parses no bytes. It composes the crate's decoders, each of which
//! is proven against its own spec: `certificate::spec::parse_certificate`,
//! `tbs::spec::parse_tbs_certificate`, `extensions::spec::parse_extensions`
//! and `parse_subject_alt_name`, `constraints::spec::parse_basic_constraints`,
//! `parse_key_usage` and `parse_extended_key_usage`,
//! `name_constraints::spec::parse_name_constraints`,
//! `policy_constraints::spec::parse_policy_constraints`,
//! `signature_algorithm::spec::prepare_signature` and
//! `time::spec::decode_time`.
//!
//! Modelling choices. A refusal that RFC 5280 or RFC 5937 does not require is
//! marked **(R)**.
//! - **`PathCert` is the design's field list** (§2.1) with one change of
//!   type: the design writes `require_explicit_policy: Option<nat>` and the
//!   decoder returns the SkipCerts as canonical magnitude octets (at most
//!   four), so the field is `clazel_der::spec::be_value` of those octets.
//!   `inhibitPolicyMapping` is decoded and dropped, because only the policy
//!   tree reads it (design §1.2, not modelled).
//! - **A certificate without extensions** (v1, v2, or v3 with no `[3]`) has
//!   `extensions == seq![]` and every extension field `None`/`false`.
//!   `parse_extensions` refuses a present but empty `Extensions`, and
//!   duplicate OIDs (RFC 5280 §4.1.2.9: "A certificate MUST NOT include more
//!   than one instance of a particular extension").
//! - **(R) A recognized extension that does not decode refuses the
//!   certificate**, whether or not it is critical. Recognized here are
//!   basicConstraints, keyUsage, extKeyUsage, subjectAltName, nameConstraints
//!   and policyConstraints, and every one is decoded on every certificate,
//!   leaf or CA: which of them matters for which position is §6.1's
//!   business, not the parser's. RFC 5280 §4.2 requires a refusal only for a
//!   critical extension that cannot be processed; a malformed non-critical
//!   one is undefined there. `leaf::spec::check_extensions` refuses the same
//!   way. Design §3.2 step 3: a certificate that does not parse is dropped
//!   from the pool, so the effect is that it cannot be used.
//! - **Unknown critical extensions are not refused here.** `extensions` keeps
//!   every extension with its `critical` flag, and design §1.6 has the §6.1
//!   spec refuse an unprocessed critical one (§6.1.3, §6.1.4 (o),
//!   §6.1.5 (f)). The same for a critical `inhibitAnyPolicy`,
//!   `certificatePolicies` and `policyMappings`.
//! - **policyMappings** (2.5.29.33) is not decoded: `has_policy_mappings`
//!   records that the extension is present, because design §1.2 and
//!   question Q8 refuse any certificate that carries it at §6.1.4 (a).
//! - **The signature** is `prepare_signature` over the TBS algorithm, the
//!   outer algorithm, the exact TBS bytes and the signature bits. It refuses
//!   a certificate whose two AlgorithmIdentifiers disagree (RFC 5280
//!   §4.1.1.2: "This field MUST contain the same algorithm identifier as the
//!   signature field in the sequence tbsCertificate"), and **(R)** a
//!   supported (RSA or ECDSA) signature whose BIT STRING has unused bits.
//!   Unsupported algorithms parse, with class `Unsupported`; the link
//!   verifier refuses them.
//! - **The SubjectPublicKeyInfo is not decoded here.** The design's field
//!   list has no key field and `tbs.subject_public_key_info_der` is what
//!   §6.1.4 (d) to (f) pass on whole, so a certificate whose key the SPKI
//!   decoder refuses still parses. This is a deliberate gap, not a rule: see
//!   the report that goes with this file.
//! - **`Anchor` is the design's field list** (§1.4) with the same change of
//!   type for `path_len` (`be_value` of the pathLenConstraint octets), and
//!   one more input: `anchor_from_root` takes the table's
//!   `server_distrust_after` text as its second argument, because that value
//!   is not in the certificate. The text is the `YYMMDDHHMMSSZ` UTCTime
//!   contents, decoded by `time::spec::decode_time`. **(R)** text that does
//!   not decode refuses the anchor.
//! - **The anchor's own signature is never read** (design §1.4), so
//!   `anchor_from_root` does not call `prepare_signature`, and a root with a
//!   signature algorithm no path could use still yields an anchor.
//!   Self-issuance is not required either.
//! - **RFC 5937 is enforced** (enforceTrustAnchorConstraints = TRUE, which
//!   §3.1 makes the only choice of an implementation that does not offer the
//!   flag):
//!   - §2: "clients MUST reject certification paths containing a trust
//!     anchor with unrecognized critical extensions". The recognized set is
//!     basicConstraints, keyCertSign/keyUsage, extKeyUsage and
//!     nameConstraints, the ones read below.
//!   - §3.2 bullet 1: no subject name refuses. **(R)** An empty subject
//!     (`SEQUENCE {}`) counts as none.
//!   - §3.2 bullets 2 and 3: the nameConstraints extension, if any, is the
//!     anchor's `name_constraints`. The intersection and union with the
//!     user's initial sets are §6.1.2 (b) and (c) in the §6.1 spec, which
//!     starts from an empty user set.
//!   - §3.2 bullet 8: the pathLenConstraint of basicConstraints, if any, is
//!     `path_len`. How it caps `max_path_length` is §6.1.2 (k).
//!   - **(R)** §3.2 bullets 5 to 7: an anchor with an `inhibitAnyPolicy` or
//!     `policyConstraints` extension is refused, because the policy tree is
//!     not modelled (design §1.2) and the bullets would set
//!     initial-any-policy-inhibit, initial-explicit-policy or
//!     initial-policy-mapping-inhibit. No Mozilla root carries either.
//!   - **(I)** §3.2 bullet 4: an anchor's `certificatePolicies` is ignored,
//!     as the browsers do. Four Mozilla roots carry it, so refusing would
//!     refuse them; with the policy tree not modelled, the user-initial-
//!     policy-set it would narrow is not read.
//! - **(R) Anchor role** (design §1.4, mozilla::pkix): the anchor must have
//!   basicConstraints with cA TRUE, and keyUsage with keyCertSign when
//!   keyUsage is present.
//! - **(R) Anchor EKU** (design §1.4): an extKeyUsage that lacks serverAuth
//!   refuses the anchor (anyExtendedKeyUsage is not accepted).
//! - **Anchor validity is not checked here.** `not_before` and `not_after`
//!   are carried, and checking them at `now` is design Q9's **(R)**, made in
//!   the §6.1 spec. The distrust-after check is likewise a comparison against
//!   the leaf's `notBefore` there.
//! - **Name constraints of an anchor are decoded, not vetted.** Whether every
//!   base is one `name_constraints::matching` supports is checked where the
//!   state is built (§6.1.4 (g)), for the anchor's set as for any other.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One certificate of a path, decoded (design §2.1).
pub struct PathCert {
    /// The complete certificate DER.
    pub der: Seq<u8>,
    /// RFC 5280 §4.1 outer fields.
    pub envelope: crate::certificate::spec::CertificateEnvelope,
    /// RFC 5280 §4.1.2 TBSCertificate fields.
    pub tbs: crate::tbs::spec::TbsCertificate,
    /// Every extension, in encoded order, with its criticality.
    pub extensions: Seq<crate::extensions::spec::Extension>,
    /// basicConstraints (§4.2.1.9), if present.
    pub basic: Option<crate::constraints::spec::BasicConstraints>,
    /// keyUsage (§4.2.1.3), if present.
    pub key_usage: Option<crate::constraints::spec::KeyUsage>,
    /// extKeyUsage (§4.2.1.12), if present.
    pub eku: Option<crate::constraints::spec::ExtendedKeyUsage>,
    /// nameConstraints (§4.2.1.10), if present.
    pub name_constraints: Option<crate::name_constraints::spec::NameConstraints>,
    /// subjectAltName (§4.2.1.6), if present.
    pub san: Option<crate::extensions::spec::SubjectAltName>,
    /// `requireExplicitPolicy` of policyConstraints (§4.2.1.11), if present.
    pub require_explicit_policy: Option<nat>,
    /// Whether the policyMappings extension (§4.2.1.5) is present.
    pub has_policy_mappings: bool,
    /// The signature inputs (§4.1.1.2, §4.1.1.3).
    pub signature: crate::signature_algorithm::spec::PreparedSignature,
}

/// A trust anchor, extracted from a root certificate (design §1.4).
pub struct Anchor {
    /// The anchor's subject Name, the complete DER TLV.
    pub subject_der: Seq<u8>,
    /// The anchor's complete SubjectPublicKeyInfo DER.
    pub spki_der: Seq<u8>,
    /// The anchor's nameConstraints (RFC 5937 §3.2 bullets 2 and 3).
    pub name_constraints: Option<crate::name_constraints::spec::NameConstraints>,
    /// The anchor's pathLenConstraint (RFC 5937 §3.2 bullet 8).
    pub path_len: Option<nat>,
    /// The start of the anchor certificate's validity.
    pub not_before: crate::time::spec::CertificateTime,
    /// The end of the anchor certificate's validity.
    pub not_after: crate::time::spec::CertificateTime,
    /// NSS `CKA_NSS_SERVER_DISTRUST_AFTER`, if the table carries one.
    pub server_distrust_after: Option<crate::time::spec::CertificateTime>,
}

/// id-ce-policyMappings `{ 2 5 29 33 }`.
pub open spec fn policy_mappings_oid() -> Seq<nat> { seq![2nat, 5, 29, 33] }

/// id-ce-inhibitAnyPolicy `{ 2 5 29 54 }`.
pub open spec fn inhibit_any_policy_oid() -> Seq<nat> { seq![2nat, 5, 29, 54] }

/// Whether an extension with this OID is present (extension lists are
/// duplicate-free).
pub open spec fn has_extension(extensions: Seq<crate::extensions::spec::Extension>, oid: Seq<nat>) -> bool {
    crate::leaf::spec::find_extension_index(extensions, oid, 0) is Some
}

/// The SkipCerts octets as the number they spell (design §1.7: the spec
/// needs a `nat`; any value at least the path length behaves alike).
pub open spec fn skip_certs_value(octets: Seq<u8>) -> nat {
    clazel_der::spec::be_value(octets)
}

/// The Extensions of a TBSCertificate: none when the `[3]` field is absent.
/// `None` when it is present and `parse_extensions` refuses it.
pub open spec fn tbs_extensions(tbs: crate::tbs::spec::TbsCertificate)
    -> Option<Seq<crate::extensions::spec::Extension>>
{
    match tbs.extensions_sequence_der {
        None => Some(seq![]),
        Some(encoded) => crate::extensions::spec::parse_extensions(encoded),
    }
}

/// Decode an optional subjectAltName; outer `None` means malformed.
pub open spec fn optional_subject_alt_name(extensions: Seq<crate::extensions::spec::Extension>)
    -> Option<Option<crate::extensions::spec::SubjectAltName>>
{
    match crate::leaf::spec::find_extension_index(extensions, crate::extensions::spec::subject_alt_name_oid(), 0) {
        None => Some(None),
        Some(index) => match crate::extensions::spec::parse_subject_alt_name(extensions[index].value) {
            Some(value) => Some(Some(value)), None => None,
        },
    }
}

/// Decode an optional nameConstraints; outer `None` means malformed.
pub open spec fn optional_name_constraints(extensions: Seq<crate::extensions::spec::Extension>)
    -> Option<Option<crate::name_constraints::spec::NameConstraints>>
{
    match crate::leaf::spec::find_extension_index(extensions, crate::name_constraints::spec::name_constraints_oid(), 0) {
        None => Some(None),
        Some(index) => match crate::name_constraints::spec::parse_name_constraints(extensions[index].value) {
            Some(value) => Some(Some(value)), None => None,
        },
    }
}

/// Decode an optional policyConstraints; outer `None` means malformed.
pub open spec fn optional_policy_constraints(extensions: Seq<crate::extensions::spec::Extension>)
    -> Option<Option<crate::policy_constraints::spec::PolicyConstraints>>
{
    match crate::leaf::spec::find_extension_index(extensions, crate::policy_constraints::spec::policy_constraints_oid(), 0) {
        None => Some(None),
        Some(index) => match crate::policy_constraints::spec::parse_policy_constraints(extensions[index].value) {
            Some(value) => Some(Some(value)), None => None,
        },
    }
}

/// `requireExplicitPolicy` of an optional policyConstraints, as a number.
pub open spec fn require_explicit_policy_of(
    constraints: Option<crate::policy_constraints::spec::PolicyConstraints>,
) -> Option<nat> {
    match constraints {
        Some(value) => match value.require_explicit_policy {
            Some(octets) => Some(skip_certs_value(octets)),
            None => None,
        },
        None => None,
    }
}

/// Design §3.2, `parse_path_cert`: the decoders composed, in the order of
/// RFC 5280 §4.1: the outer Certificate, its TBSCertificate, the
/// Extensions, each recognized extension, and the signature inputs.
pub open spec fn parse_path_cert(der: Seq<u8>) -> Option<PathCert> {
    // 1. RFC 5280 §4.1: Certificate ::= SEQUENCE { tbsCertificate,
    //    signatureAlgorithm, signatureValue }.
    match crate::certificate::spec::parse_certificate(der) {
        None => None,
        Some(envelope) =>
        // 2. §4.1.2: the TBSCertificate, from the exact bytes the signature covers.
        match crate::tbs::spec::parse_tbs_certificate(envelope.tbs_certificate_der) {
            None => None,
            Some(tbs) =>
            // 3. §4.1.2.9: the Extensions, when the [3] field is present.
            match tbs_extensions(tbs) {
                None => None,
                Some(extensions) =>
                // 4. §4.2.1.9, .3, .12, .6, .10, .11: the recognized extensions.
                match (
                    crate::leaf::spec::optional_basic_constraints(extensions),
                    crate::leaf::spec::optional_key_usage(extensions),
                    crate::leaf::spec::optional_extended_key_usage(extensions),
                    optional_name_constraints(extensions),
                    optional_subject_alt_name(extensions),
                    optional_policy_constraints(extensions),
                ) {
                    (Some(basic), Some(key_usage), Some(eku), Some(name_constraints), Some(san), Some(policy)) =>
                    // 5. §4.1.1.2: the two signature AlgorithmIdentifiers agree.
                    match crate::signature_algorithm::spec::prepare_signature(
                        tbs.signature, envelope.signature_algorithm, envelope.tbs_certificate_der,
                        envelope.signature_bits, envelope.signature_unused_bits,
                    ) {
                        None => None,
                        Some(signature) => Some(PathCert {
                            der, envelope, tbs, extensions, basic, key_usage, eku, name_constraints, san,
                            require_explicit_policy: require_explicit_policy_of(policy),
                            // 6. Q8: policyMappings is recorded, not decoded.
                            has_policy_mappings: has_extension(extensions, policy_mappings_oid()),
                            signature,
                        }),
                    },
                    _ => None,
                },
            },
        },
    }
}

/// RFC 5937 §2: every critical extension of the anchor is one this module
/// reads (basicConstraints, keyUsage, extKeyUsage, nameConstraints).
pub open spec fn anchor_critical_supported(
    extensions: Seq<crate::extensions::spec::Extension>, index: int,
) -> bool
    recommends 0 <= index <= extensions.len()
    decreases extensions.len() as int - index
{
    if index >= extensions.len() { true }
    else {
        let extension = extensions[index];
        (!extension.critical
            || extension.oid =~= crate::leaf::spec::basic_constraints_oid()
            || extension.oid =~= crate::leaf::spec::key_usage_oid()
            || extension.oid =~= crate::leaf::spec::extended_key_usage_extension_oid()
            || extension.oid =~= crate::name_constraints::spec::name_constraints_oid())
            && anchor_critical_supported(extensions, index + 1)
    }
}

/// RFC 5937 §3.2 bullet 1: the anchor has a subject name. **(R)** The empty
/// Name `SEQUENCE {}` is none.
pub open spec fn anchor_has_subject(subject_der: Seq<u8>) -> bool {
    subject_der != seq![0x30u8, 0x00u8]
}

/// **(R)** RFC 5937 §3.2 bullets 5 to 7: the anchor carries no
/// `inhibitAnyPolicy` or `policyConstraints`, which the policy tree (not
/// modelled) would have to honour.
pub open spec fn anchor_policy_inputs_absent(extensions: Seq<crate::extensions::spec::Extension>) -> bool {
    !has_extension(extensions, inhibit_any_policy_oid())
        && !has_extension(extensions, crate::policy_constraints::spec::policy_constraints_oid())
}

/// RFC 5937 §3.2 bullet 8: the pathLenConstraint of basicConstraints, as a number.
pub open spec fn anchor_path_len(basic: crate::constraints::spec::BasicConstraints) -> Option<nat> {
    match basic.path_len_constraint {
        Some(octets) => Some(skip_certs_value(octets)),
        None => None,
    }
}

/// **(R)** Anchor role: cA TRUE, and keyCertSign if keyUsage is present.
pub open spec fn anchor_role_allowed(
    basic: crate::constraints::spec::BasicConstraints,
    key_usage: Option<crate::constraints::spec::KeyUsage>,
) -> bool {
    basic.ca && match key_usage {
        Some(usage) => crate::constraints::spec::key_usage_has(
            usage, crate::constraints::spec::KeyUsageBit::KeyCertSign),
        None => true,
    }
}

/// **(R)** Anchor EKU: absent, or it contains serverAuth (not anyEKU).
pub open spec fn anchor_eku_allowed(eku: Option<crate::constraints::spec::ExtendedKeyUsage>) -> bool {
    match eku {
        Some(value) => crate::constraints::spec::eku_allows_server_auth(value, false),
        None => true,
    }
}

/// The table's `CKA_NSS_SERVER_DISTRUST_AFTER` text, decoded as a UTCTime
/// (design §1.4). Outer `None` means the text does not decode.
pub open spec fn decode_distrust_after(text: Option<Seq<u8>>)
    -> Option<Option<crate::time::spec::CertificateTime>>
{
    match text {
        None => Some(None),
        Some(bytes) => match crate::time::spec::decode_time(crate::time::spec::TimeKind::Utc, bytes) {
            Some(time) => Some(Some(time)),
            None => None,
        },
    }
}

/// Design §1.4, `anchor_from_root`: the name, key, constraints and validity of
/// a root certificate, under RFC 5937 §2 and §3.2.
pub open spec fn anchor_from_root(der: Seq<u8>, server_distrust_after: Option<Seq<u8>>) -> Option<Anchor> {
    // 1. The root is a Certificate with a TBSCertificate (RFC 5280 §4.1). Its
    //    signature is not read (design §1.4: the anchor's own signature is never checked).
    match crate::certificate::spec::parse_certificate(der) {
        None => None,
        Some(envelope) => match crate::tbs::spec::parse_tbs_certificate(envelope.tbs_certificate_der) {
            None => None,
            Some(tbs) => match tbs_extensions(tbs) {
                None => None,
                Some(extensions) => {
                    // 2. RFC 5937 §2: unrecognized critical extensions refuse.
                    // 3. (R) RFC 5937 §3.2 bullets 5 to 7: policy inputs that are not modelled refuse.
                    if !anchor_critical_supported(extensions, 0)
                        || !anchor_policy_inputs_absent(extensions)
                        // 4. RFC 5937 §3.2 bullet 1: a subject name.
                        || !anchor_has_subject(tbs.subject_der) { None }
                    else { match (
                        crate::leaf::spec::optional_basic_constraints(extensions),
                        crate::leaf::spec::optional_key_usage(extensions),
                        crate::leaf::spec::optional_extended_key_usage(extensions),
                        optional_name_constraints(extensions),
                        decode_distrust_after(server_distrust_after),
                    ) {
                        // 5. (R) The role and EKU checks.
                        (Some(Some(basic)), Some(key_usage), Some(eku), Some(name_constraints), Some(distrust))
                            if anchor_role_allowed(basic, key_usage) && anchor_eku_allowed(eku) =>
                            Some(Anchor {
                                subject_der: tbs.subject_der,
                                spki_der: tbs.subject_public_key_info_der,
                                // 6. RFC 5937 §3.2 bullets 2 and 3.
                                name_constraints,
                                // 7. RFC 5937 §3.2 bullet 8.
                                path_len: anchor_path_len(basic),
                                not_before: tbs.not_before,
                                not_after: tbs.not_after,
                                server_distrust_after: distrust,
                            }),
                        _ => None,
                    }}
                },
            },
        },
    }
}

} // verus!

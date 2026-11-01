//! Known answers for the executable §6.1 fold and the verdict on one
//! candidate (`path::exec`, design `path-validation.md` §2.2 to §2.6),
//! which Verus proves equal to `path/spec.rs`, `profile.rs` and
//! `verifier.rs`. The tests check the proven code runs as the spec reads.
//!
//! - Small chains are built by hand from the ASN.1 (as `path_parsed.rs`
//!   does): every expected verdict follows from RFC 5280 §6.1 and the
//!   profile, not from the code under test. Signatures are dummies, so the
//!   link verifier is a test double: one that accepts every link, or one
//!   that refuses the links of a chosen certificate.
//! - A handful of x509-limbo testcases run through `candidate_verdict`, the
//!   path being limbo's chain as its descriptions draw it (the anchor's
//!   child first, each intermediate the issuer of the next by name), with the
//!   accept-all link verifier. Signatures are not checked here, so a limbo
//!   `FAILURE` that rests only on a signature would differ; none of the
//!   chosen cases does. The limbo pin lists of `conformance_limbo.rs` are
//!   not touched (P12).

use std::net::IpAddr;

use clazel_x509::certificate::exec::AlgorithmIdentifier;
use clazel_x509::matcher::ReferenceIdentity;
use clazel_x509::path::contract::{LinkVerifier, RevocationOracle};
use clazel_x509::path::exec::{
    Candidate, Environment, candidate_verdict, chain_inputs, path_profile, path_within_budget,
    process,
};
use clazel_x509::path::parsed::exec::{Anchor, PathCert, anchor_from_root, parse_path_cert};
use clazel_x509::path::spec::PathError;
use clazel_x509::time::exec::CertificateTime;

// ---------------------------------------------------------------------------
// Test doubles
// ---------------------------------------------------------------------------

/// Accepts every link.
struct AcceptAll;

impl LinkVerifier for AcceptAll {
    fn verify(&self, _: &[u8], _: &AlgorithmIdentifier<'_>, _: &[u8], _: &[u8]) -> bool {
        true
    }
}

/// Refuses the signature on the certificate whose TBSCertificate is `refused`.
struct RefuseOne<'r> {
    refused: &'r [u8],
}

impl LinkVerifier for RefuseOne<'_> {
    fn verify(&self, _: &[u8], _: &AlgorithmIdentifier<'_>, tbs_der: &[u8], _: &[u8]) -> bool {
        tbs_der != self.refused
    }
}

/// Nothing is revoked (the production oracle).
struct NotRevoked;

impl RevocationOracle for NotRevoked {
    fn is_revoked(&self, _: &PathCert<'_>) -> bool {
        false
    }
}

/// Everything is revoked.
struct AllRevoked;

impl RevocationOracle for AllRevoked {
    fn is_revoked(&self, _: &PathCert<'_>) -> bool {
        true
    }
}

// ---------------------------------------------------------------------------
// DER
// ---------------------------------------------------------------------------

/// One DER TLV; bodies up to 65,535 octets.
fn tlv(tag: u8, body: &[u8]) -> Vec<u8> {
    let mut out = vec![tag];
    let [high, low] = u16::try_from(body.len()).unwrap_or(0).to_be_bytes();
    if body.len() < 128 {
        out.push(low);
    } else if body.len() < 256 {
        out.extend_from_slice(&[0x81, low]);
    } else {
        out.extend_from_slice(&[0x82, high, low]);
    }
    out.extend_from_slice(body);
    out
}

/// `Name` with one commonName.
fn name(common_name: &str) -> Vec<u8> {
    let attribute = [
        &[0x06, 0x03, 0x55, 0x04, 0x03][..],
        &tlv(0x0C, common_name.as_bytes()),
    ]
    .concat();
    tlv(0x30, &tlv(0x31, &tlv(0x30, &attribute)))
}

/// ecdsa-with-SHA256.
const ECDSA_SHA256: &[u8] = &[
    0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02,
];

const BASIC_CONSTRAINTS: &[u8] = &[0x55, 0x1D, 0x13];
const KEY_USAGE: &[u8] = &[0x55, 0x1D, 0x0F];
const EXT_KEY_USAGE: &[u8] = &[0x55, 0x1D, 0x25];
const SUBJECT_ALT_NAME: &[u8] = &[0x55, 0x1D, 0x11];
const NAME_CONSTRAINTS: &[u8] = &[0x55, 0x1D, 0x1E];
/// An OID no decoder knows.
const UNKNOWN: &[u8] = &[0x2A, 0x03, 0x04];

/// `Extension ::= SEQUENCE { extnID, critical DEFAULT FALSE, extnValue }`.
fn ext(oid: &[u8], critical: bool, value: &[u8]) -> Vec<u8> {
    let mut body = tlv(0x06, oid);
    if critical {
        body.extend_from_slice(&[0x01, 0x01, 0xFF]);
    }
    body.extend_from_slice(&tlv(0x04, value));
    tlv(0x30, &body)
}

/// `BasicConstraints { cA TRUE }`, with a pathLenConstraint if given.
fn bc_ca(path_len: Option<u8>) -> Vec<u8> {
    let mut body = vec![0x01, 0x01, 0xFF];
    if let Some(p) = path_len {
        body.extend_from_slice(&[0x02, 0x01, p]);
    }
    tlv(0x30, &body)
}

/// KeyUsage keyCertSign (bit 5).
const KU_KEY_CERT_SIGN: &[u8] = &[0x03, 0x02, 0x02, 0x04];
/// KeyUsage digitalSignature (bit 0).
const KU_DIGITAL_SIGNATURE: &[u8] = &[0x03, 0x02, 0x07, 0x80];
/// ExtKeyUsage { id-kp-serverAuth }.
const EKU_SERVER_AUTH: &[u8] = &[
    0x30, 0x0A, 0x06, 0x08, 0x2B, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01,
];
/// ExtKeyUsage { id-kp-clientAuth }.
const EKU_CLIENT_AUTH: &[u8] = &[
    0x30, 0x0A, 0x06, 0x08, 0x2B, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x02,
];

/// `count` dNSName entries `host`, as a subjectAltName value.
fn san(host: &str, count: usize) -> Vec<u8> {
    let entry = tlv(0x82, host.as_bytes());
    tlv(0x30, &entry.repeat(count))
}

/// NameConstraints with `count` permitted dNSName subtrees `base`.
fn nc_permit(base: &str, count: usize) -> Vec<u8> {
    let subtree = tlv(0x30, &tlv(0x82, base.as_bytes()));
    tlv(0x30, &tlv(0xA0, &subtree.repeat(count)))
}

/// A certificate under construction.
struct Builder {
    serial: u8,
    issuer: Vec<u8>,
    subject: Vec<u8>,
    key: u8,
    extensions: Vec<Vec<u8>>,
    validity: (&'static str, &'static str),
}

impl Builder {
    fn new(serial: u8, issuer: &str, subject: &str, key: u8) -> Self {
        Self {
            serial,
            issuer: name(issuer),
            subject: name(subject),
            key,
            extensions: Vec::new(),
            validity: ("200101000000Z", "400101000000Z"),
        }
    }

    /// A CA: basicConstraints cA (pathLenConstraint `path_len`), keyUsage keyCertSign.
    fn ca(serial: u8, issuer: &str, subject: &str, key: u8, path_len: Option<u8>) -> Self {
        Self::new(serial, issuer, subject, key)
            .with(ext(BASIC_CONSTRAINTS, true, &bc_ca(path_len)))
            .with(ext(KEY_USAGE, true, KU_KEY_CERT_SIGN))
    }

    /// A leaf for `example.com`: subjectAltName, keyUsage digitalSignature, extKeyUsage serverAuth.
    fn leaf(serial: u8, issuer: &str) -> Self {
        Self::new(serial, issuer, "leaf", 9)
            .with(ext(SUBJECT_ALT_NAME, false, &san("example.com", 1)))
            .with(ext(KEY_USAGE, true, KU_DIGITAL_SIGNATURE))
            .with(ext(EXT_KEY_USAGE, false, EKU_SERVER_AUTH))
    }

    fn with(mut self, extension: Vec<u8>) -> Self {
        self.extensions.push(extension);
        self
    }

    fn build(&self) -> Vec<u8> {
        let spki = tlv(
            0x30,
            &[
                &[
                    0x30, 0x13, 0x06, 0x07, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01, 0x06, 0x08,
                    0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07,
                ][..],
                &tlv(0x03, &[&[0x00, 0x04][..], &[self.key; 64]].concat()),
            ]
            .concat(),
        );
        let validity = tlv(
            0x30,
            &[
                tlv(0x17, self.validity.0.as_bytes()),
                tlv(0x17, self.validity.1.as_bytes()),
            ]
            .concat(),
        );
        let mut tbs = vec![0xA0, 0x03, 0x02, 0x01, 0x02, 0x02, 0x01, self.serial];
        tbs.extend_from_slice(ECDSA_SHA256);
        tbs.extend_from_slice(&self.issuer);
        tbs.extend_from_slice(&validity);
        tbs.extend_from_slice(&self.subject);
        tbs.extend_from_slice(&spki);
        if !self.extensions.is_empty() {
            tbs.extend_from_slice(&tlv(0xA3, &tlv(0x30, &self.extensions.concat())));
        }
        let mut body = tlv(0x30, &tbs);
        body.extend_from_slice(ECDSA_SHA256);
        body.extend_from_slice(&tlv(0x03, &[&[0x00][..], &[0x22; 8]].concat()));
        tlv(0x30, &body)
    }
}

/// `value`, or the reason a test cannot go on.
fn need<T>(value: Option<T>, what: &str) -> Result<T, String> {
    value.ok_or_else(|| what.to_owned())
}

/// 2026-06-01T00:00:00Z.
fn now() -> CertificateTime {
    CertificateTime {
        year: 2026,
        month: 6,
        day: 1,
        hour: 0,
        minute: 0,
        second: 0,
    }
}

/// The root `root`, self-issued, with key 1.
fn root(path_len: Option<u8>) -> Builder {
    Builder::ca(1, "root", "root", 1, path_len)
}

const DNS: ReferenceIdentity<'static> = ReferenceIdentity::Dns(b"example.com");

/// Parse each DER and run `process` under the root's anchor.
fn run_with<L: LinkVerifier, R: RevocationOracle>(
    link: &L,
    revoked: &R,
    root_der: &[u8],
    ders: &[Vec<u8>],
    at: &CertificateTime,
) -> Result<Result<Vec<u8>, PathError>, String> {
    let anchor = need(anchor_from_root(root_der, None), "anchor")?;
    let parsed: Vec<PathCert<'_>> = ders
        .iter()
        .map(|der| need(parse_path_cert(der), "certificate"))
        .collect::<Result<_, _>>()?;
    let certs: Vec<&PathCert<'_>> = parsed.iter().collect();
    Ok(process(link, revoked, &anchor, &certs, at).map(<[u8]>::to_vec))
}

fn run(root_der: &[u8], ders: &[Vec<u8>]) -> Result<Result<Vec<u8>, PathError>, String> {
    run_with(&AcceptAll, &NotRevoked, root_der, ders, &now())
}

/// The key `process` returns for a leaf built with `Builder::leaf`.
fn leaf_key(leaf_der: &[u8]) -> Result<Vec<u8>, String> {
    let leaf = need(parse_path_cert(leaf_der), "leaf")?;
    Ok(leaf.tbs.subject_public_key_info_der.to_vec())
}

// ---------------------------------------------------------------------------
// §6.1, accepted
// ---------------------------------------------------------------------------

#[test]
fn a_two_certificate_path_returns_the_leaf_key() -> Result<(), String> {
    let leaf = Builder::leaf(3, "int").build();
    let path = [Builder::ca(2, "root", "int", 2, None).build(), leaf.clone()];
    assert_eq!(run(&root(None).build(), &path)?, Ok(leaf_key(&leaf)?));
    Ok(())
}

#[test]
fn a_leaf_directly_under_the_anchor_is_accepted() -> Result<(), String> {
    let leaf = Builder::leaf(3, "root").build();
    assert_eq!(
        run(&root(None).build(), std::slice::from_ref(&leaf))?,
        Ok(leaf_key(&leaf)?)
    );
    Ok(())
}

#[test]
fn a_self_issued_intermediate_does_not_count_against_path_len() -> Result<(), String> {
    // §6.1.4 (l): only non-self-issued certificates decrement max_path_length.
    let leaf = Builder::leaf(5, "int").build();
    let path = [
        Builder::ca(2, "root", "int", 2, Some(0)).build(),
        Builder::ca(3, "int", "int", 3, None).build(),
        leaf.clone(),
    ];
    assert_eq!(run(&root(None).build(), &path)?, Ok(leaf_key(&leaf)?));
    Ok(())
}

// ---------------------------------------------------------------------------
// §6.1, refused
// ---------------------------------------------------------------------------

#[test]
fn the_empty_path_and_a_repeated_certificate_are_refused() -> Result<(), String> {
    let root_der = root(None).build();
    assert_eq!(run(&root_der, &[])?, Err(PathError::EmptyPath));
    let int = Builder::ca(2, "root", "int", 2, None).build();
    let path = [int.clone(), int, Builder::leaf(3, "int").build()];
    assert_eq!(run(&root_der, &path)?, Err(PathError::RepeatedCertificate));
    Ok(())
}

#[test]
fn a_link_that_does_not_verify_is_refused() -> Result<(), String> {
    let int_der = Builder::ca(2, "root", "int", 2, None).build();
    let int = need(parse_path_cert(&int_der), "intermediate")?;
    let refused = int.envelope.tbs_certificate_der.to_vec();
    let path = [int_der.clone(), Builder::leaf(3, "int").build()];
    let link = RefuseOne { refused: &refused };
    let out = run_with(&link, &NotRevoked, &root(None).build(), &path, &now())?;
    assert_eq!(out, Err(PathError::BadSignature));
    Ok(())
}

#[test]
fn time_revocation_and_names_are_checked_in_step_order() -> Result<(), String> {
    let root_der = root(None).build();
    let path = [
        Builder::ca(2, "root", "int", 2, None).build(),
        Builder::leaf(3, "int").build(),
    ];
    // §6.1.3 (a)(2): after notAfter.
    let late = CertificateTime {
        year: 2041,
        month: 1,
        day: 1,
        hour: 0,
        minute: 0,
        second: 0,
    };
    assert_eq!(
        run_with(&AcceptAll, &NotRevoked, &root_der, &path, &late)?,
        Err(PathError::Expired)
    );
    // §6.1.3 (a)(3).
    assert_eq!(
        run_with(&AcceptAll, &AllRevoked, &root_der, &path, &now())?,
        Err(PathError::Revoked)
    );
    // §6.1.3 (a)(4): the leaf names another issuer.
    let unchained = [
        Builder::ca(2, "root", "int", 2, None).build(),
        Builder::leaf(3, "other").build(),
    ];
    assert_eq!(run(&root_der, &unchained)?, Err(PathError::NameChaining));
    Ok(())
}

#[test]
fn path_len_constraints_are_enforced() -> Result<(), String> {
    let leaf = Builder::leaf(4, "in2").build();
    // §6.1.4 (l), (m): int's pathLenConstraint 0 allows no further CA.
    let path = [
        Builder::ca(2, "root", "int", 2, Some(0)).build(),
        Builder::ca(3, "int", "in2", 3, None).build(),
        leaf.clone(),
    ];
    assert_eq!(run(&root(None).build(), &path)?, Err(PathError::PathLen));
    // RFC 5937 §3.2 bullet 8: the anchor's pathLenConstraint 1 allows one
    // intermediate, not two.
    let path = [
        Builder::ca(2, "root", "int", 2, None).build(),
        Builder::ca(3, "int", "in2", 3, None).build(),
        leaf.clone(),
    ];
    assert_eq!(run(&root(Some(1)).build(), &path)?, Err(PathError::PathLen));
    assert_eq!(run(&root(Some(2)).build(), &path)?, Ok(leaf_key(&leaf)?));
    Ok(())
}

#[test]
fn an_intermediate_must_be_a_ca_with_key_cert_sign_and_known_critical_extensions()
-> Result<(), String> {
    let root_der = root(None).build();
    let leaf = Builder::leaf(3, "int").build();
    // §6.1.4 (k): no basicConstraints.
    let not_ca = Builder::new(2, "root", "int", 2)
        .with(ext(KEY_USAGE, true, KU_KEY_CERT_SIGN))
        .build();
    assert_eq!(
        run(&root_der, &[not_ca, leaf.clone()])?,
        Err(PathError::NotCa)
    );
    // §6.1.4 (n): keyUsage without keyCertSign.
    let usage = Builder::new(2, "root", "int", 2)
        .with(ext(BASIC_CONSTRAINTS, true, &bc_ca(None)))
        .with(ext(KEY_USAGE, true, KU_DIGITAL_SIGNATURE))
        .build();
    assert_eq!(
        run(&root_der, &[usage, leaf.clone()])?,
        Err(PathError::KeyUsage)
    );
    // §6.1.4 (o): an unknown critical extension.
    let unknown = Builder::ca(2, "root", "int", 2, None)
        .with(ext(UNKNOWN, true, &[0x05, 0x00]))
        .build();
    assert_eq!(
        run(&root_der, &[unknown, leaf.clone()])?,
        Err(PathError::UnknownCriticalExtension)
    );
    // A non-critical unknown extension is ignored.
    let ignored = Builder::ca(2, "root", "int", 2, None)
        .with(ext(UNKNOWN, false, &[0x05, 0x00]))
        .build();
    assert_eq!(
        run(&root_der, &[ignored, leaf.clone()])?,
        Ok(leaf_key(&leaf)?)
    );
    Ok(())
}

#[test]
fn name_constraints_of_the_anchor_and_of_intermediates_apply() -> Result<(), String> {
    // RFC 5937 §3.2 bullet 2: the anchor permits example.com only.
    let constrained_root = Builder::ca(1, "root", "root", 1, None)
        .with(ext(NAME_CONSTRAINTS, true, &nc_permit("example.com", 1)))
        .build();
    let int = Builder::ca(2, "root", "int", 2, None).build();
    let leaf = Builder::leaf(3, "int").build();
    assert_eq!(
        run(&constrained_root, &[int.clone(), leaf.clone()])?,
        Ok(leaf_key(&leaf)?)
    );
    let other = Builder::new(3, "int", "leaf", 9)
        .with(ext(SUBJECT_ALT_NAME, false, &san("other.com", 1)))
        .with(ext(EXT_KEY_USAGE, false, EKU_SERVER_AUTH))
        .build();
    assert_eq!(
        run(&constrained_root, &[int, other])?,
        Err(PathError::NameConstraint)
    );
    // §6.1.4 (g): an intermediate's constraints apply to what follows.
    let constrained_int = Builder::ca(2, "root", "int", 2, None)
        .with(ext(NAME_CONSTRAINTS, true, &nc_permit("example.org", 1)))
        .build();
    assert_eq!(
        run(&root(None).build(), &[constrained_int, leaf])?,
        Err(PathError::NameConstraint)
    );
    Ok(())
}

// ---------------------------------------------------------------------------
// The profile and one candidate
// ---------------------------------------------------------------------------

/// `path_profile` of the parsed `ders` under the root's anchor.
fn profile(root_der: &[u8], ders: &[Vec<u8>]) -> Result<Result<(), PathError>, String> {
    let anchor = need(anchor_from_root(root_der, None), "anchor")?;
    let parsed: Vec<PathCert<'_>> = ders
        .iter()
        .map(|der| need(parse_path_cert(der), "certificate"))
        .collect::<Result<_, _>>()?;
    let certs: Vec<&PathCert<'_>> = parsed.iter().collect();
    Ok(path_profile(&anchor, &certs, DNS, &now()))
}

#[test]
fn the_profile_refuses_what_the_rfc_allows() -> Result<(), String> {
    let root_der = root(None).build();
    let int = Builder::ca(2, "root", "int", 2, None).build();
    assert_eq!(
        profile(&root_der, &[int.clone(), Builder::leaf(3, "int").build()])?,
        Ok(())
    );
    // (R) A leaf without extKeyUsage.
    let no_eku = Builder::new(3, "int", "leaf", 9)
        .with(ext(SUBJECT_ALT_NAME, false, &san("example.com", 1)))
        .build();
    assert_eq!(
        profile(&root_der, &[int.clone(), no_eku])?,
        Err(PathError::ExtendedKeyUsage)
    );
    // The leaf's identity.
    let wrong_name = Builder::new(3, "int", "leaf", 9)
        .with(ext(SUBJECT_ALT_NAME, false, &san("other.com", 1)))
        .with(ext(EXT_KEY_USAGE, false, EKU_SERVER_AUTH))
        .build();
    assert_eq!(
        profile(&root_der, &[int.clone(), wrong_name])?,
        Err(PathError::Leaf)
    );
    // (R) An intermediate without keyUsage.
    let no_usage = Builder::new(2, "root", "int", 2)
        .with(ext(BASIC_CONSTRAINTS, true, &bc_ca(None)))
        .build();
    assert_eq!(
        profile(&root_der, &[no_usage, Builder::leaf(3, "int").build()])?,
        Err(PathError::KeyUsage)
    );
    // (R) An intermediate whose extKeyUsage lacks serverAuth.
    let client = Builder::ca(2, "root", "int", 2, None)
        .with(ext(EXT_KEY_USAGE, false, EKU_CLIENT_AUTH))
        .build();
    assert_eq!(
        profile(&root_der, &[client, Builder::leaf(3, "int").build()])?,
        Err(PathError::ExtendedKeyUsage)
    );
    // (R) The anchor certificate must be valid at now.
    let mut expired_root = root(None);
    expired_root.validity = ("200101000000Z", "250101000000Z");
    assert_eq!(
        profile(
            &expired_root.build(),
            &[int, Builder::leaf(3, "int").build()]
        )?,
        Err(PathError::AnchorExpired)
    );
    Ok(())
}

#[test]
fn candidate_verdicts_over_a_presented_chain() -> Result<(), String> {
    let root_der = root(None).build();
    let anchors = vec![need(anchor_from_root(&root_der, None), "anchor")?];
    let leaf_der = Builder::leaf(3, "int").build();
    let int_der = Builder::ca(2, "root", "int", 2, None).build();
    let garbage = vec![0x30, 0x00];
    let presented: Vec<&[u8]> = vec![&leaf_der, &int_der, &garbage];
    let inputs = chain_inputs(&presented, 1_780_272_000).map_err(|e| format!("{e:?}"))?;
    assert!(inputs.pool.first().is_some_and(Option::is_some));
    assert!(inputs.pool.get(1).is_some_and(Option::is_none));
    let environment = Environment {
        link: &AcceptAll,
        revoked: &NotRevoked,
        max_intermediates: 6,
    };
    let verdict = |path: &[usize], environment: &Environment<'_, AcceptAll, NotRevoked>| {
        candidate_verdict(
            environment,
            &anchors,
            &inputs.pool,
            &inputs.leaf,
            &Candidate { anchor: 0, path },
            DNS,
            &inputs.now,
        )
        .map(<[u8]>::to_vec)
    };
    assert_eq!(verdict(&[0], &environment), Ok(leaf_key(&leaf_der)?));
    // The leaf alone does not chain to the anchor.
    assert_eq!(verdict(&[], &environment), Err(PathError::NameChaining));
    // An unusable pool certificate, a pool index out of range, a repeated index.
    assert_eq!(verdict(&[1], &environment), Err(PathError::UnknownIssuer));
    assert_eq!(verdict(&[7], &environment), Err(PathError::UnknownIssuer));
    assert_eq!(
        verdict(&[0, 0], &environment),
        Err(PathError::UnknownIssuer)
    );
    // More intermediates than allowed.
    let shallow = Environment {
        link: &AcceptAll,
        revoked: &NotRevoked,
        max_intermediates: 0,
    };
    assert_eq!(
        verdict(&[0], &shallow),
        Err(PathError::TooManyIntermediates)
    );
    Ok(())
}

#[test]
fn chain_inputs_refuse_an_empty_or_unparseable_chain() {
    assert!(matches!(chain_inputs(&[], 0), Err(PathError::Malformed)));
    let garbage: &[u8] = &[0x30, 0x00];
    assert!(matches!(
        chain_inputs(&[garbage], 0),
        Err(PathError::Malformed)
    ));
}

#[test]
fn the_comparison_bound_refuses_before_section_6_1_runs() -> Result<(), String> {
    // 65 permitted subtrees on the anchor; a leaf with 63 subjectAltName
    // entries costs (63 + 1) * 65 = 4,160 comparisons, beyond 4,096.
    let root_der = Builder::ca(1, "root", "root", 1, None)
        .with(ext(NAME_CONSTRAINTS, true, &nc_permit("example.com", 65)))
        .build();
    let anchors = vec![need(anchor_from_root(&root_der, None), "anchor")?];
    let big_leaf = |entries: usize| {
        Builder::new(3, "root", "leaf", 9)
            .with(ext(SUBJECT_ALT_NAME, false, &san("example.com", entries)))
            .with(ext(EXT_KEY_USAGE, false, EKU_SERVER_AUTH))
            .build()
    };
    for (entries, within) in [(61, true), (62, true), (63, false)] {
        let leaf_der = big_leaf(entries);
        let leaf = need(parse_path_cert(&leaf_der), "leaf")?;
        let anchor = need(anchors.first(), "anchor")?;
        assert_eq!(
            path_within_budget(anchor, &[&leaf]),
            within,
            "{entries} entries"
        );
        let pool: Vec<Option<PathCert<'_>>> = Vec::new();
        // A link verifier that refuses the leaf: §6.1 would say BadSignature,
        // but beyond the bound the verdict is decided first.
        let refused = leaf.envelope.tbs_certificate_der.to_vec();
        let link = RefuseOne { refused: &refused };
        let environment = Environment {
            link: &link,
            revoked: &NotRevoked,
            max_intermediates: 6,
        };
        let verdict = candidate_verdict(
            &environment,
            &anchors,
            &pool,
            &leaf,
            &Candidate {
                anchor: 0,
                path: &[],
            },
            DNS,
            &now(),
        );
        let expected = if within {
            PathError::BadSignature
        } else {
            PathError::TooManyNameComparisons
        };
        assert_eq!(verdict, Err(expected), "{entries} entries");
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// x509-limbo
// ---------------------------------------------------------------------------

/// One testcase of the index.
struct Case {
    id: &'static str,
    kind: &'static str,
    expected: &'static str,
    peer: (&'static str, &'static str),
    peer_names: &'static [(&'static str, &'static str)],
    time: &'static str,
    features: &'static [&'static str],
    importance: &'static str,
    max_chain_depth: Option<u32>,
    key_usage: &'static [&'static str],
    extended_key_usage: &'static [&'static str],
    trusted: &'static [usize],
    intermediates: &'static [usize],
    leaf: usize,
}

// `TESTCASE_COUNT`, `CERT_SPANS` and `CASES`, generated from the vendored file.
include!("generated/x509_limbo.rs");

static CERTS: &[u8] = include_bytes!("generated/x509_limbo_certs.bin");

fn limbo_cert(index: usize) -> Option<&'static [u8]> {
    let &(offset, length) = CERT_SPANS.get(index)?;
    let start = usize::try_from(offset).ok()?;
    let end = start.checked_add(usize::try_from(length).ok()?)?;
    CERTS.get(start..end)
}

/// `YYYY-MM-DDTHH:MM:SS+00:00`, fractional seconds truncated.
fn parse_time(text: &str) -> Option<CertificateTime> {
    let body = text.strip_suffix("+00:00")?;
    let (date, clock) = body.split_once('T')?;
    let mut d = date.split('-');
    let mut c = clock.split(':');
    let time = CertificateTime {
        year: d.next()?.parse().ok()?,
        month: d.next()?.parse().ok()?,
        day: d.next()?.parse().ok()?,
        hour: c.next()?.parse().ok()?,
        minute: c.next()?.parse().ok()?,
        second: c.next()?.split('.').next()?.parse().ok()?,
    };
    (d.next().is_none() && c.next().is_none()).then_some(time)
}

/// Whether the testcase's key-usage and extended-key-usage expectations are
/// ones the profile always meets: digitalSignature, and serverAuth for a
/// server (the profile requires both whenever the certificate states them).
fn usage_expectations_are_the_profiles(case: &Case) -> bool {
    case.key_usage.iter().all(|k| *k == "digitalSignature")
        && case.extended_key_usage.iter().all(|e| *e == "serverAuth")
}

/// The testcases run here. `Some(reason)` marks one where this verifier's
/// verdict is not limbo's, and why; every other gets limbo's.
const LIMBO_CASES: &[(&str, Option<&str>)] = &[
    ("rfc5280::nc::permitted-dns-match", None),
    ("rfc5280::nc::permitted-dns-mismatch", None),
    ("rfc5280::nc::excluded-dns-match", None),
    ("rfc5280::nc::permitted-ipv4-match", None),
    ("rfc5280::nc::not-allowed-in-ee-critical", None),
    (
        "rfc5280::nc::intermediate-with-san-rejected-by-root-nc",
        None,
    ),
    (
        "rfc5280::nc::restrictive-permits-in-intermediates-narrows",
        None,
    ),
    (
        "rfc5280::nc::permitted-self-issued",
        Some("(R) self-issued intermediates are name-checked too (Firefox)"),
    ),
    ("pathlen::ee-with-intermediate-pathlen-0", None),
    ("pathlen::intermediate-violates-pathlen-0", None),
    ("pathlen::intermediate-pathlen-may-increase", None),
    ("pathlen::self-issued-certs-pathlen", None),
    ("rfc5280::validity::expired-root", None),
    ("rfc5280::validity::expired-intermediate", None),
    ("rfc5280::validity::expired-leaf", None),
    ("rfc5280::validity::notbefore-exact", None),
    ("rfc5280::validity::notafter-exact", None),
    ("rfc5280::validity::expired-1-second", None),
    ("rfc5280::validity::not-yet-valid-1-second", None),
    ("rfc5280::ee-critical-aia-invalid", None),
    (
        "rfc5280::eku::ee-without-eku",
        Some("(R) the leaf must have extKeyUsage (BR §7.1.2.7.6, design Q7)"),
    ),
    ("webpki::eku::ee-without-eku", None),
];

/// The verdict on one limbo testcase, with the accept-all link verifier.
fn limbo_verdict(case: &Case) -> Result<Result<Vec<u8>, PathError>, String> {
    let anchors: Vec<Anchor<'static>> = case
        .trusted
        .iter()
        .filter_map(|&i| anchor_from_root(limbo_cert(i)?, None))
        .collect();
    let leaf_der = need(limbo_cert(case.leaf), "leaf")?;
    let mut presented: Vec<&[u8]> = vec![leaf_der];
    for &i in case.intermediates {
        presented.push(need(limbo_cert(i), "intermediate")?);
    }
    let inputs = chain_inputs(&presented, 0).map_err(|e| format!("{}: {e:?}", case.id))?;
    let now = if case.time.is_empty() {
        copy(&inputs.leaf.tbs.not_before)
    } else {
        need(parse_time(case.time), "time")?
    };
    // Limbo's chain as drawn: from the leaf, each issuer by name, a presented
    // intermediate before an anchor and a self-issued one before another of
    // the same name (self-issued certificates sit below the certificate whose
    // name they repeat), none twice.
    let mut path: Vec<usize> = Vec::new();
    let mut issuer = inputs.leaf.tbs.issuer_der;
    let anchor = loop {
        let issues = |j: usize, c: &Option<PathCert<'_>>, self_issued: bool| {
            !path.contains(&j)
                && c.as_ref().is_some_and(|c| {
                    c.tbs.subject_der == issuer
                        && (!self_issued || c.tbs.issuer_der == c.tbs.subject_der)
                })
        };
        let next = inputs
            .pool
            .iter()
            .enumerate()
            .position(|(j, c)| issues(j, c, true))
            .or_else(|| {
                inputs
                    .pool
                    .iter()
                    .enumerate()
                    .position(|(j, c)| issues(j, c, false))
            });
        if let Some(j) = next {
            path.insert(0, j);
            issuer = need(
                inputs.pool.get(j).and_then(Option::as_ref),
                "pool certificate",
            )?
            .tbs
            .issuer_der;
            continue;
        }
        break need(
            anchors.iter().position(|a| a.subject_der == issuer),
            "an anchor for the chain",
        )?;
    };
    if path.len() != case.intermediates.len() {
        return Err(format!("{}: the chain leaves out an intermediate", case.id));
    }
    let address;
    let reference = match case.peer {
        ("DNS", host) => ReferenceIdentity::Dns(host.as_bytes()),
        ("IP", text) => {
            address = match text.parse::<IpAddr>().map_err(|e| e.to_string())? {
                IpAddr::V4(a) => a.octets().to_vec(),
                IpAddr::V6(a) => a.octets().to_vec(),
            };
            ReferenceIdentity::Ip(&address)
        }
        _ => return Err(format!("{}: no peer name", case.id)),
    };
    let environment = Environment {
        link: &AcceptAll,
        revoked: &NotRevoked,
        max_intermediates: case
            .max_chain_depth
            .map_or(6, |d| usize::try_from(d).unwrap_or(6)),
    };
    Ok(candidate_verdict(
        &environment,
        &anchors,
        &inputs.pool,
        &inputs.leaf,
        &Candidate {
            anchor,
            path: &path,
        },
        reference,
        &now,
    )
    .map(<[u8]>::to_vec))
}

fn copy(time: &CertificateTime) -> CertificateTime {
    CertificateTime {
        year: time.year,
        month: time.month,
        day: time.day,
        hour: time.hour,
        minute: time.minute,
        second: time.second,
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn limbo_chains_in_limbo_order_get_the_expected_verdict() -> Result<(), String> {
    assert_eq!(CASES.len(), TESTCASE_COUNT);
    let mut wrong = Vec::new();
    for &(id, divergence) in LIMBO_CASES {
        let case = need(CASES.iter().find(|c| c.id == id), id)?;
        assert!(case.kind == "SERVER" && case.peer_names.is_empty(), "{id}");
        assert!(usage_expectations_are_the_profiles(case), "{id}");
        let accepted = (case.expected == "SUCCESS") != divergence.is_some();
        let verdict = limbo_verdict(case)?;
        if verdict.is_ok() != accepted {
            wrong.push(format!(
                "{id} ({:?}, {}): {verdict:?}",
                case.features, case.importance
            ));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
    Ok(())
}

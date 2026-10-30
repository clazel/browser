//! `parse_path_cert` and `anchor_from_root` (design `path-validation.md`
//! §1.4 and §3.2; RFC 5280 §4.1, RFC 5937 §2 and §3.2).
//!
//! Certificates are built by hand from the ASN.1 in this file (a minimal
//! v3 certificate with an EC P-256 key and a dummy signature, since neither
//! function reads a signature), so every expected value is written out from
//! the standards rather than produced by the code under test. The Mozilla
//! root table and the x509-limbo corpus (the latter in
//! `conformance_limbo.rs`) are the real-world inputs.

use clazel_x509::path::parsed::exec::{Anchor, PathCert, anchor_from_root, parse_path_cert};
use clazel_x509::roots::ROOTS;
use clazel_x509::signature_algorithm::exec::{AlgorithmClass, EcdsaHash};
use clazel_x509::time::exec::CertificateTime;

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

const ECDSA_SHA256: &[u8] = &[
    0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02,
];
const ECDSA_SHA384: &[u8] = &[
    0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x03,
];

const BASIC_CONSTRAINTS: &[u8] = &[0x55, 0x1D, 0x13];
const KEY_USAGE: &[u8] = &[0x55, 0x1D, 0x0F];
const EXT_KEY_USAGE: &[u8] = &[0x55, 0x1D, 0x25];
const SUBJECT_ALT_NAME: &[u8] = &[0x55, 0x1D, 0x11];
const NAME_CONSTRAINTS: &[u8] = &[0x55, 0x1D, 0x1E];
const POLICY_CONSTRAINTS: &[u8] = &[0x55, 0x1D, 0x24];
const POLICY_MAPPINGS: &[u8] = &[0x55, 0x1D, 0x21];
const INHIBIT_ANY_POLICY: &[u8] = &[0x55, 0x1D, 0x36];
const CERTIFICATE_POLICIES: &[u8] = &[0x55, 0x1D, 0x20];
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

// Extension values, written out from the ASN.1.
/// `BasicConstraints { cA TRUE }`.
const BC_CA: &[u8] = &[0x30, 0x03, 0x01, 0x01, 0xFF];
/// `BasicConstraints { cA TRUE, pathLenConstraint 3 }`.
const BC_CA_PATH_3: &[u8] = &[0x30, 0x06, 0x01, 0x01, 0xFF, 0x02, 0x01, 0x03];
/// `BasicConstraints {}`: an end entity.
const BC_END_ENTITY: &[u8] = &[0x30, 0x00];
/// KeyUsage keyCertSign (bit 5).
const KU_KEY_CERT_SIGN: &[u8] = &[0x03, 0x02, 0x02, 0x04];
/// KeyUsage digitalSignature (bit 0) only.
const KU_DIGITAL_SIGNATURE: &[u8] = &[0x03, 0x02, 0x07, 0x80];
/// ExtKeyUsage { id-kp-serverAuth }.
const EKU_SERVER_AUTH: &[u8] = &[
    0x30, 0x0A, 0x06, 0x08, 0x2B, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01,
];
/// ExtKeyUsage { id-kp-clientAuth }.
const EKU_CLIENT_AUTH: &[u8] = &[
    0x30, 0x0A, 0x06, 0x08, 0x2B, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x02,
];
/// ExtKeyUsage { anyExtendedKeyUsage }.
const EKU_ANY: &[u8] = &[0x30, 0x06, 0x06, 0x04, 0x55, 0x1D, 0x25, 0x00];
/// SubjectAltName { dNSName "example.com" }.
const SAN_EXAMPLE: &[u8] = &[
    0x30, 0x0D, 0x82, 0x0B, b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.', b'c', b'o', b'm',
];
/// NameConstraints { permittedSubtrees { dNSName "example.com" } }.
const NC_PERMIT_EXAMPLE: &[u8] = &[
    0x30, 0x11, 0xA0, 0x0F, 0x30, 0x0D, 0x82, 0x0B, b'e', b'x', b'a', b'm', b'p', b'l', b'e', b'.',
    b'c', b'o', b'm',
];
/// PolicyConstraints { requireExplicitPolicy 2 }.
const PC_REQUIRE_2: &[u8] = &[0x30, 0x03, 0x80, 0x01, 0x02];
/// PolicyConstraints { inhibitPolicyMapping 1 }.
const PC_INHIBIT_MAPPING_1: &[u8] = &[0x30, 0x03, 0x81, 0x01, 0x01];
/// A well-formed PolicyMappings value is never decoded; any bytes will do.
const ANY_VALUE: &[u8] = &[0x30, 0x00];

/// A certificate under construction.
struct Builder {
    subject: Vec<u8>,
    /// Empty means no `[3]` field at all (an empty Extensions is malformed).
    extensions: Vec<Vec<u8>>,
    tbs_algorithm: Vec<u8>,
    outer_algorithm: Vec<u8>,
    validity: (&'static str, &'static str),
}

impl Builder {
    fn new() -> Self {
        Self {
            subject: name("root"),
            extensions: Vec::new(),
            tbs_algorithm: ECDSA_SHA256.to_vec(),
            outer_algorithm: ECDSA_SHA256.to_vec(),
            validity: ("200101000000Z", "400101000000Z"),
        }
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
                &tlv(0x03, &[&[0x00, 0x04][..], &[0x11; 64]].concat()),
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
        let mut tbs = vec![0xA0, 0x03, 0x02, 0x01, 0x02, 0x02, 0x01, 0x01];
        tbs.extend_from_slice(&self.tbs_algorithm);
        tbs.extend_from_slice(&name("issuer"));
        tbs.extend_from_slice(&validity);
        tbs.extend_from_slice(&self.subject);
        tbs.extend_from_slice(&spki);
        if !self.extensions.is_empty() {
            tbs.extend_from_slice(&tlv(0xA3, &tlv(0x30, &self.extensions.concat())));
        }
        let mut body = tlv(0x30, &tbs);
        body.extend_from_slice(&self.outer_algorithm);
        body.extend_from_slice(&tlv(0x03, &[&[0x00][..], &[0x22; 8]].concat()));
        tlv(0x30, &body)
    }
}

/// A CA certificate with every extension the parser reads.
fn full() -> Builder {
    Builder::new()
        .with(ext(BASIC_CONSTRAINTS, true, BC_CA_PATH_3))
        .with(ext(KEY_USAGE, true, KU_KEY_CERT_SIGN))
        .with(ext(EXT_KEY_USAGE, false, EKU_SERVER_AUTH))
        .with(ext(SUBJECT_ALT_NAME, false, SAN_EXAMPLE))
        .with(ext(NAME_CONSTRAINTS, true, NC_PERMIT_EXAMPLE))
        .with(ext(POLICY_CONSTRAINTS, true, PC_REQUIRE_2))
        .with(ext(POLICY_MAPPINGS, false, ANY_VALUE))
}

/// `value`, or the reason a test cannot go on.
fn need<T>(value: Option<T>, what: &str) -> Result<T, String> {
    value.ok_or_else(|| what.to_owned())
}

fn path_cert(builder: &Builder) -> Option<Vec<u8>> {
    let der = builder.build();
    let parsed = parse_path_cert(&der).is_some();
    parsed.then_some(der)
}

// ---------------------------------------------------------------------------
// parse_path_cert
// ---------------------------------------------------------------------------

#[test]
fn every_recognized_extension_is_decoded_into_its_field() -> Result<(), String> {
    let der = full().build();
    let cert = need(
        parse_path_cert(&der),
        "a well-formed certificate must parse",
    )?;
    assert_eq!(cert.der, der.as_slice());
    assert_eq!(cert.tbs.version, 2);
    assert_eq!(cert.tbs.subject_der, name("root").as_slice());
    assert_eq!(cert.tbs.issuer_der, name("issuer").as_slice());
    assert_eq!(cert.extensions.len(), 7);
    let basic = need(cert.basic, "basicConstraints")?;
    assert!(basic.ca);
    assert_eq!(basic.path_len_constraint, Some(&[3u8][..]));
    assert!(cert.key_usage.is_some());
    assert_eq!(cert.eku.map(|eku| eku.purposes.len()), Some(1));
    let san = need(cert.san, "subjectAltName")?;
    assert_eq!(san.names.len(), 1);
    let nc = need(cert.name_constraints, "nameConstraints")?;
    assert_eq!(nc.permitted_subtrees.map(|list| list.len()), Some(1));
    assert!(nc.excluded_subtrees.is_none());
    assert_eq!(cert.require_explicit_policy, Some(&[2u8][..]));
    assert!(cert.has_policy_mappings);
    assert!(matches!(
        cert.signature_class,
        AlgorithmClass::Ecdsa(EcdsaHash::Sha256)
    ));
    Ok(())
}

#[test]
fn a_certificate_without_extensions_has_none() -> Result<(), String> {
    let der = Builder::new().build();
    let cert = need(
        parse_path_cert(&der),
        "a certificate with no extensions must parse",
    )?;
    assert!(cert.extensions.is_empty());
    assert!(cert.basic.is_none() && cert.key_usage.is_none() && cert.eku.is_none());
    assert!(cert.name_constraints.is_none() && cert.san.is_none());
    assert_eq!(cert.require_explicit_policy, None);
    assert!(!cert.has_policy_mappings);
    Ok(())
}

#[test]
fn inhibit_policy_mapping_alone_leaves_require_explicit_policy_unset() -> Result<(), String> {
    let der = Builder::new()
        .with(ext(POLICY_CONSTRAINTS, false, PC_INHIBIT_MAPPING_1))
        .build();
    let cert = need(parse_path_cert(&der), "must parse")?;
    assert_eq!(cert.require_explicit_policy, None);
    Ok(())
}

#[test]
fn the_second_signature_algorithm_class_is_read_from_the_tbs() -> Result<(), String> {
    let mut builder = Builder::new();
    builder.tbs_algorithm = ECDSA_SHA384.to_vec();
    builder.outer_algorithm = ECDSA_SHA384.to_vec();
    let der = builder.build();
    let cert = need(parse_path_cert(&der), "must parse")?;
    assert!(matches!(
        cert.signature_class,
        AlgorithmClass::Ecdsa(EcdsaHash::Sha384)
    ));
    Ok(())
}

#[test]
fn an_unknown_critical_extension_does_not_stop_parsing() -> Result<(), String> {
    // Refusing it is the §6.1 spec's job (design §1.6); the parser keeps it.
    let der = Builder::new().with(ext(UNKNOWN, true, ANY_VALUE)).build();
    let cert = need(parse_path_cert(&der), "must parse")?;
    assert_eq!(cert.extensions.len(), 1);
    assert!(cert.extensions.first().is_some_and(|e| e.critical));
    Ok(())
}

#[test]
fn the_certificate_is_refused_when_a_recognized_extension_does_not_decode() {
    // An empty GeneralNames, an empty permittedSubtrees, an empty
    // PolicyConstraints, a pathLenConstraint without cA, an empty KeyUsage
    // BIT STRING and an empty ExtKeyUsage, each non-critical.
    let bad = [
        ext(SUBJECT_ALT_NAME, false, &[0x30, 0x00]),
        ext(NAME_CONSTRAINTS, false, &[0x30, 0x02, 0xA0, 0x00]),
        ext(POLICY_CONSTRAINTS, false, &[0x30, 0x00]),
        ext(BASIC_CONSTRAINTS, false, &[0x30, 0x03, 0x02, 0x01, 0x01]),
        ext(KEY_USAGE, false, &[0x03, 0x01, 0x00]),
        ext(EXT_KEY_USAGE, false, &[0x30, 0x00]),
    ];
    for extension in bad {
        let der = Builder::new().with(extension).build();
        assert!(parse_path_cert(&der).is_none());
    }
}

#[test]
fn a_duplicate_extension_is_refused() {
    assert!(path_cert(&Builder::new().with(ext(BASIC_CONSTRAINTS, true, BC_CA))).is_some());
    let builder = Builder::new()
        .with(ext(BASIC_CONSTRAINTS, true, BC_CA))
        .with(ext(BASIC_CONSTRAINTS, true, BC_CA));
    assert!(path_cert(&builder).is_none());
}

#[test]
fn disagreeing_signature_algorithms_are_refused() {
    assert!(path_cert(&Builder::new()).is_some());
    let mut builder = Builder::new();
    builder.outer_algorithm = ECDSA_SHA384.to_vec();
    assert!(path_cert(&builder).is_none());
}

#[test]
fn trailing_bytes_and_truncation_are_refused() {
    let mut der = full().build();
    der.push(0);
    assert!(parse_path_cert(&der).is_none());
    der.pop();
    der.pop();
    assert!(parse_path_cert(&der).is_none());
    assert!(parse_path_cert(&[]).is_none());
}

// ---------------------------------------------------------------------------
// anchor_from_root
// ---------------------------------------------------------------------------

/// An acceptable root: cA TRUE (critical), keyCertSign.
fn root() -> Builder {
    Builder::new()
        .with(ext(BASIC_CONSTRAINTS, true, BC_CA))
        .with(ext(KEY_USAGE, true, KU_KEY_CERT_SIGN))
}

fn anchor(builder: &Builder) -> bool {
    anchor_from_root(&builder.build(), None).is_some()
}

#[test]
fn an_anchor_carries_name_key_validity_and_nothing_else() -> Result<(), String> {
    let der = root().build();
    let anchor = need(
        anchor_from_root(&der, None),
        "a plain root must yield an anchor",
    )?;
    assert_eq!(anchor.subject_der, name("root").as_slice());
    assert!(anchor.spki_der.starts_with(&[0x30, 0x59, 0x30, 0x13]));
    assert_eq!(anchor.spki_der.len(), 91);
    assert!(anchor.name_constraints.is_none());
    assert_eq!(anchor.path_len, None);
    assert_eq!(
        (
            anchor.not_before.year,
            anchor.not_before.month,
            anchor.not_before.day
        ),
        (2020, 1, 1)
    );
    assert_eq!(anchor.not_after.year, 2040);
    assert!(anchor.server_distrust_after.is_none());
    Ok(())
}

#[test]
fn the_path_length_and_name_constraints_are_the_anchors() -> Result<(), String> {
    // RFC 5937 §3.2 bullets 2, 3 and 8.
    let builder = Builder::new()
        .with(ext(BASIC_CONSTRAINTS, true, BC_CA_PATH_3))
        .with(ext(KEY_USAGE, true, KU_KEY_CERT_SIGN))
        .with(ext(NAME_CONSTRAINTS, true, NC_PERMIT_EXAMPLE));
    let der = builder.build();
    let anchor = need(anchor_from_root(&der, None), "must yield an anchor")?;
    assert_eq!(anchor.path_len, Some(&[3u8][..]));
    let nc = need(anchor.name_constraints, "nameConstraints")?;
    assert_eq!(nc.permitted_subtrees.map(|list| list.len()), Some(1));
    Ok(())
}

#[test]
fn the_distrust_after_text_is_decoded_as_a_utc_time() -> Result<(), String> {
    let der = root().build();
    let anchor = need(
        anchor_from_root(&der, Some(b"260415235959Z")),
        "must yield an anchor",
    )?;
    let time = need(anchor.server_distrust_after, "distrust-after")?;
    assert_eq!(
        (
            time.year,
            time.month,
            time.day,
            time.hour,
            time.minute,
            time.second
        ),
        (2026, 4, 15, 23, 59, 59)
    );
    // (R) text that is not a UTCTime refuses the anchor.
    for bad in [&b"2604152359Z"[..], b"260415235959", b"261315235959Z", b""] {
        assert!(anchor_from_root(&der, Some(bad)).is_none());
    }
    Ok(())
}

#[test]
fn the_role_checks_refuse() {
    // (R) cA FALSE, no basicConstraints, keyUsage without keyCertSign.
    assert!(!anchor(
        &Builder::new()
            .with(ext(BASIC_CONSTRAINTS, true, BC_END_ENTITY))
            .with(ext(KEY_USAGE, true, KU_KEY_CERT_SIGN))
    ));
    assert!(!anchor(&Builder::new().with(ext(
        KEY_USAGE,
        true,
        KU_KEY_CERT_SIGN
    ))));
    assert!(!anchor(
        &Builder::new()
            .with(ext(BASIC_CONSTRAINTS, true, BC_CA))
            .with(ext(KEY_USAGE, true, KU_DIGITAL_SIGNATURE))
    ));
    // keyUsage may be absent.
    assert!(anchor(&Builder::new().with(ext(
        BASIC_CONSTRAINTS,
        true,
        BC_CA
    ))));
}

#[test]
fn the_root_eku_must_allow_server_auth() {
    // limbo webpki::eku::root-has-eku; (R).
    assert!(anchor(&root().with(ext(
        EXT_KEY_USAGE,
        false,
        EKU_SERVER_AUTH
    ))));
    assert!(!anchor(&root().with(ext(
        EXT_KEY_USAGE,
        false,
        EKU_CLIENT_AUTH
    ))));
    assert!(!anchor(&root().with(ext(EXT_KEY_USAGE, false, EKU_ANY))));
}

#[test]
fn unrecognized_critical_extensions_refuse_but_noncritical_ones_do_not() {
    // RFC 5937 §2.
    assert!(!anchor(&root().with(ext(UNKNOWN, true, ANY_VALUE))));
    assert!(anchor(&root().with(ext(UNKNOWN, false, ANY_VALUE))));
    // A critical subjectAltName is not one the anchor reads.
    assert!(!anchor(&root().with(ext(
        SUBJECT_ALT_NAME,
        true,
        SAN_EXAMPLE
    ))));
    assert!(anchor(&root().with(ext(
        SUBJECT_ALT_NAME,
        false,
        SAN_EXAMPLE
    ))));
}

#[test]
fn policy_inputs_that_are_not_modelled_refuse_except_certificate_policies() {
    // (R) RFC 5937 §3.2 bullets 5 to 7; (I) bullet 4.
    assert!(!anchor(&root().with(ext(
        INHIBIT_ANY_POLICY,
        false,
        &[0x02, 0x01, 0x00]
    ))));
    assert!(!anchor(&root().with(ext(
        POLICY_CONSTRAINTS,
        false,
        PC_REQUIRE_2
    ))));
    assert!(anchor(&root().with(ext(
        CERTIFICATE_POLICIES,
        false,
        ANY_VALUE
    ))));
}

#[test]
fn a_malformed_read_extension_or_an_empty_subject_refuses() {
    assert!(!anchor(&root().with(ext(
        NAME_CONSTRAINTS,
        false,
        &[0x30, 0x00, 0x00]
    ))));
    let mut builder = root();
    builder.subject = vec![0x30, 0x00];
    assert!(!anchor(&builder));
    // The anchor's signature is never read: algorithms that disagree still yield one.
    let mut builder = root();
    builder.outer_algorithm = ECDSA_SHA384.to_vec();
    assert!(anchor(&builder));
}

// ---------------------------------------------------------------------------
// The Mozilla roots
// ---------------------------------------------------------------------------

/// The roots the table gives a server distrust-after date.
const DISTRUST_AFTER_ROOTS: usize = 1;

fn time_is(time: &CertificateTime, parts: (u16, u8, u8, u8, u8, u8)) -> bool {
    (
        time.year,
        time.month,
        time.day,
        time.hour,
        time.minute,
        time.second,
    ) == parts
}

#[test]
fn all_118_mozilla_roots_yield_an_anchor() -> Result<(), String> {
    assert_eq!(ROOTS.len(), 118);
    let mut with_distrust = 0usize;
    for root in &ROOTS {
        let text = root.server_distrust_after.map(str::as_bytes);
        let anchor: Anchor<'_> = need(anchor_from_root(root.der, text), root.label)?;
        // The anchor's name and key are the certificate's own.
        let cert: PathCert<'_> = need(parse_path_cert(root.der), root.label)?;
        assert_eq!(anchor.subject_der, cert.tbs.subject_der, "{}", root.label);
        assert_eq!(
            anchor.spki_der, cert.tbs.subject_public_key_info_der,
            "{}",
            root.label
        );
        assert!(anchor.name_constraints.is_none(), "{}", root.label);
        assert_eq!(
            anchor.path_len,
            cert.basic.and_then(|basic| basic.path_len_constraint),
            "{}",
            root.label
        );
        assert_eq!(anchor.server_distrust_after.is_some(), text.is_some());
        with_distrust = with_distrust.saturating_add(usize::from(text.is_some()));
        if let Some(time) = &anchor.server_distrust_after {
            assert!(time_is(time, (2026, 4, 15, 23, 59, 59)), "{}", root.label);
        }
    }
    assert_eq!(with_distrust, DISTRUST_AFTER_ROOTS);
    Ok(())
}

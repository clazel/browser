//! The production `clazel_tls::auth::spec::ChainValidation` (path-validation
//! design P16): RFC 8446 §4.4.2's server Certificate message, validated by
//! `clazel_x509::path` (RFC 5280 §6.1 and the browser profile, with P9's
//! chain-building search) under the production link verifier of
//! [`crate::chain`] (P11), for the typed target host and the captured clock.
//!
//! Sources, by step:
//! - RFC 8446 (August 2018) §4.4.2, Certificate,
//!   <https://www.rfc-editor.org/rfc/rfc8446#section-4.4.2>: "certificate_list:
//!   A sequence (chain) of CertificateEntry structures, each containing a
//!   single certificate and list of extensions"; "The sender's certificate
//!   MUST come in the first CertificateEntry in the list. Each following
//!   certificate SHOULD directly certify the one immediately preceding it";
//!   "clients SHOULD be prepared to handle potentially extraneous
//!   certificates and arbitrary orderings from any TLS version".
//!   The body is read by `clazel_tls::spec::read_certificate`, the crate's
//!   own §4.4.2 decoder.
//! - RFC 8446 §6.2, Error Alerts,
//!   <https://www.rfc-editor.org/rfc/rfc8446#section-6.2>, for the alert
//!   each refusal sends (`clazel_tls::auth::spec::certificate_alert` turns a
//!   `CertificateError` into the alert; [`certificate_error`] says which).
//! - RFC 5280 §6.1 and the design's profile and search:
//!   `clazel_x509::path::search::spec::verify_server_chain`, which converts
//!   the clock with `clazel_x509::time::spec::from_unix_seconds` (P1) in
//!   `path::verifier::chain_inputs`.
//! - RFC 9525 §6.2 to §6.4 for the reference identity: an IP host is an
//!   IP-ID, matched only against iPAddress subjectAltName entries, and a DNS
//!   host a DNS-ID, matched only against dNSName entries
//!   (`clazel_x509::spec::service_identity_match`).
//!
//! Modelling choices:
//! - **(=) The leaf, then the pool.** `presented` is every entry's
//!   `cert_data`, in message order: `presented[0]` is the server's
//!   certificate and the rest are the search's pool, used in any order
//!   (design Q3). The entries' extensions are not read here: the auth
//!   machine refuses an entry extension the ClientHello did not offer
//!   (§4.4.2), and this client offers neither status_request nor
//!   signed_certificate_timestamp, so a chain that reaches validation
//!   carries none.
//! - **(=) The body is the whole message body.** The auth machine has
//!   already parsed it (`parse_handshake_body`) and refused an empty list
//!   (decode_error), a nonempty context (illegal_parameter) and unoffered
//!   entry extensions before it calls the validator. A body that does not
//!   parse here therefore never comes from the auth machine; it is refused
//!   as `BadCertificate` so that this function is total.
//! - **(=) The host becomes the reference identity unchanged** (design Q2):
//!   `Host::Dns(name)` is `ReferenceIdentity::Dns(name)` and `Host::Ip(a)`
//!   is `ReferenceIdentity::Ip(a)`. Nothing is re-parsed.
//! - **(=) The trust anchors are a parameter**, `anchors`. The production
//!   value is [`anchors_from_roots`] of Mozilla's 118 server roots
//!   (`clazel_x509::roots::ROOTS`, generated from NSS `certdata.txt`), each
//!   with its table row's `server_distrust_after`, through P6's
//!   `anchor_from_root`. **(R)** A root that `anchor_from_root` refuses is
//!   left out (fewer anchors can only refuse more); all 118 are accepted
//!   today (clazel-x509's tests/path_parsed.rs). The executable verifier
//!   builds them once, when it is made (`exec::ChainVerifier::new`), and
//!   its spec function is this one over exactly the anchors it built.
//! - **(=) Revocation:** nothing is revoked ([`not_revoked`]; design Q4 and
//!   P7: revocation and CT are Phase 8). **(=) Links:** P11's
//!   `crate::chain::spec::production_link`. **(=) Depth:** 6 intermediates,
//!   mozilla::pkix `MAX_SUBCA_COUNT` (`path::verifier::default_max_intermediates`).
//! - **The key** returned is the leaf's complete SubjectPublicKeyInfo DER
//!   (`Validated::leaf_spki`), which `crate::signature::spec::verify` reads
//!   for CertificateVerify.
//! - **Errors to alerts** ([`certificate_error`]), P7's intended mapping
//!   (`clazel_x509::path::verifier`'s P16 note), each with the RFC 8446
//!   §6.2 alert it sends:
//!   - `Expired`, `AnchorExpired` to `Expired`, certificate_expired (45):
//!     "A certificate has expired or is not currently valid."
//!   - `UnsupportedAlgorithm` to `Unsupported`, unsupported_certificate
//!     (43): "A certificate was of an unsupported type."
//!   - `UnknownIssuer`, `BadSignature`, `NameChaining`, `Distrusted`,
//!     `Revoked` and `BuildBudgetExhausted` to `UnknownCa`, unknown_ca (48):
//!     "A valid certificate chain or partial chain was received, but the
//!     certificate was not accepted because the CA certificate could not be
//!     located or could not be matched with a known trust anchor."
//!     `BuildBudgetExhausted` is Firefox's `ERROR_UNKNOWN_ISSUER` (the
//!     budget's "Result::ERROR_UNKNOWN_ISSUER"), so it maps as that does.
//!   - Every other error, and a body that does not parse, to
//!     `BadCertificate`, bad_certificate (42): "A certificate was corrupt,
//!     contained signatures that did not verify correctly, etc." This
//!     includes `Leaf`, which covers the leaf's identity and its validity
//!     (`leaf::spec::check_extensions` does not say which), so a wrong host
//!     and an expired leaf both send 42.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The trust anchors
// ---------------------------------------------------------------------------

/// One row of the root table, as `anchor_from_root` reads it: the DER
/// certificate and NSS's `CKA_NSS_SERVER_DISTRUST_AFTER` UTCTime text.
pub struct RootEntry {
    /// The complete DER `Certificate`.
    pub der: Seq<u8>,
    /// `YYMMDDHHMMSSZ`, if the root sets one.
    pub server_distrust_after: Option<Seq<u8>>,
}

/// The anchors of a root table, in table order: every row that
/// `anchor_from_root` accepts ((R) the others are left out).
pub open spec fn anchors_from_roots(roots: Seq<RootEntry>) -> Seq<clazel_x509::path::parsed::spec::Anchor>
    decreases roots.len()
{
    if roots.len() == 0 { seq![] }
    else {
        let before = anchors_from_roots(roots.drop_last());
        match clazel_x509::path::parsed::spec::anchor_from_root(roots.last().der, roots.last().server_distrust_after) {
            Some(anchor) => before.push(anchor),
            None => before,
        }
    }
}

// ---------------------------------------------------------------------------
// The validator's inputs
// ---------------------------------------------------------------------------

/// Design Q2: the typed host as the validator's reference identity.
pub open spec fn reference_identity(host: clazel_tls::host::spec::Host) -> clazel_x509::spec::ReferenceIdentity {
    match host {
        clazel_tls::host::spec::Host::Dns(name) => clazel_x509::spec::ReferenceIdentity::Dns(name),
        clazel_tls::host::spec::Host::Ip(address) => clazel_x509::spec::ReferenceIdentity::Ip(address),
    }
}

/// RFC 8446 §4.4.2: the certificates of `certificate_list`, in order; the
/// sender's first.
pub open spec fn presented(entries: Seq<clazel_tls::spec::CertificateEntry>) -> Seq<Seq<u8>> {
    entries.map_values(|entry: clazel_tls::spec::CertificateEntry| entry.cert_data)
}

/// §6.1.3 (a)(3), design Q4: nothing is revoked.
pub open spec fn not_revoked() -> clazel_x509::path::spec::RevokedFn {
    |cert: clazel_x509::path::parsed::spec::PathCert| false
}

/// The production environment: P11's links, no revocation, at most 6
/// intermediates.
pub open spec fn production_environment() -> clazel_x509::path::verifier::Environment {
    clazel_x509::path::verifier::Environment {
        link: crate::chain::spec::production_link(),
        revoked: not_revoked(),
        max_intermediates: clazel_x509::path::verifier::default_max_intermediates(),
    }
}

// ---------------------------------------------------------------------------
// Errors (header, "Errors to alerts")
// ---------------------------------------------------------------------------

/// The certificate error, and so the RFC 8446 §6.2 alert, of each refusal.
pub open spec fn certificate_error(error: clazel_x509::path::spec::PathError) -> clazel_tls::auth::spec::CertificateError {
    match error {
        // certificate_expired (45).
        clazel_x509::path::spec::PathError::Expired => clazel_tls::auth::spec::CertificateError::Expired,
        clazel_x509::path::spec::PathError::AnchorExpired => clazel_tls::auth::spec::CertificateError::Expired,
        // unsupported_certificate (43).
        clazel_x509::path::spec::PathError::UnsupportedAlgorithm => clazel_tls::auth::spec::CertificateError::Unsupported,
        // unknown_ca (48).
        clazel_x509::path::spec::PathError::UnknownIssuer => clazel_tls::auth::spec::CertificateError::UnknownCa,
        clazel_x509::path::spec::PathError::BadSignature => clazel_tls::auth::spec::CertificateError::UnknownCa,
        clazel_x509::path::spec::PathError::NameChaining => clazel_tls::auth::spec::CertificateError::UnknownCa,
        clazel_x509::path::spec::PathError::Distrusted => clazel_tls::auth::spec::CertificateError::UnknownCa,
        clazel_x509::path::spec::PathError::Revoked => clazel_tls::auth::spec::CertificateError::UnknownCa,
        clazel_x509::path::spec::PathError::BuildBudgetExhausted => clazel_tls::auth::spec::CertificateError::UnknownCa,
        // bad_certificate (42).
        _ => clazel_tls::auth::spec::CertificateError::BadCertificate,
    }
}

// ---------------------------------------------------------------------------
// The validator
// ---------------------------------------------------------------------------

/// RFC 8446 §4.4.2: the server's Certificate body, validated for `host` at
/// Unix time `now` against `anchors`; `Ok` carries the leaf's
/// SubjectPublicKeyInfo DER.
pub open spec fn validate(anchors: Seq<clazel_x509::path::parsed::spec::Anchor>,
    host: clazel_tls::host::spec::Host, now: u64, body: Seq<u8>,
) -> Result<Seq<u8>, clazel_tls::auth::spec::CertificateError> {
    // 1. §4.4.2: the body is a Certificate (header: never otherwise here).
    match clazel_tls::spec::read_certificate(body) {
        None => Err(clazel_tls::auth::spec::CertificateError::BadCertificate),
        // 2. The leaf first, then the pool, for this reference identity and
        //    clock: RFC 5280 §6.1 with the profile and the search.
        Some(certificate) => match clazel_x509::path::search::spec::verify_server_chain(
            production_environment(), anchors, presented(certificate.entries), reference_identity(host), now) {
            // 3. The leaf's key, for CertificateVerify (§4.4.3).
            Ok(validated) => Ok(validated.leaf_spki),
            // 4. §6.2: the alert of the refusal.
            Err(error) => Err(certificate_error(error)),
        },
    }
}

/// The production `ChainValidation` over `anchors`.
pub open spec fn chain_validation(anchors: Seq<clazel_x509::path::parsed::spec::Anchor>) -> clazel_tls::auth::spec::ChainValidation {
    |host: clazel_tls::host::spec::Host, now: u64, body: Seq<u8>| validate(anchors, host, now, body)
}

/// The production `Verification`: this chain validation, and
/// CertificateVerify by [`crate::signature::spec::verify`] (3.5b).
pub open spec fn verification(anchors: Seq<clazel_x509::path::parsed::spec::Anchor>) -> clazel_tls::auth::spec::Verification {
    clazel_tls::auth::spec::Verification {
        chain: chain_validation(anchors),
        signature: |key: Seq<u8>, scheme: u16, input: Seq<u8>, signature: Seq<u8>|
            crate::signature::spec::verify(key, scheme, input, signature),
    }
}

} // verus!

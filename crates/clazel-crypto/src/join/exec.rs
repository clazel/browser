//! The executable join, proven to meet [`super::contract`]: the production
//! `clazel_tls::auth::verify::Verifier`. Chain validation is
//! `clazel_x509::path::search::exec::verify_server_chain` (P9) with
//! [`crate::chain::exec::CertificateLinks`] (P11); CertificateVerify is
//! [`crate::signature::exec::verify`]; Finished is compared by
//! [`crate::compare::constant_time_eq`].
//!
//! The verifier over Mozilla's roots is [`mozilla`], outside `verus!`: it
//! only copies each row of `clazel_x509::roots::ROOTS` (a plain Rust table,
//! which Verus does not read) into a [`Root`] and calls the proven
//! [`ChainVerifier::new`]. That copy is the one unverified step between the
//! table and the anchors; `tests/join.rs` checks that it yields 118 anchors.
use clazel_tls::auth::spec::CertificateError;
use clazel_tls::host::exec::Host;
use clazel_x509::exec::ReferenceIdentity;
use clazel_x509::path::exec::Environment;
use clazel_x509::path::parsed::exec::{Anchor, PathCert};
use clazel_x509::path::spec::PathError;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One row of a root table ([`super::spec::RootEntry`]).
#[derive(Clone, Copy, Debug)]
pub struct Root<'a> {
    /// The complete DER `Certificate`.
    pub der: &'a [u8],
    /// NSS's `CKA_NSS_SERVER_DISTRUST_AFTER` UTCTime text, if any.
    pub server_distrust_after: Option<&'a [u8]>,
}

/// The spec value of a row.
pub open spec fn view_root(root: Root<'_>) -> super::spec::RootEntry {
    super::spec::RootEntry {
        der: root.der@,
        server_distrust_after: match root.server_distrust_after { Some(text) => Some(text@), None => None },
    }
}

/// The spec value of a table.
pub open spec fn view_roots(roots: Seq<Root<'_>>) -> Seq<super::spec::RootEntry> {
    roots.map_values(|root: Root<'_>| view_root(root))
}

/// §6.1.3 (a)(3), design Q4: the production revocation oracle, which
/// revokes nothing.
pub struct NothingRevoked;

impl clazel_x509::path::contract::RevocationOracle for NothingRevoked {
    open spec fn revoked(&self) -> clazel_x509::path::spec::RevokedFn {
        super::spec::not_revoked()
    }

    fn is_revoked(&self, _cert: &PathCert<'_>) -> (out: bool) {
        false
    }
}

/// RFC 8446 §6.2: [`super::spec::certificate_error`].
fn certificate_error(error: PathError) -> (out: CertificateError)
    ensures out == super::spec::certificate_error(error),
{
    match error {
        PathError::Expired | PathError::AnchorExpired => CertificateError::Expired,
        PathError::UnsupportedAlgorithm => CertificateError::Unsupported,
        PathError::UnknownIssuer | PathError::BadSignature | PathError::NameChaining
            | PathError::Distrusted | PathError::Revoked | PathError::BuildBudgetExhausted => CertificateError::UnknownCa,
        _ => CertificateError::BadCertificate,
    }
}

/// Design Q2: the typed host as the reference identity.
fn reference_identity(host: &Host) -> (out: ReferenceIdentity<'_>)
    ensures clazel_x509::exec::view_reference_identity(&out) == super::spec::reference_identity(host@),
{
    match host {
        Host::Dns(name) => ReferenceIdentity::Dns(name.as_slice()),
        Host::Ip(address) => ReferenceIdentity::Ip(address.as_slice()),
    }
}

/// The spec value of a validator result.
pub open spec fn view_result(out: Result<Vec<u8>, CertificateError>) -> Result<Seq<u8>, CertificateError> {
    match out { Ok(key) => Ok(key@), Err(e) => Err(e) }
}

/// The production chain verifier over a fixed set of trust anchors.
pub struct ChainVerifier<'r> {
    anchors: Vec<Anchor<'r>>,
}

impl<'r> ChainVerifier<'r> {
    /// The trust anchors this verifier validates against.
    pub closed spec fn anchors(&self) -> Seq<clazel_x509::path::parsed::spec::Anchor> {
        clazel_x509::path::exec::view_anchors(self.anchors@)
    }

    /// The verifier over the anchors of `roots` ([`super::spec::anchors_from_roots`]).
    pub fn new(roots: &[Root<'r>]) -> (out: Self)
        ensures super::contract::new_ensures(view_roots(roots@), out.anchors()),
    {
        hide(clazel_x509::path::parsed::spec::anchor_from_root);
        let mut anchors: Vec<Anchor<'r>> = Vec::new();
        let mut i: usize = 0;
        proof { assert(view_roots(roots@).take(0) =~= Seq::<super::spec::RootEntry>::empty()); }
        while i < roots.len()
            invariant
                i <= roots.len(),
                clazel_x509::path::exec::view_anchors(anchors@) == super::spec::anchors_from_roots(view_roots(roots@).take(i as int)),
            decreases roots.len() - i,
        {
            // Not reached: i < roots.len().
            let Some(root) = roots.get(i) else { return ChainVerifier { anchors }; };
            let ghost before = anchors@;
            let ghost prefix = view_roots(roots@).take(i as int + 1);
            proof {
                assert(prefix.drop_last() =~= view_roots(roots@).take(i as int));
                assert(prefix.last() == view_root(*root));
            }
            if let Some(anchor) = clazel_x509::path::parsed::exec::anchor_from_root(root.der, root.server_distrust_after) {
                anchors.push(anchor);
                proof {
                    assert(clazel_x509::path::exec::view_anchors(anchors@)
                        =~= clazel_x509::path::exec::view_anchors(before).push(clazel_x509::path::parsed::exec::view_anchor(&anchor)));
                }
            }
            // i < roots.len(), so this is exact.
            i = i.saturating_add(1);
        }
        proof { assert(view_roots(roots@).take(roots@.len() as int) =~= view_roots(roots@)); }
        ChainVerifier { anchors }
    }

    /// How many trust anchors this verifier holds.
    pub fn anchor_count(&self) -> (out: usize)
        ensures out == self.anchors().len(),
    {
        self.anchors.len()
    }

    /// RFC 8446 §4.4.2: [`super::spec::validate`] over this verifier's
    /// anchors; an `Ok` key is `chain_verified` (`contract::thm_validate_sound`).
    pub fn validate(&self, host: &Host, now: u64, body: &[u8]) -> (out: Result<Vec<u8>, CertificateError>)
        ensures
            super::contract::validate_ensures(self.anchors(), host@, now, body@, view_result(out)),
            match out {
                Ok(key) => super::contract::chain_verified(self.anchors(), host@, now, body@, key@),
                Err(_) => true,
            },
    {
        hide(clazel_x509::path::parsed::spec::parse_path_cert);
        hide(clazel_x509::path::verifier::candidate_verdict);
        hide(clazel_x509::path::search::spec::verify_server_chain);
        hide(super::contract::chain_verified);
        proof { super::lemmas::lemma_thm_validate_sound(self.anchors(), host@, now, body@); }
        // 1. §4.4.2: the body is a Certificate.
        let certificate = match clazel_tls::handshake::read_certificate(body) {
            Some(certificate) => certificate,
            None => return Err(CertificateError::BadCertificate),
        };
        // 2. The leaf first, then the pool: every entry's cert_data, in order.
        let ghost entries = clazel_tls::types::views(certificate.entries@);
        let mut presented: Vec<&[u8]> = Vec::new();
        let mut k: usize = 0;
        while k < certificate.entries.len()
            invariant
                k <= certificate.entries.len(),
                entries == clazel_tls::types::views(certificate.entries@),
                clazel_x509::path::exec::view_presented(presented@) == super::spec::presented(entries).take(k as int),
            decreases certificate.entries.len() - k,
        {
            // Not reached: k < certificate.entries.len().
            let Some(entry) = certificate.entries.get(k) else { return Err(CertificateError::BadCertificate); };
            let ghost before = presented@;
            presented.push(entry.cert_data);
            proof {
                assert(entries.len() == certificate.entries@.len());
                assert(super::spec::presented(entries).len() == entries.len());
                assert(entries[k as int] == entry@);
                let expected = super::spec::presented(entries).take(k as int + 1);
                let got = clazel_x509::path::exec::view_presented(presented@);
                assert(clazel_x509::path::exec::view_presented(before).len() == before.len());
                assert(before.len() == k);
                assert(presented@.len() == k + 1);
                assert(got.len() == k + 1);
                assert(expected.len() == k + 1);
                assert forall|j: int| 0 <= j < got.len() implies got[j] == expected[j] by {
                    if j < k {
                        assert(presented@[j] == before[j]);
                        assert(got[j] == clazel_x509::path::exec::view_presented(before)[j]);
                    } else {
                        assert(presented@[j] == entry.cert_data);
                    }
                }
                assert(got =~= expected);
            }
            // k < len, so this is exact.
            k = k.saturating_add(1);
        }
        proof {
            assert(super::spec::presented(entries).take(entries.len() as int) =~= super::spec::presented(entries));
        }
        let reference = reference_identity(host);
        let links = crate::chain::exec::CertificateLinks;
        let revoked = NothingRevoked;
        // Design §1.12: mozilla::pkix `MAX_SUBCA_COUNT`.
        let environment = Environment { link: &links, revoked: &revoked, max_intermediates: 6 };
        proof {
            assert(clazel_x509::path::exec::view_environment(&environment) == super::spec::production_environment());
        }
        match clazel_x509::path::search::exec::verify_server_chain(&environment, self.anchors.as_slice(),
            presented.as_slice(), reference, now) {
            // 3. The leaf's key.
            Ok(validated) => Ok(validated.leaf_spki),
            // 4. §6.2: the refusal's alert.
            Err(error) => Err(certificate_error(error)),
        }
    }
}

impl<'r> clazel_tls::auth::verify::Verifier for ChainVerifier<'r> {
    open spec fn functions(&self) -> clazel_tls::auth::spec::Verification {
        super::spec::verification(self.anchors())
    }

    fn chain(&self, host: &Host, now: u64, certificate_body: &[u8]) -> (out: Result<Vec<u8>, CertificateError>)
        ensures match out {
            Ok(key) => super::contract::chain_verified(self.anchors(), host@, now, certificate_body@, key@),
            Err(_) => true,
        },
    {
        self.validate(host, now, certificate_body)
    }

    fn signature(&self, key: &[u8], scheme: u16, input: &[u8], signature: &[u8]) -> (out: bool) {
        crate::signature::exec::verify(key, scheme, input, signature)
    }

    fn finished_equal(&self, received: &[u8], expected: &[u8]) -> (out: bool) {
        crate::compare::constant_time_eq(received, expected)
    }
}

} // verus!

/// The production verifier: [`ChainVerifier::new`] over every row of
/// Mozilla's server-root table, `clazel_x509::roots::ROOTS`, in table order,
/// with its `server_distrust_after` text. Not verified (the module header
/// says why); it copies the rows and nothing else.
pub fn mozilla() -> ChainVerifier<'static> {
    let roots: Vec<Root<'static>> = clazel_x509::roots::ROOTS
        .iter()
        .map(|root| Root {
            der: root.der,
            server_distrust_after: root.server_distrust_after.map(str::as_bytes),
        })
        .collect();
    ChainVerifier::new(&roots)
}

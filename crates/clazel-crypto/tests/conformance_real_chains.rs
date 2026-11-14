//! Real certificate chains (phase-3.md item 3.5g, "Real-certificate
//! compatibility measurement"): what servers actually sent, through this
//! crate's production verifier and through `rustls-webpki`, both with real
//! signatures and the Mozilla root table.
//!
//! The corpus is vendored under `tests/fixtures/real-chains-2026-11-05`, with
//! `SOURCE.md` saying how it was collected. `certs.der` holds each
//! certificate once; `chains.tsv` gives each host's chain, in the order the
//! server sent it, by SHA-256 fingerprint.
//!
//! Two suites:
//! - every certificate decodes (envelope, TBSCertificate, SubjectPublicKeyInfo,
//!   extensions, signature algorithm). The extension decoder refuses an
//!   explicit `critical` FALSE (X.690 §11.5) and a BOOLEAN other than 0xFF, so
//!   this also says no certificate here has either;
//! - each chain gets the same verdict from both engines, for its host at
//!   [`NOW`]. Every difference is listed in [`DIFFERENCES`] with its reason,
//!   and the test fails on an unlisted difference or a listed case that no
//!   longer differs.

use std::collections::{BTreeMap, BTreeSet};

use clazel_crypto::axioms::sha256;
use clazel_crypto::join::exec::{ChainVerifier, mozilla};
use clazel_tls::host::exec::Host;
use clazel_x509::certificate::exec::parse_certificate;
use clazel_x509::extensions::exec::parse_extensions;
use clazel_x509::roots::ROOTS;
use clazel_x509::signature_algorithm::exec::classify;
use clazel_x509::spki::exec::parse_subject_public_key_info;
use clazel_x509::tbs::exec::parse_tbs_certificate;
use rustls::RootCertStore;
use rustls::client::WebPkiServerVerifier;
use rustls::client::danger::ServerCertVerifier;
use rustls::crypto::ring::default_provider;
use rustls::pki_types::{CertificateDer, ServerName, UnixTime};
use std::sync::Arc;
use std::time::Duration;

const CERTS: &[u8] = include_bytes!("fixtures/real-chains-2026-11-05/certs.der");
const CHAINS: &str = include_str!("fixtures/real-chains-2026-11-05/chains.tsv");

/// When the chains were collected, in seconds since the Unix epoch.
const NOW: u64 = 1_793_895_800;

/// Chains, certificates sent, distinct certificates, those only ever sent
/// first (leaves), only ever sent later, and those in the root table.
const COUNTS: (usize, usize, usize, usize, usize, usize) = (760, 2276, 868, 709, 156, 14);

/// (host, which engine accepts, reason), by hand.
const DIFFERENCES: &[(&str, &str, &str)] = &[];

/// The length of the DER value at the start of `der`, header included.
fn der_len(der: &[u8]) -> Option<usize> {
    let first = usize::from(*der.get(1)?);
    if first < 0x80 {
        return first.checked_add(2);
    }
    let octets = first & 0x7f;
    let header = der.get(2..octets.checked_add(2)?)?;
    let body = header
        .iter()
        .fold(0usize, |n, b| (n << 8) | usize::from(*b));
    body.checked_add(octets)?.checked_add(2)
}

/// Every certificate of `certs.der` by SHA-256 fingerprint, in hex.
fn certificates() -> Result<BTreeMap<String, &'static [u8]>, String> {
    let mut out = BTreeMap::new();
    let mut rest = CERTS;
    while !rest.is_empty() {
        let len = der_len(rest).ok_or("a certificate has no DER length")?;
        let (der, after) = rest
            .split_at_checked(len)
            .ok_or("a truncated certificate")?;
        let hex: String = sha256(der).iter().map(|b| format!("{b:02x}")).collect();
        out.insert(hex, der);
        rest = after;
    }
    Ok(out)
}

/// Why `der` does not decode, or `None`.
fn decode_failure(der: &[u8]) -> Option<&'static str> {
    let Some(cert) = parse_certificate(der) else {
        return Some("envelope");
    };
    let Some(tbs) = parse_tbs_certificate(cert.tbs_certificate_der) else {
        return Some("TBSCertificate");
    };
    if parse_subject_public_key_info(tbs.subject_public_key_info_der).is_none() {
        return Some("SubjectPublicKeyInfo");
    }
    if let Some(ext) = tbs.extensions_sequence_der
        && parse_extensions(ext).is_none()
    {
        return Some("extensions");
    }
    if classify(&cert.signature_algorithm).is_none() {
        return Some("signature algorithm");
    }
    None
}

/// RFC 8446 §4.4.2's Certificate body for `chain`: an empty context, then
/// each certificate with no extensions.
fn body_of(chain: &[&[u8]]) -> Option<Vec<u8>> {
    fn u24(n: usize) -> Option<[u8; 3]> {
        let [_, a, b, c] = u32::try_from(n).ok()?.to_be_bytes();
        Some([a, b, c])
    }
    let mut list = Vec::new();
    for der in chain {
        list.extend_from_slice(&u24(der.len())?);
        list.extend_from_slice(der);
        list.extend_from_slice(&[0, 0]);
    }
    let mut body = vec![0];
    body.extend_from_slice(&u24(list.len())?);
    body.extend_from_slice(&list);
    Some(body)
}

/// Our verdict on `chain` for `host`.
fn ours(verifier: &ChainVerifier<'_>, host: &str, chain: &[&[u8]]) -> Result<bool, String> {
    let body = body_of(chain).ok_or("a chain too long to encode")?;
    let name = Host::Dns(host.as_bytes().to_vec());
    Ok(verifier.validate(&name, NOW, &body).is_ok())
}

/// `rustls-webpki`'s verdict on `chain` for `host`, through rustls's verifier.
fn theirs(verifier: &WebPkiServerVerifier, host: &str, chain: &[&[u8]]) -> Result<bool, String> {
    let (leaf, rest) = chain.split_first().ok_or("an empty chain")?;
    let leaf = CertificateDer::from(*leaf);
    let rest: Vec<CertificateDer<'_>> = rest.iter().map(|d| CertificateDer::from(*d)).collect();
    let name = ServerName::try_from(host).map_err(|e| e.to_string())?;
    let now = UnixTime::since_unix_epoch(Duration::from_secs(NOW));
    Ok(verifier
        .verify_server_cert(&leaf, &rest, &name, &[], now)
        .is_ok())
}

/// The second engine, over the same roots.
fn webpki() -> Result<Arc<WebPkiServerVerifier>, String> {
    let mut roots = RootCertStore::empty();
    let (added, ignored) =
        roots.add_parsable_certificates(ROOTS.iter().map(|r| CertificateDer::from(r.der)));
    assert_eq!((added, ignored), (ROOTS.len(), 0));
    WebPkiServerVerifier::builder_with_provider(Arc::new(roots), Arc::new(default_provider()))
        .build()
        .map_err(|e| e.to_string())
}

/// The fingerprints of each chain, in the order the server sent them.
fn sent_chains() -> impl Iterator<Item = Vec<&'static str>> {
    CHAINS
        .lines()
        .filter_map(|line| line.rsplit('\t').next())
        .map(|prints| prints.split(' ').collect())
}

#[test]
#[cfg_attr(miri, ignore = "hashes 1.4 MB of certificates")]
fn corpus_counts() -> Result<(), String> {
    let certs = certificates()?;
    let mut first = BTreeSet::new();
    let mut later = BTreeSet::new();
    let mut sent = 0usize;
    for chain in sent_chains() {
        sent = sent.saturating_add(chain.len());
        let mut prints = chain.into_iter();
        first.extend(prints.next());
        later.extend(prints);
    }
    let anchors = certs
        .values()
        .filter(|der| ROOTS.iter().any(|root| root.der == **der))
        .count();
    assert_eq!(
        (
            sent_chains().count(),
            sent,
            certs.len(),
            first.difference(&later).count(),
            later.difference(&first).count(),
            anchors,
        ),
        COUNTS
    );
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "verifies 760 chains with real signatures")]
fn real_chains() -> Result<(), String> {
    let certs = certificates()?;
    let decoded = certs
        .values()
        .filter(|d| decode_failure(d).is_none())
        .count();
    let refused = certs.len().saturating_sub(decoded);
    println!(
        "clazel-conformance: suite=\"real certificates decode\" pass={decoded} xfail=0 fail={refused} total={}",
        certs.len()
    );

    let mozilla_roots = mozilla();
    let reference = webpki()?;
    let mut chains = 0usize;
    let (mut both, mut neither, mut listed, mut unexpected) = (0usize, 0usize, 0usize, 0usize);
    for line in CHAINS.lines() {
        let mut fields = line.split('\t');
        let (Some(_rank), Some(host), Some(prints)) = (fields.next(), fields.next(), fields.next())
        else {
            return Err(format!("bad line: {line}"));
        };
        let chain = prints
            .split(' ')
            .map(|p| certs.get(p).copied().ok_or(format!("no certificate {p}")))
            .collect::<Result<Vec<&[u8]>, String>>()?;
        chains = chains.saturating_add(1);
        let verdicts = (
            ours(&mozilla_roots, host, &chain)?,
            theirs(&reference, host, &chain)?,
        );
        match verdicts {
            (true, true) => both = both.saturating_add(1),
            (false, false) => neither = neither.saturating_add(1),
            (ours, _) => {
                let accepts = if ours { "ours" } else { "webpki" };
                if DIFFERENCES.iter().any(|d| (d.0, d.1) == (host, accepts)) {
                    listed = listed.saturating_add(1);
                } else {
                    println!("unlisted difference: {host}, accepted by {accepts}");
                    unexpected = unexpected.saturating_add(1);
                }
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"real chains, ours against webpki\" pass={} xfail={listed} fail={unexpected} total={chains}",
        both.saturating_add(neither)
    );
    println!("accepted by both {both}, refused by both {neither}");
    assert_eq!(refused, 0, "a real certificate does not decode");
    assert_eq!(unexpected, 0, "an unlisted difference");
    assert_eq!(listed, DIFFERENCES.len(), "a listed case no longer differs");
    Ok(())
}

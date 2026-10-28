//! The root certificate table (`clazel_x509::roots`), generated from NSS's
//! `certdata.txt` by `cargo xtask tables`.
//!
//! Three kinds of evidence, none of them the generator's own code:
//! - every root decodes with this crate's own decoders (envelope, TBS,
//!   SubjectPublicKeyInfo, extensions, signature algorithm), and is
//!   self-issued with a decodable signature algorithm;
//! - the table is internally consistent (count, well-known labels, no
//!   duplicates, the fingerprint of the ISRG Root X1 from its published
//!   value, `sha256` the real SHA-256 of `der`);
//! - the table equals the vendored `certdata.txt` read by a second, separate
//!   scanner in this file: the same set of roots, DER bytes and distrust-after
//!   dates, found through the `# Fingerprint (SHA-256)` comments NSS writes
//!   rather than through the generator's issuer-and-serial join.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::process::{Command, Stdio};

use clazel_x509::certificate::exec::parse_certificate;
use clazel_x509::extensions::exec::parse_extensions;
use clazel_x509::roots::{ROOTS, Root};
use clazel_x509::signature_algorithm::exec::classify;
use clazel_x509::spki::exec::parse_subject_public_key_info;
use clazel_x509::tbs::exec::parse_tbs_certificate;

const CERTDATA: &str = include_str!("../data/nss-0a2b0c75/certdata.txt");

/// Roots in the table at NSS commit 0a2b0c75.
const ROOT_COUNT: usize = 118;

/// Roots our decoders reject, with the reason. Empty: every root decodes.
const REJECTED: &[(&str, &str)] = &[];

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Why the certificate `der` does not decode, or `None`.
fn decode_failure(der: &[u8]) -> Option<String> {
    let Some(cert) = parse_certificate(der) else {
        return Some("envelope".into());
    };
    let Some(tbs) = parse_tbs_certificate(cert.tbs_certificate_der) else {
        return Some("TBSCertificate".into());
    };
    if parse_subject_public_key_info(tbs.subject_public_key_info_der).is_none() {
        return Some("SubjectPublicKeyInfo".into());
    }
    if let Some(ext) = tbs.extensions_sequence_der
        && parse_extensions(ext).is_none()
    {
        return Some("extensions".into());
    }
    if classify(&cert.signature_algorithm).is_none() {
        return Some("signature algorithm".into());
    }
    if classify(&tbs.signature).is_none() {
        return Some("TBS signature algorithm".into());
    }
    if tbs.issuer_der != tbs.subject_der {
        return Some("not self-issued".into());
    }
    None
}

#[test]
fn every_root_decodes() {
    let mut failures: Vec<(&str, String)> = Vec::new();
    for root in &ROOTS {
        if let Some(why) = decode_failure(root.der) {
            failures.push((root.label, why));
        }
    }
    let expected: Vec<(&str, String)> = REJECTED
        .iter()
        .map(|(l, w)| (*l, (*w).to_owned()))
        .collect();
    assert_eq!(failures, expected, "roots our decoders reject");
}

#[test]
fn the_decode_check_can_fail() {
    // The check above is not vacuous: a damaged root is reported.
    let mut der = ROOTS[0].der.to_vec();
    der.truncate(der.len() - 1);
    assert_eq!(decode_failure(&der).as_deref(), Some("envelope"));
    let with_extensions = ROOTS
        .iter()
        .filter(|r| {
            parse_certificate(r.der).and_then(|c| {
                parse_tbs_certificate(c.tbs_certificate_der)
                    .map(|t| t.extensions_sequence_der.is_some())
            }) == Some(true)
        })
        .count();
    assert!(with_extensions > 100, "{with_extensions}");
}

#[test]
fn count_and_well_known_labels() {
    assert_eq!(ROOTS.len(), ROOT_COUNT);
    let labels: BTreeSet<&str> = ROOTS.iter().map(|r| r.label).collect();
    for want in [
        "ISRG Root X1",
        "ISRG Root X2",
        "DigiCert Global Root G2",
        "GlobalSign Root CA - R3",
        "USERTrust RSA Certification Authority",
        "Amazon Root CA 1",
        "Microsoft ECC Root Certificate Authority 2017",
    ] {
        assert!(labels.contains(want), "{want} is missing");
    }
    // Present in certdata.txt but not trusted for TLS servers.
    for not in [
        "Entrust.net Premium 2048 Secure Server CA",
        "Go Daddy Class 2 CA",
        "Starfield Class 2 CA",
    ] {
        assert!(!labels.contains(not), "{not} must be excluded");
    }
}

#[test]
fn no_duplicates() {
    let labels: BTreeSet<&str> = ROOTS.iter().map(|r| r.label).collect();
    let ders: BTreeSet<&[u8]> = ROOTS.iter().map(|r| r.der).collect();
    let prints: BTreeSet<[u8; 32]> = ROOTS.iter().map(|r| r.sha256).collect();
    assert_eq!(labels.len(), ROOTS.len(), "duplicate label");
    assert_eq!(ders.len(), ROOTS.len(), "duplicate DER");
    assert_eq!(prints.len(), ROOTS.len(), "duplicate fingerprint");
}

#[test]
fn isrg_root_x1_fingerprint_is_the_published_one() {
    // letsencrypt.org/certificates: ISRG Root X1, SHA-256 fingerprint.
    let want = "96bcec06264976f37460779acf28c5a7cfe8a3c0aae11a8ffcee05c0bddf08c6";
    let root = ROOTS.iter().find(|r| r.label == "ISRG Root X1");
    assert_eq!(root.map(|r| hex(&r.sha256)).as_deref(), Some(want));
}

#[test]
fn distrust_after_is_carried() {
    let dated: BTreeMap<&str, &str> = ROOTS
        .iter()
        .filter_map(|r| r.server_distrust_after.map(|d| (r.label, d)))
        .collect();
    assert_eq!(dated, BTreeMap::from([("Izenpe.com", "260415235959Z")]));
}

/// SHA-256 through the system's tool, so no hash code of ours is trusted.
fn system_sha256(data: &[u8]) -> Option<String> {
    for (program, args) in [("sha256sum", &[][..]), ("shasum", &["-a", "256"][..])] {
        let Ok(mut child) = Command::new(program)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
        else {
            continue;
        };
        child.stdin.take()?.write_all(data).ok()?;
        let out = child.wait_with_output().ok()?;
        return String::from_utf8(out.stdout)
            .ok()?
            .split_whitespace()
            .next()
            .map(str::to_owned);
    }
    None
}

#[test]
#[cfg_attr(miri, ignore = "runs sha256sum")]
fn sha256_field_is_the_hash_of_the_der() {
    for root in &ROOTS {
        assert_eq!(
            system_sha256(root.der).as_deref(),
            Some(hex(&root.sha256).as_str()),
            "{}",
            root.label
        );
    }
}

/// `\ooo` escapes of a `MULTILINE_OCTAL` body.
fn octal(body: &[&str]) -> Vec<u8> {
    let mut out = Vec::new();
    for line in body {
        for esc in line.split('\\').skip(1) {
            out.push(u8::from_str_radix(esc, 8).unwrap_or(0));
        }
    }
    out
}

/// The lines after `name MULTILINE_OCTAL` up to `END`.
fn multiline<'a>(chunk: &'a [&'a str], name: &str) -> Option<Vec<&'a str>> {
    let start = chunk
        .iter()
        .position(|l| *l == format!("{name} MULTILINE_OCTAL"))?;
    Some(
        chunk
            .iter()
            .skip(start.saturating_add(1))
            .take_while(|l| **l != "END")
            .copied()
            .collect(),
    )
}

/// What a second reading of `certdata.txt` expects, by SHA-256 hex.
struct Expected {
    label: String,
    der: Vec<u8>,
    distrust_after: Option<String>,
}

/// Objects are blank-line separated chunks; a chunk's own `# Fingerprint
/// (SHA-256)` comment names the certificate. Trusted-delegator trust chunks
/// choose the fingerprints; certificate chunks give their DER and date.
fn expected_from_certdata() -> BTreeMap<String, Expected> {
    let chunks: Vec<Vec<&str>> = CERTDATA
        .split("\n\n")
        .map(|c| c.lines().collect())
        .collect();
    let print = |chunk: &[&str]| -> Option<String> {
        chunk.iter().find_map(|l| {
            l.strip_prefix("# Fingerprint (SHA-256): ")
                .map(|f| f.replace(':', "").to_ascii_lowercase())
        })
    };
    let is = |chunk: &[&str], line: &str| chunk.contains(&line);
    let trusted: BTreeSet<String> = chunks
        .iter()
        .filter(|c| {
            is(c, "CKA_CLASS CK_OBJECT_CLASS CKO_NSS_TRUST")
                && is(
                    c,
                    "CKA_TRUST_SERVER_AUTH CK_TRUST CKT_NSS_TRUSTED_DELEGATOR",
                )
        })
        .filter_map(|c| print(c))
        .collect();
    let mut out = BTreeMap::new();
    for c in chunks
        .iter()
        .filter(|c| is(c, "CKA_CLASS CK_OBJECT_CLASS CKO_CERTIFICATE"))
    {
        let Some(fp) = print(c).filter(|f| trusted.contains(f)) else {
            continue;
        };
        let label = c
            .iter()
            .find_map(|l| l.strip_prefix("CKA_LABEL UTF8 \""))
            .and_then(|l| l.strip_suffix('"'))
            .unwrap_or("")
            .to_owned();
        let der = multiline(c, "CKA_VALUE")
            .map(|b| octal(&b))
            .unwrap_or_default();
        let distrust_after = multiline(c, "CKA_NSS_SERVER_DISTRUST_AFTER")
            .map(|b| String::from_utf8_lossy(&octal(&b)).into_owned());
        out.insert(
            fp,
            Expected {
                label,
                der,
                distrust_after,
            },
        );
    }
    assert_eq!(
        out.len(),
        trusted.len(),
        "a trusted fingerprint with no certificate"
    );
    out
}

#[test]
#[cfg_attr(miri, ignore = "scans the 1.3 MB certdata.txt")]
fn table_equals_certdata_txt() {
    let expected = expected_from_certdata();
    assert_eq!(expected.len(), ROOT_COUNT);
    let table: BTreeMap<String, &Root> = ROOTS.iter().map(|r| (hex(&r.sha256), r)).collect();
    assert_eq!(
        table.keys().collect::<Vec<_>>(),
        expected.keys().collect::<Vec<_>>(),
        "different sets of roots"
    );
    for (fp, want) in &expected {
        let Some(root) = table.get(fp) else {
            continue;
        };
        assert_eq!(root.label, want.label, "{fp}");
        assert_eq!(root.der, want.der.as_slice(), "{}", want.label);
        assert_eq!(
            root.server_distrust_after,
            want.distrust_after.as_deref(),
            "{}",
            want.label
        );
    }
}

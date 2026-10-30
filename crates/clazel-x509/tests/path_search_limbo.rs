//! Every x509-limbo `SERVER` testcase through the full
//! `path::search::exec::verify_server_chain` (P9), reported, not pinned:
//! the limbo pin lists of `conformance_limbo.rs` are P12's and are not
//! touched here.
//!
//! - **Signatures are not checked.** clazel-x509 has no signature verifier
//!   of its own (P11 supplies the real one, in `clazel-crypto`, which depends
//!   on this crate), so the link verifier accepts every link. A limbo
//!   `FAILURE` that rests on a bad signature is therefore accepted here.
//! - **Depth** is the production `max_intermediates` 6: the generated index
//!   does not carry limbo's `max_chain_depth` yet (P12).
//! - **Inputs**: `presented` is the leaf then limbo's intermediates in
//!   order; the anchors are limbo's trusted certificates that
//!   `anchor_from_root` accepts; the time is limbo's validation time, or the
//!   leaf's notBefore when limbo gives none.
//!
//! The test fails only if the search panics or a case cannot be set up; it
//! prints the agreement counts and every disagreement class.

use std::collections::BTreeMap;
use std::net::IpAddr;

use clazel_x509::certificate::exec::{AlgorithmIdentifier, parse_certificate};
use clazel_x509::matcher::ReferenceIdentity;
use clazel_x509::path::contract::{LinkVerifier, RevocationOracle};
use clazel_x509::path::exec::Environment;
use clazel_x509::path::parsed::exec::{Anchor, PathCert, anchor_from_root};
use clazel_x509::path::search::exec::verify_server_chain;
use clazel_x509::tbs::exec::parse_tbs_certificate;
use clazel_x509::time::exec::CertificateTime;

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
    trusted: &'static [usize],
    intermediates: &'static [usize],
    leaf: usize,
}

// `TESTCASE_COUNT`, `CERT_SPANS` and `CASES`, generated from the vendored file.
include!("generated/x509_limbo.rs");

static CERTS: &[u8] = include_bytes!("generated/x509_limbo_certs.bin");

fn cert(index: usize) -> Option<&'static [u8]> {
    let &(offset, length) = CERT_SPANS.get(index)?;
    let start = usize::try_from(offset).ok()?;
    let end = start.checked_add(usize::try_from(length).ok()?)?;
    CERTS.get(start..end)
}

struct AcceptAll;

impl LinkVerifier for AcceptAll {
    fn verify(&self, _: &[u8], _: &AlgorithmIdentifier<'_>, _: &[u8], _: &[u8]) -> bool {
        true
    }
}

struct NotRevoked;

impl RevocationOracle for NotRevoked {
    fn is_revoked(&self, _: &PathCert<'_>) -> bool {
        false
    }
}

/// `YYYY-MM-DDTHH:MM:SS[.fff]+00:00`.
fn parse_time(text: &str) -> Option<CertificateTime> {
    let body = text.strip_suffix("+00:00")?;
    let (date, clock) = body.split_once('T')?;
    let mut d = date.split('-');
    let mut c = clock.split(':');
    Some(CertificateTime {
        year: d.next()?.parse().ok()?,
        month: d.next()?.parse().ok()?,
        day: d.next()?.parse().ok()?,
        hour: c.next()?.parse().ok()?,
        minute: c.next()?.parse().ok()?,
        second: c.next()?.split('.').next()?.parse().ok()?,
    })
}

/// Unix seconds of a UTC time (proleptic Gregorian, days from civil).
fn unix_seconds(t: &CertificateTime) -> Option<u64> {
    let (m, d) = (i64::from(t.month), i64::from(t.day));
    let y = i64::from(t.year).checked_sub(i64::from(m <= 2))?;
    let era = y.div_euclid(400);
    let yoe = y.rem_euclid(400);
    let mp = m.checked_add(9)?.checked_rem(12)?;
    let doy = mp
        .checked_mul(153)?
        .checked_add(2)?
        .checked_div(5)?
        .checked_add(d)?
        .checked_sub(1)?;
    let doe = yoe
        .checked_mul(365)?
        .checked_add(yoe / 4)?
        .checked_sub(yoe / 100)?
        .checked_add(doy)?;
    let days = era
        .checked_mul(146_097)?
        .checked_add(doe)?
        .checked_sub(719_468)?;
    let clock = i64::from(t.hour)
        .checked_mul(3600)?
        .checked_add(i64::from(t.minute).checked_mul(60)?)?
        .checked_add(i64::from(t.second))?;
    u64::try_from(days.checked_mul(86_400)?.checked_add(clock)?).ok()
}

/// The case's time as Unix seconds.
fn case_time(case: &Case) -> Option<u64> {
    let time = if case.time.is_empty() {
        let envelope = parse_certificate(cert(case.leaf)?)?;
        parse_tbs_certificate(envelope.tbs_certificate_der)?.not_before
    } else {
        parse_time(case.time)?
    };
    unix_seconds(&time)
}

/// The id's first two components (`webpki::san`, `bettertls::nameconstraints`).
fn family(id: &str) -> String {
    id.split("::").take(2).collect::<Vec<_>>().join("::")
}

#[derive(Default)]
struct Tally {
    agree_success: usize,
    agree_failure: usize,
    /// Expected SUCCESS, refused: (error, family) -> count.
    false_refusals: BTreeMap<(String, String), usize>,
    /// Expected FAILURE, accepted: (family, features, importance) -> count.
    false_accepts: BTreeMap<(String, String, &'static str), usize>,
    /// Cases with more than one peer name (only the first is used).
    several_names: usize,
    /// Cases not run: reason -> count.
    skipped: BTreeMap<&'static str, usize>,
}

#[test]
#[cfg_attr(miri, ignore)]
fn limbo_server_cases_through_verify_server_chain() {
    assert_eq!(CASES.len(), TESTCASE_COUNT);
    let mut tally = Tally::default();
    for case in CASES.iter().filter(|c| c.kind == "SERVER") {
        tally.several_names = tally
            .several_names
            .saturating_add(usize::from(case.peer_names.len() > 1));
        let mut skip = |reason| {
            let n = tally.skipped.entry(reason).or_insert(0);
            *n = n.saturating_add(1);
        };
        let Some(now) = case_time(case) else {
            skip("time");
            continue;
        };
        let ip;
        let reference = match case.peer {
            ("DNS", name) => ReferenceIdentity::Dns(name.as_bytes()),
            ("IP", text) => match text.parse::<IpAddr>() {
                Ok(IpAddr::V4(a)) => {
                    ip = a.octets().to_vec();
                    ReferenceIdentity::Ip(&ip)
                }
                Ok(IpAddr::V6(a)) => {
                    ip = a.octets().to_vec();
                    ReferenceIdentity::Ip(&ip)
                }
                Err(_) => {
                    skip("peer address");
                    continue;
                }
            },
            _ => {
                skip("no peer name");
                continue;
            }
        };
        let anchors: Vec<Anchor<'_>> = case
            .trusted
            .iter()
            .filter_map(|&i| cert(i).and_then(|der| anchor_from_root(der, None)))
            .collect();
        let presented: Option<Vec<&[u8]>> = std::iter::once(case.leaf)
            .chain(case.intermediates.iter().copied())
            .map(cert)
            .collect();
        let Some(presented) = presented else {
            skip("certificate index");
            continue;
        };
        let environment = Environment {
            link: &AcceptAll,
            revoked: &NotRevoked,
            max_intermediates: 6,
        };
        let out = verify_server_chain(&environment, &anchors, &presented, reference, now);
        match (case.expected, out) {
            ("SUCCESS", Ok(_)) => tally.agree_success = tally.agree_success.saturating_add(1),
            ("FAILURE", Err(_)) => tally.agree_failure = tally.agree_failure.saturating_add(1),
            ("SUCCESS", Err(e)) => {
                let error = if anchors.len() < case.trusted.len() && anchors.is_empty() {
                    format!("{e:?} (no trusted certificate is an anchor)")
                } else {
                    format!("{e:?}")
                };
                let n = tally
                    .false_refusals
                    .entry((error, family(case.id)))
                    .or_insert(0);
                *n = n.saturating_add(1);
            }
            (_, Ok(_)) => {
                let key = (family(case.id), case.features.join(","), case.importance);
                let n = tally.false_accepts.entry(key).or_insert(0);
                *n = n.saturating_add(1);
            }
            (_, Err(_)) => skip("unknown expectation"),
        }
    }
    let refusals: usize = tally.false_refusals.values().sum();
    let accepts: usize = tally.false_accepts.values().sum();
    println!(
        "limbo SERVER through verify_server_chain (accept-all links, depth 6): \
         agree {} SUCCESS + {} FAILURE; expected SUCCESS but refused {refusals}; \
         expected FAILURE but accepted {accepts}; skipped {:?}",
        tally.agree_success, tally.agree_failure, tally.skipped
    );
    for ((error, family), n) in &tally.false_refusals {
        println!("limbo refused (expected SUCCESS): {n}: {family}: {error}");
    }
    for ((family, features, importance), n) in &tally.false_accepts {
        println!("limbo accepted (expected FAILURE): {n}: {family} [{features}] ({importance})");
    }
    println!(
        "limbo cases naming several peers (first used): {}",
        tally.several_names
    );
}

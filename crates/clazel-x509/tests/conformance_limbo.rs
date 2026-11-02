//! x509-limbo conformance (docs/phases/phase-3.md item 3.5b).
//!
//! The corpus (C2SP/x509-limbo, Apache-2.0) is vendored in full under
//! `tests/data/x509-limbo/` and reduced by `cargo xtask testdata` to
//! `tests/generated/x509_limbo.rs`, the testcase index, and
//! `x509_limbo_certs.bin`, every distinct certificate as DER. This file:
//!
//! 1. Runs the decoders on every distinct certificate of the corpus
//!    (leaves, intermediates and trust anchors): envelope, TBS, SPKI,
//!    extensions, and the SAN, BasicConstraints, KeyUsage, ExtendedKeyUsage,
//!    NameConstraints and PolicyConstraints extension decoders, plus
//!    signature-algorithm classification. None may panic, and the number of
//!    certificates each stage accepts is pinned in `DECODE_COUNTS`, so a
//!    decoder change that moves it is noticed.
//! 2. Runs every `SERVER` testcase that names a DNS or IP peer through
//!    `path::search::exec::verify_server_chain` (RFC 5280 section 6.1 with
//!    the browser profile, over limbo's presented chain and trusted
//!    certificates, at limbo's validation time and with limbo's
//!    `max_chain_depth` as `max_intermediates`) and compares the verdict
//!    with limbo's `SUCCESS` or `FAILURE`.
//!    - **Signatures are not checked here.** The link verifier is a stand-in
//!      that accepts every signature: the real one (`CertificateLinks`) is in
//!      `clazel-crypto`, which depends on this crate. Limbo's `SUCCESS`
//!      chains have valid signatures, so the stand-in is exact for them; a
//!      `FAILURE` that rests on a signature is accepted here and is listed
//!      as such (`clazel-crypto/tests/chain_limbo.rs` pins those with the
//!      real links).
//!    - A `FAILURE` that this run refuses counts as agreeing whatever the
//!      reason (the error is not compared).
//! 3. Accounts for every testcase that disagrees or is not run (`CLIENT`
//!    cases, a `SERVER` case without a DNS or IP name) in
//!    `EXPECTED_FAILURES` (`tests/limbo/expected_failures.rs`), by id, with a
//!    reason. The test fails if a corpus id is neither agreeing nor listed,
//!    if a listed id is not in the corpus, if a listed testcase now agrees
//!    (remove it), or if a testcase that disagrees is not listed.
//! 4. Checks that no certificate of a `SUCCESS` testcase is rejected by a
//!    decoder.

use std::net::IpAddr;

use clazel_x509::{
    certificate::exec::{AlgorithmIdentifier, parse_certificate},
    constraints::exec::{parse_basic_constraints, parse_extended_key_usage, parse_key_usage},
    extensions::exec::{parse_extensions, parse_subject_alt_name},
    matcher::ReferenceIdentity,
    name_constraints::exec::parse_name_constraints,
    path::{
        contract::{LinkVerifier, RevocationOracle},
        exec::Environment,
        parsed::exec::{Anchor, PathCert, anchor_from_root, parse_path_cert},
        search::exec::verify_server_chain,
    },
    policy_constraints::exec::parse_policy_constraints,
    signature_algorithm::exec::classify,
    spki::exec::parse_subject_public_key_info,
    tbs::exec::parse_tbs_certificate,
    time::exec::CertificateTime,
};

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

// `EXPECTED_FAILURES`: (testcase id, reason), checked in by hand.
include!("limbo/expected_failures.rs");

static CERTS: &[u8] = include_bytes!("generated/x509_limbo_certs.bin");

fn cert(index: usize) -> Option<&'static [u8]> {
    let &(offset, length) = CERT_SPANS.get(index)?;
    let start = usize::try_from(offset).ok()?;
    let end = start.checked_add(usize::try_from(length).ok()?)?;
    CERTS.get(start..end)
}

/// `YYYY-MM-DDTHH:MM:SS+00:00` (all of limbo's times are UTC).
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
        // Fractional seconds (`...:00.005`) are truncated, as RFC 5280 time
        // has whole-second precision.
        second: c.next()?.split('.').next()?.parse().ok()?,
    };
    (d.next().is_none() && c.next().is_none()).then_some(time)
}

const SAN: &[u64] = &[2, 5, 29, 17];
const KEY_USAGE: &[u64] = &[2, 5, 29, 15];
const BASIC_CONSTRAINTS: &[u64] = &[2, 5, 29, 19];
const NAME_CONSTRAINTS: &[u64] = &[2, 5, 29, 30];
const EXTENDED_KEY_USAGE: &[u64] = &[2, 5, 29, 37];
const POLICY_CONSTRAINTS: &[u64] = &[2, 5, 29, 36];

/// For each decoder stage of `STAGES`, how many corpus certificates it applied
/// to and how many it accepted, as of this commit's decoders.
const DECODE_COUNTS: &[(usize, usize)] = &[
    (30379, 30379),
    (30379, 30379),
    (30379, 30375),
    (30375, 30374),
    (30374, 30373),
    (9098, 8545),
    (30158, 30158),
    (30369, 30368),
    (9818, 9817),
    (9458, 9453),
    (1, 1),
];

/// Decoder stages, in the order of `DECODE_COUNTS`. Each counts how many
/// certificates the stage was applicable to and how many it accepted.
const STAGES: &[&str] = &[
    "envelope",
    "signature algorithm classified",
    "tbs",
    "spki",
    "extensions",
    "subjectAltName",
    "basicConstraints",
    "keyUsage",
    "extKeyUsage",
    "nameConstraints",
    "policyConstraints",
];

/// Run every decoder on one certificate. Entry `i` is `None` when stage `i`
/// did not apply (an earlier stage failed or the extension is absent), and
/// otherwise whether it accepted.
fn decode(der: &[u8]) -> Vec<Option<bool>> {
    let mut out: Vec<Option<bool>> = vec![None; STAGES.len()];
    let mut set = |stage: usize, ok: bool| {
        if let Some(slot) = out.get_mut(stage) {
            *slot = Some(ok);
        }
    };
    let Some(envelope) = parse_certificate(der) else {
        set(0, false);
        return out;
    };
    set(0, true);
    set(1, classify(&envelope.signature_algorithm).is_some());
    let Some(tbs) = parse_tbs_certificate(envelope.tbs_certificate_der) else {
        set(2, false);
        return out;
    };
    set(2, true);
    set(
        3,
        parse_subject_public_key_info(tbs.subject_public_key_info_der).is_some(),
    );
    let Some(sequence) = tbs.extensions_sequence_der else {
        return out;
    };
    let Some(extensions) = parse_extensions(sequence) else {
        set(4, false);
        return out;
    };
    set(4, true);
    for e in &extensions {
        let oid = e.oid.as_slice();
        if oid == SAN {
            set(5, parse_subject_alt_name(e.value).is_some());
        } else if oid == BASIC_CONSTRAINTS {
            set(6, parse_basic_constraints(e.value).is_some());
        } else if oid == KEY_USAGE {
            set(7, parse_key_usage(e.value).is_some());
        } else if oid == EXTENDED_KEY_USAGE {
            set(8, parse_extended_key_usage(e.value).is_some());
        } else if oid == NAME_CONSTRAINTS {
            set(9, parse_name_constraints(e.value).is_some());
        } else if oid == POLICY_CONSTRAINTS {
            set(10, parse_policy_constraints(e.value).is_some());
        }
    }
    out
}

/// Accepts every signature: the stand-in for `clazel-crypto`'s real link
/// verifier (see the module docs).
struct AcceptAll;

impl LinkVerifier for AcceptAll {
    fn verify(&self, _: &[u8], _: &AlgorithmIdentifier<'_>, _: &[u8], _: &[u8]) -> bool {
        true
    }
}

/// Nothing is revoked (the production oracle; CRLs are Phase 8).
struct NotRevoked;

impl RevocationOracle for NotRevoked {
    fn is_revoked(&self, _: &PathCert<'_>) -> bool {
        false
    }
}

/// Production `max_intermediates`, used when the testcase gives no
/// `max_chain_depth`.
const DEFAULT_MAX_INTERMEDIATES: usize = 6;

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

/// What running a testcase gave.
enum Outcome {
    /// Our verdict is limbo's.
    Agrees,
    /// Our verdict is not limbo's: `accepted` is ours.
    Disagrees { accepted: bool },
    /// Not run, and why.
    NotRun(&'static str),
}

/// The testcase's validation time as Unix seconds. Limbo leaves the time out
/// of some testcases (`time` is empty): the leaf is then judged at its own
/// notBefore, which its validity includes. A leaf that does not decode gives
/// 0: the chain is refused whatever the time.
fn case_time(case: &Case) -> Option<u64> {
    if case.time.is_empty() {
        let decoded = cert(case.leaf)
            .and_then(parse_certificate)
            .and_then(|e| parse_tbs_certificate(e.tbs_certificate_der));
        return match decoded {
            Some(tbs) => unix_seconds(&tbs.not_before),
            None => Some(0),
        };
    }
    unix_seconds(&parse_time(case.time)?)
}

/// Run one testcase through `verify_server_chain`.
fn run(case: &Case) -> Outcome {
    if case.kind != "SERVER" {
        return Outcome::NotRun("not a SERVER testcase");
    }
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
            Err(_) => return Outcome::NotRun("peer address does not parse"),
        },
        _ => return Outcome::NotRun("no DNS or IP peer name"),
    };
    let Some(now) = case_time(case) else {
        return Outcome::NotRun("validation time does not parse");
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
        return Outcome::NotRun("certificate index out of range");
    };
    let environment = Environment {
        link: &AcceptAll,
        revoked: &NotRevoked,
        max_intermediates: case.max_chain_depth.map_or(DEFAULT_MAX_INTERMEDIATES, |d| {
            usize::try_from(d).unwrap_or(DEFAULT_MAX_INTERMEDIATES)
        }),
    };
    let accepted = verify_server_chain(&environment, &anchors, &presented, reference, now).is_ok();
    if accepted == (case.expected == "SUCCESS") {
        Outcome::Agrees
    } else {
        Outcome::Disagrees { accepted }
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn limbo_corpus_decodes_without_panic_and_pins_what_it_decides() {
    let mut problems: Vec<String> = Vec::new();

    // The index and the certificate file agree with each other.
    if CASES.len() != TESTCASE_COUNT {
        problems.push(format!(
            "{} cases, but the converter counted {TESTCASE_COUNT}",
            CASES.len()
        ));
    }
    for (i, _) in CERT_SPANS.iter().enumerate() {
        if cert(i).is_none() {
            problems.push(format!("certificate {i} lies outside the certificate file"));
        }
    }
    let used = |idx: usize| idx < CERT_SPANS.len();
    for c in CASES {
        let all = std::iter::once(&c.leaf)
            .chain(c.trusted)
            .chain(c.intermediates);
        if !all.copied().all(used) {
            problems.push(format!("{}: certificate index out of range", c.id));
        }
    }

    // 1. Every certificate through every decoder.
    let mut counts = vec![(0usize, 0usize); STAGES.len()];
    for i in 0..CERT_SPANS.len() {
        let Some(der) = cert(i) else { continue };
        for (slot, outcome) in counts.iter_mut().zip(decode(der)) {
            if let Some(ok) = outcome {
                slot.0 = slot.0.saturating_add(1);
                slot.1 = slot.1.saturating_add(usize::from(ok));
            }
        }
    }
    for (stage, (applicable, accepted)) in STAGES.iter().zip(&counts) {
        println!("limbo decode: {stage}: accepted {accepted} of {applicable}");
    }
    if counts.as_slice() != DECODE_COUNTS {
        problems.push(format!(
            "decode counts changed: now {counts:?}, pinned {DECODE_COUNTS:?}"
        ));
    }

    for c in CASES.iter().filter(|c| c.expected == "SUCCESS") {
        let all = std::iter::once(&c.leaf)
            .chain(c.trusted)
            .chain(c.intermediates);
        for &i in all {
            if cert(i).is_some_and(|der| decode(der).contains(&Some(false))) {
                problems.push(format!(
                    "{}: expects SUCCESS, but certificate {i} is rejected by a decoder",
                    c.id
                ));
            }
        }
    }
    // 2 and 3. The chain verdicts and the expected-failure list.
    let mut listed: std::collections::BTreeMap<&str, &str> = std::collections::BTreeMap::new();
    for (id, reason) in EXPECTED_FAILURES {
        if listed.insert(id, reason).is_some() {
            problems.push(format!("{id}: listed twice"));
        }
    }
    let mut seen = std::collections::BTreeSet::new();
    let (mut agreeing, mut listed_count, mut case_fail) = (0usize, 0usize, 0usize);
    for c in CASES {
        if !seen.insert(c.id) {
            problems.push(format!("{}: duplicate id in the corpus", c.id));
        }
        let is_listed = listed.contains_key(c.id);
        listed_count = listed_count.saturating_add(usize::from(is_listed));
        match run(c) {
            Outcome::Agrees if is_listed => problems.push(format!(
                "{}: listed as an expected failure, but verify_server_chain now agrees with limbo ({}): remove it from the list",
                c.id, c.expected
            )),
            Outcome::Agrees => agreeing = agreeing.saturating_add(1),
            Outcome::Disagrees { .. } | Outcome::NotRun(_) if is_listed => {}
            Outcome::Disagrees { accepted } => {
                case_fail = case_fail.saturating_add(1);
                problems.push(format!(
                    "{}: limbo expects {}, verify_server_chain {} it, and the testcase is not in EXPECTED_FAILURES",
                    c.id,
                    c.expected,
                    if accepted { "accepts" } else { "refuses" }
                ));
            }
            Outcome::NotRun(why) => {
                case_fail = case_fail.saturating_add(1);
                problems.push(format!(
                    "{}: not run ({why}) and not in EXPECTED_FAILURES",
                    c.id
                ));
            }
        }
    }
    for id in listed.keys() {
        if !seen.contains(id) {
            problems.push(format!("{id}: listed, but no longer in the corpus"));
        }
    }
    println!(
        "limbo: {} testcases, {agreeing} agree with verify_server_chain (accept-all links), {listed_count} expected failures",
        CASES.len()
    );
    // One unit per testcase: an agreeing verdict, a listed testcase (an
    // expected failure, with its reason in EXPECTED_FAILURES), or a
    // testcase that is neither (xtask/src/conformance.rs).
    println!(
        "clazel-conformance: suite=\"x509-limbo path validation (accept-all links)\" pass={agreeing} xfail={listed_count} fail={case_fail} total={}",
        CASES.len()
    );
    let reasons: std::collections::BTreeSet<&&str> = listed.values().collect();
    for r in reasons {
        let n = listed.values().filter(|v| *v == r).count();
        println!("limbo expected failures: {n}: {r}");
    }
    // The index's other fields have the shapes the converter promises.
    for c in CASES {
        let names_ok = c
            .peer_names
            .iter()
            .all(|(k, _)| matches!(*k, "DNS" | "IP" | "RFC822"));
        let known = matches!(c.importance, "undetermined" | "low" | "high" | "critical");
        // The profile always requires digitalSignature (if keyUsage is
        // present) and serverAuth for a server, so the only expectations a
        // testcase can state are these, and the profile meets them.
        let usage_ok = c.key_usage.iter().all(|k| *k == "digitalSignature")
            && c.extended_key_usage.iter().all(|e| {
                *e == if c.kind == "SERVER" {
                    "serverAuth"
                } else {
                    "clientAuth"
                }
            });
        if !usage_ok || c.max_chain_depth.is_some_and(|d| d > 255) {
            problems.push(format!("{}: unexpected usage or depth expectation", c.id));
        }
        if !names_ok || !known || c.features.iter().any(|f| f.is_empty()) {
            problems.push(format!("{}: unexpected index fields", c.id));
        }
    }
    problems.truncate(40);
    assert!(problems.is_empty(), "limbo: {}", problems.join("\n"));
}

/// How many corpus certificates `parse_path_cert` accepts, of how many.
/// Every distinct certificate of the corpus (30,379) is offered to it. The
/// 566 it refuses are 553 whose subjectAltName does not decode, 5 whose
/// nameConstraints, 4 whose TBS, and one each whose Extensions, keyUsage,
/// extKeyUsage or signature-algorithm pairing does not; no new rule refuses any.
const PATH_CERT_COUNTS: (usize, usize) = (29813, 30379);

/// How many certificates that some testcase lists as a trust anchor
/// `anchor_from_root` (with no distrust-after) turns into an `Anchor`, of
/// how many such certificates there are. The 10 it refuses: four with a
/// critical extension it does not read (limbo's canary OID twice, a critical
/// AKI, a critical SKI), two whose nameConstraints, one whose keyUsage and
/// one whose TBS does not decode, one with an empty subject and one without
/// basicConstraints.
const ANCHOR_COUNTS: (usize, usize) = (218, 228);

#[test]
#[cfg_attr(miri, ignore)]
fn limbo_corpus_path_cert_and_anchor_counts_are_pinned() {
    let mut parsed = 0usize;
    let mut total = 0usize;
    // The certificates that parse to a `PathCert`, by what the first decoder
    // to refuse the others was.
    let mut refused_by: std::collections::BTreeMap<&str, usize> = std::collections::BTreeMap::new();
    for i in 0..CERT_SPANS.len() {
        let Some(der) = cert(i) else { continue };
        total = total.saturating_add(1);
        if parse_path_cert(der).is_some() {
            parsed = parsed.saturating_add(1);
            continue;
        }
        let outcome = decode(der);
        let stage = outcome
            .iter()
            .position(|o| *o == Some(false))
            .and_then(|k| STAGES.get(k))
            .copied()
            .unwrap_or("signature algorithms disagree");
        let slot = refused_by.entry(stage).or_insert(0);
        *slot = slot.saturating_add(1);
    }
    println!("limbo path certs: parsed {parsed} of {total}; refused by {refused_by:?}");

    let mut anchors = std::collections::BTreeSet::new();
    for c in CASES {
        anchors.extend(c.trusted.iter().copied());
    }
    let mut made = 0usize;
    for &i in &anchors {
        if cert(i).is_some_and(|der| anchor_from_root(der, None).is_some()) {
            made = made.saturating_add(1);
        }
    }
    println!("limbo anchors: {made} of {}", anchors.len());

    assert_eq!((parsed, total), PATH_CERT_COUNTS, "parse_path_cert counts");
    assert_eq!(
        (made, anchors.len()),
        ANCHOR_COUNTS,
        "anchor_from_root counts"
    );
}

//! x509-limbo conformance (docs/phases/phase-3.md item 3.5b), as far as
//! clazel-x509 goes today.
//!
//! clazel-x509 has no path validation yet, so limbo's chain verdicts are not
//! run. What this file does with the corpus (C2SP/x509-limbo, Apache-2.0,
//! vendored in full under `tests/data/x509-limbo/` and reduced by
//! `cargo xtask testdata` to `tests/generated/x509_limbo.rs`, the testcase
//! index, and `x509_limbo_certs.bin`, every distinct certificate as DER):
//!
//! 1. Runs the decoders on every distinct certificate of the corpus
//!    (leaves, intermediates and trust anchors): envelope, TBS, SPKI,
//!    extensions, and the SAN, BasicConstraints, KeyUsage, ExtendedKeyUsage
//!    and NameConstraints extension decoders, plus signature-algorithm
//!    classification. None may panic, and the number of certificates each
//!    stage accepts is pinned in `DECODE_COUNTS`, so a decoder change that
//!    moves it is noticed.
//! 2. Pins the one outcome limbo's expectations decide for a decoder: a
//!    `SERVER` testcase that expects `SUCCESS` for a DNS or IP peer name has
//!    a leaf that `check_leaf_certificate` (envelope, TBS, extensions, the
//!    RFC 9525 SAN match, validity at the testcase's time, EKU, key usage
//!    and BasicConstraints leaf role) accepts for that name at that time.
//! 3. Accounts for every other testcase in `NOT_YET_SUPPORTED`
//!    (`tests/limbo/not_yet_supported.rs`), by id, with a reason. The test
//!    fails if a corpus id is neither pinned nor listed, if a listed id is not
//!    in the corpus, if a listed testcase now passes its pin, or if a pinned
//!    testcase fails and is not listed. The list shrinks as path validation
//!    lands; limbo's `FAILURE` verdicts cannot be pinned before then, since
//!    most rest on chain building, trust, policy or CRLs, not on one decoder.

use std::net::IpAddr;

use clazel_x509::{
    certificate::exec::parse_certificate,
    constraints::exec::{parse_basic_constraints, parse_extended_key_usage, parse_key_usage},
    extensions::exec::{parse_extensions, parse_subject_alt_name},
    leaf::exec::{LeafPolicy, check_leaf_certificate},
    matcher::ReferenceIdentity,
    name_constraints::exec::parse_name_constraints,
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
    trusted: &'static [usize],
    intermediates: &'static [usize],
    leaf: usize,
}

// `TESTCASE_COUNT`, `CERT_SPANS` and `CASES`, generated from the vendored file.
include!("generated/x509_limbo.rs");

// `NOT_YET_SUPPORTED`: (testcase id, reason), checked in by hand.
include!("limbo/not_yet_supported.rs");

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
        }
    }
    out
}

/// What the pin says about a testcase.
enum Pin {
    /// Limbo's expectations decide nothing for the decoders.
    None,
    /// The leaf must be accepted for this peer at this time.
    Accept,
}

fn pin_of(case: &Case) -> Pin {
    let named = matches!(case.peer.0, "DNS" | "IP");
    if case.kind == "SERVER" && case.expected == "SUCCESS" && named {
        Pin::Accept
    } else {
        Pin::None
    }
}

/// Whether `check_leaf_certificate` accepts the testcase's leaf for its peer
/// name at its validation time. `None` when the testcase gives no usable
/// name, or a time that does not parse.
fn leaf_accepted(case: &Case) -> Option<bool> {
    let der = cert(case.leaf)?;
    // Limbo leaves the time out of some testcases (`time` is empty); the leaf
    // is then checked at its own notBefore, which its validity includes.
    let now = if case.time.is_empty() {
        let envelope = parse_certificate(der)?;
        parse_tbs_certificate(envelope.tbs_certificate_der)?.not_before
    } else {
        parse_time(case.time)?
    };
    let policy = LeafPolicy {
        allow_any_extended_key_usage: false,
    };
    let accepted = |reference: ReferenceIdentity<'_>| {
        check_leaf_certificate(der, reference, &now, policy)
            .is_some_and(|r| r.identity_matched && r.valid_at_captured_time)
    };
    Some(match case.peer {
        ("DNS", name) => accepted(ReferenceIdentity::Dns(name.as_bytes())),
        ("IP", text) => match text.parse::<IpAddr>().ok()? {
            IpAddr::V4(a) => accepted(ReferenceIdentity::Ip(&a.octets())),
            IpAddr::V6(a) => accepted(ReferenceIdentity::Ip(&a.octets())),
        },
        _ => return None,
    })
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
    // 2 and 3. Pins and the not-yet-supported list.
    let mut listed: std::collections::BTreeMap<&str, &str> = std::collections::BTreeMap::new();
    for (id, reason) in NOT_YET_SUPPORTED {
        if listed.insert(id, reason).is_some() {
            problems.push(format!("{id}: listed twice"));
        }
    }
    let mut seen = std::collections::BTreeSet::new();
    let (mut pinned_pass, mut listed_count, mut case_fail) = (0usize, 0usize, 0usize);
    for c in CASES {
        if !seen.insert(c.id) {
            problems.push(format!("{}: duplicate id in the corpus", c.id));
        }
        let is_listed = listed.contains_key(c.id);
        listed_count = listed_count.saturating_add(usize::from(is_listed));
        match pin_of(c) {
            Pin::None if !is_listed => {
                case_fail = case_fail.saturating_add(1);
                problems.push(format!(
                    "{}: new testcase: neither pinned nor in NOT_YET_SUPPORTED",
                    c.id
                ));
            }
            Pin::None => {}
            Pin::Accept => match leaf_accepted(c) {
                Some(true) if is_listed => {
                    // Counted below as listed; the stale entry fails the run.
                    problems.push(format!(
                        "{}: listed as not yet supported, but its pin now passes: remove it from the list",
                        c.id
                    ));
                }
                Some(true) => pinned_pass = pinned_pass.saturating_add(1),
                Some(false) | None if is_listed => {}
                Some(false) | None => {
                    case_fail = case_fail.saturating_add(1);
                    problems.push(format!(
                        "{}: limbo expects SUCCESS for {:?} at {}, but the leaf is rejected",
                        c.id, c.peer, c.time
                    ));
                }
            },
        }
    }
    for id in listed.keys() {
        if !seen.contains(id) {
            problems.push(format!("{id}: listed, but no longer in the corpus"));
        }
    }
    println!(
        "limbo: {} testcases, {pinned_pass} pinned and passing, {listed_count} not yet supported",
        CASES.len()
    );
    // One unit per testcase: a pin that passes, a listed testcase (an
    // expected failure, with its reason in NOT_YET_SUPPORTED), or a
    // testcase that is neither (xtask/src/conformance.rs).
    println!(
        "clazel-conformance: suite=\"x509-limbo leaf checks\" pass={pinned_pass} xfail={listed_count} fail={case_fail} total={}",
        CASES.len()
    );
    let reasons: std::collections::BTreeSet<&&str> = listed.values().collect();
    for r in reasons {
        let n = listed.values().filter(|v| *v == r).count();
        println!("limbo not yet supported: {n}: {r}");
    }
    // The index's other fields have the shapes the converter promises.
    for c in CASES {
        let names_ok = c
            .peer_names
            .iter()
            .all(|(k, _)| matches!(*k, "DNS" | "IP" | "RFC822"));
        let known = matches!(c.importance, "undetermined" | "low" | "high" | "critical");
        if !names_ok || !known || c.features.iter().any(|f| f.is_empty()) {
            problems.push(format!("{}: unexpected index fields", c.id));
        }
    }
    problems.truncate(40);
    assert!(problems.is_empty(), "limbo: {}", problems.join("\n"));
}

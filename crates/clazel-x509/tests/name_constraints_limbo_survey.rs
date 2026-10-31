//! A survey, not a pin: the executable name-constraint matcher
//! (`name_constraints::matching::exec`) against x509-limbo's name-constraint
//! testcases, to see how far its verdicts agree with limbo's expectations
//! before path validation (P9, P12) exists. Nothing here fixes a verdict;
//! `NOT_YET_SUPPORTED` in `conformance_limbo.rs` is unchanged, and pinning
//! is piece P12. Run it with
//!
//! ```text
//! cargo test -p clazel-x509 --test name_constraints_limbo_survey -- --nocapture
//! ```
//!
//! Path building is piece P9, so the chain is the testcase's own: the
//! intermediates are ordered by following issuer to subject from the leaf up
//! (limbo gives them as an unordered pool), the chain is `intermediates in
//! that order, then the leaf`, and the state starts with the trust anchor's
//! NameConstraints if it has one. The verdict is "the matcher accepts the
//! chain". Limbo's `expected_result` also depends on the hostname, the
//! leaf's own extensions (piece P7), and everything else path validation
//! checks, so a disagreement is classified:
//!
//! - `hostname`: limbo expects FAILURE, the matcher accepts, and the leaf is
//!   not valid for the testcase's peer name (so limbo's FAILURE has that cause);
//! - `P7`: limbo expects FAILURE, the matcher accepts, and the final
//!   certificate carries its own NameConstraints extension, which this module
//!   never processes (RFC 5280 §6.1.4 applies to certificates below the
//!   last); refusing it is P7's job;
//! - `listed divergence`: `rfc5280::nc::permitted-self-issued`, where the
//!   spec follows Firefox and checks self-issued intermediates;
//! - `decoder`: a certificate's SubjectAltName or NameConstraints does not
//!   decode, so the chain is refused before matching;
//! - `MISMATCH`: anything else, a real difference between the matcher (or
//!   the spec) and limbo.

use std::collections::BTreeMap;

use clazel_x509::{
    certificate::exec::parse_certificate,
    extensions::exec::{GeneralName, parse_extensions, parse_subject_alt_name},
    leaf::exec::{LeafPolicy, check_leaf_certificate},
    matcher::ReferenceIdentity,
    name_constraints::exec::{NameConstraints, parse_name_constraints},
    name_constraints::matching::exec::{
        NcCertificate, names_constrained, prepare_name_constraints,
    },
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

static CERTS: &[u8] = include_bytes!("generated/x509_limbo_certs.bin");

const SAN: &[u64] = &[2, 5, 29, 17];
const NAME_CONSTRAINTS: &[u64] = &[2, 5, 29, 30];
const SUBJECT_KEY_IDENTIFIER: &[u64] = &[2, 5, 29, 14];
const AUTHORITY_KEY_IDENTIFIER: &[u64] = &[2, 5, 29, 35];

fn cert(index: usize) -> Option<&'static [u8]> {
    let &(offset, length) = CERT_SPANS.get(index)?;
    let start = usize::try_from(offset).ok()?;
    let end = start.checked_add(usize::try_from(length).ok()?)?;
    CERTS.get(start..end)
}

/// What the matcher needs from one certificate.
struct Parts {
    subject: &'static [u8],
    issuer: &'static [u8],
    names: Vec<GeneralName<'static>>,
    name_constraints: Option<NameConstraints<'static>>,
    /// The extension is present (decoded or not).
    has_name_constraints: bool,
    /// The extension is present and not marked critical (RFC 5280 §4.2.1.10
    /// says it MUST be critical; that check is piece P7's).
    name_constraints_not_critical: bool,
    /// subjectKeyIdentifier's key identifier, if present.
    subject_key_id: Option<&'static [u8]>,
    /// authorityKeyIdentifier's key identifier, if present.
    authority_key_id: Option<&'static [u8]>,
}

/// The contents of a short-form TLV with tag `tag` filling `bytes` exactly.
fn short_tlv(bytes: &'static [u8], tag: u8) -> Option<&'static [u8]> {
    let (&first, rest) = bytes.split_first()?;
    let (&length, content) = rest.split_first()?;
    (first == tag && length < 0x80 && usize::from(length) == content.len()).then_some(content)
}

/// The key identifier of an authorityKeyIdentifier value, `[0] keyIdentifier`
/// being its first field: `SEQUENCE { [0] OCTET STRING ... }`.
fn authority_key_identifier(value: &'static [u8]) -> Option<&'static [u8]> {
    let body = short_tlv(value, 0x30)?;
    let (&tag, rest) = body.split_first()?;
    let (&length, content) = rest.split_first()?;
    if tag != 0x80 || length >= 0x80 {
        return None;
    }
    content.get(..usize::from(length))
}

/// `Err` says why the certificate could not be read.
fn parts(index: usize) -> Result<Parts, String> {
    let der = cert(index).ok_or("certificate out of range")?;
    let envelope = parse_certificate(der).ok_or("certificate does not decode")?;
    let tbs = parse_tbs_certificate(envelope.tbs_certificate_der).ok_or("TBS does not decode")?;
    let mut parts = Parts {
        subject: tbs.subject_der,
        issuer: tbs.issuer_der,
        names: Vec::new(),
        name_constraints: None,
        has_name_constraints: false,
        name_constraints_not_critical: false,
        subject_key_id: None,
        authority_key_id: None,
    };
    let Some(sequence) = tbs.extensions_sequence_der else {
        return Ok(parts);
    };
    let extensions = parse_extensions(sequence).ok_or("extensions do not decode")?;
    for extension in extensions {
        if extension.oid.as_slice() == SAN {
            parts.names = parse_subject_alt_name(extension.value)
                .ok_or("subjectAltName does not decode")?
                .names;
        } else if extension.oid.as_slice() == SUBJECT_KEY_IDENTIFIER {
            parts.subject_key_id = short_tlv(extension.value, 0x04);
        } else if extension.oid.as_slice() == AUTHORITY_KEY_IDENTIFIER {
            parts.authority_key_id = authority_key_identifier(extension.value);
        } else if extension.oid.as_slice() == NAME_CONSTRAINTS {
            parts.has_name_constraints = true;
            parts.name_constraints_not_critical = !extension.critical;
            parts.name_constraints = Some(
                parse_name_constraints(extension.value).ok_or("nameConstraints does not decode")?,
            );
        }
    }
    Ok(parts)
}

/// The verdict of the matcher on one testcase.
struct Verdict {
    accepted: bool,
    /// The final certificate has a NameConstraints extension.
    leaf_has_name_constraints: bool,
    /// Some certificate of the (first) candidate chain, or its anchor, has a
    /// NameConstraints extension that is not critical.
    non_critical_name_constraints: bool,
    /// The first candidate chain is not the pool in the order given.
    reordered: bool,
    /// How many candidate chains the pool offers.
    candidates: usize,
    /// The pool certificates that are on no candidate chain.
    unused: usize,
}

/// Every chain of pool certificates from the leaf up to a trust anchor, by
/// following issuer to subject (path building proper is piece P9): the
/// pool positions in leaf-first order, and the anchor's position.
fn candidate_chains(
    pool: &[(usize, Parts)],
    anchors: &[(usize, Parts)],
    chain: &mut Vec<usize>,
    issuer: &[u8],
    wanted_key: Option<&[u8]>,
    found: &mut Vec<(Vec<usize>, Option<usize>)>,
) {
    // The issuer's name matches, and so does its key identifier when both
    // the child names one and the issuer has one (a stand-in for the
    // signature check that path building will do).
    let issues = |candidate: &Parts| {
        candidate.subject == issuer
            && match (wanted_key, candidate.subject_key_id) {
                (Some(wanted), Some(have)) => wanted == have,
                _ => true,
            }
    };
    let mut anchored = false;
    for (position, (_, anchor)) in anchors.iter().enumerate() {
        if issues(anchor) {
            found.push((chain.clone(), Some(position)));
            anchored = true;
        }
    }
    if anchored || chain.len() >= 16 {
        return;
    }
    for (position, (_, candidate)) in pool.iter().enumerate() {
        if issues(candidate) && !chain.contains(&position) {
            chain.push(position);
            candidate_chains(
                pool,
                anchors,
                chain,
                candidate.issuer,
                candidate.authority_key_id,
                found,
            );
            chain.pop();
        }
    }
}

fn survey(case: &Case) -> Result<Verdict, String> {
    let leaf = parts(case.leaf)?;
    let mut pool: Vec<(usize, Parts)> = Vec::new();
    for &index in case.intermediates {
        pool.push((index, parts(index)?));
    }
    let mut anchors: Vec<(usize, Parts)> = Vec::new();
    for &index in case.trusted {
        anchors.push((index, parts(index)?));
    }
    let mut found: Vec<(Vec<usize>, Option<usize>)> = Vec::new();
    candidate_chains(
        &pool,
        &anchors,
        &mut Vec::new(),
        leaf.issuer,
        leaf.authority_key_id,
        &mut found,
    );
    if found.is_empty() {
        // No chain reaches an anchor: judge the pool as it was given.
        found.push(((0..pool.len()).collect(), None));
    }
    let mut used = vec![false; pool.len()];
    let mut accepted = false;
    let mut first: Option<(Vec<usize>, bool)> = None;
    for (chain, anchor) in &found {
        for &position in chain {
            if let Some(slot) = used.get_mut(position) {
                *slot = true;
            }
        }
        // Leaf first in `chain`; the path is the other way round, then the leaf.
        let mut path_parts: Vec<&Parts> = chain
            .iter()
            .rev()
            .filter_map(|&position| pool.get(position).map(|(_, p)| p))
            .collect();
        let anchor_parts = anchor
            .and_then(|position| anchors.get(position))
            .map(|(_, p)| p);
        let non_critical = path_parts.iter().any(|p| p.name_constraints_not_critical)
            || anchor_parts.is_some_and(|p| p.name_constraints_not_critical);
        path_parts.push(&leaf);
        let path: Vec<NcCertificate<'_>> = path_parts
            .iter()
            .map(|p| NcCertificate {
                subject: p.subject,
                subject_alt_names: &p.names,
                name_constraints: p.name_constraints.as_ref(),
            })
            .collect();
        let mut state: Vec<&NameConstraints<'_>> = Vec::new();
        let anchor_constraints = anchor_parts.and_then(|p| p.name_constraints.as_ref());
        let anchor_ok = prepare_name_constraints(&mut state, anchor_constraints);
        accepted = accepted || (anchor_ok && names_constrained(&path, state));
        if first.is_none() {
            let order: Vec<usize> = chain
                .iter()
                .rev()
                .filter_map(|&position| pool.get(position).map(|(index, _)| *index))
                .collect();
            first = Some((order, non_critical));
        }
    }
    let (order, non_critical_name_constraints) = first.unwrap_or_default();
    Ok(Verdict {
        accepted,
        leaf_has_name_constraints: leaf.has_name_constraints,
        non_critical_name_constraints,
        reordered: order != case.intermediates,
        candidates: found.len(),
        unused: used.iter().filter(|u| !**u).count(),
    })
}

/// `YYYY-MM-DDTHH:MM:SS+00:00`.
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

/// Whether the leaf is valid for the testcase's peer name (so a limbo
/// FAILURE need not be about name constraints). `None` if unknown.
fn hostname_ok(case: &Case) -> Option<bool> {
    let der = cert(case.leaf)?;
    let now = if case.time.is_empty() {
        let envelope = parse_certificate(der)?;
        parse_tbs_certificate(envelope.tbs_certificate_der)?.not_before
    } else {
        parse_time(case.time)?
    };
    let policy = LeafPolicy {
        allow_any_extended_key_usage: false,
    };
    let matched = |reference: ReferenceIdentity<'_>| {
        check_leaf_certificate(der, reference, &now, policy).is_some_and(|r| r.identity_matched)
    };
    match case.peer {
        ("DNS", name) => Some(matched(ReferenceIdentity::Dns(name.as_bytes()))),
        ("IP", text) => match text.parse::<std::net::IpAddr>().ok()? {
            std::net::IpAddr::V4(a) => Some(matched(ReferenceIdentity::Ip(&a.octets()))),
            std::net::IpAddr::V6(a) => Some(matched(ReferenceIdentity::Ip(&a.octets()))),
        },
        _ => None,
    }
}

fn is_name_constraint_case(id: &str) -> bool {
    id.starts_with("bettertls::nameconstraints::")
        || id.starts_with("rfc5280::nc::")
        || id.starts_with("webpki::nc::")
        || id.starts_with("cve::")
        || id.starts_with("pathological::nc-dos-")
}

fn group_of(id: &str) -> &'static str {
    if id.starts_with("bettertls::nameconstraints::") {
        "bettertls::nameconstraints"
    } else if id.starts_with("rfc5280::nc::") {
        "rfc5280::nc"
    } else if id.starts_with("webpki::nc::") {
        "webpki::nc"
    } else if id.starts_with("cve::") {
        "cve"
    } else {
        "pathological::nc-dos"
    }
}

#[derive(Default)]
struct Tally {
    total: usize,
    agree: usize,
    disagree: usize,
}

#[test]
#[cfg_attr(miri, ignore)]
fn survey_name_constraint_testcases() {
    let mut groups: BTreeMap<&str, Tally> = BTreeMap::new();
    let mut classes: BTreeMap<&str, usize> = BTreeMap::new();
    let mut disagreements: Vec<String> = Vec::new();
    let (mut reordered, mut unused, mut unreadable, mut ambiguous) =
        (0usize, 0usize, 0usize, 0usize);
    // limbo's expected verdict against "the matcher accepts and the leaf is
    // valid for the peer name": the closest this survey comes to the whole
    // verdict.
    let mut combined_agree = 0usize;
    let mut combined_misses: Vec<String> = Vec::new();
    let mut ran = 0usize;
    for case in CASES.iter().filter(|c| is_name_constraint_case(c.id)) {
        ran = ran.saturating_add(1);
        let tally = groups.entry(group_of(case.id)).or_default();
        tally.total = tally.total.saturating_add(1);
        let expect_success = case.expected == "SUCCESS";
        let verdict = survey(case);
        let (accepted, note) = match &verdict {
            Ok(v) => {
                reordered = reordered.saturating_add(usize::from(v.reordered));
                unused = unused.saturating_add(v.unused);
                ambiguous = ambiguous.saturating_add(usize::from(v.candidates > 1));
                (v.accepted, None)
            }
            Err(why) => {
                unreadable = unreadable.saturating_add(1);
                (false, Some(why.clone()))
            }
        };
        let combined = accepted && hostname_ok(case) == Some(true);
        combined_agree = combined_agree.saturating_add(usize::from(combined == expect_success));
        if combined != expect_success {
            combined_misses.push(format!(
                "{}: limbo {}, matcher {}, leaf valid for the peer name: {:?}",
                case.id,
                case.expected,
                if accepted { "accepts" } else { "refuses" },
                hostname_ok(case)
            ));
        }
        if accepted == expect_success {
            tally.agree = tally.agree.saturating_add(1);
            continue;
        }
        tally.disagree = tally.disagree.saturating_add(1);
        let (kind, detail): (&'static str, String) = if let Some(why) = &note {
            ("decoder", why.clone())
        } else if case.id == "rfc5280::nc::permitted-self-issued" {
            ("listed divergence", String::new())
        } else if !accepted {
            ("MISMATCH (refused, limbo expects SUCCESS)", String::new())
        } else if verdict
            .as_ref()
            .is_ok_and(|v| v.leaf_has_name_constraints || v.non_critical_name_constraints)
        {
            ("P7", String::new())
        } else if hostname_ok(case) == Some(false) {
            ("hostname", String::new())
        } else {
            ("MISMATCH (accepted, limbo expects FAILURE)", String::new())
        };
        let count = classes.entry(kind).or_default();
        *count = count.saturating_add(1);
        let class = if detail.is_empty() {
            kind.to_owned()
        } else {
            format!("{kind} ({detail})")
        };
        disagreements.push(format!(
            "{}: limbo {}, matcher {}: {class}",
            case.id,
            case.expected,
            if accepted { "accepts" } else { "refuses" }
        ));
    }
    println!("name-constraint survey (not a pin):");
    for case in CASES
        .iter()
        .filter(|c| c.id.starts_with("pathological::nc-dos-"))
    {
        let describe = |index: usize| match parts(index) {
            Ok(p) => {
                let subtrees = p.name_constraints.as_ref().map_or(0, |nc| {
                    nc.permitted_subtrees.as_ref().map_or(0, Vec::len)
                        + nc.excluded_subtrees.as_ref().map_or(0, Vec::len)
                });
                format!("{} SAN entries, {} subtrees", p.names.len(), subtrees)
            }
            Err(why) => why,
        };
        let chain: Vec<String> = case
            .intermediates
            .iter()
            .chain(std::iter::once(&case.leaf))
            .map(|&i| describe(i))
            .collect();
        let anchors: Vec<String> = case.trusted.iter().map(|&i| describe(i)).collect();
        println!(
            "  {}: anchor [{}], chain [{}]",
            case.id,
            anchors.join("; "),
            chain.join("; ")
        );
    }
    let (mut total, mut agree) = (0usize, 0usize);
    for (group, t) in &groups {
        println!(
            "  {group}: total {}, agree {}, disagree {}",
            t.total, t.agree, t.disagree
        );
        total = total.saturating_add(t.total);
        agree = agree.saturating_add(t.agree);
    }
    println!(
        "  all: total {total}, agree {agree}, disagree {}",
        total.saturating_sub(agree)
    );
    println!(
        "  chain order: {reordered} chains reordered from the pool order, {ambiguous} testcases with several candidate chains, {unused} pool certificates on no candidate chain, {unreadable} testcases with an unreadable certificate"
    );
    println!(
        "  matcher accepts and leaf valid for the peer name, against limbo's verdict: agree {combined_agree} of {total}"
    );
    for line in &combined_misses {
        println!("  combined disagreement: {line}");
    }
    for (class, count) in &classes {
        println!("  disagreements classified {class}: {count}");
    }
    for line in disagreements.iter().take(10) {
        println!("  first disagreements: {line}");
    }
    // Beyond the first ten, only those that are not plain hostname cases.
    for line in disagreements
        .iter()
        .skip(10)
        .filter(|l| !l.ends_with(": hostname"))
    {
        println!("  further disagreement: {line}");
    }
    let selected = || CASES.iter().filter(|c| is_name_constraint_case(c.id));
    println!(
        "  selected testcases: {} SERVER, {} with several peer names, {} with features, {} of importance 'undetermined'",
        selected().filter(|c| c.kind == "SERVER").count(),
        selected().filter(|c| !c.peer_names.is_empty()).count(),
        selected().filter(|c| !c.features.is_empty()).count(),
        selected()
            .filter(|c| c.importance == "undetermined")
            .count(),
    );
    // Only that the survey ran everything it should: no verdict is pinned.
    assert_eq!(CASES.len(), TESTCASE_COUNT);
    assert_eq!(ran, groups.values().map(|t| t.total).sum::<usize>());
    assert!(
        groups
            .get("bettertls::nameconstraints")
            .is_some_and(|t| t.total == 9491)
    );
}

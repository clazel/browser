//! Known answers for the chain-building search (`path::search::exec`,
//! design `path-validation.md` §2.6), which Verus proves equal to
//! `path/search/spec.rs`. The tests check the proven code runs as the spec
//! reads, on DER chains built by hand, and measure the signature work of
//! hostile chain shapes (design §1.12's open P9 question).
//!
//! Signatures are stand-ins: each built certificate's signature bits are
//! one byte repeated, the byte of the key it claims to be signed with, and
//! `KeyedLink` accepts a link exactly when that byte is the issuer key's
//! (the last byte of the issuer's SubjectPublicKeyInfo). A certificate
//! "signed" with the wrong key fails, as a forged one would.

use std::cell::{Cell, RefCell};
use std::collections::HashSet;

use clazel_x509::certificate::exec::AlgorithmIdentifier;
use clazel_x509::matcher::ReferenceIdentity;
use clazel_x509::path::contract::{LinkVerifier, RevocationOracle};
use clazel_x509::path::exec::Environment;
use clazel_x509::path::parsed::exec::{Anchor, PathCert, anchor_from_root, parse_path_cert};
use clazel_x509::path::search::exec::{Validated, search, verify_server_chain};
use clazel_x509::path::spec::PathError;
use clazel_x509::time::exec::CertificateTime;

// ---------------------------------------------------------------------------
// Test doubles
// ---------------------------------------------------------------------------

/// Accepts a link when the signature's last byte is the issuer key's.
struct KeyedLink;

impl LinkVerifier for KeyedLink {
    fn verify(
        &self,
        issuer_spki: &[u8],
        _: &AlgorithmIdentifier<'_>,
        _: &[u8],
        signature: &[u8],
    ) -> bool {
        matches!((issuer_spki.last(), signature.last()), (Some(k), Some(s)) if k == s)
    }
}

/// `KeyedLink`, counting the calls and the distinct (issuer key, TBS) pairs
/// verified: the second is what a per-link cache would verify.
#[derive(Default)]
struct CountingLink {
    calls: Cell<u64>,
    distinct: RefCell<HashSet<(Vec<u8>, Vec<u8>)>>,
}

impl LinkVerifier for CountingLink {
    fn verify(
        &self,
        issuer_spki: &[u8],
        algorithm: &AlgorithmIdentifier<'_>,
        tbs: &[u8],
        signature: &[u8],
    ) -> bool {
        self.calls.set(self.calls.get().saturating_add(1));
        self.distinct
            .borrow_mut()
            .insert((issuer_spki.to_vec(), tbs.to_vec()));
        KeyedLink.verify(issuer_spki, algorithm, tbs, signature)
    }
}

/// Nothing is revoked (the production oracle).
struct NotRevoked;

impl RevocationOracle for NotRevoked {
    fn is_revoked(&self, _: &PathCert<'_>) -> bool {
        false
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
const KU_KEY_CERT_SIGN: &[u8] = &[0x03, 0x02, 0x02, 0x04];
const KU_DIGITAL_SIGNATURE: &[u8] = &[0x03, 0x02, 0x07, 0x80];
const EKU_SERVER_AUTH: &[u8] = &[
    0x30, 0x0A, 0x06, 0x08, 0x2B, 0x06, 0x01, 0x05, 0x05, 0x07, 0x03, 0x01,
];

fn ext(oid: &[u8], critical: bool, value: &[u8]) -> Vec<u8> {
    let mut body = tlv(0x06, oid);
    if critical {
        body.extend_from_slice(&[0x01, 0x01, 0xFF]);
    }
    body.extend_from_slice(&tlv(0x04, value));
    tlv(0x30, &body)
}

/// A certificate `issuer -> subject` with key byte `key`, signed with key
/// byte `signer`; `serial` (two bytes) makes its DER distinct.
fn cert(
    serial: u16,
    issuer: &str,
    subject: &str,
    key: u8,
    signer: u8,
    extensions: &[Vec<u8>],
) -> Vec<u8> {
    let spki = tlv(
        0x30,
        &[
            &[
                0x30, 0x13, 0x06, 0x07, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01, 0x06, 0x08, 0x2A,
                0x86, 0x48, 0xCE, 0x3D, 0x03, 0x01, 0x07,
            ][..],
            &tlv(0x03, &[&[0x00, 0x04][..], &[key; 64]].concat()),
        ]
        .concat(),
    );
    let validity = tlv(
        0x30,
        &[tlv(0x17, b"200101000000Z"), tlv(0x17, b"400101000000Z")].concat(),
    );
    let [s1, s2] = serial.to_be_bytes();
    let mut tbs = vec![0xA0, 0x03, 0x02, 0x01, 0x02, 0x02, 0x03, 0x01, s1, s2];
    tbs.extend_from_slice(ECDSA_SHA256);
    tbs.extend_from_slice(&name(issuer));
    tbs.extend_from_slice(&validity);
    tbs.extend_from_slice(&name(subject));
    tbs.extend_from_slice(&spki);
    if !extensions.is_empty() {
        tbs.extend_from_slice(&tlv(0xA3, &tlv(0x30, &extensions.concat())));
    }
    let mut body = tlv(0x30, &tbs);
    body.extend_from_slice(ECDSA_SHA256);
    body.extend_from_slice(&tlv(0x03, &[&[0x00][..], &[signer; 8]].concat()));
    tlv(0x30, &body)
}

/// A CA certificate.
fn ca(serial: u16, issuer: &str, subject: &str, key: u8, signer: u8) -> Vec<u8> {
    let extensions = [
        ext(BASIC_CONSTRAINTS, true, &tlv(0x30, &[0x01, 0x01, 0xFF])),
        ext(KEY_USAGE, true, KU_KEY_CERT_SIGN),
    ];
    cert(serial, issuer, subject, key, signer, &extensions)
}

/// A leaf for `example.com`, with key byte 9.
fn leaf(issuer: &str, signer: u8) -> Vec<u8> {
    let san = tlv(0x30, &tlv(0x82, b"example.com"));
    let extensions = [
        ext(SUBJECT_ALT_NAME, false, &san),
        ext(KEY_USAGE, true, KU_DIGITAL_SIGNATURE),
        ext(EXT_KEY_USAGE, false, EKU_SERVER_AUTH),
    ];
    cert(9999, issuer, "leaf", 9, signer, &extensions)
}

/// The root `root`, key 1.
fn root() -> Vec<u8> {
    ca(1, "root", "root", 1, 1)
}

const DNS: ReferenceIdentity<'static> = ReferenceIdentity::Dns(b"example.com");

/// 2026-06-01T00:00:00Z.
const NOW: u64 = 1_780_272_000;

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

/// `verify_server_chain` of `[leaf, pool...]` under the given roots.
fn verify_with<L: LinkVerifier>(
    link: &L,
    roots: &[Vec<u8>],
    presented: &[Vec<u8>],
    max: usize,
) -> Result<Validated, PathError> {
    let anchors: Vec<Anchor<'_>> = roots
        .iter()
        .filter_map(|der| anchor_from_root(der, None))
        .collect();
    assert_eq!(anchors.len(), roots.len(), "every root is an anchor");
    let slices: Vec<&[u8]> = presented.iter().map(Vec::as_slice).collect();
    let environment = Environment {
        link,
        revoked: &NotRevoked,
        max_intermediates: max,
    };
    verify_server_chain(&environment, &anchors, &slices, DNS, NOW)
}

fn verify(presented: &[Vec<u8>]) -> Result<Validated, PathError> {
    verify_with(&KeyedLink, &[root()], presented, 6)
}

/// The search with a budget, on `[leaf, pool...]` under `root()`.
fn search_with_budget(presented: &[Vec<u8>], budget: usize) -> Result<Validated, PathError> {
    search_with_budget_using(&KeyedLink, presented, budget)
}

/// `search_with_budget` with the given link verifier.
fn search_with_budget_using<L: LinkVerifier>(
    link: &L,
    presented: &[Vec<u8>],
    budget: usize,
) -> Result<Validated, PathError> {
    let root_der = root();
    let anchors: Vec<Anchor<'_>> = anchor_from_root(&root_der, None).into_iter().collect();
    let Some((first, rest)) = presented.split_first() else {
        return Err(PathError::Malformed);
    };
    let Some(leaf) = parse_path_cert(first) else {
        return Err(PathError::Malformed);
    };
    let pool: Vec<Option<PathCert<'_>>> = rest.iter().map(|der| parse_path_cert(der)).collect();
    let environment = Environment {
        link,
        revoked: &NotRevoked,
        max_intermediates: 6,
    };
    search(&environment, &anchors, &pool, &leaf, DNS, &now(), budget)
}

fn path_of(out: &Result<Validated, PathError>) -> Option<Vec<usize>> {
    out.as_ref().ok().map(|v| v.path.clone())
}

// ---------------------------------------------------------------------------
// Known answers
// ---------------------------------------------------------------------------

#[test]
fn a_plain_chain_is_accepted_with_the_leaf_key() {
    let leaf_der = leaf("int", 2);
    let out = verify(&[leaf_der.clone(), ca(2, "root", "int", 2, 1)]);
    let key = parse_path_cert(&leaf_der).map(|c| c.tbs.subject_public_key_info_der.to_vec());
    assert_eq!(
        out.as_ref()
            .map(|v| (v.anchor, v.path.clone(), v.leaf_spki.clone()))
            .ok(),
        key.map(|k| (0, vec![0], k))
    );
}

#[test]
fn anchors_come_before_intermediates() {
    // The server sends a copy of the root first; the anchor is examined for
    // `int` before the copy, so the short path is found.
    let out = verify(&[leaf("int", 2), root(), ca(2, "root", "int", 2, 1)]);
    assert_eq!(path_of(&out), Some(vec![1]));
}

#[test]
fn a_dead_end_cross_sign_is_backtracked() {
    // `int` cross-signed by an issuer with no anchor comes first.
    let out = verify(&[
        leaf("int", 2),
        ca(3, "other", "int", 2, 7),
        ca(2, "root", "int", 2, 1),
    ]);
    assert_eq!(path_of(&out), Some(vec![1]));
}

#[test]
fn a_cross_signed_choice_takes_the_first_valid_in_order() {
    // Two anchors issue `int`, both certificates present: anchors in table
    // order at each node, pool certificates in message order, so the first
    // pool certificate's anchor wins.
    let other_root = ca(5, "other", "other", 7, 7);
    let presented = [
        leaf("int", 2),
        ca(3, "other", "int", 2, 7),
        ca(2, "root", "int", 2, 1),
    ];
    let out = verify_with(&KeyedLink, &[root(), other_root], &presented, 6);
    assert_eq!(
        out.as_ref().map(|v| (v.anchor, v.path.clone())).ok(),
        Some((1, vec![0]))
    );
}

#[test]
fn a_loop_terminates() {
    let out = verify(&[leaf("a", 2), ca(2, "b", "a", 2, 3), ca(3, "a", "b", 3, 2)]);
    assert_eq!(out.err(), Some(PathError::UnknownIssuer));
}

/// `root -> c1 -> ... -> cn -> leaf`, each `ci` with its own name and key
/// byte `i + 1`.
fn chain(n: u8) -> Vec<Vec<u8>> {
    let label = |i: u8| {
        if i == 0 {
            "root".to_owned()
        } else {
            format!("c{i}")
        }
    };
    let mut presented = vec![leaf(&label(n), n.saturating_add(1))];
    presented.extend((1..=n).map(|i| {
        let below = i.saturating_sub(1);
        ca(
            u16::from(i).saturating_add(10),
            &label(below),
            &label(i),
            i.saturating_add(1),
            below.saturating_add(1),
        )
    }));
    presented
}

#[test]
fn six_intermediates_are_accepted_and_seven_are_not() {
    assert_eq!(path_of(&verify(&chain(6))).map(|p| p.len()), Some(6));
    assert_eq!(verify(&chain(7)).err(), Some(PathError::UnknownIssuer));
}

/// `root -> int`, then `m` self-issued re-issues of `int`, each signed by
/// the previous key, and the leaf under the last: the only valid path has
/// `m + 1` intermediates. The re-issues come first in message order.
fn reissued_chain(m: u8) -> Vec<Vec<u8>> {
    let mut presented = vec![leaf("int", m.saturating_add(2))];
    presented.extend((1..=m).map(|i| {
        ca(
            u16::from(i).saturating_add(20),
            "int",
            "int",
            i.saturating_add(2),
            i.saturating_add(1),
        )
    }));
    presented.push(ca(2, "root", "int", 2, 1));
    presented
}

#[test]
fn self_issued_intermediates_count_toward_the_depth() {
    // mozilla::pkix counts every non-anchor CA against MAX_SUBCA_COUNT,
    // self-issued ones included.
    assert_eq!(
        path_of(&verify(&reissued_chain(5))).map(|p| p.len()),
        Some(6)
    );
    let out = verify(&reissued_chain(6));
    assert!(
        matches!(out, Err(e) if e != PathError::BuildBudgetExhausted),
        "{:?}",
        out.as_ref().err()
    );
}

#[test]
fn first_valid_follows_message_order_depth_first() {
    // [int re-issued, int]: the re-issue is first in message order, so the
    // first valid path goes through it.
    let presented = [
        leaf("int", 2),
        ca(3, "int", "int", 2, 2),
        ca(2, "root", "int", 2, 1),
    ];
    assert_eq!(path_of(&verify(&presented)), Some(vec![1, 0]));
}

#[test]
fn a_small_budget_is_exhausted() {
    let presented = [
        leaf("int", 2),
        ca(3, "int", "int", 2, 2),
        ca(2, "root", "int", 2, 1),
    ];
    assert_eq!(
        search_with_budget(&presented, 2).err(),
        Some(PathError::BuildBudgetExhausted)
    );
    assert_eq!(
        path_of(&search_with_budget(&presented, 3)),
        Some(vec![1, 0])
    );
    assert_eq!(
        search_with_budget(&presented, 0).err(),
        Some(PathError::BuildBudgetExhausted)
    );
}

#[test]
fn the_first_candidates_error_is_reported() {
    // `int` is not signed by the root's key: the one candidate fails §6.1.3 (a)(1).
    let out = verify(&[leaf("int", 2), ca(2, "root", "int", 2, 5)]);
    assert_eq!(out.err(), Some(PathError::BadSignature));
    // No intermediate at all: no candidate.
    assert_eq!(
        verify(&[leaf("int", 2)]).err(),
        Some(PathError::UnknownIssuer)
    );
    // Nothing presented, or a leaf that does not parse.
    assert_eq!(verify(&[]).err(), Some(PathError::Malformed));
    assert_eq!(
        verify(&[vec![0x30, 0x00]]).err(),
        Some(PathError::Malformed)
    );
}

#[test]
fn an_unparsable_pool_certificate_is_dropped() {
    let out = verify(&[leaf("int", 2), vec![0x30, 0x00], ca(2, "root", "int", 2, 1)]);
    assert_eq!(path_of(&out), Some(vec![1]));
}

// ---------------------------------------------------------------------------
// Signature work (design §1.12)
// ---------------------------------------------------------------------------

struct Work {
    result: Result<Validated, PathError>,
    calls: u64,
    distinct: usize,
}

/// Signature work of the search on `presented`: `verify_server_chain` (the
/// production budget) when `budget` is `None`, else the search with that
/// budget.
fn measure(presented: &[Vec<u8>], budget: Option<usize>) -> Work {
    let link = CountingLink::default();
    let result = match budget {
        None => verify_with(&link, &[root()], presented, 6),
        Some(b) => search_with_budget_using(&link, presented, b),
    };
    let distinct = link.distinct.borrow().len();
    Work {
        result,
        calls: link.calls.get(),
        distinct,
    }
}

#[test]
fn signature_work_of_a_fan_of_junk_issuers() {
    // `root -> x` is real; `junk_i: x -> mid` are forgeries (wrong key);
    // the leaf is under `mid`. Each junk certificate is one candidate
    // `root -> x -> junk_i -> leaf` costing three steps and two links,
    // `root -> x` (verifies) and `x -> junk_i` (fails).
    //
    // Under Miri the fan is 20 wide, not 2,000: the interpreter is far too
    // slow for the full measurement (it timed out CI's 6-hour Miri job on
    // #46), and the assertions are formulas in `n`, so the same code runs
    // and the same facts are checked on a smaller input.
    let n: u16 = if cfg!(miri) { 20 } else { 2000 };
    let mut presented = vec![leaf("mid", 50), ca(2, "root", "x", 2, 1)];
    presented.extend((0..n).map(|i| ca(i.saturating_add(100), "x", "mid", 50, 77)));
    let work = measure(&presented, None);
    println!(
        "fan of {n}: {:?}, {} link calls, {} distinct links",
        work.result.as_ref().err(),
        work.calls,
        work.distinct
    );
    assert_eq!(work.result.err(), Some(PathError::BadSignature));
    assert_eq!(work.calls, u64::from(n).saturating_mul(2));
    assert_eq!(work.distinct, usize::from(n).saturating_add(1));
}

#[test]
fn signature_work_of_a_tree_of_self_issued_junk() {
    // `root -> mid` is real; `junk_i: mid -> mid` are forgeries; the leaf is
    // under `mid`. Every ordering of up to five junk certificates above the
    // leaf, topped by the real `mid`, is a candidate: the budget bounds the
    // search, and each candidate verifies `root -> mid` again and fails on
    // `mid -> junk`.
    //
    // Natively: 12 junk certificates under the production budget. Under
    // Miri (see the fan above): 4 junk certificates, whose tree of
    // candidates still exceeds a budget of 60 steps, so the search ends the
    // same way, through the same code, on an input Miri can interpret.
    let (n, budget): (u16, Option<usize>) = if cfg!(miri) {
        (4, Some(60))
    } else {
        (12, None)
    };
    let mut presented = vec![leaf("mid", 50), ca(2, "root", "mid", 2, 1)];
    presented.extend((0..n).map(|i| ca(i.saturating_add(100), "mid", "mid", 50, 77)));
    let work = measure(&presented, budget);
    println!(
        "tree of {n}: {:?}, {} link calls, {} distinct links",
        work.result.as_ref().err(),
        work.calls,
        work.distinct
    );
    // The real `root -> mid -> leaf`? The leaf is signed with key 50, not
    // `mid`'s key 2, so no candidate is valid.
    assert_eq!(work.result.err(), Some(PathError::BuildBudgetExhausted));
    assert!(work.distinct <= usize::from(n).saturating_add(2));
}

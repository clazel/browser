//! RSA PKCS#1 v1.5 verification conformance (docs/phases/phase-3.md item
//! 3.5c).
//!
//! The proofs show `verify` equals `spec.rs`, and `independent.rs` shows the
//! spec equals RFC 2313's parse-and-compare verification. This file checks
//! the implementation against the outside world:
//!
//! 1. Wycheproof's `RsassaPkcs1Verify` vectors (Apache-2.0, vendored at a
//!    pinned commit under `tests/data/wycheproof-rsa-pkcs1/` and converted
//!    by `cargo xtask testdata`): 2048-bit SHA-256 (with two more keys of
//!    exponent 3), 2048-bit SHA-384, 3072-bit SHA-256 and 4096-bit SHA-512,
//!    1035 vectors. The message digest is computed with
//!    `sha2`. `valid` must verify and `invalid` must not. The one
//!    `acceptable` vector of each file is flagged `MissingNull`
//!    (`DigestInfo` without the NULL parameters, which some verifiers
//!    accept); this verifier compares whole encoded messages (RFC 8017
//!    §9.2), so it rejects them, and they are listed in `ACCEPTABLE` and
//!    counted as expected failures, never as passes. An `acceptable`
//!    vector that is not listed there, or that this verifier accepts, is a
//!    failure.
//! 2. Hand-built cases (`tests/handbuilt/mod.rs`): OpenSSL-made valid
//!    signatures at 2048, 3072, 4096 and 8192 bits and exponents 3, 65537 and
//!    2^64 - 59, and every way to be wrong that the task names: a
//!    signature of at least n, a wrong `DigestInfo`, wrong padding bytes,
//!    short padding, a modulus out of range, and the e = 3 Bleichenbacher
//!    2006 forgery (garbage after the digest).
//! 3. Bit flips of the valid Wycheproof signatures, all of which must be
//!    rejected (RSA is a permutation of the integers below n, so a different
//!    in-range signature cannot decrypt to the same block).
//!
//! Under Miri (about 50 times slower than a debug build, which is itself
//! 14 times slower than release) only the exponent 3 vectors of the
//! Wycheproof files, the hand-built cases with `e <= 3`, and nothing else
//! run; the summary lines are printed only by a native run, which is the one
//! `cargo xtask verify` reads.
//!
//! No differential against the `rsa` crate: its dependency tree is 35
//! packages with default features off, far over the ten the task allows.
//! The independent engine is OpenSSL, through the hand-built cases.

mod handbuilt;

use clazel_pkcs1::spec::HashId;
use clazel_pkcs1::verify::verify;
use sha2::{Digest, Sha256, Sha384, Sha512};

/// One public key of the Wycheproof files.
struct Key {
    file: &'static str,
    group: usize,
    key_size: u64,
    sha: &'static str,
    modulus: &'static str,
    exponent: &'static str,
}

/// One Wycheproof test.
struct Case {
    key: usize,
    tc_id: u64,
    result: &'static str,
    flags: &'static [&'static str],
    comment: &'static str,
    msg: &'static str,
    sig: &'static str,
}

// `NUMBER_OF_TESTS`, `KEYS` and `CASES`, generated from the vendored files.
include!("generated/wycheproof_rsa_pkcs1.rs");

/// The `acceptable` vectors, with the flag that explains them. Wycheproof
/// calls a `DigestInfo` without its NULL parameters `acceptable`: some
/// libraries accept it. This verifier rejects it (RFC 8017 §9.2 note 1
/// gives the NULL, and §8.2.2 compares whole encoded messages), so each is
/// an expected failure.
const ACCEPTABLE: &[(&str, u64, &str)] = &[
    ("rsa_signature_2048_sha256_test.json", 8, "MissingNull"),
    ("rsa_signature_2048_sha384_test.json", 8, "MissingNull"),
    ("rsa_signature_3072_sha256_test.json", 8, "MissingNull"),
    ("rsa_signature_4096_sha512_test.json", 8, "MissingNull"),
];

fn nibble(b: u8) -> u8 {
    match b {
        b'0'..=b'9' => b.saturating_sub(b'0'),
        b'a'..=b'f' => b.saturating_sub(b'a').saturating_add(10),
        b'A'..=b'F' => b.saturating_sub(b'A').saturating_add(10),
        _ => 0,
    }
}

fn hex(s: &str) -> Vec<u8> {
    s.as_bytes()
        .chunks(2)
        .map(|p| {
            let hi = p.first().copied().map(nibble).unwrap_or(0);
            let lo = p.get(1).copied().map(nibble).unwrap_or(0);
            hi.wrapping_shl(4) | lo
        })
        .collect()
}

/// The exponent as a `u64`, if it fits.
fn exponent(s: &str) -> Option<u64> {
    let bytes = hex(s);
    let start = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
    let sig = bytes.get(start..)?;
    if sig.len() > 8 {
        return None;
    }
    Some(
        sig.iter()
            .fold(0u64, |acc, &b| acc.wrapping_shl(8) | u64::from(b)),
    )
}

fn hash_of(sha: &str) -> Option<HashId> {
    match sha {
        "SHA-256" => Some(HashId::Sha256),
        "SHA-384" => Some(HashId::Sha384),
        "SHA-512" => Some(HashId::Sha512),
        _ => None,
    }
}

fn digest(h: HashId, msg: &[u8]) -> Vec<u8> {
    match h {
        HashId::Sha256 => Sha256::digest(msg).to_vec(),
        HashId::Sha384 => Sha384::digest(msg).to_vec(),
        HashId::Sha512 => Sha512::digest(msg).to_vec(),
    }
}

/// Verdict of this crate on a Wycheproof case; `None` if the key is outside
/// what `verify` can take (an exponent wider than 64 bits, an unknown hash).
fn verdict(c: &Case) -> Option<bool> {
    let k = KEYS.get(c.key)?;
    let h = hash_of(k.sha)?;
    let e = exponent(k.exponent)?;
    let msg = hex(c.msg);
    Some(verify(&hex(k.modulus), e, &digest(h, &msg), h, &hex(c.sig)))
}

fn suite_name(file: &str) -> String {
    let first = KEYS.iter().find(|k| k.file == file);
    let (bits, sha) = first.map_or((0, "?"), |k| (k.key_size, k.sha));
    format!("Wycheproof RSASSA-PKCS1-v1_5 {bits}-bit {sha} ({file})")
}

#[test]
fn wycheproof_vectors() {
    let mut failures = Vec::new();
    for (file, declared) in NUMBER_OF_TESTS {
        let (mut pass, mut xfail, mut fail) = (0usize, 0usize, 0usize);
        for c in CASES
            .iter()
            .filter(|c| KEYS.get(c.key).is_some_and(|k| k.file == *file))
        {
            // Keep Miri's workload to the exponent-3 subset documented above;
            // native runs still check every vector and report the full totals.
            if cfg!(miri)
                && !KEYS
                    .get(c.key)
                    .is_some_and(|k| exponent(k.exponent) == Some(3))
            {
                continue;
            }
            let got = verdict(c);
            let ok = match (c.result, got) {
                ("valid", Some(true)) | ("invalid", Some(false)) => Some(true),
                ("acceptable", Some(false)) => {
                    let listed = ACCEPTABLE
                        .iter()
                        .any(|(f, id, flag)| f == file && *id == c.tc_id && c.flags == [*flag]);
                    if listed { None } else { Some(false) }
                }
                _ => Some(false),
            };
            match ok {
                Some(true) => pass = pass.saturating_add(1),
                None => xfail = xfail.saturating_add(1),
                Some(false) => {
                    fail = fail.saturating_add(1);
                    let group = KEYS.get(c.key).map_or(0, |k| k.group);
                    failures.push(format!(
                        "{file} group {group} tcId {} ({}; {}; flags {:?}): expected {}, got {got:?}",
                        c.tc_id, c.comment, c.result, c.flags, c.result
                    ));
                }
            }
        }
        if !cfg!(miri) {
            println!(
                "clazel-conformance: suite=\"{}\" pass={pass} xfail={xfail} fail={fail} total={declared}",
                suite_name(file)
            );
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

#[test]
fn every_acceptable_vector_is_listed() {
    let listed = CASES.iter().filter(|c| c.result == "acceptable").count();
    assert_eq!(listed, ACCEPTABLE.len());
    for c in CASES.iter().filter(|c| c.result == "acceptable") {
        let file = KEYS.get(c.key).map_or("", |k| k.file);
        assert!(
            ACCEPTABLE
                .iter()
                .any(|(f, id, flag)| *f == file && *id == c.tc_id && c.flags == [*flag]),
            "{file} tcId {} is acceptable but not listed",
            c.tc_id
        );
    }
}

#[test]
fn hand_built_cases() {
    let mut failures = Vec::new();
    let (mut pass, mut fail) = (0usize, 0usize);
    for c in handbuilt::CASES {
        if cfg!(miri) && c.e > 3 {
            continue;
        }
        let d = digest(c.hash, c.msg);
        let got = verify(&hex(c.n), c.e, &d, c.hash, &hex(c.sig));
        if got == c.expect {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            failures.push(format!(
                "{} ({}): expected {}, got {got}",
                c.name, c.why, c.expect
            ));
        }
    }
    if !cfg!(miri) {
        println!(
            "clazel-conformance: suite=\"Hand-built cases (OpenSSL signatures, malformed encodings, forgeries, ranges)\" pass={pass} xfail=0 fail={fail} total={}",
            handbuilt::CASES.len()
        );
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Flipping one bit of a valid signature must make it invalid.
#[test]
fn bit_flips_of_valid_signatures_are_rejected() {
    if cfg!(miri) {
        return;
    }
    let mut checked = 0usize;
    for c in CASES.iter().filter(|c| c.result == "valid") {
        let Some(k) = KEYS.get(c.key) else { continue };
        let (Some(h), Some(e)) = (hash_of(k.sha), exponent(k.exponent)) else {
            continue;
        };
        let (n, msg, sig) = (hex(k.modulus), hex(c.msg), hex(c.sig));
        let d = digest(h, &msg);
        assert!(verify(&n, e, &d, h, &sig), "tcId {} is valid", c.tc_id);
        // The first octet, the last, and one in the middle; one bit each.
        for (pos, bit) in [
            (0usize, 0u8),
            (sig.len().saturating_sub(1), 3),
            (sig.len() / 2, 7),
        ] {
            let mut bad = sig.clone();
            if let Some(b) = bad.get_mut(pos) {
                *b ^= 1u8.wrapping_shl(u32::from(bit));
            }
            assert!(
                !verify(&n, e, &d, h, &bad),
                "tcId {} bit flip at {pos}",
                c.tc_id
            );
            checked = checked.saturating_add(1);
        }
    }
    assert!(checked >= 30, "only {checked} flips checked");
}

/// One verification with a 2048-bit key and e = 65537, timed (it is a debug
/// build under `cargo test`; the number is printed, and bounded loosely so
/// that a regression to something unusable fails).
#[test]
fn time_of_one_2048_bit_verification() {
    if cfg!(miri) {
        return;
    }
    let c = CASES.iter().find(|c| {
        c.result == "valid"
            && KEYS.get(c.key).is_some_and(|k| {
                k.file == "rsa_signature_2048_sha256_test.json" && k.exponent == "010001"
            })
    });
    assert!(c.is_some(), "no valid 2048-bit e=65537 vector");
    let Some(c) = c else { return };
    let Some(k) = KEYS.get(c.key) else { return };
    let (n, msg, sig) = (hex(k.modulus), hex(c.msg), hex(c.sig));
    let d = digest(HashId::Sha256, &msg);
    let start = std::time::Instant::now();
    let rounds = 10u32;
    for _ in 0..rounds {
        assert!(verify(&n, 65537, &d, HashId::Sha256, &sig));
    }
    let each = start.elapsed() / rounds;
    println!("time of one 2048-bit verification, e = 65537: {each:?}");
    assert!(each < std::time::Duration::from_secs(1), "{each:?}");
}

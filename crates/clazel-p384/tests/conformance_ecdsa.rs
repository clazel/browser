//! ECDSA P-384 verification conformance (docs/phases/phase-3.md item 3.5h).
//!
//! The proofs show `verify` equals `spec.rs`. This file checks the whole
//! stack against the outside world, with two suites that were written by
//! others and are vendored under `tests/data/` (converted to Rust tables by
//! `cargo xtask testdata`, so this crate ships no JSON or `.rsp` parser):
//!
//! 1. **Wycheproof** `ecdsa_secp384r1_sha{256,384,512}_test.json` (Apache-2.0,
//!    commit `d17cc89f`; 1,518 tests). Each test is a message, a DER
//!    `Ecdsa-Sig-Value` and a key. The table already holds the digest of the
//!    message (computed by the converter under the group's hash), so each
//!    case runs end to end the way a TLS client would use this crate:
//!    `clazel-der` reads the signature (RFC 3279 §2.2.3) into `r` and `s`,
//!    and `clazel_p384::verify::verify` decides. A signature that DER
//!    refuses (BER lengths, a negative or over-long INTEGER, trailing bytes)
//!    counts as rejected, which is the expected verdict of every such test.
//!    This crate has no DER layer of its own (it takes `r` and `s`), so the
//!    reading of the encoding is `clazel-der`'s, and a DER decoder that was
//!    too lenient would show up here as a failed `invalid` test. `valid`
//!    must be accepted and `invalid` rejected. The file has no `acceptable`
//!    tests at this commit; one would have to be listed in [`ACCEPTABLE`]
//!    with its reason, and counts as an expected failure, never a pass.
//!    Anything else that disagrees is a failure unless listed, with its
//!    reason, in [`EXPECTED_FAILURES`] (empty).
//! 2. **NIST CAVP** FIPS 186-4 `SigVer.rsp`, the P-384 sections (SHA-1,
//!    SHA-224, SHA-256, SHA-384 and SHA-512; 15 cases each, 75 in all). `Msg`
//!    is hashed by the converter; `R` and `S` are given as integers, so the
//!    DER layer is not involved. `Result = P` must verify and `F` must not.
//!    SHA-1 and SHA-224 are included: `verify` takes any digest of 0 to 64
//!    octets and uses its leftmost 48 (FIPS 186-5 §6.4.2 step 2 and
//!    spec choice 10), so 20- and 28-octet digests are inputs it must handle.
//!
//! The summary lines are printed before anything is asserted, as
//! `xtask/src/conformance.rs` requires.
//!
//! Speed: a verification is about 1,150 group operations with an inversion
//! each, about 0.9 s in an unoptimised build. The workspace manifest compiles
//! this crate with `opt-level = 3` in the dev profile
//! (`[profile.dev.package.clazel-p384]`), which brings the 1,593 cases to
//! well under a minute. Miri is about 50 times slower than that profile's
//! debug build, so these tests are ignored under it.

use clazel_der::decode::{expect_sequence, read_integer};
use clazel_p384::verify::verify;

/// Wycheproof's tables (generated from the vendored JSON).
mod wycheproof {
    /// One group's public key.
    pub struct Key {
        pub file: &'static str,
        pub group: usize,
        pub sha: &'static str,
        pub point: &'static str,
    }

    /// One Wycheproof test.
    pub struct Case {
        pub key: usize,
        pub tc_id: u64,
        pub result: &'static str,
        pub flags: &'static [&'static str],
        pub comment: &'static str,
        pub digest: &'static str,
        pub sig: &'static str,
    }

    // `NUMBER_OF_TESTS`, `KEYS` and `CASES`.
    include!("generated/wycheproof_ecdsa_p384.rs");

    // The generated constants are private to this module; export them.
    pub const FILE_COUNTS: &[(&str, usize)] = NUMBER_OF_TESTS;
    pub const ALL_KEYS: &[Key] = KEYS;
    pub const ALL_CASES: &[Case] = CASES;
}

/// NIST's table (generated from the vendored `SigVer.rsp`).
mod cavp {
    /// One CAVP case.
    pub struct Case {
        pub sha: &'static str,
        pub digest: &'static str,
        pub key: &'static str,
        pub r: &'static str,
        pub s: &'static str,
        pub pass: bool,
        pub reason: &'static str,
    }

    // `CASES`.
    include!("generated/nist_cavp_ecdsa_sigver.rs");

    // The generated constant is private to this module; export it.
    pub const ALL_CASES: &[Case] = CASES;
}

/// The `acceptable` Wycheproof tests, `(file, tcId, flag, reason)`. A listed
/// test must be rejected by this verifier (that is its expected failure). At
/// this commit no test is `acceptable`, so the list is empty.
const ACCEPTABLE: &[(&str, u64, &str, &str)] = &[];

/// Tests whose verdict differs from the file's, `(file, tcId, reason)`, each
/// an expected failure. A listed test that agrees with the file is a failure
/// too, so the list cannot go stale. Empty: no test disagrees.
const EXPECTED_FAILURES: &[(&str, u64, &str)] = &[];

/// CAVP has 15 cases in each of the five P-384 sections (SOURCE.md).
const CAVP_TOTAL: usize = 5 * 15;

fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => b.checked_sub(b'0'),
        b'a'..=b'f' => b.checked_sub(b'a')?.checked_add(10),
        b'A'..=b'F' => b.checked_sub(b'A')?.checked_add(10),
        _ => None,
    }
}

/// The octets of a hex string; `None` if it is not even-length hex.
fn hex(s: &str) -> Option<Vec<u8>> {
    s.as_bytes()
        .chunks(2)
        .map(|p| {
            let hi = nibble(*p.first()?)?;
            let lo = nibble(*p.get(1)?)?;
            Some(hi.wrapping_shl(4) | lo)
        })
        .collect()
}

/// Right-align a magnitude of at most 48 octets into 48.
fn pad48(magnitude: &[u8]) -> Option<[u8; 48]> {
    let mut out = [0u8; 48];
    let start = out.len().checked_sub(magnitude.len())?;
    out.get_mut(start..)?.copy_from_slice(magnitude);
    Some(out)
}

/// RFC 3279 §2.2.3: `r` and `s` of exactly one DER `Ecdsa-Sig-Value`, each a
/// non-negative INTEGER of at most 48 magnitude octets, padded to 48. This is
/// the P-384 version of `clazel-crypto`'s `ecdsa_sig_value`, over the same
/// `clazel-der` readers. `None` if the encoding is refused.
fn ecdsa_sig_value(sig: &[u8]) -> Option<([u8; 48], [u8; 48])> {
    let (cs, ce) = expect_sequence(sig, 0, sig.len())?;
    if ce != sig.len() {
        return None;
    }
    let (r_negative, rs, re, after_r) = read_integer(sig, cs, ce)?;
    let (s_negative, ss, se, after_s) = read_integer(sig, after_r, ce)?;
    if r_negative || s_negative || after_s != ce {
        return None;
    }
    let r = pad48(sig.get(rs..re)?)?;
    let s = pad48(sig.get(ss..se)?)?;
    Some((r, s))
}

/// The verdict of this crate on one Wycheproof test, and whether DER refused
/// the signature before `verify` ran.
fn wycheproof_verdict(c: &wycheproof::Case) -> Option<(bool, bool)> {
    let key = wycheproof::ALL_KEYS.get(c.key)?;
    let point = hex(key.point)?;
    let digest = hex(c.digest)?;
    let sig = hex(c.sig)?;
    Some(match ecdsa_sig_value(&sig) {
        None => (false, true),
        Some((r, s)) => (verify(&digest, &r, &s, &point), false),
    })
}

/// Name of a Wycheproof file's suite in the README table.
fn wycheproof_suite_name(file: &str) -> String {
    let stem = file.strip_suffix("_test.json").unwrap_or(file);
    format!("Wycheproof {stem}")
}

#[test]
#[cfg_attr(
    miri,
    ignore = "about 1,500 verifications of 1,150 group operations each; far too slow under Miri"
)]
fn wycheproof_ecdsa_secp384r1() {
    let mut failures = Vec::new();
    for (file, declared) in wycheproof::FILE_COUNTS {
        let (mut pass, mut xfail, mut fail) = (0usize, 0usize, 0usize);
        let (mut der_refused, mut der_refused_valid) = (0usize, 0usize);
        for c in wycheproof::ALL_CASES.iter().filter(|c| {
            wycheproof::ALL_KEYS
                .get(c.key)
                .is_some_and(|k| k.file == *file)
        }) {
            let group = wycheproof::ALL_KEYS.get(c.key).map_or(0, |k| k.group);
            // The hash the converter used is the one the file's name says.
            let hash_ok = wycheproof::ALL_KEYS
                .get(c.key)
                .is_some_and(|k| file.contains(&format!("_{}_", k.sha.replace("SHA-", "sha"))));
            if !hash_ok {
                failures.push(format!(
                    "{file} group {group}: hash does not match the file"
                ));
            }
            let verdict = wycheproof_verdict(c);
            if let Some((_, true)) = verdict {
                der_refused = der_refused.saturating_add(1);
                if c.result == "valid" {
                    der_refused_valid = der_refused_valid.saturating_add(1);
                }
            }
            let got = verdict.map(|(v, _)| v);
            let listed = EXPECTED_FAILURES
                .iter()
                .any(|(f, id, _)| f == file && *id == c.tc_id);
            let agrees = matches!(
                (c.result, got),
                ("valid", Some(true)) | ("invalid", Some(false))
            );
            let acceptable_listed = ACCEPTABLE
                .iter()
                .any(|(f, id, flag, _)| f == file && *id == c.tc_id && c.flags == [*flag]);
            let expected_failure =
                (c.result == "acceptable" && got == Some(false) && acceptable_listed)
                    || (listed && !agrees);
            let counted = if expected_failure {
                Counted::Xfail
            } else if agrees && !listed {
                Counted::Pass
            } else {
                Counted::Fail
            };
            match counted {
                Counted::Pass => pass = pass.saturating_add(1),
                Counted::Xfail => xfail = xfail.saturating_add(1),
                Counted::Fail => {
                    fail = fail.saturating_add(1);
                    failures.push(format!(
                        "{file} group {group} tcId {} ({}; {}; flags {:?}): file says {}, verify says {got:?}{}",
                        c.tc_id,
                        c.comment,
                        c.result,
                        c.flags,
                        c.result,
                        if listed { " (listed as an expected failure, but agrees)" } else { "" }
                    ));
                }
            }
        }
        println!(
            "clazel-conformance: suite=\"{}\" pass={pass} xfail={xfail} fail={fail} total={declared}",
            wycheproof_suite_name(file)
        );
        println!(
            "  {file}: DER refused {der_refused} signatures ({der_refused_valid} of them valid)"
        );
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

#[test]
#[cfg_attr(
    miri,
    ignore = "75 verifications of 1,150 group operations each; too slow under Miri"
)]
fn cavp_186_4_sigver_p384() {
    let (mut pass, mut fail) = (0usize, 0usize);
    let mut failures = Vec::new();
    for (i, c) in cavp::ALL_CASES.iter().enumerate() {
        let got = (|| {
            let digest = hex(c.digest)?;
            let point = hex(c.key)?;
            let r = <[u8; 48]>::try_from(hex(c.r)?.as_slice()).ok()?;
            let s = <[u8; 48]>::try_from(hex(c.s)?.as_slice()).ok()?;
            Some(verify(&digest, &r, &s, &point))
        })();
        if got == Some(c.pass) {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            failures.push(format!(
                "case {i} ({}; Result {}{}): verify says {got:?}",
                c.sha,
                if c.pass { "P" } else { "F" },
                if c.reason.is_empty() {
                    String::new()
                } else {
                    format!(" ({})", c.reason)
                },
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"CAVP 186-4 SigVer P-384\" pass={pass} xfail=0 fail={fail} total={CAVP_TOTAL}"
    );
    assert_eq!(cavp::ALL_CASES.len(), CAVP_TOTAL, "the table has 75 cases");
    assert!(failures.is_empty(), "{failures:#?}");
}

/// How one Wycheproof test is counted.
enum Counted {
    Pass,
    Xfail,
    Fail,
}

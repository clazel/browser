//! Differential test of `clazel_p384::verify::verify` against `ring` 0.17.14,
//! an independent engine (docs/phases/phase-3.md item 3.5h).
//!
//! `ring`'s P-384 code descends from BoringSSL's and shares nothing with this
//! crate: not the field (fiat-crypto here, `ring`'s own C and assembly
//! there), not the group law, not the encodings. So where the two disagree,
//! one of them is wrong, and a shared misreading of FIPS 186-5 would need
//! both to make it.
//!
//! What is generated, from a fixed seed (SplitMix64, [`SEED`]):
//!
//! - [`KEYS`] P-384 key pairs, [`SIGNATURES`] messages of 0 to 255 octets, and
//!   which key signs which message. `ring` signs each message with
//!   `ECDSA_P384_SHA384_FIXED_SIGNING` (SHA-384, `r || s` as 96 octets).
//! - For each signature, [`KINDS`] cases: the valid signature, one flipped bit
//!   in `r`, one in `s`, one in the message (so a wrong digest), one in the
//!   public key (usually off the curve), another key's public key, and an
//!   edge value for `r` and `s` (0, 1, n - 1, n, n + 1 and 2^384 - 1 in turn;
//!   the pair is `(edge, edge)` and, for the odd cases, `(edge, s)`).
//!
//! `verify` takes the digest (SHA-384 of the message, computed here with
//! `sha2`); `ring` takes the message. Both must give the same verdict on
//! every case, and the unmodified signature must be accepted by both. A case
//! counts as a pass when they agree and, for the valid case, accept.
//!
//! What is not seeded: `ring` draws its key pairs and signing nonces from the
//! operating system (its `SecureRandom` is sealed, so a deterministic source
//! cannot be passed in). The choice of messages, keys, flipped bits and edge
//! values is fixed, the signatures differ between runs, and the failure
//! message prints the key, digest and signature in hex so a disagreement can
//! be replayed.
//!
//! The comparisons are spread over the available cores (`verify` is a pure
//! function). The test is ignored under Miri: `ring` is C and assembly.

use clazel_p384::verify::verify;
use ring::rand::SystemRandom;
use ring::signature::{
    ECDSA_P384_SHA384_FIXED, ECDSA_P384_SHA384_FIXED_SIGNING, EcdsaKeyPair, KeyPair,
    UnparsedPublicKey,
};
use sha2::{Digest, Sha384};

/// The generator's seed.
const SEED: u64 = 0x5eed_0384_ec05_a001;
/// Key pairs generated.
const KEYS: usize = 8;
/// Messages signed.
const SIGNATURES: usize = 2000;
/// Cases per signature (the list in the module comment).
const KINDS: usize = 7;

/// The order n of P-384 (SP 800-186 §3.2.1.4), 48 octets.
const N: [u8; 48] = [
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc7, 0x63, 0x4d, 0x81, 0xf4, 0x37, 0x2d, 0xdf,
    0x58, 0x1a, 0x0d, 0xb2, 0x48, 0xb0, 0xa7, 0x7a, 0xec, 0xec, 0x19, 0x6a, 0xcc, 0xc5, 0x29, 0x73,
];

/// SplitMix64 (Steele, Lea, Flood 2014): a small fixed-seed generator.
struct Rng(u64);

impl Rng {
    fn draw(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ z.wrapping_shr(30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ z.wrapping_shr(27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ z.wrapping_shr(31)
    }

    /// A value below `bound` (modulo bias is irrelevant here).
    fn below(&mut self, bound: usize) -> usize {
        let bound = u64::try_from(bound).unwrap_or(1);
        usize::try_from(self.draw().checked_rem(bound).unwrap_or(0)).unwrap_or(0)
    }

    fn octets(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.draw().to_le_bytes()[0]).collect()
    }
}

/// `value + 1` or `value - 1` of a 48-octet big-endian integer, wrapping.
fn add_small(value: &[u8; 48], up: bool) -> [u8; 48] {
    let mut out = *value;
    for b in out.iter_mut().rev() {
        let (v, carry) = if up {
            b.overflowing_add(1)
        } else {
            b.overflowing_sub(1)
        };
        *b = v;
        if !carry {
            break;
        }
    }
    out
}

fn one() -> [u8; 48] {
    let mut v = [0u8; 48];
    if let Some(last) = v.last_mut() {
        *last = 1;
    }
    v
}

/// The `i`-th edge value: 0, 1, n - 1, n, n + 1, 2^384 - 1.
fn edge(i: usize) -> [u8; 48] {
    match i.checked_rem(6).unwrap_or(0) {
        0 => [0u8; 48],
        1 => one(),
        2 => add_small(&N, false),
        3 => N,
        4 => add_small(&N, true),
        _ => [0xff; 48],
    }
}

/// One comparison: what both engines are asked.
struct Case {
    kind: &'static str,
    /// Index of the signature it was made from.
    from: usize,
    message: Vec<u8>,
    point: Vec<u8>,
    r: [u8; 48],
    s: [u8; 48],
}

fn flip_bit(octets: &mut [u8], rng: &mut Rng) {
    let at = rng.below(octets.len().saturating_mul(8));
    if let Some(b) = octets.get_mut(at.wrapping_shr(3)) {
        *b ^= 1u8.wrapping_shl(u32::try_from(at & 7).unwrap_or(0));
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

/// `ring`'s verdict on a case.
fn ring_verdict(c: &Case) -> bool {
    let mut sig = Vec::with_capacity(96);
    sig.extend_from_slice(&c.r);
    sig.extend_from_slice(&c.s);
    UnparsedPublicKey::new(&ECDSA_P384_SHA384_FIXED, &c.point)
        .verify(&c.message, &sig)
        .is_ok()
}

/// This crate's verdict on a case.
fn our_verdict(c: &Case) -> bool {
    let digest = Sha384::digest(&c.message);
    verify(&digest, &c.r, &c.s, &c.point)
}

#[test]
#[cfg_attr(
    miri,
    ignore = "ring is C and assembly, and each verification is too slow under Miri"
)]
fn differential_against_ring() -> Result<(), String> {
    let rng_os = SystemRandom::new();
    let mut keys = Vec::new();
    for _ in 0..KEYS {
        let pkcs8 = EcdsaKeyPair::generate_pkcs8(&ECDSA_P384_SHA384_FIXED_SIGNING, &rng_os)
            .map_err(|e| format!("generate_pkcs8: {e}"))?;
        let pair =
            EcdsaKeyPair::from_pkcs8(&ECDSA_P384_SHA384_FIXED_SIGNING, pkcs8.as_ref(), &rng_os)
                .map_err(|e| format!("from_pkcs8: {e}"))?;
        keys.push(pair);
    }
    let points: Vec<Vec<u8>> = keys
        .iter()
        .map(|k| k.public_key().as_ref().to_vec())
        .collect();

    let mut rng = Rng(SEED);
    let mut cases: Vec<Case> = Vec::new();
    for i in 0..SIGNATURES {
        let ki = rng.below(KEYS);
        let len = rng.below(256);
        let message = rng.octets(len);
        let pair = keys.get(ki).ok_or("no key")?;
        let point = points.get(ki).ok_or("no point")?.clone();
        let sig = pair
            .sign(&rng_os, &message)
            .map_err(|e| format!("sign: {e}"))?;
        let sig = sig.as_ref();
        let r = <[u8; 48]>::try_from(sig.get(..48).ok_or("short signature")?)
            .map_err(|e| e.to_string())?;
        let s = <[u8; 48]>::try_from(sig.get(48..96).ok_or("short signature")?)
            .map_err(|e| e.to_string())?;
        let base = |kind: &'static str| Case {
            kind,
            from: i,
            message: message.clone(),
            point: point.clone(),
            r,
            s,
        };
        cases.push(base("valid"));
        let mut c = base("r bit flipped");
        flip_bit(&mut c.r, &mut rng);
        cases.push(c);
        let mut c = base("s bit flipped");
        flip_bit(&mut c.s, &mut rng);
        cases.push(c);
        let mut c = base("message bit flipped (wrong digest)");
        if c.message.is_empty() {
            c.message.push(rng.octets(1).first().copied().unwrap_or(0));
        } else {
            flip_bit(&mut c.message, &mut rng);
        }
        cases.push(c);
        let mut c = base("public key bit flipped");
        // Not the 04 prefix: that is a different failure (an encoding), and
        // is cheap; flip anywhere in the coordinates.
        if let Some(coords) = c.point.get_mut(1..) {
            flip_bit(coords, &mut rng);
        }
        cases.push(c);
        let mut c = base("another key");
        let other = (ki
            .saturating_add(1)
            .saturating_add(rng.below(KEYS.saturating_sub(1))))
            % KEYS;
        c.point = points.get(other).ok_or("no point")?.clone();
        cases.push(c);
        let mut c = base("edge value for r and s");
        let e = edge(i);
        c.r = e;
        c.s = if i & 1 == 0 { e } else { s };
        cases.push(c);
    }
    let total = SIGNATURES.saturating_mul(KINDS);

    let threads = std::thread::available_parallelism().map_or(1, usize::from);
    let chunk = cases.len().div_ceil(threads).max(1);
    let results: Vec<Vec<(bool, bool)>> = std::thread::scope(|scope| {
        let handles: Vec<_> = cases
            .chunks(chunk)
            .map(|part| {
                scope.spawn(move || {
                    part.iter()
                        .map(|c| (our_verdict(c), ring_verdict(c)))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_default())
            .collect()
    });
    let verdicts: Vec<(bool, bool)> = results.into_iter().flatten().collect();

    let (mut pass, mut fail) = (0usize, 0usize);
    let (mut accepted, mut rejected) = (0usize, 0usize);
    let mut failures = Vec::new();
    for (c, v) in cases.iter().zip(&verdicts) {
        let (ours, ring) = *v;
        let valid_case = c.kind == "valid";
        let ok = ours == ring && (!valid_case || ours);
        if ok {
            pass = pass.saturating_add(1);
        } else {
            fail = fail.saturating_add(1);
            failures.push(format!(
                "signature {} ({}): clazel-p384 says {ours}, ring says {ring}; key {} message {} r {} s {}",
                c.from,
                c.kind,
                hex(&c.point),
                hex(&c.message),
                hex(&c.r),
                hex(&c.s)
            ));
        }
        if ours {
            accepted = accepted.saturating_add(1);
        } else {
            rejected = rejected.saturating_add(1);
        }
    }
    // Missing verdicts (a panicked thread) are failures, not omissions.
    fail = fail.saturating_add(total.saturating_sub(pass.saturating_add(fail)));
    println!(
        "clazel-conformance: suite=\"Differential vs ring 0.17.14 P-384 SHA-384\" pass={pass} xfail=0 fail={fail} total={total}"
    );
    println!("  both engines agreed on {accepted} accepts and {rejected} rejects");
    if failures.is_empty() && fail == 0 {
        Ok(())
    } else {
        Err(format!("{fail} disagreements: {failures:#?}"))
    }
}

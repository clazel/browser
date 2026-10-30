//! `clazel_p384::verify::verify` smoke tests: Wycheproof's valid signatures
//! are accepted, and signatures and keys that are damaged in one known way
//! are rejected. Full conformance (every Wycheproof vector, ACVP, a
//! differential against another engine) is for a later change.
//!
//! # Source of the vectors
//!
//! Wycheproof `testvectors_v1/ecdsa_secp384r1_sha384_test.json` at commit
//! `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9` of
//! <https://github.com/C2SP/wycheproof> (the commit `clazel-pkcs1` pins;
//! Apache-2.0; the file's SHA-256 is
//! `8a5b3ae1760975143414811f13588c24d951d9d8c904195087ba327591dfe9cc`).
//! Each [`Vector`] below is one test of that file, named by its `tcId`:
//!
//! - `key` is the group's `publicKey.uncompressed`, the 97-octet ECPoint;
//! - `digest` is SHA-384 of the test's `msg`, computed with Python's
//!   `hashlib` (the verifier takes the digest, not the message, and no hash
//!   crate is a test dependency of this crate);
//! - `r` and `s` are the two integers of the test's DER `sig`, parsed with
//!   a strict Python DER reader and left-padded to 48 octets.
//!
//! The 14 vectors were chosen to reach different code: pseudorandom and
//! malleable signatures (1, 2, 5, 7), the Shamir edge case (295), digests
//! that are special (296, 297, 300: all-zero, all-one and similar), and, as
//! invalid ones, a changed first octet of r (102), `r = 0` (109), `s = 0`
//! (151), `r = 0, s = n` (171), `r = n, s = n` (195) and `r = n - 1, s = n - 1`
//! (204). The valid ones are `"valid"` in the file and the invalid ones are
//! `"invalid"`; none is `"acceptable"`.

use clazel_p384::verify::verify;
use std::time::Instant;

type TestResult = Result<(), String>;

/// One Wycheproof test, as hexadecimal strings.
struct Vector {
    tc_id: u32,
    comment: &'static str,
    key: &'static str,
    digest: &'static str,
    r: &'static str,
    s: &'static str,
}

const VALID: &[Vector] = &[
    Vector {
        tc_id: 1,
        comment: "pseudorandom signature",
        key: "0429bdb76d5fa741bfd70233cb3a66cc7d44beb3b0663d92a8136650478bcefb61ef182e155a54345a5e8e5e88f064e5bc9a525ab7f764dad3dae1468c2b419f3b62b9ba917d5e8c4fb1ec47404a3fc76474b2713081be9db4c00e043ada9fc4a3",
        digest: "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b",
        r: "32401249714e9091f05a5e109d5c1216fdc05e98614261aa0dbd9e9cd4415dee29238afbd3b103c1e40ee5c9144aee0f",
        s: "4326756fb2c4fd726360dd6479b5849478c7a9d054a833a58c1631c33b63c3441336ddf2c7fe0ed129aae6d4ddfeb753",
    },
    Vector {
        tc_id: 2,
        comment: "pseudorandom signature",
        key: "0429bdb76d5fa741bfd70233cb3a66cc7d44beb3b0663d92a8136650478bcefb61ef182e155a54345a5e8e5e88f064e5bc9a525ab7f764dad3dae1468c2b419f3b62b9ba917d5e8c4fb1ec47404a3fc76474b2713081be9db4c00e043ada9fc4a3",
        digest: "5340980991c93d7111312700b83e9e61eed0977c5bca41d5dc9e26a7af4dbef3908df6661e32e039842176176609ba8f",
        r: "d7143a836608b25599a7f28dec6635494c2992ad1e2bbeecb7ef601a9c01746e710ce0d9c48accb38a79ede5b9638f34",
        s: "80f9e165e8c61035bf8aa7b5533960e46dd0e211c904a064edb6de41f797c0eae4e327612ee3f816f4157272bb4fabc9",
    },
    Vector {
        tc_id: 5,
        comment: "signature malleability",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "f9b127f0d81ebcd17b7ba0ea131c660d340b05ce557c82160e0f793de07d38179023942871acb7002dfafdfffc8deace",
        r: "12b30abef6b5476fe6b612ae557c0425661e26b44b1bfe19daf2ca28e3113083ba8e4ae4cc45a0320abd3394f1c548d7",
        s: "1840da9fc1d2f8f8900cf485d5413b8c2574ee3a8d4ca03995ca30240e09513805bf6209b58ac7aa9cff54eecd82b9f1",
    },
    Vector {
        tc_id: 7,
        comment: "valid",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "f9b127f0d81ebcd17b7ba0ea131c660d340b05ce557c82160e0f793de07d38179023942871acb7002dfafdfffc8deace",
        r: "12b30abef6b5476fe6b612ae557c0425661e26b44b1bfe19daf2ca28e3113083ba8e4ae4cc45a0320abd3394f1c548d7",
        s: "e7bf25603e2d07076ff30b7a2abec473da8b11c572b35fc631991d5de62ddca7525aaba89325dfd04fecc47bff426f82",
    },
    Vector {
        tc_id: 295,
        comment: "Edge case for Shamir multiplication",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "1ea4d7e33dd2cad2b412822fb60c29b7280cae718af25c51f907eb101cca981ac86a9d1a9186a1b630fb6e7079385911",
        r: "ac042e13ab83394692019170707bc21dd3d7b8d233d11b651757085bdd5767eabbb85322984f14437335de0cdf565684",
        s: "bd770d3ee4beadbabe7ca46e8c4702783435228d46e2dd360e322fe61c86926fa49c8116ec940f72ac8c30d9beb3e12f",
    },
    Vector {
        tc_id: 296,
        comment: "special case hash",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "00000000505a3d306890ad438d155166987fcd0d78a44fa79272ef4dcade39c852dcd5a4b23075d7651bb5c57629f198",
        r: "d3298a0193c4316b34e3833ff764a82cff4ef57b5dd79ed6237b51ff76ceab13bf92131f41030515b7e012d2ba857830",
        s: "bfc7518d2ad20ed5f58f3be79720f1866f7a23b3bd1bf913d3916819d008497a071046311d3c2fd05fc284c964a39617",
    },
    Vector {
        tc_id: 297,
        comment: "special case hash",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "fc000000009322da48a8586f26f148003932f6d4c0d1ce3a21798f7b651dab7642188c9061a66dc9b190e00b0290e264",
        r: "e14f41a5fc83aa4725a9ea60ab5b0b9de27f519af4b557a601f1fee0243f8eee5180f8c531414f3473f4457430cb7a26",
        s: "1047ed2bf1f98e3ce93e8fdbdc63cc79f238998fee74e1bb6cd708694950bbffe3945066064da043f04d7083d0a596ec",
    },
    Vector {
        tc_id: 300,
        comment: "special case hash",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "3b0f107e00000000c33f3c4431329dc9f62a724c34d1f01d3b3520b01647570625a5d84e7f7770d88ad6b3f195324d65",
        r: "9ad363a1bbc67c57c82a378e988cc083cc91f8b32739ec647c0cb348fb5c86472015131a7d9083bf4740af3351755195",
        s: "d310dc1509f8c00281efe571768d488027ea760fe32971f6cb7b57cdf90621b7d0086e26443d3761df7aa3a4eccc6c58",
    },
];

const INVALID: &[Vector] = &[
    Vector {
        tc_id: 102,
        comment: "modifying first byte of r",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "f9b127f0d81ebcd17b7ba0ea131c660d340b05ce557c82160e0f793de07d38179023942871acb7002dfafdfffc8deace",
        r: "10b30abef6b5476fe6b612ae557c0425661e26b44b1bfe19daf2ca28e3113083ba8e4ae4cc45a0320abd3394f1c548d7",
        s: "e7bf25603e2d07076ff30b7a2abec473da8b11c572b35fc631991d5de62ddca7525aaba89325dfd04fecc47bff426f82",
    },
    Vector {
        tc_id: 109,
        comment: "replacing r with zero",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "f9b127f0d81ebcd17b7ba0ea131c660d340b05ce557c82160e0f793de07d38179023942871acb7002dfafdfffc8deace",
        r: "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        s: "e7bf25603e2d07076ff30b7a2abec473da8b11c572b35fc631991d5de62ddca7525aaba89325dfd04fecc47bff426f82",
    },
    Vector {
        tc_id: 151,
        comment: "replacing s with zero",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "f9b127f0d81ebcd17b7ba0ea131c660d340b05ce557c82160e0f793de07d38179023942871acb7002dfafdfffc8deace",
        r: "12b30abef6b5476fe6b612ae557c0425661e26b44b1bfe19daf2ca28e3113083ba8e4ae4cc45a0320abd3394f1c548d7",
        s: "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    },
    Vector {
        tc_id: 171,
        comment: "Signature with special case values r=0 and s=n",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "f9b127f0d81ebcd17b7ba0ea131c660d340b05ce557c82160e0f793de07d38179023942871acb7002dfafdfffc8deace",
        r: "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        s: "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
    },
    Vector {
        tc_id: 195,
        comment: "Signature with special case values r=n and s=n",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "f9b127f0d81ebcd17b7ba0ea131c660d340b05ce557c82160e0f793de07d38179023942871acb7002dfafdfffc8deace",
        r: "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
        s: "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
    },
    Vector {
        tc_id: 204,
        comment: "Signature with special case values r=n - 1 and s=n - 1",
        key: "042da57dda1089276a543f9ffdac0bff0d976cad71eb7280e7d9bfd9fee4bdb2f20f47ff888274389772d98cc5752138aa4b6d054d69dcf3e25ec49df870715e34883b1836197d76f8ad962e78f6571bbc7407b0d6091f9e4d88f014274406174f",
        digest: "f9b127f0d81ebcd17b7ba0ea131c660d340b05ce557c82160e0f793de07d38179023942871acb7002dfafdfffc8deace",
        r: "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        s: "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
    },
];

/// The order n of P-384 (SP 800-186 §3.2.1.4), 48 octets.
const N: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973";
/// The field prime p.
const P: &str = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff";

fn unhex(h: &str) -> Result<Vec<u8>, String> {
    let digits = h.as_bytes();
    if !digits.len().is_multiple_of(2) {
        return Err(format!("odd number of hex digits in {h}"));
    }
    digits
        .chunks(2)
        .map(|pair| {
            let pair = std::str::from_utf8(pair).map_err(|e| e.to_string())?;
            u8::from_str_radix(pair, 16).map_err(|e| format!("{pair}: {e}"))
        })
        .collect()
}

fn arr48(h: &str) -> Result<[u8; 48], String> {
    let v = unhex(h)?;
    <[u8; 48]>::try_from(v.as_slice()).map_err(|_| format!("{} octets, want 48", v.len()))
}

/// A vector decoded: `(key, digest, r, s)`.
type Decoded = (Vec<u8>, Vec<u8>, [u8; 48], [u8; 48]);

fn decode(v: &Vector) -> Result<Decoded, String> {
    Ok((unhex(v.key)?, unhex(v.digest)?, arr48(v.r)?, arr48(v.s)?))
}

fn expect(what: &str, got: bool, want: bool) -> TestResult {
    if got == want {
        Ok(())
    } else {
        Err(format!("{what}: verify returned {got}, want {want}"))
    }
}

fn first(set: &'static [Vector]) -> Result<&'static Vector, String> {
    set.first().ok_or_else(|| "no vectors".to_string())
}

fn vector(set: &'static [Vector], tc_id: u32) -> Result<&'static Vector, String> {
    set.iter()
        .find(|v| v.tc_id == tc_id)
        .ok_or_else(|| format!("no tcId {tc_id}"))
}

/// Flip one bit of the octet at `at`.
fn flip(o: &mut [u8], at: usize) -> TestResult {
    let b = o.get_mut(at).ok_or_else(|| format!("no octet {at}"))?;
    *b ^= 0x01;
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "a verification is about 1,150 group operations, too slow under Miri"
)]
fn wycheproof_valid_signatures_are_accepted() -> TestResult {
    for v in VALID {
        let (key, digest, r, s) = decode(v)?;
        let start = Instant::now();
        let ok = verify(&digest, &r, &s, &key);
        eprintln!("tcId {} ({}): {:?}", v.tc_id, v.comment, start.elapsed());
        expect(&format!("tcId {} ({})", v.tc_id, v.comment), ok, true)?;
    }
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "a verification is about 1,150 group operations, too slow under Miri"
)]
fn wycheproof_invalid_signatures_are_rejected() -> TestResult {
    for v in INVALID {
        let (key, digest, r, s) = decode(v)?;
        expect(
            &format!("tcId {} ({})", v.tc_id, v.comment),
            verify(&digest, &r, &s, &key),
            false,
        )?;
    }
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "a verification is about 1,150 group operations, too slow under Miri"
)]
fn tampered_r_and_s_are_rejected() -> TestResult {
    let v = first(VALID)?;
    let (key, digest, r, s) = decode(v)?;
    expect("untouched", verify(&digest, &r, &s, &key), true)?;
    for at in [0, 23, 47] {
        let mut r2 = r;
        flip(&mut r2, at)?;
        expect(
            &format!("r octet {at} flipped"),
            verify(&digest, &r2, &s, &key),
            false,
        )?;
        let mut s2 = s;
        flip(&mut s2, at)?;
        expect(
            &format!("s octet {at} flipped"),
            verify(&digest, &r, &s2, &key),
            false,
        )?;
    }
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "a verification is about 1,150 group operations, too slow under Miri"
)]
fn a_wrong_digest_is_rejected() -> TestResult {
    let v = first(VALID)?;
    let (key, digest, r, s) = decode(v)?;
    let mut d2 = digest.clone();
    flip(&mut d2, 0)?;
    expect(
        "first bit of the digest flipped",
        verify(&d2, &r, &s, &key),
        false,
    )?;
    let mut d3 = digest.clone();
    flip(&mut d3, 47)?;
    expect(
        "last bit of the digest flipped",
        verify(&d3, &r, &s, &key),
        false,
    )?;
    // A digest cut short is another digest.
    let short = digest.get(..47).ok_or("short")?;
    expect("one octet short", verify(short, &r, &s, &key), false)?;
    // One with an octet put in front is another digest too.
    let mut front = vec![0u8];
    front.extend_from_slice(&digest);
    expect("one octet in front", verify(&front, &r, &s, &key), false)?;
    expect("empty digest", verify(&[], &r, &s, &key), false)?;
    Ok(())
}

/// FIPS 186-5 §6.4.2 step 3: only the leftmost 384 bits of a longer digest
/// are used, so octets after the 48th change nothing (SHA-512's 64 octets are
/// cut to 48).
#[test]
#[cfg_attr(
    miri,
    ignore = "a verification is about 1,150 group operations, too slow under Miri"
)]
fn a_longer_digest_is_cut_to_its_leftmost_384_bits() -> TestResult {
    let v = first(VALID)?;
    let (key, digest, r, s) = decode(v)?;
    let mut long = digest.clone();
    long.extend_from_slice(&[0xa5; 16]);
    expect(
        "64 octets, first 48 as signed",
        verify(&long, &r, &s, &key),
        true,
    )?;
    let mut changed = long.clone();
    flip(&mut changed, 47)?;
    expect(
        "64 octets, 48th octet changed",
        verify(&changed, &r, &s, &key),
        false,
    )?;
    Ok(())
}

#[test]
fn r_and_s_outside_one_to_n_minus_one_are_rejected() -> TestResult {
    let v = first(VALID)?;
    let (key, digest, r, s) = decode(v)?;
    let zero = [0u8; 48];
    let n = arr48(N)?;
    let ff = [0xffu8; 48];
    let mut n_plus_1 = n;
    // n ends in ...2973, so n + 1 does not carry.
    let last = n_plus_1.last_mut().ok_or("n")?;
    *last = last.wrapping_add(1);
    for (name, bad) in [
        ("0", zero),
        ("n", n),
        ("n + 1", n_plus_1),
        ("2^384 - 1", ff),
    ] {
        expect(
            &format!("r = {name}"),
            verify(&digest, &bad, &s, &key),
            false,
        )?;
        expect(
            &format!("s = {name}"),
            verify(&digest, &r, &bad, &key),
            false,
        )?;
        expect(
            &format!("r = s = {name}"),
            verify(&digest, &bad, &bad, &key),
            false,
        )?;
    }
    Ok(())
}

#[test]
fn keys_that_do_not_decode_are_rejected() -> TestResult {
    let v = first(VALID)?;
    let (key, digest, r, s) = decode(v)?;
    // Off the curve: y changed by one bit.
    let mut off = key.clone();
    let last = off.last_mut().ok_or("key")?;
    *last ^= 1;
    expect("off the curve", verify(&digest, &r, &s, &off), false)?;
    // Compressed form (`02`/`03` || X), which the specification refuses.
    let x = key.get(1..49).ok_or("x")?;
    for tag in [2u8, 3] {
        let mut c = vec![tag];
        c.extend_from_slice(x);
        expect(
            &format!("compressed {tag:02x}"),
            verify(&digest, &r, &s, &c),
            false,
        )?;
    }
    // Hybrid forms (`06`/`07`), a first octet other than `04`, and the point
    // at infinity.
    for tag in [0u8, 1, 5, 6, 7, 0xff] {
        let mut h = key.clone();
        let first = h.first_mut().ok_or("key")?;
        *first = tag;
        expect(
            &format!("first octet {tag:02x}"),
            verify(&digest, &r, &s, &h),
            false,
        )?;
    }
    expect("point at infinity", verify(&digest, &r, &s, &[0]), false)?;
    // Wrong lengths.
    expect("empty key", verify(&digest, &r, &s, &[]), false)?;
    expect(
        "one octet short",
        verify(&digest, &r, &s, key.get(..96).ok_or("k")?),
        false,
    )?;
    let mut long = key.clone();
    long.push(0);
    expect("one octet more", verify(&digest, &r, &s, &long), false)?;
    // A coordinate that is at least p (X = p, then Y = p).
    let p = unhex(P)?;
    let mut big_x = vec![4u8];
    big_x.extend_from_slice(&p);
    big_x.extend_from_slice(key.get(49..).ok_or("y")?);
    expect("X = p", verify(&digest, &r, &s, &big_x), false)?;
    let mut big_y = key.get(..49).ok_or("x")?.to_vec();
    big_y.extend_from_slice(&p);
    expect("Y = p", verify(&digest, &r, &s, &big_y), false)?;
    Ok(())
}

#[test]
#[cfg_attr(
    miri,
    ignore = "a verification is about 1,150 group operations, too slow under Miri"
)]
fn a_signature_does_not_verify_under_another_key() -> TestResult {
    let v = first(VALID)?;
    let (_, digest, r, s) = decode(v)?;
    let other = vector(VALID, 5)?;
    let (other_key, _, _, _) = decode(other)?;
    expect("another key", verify(&digest, &r, &s, &other_key), false)
}

/// Not an assertion about speed: it prints how long one verification takes
/// (`cargo test -p clazel-p384 --test verify timing -- --nocapture`).
#[test]
#[cfg_attr(
    miri,
    ignore = "a verification is about 1,150 group operations, too slow under Miri"
)]
fn timing() -> TestResult {
    let v = first(VALID)?;
    let (key, digest, r, s) = decode(v)?;
    let start = Instant::now();
    let runs = 3;
    for _ in 0..runs {
        expect("tcId 1", verify(&digest, &r, &s, &key), true)?;
    }
    eprintln!(
        "verify: {:?} per verification (mean of {runs})",
        start.elapsed() / runs
    );
    Ok(())
}

# clazel-crypto

The libcrux providers for `clazel-tls`'s cryptographic parameters (Phase 3
item 3.5f).

`clazel-tls` is proven over abstract providers: its key schedule, record
epochs and key exchange take the cryptography as trait parameters. This crate
instantiates them with [libcrux](https://github.com/cryspen/libcrux), whose
crates used here carry the `verified-hacl` badge (safe Rust compiled from
HACL\* code that is proven memory safe, functionally correct and secret
independent). Its own code is the adapters, which Verus checks against
`clazel-tls`'s provider contracts.

| `clazel-tls` parameter | Standard | libcrux call |
|---|---|---|
| `schedule::crypto::Crypto::hash` | SHA-256, FIPS 180-4 | `libcrux_sha2::sha256` |
| `Crypto::hmac` | HMAC-SHA256, RFC 2104 | `libcrux_hmac::hmac_sha2_256` |
| `Crypto::extract` | HKDF-Extract, RFC 5869 §2.2 | `libcrux_hkdf::sha2_256::extract` |
| `Crypto::expand` | HKDF-Expand, RFC 5869 §2.3 | `libcrux_hkdf::sha2_256::expand` |
| `traffic::provider::Factory` and `record::Aead` | ChaCha20-Poly1305, RFC 8439 §2.8 | `libcrux_chacha20poly1305::{encrypt, decrypt}` |
| `hello::key_exchange::KeyExchange` | X25519, RFC 7748 | `libcrux_curve25519::{secret_to_public, ecdh}` |
| `auth::spec::Verification::signature` (CertificateVerify), as `signature::verify` | ecdsa_secp256r1_sha256, rsa_pss_rsae_sha256/384/512, ed25519 (RFC 8446 §4.2.3) | `libcrux_ecdsa::p256::verify`, `libcrux_rsa::verify`, `libcrux_ed25519::verify` |
| Finished comparison (`Verifier::finished_equal`), as `compare::constant_time_eq` | RFC 8446 §4.4.4 | none: ours, proven, no data-dependent branch |

## The trust boundary

Every libcrux call is one axiom in `src/axioms.rs`: an `external_body`
wrapper whose `ensures` says only what libcrux documents. The output is the
uninterpreted function of `src/spec.rs` applied to exactly these inputs,
with the documented output length. There is also one proof axiom: the
ChaCha20-Poly1305 tag is 16 octets. That libcrux computes the standard's
function is HACL\*'s proof, recorded in docs/VERIFICATION.md's TCB, and is
never assumed here. A session other than the one that changed
`src/axioms.rs` reviews each change to it.

Modelling choices:
- **Oversized inputs abort.** libcrux refuses, or panics on, inputs at or
  near `u32::MAX` octets, and HACL\*'s preconditions stop just short of it.
  Each wrapper checks every variable-length input against `MAX_INPUT`
  (2^32 - 256 octets) first and aborts the process above it, so it never
  returns a value no axiom covers and never unwinds. No caller in this
  browser comes near that size.
- **X25519 refuses an all-zero result.** libcrux's `ecdh` already does this
  (RFC 7748 §6.1). `clazel-tls` also checks it (RFC 8446 §7.4.2).
- **The SHA-3 crates are compiled but never called.** `libcrux-hmac` 0.0.9
  depends on `libcrux-sha3` (pre-verification) for its HMAC-SHA3 types,
  which brings `libcrux-intrinsics` and `libcrux-platform`, both with
  `unsafe`. The HMAC-SHA256 path calls only `libcrux-sha2`. The choice was
  made on 2026-10-26; see docs/DEPENDENCIES.md.

## Signature verification

`signature::verify(key, scheme, input, signature)` is proven equal to
`signature_spec::verify`. The end-entity key is its DER SubjectPublicKeyInfo,
parsed by `clazel-x509`, and an ECDSA signature's Ecdsa-Sig-Value is parsed by
`clazel-der`. Only the three verifications are libcrux's. What it accepts, and
everything it refuses, is listed at the top of `src/signature_spec.rs`: the
secp256r1 uncompressed point only, RSA keys with e = 65537 and a modulus of
exactly 2048/3072/4096/6144/8192 bits, and Ed25519 keys without parameters.
The `rsa_pss_pss_*` schemes are neither offered nor verified.

Tests use RFC 8032 §7.1 (Ed25519) and RFC 6979 A.2.5 (ECDSA P-256)
vectors, and our own RSA-PSS fixtures in `tests/fixtures/rsa-pss` (see the
`SOURCE.md` there).

## Not here
- The `auth::verify::Verifier` implementation itself. Its `chain` half is
  certificate path validation (3.5b). Certificate signatures (RSA PKCS#1
  v1.5 from `clazel-pkcs1`, and ECDSA with SHA-384) come with it.
- Randomness: the caller supplies the X25519 private scalar.
- Any side-channel claim beyond HACL\*'s. libcrux's README makes none for the
  extracted Rust, and this crate adds no secret-dependent branches.

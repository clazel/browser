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
| `auth::spec::Verification::signature` (CertificateVerify), as `signature::exec::verify` | ecdsa_secp256r1_sha256, rsa_pss_rsae_sha256/384/512, ed25519 (RFC 8446 §4.2.3) | `libcrux_ecdsa::p256::verify`, `libcrux_rsa::verify`, `libcrux_ed25519::verify` |
| `clazel_x509::path::contract::LinkVerifier` (certificate-chain links), as `chain::exec::CertificateLinks` | sha256/384/512WithRSAEncryption (RFC 4055 §5, RFC 8017 §8.2.2), ecdsa-with-SHA256/384 under P-256 (RFC 5758 §3.2) | `libcrux_sha2::{sha256, sha384, sha512}` for the RSA digests, then `clazel-pkcs1` (ours); `libcrux_ecdsa::p256::verify` |
| Finished comparison (`Verifier::finished_equal`), as `compare::constant_time_eq` | RFC 8446 §4.4.4 | none: ours, proven, no data-dependent branch |

## The trust boundary

Every libcrux call is one axiom in `src/axioms.rs`: an `external_body`
wrapper whose `ensures` says only what libcrux documents. The output is the
uninterpreted function of `src/spec.rs` applied to exactly these inputs,
with the documented output length. There is also one proof axiom: the
ChaCha20-Poly1305 tag is 16 octets. Three of the calls (SHA-384, SHA-512 and
ECDSA P-256 with SHA-384) serve only certificate-chain links. That libcrux computes the standard's
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

`signature::exec::verify(key, scheme, input, signature)` is proven equal to
`signature::spec::verify`. The end-entity key is its DER SubjectPublicKeyInfo,
parsed by `clazel-x509`, and an ECDSA signature's Ecdsa-Sig-Value is parsed by
`clazel-der`. Only the three verifications are libcrux's. What it accepts, and
everything it refuses, is listed at the top of `src/signature/spec.rs`: the
secp256r1 uncompressed point only, RSA keys with e = 65537 and a modulus of
exactly 2048/3072/4096/6144/8192 bits, and Ed25519 keys without parameters.
The `rsa_pss_pss_*` schemes are neither offered nor verified.

Tests use RFC 8032 §7.1 (Ed25519) and RFC 6979 A.2.5 (ECDSA P-256)
vectors, and our own RSA-PSS fixtures in `tests/fixtures/rsa-pss` (see the
`SOURCE.md` there).

## Certificate-chain links

`chain::exec::CertificateLinks` is the production `LinkVerifier` that
`clazel-x509`'s RFC 5280 §6.1 path validation takes as a parameter
(path-validation design P11). Its `verify` is proven equal to
`chain::spec::link`, whose header lists the profile and every refusal:
RSA PKCS#1 v1.5 with SHA-256/384/512 (modulus 2048 to 8192 bits, exponent
odd and below 2^33) and ECDSA P-256 with SHA-256 or SHA-384; RSA-PSS,
Ed25519, SHA-1, P-521 and, until P17, P-384 issuer keys are refused.
`chain::lemmas::lemma_thm_production_links_verify` composes `clazel-x509`'s
`thm_links_verify` with it: every link of an accepted path is one of those
verifications, on the certificate's exact TBS octets.

Tests: our own certificates in `tests/fixtures/chain` (see `SOURCE.md`),
the self-signatures of Mozilla's 118 roots, and x509-limbo chains in
limbo's order through `clazel-x509`'s candidate verdict
(`tests/chain_limbo.rs`).

## The chain validation and the end-to-end test

`join::exec::ChainVerifier` is the production `auth::verify::Verifier`
(path-validation P9 and P16): `clazel-x509`'s chain search with the links of
`chain`, CertificateVerify by `signature` and Finished by `compare`. Its
trust anchors are a parameter (`ChainVerifier::new(&[Root])`);
`join::exec::mozilla()` passes `clazel_x509::roots::ROOTS`, the only
production use.

`tests/conformance_tls.rs` runs our client against a real server for the first
time (phase-3.md 3.5g, first part). The client is `Bootstrap`,
`Established::into_record_auth` and `Connection` over this crate's providers
and `ChainVerifier` with the test root of `tests/fixtures/tls` as its only
anchor. The server is rustls 0.23.46 (ring provider; a `test` dependency, no
new package) limited to TLS 1.3, `TLS_CHACHA20_POLY1305_SHA256` and X25519, in
the same process, over an in-memory byte pipe. It checks:

- a full handshake for an ECDSA P-256 chain and for an RSA chain (leaf signed
  by PKCS#1 v1.5 SHA-256, CertificateVerify in RSA-PSS), then application
  data both ways (several records, so the sequence numbers advance), a client
  KeyUpdate and close_notify both ways;
- hostile servers, each ending in the dispatcher's `Fail` with the RFC 8446
  §6.2 alert and no panic: a wrong `Finished` and a wrong CertificateVerify
  (decrypt_error), a certificate for another name (bad_certificate), an
  expired leaf (bad_certificate, by `join::spec::certificate_error`'s design)
  and an expired intermediate (certificate_expired), a self-signed leaf and a
  missing intermediate (unknown_ca), an empty trust store, records over the
  limit (record_overflow), a TLS 1.2 ServerHello with and without the
  downgrade sentinel (protocol_version), and `change_cipher_spec` in the wrong
  place (unexpected_message). The hostile flights are the real rustls flight,
  decrypted with the handshake keys, changed in one place and re-encrypted
  ("scripted server"); an unchanged flight completes the handshake.

Randomness in that test (the client's X25519 scalar, ClientHello random and
legacy_session_id, and the server's scalar) is a fixed test seed through
SHA-256: test-only. The test is `#![cfg(not(miri))]` (ring is C and assembly).

## Not here
- Randomness: the caller supplies the X25519 private scalar and the
  ClientHello random and session id. A source needs `clazel-sys`.
- Any socket I/O, the TLS loop in `clazel-net`, `tls: true` in the fetch
  transducer and the kernel's `https:` path (phase-3.md 3.6 to 3.8).
- A measurement against public servers (3.5g's local item) and the
  real-certificate corpus: not run, no result claimed.
- Any side-channel claim beyond HACL\*'s. libcrux's README makes none for the
  extracted Rust, and this crate adds no secret-dependent branches.

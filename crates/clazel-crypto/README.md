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
  limit (record_overflow), a TLS 1.2 ServerHello without the RFC 8446
  §4.1.3 downgrade sentinel (protocol_version) and with either sentinel
  (illegal_parameter), and `change_cipher_spec` in the wrong
  place (unexpected_message). The hostile flights are the real rustls flight,
  decrypted with the handshake keys, changed in one place and re-encrypted
  ("scripted server"); an unchanged flight completes the handshake.

Randomness in that test (the client's X25519 scalar, ClientHello random and
legacy_session_id, and the server's scalar) is a fixed test seed through
SHA-256: test-only. The test is `#![cfg(not(miri))]` (ring is C and assembly).

## The client driver

`client::Client` is the socket-free TLS 1.3 client that the network shell
drives (phase-3.md 3.5f, "the `clazel-tls` public API the shell drives"). It
owns `Bootstrap`, the key exchange handoff (`traffic::handshake::start`, what
`Established::into_record_auth` calls) and `Connection`, with this crate's
providers and a `ChainVerifier`, and it carries no I/O, clock or randomness of
its own:

- `Client::connect(host, now, verifier, random) -> (Client, Output)`: `random`
  is a caller-supplied `&mut dyn FnMut(&mut [u8])`, called three times for 32
  octets each (the X25519 scalar, the ClientHello random, the
  legacy_session_id). The output's `send` is the ClientHello record.
- `receive(octets)`, `receive_eof()`, `send(data)` (records of at most 2^14
  octets; `Err(NotOpen)` unless `Open`) and `close()` each return an `Output`:
  octets to send, plaintext delivered and the `State`.
- `State`: `Handshaking`, `Open`, `Closing` (our close_notify sent), `Closed`,
  `Failed(Failure { alert, origin })`, where `alert` is the RFC 8446 §6.2
  description and `origin` is `Sent` (the client's alert is the last record
  in `send`), `NotSent` (a local failure with no key to seal the alert
  under), `Peer` (the server's alert, never answered) or `Truncated` (end of
  stream before close_notify).

Alerts: before the handshake keys `Bootstrap` puts none on the wire, so the
driver writes a plaintext fatal alert. From the ServerHello on, `Connection`
(in `clazel-tls`) seals the fatal alert of a local failure itself, under the
write epoch the server reads next (the client handshake epoch during the
server's flight, the client application epoch after the client Finished) at
its next sequence number, before it drops its keys, and returns it in
`Fail(description, Some(record))`; the driver sends that record and holds no
key of its own. `Connection` reports a fatal alert from the server as
`PeerAlert(description)`, which is not answered. When `Connection` holds no
settled write epoch (our close_notify already sealed, a failed or spent
epoch) the failure is `NotSent`. The server's close_notify is answered with
ours after the handshake; during the server's flight a close_notify from the
server, or `close()`, ends the connection without one, since `Connection`
seals only fatal alerts there. Before the ServerHello `close()` sends a
plaintext close_notify.

The driver is plain safe Rust outside `verus!` (tier 0, shell glue). Its tests
are in `src/client.rs` (bytes that are not TLS, a plaintext alert, close_notify
and end of stream before the ServerHello) and `tests/client.rs`, against the
same rustls server as `tests/conformance_tls.rs` with ring's own X25519:
handshakes for the ECDSA and the RSA chain, a request, a 40000-octet response,
a 20000-octet upload, close_notify both ways; the server's close_notify
answered; another name (bad_certificate) and an empty trust store
(unknown_ca), each alert sealed and read by rustls; after the handshake, a
server record that fails to decrypt, answered with bad_record_mac sealed under
the application key and read by rustls, and a server alert, not answered;
truncation after the handshake. `tests/conformance_tls.rs` still assembles
the client by hand and should move to this driver.

## Not here
- Randomness: the caller supplies it (`Client::connect`'s `random`). The
  production source is in `clazel-net`: `TlsConnection::open` draws from
  `clazel_sys::fill_random` (audited, `docs/SYS-AUDITS.md`). Tests here use
  a fixed seed through SHA-256.
- Socket I/O: `clazel-net`'s `TlsConnection` runs the driver over TCP. Not
  yet used by `clazel-fetch` (`tls: true` in its transducer), the kernel's
  `https:` path or `clazel fetch https://` (phase-3.md 3.6 to 3.8).
- A close_notify during the server's protected flight (see "The client
  driver"): `Connection` seals only fatal alerts there.
- A measurement against public servers (3.5g's local item) and the
  real-certificate corpus: not run, no result claimed.
- Any side-channel claim beyond HACL\*'s. libcrux's README makes none for the
  extracted Rust, and this crate adds no secret-dependent branches.

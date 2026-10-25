# clazel-tls

The TLS 1.3 record layer and handshake message formats of RFC 8446, as
bytes in and bytes out: the presentation language, records, handshake
messages, extensions and alerts. Part of [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs.

This covers phase-3.md item 3.5d and the SHA-256 key schedule from 3.5e.
The initial Hello/authentication flow is built over explicit validator,
key-exchange and crypto parameters for the fixed TLS 1.3/X25519/ChaCha20-Poly1305
profile. **Protected record I/O, entropy sourcing and the production
cryptography provider (items 3.5e and 3.5f) remain**, as does
X.509 certificate interpretation and validation (3.5b). The crate stays at
`tier = 0` with `target-tier = 2` until they are, and until CI's full run
has checked every proof, mutation and conformance test on a pull request;
what is proven today is stated below, not implied by the tier.

## What it is

- **Presentation language** (RFC 8446 §3, `reader`, `writer`): fixed-length
  vectors, variable-length vectors with a 1-, 2- or 3-byte length field
  chosen from the ceiling and checked against the floor and ceiling,
  `uint8` to `uint32`, enums as numbers, and lists that must end exactly
  where their bytes do. Every message is a chain of these.
- **Records** (§5, `record`, `reassemble`): `read_record` takes bytes off a
  stream and answers "need more", an error with its alert, or a record;
  `TLSPlaintext` (content type, `legacy_record_version`, the 2^14 limit),
  `TLSCiphertext` (the 2^14 + 256 limit, and the header that is the AEAD's
  additional data), `TLSInnerPlaintext` (padding removed from the end, an
  all-zero plaintext refused), the per-record nonce (the sequence number
  XORed into the IV), the unprotected change_cipher_spec of the middlebox
  compatibility mode, and `encrypt_record` and `decrypt_record` over an
  `Aead` trait that the cryptography (item 3.5f) implements. The reassembler
  turns records into whole handshake messages (coalesced, fragmented, never
  interleaved with another content type, no zero-length fragment) in a
  buffer bounded by 2^14 + 4 + 2^18 bytes.
- **Handshake messages** (§4, `handshake`, `encode`): ClientHello,
  ServerHello and HelloRetryRequest (recognised by its fixed `Random`),
  EncryptedExtensions, CertificateRequest (read so it can be refused),
  Certificate (entries as opaque DER), CertificateVerify, Finished,
  NewSessionTicket (read, then ignored: no resumption in this phase),
  EndOfEarlyData, KeyUpdate. An unknown handshake type is an error.
  ClientHello, Finished, KeyUpdate, the empty Certificate that refuses a
  CertificateRequest, and alerts can be written; the others can be written
  too, which the tests use.
- **Extensions** (§4.2, `extension`): the table of which extension may
  appear in which message as a function, duplicates refused, and the
  typed bodies of `supported_versions`, `cookie`, `signature_algorithms`
  (and `_cert`), `supported_groups`, `key_share` (ClientHello,
  HelloRetryRequest and ServerHello forms) and `server_name`; every other
  extension is `opaque` with its type kept.
- **Alerts** (§6): `AlertLevel`, `AlertDescription` and the mapping from
  each error (`ErrKind`) to the alert §6.2 names for it. Every reader
  returns a typed error that carries it.

- **Key schedule** (§7.1–§7.3, §4.4.4, `schedule`): HkdfLabel encoding,
  HKDF-Expand-Label and Derive-Secret, early/handshake/master secrets for
  a non-PSK SHA-256 handshake, client/server traffic-secret labels,
  Finished verify_data, traffic-secret updates, and ChaCha20's write key
  and IV. The `Crypto` trait supplies SHA-256, HKDF and HMAC. Each executable
  function is proven equal to its equation over those parameters, without
  axioms. This does not prove a provider correct or enforce transcript
  boundaries: the handshake state machine must supply the right messages,
  including the HelloRetryRequest transcript transformation.

  `tests/conformance_key_schedule.rs` checks 40 RFC 8448 §3/§5 operations
  through the proven code, with a test-only RFC 5869 provider over
  RustCrypto SHA-256 (itself checked against RFC 5869 Appendix A.1).
  The RFC traces select AES-128-GCM/SHA-256; their 16-byte key vectors test
  generic Expand-Label, while the 32-byte ChaCha20 key and update helpers
  have separate checks. These tests exercise the key schedule, not a TLS
  handshake implementation. `schedule/examples.rs` adds concrete tagged
  argument-routing witnesses and ASCII-label witnesses for 19 mutations.

- **Transcript construction** (§4.4.1, `transcript`): retain handshake
  headers and bodies, replace ClientHello1 with the synthetic message_hash
  on HelloRetryRequest, require a second ClientHello before the final
  ServerHello, and reject subsequent retries. The refinement proof also
  establishes a 4 MiB retained-byte bound and that rejection leaves the
  accumulator unchanged. The caller supplies already classified bodies;
  this is not the complete handshake or authentication state machine.
  The CertificateVerify input builder (§4.4.3) produces the 64-byte pad,
  the server/client context string, the separator and transcript hash.
  RFC 8448 §3/§5 tests now construct live transcripts from 16 handshake
  messages, checking 12 hash/Finished checkpoints against the existing
  official vectors. RFC 8446's explicit signature-input example also passes.

- **Initial authentication** (§4.3–§4.4, `auth`): after final ServerHello,
  own the transcript through EncryptedExtensions, optional CertificateRequest,
  mandatory nonempty Certificate, CertificateVerify and server Finished.
  Chain validation receives the captured host, time and certificate body;
  the returned leaf key is used for the offered TLS 1.3 signature scheme and
  the server-context transcript input. Finished uses the server handshake
  secret and the transcript before that message. Only then is the client
  Finished emitted (preceded by an empty Certificate when requested).
  Application delivery waits for acknowledgement of that exact client flight.

  All executable handlers refine the pure transducer. Trace theorems prove
  the application gate and terminal-state absorption; binding lemmas state
  the exact chain, signature and Finished inputs. Eight input-sensitive
  mock-provider tests check these decisions, including distinct handshake
  secrets, typed alerts, transcript checkpoints and rejection ordering; all
  eight pass under Miri. They do not establish real X.509/signature correctness.
  EE support is limited to server_name/supported_groups responses to actual
  offers; no PSK, early data or ALPN. The Hello join supplies the
  negotiated secrets and actual offers; the future record loop supplies
  complete authenticated bodies. Production Finished comparison must use a
  timing-safe provider; the functional proof makes no timing guarantee.

- **Server selection** (§4.1.3–§4.2.8, `hello`): accept only TLS 1.3,
  TLS_CHACHA20_POLY1305_SHA256 and a 32-byte X25519 peer share, with the
  exact offered session ID echoed. `supported_versions` determines the
  version; `legacy_version` is ignored as §4.2.1 requires. Unknown unoffered
  responses fail. The profile already sends an X25519 share, so HRR may
  request a cookie but cannot request an existing or unoffered group.
  A second retry and a no-op retry fail; accepted cookie extension_data is
  returned verbatim. Eight hand-built tests pass under Miri. This stateless
  component receives the actual session/retry state from `client::Hello`.
- **Owned Hello exchange** (§4.1.2/§4.1.4/§4.4.1, `hello::client`):
  generate ClientHello from captured host/time, caller entropy and public share;
  retain exactly its transcript; validate server selections against retained
  session/retry state; and build ClientHello2 with only the exact cookie
  extension added. The 4098-byte cookie extension_data cap is a resource policy.
  Four tests pass under Miri, including unchanged offers and the complete
  message_hash/HRR/CH2/final-SH transcript. The caller classifies DNS versus
  IP hosts for SNI and implements record-level send ordering/compatibility CCS.
- **Hello-to-authentication join** (§7.1/§7.4.2, `hello::join`): verify the
  borrowed private scalar derives the public share actually sent, call the
  key-exchange provider with that scalar and exact peer share, reject provider
  failure/all-zero shared secrets, derive both handshake traffic secrets over
  the final-SH transcript, and transfer captured host/time/offers/transcript
  into authentication. Return the master secret for later application keys.
  Six input-sensitive mock-provider tests pass under Miri, including a complete
  mock authentication flight through both Finished messages. They assert actual
  chain and signature inputs and independently compute the joined traffic secrets.
  They do not establish real X25519/HKDF/HMAC/X.509/signature correctness.
  The caller retains private-scalar ownership; no erasure or timing guarantee
  is established. Production providers and entropy sourcing remain absent.

Out of scope: protected record I/O and post-handshake dispatch (Appendix A), the
production cryptography, the contents of a certificate, `pre_shared_key` and the other
extensions kept opaque (their data is not read), client certificates (a
CertificateRequest is read and then refused by sending an empty
Certificate), and any use of the network.

## Verification

Tier 0, target tier 2. The current numbers are in the
[status table](../../README.md#verification-status).

- **Proven (Verus, `cargo verus verify`: 595 verified, 0 errors):** the
  executable functions of `reader`, `writer`, `record`, `reassemble`,
  `extension`, `handshake` and `encode` meet the contracts in
  `contract.rs`, which are the spec's functions in `spec.rs`. About the
  spec itself (`lemmas_*.rs`): serialize then parse gives back every
  message the client sends (ClientHello, Finished, KeyUpdate, the empty
  Certificate) and the record header, and what a reader accepts is
  exactly what the writer writes, so no two byte strings give the same
  message; no over-read (a reader's result depends only on the bytes it
  consumed); bounded reservation (a list never has more elements than
  bytes; an extension block at most a quarter as many); the reassembler's
  buffer never reaches its bound, never loses or invents a byte, and
  emits a message only when all its bytes have arrived (on every proper
  prefix of a message it emits nothing); every proper prefix of a record
  is "need more"; the nonce of sequence number 0 is the IV and distinct
  sequence numbers give distinct nonces; protecting a record and reading
  it back gives the record, if the AEAD opens what it seals. The §4.2
  table has one concrete lemma per row (`examples.rs`, `lemma_ext_row_*`).
  `schedule` and `transcript` refine their own specs and contracts;
  transcript lemmas prove exact append/retry encodings and that a retry
  cannot be accepted twice. These properties do not establish peer authentication.
- **Independent transcription:** `independent.rs` is RFC 8446 Appendix B
  as a grammar of generated byte strings, proven to accept exactly what
  the prose parsers accept, for ClientHello, ServerHello,
  EncryptedExtensions, CertificateRequest, CertificateVerify,
  NewSessionTicket, Finished, KeyUpdate, Alert, the `Handshake` and
  `TLSPlaintext` frames and the extension bodies (the class is stated at
  the top of the file; `Certificate` is outside it). **It was written
  after `spec.rs` in the same session, not before, and not hidden from
  it**, so it is weaker evidence than a second author's text read first.
- **Mutations:** `mutations.json` lists 151 deliberate breaks: 76 for
  formats, 19 for the key schedule, 17 for transcript construction and 17
  for authentication, 10 for server selection and 12 for ClientHello/key handoff.
  All 129 certificates through authentication passed locally and in CI.
  Additional certificate checks use isolated copies: each theorem must fail
  on its mutant, and its certificate must verify on the mutant and fail on
  the original. The full expanded run remains required.
  Each `killed` entry requires a certificate that Verus checks; the
  certificate must pass on the mutant and fail on the real spec.
  Full workspace and CI verification remain required before tier promotion.
- **Conformance** (`tests/conformance_tls_formats.rs`, through the proven
  code): RFC 8448 sections 3 to 7: all 40 handshake messages (39 read and
  written back byte for byte, one expected failure: a ClientHello shown
  before its PSK binders, a prefix of the 512-octet message that follows
  it), all 41 records (each read, written back, its encrypted header
  checked to be the additional data, its inner plaintext read, every
  proper prefix "need more"), and the 24 handshake payloads through the
  reassembler in fragments of 1, 2, 7, 100 and 16384 bytes. 68
  hand-built cases, one or more per error rule, each with the alert it
  names. A differential against rustls 0.23.46 (`rustls::internal::msgs`:
  rustls exposes `MessagePayload::new`, the fragmenter and the number
  enums, not its handshake types): the numbers of every enum we define; all
  65536 two-byte alerts and every one-byte change_cipher_spec; RFC 8448
  payloads cut into records by rustls's fragmenter at seven sizes and
  read back here; and the acceptance of 16040 handshake messages (the 40
  of RFC 8448 and 400 mutations of each). Where we reject and rustls
  accepts, or the reverse, the difference is classified in the test:
  rules about meaning that rustls applies later (duplicate extensions,
  an extension in the wrong message), the data of extensions this crate
  reads while rustls keeps them opaque, the extension block floors of
  Appendix B and the Finished length, which rustls does not enforce, and
  extensions rustls refuses in a ServerHello or HelloRetryRequest as not
  offered (this crate leaves that to item 3.5e). 83 of the 16040 are such
  differences; no other was found.
- **Modelling choices** (listed at the top of `src/spec.rs`, with their
  numbers): a reader returns what is left; failure is `None` or an
  `ErrKind`; the AEAD is a parameter; a handshake message body is at most
  2^18 octets (the standard allows 2^24 - 1); `legacy_record_version` must
  be 0x0303, or 0x0301 on an unprotected record, although §5.1 says to
  ignore it; unknown record and handshake types are errors; a type that
  is not a row of the §4.2 table passes it (the handshake refuses one that
  was not offered); `legacy_version` is read, not checked.

## Trust

The proofs assume the Rust compiler, Verus and its solver, the `vstd`
library, and that the spec transcribes the standard; the conformance
tests, the independent transcription and the mutations are the checks on
that last point, not proofs. The `Aead` trait is the boundary to the
cryptography: its methods are specified, not implemented, here. The full
list is in [docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false`). The reassembler and
the record reader are meant to be driven by the handshake state machine of
item 3.5e:

```rust
use clazel_tls::reassemble::{Event, Reassembler};
use clazel_tls::record::{Frame, ReadOut, read_record};
use clazel_tls::handshake::parse_handshake;

// Unprotected records, as at the start of a handshake.
let mut input: &[u8] = bytes_from_the_socket;
let mut reasm = Reassembler::new();
loop {
    match read_record(input, false) {
        ReadOut::NeedMore => break,                       // read more bytes
        ReadOut::Fail(kind) => return Err(kind),           // send the alert
        ReadOut::Done(Frame::Plain(ctype, fragment), rest) => {
            if let Ok(Event::Messages(messages)) = reasm.feed_record(ctype, fragment) {
                for m in &messages {
                    let msg = parse_handshake(m, 32)?;     // 32: the SHA-256 length
                }
            }
            input = rest;
        }
        ReadOut::Done(Frame::Ccs, rest) => input = rest,   // dropped, section 5
        ReadOut::Done(Frame::Protected(header, body), rest) => {
            // decrypt_record(&aead, &iv, seqno, header, body), then feed the result
            input = rest;
        }
    }
}
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.

# Phase 3: Networking, detailed plan

**Goal:** the kernel fetches documents from the network. Every byte that
arrives from a server is parsed by proven code: HTTP/1.1 (RFC 9110 and
RFC 9112), DNS messages (RFC 1035), and TLS as decided in 3.0. Every parser
and every decision (what request to send, which cookies to attach, whether
to follow a redirect) is a pure function or a pure state machine proven in
Verus; the sockets, timers and threads around them are a short Tier 0
shell whose line count the README reports, as for the Phase 2 host shell.

*Exit:* a verified `curl` clone: `cargo run -p clazel -- fetch URL` resolves
the host, connects, speaks TLS, sends the request, and prints the status
line, the fields and the body, with every parser on that path at tier 2.

Nothing in this phase renders anything. The body is bytes; HTML is Phase 4.

## Exit criteria

Phase 3 is done when all of these hold on macOS arm64 and Linux x86-64:

1. `clazel-http`, `clazel-dns` and `clazel-fetch` are at **tier 2**,
   accepted by `cargo xtask check` (every mutation a certified `killed`,
   conformance tests, an independent transcription each), and the TLS
   crate is at the tier 3.0 decides.
2. `cargo run -p clazel -- fetch https://example.com/` prints the response
   of a real server, through the proven DNS, TLS, HTTP and client code and
   the network shell only. `fetch` follows redirects and stores and sends
   cookies through the Phase 2 jar: the `http-state` parser corpus (222
   rows) passes over a real socket against an in-process server (3.8), and
   the WPT `cookies/` tests that needed a server in Phase 2 run the same way.
3. `clazel-fetch` proves `theorem_wire_cookies` (3.6): the only bytes derived
   from the cookie jar that reach the wire for a request to host *h* are the
   cookie string RFC 6265bis §5.8 retrieves for that request; and
   `clazel-kernel`'s Phase 2 theorems still hold with network events (3.7).
4. `scripts/verify.sh` exits 0, with the README table showing the new rows
   and the network shell's line count.
5. CLAUDE.md, VERIFICATION.md, DEPENDENCIES.md and the checker match the
   TLS decision recorded in 3.0.
6. A certificate on the pushed revocation set is refused (3.5h), and the
   cookie jar, `localStorage`, the history and the revocation set survive
   a restart through the proven store (3.10), whose recovery theorem holds
   for a write cut off at any octet. Added 2026-11-03; `localStorage` and
   recovery added the same day when 3.10 became generic storage.

## What is proven, and what is assumed

1. **Proven (Verus):** response parsing and request serialization
   (`clazel-http`), chunked decoding, DNS message encoding and decoding,
   the client state machine from a URL to the request bytes and from the
   response bytes to a result (`clazel-fetch`), including redirects and the
   cookie steps; and, per 3.0, the TLS record and handshake parsers.
2. **Small and unproven (Tier 0, listed in the TCB):** the network shell:
   UDP to the resolver, TCP, the TLS I/O loop, timeouts. Its one security
   duty is to carry bytes between the right socket and the right state
   machine, and never to look inside them. It never touches the cookie jar:
   the `Cookie` header arrives in the request bytes the proven code built.
3. **Assumed (TCB):** the OS, the cryptography library, and whatever 3.0
   adds (a TLS library, or nothing).

Not covered by any theorem, and said so: timing, resource exhaustion, and
everything outside the phase: HTTP/2 and HTTP/3, caching (RFC 9111),
proxies, HSTS, authentication, compression (the client sends no
`Accept-Encoding`, so a conforming server sends identity), `Upgrade`,
EDNS(0), DNSSEC, DNS over TLS or HTTPS, and IPv6 happy eyeballs (the shell
tries addresses in order).

## Crates

| Crate | Tier (target) | Standard | Contents |
|-------|---------------|----------|----------|
| `clazel-http` | 2 | RFC 9110 §5, §8.6, §10.2.2; RFC 9112 §2 to §7 | field syntax, message framing, chunked coding, request serialization |
| `clazel-dns` | 2 | RFC 1035 §2.3, §3, §4; RFC 1034 §3.6.2; RFC 3596 | message format, name compression, query building, answer extraction |
| `clazel-der` | 2 | ITU-T X.690 §8, §10 | DER decoding and the few encodings we write |
| `clazel-x509` | 2 | RFC 5280 §4, §6.1, §7.1; RFC 9525 §6 | certificates, extensions, path validation, host names, the Mozilla root table |
| `clazel-pkcs1` | 2 | RFC 8017 §4, §5.2.2, §8.2.2, §9.2 | RSA PKCS#1 v1.5 signature verification and the multiple-precision arithmetic it needs |
| `clazel-tls` | 2 | RFC 8446 §3 to §7, Appendix A.1; RFC 6066 §3 | record layer, handshake messages, key schedule, the client state machine, joined to libcrux |
| `clazel-fetch` | 2 | (ours); Fetch §4.4 to §4.6 in part; RFC 6265bis §5.2, §5.3, §5.7, §5.8 HTTP parts; RFC 9110 §15.4 | the client state machine: URL to request, response to result, redirects, cookies |
| `clazel-net` | 0 | — | the network shell: resolver, TCP, TLS I/O; counted like the host shell |
| `clazel-store-shell` | 0 | — | the store's shell: its files, lock, syncs and renames; counted like the host shell |
| (decided in 3.10a.0) | 2 | WHATWG Storage §4, §6; records ours or DER (X.690) through `clazel-der` | the generic store: an ordered key–value store with transactions and a proven recovery, holding the cookie jar, `localStorage`, history and revocation set first (3.10) |
| `clazel-crlite` | 2 | CRLite, as a pinned `clubcard-crlite` version encodes it (3.5h.0) | the revocation set's parser, its signed records (with their JSON) and the revocation oracle (3.5h) |

Section numbers are from the documents at the time of writing; each spec
header pins the exact RFC or commit it transcribes.

Each Tier 2 crate starts as `tier = 0, target-tier = 2`. `clazel-net` is
Tier 0 because it does I/O; the plan keeps every decision out of it.

## Dependencies on Phase 2

Phase 2 is merged; its remaining open point (2.16 on Linux and CI) does not
block anything here. Used: `clazel-url` (the request target, `Host`, and
resolving `Location`), `clazel-cookie` (storage and retrieval with the
HTTP request contexts Phase 2 left abstract: the table in phase-2.md item
2.9 lists which parts of RFC 6265bis are this phase's), `clazel-origin`
(same-site for redirect chains), `clazel-psl` (through `clazel-cookie`),
`clazel-kernel` (3.7 adds network events to the step function) and the host
shell `clazel` (3.8 adds the network thread).

As in Phase 2, each crate is written against abstract records first and
joined to the real functions last: `clazel-fetch` takes the HTTP parser and
the URL functions as parameters, exactly as the kernel took `UrlFns`, so its
proofs do not wait for 3.2 and its theorem is stated once.

## Work items

Ordered by dependency. Size: S is under a day, M a few days, L a week or
more. Each item follows CLAUDE.md rule 3: spec and contracts in one commit,
then the implementation and proof. Items marked **waits on 3.0** must not
start before the maintainer's decision is recorded there.

### 3.0 The TLS decision (S)

The roadmap says "TLS via rustls with verified crypto", and CLAUDE.md rule 8
says shipped dependencies are allowed only for cryptography from verified
libraries, OS and windowing bindings, and GPU access. rustls is a parser of
untrusted bytes (records, handshake messages, certificates), so the two
conflict, and the maintainer must choose. The facts below were checked on
2026-10-23 against the sources cited; "unverified" marks what could not be
checked. Dependency counts are `cargo tree --edges normal` (and, where
stated, `--edges normal,build`) on a scratch crate outside the repository,
counting packages other than the scratch crate, on macOS arm64 with
cargo 1.98.1.

#### Checked facts

**rustls and its two parsers.** The newest stable `rustls` on crates.io is
0.23.46 (2026-10-14); 0.24.0-dev.2 was published the same day and is not
stable ([crates.io/crates/rustls](https://crates.io/crates/rustls)). With
`default-features = false` it has seven packages: `rustls` 0.23.46,
`rustls-webpki` 0.103.16, `rustls-pki-types` 1.15.1, `subtle` 2.6.1,
`zeroize` 1.9.1, `untrusted` 0.9.0 and `once_cell` 1.21.4. Without a crypto
provider it can do nothing. `rustls-pki-types` holds the DER-carrying types
(certificates, keys, names; 4,103 lines under `src/`, one `unsafe`
`transmute` in `server_name.rs`). `rustls-webpki` is the X.509 parser and
path validator (10,197 lines under `src/`, no `unsafe`); it hands the
signature check to the provider. `rustls` itself is 49,208 lines under
`src/` (all features, in-file tests included; TLS 1.2 is part of that) and
declares `#![forbid(unsafe_code)]`. Line counts are `wc -l` on the crates
as downloaded, and are not a count of the parts a TLS 1.3 client uses.
Of the dependencies, `zeroize` (21 mentions of `unsafe`), `once_cell` (51)
and `subtle` (2) contain `unsafe`, so "100% safe Rust" is false for any
rustls build whatever the provider.

**What a provider supplies.** From the 0.23.46 source
([docs.rs/rustls/0.23.46/rustls/crypto](https://docs.rs/rustls/0.23.46/rustls/crypto/struct.CryptoProvider.html)):
a `CryptoProvider` has five fields: `cipher_suites`, `kx_groups`,
`signature_verification_algorithms`, `secure_random` and `key_provider`. For
a TLS 1.3-only client with one suite, the provider writes: one
`Tls13CipherSuite` (its `CipherSuiteCommon`, a `crypto::hash::Hash` for the
transcript, a `crypto::tls13::Hkdf` with `crypto::hmac::Hmac`, and a
`Tls13AeadAlgorithm` that makes a `MessageEncrypter` and
`MessageDecrypter`); one `SupportedKxGroup` with its `ActiveKeyExchange`;
a `WebPkiSupportedAlgorithms` (a list of `SignatureVerificationAlgorithm`,
and a mapping from TLS `SignatureScheme` to them, which for TLS 1.3 tries
only the first); a `SecureRandom`; and a `KeyProvider`, which a client with
no client certificate can make fail on every call (unverified: not tried).
The rustls project's own list of third-party providers
([PROVIDERS.md](https://raw.githubusercontent.com/rustls/rustls/main/PROVIDERS.md))
names ten (graviola, SymCrypt, OpenSSL, BoringSSL, CCM, mbedTLS,
`rustls-pure`, RustCrypto, scytale, wolfCrypt), none of them libcrux or
HACL\*, and says the rustls maintainers have not evaluated them. rustls
recommends its own `rustls-aws-lc-rs` provider; `rustls-ring` is the other
first-party one.

**Dependency trees by provider** (`rustls` 0.23.46, `default-features =
false`, feature `std`):

| Provider | Packages (`normal`) | Packages (`normal,build`) | Notes |
|----------|---------------------|---------------------------|-------|
| none | 7 | 7 | no cryptography |
| `ring` 0.17.14 | 11 | 14 | adds `ring`, `cfg-if`, `getrandom`, `libc`; build adds `cc`, `find-msvc-tools`, `shlex` |
| `aws-lc-rs` 1.18.2 (`aws_lc_rs`) | 9 | 18 | adds `aws-lc-rs`, `aws-lc-sys`; build adds `cc`, `cmake`, `dunce`, `find-msvc-tools`, `fs_extra`, `jobserver`, `pkg-config`, `shlex`, `libc` |
| `rustls-provider-libcrux-pq` 0.1.1 | 42 | 42 | 35 more packages than none, see below |
| `rustls-graviola` 0.4.0 | 12 | not run | not examined (unverified) |
| `rustls-rustcrypto` 0.0.2-alpha | 78 | not run | RustCrypto; version is an alpha |

**aws-lc-rs.** `aws-lc-sys` 0.46.0 holds 1,529,921 lines of C, headers and
assembly in 421 `.c` and 912 `.S` files (`wc -l`, whole `aws-lc/`
directory, tests and generated assembly included, so an upper bound for the
code a build uses). A build with no CMake installed (only `cc`, `clang`,
`go` and `perl` on the path) completed in 21 seconds for `rustls` plus
`aws_lc_rs`; the `cmake` crate is a build dependency, but the CMake program
was not needed. The aws-lc-rs requirements page says a C or C++ compiler is
enough and that CMake, Go and bindgen are needed only for the FIPS build
([aws.github.io/aws-lc-rs/requirements](https://aws.github.io/aws-lc-rs/requirements/index.html)).
What AWS-LC has proven, per the
[AWS-LC formal verification repository](https://github.com/awslabs/aws-lc-verification)
and the [AWS-LC README](https://github.com/aws/aws-lc/blob/main/README.md):
SHA-2 (384 and 512, not 256) on x86-64 SandyBridge or later and, for 384,
on Neoverse N1 and V1; HMAC with SHA-384 on x86-64; AES-KW(P) with 256-bit
keys; and AES-256-GCM on x86-64 (SandyBridge to Skylake), only for 12-byte
IVs and 16-byte tags. The tools are SAW with Cryptol on C and x86-64
(on the code Clang produces), and NSym on AArch64 assembly. Separately,
assembly from s2n-bignum, proven in HOL Light, is used for P-256, P-384,
P-521, X25519 and Ed25519 on aarch64 and x86-64 and for RSA on aarch64
only. Not in the verified table: ChaCha20-Poly1305, HKDF (compositional
proofs referenced, not in the table), ECDSA (some helpers), RSA on x86-64.
So in AWS-LC the best-covered suite is `TLS_AES_256_GCM_SHA384`, and only
on particular CPUs. `ring` 0.17.14 (last release 2025-03-11) makes no
claim of formal verification; most of its C and assembly comes from
BoringSSL ([github.com/briansmith/ring](https://github.com/briansmith/ring)).

**libcrux.** Cryspen's libcrux (the repository now redirects to
`celabshq/libcrux`; how that organisation relates to Cryspen is
unverified) is "in pre-release (all of its crates are versioned < 0.1)"
and says its executables are not verified to be side-channel resistant
([README](https://api.github.com/repositories/561361007/readme)). Each crate
carries one of three badges, which I read in each crate's `Readme.md` on
2026-10-23:

- `verified-hacl`: `libcrux-chacha20poly1305`, `-poly1305`,
  `-curve25519`, `-ed25519`, `-p256`, `-ecdsa`, `-sha2`, `-hmac`, `-hkdf`
  and `-rsa`. The README says each "contains safe Rust that was compiled
  from verified C originating in the HACL\* project", where the F\* source is
  proven memory safe, functionally correct against a specification, and
  secret independent. The README cites Fromherz and Protzenko,
  "Compiling C to Safe Rust, Formalized"
  ([arXiv:2412.15042](https://arxiv.org/abs/2412.15042)), whose tool is
  Scylla; I did not confirm which tool produced the checked-in code. The
  abstract page describes a type-directed translation and does not claim
  it is itself proven, so the translation is in the TCB.
  (Eurydice, named in the task, compiles Rust to C, the other direction;
  it is not what produces these crates.)
- `verified` (hax to F\*): `libcrux-ml-kem` (I did not read `libcrux-ml-dsa`'s
  badge; unverified). The ML-KEM
  status file says its table is "a rough guide", and in it, for example,
  `ind_cpa`, `sampling` and the whole Neon back end have 0 of their
  functions proven panic free.
- `pre-verification`: `libcrux-aes` (AES-GCM and AES-CCM), so
  `TLS_AES_128_GCM_SHA256`, the suite RFC 8446 §9.1 requires, has no
  verified AEAD in libcrux. `libcrux-p384` 0.0.1 says it is an internal
  dependency that should not be used directly and comes from fiat-crypto
  and AU-Curves, not HACL\*.

`libcrux-rsa` 0.0.9 exposes RSA-PSS signing and verification only (its
public functions are `sign`, `verify`, `sign_varlen`, `verify_varlen`
over PSS); there is no PKCS#1 v1.5 and no raw modular exponentiation. The
`unsafe` count in the sources: `libcrux-intrinsics` 196 mentions,
`libcrux-secrets` 22, `libcrux-ml-kem` 102, `libcrux-ml-dsa` 70,
`libcrux-aes` 14, the `verified-hacl` crates 0 to 1 each.

**A libcrux provider for rustls.** There are two. `rustls-provider-libcrux-pq`
0.1.1 (crates.io, 2026-10-16; repository `ctf16/rustls-provider-libcrux-pq`,
author not affiliated with Cryspen as far as the README says) offers three
TLS 1.3 suites (AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305), X25519 and
P-256 and ML-KEM hybrids, and verifies ECDSA P-256, Ed25519, ML-DSA and
RSA-PSS. Its README says: P-384 ECDSA and RSA PKCS#1 v1.5 are missing, and
"certificates signed with PKCS#1 v1.5, which is OpenSSL's default for RSA
and what most public CAs use, don't verify"; it has "No security audit";
its AES comes from the pre-verification crate. The other is
`celabshq/rustls-libcrux` (`rustls-libcrux-provider` 0.0.1, not on
crates.io; 23 commits, last push 2026-09-09): ChaCha20-Poly1305 only,
X25519 and X25519MLKEM768, verification of ECDSA P-256, Ed25519, RSA-PSS and
RSA PKCS#1 v1.5. Its `verify.rs` gets PKCS#1 v1.5 from
`webpki::aws_lc_rs::RSA_PKCS1_2048_8192_SHA256`, that is from aws-lc-rs,
which I read but did not build. So no libcrux provider verifies RSA
PKCS#1 v1.5 with verified code, and RSA PKCS#1 v1.5 is needed for most
certificate chains (the claim of both provider READMEs; I did not measure
it). Counting packages for the first provider, the 42 are: the seven rustls
ones, the provider, 20 `libcrux-*` crates (aes, chacha20poly1305,
curve25519, ecdsa, ed25519, hacl-rs, hmac, intrinsics, macros, ml-dsa,
ml-kem, p256, p384, platform, poly1305, rsa, secrets, sha2, sha3, traits),
and `cfg-if`, `const-oid`, `der`, `getrandom` 0.4.3, `libc`, `pkcs8`,
`proc-macro2`, `quote`, `rand` 0.10.3, `rand_core`, `sec1`, `spki`, `syn`
3.0.9, `unicode-ident`. Several of these parse untrusted DER (`der`,
`pkcs8`, `sec1`, `spki`) for private keys a client does not need.

**Option B's size.** RFC 8446 is 160 pages. A client needs §4 (handshake;
the text from §4 to §5 is about 2,970 lines), §5 (record protocol, about 430
lines), §7.1 (key schedule, about 390 lines), §4.4.2 and §4.4.3
(Certificate, CertificateVerify), §4.4.4 (Finished), the alerts of §6, and
the extensions of §9.2 (`supported_versions`, `signature_algorithms`,
`supported_groups`, `key_share`, `server_name`, plus `cookie` for
HelloRetryRequest). §9.1 says a compliant application MUST implement
`TLS_AES_128_GCM_SHA256`, MUST support `rsa_pkcs1_sha256` for certificates,
`rsa_pss_rsae_sha256` and `ecdsa_secp256r1_sha256`, and MUST support
secp256r1 key exchange (X25519 only SHOULD). A client with
`TLS_CHACHA20_POLY1305_SHA256` and X25519 only, the choices whose
primitives are `verified-hacl`, is therefore non-compliant with §9.1 by
design, and would have to be recorded as a modelling choice; whether
the servers we care about accept it is unverified. RFC 5280 is 151 pages;
the certificate profile is §4.1 to §4.2, path validation §6.1 is about
980 lines, and DER itself is X.690 (not read). A client still needs RSA
PKCS#1 v1.5 verification, which means either aws-lc-rs for that one
function, or our own modular exponentiation with a Verus proof (public-key
operations handle no secrets, so side channels do not arise, but
VERIFICATION.md currently says cryptography is not our own code).

Existing formal work that can serve as a second source (reference text for
an independent transcription, and as a differential-test oracle; never as
a shipped dependency, since rule 8 says we write our own parsers):
`miTLS` of Project Everest, a verified TLS 1.2 and 1.3 implementation in
F\*, whose message formats were generated by EverParse
([Everest](https://www.microsoft.com/en-us/research/project/project-everest-verified-secure-implementations-https-ecosystem/);
a Microsoft and INRIA slide deck dates Everest 2016 to 2021, current status
unverified); `ASN1*`, a formalisation of ASN.1 DER with a mechanised
non-malleability proof, in F\* on EverParse (CPP 2023), which does not do
X.509 chain validation; ARMOR (Stony Brook and CUHK) for RFC 5280 chain
validation; and Verdict (Lin et al., USENIX Security 2025, Carnegie Mellon),
a formally verified X.509 validator in Rust checked with Verus, covering
parsing, path building and path validation, published as the `verdict` 0.1.0
crate ([repository](https://github.com/secure-foundations/verdict)).
Verdict's README says its default build uses verified primitives from
libcrux and aws-lc-rs, and that its `aws-lc` feature uses "unverified
signature checking for RSA and ECDSA P-256"; I did not read the code or the
paper beyond its abstract, so its size and its fit to our spec style are
unverified. I found no evidence that s2n-tls's ASN.1 or X.509 parser is
formally verified: Galois's SAW proofs of s2n cover HMAC and the DRBG.
The Galois X.509 work named in the task I could not find (unverified).

#### The options

**Option A: rustls as a listed exception.** `clazel-tls` is Tier 0 glue
around rustls, with a provider. Two providers are realistic. (A1) aws-lc-rs:
`aws-lc-rs` 1.18.2 and `aws-lc-sys` 0.46.0 are two packages, with 1.5
million lines of C and assembly, `unsafe` FFI, and verification that is
partial and CPU-specific (above); restricting the provider to
`TLS_AES_256_GCM_SHA384` and X25519 keeps to the primitives AWS-LC lists as
proven. It covers RSA PKCS#1 v1.5 and all the signature schemes a web
client needs. (A2) A libcrux provider: its primitives for ChaCha20-Poly1305,
X25519, SHA-256, HKDF and ECDSA P-256 are `verified-hacl`, but both
existing providers are 0.0.x or unpublished, one is unaudited by its own
account, neither verifies RSA PKCS#1 v1.5 with libcrux, so it cannot validate
most chains alone; it would have to borrow aws-lc-rs for that function, and
the project would then carry both libraries. The policy preference stated
in the first draft of this item (a libcrux or HACL\* provider "if one covers
a full TLS 1.3 cipher suite") is met for the suite but not for certificates.
Costs: rustls, webpki and pki-types, about 63,000 lines under `src/` of
unproven parsing of records, handshakes and certificates, are in the TCB;
every version bump goes unaudited; the 0.24 line is pre-release and changes
how providers are chosen (unverified: not examined).

*Rows A1 would add to `DEPENDENCIES.md`, class `shipped`:* `rustls` 0.23.46,
`rustls-webpki` 0.103.16, `rustls-pki-types` 1.15.1, `aws-lc-rs` 1.18.2,
`aws-lc-sys` 0.46.0, `subtle` 2.6.1, `zeroize` 1.9.1, `untrusted` 0.9.0,
`once_cell` 1.21.4; and for build scripts only, `cc` 1.10.0, `cmake` 0.1.58,
`dunce` 1.0.5, `find-msvc-tools` 0.1.15, `fs_extra` 1.3.0, `jobserver`
0.1.35, `pkg-config` 0.3.34, `shlex` 2.0.1. The `libc` row (0.2.190, Linux
only, no default features) would have to cover every target through
`jobserver`. The class list has no "build" class, so either these eight are
`shipped` (rule 8 does not fit them) or the checker gains a class.
*Rows A2 would add:* the 42 packages above (the aws-lc-rs ones too for
PKCS#1 v1.5); `syn` 3.0.9 is a new version beside the `proof` row `syn`
2.0.119, and `proc-macro2`, `quote` and `unicode-ident` would move from
`proof` to `shipped`, the strictest class that covers them.
*Rule 8 text (A):* after the sentence on shipped dependencies, "One further
exception: the TLS stack, `rustls`, `rustls-webpki`, `rustls-pki-types` and
the packages of the chosen crypto provider, which parse untrusted bytes
without proofs. Only `clazel-tls` may depend on them, and the exception
lasts until `clazel-tls` is replaced by a verified TLS client." *TCB entry:*
"rustls, rustls-webpki, rustls-pki-types and the crypto provider
(aws-lc-rs over AWS-LC, partly verified for particular algorithms and CPUs):
TLS records, handshake messages and X.509 certificates are parsed by
unproven code." The existing line "Cryptography ... from formally verified
libraries (libcrux / HACL\*)" becomes false for A1 and would be reworded.
The README's "100% safe Rust" claim is qualified as above.

**Option B: our own TLS 1.3 client, Tier 2.** The record layer (§5),
handshake messages (§4), key schedule (§7.1), one suite and one key exchange
as a state machine like `clazel-fetch`'s, with X.509 and DER (RFC 5280, X.690)
and path validation (§6) as our own Tier 2 crates, and cryptography from
`verified-hacl` libcrux crates. The suite choice is forced by the facts:
`TLS_CHACHA20_POLY1305_SHA256` with X25519, ECDSA P-256 and RSA-PSS
verification and SHA-256 and SHA-384, since AES-GCM in libcrux is
`pre-verification`; that departs from §9.1's mandatory suite and from its
mandatory secp256r1 key exchange. Costs: it is the largest item in the
roadmap; RSA PKCS#1 v1.5 verification has no verified source (own bignum
code, or aws-lc-rs for that one function, which brings back the C library
and its build dependencies); chains with RSA-signed certificates do not
validate without it; the
crypto crates' extraction (Scylla) and `libcrux-intrinsics`, `-secrets` and
`-platform` (`unsafe`) stay in the TCB, so "100% safe Rust" is qualified
even here. Verdict (above) shows that Verus can carry an X.509 validator;
it is the nearest precedent and a candidate oracle.

*Rows B would add, class `shipped`:* `libcrux-chacha20poly1305` 0.0.10,
`libcrux-curve25519` 0.0.9, `libcrux-ecdsa` 0.0.9, `libcrux-hacl-rs` 0.0.6,
`libcrux-hkdf` 0.0.9, `libcrux-hmac` 0.0.9, `libcrux-intrinsics` 0.0.9,
`libcrux-macros` 0.0.4, `libcrux-p256` 0.0.9, `libcrux-platform` 0.0.4,
`libcrux-poly1305` 0.0.7, `libcrux-rsa` 0.0.9, `libcrux-secrets` 0.0.7,
`libcrux-sha2` 0.0.9, `libcrux-sha3` 0.0.11, `libcrux-traits` 0.0.9,
`rand` 0.10.3, `rand_core` 0.10.1, `syn` 3.0.9, and the reclassification of
`proc-macro2`, `quote`, `unicode-ident` and the existing `libc` row (23
packages in this resolution, all with default features off; the exact set
is to be re-measured by the item that adds them). *Rule 8 text (B):* no
exception; the sentence on crypto gains "from the formally verified
`libcrux` crates named in `docs/DEPENDENCIES.md`, which are
`verified-hacl` or `verified` in their own READMEs, and the proc-macro
packages they need at build time". *TCB entry:* replace the cryptography
line with "libcrux: `verified-hacl` algorithms (F\* proofs, with the
C-to-Rust translation trusted), plus the `unsafe` in `libcrux-intrinsics`,
`libcrux-secrets` and `libcrux-platform`; RSA PKCS#1 v1.5 verification
(none verified, or our own code)".

**Option C: A now, B later.** Take A, with the exception written as
temporary and a roadmap entry for B, so the `curl` clone and Phase 4's
text-mode browser do not wait for a TLS proof. The shell keeps TLS behind
one trait so the replacement is a swap. The rows, rule 8 text and TCB entry
are those of A, written with an end date condition. Costs: those of A for
as long as it lasts, and the risk that the exception does not end.

**Recommendation:** C, with the exception recorded exactly (the rows, the
rule 8 text, the TCB entry) so that the README's "100% safe Rust" and
"every parser of untrusted input carries proofs" claims are qualified
wherever they appear until B lands. The checked facts change two details,
not the choice. First, the "better fit" provider in the first draft, one
over libcrux, does not exist in usable form: the only candidates are
0.x, one unaudited, none with verified RSA PKCS#1 v1.5, so the interim
provider is aws-lc-rs (A1), limited to `TLS_AES_256_GCM_SHA384` and
X25519, and the cryptography sentence in VERIFICATION.md is reworded to say
"partly verified". Second, B's suite is not the RFC's mandatory one, and B
needs an answer to RSA PKCS#1 v1.5 (own proof or a retained aws-lc-rs call)
before it can drop A's dependency entirely; that should be a question
for item 3.5's spec, not a surprise there. The maintainer should also
decide whether the eight build-script packages are `shipped` or get a
`build` class in `docs/DEPENDENCIES.md`.

**Decision (2026-10-23): option B**, our own TLS 1.3 client at Tier 2
with cryptography from libcrux's `verified-hacl` crates and no rustls.
Chosen by the agent at the maintainer's request ("do what you think is the
best option, taking into account the project goals"), on these grounds:

- *The claims must be true when they are announced.* The project's two
  headline claims, that every parser of untrusted input carries a proof
  and that our code is 100% safe Rust, are what the Phase 5 Show HN post
  says. TLS is the first parser an attacker on the network reaches. Under
  A or C both claims would be false at the moment they are made, with the
  largest unverified component the project had ever added, and "temporary"
  exceptions of that size rarely end: Phase 8's compatibility grind would
  always have something more urgent. Phases 1 and 2 (a 565-function URL
  proof, a proven kernel) show the method carries this size of work.
- *The facts removed A's advantage.* No verified provider exists for the
  certificate half; A1's verification is narrow and CPU-specific; the
  libcrux provider route needs aws-lc-rs anyway. A would add 1.5 million
  lines of C and assembly to the TCB for a result that is "partly
  verified" on some CPUs.
- *The costs are taken knowingly, and recorded here:*
  1. **Time.** 3.5 becomes seven items (3.5a to 3.5g below), several of
     them L. The `http://` half of the `curl` clone (3.8) does not wait on
     them, and Phase 4's text-mode browser can start on `http://` and
     local files; Phase 5's milestone needs TLS, and that is the right
     order: the claim is true when it is announced.
  2. **One cipher suite.** `TLS_CHACHA20_POLY1305_SHA256` with X25519, the
     primitives that are `verified-hacl`. RFC 8446 §9.1 requires
     `TLS_AES_128_GCM_SHA256` and secp256r1; this client offers neither
     until a verified AES-GCM exists (libcrux's is `pre-verification`), so
     it is non-compliant with §9.1 by design. The spec header lists it as
     a modelling choice, and 3.5g measures which servers refuse it.
  3. **RSA PKCS#1 v1.5 verification is our own code**, at Tier 2 (3.5c).
     No verified library has it and most certificate chains need it.
     Signature verification handles no secrets (the key, the signature and
     the message are all public), so the side-channel argument for never
     writing our own cryptography does not apply. VERIFICATION.md's TCB
     line changes from "cryptography is not our own code" to "cryptography
     that handles secrets is not our own code; public-key signature
     verification for RSA PKCS#1 v1.5 is ours and proven against RFC 8017".
  4. **libcrux is in the TCB** with what is known: `verified-hacl` crates
     are F\* proofs plus a trusted C-to-Rust translation (Scylla);
     `libcrux-intrinsics`, `-secrets` and `-platform` contain `unsafe`; the
     README makes no side-channel claim for the extracted code. Versions
     are 0.0.x, pinned exactly and bumped deliberately. The proc-macro
     chain a libcrux crate may need at compile time is listed `shipped`
     with a "Why" saying it runs at compile time only (no `build` class is
     added; the question of build-script packages was A's and is moot).
     The README's safe-Rust line becomes "our code is 100% safe Rust except
     `clazel-sys`; shipped dependencies are `libc` and libcrux".
  5. **Revocation is out of scope** for the phase (no CRL or OCSP), as it
     is for the browsers' default behaviour on most certificates; listed in
     3.5b and in the README.

Rule 8 needs no exception. The crypto sentence of rule 8 and the TCB entry
are written by 3.5f, which adds the rows.

### 3.1 HTTP field syntax (M)

`crates/clazel-http`, module `field/`. RFC 9110 §5.1 field names (and that
they are compared case-insensitively), §5.2 field lines and the combined
field value (comma-joined in order; `Set-Cookie` excluded, as §5.3's note
says: it is a list of its own, one field line per cookie), §5.5 field
values (what octets are allowed; leading and trailing whitespace is not part
of the value), §5.6.1 lists (the `#` rule, with empty elements dropped),
§5.6.2 tokens, §5.6.3 whitespace (OWS, RWS, BWS), §5.6.4 quoted strings
(and `quoted-pair`), §5.6.6 parameters, §8.6 the `Content-Length` grammar
(`1*DIGIT`, the list case where every element is the same value), and the
`Transfer-Encoding` and `Connection` list values 3.2 needs.

Spec functions take `Seq<u8>` (fields are octets, RFC 9110 §5.5). Lemmas: a
token contains no delimiter; unquoting a quoted string of a token-free
value and quoting it again round-trips; a combined value splits back into
its field lines when none contains a comma; `Content-Length` with repeated
identical values equals the single value.

Independent: the Fetch Standard §2.2 "HTTP" definitions (header names,
header values, "HTTP token code point", "collect an HTTP quoted string",
"get, decode, and split"), a different body's text for the same grammar,
proven equal on the inputs both define (the lemma states the class). Where
Fetch and RFC 9110 differ (Fetch strips only HTTP tab or space; the
`#` rule's treatment of empty elements), the difference is stated in the
lemma, not hidden.

Mutations seeded for each grammar rule. Conformance for this item is 3.3's.

**As built:** `crates/clazel-http/src/field/` (`spec`, `contract`,
`termination`, `string`, `section`, `list`, `quoted`, `params`,
`content_length`, `types`, `lemmas`, `examples`, `independent`, `tests`),
`mutations.json` and a README. Verus verifies 146 items with no errors; the
crate stays `tier = 0`, `target-tier = 2`, because framing (3.2) and the
conformance tests (3.3) do not exist. Every exec function is proven equal to
its contract (tokens, field names and case-insensitive comparison, OWS/RWS/BWS
and stripping, field values, field lines of one name, the combined value,
`Set-Cookie` lines, list splitting, quoted strings read and written,
parameters in both the §5.6.6 and §10.1.4 forms, `Transfer-Encoding`,
`Connection`, `Content-Length` with a `u64` limit). Proven lemmas: a token
has no delimiter and tchar is "VCHAR except delimiters"; unquote after quote,
and quote after unquote on canonical quoted strings; a combined value splits
back into its lines (needs no comma and no DQUOTE in a line, because a
DQUOTE opens a quoted string that swallows later commas); repeated identical
`Content-Length` equals the single value; `Set-Cookie` is never combined.
`examples.rs` evaluates RFC 9110's examples and a case per rule boundary.
`independent.rs` is the Fetch §2.2 transcription (token code points from MIME
Sniffing, which Fetch defers to the RFC for), proven equal to the spec on
every byte sequence for header names, for trimming tab and space, and for
"get, decode, and split" against `split_values` (empty pieces kept; dropping
them is `list_elements`), and equal on every RFC quoted string for "collect
an HTTP quoted string". Differences, stated in the lemmas: Fetch keeps empty
elements, its *normalize* also strips CR and LF, its header value allows
control bytes other than NUL, CR and LF, and its quoted-string reader accepts
unterminated strings. (HTTP tab or space is exactly OWS, so there is no
difference there.) 76 mutations, all `killed` with certificates, one or more
per grammar rule. 10 unit tests. Choices worth review: "the same decimal
value" in §8.6 is read as the same digits (`42, 042` is rejected); `Content-Length`
keeps empty list members as errors where `list_elements` drops them;
`quote` returns `None` for a value with a CR, LF, NUL or other control.
Not done: conformance (3.3), framing (3.2).

### 3.2 HTTP/1.1 message framing (L)

`clazel-http`, module `message/`. RFC 9112 §2.1 message format, §2.2
message parsing (the leading CRLF rule, no whitespace between start-line and
first field line, what to do with a bare CR), §2.3 version, §4 status line
(status code exactly three digits; the reason phrase is kept but never
interpreted), §5 field line parsing with §5.1's rejection of whitespace
between field name and colon, and §5.2 obsolete line folding replaced by SP
as a user agent must, §6 message body: §6.1 `Transfer-Encoding` (only
`chunked`, and only as the final coding; anything else is unsupported and
closes the connection), §6.2 `Content-Length`, §6.3 message body length
(steps 1 to 8, as a client: 1xx, 204 and 304 and HEAD responses have no
body; `Transfer-Encoding` and `Content-Length` together is an error, the
smuggling case of §11.2, never resolved in favour of either), §7.1 chunked
transfer coding (chunk size in hex, chunk extensions parsed and ignored,
the trailer section parsed and dropped, §7.1.3 decoding), and §9.3 and
§9.6: when the response ends by connection close.

Request side: §3 request line, `Host` (RFC 9110 §7.2) and the fields 3.6
chooses, as a serializer `serialize_request(request) -> Seq<u8>`, with a
lemma that what it writes parses back as the same request (the request
parser exists only for this lemma and the differential test; the browser
never parses requests).

Modelling choices, listed in the spec header: the spec is a function over
the *complete* received bytes to one of `Incomplete`, `Invalid` or a parsed
response plus the bytes after it; the executable parser is incremental (it
takes bytes as they arrive and keeps a state) and is proven equal to the
spec on the concatenation of everything it was given, and to give
`Incomplete` on every proper prefix of a message it accepts, so that no
decision is ever made before the bytes that justify it have arrived. Limits
are modelling choices too, each stated with its number: the longest
status line, field line and field section accepted, the largest
`Content-Length` and chunk size (a `u64`, with overflow an error), and the
largest body. The parser never reserves more memory than the bytes it has
received, as the CBOR decoder does.

Independent: RFC 7230 §3 (the obsoleted text of the same protocol, by the
same working group, so weaker than a second body) for framing, and the
Fetch Standard's "HTTP-network fetch" step that reads the body for the
cases of §6.3, proven equal where the texts agree, with the differences
listed (RFC 7230 allowed obs-fold in a request; RFC 9112 does not).

**As built (3.2):** `crates/clazel-http/src/message/` (`spec`, `contract`,
`termination`, `line`, `body`, `serialize`, `types`, `examples`, `independent`,
`lemmas`, `incremental`, `request`, `request_parser`, `tests`). The spec, the examples and the executable response parser and request
serializer are as the plan describes, with the status line and obs-fold
choices listed in `spec.rs`'s header. Limits (`max_line` 8192, `max_lines` 256,
`max_body` 64 MiB) are parameterised in two spec functions
(`read_line_with`, `close_body_pending`, with `read_line` and `parse_response`
passing the limits), so examples at a limit of 4 reach the boundaries, which
the limit mutations (`line-max-off-by-one`, `line-max-widened`,
`line-incomplete-limit-early`, `line-incomplete-limit-late`,
`close-limit-dropped`) needed; all 150 mutations are `killed` with certificates.
`independent.rs` is RFC 7230 §3, §3.4 and §4.1 read on its own, with two theorems.
`theorem_independent_framing`: where it says a response is there, `parse_response`
finds the same one, and where it says there is none, `parse_response` is not
`Done`. `theorem_independent_at_close` (`r_parse_at_close`, RFC 7230 §3.3.3
items 5 and 7 and §3.4): on a closed connection a response it finishes is the
one `parse_response_at_close` finishes, with the same octets after it, and a
message it calls incomplete (a head, a `Content-Length` body or a chunked body
cut short by the close, or a framing error or limit) is `Invalid`; a body with
no declared length is everything received. `Transfer-Encoding` with
`Content-Length` is covered by both: it was a plain omission, since RFC 7230
§3.3.3 item 3 and RFC 9112 §6.3 item 3 say the same words (the field "overrides"
`Content-Length` and the message "ought to be handled as an error"); the
spec and the transcription both take the error, a stated choice and not a
difference of text. Still `Out`, each with its reason in the header, are the
places the two RFCs really differ or word a rule differently: obs-fold, other
codings (RFC 7230 would decode them or read to the close), HTTP/1.0 with
`Transfer-Encoding`, repeated `Content-Length` (same decimal value against same
digits), chunk-extension whitespace, status line without the second SP or with
another major version.
RFC 7230's `field-content` cannot match `a b c`; the transcription reads it as
RFC 9110 §5.5 does (`docs/ERRATA.md`). Unlike `field/independent.rs`, its
author had read `spec.rs`, so the independence is the other RFC's grammar and
the proof, not isolation. `lemmas.rs` proves that each reader keeps its decision when bytes are
appended, from which `theorem_monotone` and `theorem_no_early_decision`
follow. `incremental.rs` keeps the parser's place (status line, field lines
read, body start and length, chunks decoded) under an invariant `wf`: for
every continuation, resuming from the saved state equals parsing from the
start; `feed` requires and keeps `wf`. `request.rs` specifies a request
parser (HTTP/1.1 only, the target a run of VCHAR, no leading empty lines,
no body) and proves `parse_request(serialize_request(r) + more)` gives `r`
back for every valid request within the limits. The Fetch comparison
(`message/independent_fetch.rs`, Fetch commit `59afe34`) is narrower than the
plan expected: "HTTP-network fetch" defers the wire format to HTTP ("follow
the relevant requirements from HTTP") and only forwards the bytes HTTP
transmits (closing the stream when the body is "done normally", erroring it
on abort), and Fetch has no text for the chunked coding, the read-until-close
rule or truncation, so none is invented. What Fetch does define is "extract a
length" (with header list "get" and "get, decode, and split"), transcribed
and proven (`theorem_fetch_extract_length`) against `body_length` for every
field section when no `Transfer-Encoding` is present and the status and
method give a body: a number exactly when the spec's `Content-Length` is
valid (the same number, `Invalid` only past the body limit), failure only for
`Invalid`, no line for `Close`. The difference: a present but non-numeric
`Content-Length` is null in Fetch (ignored) and `Invalid` here (RFC 9112
§6.3 item 5). The header lists the rest.

### 3.3 HTTP conformance (M)

`tests/conformance_http.rs`: a differential test against `httparse` (the
parser hyper uses; no dependencies; a `test` row) on random messages,
mutated messages and the vendored corpora, comparing status, every field,
and where we reject whether `httparse` does; and the llhttp fixtures
(Node's HTTP parser, `test/response/*.md` and the chunked and
`Content-Length` cases of `test/request/*.md` that a client also sees),
vendored at a pinned commit with their license and converted by a
`cargo xtask testdata` converter that reads the fixed markdown shape and
fails if it changes. Every RFC 9112 §7.1 and §11 example appears as a case.
Expected failures (cases where llhttp is lenient by design) are listed with
reasons and never counted as passes. The summary lines follow
`xtask/src/conformance.rs`. Miri runs the unit tests.

**As built:** `tests/conformance_http.rs` has seven suites, each printing one
`clazel-conformance:` line: the RFC 9112 §7.1 and §11 cases (122), the llhttp
`test/response` and framing cases (136: 109 pass, 27 expected failures with
reasons), httparse differentials on random responses (6000), mutated responses
(60000: 53915 pass, 6085 expected differences, each explained by a documented
choice), the llhttp corpus heads (136: 124 + 12) and handcrafted heads (44: 29
+ 15), and framing by construction (3000 random bodies by `Content-Length`,
chunked, close and no body). 0 unexpected failures. Differences from the plan:
RFC 9112 has no wire examples in §7.1 or §11, so each case is one production,
one decoding step or one attack (response splitting, smuggling, truncation)
written out as bytes; the llhttp fixtures are vendored under
`tests/data/llhttp/` with their license and converted into
`tests/generated/llhttp.rs` by `cargo xtask testdata`; `httparse` reads only
heads, so framing is checked by construction and against llhttp instead.

After 3.1 to 3.3: **raise `clazel-http` to tier 2.**

### 3.4 DNS message format (M)

`crates/clazel-dns`. RFC 1035 §4.1.1 header (ID, QR, OPCODE, AA, TC, RD, RA,
Z must be zero, RCODE, the four counts), §4.1.2 question, §4.1.3 resource
record, §4.1.4 message compression (a pointer must point to an earlier
octet of the message than the pointer itself, which gives the decoder a
`decreases` clause and makes a forward or self pointer an error; the
standard says "a prior occurrence", and the comment at that spot says why
"prior" means a lower offset), §2.3.4 size limits (labels at most 63
octets, names at most 255, UDP messages at most 512), §2.3.3 case (names
compare case-insensitively; the decoder keeps what the server sent),
§3.2.2 and §3.2.4 TYPE and CLASS values (A, CNAME, AAAA from RFC 3596 §2;
IN), §3.3.1 CNAME, §3.4.1 A, RFC 3596 §2.2 AAAA, §4.2.2 the two-octet TCP
length prefix (for TC=1 fallback, RFC 7766 §8).

Functions: `encode_query(id, name) -> Seq<u8>` (a standard query, RD=1, one
question of type A or AAAA, class IN, no compression; the name is ASCII
already, `clazel-url` having applied IDNA), `decode_message(bytes) ->
Option<Message>`, and `answer_addresses(query, message) -> Option<Seq<Addr>>`,
which accepts a message only if its ID and question equal the query's
(RFC 5452 §4 to §6), its RCODE is 0 or 3 (NXDOMAIN gives the empty answer),
and returns the addresses of the records in the answer section whose owner
is the query name or a CNAME target reached from it within the answer
section (RFC 1034 §3.6.2); records in the authority and additional sections
are never used, and a CNAME chain that does not end in the answer section
gives no addresses (the shell may re-query the last target, RFC 1034 §5.3.3
step 3a). Lemmas: decoding a query we encoded gives it back; a decoded name
is at most 255 octets with labels at most 63; `answer_addresses` returns
only addresses from the answer section.

Independent: RFC 883 §4 (the predecessor, same wire format, different
text), proven equal to the decoder on every message, with any difference
listed; if the texts turn out identical in substance, say so and record the
transcription as same-RFC, as `clazel-ipc` did for RFC 7049.

Conformance: a differential against an independent crate with the fewest
dependencies that parses full messages (candidates: `simple-dns`,
`dns-parser`; the agent picks and the DEPENDENCIES.md row says why) on
random and mutated messages; a vendored corpus of real resolver responses
(captured once, stored as hex under `tests/data/` with a `SOURCE.md`
saying how, since no official suite exists), including a truncated one, a
NXDOMAIN, a CNAME chain and an AAAA answer; and the RFC 1035 §4.1.4
compression example. **Raise `clazel-dns` to tier 2.**

**As built:** `crates/clazel-dns`, tier 2 (raised 2026-10-24 after CI's
full verification passed). API (exec, each proven equal
to its spec): `decode_message`, `decode_udp`, `encode_query(id, dotted_name,
qtype) -> Option<Vec<u8>>` (names are dotted ASCII; `None` if not a name),
`answer_addresses(id, dotted_name, qtype, &Msg) -> Option<Resolved>` with
`Resolved { addresses, redirect }`, `Msg::tc()`, `tcp_frame` and
`tcp_message_len`, and `resolv::parse::nameservers(&[u8]) -> Vec<Addr>` (the
grammar is ours; IPv4 is strict dotted decimal, IPv6 uses `clazel-url`'s proven
parser, which is a dependency). Findings: (1) "a lower offset" is not enough
for the pointer rule, since a label at offset 0 followed by a pointer to 0
loops; the spec requires the target name to end before the pointer
(`ERRATA.md`), and the explicit `target < pos` check is then redundant (kept
for fidelity). (2) RFC 883's TTL is 16 bits, so the "same wire format" is not
exact; `independent.rs` uses 32 bits, lists that and the other differences, and
is the same family as RFC 1035, not a second body. (3) Z is rejected when
nonzero, including the AD and CD bits of RFC 4035: 3.8 must treat that as
fail-closed (a resolver that sets AD without DO would fail every lookup).
Choices: answers come from the final name of the CNAME chain only, following
the first CNAME at each name; octets after the last record are an error; only
QTYPE A and AAAA are queried. Proven: the lemmas listed above plus the
bounded-reservation lemma, Verus 228 verified. 147 mutations, all certified
kills (the MAX_TCP bound is killed through a statement about the constant,
since a 65536-octet witness is too big to evaluate). Conformance:
hand-built messages (24), real responses captured on 2026-10-23 from 8.8.8.8
and an authoritative server (12, stored as hex in the test, not under
`tests/data/`, which is for vendored suites), `simple-dns` 0.12.0 (chosen over
`dnsparse`, which reads only the header, questions and answers, and
`dns-parser`, which writes only queries) on 8000 random messages, 4000 queries
and 60000 mutated messages (1269 expected differences, each assigned to a
rule: the prior-occurrence rule, trailing octets, AD/CD, RDLENGTH 0 or longer
than the data, unknown types or classes; none unexplained), and 10
`resolv.conf` files.

**Added for 3.8 (2026-10-25):** `encode::wire_to_dotted(&[u8]) -> Option<Vec<u8>>`,
the inverse of `dotted_to_wire` for a CNAME target, proven equal to
`spec::wire_to_dotted` (RFC 1035 §3.1 labels, §2.3.4 limits; the spec is
`wire_scan`, a recursion on the labels with the dotted forms joined). `None`
for the root, a label holding a `.` or an octet of 128 or more, a pointer or
reserved length octet, octets after the zero octet, a missing zero octet and a
name over 255 octets; octets outside the preferred syntax of §2.3.1 are kept,
as `dotted_to_wire` keeps them. Proven: `lemma_wire_to_dotted_round_trip`
(`dotted_to_wire` of the result is the input, which is what the shell's run-time
guard checked), with `lemma_wire_scan_inverts`, `lemma_dotted_scan_skip` and
`lemma_dotted_scan_shift`; examples `lemma_wire_names` and
`lemma_wire_limits`, evaluated by Verus. 16 more mutations, all certified kills
(163 in all). Verus 242 verified. Conformance: `wire_to_dotted` is checked on
the 4000 queries of the `simple-dns` differential (it must give back the name,
and equal the labels `simple-dns` reads) and on the 255 and 256 octet names;
the suite totals are unchanged. Not covered by a mutation: the check that a
label does not run past the end of the name (a mutant that drops it makes the
spec take an out-of-range `subrange`, which `compute_only` cannot evaluate; the
`>` to `>=` change is equivalent). `independent.rs` does not cover it, as it
does not cover `dotted_to_wire`: it is the decoder's second transcription.

### 3.5 TLS (eight items; 3.0 decided option B; 3.5h added 2026-11-03)

Our own TLS 1.3 client. Every parser is a pure function over bytes and the
handshake is a transducer with the cryptography as parameters, joined to
libcrux in 3.5f, as the kernel took `UrlFns`. The pure parsers (3.5a, 3.5c,
3.5d) start at once and add no shipped dependency.

#### 3.5a DER (M)

`crates/clazel-der`. ITU-T X.690 (08/2015): §8.1 the identifier, length
and contents octets; §10 the DER restrictions (definite length only,
shortest length form, §11.1 BOOLEAN as `0x00` or `0xFF`, §8.3 INTEGER with
no redundant leading octets, BIT STRING with the unused-bits octet and
zero padding bits, §11.5 SET OF ordering is parsed as given and checked by
X.509 where it matters); the universal types X.509 needs (BOOLEAN,
INTEGER, BIT STRING, OCTET STRING, NULL, OBJECT IDENTIFIER §8.19,
UTF8String, PrintableString, IA5String, UTCTime and GeneralizedTime with
RFC 5280 §4.1.2.5's restrictions applied by X.509, SEQUENCE, SET, and
context-specific tags, both IMPLICIT and EXPLICIT); nothing indefinite,
no high-tag-number forms beyond what X.509 uses (reject the rest, listed).
Functions: a cursor-style decoder over `Seq<u8>` (read one TLV, descend
into a constructed value, require end of contents), and an encoder for
the few values 3.5c and 3.5e write (`DigestInfo`, lengths). Lemmas: no
over-read (the decoder consults no byte past the length it read); encode
then decode round-trips; decode then encode gives the same bytes (DER is
canonical); bounded reservation. Independent: Kaliski, "A Layman's Guide
to a Subset of ASN.1, BER, and DER" (RSA Laboratories, 1993), a different
author's text of the same rules, proven equal on its subset. Conformance:
a differential against RustCrypto's `der` crate (a `test` row, counting its
dependencies) on random and mutated TLVs, and the DER cases of the
`x509-limbo` corpus (3.5b vendors it) that are pure encoding errors.

**As built** (on `main`): `crates/clazel-der`, tier 2 (raised on CI's full verification of the pull request
that raised it; `main`'s run at `35160d8` measured Verus 241 verified and 59 of 59 mutations certified). Cursor-based DER readers and
encoders cover the types listed above, with contracts, round-trip,
canonicity, no-over-read and bounded-reservation lemmas. The independent
transcription uses Kaliski's Guide, with its coverage limits recorded in the
crate README; the same agent wrote both transcriptions. `mutations.json`
contains 59 certified mutations. Conformance includes hand-built cases and
a differential against RustCrypto `der` 0.8.2. Character and time validation,
SET OF ordering and DEFAULT omission remain the X.509 caller's duty.

#### 3.5b X.509 certificates and path validation (L, after 3.5a)

`crates/clazel-x509`. RFC 5280 §4.1 `Certificate`, `TBSCertificate` and
its fields (§4.1.2.1 to §4.1.2.9), §4.1.1.2 and RFC 3279, RFC 4055,
RFC 5758 and RFC 8410 for the signature algorithm identifiers
(`sha256WithRSAEncryption`, `sha384WithRSAEncryption`, `rsassa-pss` with
its parameters, `ecdsa-with-SHA256`, `ecdsa-with-SHA384`, `ed25519`),
`SubjectPublicKeyInfo` for RSA (RFC 8017 Appendix A.1.1) and EC (RFC 5480
§2, P-256 uncompressed points only), the extensions validation needs
(§4.2.1.3 Key Usage, §4.2.1.6 Subject Alternative Name with `dNSName` and
`iPAddress`, §4.2.1.9 Basic Constraints, §4.2.1.10 Name Constraints,
§4.2.1.12 Extended Key Usage with `id-kp-serverAuth`; unknown critical
extensions reject, unknown non-critical ones are kept opaque), §6.1 basic
path validation (steps 6.1.1 to 6.1.5 as a function over a candidate chain,
with the policy steps taken as "no policy required" and said so, and
revocation not checked: a modelling choice, listed, with CRL and OCSP as
Phase 8 work), §7.1 name comparison on the class the lemma states (binary
after the §7.1 case-folding for PrintableString; the full LDAP StringPrep
is not transcribed and the class says so), and RFC 9525 §6 host name
matching (`dNSName`, a wildcard only as the whole leftmost label, IP
addresses by octets). Path building: the chain the server sent, in order,
plus one root from the trust store (RFC 5280 §6.1 takes the chain as
given; §6.2 lets us choose the simple policy and say so). The trust store:
Mozilla's `certdata.txt` (NSS, MPL-2.0), vendored at a pinned commit under
`tests/data/`-like rules but shipped, converted by `cargo xtask tables`
into a Rust table of DER roots, as the Public Suffix List is. Independent:
ITU-T X.509 (10/2019) §7 to §12 for the structures and path processing
(the ITU text, not the IETF profile), proven equal on the profile's
inputs. Conformance: the `x509-limbo` corpus (C2SP, Apache-2.0 / MIT),
expected failures listed; a differential against `rustls-webpki` as a
`test` row; Verdict (`verdict`, USENIX Security 2025) as a second oracle
if its dependency tree allows a `test` row, and as reference text for the
spec's structure. The signature checks themselves are parameters until
3.5f.

**As built** (on `main`, `crates/clazel-x509`, `tier = 0`, `target-tier = 2`; the verification counts are in the README table): the decoders (certificate, TBS, SPKI, extensions, names, name and policy constraints, time, signature-algorithm identifiers), RFC 9525 matching, the Mozilla root table (`roots`, from the vendored `certdata.txt`), the leaf checks, and RFC 5280 §6.1 path validation in `src/path/`: the §6.1 transcription (`spec`), the browser profile on top of it (`profile`: only refusals, each marked and sourced), the verdict on one candidate (`verifier`, `exec`) and the bounded depth-first chain search (`search`, `verify_server_chain`). Signature verification is a parameter (`LinkVerifier`); the real one is `clazel-crypto`'s `CertificateLinks`. Revocation is not checked (Phase 8). **x509-limbo** (`tests/conformance_limbo.rs`): every `SERVER` testcase with a DNS or IP peer name runs through `verify_server_chain` with limbo's trusted certificates, validation time and `max_chain_depth` (carried into the generated index by `cargo xtask testdata`) and a link verifier that accepts every signature; limbo's `SUCCESS` or `FAILURE` is compared with the verdict. **9,736 of 9,802 testcases agree** (923 `SUCCESS`, 8,813 `FAILURE`); 66 are expected failures listed by id with a reason in `tests/limbo/expected_failures.rs`, and the test fails if an id appears, vanishes or starts to agree: 10 `CLIENT` testcases; 10 needing CRLs; 4 needing signature verification (3.5f, P11); 3 ML-DSA; 1 `SUCCESS` without a DNS or IP name; 3 deliberate profile refusals of what RFC 5280 alone accepts (a CA certificate as the target, no extKeyUsage on the target); and 34 where limbo asks for the refusal of something that is an issuer-side or CA/Browser Forum certificate-profile rule that no §6.1 step or profile rule checks (authority and subject key identifiers, extension criticality flags, serial zero, subjectAltName criticality, root contents, extra or critical extKeyUsage, the subject commonName, malformed authorityInfoAccess, the target's key type and size, and a 2052-bit RSA root); and 1 where limbo refuses a wildcard over a suffix in the PSL's private section, which BR 3.2.2.6 and `dns_match` do not. The run found no disagreement that was a defect of the §6.1 transcription, the profile or the search, so it changed none of them. **What is not checked:** signatures in this crate's own run (the stand-in accepts all, so a `FAILURE` that rests on a signature is listed, not pinned; `clazel-crypto/tests/chain_limbo.rs` runs those cases with the real links); revocation; client-certificate validation; the target's key type and size (a profile gap, listed); that Chrome and Firefox agree with the profile where the profile's source marks a behaviour *unconfirmed*. **Not done for tier 2:** the differential against `rustls-webpki`, the independent transcription of ITU-T X.509 §7 to §12, and the raised tier itself. The path-validation design the doc comments cite (work packages P1 to P12) is not committed anywhere in the repository or its branches.

#### 3.5c RSA PKCS#1 v1.5 signature verification (M)

`crates/clazel-pkcs1`. RFC 8017: §4.1 I2OSP, §4.2 OS2IP, §5.2.2 RSAVP1,
§8.2.2 RSASSA-PKCS1-v1_5-VERIFY, §9.2 EMSA-PKCS1-v1_5-ENCODE with the
`DigestInfo` encodings for SHA-256, SHA-384 and SHA-512 (the exact octet
strings in §9.2's Notes, also derivable with 3.5a's encoder: prove they
agree). Our own multiple-precision arithmetic over `u64` limbs, with a
`nat` spec: comparison, subtraction, Montgomery or plain modular
multiplication, and square-and-multiply exponentiation for a public
exponent up to 2^64 (RFC 8017 allows any; the cap is a modelling choice)
and a modulus of 2048 to 8192 bits, proven `pow(s, e) % n` against the
spec and panic-free. The inputs are all public, so there is no
constant-time requirement, and the file says so. The digest is an input
(libcrux-sha2 computes it in 3.5f). Independent: FIPS 186-5 §5.4 / the
PKCS #1 v1.5 text of RFC 2313 §10.1 for the padding, and Knuth's
Algorithm M / D or Menezes, van Oorschot and Vanstone, *Handbook of
Applied Cryptography* §14.2 to §14.3 for the arithmetic, proven equal.
Conformance: the signature vectors of Wycheproof (`rsa_signature_*_test.json`,
Apache-2.0) and FIPS 186-3 `SigVer15_186-3.rsp`, vendored with converters;
a differential against the `rsa` crate (RustCrypto) as a `test` row;
a Kani harness on the limb arithmetic for small widths.

**As built** (on `main`): `crates/clazel-pkcs1`, tier 2 (raised on CI's full verification of the pull request
that raised it; `main`'s run at `35160d8` measured Verus 170 verified and 54 of 54 mutations certified). `src/spec.rs` transcribes RFC 8017
§4.1, §4.2, §5.2.2, §8.2.2 (the steps are `rsassa_pkcs1_v1_5_verify_steps`,
under the domain restrictions of `rsassa_pkcs1_v1_5_verify`) and §9.2 with
Note 1's three `DigestInfo` prefixes as literals; its header lists the
modelling choices (a digest of the wrong length is "invalid signature",
`3 <= e <= 2^64 - 1`, 2048 to 8192 bit moduli, plain equality of the encoded
messages). `src/bignum/` is the arithmetic: little-endian `u64` limbs with
`value`, add, subtract, compare (the borrow of the subtraction), and
**double-and-add modular multiplication** (not Montgomery: add, subtract
and a loop, any modulus, a proof that is a chain of congruences),
right-to-left square-and-multiply for any `u64` exponent, and OS2IP by
Horner's rule; `src/verify.rs` is `verify` and `encode_message`. Everything
executable is proven against `contract.rs` (Verus: 169 verified, 0 errors),
which includes absence of panics and overflow. Lemmas (`lemmas.rs`): I2OSP
and OS2IP are inverse, the modulus range check, the prefix lengths (and
that their length octets say `tLen - 2` and `hLen`), a representative at
least `n` and a signature of the wrong length are rejected, and
`lemma_sign_verify`, the RFC's correctness claim for the textbook signer,
**with the Carmichael-exponent property of the modulus as a hypothesis**
(Fermat's little theorem is not in `vstd` and is not proven here); it is
not a security claim. `examples.rs` proves known answers by evaluation
(`compute_only`); to make 2048-bit moduli evaluable, `pow256` and `two_to`
recurse by squaring and are proven equal to `vstd`'s `pow` and `pow2`.
Independent: `independent.rs` is RFC 2313's parse-the-block-and-compare
verification with HAC Algorithm 14.79, proven to accept exactly what the
spec accepts (the parse-versus-build difference is the Bleichenbacher
case); `bignum/independent.rs` is HAC Algorithm 14.12 (multiplication),
proven to compute the product. The HAC numbers are from memory (the
chapter PDF could not be read here) and the brief's "14.7" is, as the
author recalls, the addition algorithm; Algorithm 14.20 (division) is not
transcribed. Both files were written by the agent that wrote the spec. 54
mutations, every one a certified kill (`mutations.json`; the certificates
live in the empty module `certificates.rs`, because a certificate is
verified with its module and the examples fail under a mutated spec). Kani:
seven harnesses (`adc`, `sbb`, and `add`, `sub`, `lt`, `shl8_add`,
`mod_add` for every 2-limb input against `u128`), not `mod_mul` (CBMC does
not unroll 64 iterations per limb in reasonable time); "multiply by a limb"
is `shl8_add`, the multiplication the code has. Conformance: Wycheproof at
commit `d17cc89f`, 1035 vectors (2048-bit SHA-256 and SHA-384, 3072-bit
SHA-256, 4096-bit SHA-512), 1031 pass and the four `acceptable`
`MissingNull` vectors are expected failures (listed by `tcId` in the test);
35 hand-built cases, several made by OpenSSL, including the e = 3
Bleichenbacher forgery, signatures of at least `n`, a wrong `DigestInfo`,
bad and short padding, 1024-, 2047- and 8200-bit moduli, `e` of 0, 1 and 2
and `e = 2^64 - 59`; bit flips of every valid vector. A new converter,
`xtask/src/testdata/wycheproof_rsa.rs`; `sha2` and six more packages as
`test` rows. **Not done, and why:** the named `rsa_signature_test.json`
does not exist at the pinned Wycheproof commit (the legacy directory was
removed; `SOURCE.md` says what replaced it); the 8192-bit Wycheproof file
was vendored and dropped (about two seconds per verification in a debug
build, nine minutes for 258 vectors, for the checks the 4096-bit file
already makes; the size limit has two hand-built cases); FIPS 186-3
`SigVer15_186-3.rsp` was not vendored; no differential against the `rsa`
crate (35 packages with default features off, over the ten allowed), so
OpenSSL, through the hand-built cases, is the only independent engine;
the equality of the `DigestInfo` literals with a DER encoding is left to
3.5f. Measured (Apple M-series, `cargo test`): one verification with a
2048-bit key and `e = 65537` takes about 120 ms in a debug build (9 ms
release), and one with an 8192-bit key about 2 s; the Wycheproof run takes
about four minutes in a debug build, so the arithmetic is quadratic with a
large constant and Montgomery multiplication would be the next step if it
matters. Under Miri the test runs only the exponent 3 vectors and the
hand-built cases with `e <= 3`.

#### 3.5d TLS 1.3 record layer and handshake message formats (L)

`crates/clazel-tls`. RFC 8446 §3 the presentation language (fixed and
variable-length vectors, enums, the length prefixes) as the one core
decoder; §5.1 `TLSPlaintext` (content types, legacy version, the 2^14
length limit, fragmentation and coalescing of handshake messages across
records, no interleaving with other content types); §5.2 `TLSCiphertext`
and `TLSInnerPlaintext` (padding removal from the end, the 2^14 + 256
limit); §5.3 the per-record nonce as a function of the sequence number;
§4.1.2 `ClientHello` (serialize), §4.1.3 `ServerHello` and §4.1.4
`HelloRetryRequest` (the fixed `Random` value), §4.2 extensions:
`supported_versions` (§4.2.1), `cookie` (§4.2.2), `signature_algorithms`
(§4.2.3), `supported_groups` (§4.2.7), `key_share` (§4.2.8), `server_name`
(RFC 6066 §3), others parsed as opaque and rejected where the RFC says
`illegal_parameter` or `unsupported_extension` (§4.2's table of which
extension may appear in which message is transcribed as a function);
§4.3.1 `EncryptedExtensions`, §4.4.2 `Certificate` (with `certificate_list`
entries as opaque DER for 3.5b), §4.4.3 `CertificateVerify`, §4.4.4
`Finished`, §4.6.1 `NewSessionTicket` (parsed, then ignored: no
resumption in this phase, listed), §4.6.3 `KeyUpdate`; §6 alerts.
Lemmas: serialize then parse round-trips for every message the client
sends; no over-read; bounded reservation; a record never holds more than
one handshake message's worth of state beyond its own bytes (the
coalescing buffer is bounded by 2^14 + the largest message, stated).
Independent: the RFC's Appendix B (the collected presentation-language
definitions), transcribed before the prose, and proven to accept exactly
what the prose parsers accept. Conformance: RFC 8448's handshake traces
(every message of §3 to §7 decoded and re-encoded byte for byte), and a
differential against rustls's message codec as a `test` row on random
and mutated records.

**As built** (on the `phase3/tls` branch, not on `main`): `crates/clazel-tls`, `tier = 0`, `target-tier = 2`; the README
says the key schedule, the state machine and the cryptography are not here.
`spec.rs` is one file (the section 3 reader and writer, section 6 alerts
and the `ErrKind` to alert mapping, section 5 records and the reassembler,
section 4.2 extensions with the table as `extension_allowed`, section 4
messages), its modelling choices listed at its top with numbers: a reader
returns what is left; the AEAD is a parameter (`spec_fn` in the spec, the
`Aead` trait in `record.rs`, which 3.5f implements); handshake bodies are
refused above 2^18 octets and the reassembly buffer is below 2^14 + 4 + 2^18
bytes; `legacy_record_version` must be 0x0303 (0x0301 only on an
unprotected record), stricter than section 5.1's "MUST be ignored"; a type
that is not a row of the section 4.2 table passes it; unknown record and
handshake types are errors; `legacy_version` is read, not checked. Every
parse error is an `ErrKind` with its alert. The proofs are Verus, 418
verified: all the `exec` code (`reader` cursor, `writer`, `record`,
`reassemble`, `extension`, `handshake`, `encode`) is proven against
`contract.rs`, the round trips and their converses, no over-read
(`lemma_*_extend`), bounded reservation, the reassembler's bound,
conservation and prefix lemmas, the nonce lemmas, and the encrypt then
decrypt round trip over any AEAD that opens what it seals
(`lemmas_*.rs`); `examples.rs` and `examples_hs.rs` hold one concrete lemma
per rule and per table row. Two deviations from the plan: the extension
block checks (`check_extensions`) are recursions, with the quantified rules
proven equal, because Verus's evaluator cannot run a quantifier and the
mutation certificates need to; and `independent.rs` (Appendix B as a grammar
of generated strings, proven to accept what the parsers accept for the
messages and bodies listed at its top; `Certificate` is outside its class)
was written after `spec.rs` in the same session and not hidden from it,
which the task wanted the other way round, so it is weaker evidence than
planned. `mutations.json` has 76 mutations, each `killed` with a certificate,
held in `src/certificates.rs`, a module with nothing else in it. Conformance
is `tests/conformance_tls_formats.rs`: RFC 8448 sections 3 to 7 (vectors as
Rust literals in `tests/rfc8448/mod.rs`, with section and line, since an
RFC has no commit for `SOURCE.md`): 39 of 40 messages read and written back
byte for byte, the 40th an expected failure (the section 4 ClientHello shown
before its PSK binders: a prefix of the message at line 972), 41 of 41
records, the reassembler on 24 payloads; 68 hand-built error cases; and a
rustls 0.23.46 differential through `rustls::internal::msgs`, which exposes
the message reader, the fragmenter and the enums but not the handshake types,
so it compares enum numbers (79), all 65536 alerts and every change_cipher_spec
byte, fragmenter output at seven sizes (168), and the acceptance of 16040
handshake messages, 83 of whose differences are classified in the test (we
refuse what rustls leaves to its state machine; rustls reads the data of
extensions we keep opaque and refuses unoffered extensions in a
ServerHello). DEPENDENCIES.md has a `test` row for `rustls`, its six
packages as built (`once_cell`, `rustls-pki-types`, `rustls-webpki`,
`subtle`, `untrusted`, `zeroize`) and the sixteen packages the lock lists
but never compiles (`ring` and what `ring` names). Not done: the tier stays
0 (it is 3.5e and 3.5f that complete the crate, and CI's full run on a pull
request has not been seen); `NewSessionTicket` is parsed and has no
consumer; a client Certificate other than the empty one is written but is
not exercised by the handshake.

#### 3.5e Key schedule and the client handshake state machine (L)

`clazel-tls`. §7.1 the key schedule (`HKDF-Expand-Label`, `Derive-Secret`,
the early, handshake and master secrets, the traffic secrets, `Finished`
keys §4.4.4), §7.2 and §7.3 the traffic keys and their update, §4.4.1 the
transcript hash, and Appendix A.1's client state machine as a transducer
(`step(state, input) -> (actions, state)` with inputs `Bytes`, `Closed` and
actions `Send`, `Deliver(plaintext)`, `Close`, `Fail(alert)`), over
abstract hash, HMAC, HKDF, AEAD, X25519 and signature-verification
functions as parameters (traits with spec functions, as `UrlFns`). Proven:
no application data is delivered before the server's `Finished` has
been verified over the right transcript (§4.4.4); the server's
`CertificateVerify` is checked over the transcript with the context
string of §4.4.3; the certificate chain is handed to 3.5b before any key
derived from the handshake is used to send anything but alerts; every
`Send` is the serialization of a message the state machine chose;
`HelloRetryRequest` is followed at most once (§4.1.4); the prefix lemma
of 3.2 (no action before the bytes that justify it). Conformance: RFC 8448
§3 (a simple 1-RTT handshake) and §5 (HelloRetryRequest), with the traces'
private keys and randoms injected, so the derived secrets and every
encrypted record match byte for byte; RFC 8448 is the independent
transcription's evidence too.

**Key schedule as built (2026-10-25):** `clazel-tls/src/schedule/` now
contains the SHA-256, non-PSK key schedule: separate spec and contracts
(committed before implementation), HkdfLabel encoding, HKDF-Expand-Label,
Derive-Secret, early/handshake/master secrets, client/server traffic-secret
labels, Finished verify_data, traffic updates and ChaCha20's write key/IV.
The executable code refines the RFC equations over a `Crypto` trait; it
adds no axioms and no shipped dependency. All 448 TLS proof obligations
pass locally. RFC 8448 §3 and §5 supply 40 passing key-schedule operations
(including both Finished values and the HelloRetryRequest transcript),
using a test-only RFC 5869 provider over RustCrypto SHA-256; RFC 5869
Appendix A.1 checks that provider. The traces use AES-128-GCM/SHA-256, so
16-byte key vectors exercise generic Expand-Label, not the ChaCha20 helper.
Nineteen new mutation witnesses cover label spelling, HKDF framing,
argument order, zero IKM, derived salts and transcript hashing.
Still missing: the transcript-owning handshake state machine and its
security theorems, CertificateVerify inputs, the libcrux provider and the
end-to-end encrypted traces. The crate remains tier 0; local proof and
vector results do not replace CI's full verification.

**Transcript construction as built (2026-10-25):**
`clazel-tls/src/transcript/` accumulates classified handshake bodies with
their handshake headers, implements §4.4.1's synthetic message_hash rewrite
for HelloRetryRequest, and enforces the first/second Hello progression.
It proves exact append/retry encodings, at most one accepted retry,
a 4 MiB retained-byte bound, and preservation of the accumulator on error.
The §4.4.3 CertificateVerify input builder adds the pad, the server/client
context string, the separator and transcript hash. All 480 TLS obligations
pass locally. Tests construct live transcripts from RFC 8448 §3/§5's 16
messages and match all 12 hash/Finished checkpoints; RFC 8446's explicit
signature-input example passes. The 95 existing mutation certificates now
all pass (the six missing fixture references were fixed); 17 transcript
witnesses are added and require certification by the mutation checker. Authentication
message ordering, server negotiation, signature verification and Finished
verification as state transitions remain for the handshake state machine.
No tier is raised, and full verification is still pending.

**Initial authentication as built (2026-10-25):** `clazel-tls/src/auth/`
now implements the initial client certificate-authentication transducer after
final ServerHello, not just transcript bookkeeping. Specifications/contracts
were committed before implementation. It accepts EncryptedExtensions only
for the stated non-PSK profile's actual offers, allows one CertificateRequest,
validates a nonempty server chain for the captured target/time, checks
CertificateVerify with the validated leaf key and offered TLS 1.3 scheme,
and compares server Finished over the correct transcript using the server
handshake secret. It builds the client's Finished with the client secret,
preceded by an empty Certificate when requested, and releases application
data only after the exact-send acknowledgement. It captures the application
traffic-secret transcript hash immediately after server Finished.

All 532 TLS obligations pass locally, including executable refinement,
finite-trace application gating, terminal absorption and validation-input
binding lemmas. The cheaper test subagent contributed eight tests with
input-sensitive mock providers; the parent reviewed them, and all eight pass
under Miri. Seventeen authentication mutation witnesses are added; their
expanded run subsequently certified all 129 mutations, locally and in CI.
No validator/crypto axiom was introduced.
The X.509/name/time validator, signature verifier and timing-safe Finished
comparison are explicit parameters with no production implementation yet.
Remaining: Hello negotiation, X.509/libcrux joins, protected record-I/O
integration, post-handshake dispatch, independent evidence for the full
client and full verification on both platforms. The crate remains tier 0.

**ServerHello/HRR acceptance (2026-10-25).** `clazel-tls::hello` checks
the fixed TLS 1.3/ChaCha20-Poly1305/X25519 profile's server response and
exact session echo. Version selection follows `supported_versions`, ignoring
the legacy field as §4.2.1 requires. It rejects unsolicited responses,
unoffered groups, wrong share lengths, repeat/no-op retries and retry share
replacement (the sole supported group already has an initial share).
Cookie-only retries return the exact cookie extension_data to echo.
Contracts were committed before implementation. All 557 TLS proof obligations
pass locally; eight server-selection tests pass under Miri. Ten new mutation
certificates are added; their expanded run is pending. ClientHello generation,
binding this stateless checker to the actual offers and retry history,
X25519/shared-secret validation, secret/transcript handoff and record I/O
remain. This does not establish a complete or production TLS client.

The authentication CI run passed base and every crate job, but its final
assembly failed solely because the TLS branch retained the obsolete check
that a generated README table must already match. Main's existing fix
(`10a47d6`, cherry-picked here) aligns that check with the current contributor
policy: report a stale table and let CI update it on main. The table was not
edited. A new full run is still required; no tier is raised.

**Owned Hello exchange and authentication handoff (2026-10-25).**
`hello::client` generates the fixed-profile ClientHello and retains the actual
configuration and transcript. Server validation uses the captured session ID
and retry state. A cookie-only HRR yields a second ClientHello with the original
random/session/cipher/groups/signatures/share and only the cookie extension
added, capped at 4098 bytes of extension_data as a documented resource policy.
The transcript retains the message_hash/HRR/CH2/final-SH sequence.
`hello::join` binds a borrowed private scalar to the public share actually sent,
uses the exact private/peer inputs, rejects provider failure/all-zero shared
secrets, derives client/server handshake secrets over the final-SH prefix,
and starts authentication with the original host/time/offers/transcript.
The caller retains scalar ownership; no erasure guarantee is claimed.

Contracts were committed before implementation. All 595 TLS obligations pass
locally, including offer/configuration binding and nonzero-test equivalence.
Four builder/controller and six key-handoff/mock-authentication tests pass
under Miri. The cheaper subagent supplied these tests and a read-only review;
the parent reviewed the tests. Twelve further mutation certificates cover
construction, key binding, zero rejection, traffic labels/transcript, master
secret source and captured host/time. The expanded full run remains required.
No production crypto, X.509/trust store, entropy source, protected record-I/O
driver or post-handshake dispatcher is joined yet. No tier is raised.

**Protected record epochs and handshake key directions (2026-10-25).**
`clazel-tls::traffic` derives the §7.3 key/IV from an actual traffic secret
and binds the derived key to an owned, parameterized AEAD. Separate send and
receive objects own their own counters, beginning at zero; a successful
record consumes one counter, the last u64 value becomes explicitly exhausted,
and no reset/clone API is supplied. Partial wire input preserves state and
is retained/resubmitted by the caller. Complete malformed or unauthenticated
records permanently disable that epoch. Size/type/padding bounds and exact
header additional-data binding use the existing proven record functions.

`Established::into_record_auth` shares the existing checked Hello derivation,
installs the client handshake secret for sending and server handshake secret
for receiving, and returns those epochs with Auth and the master secret.
The existing `into_auth` handoff is preserved. Contracts were committed before
implementation. All 632 TLS obligations pass locally, including counter,
terminal-state and direction-binding lemmas. Seven traffic/handoff tests pass
under Miri; six existing Hello/authentication-join tests also pass after the
derivation refactor. The cheaper subagent contributed tests and a read-only
review, with the parent reviewing the tests. Thirteen epoch and two direction
mutation certificates were checked individually in isolated copies; the full
expanded run remains required. Strict clippy and all TLS package tests pass.

**Initial connection dispatcher as built (2026-10-26).** `connection::framing`
and `connection::exec` now add a bounded initial record dispatcher on top of
the proved traffic epochs and Auth machine. It buffers partial records, consumes
one complete record prefix at a time, leaves a coalesced suffix to its caller,
drops compatibility CCS only in the pre-server-Finished window, reassembles
and authenticates handshake messages, requires server Finished to end the
record/message flight, protects the exact client flight, and waits for its send
acknowledgement before installing application epochs from Auth's captured
checkpoint. Fatal record/Auth errors drop both directions and partial state;
application data reaches Auth only in Ready. Ready also handles KeyUpdate:
receive epochs rotate independently, requested updates queue a KeyUpdate(0)
response, and send epochs rotate only after exact I/O acknowledgement. It parses
and discards valid NewSessionTicket messages because this profile does not offer
PSK modes or cache tickets; malformed tickets retain parser alerts and duplicate
extensions are rejected. Focused Verus verification of `connection::exec`
passes (29 verified, 0 errors); ten deterministic-provider dispatcher tests
pass locally and under Miri, and strict clippy passes. These providers are not
production crypto or certificate validation.

This does not add socket I/O, post-handshake client authentication, ticket
caching/resumption, 0-RTT, or production AEAD. The no-wrap guarantee remains
per owned epoch and the future transport still owns I/O/timeout policy. Full
combined PR verification remains required and the crate stays tier 0.

**Post-handshake transducer as built (2026-10-31, on `phase3/tls-post-handshake`,
not on `main`).** `connection::post_handshake_*` is the application-traffic
phase of the client as the `step(state, input) -> (actions, state)` transducer
that 3.5e describes: inputs `Bytes` and `Closed`, actions `Send`, `Deliver`,
`Close` and `Fail`. It starts from the two application traffic secrets and owns
both traffic epochs, both secrets and the handshake reassembler. It is a
second, pure formulation of what the dispatcher's `Ready` phase does, with a
spec that has no acknowledgement round trips (a `Send` is final and a key
update takes effect in the same step); joining it to the dispatcher, which
holds those secrets, is not done. Spec and contracts were committed before the
implementation, with fourteen modelling choices listed at the top of
`post_handshake_spec.rs`. What it does, by RFC 8446 section:

- §5, §7.3: records under the application keys; `application_data` is delivered
  as plaintext, in order; one record is processed per step and `consumed` says
  how many bytes it took (an incomplete record consumes nothing); bytes after
  the end of the connection are consumed and ignored (§6.1).
- §4.6.1: NewSessionTicket is read by the existing parser and then ignored
  (listed: no resumption in this phase, no PSK derived or cached); a malformed
  one is `decode_error` or `illegal_parameter` as the parser says.
- §4.6.3, §7.2: on KeyUpdate the server secret, read key, IV and sequence
  number move on for the next record; with `update_requested` the client sends
  KeyUpdate(`update_not_requested`) under its old write keys and then moves its
  write secret, key, IV and sequence number on. A client-initiated update
  (`update_keys`, with or without `update_requested`) does the sending half. An
  invalid `request_update` is `illegal_parameter`. A KeyUpdate must be the last
  message of its record and leave no unfinished message, else
  `unexpected_message` (§5.1: handshake messages must not span key changes).
- §4.6: any other handshake message after the handshake is `unexpected_message`,
  decided by its type byte before its body is read (this client never offers
  `post_handshake_auth`); an unprotected or protected `change_cipher_spec` is
  `unexpected_message` (§5); a handshake message interleaved with another record
  type is too (§5.1).
- §6, §6.1: `close_notify` is answered with the client's own and ends the
  connection (`Send`, `Close`); every other alert, `user_canceled` included, is
  fatal (`Fail`) and is not answered; the transport closing first is `Fail`
  (internal_error, nothing sent); `close()` is the client-initiated close. A
  locally detected fatal error sends the protected alert, then `Fail`.
- §5.3: sequence numbers close or rekey, never wrap. The receive side closes
  (an exhausted receive epoch fails the next record with internal_error). The
  send side rekeys: a data record that would use the last sequence number is
  preceded by KeyUpdate(`update_not_requested`), which uses it, and the data goes
  out at sequence number 0 of the new epoch, so the send epoch is never exhausted
  while the connection is open.

Lemmas stated in `post_handshake_lemmas.rs`: a record that failed to open (or
was incomplete) delivers nothing, and what is delivered is an
`application_data` record's content; a step that ends the connection leaves it
not open, and an ended connection sends and delivers nothing for any later
input (the one-step form of "after `close_notify` or `Fail` nothing more is
delivered"); every `Send` is the encryption of a message the transducer chose
(KeyUpdate, application data, `close_notify`, the fatal alert) under the next
sequence number; read and write sequence numbers are replaced by fresh epochs
exactly on a key update, and an application data record leaves the send epoch and
both secrets alone; the last sequence number rekeys. `post_handshake_examples.rs`
holds 20 concrete lemmas (one per rule, `compute_only`), and `mutations.json`
has 20 new entries (19 `killed` with certificates, one `survives`, an
equivalent mutant explained in its reason).

**Proven, locally.** The spec, contracts, the executable's refinement proofs,
the 20 example lemmas and the lemmas of `post_handshake_lemmas` verify
(`clazel-tls` 814 verified, 0 errors, up from 632), and all 19 certificates
pass, in a local run of CI's per-crate job; CI's own run on the pull request is
pending. One lemma carries a hypothesis: the last-sequence-number rekey holds
when the epoch started from the next client secret is well formed (key and IV
of the lengths expanded). `schedule::spec::Crypto` deliberately leaves
HKDF-Expand's output length unconstrained, so the spec cannot supply this; the
executable establishes it when it builds the epoch. The 25 integration tests
(`tests/post_handshake.rs`) run the executable against an independent model of
the server. The send side's
wrap rule (rekey on the last sequence number) is witnessed in the spec but is
not exercised by a test, because no API positions a counter near 2^64 - 1. RFC
8448's records are AES-128-GCM and cannot be opened by this profile, so its
handshake messages are the plaintext of test-cipher records and no RFC 8448
ciphertext is checked here. `clazel-tls` stays at tier 0.

**The transducer's closure rules (2026-11-05, on `phase3/tls-join`; not run
through Verus, CI's full verification pending).** The maintainer decided that
the transducer replaces the dispatcher's `Ready` phase in production, so that
one machine runs after the handshake and its theorems are about the shipped
code. As the first step it now follows RFC 8446 §6.1: each direction closes on
its own (`Phase::WriteClosed`, `Phase::ReadClosed`, `End::PeerClosed`) and
`user_canceled` changes nothing. The earlier text quoted an immediate
close_notify reply as a TLS 1.3 requirement, which §6.1 is not.

**The handoff (2026-11-05, on `phase3/tls-join-handoff`; local Verus run, 828
verified, 0 errors; CI's full verification and the mutation run pending).**
`Connection` now stops at `Ready`, holding only the two application traffic
secrets, and `Connection::into_post_handshake` consumes it and starts the
transducer from them (`dispatcher_contract::handoff_ensures`). `Client` runs
the transducer after the handshake, so the post-handshake theorems are about
the shipped code. The dispatcher's KeyUpdate, close and application-data rules
are gone, with their lemmas, fixtures, tests and eight mutations; the transducer
has its own for each. It also reports `PeerAlert` apart from its own failures,
and the unreachable message arm whose mutation could only survive is gone.
This changes one behaviour: at the last sequence number the send side now
rekeys, where the dispatcher's seal refused. 3.5f's join of these machines is
recorded there ("The joined client", 2026-11-05).

**The dispatcher's own fatal alerts (2026-11-03, on `main`, #86).** `Connection` (`connection::dispatcher_*`, `exec`) now puts
the RFC 8446 §6 alert on the wire itself. A fatal error it detects is
`Fail(description, wire)`: `wire` is the fatal alert record (§6.2, level
fatal) sealed under the write epoch the server reads next, at that epoch's
next sequence number (§5.3), computed from the state before every key is
dropped (`dispatcher_spec::fatal`, `alert_epoch`, `alert_wire`). That epoch
is the client handshake epoch during the server's flight and the current
client application epoch after the handshake. `wire` is `None` where no
settled write epoch is held: while the client Finished awaits its
acknowledgement, after our close_notify is sealed, while a KeyUpdate awaits
acknowledgement, and when the epoch has failed or spent its sequence
numbers. A fatal alert from the server is `PeerAlert(description)` and is
never answered (§6, §6.2); truncation is `Fail(internal_error, None)`. The
spec's modelling-choices list states each of these, and why no
compatibility CCS precedes the alert and why a close_notify from the server
during its flight is not answered. Spec and contracts were committed before
the implementation. Contracts: `fail_ensures` (the exec `fail` equals
`fatal` on the state at the failure), `peer_alert_ensures` (a decrypted
record that is a fatal alert gives `PeerAlert`), `truncation_ensures`, the
CCS contract over `fatal`, and the close_notify acknowledgement failure with
no alert. Lemmas stated in `dispatcher_lemmas.rs`: the alert uses the settled
epoch's next sequence number; the state after it holds no key, so nothing is
sealed after it under that key; the epoch is one the client holds, in a phase
where the server reads it; no settled key, no protected alert; a peer's
alert is never answered; truncation sends nothing; and four concrete lemmas
evaluated with `compute_only` on fixtures whose AEAD shows its nonce. Eight
new mutations, each `killed` with a certificate: the alert not sent during
the flight, not sent after the handshake, a peer alert answered, the alert
sealed at a used sequence number, the wrong description, warning level, an
alert while a KeyUpdate is pending, an alert after close_notify. The proofs and
certificates passed in CI's full verification green on bf6a9ea. `tests/connection_dispatch.rs` checks each failure's
exact record (decryptable under the expected epoch and sequence number) and
has three new tests (peer alerts in both phases and at both levels; the
sequence number after earlier records; no alert after a sealed close_notify
or before the Finished acknowledgement); 20 pass. `clazel-tls` stays at
tier 0.

#### 3.5f The cryptography and the join (M)

The `shipped` rows for libcrux (`libcrux-chacha20poly1305`,
`libcrux-curve25519`, `libcrux-ecdsa`, `libcrux-p256`, `libcrux-sha2`,
`libcrux-hmac`, `libcrux-hkdf`, `libcrux-rsa` for RSA-PSS, `libcrux-ed25519`,
and the crates they bring, re-measured and pinned exactly), the rule 8
crypto sentence and VERIFICATION.md's TCB entry as 3.0 records them, the
README's safe-Rust line; the instantiation of 3.5e's parameters with
libcrux, of 3.5b's signature checks with libcrux (ECDSA P-256, RSA-PSS,
Ed25519) and 3.5c (RSA PKCS#1 v1.5), and of SHA-256 for 3.5c's digest;
the `clazel-tls` public API the shell drives (`connect(host) -> state`,
`step`). Proven: the joined machine equals 3.5e's for the libcrux
functions' specs (the libraries' functions are axiomatised by their
documented input/output types only, in `axioms.rs` with `// AXIOM:`
lines, and counted in the README).

**As built, the driver (2026-11-02, on `main`, #85).** `clazel_crypto::client::Client` is the public API the
shell drives. It sits in `clazel-crypto`, not `clazel-tls`, because it fixes
the providers (libcrux) and the verifier (`ChainVerifier`), which are this
crate's and which `clazel-tls` cannot depend on. `Client::connect(host, now,
verifier, random)` returns the ClientHello; `receive`, `receive_eof`, `send`
and `close` return the octets to send, the plaintext delivered and the state
(`Handshaking`, `Open`, `Closing`, `Closed`, or `Failed` with the §6.2 alert
and its origin: sent by us, sent by the server, not sent, or truncated). It
owns `Bootstrap`, the key exchange handoff (`traffic::handshake::start`,
which is what `Established::into_record_auth` calls) and `Connection`.
Randomness is a caller-supplied `&mut dyn FnMut(&mut [u8])` (the scalar, the
ClientHello random, the session id); **there is no production source** (it
needs `clazel-sys` and its own audit), and the tests use a fixed seed.
Alerts: before the handshake keys `Bootstrap` sends none, so the driver
writes a plaintext fatal alert. From the ServerHello on, `Connection` seals
the fatal alert itself (3.5e, "The dispatcher's own fatal alerts"), during the server's flight and after the client
Finished alike, and the driver sends the record it returns
(`Fail(description, Some(record))`, origin `Sent`); `PeerAlert` is the
server's alert, never answered (origin `Peer`); `Fail(description, None)` is
a local failure with no settled write epoch (origin `NotSent`). The driver
holds no key: the earlier second copy of the client handshake epoch and the
copy of the server epoch that decrypted the flight in step with `Connection`
(`Shadow`) are removed. Both limits this paragraph first recorded are
superseded by "The joined client" below: `close()` during the server's flight
now sends close_notify, and the join moved into `verus!` in `clazel-tls`.
Tests: 7 unit tests in `src/client.rs` and 8 in `tests/client.rs` against
rustls (ECDSA and RSA handshakes, data both ways over several records,
close_notify both ways, bad_certificate and unknown_ca sealed and read by
rustls; after the handshake, a server record that fails to decrypt answered
with bad_record_mac (20) sealed under the client application key, which
rustls decrypts and reports, and a server alert not answered; truncation).
`tests/conformance_tls.rs` runs through this driver (2026-11-05, stacked on
#114). Its KeyUpdate case is the server's: the driver answers one and has no
way to start one, so a client-requested KeyUpdate is tested only in
`clazel-tls/tests/post_handshake.rs`.

**The joined client (2026-11-05, stacked on #109, not yet on `main`).** The
join moved from `clazel-crypto` into `clazel-tls` as
`connection::driver_exec::Driver`, generic over the providers and the
verifier, so it is inside `verus!`. `clazel_crypto::client::Client` is now a
thin libcrux wrapper around it. The crate boundary recorded in "As built, the
driver" still holds for the wrapper, which fixes the providers and
`ChainVerifier`.

Proven, for any providers meeting the provider contracts
(`driver_contract.rs`):

- A step in the Hello stage is `Bootstrap`'s own `feed`: same octets consumed,
  same record sent, or `internal_error` if that record cannot be built. The
  dispatcher starts only from `Established`, in exactly the state the handoff
  derives from it and our scalar.
- A step of application traffic, `send` and `close` are exactly the
  transducer's `step`, `send_application` and `close`, carried through
  `carry_out`.
- The transducer starts only from the secrets of a dispatcher that reached
  `Ready` (`handoff_ensures`), and plaintext comes from it alone: no step before
  it delivers anything.
- `close` during the flight is `closing`'s sealed close_notify (RFC 8446 §6.1,
  under the next number of the client handshake epoch); before the ServerHello
  it is a plaintext one. `Connection` gained `Action::Close` for this, and the
  earlier limit that nothing was sent there is gone. Both alerts are sealed by
  one spec function, `protected_alert`.

**Not proven, and known:**

- **The flight step's contract is relational, not exact.** `flight_step_ensures`
  says the step consumes no more than its input, stays well formed, sends
  nothing while it stays in the flight, leaves for the transducer only through
  `Ready`, and otherwise ends in a final status. It does not say the result
  equals the dispatcher's `step`; that is `Connection`'s own contract, and the
  join does not restate it. So "the joined machine equals 3.5e's", as this
  item's opening words it, is proven for the Hello and application stages and
  not for the flight.
- **`Client`'s input loop and `send` chunking are tier 0 glue**, plain Rust in
  `clazel-crypto`, outside `verus!`. They are tested, not proven: the `inbox`
  buffering, feeding `Driver::step` until it stops consuming, and splitting
  `send` into records.
- The libcrux functions are trusted to meet the provider contracts, as
  VERIFICATION.md records.

Mutations: 9 `driver-*` and `dispatcher-close-notify-fatal-level`, each certified
(`driver_examples.rs`, `dispatcher_lemmas.rs`). Tests: `tests/client.rs` adds
`closing_during_the_servers_flight_sends_close_notify`, in which rustls decrypts
the record. It reports a close_notify mid-handshake as an error, and the test
asserts that.

#### 3.5g TLS conformance and the trust store (M)

`tests/conformance_tls.rs`: an in-process rustls server (a `test` row, with
`rcgen` or pre-generated certificates) for full handshakes with ECDSA and
RSA chains, with the client's trust store set to the test root; the
hostile-server cases (wrong `Finished`, a certificate for another name, an
expired chain, a self-signed chain, records over the limit, a downgrade to
TLS 1.2, `change_cipher_spec` in the wrong place) each giving `Fail` with
the right alert and no panic; the Mozilla root table regenerated and
checked; and a local measurement, documented not asserted, of which of the
top sites refuse a ChaCha20-only, X25519-only client (run locally, like
the demo). **Raise `clazel-der`, `clazel-x509`, `clazel-pkcs1` and
`clazel-tls` to tier 2** as each earns it.

**As built, first part (2026-10-31, local run, not yet CI-verified):**
`crates/clazel-crypto/tests/conformance_tls.rs`, 17 cases in two suites (5 success and control, 12 hostile), drives our client
(`Bootstrap`, `Established::into_record_auth`, `Connection`, over the libcrux
providers and `join::exec::ChainVerifier`) against rustls 0.23.46 over an
in-memory byte pipe. The server uses rustls's `ring` provider, configured for
TLS 1.3, `TLS_CHACHA20_POLY1305_SHA256` and X25519 only; that adds no package
(`ring` was already a `test` dependency; docs/DEPENDENCIES.md). The
certificates are pre-generated, not `rcgen`: `tests/fixtures/tls` with a
`SOURCE.md` (a test root and intermediate, RSA, signed with PKCS#1 v1.5
SHA-256; leaves for ECDSA P-256 and RSA, the latter with CertificateVerify in
RSA-PSS; for `test.example`). The client's trust store is the test root,
through `ChainVerifier::new`'s anchor parameter; production still uses
`roots::ROOTS` (`join::exec::mozilla`). The client's X25519 scalar,
ClientHello random and session id (and the server's scalar) come from a
fixed, test-only seed through SHA-256.
- *Passing:* a full handshake for the ECDSA chain and for the RSA chain, then
  application data both ways (five 3000-octet records each way after the
  first exchange), a client-requested KeyUpdate, and close_notify both ways.
  rustls sends no NewSessionTicket to this client (it offers no
  `psk_key_exchange_modes`), so ticket handling is covered only by the
  dispatcher's own tests.
- *Hostile servers:* the real rustls flight, decrypted with the handshake
  keys, changed in one place and re-encrypted (the control, unchanged,
  completes the handshake). Each gives the client's `Fail` with the alert in
  parentheses, and the connection is `Failed`: a wrong `Finished` (51) and a
  wrong CertificateVerify, ECDSA and RSA (51); a certificate for another name
  (42); an expired leaf (42, see below) and an expired intermediate (45); a
  self-signed leaf, a leaf without its intermediate and an empty trust store
  (48); a plaintext record over 2^14 (22), and protected records of 2^14 + 257
  and 65535 octets (22), while one of exactly 2^14 + 256 reaches the AEAD
  (20); a ServerHello without `supported_versions` (70), and the same with
  its random ending in the `DOWNGRD\x01` or `DOWNGRD\x00` sentinel (47, see
  below); `change_cipher_spec` with a payload other than
  0x01, with a length other than 1, between the two fragments of a
  ServerHello, as the inner type of a protected record, and after the
  server's Finished (each 10), while the permitted dummy CCS before the
  ServerHello and after it is dropped.
- *A behaviour the test pins that differs from the RFC's likeliest reading,
  left as it is because both alerts are fatal:* an expired leaf gives
  `bad_certificate` (the leaf profile covers validity,
  `join::spec::certificate_error`; an expired intermediate gives
  `certificate_expired`).
- *Downgrade sentinel (2026-11-02, local run, not yet CI-verified):* the
  first part found that a ServerHello selecting TLS 1.2 was always
  `protocol_version`, so RFC 8446 §4.1.3's downgrade-sentinel check
  (`illegal_parameter`) was never reached. It is now checked:
  `hello::spec::below_tls13` gives `illegal_parameter` when a ServerHello
  without `supported_versions` (one "indicating TLS 1.2 or below") has a
  random ending in `44 4F 57 4E 47 52 44 01` or `... 00`, whatever its
  `legacy_version`, and `protocol_version` otherwise; the sentinel is
  checked before the missing version is reported. A ServerHello whose
  `supported_versions` selects TLS 1.3 is not checked (it does not indicate
  TLS 1.2 or below), and one selecting an earlier version there was already
  `illegal_parameter` (§4.2.1). Three certified mutations in
  `clazel-tls/mutations.json` cover the check and each sentinel value; the
  Verus proofs and mutation certificates have not yet run (no Verus on the
  machine that wrote them), and `clazel-tls` stays at tier 0.
- *Not done:* no HelloRetryRequest, a PSK or a client-certificate request is
  exercised (the rustls server never sends one for this client; a scripted
  HRR would need a second key share); no truncated or fragmented-in-flight
  server flight against a real server beyond the dispatcher's own tests;
  no X25519 or ChaCha20 independent of ours on the server side (the server's
  key share uses our libcrux X25519 with a fixed scalar, so that the
  scripted server can derive the handshake keys; the AEAD, signatures and
  hashes of rustls's side are ring's, and agree with ours on every record);
  no socket, no `clazel-net` TLS loop, no `tls: true` in the fetch transducer,
  no kernel `https:`; the Mozilla root table is not regenerated here; the
  local measurement of top sites and the real-certificate corpus below are
  **not run, and no result is claimed**; no crate is raised to tier 2.

**Top-site measurement (2026-11-05, local run, documented not asserted):**
`crates/clazel-net/examples/tls_survey.rs` ran one handshake with the
production verifier against each of the top 1,000 domains of the Tranco list
JZPGY, on port 443, trying `www.<domain>` when the apex gave no answer. Every
domain that failed then got OpenSSL 3.0.13 control handshakes from the same
machine: our suite and group, AES with X25519, ChaCha20 with P-256, OpenSSL's
default TLS 1.3 offer, and TLS 1.2. No server caused a panic.

| Result | Domains |
|---|---|
| Handshake completed | 577 |
| No DNS record for the domain or its `www` (mostly infrastructure domains) | 179 |
| Has DNS, but OpenSSL's controls got no TLS either | 56 |
| TLS 1.2 only | 123 |
| TLS 1.3, needs AES (X25519 is enough) | 15 |
| TLS 1.3, needs P-256 (ChaCha20 is enough) | 4 |
| TLS 1.3, needs AES and a group other than X25519 together | 23 |
| Needs `ecdsa_secp384r1_sha384`, which the ClientHello does not offer | 6 |
| Refused correctly: the name does not match | 11 |
| Refused correctly: the chain does not verify in OpenSSL either | 3 |
| Refused by the public-suffix wildcard rule | 2 |
| Unstable: airbnb.com's answer changed between runs, for both clients | 1 |

So 577 of the 765 domains with a TLS server answered this client (75%).
- *TLS 1.2 (16% of the 765)* is the largest group, and 3.0's decision to speak
  TLS 1.3 only is its cause. Among them, 21 end the handshake with a
  close_notify rather than an alert.
- *AES and P-256 (42, 5.5%)* include microsoft.com, bing.com, office.com,
  live.com, outlook.com, azure.com and ebay.com. This is the "one suite, no
  AES" risk, and it is material. These controls ran with OpenSSL's signature
  list, so some may also need the scheme below.
- *`ecdsa_secp384r1_sha384` (0x0503):* cnn.com, telekom.de, statista.com,
  namecheap.com, pbs.org and www.kaspersky-labs.com. With our exact signature
  list OpenSSL fails on each as we do, and adding this scheme makes each
  succeed. Some servers refuse (40), and others use the scheme unoffered,
  which we refuse (47); cnn.com ends in 10. `clazel-p384` already checks P-384
  signatures in chain links, not yet in CertificateVerify.
- *Public-suffix wildcards:* `dns_match` refused a wildcard over any public
  suffix, including the PSL's private section, so `*.githubusercontent.com`
  and `*.github.io` never matched. www.githubusercontent.com and
  www.wixsite.com were the two in this list, and raw.githubusercontent.com
  failed the same way. OpenSSL accepts them. Decided (maintainer, 2026-11-05):
  the veto covers the ICANN section only, as BR 2.3.1 §3.2.2.6 and Chromium's
  `VerifyHostname` do, and x509-limbo's case refusing such a wildcard is an
  expected failure. The table above is the run before that change.

Limits: one vantage point on one day, domains rather than the hosts pages
use, and a domain's apex stands for it unless it gave no answer. The
list and raw results are not vendored.

**Real-certificate compatibility measurement:** vendor a reproducible corpus
of complete, original DER chains, with collection date, source, licence and
SHA-256 fingerprints. Deduplicate certificates by fingerprint, retain their
leaf/intermediate/root role, and report both certificate and chain totals.
Measure explicit `Extension.critical = FALSE` separately from malformed
BOOLEANs and other DER errors: our current X.690 §11.5 profile rejects that
explicit DEFAULT. Report affected certificates, extension OIDs and chains,
including how many chains fail solely for this encoding. Compare the same
original bytes against the independent certificate engine(s) used by the
conformance suite; record their versions and acceptance differences.

Keep explicit-FALSE fixtures for the strict result and any compatibility
result. Decide whether to retain strict rejection or introduce a documented
certificate-profile exception only after recording those measurements and
the interoperability rationale. Any exception needs its own spec, proofs
and negative cases; it must preserve the original signed TBS bytes and must
not relax the general DER decoder.

**Measured (2026-11-05):** `clazel-crypto/tests/conformance_real_chains.rs`
over `tests/fixtures/real-chains-2026-11-05` (`SOURCE.md` there): the chains sent
by the hosts of the top-site measurement, 760 chains and 2,276 certificates
sent, 868 distinct (709 only ever leaves, 156 only ever later in a chain, 3
both; 14 are in the root table).
- *Encoding:* all 868 decode. A separate DER walk, outside the crate's
  decoders, found no explicit `critical` FALSE and no malformed BOOLEAN, so no
  extension OID, certificate or chain is affected, and no chain fails for this
  encoding. `extensions.rs` keeps the strict result's fixture.
- *Against `rustls-webpki` 0.103.16* (through rustls 0.23.46 and ring, on the
  same bytes, with real signatures, the same roots, host and time): both accept
  725 and both refuse 35. The first run differed on 4, where webpki accepted
  and we refused a wildcard over a suffix in the PSL's private section
  (www.azurefd.net, www.azureedge.net, www.wixsite.com,
  www.githubusercontent.com); limiting `dns_match`'s veto to the ICANN section
  removed them. The test fails on any difference.
- *Limits:* one day's chains from popular sites, which are mostly recent
  certificates. It says nothing of older or private ones.

These measurements give no reason for a certificate-profile exception. The
decision to keep strict rejection is the maintainer's and is not yet recorded.

#### 3.5h Certificate revocation: a pushed set (L, after 3.5g and 3.10)

**Decided (maintainer, 2026-11-03): option 1, a revocation set pushed to
the browser**, in the style of Firefox's CRLite or Chrome's CRLSets, not
online OCSP or CRL downloads during the handshake (slow, a leak of what is
browsed to the CA, and they fail open) and not stapled OCSP alone (only the
servers that staple are covered).

Today RFC 5280 §6.1.3 (a)(3) is already a parameter of the proven path
validation (`clazel_x509::path::spec::RevokedFn`, the `RevocationOracle`
trait), every path theorem holds for every revocation function, and
production passes `NothingRevoked` (`clazel-crypto`'s `join`): a revoked
certificate is accepted. This item replaces that oracle; the path proofs do
not change.

- **3.5h.0 Decision (S), before any code:** which set. Record checked facts
  (each read from its source, with the date) for CRLite and for CRLSets:
  the format and whether it is specified; who publishes it, where, how
  often and under what licence; how an update is signed and with what key;
  how big it is; what it covers (which CAs, which revocation reasons, and
  whether the absence of a certificate means "not revoked"); and how a
  client queries it (issuer key hash and serial, or a filter cascade). The
  choice and its accepted costs go here, as 3.0 did for TLS.
- **The set's parser (ours, CLAUDE.md rule 8; target tier 2):** a spec
  transcribing the chosen format with its step numbers, a parser proven to
  it (total, never reads past its input, refuses anything else), examples,
  certified mutations, conformance against the publisher's own files and an
  independent engine (a `test` row). Crate: `clazel-crlite`, new; only
  the SCT-list parser goes in `clazel-x509`.
- **The oracle:** `revoked(set, cert)` as a pure spec function of the set
  and the certificate (whatever 3.5h.0's format keys on), an executable one
  proven equal to it, and a `RevocationOracle` holding a set. A theorem: a
  path whose certificate the set lists is refused with
  `PathError::Revoked`. Revisit the alert: `join` maps `Revoked` to
  `unknown_ca` (48) today; RFC 8446 §6.2 has `certificate_revoked` (44).
- **Updates (shell, tier 0):** fetched over our own `https:` client (3.6,
  3.8), its signature checked with the publisher's key by proven code
  before it replaces the stored set (3.10). The schedule and the key are
  3.5h.0's.
- **Staleness (decided 2026-11-05, 3.5h.0):** revocation fails open.
  `clazel fetch` always says how old the set is, or that there is none.
- **Tests:** a revoked certificate refused end to end (a fixture chain
  with a test set, and, run locally like the demo, a public test site with
  a revoked certificate); a set that does not parse or whose signature
  fails is not used; an expired set follows the staleness rule.

#### 3.5h.0 Checked facts and the options (2026-11-03; decided 2026-11-05: CRLite)

These facts were checked on 2026-11-03 against the sources cited. The
sizes and counts were measured that day from the publishers' own live
endpoints, using a scratch script outside the repository. "Unverified" marks
anything that could not be checked. A recommendation and the maintainer's
decision follow the facts.

**CRLite (Mozilla).**
- *What it is and who uses it.* CRLite ships the full set of revocations
  to the client, which queries it locally. Firefox enabled it for all
  desktop users in Firefox 137
  ([Mozilla Hacks, 2025-08-19](https://hacks.mozilla.org/2025/08/crlite-fast-private-and-comprehensive-certificate-revocation-checking-in-firefox/)).
- *Publisher and pipeline.* The set is built by Mozilla's open pipeline
  ([`mozilla/crlite`](https://github.com/mozilla/crlite), MPL-2.0; at
  commit `0082998261`, 2026-08-03). It takes certificates from CT logs
  enrolled by a Mozilla engineer (the `ct-logs` collection), and
  revocations from the CRLs that CAs disclose to CCADB. Only issuers in
  Mozilla's root program are included
  ([wiki FAQ](https://github.com/mozilla/crlite/wiki)).
- *Where it is published.* Remote Settings, bucket `security-state`,
  collection `cert-revocations`
  (`https://firefox.settings.services.mozilla.com/v1/buckets/security-state/collections/cert-revocations/records`).
  The files are attachments under
  `https://firefox-settings-attachments.cdn.mozilla.net/`.
- *Channels and coverage.* There are two channels.
  - `default` keeps every revocation.
  - `compat` keeps only the reasons keyCompromise, cessationOfOperation and
    privilegeWithdrawn.

  Both definitions are in `moz_kinto_publisher/main.py` (`CHANNELS`) and
  `rust-create-cascade/src/main.rs` (`ReasonSet::Priority`).
- *Sizes, measured.* On 2026-11-03 the collection held:
  - one full filter per channel, from 2026-10-17: `default` 6,006,419
    octets, `compat` 1,574,015 octets;
  - 34 deltas per channel since then, about two a day: `default` 203,061
    to 445,838 octets (237,246 on average), `compat` 122,497 on average.

  That is about 475 KB a day on `default`, against the Hacks post's "300
  kB per day". A full filter lasts at most 45 days (`max_filter_age_days`).
- *Format.*
  - Each file starts with a 2-octet little-endian encoding number.
  - The live files are `03 00`, encoding V3: a `bincode` 1.3
    serialization of the `clubcard-crlite` crate's Rust structures
    (`CRLiteClubcard::from_bytes`,
    [`mozilla/clubcard-crlite`](https://github.com/mozilla/clubcard-crlite)
    0.6.2, MPL-2.0, at `054c1799ae`).
  - Version 0.6.2 also defines V4, a TLS-style encoding described only in
    comments in `src/codec.rs`. No live file uses it.
  - The filter is a pair of ribbon filters partitioned by issuer
    ([`mozilla/clubcard`](https://github.com/mozilla/clubcard) 0.3.4). Its
    README says "Neither the API nor the serialization format for clubcard
    are stable".
  - There is no specification beyond this code.
- *Query.*
  - The key is `SHA-256(issuer SPKI hash ‖ serial)`, where the issuer SPKI
    hash is the SHA-256 of the issuer's SubjectPublicKeyInfo
    (`CRLiteKey::new`).
  - The query also needs a (CT log ID, timestamp) pair from one of the
    certificate's SCTs (`CRLiteQuery`).
  - The result is `Good`, `Revoked`, `NotEnrolled` (issuer not in the set)
    or `NotCovered` (no SCT, or one outside the logs' covered time ranges:
    `in_universe`).
  - Within the covered universe, absence does mean not revoked. That is
    the design's point: false positives are removed by an exact second
    filter.
  - Firefox falls back to OCSP for certificates that aren't covered (wiki
    FAQ). clazel has no OCSP.
- *Signing.* The collection, not each file, carries a Remote Settings
  content signature.
  - Algorithm: ECDSA P-384 with SHA-384 (`mode: p384ecdsa`, signer
    `onecrl_202402`). The signed message is `"Content-Signature:\x00"`
    followed by canonical JSON of the records, sorted by `id`, together
    with `last_modified`
    ([application-services `signatures.rs`](https://mozilla.github.io/application-services/book/rust-docs/src/remote_settings/signatures.rs.html),
    [Autograph `contentsignature`](https://pkg.go.dev/github.com/mozilla-services/autograph/signer/contentsignature)).
  - Each record holds its attachment's SHA-256. The downloaded delta
    `20261103-1-default.filter.delta` (255,061 octets) matched its
    record's hash.
  - The `x5u` URL serves a PEM chain of three certificates:
    1. an end-entity `onecrl.content-signature.mozilla.org` (P-384), valid
       2026-09-26 to 2026-12-15, so it rotates about every 80 days;
    2. an intermediate `Content Signing Intermediate` (P-384);
    3. a root `root-ca-production-amo` (RSA-4096, SHA-256 of its DER
       `c8a80e9a…a106db`).

    Firefox pins that root by hash.
- *Licence of the data.* Unverified. Neither the repository nor Remote
  Settings states terms for clients other than Firefox.

**CRLSets (Google).**
- *What it is.* Chrome's pushed set. Chromium's page says "A subset of the
  certificates identified as revoked" on the crawled CRLs is included,
  and that "the process by which they are generated is not" public
  ([chromium.org, CRLSets](https://www.chromium.org/Home/chromium-security/crlsets/),
  no date shown).
- *Coverage.* Coverage is curated. Absence doesn't mean "not revoked":
  `CheckSerial` returns `GOOD` for a listed issuer whose serial is absent,
  but the set is a subset by design. Which reasons are kept is
  unpublished (unverified).
- *Delivery.*
  - Google's component updater (Omaha), app ID
    `hfnkpimlhhgieaddgfemjhofmfblmnib`. The update request goes to
    `https://clients2.google.com/service/update2/crx` and gets an XML
    response that names a CRX3 file
    ([`agl/crlset-tools`](https://github.com/agl/crlset-tools), 2026-08-05).
  - Requests are put in cohorts. On 2026-11-03, version 10881 was
    36,966 octets for "Auto androidlowmem" (the default: 204 issuers, 994
    serials) and 2,031,437 octets for "Auto full" (`tag=force_full`: 415
    issuers, 117,604 serials).
  - Both also carry 177 `BlockedSPKIs` and 9 `BlockedInterceptionSPKIs`.
  - `NotAfter` is 2026-11-07, four days later.
  - Whether a client that isn't Chrome may use this service is
    unverified. Chromium's page licenses its own text (CC BY 2.5), not the
    service.
- *Format.* The format isn't specified anywhere except in code.
  - A CRX3 file: `Cr24`, a version number, and a protobuf `CrxFileHeader`
    (`components/crx_file/crx3.proto`), followed by a ZIP. In version
    10881 every entry was "Stored", uncompressed, but nothing promises
    that.
  - Inside it, `crl-set` is described in the comment at the top of
    `net/cert/crl_set.cc`: a 2-octet little-endian header length; a JSON
    header (`Version` 0, `ContentType` "CRLSet", `Sequence`, `NotAfter`,
    the SPKI lists); then repeated entries of a 32-octet parent SPKI
    SHA-256, a 4-octet little-endian count, and serials each preceded by a
    1-octet length.
- *Query.* By the issuer's SPKI SHA-256 and the serial, with leading zero
  octets removed (`CRLSet::CheckSerial`), plus `CheckSPKI` against the
  blocked keys.
- *Signing.*
  - CRX3 proofs over `"CRX3 SignedData\x00"`, the signed header data's
    4-octet length, the signed header data, and the archive
    (`components/crx_file/crx_verifier.cc`, `crx_file.h`).
  - Chromium requires the proof whose SPKI SHA-256 is
    `kCrlSetPublicKeySHA256` (`75daf8cb…edb84397`,
    `chrome/browser/component_updater/crl_set_component_installer.cc`).
    In the downloaded file, that is an RSA-2048 key signing with PKCS#1
    v1.5 and SHA-256.

**What each would cost clazel.** Under CLAUDE.md rule 8, every parser
below is ours.

| | CRLite (`default`) | CRLSets ("Auto full") |
|---|---|---|
| Coverage | every revocation on CCADB-disclosed CRLs, for certificates with an SCT in an enrolled log; not covered → no answer | a curated subset; absence proves nothing |
| Download | ~6 MB every ≤45 days plus ~475 KB a day | ~2 MB a version, full each time (`DeltaFrom` 0) |
| Set format | bincode V3 of Rust structures, declared unstable; V4 documented only in code | small binary body; a JSON header |
| Container | none (Remote Settings JSON records, an attachment) | Omaha XML, a CRX3 protobuf header, ZIP |
| Signature | P-384 ECDSA (`clazel-p384`, P17) over canonical JSON, needing a JSON parser and a canonical serializer; a three-certificate chain to a pinned RSA-4096 root, rotating about every 80 days | RSA-2048 PKCS#1 v1.5 (`clazel-pkcs1`) with a pinned key hash |
| New parser in X.509 | the SCT list extension (RFC 6962 §3.3), for the coverage check | none |
| Spec source | code only (`clubcard`, `clubcard-crlite`) | code only (`crl_set.cc`, `crx3.proto`) |
| Terms for other clients | unverified | unverified; it means acting as a Chrome component client |

**Recommendation: CRLite, `default` channel.** Exit criterion 6 is that a
revoked certificate is refused. Only CRLite can say that a covered
certificate is *not* revoked, and its pipeline, coverage rule and query are
public, while CRLSets' selection isn't. clazel already has the P-384 and
X.509 code its signature needs. The costs to accept:
- *An unstable format.* The spec transcribes the code of a pinned
  `clubcard-crlite` version, with its encoding number. A new number is
  refused, not guessed, and moving to V4 is an erratum-style update.
- *Canonical JSON.* We need a JSON parser and a canonical serializer for
  the records, both ours and proven.
- *An SCT-list parser* in `clazel-x509`.
- *About 475 KB a day*, or `compat`'s about 120 KB a day for the three
  priority reasons only, if bandwidth matters more than coverage.
- *A staleness rule* for `NotCovered` and for an old set (3.5h's
  staleness bullet). There is no OCSP to fall back to.
- *Asking Mozilla.* Whether a third-party client may use the endpoint is
  unverified. Asking is outward contact, so it is left to the maintainer;
  no agent contacts Mozilla or Google.

**Decided (maintainer, 2026-11-05): CRLite, `default` channel**, with the
costs above accepted. Still open: the terms question for Mozilla.

**Decided (maintainer, 2026-11-05): staleness fails open.**
- With no set, or one that cannot be used, the connection proceeds with no
  revocation check, and `clazel fetch` says so.
- An old set is still used, since what it lists as revoked stays revoked, and
  one older than 45 days (`max_filter_age_days`) is flagged as stale.
- `NotCovered` and `NotEnrolled` count as not revoked. Firefox falls back to
  OCSP there and clazel has none, so this is the accepted gap.
- Failing closed is not an option: updates arrive over our own `https:`
  client, so a set that blocked connections could not be replaced. The cost
  accepted is that a stale set can let a revoked certificate through.

**Decided (maintainer, 2026-11-05): a new crate, `clazel-crlite`, target tier
2**, for the filter format, the signed records, the JSON parser and canonical
serializer, and the oracle. None of it is X.509, and the format is declared
unstable, so its updates stay out of `clazel-x509`. Only the SCT-list parser
goes in `clazel-x509`. The JSON code moves out if something else needs it.

### 3.6 The client state machine (L)

`crates/clazel-fetch`. A pure transducer: `start(url, jar, now, context)`
gives the first action (`Connect { host, port, tls }`), and
`step(state, input)` maps an input (`Connected`, `Bytes(b)`, `Closed`,
`Error`) to actions (`Send(bytes)`, `Close`, `Done(response)`,
`Fail(reason)`) and the next state; the jar is part of the state and comes
back updated. It takes the HTTP functions (3.2) and URL functions as
parameters, as the kernel takes `UrlFns`, and `clazel-fetch` joins them to
the real ones in its last commit, like 2.13.

What it decides, each cited: the request (RFC 9112 §3.2.1 origin-form
target from the URL's path and query; `Host` from the URL, RFC 9110 §7.2;
`Connection: close`, one request per connection in this phase; `Accept:
*/*`; `User-Agent`), the `Cookie` field from RFC 6265bis §5.8.3 with the
HTTP request context of §5.2 (a navigation, top-level, GET, the redirect
chain's same-site status as §5.2.1 computes it), `Set-Cookie` field lines
of the response stored one by one by §5.7 as HTTP (never for a 1xx
response, §5.3), the `Secure` requirement from whether the connection is
TLS, redirects (RFC 9110 §15.4: 301, 302, 303, 307 and 308 with a
`Location`, resolved against the request URL by the URL parser; at most 20,
Fetch §4.4 step 5; a redirect to a non-HTTP(S) scheme fails), and failure
on anything else (an unsupported transfer coding, an invalid message, a
response that is not complete when the connection closes, unless §6.3
step 8 says close ends it).

Proven: `theorem_wire_cookies`, that in every trace the bytes of every
`Send` are the serialization of a request whose only jar-derived part is
the `Cookie` field value, and that value is §5.8's retrieval for that
request's URL and context; `theorem_jar_frame`, that the jar changes only
by §5.7 storage of the response's own `Set-Cookie` lines (so the Phase 2
root lemmas carry over); totality (at most 21 requests per fetch) and that
no action is emitted before the bytes that justify it (from 3.2's prefix
lemma). Mutations for each decision. Independent: the Fetch Standard's
"HTTP-redirect fetch" and the cookie steps of "HTTP-network-or-cache
fetch", transcribed and proven to give the same request sequence on a
stated class (no caching, GET only, no CORS).

**As built** (on `main`, `http://` only): `crates/clazel-fetch`, tier 2 (raised on CI's full verification of the pull request that raised it; `main`'s run at `35160d8` measured Verus 164 verified and 64 of 64 mutations certified). Besides the `request`
module, `src/transducer/`: `spec.rs` (the transducer: `start(url)` gives
`Connect { host, port, tls }`, `step(http, urls, state, input)` maps
`Connected`, `Bytes`, `Closed`, `Error` to `Send`, `Close`, `Done { url,
response }`, `Fail(reason)`; interim 1xx responses skipped, a
close-delimited body ended at `Closed`, failure on an invalid message, an
unsupported coding or a response incomplete at close; redirects as Fetch
§4.5 steps 3 to 8, 18 and 22, commit `59afe34…` of 19 October 2026, with
§2.2.3's redirect statuses and §2.2.6's location URL), `contract.rs` (exec
contracts, the traits `HttpFnsExec` and `UrlFnsExec` the parameters are
passed as, and the theorem statements), `step.rs` and `types.rs` (the exec
transducer, proven equal to the spec), `theorems.rs`, `real.rs` (the join:
`parse_response`/`parse_response_at_close` for a GET, and a `Location`
value UTF-8 decoded and parsed by the basic URL parser against the request
URL; `step_real`) and `examples.rs`. The plan cites "Fetch §4.4 step 5"
for the limit; in the pinned Fetch text it is §4.5 HTTP-redirect fetch,
step 7. `Connect.tls` is always false and an `https:` URL (also as a
redirect target) fails as not fetched. `clazel-net`'s `fetch` now only
carries out the transducer's actions; `clazel fetch URL` follows
redirects. Verus: `clazel-fetch` 128 verified, 0 errors (2026-10-25). **Proven**, for
every HTTP and URL function: `theorem_requests_bounded` (at most 21
`Connect`s and 21 `Send`s in any trace), `theorem_redirects_bounded`,
`theorem_url_changes_only_by_redirect` (to an HTTP(S) URL, count plus
one), `theorem_sends_are_requests` (every `Send` is `request_bytes` of the
current URL), `theorem_silent_until_decided` (no action on `Bytes` until
the parser, past the interim responses, is not `Incomplete`), and
`theorem_split_invariant` (bytes `a` then `b` give what `a + b` gives, so
no decision is taken on fewer bytes than it needs) for every parser that
is `prefix_stable`. **Proven of the shipped client** (`real.rs`):
`theorem_real_prefix_stable`, that `real_http()` is `prefix_stable`, from
`clazel-http`'s `lemma_parse_response_append` (the append lemma behind
`theorem_monotone`, which fixes the octets after a finished response to
`rest + more`), and so `theorem_real_split_invariant`. The exec
transducer does not re-parse: `HttpFnsExec` is `new_parser`, `feed` and
`parse_at_close` on a `clazel-http` `ResponseParser`, which the reading
state holds (its view's `received` is the parser's), and `step` feeds it
only each `Bytes` input's new octets, starting a new parser on the octets
after an interim response and at each new connection; `RealHttp`'s
invariant `parser_ok` is the parser's `wf` for a request that is not
`HEAD`, kept as `state_ok`, which `start` gives and `step` requires and
keeps. **Not proven**: that the
real parser always consumes at least one octet for a finished response
(the interim-skipping guard turns the other case into `Invalid`; it only
affects liveness), and anything about the real URL parser beyond its own
proofs: the examples run the transducer with the real HTTP parser but a
stand-in URL function, because Verus does not finish evaluating them with
the real one. Mutations: 34 in `mutations.json`, all certified kills (17
of the request spec, 17 of the transducer: the five redirect statuses
dropped and 304 added, the limit check off by one either way and the
limit raised to 21, the scheme check removed, interim responses not
skipped, the open-connection parser used at close, `Close` after the
server closed, two `Location`s accepted, none treated as failure, the
fragment dropped, the request not sent); two are killed by theorems, the
rest by examples. Tests: `clazel-net` against local servers, a redirect
chain through all five statuses with relative and absolute `Location`s,
exactly 20 redirects followed, the 21st refused after exactly 21
requests, `mailto:` and two-`Location` redirects.

**Tier 2 evidence added (branch `claude/heuristic-zhukovsky-53e777`, from `phase3/fetch-kernel-join`; tier still 0 until CI's full run):** (1) *Whole-run equivalence.* `independent.rs` gains `theorem_independent_run` (from `lemma_independent_run`, by induction over the hops): for any URL, any jar and any hops a well-behaved shell delivers whole (`Connected`, then one `Bytes` that the parser reads as a final response), the transducer driven by `step` (`tx_fetch`) sends the request bytes of Fetch's own loop (`indep_fetch`, a recursion over the URL list: HTTP-redirect fetch, then main fetch), leaves the same jar (retrieval and `Set-Cookie` storage at every hop) and ends the same way (response, network error, or waiting). No spec or contract changed. (2) *Conformance against independent engines.* `tests/conformance_differential.rs`: 1500 random redirect chains through the client against a Fetch §4.5 loop built on rust-url (`Location` resolution) and `cookie_store` (cookie storage and the `Cookie` field), all agree; no new package (the same pins as `clazel-cookie`'s differential). No WPT `fetch/` suite is vendored, so none is run. (3) *Mutations.* Five mutations had stopped applying when the jar left the transducer's state (their `find` text no longer matched `spec.rs`): `close-closes-again`, `jar-after-retrieval-dropped`, `storage-after-redirect-decision`, `storage-skipped` and `cookie-string-wrong-time` now mutate the current code (same `expect`, same certificate lemmas). Twelve new certified kills for decisions that had none (examples `lemma_transducer_16` to `_27`): the connection closed or not on `Closed`, `Error`, `Connected` and `Bytes` in the wrong phase, an interim response at close, the reasons `Invalid` and `Unsupported`, `tls: false`, a URL with no request, the octets kept while a head is incomplete, input after the end.

**Cookies.** The jar (`clazel-cookie`'s model), the time `now` and the
redirect-taint are fields of the state: `start(url, jar, now)`, and the
jar is what `Done` or `Fail` ends with. When a request is sent its `Cookie`
field, appended last and only when not empty, is RFC 6265bis §5.8.3's
retrieval for the current URL with a fixed context (a top-level navigation
GET with no client: same-site, unless a redirect crossed sites, which
Fetch's redirect-taint makes cross-site so `SameSite=Strict` cookies are
withheld), and the jar becomes the jar after the retrieval's step 5. Every
`Set-Cookie` line of a final response is stored one by one by §5.7 as HTTP
before the redirect is decided; a 1xx response never reaches storage, and a
failure after a final response keeps what it stored. `Secure` follows the
connection, which is never TLS yet, so no `Secure` cookie is sent. Proven
for every HTTP and URL function: `theorem_wire_cookies` (every `Send` is
the request for the current URL whose only jar-derived part is its
`Cookie` field, and that is §5.8.3's retrieval) and `theorem_jar_frame`
(the jar changes only by the retrieval's step 5 when a request is sent, or
by §5.7 storage of the final response's own `Set-Cookie` lines). The
cookie view of a URL is a parameter (`UrlFns::request_url`), joined to
`clazel-url` and `clazel-cookie` in `real.rs`. Cookie mutations: 18, each
with a certificate (field omitted, duplicated, first, or present when
empty; `Secure` ignored; the taint ignored, never set or always set; an
unsafe method; not top-level; a reload; storage skipped, after the
redirect decision, or lost on a failed redirect; only the first
`Set-Cookie`; interim cookies stored; step 5 dropped; the wrong time).
Storage mutations are certified through an expired cookie's eviction,
because `create_a_cookie`'s quantifiers do not evaluate under
`compute_only`. `clazel-net` has `fetch_jar` and `now_1601`; `fetch`
and `clazel fetch URL` start from an empty jar.

**Independent transcription** (`transducer/independent.rs`): Fetch's
HTTP-redirect fetch (steps 3 to 8, 18 and 22), "location URL", and the
`Cookie` and `Set-Cookie` steps of HTTP-network-or-cache and HTTP-network
fetch, with the request as its URL list (the redirect count and the taint
computed from it), for a navigation GET with no body, cache or CORS and
credentials "include". `theorem_independent_request` and
`theorem_independent_redirect` prove the transducer's cookie-string,
request bytes, jar and decision on a final response equal the
independent ones for corresponding states: a one-step equivalence, not a
theorem over whole runs. The Fetch text was read from the commit snapshot
on the web; the repository holds no copy. Open question: Fetch §3.1.3
"determine the same-site mode" step 3, as read, would withhold `Strict`
cookies from a same-site navigation; the transducer follows RFC 6265bis
§5.2, and no erratum is filed until the reading is checked.

**Conformance** (`tests/conformance_http_state.rs`): the 222 rows of the
http-state parser corpus run through `start`, `step_real` and the real
parsers, in memory: 195 pass, 27 expected failures with reasons, none
fail. WPT fetch/redirect rows and a differential against another engine
are not written.

Not built: TLS, a request context other than a top-level navigation (a
client, a cross-site initiator), a theorem over whole runs for the
independent transcription, and the conformance suites beyond http-state.

### 3.7 Kernel integration (M)

`clazel-kernel`: a `Navigate` (and the user's `NavigateTab`) now produces an
output `Fetch { tab, url }` instead of an immediate commit; a new event
`Fetched { tab, outcome }` carries 3.6's result and commits the body (as
the `Commit` message's script field for now; Phase 4 gives it a document)
or an error. The jar updates happen in 3.6's transducer, which the kernel
runs as part of the fetch: so the kernel owns the jar, and the shell never
sees it. Restate the Phase 2 theorems with the new event and output: a
`Fetched` event is attributed to its tab's lock, like a frame to its
socket; a redirect is a navigation the user is treated as having made (the
same declassification 2.11 states). Each theorem keeps its certified
mutation. The IPC schema is unchanged. The kernel's WPT `cookies/` run adds
the rows that needed `Set-Cookie` from HTTP.

**As built** (branch `claude/phase3-kernel-join-a-d56e97`, from `phase3/fetch-kernel-join`): `clazel-kernel`, tier 2 as before, **joined to 3.6's transducer**: the kernel steps it itself. A navigation (`NavigateTab { tab, url }`, a renderer's `Navigate`) calls `begin_navigation`: the tab's connections are closed, `FetchFns::parse` reads the URL, 3.6's `start` gives the first actions, and `carry_out` does them. The tab's renderer holds the navigation in `Renderer::pending = Some(Navigation { url, fetch, partition })`: the transducer's state, and the partition key (the domain of the renderer that started it). **Connections are first-class kernel state**: `State::conns: Seq<Connection { id, tab, endpoint, partition }>` and `next_conn` (ids from their own counter, never reused). New outputs `Connect { conn, host, port, tls }`, `Send { conn, bytes }` and `Close { conn }`; new event `Net { conn, input }` (the transducer's `Connected`, `Bytes`, `Closed`, `Error`); `Fetch` and `Fetched` are gone. `net` finds the connection, its tab's renderer and that renderer's navigation (a connection that is not open, or whose tab has gone or is not navigating, is ignored in full), steps the transducer with the kernel's jar and clock, applies its jar operations to the kernel's jar (`apply_net_ops`: `Retrieved` is §5.8.3 step 5 and the eviction of expired cookies, `Stored` is §5.7 storage behind `store_allowed`, so a response's cookie is never stored for a public-suffix or empty host) and carries out its actions: `Connect` opens a connection (**the one decision about reusing one is `choose_connection`, always `None` today**: each request has its own connection and `Connection: close`; keep-alive, HTTP/2 and coalescing change that function and nothing else in the state machine, and a connection it returns must be of the navigation's partition), `Send` and `Close` go to the connection the actions are for, `Done` commits the final URL's serialization with the body as the script (`commit_navigation`; a URL that is not scalar or has no lock is `Error` 3), `Fail` is `Error` 5 and the renderer stays (`abort_navigation`). `Done` and `Fail` close every connection the tab still has, a renderer that exits or is killed takes its connections with it, and a `Closed` or `Error` input removes its connection first (so the `Close` the transducer may still ask for is harmless). **The shell only pipes bytes**; the kernel decides every request, redirect and stop. **Parameters:** `FetchFns { http, urls, parse }` replaces `run`: 3.6's `HttpFns` and `UrlFns` and the parser of a navigation URL; the contract requires the transducer's Public Suffix List to be the kernel's (`fetch.urls.rules == psl()`), so the `Cookie` field is read with the cookie roots the jar operations are applied with, and that `next_conn + 21` fits a `u64` (a step uses at most 21 connection ids). **Invariants:** `kernel_wf` gains `navigations_wf` (a navigation's partition is its renderer's domain and its transducer state meets 3.6's `step_requires`) and `conns_wf` (ids below the counter and unique; each connection belongs to a navigating tab, with that navigation's partition). **Theorems, all proven for every `FetchFns`, `UrlFns` and `rules`:** `lemma_step_preserves_wf` over `Net` and the connection operations; `theorem_net_only_to_tab` (a `Net` event is attributed to its connection's tab: its outputs go to that tab's renderer, the one spawned for it, or to connections the tab owns, never to another); `theorem_net_answers_connection` (a `Net` event for a connection that is not open of a navigating tab is ignored; one that ends the fetch leaves the renderer not navigating and its tab with no connection); `theorem_connection_ownership` (every `Connect`, `Send` and `Close` output names a connection the tab of the event owns or opens, so one tab's navigation never writes to, closes or reads another's); `theorem_wire_cookies` (every octet derived from the jar that a `Send` carries is the cookie string RFC 6265bis §5.8 retrieves for that request from the kernel's jar: 3.6's theorem, carried through the kernel's jar) and `theorem_net_jar_frame` (a `Net` event changes the jar only by its jar operations); `theorem_reply_only_to_sender`, `theorem_cookie_integrity` (a `Net` arm) and `theorem_lock_set_only_by_navigation` restated; `corollary_real_wire_cookies`. **Noninterference:** `theorem_cookie_noninterference` keeps its statement over every `fetch`, with the network outside every renderer domain: `rel` gains `rel_conn` (the same `next_conn`; every connection of the first run is in the second; every connection of the second whose tab is open in the first is in the first), `user_tabs_open` also requires a `Net` event to name an open connection, the unwinding lemmas conclude that the renderer-bound outputs agree (`renderer_outs`: the network-bound ones may differ in the order of `Close`s and in the octets of a `Send`, which no renderer sees), and `example_dead_tab_breaks_noninterference` is a trace over `Net` in which a closed tab's connection answers and commits into the observer's domain in the purged run only. **Exec:** `exec::fetch::FetchFnsExec` (associated `H: HttpFnsExec` and `U: UrlFnsExec` of 3.6, `http_fns`, `url_fns`, `parse`, and `nav_ok`, the parser invariant of a navigation's state stated without an instance); `exec::real_urls::RealFetch` (3.6's `RealHttp` and `RealUrls`, and the basic URL parser) is proven to implement `urls::real_fetch()`; `begin_navigation_exec`, `net_exec` (steps `clazel_fetch::transducer::step::step` on the navigation's `StateBuf` and the kernel's jar), `carry_out_exec` (recursive over the actions), `commit_navigation_exec`, `abort_navigation_exec`, `close_tab_conns_exec`, `apply_net_ops_exec`, `step_exec` generic over the fetch, each proven equal to its spec; `step_real` runs with `RealFetch`. **Host shell (`crates/clazel`, 299 lines) and `clazel-net`:** the host only routes between the kernel and `clazel_net::Driver` (Tier 0, with `read_frames`): `Connect` starts a thread that resolves, connects, reports `Connected` and reads; `Send` writes on the driver's end; `Close` shuts the socket; bytes, closes and failures come back as `Net` events (a `Connect` with `tls` fails: TLS is not carried out). `navigate_tab(tab, url)` lost its stand-in script; the page is what the network serves, and `Host::route` (a test hook) sends every connection to one address. Verus: `clazel-kernel` 503 verified, 0 errors. **Mutations:** 40 in `mutations.json`, all certified kills: 22 that remain (the Phase 2 decisions, the public-suffix and empty-host refusals, `store_one`; 14 that were about the stand-in fetch and `Fetched` are gone) and 18 new, for the join's decisions: a `Net` event for an unknown connection changing state, a `Net` event attributed to another tab, the new connection's tab, partition, endpoint, id, counter and TLS flag, the `Retrieved` jar operation left out, the `Stored` operation skipping `store_allowed`, the body dropped from the commit, a failed fetch that does not end the navigation, connections kept by `close_tab_conns`, by a new navigation and by a commit, a `Send` on the wrong connection or with other octets, a `Close` that leaves the connection in the table. **Tests:** `tests/fetch.rs` (11, against a test network: a navigation opens a connection, sends the request and commits the body; an unknown, stale or closed connection is ignored; a second navigation closes the first's connection; a tab that exits or is killed takes its connections; failure and close; a URL the transducer does not fetch; a cross-origin redirect; a cookie from a response stored for the right root and not for a public suffix; the jar's cookie on the wire; each connection committing to its own tab); the other kernel tests settle each `Connect` and `Send` with an empty response; `crates/clazel/tests/host.rs` runs a cross-origin navigation over a loopback socket. **Not built:** a `https:` URL is not fetched (3.6 is `http://` only, so a navigation to one fails at once with `Error` 5 and the renderer stays; the kernel tests that navigated to `https:` pages with the stand-in now navigate to `http:` ones, and the differential test expects `Error` 5 for an `https:` target); the WPT `cookies/` rows that needed `Set-Cookie` from HTTP are not run through the kernel (the shell can now carry them; `clazel-net/tests` run them against a server).

### 3.8 The network shell and the `curl` clone (M)

`crates/clazel-net` (Tier 0, counted): the resolver (nameservers read from
`/etc/resolv.conf` on Linux and macOS and from `GetAdaptersAddresses` on
Windows, which has no such file; a query over UDP with a random ID,
one retry, TCP on TC=1; `127.0.0.1` and `::1` and IP-literal hosts need no
query), TCP connect with a timeout, the TLS loop (3.5), and the loop that
drives 3.6's transducer: read bytes, call `step`, carry out actions. The
shell contains no parsing of its own; `resolv.conf` is read by a proven
function in `clazel-dns` (RFC 1035 has no format for it; the `nameserver`
line grammar is ours, listed as a modelling choice). `clazel fetch URL`
prints the status line, the fields and the body. Tests, all without the
Internet: an in-process server (`std::net::TcpListener`) that serves the
`http-state` parser corpus the way its upstream server does (`Set-Cookie`
lines, then a redirect to `/cookie-parser-result`, which the row's
expected `Cookie` header checks), and the WPT `cookies/` rows that needed a
server; a hostile server (bytes that are not HTTP, a body that never ends,
a redirect loop, a chunk size of 2^64) that must give `Fail` and never a
panic or unbounded memory. The demo (`fetch https://example.com/`) needs the
Internet and is run locally, like the Phase 2 demo.

**As built, the TLS loop (2026-11-02, on `main`, #85).** `clazel_net::TlsConnection` (`src/tls.rs`): `open(addrs,
port, timeouts, host, now, verifier, random)` connects, runs the handshake
through 3.5f's driver with the existing timeouts, and `send`, `read` and
`close` mirror `Connection`. The shell writes what the driver sends, feeds it
what arrives and the end of the stream, and keeps delivered plaintext until it
is read; it makes no protocol decision. A TLS end is `NetError::Tls(Failure)`
(the §6.2 alert and its origin, displayed by name); a timeout before the
handshake completes is `Timeout(Stage::Handshake)`. `tests/tls.rs`, 8 cases
against an in-process rustls server on a loopback socket (test root as the
trust store, a fixed test seed as randomness): ECDSA and RSA handshakes with a
request, a response and close_notify both ways; a 100000-octet response; a
server that closes during the handshake (truncation, alert 80, nothing sent);
one that stalls (handshake timeout); a certificate for another name (alert 42,
sent and read by rustls); a response record that fails to decrypt after the
handshake (bad_record_mac, 20, sealed by `Connection` under the application
key and read by rustls, #86); bytes that
are not TLS (a plaintext alert on the wire). **Randomness (on `phase3/tls-os-random`, local run, CI not yet):**
`open` now takes the driver's random octets from `clazel_sys::fill_random`
(audited at aa66b138) and fails with `NetError::Random` before opening a
socket if the OS source fails; `open_with_random` keeps the seeded path for
tests. The resolver's query ID comes from the same call, replacing
`/dev/urandom` on Unix and `std`'s hasher key on Windows. Three more tests
use the OS source (ECDSA and RSA handshakes, two ClientHellos that differ),
and a unit test shows a failing source opens no socket. **Not yet:** `tls: true` in 3.6's
transducer, `https:` in the kernel (3.7), `clazel fetch https://` and the
demo; nothing calls `TlsConnection` outside its tests.

**As built, the Windows resolver (2026-11-03, on `main`, #96, CI's full verification green on bf6a9ea).** Windows has no `/etc/resolv.conf`, so every host
name failed there with `ResolvConf(NotFound)`. `clazel_sys::windows::adapter_addresses`
calls `GetAdaptersAddresses` (one new foreign call, audited in
`docs/SYS-AUDITS.md`) and hands over a copy of the buffer's octets and the
address it was at, following no pointer. `clazel-dns`'s new `adapters` module
reads them: `spec.rs` is the 64-bit layout of `IP_ADAPTER_ADDRESSES_LH`,
`IP_ADAPTER_DNS_SERVER_ADDRESS_XP` and `SOCKADDR_IN`/`SOCKADDR_IN6` from the
Windows SDK 10.0.26100.0 headers (checked against a real buffer), each
pointer turned into an offset and used only if what it points at lies in the
buffer, lists followed only forward (so any octets terminate), only adapters
that are up, and no scoped IPv6 servers (`fe80::/10`, and `fec0::/10`, which
Windows lists on every adapter with no IPv6 server). `parse::dns_servers` is
proven equal to it; 11 examples evaluated by Verus; 9 mutations, all killed
with certificates; a seventh conformance suite (`GetAdaptersAddresses
buffers`, 10 cases including 2000 damaged buffers). The resolver uses it on
Windows in place of `resolv.conf`; `clazel fetch http://example.com/` gets
200 on Windows 11 with the OS's servers. **Not covered:** `independent.rs`
has no second transcription of the buffer layout; 32-bit Windows (the layout
is the 64-bit one, and `clazel-net` refuses to build otherwise).

### 3.10 Persistent storage: one store for everything that outlives a run (L, split into 3.10a and 3.10b)

Added 2026-11-03, for 3.5h, because a revocation set is useless if it is
downloaded again on every run. Reshaped the same day (maintainer): 3.10 is
**generic storage**, not one snapshot file per kind of state. Later phases
will need `localStorage` persisted, IndexedDB, the Cache API, an HTTP cache
(RFC 9111) and service-worker registrations, and each of them goes into
this store rather than inventing its own.

Today nothing outlives a run:
- the kernel's cookie jar starts empty;
- the kernel's `localStorage` is in memory only (Phase 2: an ordered list
  per origin with a proven 5 MiB quota, `crates/clazel-kernel/src/exec/storage.rs`);
- `clazel fetch` keeps its jar for one fetch;
- `clazel browse` keeps its back list (`crates/clazel/cli/browse.rs`) in
  memory.

**The model: the WHATWG Storage Standard** ([storage.spec.whatwg.org](https://storage.spec.whatwg.org/),
last updated 2026-10-19).
- **The web-visible part follows §4:**
  - a *storage shed* (§4.3) maps *storage keys* (§4.2) to *storage
    shelves* (§4.4);
  - a shelf holds *storage buckets* (§4.5), each with a mode,
    "best-effort" or "persistent";
  - a bucket holds one *storage bottle* (§4.6) per *storage endpoint*
    (§4.1).

  The registered endpoints are `caches`, `indexedDB`, `localStorage`,
  `serviceWorkerRegistrations` (type local) and `sessionStorage` (type
  session). Usage and quota follow §6. A session-type shed is never
  written to disk.
- **Browser state no page may reach goes in browser buckets:** the cookie
  jar, the history and the revocation set. These buckets sit outside
  every storage key, so no renderer can name them. That is a modelling
  choice to list in the spec, since the standard covers only what the web
  can reach.
- **Consumers name a bottle, never a file.** The store maps (shed, storage
  key or browser bucket, bucket, endpoint) to a bottle, and a bottle holds
  ordered keys and values. Adding an endpoint later adds a bottle kind; it
  needs no change to the format.

#### 3.10a The store (L)

- **3.10a.0 Design note (S), before any code.** Record the choice and its
  costs, as 3.0 and 3.5h.0 did:
  - the layout: a log of records with commit points and compaction, or
    B-tree pages;
  - the record encoding: DER through `clazel-der`, whose encoders and
    decoders and their round trip and canonicity are already proven, or a
    format of ours;
  - how large values are kept (a revocation set is about 6 MB, a cached
    response can be larger);
  - what one file holds (the whole store, or one file per shelf).
- **The substrate (ours, rule 8; target tier 2): an ordered key–value
  store with transactions.**
  - Keys and values are octet strings. Keys are ordered by octets, so
    IndexedDB's key ordering can later be encoded to preserve that order.
  - A transaction is a list of puts and deletes over one or more bottles,
    and it is applied whole or not at all.
  - Operations: get, range scan, put, delete, commit, and usage per bucket
    (§6).
  - The file is parsed as untrusted bytes, since another local program may
    have changed it.
- **What is proven:**
  - *Records.* An encoder and a decoder proven to the spec, with **round
    trip** (decoding what was encoded gives it back), **canonicity**
    (encoding what was decoded gives the same octets) and **refusal**
    (anything else is refused, never half-read).
  - *Recovery, the main theorem.* Opening any prefix of a file the store
    wrote gives exactly the state after the last transaction committed in
    that prefix: never a partial transaction, and never a state that no
    sequence of commits produced. A prefix models a write the OS cut off at
    any octet. A file the store did not write is refused, or read as the
    longest valid prefix (the design note picks one).
  - *Compaction.* It changes the octets, never the state.
  - *Quota.* Usage per bucket is computed exactly, and a transaction that
    would exceed the quota is refused whole. This extends Phase 2's
    `lemma_quota_push` and `lemma_quota_update`.
  - Examples, certified mutations, and an independent transcription, as
    for every tier 2 crate.
- **The shell (tier 0):**
  - where the files live (the platform's per-user application data
    directory);
  - permissions readable by the user only;
  - one process at a time (a lock file);
  - `fsync` at each commit point;
  - the rename that publishes a compacted file.

  A store that doesn't open starts empty, says so, and never crashes. The
  old file is kept beside it for the user, not deleted.
- **Not claimed:** protection against a local attacker who can write the
  user's files (they can replace the browser too), encryption at rest,
  durability beyond what `fsync` gives on the platform, and a private
  browsing mode.

**3.10a.0 Design note: accepted by the maintainer, 2026-11-03.** Each
choice below is followed by what it costs.

- **Layout: an append-only log per bucket, compacted by rewriting.**
  - *How it works.* Each commit appends one record that holds the whole
    transaction. Opening the store replays the records in order.
    Compaction writes the live state as a new log and renames it over the
    old one.
  - *Why a log.* Recovery is then a fold over a list of records, which is
    a short proof. A B-tree changes pages in place, so it needs a
    write-ahead log anyway, plus proofs of page splits and merges.
  - *The cost.* A store this size keeps its whole index in memory: about
    6 MB for the revocation set plus small amounts for the rest. That is
    no problem in Phase 3. An HTTP cache in gigabytes will need values
    read from disk by offset, and the record format allows that (each
    value is one octet string at a known position). The design leaves
    room for it but doesn't build it.
  - *Precedent, unchecked here.* Chromium keeps `localStorage` and
    IndexedDB in LevelDB, which is log-structured; Firefox uses SQLite.
    Neither is a dependency we may take (rule 8), and neither shapes the
    proof.
- **Granularity: one log file per bucket.**
  - The Storage Standard scopes every endpoint to a bucket (§4.5), and
    IndexedDB transactions never cross a bucket. So no transaction needs
    two files, and the recovery theorem is about a single file.
  - Clearing a site's data deletes its files, and a damaged file loses one
    bucket, not the whole store.
  - The file is named by the SHA-256 of its encoded bucket identity (the
    storage key, or the browser bucket's name, plus the bucket name). The
    identity is repeated in the header, and a file whose header doesn't
    match its name is refused.
  - *The cost.* One file per origin that stores anything, and one `fsync`
    per bucket that commits.
- **Records: DER through `clazel-der`.**
  - `clazel-der` is already tier 2, and its TLV round trip is proven in
    both directions (`lemma_read_tlv_encode_tlv`,
    `lemma_encode_tlv_read_tlv`), as is never reading past the input
    (`lemma_read_tlv_no_overread`). Lengths go up to 2^64.
  - Whatever the new crate encodes reuses those proofs. A format of our
    own would need all of them proven again.
  - The header is
    `SEQUENCE { magic OCTET STRING "clazel-store", version INTEGER 1, identity OCTET STRING }`.
  - Each record is
    `SEQUENCE { commit INTEGER, ops SEQUENCE OF Op, check OCTET STRING (4) }`,
    where `Op` is one of three context-tagged choices:
    - `put [0] { bottle, key, value }`;
    - `delete [1] { bottle, key }`;
    - `clear [2] { bottle }`.

    `commit` increases by exactly 1 from record to record, and the first
    record's `commit` is 1. (That last clause was added on 2026-11-04: the
    independent transcription found this note silent on the first number.)
  - *The cost.* DER spends a few octets of framing per field. A record's
    length must be known before it is written, which is fine for a
    transaction that is already built.
- **Torn writes: a CRC-32C per record, the Castagnoli polynomial
  `0x11edc6f41`** (RFC 7143 §13.1, which obsoletes RFC 3720, with test
  vectors in §A.4). Read §13.1 with §11's convention that bit 0 is the
  most significant bit: its "bit 7" is the least significant bit, so the
  CRC is the reflected one.
  - A crash can leave the tail of the file truncated, or on some file
    systems holding octets that were never written. The `check` field
    covers the record's other contents.
  - Recovery takes the longest run of records, from the header on, that
    decode, check correctly, and number their commits in sequence. It
    stops at the first record that fails any of these.
  - CRC-32C is specified exactly in the spec and proven against it. No
    cryptographic function is assumed.
  - *The cost, a modelling choice to list.* Damaged octets that happen to
    form a valid record with a matching CRC (about 1 in 2^32 for each
    damaged tail) are taken as a commit. That isn't a defence against an
    attacker, and none is claimed (see "Not claimed").
  - If recovery drops any octets, the shell keeps the original file beside
    the new one and says how much was dropped.
- **Large values: kept inline, one octet string per value, at most 64 MiB
  per record.**
  - The revocation set is one value of about 6 MB.
  - A value too large for one record is refused, not split. Splitting
    belongs to the later cache, with values read by offset.
- **The theorems this gives, in the spec's terms.** Let `state(file)` be
  the fold of the recovered records over the empty state.
  1. For every list of transactions `ts` and every prefix `p` of the file
     written from `ts`, `state(p)` is the state after the first `k`
     transactions of `ts`, for some `k`.
  2. When `p` is the whole file, `k` is the length of `ts`.
  3. Compacting gives a file with the same `state`.
  4. A transaction that would take a bucket over its quota is refused
     whole.
- **The crate:** `clazel-store`, target tier 2. Its spec and
  contracts come first, in a commit of their own (rule 3). It depends on
  `clazel-der` and `vstd` only, with SHA-256 for file names taken from the
  shell's existing crypto, not from the store's spec.

#### 3.10b The first consumers (M, after 3.10a)

- **The kernel decides what is written.**
  - A new kernel output asks the host to commit a transaction the kernel
    built, and loading is an event: the only way stored state enters the
    kernel.
  - The jar and `localStorage` theorems hold from loaded state as from an
    empty one. Restate each one that is affected.
  - The store is outside every renderer domain, like the network.
- **The cookie jar:** only cookies whose persistent-flag is set. RFC
  6265bis §5.7 gives a cookie without `Expires` or `Max-Age` a
  persistent-flag of false, and such a cookie ends with the session.
  Expired cookies are dropped before writing. A loaded jar must meet
  `clazel-cookie`'s `jar_in_range` and its uniqueness rules, or it is
  refused.
- **`localStorage`:** the `localStorage` bottle of each storage key's
  default bucket, holding Phase 2's per-origin lists. A loaded list must
  meet the invariants Phase 2 proved (unique keys, within the 5 MiB
  quota). `sessionStorage` is never stored.
- **The history:** the URLs the user visited, with their times. What is
  kept, and whether it is per tab or global, is decided here.
- **The revocation set:** 3.5h's set with its fetch time and signature, in
  a browser bucket. A stored set must be one 3.5h's parser accepts, so
  this consumer comes last and waits for 3.5h.0's choice.
- **Not stored in Phase 3:** IndexedDB, the Cache API, an HTTP cache
  (RFC 9111 is outside the phase), service-worker registrations,
  connections and renderer state. The design note must show where each of
  these would go, without building them. WebSQL is out of scope for
  good: the web platform removed it, and IndexedDB replaces it.
- **Tests:**
  - round trips of real jars, `localStorage` lists and sets;
  - truncated, oversized and hostile files refused or recovered as the
    recovery theorem says;
  - a kernel restarted from a stored jar sends the same `Cookie` fields as
    before the restart, and a page reads back its `localStorage`;
  - a process killed at every write leaves a store that opens to a
    committed state (run locally, like the demo).

### 3.9 Status and README (S)

`cargo xtask report --write`, the network shell's line count next to the
host shell's, the Phase 3 note in README.md, this file's Status table and
ROADMAP.md.

## Order of work

```
3.0 TLS decision (done: B)
3.5a DER ─> 3.5b X.509 ──────────────┐
3.5c PKCS#1 v1.5 ────────────────────┼─> 3.5f crypto join ─> 3.5g TLS conformance ─┐
3.5d TLS formats ─> 3.5e handshake ──┘                                               │
3.1 field syntax ─> 3.2 framing ─> 3.3 conformance ──┐                               │
3.4 DNS ──────────────────────────────────────────────┼─> 3.8 shell + curl clone ─> 3.9
                                                     └─> 3.6 client ─> 3.7 kernel ─┘ │
3.5g, 3.6, 3.7 ─> 3.10a store ─> 3.10b consumers ─> 3.5h revocation ─────────────────┘
```

3.1, 3.4, 3.5a, 3.5c and 3.5d start at once; 3.6 can start against
abstract parameters as soon as 3.1's field types exist; 3.8's `http://`
half does not wait on TLS. 3.10 and 3.5h (added 2026-11-03) come after the
`https:` path works: 3.5h's updates are fetched over it and stored by 3.10.
3.10a needs nothing from TLS and can start at once. In 3.10b only the
revocation set waits for 3.5h.0's choice.

## Status

| Item | State |
|------|-------|
| 3.0 TLS decision | done (2026-10-23): option B, our own TLS 1.3 client over libcrux, grounds and accepted costs recorded above |
| 3.1 HTTP field syntax | built: 146 verified, independent transcription (Fetch), 76 certified mutations, 10 unit tests; tier 2 with 3.2 and 3.3 (2026-10-25) |
| 3.2 HTTP/1.1 message framing | response side and request serializer built, tier 2 (2026-10-25, CI's full verification green on 9ce4086): spec, contracts, examples evaluated by Verus, implementation proven equal to the spec; independent transcription of RFC 7230 §3 and §4.1 (`message/independent.rs`) proven equal to the spec wherever they decide, with the inputs where the RFCs differ listed and excluded (`Out`); 150 mutations, all `killed` with certificates (the five limit survivors closed with parameterised limits `read_line_with` and `close_body_pending` and examples at limit 4). `theorem_monotone` and `theorem_no_early_decision` proven (`message/lemmas.rs`); an incremental `ResponseParser` (`message/incremental.rs`) proven to `feed_ensures`; a request parser spec and `theorem_request_round_trip`, with an executable request parser proven to it (a test aid: no leading empty lines, no request body). `ResponseParser::received_bytes` (proven to `received_bytes_ensures`) lets the fetch transducer keep no second copy of the octets. `clazel-http` 379 verified, 0 errors (2026-10-25). Not yet: an incremental `close` (it re-parses once); the independent transcription covers `parse_response_at_close` and `Transfer-Encoding` with `Content-Length` (2026-10-26, not yet CI-verified) but not obs-fold, codings other than a lone `chunked`, repeated `Content-Length`, chunk-extension whitespace, or a status line with no second SP or a major version other than 1 (each `Out`, with the reason in its header); the Fetch "HTTP-network fetch" transcription the plan names is not written |
| 3.3 HTTP conformance | built (`crates/clazel-http/tests/conformance_http.rs`, 7 suites, 0 unexpected failures): httparse differential on 6000 random, 60000 mutated (53915 pass, 6085 expected differences), 136 llhttp-corpus and 44 handcrafted heads (124 + 12 and 29 + 15 expected); the llhttp `test/response` and framing cases, 136 (109 pass, 27 expected failures, each listed with its reason); RFC 9112 §7.1 and §11 cases, 122; 3000 framing-by-construction messages. The llhttp fixtures are vendored under `tests/data/llhttp/` and converted by `cargo xtask testdata` (136 cases). `clazel-http` raised to tier 2 on 2026-10-25 |
| 3.4 DNS message format | done (2026-10-24): tier 2 (see As built) |
| 3.5a DER | on `main`; tier 2 (see As built) |
| 3.5b X.509 and path validation | on `main`; tier 0, target 2 (see As built): decoders, RFC 9525 matching, root table, RFC 5280 §6.1 with the browser profile and the bounded chain search; x509-limbo 9,736 of 9,802 testcases agree with `verify_server_chain` (accept-all signature links), 66 listed expected failures (10 client, 10 CRL, 4 need signatures, 3 ML-DSA, 38 profile or certificate-profile rules, 1 of them a private-suffix wildcard); signatures checked by `clazel-crypto`'s links (P-384 issuer keys too, on `main`, #91, CI's full verification green on bf6a9ea, design P17: `clazel-p384` in the links, the 35 P-384 Mozilla roots' self-signatures verify, all 14 limbo online chains validate), no revocation; independent transcriptions on `main` (2026-11-03): X.509 (10/2019) §12 path processing (`path/independent.rs`, #72) and the browser profile (`path/independent_profile.rs`, #73), each with an equivalence proof to the spec on its stated domain (`path/independent_equivalence.rs`, #81, whose excluded inputs are listed in its header; `path/independent_profile_equivalence.rs`, #73, CI's full verification green on e86ebc5); #72 and #81 reached `main` together in f48d601 (CI's full verification green on bf6a9ea). Differential not done |
| 3.5c RSA PKCS#1 v1.5 | on `main`; tier 2 (see As built) |
| 3.5d TLS record and handshake formats | built and proven to the level stated in its **As built** paragraph (2026-10-24), `clazel-tls` at tier 0: tier 2 waits for 3.5e and 3.5f and for CI's full run |
| 3.5e Key schedule and handshake state machine | Non-PSK key schedule, owned ClientHello/retry exchange, server selection, initial authentication and bounded initial connection dispatcher built over provider parameters, and a post-handshake transducer: spec, contracts, executable, lemmas, 20 witnesses, 20 mutations and 25 passing integration tests (on `main`, #77, CI's full verification green on 797e26b). The dispatcher seals its own fatal alert (§6, §6.2) under the settled write epoch's next sequence number (§5.3) before dropping its keys, in the server's flight and after the handshake, and never answers a peer's alert (`PeerAlert`): spec, contracts, exec, lemmas, 8 new mutations with certificates and 20 dispatcher integration tests (on `main`, #86, 2026-11-03, CI's full verification green on bf6a9ea). Production providers and socket I/O are 3.5f and 3.8; the join of the transducer to the dispatcher remains; tier 0 |
| 3.5f Cryptography and the join | Hello-to-authentication and handshake record-key handoffs built over explicit providers; `clazel-crypto` (tier 0) has the libcrux providers (SHA-256, HMAC, HKDF, ChaCha20-Poly1305, X25519), CertificateVerify, the chain-link signatures and the production `Verifier` over `clazel-x509`'s path validation, and 3.5g's test runs them end to end against rustls. Randomness: `clazel_sys::fill_random` exists (Linux `getrandom` with flags 0, macOS `getentropy`, Windows `BCryptGenRandom` with the system-preferred RNG) and is audited (`docs/SYS-AUDITS.md`, source aa66b138); `clazel_net::TlsConnection::open` draws the scalar, ClientHello random and session id from it (on `main`, #88, CI's full verification green on bf6a9ea), and the driver itself still takes them from its caller. The client driver `clazel_crypto::client::Client` (on `main`, #85, CI's full verification green on 0a6fbec): connect/receive/send/close over `Bootstrap`, the key exchange and `Connection`; alerts in plaintext before the handshake keys, and from the ServerHello on the record `Connection` seals itself (#86, 2026-11-03: the driver's copy of the handshake epochs is removed, and a failure after the client Finished now sends its alert), 15 passing tests (8 against rustls, among them bad_record_mac after the handshake read by rustls); the join moved into `clazel-tls` as `Driver` (2026-11-05, stacked on #109, not yet on `main`): Hello and application stages proven to be those machines' own steps, the flight step's contract relational rather than exact, close_notify now sent during the flight; `Client`'s input loop and `send` chunking stay tier 0 glue |
| 3.5g TLS conformance and trust store | first part built (2026-10-31, on `main`, #82, CI's full verification green on bcc4040): `clazel-crypto/tests/conformance_tls.rs`, 17 cases in two suites (5 success and control, 12 hostile): full handshakes with ECDSA and RSA chains against rustls (TLS 1.3, ChaCha20-Poly1305, X25519, the test root as the trust store), application data both ways, KeyUpdate, close_notify, and 12 hostile-server tests (wrong Finished, wrong CertificateVerify, another name, expired leaf and intermediate, self-signed, missing intermediate, empty trust store, oversized records, TLS 1.2 ServerHello without and with the §4.1.3 downgrade sentinel, misplaced CCS) each ending in `Fail` with the §6.2 alert (the 3.5g paragraph lists them and the behaviour it pins); the downgrade sentinel is checked (`illegal_parameter`, 2026-11-02, on `main`, #83, CI's full verification green on 2755dde). `conformance_tls.rs` runs through 3.5f's driver (2026-11-05, stacked on #114). Top-site measurement run locally (2026-11-05, see 3.5g): 577 of the 765 domains with a TLS server completed a handshake. Real-certificate corpus vendored and measured (2026-11-05, see 3.5g): 868 certificates all decode, none with an explicit `critical` FALSE; all 760 chains get the same verdict from `rustls-webpki`. Not done: the Mozilla root table check, HelloRetryRequest and ticket paths against a real server, the tier 2 raises |
| 3.5h Revocation (pushed set) | planned (2026-11-03): option 1 decided by the maintainer; 3.5h.0 facts checked and written up (2026-11-03); CRLite on its `default` channel, failing open and in a new `clazel-crlite`, decided by the maintainer (2026-11-05); nothing built. Production still passes `NothingRevoked`, so a revoked certificate is accepted |
| 3.6 Client state machine | on `main` (#3, #5): transducer, redirects and cookies proven to their contracts; at most 21 requests, redirect bound, URL changes only by redirect, every `Send` the current request, silence until decided, split invariance for the shipped parser, `theorem_wire_cookies` and `theorem_jar_frame` proven; linear in the response's size; independent transcription of Fetch's redirect and cookie steps proven equal step by step and over whole runs (`theorem_independent_run`); conformance: http-state corpus through the client, 195 pass, 27 expected failures, and a differential of 1500 random redirect chains against rust-url and `cookie_store`; 64 mutations, every one a certified kill; tier 2 (see As built). `https:` (on `main`, #90, CI's full verification green on bf6a9ea): `https:` URLs get the same request as `http:`, port 443 by default and `Connect.tls` exactly for `https` (RFC 9110 §4.2.2), with `theorem_tls_when_secure` (every `Connect` is the current request's and speaks TLS exactly when the cookie functions see it as secure), 6 new examples and 4 new mutations with certificates; the independent transcription does not cover the connection (port, TLS). Not yet: other request contexts, HSTS, WPT fetch suites (none vendored) |
| 3.7 Kernel integration | on `main` (#6), joined to 3.6 (see As built): the kernel steps 3.6's transducer itself; connections are kernel state (owner tab, endpoint, partition key); `Connect`, `Send`, `Close` outputs and `Net` events; the shell only pipes bytes; `theorem_wire_cookies` carried through the kernel jar, ownership, ending-a-fetch and `Net` attribution theorems, the Phase 2 theorems restated and proven over every fetch, noninterference with the network outside every domain; 40 certified mutations, `clazel-kernel` 503 verified. `https:` through the kernel's `Driver` (#93, see 3.8). Open: the WPT `cookies/` rows that need `Set-Cookie` from HTTP through the kernel (they run through `clazel-net` over sockets, see 3.8, but not through the kernel) |
| 3.8 Network shell and `curl` clone | built: `clazel-net` (resolver, TCP, `fetch` driving 3.6's transducer, so redirects are followed) and `clazel fetch URL`, tested against local servers and checked by hand against http://example.com/. Hostile-server tests built (`clazel-net/tests/hostile.rs`, 11 passing, about 1.5 s, 142 MB peak, nearly all of it the endless chunked body, whose parser keeps both the 64 MiB of octets received and the body decoded from them): bytes that are not HTTP, an endless body (no framing, a Content-Length over the limit, and chunked), chunk sizes of 2^64 and 2^64-1, a field line over 8192 octets, 300 field lines, an immediate close, partial heads, silence and a stalled head (timeout), a short Content-Length. The endless chunked body did not return within 20 s while `ResponseParser` re-parsed its buffer on every feed; the incremental parser (3.2) fixed it. It regressed when `fetch` moved onto 3.6's transducer, which re-parsed everything received on every `Bytes` input; the transducer now feeds the incremental parser (see 3.6's As built), and the test takes under a second. Server tests over real sockets built: the `http-state` parser corpus (`clazel-net/tests/http_state.rs`, 222 rows: 195 pass, 27 expected failures, each with its reason) and the WPT `cookies/` `httpCookieTest` tables (`clazel-net/tests/wpt_cookies.rs`, 167 cases: 157 pass, 10 expected failures), both through `fetch_jar` against an in-process server (2026-10-29). The network shell's line count (`crates/clazel-net/src`, 1805 lines) is in the README table's footnotes, written by `cargo xtask report` (3.9). `resolv.conf` is read by `clazel-dns`'s proven nameserver-line function; on Windows the DNS servers come from `GetAdaptersAddresses`, read by `clazel-dns`'s proven `adapters` reader (on `main`, #96, CI's full verification green on bf6a9ea, its `clazel-sys` call audited in `docs/SYS-AUDITS.md`). TLS loop built (on `main`, #85, CI's full verification green on 0a6fbec): `TlsConnection` over 3.5f's driver, `NetError::Tls` with the §6.2 alert, `Timeout(Stage::Handshake)`, `tests/tls.rs` against rustls on loopback (ECDSA, RSA, a 100000-octet response, close during the handshake, a stall, another name, an undecryptable response answered with bad_record_mac (#86), bytes that are not TLS). Randomness from the OS (#88): `open` draws from `clazel_sys::fill_random` and fails with `NetError::Random` before opening a socket, `open_with_random` keeps a seeded source for tests, the resolver's query ID comes from the same call, and `tests/tls.rs` has 11 tests (3 with the OS source; CI's full verification green on bf6a9ea). `https:` in `fetch` and `clazel fetch` (on `main`, #90, CI's full verification green on bf6a9ea): `Connect { tls: true }` opens a `TlsConnection` with Mozilla's roots, and any TLS failure (a truncation included) fails the fetch; `tests/tls.rs` adds four `fetch` tests over TLS (a request and response, another name, a truncated close-delimited body, a `Secure` cookie stored and sent). Checked by hand (2026-11-03): https://www.rust-lang.org/ gives 200; example.com, www.google.com, en.wikipedia.org, github.com, www.cloudflare.com, letsencrypt.org, http.cat and https://1.1.1.1/ fail with unknown_ca, each chain having a P-384 issuer key, which `clazel-crypto` refuses until P17 at that time. With P17 merged, the same hosts gave 200 from `fetch_with` in a run by hand (2026-11-03, the system resolver; no test asserts this). `https:` in the kernel's network driver (on `main`, #93, CI's full verification green on bf6a9ea): `Driver` carries out `Connect { tls: true }` with a thread that owns the `TlsConnection` (Mozilla's roots, or `Driver::with_verifier`'s) and takes the request over a channel; a `Close` sends close_notify (sealed by the thread right after the request, written by the driver; on Windows shutting down only the read side does not wake a blocked read) and then shuts the socket down; `tests/tls.rs` adds three driver tests against rustls (a request and response until close_notify, another name refused with bad_certificate, a `Close` while reading that the server reads as a clean close_notify), and `crates/clazel/tests/host.rs` an `https:` navigation through the host and the kernel against rustls (Unix only, like the rest of that file). The CNAME target is converted by `clazel-dns`'s proven `wire_to_dotted` (done 2026-10-25, see 3.4); the shell no longer has a conversion of its own |
| 3.9 Status and README | non-TLS part done (2026-10-29): README.md's Phase 3 note, `cargo xtask report` writes the network shell's line count next to the host shell's (CI's `table` job puts it in the README), this table and ROADMAP.md. Left for when TLS lands: the `https://` demo in the README, the 3.5 rows and marking the phase done |
| 3.10 Persistent storage | planned (2026-11-03), reshaped the same day into generic storage on the WHATWG Storage model. **3.10a store: built** (`clazel-store`, tier 2 claimed on PR #98, pending CI's full verification): the log format, CRC-32C, recovery, compaction, usage and quota, a sorted in-memory bucket with `get` and range scans, the note's four theorems, an independent transcription, conformance against published CRC vectors, `crc` and `der`, and 67 certified mutations; the tier 0 file shell is `clazel-store-shell`. A commit copies its bucket, and the shell has not been tested with a process really killed. **3.10b consumers: not started**, so the cookie jar, `localStorage`, history and revocation set still do not outlive a run |

## Risks

- **TLS dominates.** Option B makes the phase several times its size, and
  3.5b and 3.5e are each as large as the URL parser. Accepted in 3.0; the
  `http://` path and Phase 4 do not wait on it.
- **One suite, no AES.** A server that offers only AES-GCM refuses this
  client. 3.5g measures how many; if it is material, the answer is a
  verified AES-GCM (libcrux's, once its badge changes), never an unverified
  one.
- **Our own RSA verification.** Public inputs only, so timing is not a
  concern, but a bignum bug is a signature-forgery bug. It is Tier 2 with
  Wycheproof and FIPS vectors; the proof is the defence.
- **libcrux is pre-release.** APIs at 0.0.x move; every bump is a deliberate
  re-pin with its rows updated.
- **Incremental parsing proofs.** The prefix lemma (no decision before the
  data) is new; the UTF-8 decoder's "restore to the queue" modelling and
  the CBOR decoder's bounded-reservation lemma are the nearest precedents.
  If a single state machine is too slow for Verus, split it by section
  (status line, fields, body) as the URL parser was split by state.
- **Limits are policy.** Every maximum (field section size, body size,
  chunk size) is a choice the standard leaves open; each is a listed
  modelling choice with a number, never an unstated constant.
- **No Internet in CI.** Every test runs against in-process servers; only
  the demo reaches a real server, and it runs locally, as in Phase 2.
- **`Secure` needs TLS.** Until 3.5 lands, cookie tests over the socket run
  on `http://`, and `Secure` cookies are exercised only in the kernel's
  tests, which set the flag directly.
- **The resolver is environment-dependent.** `resolv.conf` differs across
  systems and may be absent (macOS keeps it generated); the shell fails
  closed with a message, and the demo documents it.

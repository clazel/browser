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

### 3.5 TLS (seven items; 3.0 decided option B)

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

**As built** (on the `phase3/tls` branch, not on `main`): `crates/clazel-der`, tier 0, target tier 2; promotion waits
for CI's full verification on a pull request. Cursor-based DER readers and
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

**As built** (on the `phase3/tls` branch, not on `main`): `crates/clazel-pkcs1`, tier 0, target tier 2; promotion waits
for CI's full verification on a pull request. `src/spec.rs` transcribes RFC 8017
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

**As built** (branch `phase3/fetch-cookies`, `http://` only): `crates/clazel-fetch`, tier 0, target 2. Besides the `request`
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

**As built** (branch `phase3/kernel-fetch`, from `phase3/net-fetch`; not joined to the real transducer, no cookies from HTTP yet): `clazel-kernel`, tier 2 as before. `NavigateTab { tab, url }` (it lost its `script`) and a renderer's `Navigate` call `begin_navigation`: the tab's renderer records the URL in a new field `Renderer::pending` and the kernel outputs `Fetch { tab, url }`; nothing is committed. `Fetched { tab, outcome }` (`outcome` is `NetOutcome { url, net }`: the URL the fetch was started for and the octets the network delivered) calls `fetched`. `OpenTab` is unchanged (the demo's script is still its document). **Deviation from the plan's text:** the plan has the outcome carry 3.6's result and the jar; here the kernel takes the fetch as a parameter, `FetchFns { run(url, net) -> FetchRun }`, as it takes `UrlFns`, and runs it itself on `outcome.net`. A `FetchRun` is the result (`Done { url, body }` or `Failed`) and the `Set-Cookie` lines of the response chain, each with the request URL and context it answers (`HttpStore`). The kernel stores them through `apply_stores` (RFC 6265bis §5.7, `store_a_set_cookie_string`), so the jar is the kernel's, the shell never sees it, and no outcome can change it except by §5.7 storage; a fetch's result does not depend on the jar. Modelling choices (stated in `spec.rs`): a `Fetched` for a tab that is closed, whose renderer is not navigating, or navigating to another URL than the outcome's is ignored in full (no state change, no output, no cookie stored); a response's cookie is not stored for a request whose host is a public suffix or empty (as a document there is cookie-averse), so `jar_no_public_suffix` holds whatever the fetch returns; a final URL that is not a string of scalar values or has no lock is `Error` 3, a failed fetch `Error` 5, and the renderer stays; a redirect lands wherever the fetch says (the user is treated as having navigated there). **Phase 2 theorems:** all keep their statements, now over every `FetchFns` (`step`, `reachable`, `run_*` and the statements take `fetch`), and are proven: `kernel_wf` is preserved by `Fetched` (`lemma_fetched_wf`, `lemma_apply_stores_wf`); `theorem_reply_only_to_sender` gains an arm for `Fetch` (it names the sender's tab); `theorem_lock_set_only_by_navigation` counts `Fetched` as a navigation event; `theorem_cookie_integrity` has a `Fetched` case (the jar is `apply_stores` of the run's lines, or unchanged); `quark_cookie_integrity` gains the disjunct "a line of the fetch, for a host that may store, has this cookie's root". `theorem_cookie_noninterference`: a `Fetched` is kept in every observer's purge (what it carries came from the network; the other domain's renderer only contributed the URL it navigated to, which is the declassified `NavigateTab`, now `NavigateTab { tab, url }`, and a redirect into the observer's domain is that navigation), `user_tabs_open` also requires a `Fetched` to name an open tab, and `example_dead_tab_breaks_noninterference` is now a trace in which a closed tab's `Fetched` commits into the observer's domain in the purged run (a `NavigateTab` to a closed tab no longer shows anything to the observer, so that clause of the hypothesis is kept but no longer shown necessary). New theorems: `theorem_fetched_only_to_tab` (a `Fetched` is attributed to its tab's renderer, as a frame to its socket: its outputs go to that renderer or the one spawned, never a `Fetch`) and `theorem_fetched_answers_navigation` (ignored unless it answers the navigation in flight; one that does leaves the renderer not navigating), and `lemma_fetched_consistency`/`lemma_apply_stores_agree` for the unwinding. **Exec:** `exec::fetch` (`FetchFnsExec`, the exec twin of `FetchFns`, and the stand-in `StubFetch`: the octets are the body of a document at the URL asked for, no cookies), `begin_navigation_exec`, `fetched_exec`, `apply_stores_exec`, `step_exec` generic over the fetch; `step_real` runs with the stand-in. The host shell (`crates/clazel`) answers a `Fetch` with a stand-in network (the user's script as the page, empty for a renderer's own `Navigate`). Verus: `clazel-kernel` 340 verified, 0 errors (2026-10-25). Mutations: 36 in `mutations.json` (16 before, 20 new for the decisions above: stale, unsolicited and wrong-tab answers, the commit's body and final URL, `pending` kept after a commit or a failure, the URL and the `Fetch` of a navigation, the public-suffix, empty-host and no-host refusals, the jar update dropped (success and failure), a stale answer storing cookies, the error code of a failed fetch, the scalar check), all certified kills (the cookie ones evaluate `Seq::filter` through the certificate's `reveal`). Tests: `tests/fetch.rs` (test fetches through `step_exec`: body committed, stale, unsolicited and closed-tab answers ignored, failure, a cross-origin redirect, cookies stored through the kernel jar for the right root, not stored for a stale answer or a public suffix), and the other kernel tests settle each `Fetch` with an empty document; WPT `cookies/`, webstorage and the differential test pass unchanged. **Not built:** the join with 3.6's transducer, and with it the WPT `cookies/` rows that need `Set-Cookie` from HTTP (open). The join needs: (1) the transducer to give, with `Done`/`Fail`, the `Set-Cookie` lines it stored with their request URLs and contexts (a list of `HttpStore`s, with `theorem_jar_frame` as "the jar is those stores folded in"), since `FetchFns::run` reads no jar (the other option is jar in and jar out, which makes the kernel theorems need a locality condition on the fetch); (2) a proven encoding of `NetOutcome::net` as the transducer's inputs (`Connected`, `Bytes`, `Closed`, `Error`), and a `RealFetch: FetchFnsExec` that replays the transducer over it with `fetch()` its spec; (3) a design for how the shell learns what to `Send` (the `Cookie` field comes from the jar): either the kernel runs the transducer step by step (outputs for connect and send, events for network input) or the shell is given the `Cookie` value per request; replaying after the fact does not give it; (4) `step_real` switched to `RealFetch` and the host and tests to a real or test server. The corollaries in `real_theorems.rs` hold for every fetch and need no change.

### 3.8 The network shell and the `curl` clone (M)

`crates/clazel-net` (Tier 0, counted): the resolver (nameservers read from
`/etc/resolv.conf` on both platforms, a query over UDP with a random ID,
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
                                                     └─> 3.6 client ─> 3.7 kernel ─┘
```

3.1, 3.4, 3.5a, 3.5c and 3.5d start at once; 3.6 can start against
abstract parameters as soon as 3.1's field types exist; 3.8's `http://`
half does not wait on TLS.

## Status

| Item | State |
|------|-------|
| 3.0 TLS decision | done (2026-10-23): option B, our own TLS 1.3 client over libcrux, grounds and accepted costs recorded above |
| 3.1 HTTP field syntax | built: 146 verified, independent transcription (Fetch), 76 certified mutations, 10 unit tests; tier 2 with 3.2 and 3.3 (2026-10-25) |
| 3.2 HTTP/1.1 message framing | response side and request serializer built, tier 2 (2026-10-25, CI's full verification green on 9ce4086): spec, contracts, examples evaluated by Verus, implementation proven equal to the spec; independent transcription of RFC 7230 §3 and §4.1 (`message/independent.rs`) proven equal to the spec wherever they decide, with the inputs where the RFCs differ listed and excluded (`Out`); 150 mutations, all `killed` with certificates (the five limit survivors closed with parameterised limits `read_line_with` and `close_body_pending` and examples at limit 4). `theorem_monotone` and `theorem_no_early_decision` proven (`message/lemmas.rs`); an incremental `ResponseParser` (`message/incremental.rs`) proven to `feed_ensures`; a request parser spec and `theorem_request_round_trip`, with an executable request parser proven to it (a test aid: no leading empty lines, no request body). `ResponseParser::received_bytes` (proven to `received_bytes_ensures`) lets the fetch transducer keep no second copy of the octets. `clazel-http` 379 verified, 0 errors (2026-10-25). Not yet: an incremental `close` (it re-parses once); the independent transcription covers `parse_response_at_close` and `Transfer-Encoding` with `Content-Length` (2026-10-26, not yet CI-verified) but not obs-fold, codings other than a lone `chunked`, repeated `Content-Length`, chunk-extension whitespace, or a status line with no second SP or a major version other than 1 (each `Out`, with the reason in its header); the Fetch "HTTP-network fetch" transcription the plan names is not written |
| 3.3 HTTP conformance | built (`crates/clazel-http/tests/conformance_http.rs`, 7 suites, 0 unexpected failures): httparse differential on 6000 random, 60000 mutated (53915 pass, 6085 expected differences), 136 llhttp-corpus and 44 handcrafted heads (124 + 12 and 29 + 15 expected); the llhttp `test/response` and framing cases, 136 (109 pass, 27 expected failures, each listed with its reason); RFC 9112 §7.1 and §11 cases, 122; 3000 framing-by-construction messages. The llhttp fixtures are vendored under `tests/data/llhttp/` and converted by `cargo xtask testdata` (136 cases). `clazel-http` raised to tier 2 on 2026-10-25 |
| 3.4 DNS message format | done (2026-10-24): tier 2 (see As built) |
| 3.5a DER | built, but moved off `main` to the `phase3/tls` branch (2026-10-24) because it fails CI; see its **As built** paragraph there |
| 3.5b X.509 and path validation | not started (after 3.5a) |
| 3.5c RSA PKCS#1 v1.5 | built, but moved off `main` to the `phase3/tls` branch (2026-10-24) because it fails CI; see its **As built** paragraph there |
| 3.5d TLS record and handshake formats | built, but moved off `main` to the `phase3/tls` branch (2026-10-24) because it fails CI; see its **As built** paragraph there |
| 3.5e Key schedule and handshake state machine | not started (after 3.5d) |
| 3.5f Cryptography and the join | not started |
| 3.5g TLS conformance and trust store | not started |
| 3.6 Client state machine | built, `http://` only (branch `phase3/fetch-cookies`): transducer, redirects and cookies proven to their contracts; at most 21 requests, redirect bound, URL changes only by redirect, every `Send` the current request, silence until decided, split invariance for the shipped parser, `theorem_wire_cookies` and `theorem_jar_frame` proven; linear in the response's size; independent transcription of Fetch's redirect and cookie steps proven equal step by step and over whole runs (`theorem_independent_run`); conformance: http-state corpus through the client, 195 pass, 27 expected failures, and a differential of 1500 random redirect chains against rust-url and `cookie_store`; 64 mutations, every one a certified kill; tier 0 (see As built). Not yet: TLS, other request contexts, WPT fetch suites (none vendored), a CI run |
| 3.7 Kernel integration | built, not joined to 3.6's transducer (branch `phase3/kernel-fetch`, see As built): navigations are `Fetch` outputs and `Fetched` events, the fetch a `FetchFns` parameter, the jar updated by §5.7 storage of the run's `Set-Cookie` lines; the Phase 2 theorems restated and proven over every fetch, two new theorems, 36 certified mutations, `clazel-kernel` 340 verified. Open: the join (stand-in fetch today), the WPT `cookies/` rows that need `Set-Cookie` from HTTP |
| 3.8 Network shell and `curl` clone | `http://` half built: `clazel-net` (resolver, TCP, `fetch` driving 3.6's transducer, so redirects are followed) and `clazel fetch URL`, tested against local servers and checked by hand against http://example.com/. Hostile-server tests built (`clazel-net/tests/hostile.rs`, 11 passing, about 1.5 s, 142 MB peak, nearly all of it the endless chunked body, whose parser keeps both the 64 MiB of octets received and the body decoded from them): bytes that are not HTTP, an endless body (no framing, a Content-Length over the limit, and chunked), chunk sizes of 2^64 and 2^64-1, a field line over 8192 octets, 300 field lines, an immediate close, partial heads, silence and a stalled head (timeout), a short Content-Length. The endless chunked body did not return within 20 s while `ResponseParser` re-parsed its buffer on every feed; the incremental parser (3.2) fixed it. It regressed when `fetch` moved onto 3.6's transducer, which re-parsed everything received on every `Bytes` input; the transducer now feeds the incremental parser (see 3.6's As built), and the test takes under a second. Not yet: TLS, the http-state and WPT server tests, the line count in the README table. The CNAME target is converted by `clazel-dns`'s proven `wire_to_dotted` (done 2026-10-25, see 3.4); the shell no longer has a conversion of its own |
| 3.9 Status and README | not started |

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

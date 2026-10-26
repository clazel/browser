# Dependencies

Every third-party package in the resolved dependency graph (`Cargo.lock`)
needs a row in the allowlist below (see CLAUDE.md rule 8). `cargo xtask check`
enforces it:

1. Every resolved third-party package has a row with its **exact** version,
   and comes from crates.io. Git and path dependencies outside the workspace
   are rejected.
2. Every row is used. Stale rows fail, so the table never lists more than
   is really there.
3. The class matches how the package is reached:
   - `shipped`: may be reached directly from browser crates (every
     workspace crate except tooling). Allowed only for crypto (verified
     libraries), OS and windowing bindings, and GPU access.
   - `proof`: reached from browser crates only through `vstd`, or below a
     dev-only edge. This is Verus's proof library and its macro chain; ghost
     code is erased from normal builds. (A proof package may also be reached
     below a dev-only edge, as `proc-macro2` is through `serde_derive` named
     by `time` under the always-false `cfg(any())`: neither is compiled into a
     shipped binary.)
   - `test`: reached from browser crates only through their
     `[dev-dependencies]`, so it is compiled into test binaries and never
     into the browser. Used for differential testing against other engines.
     The checker follows the edge kind in `cargo metadata`: a package that a
     browser crate also reaches through `[dependencies]` or
     `[build-dependencies]` fails, whatever its row says.
   - `tooling`: must be unreachable from browser crates. Used by `xtask`,
     which never ships.

A package used in more than one way takes the strictest class that covers
all of them, in the order `shipped`, `proof`, `test`, `tooling` (e.g. one
used by both proof and tooling code is `proof`).

Dev-dependencies of browser crates are pinned to an exact version
(`=x.y.z`) like everything else.

Changing a row is a reviewable act. Adding one means saying why below.

<!-- BEGIN ALLOWLIST: checked by `cargo xtask check` -->
| Package | Version | Class | Why |
|---------|---------|-------|-----|
| vstd | 0.0.0-2026-10-04-0306 | proof | Verus standard library (`Seq`, `spec fn`s). Pinned to the installed Verus release. |
| verus_builtin | 0.0.0-2026-09-16-0054 | proof | Verus built-in items, required by `vstd`. |
| verus_builtin_macros | 0.0.0-2026-09-20-0158 | proof | The `verus!` macro (proc-macro). |
| verus_state_machines_macros | 0.0.0-2026-09-06-0133 | proof | Verus state-machine macros (proc-macro), required by `vstd`. |
| verus_syn | 0.0.0-2026-09-06-0133 | proof | Verus's fork of `syn`, used by its macros. |
| verus_prettyplease | 0.0.0-2026-09-06-0133 | proof | Verus macro output formatting. |
| syn | 2.0.119 | proof | Rust parser, used by Verus's macros. |
| synstructure | 0.13.2 | proof | Derive helper, used by Verus's macros. |
| convert_case | 0.4.0 | proof | Identifier case conversion, used by Verus's macros. |
| indexmap | 2.14.2 | proof | Ordered map, used by Verus's macros. |
| hashbrown | 0.17.1 | proof | Hash table, used by `indexmap`. |
| equivalent | 1.0.3 | proof | Key comparison trait, used by `indexmap`. |
| proc-macro2 | 1.0.107 | proof | Token streams for Verus's macros. Also used by `xtask` (with `span-locations`) to lex source files. |
| quote | 1.0.47 | proof | Token generation for Verus's macros. Also locked under `serde_derive` (tooling). |
| unicode-ident | 1.0.27 | proof | Identifier rules for `proc-macro2`. |
| encoding_rs | 0.8.35 | test | Firefox's Encoding Standard implementation: the reference engine in `clazel-encoding`'s differential test (`tests/conformance_utf8.rs`). Pinned to 0.8.35, whose only dependency is `cfg-if`; later releases add five more. |
| base64 | 0.22.1 | test | RFC 4648 base64 implementation (rust-base64): the reference engine in `clazel-base64`'s differential test (`tests/conformance_base64.rs`). No dependencies. |
| mime | 0.3.17 | test | hyperium's media type parser (used by `hyper` and `reqwest`): the reference engine in `clazel-mime`'s differential test (`tests/conformance_mime_types.rs`). No dependencies. |
| infer | 0.19.0 | test | A file-type detector by magic numbers (bojand/infer), written without the WHATWG standard: the reference in `clazel-mime`'s sniffing differential test (`tests/conformance_sniffing.rs`). Used without default features, so it has no dependencies (`cfb` is optional). |
| psl-types | 2.0.11 | test | Types of the `publicsuffix` crate's API (no dependencies). |
| publicsuffix | 2.3.0 | test | An independent Public Suffix List implementation (rust-publicsuffix, used by `cookie_store`), written from the list's own format: the reference engine in `clazel-psl`'s differential test (`tests/conformance_differential.rs`). Used without default features, so it has no `idna` dependency and handles ASCII hosts only; its only dependency is `psl-types`. |
| cfg-if | 1.0.5 | test | `#[cfg]` helper macro, required by `encoding_rs`. |
| percent-encoding | 2.3.2 | test | rust-url's percent-encoding (used by the `url` crate and Servo): a reference engine in `clazel-percent`'s differential test (`tests/conformance_percent.rs`). No dependencies. |
| form_urlencoded | 1.2.2 | test | rust-url's `application/x-www-form-urlencoded` serializer: the reference for that percent-encode set in the same test. Its only dependency is `percent-encoding`. |
| url | 2.5.8 | test | rust-url, the WHATWG URL parser used by Servo: the reference engine in `clazel-url`'s differential test (`tests/conformance_url.rs`); also a dev-dependency of `clazel-kernel`, whose differential test parses the URLs of its generated traces with it. Used without default features, so its `std` feature (which names `serde` as a weak dependency) is off; its dependencies (`form_urlencoded`, `idna`, `percent-encoding`) are already listed. |
| idna | 1.1.0 | test | rust-url's IDNA implementation (used by the `url` crate, Servo and Firefox): the reference engine in `clazel-idna`'s Punycode and UTS #46 differential tests (`tests/conformance_punycode.rs`, `tests/conformance_uts46.rs`). |
| idna_adapter | 1.1.0 | test | `idna`'s Unicode back end, pinned to 1.1.0, the unicode-rs one (the 1.2 releases pull in ICU4X, about twenty crates). |
| idna_mapping | 1.1.0 | test | UTS #46 mapping data for `idna_adapter` 1.1.0. |
| unicode-joining-type | 1.0.0 | test | Joining_Type data, required by `idna_mapping`. No dependencies. |
| unicode-bidi | 0.3.18 | test | Bidi_Class data, required by `idna_adapter` 1.1.0. |
| unicode-normalization | 0.1.26 | test | NFC, required by `idna_adapter` 1.1.0. |
| tinyvec | 1.13.3 | test | Small-vector type, required by `unicode-normalization`. |
| smallvec | 1.16.3 | test | Small-vector type, required by `idna`. No dependencies. |
| utf8_iter | 1.0.4 | test | UTF-8 iteration, required by `idna`. No dependencies. |
| cookie_store | 0.21.1 | test | The cookie jar of reqwest's `cookie_store` feature (it follows RFC 6265): the reference engine in `clazel-cookie`'s differential test (`tests/conformance_differential.rs`) and in `clazel-kernel`'s (multi-renderer `document.cookie` traces). Used without default features, so it has no Public Suffix List and no serde. Pinned to 0.21.1, whose `time` requirement (^0.3.16) lets `time` stay at 0.3.17, which has no dependency on `deranged`, `powerfmt` or `num-conv`. |
| cookie | 0.18.2 | test | The `cookie` crate (`Cookie::parse`), used by `cookie_store`. Its dependencies are `time`, `percent-encoding` (already listed) and, as a build dependency, `version_check`. |
| time | 0.3.17 | test | Date and time types, required by `cookie` and `cookie_store`; also a direct dev-dependency of `clazel-cookie` and `clazel-kernel`, to pin it to 0.3.17 (later releases pull `deranged`, `powerfmt` and `num-conv`). Its optional `serde` dependency is named by the weak feature `serde?/alloc`, which `cargo metadata` lists as an edge although `cargo tree` shows none; that is why `serde` and its pinned dependencies are `test` and not `tooling`. |
| time-core | 0.1.0 | test | `time`'s shared constants. No dependencies. |
| time-macros | 0.2.6 | test | `time`'s `format_description!` and date macros (proc-macro), required by `time` with the `macros` feature that `cookie` asks for. Its only dependency is `time-core`. |
| version_check | 0.9.5 | test | Rust version detection in `cookie`'s build script. No dependencies. |
| document-features | 0.2.12 | test | Documentation generation helper (proc-macro) named by `cookie_store`. Its only dependency is `litrs`. |
| litrs | 1.0.1 | test | Literal parsing, required by `document-features`. No dependencies (its `proc-macro2` feature is off). |
| log | 0.4.34 | test | The `log` facade, required by `cookie_store`. No dependencies. |
| libc | 0.2.190 | shipped | Rust bindings to the C library: struct layouts and constants (`sock_filter`, `sock_fprog`, `CLONE_NEW*`, `SECCOMP_SET_MODE_FILTER`, `SYS_seccomp`, `SYS_landlock_*`, `SYS_ptrace`, `PTRACE_ATTACH`, `PR_SET_NO_NEW_PRIVS`) and the declarations of `prctl`, `syscall`, `unshare`, `fork` and `_exit`, for `clazel-sys` only (CLAUDE.md rules 1 and 8). Reached only on Linux (`[target.'cfg(target_os = "linux")'.dependencies]`), with default features off, so it has no dependencies; macOS needs none. Getting these layouts wrong by hand is undefined behaviour, which is why it is a dependency rather than our own declarations. It is also reached by `cpufeatures` (class `test`, below the dev-only edge of `sha2` in `clazel-pkcs1`), on every target; that edge compiles into test binaries only. |
| minicbor | 2.3.1 | test | A small CBOR codec (no_std): the reference engine in `clazel-ipc`'s differential test (`tests/conformance_cbor.rs`). Chosen over `ciborium` (which pulls `serde`, `half` and two more). Used without default features (only `alloc`), so it has no dependencies. It accepts non-shortest arguments, which the test accounts for. |
| simple-dns | 0.12.0 | test | A DNS message parser and writer (balliegojr/simple-dns): the reference engine in `clazel-dns`'s differential test (`tests/conformance_dns.rs`), which writes random messages with it (with and without name compression), reads them with `clazel-dns` and compares, and compares what both read from the same mutated octets. Chosen as the full-message parser with the fewest dependencies that also writes responses: `dnsparse` has none but reads only the header, questions and answers (and uses `unsafe`), and `dns-parser` has two (`byteorder`, `quick-error`) and writes only queries. Its only dependency is `bitflags`. |
| httparse | 1.10.1 | test | The HTTP/1.x message-head parser of hyper (Sean McArthur's `httparse`): the reference engine in `clazel-http`'s differential test (`tests/conformance_http.rs`), which compares the status code, every field and the head length it reads from random and mutated responses with ours. It parses only the head, so the framing (`Content-Length`, chunked) is checked against expectations the test builds by construction. Used without default features (`std` adds nothing to it); no dependencies, and its build script uses none. |
| bitflags | 2.13.2 | test | Bit-flag macro, required by `simple-dns`. No dependencies. |
| der | 0.8.2 | test | RustCrypto's DER implementation (used by `rsa`, `x509-cert` and `pkcs8`): the reference engine in `clazel-der`'s differential test (`tests/conformance_der.rs`). Used with default features off and only `alloc` and `oid`, so its only dependencies are `const-oid` and `zeroize` (the smallest DER crate that parses and writes every type item 3.5a covers; no other candidate was needed). Pinned to 0.8.2, the latest stable release. |
| const-oid | 0.10.2 | test | `der`'s OBJECT IDENTIFIER type (the `oid` feature). No dependencies with default features off. |
| zeroize | 1.9.1 | test | Zeroing of memory on drop, required by `der`'s `alloc` feature. No dependencies as built. |
| serde_json | 1.0.154 | tooling | `xtask` parses `cargo metadata` output. |
| serde_core | 1.0.229 | test | Required by `serde_json`. |
| itoa | 1.0.18 | test | Integer formatting, required by `serde_json`. |
| memchr | 2.8.3 | tooling | Byte search, required by `serde_json`. |
| zmij | 1.0.23 | tooling | Float formatting, required by `serde_json`. |
| serde | 1.0.229 | test | Locked but never compiled: `serde_json` names it under the always-false `cfg(any())` to pin versions. |
| serde_derive | 1.0.229 | test | Locked but never compiled: `serde_core` names it under `cfg(any())`. |
| syn | 3.0.9 | test | Locked but never compiled: dependency of `serde_derive`. |
<!-- END ALLOWLIST -->

The only `shipped` package is `libc`, and only `clazel-sys` depends on it
(only on Linux). Everything else that runs in the browser is our own code. The
`test` packages are compiled only into test binaries.

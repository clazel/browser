# x509-limbo: path-validation testcases for X.509 implementations

Upstream: https://github.com/C2SP/x509-limbo
Commit: 1080e565f26e544bbe9cf99953be8a57c08e7e20
License: Apache-2.0 (`LICENSE.md`, copied from `LICENSE` at the root of the repository)

Commit date: not recorded by this download; it is the head of upstream's
default branch when vendored on 2026-10-26.

The upstream README says "Apache-2.0 / MIT", but the repository ships only the
Apache-2.0 text (`LICENSE`); `LICENSE-APACHE` and `LICENSE-MIT` do not exist at
this commit. We vendor the one licence text that exists.

Files, copied byte for byte from that commit (fetched from
`https://github.com/C2SP/x509-limbo/raw/<commit>/<file>`):

| Here | SHA-256 | Size |
|------|---------|------|
| `limbo.json` | `611e337b9fb477b927bae65434650692cb9d2070ff5b05f975d0403510acd4de` | 41,791,455 bytes |
| `LICENSE.md` | `aac73b3148f6d1d7111dbca32099f68d26c644c6813ae1e4f05f6579aa2663fe` | 11,360 bytes |

`limbo.json` is the whole published corpus: 9,802 testcases (9,572 `bettertls`,
109 `rfc5280`, 56 `webpki`, and a few dozen `crl`, `pathlen`, `pathological`,
`online`, `rfc9881`, `cve` and `invalid` cases) and 30,379 distinct
certificates. It was vendored in full, byte for byte, on Alex's decision to
raise the 20 MB cap for this file.

`xtask/src/testdata/x509_limbo.rs` reduces it to two derived files, which are
ours and reproducible (`cargo xtask check` fails if either is stale), so no
Rust source holds 41.8 MB of literals:

- `tests/generated/x509_limbo.rs`: an index of the testcases (id, validation
  kind, expected result and peer name, validation time, features,
  importance, and the certificates of each as indices);
- `tests/generated/x509_limbo_certs.bin`: the distinct certificates as DER,
  concatenated; the index gives each one's offset and length.

Both are read by `tests/conformance_limbo.rs`, which runs every `SERVER`
testcase through `verify_server_chain` with accept-all signature links and
compares limbo's verdict. See the crate README for what it covers.

To update, download `limbo.json` and `LICENSE` from a newer commit into an
empty directory, copy them here, change the commit, size and hashes above, run
`cargo xtask testdata`, and update `EXPECTED_FAILURES` in
`tests/limbo/expected_failures.rs` (the test names every id that appeared or
vanished).

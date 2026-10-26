# clazel-x509

## x509-limbo harness (`tests/conformance_limbo.rs`)

The x509-limbo corpus (C2SP, Apache-2.0; 9,802 testcases, 30,379 distinct
certificates) is vendored byte for byte in `tests/data/x509-limbo/` and reduced
by `cargo xtask testdata` to a testcase index and a binary file of DER
certificates under `tests/generated/` (`cargo xtask check` fails if either is
stale).

What the harness covers: every distinct certificate goes through every decoder
(envelope, signature algorithm, TBS, SPKI, extensions, SAN, BasicConstraints,
KeyUsage, ExtendedKeyUsage, NameConstraints) without panicking, with the
accepted counts pinned; every `SERVER` testcase that expects `SUCCESS` for a DNS
or IP name has a leaf that `check_leaf_certificate` accepts (RFC 9525 match,
validity, EKU, key usage), and none of its certificates is rejected by a decoder.

What it does not cover: limbo's chain-validation verdicts. There is no path
validation yet, so every other testcase is listed by id, with a reason, in
`tests/limbo/not_yet_supported.rs`; the test fails if an id appears or vanishes,
or if a listed case starts passing. Two server-leaf cases (`rfc5280::ca-as-leaf`,
`pathlen::validation-ignores-pathlen-in-leaf`) are listed because the leaf
policy rejects a CA certificate as an end entity, where limbo follows RFC 5280.

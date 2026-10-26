# Wycheproof RSASSA-PKCS1-v1_5 signature verification vectors

Upstream: https://github.com/C2SP/wycheproof/tree/d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9/testvectors_v1
Commit: d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9
License: Apache-2.0 (`LICENSE.md`, copied from the root of the Wycheproof repository)

Files, copied byte for byte from that commit (all under `testvectors_v1/`):

| Here | Key | Hash | What it adds |
|------|-----|------|--------------|
| `rsa_signature_2048_sha256_test.json` | 2048 bits, e = 65537; two more keys with e = 3 | SHA-256 | the main corpus: BER-encoded padding, invalid ASN.1 in the padding, modified padding, wrong hash, missing hash, short padding, signature malleability, a signature of 4 bytes of value, a signature close to n |
| `rsa_signature_2048_sha384_test.json` | 2048 bits, e = 65537 | SHA-384 | the same cases for SHA-384's `DigestInfo` |
| `rsa_signature_3072_sha256_test.json` | 3072 bits, e = 65537; one more key with e = 3 | SHA-256 | |
| `rsa_signature_4096_sha512_test.json` | 4096 bits, e = 65537 | SHA-512 | the same cases for SHA-512's `DigestInfo` |

The task for this item named a fourth file, `rsa_signature_test.json`, an
older mixed-size edge-case file. It does not exist at this commit: the
legacy `testvectors/` directory has been removed upstream and every
`testvectors_v1` file is one key size and one hash. The SHA-384 file above
covers the third hash that file would have added. The 8192-bit file
(`rsa_signature_8192_sha256_test.json`, 258 vectors) was vendored first and
then dropped: one verification at that size takes about two seconds in a
debug build, so its 258 vectors took nine minutes of `cargo test`, for the
same checks the 4096-bit file makes. The largest accepted size is covered by
two hand-built cases instead (`tests/handbuilt/mod.rs`: an OpenSSL signature
at 8192 bits, and the same with one bit flipped).

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/wycheproof_rsa.rs` converts the JSON into
`tests/generated/wycheproof_rsa_pkcs1.rs`, read by
`tests/conformance_pkcs1.rs`: every key as modulus and exponent octets (hex)
and every test as message octets, signature octets, expected result
(`valid`, `invalid` or `acceptable`) and flags. The message digest is not
stored: the test computes it with `sha2`.

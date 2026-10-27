# Wycheproof ECDSA secp384r1 verification vectors (DER signatures)

Upstream: https://github.com/C2SP/wycheproof/tree/d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9/testvectors_v1
Commit: d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9
License: Apache-2.0 (`LICENSE.md`, copied from the root of the Wycheproof repository)

Files, copied byte for byte from that commit (all under `testvectors_v1/`,
fetched from `https://raw.githubusercontent.com/C2SP/wycheproof/<commit>/testvectors_v1/<file>`
on 2026-10-27):

| Here | Hash | Tests | valid / invalid / acceptable | Bytes | SHA-256 of the file |
|------|------|-------|------------------------------|-------|---------------------|
| `ecdsa_secp384r1_sha256_test.json` | SHA-256 | 472 | 162 / 310 / 0 | 361096 | `660c948e5433279ecdf966e8a1386b69ecec618efc1ff00269e85aa9dc84f0a6` |
| `ecdsa_secp384r1_sha384_test.json` | SHA-384 | 504 | 194 / 310 / 0 | 375442 | `8a5b3ae1760975143414811f13588c24d951d9d8c904195087ba327591dfe9cc` |
| `ecdsa_secp384r1_sha512_test.json` | SHA-512 | 542 | 231 / 311 / 0 | 393091 | `f44bae32e419fc75c5b5af751cff4e35145cfbcc24944e378d5f30889d310513` |

`LICENSE.md` is 11357 bytes, SHA-256
`58d1e17ffe5109a7ae296caafcadfdbe6a7d176f0bc4ab01e12a689b0499d8bd`, and is
identical to the one in `clazel-pkcs1`'s copy of the same commit.

Each file has 105 groups (one public key each, `type` `EcdsaVerify`, curve
`secp384r1`), with `sig` a DER `Ecdsa-Sig-Value`. The P1363 files
(`ecdsa_secp384r1_sha{384,512}_p1363_test.json`, raw `r || s`) exist at this
commit and are not vendored: they test the same group law and range checks,
and the DER files add the encoding cases, which the test sends through
`clazel-der`.

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/wycheproof_ecdsa.rs` converts the JSON into
`tests/generated/wycheproof_ecdsa_p384.rs`, read by
`tests/conformance_ecdsa.rs`: every key as its 97-octet uncompressed ECPoint
(hex), and every test as the digest of `msg` (computed by the converter with
the file's own hash), the DER signature, the expected result (`valid`,
`invalid` or `acceptable`) and the flags.

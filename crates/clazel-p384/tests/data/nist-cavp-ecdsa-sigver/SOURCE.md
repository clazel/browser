# NIST CAVP FIPS 186-4 ECDSA SigVer examples

Upstream: https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/dss/186-4ecdsatestvectors.zip
SHA-256: fe47cc92b4cee418236125c9ffbcd9bb01c8c34e74a4ba195d954bcb72824752
License: Public domain (a work of the United States government, 17 U.S.C. 105; see `LICENSE.md`)

There is no git commit: NIST publishes this as a zip, "Example test files for
FIPS 186-3 ECDSA" (`Readme.txt` in the zip, updated May 5, 2015), from the
Cryptographic Algorithm Validation Program page "Digital Signature Algorithm
Validation System" (Digital Signatures, ECDSA test vectors). The `SHA-256:`
line above is the zip's: 1144603 bytes, downloaded twice on 2026-10-27 with
the same hash. The `SHA-256:` line stands in for the `Commit:` line that
git-hosted suites carry.

Only one file of the zip is vendored, copied byte for byte (CRLF line
endings, as published; the zip entry is dated 2011-05-09):

| Here | Zip entry | Bytes | SHA-256 of the file |
|------|-----------|-------|---------------------|
| `SigVer.rsp` | `186-4ecdsatestvectors/SigVer.rsp` | 730106 | `e9841c3d12e323042751460d0b8ef4bc59c2640105ec7da4852775f80ab10191` |

The file covers every NIST curve (P, K and B) with SHA-1, SHA-224, SHA-256,
SHA-384 and SHA-512, 15 cases per section. The converter
(`xtask/src/testdata/nist_cavp_sigver.rs`) reads only the five `[P-384,SHA-x]`
sections (75 cases) and checks that nothing else in the file is a P-384
section. SHA-1 is included: `verify` takes a digest of 0 to 64 octets, so a
20-octet SHA-1 digest is a valid input, and these cases test the digest
truncation and padding rules for short digests. `Msg` is the message, not a
digest; the converter hashes it. Not vendored: `SigVer_TruncatedSHAs.rsp`
(SHA-512/224 and SHA-512/256) and the generation and key-pair files.

To update, replace the file from a newer zip, change the hashes above, and run
`cargo xtask testdata`.

`tests/generated/nist_cavp_ecdsa_sigver.rs` is the converted table, read by
`tests/conformance_ecdsa.rs`: for each case the digest, the key as
`04 || Qx || Qy`, `R`, `S`, the expected result and NIST's reason for a failure.

# clazel-pkcs1

RSA PKCS#1 v1.5 signature verification (RFC 8017 §8.2.2) over our own
multiple-precision arithmetic. Part of [Clazel](../../README.md), a web
browser whose parsers of untrusted input carry machine-checked proofs.

## What it is, and what it is not

**Public-key verification only.** `verify(n, e, digest, hash, signature)`
takes a public key (modulus and exponent), the digest of the message and a
signature, and answers whether the signature is valid. Every input is
public. There is no signing, no private key and no secret anywhere in the
crate.

**Why it is our own code.** No formally verified library offers RSA
PKCS#1 v1.5 verification, and most certificate chains need it (the TLS plan,
[docs/phases/phase-3.md](../../docs/phases/phase-3.md) item 3.0). The usual
argument for never writing your own cryptography is side channels from
secret-dependent operations; verification has no secrets, so that argument
does not apply, and the code is proven against the RFC instead.

**No constant-time claim.** Comparisons, branches and loop counts depend on
the (public) inputs, and nothing here is constant time. Do not use any of
this for a private-key operation.

## What it checks

- RFC 8017 §4.1 I2OSP, §4.2 OS2IP, §5.2.2 RSAVP1 (with its range check on
  the signature representative), §8.2.2 RSASSA-PKCS1-v1_5-VERIFY (every
  step, including the length check and the comparison of the two encoded
  messages), §9.2 EMSA-PKCS1-v1_5-ENCODE with the `DigestInfo` strings of
  Note 1 for SHA-256, SHA-384 and SHA-512 (`src/spec.rs`).
- The digest is an input (the hash is computed elsewhere). The encoded
  message is compared whole, so a signature with garbage after the digest
  (the e = 3 forgery of Bleichenbacher, 2006) is invalid.
- Domain restrictions, stated in the spec header, outside the RFC: the
  modulus has 2048 to 8192 bits, and `3 <= e <= 2^64 - 1`; anything else is
  "invalid signature".

## The arithmetic

Numbers are little-endian `Vec<u64>` limbs with a `nat` spec
(`src/bignum/spec.rs`). Comparison and subtraction are limb loops with
carries. **Modular multiplication is double-and-add** (right to left over the
bits of one factor, with one conditional subtraction per step), not
Montgomery or schoolbook-plus-division: it needs only add, subtract and a
loop, works for every modulus, and its proof is a chain of congruences.
Exponentiation is right-to-left square-and-multiply over it, for any `e`
up to 2^64 - 1. It is quadratic with a large constant. Measured in a debug
build (`cargo test`, Apple M-series): one 2048-bit verification with
`e = 65537` takes about 120 ms (9 ms in a release build), and one 8192-bit
verification about 2 s. The Wycheproof run (1035 vectors, up to 4096
bits) takes about four minutes in a debug build, which is why the 8192-bit
Wycheproof file is not vendored and the largest size is two hand-built
cases.

## Verification

Tier 2 (raised on CI's full verification of its pull request; see the
[phase 3 plan](../../docs/phases/phase-3.md)). The current numbers are in the
[status table](../../README.md#verification-status).

- **Proven (Verus):** `verify`, `encode_message` and every arithmetic
  function meet the contracts in `src/contract.rs` and
  `src/bignum/contract.rs`, for numbers of any length; that includes
  absence of panics and of overflow. `mod_exp` equals `s^e mod n` with
  `vstd`'s `pow`. Lemmas (`src/lemmas.rs`): I2OSP after OS2IP is the
  identity on octet strings, a signature made by the textbook RSASP1
  verifies (the RFC's correctness claim, with the Carmichael-exponent
  property of the modulus as a stated hypothesis, not a security claim), a
  representative at least `n` is rejected, a signature of the wrong length
  is rejected, and the three `DigestInfo` prefixes have the lengths §9.2
  says.
- **Evaluated:** `src/examples.rs` proves known answers of every RFC
  function by evaluating the spec (small keys with `e = 1`, the textbook
  `4^13 mod 497`, the boundary of every range).
- **Independent transcription:** `src/independent.rs` is written from RFC
  2313 (parse the decrypted block, then compare the data) with HAC
  Algorithm 14.79 for the exponentiation, and is proven to accept exactly
  what the RFC 8017 spec accepts; `src/bignum/independent.rs` transcribes HAC
  Algorithm 14.12 (multiplication) and proves it computes the product. The
  same agent wrote both, so they are independent in source document and
  order of writing only.
- **Mutations:** every deliberately broken spec rule is rejected by a
  checked certificate (`mutations.json`); counts are in the table.
- **Kani:** harnesses (`src/proofs.rs`) check the limb arithmetic
  exhaustively for 2-limb numbers against `u128`.
- **Conformance:** Wycheproof's RSASSA-PKCS1-v1_5 vectors (2048, 3072 and 4096
  bits; SHA-256, SHA-384, SHA-512), with the `acceptable`
  vectors (`DigestInfo` without NULL parameters) listed as expected
  failures, and hand-built cases (OpenSSL signatures, malformed encoded
  messages, signatures at least `n`, the e = 3 forgery, out-of-range keys).
  There is no differential against the `rsa` crate: its tree is 35
  packages with default features off.

## Trust

The proofs assume the Rust compiler, Verus and its solver, the `vstd`
library, and that the specs transcribe the standards correctly; testing
against the suites above is the check on that last point, not a proof. The
`DigestInfo` octet strings are literals from the RFC; that they equal a DER
encoding is item 3.5f's lemma. The full list is in
[docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

```rust
use clazel_pkcs1::spec::HashId;
use clazel_pkcs1::verify::verify;

// `n` is the modulus as big-endian octets (leading zero octets allowed),
// `digest` is the SHA-256 of the signed message, computed elsewhere.
fn check(n: &[u8], e: u64, digest: &[u8], signature: &[u8]) -> bool {
    verify(n, e, digest, HashId::Sha256, signature)
}
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.

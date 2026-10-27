# clazel-p384

ECDSA signature verification over NIST P-384 (FIPS 186-5 §6.4.2), specified
in Verus. Part of [Clazel](../../README.md), a web browser whose parsers of
untrusted input carry machine-checked proofs.

## Status: specification, field, point arithmetic and `verify`

**Tier 0, target tier 2.** The specification, the field arithmetic, the
point arithmetic and `verify` are written, and `verify` is proven against
the contract below the six axioms. The tier 1 and tier 2 evidence is not
(see Verification). What exists:

- `src/spec.rs`: what "a valid ECDSA P-384 signature" means, transcribed
  step by step from FIPS 186-5 §6.4.2, with the routines it defers to taken
  from SP 800-186 (Appendices D.1.1.1 and F.1, and B.1 of FIPS 186-5) and
  SEC 1 v2 (§2.2.1 the group law, §2.3 conversions, §3.2.2.1, §4.1.4). The
  sources are pinned by SHA-256 in the file's header, which also lists every
  modelling choice (13 of them) and how the lossy text extraction of the
  PDFs was read.
- `src/contract.rs`: what the executable `verify(digest, r, s, point)` is
  proven to satisfy, as predicates over the spec. `src/point_contract.rs`:
  the same for the group law, the scalar product, the key decoding and the
  digest's reduction.
- `src/examples.rs`: known answers, proven by evaluating the spec
  (`by (compute_only)`), on a toy curve and on P-384.
- `src/axioms.rs`, `src/field/`: the field arithmetic, described below.
- `src/point.rs`, `src/scalar.rs`, `src/verify.rs`, `src/convert.rs`,
  `src/lemmas.rs`: the executable group law, key decoding, scalar product,
  `verify`, and their lemmas, described below.
- `tests/field.rs`: known answers for the field, computed with Python.
- `tests/verify.rs`: smoke tests of `verify` (Wycheproof vectors and
  hand-damaged inputs), described below.
- `tests/conformance_ecdsa.rs`, `tests/conformance_differential.rs`: the
  conformance suites and the differential against `ring`, described under
  Conformance below.

What is evaluated in `examples.rs` is the spec itself, which shows the
transcription computes what was worked out independently, not that it matches
the standards (a person reads it against them;
[docs/SPEC-STYLE.md](../../docs/SPEC-STYLE.md)).

## The field (modulo p and modulo n)

A field element, `field::Fe`, is a residue modulo p (coordinates) or modulo n
(scalars): six little-endian `u64` limbs in the Montgomery domain, with the
invariant that their value is below the modulus. `Fe::val` is the residue
they stand for.

- **fiat-crypto =0.3.0 is a shipped dependency** (default features off, no
  dependencies of its own, no `unsafe`). Its `p384_64` and `p384_scalar_64`
  modules are Coq-synthesized Montgomery arithmetic. It cannot be vendored
  under our lints (it indexes arrays and uses plain arithmetic), so it is
  called, and trusted as a verified library: see the TCB in
  [docs/VERIFICATION.md](../../docs/VERIFICATION.md).
- **Six axioms**, in `src/axioms.rs`: `mul`, `add` and `sub` for each of the
  two modules. Each is a thin `external_body` wrapper around one fiat
  function whose `ensures` copies the postcondition fiat prints above it and
  whose `requires` copies the printed precondition (an input below `m`). The
  `Fe` invariant discharges that precondition at every call. Nothing else
  about fiat is assumed, and a different session reviews the six.
- **Proven over those axioms** (`src/field/fe.rs`, `lemmas.rs`, against
  `field/contract.rs`): conversion into the Montgomery domain (`mul` by
  `R^2 mod m`) and out of it (`mul` by 1); our own big-endian octet-string
  conversions, with the range check as a limb comparison (`from_octets`
  returns none unless the integer is below the modulus); equality; `pow` by
  square-and-multiply over a 48-octet exponent against the spec's `pow_mod`;
  and `inv`, `pow` with exponent `m - 2` and the check `a w ≡ 1`, against
  the spec's `inv` (so `Some(w)` exactly when the spec's `inv` is, and
  Fermat's little theorem is not used).
- **Not used from fiat:** its `to_bytes`, `from_bytes`, `to_montgomery`,
  `from_montgomery`, `nonzero`, `opp`, `square` and `divstep` (no axiom for
  any of them).
- **Not constant time, by design:** `pow` branches on the exponent's bits
  (every input is public).
- **Checked against Python:** `tests/field.rs` compares `add`, `sub`, `mul`,
  `inv`, `pow` and the octet conversions with known answers for both moduli.
  That is the check on the axioms' fit to the real fiat, and on the constants
  of `field/spec.rs` and `fe.rs` (the moduli, `R^2 mod m`, the exponents).

## The group law, the scalar product and `verify`

Proven in Verus against `spec.rs`, over the six axioms and nothing else (no
new axiom, no `assume`, no `external_body` outside `axioms.rs`).

- **`point::Point`** is the point at infinity or an affine pair of `Fe`s
  modulo p, with a view to `spec::Point`. `point::ec_add` runs SEC 1 §2.2.1's
  rules in the spec's order (rules 1 and 2, then the negation test `x1 == x2
  && (y1 + y2) % p == 0`, then different x, then doubling), each field
  operation an `Fe` operation, so its contract is `r == spec::ec_add(p384(),
  a, b)`, `None` exactly when the spec's is (a failed `inv`).
- **`point::decode_public_key`** is `spec::decode_public_key`: length 97, first
  octet `04`, each coordinate below p by `Fe::from_octets`, and the curve
  equation. Compressed, hybrid and infinity encodings are refused.
- **`scalar::scalar_mul`** is MSB-first double-and-add over the 48 octets of
  the scalar, one bit at a time; the loop invariant is that after the top `i`
  bits the accumulator is `spec::scalar_mul` of the integer they make, from
  the spec's own recursion. No associativity is used.
- **`scalar::derive_e`** reads the leftmost `min(|H|, 48)` octets of the digest
  and reduces them modulo n by Horner's rule in the field, so `e >= n` is
  handled; the proof relates the spec's bit-string `derive_e` to `os2ip`.
- **`verify::verify`** follows the spec's order: the key first, step 1 (`r`
  and `s` in `[1, n - 1]` as integers, before any reduction), step 3, step 4
  (`Fe::inv` mod n), step 5, step 6 as the sum of two separately computed
  products (infinity and any failed operation reject), and step 9 with
  `x_R mod n` reduced properly (`x_R < p` can exceed n). Its contract is
  `ok == ecdsa_verify(p384(), digest, os2ip(r), os2ip(s), point)` for a
  digest of 0 to 64 octets.
- **Not constant time, by design**, and slow by design: this is the affine
  stage, one field inversion (about 768 multiplications) per group
  operation. Measured by `tests/verify.rs`'s `timing` test on the development
  machine (Apple silicon): about 0.94 s per verification in a debug build and
  about 45 ms in a release build.
- **Smoke tests.** `tests/verify.rs` accepts eight valid and rejects six
  invalid vectors of Wycheproof's `ecdsa_secp384r1_sha384_test.json`
  (commit `d17cc89f`; tcIds in the file), and rejects damaged `r`, `s`,
  digests and keys. The full suites are under Conformance below.
- **One addition to `field::Fe`:** `Fe::dup`, a copy with the same
  `which` and `val`. `Fe` is not `Clone` and `Fe`'s contracts and the axioms
  are unchanged.

## Conformance

Three test targets run `verify` against the outside world. The numbers are
printed by the tests (`clazel-conformance:` lines) and read by `cargo xtask
verify`; the README table is written from them by CI.

- **Wycheproof** (`tests/conformance_ecdsa.rs`; Apache-2.0, commit
  `d17cc89f`, vendored under `tests/data/wycheproof-ecdsa-p384/` and
  converted to a Rust table by `cargo xtask testdata`):
  `ecdsa_secp384r1_sha256_test.json` (472 tests), `..._sha384_...` (504) and
  `..._sha512_...` (542), 1,518 in all, all passing, none `acceptable`, no
  expected failure. The signatures are DER, so each test runs the way a TLS
  client would use the crate: `clazel-der` reads the `Ecdsa-Sig-Value` into
  `r` and `s` (a dev-dependency; this crate has no DER layer), then `verify`
  decides. The malformed-DER tests (BER lengths, negative or oversized
  INTEGERs, trailing bytes) are rejected by `clazel-der`: 705 of the 1,518
  signatures never reach `verify`, none of them a `valid` test, and each
  still counts in `total`. The SHA-512 digest is 64 octets, which `verify`
  truncates (spec choice 10). The converter hashes the messages itself.
- **NIST CAVP 186-4 `SigVer.rsp`** (public domain, vendored under
  `tests/data/nist-cavp-ecdsa-sigver/`): the five `[P-384,SHA-x]` sections,
  SHA-1, SHA-224, SHA-256, SHA-384 and SHA-512, 15 cases each, 75 in all, all
  passing. `R` and `S` are integers, so the DER layer is not involved. SHA-1
  is included because `verify` takes any digest of 0 to 64 octets.
- **Differential against `ring` 0.17.14** (`tests/conformance_differential.rs`):
  a fixed-seed generator picks 2,000 messages and which of 8 key pairs signs
  each; `ring` signs (SHA-384) and verifies; for each signature seven cases
  (the valid one, a flipped bit in `r`, in `s`, in the message, in the public
  key, another key, and edge values 0, 1, n - 1, n, n + 1, 2^384 - 1 for `r`
  and `s`) are given to both engines, 14,000 comparisons, and the verdicts
  must be equal (and the valid signature accepted). `ring`'s keys and nonces
  come from the operating system (its random source cannot be replaced), so
  the signatures differ between runs and only the choices around them are
  seeded. There is no SHA-256 differential: `ring` can verify but not sign
  P-384 with SHA-256 in a fixed-width form.
- **Speed and Miri.** A verification is about 1 s in an unoptimised build, so
  the workspace manifest builds this package with `opt-level = 3` in the dev
  profile (overflow checks stay on); the Wycheproof and CAVP suites then
  take about 30 s together and the differential about 80 s on an 8-core
  machine. All three targets are ignored under Miri.
- **Not done:** the independent field differential of the design was dropped
  (it would test fiat-crypto against itself); ACVP-Server's JSON is not
  vendored; the P1363 Wycheproof files are not vendored.

## What it is, and what it is not

**Public-key verification only.** The key, the signature and the digest are
public, so nothing here has a constant-time requirement, and none is claimed.
No signing, no private key.

**The input is the digest**, 0 to 64 octets, not the message. Hashing is done
by `clazel-crypto`, so the only axioms are the six field ones above. The key
is the full 97-octet ECPoint `04 || X || Y`; decoding and validation are
inside the verified code (uncompressed form only; the compressed form is
refused).

## The spec's shape

- `ecdsa_verify_steps` returns `Ok(())` or `Err(step)`, the numbered step
  that rejected, so that a deliberate bug in one check can be told from a bug
  elsewhere. `ecdsa_verify` is "accept".
- The group law is SEC 1 §2.2.1's affine rules in its order, with the point
  at infinity a distinct value. `[k]P` is MSB-first double-and-add. Division
  is Fermat with a checked result (`inv`); FIPS 186-5 Appendix B.1 is
  transcribed too (`b1_inverse`) and the examples evaluate both.
- **Cited, not proven:** associativity of the group law (so that double-and-add
  is the k-fold sum) and Fermat's little theorem for P-384's p and n (so that
  the `None` branch of `inv` is unreachable). The primality of p and n is
  SP 800-186's statement.
- The public key is always validated (SP 800-186 D.1.1.1). The `nQ = O` check
  is omitted because the cofactor is 1 (SEC 1 §3.2.2.1 says why that is
  sound).
- `toy()` is a 7-bit curve (p = 83, n = 67, h = 1, a = -3) used only for
  evaluated examples. No standard defines it and no executable code can reach
  it.

## What is evaluated

Known answers on the toy curve: a valid signature (with `x_R >= n`, so step
9's reduction matters, and a digest cut at a bit that is not an octet
boundary), rejections at steps 1, 6 and 9, and an invalid key (off the
curve, compressed, hybrid, a coordinate at least p, the point at infinity,
wrong lengths). On P-384: the constants' consequences (G is on the curve),
`2G` and `3G`, key decoding, and whole verifications whose scalars are small
by construction. A verification with full-size scalars (about 1,150 group
operations) is **not** evaluated: the interpreter of `by (compute_only)`
times out on it.

## Verification

Run `cargo verus focus -- -A missing_docs` in this directory. What it
proves today is that every spec function terminates (each recursive one has a
`decreases`), that the evaluated examples hold, that each field function
meets its contract in `field/contract.rs`, and that `ec_add`,
`scalar_mul`, `decode_public_key`, `derive_e` and `verify` meet theirs
(`point_contract.rs`, `contract.rs`), over the six axioms.
`mutations.json` holds 26 mutations of `spec.rs`, each killed with a
certificate that contradicts one of those examples; the executable code has
no mutations yet. There is no lemma about the spec of the signature itself,
no independent transcription, no mutation of the executable code and no
Kani harness yet, so the crate stays at tier 0 even though the conformance
suites and the differential pass; see
[docs/VERIFICATION.md](../../docs/VERIFICATION.md) for what each tier
requires. The proofs cover memory and arithmetic safety of the Verus-checked
code, but the claim is only as good as `spec.rs` (read against the standards
by a person) and the six axioms (fiat-crypto's printed postconditions).

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE).

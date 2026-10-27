# clazel-p384

ECDSA signature verification over NIST P-384 (FIPS 186-5 §6.4.2), specified
in Verus. Part of [Clazel](../../README.md), a web browser whose parsers of
untrusted input carry machine-checked proofs.

## Status: specification and field arithmetic

**Tier 0, target tier 2.** The specification and the field arithmetic are
written; the point arithmetic and `verify` are not. What exists:

- `src/spec.rs`: what "a valid ECDSA P-384 signature" means, transcribed
  step by step from FIPS 186-5 §6.4.2, with the routines it defers to taken
  from SP 800-186 (Appendices D.1.1.1 and F.1, and B.1 of FIPS 186-5) and
  SEC 1 v2 (§2.2.1 the group law, §2.3 conversions, §3.2.2.1, §4.1.4). The
  sources are pinned by SHA-256 in the file's header, which also lists every
  modelling choice (13 of them) and how the lossy text extraction of the
  PDFs was read.
- `src/contract.rs`: what the executable `verify(digest, r, s, point)` will
  be proven to satisfy, as predicates over the spec.
- `src/examples.rs`: known answers, proven by evaluating the spec
  (`by (compute_only)`), on a toy curve and on P-384.
- `src/axioms.rs`, `src/field/`: the field arithmetic, described below.
- `tests/field.rs`: known answers for the field, computed with Python.

Nothing here claims verification of `verify`, which does not exist yet. What
is evaluated is the spec itself, which shows the transcription computes what
was worked out independently, not that it matches the standards (a person
reads it against them; [docs/SPEC-STYLE.md](../../docs/SPEC-STYLE.md)).

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
`decreases`), that the evaluated examples hold, and that each field function
meets its contract in `field/contract.rs` over the six axioms. There is no
`mutations.json`, no lemma about the spec of the signature itself, no
independent transcription, no conformance test against an official suite and
no Kani harness yet, so the crate stays at tier 0; see
[docs/VERIFICATION.md](../../docs/VERIFICATION.md) for what each tier
requires. `verify` is not written, so nothing here proves anything about
ECDSA verification yet.

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE).

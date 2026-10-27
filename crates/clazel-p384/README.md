# clazel-p384

ECDSA signature verification over NIST P-384 (FIPS 186-5 §6.4.2), specified
in Verus. Part of [Clazel](../../README.md), a web browser whose parsers of
untrusted input carry machine-checked proofs.

## Status: specification only

**Tier 0, target tier 2.** Nothing is implemented. This crate has no
executable code: no field arithmetic, no point arithmetic and no `verify`
function. What exists is the part a person reviews:

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

Nothing here claims verification of any code. What is evaluated is the spec
itself, which shows the transcription computes what was worked out
independently, not that it matches the standards (a person reads it against
them; [docs/SPEC-STYLE.md](../../docs/SPEC-STYLE.md)).

## What it is, and what it is not

**Public-key verification only.** The key, the signature and the digest are
public, so nothing here has a constant-time requirement, and none is claimed.
No signing, no private key.

**The input is the digest**, 0 to 64 octets, not the message. Hashing is done
by `clazel-crypto`, so this crate has **no axiom**. The key is the full
97-octet ECPoint `04 || X || Y`; decoding and validation are inside the
verified code (uncompressed form only; the compressed form is refused).

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
`decreases`) and that the evaluated examples hold. There is no
`mutations.json`, no lemma about the spec, no independent transcription, no
conformance test and no Kani harness yet, so the crate stays at tier 0; see
[docs/VERIFICATION.md](../../docs/VERIFICATION.md) for what each tier
requires.

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE).

//! RSA PKCS#1 v1.5 signature verification, RFC 8017 §8.2.2, over our own
//! multiple-precision arithmetic.
//!
//! This is public-key *verification* only: the key, the signature and the
//! message digest are all public, so the code has no constant-time
//! requirement and makes no side-channel claim. It is our own code, not a
//! library's, because no formally verified library offers it (docs/phases/
//! phase-3.md, item 3.0). Signing and any private-key operation are out of
//! scope.
//!
//! - [`spec`]: a step-by-step transcription of RFC 8017 (§4.1 I2OSP, §4.2
//!   OS2IP, §5.2.2 RSAVP1, §8.2.2 RSASSA-PKCS1-v1_5-VERIFY, §9.2
//!   EMSA-PKCS1-v1_5-ENCODE).
//! - [`bignum`]: little-endian `u64` limbs with a `nat` spec, and the
//!   arithmetic the verification needs.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`independent`]: a second transcription, from RFC 2313 and the Handbook
//!   of Applied Cryptography, proven equal to [`spec`].
//! - [`lemmas`]: facts proven about the spec itself.
//! - [`verify`]: the executable `verify` and `encode_message`.
//! - `proofs` (under `cfg(kani)`): Kani harnesses on the limb arithmetic.

pub mod bignum;
pub mod certificates;
pub mod contract;
pub mod examples;
pub mod independent;
pub mod lemmas;
pub mod spec;
pub mod verify;

#[cfg(kani)]
mod proofs;

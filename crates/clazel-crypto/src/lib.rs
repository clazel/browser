//! The libcrux providers for `clazel-tls`'s cryptographic parameters
//! (docs/phases/phase-3.md item 3.5f).
//!
//! `clazel-tls` is proven over abstract providers: its key schedule, record
//! epochs and key exchange take the cryptography as trait parameters. This
//! crate instantiates them with libcrux and adds nothing else:
//!
//! - [`spec`]: the libcrux functions as uninterpreted specification
//!   functions.
//! - [`axioms`]: the trust boundary, one `external_body` wrapper per libcrux
//!   call, each an `// AXIOM:`.
//! - [`provider`]: the adapters, checked by Verus against `clazel-tls`'s
//!   provider contracts.
//! - [`compare`]: the timing-safe comparison for Finished values.
//! - [`signature`]: the CertificateVerify signature check (3.5b), whose key
//!   parsing is ours and whose three verifications are axioms.
//! - [`chain`]: certificate-chain link signatures, the production
//!   `clazel_x509::path` `LinkVerifier` (path-validation P11): RSA PKCS#1
//!   v1.5 by `clazel-pkcs1` over libcrux SHA-2, and ECDSA P-256 by libcrux.
//!
//! The suite is the profile's only one, `TLS_CHACHA20_POLY1305_SHA256` with
//! X25519 (phase-3.md 3.0, cost 2). Path validation itself is `clazel-x509`'s;
//! only its link signatures are here.

pub mod axioms;
pub mod chain;
pub mod compare;
pub mod provider;
pub mod signature;
pub mod spec;

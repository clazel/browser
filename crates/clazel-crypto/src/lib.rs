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
//!
//! The suite is the profile's only one, `TLS_CHACHA20_POLY1305_SHA256` with
//! X25519 (phase-3.md 3.0, cost 2). Signature verification and certificate
//! validation are separate (3.5b and 3.5c) and not here.

pub mod axioms;
pub mod spec;

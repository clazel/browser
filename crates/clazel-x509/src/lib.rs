//! RFC 5280 X.509 envelope, TBS, extension, time, public-key, and selected
//! constraint decoders, plus RFC 9525 DNS-ID/IP-ID matching and partial
//! server-leaf checks.
//!
//! `PartialLeafChecks` deliberately does not mean a certificate is valid.
//! Signature verification, TBS/outer signature-algorithm agreement, path
//! building and validation, trust, revocation, name constraints, and remaining
//! policy checks still require a later verifier. DNS references are supplied
//! as canonical ASCII from the URL layer. Common Name fallback is not used.

pub mod certificate;
pub mod certificates;
pub mod constraints;
pub mod contract;
pub mod exec;
pub mod extensions;
pub mod leaf;
pub mod lemmas;
pub mod matcher;
pub mod name;
pub mod name_constraints;
pub mod roots;
pub mod signature_algorithm;
pub mod spec;
pub mod spki;
pub mod tbs;
pub mod time;

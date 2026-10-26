//! RFC 5280 certificate extension container and subjectAltName extraction.
//!
//! The decoder exposes syntax and raw extension values; it does not establish
//! that extension semantics were processed or that a certificate is trusted.

pub mod contract;
pub mod exec;
pub mod lemmas;
pub mod mutation_certificates;
pub mod spec;

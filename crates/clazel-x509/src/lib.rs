//! Service identity matching for the DNS-ID and IP-ID forms in RFC 9525.
//!
//! This crate does not decode certificates or validate paths. The caller
//! supplies already-extracted subjectAltName values and a canonical
//! reference identifier from the URL layer.

pub mod certificate;
pub mod certificates;
pub mod constraints;
pub mod contract;
pub mod exec;
pub mod extensions;
pub mod leaf;
pub mod lemmas;
pub mod matcher;
pub mod spec;
pub mod spki;
pub mod signature_algorithm;
pub mod tbs;
pub mod time;

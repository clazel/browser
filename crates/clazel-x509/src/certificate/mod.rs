//! RFC 5280 §4.1 Certificate envelope parsing.
//!
//! The envelope retains the exact DER encoding of TBSCertificate. It does
//! not validate the TBS fields, algorithm-specific parameters, signatures,
//! certificate paths, or trust.

pub mod contract;
pub mod spec;

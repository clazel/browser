//! RFC 5280 X.509 Name and RelativeDistinguishedName DER structure.
//!
//! This module retains encoded names and attribute values. It does not apply
//! RFC 5280 §7.1 name comparison/string preparation, build paths, or validate
//! certificate policy.

pub mod contract;
pub mod spec;

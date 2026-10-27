//! Field arithmetic modulo p (coordinates) and modulo n (scalars) for NIST
//! P-384, over fiat-crypto's generated Montgomery code.
//!
//! - [`spec`]: what a field element is: six little-endian `u64` limbs in the
//!   Montgomery domain, and the number they stand for. This is the part to
//!   review against fiat-crypto's printed pre- and postconditions.
//! - [`contract`]: what each executable field function is proven to satisfy,
//!   as predicates over residues and octet strings (the vocabulary of
//!   [`crate::spec`]).

pub mod contract;
pub mod spec;

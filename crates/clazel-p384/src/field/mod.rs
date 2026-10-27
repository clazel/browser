//! Field arithmetic modulo p (coordinates) and modulo n (scalars) for NIST
//! P-384, over fiat-crypto's generated Montgomery code.
//!
//! - [`spec`]: what a field element is: six little-endian `u64` limbs in the
//!   Montgomery domain, and the number they stand for. This is the part to
//!   review against fiat-crypto's printed pre- and postconditions.
//! - [`contract`]: what each executable field function is proven to satisfy,
//!   as predicates over residues and octet strings (the vocabulary of
//!   [`crate::spec`]).
//! - [`fe`]: the executable field element [`Fe`] and its operations, proven
//!   against the contracts over the six axioms of [`crate::axioms`].
//! - [`lemmas`]: the facts those proofs use (about the spec's constants,
//!   limb sequences, octet strings and modular arithmetic).

pub mod contract;
pub mod fe;
pub mod lemmas;
pub mod spec;

pub use fe::Fe;
pub use spec::Which;

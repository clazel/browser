//! Multiple-precision arithmetic over little-endian `u64` limbs.
//!
//! - [`spec`]: `value`, the `nat` a limb sequence denotes.
//! - [`contract`]: what the arithmetic is proven to satisfy.
//! - [`independent`]: Algorithm 14.12 of the Handbook of Applied Cryptography.
//! - [`lemmas`]: facts about `value` the invariants use.
//! - [`limb`]: add and subtract one limb with carry.
//! - [`arith`]: add, subtract and compare whole numbers.
//! - [`convert`]: octet strings to limbs.
//! - [`modular`]: modular add, multiply and exponentiate.

pub mod arith;
pub mod contract;
pub mod convert;
pub mod independent;
pub mod lemmas;
pub mod limb;
pub mod modular;
pub mod spec;

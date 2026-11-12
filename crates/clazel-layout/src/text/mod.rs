//! White space and line breaking (phase-5.md item 5.12).

pub mod classes;
pub mod data;
pub mod uax14;

pub use classes::{Lb, Props};
pub use uax14::{Break, Rule, breaks, breaks_with_rules};

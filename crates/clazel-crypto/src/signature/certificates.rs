//! The module that hosts the kill certificates of `mutations.json`
//! (xtask/src/mutate.rs adds one proof function here per certified
//! mutation, at run time, to a copy of the crate). It is empty on purpose:
//! a certificate is run alone in this module, and the evaluated examples in
//! [`super::examples`] (which a mutated spec makes fail) must not be in the
//! module being verified.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {} // verus!

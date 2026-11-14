//! A module with nothing in it, on purpose. `cargo xtask mutate` adds one
//! function to the module it is told to for each `killed` mutation of
//! `driver_spec` (the certificate of `mutations.json`), and verifies that
//! module alone. The certificates cannot go in `driver_examples`, whose own
//! proofs are evaluations that fail on a mutant, and a failed evaluation stops
//! Verus before it reaches the certificate.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {} // verus!

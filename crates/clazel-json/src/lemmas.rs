//! Facts proven about the spec itself. They are evidence that the
//! transcription is right, not part of what the implementation must meet.
//!
//! Kill certificates in `mutations.json` are added to this file: the
//! examples in [`super::examples`] are evaluated with `compute_only`, which
//! Verus runs on a whole module at once, so a mutant that breaks an example
//! would stop it before it reached a certificate in the same module.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {} // verus!

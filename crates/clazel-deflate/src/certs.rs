//! Where the kill certificates of `mutations.json` for the lemmas that
//! evaluate the spec (`examples.rs`, `lemmas_usable.rs`) are added. A
//! certificate is verified together with its whole module, and in a mutant
//! those lemmas' own bodies fail (that is the kill), so the certificate lives
//! in a module of its own that calls them by path and checks only its
//! witness.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Verus lists only modules that hold something to verify, and the mutation
/// tool names this one with `module`, so it holds this.
pub proof fn lemma_certs_module_is_not_empty()
    ensures
        true,
{
}

} // verus!

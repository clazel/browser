//! Concrete instances of the host-acyclicity theorems, the kill certificates
//! of the mutations of [`pre_insert_error`] and [`host_including_within`] in
//! `mutations.json` (`xtask/src/mutate.rs`). Each lemma states a fact about
//! a concrete arena that a proven theorem implies for the real spec, and
//! that a mutant makes false (the certificate's witness).
//!
//! The arena is [`ds_tmpl`]: a document (0), a template element (1) and its
//! contents, the fragment (2) whose host is 1. Inserting the template into its
//! own contents is not refused by an inclusive-ancestor check (the fragment
//! has no parent), only by the host-including one, and would make a cycle
//! through the host.

#[cfg(verus_only)]
use super::contract::*;
#[cfg(verus_only)]
use super::deep_clone_size_lemmas::*;
#[cfg(verus_only)]
use super::deep_clone_size_mutation_lemmas::*;
#[cfg(verus_only)]
use super::host_acyclic_lemmas::*;
#[cfg(verus_only)]
use super::ops_lemmas::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Ensure pre-insertion validity" refuses to insert the template into its
/// own contents: were it allowed, the arena after it would be
/// host-acyclic (`theorem_pre_insert_host_acyclic`), but the template
/// would be a child of its contents, which are its contents.
pub proof fn ml_host_cycle_refused()
    ensures
        !(pre_insert_error(ds_tmpl(), 1, 2, None) is None),
{
    ds_tmpl_facts();
    if pre_insert_error(ds_tmpl(), 1, 2, None) is None {
        assert(valid(ds_tmpl(), 1));
        assert(valid(ds_tmpl(), 2));
        assert(pre_insert_requires(ds_tmpl(), 1, 2, None));
        theorem_pre_insert_host_acyclic(ds_tmpl(), 1, 2, None);
        theorem_pre_insert_wf(ds_tmpl(), 1, 2, None);
        let d2 = pre_insert(ds_tmpl(), 1, 2, None);
        assert(!(ds_tmpl().nodes[1].kind is DocumentFragment)) by (compute_only);
        assert(ds_tmpl().nodes[2].kind == (NodeKind::DocumentFragment { host: Some(1usize) })) by (compute_only);
        assert(d2.nodes[1].parent == Some(2usize));
        assert(d2.nodes[2].kind == ds_tmpl().nodes[2].kind);
        let rank = lemma_rank_witness(d2);
        assert(ranked_at(d2, rank, 1));
        assert(ranked_at(d2, rank, 2));
        theorem_ranked_at_facts(d2, rank, 1);
        theorem_ranked_at_facts(d2, rank, 2);
        assert(false);
    }
}

} // verus!

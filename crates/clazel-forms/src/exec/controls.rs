//! The controls of a form: the form owner of each submittable element of
//! the form's tree, in tree order.

use super::read::*;
use super::strings::*;
use super::tree::*;
use super::walk::*;
#[cfg(verus_only)]
use crate::contract::*;
#[cfg(verus_only)]
use crate::lemmas::*;
#[cfg(verus_only)]
use clazel_dom::lemmas::lemma_wf_witness;
use crate::spec::*;
use clazel_dom::exec::{Arena, ExecKind};
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The first element of `order` whose ID is `id`: [`first_with_id`].
pub fn first_with_id_exec(arena: &Arena, order: &[usize], id: &[u32]) -> (r: Option<usize>)
    requires
        forall|k: int| 0 <= k < order@.len() ==> dom::valid(arena@, #[trigger] order@[k]),
    ensures
        r == first_with_id(arena@, order@, id@),
{
    let mut i: usize = 0;
    proof {
        assert(order@.skip(0) =~= order@);
    }
    while i < order.len()
        invariant
            i <= order.len(),
            forall|k: int| 0 <= k < order@.len() ==> dom::valid(arena@, #[trigger] order@[k]),
            first_with_id(arena@, order@, id@) == first_with_id(arena@, order@.skip(i as int), id@),
        decreases order.len() - i,
    {
        if let Some(e) = order.get(i) {
            let e = *e;
            proof {
                assert(order@.skip(i as int).drop_first() =~= order@.skip(i as int + 1));
                assert(order@.skip(i as int)[0] == order@[i as int]);
            }
            if is_element_exec(arena, e) {
                if let Some(v) = element_id_exec(arena, e) {
                    if eq_slices(v.as_slice(), id) {
                        return Some(e);
                    }
                }
            }
        }
        // Never saturates: i < order.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(order@.skip(order.len() as int) =~= Seq::<usize>::empty());
    }
    None
}

/// Whether `e`, a submittable element of the tree of `form`, has `form` as
/// its form owner: [`form_owner`] equals `Some(form)`. `connected` and
/// `fid` are computed once per form (see [`fid_value`]).
pub fn owner_is_exec(
    arena: &Arena,
    form: usize,
    e: usize,
    connected: bool,
    fid: Option<&Vec<u32>>,
    Ghost(order): Ghost<Seq<NodeId>>,
) -> (r: bool)
    requires
        dom::wf(arena@),
        dom::valid(arena@, form),
        dom::valid(arena@, e),
        is_submittable(arena@, e),
        root(arena@, e) == root(arena@, form),
        connected == dom::connected(arena@, e),
        order == tree_order(arena@, root(arena@, form), arena@.nodes.len()),
        ref_view(fid) == fid_value(arena@, order, form),
    ensures
        r == (form_owner(arena@, e) == Some(form)),
{
    proof {
        assert(is_element(arena@, e));
        assert(is_listed(arena@, e));
    }
    let owner = match arena.kind(e) {
        ExecKind::Element { form_owner, .. } => *form_owner,
        _ => None,
    };
    match owner {
        Some(f) => f == form,
        None => {
            let named = attr_exec(arena, e, b"form");
            match named {
                Some(a) => {
                    if connected {
                        proof {
                            lemma_fid(arena@, order, form, a@);
                        }
                        match fid {
                            Some(v) => eq_slices(a.as_slice(), v.as_slice()),
                            None => false,
                        }
                    } else {
                        nearest_form_exec(arena, e) == Some(form)
                    }
                },
                None => nearest_form_exec(arena, e) == Some(form),
            }
        },
    }
}

/// [`controls`]: the submittable elements whose form owner is `form`, in
/// tree order.
pub fn controls_exec(arena: &Arena, form: usize) -> (r: Vec<usize>)
    requires
        controls_requires(arena@, form),
    ensures
        controls_ensures(arena@, form, r@),
{
    let r0 = root_exec(arena, form);
    proof {
        let paths = lemma_wf_witness(arena@);
        lemma_root_facts(arena@, paths, form);
    }
    let order = tree_order_exec(arena, r0);
    proof {
        assert forall|k: int| 0 <= k < order@.len() implies dom::valid(arena@, #[trigger] order@[k]) by {
            lemma_in_order(arena@, form, order@[k]);
        }
    }
    let connected_root = r0 == 0;
    let mut fid: Option<&Vec<u32>> = None;
    if is_html_exec(arena, form, b"form") {
        proof {
            assert(is_element(arena@, form));
        }
        if let Some(v) = element_id_exec(arena, form) {
            if let Some(x) = first_with_id_exec(arena, order.as_slice(), v.as_slice()) {
                if x == form {
                    fid = Some(v);
                }
            }
        }
    }
    let ghost ord = order@;
    let mut out: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(ord.subrange(0, 0) =~= Seq::<usize>::empty());
    }
    while i < order.len()
        invariant
            i <= order.len(),
            dom::wf(arena@),
            dom::valid(arena@, form),
            order@ == ord,
            r0 == root(arena@, form),
            ord == tree_order(arena@, root(arena@, form), arena@.nodes.len()),
            connected_root == (r0 == 0),
            ref_view(fid) == fid_value(arena@, ord, form),
            forall|k: int| 0 <= k < ord.len() ==> dom::valid(arena@, #[trigger] ord[k]),
            out@ == controls_in(arena@, form, ord.subrange(0, i as int)),
        decreases order.len() - i,
    {
        if let Some(e) = order.get(i) {
            let e = *e;
            proof {
                lemma_in_order(arena@, form, e);
                assert(ord.subrange(0, i as int + 1).drop_last() =~= ord.subrange(0, i as int));
                assert(ord.subrange(0, i as int + 1).last() == ord[i as int]);
            }
            let ghost before = out@;
            if is_submittable_exec(arena, e) {
                if owner_is_exec(arena, form, e, connected_root, fid, Ghost(ord)) {
                    out.push(e);
                    proof {
                        assert(out@ =~= before.push(e));
                    }
                }
            }
        }
        // Never saturates: i < order.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(ord.subrange(0, ord.len() as int) =~= ord);
    }
    out
}

} // verus!

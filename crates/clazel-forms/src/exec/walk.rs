//! Walks up the ancestors of a node of a well-formed arena, each with the
//! fuel of its spec function (the arena's size), and the first `legend`
//! child of a node.

use super::read::*;
#[cfg(verus_only)]
use crate::contract::*;
#[cfg(verus_only)]
use crate::spec::*;
use clazel_dom::exec::Arena;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`root`].
pub fn root_exec(arena: &Arena, x: usize) -> (r: usize)
    requires
        root_requires(arena@, x),
    ensures
        root_ensures(arena@, x, r),
{
    let fuel = arena.len();
    let mut cur = x;
    let mut steps: usize = 0;
    while steps <= fuel
        invariant
            steps <= fuel,
            fuel == arena@.nodes.len(),
            dom::wf(arena@),
            dom::valid(arena@, cur),
            root_within(arena@, x, fuel as nat) == root_within(arena@, cur, (fuel - steps) as nat),
        decreases fuel - steps,
    {
        match arena.parent(cur) {
            None => {
                return cur;
            },
            Some(p) => {
                if steps == fuel {
                    return cur;
                }
                proof {
                    lemma_parent_valid(arena@, cur);
                }
                cur = p;
            },
        }
        // Never saturates: steps < fuel.
        steps = steps.saturating_add(1);
    }
    x
}

/// [`nearest_form_ancestor`].
pub fn nearest_form_exec(arena: &Arena, x: usize) -> (r: Option<usize>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, x),
    ensures
        r == nearest_form_ancestor(arena@, x),
{
    let fuel = arena.len();
    let mut cur = x;
    let mut steps: usize = 0;
    while steps <= fuel
        invariant
            steps <= fuel,
            fuel == arena@.nodes.len(),
            dom::wf(arena@),
            dom::valid(arena@, cur),
            nearest_form_within(arena@, x, fuel as nat) == nearest_form_within(arena@, cur, (fuel - steps) as nat),
        decreases fuel - steps,
    {
        match arena.parent(cur) {
            None => {
                return None;
            },
            Some(p) => {
                proof {
                    lemma_parent_valid(arena@, cur);
                }
                if is_html_exec(arena, p, b"form") {
                    return Some(p);
                }
                if steps == fuel {
                    return None;
                }
                cur = p;
            },
        }
        // Never saturates: steps < fuel.
        steps = steps.saturating_add(1);
    }
    None
}

/// [`has_datalist_ancestor`].
pub fn datalist_exec(arena: &Arena, x: usize) -> (r: bool)
    requires
        dom::wf(arena@),
        dom::valid(arena@, x),
    ensures
        r == has_datalist_ancestor(arena@, x),
{
    let fuel = arena.len();
    let mut cur = x;
    let mut steps: usize = 0;
    while steps <= fuel
        invariant
            steps <= fuel,
            fuel == arena@.nodes.len(),
            dom::wf(arena@),
            dom::valid(arena@, cur),
            datalist_within(arena@, x, fuel as nat) == datalist_within(arena@, cur, (fuel - steps) as nat),
        decreases fuel - steps,
    {
        match arena.parent(cur) {
            None => {
                return false;
            },
            Some(p) => {
                proof {
                    lemma_parent_valid(arena@, cur);
                }
                if is_html_exec(arena, p, b"datalist") {
                    return true;
                }
                if steps == fuel {
                    return false;
                }
                cur = p;
            },
        }
        // Never saturates: steps < fuel.
        steps = steps.saturating_add(1);
    }
    false
}

/// [`first_legend_child`].
pub fn first_legend_exec(arena: &Arena, f: usize) -> (r: Option<usize>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, f),
    ensures
        r == first_legend_child(arena@, f),
{
    let kids = arena.children(f);
    let ghost doc = arena@;
    let mut i: usize = 0;
    proof {
        assert(kids@.skip(0) =~= kids@);
    }
    while i < kids.len()
        invariant
            i <= kids.len(),
            kids@ == doc.nodes[f as int].children,
            doc == arena@,
            dom::wf(doc),
            dom::valid(doc, f),
            first_legend_in(doc, kids@) == first_legend_in(doc, kids@.skip(i as int)),
        decreases kids.len() - i,
    {
        if let Some(c) = kids.get(i) {
            let c = *c;
            proof {
                lemma_child_valid(doc, f, i as int);
                assert(kids@.skip(i as int).drop_first() =~= kids@.skip(i as int + 1));
                assert(kids@.skip(i as int)[0] == kids@[i as int]);
            }
            if is_html_exec(arena, c, b"legend") {
                return Some(c);
            }
        }
        // Never saturates: i < kids.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(kids@.skip(kids.len() as int) =~= Seq::<usize>::empty());
    }
    None
}

/// The first `legend` child of `p` is not `child`, a child of `p`.
fn not_first_legend(arena: &Arena, p: usize, child: usize) -> (r: bool)
    requires
        dom::wf(arena@),
        dom::valid(arena@, p),
    ensures
        r == (first_legend_child(arena@, p) != Some(child)),
{
    match first_legend_exec(arena, p) {
        Some(l) => l != child,
        None => true,
    }
}

/// The second bullet of [`is_disabled`]: [`fieldset_disables`] from `x`
/// with the arena's size as fuel.
pub fn fieldset_disables_exec(arena: &Arena, x: usize) -> (r: bool)
    requires
        dom::wf(arena@),
        dom::valid(arena@, x),
    ensures
        r == fieldset_disables(arena@, x, arena@.nodes.len()),
{
    let fuel = arena.len();
    let mut cur = x;
    let mut steps: usize = 0;
    while steps <= fuel
        invariant
            steps <= fuel,
            fuel == arena@.nodes.len(),
            dom::wf(arena@),
            dom::valid(arena@, cur),
            fieldset_disables(arena@, x, fuel as nat) == fieldset_disables(arena@, cur, (fuel - steps) as nat),
        decreases fuel - steps,
    {
        match arena.parent(cur) {
            None => {
                return false;
            },
            Some(p) => {
                proof {
                    lemma_parent_valid(arena@, cur);
                }
                if is_html_exec(arena, p, b"fieldset") && has_attr_exec(arena, p, b"disabled") && not_first_legend(
                    arena,
                    p,
                    cur,
                ) {
                    return true;
                }
                if steps == fuel {
                    return false;
                }
                cur = p;
            },
        }
        // Never saturates: steps < fuel.
        steps = steps.saturating_add(1);
    }
    false
}

/// [`option_ancestors_disable`] from `x` with the arena's size as fuel.
pub fn option_ancestors_exec(arena: &Arena, x: usize) -> (r: bool)
    requires
        dom::wf(arena@),
        dom::valid(arena@, x),
    ensures
        r == option_ancestors_disable(arena@, x, arena@.nodes.len()),
{
    let fuel = arena.len();
    let mut cur = x;
    let mut steps: usize = 0;
    while steps <= fuel
        invariant
            steps <= fuel,
            fuel == arena@.nodes.len(),
            dom::wf(arena@),
            dom::valid(arena@, cur),
            option_ancestors_disable(arena@, x, fuel as nat) == option_ancestors_disable(
                arena@,
                cur,
                (fuel - steps) as nat,
            ),
        decreases fuel - steps,
    {
        match arena.parent(cur) {
            None => {
                return false;
            },
            Some(p) => {
                proof {
                    lemma_parent_valid(arena@, cur);
                }
                if is_html_exec(arena, p, b"select") || is_html_exec(arena, p, b"hr") || is_html_exec(arena, p, b"datalist")
                    || is_html_exec(arena, p, b"option") {
                    return false;
                }
                if is_html_exec(arena, p, b"optgroup") {
                    return has_attr_exec(arena, p, b"disabled");
                }
                if steps == fuel {
                    return false;
                }
                cur = p;
            },
        }
        // Never saturates: steps < fuel.
        steps = steps.saturating_add(1);
    }
    false
}

} // verus!

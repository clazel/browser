//! §21.3 "match a selector against an element", proven to meet
//! [`super::contract::match_ensures`]: each complex selector runs the algorithm of
//! [`super::algorithm`], which `lemmas::theorem_match_total` proves gives the spec's answer.

#[allow(unused_imports)]
use super::algorithm::*;
#[allow(unused_imports)]
use super::contract::*;
use super::exec_element::*;
use super::exec_types::*;
#[allow(unused_imports)]
use super::spec::*;
use clazel_dom::exec::{Arena, ExecKind};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------------------------
// Well-formedness reaches the parts
// ------------------------------------------------------------------------------------

/// Each of the first `k` complex selectors of a well-formed list is well-formed.
pub proof fn lemma_list_wf_at(list: Seq<Complex>, k: int, i: int)
    requires
        list_wf(list, k),
        0 <= i < k <= list.len(),
    ensures
        complex_wf(list[i]),
    decreases k,
{
    if i < k - 1 {
        lemma_list_wf_at(list, k - 1, i);
    }
}

/// Each compound selector of a well-formed complex selector is well-formed and not empty.
pub proof fn lemma_compounds_wf_at(c: Complex, n: int, i: int)
    requires
        compounds_wf(c, n),
        0 <= i < n <= c.compounds.len(),
    ensures
        c.compounds[i].len() > 0,
        compound_wf(c.compounds[i], c.compounds[i].len() as int),
    decreases n,
{
    if i < n - 1 {
        lemma_compounds_wf_at(c, n - 1, i);
    }
}

/// Each simple selector of a well-formed compound selector is well-formed.
pub proof fn lemma_compound_wf_at(compound: Seq<Simple>, k: int, i: int)
    requires
        compound_wf(compound, k),
        0 <= i < k <= compound.len(),
    ensures
        simple_wf(compound[i]),
    decreases k,
{
    if i < k - 1 {
        lemma_compound_wf_at(compound, k - 1, i);
    }
}

/// A compound selector stops matching at the first simple selector that does not.
proof fn lemma_compound_stops(doc: Document, compound: Seq<Simple>, k: int, m: int, x: NodeId)
    requires
        0 <= k < m <= compound.len(),
        !compound_matches(doc, compound, k + 1, x),
    ensures
        !compound_matches(doc, compound, m, x),
    decreases m - k,
{
    if m > k + 1 {
        lemma_compound_stops(doc, compound, k, m - 1, x);
    }
}

/// A list matches once one of its selectors does.
proof fn lemma_list_keeps(doc: Document, list: Seq<Complex>, k: int, m: int, x: NodeId)
    requires
        0 < k <= m <= list.len(),
        match_list(doc, list, k, x),
    ensures
        match_list(doc, list, m, x),
    decreases m - k,
{
    if m > k {
        lemma_list_keeps(doc, list, k, m - 1, x);
    }
}

// ------------------------------------------------------------------------------------
// Rows of truth values
// ------------------------------------------------------------------------------------

/// [`falses`].
fn exec_falses(n: usize) -> (r: Vec<bool>)
    ensures
        r@ == falses(n as nat),
{
    let mut out: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> !(#[trigger] out@[j]),
        decreases n - i,
    {
        out.push(false);
        i = i.saturating_add(1);
    }
    proof {
        assert(out@ =~= falses(n as nat));
    }
    out
}

/// [`or_rows`].
fn exec_or(a: &[bool], b: &[bool]) -> (r: Vec<bool>)
    requires
        a@.len() == b@.len(),
    ensures
        r@ == or_rows(a@, b@),
{
    let mut out: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a@.len() == b@.len(),
            out@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] out@[j]) == (a@[j] || b@[j]),
        decreases a.len() - i,
    {
        out.push(*item(a, i) || *item(b, i));
        i = i.saturating_add(1);
    }
    proof {
        assert(out@ =~= or_rows(a@, b@));
    }
    out
}

/// [`related`].
fn exec_related(
    combinator: Combinator,
    i: usize,
    parent: &[bool],
    descendant: &[bool],
    previous: &[bool],
    earlier: &[bool],
) -> (r: bool)
    requires
        i < parent@.len(),
        i < descendant@.len(),
        i < previous@.len(),
        i < earlier@.len(),
    ensures
        r == related(combinator, i as int, parent@, descendant@, previous@, earlier@),
{
    match combinator {
        Combinator::Descendant => *item(descendant, i),
        Combinator::Child => *item(parent, i),
        Combinator::NextSibling => *item(previous, i),
        Combinator::SubsequentSibling => *item(earlier, i),
    }
}

// ------------------------------------------------------------------------------------
// Simple and compound selectors
// ------------------------------------------------------------------------------------

/// What every matching function needs of its arguments.
pub open spec fn match_args(arena: Document, s: ExecSelectors, bound: int) -> bool {
    &&& clazel_dom::spec::wf(arena)
    &&& ranges_wf(s)
    &&& 0 <= bound <= s.lists.len()
}

/// True if the simple selector at `si` of the list `bound` matches `x`.
fn simple_matches_exec(arena: &Arena, s: &ExecSelectors, bound: usize, si: usize, x: usize) -> (r: bool)
    requires
        match_args(arena@, *s, bound as int),
        si < s.simples.len(),
        simple_wf(view_simple(*s, bound as int, si as int)),
    ensures
        r == simple_matches(arena@, view_simple(*s, bound as int, si as int), x),
    decreases bound, 0int, 0int,
{
    if !element(arena, x) {
        return false;
    }
    let ghost doc = arena@;
    let (namespace, local_name, attributes) = match arena.kind(x) {
        ExecKind::Element { namespace, local_name, attributes, .. } => (namespace, local_name, attributes),
        _ => {
            return false;
        },
    };
    let html = is_html(namespace);
    proof {
        assert(attributes_of(doc, x) == clazel_dom::exec::attrs_view(attributes@));
        assert(local_name_of(doc, x) == local_name@);
        assert(namespace_of(doc, x) == *namespace);
    }
    match item(s.simples.as_slice(), si) {
        ExecSimple::Type { ns, name } => {
            let ns_ok = match ns {
                NsPrefix::NoNamespace => namespace.is_none(),
                _ => true,
            };
            let name_ok = if html {
                super::exec_strings::lowered_is(name.as_slice(), local_name.as_slice())
            } else {
                super::exec_strings::same(name.as_slice(), local_name.as_slice())
            };
            ns_ok && name_ok
        },
        ExecSimple::Universal { ns } => match ns {
            NsPrefix::NoNamespace => namespace.is_none(),
            _ => true,
        },
        ExecSimple::Id { name } => id_matches(
            attributes,
            name.as_slice(),
            quirks(arena),
            Ghost(doc),
            Ghost(x),
        ),
        ExecSimple::Class { name } => class_matches(
            attributes,
            name.as_slice(),
            quirks(arena),
            Ghost(doc),
            Ghost(x),
        ),
        ExecSimple::Attribute { ns, name, test } => attribute_matches(
            attributes,
            *ns,
            name.as_slice(),
            test,
            html,
            Ghost(doc),
            Ghost(x),
        ),
        ExecSimple::PseudoClass { class } => match class {
            PseudoClass::Link => hyperlink(arena, x),
            PseudoClass::Visited => false,
            PseudoClass::AnyLink => hyperlink(arena, x),
            PseudoClass::Root => root(arena, x),
            PseudoClass::Empty => empty(arena, x),
            PseudoClass::FirstChild => index_among_siblings(arena, x, false, false) == 1,
            PseudoClass::LastChild => index_among_siblings(arena, x, false, true) == 1,
            PseudoClass::OnlyChild => index_among_siblings(arena, x, false, false) == 1
                && index_among_siblings(arena, x, false, true) == 1,
            PseudoClass::FirstOfType => index_among_siblings(arena, x, true, false) == 1,
            PseudoClass::LastOfType => index_among_siblings(arena, x, true, true) == 1,
            PseudoClass::OnlyOfType => index_among_siblings(arena, x, true, false) == 1
                && index_among_siblings(arena, x, true, true) == 1,
            PseudoClass::Hover => false,
            PseudoClass::Active => false,
            PseudoClass::Focus => false,
            PseudoClass::FocusVisible => false,
            PseudoClass::FocusWithin => false,
        },
        ExecSimple::Nth { kind, a, b } => {
            let i = match kind {
                NthKind::Child => index_among_siblings(arena, x, false, false),
                NthKind::LastChild => index_among_siblings(arena, x, false, true),
                NthKind::OfType => index_among_siblings(arena, x, true, false),
                NthKind::LastOfType => index_among_siblings(arena, x, true, true),
            };
            nth(*a, *b, i)
        },
        ExecSimple::Is { list } => if *list < bound {
            list_matches_exec(arena, s, *list, x)
        } else {
            false
        },
        ExecSimple::Where { list } => if *list < bound {
            list_matches_exec(arena, s, *list, x)
        } else {
            false
        },
        ExecSimple::Not { list } => if *list < bound {
            !list_matches_exec(arena, s, *list, x)
        } else {
            true
        },
        ExecSimple::PseudoElement { .. } => false,
    }
}

/// True if the compound selector at `ci` of the list `bound` matches `x`.
fn compound_matches_exec(arena: &Arena, s: &ExecSelectors, bound: usize, ci: usize, x: usize) -> (r: bool)
    requires
        match_args(arena@, *s, bound as int),
        ci < s.compounds.len(),
        compound_wf(
            view_compound(*s, bound as int, ci as int),
            view_compound(*s, bound as int, ci as int).len() as int,
        ),
    ensures
        r == compound_matches(
            arena@,
            view_compound(*s, bound as int, ci as int),
            view_compound(*s, bound as int, ci as int).len() as int,
            x,
        ),
    decreases bound, 1int, 0int,
{
    let ghost v = view_compound(*s, bound as int, ci as int);
    proof {
        lemma_view_compound(*s, bound as int, ci as int);
    }
    let lo = item(s.compounds.as_slice(), ci).lo;
    let hi = item(s.compounds.as_slice(), ci).hi;
    let mut k = lo;
    while k < hi
        invariant
            match_args(arena@, *s, bound as int),
            lo <= k <= hi <= s.simples.len(),
            v == view_compound(*s, bound as int, ci as int),
            v.len() == hi - lo,
            compound_wf(v, v.len() as int),
            forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == view_simple(*s, bound as int, lo + j),
            compound_matches(arena@, v, k - lo, x),
        decreases hi - k,
    {
        proof {
            lemma_compound_wf_at(v, v.len() as int, k - lo);
            assert(v[k - lo] == view_simple(*s, bound as int, k as int));
        }
        if !simple_matches_exec(arena, s, bound, k, x) {
            proof {
                lemma_compound_stops(arena@, v, k - lo, v.len() as int, x);
            }
            return false;
        }
        k = k.saturating_add(1);
    }
    true
}

/// [`row`] for the complex selector at `ci` of the list `bound`, at `x`.
fn row_exec(
    arena: &Arena,
    s: &ExecSelectors,
    bound: usize,
    ci: usize,
    x: usize,
    inputs: (&[bool], &[bool], &[bool], &[bool]),
) -> (r: Vec<bool>)
    requires
        match_args(arena@, *s, bound as int),
        ci < s.complexes.len(),
        complex_wf(view_complex(*s, bound as int, ci as int)),
        inputs.0@.len() == view_complex(*s, bound as int, ci as int).compounds.len(),
        inputs.1@.len() == inputs.0@.len(),
        inputs.2@.len() == inputs.0@.len(),
        inputs.3@.len() == inputs.0@.len(),
    ensures
        r@ == row(
            arena@,
            view_complex(*s, bound as int, ci as int),
            x,
            inputs.0@,
            inputs.1@,
            inputs.2@,
            inputs.3@,
        ),
        r@.len() == inputs.0@.len(),
    decreases bound, 2int, 0int,
{
    let (parent, descendant, previous, earlier) = inputs;
    let ghost c = view_complex(*s, bound as int, ci as int);
    proof {
        lemma_view_complex(*s, bound as int, ci as int);
    }
    let cx = *item(s.complexes.as_slice(), ci);
    let n = cx.compounds.hi.saturating_sub(cx.compounds.lo);
    let is_el = element(arena, x);
    let mut out: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            match_args(arena@, *s, bound as int),
            ci < s.complexes.len(),
            cx == s.complexes@[ci as int],
            c == view_complex(*s, bound as int, ci as int),
            complex_wf(c),
            n == c.compounds.len(),
            c.combinators.len() + 1 == n,
            parent@.len() == n,
            descendant@.len() == n,
            previous@.len() == n,
            earlier@.len() == n,
            is_el == is_element(arena@, x),
            forall|k: int| 0 <= k < n ==> #[trigger] c.compounds[k] == view_compound(*s, bound as int, cx.compounds.lo + k),
            forall|k: int| 0 <= k < c.combinators.len() ==> #[trigger] c.combinators[k] == s.combinators@[cx.combinators.lo + k],
            cx.compounds.lo + n <= s.compounds.len(),
            cx.combinators.lo + (n - 1) <= s.combinators.len(),
            i <= n,
            out@.len() == i,
            forall|k: int|
                0 <= k < i ==> #[trigger] out@[k] == (is_element(arena@, x) && compound_matches(
                    arena@,
                    c.compounds[k],
                    c.compounds[k].len() as int,
                    x,
                ) && (k == 0 || related(c.combinators[k - 1], k - 1, parent@, descendant@, previous@, earlier@))),
        decreases n - i,
    {
        let cell = if !is_el {
            false
        } else {
            proof {
                lemma_compounds_wf_at(c, n as int, i as int);
            }
            let here = compound_matches_exec(arena, s, bound, cx.compounds.lo.saturating_add(i), x);
            here && (i == 0 || exec_related(
                *item(s.combinators.as_slice(), cx.combinators.lo.saturating_add(i).saturating_sub(1)),
                i.saturating_sub(1),
                parent,
                descendant,
                previous,
                earlier,
            ))
        };
        out.push(cell);
        i = i.saturating_add(1);
    }
    proof {
        assert(out@ =~= row(arena@, c, x, parent@, descendant@, previous@, earlier@));
    }
    out
}

// ------------------------------------------------------------------------------------
// The walk
// ------------------------------------------------------------------------------------

/// [`uses_siblings`] for the complex selector at `ci`.
fn has_sibling_combinator(s: &ExecSelectors, Ghost(bound): Ghost<int>, ci: usize) -> (r: bool)
    requires
        ranges_wf(*s),
        ci < s.complexes.len(),
    ensures
        r == uses_siblings(view_complex(*s, bound, ci as int)),
{
    let ghost c = view_complex(*s, bound, ci as int);
    proof {
        lemma_view_complex(*s, bound, ci as int);
    }
    let lo = item(s.complexes.as_slice(), ci).combinators.lo;
    let hi = item(s.complexes.as_slice(), ci).combinators.hi;
    let mut k = lo;
    let mut found = false;
    while k < hi
        invariant
            lo <= k <= hi <= s.combinators.len(),
            c == view_complex(*s, bound, ci as int),
            c.combinators.len() == hi - lo,
            forall|j: int| 0 <= j < c.combinators.len() ==> #[trigger] c.combinators[j] == s.combinators@[lo + j],
            found == sibling_combinator_within(c, k - lo),
        decreases hi - k,
    {
        let here = matches!(
            item(s.combinators.as_slice(), k),
            Combinator::NextSibling | Combinator::SubsequentSibling
        );
        proof {
            assert(c.combinators[k - lo] == s.combinators@[k as int]);
        }
        found = here || found;
        k = k.saturating_add(1);
    }
    found
}

/// [`chain`] of `x`, as a vector from `x` up: entry `k` of the chain is entry `len - 1 - k`.
fn chain_up(arena: &Arena, x: usize) -> (r: Vec<usize>)
    ensures
        r@.len() == chain(arena@, x).len(),
        r@.len() >= 1,
        forall|k: int| 0 <= k < r@.len() ==> #[trigger] chain(arena@, x)[k] == r@[r@.len() - 1 - k],
{
    let ghost doc = arena@;
    let mut up: Vec<usize> = Vec::new();
    up.push(x);
    let mut cur = x;
    let mut fuel = arena.len();
    let ghost mut suffix: Seq<NodeId> = Seq::empty();
    loop
        invariant_except_break
            doc == arena@,
            chain(doc, x) == chain_from(doc, cur, fuel as nat) + suffix,
            fuel <= doc.nodes.len(),
            up@.len() >= 1,
            up@.len() == suffix.len() + 1,
            up@[up@.len() - 1] == cur,
            forall|k: int| 0 <= k < suffix.len() ==> #[trigger] suffix[k] == up@[up@.len() - 2 - k],
        ensures
            up@.len() >= 1,
            up@.len() == chain(doc, x).len(),
            forall|k: int| 0 <= k < up@.len() ==> #[trigger] chain(doc, x)[k] == up@[up@.len() - 1 - k],
        decreases fuel,
    {
        let next = if cur < arena.len() {
            arena.parent(cur)
        } else {
            None
        };
        match next {
            Some(p) => {
                if fuel == 0 {
                    proof {
                        assert(chain_from(doc, cur, fuel as nat) == seq![cur]);
                        let ch = seq![cur] + suffix;
                        assert(chain(doc, x) =~= ch);
                        assert forall|k: int| 0 <= k < up@.len() implies #[trigger] chain(doc, x)[k] == up@[up@.len() - 1 - k] by {
                            if k > 0 {
                                assert(ch[k] == suffix[k - 1]);
                            }
                        }
                    }
                    break;
                }
                proof {
                    assert(parent_of(doc, cur) == Some(p));
                    assert(chain_from(doc, cur, fuel as nat) == chain_from(doc, p, (fuel - 1) as nat).push(cur));
                    assert(chain_from(doc, p, (fuel - 1) as nat).push(cur) + suffix =~= chain_from(doc, p, (fuel - 1) as nat) + (seq![cur] + suffix));
                }
                let ghost old_up = up@;
                let ghost old_suffix = suffix;
                proof {
                    suffix = seq![cur] + suffix;
                }
                up.push(p);
                cur = p;
                fuel = fuel.saturating_sub(1);
                proof {
                    assert forall|k: int| 0 <= k < suffix.len() implies #[trigger] suffix[k] == up@[up@.len() - 2 - k] by {
                        if k > 0 {
                            assert(suffix[k] == old_suffix[k - 1]);
                            assert(up@[up@.len() - 2 - k] == old_up[old_up.len() - 2 - (k - 1)]);
                        } else {
                            assert(up@[up@.len() - 2] == old_up[old_up.len() - 1]);
                        }
                    }
                }
            },
            None => {
                proof {
                    assert(parent_of(doc, cur) is None);
                    assert(chain_from(doc, cur, fuel as nat) == seq![cur]);
                    let ch = seq![cur] + suffix;
                    assert(chain(doc, x) =~= ch);
                    assert forall|k: int| 0 <= k < up@.len() implies #[trigger] chain(doc, x)[k] == up@[up@.len() - 1 - k] by {
                        if k > 0 {
                            assert(ch[k] == suffix[k - 1]);
                        }
                    }
                }
                break;
            },
        }
    }
    up
}

/// [`dp_match`]'s answer for the complex selector at `ci` of the list `bound`, and its work.
fn complex_matches_exec(arena: &Arena, s: &ExecSelectors, bound: usize, ci: usize, x: usize) -> (r: (bool, Ghost<nat>))
    requires
        match_args(arena@, *s, bound as int),
        ci < s.complexes.len(),
        complex_wf(view_complex(*s, bound as int, ci as int)),
    ensures
        r.0 == dp_match(arena@, view_complex(*s, bound as int, ci as int), x).0,
        r.1@ == dp_match(arena@, view_complex(*s, bound as int, ci as int), x).1,
    decreases bound, 3int, 0int,
{
    let ghost doc = arena@;
    let ghost c = view_complex(*s, bound as int, ci as int);
    proof {
        lemma_view_complex(*s, bound as int, ci as int);
    }
    let cx = *item(s.complexes.as_slice(), ci);
    let n = cx.compounds.hi.saturating_sub(cx.compounds.lo);
    let siblings = has_sibling_combinator(s, Ghost(bound as int), ci);
    let up = chain_up(arena, x);
    let ghost ch = chain(doc, x);
    let len = up.len();
    let none = exec_falses(n);
    // Level 0, the root of the chain.
    let root = *item(up.as_slice(), len.saturating_sub(1));
    let mut m = row_exec(
        arena,
        s,
        bound,
        ci,
        root,
        (none.as_slice(), none.as_slice(), none.as_slice(), none.as_slice()),
    );
    let mut d = exec_falses(n);
    let ghost mut work: nat = n as nat;
    proof {
        assert(ch[0] == up@[len - 1]);
    }
    let mut k: usize = 1;
    while k < len
        invariant
            match_args(arena@, *s, bound as int),
            doc == arena@,
            ci < s.complexes.len(),
            c == view_complex(*s, bound as int, ci as int),
            complex_wf(c),
            n == c.compounds.len(),
            none@ == falses(n as nat),
            siblings == uses_siblings(c),
            ch == chain(doc, x),
            len == up@.len(),
            len == ch.len(),
            forall|j: int| 0 <= j < len ==> #[trigger] ch[j] == up@[len - 1 - j],
            1 <= k <= len,
            m@ == level(doc, c, ch, k - 1, siblings).row,
            d@ == level(doc, c, ch, k - 1, siblings).descendant,
            work == level(doc, c, ch, k - 1, siblings).work,
            m@.len() == n,
            d@.len() == n,
        decreases len - k,
    {
        let p = *item(up.as_slice(), len.saturating_sub(k));
        let node = *item(up.as_slice(), len.saturating_sub(1).saturating_sub(k));
        proof {
            assert(ch[k - 1] == p);
            assert(ch[k as int] == node);
        }
        let descendant = exec_or(&m, &d);
        if siblings {
            let kids: &[usize] = if p < arena.len() {
                arena.children(p)
            } else {
                &[]
            };
            proof {
                assert(kids@ == children_of(doc, p));
            }
            let end = clazel_dom::exec::find(kids, node).unwrap_or_default();
            let ghost target = clazel_dom::spec::index_of(kids@, node);
            let mut previous = exec_falses(n);
            let mut earlier = exec_falses(n);
            let ghost mut inner: nat = 0;
            let mut j: usize = 0;
            while j < end
                invariant
                    match_args(arena@, *s, bound as int),
                    doc == arena@,
                    ci < s.complexes.len(),
                    c == view_complex(*s, bound as int, ci as int),
                    complex_wf(c),
                    n == c.compounds.len(),
                    j <= end <= kids@.len(),
                    m@.len() == n,
                    descendant@.len() == n,
                    previous@ == siblings_loop(doc, c, kids@, j as int, m@, descendant@).previous,
                    earlier@ == siblings_loop(doc, c, kids@, j as int, m@, descendant@).earlier,
                    inner == siblings_loop(doc, c, kids@, j as int, m@, descendant@).work,
                    previous@.len() == n,
                    earlier@.len() == n,
                decreases end - j,
            {
                let sib = *item(kids, j);
                if element(arena, sib) {
                    let r = row_exec(
                        arena,
                        s,
                        bound,
                        ci,
                        sib,
                        (m.as_slice(), descendant.as_slice(), previous.as_slice(), earlier.as_slice()),
                    );
                    earlier = exec_or(&earlier, &r);
                    previous = r;
                    proof {
                        inner = inner + n as nat;
                    }
                }
                j = j.saturating_add(1);
            }
            proof {
                if end == 0 && target != 0 {
                    assert(target == -1);
                }
            }
            let next = row_exec(
                arena,
                s,
                bound,
                ci,
                node,
                (m.as_slice(), descendant.as_slice(), previous.as_slice(), earlier.as_slice()),
            );
            m = next;
            proof {
                work = work + inner + n as nat;
            }
        } else {
            let next = row_exec(
                arena,
                s,
                bound,
                ci,
                node,
                (m.as_slice(), descendant.as_slice(), none.as_slice(), none.as_slice()),
            );
            m = next;
            proof {
                work = work + n as nat;
            }
        }
        d = descendant;
        k = k.saturating_add(1);
    }
    (*item(m.as_slice(), n.saturating_sub(1)), Ghost(work))
}

/// True if one of the complex selectors of the list at `li` matches `x`.
fn list_matches_exec(arena: &Arena, s: &ExecSelectors, li: usize, x: usize) -> (r: bool)
    requires
        match_args(arena@, *s, li as int),
        li < s.lists.len(),
        x < arena@.nodes.len(),
        list_wf(view_list(*s, li as int), view_list(*s, li as int).len() as int),
    ensures
        r == match_list(arena@, view_list(*s, li as int), view_list(*s, li as int).len() as int, x),
    decreases li, 4int, 0int,
{
    let ghost v = view_list(*s, li as int);
    proof {
        lemma_view_list(*s, li as int);
    }
    let lo = item(s.lists.as_slice(), li).lo;
    let hi = item(s.lists.as_slice(), li).hi;
    let mut k = lo;
    while k < hi
        invariant
            match_args(arena@, *s, li as int),
            li < s.lists.len(),
            x < arena@.nodes.len(),
            lo <= k <= hi <= s.complexes.len(),
            v == view_list(*s, li as int),
            v.len() == hi - lo,
            list_wf(v, v.len() as int),
            forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == view_complex(*s, li as int, lo + j),
            !match_list(arena@, v, k - lo, x),
        decreases hi - k,
    {
        proof {
            lemma_list_wf_at(v, v.len() as int, k - lo);
            assert(v[k - lo] == view_complex(*s, li as int, k as int));
        }
        let (found, Ghost(_work)) = complex_matches_exec(arena, s, li, k, x);
        proof {
            super::lemmas::theorem_match_total(arena@, v[k - lo], x);
        }
        if found {
            proof {
                lemma_list_keeps(arena@, v, k - lo + 1, v.len() as int, x);
            }
            return true;
        }
        k = k.saturating_add(1);
    }
    false
}

/// §21.3 "match a selector against an element": the result list of `s` against `x`.
pub fn matches(arena: &Arena, s: &ExecSelectors, x: usize) -> (r: bool)
    requires
        match_requires(arena@, x),
        ranges_wf(*s),
        s.lists.len() > 0,
        list_wf(view_selectors(*s), view_selectors(*s).len() as int),
    ensures
        match_ensures(arena@, view_selectors(*s), x, r),
{
    list_matches_exec(arena, s, s.lists.len().saturating_sub(1), x)
}

} // verus!

//! HTML §13.2.4.3 the list of active formatting elements over
//! [`ParserBuf`]: "push onto the list" (with the Noah's Ark clause),
//! markers, "clear … up to the last marker", and the searches. Each
//! function is proven equal to the spec function of `spec/base/state.rs` it
//! names, and to keep [`parser_inv`].

#[cfg(verus_only)]
use super::frame::*;
use super::names::*;
#[allow(unused_imports)]
use super::spec::*;
use super::stack::*;
use super::types::*;
use clazel_dom::exec::ExecAttr;
#[cfg(verus_only)]
use clazel_dom::exec::attrs_view;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use vstd::seq_lib::group_to_multiset_ensures;

// ---------------------------------------------------------------------
// Same attributes

/// Two multisets that both hold `x` are equal exactly when they are equal
/// with one `x` removed.
proof fn lemma_ms_cancel(m1: vstd::multiset::Multiset<Attr>, m2: vstd::multiset::Multiset<Attr>, x: Attr)
    requires
        m1.count(x) > 0,
        m2.count(x) > 0,
    ensures
        (m1 == m2) == (m1.remove(x) == m2.remove(x)),
{
    broadcast use vstd::multiset::group_multiset_axioms;

    if m1.remove(x) == m2.remove(x) {
        assert forall|y: Attr| m1.count(y) == m2.count(y) by {
            assert(m1.remove(x).count(y) == m2.remove(x).count(y));
        }
        assert(m1 =~= m2);
    }
}

/// The attributes of `b` at the indices `rest`.
pub open spec fn at_indices(b: Seq<Attr>, rest: Seq<usize>) -> Seq<Attr> {
    rest.map_values(|k: usize| b[k as int])
}

/// [`same_attributes`]: whether the lists are equal as multisets, by
/// pairing each attribute of `a` with an unpaired equal one of `b`.
pub fn same_attributes_exec(a: &[ExecAttr], b: &[ExecAttr]) -> (r: bool)
    ensures
        r == same_attributes(attrs_view(a@), attrs_view(b@)),
{
    let ghost av = attrs_view(a@);
    let ghost bv = attrs_view(b@);
    if a.len() != b.len() {
        proof {
            assert(av.to_multiset().len() != bv.to_multiset().len());
        }
        return false;
    }
    let n = a.len();
    let mut rest: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            n == b@.len(),
            rest@.len() == k,
            forall|j: int| 0 <= j < k ==> rest@[j] == j,
        decreases n - k,
    {
        rest.push(k);
        // Never saturates: k < n.
        k = k.saturating_add(1);
    }
    proof {
        assert(at_indices(bv, rest@) =~= bv);
        assert(av.subrange(0, n as int) =~= av);
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == a@.len(),
            n == b@.len(),
            av == attrs_view(a@),
            bv == attrs_view(b@),
            i <= n,
            rest@.len() == n - i,
            forall|j: int| 0 <= j < rest@.len() ==> (#[trigger] rest@[j]) < n,
            (av.to_multiset() == bv.to_multiset()) == (av.subrange(i as int, n as int).to_multiset() == at_indices(
                bv,
                rest@,
            ).to_multiset()),
        decreases n - i,
    {
        let x = match a.get(i) {
            Some(x) => x,
            None => vstd::pervasive::unreached(),
        };
        let ghost xv = av[i as int];
        let ghost tail = av.subrange(i as int, n as int);
        let ghost rv = at_indices(bv, rest@);
        let mut j: usize = 0;
        let mut found = false;
        while j < rest.len()
            invariant
                j <= rest@.len(),
                n == b@.len(),
                forall|q: int| 0 <= q < rest@.len() ==> (#[trigger] rest@[q]) < n,
                !found ==> forall|q: int| 0 <= q < j ==> bv[#[trigger] rest@[q] as int] != xv,
                found ==> j < rest@.len() && bv[rest@[j as int] as int] == xv,
                bv == attrs_view(b@),
                xv == x@,
            ensures
                !found ==> forall|q: int| 0 <= q < rest@.len() ==> bv[#[trigger] rest@[q] as int] != xv,
                found ==> j < rest@.len() && bv[rest@[j as int] as int] == xv,
            decreases rest@.len() - j,
        {
            let k = match rest.get(j) {
                Some(k) => *k,
                None => vstd::pervasive::unreached(),
            };
            let y = match b.get(k) {
                Some(y) => y,
                None => vstd::pervasive::unreached(),
            };
            if attr_eq(y, x) {
                found = true;
                break;
            }
            // Never saturates: j < rest.len().
            j = j.saturating_add(1);
        }
        if !found {
            proof {
                assert(tail[0] == xv);
                assert(tail.contains(xv));
                if rv.contains(xv) {
                    let q = choose|q: int| 0 <= q < rv.len() && rv[q] == xv;
                    assert(bv[rest@[q] as int] != xv);
                }
            }
            return false;
        }
        let ghost before = rest@;
        let _ = rest.remove(j);
        proof {
            assert(at_indices(bv, rest@) =~= rv.remove(j as int));
            assert(tail.remove(0) =~= av.subrange(i as int + 1, n as int));
            assert(tail.contains(xv));
            assert(rv[j as int] == xv);
            assert(rv.contains(xv));
            lemma_ms_cancel(tail.to_multiset(), rv.to_multiset(), xv);
            assert forall|q: int| 0 <= q < rest@.len() implies (#[trigger] rest@[q]) < n by {
                if q < j {
                    assert(rest@[q] == before[q]);
                } else {
                    assert(rest@[q] == before[q + 1]);
                }
            }
        }
        // Never saturates: i < n.
        i = i.saturating_add(1);
    }
    proof {
        assert(av.subrange(n as int, n as int) =~= Seq::<Attr>::empty());
        assert(at_indices(bv, rest@) =~= Seq::<Attr>::empty());
    }
    true
}

// ---------------------------------------------------------------------
// The list's searches

/// [`after_last_marker`] over the whole list.
pub fn after_last_marker_exec(f: &[ExecFmt]) -> (r: usize)
    ensures
        r as int == after_last_marker(fmts_view(f@), f@.len() as int),
        r <= f@.len(),
{
    let ghost v = fmts_view(f@);
    let mut i = f.len();
    while i > 0
        invariant
            i <= f@.len(),
            v == fmts_view(f@),
            after_last_marker(v, f@.len() as int) == after_last_marker(v, i as int),
        decreases i,
    {
        let x = match f.get(i.saturating_sub(1)) {
            Some(x) => x,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(x@ == v[i - 1]);
        }
        if matches!(x, ExecFmt::Marker) {
            return i;
        }
        i = i.saturating_sub(1);
    }
    0
}

/// [`same_family`].
pub fn same_family_exec(x: &ExecFmt, e: &ExecElem, t: &ExecTagTok) -> (r: bool)
    ensures
        r == same_family(x@, e@, t@),
{
    match x {
        ExecFmt::Marker => false,
        ExecFmt::Entry { elem, token } => u32s_eq(elem.name.as_slice(), e.name.as_slice()) && ns_eq(&elem.ns, &e.ns)
            && same_attributes_exec(token.attrs.as_slice(), t.attrs.as_slice()),
    }
}

/// [`fmt_index_of`] over the first `i` entries: `Some` of the index, or
/// `None` for -1.
pub fn fmt_index_of_exec(f: &[ExecFmt], i: usize, id: usize) -> (r: Option<usize>)
    requires
        i <= f@.len(),
    ensures
        match r {
            Some(k) => k < i && k as int == fmt_index_of(fmts_view(f@), i as int, id),
            None => fmt_index_of(fmts_view(f@), i as int, id) == -1,
        },
{
    let ghost v = fmts_view(f@);
    let mut j = i;
    while j > 0
        invariant
            j <= i,
            i <= f@.len(),
            v == fmts_view(f@),
            fmt_index_of(v, i as int, id) == fmt_index_of(v, j as int, id),
        decreases j,
    {
        let x = match f.get(j.saturating_sub(1)) {
            Some(x) => x,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(x@ == v[j - 1]);
        }
        match x {
            ExecFmt::Entry { elem, .. } if elem.id == id => return Some(j.saturating_sub(1)),
            _ => {},
        }
        j = j.saturating_sub(1);
    }
    None
}

/// [`in_formatting`].
pub fn in_formatting_exec(p: &ParserBuf, id: usize) -> (r: bool)
    ensures
        r == in_formatting(p@, id),
{
    fmt_index_of_exec(p.formatting.as_slice(), p.formatting.len(), id).is_some()
}

/// [`fmt_on_stack`].
pub fn fmt_on_stack_exec(p: &ParserBuf, x: &ExecFmt) -> (r: bool)
    ensures
        r == fmt_on_stack(p@, x@),
{
    match x {
        ExecFmt::Marker => false,
        ExecFmt::Entry { elem, .. } => open_index_of_exec(p, elem.id).is_some(),
    }
}

// ---------------------------------------------------------------------
// Changing the list

/// The view of the list after removing entry `i`.
proof fn lemma_fmts_view_remove(v: Seq<ExecFmt>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        fmts_view(v.remove(i)) == fmts_view(v).remove(i),
{
    assert(fmts_view(v.remove(i)) =~= fmts_view(v).remove(i));
}

/// The view of the list after pushing `x`.
proof fn lemma_fmts_view_push(v: Seq<ExecFmt>, x: ExecFmt)
    ensures
        fmts_view(v.push(x)) == fmts_view(v).push(x@),
{
    assert(fmts_view(v.push(x)) =~= fmts_view(v).push(x@));
}

/// The view of the list after dropping the last entry.
proof fn lemma_fmts_view_drop_last(v: Seq<ExecFmt>)
    requires
        v.len() > 0,
    ensures
        fmts_view(v.drop_last()) == fmts_view(v).drop_last(),
{
    assert(fmts_view(v.drop_last()) =~= fmts_view(v).drop_last());
}

/// §13.2.4.3 "push onto the list of active formatting elements"
/// ([`push_formatting`]): the element and its token must be [`fmt_ok`]
/// unless parsing has stopped.
pub fn push_formatting_exec(p: &mut ParserBuf, e: ExecElem, t: ExecTagTok)
    requires
        parser_inv(old(p)@),
        !old(p)@.stopped ==> fmt_ok(old(p)@.doc, Fmt::Entry { elem: e@, token: t@ }),
    ensures
        final(p)@ == push_formatting(old(p)@, e@, t@),
        parser_inv(final(p)@),
{
    if p.stopped {
        return;
    }
    let ghost f = fmts_view(p.formatting@);
    let ghost ev = e@;
    let ghost tv = t@;
    let n = p.formatting.len();
    // 1.
    let from = after_last_marker_exec(p.formatting.as_slice());
    let mut count: usize = 0;
    let mut first: usize = 0;
    let mut j: usize = from;
    while j < n
        invariant
            from <= j <= n,
            n == p.formatting@.len(),
            f == fmts_view(p.formatting@),
            ev == e@,
            tv == t@,
            count == family_indices(f, from as int, j as int, ev, tv).len(),
            count <= j,
            count > 0 ==> first as int == family_indices(f, from as int, j as int, ev, tv)[0] && first < j,
        decreases n - j,
    {
        let x = match p.formatting.get(j) {
            Some(x) => x,
            None => vstd::pervasive::unreached(),
        };
        proof {
            assert(x@ == f[j as int]);
        }
        if same_family_exec(x, &e, &t) {
            if count == 0 {
                first = j;
            }
            // Never saturates: count <= j < n.
            count = count.saturating_add(1);
        }
        // Never saturates: j < n.
        j = j.saturating_add(1);
    }
    proof {
        lemma_inv_iff(old(p)@);
    }
    let ghost fam = family_indices(f, from as int, n as int, ev, tv);
    let ghost v0 = p.formatting@;
    if count >= 3 {
        let _ = p.formatting.remove(first);
        proof {
            lemma_fmts_view_remove(v0, first as int);
            lemma_fmts_remove(p@.doc, f, first as int);
        }
    }
    // 2.
    let ghost v1 = p.formatting@;
    p.formatting.push(ExecFmt::Entry { elem: e, token: t });
    proof {
        lemma_fmts_view_push(v1, ExecFmt::Entry { elem: e, token: t });
        lemma_fmts_push(p@.doc, fmts_view(v1), Fmt::Entry { elem: ev, token: tv });
        lemma_inv_iff(p@);
    }
}

/// Insert a marker at the end of the list ([`push_marker`]).
pub fn push_marker_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == push_marker(old(p)@),
        parser_inv(final(p)@),
{
    let ghost v = p.formatting@;
    p.formatting.push(ExecFmt::Marker);
    proof {
        lemma_fmts_view_push(v, ExecFmt::Marker);
        lemma_inv_iff(old(p)@);
        lemma_fmts_push(p@.doc, fmts_view(v), Fmt::Marker);
        lemma_inv_iff(p@);
    }
}

/// §13.2.4.3 "clear the list of active formatting elements up to the last
/// marker" ([`clear_to_last_marker`]).
pub fn clear_to_last_marker_exec(p: &mut ParserBuf)
    requires
        parser_inv(old(p)@),
    ensures
        final(p)@ == clear_to_last_marker(old(p)@),
        parser_inv(final(p)@),
{
    loop
        invariant
            parser_inv(p@),
            clear_to_last_marker(p@) == clear_to_last_marker(old(p)@),
        decreases p@.formatting.len(),
    {
        let ghost v = p.formatting@;
        let ghost p0 = p@;
        // 1., 2.
        let entry = match p.formatting.pop() {
            Some(x) => x,
            None => return ,
        };
        proof {
            assert(v.drop_last() == p.formatting@);
            lemma_fmts_view_drop_last(v);
            lemma_inv_iff(p0);
            lemma_fmts_drop_last(p@.doc, fmts_view(v));
            lemma_inv_iff(p@);
        }
        // 3.
        if matches!(entry, ExecFmt::Marker) {
            return ;
        }
    }
}

} // verus!

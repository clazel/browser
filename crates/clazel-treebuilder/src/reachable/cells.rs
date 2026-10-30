//! The stack's last cell ([`last_cell`]) under the changes the helpers
//! make to the stack, and [`cells_wf`] under changes of the stack that add
//! no cell (see [`super`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `id` names a node of the arena and no cell on the stack: the id of an
/// element the parser just created.
pub open spec fn id_new(p: Parser, id: NodeId) -> bool {
    &&& id < p.doc.nodes.len()
    &&& forall|j: int| 0 <= j < p.open.len() && cell_pred()(#[trigger] p.open[j]) ==> p.open[j].id != id
}

/// No entry of `o` from index `m` to index `n - 1` satisfies `f`: the last
/// index satisfying `f` among the first `n` is the one among the first `m`.
pub proof fn lemma_liw_skip(o: Seq<Elem>, m: int, n: int, f: spec_fn(Elem) -> bool)
    requires
        0 <= m <= n <= o.len(),
        forall|j: int| m <= j < n ==> !f(#[trigger] o[j]),
    ensures
        last_index_where(o, n, f) == last_index_where(o, m, f),
    decreases n,
{
    if n > m {
        assert(!f(o[n - 1]));
        lemma_liw_skip(o, m, n - 1, f);
    }
}

/// [`last_index_where`] of a stack is `k` when entry `k` satisfies `f` and
/// none above it does.
pub proof fn lemma_liw_is(o: Seq<Elem>, k: int, f: spec_fn(Elem) -> bool)
    requires
        0 <= k < o.len(),
        f(o[k]),
        forall|j: int| k < j < o.len() ==> !f(#[trigger] o[j]),
    ensures
        last_index_where(o, o.len() as int, f) == k,
{
    lemma_liw_skip(o, k + 1, o.len() as int, f);
}

/// The last entry satisfying `f` does, and none above it does.
pub proof fn lemma_liw_top(o: Seq<Elem>, f: spec_fn(Elem) -> bool)
    ensures
        -1 <= last_index_where(o, o.len() as int, f) < o.len(),
        last_index_where(o, o.len() as int, f) >= 0 ==> f(o[last_index_where(o, o.len() as int, f)]),
        forall|j: int| last_index_where(o, o.len() as int, f) < j < o.len() ==> !f(#[trigger] o[j]),
{
    crate::termination::helpers_ranking::lemma_last_index_where(o, o.len() as int, f);
    assert forall|j: int| last_index_where(o, o.len() as int, f) < j < o.len() implies !f(#[trigger] o[j]) by {
        super::adoption::lemma_liw_last(o, o.len() as int, f, j);
    }
}

/// The last cell of a stack is a cell, and none above it is.
pub proof fn lemma_cell_top(o: Seq<Elem>)
    ensures
        -1 <= last_cell(o) < o.len(),
        has_cell(o) ==> cell_pred()(o[last_cell(o)]),
        forall|j: int| last_cell(o) < j < o.len() ==> !cell_pred()(#[trigger] o[j]),
{
    lemma_liw_top(o, cell_pred());
}

/// A prefix of the stack holding its last cell has the same last cell.
pub proof fn lemma_cell_prefix(o: Seq<Elem>, q: Seq<Elem>)
    requires
        has_cell(o),
        last_cell(o) < q.len() <= o.len(),
        forall|j: int| 0 <= j < q.len() ==> #[trigger] q[j] == o[j],
    ensures
        last_cell(q) == last_cell(o),
        has_cell(q),
{
    lemma_cell_top(o);
    let c = last_cell(o);
    assert(q[c] == o[c]);
    assert forall|j: int| c < j < q.len() implies !cell_pred()(#[trigger] q[j]) by {
        assert(q[j] == o[j]);
    }
    lemma_liw_is(q, c, cell_pred());
}

/// Pushing an element that is not a cell keeps the last cell.
pub proof fn lemma_cell_push(o: Seq<Elem>, e: Elem)
    requires
        has_cell(o),
        !cell_pred()(e),
    ensures
        last_cell(o.push(e)) == last_cell(o),
        has_cell(o.push(e)),
{
    lemma_cell_top(o);
    let c = last_cell(o);
    let q = o.push(e);
    assert(q[c] == o[c]);
    assert forall|j: int| c < j < q.len() implies !cell_pred()(#[trigger] q[j]) by {
        if j < o.len() {
            assert(q[j] == o[j]);
        }
    }
    lemma_liw_is(q, c, cell_pred());
}

/// Removing an entry other than the last cell keeps the last cell (the
/// record).
pub proof fn lemma_cell_remove(o: Seq<Elem>, i: int)
    requires
        has_cell(o),
        0 <= i < o.len(),
        i != last_cell(o),
    ensures
        has_cell(o.remove(i)),
        o.remove(i)[last_cell(o.remove(i))] == o[last_cell(o)],
        i > last_cell(o) ==> last_cell(o.remove(i)) == last_cell(o),
{
    lemma_cell_top(o);
    let c = last_cell(o);
    let q = o.remove(i);
    if i > c {
        assert(q[c] == o[c]);
        assert forall|j: int| c < j < q.len() implies !cell_pred()(#[trigger] q[j]) by {
            if j < i {
                assert(q[j] == o[j]);
            } else {
                assert(q[j] == o[j + 1]);
            }
        }
        lemma_liw_is(q, c, cell_pred());
    } else {
        assert(q[c - 1] == o[c]);
        assert forall|j: int| c - 1 < j < q.len() implies !cell_pred()(#[trigger] q[j]) by {
            assert(q[j] == o[j + 1]);
        }
        lemma_liw_is(q, c - 1, cell_pred());
    }
}

/// Replacing an entry above the last cell by an element that is not a cell
/// keeps the last cell.
pub proof fn lemma_cell_update(o: Seq<Elem>, i: int, e: Elem)
    requires
        has_cell(o),
        last_cell(o) < i < o.len(),
        !cell_pred()(e),
    ensures
        last_cell(o.update(i, e)) == last_cell(o),
        has_cell(o.update(i, e)),
{
    lemma_cell_top(o);
    let c = last_cell(o);
    let q = o.update(i, e);
    assert(q[c] == o[c]);
    assert forall|j: int| c < j < q.len() implies !cell_pred()(#[trigger] q[j]) by {
        if j != i {
            assert(q[j] == o[j]);
        }
    }
    lemma_liw_is(q, c, cell_pred());
}

/// Inserting an element that is not a cell above the last cell keeps the
/// last cell.
pub proof fn lemma_cell_insert(o: Seq<Elem>, i: int, e: Elem)
    requires
        has_cell(o),
        last_cell(o) < i <= o.len(),
        !cell_pred()(e),
    ensures
        last_cell(o.insert(i, e)) == last_cell(o),
        has_cell(o.insert(i, e)),
{
    lemma_cell_top(o);
    let c = last_cell(o);
    let q = o.insert(i, e);
    assert(q[c] == o[c]);
    assert forall|j: int| c < j < q.len() implies !cell_pred()(#[trigger] q[j]) by {
        if j < i {
            assert(q[j] == o[j]);
        } else if j > i {
            assert(q[j] == o[j - 1]);
        }
    }
    lemma_liw_is(q, c, cell_pred());
}

/// A parser whose stack's cells are among `p`'s, with `p`'s list and form
/// element pointer and an arena at least as large, keeps [`cells_wf`].
pub proof fn lemma_cells_wf_open(p: Parser, q: Parser)
    requires
        cells_wf(p),
        q.formatting == p.formatting,
        q.form == p.form,
        q.doc.nodes.len() >= p.doc.nodes.len(),
        forall|j: int|
            0 <= j < q.open.len() && cell_pred()(#[trigger] q.open[j]) ==> exists|k: int|
                0 <= k < p.open.len() && (#[trigger] p.open[k]) == q.open[j],
    ensures
        cells_wf(q),
{
    assert forall|j: int| 0 <= j < q.open.len() && cell_pred()(#[trigger] q.open[j]) implies cell_fresh(q, q.open[j].id) by {
        let k = choose|k: int| 0 <= k < p.open.len() && (#[trigger] p.open[k]) == q.open[j];
        assert(cell_pred()(p.open[k]));
        assert(cell_fresh(p, p.open[k].id));
    }
}

/// Between the last target of a successful scope search and the top of the
/// stack, no entry is in the scope's list.
pub proof fn lemma_scope_above(o: Seq<Elem>, i: int, f: spec_fn(Elem) -> bool, s: Scope)
    requires
        0 <= i <= o.len(),
        in_scope_from(o, i, f, s),
    ensures
        forall|j: int| last_index_where(o, i, f) < j < i ==> !in_scope_list(#[trigger] o[j], s),
    decreases i,
{
    if i > 0 && !f(o[i - 1]) {
        lemma_scope_above(o, i - 1, f, s);
    }
}

/// A target in a scope whose list holds the cells, that is not a cell
/// itself, is above the last cell.
pub proof fn lemma_scope_cell(o: Seq<Elem>, f: spec_fn(Elem) -> bool, s: Scope)
    requires
        in_scope_from(o, o.len() as int, f, s),
        s != Scope::Table,
        last_index_where(o, o.len() as int, f) >= 0 ==> !cell_pred()(o[last_index_where(o, o.len() as int, f)]),
    ensures
        last_cell(o) < last_index_where(o, o.len() as int, f),
{
    let n = o.len() as int;
    crate::exec::modes::in_body_start_lemmas::lemma_scope_liw(o, n, f, s);
    crate::termination::helpers_ranking::lemma_last_index_where(o, n, f);
    let k = last_index_where(o, n, f);
    lemma_scope_above(o, n, f, s);
    assert forall|j: int| k + 1 <= j < n implies !cell_pred()(#[trigger] o[j]) by {
        assert(!in_scope_list(o[j], s));
    }
    lemma_liw_skip(o, k + 1, n, cell_pred());
    crate::termination::helpers_ranking::lemma_last_index_where(o, k, cell_pred());
}

// ---------------------------------------------------------------------
// The helpers do not read the insertion mode. The rules that pop the cell
// in the "in cell" mode and then switch the mode ("close the cell", the
// `template` end tag, "in template"'s end of file, the `frameset` start
// tag) are proven on the parser put in another mode.

/// The parser `p` with the insertion mode `m`.
pub open spec fn mode_as(p: Parser, m: Mode) -> Parser {
    Parser { mode: m, ..p }
}

/// [`pop_while`] does not read the mode.
pub proof fn lemma_pop_while_mode(p: Parser, f: spec_fn(Elem) -> bool, m: Mode)
    ensures
        pop_while(mode_as(p, m), f) == mode_as(pop_while(p, f), m),
    decreases p.open.len(),
{
    if p.open.len() > 0 && f(current_node(p)) {
        assert(pop(mode_as(p, m)) == mode_as(pop(p), m));
        lemma_pop_while_mode(pop(p), f, m);
    }
}

/// `exec::stack::pop_until_where` does not read the mode.
pub proof fn lemma_pop_until_where_mode(p: Parser, f: spec_fn(Elem) -> bool, m: Mode)
    ensures
        crate::exec::stack::pop_until_where(mode_as(p, m), f) == mode_as(crate::exec::stack::pop_until_where(p, f), m),
    decreases p.open.len(),
{
    if p.open.len() > 0 {
        assert(pop(mode_as(p, m)) == mode_as(pop(p), m));
        if !f(current_node(p)) {
            lemma_pop_until_where_mode(pop(p), f, m);
        }
    }
}

/// [`clear_to_last_marker`] does not read the mode.
pub proof fn lemma_clear_mode(p: Parser, m: Mode)
    ensures
        clear_to_last_marker(mode_as(p, m)) == mode_as(clear_to_last_marker(p), m),
    decreases p.formatting.len(),
{
    if p.formatting.len() > 0 && !(p.formatting.last() is Marker) {
        let q = Parser { formatting: p.formatting.drop_last(), ..p };
        assert(Parser { formatting: mode_as(p, m).formatting.drop_last(), ..mode_as(p, m) } == mode_as(q, m));
        lemma_clear_mode(q, m);
    }
}

/// [`reset_from`] does not read the mode.
pub proof fn lemma_reset_from_mode(p: Parser, m: Mode, i: int)
    ensures
        reset_from(mode_as(p, m), i) == reset_from(p, i),
    decreases i,
{
    if i >= 1 {
        lemma_reset_from_mode(p, m, i - 1);
    }
}

} // verus!

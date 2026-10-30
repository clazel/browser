//! [`cell_scoped`] (the last cell has no `table` or `template` element
//! above it) and [`html_once`] (the `html` element is only at the root)
//! under the changes the helpers make to the stack (see [`super`]).

#[cfg(verus_only)]
use super::cells::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A prefix of the stack holding its last cell keeps [`cell_scoped`].
pub proof fn lemma_scoped_prefix(o: Seq<Elem>, q: Seq<Elem>)
    requires
        cell_scoped(o),
        last_cell(o) < q.len() <= o.len(),
        forall|j: int| 0 <= j < q.len() ==> #[trigger] q[j] == o[j],
    ensures
        cell_scoped(q),
{
    lemma_cell_prefix(o, q);
    assert forall|j: int| last_cell(q) < j < q.len() implies !table_wall(#[trigger] q[j]) by {
        assert(q[j] == o[j]);
    }
}

/// Pushing an element that is neither a cell nor a `table` or `template`
/// keeps [`cell_scoped`].
pub proof fn lemma_scoped_push(o: Seq<Elem>, e: Elem)
    requires
        cell_scoped(o),
        !cell_pred()(e),
        !table_wall(e),
    ensures
        cell_scoped(o.push(e)),
{
    lemma_cell_push(o, e);
    let q = o.push(e);
    assert forall|j: int| last_cell(q) < j < q.len() implies !table_wall(#[trigger] q[j]) by {
        if j < o.len() {
            assert(q[j] == o[j]);
        }
    }
}

/// Removing an entry other than the last cell keeps [`cell_scoped`].
pub proof fn lemma_scoped_remove(o: Seq<Elem>, i: int)
    requires
        cell_scoped(o),
        0 <= i < o.len(),
        i != last_cell(o),
    ensures
        cell_scoped(o.remove(i)),
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
        assert forall|j: int| last_cell(q) < j < q.len() implies !table_wall(#[trigger] q[j]) by {
            if j < i {
                assert(q[j] == o[j]);
            } else {
                assert(q[j] == o[j + 1]);
            }
        }
    } else {
        assert(q[c - 1] == o[c]);
        assert forall|j: int| c - 1 < j < q.len() implies !cell_pred()(#[trigger] q[j]) by {
            assert(q[j] == o[j + 1]);
        }
        lemma_liw_is(q, c - 1, cell_pred());
        assert forall|j: int| last_cell(q) < j < q.len() implies !table_wall(#[trigger] q[j]) by {
            assert(q[j] == o[j + 1]);
        }
    }
}

/// Replacing an entry above the last cell by an element that is neither a
/// cell nor a `table` or `template` keeps [`cell_scoped`].
pub proof fn lemma_scoped_update(o: Seq<Elem>, i: int, e: Elem)
    requires
        cell_scoped(o),
        last_cell(o) < i < o.len(),
        !cell_pred()(e),
        !table_wall(e),
    ensures
        cell_scoped(o.update(i, e)),
{
    lemma_cell_update(o, i, e);
    let q = o.update(i, e);
    assert forall|j: int| last_cell(q) < j < q.len() implies !table_wall(#[trigger] q[j]) by {
        if j != i {
            assert(q[j] == o[j]);
        }
    }
}

/// Inserting an element that is neither a cell nor a `table` or `template`
/// above the last cell keeps [`cell_scoped`].
pub proof fn lemma_scoped_insert(o: Seq<Elem>, i: int, e: Elem)
    requires
        cell_scoped(o),
        last_cell(o) < i <= o.len(),
        !cell_pred()(e),
        !table_wall(e),
    ensures
        cell_scoped(o.insert(i, e)),
{
    lemma_cell_insert(o, i, e);
    let q = o.insert(i, e);
    assert forall|j: int| last_cell(q) < j < q.len() implies !table_wall(#[trigger] q[j]) by {
        if j < i {
            assert(q[j] == o[j]);
        } else if j > i {
            assert(q[j] == o[j - 1]);
        }
    }
}

/// A cell pushed onto the stack is its last cell, in table scope.
pub proof fn lemma_scoped_push_cell(o: Seq<Elem>, e: Elem)
    requires
        cell_pred()(e),
    ensures
        cell_scoped(o.push(e)),
        last_cell(o.push(e)) == o.len(),
{
    let q = o.push(e);
    lemma_liw_is(q, o.len() as int, cell_pred());
}

/// A prefix of the stack keeps [`html_once`].
pub proof fn lemma_once_prefix(o: Seq<Elem>, q: Seq<Elem>)
    requires
        html_once(o),
        q.len() <= o.len(),
        forall|j: int| 0 <= j < q.len() ==> #[trigger] q[j] == o[j],
    ensures
        html_once(q),
{
    assert forall|j: int| 0 < j < q.len() implies !is_html(#[trigger] q[j], Tag::Html) by {
        assert(q[j] == o[j]);
    }
}

/// Pushing an element other than `html` onto a nonempty stack keeps
/// [`html_once`].
pub proof fn lemma_once_push(o: Seq<Elem>, e: Elem)
    requires
        html_once(o),
        !is_html(e, Tag::Html),
    ensures
        html_once(o.push(e)),
{
    let q = o.push(e);
    assert forall|j: int| 0 < j < q.len() implies !is_html(#[trigger] q[j], Tag::Html) by {
        if j < o.len() {
            assert(q[j] == o[j]);
        }
    }
}

/// Removing an entry at index `i >= 1` keeps [`html_once`].
pub proof fn lemma_once_remove(o: Seq<Elem>, i: int)
    requires
        html_once(o),
        1 <= i < o.len(),
    ensures
        html_once(o.remove(i)),
{
    let q = o.remove(i);
    assert forall|j: int| 0 < j < q.len() implies !is_html(#[trigger] q[j], Tag::Html) by {
        if j < i {
            assert(q[j] == o[j]);
        } else {
            assert(q[j] == o[j + 1]);
        }
    }
}

/// Replacing an entry at index `i >= 1` by an element other than `html`
/// keeps [`html_once`].
pub proof fn lemma_once_update(o: Seq<Elem>, i: int, e: Elem)
    requires
        html_once(o),
        1 <= i < o.len(),
        !is_html(e, Tag::Html),
    ensures
        html_once(o.update(i, e)),
{
    let q = o.update(i, e);
    assert forall|j: int| 0 < j < q.len() implies !is_html(#[trigger] q[j], Tag::Html) by {
        if j != i {
            assert(q[j] == o[j]);
        }
    }
}

/// Inserting an element other than `html` at index `i >= 1` keeps
/// [`html_once`].
pub proof fn lemma_once_insert(o: Seq<Elem>, i: int, e: Elem)
    requires
        html_once(o),
        1 <= i <= o.len(),
        !is_html(e, Tag::Html),
    ensures
        html_once(o.insert(i, e)),
{
    let q = o.insert(i, e);
    assert forall|j: int| 0 < j < q.len() implies !is_html(#[trigger] q[j], Tag::Html) by {
        if j < i {
            assert(q[j] == o[j]);
        } else if j > i {
            assert(q[j] == o[j - 1]);
        }
    }
}

/// A last cell with no `table` or `template` above it, and no `html`
/// element above the root, is in table scope (from entry `i` down to it).
pub proof fn lemma_scoped_in_scope(o: Seq<Elem>, i: int)
    requires
        cell_scoped(o),
        html_once(o),
        last_cell(o) < i <= o.len(),
    ensures
        in_scope_from(o, i, cell_pred(), Scope::Table),
    decreases i,
{
    lemma_cell_top(o);
    let c = last_cell(o);
    if i - 1 > c {
        assert(!table_wall(o[i - 1]));
        assert(!is_html(o[i - 1], Tag::Html));
        assert(!cell_pred()(o[i - 1]));
        lemma_scoped_in_scope(o, i - 1);
    } else {
        assert(cell_pred()(o[c]));
    }
}

/// [`reset_from`] chooses "in cell" only on a cell (step 4) with no `table`
/// or `template` element above it (steps 9 and 10 stop there first, and a
/// template insertion mode is never "in cell").
pub proof fn lemma_reset_walls(p: Parser, i: int)
    requires
        rooted_seq(p.open),
        crate::termination::helpers_ranking::count_ok(p),
        0 <= i < p.open.len(),
    ensures
        reset_from(p, i) == Mode::InCell ==> {
            let c = last_index_where(p.open, i + 1, cell_pred());
            &&& c >= 0
            &&& forall|j: int| c < j <= i ==> !table_wall(#[trigger] p.open[j])
        },
    decreases i,
{
    let last = i == 0;
    let node = if last && p.context is Some {
        p.context->Some_0
    } else {
        p.open[i]
    };
    if is_html(node, Tag::Template) {
        if last && p.context is Some {
            assert(template_count(p) >= 1);
        } else {
            crate::termination::helpers_ranking::lemma_templates_in_pos(p.open, p.open.len() as int, i);
            assert(template_count(p) >= 1);
        }
        assert(p.template_modes.len() > 0);
        assert(crate::termination::template_mode_ok(p.template_modes[p.template_modes.len() - 1]));
    }
    if i >= 1 {
        lemma_reset_walls(p, i - 1);
    }
}

/// "Reset the insertion mode appropriately" chooses "in cell" only on a
/// stack with [`cell_scoped`].
pub proof fn lemma_reset_scoped(p: Parser)
    requires
        rooted_seq(p.open),
        crate::termination::helpers_ranking::count_ok(p),
    ensures
        reset_insertion_mode(p).mode == Mode::InCell ==> cell_scoped(p.open),
{
    lemma_reset_walls(p, p.open.len() - 1);
}

} // verus!

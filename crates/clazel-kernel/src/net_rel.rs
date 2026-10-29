//! Item 3.7: the unwinding lemmas for the network. The relation `rel` of two
//! runs (the trace and its purge) says, of connections, `rel_conn`: the same
//! counter, every connection of the first run is in the second, and every
//! connection of the second whose tab is open in the first is in the first.
//! Here: the connection part of `rel` through the table's operations, and the
//! consistency of `commit_navigation`, `abort_navigation`, `carry_out`,
//! `begin_navigation` and `net` from related states. The outputs of related
//! runs agree on the renderer-bound ones (`renderer_outs`); the network-bound
//! ones differ in the order of `Close`s and in the octets of `Send`s, which no
//! renderer sees.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Tabs.
// ---------------------------------------------------------------------

/// A tab is open exactly when some renderer has it.
pub proof fn lemma_tab_open_iff(rs: Seq<Renderer>, tab: nat)
    ensures
        (find_by_tab(rs, tab, 0) is Some) == (exists|j: int| 0 <= j < rs.len() && (#[trigger] rs[j]).tab == tab),
{
    crate::invariant::lemma_find_by_tab(rs, tab, 0);
}

/// Replacing a renderer by one of the same tab opens no new tab.
pub proof fn lemma_tabs_update(rs: Seq<Renderer>, i: int, r: Renderer)
    requires
        0 <= i < rs.len(),
        r.tab == rs[i].tab,
    ensures
        forall|tab: nat| find_by_tab(rs.update(i, r), tab, 0) is Some ==> find_by_tab(rs, tab, 0) is Some,
{
    assert forall|tab: nat| find_by_tab(rs.update(i, r), tab, 0) is Some implies find_by_tab(rs, tab, 0) is Some by {
        lemma_tab_open_iff(rs.update(i, r), tab);
        lemma_tab_open_iff(rs, tab);
        let j = choose|j: int| 0 <= j < rs.update(i, r).len() && rs.update(i, r)[j].tab == tab;
        if j != i {
            assert(rs.update(i, r)[j] == rs[j]);
        }
        assert(rs[j].tab == tab);
    }
}

/// Removing a renderer opens no new tab, and closes its own.
pub proof fn lemma_tabs_remove(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, i: int)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        0 <= i < rs.len(),
    ensures
        forall|tab: nat| find_by_tab(rs.remove(i), tab, 0) is Some ==> find_by_tab(rs, tab, 0) is Some && tab != rs[i].tab,
{
    assert forall|tab: nat| find_by_tab(rs.remove(i), tab, 0) is Some implies find_by_tab(rs, tab, 0) is Some && tab != rs[i].tab by {
        lemma_tab_open_iff(rs.remove(i), tab);
        lemma_tab_open_iff(rs, tab);
        let j = choose|j: int| 0 <= j < rs.remove(i).len() && rs.remove(i)[j].tab == tab;
        let m = if j < i { j } else { j + 1 };
        assert(rs.remove(i)[j] == rs[m]);
        assert(rs[m].tab == tab);
        if tab == rs[i].tab {
            crate::theorems::tab_unique(urls, ghost_state_of(rs, next_id), i, m);
        }
    }
}

/// A state with the renderer table `rs` (for lemmas stated on tables).
pub open spec fn ghost_state_of(rs: Seq<Renderer>, next_id: nat) -> State {
    State { renderers: rs, jar: seq![], storage: Map::empty(), next_id, conns: seq![], next_conn: 0, now: 0 }
}

// ---------------------------------------------------------------------
// `crate::noninterference::rel` through a change of connections only.
// ---------------------------------------------------------------------

/// `crate::noninterference::rel_conn` of two states whose connections are those of two related states
/// and whose tabs are among theirs.
pub proof fn lemma_rel_conn_tabs(s1: State, s2: State, s1b: State, s2b: State)
    requires
        crate::noninterference::rel_conn(s1, s2),
        s1b.conns == s1.conns,
        s2b.conns == s2.conns,
        s1b.next_conn == s1.next_conn,
        s2b.next_conn == s2.next_conn,
        forall|tab: nat| find_by_tab(s1b.renderers, tab, 0) is Some ==> find_by_tab(s1.renderers, tab, 0) is Some,
    ensures
        crate::noninterference::rel_conn(s1b, s2b),
{
}

/// `crate::noninterference::rel` of two states that differ from related ones in their connections
/// (and counter) only.
pub proof fn lemma_rel_conns_only(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, s1b: State, s2b: State)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::invariant::kernel_wf(rules, urls, s1b),
        crate::invariant::kernel_wf(rules, urls, s2b),
        s1b.renderers == s1.renderers,
        s1b.jar == s1.jar,
        s1b.storage == s1.storage,
        s1b.next_id == s1.next_id,
        s1b.now == s1.now,
        s2b.renderers == s2.renderers,
        s2b.jar == s2.jar,
        s2b.storage == s2.storage,
        s2b.next_id == s2.next_id,
        s2b.now == s2.now,
        crate::noninterference::rel_conn(s1b, s2b),
    ensures
        crate::noninterference::rel(rules, urls, d, s1b, s2b),
{
}

/// Closing the connections of a tab, in both runs, keeps them related.
pub proof fn lemma_rel_close_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, tab: nat)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        crate::noninterference::rel(rules, urls, d, close_tab_conns(s1, tab).0, close_tab_conns(s2, tab).0),
{
    let s1m = close_tab_conns(s1, tab).0;
    let s2m = close_tab_conns(s2, tab).0;
    crate::net_wf::lemma_close_tab_conns_wf(rules, urls, s1, tab);
    crate::net_wf::lemma_close_tab_conns_wf(rules, urls, s2, tab);
    assert forall|i: int| 0 <= i < s1m.conns.len() implies s2m.conns.contains(#[trigger] s1m.conns[i]) by {
        assert(s1m.conns.contains(s1m.conns[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s1.conns, |c: Connection| c.tab != tab, s1m.conns[i]);
        assert(s2.conns.contains(s1m.conns[i]));
        crate::net_wf::lemma_without_tab_keeps(s2.conns, tab, s1m.conns[i]);
    }
    assert forall|i: int| 0 <= i < s2m.conns.len() && find_by_tab(s1m.renderers, (#[trigger] s2m.conns[i]).tab, 0) is Some implies s1m.conns.contains(s2m.conns[i]) by {
        assert(s2m.conns.contains(s2m.conns[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s2.conns, |c: Connection| c.tab != tab, s2m.conns[i]);
        let j = choose|j: int| 0 <= j < s2.conns.len() && s2.conns[j] == s2m.conns[i];
        assert(s1.conns.contains(s2m.conns[i]));
        crate::net_wf::lemma_without_tab_keeps(s1.conns, tab, s2m.conns[i]);
    }
    lemma_rel_conns_only(rules, urls, d, s1, s2, s1m, s2m);
}

/// Forgetting the same connection in both runs keeps them related.
pub proof fn lemma_rel_without_conn(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, id: nat)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        crate::noninterference::rel(rules, urls, d, State { conns: without_conn(s1.conns, id), ..s1 }, State { conns: without_conn(s2.conns, id), ..s2 }),
{
    let s1m = State { conns: without_conn(s1.conns, id), ..s1 };
    let s2m = State { conns: without_conn(s2.conns, id), ..s2 };
    crate::net_wf::lemma_without_conn_wf(s1.renderers, s1.conns, s1.next_conn, id);
    crate::net_wf::lemma_without_conn_wf(s2.renderers, s2.conns, s2.next_conn, id);
    assert forall|i: int| 0 <= i < s1m.conns.len() implies s2m.conns.contains(#[trigger] s1m.conns[i]) by {
        assert(s1m.conns.contains(s1m.conns[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s1.conns, |c: Connection| c.id != id, s1m.conns[i]);
        assert(s2.conns.contains(s1m.conns[i]));
        crate::net_wf::lemma_filter_keeps(s2.conns, |c: Connection| c.id != id, s1m.conns[i]);
    }
    assert forall|i: int| 0 <= i < s2m.conns.len() && find_by_tab(s1m.renderers, (#[trigger] s2m.conns[i]).tab, 0) is Some implies s1m.conns.contains(s2m.conns[i]) by {
        assert(s2m.conns.contains(s2m.conns[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s2.conns, |c: Connection| c.id != id, s2m.conns[i]);
        assert(s1.conns.contains(s2m.conns[i]));
        crate::net_wf::lemma_filter_keeps(s1.conns, |c: Connection| c.id != id, s2m.conns[i]);
    }
    lemma_rel_conns_only(rules, urls, d, s1, s2, s1m, s2m);
}

/// Opening the same connection in both runs keeps them related, if the tab
/// is navigating in both.
pub proof fn lemma_rel_push_conn(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, c: Connection)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        c.id == s1.next_conn,
        crate::invariant::conn_backed(s1.renderers, c),
        crate::invariant::conn_backed(s2.renderers, c),
    ensures
        crate::noninterference::rel(
            rules,
            urls,
            d,
            State { conns: s1.conns.push(c), next_conn: s1.next_conn + 1, ..s1 },
            State { conns: s2.conns.push(c), next_conn: s2.next_conn + 1, ..s2 },
        ),
{
    let s1m = State { conns: s1.conns.push(c), next_conn: s1.next_conn + 1, ..s1 };
    let s2m = State { conns: s2.conns.push(c), next_conn: s2.next_conn + 1, ..s2 };
    crate::net_wf::lemma_conns_wf_push_conn(s1.renderers, s1.conns, s1.next_conn, c);
    crate::net_wf::lemma_conns_wf_push_conn(s2.renderers, s2.conns, s2.next_conn, c);
    assert forall|i: int| 0 <= i < s1m.conns.len() implies s2m.conns.contains(#[trigger] s1m.conns[i]) by {
        if i < s1.conns.len() {
            assert(s1m.conns[i] == s1.conns[i]);
            assert(s2.conns.contains(s1.conns[i]));
            let j = choose|j: int| 0 <= j < s2.conns.len() && s2.conns[j] == s1.conns[i];
            assert(s2m.conns[j] == s2.conns[j]);
        } else {
            assert(s1m.conns[i] == c);
            assert(s2m.conns[s2.conns.len() as int] == c);
        }
    }
    assert forall|i: int| 0 <= i < s2m.conns.len() && find_by_tab(s1m.renderers, (#[trigger] s2m.conns[i]).tab, 0) is Some implies s1m.conns.contains(s2m.conns[i]) by {
        if i < s2.conns.len() {
            assert(s2m.conns[i] == s2.conns[i]);
            assert(s1.conns.contains(s2.conns[i]));
            let j = choose|j: int| 0 <= j < s1.conns.len() && s1.conns[j] == s2.conns[i];
            assert(s1m.conns[j] == s1.conns[j]);
        } else {
            assert(s2m.conns[i] == c);
            assert(s1m.conns[s1.conns.len() as int] == c);
        }
    }
    lemma_rel_conns_only(rules, urls, d, s1, s2, s1m, s2m);
}

/// The renderer-bound outputs of a sequence of `Close`s are none.
pub proof fn lemma_closes_not_renderer(conns: Seq<Connection>, tab: nat)
    ensures
        crate::noninterference::renderer_outs(closes_of_tab(conns, tab)) == Seq::<Output>::empty(),
{
    crate::net_theorems::lemma_closes_of_tab(conns, tab);
    let cs = closes_of_tab(conns, tab);
    assert forall|k: int| 0 <= k < cs.len() implies !(|o: Output| crate::noninterference::renderer_bound(o))(#[trigger] cs[k]) by {}
    crate::unwind_base::lemma_filter_none(cs, |o: Output| crate::noninterference::renderer_bound(o));
}

/// Opening a new tab, in both runs, keeps the connections related.
pub proof fn lemma_rel_conn_open_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s1: State, s2: State, s1b: State, s2b: State, rn: Renderer)
    requires
        crate::noninterference::rel_conn(s1, s2),
        crate::invariant::kernel_wf(rules, urls, s2),
        s1.next_id == s2.next_id,
        s1b.renderers == s1.renderers.push(rn),
        rn.tab == s1.next_id,
        s1b.conns == s1.conns,
        s2b.conns == s2.conns,
        s1b.next_conn == s1.next_conn,
        s2b.next_conn == s2.next_conn,
    ensures
        crate::noninterference::rel_conn(s1b, s2b),
{
    assert forall|i: int| 0 <= i < s2b.conns.len() && find_by_tab(s1b.renderers, (#[trigger] s2b.conns[i]).tab, 0) is Some implies s1b.conns.contains(s2b.conns[i]) by {
        let c = s2b.conns[i];
        lemma_tab_open_iff(s1b.renderers, c.tab);
        let j = choose|j: int| 0 <= j < s1b.renderers.len() && s1b.renderers[j].tab == c.tab;
        assert(crate::invariant::conn_backed(s2.renderers, c));
        let m = choose|m: int| 0 <= m < s2.renderers.len() && s2.renderers[m].tab == c.tab && (s2.renderers[m].pending matches Some(nav) && nav.partition == c.partition);
        assert(s2.renderers[m].tab < s2.next_id);
        if j < s1.renderers.len() {
            assert(s1b.renderers[j] == s1.renderers[j]);
            lemma_tab_open_iff(s1.renderers, c.tab);
        } else {
            assert(s1b.renderers[j] == rn);
            assert(false);
        }
    }
}

/// A renderer's exit, in both runs (the same renderer), keeps the connections related.
pub proof fn lemma_rel_conn_exit_both(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s1: State, s2: State, i1: int, i2: int)
    requires
        crate::noninterference::rel_conn(s1, s2),
        crate::invariant::kernel_wf(rules, urls, s1),
        crate::invariant::kernel_wf(rules, urls, s2),
        0 <= i1 < s1.renderers.len(),
        0 <= i2 < s2.renderers.len(),
        s1.renderers[i1] == s2.renderers[i2],
    ensures
        crate::noninterference::rel_conn(
            State { conns: without_tab(s1.conns, s1.renderers[i1].tab), renderers: s1.renderers.remove(i1), ..s1 },
            State { conns: without_tab(s2.conns, s2.renderers[i2].tab), renderers: s2.renderers.remove(i2), ..s2 },
        ),
{
    let t = s1.renderers[i1].tab;
    let s1b = State { conns: without_tab(s1.conns, t), renderers: s1.renderers.remove(i1), ..s1 };
    let s2b = State { conns: without_tab(s2.conns, t), renderers: s2.renderers.remove(i2), ..s2 };
    assert forall|i: int| 0 <= i < s1b.conns.len() implies s2b.conns.contains(#[trigger] s1b.conns[i]) by {
        assert(s1b.conns.contains(s1b.conns[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s1.conns, |c: Connection| c.tab != t, s1b.conns[i]);
        assert(s2.conns.contains(s1b.conns[i]));
        crate::net_wf::lemma_without_tab_keeps(s2.conns, t, s1b.conns[i]);
    }
    lemma_tabs_remove(urls, s1.renderers, s1.next_id, i1);
    assert forall|i: int| 0 <= i < s2b.conns.len() && find_by_tab(s1b.renderers, (#[trigger] s2b.conns[i]).tab, 0) is Some implies s1b.conns.contains(s2b.conns[i]) by {
        assert(s2b.conns.contains(s2b.conns[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s2.conns, |c: Connection| c.tab != t, s2b.conns[i]);
        assert(find_by_tab(s1.renderers, s2b.conns[i].tab, 0) is Some);
        assert(s1.conns.contains(s2b.conns[i]));
        crate::net_wf::lemma_without_tab_keeps(s1.conns, t, s2b.conns[i]);
    }
}

/// A renderer's exit in the first run only keeps the connections related.
pub proof fn lemma_rel_conn_exit_first(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s1: State, s2: State, i1: int)
    requires
        crate::noninterference::rel_conn(s1, s2),
        crate::invariant::kernel_wf(rules, urls, s1),
        0 <= i1 < s1.renderers.len(),
    ensures
        crate::noninterference::rel_conn(State { conns: without_tab(s1.conns, s1.renderers[i1].tab), renderers: s1.renderers.remove(i1), ..s1 }, s2),
{
    let t = s1.renderers[i1].tab;
    let s1b = State { conns: without_tab(s1.conns, t), renderers: s1.renderers.remove(i1), ..s1 };
    assert forall|i: int| 0 <= i < s1b.conns.len() implies s2.conns.contains(#[trigger] s1b.conns[i]) by {
        assert(s1b.conns.contains(s1b.conns[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s1.conns, |c: Connection| c.tab != t, s1b.conns[i]);
    }
    lemma_tabs_remove(urls, s1.renderers, s1.next_id, i1);
    assert forall|i: int| 0 <= i < s2.conns.len() && find_by_tab(s1b.renderers, (#[trigger] s2.conns[i]).tab, 0) is Some implies s1b.conns.contains(s2.conns[i]) by {
        assert(find_by_tab(s1.renderers, s2.conns[i].tab, 0) is Some);
        assert(s1.conns.contains(s2.conns[i]));
        crate::net_wf::lemma_without_tab_keeps(s1.conns, t, s2.conns[i]);
    }
}

/// A renderer's exit in the second run only (the first run does not have it)
/// keeps the connections related.
pub proof fn lemma_rel_conn_exit_second(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s1: State, s2: State, i2: int)
    requires
        crate::noninterference::rel_conn(s1, s2),
        crate::invariant::kernel_wf(rules, urls, s1),
        crate::invariant::kernel_wf(rules, urls, s2),
        0 <= i2 < s2.renderers.len(),
        forall|k: int| 0 <= k < s1.renderers.len() ==> s2.renderers.contains(#[trigger] s1.renderers[k]),
        !s1.renderers.contains(s2.renderers[i2]),
    ensures
        crate::noninterference::rel_conn(s1, State { conns: without_tab(s2.conns, s2.renderers[i2].tab), renderers: s2.renderers.remove(i2), ..s2 }),
{
    let t = s2.renderers[i2].tab;
    let s2b = State { conns: without_tab(s2.conns, t), renderers: s2.renderers.remove(i2), ..s2 };
    // The first run has no renderer of the tab: it would be the second's (unique tabs).
    assert(find_by_tab(s1.renderers, t, 0) is None) by {
        lemma_tab_open_iff(s1.renderers, t);
        if find_by_tab(s1.renderers, t, 0) is Some {
            let j = choose|j: int| 0 <= j < s1.renderers.len() && s1.renderers[j].tab == t;
            assert(s2.renderers.contains(s1.renderers[j]));
            let m = choose|m: int| 0 <= m < s2.renderers.len() && s2.renderers[m] == s1.renderers[j];
            crate::theorems::tab_unique(urls, s2, i2, m);
            assert(s1.renderers[j] == s2.renderers[i2]);
        }
    }
    assert forall|i: int| 0 <= i < s1.conns.len() implies s2b.conns.contains(#[trigger] s1.conns[i]) by {
        assert(s1.conns.contains(s1.conns[i]));
        assert(s2.conns.contains(s1.conns[i]));
        assert(crate::invariant::conn_backed(s1.renderers, s1.conns[i]));
        let m = choose|m: int| 0 <= m < s1.renderers.len() && s1.renderers[m].tab == s1.conns[i].tab && (s1.renderers[m].pending matches Some(nav) && nav.partition == s1.conns[i].partition);
        assert(s1.conns[i].tab != t);
        crate::net_wf::lemma_without_tab_keeps(s2.conns, t, s1.conns[i]);
    }
    assert forall|i: int| 0 <= i < s2b.conns.len() && find_by_tab(s1.renderers, (#[trigger] s2b.conns[i]).tab, 0) is Some implies s1.conns.contains(s2b.conns[i]) by {
        assert(s2b.conns.contains(s2b.conns[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s2.conns, |c: Connection| c.tab != t, s2b.conns[i]);
    }
}

// ---------------------------------------------------------------------
// Ending a navigation.
// ---------------------------------------------------------------------

/// The renderer-bound outputs of a concatenation.
pub proof fn lemma_renderer_outs_concat(a: Seq<Output>, b: Seq<Output>)
    ensures
        crate::noninterference::renderer_outs(a + b) == crate::noninterference::renderer_outs(a) + crate::noninterference::renderer_outs(b),
{
    Seq::<Output>::filter_distributes_over_add(a, b, |o: Output| crate::noninterference::renderer_bound(o));
}

/// A single output that is not renderer-bound has no renderer-bound outputs.
pub proof fn lemma_renderer_outs_single(o: Output)
    requires
        !crate::noninterference::renderer_bound(o),
    ensures
        crate::noninterference::renderer_outs(seq![o]) == Seq::<Output>::empty(),
{
    let p = |x: Output| crate::noninterference::renderer_bound(x);
    reveal(Seq::filter);
    assert(seq![o].drop_last() =~= Seq::<Output>::empty());
    assert(Seq::<Output>::empty().filter(p) =~= Seq::<Output>::empty());
    assert(seq![o].last() == o);
    assert(!p(o));
    assert(seq![o].filter(p) =~= Seq::<Output>::empty());
}

/// The renderer-bound outputs of a kill are the `Kill` alone.
pub proof fn lemma_renderer_outs_kill(id: nat, conns: Seq<Connection>, tab: nat)
    ensures
        crate::noninterference::renderer_outs(seq![Output::Kill { id }] + closes_of_tab(conns, tab)) == seq![Output::Kill { id }],
{
    let p = |x: Output| crate::noninterference::renderer_bound(x);
    lemma_renderer_outs_concat(seq![Output::Kill { id }], closes_of_tab(conns, tab));
    lemma_closes_not_renderer(conns, tab);
    reveal(Seq::filter);
    assert(seq![Output::Kill { id }].drop_last() =~= Seq::<Output>::empty());
    assert(Seq::<Output>::empty().filter(p) =~= Seq::<Output>::empty());
    assert(seq![Output::Kill { id }].last() == (Output::Kill { id }));
    assert(p(Output::Kill { id }));
    assert(seq![Output::Kill { id }].filter(p) =~= seq![Output::Kill { id }]);
    assert(seq![Output::Kill { id }] + Seq::<Output>::empty() =~= seq![Output::Kill { id }]);
}

/// The renderer in related states, found by tab, is the same one.
pub proof fn lemma_same_renderer_by_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, tab: nat)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        find_by_tab(s1.renderers, tab, 0) is Some,
    ensures
        find_by_tab(s2.renderers, tab, 0) is Some,
        s1.renderers[find_by_tab(s1.renderers, tab, 0)->Some_0] == s2.renderers[find_by_tab(s2.renderers, tab, 0)->Some_0],
{
    crate::unwind_base::lemma_found_contained(s1, tab);
    let i1 = find_by_tab(s1.renderers, tab, 0)->Some_0;
    let old = s1.renderers[i1];
    assert(s2.renderers.contains(old));
    crate::unwind_base::lemma_find_contained(urls, s2, old);
    crate::unwind_base::lemma_found_contained(s2, tab);
    let i2 = find_by_tab(s2.renderers, tab, 0)->Some_0;
    assert(s2.renderers[i2] == old);
}

/// `commit_navigation` from related states, for a tab open in the first.
pub proof fn lemma_commit_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, tab: nat, href: Seq<u32>, body: Seq<u8>)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        find_by_tab(s1.renderers, tab, 0) is Some,
    ensures
        crate::noninterference::renderer_outs(commit_navigation(urls, s1, tab, href, body).1) == crate::noninterference::renderer_outs(commit_navigation(urls, s2, tab, href, body).1),
        crate::noninterference::rel(rules, urls, d, commit_navigation(urls, s1, tab, href, body).0, commit_navigation(urls, s2, tab, href, body).0),
{
    let (m1, c1) = close_tab_conns(s1, tab);
    let (m2, c2) = close_tab_conns(s2, tab);
    lemma_rel_close_tab(rules, urls, d, s1, s2, tab);
    lemma_closes_not_renderer(s1.conns, tab);
    lemma_closes_not_renderer(s2.conns, tab);
    crate::net_theorems::lemma_without_tab_wf_conns(s1.conns, tab);
    crate::net_theorems::lemma_without_tab_wf_conns(s2.conns, tab);
    lemma_same_renderer_by_tab(rules, urls, d, s1, s2, tab);
    crate::invariant::lemma_find_by_tab(m1.renderers, tab, 0);
    crate::invariant::lemma_find_by_tab(m2.renderers, tab, 0);
    let i1 = find_by_tab(m1.renderers, tab, 0)->Some_0;
    let i2 = find_by_tab(m2.renderers, tab, 0)->Some_0;
    assert(m1.renderers[i1] == m2.renderers[i2]);
    if scalar_url(href) && lock_of_url(urls, href, m1.next_id) is Some {
        crate::unwinding::lemma_navigate_tab_consistency(rules, urls, d, m1, m2, tab, href, body);
        let o1 = navigate_tab(urls, m1, tab, href, body).1;
        let o2 = navigate_tab(urls, m2, tab, href, body).1;
        lemma_renderer_outs_concat(c1, o1);
        lemma_renderer_outs_concat(c2, o2);
    } else {
        crate::unwinding::lemma_fail_consistency(rules, urls, d, m1, m2, i1, i2, error_bad_url());
        let o1 = fail_navigation(m1, i1, m1.renderers[i1], error_bad_url()).1;
        let o2 = fail_navigation(m2, i2, m2.renderers[i2], error_bad_url()).1;
        lemma_renderer_outs_concat(c1, o1);
        lemma_renderer_outs_concat(c2, o2);
    }
}

/// `abort_navigation` from related states, for a tab open in the first.
pub proof fn lemma_abort_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, tab: nat, code: u64)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        find_by_tab(s1.renderers, tab, 0) is Some,
    ensures
        crate::noninterference::renderer_outs(abort_navigation(s1, tab, code).1) == crate::noninterference::renderer_outs(abort_navigation(s2, tab, code).1),
        crate::noninterference::rel(rules, urls, d, abort_navigation(s1, tab, code).0, abort_navigation(s2, tab, code).0),
{
    let (m1, c1) = close_tab_conns(s1, tab);
    let (m2, c2) = close_tab_conns(s2, tab);
    lemma_rel_close_tab(rules, urls, d, s1, s2, tab);
    lemma_closes_not_renderer(s1.conns, tab);
    lemma_closes_not_renderer(s2.conns, tab);
    crate::net_theorems::lemma_without_tab_wf_conns(s1.conns, tab);
    crate::net_theorems::lemma_without_tab_wf_conns(s2.conns, tab);
    lemma_same_renderer_by_tab(rules, urls, d, s1, s2, tab);
    crate::invariant::lemma_find_by_tab(m1.renderers, tab, 0);
    crate::invariant::lemma_find_by_tab(m2.renderers, tab, 0);
    let i1 = find_by_tab(m1.renderers, tab, 0)->Some_0;
    let i2 = find_by_tab(m2.renderers, tab, 0)->Some_0;
    assert(m1.renderers[i1] == m2.renderers[i2]);
    crate::unwinding::lemma_fail_consistency(rules, urls, d, m1, m2, i1, i2, code);
    let o1 = fail_navigation(m1, i1, m1.renderers[i1], code).1;
    let o2 = fail_navigation(m2, i2, m2.renderers[i2], code).1;
    lemma_renderer_outs_concat(c1, o1);
    lemma_renderer_outs_concat(c2, o2);
}

// ---------------------------------------------------------------------
// Carrying out the actions.
// ---------------------------------------------------------------------

/// `carry_out` from related states, for the same actions up to the octets of
/// their `Send`s, for a navigating tab open in the first.
pub proof fn lemma_carry_out_consistency(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    tab: nat,
    partition: crate::domain::Domain,
    cur: Option<nat>,
    a1: Seq<NetAction>,
    a2: Seq<NetAction>,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        find_by_tab(s1.renderers, tab, 0) is Some,
        crate::net_wf::tab_navigating(s1, tab, partition),
        crate::net_wf::tab_navigating(s2, tab, partition),
        clazel_fetch::transducer::contract::same_but_sends(a1, a2),
    ensures
        crate::noninterference::renderer_outs(carry_out(urls, s1, tab, partition, cur, a1).1) == crate::noninterference::renderer_outs(carry_out(urls, s2, tab, partition, cur, a2).1),
        crate::noninterference::rel(rules, urls, d, carry_out(urls, s1, tab, partition, cur, a1).0, carry_out(urls, s2, tab, partition, cur, a2).0),
    decreases a1.len(),
{
    if a1.len() > 0 {
        let r1 = a1.drop_first();
        let r2 = a2.drop_first();
        assert(clazel_fetch::transducer::contract::same_but_sends(r1, r2)) by {
            assert forall|k: int| 0 <= k < r1.len() implies ((#[trigger] r1[k]) is Send && r2[k] is Send) || r1[k] == r2[k] by {
                assert(r1[k] == a1[k + 1] && r2[k] == a2[k + 1]);
            }
        }
        assert((a1[0] is Send && a2[0] is Send) || a1[0] == a2[0]);
        match a1[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                assert(a2[0] == a1[0]);
                let ep = Endpoint { host, port, tls };
                let (sa1, id1, oa1) = open_connection(s1, tab, partition, ep);
                let (sa2, id2, oa2) = open_connection(s2, tab, partition, ep);
                let c = Connection { id: s1.next_conn, tab, endpoint: ep, partition };
                assert(s2.next_conn == s1.next_conn);
                lemma_rel_push_conn(rules, urls, d, s1, s2, c);
                assert(sa1.renderers == s1.renderers && sa2.renderers == s2.renderers);
                lemma_carry_out_consistency(rules, urls, d, sa1, sa2, tab, partition, Some(id1), r1, r2);
                let o1 = carry_out(urls, sa1, tab, partition, Some(id1), r1).1;
                let o2 = carry_out(urls, sa2, tab, partition, Some(id2), r2).1;
                lemma_renderer_outs_concat(oa1, o1);
                lemma_renderer_outs_concat(oa2, o2);
                assert(oa1 == oa2);
            },
            clazel_fetch::transducer::spec::Action::Send(b1) => {
                lemma_carry_out_consistency(rules, urls, d, s1, s2, tab, partition, cur, r1, r2);
                let o1 = carry_out(urls, s1, tab, partition, cur, r1).1;
                let o2 = carry_out(urls, s2, tab, partition, cur, r2).1;
                match cur {
                    Some(c) => {
                        assert(a2[0] is Send);
                        let b2 = a2[0]->Send_0;
                        lemma_renderer_outs_concat(seq![Output::Send { conn: c, bytes: b1 }], o1);
                        lemma_renderer_outs_concat(seq![Output::Send { conn: c, bytes: b2 }], o2);
                        lemma_renderer_outs_single(Output::Send { conn: c, bytes: b1 });
                        lemma_renderer_outs_single(Output::Send { conn: c, bytes: b2 });
                    },
                    None => {},
                }
            },
            clazel_fetch::transducer::spec::Action::Close => {
                assert(a2[0] == a1[0]);
                match cur {
                    Some(c) => {
                        lemma_rel_without_conn(rules, urls, d, s1, s2, c);
                        let sa1 = State { conns: without_conn(s1.conns, c), ..s1 };
                        let sa2 = State { conns: without_conn(s2.conns, c), ..s2 };
                        lemma_carry_out_consistency(rules, urls, d, sa1, sa2, tab, partition, None, r1, r2);
                        let o1 = carry_out(urls, sa1, tab, partition, None, r1).1;
                        let o2 = carry_out(urls, sa2, tab, partition, None, r2).1;
                        lemma_renderer_outs_concat(seq![Output::Close { conn: c }], o1);
                        lemma_renderer_outs_concat(seq![Output::Close { conn: c }], o2);
                        lemma_renderer_outs_single(Output::Close { conn: c });
                    },
                    None => {
                        lemma_carry_out_consistency(rules, urls, d, s1, s2, tab, partition, cur, r1, r2);
                    },
                }
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                assert(a2[0] == a1[0]);
                lemma_commit_consistency(rules, urls, d, s1, s2, tab, clazel_url::url::spec::url_serializer(url, false), response.body);
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                assert(a2[0] == a1[0]);
                lemma_abort_consistency(rules, urls, d, s1, s2, tab, error_fetch());
            },
        }
    }
}

// ---------------------------------------------------------------------
// Beginning a navigation and stepping it.
// ---------------------------------------------------------------------

/// `begin_navigation` from related states, for a tab open in the first: the
/// same renderer-bound outputs, and related states.
pub proof fn lemma_begin_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, tab: nat, url: Seq<u32>)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        find_by_tab(s1.renderers, tab, 0) is Some,
    ensures
        crate::noninterference::renderer_outs(begin_navigation(rules, urls, fetch, s1, tab, url).1) == crate::noninterference::renderer_outs(begin_navigation(rules, urls, fetch, s2, tab, url).1),
        crate::noninterference::rel(rules, urls, d, begin_navigation(rules, urls, fetch, s1, tab, url).0, begin_navigation(rules, urls, fetch, s2, tab, url).0),
{
    lemma_same_renderer_by_tab(rules, urls, d, s1, s2, tab);
    if lock_of_url(urls, url, s1.next_id) is Some {
        let (m1, c1) = close_tab_conns(s1, tab);
        let (m2, c2) = close_tab_conns(s2, tab);
        lemma_rel_close_tab(rules, urls, d, s1, s2, tab);
        lemma_closes_not_renderer(s1.conns, tab);
        lemma_closes_not_renderer(s2.conns, tab);
        crate::net_theorems::lemma_without_tab_wf_conns(s1.conns, tab);
        crate::net_theorems::lemma_without_tab_wf_conns(s2.conns, tab);
        crate::invariant::lemma_find_by_tab(m1.renderers, tab, 0);
        crate::invariant::lemma_find_by_tab(m2.renderers, tab, 0);
        let i1 = find_by_tab(m1.renderers, tab, 0)->Some_0;
        let i2 = find_by_tab(m2.renderers, tab, 0)->Some_0;
        let old = m1.renderers[i1];
        assert(old == m2.renderers[i2]);
        match (fetch.parse)(url) {
            None => {
                crate::unwinding::lemma_fail_consistency(rules, urls, d, m1, m2, i1, i2, error_bad_url());
                let o1 = fail_navigation(m1, i1, old, error_bad_url()).1;
                let o2 = fail_navigation(m2, i2, old, error_bad_url()).1;
                lemma_renderer_outs_concat(c1, o1);
                lemma_renderer_outs_concat(c2, o2);
            },
            Some(parsed) => {
                lemma_begin_started(rules, urls, d, m1, m2, tab, i1, i2, url, parsed);
                let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                let u1 = State { renderers: m1.renderers.update(i1, Renderer { pending: Some(nav), ..old }), ..m1 };
                let u2 = State { renderers: m2.renderers.update(i2, Renderer { pending: Some(nav), ..old }), ..m2 };
                let o1 = carry_out(urls, u1, tab, nav.partition, None, actions).1;
                let o2 = carry_out(urls, u2, tab, nav.partition, None, actions).1;
                lemma_renderer_outs_concat(c1, o1);
                lemma_renderer_outs_concat(c2, o2);
            },
        }
    }
}

/// `begin_navigation` after the connections are closed and the URL parsed: the
/// navigation is recorded and the transducer's first actions carried out.
pub proof fn lemma_begin_started(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    d: crate::domain::Domain,
    m1: State,
    m2: State,
    tab: nat,
    i1: int,
    i2: int,
    url: Seq<u32>,
    parsed: clazel_url::url::spec::Url,
)
    requires
        crate::noninterference::rel(rules, urls, d, m1, m2),
        0 <= i1 < m1.renderers.len(),
        0 <= i2 < m2.renderers.len(),
        m1.renderers[i1].tab == tab,
        m1.renderers[i1] == m2.renderers[i2],
        crate::invariant::no_tab_conns(m1.conns, tab),
        crate::invariant::no_tab_conns(m2.conns, tab),
    ensures
        ({
            let old = m1.renderers[i1];
            let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
            let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
            let u1 = State { renderers: m1.renderers.update(i1, Renderer { pending: Some(nav), ..old }), ..m1 };
            let u2 = State { renderers: m2.renderers.update(i2, Renderer { pending: Some(nav), ..old }), ..m2 };
            crate::noninterference::renderer_outs(carry_out(urls, u1, tab, nav.partition, None, actions).1) == crate::noninterference::renderer_outs(carry_out(urls, u2, tab, nav.partition, None, actions).1)
                && crate::noninterference::rel(rules, urls, d, carry_out(urls, u1, tab, nav.partition, None, actions).0, carry_out(urls, u2, tab, nav.partition, None, actions).0)
        }),
{
    let old = m1.renderers[i1];
    let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
    crate::net_theorems::lemma_start_shape(parsed);
    let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
    let r = Renderer { pending: Some(nav), ..old };
    let u1 = State { renderers: m1.renderers.update(i1, r), ..m1 };
    let u2 = State { renderers: m2.renderers.update(i2, r), ..m2 };
    crate::net_wf::lemma_begin_mid_wf(rules, urls, m1, i1, nav);
    crate::net_wf::lemma_begin_mid_wf(rules, urls, m2, i2, nav);
    assert(crate::unwinding::cookies_agree(rules, d, u1, u2));
    crate::unwinding::lemma_rel_after_update(rules, urls, d, m1, m2, i1, i2, r, u1, u2);
    assert(u1.renderers[i1] == r);
    assert(u2.renderers[i2] == r);
    assert(crate::net_wf::tab_navigating(u1, tab, nav.partition));
    assert(crate::net_wf::tab_navigating(u2, tab, nav.partition));
    crate::invariant::lemma_find_by_tab(u1.renderers, tab, 0);
    assert(find_by_tab(u1.renderers, tab, 0) is Some) by {
        assert(u1.renderers[i1].tab == tab);
    }
    assert(clazel_fetch::transducer::contract::same_but_sends(actions, actions)) by {
        assert forall|k: int| 0 <= k < actions.len() implies ((#[trigger] actions[k]) is Send && actions[k] is Send) || actions[k] == actions[k] by {}
    }
    lemma_carry_out_consistency(rules, urls, d, u1, u2, tab, nav.partition, None, actions, actions);
}

/// A connection of a well-formed table is found by its id.
pub proof fn lemma_find_conn_contains(rs: Seq<Renderer>, cs: Seq<Connection>, nc: nat, c: Connection)
    requires
        crate::invariant::conns_wf(rs, cs, nc),
        cs.contains(c),
    ensures
        find_conn(cs, c.id, 0) is Some,
        cs[find_conn(cs, c.id, 0)->Some_0] == c,
{
    crate::net_wf::lemma_find_conn(cs, c.id, 0);
    let j = choose|j: int| 0 <= j < cs.len() && cs[j] == c;
    assert(cs[j].id == c.id);
    let k = find_conn(cs, c.id, 0)->Some_0;
    assert(cs[k].id == cs[j].id);
}

/// A `Net` event from related states, for a connection open in the first:
/// the same renderer-bound outputs, and related states.
pub proof fn lemma_net_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, conn: nat, input: NetInput)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        net_target(s1, conn) is Some,
    ensures
        crate::noninterference::renderer_outs(net(rules, urls, fetch, s1, conn, input).1) == crate::noninterference::renderer_outs(net(rules, urls, fetch, s2, conn, input).1),
        crate::noninterference::rel(rules, urls, d, net(rules, urls, fetch, s1, conn, input).0, net(rules, urls, fetch, s2, conn, input).0),
{
    crate::net_wf::lemma_net_target(s1, conn);
    let (c, i1, nav) = net_target(s1, conn)->Some_0;
    // The second run has the same connection, renderer and navigation.
    assert(s2.conns.contains(c));
    lemma_find_conn_contains(s2.renderers, s2.conns, s2.next_conn, c);
    lemma_same_renderer_by_tab(rules, urls, d, s1, s2, c.tab);
    crate::invariant::lemma_find_by_tab(s2.renderers, c.tab, 0);
    let i2 = find_by_tab(s2.renderers, c.tab, 0)->Some_0;
    assert(s2.renderers[i2] == s1.renderers[i1]);
    assert(net_target(s2, conn) == Some((c, i2, nav)));
    // The transducer's step does not depend on the jar but in the octets sent.
    let (fs1, a1, ops1) = net_transducer_step(fetch, s1, nav, input);
    let (fs2, a2, ops2) = net_transducer_step(fetch, s2, nav, input);
    clazel_fetch::transducer::theorems::theorem_jar_only_in_sends(fetch.http, fetch.urls, nav.fetch, input, s1.jar, s2.jar, s1.now);
    assert(fs1 == fs2 && ops1 == ops2);
    crate::net_wf::lemma_net_mid_wf(rules, urls, fetch, s1, conn, input);
    crate::net_wf::lemma_net_mid_wf(rules, urls, fetch, s2, conn, input);
    let mid1 = crate::net_theorems::net_mid(rules, fetch, s1, conn, input, i1, nav);
    let mid2 = crate::net_theorems::net_mid(rules, fetch, s2, conn, input, i2, nav);
    // The connection the event reports dead is forgotten in both.
    let closed = input is Closed || input is Error;
    let sa1 = State { conns: if closed { without_conn(s1.conns, conn) } else { s1.conns }, ..s1 };
    let sa2 = State { conns: if closed { without_conn(s2.conns, conn) } else { s2.conns }, ..s2 };
    if closed {
        lemma_rel_without_conn(rules, urls, d, s1, s2, conn);
    }
    assert(crate::noninterference::rel(rules, urls, d, sa1, sa2));
    // The jars agree for `d` after the operations.
    clazel_fetch::transducer::theorems::theorem_ops_name_request(fetch.http, fetch.urls, nav.fetch, input, s1.jar, s1.now);
    assert(clazel_fetch::transducer::contract::ops_at(ops1, s1.now)) by {
        assert forall|k: int| 0 <= k < ops1.len() implies clazel_fetch::transducer::contract::op_now(#[trigger] ops1[k]) == s1.now by {
            match ops1[k] {
                clazel_fetch::transducer::spec::JarOp::Retrieved { now, .. } => {},
                clazel_fetch::transducer::spec::JarOp::Stored { now, .. } => {},
            }
        }
    }
    if let crate::domain::Domain::Root(root) = d {
        crate::store_projection::lemma_apply_net_ops_agree(rules, s1.jar, s2.jar, ops1, s1.now, root);
    }
    assert(crate::unwinding::cookies_agree(rules, d, mid1, mid2));
    crate::unwinding::lemma_rel_after_update(rules, urls, d, sa1, sa2, i1, i2, Renderer { pending: Some(Navigation { fetch: fs1, ..nav }), ..s1.renderers[i1] }, mid1, mid2);
    assert(crate::net_wf::tab_navigating(mid1, c.tab, nav.partition));
    assert(crate::net_wf::tab_navigating(mid2, c.tab, nav.partition));
    lemma_tab_open_iff(mid1.renderers, c.tab);
    assert(find_by_tab(mid1.renderers, c.tab, 0) is Some) by {
        assert(mid1.renderers[i1].tab == c.tab);
        crate::invariant::lemma_find_by_tab(mid1.renderers, c.tab, 0);
    }
    lemma_carry_out_consistency(rules, urls, d, mid1, mid2, c.tab, nav.partition, Some(conn), a1, a2);
}

} // verus!

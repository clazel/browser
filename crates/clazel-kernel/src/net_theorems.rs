//! Item 3.7: the theorems about the kernel's stepping of the fetch. Each
//! `theorem_*` has the statement of `statements.rs` of the same name as its
//! `ensures`; the lemmas are the induction over the transducer's actions
//! (`carry_out`), which is generic: it never unfolds the transducer.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The table holds a connection with id `x` of `tab`.
pub open spec fn owned_in(cs: Seq<Connection>, tab: nat, x: nat) -> bool {
    exists|j: int| 0 <= j < cs.len() && (#[trigger] cs[j]).id == x && cs[j].tab == tab
}

/// Every `Close` of `closes_of_tab` is for a connection of the tab.
pub proof fn lemma_closes_of_tab(conns: Seq<Connection>, tab: nat)
    ensures
        forall|k: int|
            0 <= k < closes_of_tab(conns, tab).len() ==> match #[trigger] closes_of_tab(conns, tab)[k] {
                Output::Close { conn: x } => owned_in(conns, tab, x),
                _ => false,
            },
    decreases conns.len(),
{
    if conns.len() > 0 {
        let rest = conns.drop_first();
        lemma_closes_of_tab(rest, tab);
        let first = if conns[0].tab == tab {
            seq![Output::Close { conn: conns[0].id }]
        } else {
            seq![]
        };
        assert forall|k: int| 0 <= k < closes_of_tab(conns, tab).len() implies match #[trigger] closes_of_tab(conns, tab)[k] {
            Output::Close { conn: x } => owned_in(conns, tab, x),
            _ => false,
        } by {
            assert(closes_of_tab(conns, tab) == first + closes_of_tab(rest, tab));
            if k < first.len() {
                assert(closes_of_tab(conns, tab)[k] == first[k]);
                assert(conns[0].id == conns[0].id && conns[0].tab == tab);
            } else {
                let k2 = k - first.len();
                assert(closes_of_tab(conns, tab)[k] == closes_of_tab(rest, tab)[k2]);
                match closes_of_tab(rest, tab)[k2] {
                    Output::Close { conn: x } => {
                        let j = choose|j: int| 0 <= j < rest.len() && rest[j].id == x && rest[j].tab == tab;
                        assert(conns[j + 1] == rest[j]);
                    },
                    _ => {},
                }
            }
        }
    }
}

/// What `carry_out` does to the connection table and the connection
/// outputs, for any actions: the connections it adds belong to the navigating
/// tab and carry its partition key, the others are those it had (minus the
/// ones closed), and its `Connect`, `Send` and `Close` name connections of
/// that tab, the event's (`cur`) or new.
pub proof fn lemma_carry_out_conns(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    ensures
        ({
            let (s1, out) = carry_out(urls, s, tab, partition, cur, actions);
            &&& s.next_conn <= s1.next_conn
            &&& forall|j: int|
                0 <= j < s1.conns.len() ==> s.conns.contains(#[trigger] s1.conns[j]) || (s.next_conn <= s1.conns[j].id < s1.next_conn && s1.conns[j].tab == tab
                    && s1.conns[j].partition == partition)
            &&& forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                    Output::Send { conn: x, .. } => cur == Some(x) || (s.next_conn <= x < s1.next_conn),
                    Output::Close { conn: x } => cur == Some(x) || owned_in(s.conns, tab, x) || (s.next_conn <= x < s1.next_conn),
                    _ => true,
                }
        }),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        let (s1, out) = carry_out(urls, s, tab, partition, cur, actions);
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let ep = Endpoint { host, port, tls };
                let (sa, id, out_a) = open_connection(s, tab, partition, ep);
                lemma_carry_out_conns(urls, sa, tab, partition, Some(id), rest);
                let (s2, out2) = carry_out(urls, sa, tab, partition, Some(id), rest);
                assert(sa.conns == s.conns.push(Connection { id: s.next_conn, tab, endpoint: ep, partition }));
                assert(sa.next_conn == s.next_conn + 1);
                assert forall|j: int| 0 <= j < s1.conns.len() implies s.conns.contains(#[trigger] s1.conns[j]) || (s.next_conn <= s1.conns[j].id < s1.next_conn && s1.conns[j].tab == tab
                    && s1.conns[j].partition == partition) by {
                    if sa.conns.contains(s1.conns[j]) {
                        let m = choose|m: int| 0 <= m < sa.conns.len() && sa.conns[m] == s1.conns[j];
                        if m < s.conns.len() {
                            assert(s.conns.contains(s.conns[m]));
                            assert(sa.conns[m] == s.conns[m]);
                        } else {
                            assert(sa.conns[m].id == s.next_conn);
                        }
                    }
                }
                assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                    Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                    Output::Send { conn: x, .. } => cur == Some(x) || (s.next_conn <= x < s1.next_conn),
                    Output::Close { conn: x } => cur == Some(x) || owned_in(s.conns, tab, x) || (s.next_conn <= x < s1.next_conn),
                    _ => true,
                } by {
                    assert(out == out_a + out2);
                    if k < out_a.len() {
                        assert(out[k] == out_a[k]);
                    } else {
                        assert(out[k] == out2[k - out_a.len()]);
                        match out2[k - out_a.len()] {
                            Output::Close { conn: x } => {
                                if owned_in(sa.conns, tab, x) {
                                    let m = choose|m: int| 0 <= m < sa.conns.len() && sa.conns[m].id == x && sa.conns[m].tab == tab;
                                    if m < s.conns.len() {
                                        assert(sa.conns[m] == s.conns[m]);
                                    }
                                }
                            },
                            _ => {},
                        }
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_conns(urls, s, tab, partition, cur, rest);
                let (s2, out2) = carry_out(urls, s, tab, partition, cur, rest);
                match cur {
                    Some(c) => {
                        assert(out == seq![Output::Send { conn: c, bytes }] + out2);
                        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                            Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                            Output::Send { conn: x, .. } => cur == Some(x) || (s.next_conn <= x < s1.next_conn),
                            Output::Close { conn: x } => cur == Some(x) || owned_in(s.conns, tab, x) || (s.next_conn <= x < s1.next_conn),
                            _ => true,
                        } by {
                            if k > 0 {
                                assert(out[k] == out2[k - 1]);
                            }
                        }
                    },
                    None => {},
                }
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    let sa = State { conns: without_conn(s.conns, c), ..s };
                    lemma_carry_out_conns(urls, sa, tab, partition, None, rest);
                    let (s2, out2) = carry_out(urls, sa, tab, partition, None, rest);
                    assert(out == seq![Output::Close { conn: c }] + out2);
                    assert forall|j: int| 0 <= j < s1.conns.len() implies s.conns.contains(#[trigger] s1.conns[j]) || (s.next_conn <= s1.conns[j].id < s1.next_conn && s1.conns[j].tab == tab
                        && s1.conns[j].partition == partition) by {
                        if sa.conns.contains(s1.conns[j]) {
                            clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |x: Connection| x.id != c, s1.conns[j]);
                        }
                    }
                    assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                        Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                        Output::Send { conn: x, .. } => cur == Some(x) || (s.next_conn <= x < s1.next_conn),
                        Output::Close { conn: x } => cur == Some(x) || owned_in(s.conns, tab, x) || (s.next_conn <= x < s1.next_conn),
                        _ => true,
                    } by {
                        if k > 0 {
                            assert(out[k] == out2[k - 1]);
                            match out2[k - 1] {
                                Output::Close { conn: x } => {
                                    if owned_in(sa.conns, tab, x) {
                                        let m = choose|m: int| 0 <= m < sa.conns.len() && sa.conns[m].id == x && sa.conns[m].tab == tab;
                                        assert(sa.conns.contains(sa.conns[m]));
                                        clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |y: Connection| y.id != c, sa.conns[m]);
                                    }
                                },
                                _ => {},
                            }
                        }
                    }
                },
                None => {
                    lemma_carry_out_conns(urls, s, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                lemma_commit_conns(urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response));
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                lemma_abort_conns(s, tab, error_fetch());
            },
        }
    }
}

/// `commit_navigation` keeps a subset of the connections (those of other
/// tabs) and opens none; its `Close`s are for connections of the tab.
pub proof fn lemma_commit_conns(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Document)
    ensures
        ({
            let (s1, out) = commit_navigation(urls, s, tab, href, body);
            &&& s1.next_conn == s.next_conn
            &&& forall|j: int| 0 <= j < s1.conns.len() ==> s.conns.contains(#[trigger] s1.conns[j])
            &&& forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::Connect { .. } | Output::Send { .. } => false,
                    Output::Close { conn: x } => owned_in(s.conns, tab, x),
                    _ => true,
                }
        }),
{
    let (s0, closes) = close_tab_conns(s, tab);
    lemma_closes_of_tab(s.conns, tab);
    assert forall|j: int| 0 <= j < s0.conns.len() implies s.conns.contains(#[trigger] s0.conns[j]) by {
        assert(s0.conns.contains(s0.conns[j]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |c: Connection| c.tab != tab, s0.conns[j]);
    }
    crate::invariant::lemma_find_by_tab(s0.renderers, tab, 0);
    if let Some(i) = find_by_tab(s0.renderers, tab, 0) {
        let (s2, out) = if scalar_url(href) && lock_of_url(urls, href, s0.next_id) is Some {
            navigate_tab(urls, s0, tab, href, body)
        } else {
            fail_navigation(s0, i, s0.renderers[i], error_bad_url())
        };
        let all = closes + out;
        assert forall|k: int| 0 <= k < all.len() implies match #[trigger] all[k] {
            Output::Connect { .. } | Output::Send { .. } => false,
            Output::Close { conn: x } => owned_in(s.conns, tab, x),
            _ => true,
        } by {
            if k >= closes.len() {
                assert(all[k] == out[k - closes.len()]);
                lemma_nav_out_not_conn(urls, s0, tab, href, body, i);
            } else {
                assert(all[k] == closes[k]);
            }
        }
    }
}

/// The outputs of the commit or the failure that follows are not about
/// connections.
pub proof fn lemma_nav_out_not_conn(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Document, i: int)
    requires
        0 <= i < s.renderers.len(),
    ensures
        forall|k: int|
            0 <= k < navigate_tab(urls, s, tab, href, body).1.len() ==> match #[trigger] navigate_tab(urls, s, tab, href, body).1[k] {
                Output::Connect { .. } | Output::Send { .. } | Output::Close { .. } => false,
                _ => true,
            },
        forall|code: u64, k: int|
            0 <= k < fail_navigation(s, i, s.renderers[i], code).1.len() ==> match #[trigger] fail_navigation(s, i, s.renderers[i], code).1[k] {
                Output::Connect { .. } | Output::Send { .. } | Output::Close { .. } => false,
                _ => true,
            },
{
}

/// `abort_navigation`, likewise.
pub proof fn lemma_abort_conns(s: State, tab: nat, code: u64)
    ensures
        ({
            let (s1, out) = abort_navigation(s, tab, code);
            &&& s1.next_conn == s.next_conn
            &&& forall|j: int| 0 <= j < s1.conns.len() ==> s.conns.contains(#[trigger] s1.conns[j])
            &&& forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::Connect { .. } | Output::Send { .. } => false,
                    Output::Close { conn: x } => owned_in(s.conns, tab, x),
                    _ => true,
                }
        }),
{
    let (s0, closes) = close_tab_conns(s, tab);
    lemma_closes_of_tab(s.conns, tab);
    assert forall|j: int| 0 <= j < s0.conns.len() implies s.conns.contains(#[trigger] s0.conns[j]) by {
        assert(s0.conns.contains(s0.conns[j]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |c: Connection| c.tab != tab, s0.conns[j]);
    }
    if let Some(i) = find_by_tab(s0.renderers, tab, 0) {
        let (s2, out) = fail_navigation(s0, i, s0.renderers[i], code);
        let all = closes + out;
        assert forall|k: int| 0 <= k < all.len() implies match #[trigger] all[k] {
            Output::Connect { .. } | Output::Send { .. } => false,
            Output::Close { conn: x } => owned_in(s.conns, tab, x),
            _ => true,
        } by {
            if k >= closes.len() {
                assert(all[k] == out[k - closes.len()]);
            } else {
                assert(all[k] == closes[k]);
            }
        }
    }
}

/// Every renderer-bound output of `carry_out` is for the navigating tab's
/// renderer (a reply, a `Kill`), or for the renderer a commit spawns.
pub proof fn lemma_carry_out_renderer_outputs(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let (s1, out) = carry_out(urls, s, tab, partition, cur, actions);
            forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x) || (x == s.next_id && out.contains(
                        Output::Spawn { id: x, policy: Policy::Renderer },
                    )),
                    Output::Spawn { id: x, .. } => x == s.next_id,
                    Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                    Output::Show { .. } => false,
                    _ => true,
                }
        }),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        let (s1, out) = carry_out(urls, s, tab, partition, cur, actions);
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let (sa, id, out_a) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                lemma_carry_out_renderer_outputs(urls, sa, tab, partition, Some(id), rest);
                let out2 = carry_out(urls, sa, tab, partition, Some(id), rest).1;
                assert(out == out_a + out2);
                assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                    Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x) || (x == s.next_id && out.contains(
                        Output::Spawn { id: x, policy: Policy::Renderer },
                    )),
                    Output::Spawn { id: x, .. } => x == s.next_id,
                    Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                    _ => true,
                } by {
                    if k >= out_a.len() {
                        assert(out[k] == out2[k - out_a.len()]);
                        if out2.contains(Output::Spawn { id: s.next_id, policy: Policy::Renderer }) {
                            let m = choose|m: int| 0 <= m < out2.len() && out2[m] == (Output::Spawn { id: s.next_id, policy: Policy::Renderer });
                            assert(out[m + out_a.len()] == out2[m]);
                        }
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_renderer_outputs(urls, s, tab, partition, cur, rest);
                let out2 = carry_out(urls, s, tab, partition, cur, rest).1;
                match cur {
                    Some(c) => {
                        assert(out == seq![Output::Send { conn: c, bytes }] + out2);
                        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                            Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x) || (x == s.next_id && out.contains(
                                Output::Spawn { id: x, policy: Policy::Renderer },
                            )),
                            Output::Spawn { id: x, .. } => x == s.next_id,
                            Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                            _ => true,
                        } by {
                            if k > 0 {
                                assert(out[k] == out2[k - 1]);
                                if out2.contains(Output::Spawn { id: s.next_id, policy: Policy::Renderer }) {
                                    let m = choose|m: int| 0 <= m < out2.len() && out2[m] == (Output::Spawn { id: s.next_id, policy: Policy::Renderer });
                                    assert(out[m + 1] == out2[m]);
                                }
                            }
                        }
                    },
                    None => {},
                }
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    let sa = State { conns: without_conn(s.conns, c), ..s };
                    lemma_carry_out_renderer_outputs(urls, sa, tab, partition, None, rest);
                    let out2 = carry_out(urls, sa, tab, partition, None, rest).1;
                    assert(out == seq![Output::Close { conn: c }] + out2);
                    assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                        Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x) || (x == s.next_id && out.contains(
                            Output::Spawn { id: x, policy: Policy::Renderer },
                        )),
                        Output::Spawn { id: x, .. } => x == s.next_id,
                        Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                        _ => true,
                    } by {
                        if k > 0 {
                            assert(out[k] == out2[k - 1]);
                            if out2.contains(Output::Spawn { id: s.next_id, policy: Policy::Renderer }) {
                                let m = choose|m: int| 0 <= m < out2.len() && out2[m] == (Output::Spawn { id: s.next_id, policy: Policy::Renderer });
                                assert(out[m + 1] == out2[m]);
                            }
                        }
                    }
                },
                None => {
                    lemma_carry_out_renderer_outputs(urls, s, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                lemma_commit_renderer_outputs(urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response));
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                lemma_abort_renderer_outputs(urls, s, tab, error_fetch());
            },
        }
    }
}

/// The renderer-bound outputs of `commit_navigation`.
pub proof fn lemma_commit_renderer_outputs(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Document)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let out = commit_navigation(urls, s, tab, href, body).1;
            forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x) || (x == s.next_id && out.contains(
                        Output::Spawn { id: x, policy: Policy::Renderer },
                    )),
                    Output::Spawn { id: x, .. } => x == s.next_id,
                    Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                    Output::Show { .. } => false,
                    _ => true,
                }
        }),
{
    let (s0, closes) = close_tab_conns(s, tab);
    assert(s0.renderers == s.renderers && s0.next_id == s.next_id);
    lemma_closes_of_tab(s.conns, tab);
    crate::invariant::lemma_find_by_tab(s0.renderers, tab, 0);
    if let Some(i) = find_by_tab(s0.renderers, tab, 0) {
        let all = commit_navigation(urls, s, tab, href, body).1;
        if scalar_url(href) && lock_of_url(urls, href, s0.next_id) is Some {
            crate::theorems::lemma_navigate_tab_outputs(urls, s0, tab, href, body);
            let out = navigate_tab(urls, s0, tab, href, body).1;
            assert(all == closes + out);
            assert forall|k: int| 0 <= k < all.len() implies match #[trigger] all[k] {
                Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x) || (x == s.next_id && all.contains(
                    Output::Spawn { id: x, policy: Policy::Renderer },
                )),
                Output::Spawn { id: x, .. } => x == s.next_id,
                Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                _ => true,
            } by {
                if k >= closes.len() {
                    assert(all[k] == out[k - closes.len()]);
                    if out.contains(Output::Spawn { id: s.next_id, policy: Policy::Renderer }) {
                        let m = choose|m: int| 0 <= m < out.len() && out[m] == (Output::Spawn { id: s.next_id, policy: Policy::Renderer });
                        assert(all[m + closes.len()] == out[m]);
                    }
                } else {
                    assert(all[k] == closes[k]);
                }
            }
        } else {
            let out = fail_navigation(s0, i, s0.renderers[i], error_bad_url()).1;
            assert(all == closes + out);
            assert forall|k: int| 0 <= k < all.len() implies match #[trigger] all[k] {
                Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x),
                Output::Spawn { id: x, .. } => x == s.next_id,
                Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                _ => true,
            } by {
                if k >= closes.len() {
                    assert(all[k] == out[k - closes.len()]);
                    assert(s.renderers[i].tab == tab && s.renderers[i].id == s.renderers[i].id);
                    assert(s.renderers[i] == s0.renderers[i]);
                } else {
                    assert(all[k] == closes[k]);
                }
            }
        }
    }
}

/// The renderer-bound outputs of `abort_navigation`.
pub proof fn lemma_abort_renderer_outputs(urls: UrlFns, s: State, tab: nat, code: u64)
    ensures
        ({
            let out = abort_navigation(s, tab, code).1;
            forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x),
                    Output::Spawn { .. } => false,
                    Output::Kill { .. } => false,
                    Output::Show { .. } => false,
                    _ => true,
                }
        }),
{
    let (s0, closes) = close_tab_conns(s, tab);
    assert(s0.renderers == s.renderers);
    lemma_closes_of_tab(s.conns, tab);
    crate::invariant::lemma_find_by_tab(s0.renderers, tab, 0);
    if let Some(i) = find_by_tab(s0.renderers, tab, 0) {
        let out = fail_navigation(s0, i, s0.renderers[i], code).1;
        let all = closes + out;
        assert forall|k: int| 0 <= k < all.len() implies match #[trigger] all[k] {
            Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x),
            Output::Spawn { .. } => false,
            Output::Kill { .. } => false,
            _ => true,
        } by {
            if k >= closes.len() {
                assert(all[k] == out[k - closes.len()]);
                assert(s.renderers[i].tab == tab);
            } else {
                assert(all[k] == closes[k]);
            }
        }
    }
}

/// A `carry_out` whose actions include `Done` or `Fail` ends the navigation:
/// no renderer of the tab is navigating, and the tab has no connection.
pub proof fn lemma_carry_out_terminal(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
        exists|a: int| 0 <= a < actions.len() && ((#[trigger] actions[a]) is Done || actions[a] is Fail),
    ensures
        ({
            let s1 = carry_out(urls, s, tab, partition, cur, actions).0;
            &&& forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab ==> s1.renderers[j].pending is None
            &&& crate::invariant::no_tab_conns(s1.conns, tab)
        }),
    decreases actions.len(),
{
    let rest = actions.drop_first();
    let a = choose|a: int| 0 <= a < actions.len() && (actions[a] is Done || actions[a] is Fail);
    match actions[0] {
        clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
            let (sa, id, out_a) = open_connection(s, tab, partition, Endpoint { host, port, tls });
            assert(rest[a - 1] == actions[a]);
            lemma_carry_out_terminal(urls, sa, tab, partition, Some(id), rest);
        },
        clazel_fetch::transducer::spec::Action::Send(bytes) => {
            assert(rest[a - 1] == actions[a]);
            lemma_carry_out_terminal(urls, s, tab, partition, cur, rest);
        },
        clazel_fetch::transducer::spec::Action::Close => match cur {
            Some(c) => {
                assert(rest[a - 1] == actions[a]);
                lemma_carry_out_terminal(urls, State { conns: without_conn(s.conns, c), ..s }, tab, partition, None, rest);
            },
            None => {
                assert(rest[a - 1] == actions[a]);
                lemma_carry_out_terminal(urls, s, tab, partition, cur, rest);
            },
        },
        clazel_fetch::transducer::spec::Action::Done { url, response } => {
            lemma_commit_terminal(urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response));
        },
        clazel_fetch::transducer::spec::Action::Fail(_) => {
            lemma_abort_terminal(urls, s, tab, error_fetch());
        },
    }
}

/// A commit leaves no renderer of the tab navigating and no connection.
pub proof fn lemma_commit_terminal(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Document)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = commit_navigation(urls, s, tab, href, body).0;
            &&& forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab ==> s1.renderers[j].pending is None
            &&& crate::invariant::no_tab_conns(s1.conns, tab)
        }),
{
    let s0 = close_tab_conns(s, tab).0;
    lemma_without_tab_wf_conns(s.conns, tab);
    crate::invariant::lemma_find_by_tab(s0.renderers, tab, 0);
    if let Some(i) = find_by_tab(s0.renderers, tab, 0) {
        if scalar_url(href) && lock_of_url(urls, href, s0.next_id) is Some {
            assert(s0.next_id == s.next_id);
            lemma_navigate_tab_pending(urls, s0, tab, href, body, i);
        } else {
            lemma_fail_pending(urls, s0, tab, i, error_bad_url());
        }
    }
}

/// An abort leaves no renderer of the tab navigating and no connection.
pub proof fn lemma_abort_terminal(urls: UrlFns, s: State, tab: nat, code: u64)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = abort_navigation(s, tab, code).0;
            &&& forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab ==> s1.renderers[j].pending is None
            &&& crate::invariant::no_tab_conns(s1.conns, tab)
        }),
{
    let s0 = close_tab_conns(s, tab).0;
    lemma_without_tab_wf_conns(s.conns, tab);
    crate::invariant::lemma_find_by_tab(s0.renderers, tab, 0);
    if let Some(i) = find_by_tab(s0.renderers, tab, 0) {
        lemma_fail_pending(urls, s0, tab, i, code);
    }
}

/// `without_tab` holds no connection of the tab.
pub proof fn lemma_without_tab_wf_conns(cs: Seq<Connection>, tab: nat)
    ensures
        crate::invariant::no_tab_conns(without_tab(cs, tab), tab),
{
    let t = without_tab(cs, tab);
    assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).tab != tab by {
        assert(t.contains(t[k]));
        clazel_cookie::storage::isolation::lemma_filter_elem(cs, |c: Connection| c.tab != tab, t[k]);
    }
}

/// After `navigate_tab` at index `i`, every renderer of the tab is not navigating.
pub proof fn lemma_navigate_tab_pending(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Document, i: int)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        0 <= i < s.renderers.len(),
        lock_of_url(urls, href, s.next_id) is Some,
    ensures
        ({
            let s1 = navigate_tab(urls, s, tab, href, body).0;
            forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab ==> s1.renderers[j].pending is None
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    let s1 = navigate_tab(urls, s, tab, href, body).0;
    assert forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab implies s1.renderers[j].pending is None by {
        if j != i {
            assert(s1.renderers[j] == s.renderers[j]);
            crate::theorems::tab_unique(urls, s, i, j);
        }
    }
}

/// After `fail_navigation` at index `i`, every renderer of the tab is not navigating.
pub proof fn lemma_fail_pending(urls: UrlFns, s: State, tab: nat, i: int, code: u64)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        0 <= i < s.renderers.len(),
    ensures
        ({
            let s1 = fail_navigation(s, i, s.renderers[i], code).0;
            forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab ==> s1.renderers[j].pending is None
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    let s1 = fail_navigation(s, i, s.renderers[i], code).0;
    assert forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab implies s1.renderers[j].pending is None by {
        if j != i {
            assert(s1.renderers[j] == s.renderers[j]);
            crate::theorems::tab_unique(urls, s, i, j);
        }
    }
}

// ---------------------------------------------------------------------
// `begin_navigation`.
// ---------------------------------------------------------------------

/// `start` gives a `Connect` or a `Fail`: it never commits, and sends nothing.
pub proof fn lemma_start_shape(url: clazel_url::url::spec::Url)
    ensures
        ({
            let a = clazel_fetch::transducer::spec::start(url).1;
            (a.len() == 1 && a[0] is Connect) || (a.len() == 1 && a[0] is Fail)
        }),
{
}

/// What `begin_navigation` does to the connections and its outputs (for a
/// well-formed renderer table): it closes the tab's connections, opens at most
/// one for the tab, and replies to the tab's renderer on a failure; it spawns
/// and kills nothing and sends nothing.
pub proof fn lemma_begin_outputs(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let (s1, out) = begin_navigation(rules, urls, fetch, s, tab, url);
            &&& s.next_conn <= s1.next_conn
            &&& forall|j: int|
                0 <= j < s1.conns.len() ==> s.conns.contains(#[trigger] s1.conns[j]) || (s.next_conn <= s1.conns[j].id < s1.next_conn && s1.conns[j].tab == tab)
            &&& forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::ToRenderer { id: x, .. } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                    Output::Spawn { .. } => false,
                    Output::Kill { .. } => false,
                    Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                    Output::Send { .. } => false,
                    Output::Show { .. } => false,
                    Output::Close { conn: x } => owned_in(s.conns, tab, x),
                }
            &&& s1.next_id == s.next_id
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if lock_of_url(urls, url, s.next_id) is Some {
            let (s0, closes) = close_tab_conns(s, tab);
            assert(s0.renderers == s.renderers);
            lemma_closes_of_tab(s.conns, tab);
            lemma_without_tab_wf_conns(s.conns, tab);
            let old = s0.renderers[i];
            assert forall|j: int| 0 <= j < s0.conns.len() implies s.conns.contains(#[trigger] s0.conns[j]) by {
                assert(s0.conns.contains(s0.conns[j]));
                clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |c: Connection| c.tab != tab, s0.conns[j]);
            }
            match (fetch.parse)(url) {
                None => {
                    let (s1, out) = fail_navigation(s0, i, old, error_bad_url());
                    assert(begin_navigation(rules, urls, fetch, s, tab, url) == (s1, closes + out));
                    let all = closes + out;
                    assert forall|j: int| 0 <= j < s1.conns.len() implies s.conns.contains(#[trigger] s1.conns[j]) || (s.next_conn <= s1.conns[j].id < s1.next_conn && s1.conns[j].tab == tab) by {
                        assert(s1.conns == s0.conns);
                        assert(s0.conns.contains(s0.conns[j]));
                    }
                    assert forall|k: int| 0 <= k < all.len() implies match #[trigger] all[k] {
                        Output::ToRenderer { id: x, .. } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                        Output::Spawn { .. } => false,
                        Output::Kill { .. } => false,
                        Output::Connect { .. } => false,
                        Output::Send { .. } => false,
                        Output::Show { .. } => false,
                        Output::Close { conn: x } => owned_in(s.conns, tab, x),
                    } by {
                        if k >= closes.len() {
                            assert(all[k] == out[k - closes.len()]);
                            assert(s.renderers[i].tab == tab);
                        } else {
                            assert(all[k] == closes[k]);
                        }
                    }
                },
                Some(parsed) => {
                    let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                    lemma_start_shape(parsed);
                    let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                    let s1 = State { renderers: s0.renderers.update(i, Renderer { pending: Some(nav), ..old }), ..s0 };
                    let (s2, out) = carry_out(urls, s1, tab, nav.partition, None, actions);
                    let all = closes + out;
                    assert(begin_navigation(rules, urls, fetch, s, tab, url) == (s2, all));
                    assert(actions.drop_first() =~= Seq::<NetAction>::empty());
                    if actions[0] is Fail {
                        lemma_abort_conns(s1, tab, error_fetch());
                        lemma_abort_renderer_outputs(urls, s1, tab, error_fetch());
                        assert(out == abort_navigation(s1, tab, error_fetch()).1);
                        assert(s1.conns == s0.conns);
                        assert forall|k: int| 0 <= k < all.len() implies match #[trigger] all[k] {
                            Output::ToRenderer { id: x, .. } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                            Output::Spawn { .. } => false,
                            Output::Kill { .. } => false,
                            Output::Connect { .. } => false,
                            Output::Send { .. } => false,
                            Output::Show { .. } => false,
                            Output::Close { conn: x } => owned_in(s.conns, tab, x),
                        } by {
                            if k >= closes.len() {
                                assert(all[k] == out[k - closes.len()]);
                                match out[k - closes.len()] {
                                    Output::Close { conn: x } => {
                                        assert(owned_in(s0.conns, tab, x));
                                        let m = choose|m: int| 0 <= m < s0.conns.len() && s0.conns[m].id == x && s0.conns[m].tab == tab;
                                        assert(s0.conns[m].tab != tab);
                                    },
                                    _ => {},
                                }
                                assert(s.renderers[i].tab == tab);
                            } else {
                                assert(all[k] == closes[k]);
                            }
                        }
                        assert forall|j: int| 0 <= j < s2.conns.len() implies s.conns.contains(#[trigger] s2.conns[j]) || (s.next_conn <= s2.conns[j].id < s2.next_conn
                            && s2.conns[j].tab == tab) by {
                            assert(s0.conns.contains(s2.conns[j]));
                            let m = choose|m: int| 0 <= m < s0.conns.len() && s0.conns[m] == s2.conns[j];
                        }
                    } else {
                        let ep = Endpoint { host: actions[0]->Connect_host, port: actions[0]->Connect_port, tls: actions[0]->Connect_tls };
                        let (sa, id, out_a) = open_connection(s1, tab, nav.partition, ep);
                        assert(carry_out(urls, sa, tab, nav.partition, Some(id), Seq::<NetAction>::empty()) == (sa, Seq::<Output>::empty()));
                        assert(out =~= out_a + Seq::<Output>::empty());
                        assert(out_a + Seq::<Output>::empty() =~= out_a);
                        assert(s2 == sa);
                        assert forall|k: int| 0 <= k < all.len() implies match #[trigger] all[k] {
                            Output::ToRenderer { id: x, .. } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                            Output::Spawn { .. } => false,
                            Output::Kill { .. } => false,
                            Output::Connect { conn: x, .. } => s.next_conn <= x < s2.next_conn,
                            Output::Send { .. } => false,
                            Output::Show { .. } => false,
                            Output::Close { conn: x } => owned_in(s.conns, tab, x),
                        } by {
                            if k >= closes.len() {
                                assert(all[k] == out[k - closes.len()]);
                            } else {
                                assert(all[k] == closes[k]);
                            }
                        }
                        assert forall|j: int| 0 <= j < s2.conns.len() implies s.conns.contains(#[trigger] s2.conns[j]) || (s.next_conn <= s2.conns[j].id < s2.next_conn
                            && s2.conns[j].tab == tab) by {
                            assert(s2.conns == s0.conns.push(Connection { id: s.next_conn, tab, endpoint: ep, partition: nav.partition }));
                            if j < s0.conns.len() {
                                assert(s2.conns[j] == s0.conns[j]);
                                assert(s0.conns.contains(s0.conns[j]));
                            }
                        }
                    }
                },
            }
        }
    }
}

// ---------------------------------------------------------------------
// The statements of `Net` events.
// ---------------------------------------------------------------------

/// Every `Send` output of `carry_out` carries the octets of a `Send` action.
pub proof fn lemma_carry_out_sends(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    ensures
        ({
            let out = carry_out(urls, s, tab, partition, cur, actions).1;
            forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::Send { bytes, .. } => exists|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(bytes),
                    _ => true,
                }
        }),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        let out = carry_out(urls, s, tab, partition, cur, actions).1;
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let (sa, id, out_a) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                lemma_carry_out_sends(urls, sa, tab, partition, Some(id), rest);
                let out2 = carry_out(urls, sa, tab, partition, Some(id), rest).1;
                assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                    Output::Send { bytes, .. } => exists|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(bytes),
                    _ => true,
                } by {
                    if k >= out_a.len() {
                        assert(out[k] == out2[k - out_a.len()]);
                        if let Output::Send { bytes, .. } = out[k] {
                            let a = choose|a: int| 0 <= a < rest.len() && rest[a] == clazel_fetch::transducer::spec::Action::Send(bytes);
                            assert(actions[a + 1] == rest[a]);
                        }
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_sends(urls, s, tab, partition, cur, rest);
                let out2 = carry_out(urls, s, tab, partition, cur, rest).1;
                match cur {
                    Some(c) => {
                        assert(out == seq![Output::Send { conn: c, bytes }] + out2);
                        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                            Output::Send { bytes: b2, .. } => exists|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(b2),
                            _ => true,
                        } by {
                            if k == 0 {
                                assert(actions[0] == clazel_fetch::transducer::spec::Action::Send(bytes));
                            } else {
                                assert(out[k] == out2[k - 1]);
                                if let Output::Send { bytes: b2, .. } = out[k] {
                                    let a = choose|a: int| 0 <= a < rest.len() && rest[a] == clazel_fetch::transducer::spec::Action::Send(b2);
                                    assert(actions[a + 1] == rest[a]);
                                }
                            }
                        }
                    },
                    None => {
                        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                            Output::Send { bytes: b2, .. } => exists|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(b2),
                            _ => true,
                        } by {
                            if let Output::Send { bytes: b2, .. } = out[k] {
                                let a = choose|a: int| 0 <= a < rest.len() && rest[a] == clazel_fetch::transducer::spec::Action::Send(b2);
                                assert(actions[a + 1] == rest[a]);
                            }
                        }
                    },
                }
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    let sa = State { conns: without_conn(s.conns, c), ..s };
                    lemma_carry_out_sends(urls, sa, tab, partition, None, rest);
                    let out2 = carry_out(urls, sa, tab, partition, None, rest).1;
                    assert(out == seq![Output::Close { conn: c }] + out2);
                    assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                        Output::Send { bytes: b2, .. } => exists|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(b2),
                        _ => true,
                    } by {
                        if k > 0 {
                            assert(out[k] == out2[k - 1]);
                            if let Output::Send { bytes: b2, .. } = out[k] {
                                let a = choose|a: int| 0 <= a < rest.len() && rest[a] == clazel_fetch::transducer::spec::Action::Send(b2);
                                assert(actions[a + 1] == rest[a]);
                            }
                        }
                    }
                },
                None => {
                    lemma_carry_out_sends(urls, s, tab, partition, cur, rest);
                    let out2 = carry_out(urls, s, tab, partition, cur, rest).1;
                    assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                        Output::Send { bytes: b2, .. } => exists|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(b2),
                        _ => true,
                    } by {
                        if let Output::Send { bytes: b2, .. } = out[k] {
                            let a = choose|a: int| 0 <= a < rest.len() && rest[a] == clazel_fetch::transducer::spec::Action::Send(b2);
                            assert(actions[a + 1] == rest[a]);
                        }
                    }
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                lemma_commit_conns(urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response));
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                lemma_abort_conns(s, tab, error_fetch());
            },
        }
    }
}

/// The state `net` runs the actions in: the jar operations applied, the
/// dead connection forgotten, the navigation updated.
pub open spec fn net_mid(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns, s: State, conn: nat, input: NetInput, i: int, nav: Navigation) -> State {
    let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
    State {
        jar: apply_net_ops(rules, s.jar, ops),
        conns: if input is Closed || input is Error { without_conn(s.conns, conn) } else { s.conns },
        renderers: s.renderers.update(i, Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..s.renderers[i] }),
        ..s
    }
}

/// The middle state keeps the renderers' ids, tabs and locks in place and
/// the renderer table well formed.
pub proof fn lemma_net_mid(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput, i: int, nav: Navigation)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
        0 <= i < s.renderers.len(),
    ensures
        ({
            let s1 = net_mid(rules, fetch, s, conn, input, i, nav);
            &&& crate::invariant::renderers_wf(urls, s1.renderers, s1.next_id)
            &&& s1.next_id == s.next_id
            &&& s1.renderers.len() == s.renderers.len()
            &&& forall|a: int| 0 <= a < s.renderers.len() ==> (#[trigger] s1.renderers[a]).id == s.renderers[a].id && s1.renderers[a].tab == s.renderers[a].tab
        }),
{
    let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
    let old = s.renderers[i];
    let r = Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..old };
    assert(lock_of_url(urls, old.url, old.id) == Some(old.lock));
    crate::invariant::lemma_renderers_wf_update(urls, s.renderers, s.next_id, i, r, s.next_id);
}

/// **`theorem_net_only_to_tab`.**
pub proof fn theorem_net_only_to_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::net_only_to_tab_statement(rules, urls, fetch, s, conn, input),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::net_wf::lemma_net_target(s, conn);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        lemma_net_mid(rules, urls, fetch, s, conn, input, i, nav);
        let s1 = net_mid(rules, fetch, s, conn, input, i, nav);
        lemma_carry_out_renderer_outputs(urls, s1, c.tab, nav.partition, Some(conn), actions);
        let out = carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions).1;
        assert(step(rules, urls, fetch, s, Event::Net { conn, input }).1 == out);
        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
            Output::ToRenderer { id: x, .. } => (exists|i2: int| 0 <= i2 < s.renderers.len() && s.renderers[i2].tab == c.tab && s.renderers[i2].id == x) || (x == s.next_id && out.contains(
                Output::Spawn { id: x, policy: Policy::Renderer },
            )),
            Output::Spawn { id: x, .. } => x == s.next_id,
            Output::Kill { id: x } => exists|i2: int| 0 <= i2 < s.renderers.len() && s.renderers[i2].tab == c.tab && s.renderers[i2].id == x,
            Output::Connect { .. } => true,
            Output::Send { .. } => true,
            Output::Show { .. } => false,
            Output::Close { .. } => true,
        } by {
            match out[k] {
                Output::ToRenderer { id: x, .. } => {
                    if exists|i2: int| 0 <= i2 < s1.renderers.len() && s1.renderers[i2].tab == c.tab && s1.renderers[i2].id == x {
                        let i2 = choose|i2: int| 0 <= i2 < s1.renderers.len() && s1.renderers[i2].tab == c.tab && s1.renderers[i2].id == x;
                        assert(s.renderers[i2].tab == c.tab && s.renderers[i2].id == x);
                    }
                },
                Output::Kill { id: x } => {
                    let i2 = choose|i2: int| 0 <= i2 < s1.renderers.len() && s1.renderers[i2].tab == c.tab && s1.renderers[i2].id == x;
                    assert(s.renderers[i2].tab == c.tab && s.renderers[i2].id == x);
                },
                _ => {},
            }
        }
    }
}

/// **`theorem_net_answers_connection`.**
pub proof fn theorem_net_answers_connection(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::net_answers_connection_statement(rules, urls, fetch, s, conn, input),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::net_wf::lemma_net_target(s, conn);
    let e = Event::Net { conn, input };
    let (r1, out) = step(rules, urls, fetch, s, e);
    crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s, e);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        // Every connection of the tab is backed by a navigating renderer; tabs are unique.
        assert forall|j: int, k: int| 0 <= j < r1.renderers.len() && 0 <= k < r1.conns.len() && (#[trigger] r1.renderers[j]).tab == c.tab && (#[trigger] r1.conns[k]).tab == c.tab implies r1.renderers[j].pending is Some by {
            assert(crate::invariant::conn_backed(r1.renderers, r1.conns[k]));
            let m = choose|m: int| 0 <= m < r1.renderers.len() && r1.renderers[m].tab == r1.conns[k].tab && (r1.renderers[m].pending matches Some(n) && n.partition == r1.conns[k].partition);
            crate::theorems::tab_unique(urls, r1, j, m);
        }
        if exists|a: int| 0 <= a < actions.len() && ((#[trigger] actions[a]) is Done || actions[a] is Fail) {
            lemma_net_mid(rules, urls, fetch, s, conn, input, i, nav);
            let s1 = net_mid(rules, fetch, s, conn, input, i, nav);
            lemma_carry_out_terminal(urls, s1, c.tab, nav.partition, Some(conn), actions);
        }
    }
}

/// **`theorem_wire_cookies`** (kernel level): every `Send` the kernel
/// outputs is the transducer's.
pub proof fn theorem_wire_cookies(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::wire_cookies_statement(rules, urls, fetch, s, conn, input),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::net_wf::lemma_net_target(s, conn);
    if fetch.urls.rules == rules {
        if let Some((c, i, nav)) = net_target(s, conn) {
            let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
            let s1 = net_mid(rules, fetch, s, conn, input, i, nav);
            let out = carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions).1;
            assert(step(rules, urls, fetch, s, Event::Net { conn, input }).1 == out);
            lemma_carry_out_sends(urls, s1, c.tab, nav.partition, Some(conn), actions);
            clazel_fetch::transducer::theorems::theorem_wire_cookies(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
            clazel_fetch::transducer::theorems::lemma_sends_only_on_connected(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
            assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                Output::Send { conn: x, bytes } => x == conn && (exists|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(bytes))
                    && clazel_fetch::transducer::contract::is_wire_request(
                    nav.fetch.url,
                    clazel_fetch::transducer::contract::carried(
                        nav.fetch.url,
                        clazel_cookie::storage::spec::retrieve_cookie_string(
                            rules,
                            s.jar,
                            (fetch.urls.request_url)(nav.fetch.url),
                            clazel_fetch::transducer::spec::request_context(fetch.urls, nav.fetch),
                            s.now,
                        ),
                    ),
                    bytes,
                ),
                _ => true,
            } by {
                if let Output::Send { conn: x, bytes } = out[k] {
                    let a = choose|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(bytes);
                    // A Send happens only on `Connected` of a connecting fetch, and then it is the only action.
                    assert(!clazel_fetch::transducer::theorems::no_sends(actions));
                    assert(nav.fetch.phase is Connecting && input is Connected);
                    assert(actions.len() == 1);
                    assert(a == 0);
                    assert(actions.drop_first() =~= Seq::<NetAction>::empty());
                    assert(actions[0] is Send);
                    let b = actions[0]->Send_0;
                    assert(bytes == b);
                    assert(carry_out(urls, s1, c.tab, nav.partition, Some(conn), Seq::<NetAction>::empty()).1 == Seq::<Output>::empty());
                    assert(out =~= seq![Output::Send { conn, bytes: b }] + Seq::<Output>::empty());
                    assert(out.len() == 1 && k == 0);
                    assert(x == conn);
                }
            }
        }
    }
}

/// **`theorem_net_jar_frame`.**
pub proof fn theorem_net_jar_frame(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::net_jar_frame_statement(rules, urls, fetch, s, conn, input),
{
    crate::unwind_base::lemma_net_frame(rules, urls, fetch, s, conn, input);
    if let Some((c, i, nav)) = net_target(s, conn) {
        clazel_fetch::transducer::theorems::theorem_jar_frame(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
        clazel_fetch::transducer::theorems::theorem_ops_name_request(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
    }
}

// ---------------------------------------------------------------------
// Ownership.
// ---------------------------------------------------------------------

/// The connections of other tabs survive `carry_out`, if the connection the
/// actions apply to is not theirs.
pub proof fn lemma_carry_out_keeps(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>, c: Connection)
    requires
        s.conns.contains(c),
        c.tab != tab,
        c.id < s.next_conn,
        forall|j: int| 0 <= j < s.conns.len() ==> (#[trigger] s.conns[j]).id < s.next_conn,
        cur is Some ==> cur->Some_0 != c.id,
    ensures
        carry_out(urls, s, tab, partition, cur, actions).0.conns.contains(c),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let ep = Endpoint { host, port, tls };
                let (sa, id, out_a) = open_connection(s, tab, partition, ep);
                let nc = Connection { id: s.next_conn, tab, endpoint: ep, partition };
                assert(sa.conns == s.conns.push(nc));
                assert(sa.conns.contains(c)) by {
                    let m = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == c;
                    assert(sa.conns[m] == c);
                }
                assert forall|j: int| 0 <= j < sa.conns.len() implies (#[trigger] sa.conns[j]).id < sa.next_conn by {
                    if j < s.conns.len() {
                        assert(sa.conns[j] == s.conns[j]);
                    }
                }
                lemma_carry_out_keeps(urls, sa, tab, partition, Some(id), rest, c);
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_keeps(urls, s, tab, partition, cur, rest, c);
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(cc) => {
                    let sa = State { conns: without_conn(s.conns, cc), ..s };
                    crate::net_wf::lemma_filter_keeps(s.conns, |x: Connection| x.id != cc, c);
                    assert forall|j: int| 0 <= j < sa.conns.len() implies (#[trigger] sa.conns[j]).id < sa.next_conn by {
                        assert(sa.conns.contains(sa.conns[j]));
                        clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |x: Connection| x.id != cc, sa.conns[j]);
                        let m = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == sa.conns[j];
                    }
                    lemma_carry_out_keeps(urls, sa, tab, partition, None, rest, c);
                },
                None => {
                    lemma_carry_out_keeps(urls, s, tab, partition, cur, rest, c);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                crate::net_wf::lemma_without_tab_keeps(s.conns, tab, c);
                lemma_commit_keeps(urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response), c);
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                crate::net_wf::lemma_without_tab_keeps(s.conns, tab, c);
                lemma_abort_keeps(s, tab, error_fetch(), c);
            },
        }
    }
}

/// `commit_navigation` keeps the connections of other tabs.
pub proof fn lemma_commit_keeps(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Document, c: Connection)
    requires
        s.conns.contains(c),
        c.tab != tab,
    ensures
        commit_navigation(urls, s, tab, href, body).0.conns.contains(c),
{
    crate::net_wf::lemma_without_tab_keeps(s.conns, tab, c);
}

/// `abort_navigation` keeps the connections of other tabs.
pub proof fn lemma_abort_keeps(s: State, tab: nat, code: u64, c: Connection)
    requires
        s.conns.contains(c),
        c.tab != tab,
    ensures
        abort_navigation(s, tab, code).0.conns.contains(c),
{
    crate::net_wf::lemma_without_tab_keeps(s.conns, tab, c);
}

/// A message other than a `Navigate` that resolves changes no connection and
/// gives no connection output (a `Navigate` that does is `begin_navigation`).
pub proof fn lemma_handle_message_conns(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    ensures
        ({
            let (s1, out) = handle_message(rules, urls, fetch, s, r, m);
            (s1.conns == s.conns && s1.next_conn == s.next_conn && s1.renderers == s.renderers && forall|k: int|
                0 <= k < out.len() ==> !((#[trigger] out[k]) is Connect || out[k] is Send || out[k] is Close)) || (m is Navigate && exists|resolved: Seq<u32>| #[trigger] (handle_message(
                rules,
                urls,
                fetch,
                s,
                r,
                m,
            )) == begin_navigation(rules, urls, fetch, s, r.tab, resolved))
        }),
{
    match m {
        clazel_ipc::message::spec::Message::Navigate { url } => {
            match clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                None => {},
                Some(relative) => match (urls.resolve)(r.url, relative) {
                    None => {},
                    Some(resolved) => {
                        if lock_of_url(urls, resolved, s.next_id) is None {
                        } else {
                            assert(handle_message(rules, urls, fetch, s, r, m) == begin_navigation(rules, urls, fetch, s, r.tab, resolved));
                        }
                    },
                },
            }
        },
        clazel_ipc::message::spec::Message::CookieGet => {},
        clazel_ipc::message::spec::Message::CookieSet { cookie_string } => {},
        _ => {
            crate::lock::lemma_storage_call_frame(s, r, m);
        },
    }
}

/// A renderer's message that is not a `Navigate` changes no connection.
pub proof fn lemma_step_non_navigate_conns(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        find_by_id(s.renderers, id, 0) is Some,
        accepted_message(s.renderers[find_by_id(s.renderers, id, 0)->Some_0], bytes) matches Some(m) && !(m is Navigate),
    ensures
        step(rules, urls, fetch, s, Event::FromRenderer { id, bytes }).0.conns == s.conns,
        step(rules, urls, fetch, s, Event::FromRenderer { id, bytes }).0.next_conn == s.next_conn,
{
    let m = accepted_message(s.renderers[find_by_id(s.renderers, id, 0)->Some_0], bytes)->Some_0;
    lemma_handle_message_conns(rules, urls, fetch, s, s.renderers[find_by_id(s.renderers, id, 0)->Some_0], m);
}

/// A step of a renderer of another domain that has no declassified part
/// either kills the sender (closing its tab's connections) or changes no
/// connection.
pub proof fn lemma_local_conns(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        find_by_id(s.renderers, id, 0) is Some,
        crate::domain::declassified(urls, s, Event::FromRenderer { id, bytes }) is None,
    ensures
        ({
            let (s1, out) = step(rules, urls, fetch, s, Event::FromRenderer { id, bytes });
            let i = find_by_id(s.renderers, id, 0)->Some_0;
            s1.next_conn == s.next_conn && (s1.conns == s.conns || (accepted_message(s.renderers[i], bytes) is None && s1.conns == without_tab(
                s.conns,
                s.renderers[i].tab,
            )))
        }),
{
    let i = find_by_id(s.renderers, id, 0)->Some_0;
    let r = s.renderers[i];
    match accepted_message(r, bytes) {
        None => {},
        Some(m) => {
            lemma_handle_message_conns(rules, urls, fetch, s, r, m);
            if let clazel_ipc::message::spec::Message::Navigate { url } = m {
                if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                    if let Some(resolved) = (urls.resolve)(r.url, relative) {
                        if lock_of_url(urls, resolved, s.next_id) is Some {
                            assert(false);
                        }
                    }
                }
            }
        },
    }
}

/// The clause of `connection_ownership_statement` for an event about tab `t`.
pub open spec fn own_some(s: State, s1: State, out: Seq<Output>, t: nat) -> bool {
    &&& forall|j: int| 0 <= j < s.conns.len() && (#[trigger] s.conns[j]).tab != t ==> s1.conns.contains(s.conns[j])
    &&& forall|j: int|
        0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id >= s.next_conn ==> s1.conns[j].tab == t && exists|i: int|
            0 <= i < s1.renderers.len() && s1.renderers[i].tab == t && (s1.renderers[i].pending matches Some(nav) && nav.partition == s1.conns[j].partition)
    &&& forall|k: int|
        0 <= k < out.len() ==> match #[trigger] out[k] {
            Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
            Output::Send { conn: x, .. } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == t) || (s.next_conn <= x < s1.next_conn),
            Output::Close { conn: x } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == t) || (s.next_conn <= x < s1.next_conn),
            _ => true,
        }
}

/// The part of the statement every event has.
pub open spec fn own_common(s: State, s1: State) -> bool {
    &&& s.next_conn <= s1.next_conn
    &&& forall|j: int| 0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id < s.next_conn ==> s.conns.contains(s1.conns[j])
}

/// The clause for an event about no tab.
pub open spec fn own_none(s: State, s1: State, out: Seq<Output>) -> bool {
    s1.conns == s.conns && s1.next_conn == s.next_conn && forall|k: int| 0 <= k < out.len() ==> !((#[trigger] out[k]) is Connect || out[k] is Send || out[k] is Close)
}

/// Nothing changes in the connections and the outputs name none.
pub proof fn lemma_own_unchanged(s: State, s1: State, out: Seq<Output>, t: Option<nat>)
    requires
        kernel_wf_conns(s),
        own_none(s, s1, out),
    ensures
        own_common(s, s1),
        t is Some ==> own_some(s, s1, out, t->Some_0),
{
    if t is Some {
        let tt = t->Some_0;
        assert forall|j: int| 0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id >= s.next_conn implies s1.conns[j].tab == tt && exists|i: int|
            0 <= i < s1.renderers.len() && s1.renderers[i].tab == tt && (s1.renderers[i].pending matches Some(nav) && nav.partition == s1.conns[j].partition) by {
            assert(s.conns[j].id < s.next_conn);
        }
    }
}

/// The ids of the connections of the table are below the counter.
pub open spec fn kernel_wf_conns(s: State) -> bool {
    forall|j: int| 0 <= j < s.conns.len() ==> (#[trigger] s.conns[j]).id < s.next_conn
}

/// A tab's exit or kill: its connections are closed and nothing is opened.
pub proof fn lemma_own_close(s: State, s1: State, out: Seq<Output>, pre: Seq<Output>, t: nat)
    requires
        kernel_wf_conns(s),
        s1.conns == without_tab(s.conns, t),
        s1.next_conn == s.next_conn,
        out == pre + closes_of_tab(s.conns, t),
        forall|k: int| 0 <= k < pre.len() ==> !((#[trigger] pre[k]) is Connect || pre[k] is Send || pre[k] is Close),
    ensures
        own_common(s, s1),
        own_some(s, s1, out, t),
{
    lemma_closes_of_tab(s.conns, t);
    assert forall|j: int| 0 <= j < s1.conns.len() implies s.conns.contains(#[trigger] s1.conns[j]) && s1.conns[j].tab != t by {
        assert(s1.conns.contains(s1.conns[j]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |c: Connection| c.tab != t, s1.conns[j]);
    }
    assert forall|j: int| 0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id >= s.next_conn implies s1.conns[j].tab == t && exists|i: int|
        0 <= i < s1.renderers.len() && s1.renderers[i].tab == t && (s1.renderers[i].pending matches Some(nav) && nav.partition == s1.conns[j].partition) by {
        assert(s.conns.contains(s1.conns[j]));
        let m = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == s1.conns[j];
        assert(s.conns[m].id < s.next_conn);
    }
    assert forall|j: int| 0 <= j < s.conns.len() && (#[trigger] s.conns[j]).tab != t implies s1.conns.contains(s.conns[j]) by {
        assert(s.conns.contains(s.conns[j]));
        crate::net_wf::lemma_without_tab_keeps(s.conns, t, s.conns[j]);
    }
    assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
        Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
        Output::Send { conn: x, .. } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == t) || (s.next_conn <= x < s1.next_conn),
        Output::Close { conn: x } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == t) || (s.next_conn <= x < s1.next_conn),
        _ => true,
    } by {
        if k < pre.len() {
            assert(out[k] == pre[k]);
        } else {
            assert(out[k] == closes_of_tab(s.conns, t)[k - pre.len()]);
        }
    }
}

/// `begin_navigation` is about its tab.
pub proof fn lemma_own_begin(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        ({
            let (s1, out) = begin_navigation(rules, urls, fetch, s, tab, url);
            own_common(s, s1) && own_some(s, s1, out, tab)
        }),
{
    lemma_begin_outputs(rules, urls, fetch, s, tab, url);
    lemma_begin_wf_helper(rules, urls, fetch, s, tab, url);
    let (s1, out) = begin_navigation(rules, urls, fetch, s, tab, url);
    assert(crate::invariant::kernel_wf(rules, urls, s1));
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    assert forall|j: int| 0 <= j < s.conns.len() && (#[trigger] s.conns[j]).tab != tab implies s1.conns.contains(s.conns[j]) by {
        assert(s.conns.contains(s.conns[j]));
        lemma_begin_keeps(rules, urls, fetch, s, tab, url, s.conns[j]);
    }
    assert forall|j: int| 0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id >= s.next_conn implies s1.conns[j].tab == tab && exists|i: int|
        0 <= i < s1.renderers.len() && s1.renderers[i].tab == tab && (s1.renderers[i].pending matches Some(nav) && nav.partition == s1.conns[j].partition) by {
        if s.conns.contains(s1.conns[j]) {
            let m = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == s1.conns[j];
            assert(s.conns[m].id < s.next_conn);
        }
        assert(crate::invariant::conn_backed(s1.renderers, s1.conns[j]));
    }
    assert forall|j: int| 0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id < s.next_conn implies s.conns.contains(s1.conns[j]) by {}
    assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
        Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
        Output::Send { conn: x, .. } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == tab) || (s.next_conn <= x < s1.next_conn),
        Output::Close { conn: x } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == tab) || (s.next_conn <= x < s1.next_conn),
        _ => true,
    } by {
        match out[k] {
            Output::Close { conn: x } => {
                assert(owned_in(s.conns, tab, x));
            },
            _ => {},
        }
    }
}

/// `begin_navigation` keeps the well-formedness (and the connections of other tabs).
pub proof fn lemma_begin_wf_helper(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        crate::invariant::kernel_wf(rules, urls, begin_navigation(rules, urls, fetch, s, tab, url).0),
{
    crate::net_wf::lemma_begin_navigation_wf(rules, urls, fetch, s, tab, url);
}

/// The connections of other tabs survive `begin_navigation`.
pub proof fn lemma_begin_keeps(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>, c: Connection)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
        s.conns.contains(c),
        c.tab != tab,
    ensures
        begin_navigation(rules, urls, fetch, s, tab, url).0.conns.contains(c),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if lock_of_url(urls, url, s.next_id) is Some {
            let (s0, closes) = close_tab_conns(s, tab);
            crate::net_wf::lemma_without_tab_keeps(s.conns, tab, c);
            let old = s0.renderers[i];
            assert forall|j: int| 0 <= j < s0.conns.len() implies (#[trigger] s0.conns[j]).id < s0.next_conn by {
                assert(s0.conns.contains(s0.conns[j]));
                clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |x: Connection| x.tab != tab, s0.conns[j]);
                let m = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == s0.conns[j];
            }
            let m0 = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == c;
            assert(c.id < s.next_conn);
            match (fetch.parse)(url) {
                None => {},
                Some(parsed) => {
                    let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                    let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                    let s1 = State { renderers: s0.renderers.update(i, Renderer { pending: Some(nav), ..old }), ..s0 };
                    lemma_carry_out_keeps(urls, s1, tab, nav.partition, None, actions, c);
                },
            }
        }
    }
}

/// A `Net` event about an open connection is about its tab.
pub proof fn lemma_own_net(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        ({
            let (s1, out) = net(rules, urls, fetch, s, conn, input);
            net_target(s, conn) matches Some((c, _, _)) ==> own_common(s, s1) && own_some(s, s1, out, c.tab)
        }),
{
    crate::net_wf::lemma_net_target(s, conn);
    crate::net_wf::lemma_net_wf(rules, urls, fetch, s, conn, input);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        let mid = net_mid(rules, fetch, s, conn, input, i, nav);
        let (s1, out) = net(rules, urls, fetch, s, conn, input);
        assert(s1 == carry_out(urls, mid, c.tab, nav.partition, Some(conn), actions).0);
        assert(out == carry_out(urls, mid, c.tab, nav.partition, Some(conn), actions).1);
        lemma_carry_out_conns(urls, mid, c.tab, nav.partition, Some(conn), actions);
        assert(mid.next_conn == s.next_conn);
        // The middle table is a subset of the old one.
        assert forall|j: int| 0 <= j < mid.conns.len() implies s.conns.contains(#[trigger] mid.conns[j]) by {
            if input is Closed || input is Error {
                assert(mid.conns.contains(mid.conns[j]));
                clazel_cookie::storage::isolation::lemma_filter_elem(s.conns, |x: Connection| x.id != conn, mid.conns[j]);
            } else {
                assert(s.conns.contains(s.conns[j]));
            }
        }
        assert forall|j: int| 0 <= j < s.conns.len() implies (#[trigger] s.conns[j]).id < s.next_conn by {}
        // The connection of the event is the tab's.
        assert(s.conns.contains(c));
        let cm = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == c;
        // (a) other tabs' connections survive.
        assert forall|j: int| 0 <= j < s.conns.len() && (#[trigger] s.conns[j]).tab != c.tab implies s1.conns.contains(s.conns[j]) by {
            let c2 = s.conns[j];
            assert(c2.id != conn) by {
                if c2.id == conn {
                    assert(s.conns[j] == s.conns[cm]);
                }
            }
            assert(mid.conns.contains(c2)) by {
                if input is Closed || input is Error {
                    crate::net_wf::lemma_filter_keeps(s.conns, |x: Connection| x.id != conn, c2);
                } else {
                    assert(mid.conns == s.conns);
                    assert(s.conns.contains(c2));
                }
            }
            assert forall|j2: int| 0 <= j2 < mid.conns.len() implies (#[trigger] mid.conns[j2]).id < mid.next_conn by {
                assert(s.conns.contains(mid.conns[j2]));
                let m = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == mid.conns[j2];
            }
            lemma_carry_out_keeps(urls, mid, c.tab, nav.partition, Some(conn), actions, c2);
        }
        // (b) the new ones are backed.
        assert forall|j: int| 0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id >= s.next_conn implies s1.conns[j].tab == c.tab && exists|i2: int|
            0 <= i2 < s1.renderers.len() && s1.renderers[i2].tab == c.tab && (s1.renderers[i2].pending matches Some(n2) && n2.partition == s1.conns[j].partition) by {
            if mid.conns.contains(s1.conns[j]) {
                assert(s.conns.contains(s1.conns[j]));
                let m = choose|m: int| 0 <= m < s.conns.len() && s.conns[m] == s1.conns[j];
                assert(s.conns[m].id < s.next_conn);
            }
            assert(crate::invariant::conn_backed(s1.renderers, s1.conns[j]));
        }
        // (c) the outputs.
        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
            Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
            Output::Send { conn: x, .. } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == c.tab) || (s.next_conn <= x < s1.next_conn),
            Output::Close { conn: x } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == c.tab) || (s.next_conn <= x < s1.next_conn),
            _ => true,
        } by {
            match out[k] {
                Output::Send { conn: x, .. } => {
                    if x == conn {
                        assert(s.conns[cm].id == x && s.conns[cm].tab == c.tab);
                    }
                },
                Output::Close { conn: x } => {
                    if x == conn {
                        assert(s.conns[cm].id == x && s.conns[cm].tab == c.tab);
                    } else if owned_in(mid.conns, c.tab, x) {
                        let m = choose|m: int| 0 <= m < mid.conns.len() && mid.conns[m].id == x && mid.conns[m].tab == c.tab;
                        assert(s.conns.contains(mid.conns[m]));
                        let m2 = choose|m2: int| 0 <= m2 < s.conns.len() && s.conns[m2] == mid.conns[m];
                    }
                },
                _ => {},
            }
        }
        assert forall|j: int| 0 <= j < s1.conns.len() && (#[trigger] s1.conns[j]).id < s.next_conn implies s.conns.contains(s1.conns[j]) by {
            if !mid.conns.contains(s1.conns[j]) {
                assert(s.next_conn <= s1.conns[j].id);
            }
        }
    }
}

/// All the clauses of `connection_ownership_statement` for an event about `t`.
pub open spec fn own_all(s: State, s1: State, out: Seq<Output>, t: Option<nat>) -> bool {
    own_common(s, s1) && (t matches Some(tt) ==> own_some(s, s1, out, tt)) && (t is None ==> own_none(s, s1, out))
}

/// The clauses are the statement.
pub proof fn lemma_own_bridge(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        own_all(s, step(rules, urls, fetch, s, e).0, step(rules, urls, fetch, s, e).1, crate::statements::event_tab(s, e)),
    ensures
        crate::statements::connection_ownership_statement(rules, urls, fetch, s, e),
{
}

/// A step that changes no connection and names none.
pub proof fn lemma_own_all_unchanged(s: State, s1: State, out: Seq<Output>, t: Option<nat>)
    requires
        kernel_wf_conns(s),
        own_none(s, s1, out),
    ensures
        own_all(s, s1, out, t),
{
    lemma_own_unchanged(s, s1, out, t);
}

/// A renderer's frame.
pub proof fn lemma_own_all_from_renderer(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        ({
            let e = Event::FromRenderer { id, bytes };
            let (s1, out) = step(rules, urls, fetch, s, e);
            own_all(s, s1, out, crate::statements::event_tab(s, e))
        }),
{
    assert(kernel_wf_conns(s));
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    let e = Event::FromRenderer { id, bytes };
    let (s1, out) = step(rules, urls, fetch, s, e);
    let t = crate::statements::event_tab(s, e);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        match accepted_message(r, bytes) {
            None => {
                lemma_own_close(s, s1, out, seq![Output::Kill { id }], r.tab);
            },
            Some(m) => {
                lemma_handle_message_conns(rules, urls, fetch, s, r, m);
                if own_none(s, s1, out) {
                    lemma_own_all_unchanged(s, s1, out, t);
                } else {
                    if let clazel_ipc::message::spec::Message::Navigate { url } = m {
                        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                                if lock_of_url(urls, resolved, s.next_id) is Some {
                                    lemma_own_begin(rules, urls, fetch, s, r.tab, resolved);
                                }
                            }
                        }
                    }
                }
            },
        }
    } else {
        lemma_own_all_unchanged(s, s1, out, t);
    }
}

/// A renderer's exit.
pub proof fn lemma_own_all_exited(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        ({
            let e = Event::RendererExited { id };
            let (s1, out) = step(rules, urls, fetch, s, e);
            own_all(s, s1, out, crate::statements::event_tab(s, e))
        }),
{
    assert(kernel_wf_conns(s));
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    let e = Event::RendererExited { id };
    let (s1, out) = step(rules, urls, fetch, s, e);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        lemma_own_close(s, s1, out, seq![], s.renderers[i].tab);
    } else {
        lemma_own_all_unchanged(s, s1, out, crate::statements::event_tab(s, e));
    }
}

/// A network event.
pub proof fn lemma_own_all_net(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        ({
            let e = Event::Net { conn, input };
            let (s1, out) = step(rules, urls, fetch, s, e);
            own_all(s, s1, out, crate::statements::event_tab(s, e))
        }),
{
    assert(kernel_wf_conns(s));
    crate::net_wf::lemma_net_target(s, conn);
    let e = Event::Net { conn, input };
    let (s1, out) = step(rules, urls, fetch, s, e);
    if net_target(s, conn) is Some {
        lemma_own_net(rules, urls, fetch, s, conn, input);
    } else {
        lemma_own_all_unchanged(s, s1, out, crate::statements::event_tab(s, e));
    }
}

/// An `OpenTab`: with a script it changes no connection; without one it is
/// a new renderer, then the start of its tab's fetch (item 4.12), whose
/// connections are that tab's (`lemma_own_begin`).
pub proof fn lemma_own_all_open_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, url: Seq<u32>, script: Option<Seq<u8>>)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
        kernel_wf_conns(s),
    ensures
        ({
            let e = Event::OpenTab { url, script };
            let (s1, out) = step(rules, urls, fetch, s, e);
            own_all(s, s1, out, crate::statements::event_tab(s, e))
        }),
{
    let e = Event::OpenTab { url, script };
    let (s1, out) = step(rules, urls, fetch, s, e);
    let id = s.next_id;
    match lock_of_url(urls, url, id) {
        None => {
            lemma_own_all_unchanged(s, s1, out, crate::statements::event_tab(s, e));
        },
        Some(lock) => {
            if script is Some {
                lemma_own_all_unchanged(s, s1, out, crate::statements::event_tab(s, e));
            } else {
                let rn = Renderer { committed: false, id, tab: id, url, lock, pending: None };
                let sp = State { renderers: s.renderers.push(rn), next_id: id + 1, ..s };
                crate::invariant::lemma_open_tab_push_wf(rules, urls, s, url, lock, false);
                lemma_own_begin(rules, urls, fetch, sp, id, url);
                let ob = begin_navigation(rules, urls, fetch, sp, id, url).1;
                assert(out == seq![Output::Spawn { id, policy: Policy::Renderer }] + ob);
                assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                    Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                    Output::Send { conn: x, .. } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == id) || (s.next_conn <= x
                        < s1.next_conn),
                    Output::Close { conn: x } => (exists|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == id) || (s.next_conn <= x
                        < s1.next_conn),
                    _ => true,
                } by {
                    if k > 0 {
                        assert(out[k] == ob[k - 1]);
                    }
                }
            }
        },
    }
}

/// **`theorem_connection_ownership`.**
pub proof fn theorem_connection_ownership(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::connection_ownership_statement(rules, urls, fetch, s, e),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    assert(kernel_wf_conns(s));
    match e {
        Event::Tick { time } => {
            let (s1, out) = step(rules, urls, fetch, s, e);
            lemma_own_all_unchanged(s, s1, out, crate::statements::event_tab(s, e));
        },
        Event::OpenTab { url, script } => {
            lemma_own_all_open_tab(rules, urls, fetch, s, url, script);
        },
        Event::RendererExited { id } => {
            lemma_own_all_exited(rules, urls, fetch, s, id);
        },
        Event::NavigateTab { tab, url } => {
            lemma_own_begin(rules, urls, fetch, s, tab, url);
        },
        Event::Net { conn, input } => {
            lemma_own_all_net(rules, urls, fetch, s, conn, input);
        },
        Event::FromRenderer { id, bytes } => {
            lemma_own_all_from_renderer(rules, urls, fetch, s, id, bytes);
        },
    }
    lemma_own_bridge(rules, urls, fetch, s, e);
}

} // verus!

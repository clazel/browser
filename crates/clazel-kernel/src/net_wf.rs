//! Item 3.7: `step` keeps the invariant over navigations and connections
//! (`navigations_wf`, `conns_wf` of `kernel_wf`), for every transducer.
//!
//! The pieces: the connection table's operations (`close_tab_conns`, the
//! `Close` of one connection, the `Connect` of a new one), the renderer
//! table's (update, remove, push) and the kernel's own steps built from them
//! (`commit_navigation`, `abort_navigation`, `carry_out`, `begin_navigation`,
//! `net`). Nothing here unfolds the transducer but its two facts: it starts
//! with no redirects, and `step` keeps the redirect bound.

#[allow(unused_imports)]
use super::spec::*;
use crate::invariant::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The connection table.
// ---------------------------------------------------------------------

/// `find_conn` finds the first connection with the id, or there is none from
/// `i` on.
pub proof fn lemma_find_conn(cs: Seq<Connection>, id: nat, i: nat)
    ensures
        match find_conn(cs, id, i) {
            Some(k) => i <= k < cs.len() && cs[k].id == id,
            None => forall|k: int| i <= k < cs.len() ==> (#[trigger] cs[k]).id != id,
        },
    decreases cs.len() - i,
{
    if i < cs.len() && cs[i as int].id != id {
        lemma_find_conn(cs, id, i + 1);
    }
}

/// What [`net_target`] finds.
pub proof fn lemma_net_target(s: State, conn: nat)
    ensures
        match net_target(s, conn) {
            Some((c, i, nav)) => 0 <= i < s.renderers.len() && s.renderers[i].tab == c.tab && s.renderers[i].pending == Some(nav) && s.conns.contains(c) && c.id == conn,
            None => true,
        },
{
    lemma_find_conn(s.conns, conn, 0);
    if let Some(ci) = find_conn(s.conns, conn, 0) {
        assert(s.conns.contains(s.conns[ci]));
        lemma_find_by_tab(s.renderers, s.conns[ci].tab, 0);
    }
}

/// A subset of the connections (each is one of them) keeps the invariant.
pub proof fn lemma_conns_wf_sub(rs: Seq<Renderer>, cs: Seq<Connection>, nc: nat, cs2: Seq<Connection>)
    requires
        conns_wf(rs, cs, nc),
        forall|k: int| 0 <= k < cs2.len() ==> cs.contains(#[trigger] cs2[k]),
    ensures
        conns_wf(rs, cs2, nc),
{
    assert forall|k: int| 0 <= k < cs2.len() implies (#[trigger] cs2[k]).id < nc && conn_backed(rs, cs2[k]) by {
        let i = choose|i: int| 0 <= i < cs.len() && cs[i] == cs2[k];
        assert(cs[i].id < nc);
        assert(conn_backed(rs, cs[i]));
    }
    assert forall|a: int, b: int| 0 <= a < cs2.len() && 0 <= b < cs2.len() && (#[trigger] cs2[a]).id == (#[trigger] cs2[b]).id implies cs2[a] == cs2[b] by {
        let i = choose|i: int| 0 <= i < cs.len() && cs[i] == cs2[a];
        let j = choose|j: int| 0 <= j < cs.len() && cs[j] == cs2[b];
        assert(cs[i].id == cs[j].id);
    }
}

/// Closing the connections of a tab keeps the invariant.
pub proof fn lemma_without_tab_wf(rs: Seq<Renderer>, cs: Seq<Connection>, nc: nat, tab: nat)
    requires
        conns_wf(rs, cs, nc),
    ensures
        conns_wf(rs, without_tab(cs, tab), nc),
        forall|k: int| 0 <= k < without_tab(cs, tab).len() ==> (#[trigger] without_tab(cs, tab)[k]).tab != tab,
{
    let f = |c: Connection| c.tab != tab;
    let t = without_tab(cs, tab);
    assert forall|k: int| 0 <= k < t.len() implies cs.contains(#[trigger] t[k]) && t[k].tab != tab by {
        assert(t.contains(t[k]));
        clazel_cookie::storage::isolation::lemma_filter_elem(cs, f, t[k]);
    }
    lemma_conns_wf_sub(rs, cs, nc, t);
}

/// Closing one connection keeps the invariant.
pub proof fn lemma_without_conn_wf(rs: Seq<Renderer>, cs: Seq<Connection>, nc: nat, id: nat)
    requires
        conns_wf(rs, cs, nc),
    ensures
        conns_wf(rs, without_conn(cs, id), nc),
{
    let f = |c: Connection| c.id != id;
    let t = without_conn(cs, id);
    assert forall|k: int| 0 <= k < t.len() implies cs.contains(#[trigger] t[k]) by {
        assert(t.contains(t[k]));
        clazel_cookie::storage::isolation::lemma_filter_elem(cs, f, t[k]);
    }
    lemma_conns_wf_sub(rs, cs, nc, t);
}

/// A connection of the table that is of another tab survives the closing of
/// a tab's connections.
pub proof fn lemma_without_tab_keeps(cs: Seq<Connection>, tab: nat, c: Connection)
    requires
        cs.contains(c),
        c.tab != tab,
    ensures
        without_tab(cs, tab).contains(c),
{
    let f = |c: Connection| c.tab != tab;
    lemma_filter_keeps(cs, f, c);
}

/// An element the predicate accepts survives the filter.
pub proof fn lemma_filter_keeps<A>(s: Seq<A>, p: spec_fn(A) -> bool, x: A)
    requires
        s.contains(x),
        p(x),
    ensures
        s.filter(p).contains(x),
{
    let i = choose|i: int| 0 <= i < s.len() && s[i] == x;
    crate::counterexamples::lemma_filter_contains_elem(s, p, i);
}

/// Opening a connection for a navigating tab keeps the invariant.
pub proof fn lemma_conns_wf_push_conn(rs: Seq<Renderer>, cs: Seq<Connection>, nc: nat, c: Connection)
    requires
        conns_wf(rs, cs, nc),
        c.id == nc,
        conn_backed(rs, c),
    ensures
        conns_wf(rs, cs.push(c), nc + 1),
{
    let t = cs.push(c);
    assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).id < nc + 1 && conn_backed(rs, t[k]) by {
        if k < cs.len() {
            assert(t[k] == cs[k]);
        } else {
            assert(t[k] == c);
        }
    }
    assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && (#[trigger] t[a]).id == (#[trigger] t[b]).id implies t[a] == t[b] by {
        if a < cs.len() {
            assert(t[a] == cs[a]);
        } else {
            assert(t[a] == c);
        }
        if b < cs.len() {
            assert(t[b] == cs[b]);
        } else {
            assert(t[b] == c);
        }
    }
}

// ---------------------------------------------------------------------
// The renderer table.
// ---------------------------------------------------------------------

/// Replacing a renderer by one of the same tab keeps every connection backed,
/// if the connections of that tab are still backed by the new one.
pub proof fn lemma_conns_wf_update(rs: Seq<Renderer>, cs: Seq<Connection>, nc: nat, i: int, r: Renderer)
    requires
        conns_wf(rs, cs, nc),
        0 <= i < rs.len(),
        r.tab == rs[i].tab,
        forall|k: int| 0 <= k < cs.len() && (#[trigger] cs[k]).tab == rs[i].tab ==> (r.pending matches Some(nav) && nav.partition == cs[k].partition),
    ensures
        conns_wf(rs.update(i, r), cs, nc),
{
    let rs2 = rs.update(i, r);
    assert forall|k: int| 0 <= k < cs.len() implies conn_backed(rs2, #[trigger] cs[k]) by {
        assert(conn_backed(rs, cs[k]));
        let j = choose|j: int| 0 <= j < rs.len() && rs[j].tab == cs[k].tab && (rs[j].pending matches Some(nav) && nav.partition == cs[k].partition);
        if j == i {
            assert(rs2[i] == r);
        } else {
            assert(rs2[j] == rs[j]);
        }
    }
}

/// A renderer's exit takes its tab's connections with it.
pub proof fn lemma_conns_wf_remove(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, cs: Seq<Connection>, nc: nat, i: int)
    requires
        renderers_wf(urls, rs, next_id),
        conns_wf(rs, cs, nc),
        0 <= i < rs.len(),
    ensures
        conns_wf(rs.remove(i), without_tab(cs, rs[i].tab), nc),
{
    lemma_without_tab_wf(rs, cs, nc, rs[i].tab);
    let t = without_tab(cs, rs[i].tab);
    let rs2 = rs.remove(i);
    // Same ids, and each remaining connection is backed by a renderer other than `i`.
    assert forall|k: int| 0 <= k < t.len() implies conn_backed(rs2, #[trigger] t[k]) by {
        assert(conn_backed(rs, t[k]));
        let j = choose|j: int| 0 <= j < rs.len() && rs[j].tab == t[k].tab && (rs[j].pending matches Some(nav) && nav.partition == t[k].partition);
        assert(t[k].tab != rs[i].tab);
        assert(j != i);
        let m = if j < i { j } else { j - 1 };
        assert(rs2[m] == rs[j]);
    }
    assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).id < nc by {
        assert(conns_wf(rs, t, nc));
    }
    assert(conns_wf(rs2, t, nc)) by {
        assert forall|a: int, b: int| 0 <= a < t.len() && 0 <= b < t.len() && (#[trigger] t[a]).id == (#[trigger] t[b]).id implies t[a] == t[b] by {
            assert(conns_wf(rs, t, nc));
        }
    }
}

/// A renderer that is not navigating added to the table.
pub proof fn lemma_conns_wf_push_renderer(rs: Seq<Renderer>, cs: Seq<Connection>, nc: nat, r: Renderer)
    requires
        conns_wf(rs, cs, nc),
    ensures
        conns_wf(rs.push(r), cs, nc),
{
    let rs2 = rs.push(r);
    assert forall|k: int| 0 <= k < cs.len() implies conn_backed(rs2, #[trigger] cs[k]) by {
        assert(conn_backed(rs, cs[k]));
        let j = choose|j: int| 0 <= j < rs.len() && rs[j].tab == cs[k].tab && (rs[j].pending matches Some(nav) && nav.partition == cs[k].partition);
        assert(rs2[j] == rs[j]);
    }
}

// ---------------------------------------------------------------------
// Navigations.
// ---------------------------------------------------------------------

/// Replacing a renderer by one whose navigation is in order.
pub proof fn lemma_navigations_wf_update(rules: Seq<clazel_psl::spec::Rule>, rs: Seq<Renderer>, i: int, r: Renderer)
    requires
        navigations_wf(rules, rs),
        0 <= i < rs.len(),
        nav_ok(rules, r),
    ensures
        navigations_wf(rules, rs.update(i, r)),
{
    let rs2 = rs.update(i, r);
    assert forall|k: int| 0 <= k < rs2.len() implies nav_ok(rules, #[trigger] rs2[k]) by {
        if k != i {
            assert(rs2[k] == rs[k]);
        }
    }
}

/// Removing a renderer.
pub proof fn lemma_navigations_wf_remove(rules: Seq<clazel_psl::spec::Rule>, rs: Seq<Renderer>, i: int)
    requires
        navigations_wf(rules, rs),
        0 <= i < rs.len(),
    ensures
        navigations_wf(rules, rs.remove(i)),
{
    let rs2 = rs.remove(i);
    assert forall|k: int| 0 <= k < rs2.len() implies nav_ok(rules, #[trigger] rs2[k]) by {
        let m = if k < i { k } else { k + 1 };
        assert(rs2[k] == rs[m]);
    }
}

/// Adding a renderer whose navigation is in order.
pub proof fn lemma_navigations_wf_push(rules: Seq<clazel_psl::spec::Rule>, rs: Seq<Renderer>, r: Renderer)
    requires
        navigations_wf(rules, rs),
        nav_ok(rules, r),
    ensures
        navigations_wf(rules, rs.push(r)),
{
    let rs2 = rs.push(r);
    assert forall|k: int| 0 <= k < rs2.len() implies nav_ok(rules, #[trigger] rs2[k]) by {
        if k < rs.len() {
            assert(rs2[k] == rs[k]);
        } else {
            assert(rs2[k] == r);
        }
    }
}

// ---------------------------------------------------------------------
// The jar operations.
// ---------------------------------------------------------------------

/// A retrieval keeps the jar free of public-suffix domains (it changes only
/// the last-access-time, and evicts).
pub proof fn lemma_retrieval_no_public_suffix(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
)
    requires
        jar_no_public_suffix(rules, jar),
    ensures
        jar_no_public_suffix(rules, clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now)),
{
    let any_root = clazel_cookie::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    let live = clazel_cookie::storage::spec::evict_expired(jar, now);
    clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, jar, now, any_root);
    let out = clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now);
    assert forall|k: int| 0 <= k < live.len() implies (#[trigger] live[k]).domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, live[k].domain.name) by {
        assert(live.contains(live[k]));
        assert(jar.contains(live[k]));
        let q = choose|q: int| 0 <= q < jar.len() && jar[q] == live[k];
    }
    match url.host {
        None => {},
        Some(h) => {
            let g = clazel_cookie::storage::spec::update_last_access_time(rules, url, ctx, h, now);
            assert forall|k: int| 0 <= k < out.len() implies (#[trigger] out[k]).domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, out[k].domain.name) by {
                assert(out[k] == g(live[k]));
                if clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, ctx, h, live[k]) {
                    assert(g(live[k]) == clazel_cookie::storage::spec::with_last_access_time(live[k], now));
                } else {
                    assert(g(live[k]) == live[k]);
                }
            }
        },
    }
}

/// One jar operation of a transducer step keeps the jar well formed and free
/// of public-suffix domains.
pub proof fn lemma_apply_net_op_wf(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, op: clazel_fetch::transducer::spec::JarOp)
    requires
        jar_wf(rules, jar),
        jar_no_public_suffix(rules, jar),
    ensures
        jar_wf(rules, apply_net_op(rules, jar, op)),
        jar_no_public_suffix(rules, apply_net_op(rules, jar, op)),
{
    match op {
        clazel_fetch::transducer::spec::JarOp::Retrieved { url, ctx, now } => {
            lemma_jar_wf_retrieval(rules, jar, url, ctx, now);
            lemma_retrieval_no_public_suffix(rules, jar, url, ctx, now);
        },
        clazel_fetch::transducer::spec::JarOp::Stored { line, url, ctx, now } => {
            lemma_store_one_wf(rules, jar, HttpStore { line, url, ctx }, now);
        },
    }
}

/// The jar operations of a transducer step keep the jar well formed and free
/// of public-suffix domains: a retrieval is `jar_after_retrieval`, and a line
/// is stored only for a request whose host is not empty and not a public
/// suffix ([`store_allowed`]).
pub proof fn lemma_apply_net_ops_wf(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, ops: Seq<clazel_fetch::transducer::spec::JarOp>)
    requires
        jar_wf(rules, jar),
        jar_no_public_suffix(rules, jar),
    ensures
        jar_wf(rules, apply_net_ops(rules, jar, ops)),
        jar_no_public_suffix(rules, apply_net_ops(rules, jar, ops)),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let jar1 = apply_net_op(rules, jar, ops[0]);
        lemma_apply_net_op_wf(rules, jar, ops[0]);
        lemma_apply_net_ops_wf(rules, jar1, ops.drop_first());
    }
}

// ---------------------------------------------------------------------
// Ending and carrying out.
// ---------------------------------------------------------------------

/// Closing the connections of a tab keeps `kernel_wf`, and leaves none.
pub proof fn lemma_close_tab_conns_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, tab: nat)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, close_tab_conns(s, tab).0),
        no_tab_conns(close_tab_conns(s, tab).0.conns, tab),
{
    lemma_without_tab_wf(s.renderers, s.conns, s.next_conn, tab);
}

/// `commit_navigation` keeps `kernel_wf`.
pub proof fn lemma_commit_navigation_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Seq<u8>)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, commit_navigation(urls, s, tab, href, body).0),
{
    lemma_close_tab_conns_wf(rules, urls, s, tab);
    let s1 = close_tab_conns(s, tab).0;
    lemma_find_by_tab(s1.renderers, tab, 0);
    if let Some(i) = find_by_tab(s1.renderers, tab, 0) {
        if scalar_url(href) && lock_of_url(urls, href, s1.next_id) is Some {
            lemma_navigate_tab_wf(rules, urls, s1, tab, href, body);
        } else {
            lemma_fail_navigation_wf(rules, urls, s1, i, s1.renderers[i], error_bad_url());
        }
    }
}

/// `abort_navigation` keeps `kernel_wf`.
pub proof fn lemma_abort_navigation_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, tab: nat, code: u64)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, abort_navigation(s, tab, code).0),
{
    lemma_close_tab_conns_wf(rules, urls, s, tab);
    let s1 = close_tab_conns(s, tab).0;
    lemma_find_by_tab(s1.renderers, tab, 0);
    if let Some(i) = find_by_tab(s1.renderers, tab, 0) {
        lemma_fail_navigation_wf(rules, urls, s1, i, s1.renderers[i], code);
    }
}

/// The renderer of `tab` is navigating with the partition key `partition`.
pub open spec fn tab_navigating(s: State, tab: nat, partition: crate::domain::Domain) -> bool {
    exists|j: int| 0 <= j < s.renderers.len() && (#[trigger] s.renderers[j]).tab == tab && (s.renderers[j].pending matches Some(nav) && nav.partition == partition)
}

/// **`carry_out` keeps `kernel_wf`**, for any actions: a new connection is
/// backed by the navigating tab, a `Close` forgets a connection, and a `Done`
/// or `Fail` ends the navigation after closing every connection of the tab.
pub proof fn lemma_carry_out_wf(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    s: State,
    tab: nat,
    partition: crate::domain::Domain,
    cur: Option<nat>,
    actions: Seq<NetAction>,
)
    requires
        kernel_wf(rules, urls, s),
        tab_navigating(s, tab, partition),
    ensures
        kernel_wf(rules, urls, carry_out(urls, s, tab, partition, cur, actions).0),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let ep = Endpoint { host, port, tls };
                match choose_connection(s, tab, partition, ep) {
                    Some(id) => {
                        lemma_carry_out_wf(rules, urls, s, tab, partition, Some(id), rest);
                    },
                    None => {
                        let id = s.next_conn;
                        let c = Connection { id, tab, endpoint: ep, partition };
                        let j = choose|j: int| 0 <= j < s.renderers.len() && s.renderers[j].tab == tab && (s.renderers[j].pending matches Some(nav) && nav.partition == partition);
                        assert(conn_backed(s.renderers, c));
                        lemma_conns_wf_push_conn(s.renderers, s.conns, s.next_conn, c);
                        let s1 = State { conns: s.conns.push(c), next_conn: id + 1, ..s };
                        assert(kernel_wf(rules, urls, s1));
                        lemma_carry_out_wf(rules, urls, s1, tab, partition, Some(id), rest);
                    },
                }
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_wf(rules, urls, s, tab, partition, cur, rest);
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    lemma_without_conn_wf(s.renderers, s.conns, s.next_conn, c);
                    let s1 = State { conns: without_conn(s.conns, c), ..s };
                    assert(kernel_wf(rules, urls, s1));
                    lemma_carry_out_wf(rules, urls, s1, tab, partition, None, rest);
                },
                None => {
                    lemma_carry_out_wf(rules, urls, s, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                lemma_commit_navigation_wf(rules, urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response.body);
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                lemma_abort_navigation_wf(rules, urls, s, tab, error_fetch());
            },
        }
    }
}

// ---------------------------------------------------------------------
// Beginning a navigation and stepping it.
// ---------------------------------------------------------------------

/// `begin_navigation` (a `NavigateTab`, and a renderer's `Navigate`) keeps
/// the invariant: it closes the tab's old connections, records the
/// navigation (with the partition key of the renderer's domain, the
/// transducer started with no redirect), and carries out the transducer's
/// first actions.
pub proof fn lemma_begin_navigation_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, begin_navigation(rules, urls, fetch, s, tab, url).0),
{
    lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if lock_of_url(urls, url, s.next_id) is Some {
            lemma_close_tab_conns_wf(rules, urls, s, tab);
            let (s0, closes) = close_tab_conns(s, tab);
            let old = s0.renderers[i];
            assert(lock_of_url(urls, old.url, old.id) == Some(old.lock));
            match (fetch.parse)(url) {
                None => {
                    lemma_fail_navigation_wf(rules, urls, s0, i, old, error_bad_url());
                },
                Some(parsed) => {
                    let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                    let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                    assert(fs.redirects == 0);
                    let r = Renderer { pending: Some(nav), ..old };
                    assert(nav_ok(rules, r));
                    lemma_renderers_wf_update(urls, s0.renderers, s0.next_id, i, r, s0.next_id);
                    lemma_navigations_wf_update(rules, s0.renderers, i, r);
                    lemma_conns_wf_update(s0.renderers, s0.conns, s0.next_conn, i, r);
                    let s1 = State { renderers: s0.renderers.update(i, r), ..s0 };
                    assert(kernel_wf(rules, urls, s1));
                    assert(s1.renderers[i] == r);
                    lemma_carry_out_wf(rules, urls, s1, tab, nav.partition, None, actions);
                },
            }
        }
    }
}

/// `net` keeps the invariant: the jar operations keep the jar well formed
/// ([`lemma_apply_net_ops_wf`]), the transducer keeps its redirect bound
/// (`theorem_redirects_bounded` of `clazel-fetch`), the connections stay owned
/// by navigating tabs, and a commit or a failure ends the navigation and its
/// connections together.
pub proof fn lemma_net_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        kernel_wf(rules, urls, s),
    ensures
        kernel_wf(rules, urls, net(rules, urls, fetch, s, conn, input).0),
{
    lemma_net_target(s, conn);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        assert(nav_ok(rules, s.renderers[i]));
        clazel_fetch::transducer::theorems::theorem_redirects_bounded(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
        assert(clazel_fetch::transducer::contract::step_requires(fs));
        lemma_apply_net_ops_wf(rules, s.jar, ops);
        let old = s.renderers[i];
        assert(lock_of_url(urls, old.url, old.id) == Some(old.lock));
        let nav2 = Navigation { fetch: fs, ..nav };
        let r = Renderer { pending: Some(nav2), ..old };
        assert(nav_ok(rules, r));
        lemma_renderers_wf_update(urls, s.renderers, s.next_id, i, r, s.next_id);
        lemma_navigations_wf_update(rules, s.renderers, i, r);
        // The connections: the dead one is forgotten, the others are backed by the same partition.
        let conns = if input is Closed || input is Error { without_conn(s.conns, conn) } else { s.conns };
        if input is Closed || input is Error {
            lemma_without_conn_wf(s.renderers, s.conns, s.next_conn, conn);
        }
        assert(conns_wf(s.renderers, conns, s.next_conn));
        assert forall|k: int| 0 <= k < conns.len() && (#[trigger] conns[k]).tab == s.renderers[i].tab implies (r.pending matches Some(n) && n.partition == conns[k].partition) by {
            assert(conn_backed(s.renderers, conns[k]));
            let j = choose|j: int| 0 <= j < s.renderers.len() && s.renderers[j].tab == conns[k].tab && (s.renderers[j].pending matches Some(n) && n.partition == conns[k].partition);
            // Tabs are distinct, so the backing renderer is the one at `i`.
            if j != i {
                if j < i {
                    assert(s.renderers[j].tab != s.renderers[i].tab);
                } else {
                    assert(s.renderers[i].tab != s.renderers[j].tab);
                }
            }
        }
        lemma_conns_wf_update(s.renderers, conns, s.next_conn, i, r);
        let s1 = State { jar: apply_net_ops(rules, s.jar, ops), conns, renderers: s.renderers.update(i, r), ..s };
        assert(kernel_wf(rules, urls, s1));
        assert(s1.renderers[i] == r);
        assert(tab_navigating(s1, c.tab, nav.partition));
        lemma_carry_out_wf(rules, urls, s1, c.tab, nav.partition, Some(conn), actions);
    }
}

/// The state `begin_navigation` runs the transducer's first actions in (the
/// tab's connections closed, the navigation recorded) is well formed.
pub proof fn lemma_begin_mid_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s0: State, i: int, nav: Navigation)
    requires
        kernel_wf(rules, urls, s0),
        0 <= i < s0.renderers.len(),
        no_tab_conns(s0.conns, s0.renderers[i].tab),
        nav.partition == crate::domain::domain_of_renderer(rules, s0.renderers[i]),
        clazel_fetch::transducer::contract::step_requires(nav.fetch),
    ensures
        kernel_wf(rules, urls, State { renderers: s0.renderers.update(i, Renderer { pending: Some(nav), ..s0.renderers[i] }), ..s0 }),
{
    let old = s0.renderers[i];
    assert(lock_of_url(urls, old.url, old.id) == Some(old.lock));
    let r = Renderer { pending: Some(nav), ..old };
    assert(nav_ok(rules, r));
    lemma_renderers_wf_update(urls, s0.renderers, s0.next_id, i, r, s0.next_id);
    lemma_navigations_wf_update(rules, s0.renderers, i, r);
    lemma_conns_wf_update(s0.renderers, s0.conns, s0.next_conn, i, r);
}

/// The state `net` runs the transducer's actions in is well formed.
pub proof fn lemma_net_mid_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        kernel_wf(rules, urls, s),
    ensures
        net_target(s, conn) matches Some((c, i, nav)) ==> kernel_wf(
            rules,
            urls,
            State {
                jar: apply_net_ops(rules, s.jar, net_transducer_step(fetch, s, nav, input).2),
                conns: if input is Closed || input is Error { without_conn(s.conns, conn) } else { s.conns },
                renderers: s.renderers.update(i, Renderer { pending: Some(Navigation { fetch: net_transducer_step(fetch, s, nav, input).0, ..nav }), ..s.renderers[i] }),
                ..s
            },
        ) && tab_navigating(
            State {
                jar: apply_net_ops(rules, s.jar, net_transducer_step(fetch, s, nav, input).2),
                conns: if input is Closed || input is Error { without_conn(s.conns, conn) } else { s.conns },
                renderers: s.renderers.update(i, Renderer { pending: Some(Navigation { fetch: net_transducer_step(fetch, s, nav, input).0, ..nav }), ..s.renderers[i] }),
                ..s
            },
            c.tab,
            nav.partition,
        ),
{
    lemma_net_target(s, conn);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        assert(nav_ok(rules, s.renderers[i]));
        clazel_fetch::transducer::theorems::theorem_redirects_bounded(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
        lemma_apply_net_ops_wf(rules, s.jar, ops);
        let old = s.renderers[i];
        assert(lock_of_url(urls, old.url, old.id) == Some(old.lock));
        let nav2 = Navigation { fetch: fs, ..nav };
        let r = Renderer { pending: Some(nav2), ..old };
        assert(nav_ok(rules, r));
        lemma_renderers_wf_update(urls, s.renderers, s.next_id, i, r, s.next_id);
        lemma_navigations_wf_update(rules, s.renderers, i, r);
        let conns = if input is Closed || input is Error { without_conn(s.conns, conn) } else { s.conns };
        if input is Closed || input is Error {
            lemma_without_conn_wf(s.renderers, s.conns, s.next_conn, conn);
        }
        assert forall|k: int| 0 <= k < conns.len() && (#[trigger] conns[k]).tab == s.renderers[i].tab implies (r.pending matches Some(n) && n.partition == conns[k].partition) by {
            assert(conn_backed(s.renderers, conns[k]));
            let j = choose|j: int| 0 <= j < s.renderers.len() && s.renderers[j].tab == conns[k].tab && (s.renderers[j].pending matches Some(n) && n.partition == conns[k].partition);
            if j != i {
                if j < i {
                    assert(s.renderers[j].tab != s.renderers[i].tab);
                } else {
                    assert(s.renderers[i].tab != s.renderers[j].tab);
                }
            }
        }
        lemma_conns_wf_update(s.renderers, conns, s.next_conn, i, r);
        let s1 = State { jar: apply_net_ops(rules, s.jar, ops), conns, renderers: s.renderers.update(i, r), ..s };
        assert(kernel_wf(rules, urls, s1));
        assert(s1.renderers[i] == r);
        assert(tab_navigating(s1, c.tab, nav.partition));
    }
}

} // verus!

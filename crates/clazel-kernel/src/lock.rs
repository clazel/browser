//! `theorem_lock_is_committed_origin` (item 2.11): the lock of a renderer is
//! the origin of its committed URL, and only navigation sets it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// **`theorem_lock_is_committed_origin`, part 1.**
pub proof fn theorem_lock_is_committed_origin_state(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::lock_is_committed_origin_statement(urls, s),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    assert forall|i: int| 0 <= i < s.renderers.len() implies (lock_of_url(urls, (#[trigger] s.renderers[i]).url, s.renderers[i].id) == Some(s.renderers[i].lock)
        && match (urls.origin_of)(s.renderers[i].url) {
        Some(o) => match o {
            clazel_origin::spec::Origin::Tuple { .. } => s.renderers[i].lock == o,
            clazel_origin::spec::Origin::Opaque(_) => s.renderers[i].lock == clazel_origin::spec::Origin::Opaque(s.renderers[i].id),
        },
        None => false,
    }) by {
        let r = s.renderers[i];
        assert(lock_of_url(urls, r.url, r.id) == Some(r.lock));
    }
}

/// Distinct positions of a well-formed table have distinct ids.
pub proof fn lemma_ids_distinct(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, a: int, b: int)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        0 <= a < rs.len(),
        0 <= b < rs.len(),
        rs[a].id == rs[b].id,
    ensures
        a == b,
{
    if a < b {
        assert(rs[a].id != rs[b].id);
    } else if b < a {
        assert(rs[b].id != rs[a].id);
    }
}

/// Locks of surviving ids after a removal.
pub proof fn lemma_stable_remove(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, i: int)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        0 <= i < rs.len(),
    ensures
        forall|a: int, b: int|
            0 <= a < rs.len() && 0 <= b < rs.remove(i).len() && (#[trigger] rs[a]).id == (#[trigger] rs.remove(i)[b]).id ==> rs[a].lock == rs.remove(i)[b].lock,
        forall|b: int| 0 <= b < rs.remove(i).len() ==> rs.contains(#[trigger] rs.remove(i)[b]),
{
    let r2 = rs.remove(i);
    assert forall|b: int| 0 <= b < r2.len() implies rs.contains(#[trigger] r2[b]) by {
        let m = if b < i { b } else { b + 1 };
        assert(r2[b] == rs[m]);
    }
    assert forall|a: int, b: int| 0 <= a < rs.len() && 0 <= b < r2.len() && (#[trigger] rs[a]).id == (#[trigger] r2[b]).id implies rs[a].lock == r2[b].lock by {
        let m = if b < i { b } else { b + 1 };
        assert(r2[b] == rs[m]);
        lemma_ids_distinct(urls, rs, next_id, a, m);
    }
}

/// Locks of surviving ids after replacing a renderer by one that keeps its
/// id and lock, or has a fresh id.
pub proof fn lemma_stable_update(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, i: int, r: Renderer)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        0 <= i < rs.len(),
        (r.id == rs[i].id && r.lock == rs[i].lock) || r.id == next_id,
    ensures
        forall|a: int, b: int|
            0 <= a < rs.len() && 0 <= b < rs.update(i, r).len() && (#[trigger] rs[a]).id == (#[trigger] rs.update(i, r)[b]).id ==> rs[a].lock
                == rs.update(i, r)[b].lock,
{
    let r2 = rs.update(i, r);
    assert forall|a: int, b: int| 0 <= a < rs.len() && 0 <= b < r2.len() && (#[trigger] rs[a]).id == (#[trigger] r2[b]).id implies rs[a].lock == r2[b].lock by {
        if b == i {
            assert(r2[b] == r);
            if r.id == next_id {
                assert(rs[a].id < next_id);
            } else {
                lemma_ids_distinct(urls, rs, next_id, a, i);
            }
        } else {
            assert(r2[b] == rs[b]);
            lemma_ids_distinct(urls, rs, next_id, a, b);
        }
    }
}

/// The renderers after a `navigate_tab` keep the lock of every id that
/// survives.
pub proof fn lemma_navigate_tab_stable(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, script: Document)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = navigate_tab(urls, s, tab, url, script).0;
            forall|a: int, b: int|
                0 <= a < s.renderers.len() && 0 <= b < s1.renderers.len() && (#[trigger] s.renderers[a]).id == (#[trigger] s1.renderers[b]).id ==> s.renderers[a].lock
                    == s1.renderers[b].lock
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if let Some(lock) = lock_of_url(urls, url, s.next_id) {
            let old = s.renderers[i];
            if lock is Tuple && lock == old.lock {
                lemma_stable_update(urls, s.renderers, s.next_id, i, Renderer { url, pending: None, committed: true, ..old });
            } else {
                lemma_stable_update(urls, s.renderers, s.next_id, i, Renderer { committed: true, id: s.next_id, tab, url, lock, pending: None });
            }
        }
    }
}

/// The renderers after `carry_out` keep the lock of every id that survives.
pub proof fn lemma_carry_out_stable(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = carry_out(urls, s, tab, partition, cur, actions).0;
            forall|a: int, b: int|
                0 <= a < s.renderers.len() && 0 <= b < s1.renderers.len() && (#[trigger] s.renderers[a]).id == (#[trigger] s1.renderers[b]).id ==> s.renderers[a].lock
                    == s1.renderers[b].lock
        }),
    decreases actions.len(),
{
    if actions.len() == 0 {
        lemma_stable_same(urls, s.renderers, s.next_id);
    } else {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let (s1, id, out) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                lemma_carry_out_stable(urls, s1, tab, partition, Some(id), rest);
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_stable(urls, s, tab, partition, cur, rest);
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    lemma_carry_out_stable(urls, State { conns: without_conn(s.conns, c), ..s }, tab, partition, None, rest);
                },
                None => {
                    lemma_carry_out_stable(urls, s, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                lemma_commit_stable(urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response));
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                lemma_abort_stable(urls, s, tab, error_fetch());
            },
        }
    }
}

/// Replacing a renderer by one with the same id and lock keeps every id and
/// lock in place.
pub proof fn lemma_update_same_id_lock(rs: Seq<Renderer>, i: int, r: Renderer)
    requires
        0 <= i < rs.len(),
        r.id == rs[i].id,
        r.lock == rs[i].lock,
    ensures
        rs.update(i, r).len() == rs.len(),
        forall|a: int| 0 <= a < rs.len() ==> (#[trigger] rs.update(i, r)[a]).id == rs[a].id && rs.update(i, r)[a].lock == rs[a].lock,
{
}

/// `commit_navigation` keeps the lock of every surviving id.
pub proof fn lemma_commit_stable(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Document)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = commit_navigation(urls, s, tab, href, body).0;
            forall|a: int, b: int|
                0 <= a < s.renderers.len() && 0 <= b < s1.renderers.len() && (#[trigger] s.renderers[a]).id == (#[trigger] s1.renderers[b]).id ==> s.renderers[a].lock
                    == s1.renderers[b].lock
        }),
{
    let s0 = close_tab_conns(s, tab).0;
    crate::invariant::lemma_find_by_tab(s0.renderers, tab, 0);
    if let Some(i) = find_by_tab(s0.renderers, tab, 0) {
        if scalar_url(href) && lock_of_url(urls, href, s0.next_id) is Some {
            lemma_navigate_tab_stable(urls, s0, tab, href, body);
        } else {
            lemma_stable_update(urls, s0.renderers, s0.next_id, i, Renderer { pending: None, ..s0.renderers[i] });
        }
    } else {
        lemma_stable_same(urls, s.renderers, s.next_id);
    }
}

/// `abort_navigation` keeps the lock of every surviving id.
pub proof fn lemma_abort_stable(urls: UrlFns, s: State, tab: nat, code: u64)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = abort_navigation(s, tab, code).0;
            forall|a: int, b: int|
                0 <= a < s.renderers.len() && 0 <= b < s1.renderers.len() && (#[trigger] s.renderers[a]).id == (#[trigger] s1.renderers[b]).id ==> s.renderers[a].lock
                    == s1.renderers[b].lock
        }),
{
    let s0 = close_tab_conns(s, tab).0;
    crate::invariant::lemma_find_by_tab(s0.renderers, tab, 0);
    if let Some(i) = find_by_tab(s0.renderers, tab, 0) {
        lemma_stable_update(urls, s0.renderers, s0.next_id, i, Renderer { pending: None, ..s0.renderers[i] });
    } else {
        lemma_stable_same(urls, s.renderers, s.next_id);
    }
}

/// The renderers after a `begin_navigation` keep the lock of every id.
pub proof fn lemma_begin_stable(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = begin_navigation(rules, urls, fetch, s, tab, url).0;
            forall|a: int, b: int|
                0 <= a < s.renderers.len() && 0 <= b < s1.renderers.len() && (#[trigger] s.renderers[a]).id == (#[trigger] s1.renderers[b]).id ==> s.renderers[a].lock
                    == s1.renderers[b].lock
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if lock_of_url(urls, url, s.next_id) is Some {
            let s0 = close_tab_conns(s, tab).0;
            let old = s0.renderers[i];
            match (fetch.parse)(url) {
                None => {
                    lemma_stable_update(urls, s0.renderers, s0.next_id, i, Renderer { pending: None, ..old });
                },
                Some(parsed) => {
                    let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                    let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                    let r = Renderer { pending: Some(nav), ..old };
                    let s1 = State { renderers: s0.renderers.update(i, r), ..s0 };
                    crate::invariant::lemma_renderers_wf_update(urls, s0.renderers, s0.next_id, i, r, s0.next_id);
                    lemma_update_same_id_lock(s0.renderers, i, r);
                    lemma_carry_out_stable(urls, s1, tab, nav.partition, None, actions);
                    let res = carry_out(urls, s1, tab, nav.partition, None, actions).0;
                    assert forall|a: int, b: int| 0 <= a < s.renderers.len() && 0 <= b < res.renderers.len() && (#[trigger] s.renderers[a]).id == (#[trigger] res.renderers[b]).id implies s.renderers[a].lock == res.renderers[b].lock by {
                        assert(s0.renderers[a] == s.renderers[a]);
                        assert(s1.renderers[a].id == s.renderers[a].id && s1.renderers[a].lock == s.renderers[a].lock);
                    }
                },
            }
        } else {
            lemma_stable_same(urls, s.renderers, s.next_id);
        }
    } else {
        lemma_stable_same(urls, s.renderers, s.next_id);
    }
}

/// The renderers after a `net` keep the lock of every id that survives.
pub proof fn lemma_net_stable(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = net(rules, urls, fetch, s, conn, input).0;
            forall|a: int, b: int|
                0 <= a < s.renderers.len() && 0 <= b < s1.renderers.len() && (#[trigger] s.renderers[a]).id == (#[trigger] s1.renderers[b]).id ==> s.renderers[a].lock
                    == s1.renderers[b].lock
        }),
{
    crate::net_wf::lemma_net_target(s, conn);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        let old = s.renderers[i];
        let r = Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..old };
        crate::invariant::lemma_renderers_wf_update(urls, s.renderers, s.next_id, i, r, s.next_id);
        lemma_update_same_id_lock(s.renderers, i, r);
        let conns = if input is Closed || input is Error { without_conn(s.conns, conn) } else { s.conns };
        let s1 = State { jar: apply_net_ops(rules, s.jar, ops), conns, renderers: s.renderers.update(i, r), ..s };
        lemma_carry_out_stable(urls, s1, c.tab, nav.partition, Some(conn), actions);
        let res = carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions).0;
        assert forall|a: int, b: int| 0 <= a < s.renderers.len() && 0 <= b < res.renderers.len() && (#[trigger] s.renderers[a]).id == (#[trigger] res.renderers[b]).id implies s.renderers[a].lock == res.renderers[b].lock by {
            assert(s1.renderers[a].id == s.renderers[a].id && s1.renderers[a].lock == s.renderers[a].lock);
        }
    } else {
        lemma_stable_same(urls, s.renderers, s.next_id);
    }
}

/// `storage_call` leaves all but the storage alone.
pub proof fn lemma_storage_call_frame(s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    ensures
        storage_call(s, r, m).0.renderers == s.renderers,
        storage_call(s, r, m).0.jar == s.jar,
        storage_call(s, r, m).0.next_id == s.next_id,
        storage_call(s, r, m).0.now == s.now,
{
}

/// How `step` changes the renderer table.
pub proof fn lemma_step_renderers_shape(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let s1 = step(rules, urls, fetch, s, e).0;
            crate::statements::navigation_event(e) || s1.renderers == s.renderers || exists|i: int| 0 <= i < s.renderers.len() && s1.renderers == s.renderers.remove(i)
        }),
{
    match e {
        Event::RendererExited { id } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
        },
        Event::FromRenderer { id, bytes } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let r = s.renderers[i];
                match accepted_message(r, bytes) {
                    None => {
                        assert(step(rules, urls, fetch, s, e).0.renderers == s.renderers.remove(i));
                    },
                    Some(m) => {
                        lemma_storage_call_frame(s, r, m);
                    },
                }
            }
        },
        _ => {},
    }
}

/// Same renderers: every surviving id has its lock.
pub proof fn lemma_stable_same(urls: UrlFns, rs: Seq<Renderer>, next_id: nat)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
    ensures
        forall|a: int, b: int| 0 <= a < rs.len() && 0 <= b < rs.len() && (#[trigger] rs[a]).id == (#[trigger] rs[b]).id ==> rs[a].lock == rs[b].lock,
{
    assert forall|a: int, b: int| 0 <= a < rs.len() && 0 <= b < rs.len() && (#[trigger] rs[a]).id == (#[trigger] rs[b]).id implies rs[a].lock == rs[b].lock by {
        lemma_ids_distinct(urls, rs, next_id, a, b);
    }
}

/// **`theorem_lock_is_committed_origin`, part 2.**
pub proof fn theorem_lock_set_only_by_navigation(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::lock_set_only_by_navigation_statement(rules, urls, fetch, s, e),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    lemma_step_renderers_shape(rules, urls, fetch, s, e);
    let s1 = step(rules, urls, fetch, s, e).0;
    lemma_stable_same(urls, s.renderers, s.next_id);
    if s1.renderers == s.renderers {
        assert forall|j: int| 0 <= j < s1.renderers.len() implies s.renderers.contains(#[trigger] s1.renderers[j]) by {
            assert(s.renderers[j] == s1.renderers[j]);
        }
    } else if !crate::statements::navigation_event(e) {
        let k = choose|k: int| 0 <= k < s.renderers.len() && s1.renderers == s.renderers.remove(k);
        lemma_stable_remove(urls, s.renderers, s.next_id, k);
    } else {
        match e {
            Event::OpenTab { url, script } => {
                if let Some(lock) = lock_of_url(urls, url, s.next_id) {
                    lemma_open_tab_stable(rules, urls, fetch, s, url, script, lock);
                }
            },
            Event::NavigateTab { tab, url } => {
                lemma_begin_stable(rules, urls, fetch, s, tab, url);
            },
            Event::Net { conn, input } => {
                lemma_net_stable(rules, urls, fetch, s, conn, input);
            },
            Event::FromRenderer { id, bytes } => {
                crate::invariant::lemma_find_by_id(s.renderers, id, 0);
                if let Some(i) = find_by_id(s.renderers, id, 0) {
                    let r = s.renderers[i];
                    if let Some(clazel_ipc::message::spec::Message::Navigate { url }) = accepted_message(r, bytes) {
                        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                                if lock_of_url(urls, resolved, s.next_id) is Some {
                                    lemma_begin_stable(rules, urls, fetch, s, r.tab, resolved);
                                }
                            }
                        }
                    }
                }
            },
            _ => {},
        }
    }
}

/// `OpenTab` keeps the lock of every renderer: it adds one, with a new id,
/// and without a script starts its tab's fetch (item 4.12), which keeps
/// every lock (`lemma_begin_stable`).
proof fn lemma_open_tab_stable(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    url: Seq<u32>,
    script: Option<Seq<u8>>,
    lock: clazel_origin::spec::Origin,
)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
        lock_of_url(urls, url, s.next_id) == Some(lock),
    ensures
        ({
            let s1 = step(rules, urls, fetch, s, Event::OpenTab { url, script }).0;
            forall|i: int, j: int|
                0 <= i < s.renderers.len() && 0 <= j < s1.renderers.len() && (#[trigger] s.renderers[i]).id == (#[trigger] s1.renderers[j]).id ==> s.renderers[i].lock
                    == s1.renderers[j].lock
        }),
{
    let s1 = step(rules, urls, fetch, s, Event::OpenTab { url, script }).0;
    let rn = Renderer { committed: script is Some, id: s.next_id, tab: s.next_id, url, lock, pending: None };
    let sp = State { renderers: s.renderers.push(rn), next_id: s.next_id + 1, ..s };
    assert forall|i: int, j: int|
        0 <= i < s.renderers.len() && 0 <= j < sp.renderers.len() && (#[trigger] s.renderers[i]).id == (#[trigger] sp.renderers[j]).id implies s.renderers[i].lock
        == sp.renderers[j].lock by {
        if j < s.renderers.len() {
            assert(sp.renderers[j] == s.renderers[j]);
            lemma_ids_distinct(urls, s.renderers, s.next_id, i, j);
        } else {
            assert(sp.renderers[j] == rn);
            assert(s.renderers[i].id < s.next_id);
        }
    }
    if script is None {
        crate::invariant::lemma_open_tab_push_wf(rules, urls, s, url, lock, false);
        lemma_begin_stable(rules, urls, fetch, sp, s.next_id, url);
        assert forall|i: int, j: int|
            0 <= i < s.renderers.len() && 0 <= j < s1.renderers.len() && (#[trigger] s.renderers[i]).id == (#[trigger] s1.renderers[j]).id implies s.renderers[i].lock
            == s1.renderers[j].lock by {
            assert(sp.renderers[i] == s.renderers[i]);
        }
    }
}

/// **`theorem_lock_is_committed_origin`.** In every reachable state each
/// renderer's lock is the origin of its committed URL, and every step keeps
/// the lock of every renderer and creates renderers only by navigating.
pub proof fn theorem_lock_is_committed_origin(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::lock_is_committed_origin_statement(urls, s),
        forall|e: Event| #[trigger] crate::statements::lock_set_only_by_navigation_statement(rules, urls, fetch, s, e),
{
    theorem_lock_is_committed_origin_state(rules, urls, fetch, s);
    assert forall|e: Event| #[trigger] crate::statements::lock_set_only_by_navigation_statement(rules, urls, fetch, s, e) by {
        theorem_lock_set_only_by_navigation(rules, urls, fetch, s, e);
    }
}

} // verus!

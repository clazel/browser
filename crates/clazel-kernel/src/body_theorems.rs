//! Item 6.16's kernel theorems: `theorem_body_from_requester`,
//! `theorem_body_sent_once`, `theorem_redirect_method` and
//! `theorem_post_cookies`. Their statements are in `statements.rs`
//! (committed first, CLAUDE.md rule 3).
//!
//! The body theorem is an invariant over traces. A request body can enter a
//! renderer's navigation in one place, [`submit`](crate::spec::submit) (a
//! frame the renderer sent), and afterwards it only stays or is dropped (a
//! redirect keeps it for 307 and 308 and drops it otherwise; a commit, a
//! failure or a renderer's exit ends the navigation). That is
//! [`bodies_step`]: after a step, every body of a navigation in flight was
//! already that tab's before the step, or is the one the step's event
//! handed the tab ([`crate::statements::event_submitted`]). [`lemma_run_bodies`]
//! chains it along a trace.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// After the step from `old` to `new`, every body of a navigation in flight in
/// `new` was already the body of a navigation of the same tab in `old`, or is
/// `sub`'s, the body the step's event handed that tab.
pub open spec fn bodies_step(old: Seq<Renderer>, new: Seq<Renderer>, sub: Option<(nat, clazel_fetch::request::spec::Payload)>) -> bool {
    forall|j: int|
        0 <= j < new.len() && crate::statements::nav_body(#[trigger] new[j]) is Some ==> (exists|i: int|
            0 <= i < old.len() && (#[trigger] old[i]).tab == new[j].tab && crate::statements::nav_body(old[i]) == crate::statements::nav_body(new[j])) || sub == Some(
            (new[j].tab, crate::statements::nav_body(new[j])->Some_0),
        )
}

/// What a navigation begun in `tab` with request `req` hands the tab.
pub open spec fn begin_sub(tab: nat, req: clazel_fetch::request::spec::Req) -> Option<(nat, clazel_fetch::request::spec::Payload)> {
    match req.body {
        Some(p) => Some((tab, p)),
        None => None,
    }
}

// ---------------------------------------------------------------------
// Building blocks.
// ---------------------------------------------------------------------

/// An unchanged table.
pub proof fn lemma_bodies_refl(rs: Seq<Renderer>, sub: Option<(nat, clazel_fetch::request::spec::Payload)>)
    ensures
        bodies_step(rs, rs, sub),
{
    assert forall|j: int| 0 <= j < rs.len() && crate::statements::nav_body(#[trigger] rs[j]) is Some implies (exists|i: int|
        0 <= i < rs.len() && (#[trigger] rs[i]).tab == rs[j].tab && crate::statements::nav_body(rs[i]) == crate::statements::nav_body(rs[j])) || sub == Some(
        (rs[j].tab, crate::statements::nav_body(rs[j])->Some_0),
    ) by {
        assert(0 <= j < rs.len() && rs[j].tab == rs[j].tab && crate::statements::nav_body(rs[j]) == crate::statements::nav_body(rs[j]));
    }
}

/// A step that hands no tab a body may be said to hand any.
pub proof fn lemma_bodies_weaken(old: Seq<Renderer>, new: Seq<Renderer>, sub: Option<(nat, clazel_fetch::request::spec::Payload)>)
    requires
        bodies_step(old, new, None),
    ensures
        bodies_step(old, new, sub),
{
    assert forall|j: int| 0 <= j < new.len() && crate::statements::nav_body(#[trigger] new[j]) is Some implies (exists|i: int|
        0 <= i < old.len() && (#[trigger] old[i]).tab == new[j].tab && crate::statements::nav_body(old[i]) == crate::statements::nav_body(new[j])) || sub == Some(
        (new[j].tab, crate::statements::nav_body(new[j])->Some_0),
    ) by {
        assert(exists|i: int| 0 <= i < old.len() && (#[trigger] old[i]).tab == new[j].tab && crate::statements::nav_body(old[i]) == crate::statements::nav_body(new[j]));
    }
}

/// A step that hands a body, then one that hands none, hand that body.
pub proof fn lemma_bodies_compose(a: Seq<Renderer>, b: Seq<Renderer>, c: Seq<Renderer>, sub: Option<(nat, clazel_fetch::request::spec::Payload)>)
    requires
        bodies_step(a, b, sub),
        bodies_step(b, c, None),
    ensures
        bodies_step(a, c, sub),
{
    assert forall|j: int| 0 <= j < c.len() && crate::statements::nav_body(#[trigger] c[j]) is Some implies (exists|i: int|
        0 <= i < a.len() && (#[trigger] a[i]).tab == c[j].tab && crate::statements::nav_body(a[i]) == crate::statements::nav_body(c[j])) || sub == Some(
        (c[j].tab, crate::statements::nav_body(c[j])->Some_0),
    ) by {
        // From `b` to `c` nothing is new: some renderer of `b` has the tab and the body.
        let m = choose|m: int| 0 <= m < b.len() && (#[trigger] b[m]).tab == c[j].tab && crate::statements::nav_body(b[m]) == crate::statements::nav_body(c[j]);
        assert(crate::statements::nav_body(b[m]) is Some);
        if exists|i: int| 0 <= i < a.len() && (#[trigger] a[i]).tab == b[m].tab && crate::statements::nav_body(a[i]) == crate::statements::nav_body(b[m]) {
            let i = choose|i: int| 0 <= i < a.len() && (#[trigger] a[i]).tab == b[m].tab && crate::statements::nav_body(a[i]) == crate::statements::nav_body(b[m]);
            assert(a[i].tab == c[j].tab && crate::statements::nav_body(a[i]) == crate::statements::nav_body(c[j]));
        } else {
            assert(sub == Some((b[m].tab, crate::statements::nav_body(b[m])->Some_0)));
        }
    }
}

/// An entry set to a navigation-free renderer.
pub proof fn lemma_bodies_update_clear(old: Seq<Renderer>, i: int, r: Renderer)
    requires
        0 <= i < old.len(),
        crate::statements::nav_body(r) is None,
    ensures
        bodies_step(old, old.update(i, r), None),
{
    let new = old.update(i, r);
    assert forall|j: int| 0 <= j < new.len() && crate::statements::nav_body(#[trigger] new[j]) is Some implies (exists|k: int|
        0 <= k < old.len() && (#[trigger] old[k]).tab == new[j].tab && crate::statements::nav_body(old[k]) == crate::statements::nav_body(new[j])) || None::<(nat, clazel_fetch::request::spec::Payload)> == Some(
        (new[j].tab, crate::statements::nav_body(new[j])->Some_0),
    ) by {
        assert(j != i);
        assert(new[j] == old[j]);
        assert(0 <= j < old.len() && old[j].tab == new[j].tab && crate::statements::nav_body(old[j]) == crate::statements::nav_body(new[j]));
    }
}

/// A removed entry.
pub proof fn lemma_bodies_remove(old: Seq<Renderer>, i: int)
    requires
        0 <= i < old.len(),
    ensures
        bodies_step(old, old.remove(i), None),
{
    let new = old.remove(i);
    assert forall|j: int| 0 <= j < new.len() && crate::statements::nav_body(#[trigger] new[j]) is Some implies (exists|k: int|
        0 <= k < old.len() && (#[trigger] old[k]).tab == new[j].tab && crate::statements::nav_body(old[k]) == crate::statements::nav_body(new[j])) || None::<(nat, clazel_fetch::request::spec::Payload)> == Some(
        (new[j].tab, crate::statements::nav_body(new[j])->Some_0),
    ) by {
        let src = if j < i {
            j
        } else {
            j + 1
        };
        assert(0 <= src < old.len());
        assert(new[j] == old[src]);
        assert(old[src].tab == new[j].tab && crate::statements::nav_body(old[src]) == crate::statements::nav_body(new[j]));
    }
}

/// A pushed navigation-free entry.
pub proof fn lemma_bodies_push(old: Seq<Renderer>, r: Renderer)
    requires
        crate::statements::nav_body(r) is None,
    ensures
        bodies_step(old, old.push(r), None),
{
    let new = old.push(r);
    assert forall|j: int| 0 <= j < new.len() && crate::statements::nav_body(#[trigger] new[j]) is Some implies (exists|k: int|
        0 <= k < old.len() && (#[trigger] old[k]).tab == new[j].tab && crate::statements::nav_body(old[k]) == crate::statements::nav_body(new[j])) || None::<(nat, clazel_fetch::request::spec::Payload)> == Some(
        (new[j].tab, crate::statements::nav_body(new[j])->Some_0),
    ) by {
        assert(j < old.len());
        assert(new[j] == old[j]);
        assert(0 <= j < old.len() && old[j].tab == new[j].tab && crate::statements::nav_body(old[j]) == crate::statements::nav_body(new[j]));
    }
}

/// A navigation's fetch state replaced by one whose body is the old one's or
/// none (a `Net` step).
pub proof fn lemma_bodies_net_update(old: Seq<Renderer>, i: int, nav: Navigation, fs: FetchState)
    requires
        0 <= i < old.len(),
        old[i].pending == Some(nav),
        fs.req.body is None || fs.req.body == nav.fetch.req.body,
    ensures
        bodies_step(old, old.update(i, Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..old[i] }), None),
{
    let new = old.update(i, Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..old[i] });
    assert forall|j: int| 0 <= j < new.len() && crate::statements::nav_body(#[trigger] new[j]) is Some implies (exists|k: int|
        0 <= k < old.len() && (#[trigger] old[k]).tab == new[j].tab && crate::statements::nav_body(old[k]) == crate::statements::nav_body(new[j])) || None::<(nat, clazel_fetch::request::spec::Payload)> == Some(
        (new[j].tab, crate::statements::nav_body(new[j])->Some_0),
    ) by {
        if j == i {
            assert(crate::statements::nav_body(new[j]) == fs.req.body);
            assert(crate::statements::nav_body(old[i]) == nav.fetch.req.body);
            assert(old[i].tab == new[j].tab && crate::statements::nav_body(old[i]) == crate::statements::nav_body(new[j]));
        } else {
            assert(new[j] == old[j]);
            assert(old[j].tab == new[j].tab && crate::statements::nav_body(old[j]) == crate::statements::nav_body(new[j]));
        }
    }
}

/// A navigation begun in entry `i`: the entry's navigation is the new one,
/// whose request's body is handed to the entry's tab.
pub proof fn lemma_bodies_begin_update(old: Seq<Renderer>, i: int, nav2: Navigation)
    requires
        0 <= i < old.len(),
    ensures
        bodies_step(old, old.update(i, Renderer { pending: Some(nav2), ..old[i] }), begin_sub(old[i].tab, nav2.fetch.req)),
{
    let new = old.update(i, Renderer { pending: Some(nav2), ..old[i] });
    assert forall|j: int| 0 <= j < new.len() && crate::statements::nav_body(#[trigger] new[j]) is Some implies (exists|k: int|
        0 <= k < old.len() && (#[trigger] old[k]).tab == new[j].tab && crate::statements::nav_body(old[k]) == crate::statements::nav_body(new[j])) || begin_sub(old[i].tab, nav2.fetch.req) == Some(
        (new[j].tab, crate::statements::nav_body(new[j])->Some_0),
    ) by {
        if j == i {
            assert(new[j].tab == old[i].tab);
            assert(crate::statements::nav_body(new[j]) == nav2.fetch.req.body);
        } else {
            assert(new[j] == old[j]);
            assert(old[j].tab == new[j].tab && crate::statements::nav_body(old[j]) == crate::statements::nav_body(new[j]));
        }
    }
}

// ---------------------------------------------------------------------
// The fetch's request body: kept or dropped.
// ---------------------------------------------------------------------

/// HTTP-redirect fetch step 12 keeps the body or drops it.
pub proof fn lemma_rewrite_body(status: nat, req: clazel_fetch::request::spec::Req)
    ensures
        clazel_fetch::request::spec::rewrite_for_redirect(status, req).body is None || clazel_fetch::request::spec::rewrite_for_redirect(status, req).body == req.body,
{
}

/// A new fetch state has the request it is begun with.
pub proof fn lemma_begin_req_all()
    ensures
        forall|u: clazel_url::url::spec::Url, r: nat, t: bool, q: clazel_fetch::request::spec::Req| #[trigger] clazel_fetch::transducer::spec::begin(u, r, t, q).0.req == q,
{
}

/// `on_final` keeps the request's body or drops it.
pub proof fn lemma_on_final_body(urls: clazel_fetch::transducer::spec::UrlFns, s: FetchState, response: clazel_fetch::transducer::spec::Response, open: bool, now: int)
    ensures
        clazel_fetch::transducer::spec::on_final(urls, s, response, open, now).0.req.body is None || clazel_fetch::transducer::spec::on_final(urls, s, response, open, now).0.req.body == s.req.body,
{
    lemma_begin_req_all();
    lemma_rewrite_body(response.status_line.status, s.req);
}

/// **A step of the transducer keeps the request's body or drops it**: it is
/// the body of the request the fetch started with, or none (a redirect
/// that rewrote the request to a `GET`).
pub proof fn lemma_fetch_step_body(http: clazel_fetch::transducer::spec::HttpFns, urls: clazel_fetch::transducer::spec::UrlFns, s: FetchState, input: NetInput, jar: Seq<clazel_cookie::storage::spec::Cookie>, now: int)
    ensures
        clazel_fetch::transducer::spec::step(http, urls, s, input, jar, now).0.req.body is None || clazel_fetch::transducer::spec::step(http, urls, s, input, jar, now).0.req.body == s.req.body,
{
    match s.phase {
        clazel_fetch::transducer::spec::Phase::Finished => {},
        clazel_fetch::transducer::spec::Phase::Connecting => {},
        clazel_fetch::transducer::spec::Phase::Reading { received } => match input {
            clazel_fetch::transducer::spec::Input::Bytes(bytes) => match clazel_fetch::transducer::spec::settle(http, received + bytes) {
                clazel_fetch::transducer::spec::Settled::Final(response) => lemma_on_final_body(urls, s, response, true, now),
                _ => {},
            },
            clazel_fetch::transducer::spec::Input::Closed => match clazel_fetch::transducer::spec::settle_at_close(http, received) {
                clazel_fetch::transducer::spec::Settled::Final(response) => lemma_on_final_body(urls, s, response, false, now),
                _ => {},
            },
            _ => {},
        },
    }
}

/// A fetch begun with request `req` has it.
pub proof fn lemma_start_req_req(url: clazel_url::url::spec::Url, req: clazel_fetch::request::spec::Req)
    ensures
        clazel_fetch::transducer::spec::start_req(url, req).0.req == req,
{
}

// ---------------------------------------------------------------------
// The kernel's functions.
// ---------------------------------------------------------------------

/// `fail_navigation` keeps no body.
pub proof fn lemma_fail_bodies(s: State, i: int, old: Renderer, code: u64)
    requires
        0 <= i < s.renderers.len(),
    ensures
        bodies_step(s.renderers, fail_navigation(s, i, old, code).0.renderers, None),
{
    lemma_bodies_update_clear(s.renderers, i, Renderer { pending: None, ..old });
}

/// `navigate_tab` (a commit) keeps no body of its tab.
pub proof fn lemma_navigate_tab_bodies(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, doc: Document)
    ensures
        bodies_step(s.renderers, navigate_tab(urls, s, tab, url, doc).0.renderers, None),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    match find_by_tab(s.renderers, tab, 0) {
        None => lemma_bodies_refl(s.renderers, None),
        Some(i) => {
            let old = s.renderers[i];
            match lock_of_url(urls, url, s.next_id) {
                None => lemma_bodies_refl(s.renderers, None),
                Some(lock) => {
                    if lock is Tuple && lock == old.lock {
                        lemma_bodies_update_clear(s.renderers, i, Renderer { url, pending: None, committed: true, ..old });
                    } else {
                        lemma_bodies_update_clear(s.renderers, i, Renderer { committed: true, id: s.next_id, tab, url, lock, pending: None });
                    }
                },
            }
        },
    }
}

/// `commit_navigation` keeps no body of its tab.
pub proof fn lemma_commit_bodies(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, doc: Document)
    ensures
        bodies_step(s.renderers, commit_navigation(urls, s, tab, href, doc).0.renderers, None),
{
    let (s1, closes) = close_tab_conns(s, tab);
    assert(s1.renderers == s.renderers);
    crate::invariant::lemma_find_by_tab(s1.renderers, tab, 0);
    match find_by_tab(s1.renderers, tab, 0) {
        None => lemma_bodies_refl(s.renderers, None),
        Some(i) => {
            if scalar_url(href) && lock_of_url(urls, href, s1.next_id) is Some {
                lemma_navigate_tab_bodies(urls, s1, tab, href, doc);
            } else {
                lemma_fail_bodies(s1, i, s1.renderers[i], error_bad_url());
            }
        },
    }
}

/// `abort_navigation` keeps no body of its tab.
pub proof fn lemma_abort_bodies(s: State, tab: nat, code: u64)
    ensures
        bodies_step(s.renderers, abort_navigation(s, tab, code).0.renderers, None),
{
    let (s1, closes) = close_tab_conns(s, tab);
    assert(s1.renderers == s.renderers);
    crate::invariant::lemma_find_by_tab(s1.renderers, tab, 0);
    match find_by_tab(s1.renderers, tab, 0) {
        None => lemma_bodies_refl(s.renderers, None),
        Some(i) => {
            lemma_fail_bodies(s1, i, s1.renderers[i], code);
        },
    }
}

/// **`carry_out` hands no tab a body**: it changes the renderers only by a
/// commit or an abort, which end a navigation.
pub proof fn lemma_carry_out_bodies(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    ensures
        bodies_step(s.renderers, carry_out(urls, s, tab, partition, cur, actions).0.renderers, None),
    decreases actions.len(),
{
    if actions.len() == 0 {
        lemma_bodies_refl(s.renderers, None);
    } else {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let (s1, id, out) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                assert(s1.renderers == s.renderers);
                lemma_carry_out_bodies(urls, s1, tab, partition, Some(id), rest);
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_bodies(urls, s, tab, partition, cur, rest);
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    let s1 = State { conns: without_conn(s.conns, c), ..s };
                    lemma_carry_out_bodies(urls, s1, tab, partition, None, rest);
                },
                None => {
                    lemma_carry_out_bodies(urls, s, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                lemma_commit_bodies(urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response));
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                lemma_abort_bodies(s, tab, error_fetch());
            },
        }
    }
}

/// **`begin_navigation` hands its tab the body of its request, and no other
/// tab any.**
pub proof fn lemma_begin_bodies(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>, req: clazel_fetch::request::spec::Req)
    ensures
        bodies_step(s.renderers, begin_navigation(rules, urls, fetch, s, tab, url, req).0.renderers, begin_sub(tab, req)),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    match find_by_tab(s.renderers, tab, 0) {
        None => lemma_bodies_refl(s.renderers, begin_sub(tab, req)),
        Some(i) => match lock_of_url(urls, url, s.next_id) {
            None => lemma_bodies_refl(s.renderers, begin_sub(tab, req)),
            Some(_) => {
                let (s0, closes) = close_tab_conns(s, tab);
                assert(s0.renderers == s.renderers);
                let old = s0.renderers[i];
                match (fetch.parse)(url) {
                    None => {
                        lemma_fail_bodies(s0, i, old, error_bad_url());
                        lemma_bodies_weaken(s.renderers, fail_navigation(s0, i, old, error_bad_url()).0.renderers, begin_sub(tab, req));
                    },
                    Some(parsed) => {
                        let (fs, actions) = clazel_fetch::transducer::spec::start_req(parsed, req);
                        lemma_start_req_req(parsed, req);
                        let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                        let s1 = State { renderers: s0.renderers.update(i, Renderer { pending: Some(nav), ..old }), ..s0 };
                        lemma_bodies_begin_update(s0.renderers, i, nav);
                        assert(old.tab == tab);
                        assert(begin_sub(old.tab, nav.fetch.req) == begin_sub(tab, req));
                        lemma_carry_out_bodies(urls, s1, tab, nav.partition, None, actions);
                        lemma_bodies_compose(s.renderers, s1.renderers, carry_out(urls, s1, tab, nav.partition, None, actions).0.renderers, begin_sub(tab, req));
                    },
                }
            },
        },
    }
}

/// `open_tab` hands no tab a body.
pub proof fn lemma_open_tab_bodies(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, url: Seq<u32>, script: Option<Seq<u8>>)
    ensures
        bodies_step(s.renderers, open_tab(rules, urls, fetch, s, url, script).0.renderers, None),
{
    let id = s.next_id;
    match lock_of_url(urls, url, id) {
        None => lemma_bodies_refl(s.renderers, None),
        Some(lock) => match script {
            Some(sc) => {
                lemma_bodies_push(s.renderers, Renderer { committed: true, id, tab: id, url, lock, pending: None });
            },
            None => {
                let rn = Renderer { committed: false, id, tab: id, url, lock, pending: None };
                let s1 = State { renderers: s.renderers.push(rn), next_id: id + 1, ..s };
                lemma_bodies_push(s.renderers, rn);
                lemma_begin_bodies(rules, urls, fetch, s1, id, url, clazel_fetch::request::spec::get_req());
                assert(begin_sub(id, clazel_fetch::request::spec::get_req()) is None);
                lemma_bodies_compose(
                    s.renderers,
                    s1.renderers,
                    begin_navigation(rules, urls, fetch, s1, id, url, clazel_fetch::request::spec::get_req()).0.renderers,
                    None,
                );
            },
        },
    }
}

/// `net` hands no tab a body: the fetch keeps its request's body or drops it,
/// and its actions end the navigation or leave the renderers alone.
pub proof fn lemma_net_bodies(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    ensures
        bodies_step(s.renderers, net(rules, urls, fetch, s, conn, input).0.renderers, None),
{
    crate::net_wf::lemma_net_target(s, conn);
    match net_target(s, conn) {
        None => lemma_bodies_refl(s.renderers, None),
        Some((c, i, nav)) => {
            let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
            lemma_fetch_step_body(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
            let s1 = crate::net_theorems::net_mid(rules, fetch, s, conn, input, i, nav);
            lemma_bodies_net_update(s.renderers, i, nav, fs);
            assert(s1.renderers == s.renderers.update(i, Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..s.renderers[i] }));
            lemma_carry_out_bodies(urls, s1, c.tab, nav.partition, Some(conn), actions);
            lemma_bodies_compose(s.renderers, s1.renderers, carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions).0.renderers, None);
        },
    }
}

/// A renderer's frame that is a `Navigate` or a `Submit` hands its tab the
/// body of its request ([`crate::statements::event_submitted`]).
pub proof fn lemma_from_renderer_bodies(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        crate::statements::navigation_event(Event::FromRenderer { id, bytes }),
    ensures
        bodies_step(s.renderers, from_renderer(rules, urls, fetch, s, id, bytes).0.renderers, crate::statements::event_submitted(s, Event::FromRenderer { id, bytes })),
{
    let e = Event::FromRenderer { id, bytes };
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    match find_by_id(s.renderers, id, 0) {
        None => lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e)),
        Some(i) => {
            let r = s.renderers[i];
            match accepted_message(r, bytes) {
                None => {
                    lemma_bodies_remove(s.renderers, i);
                    assert(from_renderer(rules, urls, fetch, s, id, bytes).0.renderers == s.renderers.remove(i));
                    lemma_bodies_weaken(s.renderers, s.renderers.remove(i), crate::statements::event_submitted(s, e));
                },
                Some(m) => match m {
                    clazel_ipc::message::spec::Message::Submit { url, method, content_type, body } => match submit_request(r, method, content_type, body) {
                        None => lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e)),
                        Some(req) => match clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                            None => lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e)),
                            Some(relative) => match (urls.resolve)(r.url, relative) {
                                None => lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e)),
                                Some(resolved) => {
                                    if lock_of_url(urls, resolved, s.next_id) is None {
                                        lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e));
                                    } else {
                                        lemma_begin_bodies(rules, urls, fetch, s, r.tab, resolved, req);
                                        assert(crate::statements::event_submitted(s, e) == begin_sub(r.tab, req));
                                    }
                                },
                            },
                        },
                    },
                    clazel_ipc::message::spec::Message::Navigate { url } => match clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                        None => lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e)),
                        Some(relative) => match (urls.resolve)(r.url, relative) {
                            None => lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e)),
                            Some(resolved) => {
                                if lock_of_url(urls, resolved, s.next_id) is None {
                                    lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e));
                                } else {
                                    lemma_begin_bodies(rules, urls, fetch, s, r.tab, resolved, clazel_fetch::request::spec::get_req());
                                    assert(begin_sub(r.tab, clazel_fetch::request::spec::get_req()) is None);
                                    assert(crate::statements::event_submitted(s, e) is None);
                                }
                            },
                        },
                    },
                    _ => {
                        // `accepted_message` is the decoded message, and a
                        // navigation event decodes to a `Navigate` or a `Submit`.
                        assert(decode_renderer_frame(bytes) == Some(m));
                        assert(false);
                    },
                },
            }
        },
    }
}

/// **Every step**: a tab's navigation in flight has a body only if it had
/// that body before the step or the step's event handed it to the tab. For
/// every event but a `SubmitTab`.
pub proof fn lemma_step_bodies(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
        !(e is SubmitTab),
    ensures
        bodies_step(s.renderers, step(rules, urls, fetch, s, e).0.renderers, crate::statements::event_submitted(s, e)),
{
    crate::lock::lemma_step_renderers_shape(rules, urls, fetch, s, e);
    let s1 = step(rules, urls, fetch, s, e).0;
    if !crate::statements::navigation_event(e) {
        if s1.renderers == s.renderers {
            lemma_bodies_refl(s.renderers, crate::statements::event_submitted(s, e));
        } else {
            let k = choose|k: int| 0 <= k < s.renderers.len() && s1.renderers == s.renderers.remove(k);
            lemma_bodies_remove(s.renderers, k);
            lemma_bodies_weaken(s.renderers, s1.renderers, crate::statements::event_submitted(s, e));
        }
    } else {
        match e {
            Event::OpenTab { url, script } => {
                lemma_open_tab_bodies(rules, urls, fetch, s, url, script);
                lemma_bodies_weaken(s.renderers, s1.renderers, crate::statements::event_submitted(s, e));
            },
            Event::NavigateTab { tab, url } => {
                lemma_begin_bodies(rules, urls, fetch, s, tab, url, clazel_fetch::request::spec::get_req());
                assert(begin_sub(tab, clazel_fetch::request::spec::get_req()) is None);
                assert(crate::statements::event_submitted(s, e) is None);
            },
            Event::Net { conn, input } => {
                lemma_net_bodies(rules, urls, fetch, s, conn, input);
                lemma_bodies_weaken(s.renderers, s1.renderers, crate::statements::event_submitted(s, e));
            },
            Event::FromRenderer { id, bytes } => {
                lemma_from_renderer_bodies(rules, urls, fetch, s, id, bytes);
            },
            _ => {},
        }
    }
}

/// **A run chains it**: from a state that satisfies the invariant, by a trace
/// with no `SubmitTab`, every body of a navigation in flight was the body of a
/// navigation of the same tab at the start, or some event of the trace
/// handed it to that tab.
pub proof fn lemma_run_bodies(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, t: Seq<Event>)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
        crate::statements::no_submit_tab(t),
    ensures
        ({
            let s1 = run_state(rules, urls, fetch, s, t);
            forall|j: int|
                0 <= j < s1.renderers.len() && crate::statements::nav_body(#[trigger] s1.renderers[j]) is Some ==> (exists|i: int|
                    0 <= i < s.renderers.len() && (#[trigger] s.renderers[i]).tab == s1.renderers[j].tab && crate::statements::nav_body(s.renderers[i]) == crate::statements::nav_body(s1.renderers[j]))
                    || crate::statements::submitted_in(rules, urls, fetch, s, t, s1.renderers[j].tab, crate::statements::nav_body(s1.renderers[j])->Some_0)
        }),
    decreases t.len(),
{
    if t.len() == 0 {
        let s1 = run_state(rules, urls, fetch, s, t);
        assert forall|j: int| 0 <= j < s1.renderers.len() && crate::statements::nav_body(#[trigger] s1.renderers[j]) is Some implies (exists|i: int|
            0 <= i < s.renderers.len() && (#[trigger] s.renderers[i]).tab == s1.renderers[j].tab && crate::statements::nav_body(s.renderers[i]) == crate::statements::nav_body(s1.renderers[j]))
            || crate::statements::submitted_in(rules, urls, fetch, s, t, s1.renderers[j].tab, crate::statements::nav_body(s1.renderers[j])->Some_0) by {
            assert(s1 == s);
            assert(0 <= j < s.renderers.len() && s.renderers[j].tab == s1.renderers[j].tab && crate::statements::nav_body(s.renderers[j]) == crate::statements::nav_body(s1.renderers[j]));
        }
    } else {
        let e = t[0];
        let rest = t.drop_first();
        let sm = step(rules, urls, fetch, s, e).0;
        assert(!(e is SubmitTab));
        assert(crate::statements::no_submit_tab(rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies !((#[trigger] rest[k]) is SubmitTab) by {
                assert(rest[k] == t[k + 1]);
            }
        }
        crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s, e);
        lemma_step_bodies(rules, urls, fetch, s, e);
        lemma_run_bodies(rules, urls, fetch, sm, rest);
        let s1 = run_state(rules, urls, fetch, s, t);
        assert(s1 == run_state(rules, urls, fetch, sm, rest));
        assert forall|j: int| 0 <= j < s1.renderers.len() && crate::statements::nav_body(#[trigger] s1.renderers[j]) is Some implies (exists|i: int|
            0 <= i < s.renderers.len() && (#[trigger] s.renderers[i]).tab == s1.renderers[j].tab && crate::statements::nav_body(s.renderers[i]) == crate::statements::nav_body(s1.renderers[j]))
            || crate::statements::submitted_in(rules, urls, fetch, s, t, s1.renderers[j].tab, crate::statements::nav_body(s1.renderers[j])->Some_0) by {
            let p = crate::statements::nav_body(s1.renderers[j])->Some_0;
            if crate::statements::submitted_in(rules, urls, fetch, sm, rest, s1.renderers[j].tab, p) {
                // `t` unfolds to its first event and the run of `rest` from `sm`.
                assert(crate::statements::submitted_in(rules, urls, fetch, s, t, s1.renderers[j].tab, p));
            } else {
                // Some renderer of `sm` has the tab and the body: `bodies_step` of the first event.
                let m = choose|m: int| 0 <= m < sm.renderers.len() && (#[trigger] sm.renderers[m]).tab == s1.renderers[j].tab && crate::statements::nav_body(sm.renderers[m]) == crate::statements::nav_body(s1.renderers[j]);
                assert(crate::statements::nav_body(sm.renderers[m]) is Some);
                if exists|i: int| 0 <= i < s.renderers.len() && (#[trigger] s.renderers[i]).tab == sm.renderers[m].tab && crate::statements::nav_body(s.renderers[i]) == crate::statements::nav_body(sm.renderers[m]) {
                    let i = choose|i: int| 0 <= i < s.renderers.len() && (#[trigger] s.renderers[i]).tab == sm.renderers[m].tab && crate::statements::nav_body(s.renderers[i]) == crate::statements::nav_body(sm.renderers[m]);
                    assert(s.renderers[i].tab == s1.renderers[j].tab && crate::statements::nav_body(s.renderers[i]) == crate::statements::nav_body(s1.renderers[j]));
                } else {
                    assert(crate::statements::event_submitted(s, e) == Some((sm.renderers[m].tab, crate::statements::nav_body(sm.renderers[m])->Some_0)));
                    assert(crate::statements::submitted_in(rules, urls, fetch, s, t, s1.renderers[j].tab, p));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// The theorems.
// ---------------------------------------------------------------------

/// A wire request ends with the request's body.
proof fn lemma_wire_ends_with_body(url: clazel_url::url::spec::Url, req: clazel_fetch::request::spec::Req, cookie: Seq<u8>, bytes: Seq<u8>)
    requires
        clazel_fetch::transducer::contract::is_wire_request(url, req, cookie, bytes),
    ensures
        crate::statements::ends_with(bytes, clazel_fetch::request::spec::body_bytes(req)),
{
    match (clazel_fetch::request::spec::request_for_req(url, req), clazel_fetch::request::spec::request_for_req_cookie(url, req, cookie)) {
        (Some(base), Some(r)) => {
            let head = clazel_http::message::spec::serialize_request(r);
            let body = clazel_fetch::request::spec::body_bytes(req);
            assert(bytes == head + body);
            assert(bytes.len() == head.len() + body.len());
            assert(bytes.subrange(bytes.len() - body.len(), bytes.len() as int) =~= body);
        },
        _ => {},
    }
}

/// **`theorem_body_from_requester`** (item 6.16).
pub proof fn theorem_body_from_requester(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, t: Seq<Event>, conn: nat, input: NetInput)
    requires
        crate::statements::no_submit_tab(t),
    ensures
        crate::statements::body_from_requester_statement(rules, urls, fetch, t, conn, input),
{
    crate::invariant::lemma_init_wf(rules, urls);
    crate::invariant::lemma_run_state_wf(rules, urls, fetch, init_state(), t);
    lemma_run_bodies(rules, urls, fetch, init_state(), t);
    let s = run_state(rules, urls, fetch, init_state(), t);
    // The first clause: the initial state has no renderer.
    assert(init_state().renderers.len() == 0);
    crate::net_wf::lemma_net_target(s, conn);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        let s1 = crate::net_theorems::net_mid(rules, fetch, s, conn, input, i, nav);
        let out = carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions).1;
        assert(step(rules, urls, fetch, s, Event::Net { conn, input }).1 == out);
        // The second clause: the navigation's own body is a renderer's.
        assert(s.renderers[i].pending == Some(nav));
        assert(crate::statements::nav_body(s.renderers[i]) == nav.fetch.req.body);
        // The third: every `Send` is a `Send` action of the transducer, which is a wire request.
        crate::net_theorems::lemma_carry_out_sends(urls, s1, c.tab, nav.partition, Some(conn), actions);
        clazel_fetch::transducer::theorems::theorem_wire_cookies(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
            Output::Send { bytes, .. } => crate::statements::ends_with(bytes, clazel_fetch::request::spec::body_bytes(nav.fetch.req)),
            _ => true,
        } by {
            if let Output::Send { conn: x, bytes } = out[k] {
                let a = choose|a: int| 0 <= a < actions.len() && actions[a] == clazel_fetch::transducer::spec::Action::Send(bytes);
                assert(actions[a] == clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now).1[a]);
                let cs = clazel_cookie::storage::spec::retrieve_cookie_string(
                    fetch.urls.rules,
                    s.jar,
                    (fetch.urls.request_url)(nav.fetch.url),
                    clazel_fetch::transducer::spec::request_context(fetch.urls, nav.fetch),
                    s.now,
                );
                assert(clazel_fetch::transducer::contract::is_wire_request(nav.fetch.url, nav.fetch.req, clazel_fetch::transducer::contract::carried(nav.fetch.url, nav.fetch.req, cs), bytes));
                lemma_wire_ends_with_body(nav.fetch.url, nav.fetch.req, clazel_fetch::transducer::contract::carried(nav.fetch.url, nav.fetch.req, cs), bytes);
            }
        }
    }
}

/// **`theorem_body_sent_once`** (item 6.16).
pub proof fn theorem_body_sent_once(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::body_sent_once_statement(rules, urls, fetch, s, e),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    match e {
        Event::FromRenderer { id, bytes } => {
            crate::theorems::theorem_reply_only_to_sender(rules, urls, fetch, s, id, bytes);
        },
        Event::NavigateTab { tab, url } => {
            crate::net_theorems::lemma_begin_outputs(rules, urls, fetch, s, tab, url, clazel_fetch::request::spec::get_req());
        },
        Event::SubmitTab { tab, url, req } => {
            crate::net_theorems::lemma_begin_outputs(rules, urls, fetch, s, tab, url, req);
        },
        Event::Net { conn, input } => {
            crate::net_wf::lemma_net_target(s, conn);
            match net_target(s, conn) {
                None => {
                    assert(step(rules, urls, fetch, s, e) == (s, seq![]));
                    assert(step(rules, urls, fetch, s, e).1 =~= Seq::<Output>::empty());
                },
                Some((c, i, nav)) => {
                    let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
                    let s1 = crate::net_theorems::net_mid(rules, fetch, s, conn, input, i, nav);
                    let out = carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions).1;
                    assert(step(rules, urls, fetch, s, e).1 == out);
                    crate::net_theorems::lemma_carry_out_sends(urls, s1, c.tab, nav.partition, Some(conn), actions);
                    clazel_fetch::transducer::theorems::lemma_sends_only_on_connected(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is Send implies nav.fetch.phase is Connecting && input is Connected && out.len() == 1 by {
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
                        }
                    }
                },
            }
        },
        _ => {},
    }
}

/// **`theorem_redirect_method`** (item 6.16), at the kernel.
pub proof fn theorem_redirect_method(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    ensures
        crate::statements::redirect_method_statement(rules, urls, fetch, s, conn, input),
{
    if let Some((_, _, nav)) = net_target(s, conn) {
        clazel_fetch::transducer::theorems::theorem_redirect_method(fetch.http, fetch.urls, nav.fetch, input, s.jar, s.now);
    }
}

/// **`theorem_post_cookies`** (item 6.16), at the kernel.
pub proof fn theorem_post_cookies(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::post_cookies_statement(rules, urls, fetch, s, conn, input),
{
    crate::net_theorems::theorem_wire_cookies(rules, urls, fetch, s, conn, input);
    if let Some((_, _, nav)) = net_target(s, conn) {
        clazel_fetch::transducer::theorems::theorem_post_cookies(fetch.urls, nav.fetch);
    }
}

} // verus!

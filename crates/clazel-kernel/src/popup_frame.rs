//! Item 7.16's `theorem_popup_needs_input`, the frame facts: which steps can
//! open a tab, and which can add or raise a user activation.
//!
//! [`frame_ok`] says a state `s1` is `s0` with, at most, activations that
//! have no more ticks than one of `s0`'s (the same renderer, the same lock)
//! and renderers that are in a tab of one of `s0`'s. Every function of the
//! step that does not itself open a tab or record an input satisfies it.
//! `popup_theorems.rs` builds the theorems on it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every entry of `a1` has an entry of `a0` with its id and its lock and at
/// least its ticks.
pub open spec fn acts_within(a1: Seq<Activation>, a0: Seq<Activation>) -> bool {
    forall|y: Activation|
        #[trigger] a1.contains(y) ==> exists|x: Activation| #[trigger] a0.contains(x) && x.id == y.id && x.lock == y.lock && y.left <= x.left
}

/// Every renderer of `r1` is in a tab of some renderer of `r0`.
pub open spec fn tabs_within(r1: Seq<Renderer>, r0: Seq<Renderer>) -> bool {
    forall|y: Renderer| #[trigger] r1.contains(y) ==> exists|x: Renderer| #[trigger] r0.contains(x) && x.tab == y.tab
}

/// `s1` adds no tab and no activation to `s0`'s.
pub open spec fn frame_ok(s0: State, s1: State) -> bool {
    &&& acts_within(s1.acts, s0.acts)
    &&& tabs_within(s1.renderers, s0.renderers)
}

/// [`acts_within`] is reflexive.
pub proof fn lemma_within_refl(a: Seq<Activation>)
    ensures
        acts_within(a, a),
{
    assert forall|y: Activation| #[trigger] a.contains(y) implies exists|x: Activation| #[trigger] a.contains(x) && x.id == y.id && x.lock == y.lock && y.left <= x.left by {
        assert(a.contains(y) && y.id == y.id);
    }
}

/// [`acts_within`] is transitive.
pub proof fn lemma_within_trans(a2: Seq<Activation>, a1: Seq<Activation>, a0: Seq<Activation>)
    requires
        acts_within(a2, a1),
        acts_within(a1, a0),
    ensures
        acts_within(a2, a0),
{
    assert forall|y: Activation| #[trigger] a2.contains(y) implies exists|x: Activation| #[trigger] a0.contains(x) && x.id == y.id && x.lock == y.lock && y.left <= x.left by {
        let m = choose|m: Activation| #[trigger] a1.contains(m) && m.id == y.id && m.lock == y.lock && y.left <= m.left;
        let x = choose|x: Activation| #[trigger] a0.contains(x) && x.id == m.id && x.lock == m.lock && m.left <= x.left;
        assert(a0.contains(x) && x.id == y.id && x.lock == y.lock && y.left <= x.left);
    }
}

/// [`tabs_within`] is reflexive.
pub proof fn lemma_tabs_refl(r: Seq<Renderer>)
    ensures
        tabs_within(r, r),
{
    assert forall|y: Renderer| #[trigger] r.contains(y) implies exists|x: Renderer| #[trigger] r.contains(x) && x.tab == y.tab by {
        assert(r.contains(y) && y.tab == y.tab);
    }
}

/// [`tabs_within`] is transitive.
pub proof fn lemma_tabs_trans(r2: Seq<Renderer>, r1: Seq<Renderer>, r0: Seq<Renderer>)
    requires
        tabs_within(r2, r1),
        tabs_within(r1, r0),
    ensures
        tabs_within(r2, r0),
{
    assert forall|y: Renderer| #[trigger] r2.contains(y) implies exists|x: Renderer| #[trigger] r0.contains(x) && x.tab == y.tab by {
        let m = choose|m: Renderer| #[trigger] r1.contains(m) && m.tab == y.tab;
        let x = choose|x: Renderer| #[trigger] r0.contains(x) && x.tab == m.tab;
        assert(r0.contains(x) && x.tab == y.tab);
    }
}

/// [`frame_ok`] is reflexive.
pub proof fn lemma_frame_refl(s: State)
    ensures
        frame_ok(s, s),
{
    lemma_within_refl(s.acts);
    lemma_tabs_refl(s.renderers);
}

/// [`frame_ok`] is transitive.
pub proof fn lemma_frame_trans(s2: State, s1: State, s0: State)
    requires
        frame_ok(s1, s2),
        frame_ok(s0, s1),
    ensures
        frame_ok(s0, s2),
{
    lemma_within_trans(s2.acts, s1.acts, s0.acts);
    lemma_tabs_trans(s2.renderers, s1.renderers, s0.renderers);
}

/// The same activations and renderers are within.
pub proof fn lemma_frame_same(s0: State, s1: State)
    requires
        s1.acts == s0.acts,
        s1.renderers == s0.renderers,
    ensures
        frame_ok(s0, s1),
{
    lemma_frame_refl(s0);
}

/// Forgetting an activation is within.
pub proof fn lemma_within_forget(a: Seq<Activation>, id: nat, lock: clazel_origin::spec::Origin)
    ensures
        acts_within(forget_activation(a, id, lock), a),
{
    let f = forget_activation(a, id, lock);
    assert forall|y: Activation| #[trigger] f.contains(y) implies exists|x: Activation| #[trigger] a.contains(x) && x.id == y.id && x.lock == y.lock && y.left <= x.left by {
        clazel_cookie::storage::isolation::lemma_filter_elem(a, |x: Activation| !(x.id == id && x.lock == lock), y);
        assert(a.contains(y) && y.id == y.id);
    }
}

/// Ageing is within.
pub proof fn lemma_within_age(a: Seq<Activation>)
    ensures
        acts_within(age_activations(a), a),
{
    let g = age_activations(a);
    assert forall|y: Activation| #[trigger] g.contains(y) implies exists|x: Activation| #[trigger] a.contains(x) && x.id == y.id && x.lock == y.lock && y.left <= x.left by {
        let k = choose|k: int| 0 <= k < g.len() && g[k] == y;
        assert(g[k] == crate::popup_rel::aged(a[k]));
        assert(a.contains(a[k]));
        assert(a[k].id == y.id && a[k].lock == y.lock && y.left <= a[k].left);
    }
}

/// Replacing a renderer by one in the same tab keeps [`tabs_within`].
pub proof fn lemma_tabs_update(rs: Seq<Renderer>, i: int, r: Renderer)
    requires
        0 <= i < rs.len(),
        r.tab == rs[i].tab,
    ensures
        tabs_within(rs.update(i, r), rs),
{
    let u = rs.update(i, r);
    assert forall|y: Renderer| #[trigger] u.contains(y) implies exists|x: Renderer| #[trigger] rs.contains(x) && x.tab == y.tab by {
        let k = choose|k: int| 0 <= k < u.len() && u[k] == y;
        if k == i {
            assert(rs.contains(rs[i]));
            assert(rs[i].tab == y.tab);
        } else {
            assert(u[k] == rs[k]);
            assert(rs.contains(rs[k]));
        }
    }
}

/// Removing a renderer keeps [`tabs_within`].
pub proof fn lemma_tabs_remove(rs: Seq<Renderer>, i: int)
    requires
        0 <= i < rs.len(),
    ensures
        tabs_within(rs.remove(i), rs),
{
    let u = rs.remove(i);
    assert forall|y: Renderer| #[trigger] u.contains(y) implies exists|x: Renderer| #[trigger] rs.contains(x) && x.tab == y.tab by {
        let k = choose|k: int| 0 <= k < u.len() && u[k] == y;
        let j = if k < i { k } else { k + 1 };
        assert(u[k] == rs[j]);
        assert(rs.contains(rs[j]));
    }
}

// ---------------------------------------------------------------------
// The functions of the step.
// ---------------------------------------------------------------------

/// `close_tab_conns` keeps [`frame_ok`].
pub proof fn lemma_close_frame(s: State, tab: nat)
    ensures
        frame_ok(s, close_tab_conns(s, tab).0),
{
    lemma_frame_same(s, close_tab_conns(s, tab).0);
}

/// `fail_navigation` of the renderer at `i` keeps [`frame_ok`].
pub proof fn lemma_fail_frame(s: State, i: int, old: Renderer, code: u64)
    requires
        0 <= i < s.renderers.len(),
        old.tab == s.renderers[i].tab,
    ensures
        frame_ok(s, fail_navigation(s, i, old, code).0),
{
    let r = Renderer { pending: None, ..old };
    lemma_tabs_update(s.renderers, i, r);
    lemma_within_refl(s.acts);
}

/// `navigate_tab` keeps [`frame_ok`]: a commit replaces a tab's renderer
/// and forgets an activation.
pub proof fn lemma_navigate_frame(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, doc: Document)
    ensures
        frame_ok(s, navigate_tab(urls, s, tab, url, doc).0),
{
    lemma_frame_refl(s);
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if let Some(lock) = lock_of_url(urls, url, s.next_id) {
            let old = s.renderers[i];
            if lock is Tuple && lock == old.lock {
                let r = Renderer { url, pending: None, committed: true, ..old };
                lemma_tabs_update(s.renderers, i, r);
                lemma_within_forget(s.acts, old.id, old.lock);
            } else {
                let id = s.next_id;
                let r = Renderer { committed: true, id, tab, url, lock, pending: None };
                lemma_tabs_update(s.renderers, i, r);
                lemma_within_refl(s.acts);
            }
        }
    }
}

/// `commit_navigation` keeps [`frame_ok`].
pub proof fn lemma_commit_frame(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, doc: Document)
    ensures
        frame_ok(s, commit_navigation(urls, s, tab, href, doc).0),
{
    let (s1, closes) = close_tab_conns(s, tab);
    lemma_close_frame(s, tab);
    crate::invariant::lemma_find_by_tab(s1.renderers, tab, 0);
    if let Some(i) = find_by_tab(s1.renderers, tab, 0) {
        if scalar_url(href) && lock_of_url(urls, href, s1.next_id) is Some {
            lemma_navigate_frame(urls, s1, tab, href, doc);
        } else {
            lemma_fail_frame(s1, i, s1.renderers[i], error_bad_url());
        }
        lemma_frame_trans(commit_navigation(urls, s, tab, href, doc).0, s1, s);
    }
}

/// `abort_navigation` keeps [`frame_ok`].
pub proof fn lemma_abort_frame(s: State, tab: nat, code: u64)
    ensures
        frame_ok(s, abort_navigation(s, tab, code).0),
{
    let (s1, closes) = close_tab_conns(s, tab);
    lemma_close_frame(s, tab);
    crate::invariant::lemma_find_by_tab(s1.renderers, tab, 0);
    if let Some(i) = find_by_tab(s1.renderers, tab, 0) {
        lemma_fail_frame(s1, i, s1.renderers[i], code);
        lemma_frame_trans(abort_navigation(s, tab, code).0, s1, s);
    }
}

/// `carry_out` keeps [`frame_ok`].
pub proof fn lemma_carry_out_frame(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    ensures
        frame_ok(s, carry_out(urls, s, tab, partition, cur, actions).0),
    decreases actions.len(),
{
    lemma_frame_refl(s);
    if actions.len() > 0 {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let (s1, id, out) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                lemma_frame_same(s, s1);
                lemma_carry_out_frame(urls, s1, tab, partition, Some(id), rest);
                lemma_frame_trans(carry_out(urls, s, tab, partition, cur, actions).0, s1, s);
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_frame(urls, s, tab, partition, cur, rest);
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    let s1 = State { conns: without_conn(s.conns, c), ..s };
                    lemma_frame_same(s, s1);
                    lemma_carry_out_frame(urls, s1, tab, partition, None, rest);
                    lemma_frame_trans(carry_out(urls, s, tab, partition, cur, actions).0, s1, s);
                },
                None => {
                    lemma_carry_out_frame(urls, s, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                lemma_commit_frame(urls, s, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response));
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                lemma_abort_frame(s, tab, error_fetch());
            },
        }
    }
}

/// `begin_navigation` keeps [`frame_ok`].
pub proof fn lemma_begin_frame(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    tab: nat,
    url: Seq<u32>,
    req: clazel_fetch::request::spec::Req,
)
    ensures
        frame_ok(s, begin_navigation(rules, urls, fetch, s, tab, url, req).0),
{
    lemma_frame_refl(s);
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if lock_of_url(urls, url, s.next_id) is Some {
            let (s0, closes) = close_tab_conns(s, tab);
            lemma_close_frame(s, tab);
            let old = s0.renderers[i];
            match (fetch.parse)(url) {
                None => {
                    lemma_fail_frame(s0, i, old, error_bad_url());
                    lemma_frame_trans(begin_navigation(rules, urls, fetch, s, tab, url, req).0, s0, s);
                },
                Some(parsed) => {
                    let (fs, actions) = clazel_fetch::transducer::spec::start_req(parsed, req);
                    let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                    let s1 = State { renderers: s0.renderers.update(i, Renderer { pending: Some(nav), ..old }), ..s0 };
                    lemma_tabs_update(s0.renderers, i, Renderer { pending: Some(nav), ..old });
                    lemma_within_refl(s0.acts);
                    lemma_carry_out_frame(urls, s1, tab, nav.partition, None, actions);
                    lemma_frame_trans(s1, s0, s);
                    lemma_frame_trans(begin_navigation(rules, urls, fetch, s, tab, url, req).0, s1, s);
                },
            }
        }
    }
}

/// `net` keeps [`frame_ok`].
pub proof fn lemma_net_frame(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    ensures
        frame_ok(s, net(rules, urls, fetch, s, conn, input).0),
{
    lemma_frame_refl(s);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        let conns = if input is Closed || input is Error {
            without_conn(s.conns, conn)
        } else {
            s.conns
        };
        let r = Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..s.renderers[i] };
        let s1 = State { jar: apply_net_ops(rules, s.jar, ops), conns, renderers: s.renderers.update(i, r), ..s };
        crate::net_wf::lemma_net_target(s, conn);
        lemma_tabs_update(s.renderers, i, r);
        lemma_within_refl(s.acts);
        lemma_carry_out_frame(urls, s1, c.tab, nav.partition, Some(conn), actions);
        lemma_frame_trans(net(rules, urls, fetch, s, conn, input).0, s1, s);
    }
}

/// Removing the renderer at `i` (a kill) keeps [`frame_ok`].
pub proof fn lemma_kill_frame(s: State, i: int, id: nat)
    requires
        0 <= i < s.renderers.len(),
    ensures
        frame_ok(s, kill_renderer(s, i, id).0),
{
    let (s0, closes) = close_tab_conns(s, s.renderers[i].tab);
    lemma_close_frame(s, s.renderers[i].tab);
    lemma_tabs_remove(s.renderers, i);
    lemma_within_refl(s.acts);
}

/// `open_tab` adds no activation: it adds one renderer, in a new tab, and
/// starts its fetch.
pub proof fn lemma_open_tab_acts(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, url: Seq<u32>, script: Option<Seq<u8>>)
    ensures
        acts_within(open_tab(rules, urls, fetch, s, url, script).0.acts, s.acts),
{
    lemma_within_refl(s.acts);
    let id = s.next_id;
    if let Some(lock) = lock_of_url(urls, url, id) {
        if script is None {
            let s1 = State { renderers: s.renderers.push(Renderer { committed: false, id, tab: id, url, lock, pending: None }), next_id: id + 1, ..s };
            lemma_begin_frame(rules, urls, fetch, s1, id, url, clazel_fetch::request::spec::get_req());
        }
    }
}

/// `handle_message` of any message but `OpenTab` keeps [`frame_ok`]; of an
/// `OpenTab` it adds no activation.
#[verifier::spinoff_prover]
#[verifier::rlimit(100)]
pub proof fn lemma_handle_frame(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    requires
        find_by_id(s.renderers, r.id, 0) is Some,
        s.renderers[find_by_id(s.renderers, r.id, 0)->Some_0] == r,
    ensures
        acts_within(handle_message(rules, urls, fetch, s, r, m).0.acts, s.acts),
        !(m is OpenTab) ==> frame_ok(s, handle_message(rules, urls, fetch, s, r, m).0),
{
    lemma_frame_refl(s);
    crate::invariant::lemma_find_by_id(s.renderers, r.id, 0);
    match m {
        clazel_ipc::message::spec::Message::Navigate { url } => {
            if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                if let Some(resolved) = (urls.resolve)(r.url, relative) {
                    if lock_of_url(urls, resolved, s.next_id) is Some {
                        lemma_begin_frame(rules, urls, fetch, s, r.tab, resolved, clazel_fetch::request::spec::get_req());
                    }
                }
            }
        },
        clazel_ipc::message::spec::Message::Submit { url, method, content_type, body } => {
            if let Some(req) = submit_request(r, method, content_type, body) {
                if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                    if let Some(resolved) = (urls.resolve)(r.url, relative) {
                        if lock_of_url(urls, resolved, s.next_id) is Some {
                            lemma_begin_frame(rules, urls, fetch, s, r.tab, resolved, req);
                        }
                    }
                }
            }
        },
        clazel_ipc::message::spec::Message::OpenTab { url } => {
            if activation_left(s.acts, r) > 0 {
                if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                    if let Some(resolved) = (urls.resolve)(r.url, relative) {
                        let s1 = open_tab(rules, urls, fetch, s, resolved, None).0;
                        lemma_open_tab_acts(rules, urls, fetch, s, resolved, None);
                        lemma_within_forget(s1.acts, r.id, r.lock);
                        lemma_within_trans(handle_message(rules, urls, fetch, s, r, m).0.acts, s1.acts, s.acts);
                    }
                }
            }
        },
        _ => {
            crate::lock::lemma_storage_call_frame(s, r, m);
        },
    }
}

} // verus!

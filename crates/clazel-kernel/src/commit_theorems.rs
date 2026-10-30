//! `theorem_committed_only_after_commit` (phase-4.md item 4.12), stated in
//! `statements.rs`: a renderer the kernel holds as committed was sent the
//! `commit_frames` write at its URL earlier in the run.
//!
//! The proof is an invariant over runs: every committed renderer of the
//! state has had its commit sent in the outputs so far ([`all_sent`]). Each
//! function of the step keeps it: a renderer whose id, URL and flag are
//! unchanged keeps the write it had, outputs only grow, and the two places
//! that set the flag (`navigate_tab` and `open_tab` with a script) output
//! the write in the same step.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Every committed renderer of `rs` was sent its commit in `out`.
pub open spec fn all_sent(rs: Seq<Renderer>, out: Seq<Output>) -> bool {
    forall|i: int| 0 <= i < rs.len() && (#[trigger] rs[i]).committed ==> crate::statements::commit_sent(out, rs[i].id, rs[i].url)
}

/// A commit sent in `out` is still sent after more outputs.
proof fn lemma_sent_prefix(out: Seq<Output>, more: Seq<Output>, id: nat, url: Seq<u32>)
    requires
        crate::statements::commit_sent(out, id, url),
    ensures
        crate::statements::commit_sent(out + more, id, url),
{
    let (k, doc) = choose|k: int, doc: Document|
        #![trigger out[k], commit_frames(url, doc)]
        0 <= k < out.len() && out[k] == Output::ToRenderer { id, bytes: commit_frames(url, doc) };
    assert((out + more)[k] == out[k]);
}

/// The commit `out` ends with is sent in `out`.
proof fn lemma_sent_last(before: Seq<Output>, id: nat, url: Seq<u32>, doc: Document)
    ensures
        crate::statements::commit_sent(before.push(Output::ToRenderer { id, bytes: commit_frames(url, doc) }), id, url),
{
    let out = before.push(Output::ToRenderer { id, bytes: commit_frames(url, doc) });
    let k = before.len() as int;
    assert(out[k] == Output::ToRenderer { id, bytes: commit_frames(url, doc) });
}

/// [`all_sent`] survives more outputs.
proof fn lemma_all_prefix(rs: Seq<Renderer>, out: Seq<Output>, more: Seq<Output>)
    requires
        all_sent(rs, out),
    ensures
        all_sent(rs, out + more),
{
    assert forall|i: int| 0 <= i < rs.len() && (#[trigger] rs[i]).committed implies crate::statements::commit_sent(out + more, rs[i].id, rs[i].url) by {
        lemma_sent_prefix(out, more, rs[i].id, rs[i].url);
    }
}

/// [`all_sent`] after replacing a renderer by one whose commit, if it is
/// committed, was sent.
proof fn lemma_all_update(rs: Seq<Renderer>, out: Seq<Output>, i: int, r: Renderer)
    requires
        all_sent(rs, out),
        0 <= i < rs.len(),
        r.committed ==> crate::statements::commit_sent(out, r.id, r.url),
    ensures
        all_sent(rs.update(i, r), out),
{
    let rs1 = rs.update(i, r);
    assert forall|j: int| 0 <= j < rs1.len() && (#[trigger] rs1[j]).committed implies crate::statements::commit_sent(out, rs1[j].id, rs1[j].url) by {
        if j != i {
            assert(rs1[j] == rs[j]);
        }
    }
}

/// [`all_sent`] after replacing renderer `i` by itself with another
/// navigation (the same id, URL and flag).
proof fn lemma_all_pending(rs: Seq<Renderer>, out: Seq<Output>, i: int, pending: Option<Navigation>)
    requires
        all_sent(rs, out),
        0 <= i < rs.len(),
    ensures
        all_sent(rs.update(i, Renderer { pending, ..rs[i] }), out),
{
    lemma_all_update(rs, out, i, Renderer { pending, ..rs[i] });
}

/// [`all_sent`] after removing a renderer.
proof fn lemma_all_remove(rs: Seq<Renderer>, out: Seq<Output>, i: int)
    requires
        all_sent(rs, out),
        0 <= i < rs.len(),
    ensures
        all_sent(rs.remove(i), out),
{
    let rs1 = rs.remove(i);
    assert forall|j: int| 0 <= j < rs1.len() && (#[trigger] rs1[j]).committed implies crate::statements::commit_sent(out, rs1[j].id, rs1[j].url) by {
        let m = if j < i { j } else { j + 1 };
        assert(rs1[j] == rs[m]);
    }
}

/// [`all_sent`] after adding a renderer whose commit, if it is committed,
/// was sent.
proof fn lemma_all_push(rs: Seq<Renderer>, out: Seq<Output>, r: Renderer)
    requires
        all_sent(rs, out),
        r.committed ==> crate::statements::commit_sent(out, r.id, r.url),
    ensures
        all_sent(rs.push(r), out),
{
    let rs1 = rs.push(r);
    assert forall|j: int| 0 <= j < rs1.len() && (#[trigger] rs1[j]).committed implies crate::statements::commit_sent(out, rs1[j].id, rs1[j].url) by {
        if j < rs.len() {
            assert(rs1[j] == rs[j]);
        }
    }
}

/// `navigate_tab` keeps [`all_sent`]: the renderer it commits is sent its
/// commit in the same outputs.
proof fn lemma_navigate_tab_sent(urls: UrlFns, s: State, o: Seq<Output>, tab: nat, url: Seq<u32>, doc: Document)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = navigate_tab(urls, s, tab, url, doc);
            all_sent(s1.renderers, o + out)
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    let (s1, out) = navigate_tab(urls, s, tab, url, doc);
    match find_by_tab(s.renderers, tab, 0) {
        None => {
            assert(o + out =~= o);
        },
        Some(i) => {
            let old = s.renderers[i];
            match lock_of_url(urls, url, s.next_id) {
                None => {
                    assert(o + out =~= o);
                },
                Some(lock) => {
                    if lock is Tuple && lock == old.lock {
                        let r = Renderer { url, pending: None, committed: true, ..old };
                        assert(o + out =~= o.push(Output::ToRenderer { id: old.id, bytes: commit_frames(url, doc) }));
                        lemma_all_prefix(s.renderers, o, out);
                        lemma_sent_last(o, old.id, url, doc);
                        lemma_all_update(s.renderers, o + out, i, r);
                    } else {
                        let id = s.next_id;
                        let r = Renderer { committed: true, id, tab, url, lock, pending: None };
                        let before = o + seq![Output::Kill { id: old.id }, Output::Spawn { id, policy: Policy::Renderer }];
                        assert(o + out =~= before.push(Output::ToRenderer { id, bytes: commit_frames(url, doc) }));
                        lemma_all_prefix(s.renderers, o, out);
                        lemma_sent_last(before, id, url, doc);
                        lemma_all_update(s.renderers, o + out, i, r);
                    }
                },
            }
        },
    }
}

/// `fail_navigation` keeps [`all_sent`].
proof fn lemma_fail_sent(s: State, o: Seq<Output>, i: int, code: u64)
    requires
        all_sent(s.renderers, o),
        0 <= i < s.renderers.len(),
    ensures
        ({
            let (s1, out) = fail_navigation(s, i, s.renderers[i], code);
            all_sent(s1.renderers, o + out)
        }),
{
    let out = fail_navigation(s, i, s.renderers[i], code).1;
    lemma_all_prefix(s.renderers, o, out);
    lemma_all_pending(s.renderers, o + out, i, None);
}

/// `commit_navigation` keeps [`all_sent`].
proof fn lemma_commit_sent(urls: UrlFns, s: State, o: Seq<Output>, tab: nat, href: Seq<u32>, doc: Document)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = commit_navigation(urls, s, tab, href, doc);
            all_sent(s1.renderers, o + out)
        }),
{
    let (s1, closes) = close_tab_conns(s, tab);
    lemma_all_prefix(s.renderers, o, closes);
    crate::invariant::lemma_find_by_tab(s1.renderers, tab, 0);
    match find_by_tab(s1.renderers, tab, 0) {
        None => {},
        Some(i) => {
            let (s2, out) = if scalar_url(href) && lock_of_url(urls, href, s1.next_id) is Some {
                lemma_navigate_tab_sent(urls, s1, o + closes, tab, href, doc);
                navigate_tab(urls, s1, tab, href, doc)
            } else {
                lemma_fail_sent(s1, o + closes, i, error_bad_url());
                fail_navigation(s1, i, s1.renderers[i], error_bad_url())
            };
            assert(o + (closes + out) =~= (o + closes) + out);
        },
    }
}

/// `abort_navigation` keeps [`all_sent`].
proof fn lemma_abort_sent(s: State, o: Seq<Output>, tab: nat, code: u64)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = abort_navigation(s, tab, code);
            all_sent(s1.renderers, o + out)
        }),
{
    let (s1, closes) = close_tab_conns(s, tab);
    lemma_all_prefix(s.renderers, o, closes);
    crate::invariant::lemma_find_by_tab(s1.renderers, tab, 0);
    match find_by_tab(s1.renderers, tab, 0) {
        None => {},
        Some(i) => {
            let out = fail_navigation(s1, i, s1.renderers[i], code).1;
            lemma_fail_sent(s1, o + closes, i, code);
            assert(o + (closes + out) =~= (o + closes) + out);
        },
    }
}

/// `carry_out` keeps [`all_sent`].
proof fn lemma_carry_out_sent(urls: UrlFns, s: State, o: Seq<Output>, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = carry_out(urls, s, tab, partition, cur, actions);
            all_sent(s1.renderers, o + out)
        }),
    decreases actions.len(),
{
    if actions.len() == 0 {
        assert(o + Seq::<Output>::empty() =~= o);
    } else {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let (s1, id, out) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                lemma_all_prefix(s.renderers, o, out);
                lemma_carry_out_sent(urls, s1, o + out, tab, partition, Some(id), rest);
                let out2 = carry_out(urls, s1, tab, partition, Some(id), rest).1;
                assert(o + (out + out2) =~= (o + out) + out2);
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => match cur {
                Some(c) => {
                    let first = seq![Output::Send { conn: c, bytes }];
                    lemma_all_prefix(s.renderers, o, first);
                    lemma_carry_out_sent(urls, s, o + first, tab, partition, cur, rest);
                    let out = carry_out(urls, s, tab, partition, cur, rest).1;
                    assert(o + (first + out) =~= (o + first) + out);
                },
                None => {
                    lemma_carry_out_sent(urls, s, o, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    let first = seq![Output::Close { conn: c }];
                    let s1 = State { conns: without_conn(s.conns, c), ..s };
                    lemma_all_prefix(s.renderers, o, first);
                    lemma_carry_out_sent(urls, s1, o + first, tab, partition, None, rest);
                    let out = carry_out(urls, s1, tab, partition, None, rest).1;
                    assert(o + (first + out) =~= (o + first) + out);
                },
                None => {
                    lemma_carry_out_sent(urls, s, o, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                lemma_commit_sent(urls, s, o, tab, clazel_url::url::spec::url_serializer(url, false), response_document(response));
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                lemma_abort_sent(s, o, tab, error_fetch());
            },
        }
    }
}

/// `begin_navigation` keeps [`all_sent`].
proof fn lemma_begin_sent(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, o: Seq<Output>, tab: nat, url: Seq<u32>)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = begin_navigation(rules, urls, fetch, s, tab, url);
            all_sent(s1.renderers, o + out)
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    let out = begin_navigation(rules, urls, fetch, s, tab, url).1;
    match find_by_tab(s.renderers, tab, 0) {
        None => {
            assert(o + out =~= o);
        },
        Some(i) => match lock_of_url(urls, url, s.next_id) {
            None => {
                assert(o + out =~= o);
            },
            Some(_) => {
                let (s0, closes) = close_tab_conns(s, tab);
                lemma_all_prefix(s.renderers, o, closes);
                let old = s0.renderers[i];
                match (fetch.parse)(url) {
                    None => {
                        lemma_fail_sent(s0, o + closes, i, error_bad_url());
                        let out1 = fail_navigation(s0, i, old, error_bad_url()).1;
                        assert(o + (closes + out1) =~= (o + closes) + out1);
                    },
                    Some(parsed) => {
                        let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                        let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                        let s1 = State { renderers: s0.renderers.update(i, Renderer { pending: Some(nav), ..old }), ..s0 };
                        lemma_all_pending(s0.renderers, o + closes, i, Some(nav));
                        lemma_carry_out_sent(urls, s1, o + closes, tab, nav.partition, None, actions);
                        let out1 = carry_out(urls, s1, tab, nav.partition, None, actions).1;
                        assert(o + (closes + out1) =~= (o + closes) + out1);
                    },
                }
            },
        },
    }
}

/// `open_tab` keeps [`all_sent`]: with a script, the renderer it adds
/// committed is sent its commit in the same outputs; without one, it is
/// added uncommitted.
proof fn lemma_open_tab_sent(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    o: Seq<Output>,
    url: Seq<u32>,
    script: Option<Seq<u8>>,
)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = open_tab(rules, urls, fetch, s, url, script);
            all_sent(s1.renderers, o + out)
        }),
{
    let id = s.next_id;
    let out = open_tab(rules, urls, fetch, s, url, script).1;
    match lock_of_url(urls, url, id) {
        None => {
            assert(o + out =~= o);
        },
        Some(lock) => match script {
            Some(script) => {
                let doc = script_document(script);
                let before = o + seq![Output::Spawn { id, policy: Policy::Renderer }];
                assert(o + out =~= before.push(Output::ToRenderer { id, bytes: commit_frames(url, doc) }));
                lemma_all_prefix(s.renderers, o, out);
                lemma_sent_last(before, id, url, doc);
                lemma_all_push(s.renderers, o + out, Renderer { committed: true, id, tab: id, url, lock, pending: None });
            },
            None => {
                let spawn = seq![Output::Spawn { id, policy: Policy::Renderer }];
                let s1 = State { renderers: s.renderers.push(Renderer { committed: false, id, tab: id, url, lock, pending: None }), next_id: id + 1, ..s };
                lemma_all_prefix(s.renderers, o, spawn);
                lemma_all_push(s.renderers, o + spawn, Renderer { committed: false, id, tab: id, url, lock, pending: None });
                lemma_begin_sent(rules, urls, fetch, s1, o + spawn, id, url);
                let out1 = begin_navigation(rules, urls, fetch, s1, id, url).1;
                assert(o + (spawn + out1) =~= (o + spawn) + out1);
            },
        },
    }
}

/// `net` keeps [`all_sent`].
proof fn lemma_net_sent(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, o: Seq<Output>, conn: nat, input: NetInput)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = net(rules, urls, fetch, s, conn, input);
            all_sent(s1.renderers, o + out)
        }),
{
    crate::net_wf::lemma_net_target(s, conn);
    match net_target(s, conn) {
        None => {
            assert(o + Seq::<Output>::empty() =~= o);
        },
        Some((c, i, nav)) => {
            let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
            let conns = if input is Closed || input is Error {
                without_conn(s.conns, conn)
            } else {
                s.conns
            };
            let s1 = State {
                jar: apply_net_ops(rules, s.jar, ops),
                conns,
                renderers: s.renderers.update(i, Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..s.renderers[i] }),
                ..s
            };
            lemma_all_pending(s.renderers, o, i, Some(Navigation { fetch: fs, ..nav }));
            lemma_carry_out_sent(urls, s1, o, c.tab, nav.partition, Some(conn), actions);
        },
    }
}

/// `handle_message` keeps [`all_sent`]: only `Navigate` changes the
/// renderers, through `begin_navigation`.
proof fn lemma_handle_message_sent(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    o: Seq<Output>,
    r: Renderer,
    m: clazel_ipc::message::spec::Message,
)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = handle_message(rules, urls, fetch, s, r, m);
            all_sent(s1.renderers, o + out)
        }),
{
    let (s1, out) = handle_message(rules, urls, fetch, s, r, m);
    crate::lock::lemma_storage_call_frame(s, r, m);
    lemma_all_prefix(s.renderers, o, out);
    if let clazel_ipc::message::spec::Message::Navigate { url } = m {
        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                if lock_of_url(urls, resolved, s.next_id) is Some {
                    lemma_begin_sent(rules, urls, fetch, s, o, r.tab, resolved);
                }
            }
        }
    } else {
        assert(s1.renderers == s.renderers);
    }
}

/// `step` keeps [`all_sent`].
proof fn lemma_step_sent(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, o: Seq<Output>, e: Event)
    requires
        all_sent(s.renderers, o),
    ensures
        ({
            let (s1, out) = step(rules, urls, fetch, s, e);
            all_sent(s1.renderers, o + out)
        }),
{
    let out = step(rules, urls, fetch, s, e).1;
    match e {
        Event::FromRenderer { id, bytes } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            match find_by_id(s.renderers, id, 0) {
                None => {
                    assert(o + out =~= o);
                },
                Some(i) => match accepted_message(s.renderers[i], bytes) {
                    None => {
                        lemma_all_prefix(s.renderers, o, out);
                        lemma_all_remove(s.renderers, o + out, i);
                    },
                    Some(m) => {
                        lemma_handle_message_sent(rules, urls, fetch, s, o, s.renderers[i], m);
                    },
                },
            }
        },
        Event::OpenTab { url, script } => {
            lemma_open_tab_sent(rules, urls, fetch, s, o, url, script);
        },
        Event::NavigateTab { tab, url } => {
            lemma_begin_sent(rules, urls, fetch, s, o, tab, url);
        },
        Event::Net { conn, input } => {
            lemma_net_sent(rules, urls, fetch, s, o, conn, input);
        },
        Event::RendererExited { id } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            lemma_all_prefix(s.renderers, o, out);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                lemma_all_remove(s.renderers, o + out, i);
            }
        },
        Event::Tick { time } => {
            lemma_all_prefix(s.renderers, o, out);
        },
    }
}

/// Running a trace keeps [`all_sent`].
proof fn lemma_run_sent(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, o: Seq<Output>, t: Seq<Event>)
    requires
        all_sent(s.renderers, o),
    ensures
        all_sent(run_state(rules, urls, fetch, s, t).renderers, o + run_outputs(rules, urls, fetch, s, t)),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(o + run_outputs(rules, urls, fetch, s, t) =~= o);
    } else {
        let (s1, out) = step(rules, urls, fetch, s, t[0]);
        lemma_step_sent(rules, urls, fetch, s, o, t[0]);
        lemma_run_sent(rules, urls, fetch, s1, o + out, t.drop_first());
        let rest = run_outputs(rules, urls, fetch, s1, t.drop_first());
        assert(o + (out + rest) =~= (o + out) + rest);
    }
}

/// **`theorem_committed_only_after_commit`.** Over every run from the
/// kernel's first state, each renderer the kernel holds as committed was sent
/// the `commit_frames` write at the URL the kernel holds for it.
pub proof fn theorem_committed_only_after_commit(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, t: Seq<Event>)
    ensures
        crate::statements::committed_only_after_commit_statement(rules, urls, fetch, t),
{
    let none = Seq::<Output>::empty();
    assert(all_sent(init_state().renderers, none));
    lemma_run_sent(rules, urls, fetch, init_state(), none, t);
    assert(none + run_outputs(rules, urls, fetch, init_state(), t) =~= run_outputs(rules, urls, fetch, init_state(), t));
}

/// The `Error` a failed navigation sends is not a commit: its octets do not
/// end with the frame of `BodyEnd`, which every commit's do.
pub proof fn lemma_error_is_not_a_commit(code: u64, url: Seq<u32>, doc: Document)
    requires
        code == error_bad_url(),
    ensures
        reply_frame(clazel_ipc::message::spec::Message::Error { code }) != commit_frames(url, doc),
{
    let e = reply_frame(clazel_ipc::message::spec::Message::Error { code: error_bad_url() });
    let b = reply_frame(clazel_ipc::message::spec::Message::BodyEnd);
    assert(!(reply_frame(clazel_ipc::message::spec::Message::Error { code: 3 }).len() >= reply_frame(clazel_ipc::message::spec::Message::BodyEnd).len() && reply_frame(clazel_ipc::message::spec::Message::Error { code: 3 }).subrange(reply_frame(clazel_ipc::message::spec::Message::Error { code: 3 }).len() - reply_frame(clazel_ipc::message::spec::Message::BodyEnd).len(), reply_frame(clazel_ipc::message::spec::Message::Error { code: 3 }).len() as int) == reply_frame(clazel_ipc::message::spec::Message::BodyEnd))) by (compute_only);
    let x = reply_frame(
        clazel_ipc::message::spec::Message::Commit { url: clazel_encoding::utf8::spec::utf8_encode(url), content_type: doc.content_type, kind: doc.kind },
    ) + body_frames(doc.body);
    assert(commit_frames(url, doc) == x + b);
    if e == commit_frames(url, doc) {
        assert(e.subrange(e.len() - b.len(), e.len() as int) =~= b);
    }
}

} // verus!

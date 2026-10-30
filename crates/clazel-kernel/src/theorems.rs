//! The isolation theorems of item 2.11 other than non-interference (that is
//! `unwinding.rs`): each is a `theorem_*` lemma, over every `UrlFns`, every
//! reachable state and every event, whose `ensures` is the predicate in
//! `statements.rs` of the same name.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// In a well-formed table, the renderer found by the tab of renderer `i` is
/// `i` itself.
pub proof fn lemma_find_by_tab_self(urls: UrlFns, s: State, i: int)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
        0 <= i < s.renderers.len(),
    ensures
        find_by_tab(s.renderers, s.renderers[i].tab, 0) == Some(i),
{
    crate::invariant::lemma_find_by_tab(s.renderers, s.renderers[i].tab, 0);
    match find_by_tab(s.renderers, s.renderers[i].tab, 0) {
        Some(k) => {
            if k != i {
                if k < i {
                    assert(s.renderers[k].tab != s.renderers[i].tab);
                } else {
                    assert(s.renderers[i].tab != s.renderers[k].tab);
                }
            }
        },
        None => {
            assert(s.renderers[i].tab == s.renderers[i].tab);
        },
    }
}

/// In a well-formed table, the renderer found by id has that id.
pub proof fn lemma_find_by_id_some(s: State, id: nat)
    ensures
        match find_by_id(s.renderers, id, 0) {
            Some(i) => 0 <= i < s.renderers.len() && s.renderers[i].id == id,
            None => forall|k: int| 0 <= k < s.renderers.len() ==> (#[trigger] s.renderers[k]).id != id,
        },
{
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
}

/// The outputs of `navigate_tab` for a well-formed table: addressed to the
/// renderer of the tab, or to the renderer spawned.
pub proof fn lemma_navigate_tab_outputs(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, script: Document)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        ({
            let out = navigate_tab(urls, s, tab, url, script).1;
            forall|k: int|
                0 <= k < out.len() ==> match #[trigger] out[k] {
                    Output::ToRenderer { id: x, .. } => (exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x)
                        || (x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Renderer })),
                    Output::Spawn { id: x, .. } => x == s.next_id,
                    Output::Kill { id: x } => exists|i: int| 0 <= i < s.renderers.len() && s.renderers[i].tab == tab && s.renderers[i].id == x,
                    Output::Show { .. } => false,
                    Output::Connect { .. } | Output::Send { .. } | Output::Close { .. } => false,
                }
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        let old = s.renderers[i];
        if let Some(lock) = lock_of_url(urls, url, s.next_id) {
            let out = navigate_tab(urls, s, tab, url, script).1;
            if lock is Tuple && lock == old.lock {
                assert(out[0] == (Output::ToRenderer { id: old.id, bytes: commit_frames(url, script) }));
                assert(out.len() == 1);
            } else {
                assert(out.len() == 3);
                assert(out[0] == (Output::Kill { id: old.id }));
                assert(out[1] == (Output::Spawn { id: s.next_id, policy: Policy::Renderer }));
                assert(out[2] == (Output::ToRenderer { id: s.next_id, bytes: commit_frames(url, script) }));
                assert(out.contains(out[1]));
            }
        }
    }
}

/// **`theorem_reply_only_to_sender`.**
pub proof fn theorem_reply_only_to_sender(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::reply_only_to_sender_statement(rules, urls, fetch, s, id, bytes),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    let (s1, out) = step(rules, urls, fetch, s, Event::FromRenderer { id, bytes });
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        match accepted_message(r, bytes) {
            None => {
                crate::net_theorems::lemma_closes_of_tab(s.conns, r.tab);
                let closes = closes_of_tab(s.conns, r.tab);
                assert(out == seq![Output::Kill { id }] + closes);
                assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                    Output::ToRenderer { id: x, .. } => x == id || (x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Renderer })),
                    Output::Spawn { id: x, .. } => x == s.next_id,
                    Output::Kill { id: x } => x == id,
                    Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                    Output::Send { .. } => false,
                    Output::Show { .. } => false,
                    Output::Close { conn: x } => exists|i2: int, j: int|
                        0 <= i2 < s.renderers.len() && 0 <= j < s.conns.len() && s.renderers[i2].id == id && s.conns[j].id == x && s.conns[j].tab == s.renderers[i2].tab,
                } by {
                    if k > 0 {
                        assert(out[k] == closes[k - 1]);
                        match closes[k - 1] {
                            Output::Close { conn: x } => {
                                let j = choose|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == r.tab;
                            },
                            _ => {},
                        }
                    }
                }
            },
            Some(m) => {
                if let clazel_ipc::message::spec::Message::Display { title, text, links } = m {
                    lemma_reply_display(rules, urls, fetch, s, id, bytes, i);
                } else if let clazel_ipc::message::spec::Message::Navigate { url } = m {
                    if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                        if let Some(resolved) = (urls.resolve)(r.url, relative) {
                            if lock_of_url(urls, resolved, s.next_id) is Some {
                                crate::net_theorems::lemma_begin_outputs(rules, urls, fetch, s, r.tab, resolved);
                                assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                                    Output::ToRenderer { id: x, .. } => x == id || (x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Renderer })),
                                    Output::Spawn { id: x, .. } => x == s.next_id,
                                    Output::Kill { id: x } => x == id,
                                    Output::Connect { conn: x, .. } => s.next_conn <= x < s1.next_conn,
                                    Output::Send { .. } => false,
                                    Output::Show { .. } => false,
                                    Output::Close { conn: x } => exists|i2: int, j: int|
                                        0 <= i2 < s.renderers.len() && 0 <= j < s.conns.len() && s.renderers[i2].id == id && s.conns[j].id == x && s.conns[j].tab == s.renderers[i2].tab,
                                } by {
                                    match out[k] {
                                        Output::ToRenderer { id: x, .. } => {
                                            let i2 = choose|i2: int| 0 <= i2 < s.renderers.len() && s.renderers[i2].tab == r.tab && s.renderers[i2].id == x;
                                            tab_unique(urls, s, i, i2);
                                        },
                                        Output::Close { conn: x } => {
                                            let j = choose|j: int| 0 <= j < s.conns.len() && s.conns[j].id == x && s.conns[j].tab == r.tab;
                                        },
                                        _ => {},
                                    }
                                }
                            }
                        }
                    }
                }
            },
        }
    }
}

/// `theorem_reply_only_to_sender` for a `Display` (item 4.12): one `Show`,
/// for the sender's tab.
proof fn lemma_reply_display(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_id(s.renderers, id, 0) == Some(i),
        s.renderers[i].id == id,
        accepted_message(s.renderers[i], bytes) matches Some(m) && m is Display,
    ensures
        crate::statements::reply_only_to_sender_statement(rules, urls, fetch, s, id, bytes),
{
    let r = s.renderers[i];
    let m = accepted_message(r, bytes)->Some_0;
    let out = step(rules, urls, fetch, s, Event::FromRenderer { id, bytes }).1;
    assert(out == seq![Output::Show { tab: r.tab, url: r.url, title: m->Display_title, text: m->Display_text, links: m->Display_links }]);
}

/// Two renderers of a well-formed table with the same tab are the same.
pub proof fn tab_unique(urls: UrlFns, s: State, i: int, j: int)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
        0 <= i < s.renderers.len(),
        0 <= j < s.renderers.len(),
        s.renderers[i].tab == s.renderers[j].tab,
    ensures
        i == j,
{
    if i < j {
        assert(s.renderers[i].tab != s.renderers[j].tab);
    } else if j < i {
        assert(s.renderers[j].tab != s.renderers[i].tab);
    }
}

} // verus!

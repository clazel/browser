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
pub proof fn lemma_navigate_tab_outputs(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, script: Seq<u8>)
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
                    Output::Fetch { .. } => false,
                }
        }),
{
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        let old = s.renderers[i];
        if let Some(lock) = lock_of_url(urls, url, s.next_id) {
            let out = navigate_tab(urls, s, tab, url, script).1;
            if lock is Tuple && lock == old.lock {
                assert(out[0] == (Output::ToRenderer { id: old.id, bytes: commit_frame(url, script) }));
                assert(out.len() == 1);
            } else {
                assert(out.len() == 3);
                assert(out[0] == (Output::Kill { id: old.id }));
                assert(out[1] == (Output::Spawn { id: s.next_id, policy: Policy::Renderer }));
                assert(out[2] == (Output::ToRenderer { id: s.next_id, bytes: commit_frame(url, script) }));
                assert(out.contains(out[1]));
            }
        }
    }
}

/// The outputs of `begin_navigation`: nothing, or one `Fetch` for the tab asked.
pub proof fn lemma_begin_navigation_outputs(urls: UrlFns, s: State, tab: nat, url: Seq<u32>)
    ensures
        ({
            let out = begin_navigation(urls, s, tab, url).1;
            out == Seq::<Output>::empty() || out == seq![Output::Fetch { tab, url }]
        }),
{
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
    let out = step(rules, urls, fetch, s, Event::FromRenderer { id, bytes }).1;
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        if let Some(m) = decode_renderer_frame(bytes) {
            if let clazel_ipc::message::spec::Message::Navigate { url } = m {
                if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                    if let Some(resolved) = (urls.resolve)(r.url, relative) {
                        if lock_of_url(urls, resolved, s.next_id) is Some {
                            lemma_begin_navigation_outputs(urls, s, r.tab, resolved);
                            assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                                Output::ToRenderer { id: x, .. } => x == id || (x == s.next_id && out.contains(Output::Spawn { id: x, policy: Policy::Renderer })),
                                Output::Spawn { id: x, .. } => x == s.next_id,
                                Output::Kill { id: x } => x == id,
                                Output::Fetch { tab: x, .. } => exists|j: int| 0 <= j < s.renderers.len() && s.renderers[j].id == id && s.renderers[j].tab == x,
                            } by {
                                assert(out == seq![Output::Fetch { tab: r.tab, url: resolved }]);
                                assert(s.renderers[i].id == id && s.renderers[i].tab == r.tab);
                            }
                        }
                    }
                }
            }
        }
    }
}

/// **`theorem_fetched_only_to_tab`** (item 3.7).
pub proof fn theorem_fetched_only_to_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::fetched_only_to_tab_statement(rules, urls, fetch, s, tab, outcome),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    let out = step(rules, urls, fetch, s, Event::Fetched { tab, outcome }).1;
    if let Some(run) = fetched_run(fetch, s, tab, outcome) {
        let i = find_by_tab(s.renderers, tab, 0)->Some_0;
        let old = s.renderers[i];
        let s1 = State { jar: apply_stores(rules, s.jar, run.stores, s.now), ..s };
        match run.result {
            FetchResult::Done { url, body } => {
                if scalar_url(url) && lock_of_url(urls, url, s1.next_id) is Some {
                    lemma_navigate_tab_outputs(urls, s1, tab, url, body);
                } else {
                    assert(out == seq![Output::ToRenderer { id: old.id, bytes: reply_frame(clazel_ipc::message::spec::Message::Error { code: error_bad_url() }) }]);
                }
            },
            FetchResult::Failed => {
                assert(out == seq![Output::ToRenderer { id: old.id, bytes: reply_frame(clazel_ipc::message::spec::Message::Error { code: error_fetch() }) }]);
            },
        }
    }
}

/// **`theorem_fetched_answers_navigation`** (item 3.7).
pub proof fn theorem_fetched_answers_navigation(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, outcome: NetOutcome)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::fetched_answers_navigation_statement(rules, urls, fetch, s, tab, outcome),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    let (s1, out) = step(rules, urls, fetch, s, Event::Fetched { tab, outcome });
    if let Some(run) = fetched_run(fetch, s, tab, outcome) {
        let i = find_by_tab(s.renderers, tab, 0)->Some_0;
        let old = s.renderers[i];
        let sp = State { jar: apply_stores(rules, s.jar, run.stores, s.now), ..s };
        let ok = match run.result {
            FetchResult::Done { url, body } => scalar_url(url) && lock_of_url(urls, url, sp.next_id) is Some,
            FetchResult::Failed => false,
        };
        if ok {
            let url = run.result->Done_url;
            let body = run.result->Done_body;
            let lock = lock_of_url(urls, url, sp.next_id)->Some_0;
            assert forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab implies s1.renderers[j].pending is None by {
                if lock is Tuple && lock == old.lock {
                    if j != i {
                        assert(s1.renderers[j] == s.renderers[j]);
                        assert(s.renderers[j].tab != tab || j == i);
                        tab_unique(urls, s, i, j);
                    }
                } else {
                    if j != i {
                        assert(s1.renderers[j] == s.renderers[j]);
                        tab_unique(urls, s, i, j);
                    }
                }
            }
        } else {
            assert forall|j: int| 0 <= j < s1.renderers.len() && (#[trigger] s1.renderers[j]).tab == tab implies s1.renderers[j].pending is None by {
                if j != i {
                    assert(s1.renderers[j] == s.renderers[j]);
                    tab_unique(urls, s, i, j);
                }
            }
        }
    }
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

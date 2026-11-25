//! `theorem_popup_needs_input` and `theorem_no_javascript_url` (phase-7.md
//! item 7.16), stated in `statements.rs`.
//!
//! The proof of the popup theorem has three parts:
//! - which steps can open a tab, and which can add or raise an activation
//!   (`popup_frame.rs`: every function but the popup's keeps [`frame_ok`]);
//! - where an activation comes from, over a run ([`lemma_run_acts`]): an
//!   entry with ticks left is a pre-existing one with more ticks, or was set
//!   by an activating `Input` the kernel delivered to the renderer, after
//!   which fewer than the window's `Tick`s came;
//! - the popup itself, which opens a tab only on a live entry and spends it
//!   ([`theorem_popup_needs_activation`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Reading an activation.
// ---------------------------------------------------------------------

/// A renderer with no entry has no ticks left.
pub proof fn lemma_left_none(acts: Seq<Activation>, r: Renderer)
    requires
        forall|k: int| 0 <= k < acts.len() ==> !((#[trigger] acts[k]).id == r.id && acts[k].lock == r.lock),
    ensures
        activation_left(acts, r) == 0,
    decreases acts.len(),
{
    if acts.len() > 0 {
        let rest = acts.drop_first();
        assert forall|k: int| 0 <= k < rest.len() implies !((#[trigger] rest[k]).id == r.id && rest[k].lock == r.lock) by {
            assert(rest[k] == acts[k + 1]);
        }
        lemma_left_none(rest, r);
    }
}

/// A renderer with ticks left has an entry with them.
pub proof fn lemma_left_entry(acts: Seq<Activation>, r: Renderer)
    requires
        activation_left(acts, r) > 0,
    ensures
        exists|k: int| 0 <= k < acts.len() && (#[trigger] acts[k]).id == r.id && acts[k].lock == r.lock && acts[k].left == activation_left(acts, r),
    decreases acts.len(),
{
    if acts.len() > 0 {
        if acts[0].id == r.id && acts[0].lock == r.lock {
            assert(acts[0].left == activation_left(acts, r));
        } else {
            let rest = acts.drop_first();
            lemma_left_entry(rest, r);
            let k = choose|k: int| 0 <= k < rest.len() && (#[trigger] rest[k]).id == r.id && rest[k].lock == r.lock && rest[k].left == activation_left(rest, r);
            assert(rest[k] == acts[k + 1]);
        }
    }
}

/// After forgetting a renderer's activation, within or not, it has none.
pub proof fn lemma_forgotten_left(acts: Seq<Activation>, a1: Seq<Activation>, r: Renderer)
    requires
        crate::popup_frame::acts_within(a1, forget_activation(acts, r.id, r.lock)),
    ensures
        activation_left(a1, r) == 0,
{
    let f = forget_activation(acts, r.id, r.lock);
    assert forall|k: int| 0 <= k < a1.len() implies !((#[trigger] a1[k]).id == r.id && a1[k].lock == r.lock) by {
        assert(a1.contains(a1[k]));
        let x = choose|x: Activation| #[trigger] f.contains(x) && x.id == a1[k].id && x.lock == a1[k].lock && a1[k].left <= x.left;
        clazel_cookie::storage::isolation::lemma_filter_elem(acts, |x: Activation| !(x.id == r.id && x.lock == r.lock), x);
    }
    lemma_left_none(a1, r);
}

// ---------------------------------------------------------------------
// The step.
// ---------------------------------------------------------------------

/// A frame of renderer `r` that is an accepted `OpenTab`.
pub open spec fn is_popup_frame(r: Renderer, bytes: Seq<u8>) -> bool {
    accepted_message(r, bytes) matches Some(clazel_ipc::message::spec::Message::OpenTab { .. })
}

/// The event is a renderer's frame that is an accepted `OpenTab` of the
/// renderer `find_by_id` finds.
pub open spec fn popup_frame_of(s: State, e: Event) -> bool {
    e is FromRenderer && (find_by_id(s.renderers, e->FromRenderer_id, 0) matches Some(i) && is_popup_frame(s.renderers[i], e->FromRenderer_bytes))
}

/// How a step changes the tabs and the activations: no event but a host's
/// `OpenTab` and a renderer's accepted `OpenTab` frame adds a tab, and no
/// event but an `Input` adds or raises an activation.
pub proof fn lemma_step_frame(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        ({
            let s1 = step(rules, urls, fetch, s, e).0;
            &&& crate::popup_frame::acts_within(s1.acts, s.acts) || e is Input
            &&& (e is OpenTab || e is Input || popup_frame_of(s, e)) || crate::popup_frame::tabs_within(s1.renderers, s.renderers)
        }),
{
    let s1 = step(rules, urls, fetch, s, e).0;
    crate::popup_frame::lemma_frame_refl(s);
    match e {
        Event::FromRenderer { id, bytes } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let r = s.renderers[i];
                match accepted_message(r, bytes) {
                    None => {
                        crate::popup_frame::lemma_kill_frame(s, i, id);
                    },
                    Some(m) => {
                        crate::popup_frame::lemma_handle_frame(rules, urls, fetch, s, r, m);
                        if m is OpenTab {
                            assert(is_popup_frame(r, bytes));
                            assert(popup_frame_of(s, e));
                        }
                    },
                }
            }
        },
        Event::OpenTab { url, script } => {
            crate::popup_frame::lemma_open_tab_acts(rules, urls, fetch, s, url, script);
        },
        Event::NavigateTab { tab, url } => {
            crate::popup_frame::lemma_begin_frame(rules, urls, fetch, s, tab, url, clazel_fetch::request::spec::get_req());
        },
        Event::SubmitTab { tab, url, req } => {
            crate::popup_frame::lemma_begin_frame(rules, urls, fetch, s, tab, url, req);
        },
        Event::Net { conn, input } => {
            crate::popup_frame::lemma_net_frame(rules, urls, fetch, s, conn, input);
        },
        Event::RendererExited { id } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let (s0, closes) = close_tab_conns(s, s.renderers[i].tab);
                crate::popup_frame::lemma_close_frame(s, s.renderers[i].tab);
                crate::popup_frame::lemma_tabs_remove(s.renderers, i);
            }
        },
        Event::Tick { time } => {
            crate::popup_frame::lemma_within_age(s.acts);
        },
        Event::FromGpu { id, bytes } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            crate::surface_rel::lemma_from_gpu_shape(s, id, bytes);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                if crate::surface_rel::gpu_kills(s.renderers[i], bytes) {
                    crate::popup_frame::lemma_kill_frame(s, i, id);
                }
            }
        },
        Event::GpuExited { id } => {
            crate::gpu_theorems::theorem_gpu_exit_contained(rules, urls, fetch, s, id);
        },
        Event::Resize { .. } | Event::GpuSoftware | Event::GpuSiteExit { .. } | Event::SubNet { .. } | Event::Input { .. } => {},
    }
}

// ---------------------------------------------------------------------
// Where an activation comes from.
// ---------------------------------------------------------------------

/// The `Tick`s `e` counts as: one for a `Tick`, none for another event.
pub open spec fn tick_of(e: Event) -> nat {
    if e is Tick {
        1nat
    } else {
        0nat
    }
}

/// An entry `a` of the activations after `e` has a source: an entry of the
/// activations before it, with the ticks `a` has and the tick `e` is; or `e`
/// is an activating `Input` to the committed renderer `a` is for, which set
/// it to the window.
pub open spec fn acts_origin(s: State, e: Event, a: Activation) -> bool {
    (exists|j: int| 0 <= j < s.acts.len() && (#[trigger] s.acts[j]).id == a.id && s.acts[j].lock == a.lock && a.left + tick_of(e) <= s.acts[j].left) || (e is Input
        && is_activating_input(e->Input_input) && exists|i: int|
        find_by_tab(s.renderers, e->Input_tab, 0) == Some(i) && s.renderers[i].id == a.id && s.renderers[i].committed && a.left <= activation_window())
}

/// Every entry with ticks left after a step has a source ([`acts_origin`]).
pub proof fn lemma_step_origin(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        forall|k: int| 0 <= k < step(rules, urls, fetch, s, e).0.acts.len() && (#[trigger] step(rules, urls, fetch, s, e).0.acts[k]).left > 0 ==> acts_origin(s, e, step(rules, urls, fetch, s, e).0.acts[k]),
{
    let s1 = step(rules, urls, fetch, s, e).0;
    lemma_step_frame(rules, urls, fetch, s, e);
    match e {
        Event::Input { tab, input } => {
            crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
            if let Some(i) = find_by_tab(s.renderers, tab, 0) {
                let r = s.renderers[i];
                if r.committed && is_activating_input(input) {
                    let f = forget_activation(s.acts, r.id, r.lock);
                    assert forall|k: int| 0 <= k < s1.acts.len() && (#[trigger] s1.acts[k]).left > 0 implies acts_origin(s, e, s1.acts[k]) by {
                        if k < f.len() {
                            assert(s1.acts[k] == f[k]);
                            assert(f.contains(f[k]));
                            clazel_cookie::storage::isolation::lemma_filter_elem(s.acts, |x: Activation| !(x.id == r.id && x.lock == r.lock), f[k]);
                            let j = choose|j: int| 0 <= j < s.acts.len() && s.acts[j] == f[k];
                            assert(s.acts[j].id == f[k].id);
                        } else {
                            assert(s1.acts[k] == Activation { id: r.id, lock: r.lock, left: activation_window() });
                        }
                    }
                } else {
                    assert(s1.acts == s.acts);
                    assert forall|k: int| 0 <= k < s1.acts.len() && (#[trigger] s1.acts[k]).left > 0 implies acts_origin(s, e, s1.acts[k]) by {
                        assert(s.acts[k].id == s1.acts[k].id);
                    }
                }
            }
        },
        Event::Tick { time } => {
            assert(s1.acts == age_activations(s.acts));
            assert forall|k: int| 0 <= k < s1.acts.len() && (#[trigger] s1.acts[k]).left > 0 implies acts_origin(s, e, s1.acts[k]) by {
                assert(s1.acts[k] == crate::popup_rel::aged(s.acts[k]));
                assert(s.acts[k].id == s1.acts[k].id);
            }
        },
        _ => {
            assert forall|k: int| 0 <= k < s1.acts.len() && (#[trigger] s1.acts[k]).left > 0 implies acts_origin(s, e, s1.acts[k]) by {
                assert(s1.acts.contains(s1.acts[k]));
                let x = choose|x: Activation| #[trigger] s.acts.contains(x) && x.id == s1.acts[k].id && x.lock == s1.acts[k].lock && s1.acts[k].left <= x.left;
                let j = choose|j: int| 0 <= j < s.acts.len() && s.acts[j] == x;
                assert(tick_of(e) == 0);
            }
        },
    }
}

/// A source of an entry over a run, the first kind: an entry of `s0` with
/// the ticks `left` and the run's `Tick`s.
pub open spec fn act_kept(s0: State, t: Seq<Event>, a: Activation) -> bool {
    exists|j: int| 0 <= j < s0.acts.len() && (#[trigger] s0.acts[j]).id == a.id && s0.acts[j].lock == a.lock && a.left + crate::statements::tick_count(t) <= s0.acts[j].left
}

/// A source of an entry over a run, the second kind: an activating `Input`
/// of the run delivered to renderer `a.id`, with the window not yet gone.
pub open spec fn act_witness(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s0: State, t: Seq<Event>, a: Activation) -> bool {
    exists|j: int|
        0 <= j < t.len() && (#[trigger] t[j]) is Input && is_activating_input(t[j]->Input_input) && step(rules, urls, fetch, run_state(rules, urls, fetch, s0, t.take(j)), t[j]).1
            == seq![Output::ToRenderer { id: a.id, bytes: input_frame(t[j]->Input_input) }] && a.left + crate::statements::tick_count(t.subrange(j + 1, t.len() as int)) <= activation_window()
}

/// Every entry with ticks left after a run has a source: one of the
/// start's with more ticks, or an `Input` of the run within the window.
pub proof fn lemma_run_acts(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s0: State, t: Seq<Event>)
    ensures
        forall|k: int|
            0 <= k < run_state(rules, urls, fetch, s0, t).acts.len() && (#[trigger] run_state(rules, urls, fetch, s0, t).acts[k]).left > 0 ==> act_kept(
                s0,
                t,
                run_state(rules, urls, fetch, s0, t).acts[k],
            ) || act_witness(rules, urls, fetch, s0, t, run_state(rules, urls, fetch, s0, t).acts[k]),
    decreases t.len(),
{
    // Sub-fetches (and item 7.16's ORB on how they end) have nothing to do
    // with activations (`lemma_step_origin` says how an entry changes);
    // hidden to keep the step's unfolding within the rlimit.
    hide(api_finish);
    hide(sub_net);
    hide(fetch_api);
    let fin = run_state(rules, urls, fetch, s0, t);
    if t.len() == 0 {
        assert forall|k: int| 0 <= k < fin.acts.len() && (#[trigger] fin.acts[k]).left > 0 implies act_kept(s0, t, fin.acts[k]) by {
            assert(fin == s0);
            assert(crate::statements::tick_count(t) == 0);
            assert(s0.acts[k].id == fin.acts[k].id);
        }
    } else {
        let e = t[0];
        let rest = t.drop_first();
        let s1 = step(rules, urls, fetch, s0, e).0;
        assert(fin == run_state(rules, urls, fetch, s1, rest));
        lemma_run_acts(rules, urls, fetch, s1, rest);
        lemma_step_origin(rules, urls, fetch, s0, e);
        assert(crate::statements::tick_count(t) == crate::statements::tick_count(rest) + tick_of(e));
        assert forall|k: int| 0 <= k < fin.acts.len() && (#[trigger] fin.acts[k]).left > 0 implies act_kept(s0, t, fin.acts[k]) || act_witness(rules, urls, fetch, s0, t, fin.acts[k]) by {
            let a = fin.acts[k];
            if act_kept(s1, rest, a) {
                let m = choose|m: int| 0 <= m < s1.acts.len() && (#[trigger] s1.acts[m]).id == a.id && s1.acts[m].lock == a.lock && a.left + crate::statements::tick_count(rest) <= s1.acts[m].left;
                assert(s1.acts[m].left > 0);
                assert(acts_origin(s0, e, s1.acts[m]));
                if exists|j: int| 0 <= j < s0.acts.len() && (#[trigger] s0.acts[j]).id == s1.acts[m].id && s0.acts[j].lock == s1.acts[m].lock && s1.acts[m].left + tick_of(e) <= s0.acts[j].left {
                    let j = choose|j: int| 0 <= j < s0.acts.len() && (#[trigger] s0.acts[j]).id == s1.acts[m].id && s0.acts[j].lock == s1.acts[m].lock && s1.acts[m].left + tick_of(e) <= s0.acts[j].left;
                    assert(act_kept(s0, t, a));
                } else {
                    // `e` is an activating `Input` to the committed renderer `a` is for.
                    assert(e is Input && is_activating_input(e->Input_input));
                    let i = choose|i: int| find_by_tab(s0.renderers, e->Input_tab, 0) == Some(i) && s0.renderers[i].id == s1.acts[m].id && s0.renderers[i].committed && s1.acts[m].left <= activation_window();
                    assert(step(rules, urls, fetch, s0, e).1 == seq![Output::ToRenderer { id: a.id, bytes: input_frame(e->Input_input) }]);
                    assert(t.take(0) =~= Seq::<Event>::empty());
                    assert(run_state(rules, urls, fetch, s0, t.take(0)) == s0);
                    assert(t.subrange(1, t.len() as int) =~= rest);
                    assert(act_witness(rules, urls, fetch, s0, t, a)) by {
                        assert(t[0] is Input && is_activating_input(t[0]->Input_input));
                    }
                }
            } else {
                assert(act_witness(rules, urls, fetch, s1, rest, a));
                let jj = choose|jj: int|
                    0 <= jj < rest.len() && (#[trigger] rest[jj]) is Input && is_activating_input(rest[jj]->Input_input) && step(rules, urls, fetch, run_state(rules, urls, fetch, s1, rest.take(jj)), rest[jj]).1
                        == seq![Output::ToRenderer { id: a.id, bytes: input_frame(rest[jj]->Input_input) }] && a.left + crate::statements::tick_count(rest.subrange(jj + 1, rest.len() as int)) <= activation_window();
                let j = jj + 1;
                assert(t[j] == rest[jj]);
                assert(t.take(j).drop_first() =~= rest.take(jj));
                assert(t.take(j)[0] == e);
                assert(run_state(rules, urls, fetch, s0, t.take(j)) == run_state(rules, urls, fetch, s1, rest.take(jj)));
                assert(t.subrange(j + 1, t.len() as int) =~= rest.subrange(jj + 1, rest.len() as int));
                assert(act_witness(rules, urls, fetch, s0, t, a));
            }
        }
    }
}

// ---------------------------------------------------------------------
// The theorems.
// ---------------------------------------------------------------------

/// The step of a popup: a step on `FromRenderer { id, bytes }` that opens a
/// tab was an accepted `OpenTab` of a committed sender that held a live
/// activation, and spent it.
pub proof fn theorem_popup_needs_activation(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    ensures
        crate::statements::popup_needs_activation_statement(rules, urls, fetch, s, id, bytes),
{
    let e = Event::FromRenderer { id, bytes };
    let s1 = step(rules, urls, fetch, s, e).0;
    lemma_step_frame(rules, urls, fetch, s, e);
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    if crate::statements::new_tab_in(s, s1) {
        // A new tab is a renderer in a tab no renderer was in: the step is
        // not one that keeps the tabs.
        assert(!crate::popup_frame::tabs_within(s1.renderers, s.renderers)) by {
            let i = choose|i: int| 0 <= i < s1.renderers.len() && !crate::statements::tab_open(s.renderers, (#[trigger] s1.renderers[i]).tab);
            if crate::popup_frame::tabs_within(s1.renderers, s.renderers) {
                assert(s1.renderers.contains(s1.renderers[i]));
                let x = choose|x: Renderer| #[trigger] s.renderers.contains(x) && x.tab == s1.renderers[i].tab;
                let j = choose|j: int| 0 <= j < s.renderers.len() && s.renderers[j] == x;
                assert(crate::statements::tab_open(s.renderers, s1.renderers[i].tab));
            }
        }
        let i = find_by_id(s.renderers, id, 0)->Some_0;
        let r = s.renderers[i];
        assert(is_popup_frame(r, bytes));
        if let Some(clazel_ipc::message::spec::Message::OpenTab { url }) = accepted_message(r, bytes) {
            assert(r.committed);
            if activation_left(s.acts, r) == 0 {
                assert(s1 == s);
                assert(false);
            } else {
                if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                    if let Some(resolved) = (urls.resolve)(r.url, relative) {
                        let so = open_tab(rules, urls, fetch, s, resolved, None).0;
                        crate::popup_frame::lemma_open_tab_acts(rules, urls, fetch, s, resolved, None);
                        crate::popup_frame::lemma_within_refl(forget_activation(so.acts, r.id, r.lock));
                        lemma_forgotten_left(so.acts, s1.acts, r);
                    } else {
                        assert(s1 == s);
                        assert(false);
                    }
                } else {
                    assert(s1 == s);
                    assert(false);
                }
            }
        }
    }
}

/// **`theorem_popup_needs_input`** (phase-7.md item 7.16): over every run
/// from the kernel's first state, a frame of a renderer that opens a tab
/// follows an activating `Input` the kernel delivered to that renderer,
/// with fewer than [`activation_window`] `Tick`s since.
pub proof fn theorem_popup_needs_input(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, u: Seq<Event>, id: nat, bytes: Seq<u8>)
    ensures
        crate::statements::popup_needs_input_statement(rules, urls, fetch, u, id, bytes),
{
    let s = run_state(rules, urls, fetch, init_state(), u);
    let e = Event::FromRenderer { id, bytes };
    let s1 = step(rules, urls, fetch, s, e).0;
    theorem_popup_needs_activation(rules, urls, fetch, s, id, bytes);
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    if crate::statements::new_tab_in(s, s1) {
        let i = find_by_id(s.renderers, id, 0)->Some_0;
        let r = s.renderers[i];
        assert(activation_left(s.acts, r) > 0);
        lemma_left_entry(s.acts, r);
        let k = choose|k: int| 0 <= k < s.acts.len() && (#[trigger] s.acts[k]).id == r.id && s.acts[k].lock == r.lock && s.acts[k].left == activation_left(s.acts, r);
        lemma_run_acts(rules, urls, fetch, init_state(), u);
        let a = s.acts[k];
        assert(!act_kept(init_state(), u, a));
        assert(act_witness(rules, urls, fetch, init_state(), u, a));
        let j = choose|j: int|
            0 <= j < u.len() && (#[trigger] u[j]) is Input && is_activating_input(u[j]->Input_input) && step(rules, urls, fetch, run_state(rules, urls, fetch, init_state(), u.take(j)), u[j]).1
                == seq![Output::ToRenderer { id: a.id, bytes: input_frame(u[j]->Input_input) }] && a.left + crate::statements::tick_count(u.subrange(j + 1, u.len() as int)) <= activation_window();
        assert(a.id == id);
    }
}

/// **`theorem_no_javascript_url`** (phase-7.md item 7.16): in every
/// reachable state no renderer holds, and no document URL is, a URL whose
/// scheme is `javascript`; and the entry points refuse one.
pub proof fn theorem_no_javascript_url(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::no_javascript_url_statement(urls, s),
        forall|url: Seq<u32>, script: Option<Seq<u8>>, tab: nat, doc: Document|
            #[trigger] crate::statements::javascript_refused_statement(rules, urls, fetch, s, url, script, tab, doc),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    assert forall|i: int| 0 <= i < s.renderers.len() implies !(urls.is_javascript)((#[trigger] s.renderers[i]).url) by {
        assert(lock_of_url(urls, s.renderers[i].url, s.renderers[i].id) == Some(s.renderers[i].lock));
    }
    assert forall|k: int| 0 <= k < s.doc_urls.len() implies !(urls.is_javascript)((#[trigger] s.doc_urls[k]).url) by {
        assert(lock_of_url(urls, s.doc_urls[k].url, s.doc_urls[k].id) == Some(s.doc_urls[k].lock));
    }
    assert forall|url: Seq<u32>, script: Option<Seq<u8>>, tab: nat, doc: Document| #[trigger] crate::statements::javascript_refused_statement(rules, urls, fetch, s, url, script, tab, doc) by {
        if (urls.is_javascript)(url) {
            assert(lock_of_url(urls, url, s.next_id) is None);
            assert(step(rules, urls, fetch, s, Event::OpenTab { url, script }) == (s, Seq::<Output>::empty()));
            assert(navigate_tab(urls, s, tab, url, doc) == (s, Seq::<Output>::empty()));
        }
    }
}

} // verus!

//! Lemmas the kill certificates of `mutations.json` for item 7.16's popups
//! and `javascript:` refusal instantiate: the core fact each rule of
//! `open_tab_from`, the activations and `lock_of_url` rests on, phrased so
//! that a concrete instance can be evaluated by Verus's `compute_only`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The opaque lock 0: the lock of the renderer of [`mp_state`].
pub open spec fn mp_lock() -> clazel_origin::spec::Origin {
    clazel_origin::spec::Origin::Opaque(0nat)
}

/// A committed renderer, id 0 and tab 0, at the URL `a`.
pub open spec fn mp_renderer() -> Renderer {
    Renderer { committed: true, id: 0, tab: 0, url: seq![0x61u32], lock: mp_lock(), pending: None }
}

/// The same renderer, not committed.
pub open spec fn mp_uncommitted() -> Renderer {
    Renderer { committed: false, ..mp_renderer() }
}

/// A state with [`mp_renderer`] and no activation.
pub open spec fn mp_state_none() -> State {
    State { renderers: seq![mp_renderer()], next_id: 1, ..init_state() }
}

/// A state with [`mp_renderer`] and an activation with `left` ticks.
pub open spec fn mp_state(left: nat) -> State {
    State { acts: seq![Activation { id: 0, lock: mp_lock(), left }], ..mp_state_none() }
}

/// A state with [`mp_uncommitted`] and no activation.
pub open spec fn mp_state_uncommitted() -> State {
    State { renderers: seq![mp_uncommitted()], next_id: 1, ..init_state() }
}

/// URL functions under which a URL resolves to itself, has an opaque origin
/// and is a `javascript:` URL.
pub open spec fn mp_urls_js() -> UrlFns {
    UrlFns {
        origin_of: |u: Seq<u32>| Some(clazel_origin::spec::Origin::Opaque(7nat)),
        path_of: |u: Seq<u32>| Seq::<u8>::empty(),
        is_javascript: |u: Seq<u32>| true,
        resolve: |b: Seq<u32>, i: Seq<u32>| Some(i),
    }
}

/// [`crate::mutation_lemmas::ml_commit_state`] with an activation of its
/// renderer.
pub open spec fn mp_commit_state() -> State {
    State {
        acts: seq![Activation { id: 0, lock: crate::mutation_lemmas::ml_tuple(seq![0x68u32, 0x74, 0x74, 0x70]), left: 3 }],
        ..crate::mutation_lemmas::ml_commit_state()
    }
}

/// A click.
pub open spec fn mp_click() -> UserInput {
    UserInput { kind: 0, x: 1, y: 2, negative: false, delta: 0, key: 0 }
}

/// A scroll.
pub open spec fn mp_scroll() -> UserInput {
    UserInput { kind: 1, x: 1, y: 2, negative: false, delta: 0, key: 0 }
}

/// A renderer with no live activation opens nothing and changes nothing.
pub proof fn mp_popup_refused(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, url: Seq<u8>)
    requires
        activation_left(s.acts, r) == 0,
    ensures
        open_tab_from(rules, urls, fetch, s, r, url) == (s, Seq::<Output>::empty()),
{
}

/// A popup spends the sender's activation.
pub proof fn mp_popup_spends(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, resolved: Seq<u32>)
    ensures
        activation_left(popup_result(rules, urls, fetch, s, r, resolved).0.acts, r) == 0,
{
    let so = open_tab(rules, urls, fetch, s, resolved, None).0;
    crate::popup_frame::lemma_open_tab_acts(rules, urls, fetch, s, resolved, None);
    crate::popup_frame::lemma_within_refl(forget_activation(so.acts, r.id, r.lock));
    crate::popup_theorems::lemma_forgotten_left(so.acts, forget_activation(so.acts, r.id, r.lock), r);
}

/// A scroll is not a user activation: it leaves the activations alone.
pub proof fn mp_scroll_no_activation(s: State, tab: nat, input: UserInput)
    requires
        input.kind == 1,
    ensures
        user_input(s, tab, input).0.acts == s.acts,
{
}

/// An input to a renderer that has not committed is no activation.
pub proof fn mp_uncommitted_input(s: State, tab: nat, input: UserInput, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        !s.renderers[i].committed,
    ensures
        user_input(s, tab, input).0.acts == s.acts,
{
}

/// An activating input gives the renderer of its tab ticks left.
pub proof fn mp_input_activates_own(s: State, tab: nat, input: UserInput, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        s.renderers[i].committed,
        is_activating_input(input),
        activation_window() > 0,
    ensures
        activation_left(user_input(s, tab, input).0.acts, s.renderers[i]) > 0,
{
    let r = s.renderers[i];
    let f = forget_activation(s.acts, r.id, r.lock);
    let acts = set_activation(s.acts, r.id, r.lock, activation_window());
    assert forall|k: int| 0 <= k < f.len() implies !((#[trigger] f[k]).id == r.id && f[k].lock == r.lock) by {
        assert(f.contains(f[k]));
        clazel_cookie::storage::isolation::lemma_filter_elem(s.acts, |x: Activation| !(x.id == r.id && x.lock == r.lock), f[k]);
    }
    mp_act_push(f, r, Activation { id: r.id, lock: r.lock, left: activation_window() });
    assert(user_input(s, tab, input).0.acts == acts);
}

/// [`activation_left`] of entries none of which is `r`'s, then one that is.
pub proof fn mp_act_push(f: Seq<Activation>, r: Renderer, x: Activation)
    requires
        forall|k: int| 0 <= k < f.len() ==> !((#[trigger] f[k]).id == r.id && f[k].lock == r.lock),
        x.id == r.id,
        x.lock == r.lock,
    ensures
        activation_left(f.push(x), r) == x.left,
    decreases f.len(),
{
    if f.len() == 0 {
        assert(f.push(x)[0] == x);
    } else {
        let g = f.drop_first();
        assert(f.push(x)[0] == f[0]);
        assert(f.push(x).drop_first() =~= g.push(x));
        assert forall|k: int| 0 <= k < g.len() implies !((#[trigger] g[k]).id == r.id && g[k].lock == r.lock) by {
            assert(g[k] == f[k + 1]);
        }
        mp_act_push(g, r, x);
    }
}

/// The window is not empty.
pub proof fn mp_window_positive()
    ensures
        activation_window() > 0,
{
}

/// A `Tick` takes a tick off every activation that has one left.
pub proof fn mp_tick_ages(s: State, time: int, k: int)
    requires
        0 <= k < s.acts.len(),
        s.acts[k].left > 0,
    ensures
        tick(s, time).0.acts[k].left < s.acts[k].left,
{
}

/// A commit to the same renderer forgets its activation.
pub proof fn mp_commit_forgets_activation(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, doc: Document, i: int, lock: clazel_origin::spec::Origin)
    requires
        0 <= i < s.renderers.len(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        lock_of_url(urls, url, s.next_id) == Some(lock),
        lock is Tuple,
        lock == s.renderers[i].lock,
    ensures
        navigate_tab(urls, s, tab, url, doc).0.acts == forget_activation(s.acts, s.renderers[i].id, lock),
{
}

/// A renderer that has not committed may not send `OpenTab`.
pub proof fn mp_uncommitted_popup(r: Renderer, bytes: Seq<u8>)
    requires
        !r.committed,
        decode_renderer_frame(bytes) matches Some(m) && m is OpenTab,
    ensures
        accepted_message(r, bytes) is None,
{
}

/// A popup without a live activation has no declassified part: nothing
/// another domain's observers see of it.
pub proof fn mp_declassified_needs_activation(urls: UrlFns, s: State, id: nat, bytes: Seq<u8>, i: int)
    requires
        0 <= i < s.renderers.len(),
        find_by_id(s.renderers, id, 0) == Some(i),
        activation_left(s.acts, s.renderers[i]) == 0,
        decode_renderer_frame(bytes) matches Some(m) && m is OpenTab,
    ensures
        crate::domain::declassified(urls, s, Event::FromRenderer { id, bytes }) is None,
{
}

/// A `javascript:` URL has no lock.
pub proof fn mp_javascript_refused(urls: UrlFns, url: Seq<u32>, id: nat)
    requires
        (urls.is_javascript)(url),
    ensures
        lock_of_url(urls, url, id) is None,
{
}

/// The scheme the shipped kernel refuses is `javascript`.
pub proof fn mp_javascript_scheme()
    ensures
        crate::urls::javascript_scheme() == seq![0x6Au32, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74],
{
}

} // verus!

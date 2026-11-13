//! Phase 5 item 5.18's theorems, stated in `statements.rs`: a GPU process's
//! frame is painted only in its own tab, under the URL and title the kernel
//! holds there, within the tab's viewport (`theorem_paint_only_own_tab`,
//! `theorem_address_bar_integrity`'s second half,
//! `theorem_paint_fits_viewport`); a GPU process is started only with the
//! renderer of its id, and written to only for its own tab
//! (`theorem_channel_only_own_tab`); and the user's input and the host's
//! viewport go only to their own tab's processes
//! (`theorem_input_only_to_own_tab`, `theorem_viewport_only_to_own_tab`).
//! None assumes anything of the GPU process: they hold for every frame it
//! can send.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// No output of `out` is a `Paint`, a `Spawn` or a `ToGpu`.
pub open spec fn no_surface(out: Seq<Output>) -> bool {
    forall|k: int| 0 <= k < out.len() ==> !((#[trigger] out[k]) is Paint || out[k] is Spawn || out[k] is ToGpu)
}

/// `a + b` has none if neither has.
proof fn lemma_no_surface_concat(a: Seq<Output>, b: Seq<Output>)
    requires
        no_surface(a),
        no_surface(b),
    ensures
        no_surface(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies !(#[trigger] (a + b)[k] is Paint || (a + b)[k] is Spawn || (a + b)[k] is ToGpu) by {
        if k >= a.len() {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// The `Close`s of a tab have none.
proof fn lemma_closes_no_surface(conns: Seq<Connection>, tab: nat)
    ensures
        no_surface(closes_of_tab(conns, tab)),
{
    crate::net_theorems::lemma_closes_of_tab(conns, tab);
}

/// `begin_navigation` (which never commits: the transducer's `start` only
/// connects or fails) has none.
proof fn lemma_begin_no_surface(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        no_surface(begin_navigation(rules, urls, fetch, s, tab, url).1),
{
    crate::net_theorems::lemma_begin_outputs(rules, urls, fetch, s, tab, url);
}

/// A `localStorage` call has none.
proof fn lemma_storage_call_no_surface(s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    ensures
        no_surface(storage_call(s, r, m).1),
{
    let list = storage_of(s, r.lock);
    match m {
        clazel_ipc::message::spec::Message::StorageGetItem { key } => {
            let _ = find_key(list, key, 0);
        },
        clazel_ipc::message::spec::Message::StorageSetItem { key, value } => {
            let _ = find_key(list, key, 0);
        },
        _ => {},
    }
}

/// A renderer's frame has none: it is answered with replies, starts a
/// navigation, shows, or kills its sender.
proof fn lemma_from_renderer_no_surface(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        no_surface(step(rules, urls, fetch, s, Event::FromRenderer { id, bytes }).1),
{
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        match accepted_message(r, bytes) {
            None => {
                lemma_closes_no_surface(s.conns, r.tab);
                lemma_no_surface_concat(seq![Output::Kill { id }], closes_of_tab(s.conns, r.tab));
            },
            Some(m) => match m {
                clazel_ipc::message::spec::Message::Navigate { url } => {
                    if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                        if let Some(resolved) = (urls.resolve)(r.url, relative) {
                            if lock_of_url(urls, resolved, s.next_id) is Some {
                                lemma_begin_no_surface(rules, urls, fetch, s, r.tab, resolved);
                            }
                        }
                    }
                },
                clazel_ipc::message::spec::Message::StorageGetItem { .. }
                | clazel_ipc::message::spec::Message::StorageSetItem { .. }
                | clazel_ipc::message::spec::Message::StorageRemoveItem { .. }
                | clazel_ipc::message::spec::Message::StorageClear
                | clazel_ipc::message::spec::Message::StorageKey { .. }
                | clazel_ipc::message::spec::Message::StorageLength => {
                    if !(r.lock is Opaque) {
                        lemma_storage_call_no_surface(s, r, m);
                    }
                },
                clazel_ipc::message::spec::Message::FetchStyle { request, url } => {
                    crate::subfetch_rel::lemma_fetch_style_shape(rules, urls, fetch, s, r, request, url);
                },
                _ => {},
            },
        }
    }
}

/// Item 5.19's events (a `Tick`'s sweep, a `SubNet`) have none.
proof fn lemma_subfetch_events_no_surface(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        e is Tick || e is SubNet,
    ensures
        no_surface(step(rules, urls, fetch, s, e).1),
{
    match e {
        Event::Tick { time } => crate::subfetch_rel::lemma_tick_all_shape(s, time),
        Event::SubNet { renderer, serial, hop, input } => crate::subfetch_rel::lemma_sub_net_shape(rules, fetch, s, renderer, serial, hop, input),
        _ => {},
    }
}

/// Every event but a GPU process's frame paints nothing.
proof fn lemma_no_paint_but_gpu(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
        !(e is FromGpu),
    ensures
        forall|k: int| 0 <= k < step(rules, urls, fetch, s, e).1.len() ==> !((#[trigger] step(rules, urls, fetch, s, e).1[k]) is Paint),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    let out = step(rules, urls, fetch, s, e).1;
    match e {
        Event::FromRenderer { id, bytes } => {
            lemma_from_renderer_no_surface(rules, urls, fetch, s, id, bytes);
        },
        Event::OpenTab { url, script } => {
            let id = s.next_id;
            if let Some(lock) = lock_of_url(urls, url, id) {
                if script is None {
                    let rn = Renderer { committed: false, id, tab: id, url, lock, pending: None };
                    let sp = State { renderers: s.renderers.push(rn), next_id: id + 1, ..s };
                    crate::invariant::lemma_open_tab_push_wf(rules, urls, s, url, lock, false);
                    lemma_begin_no_surface(rules, urls, fetch, sp, id, url);
                    let ob = begin_navigation(rules, urls, fetch, sp, id, url).1;
                    assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Paint) by {
                        if k >= 2 {
                            assert(out[k] == ob[k - 2]);
                        }
                    }
                }
            }
        },
        Event::NavigateTab { tab, url } => {
            lemma_begin_no_surface(rules, urls, fetch, s, tab, url);
        },
        Event::Net { conn, input } => {
            crate::net_theorems::theorem_net_only_to_tab(rules, urls, fetch, s, conn, input);
            assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Paint) by {
                match out[k] {
                    Output::Paint { .. } => {},
                    _ => {},
                }
            }
        },
        Event::RendererExited { id } => {
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                lemma_closes_no_surface(s.conns, s.renderers[i].tab);
            }
        },
        Event::Resize { tab, width, height, scale } => {
            assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Paint) by {
                if find_by_tab(s.renderers, tab, 0) is Some {
                    assert(k == 0 || k == 1);
                }
            }
        },
        Event::Tick { .. } | Event::SubNet { .. } => {
            lemma_subfetch_events_no_surface(rules, urls, fetch, s, e);
        },
        _ => {},
    }
}

/// **`theorem_paint_only_own_tab`** (item 5.18).
pub proof fn theorem_paint_only_own_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::paint_only_own_tab_statement(rules, urls, fetch, s, e),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    let (s1, out) = step(rules, urls, fetch, s, e);
    match e {
        Event::FromGpu { id, bytes } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            crate::surface_rel::lemma_from_gpu_shape(s, id, bytes);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let r = s.renderers[i];
                if crate::surface_rel::gpu_kills(r, bytes) {
                    let closes = closes_of_tab(s.conns, r.tab);
                    crate::net_theorems::lemma_closes_of_tab(s.conns, r.tab);
                    assert(out == seq![Output::Kill { id }] + closes);
                    assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                        Output::Paint { tab: x, .. } => exists|i2: int| 0 <= i2 < s.renderers.len() && s.renderers[i2].id == id && s.renderers[i2].tab == x,
                        Output::Kill { id: x } => x == id,
                        Output::Close { conn: x } => exists|i2: int, j: int|
                            0 <= i2 < s.renderers.len() && 0 <= j < s.conns.len() && s.renderers[i2].id == id && s.conns[j].id == x && s.conns[j].tab
                                == s.renderers[i2].tab,
                        _ => false,
                    } && !(out[k] is Paint) by {
                        if k > 0 {
                            assert(out[k] == closes[k - 1]);
                            match closes[k - 1] {
                                Output::Close { conn: x } => {
                                    let j = choose|j: int| 0 <= j < s.conns.len() && (#[trigger] s.conns[j]).id == x && s.conns[j].tab == r.tab;
                                },
                                _ => {},
                            }
                        }
                    }
                } else {
                    assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
                        Output::Paint { tab: x, .. } => exists|i2: int| 0 <= i2 < s.renderers.len() && s.renderers[i2].id == id && s.renderers[i2].tab == x,
                        Output::Kill { id: x } => x == id,
                        Output::Close { conn: x } => exists|i2: int, j: int|
                            0 <= i2 < s.renderers.len() && 0 <= j < s.conns.len() && s.renderers[i2].id == id && s.conns[j].id == x && s.conns[j].tab
                                == s.renderers[i2].tab,
                        _ => false,
                    } by {
                        assert(k == 0);
                    }
                }
            }
        },
        _ => {
            lemma_no_paint_but_gpu(rules, urls, fetch, s, e);
        },
    }
}

/// **`theorem_address_bar_integrity`, second half** (item 5.18): see
/// `crate::display_theorems::theorem_address_bar_integrity`, which ensures
/// both halves.
pub proof fn lemma_paint_address_bar(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    ensures
        crate::statements::paint_address_bar_statement(rules, urls, fetch, s, id, bytes),
{
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    crate::surface_rel::lemma_from_gpu_shape(s, id, bytes);
    let out = step(rules, urls, fetch, s, Event::FromGpu { id, bytes }).1;
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        if crate::surface_rel::gpu_kills(r, bytes) {
            crate::net_theorems::lemma_closes_of_tab(s.conns, r.tab);
            let closes = closes_of_tab(s.conns, r.tab);
            assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is Paint implies exists|i2: int|
                0 <= i2 < s.renderers.len() && s.renderers[i2].id == id && s.renderers[i2].committed && out[k]->Paint_url == s.renderers[i2].url
                    && out[k]->Paint_tab == s.renderers[i2].tab && out[k]->Paint_title == title_of(s.titles, s.renderers[i2]) by {
                if k > 0 {
                    assert(out[k] == closes[k - 1]);
                }
            }
        } else {
            assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is Paint implies exists|i2: int|
                0 <= i2 < s.renderers.len() && s.renderers[i2].id == id && s.renderers[i2].committed && out[k]->Paint_url == s.renderers[i2].url
                    && out[k]->Paint_tab == s.renderers[i2].tab && out[k]->Paint_title == title_of(s.titles, s.renderers[i2]) by {
                assert(k == 0);
            }
        }
    }
}

/// **`theorem_paint_fits_viewport`** (item 5.18).
pub proof fn theorem_paint_fits_viewport(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::paint_fits_viewport_statement(rules, urls, fetch, s, e),
{
    let out = step(rules, urls, fetch, s, e).1;
    match e {
        Event::FromGpu { id, bytes } => {
            crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            crate::surface_rel::lemma_from_gpu_shape(s, id, bytes);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let r = s.renderers[i];
                if crate::surface_rel::gpu_kills(r, bytes) {
                    crate::net_theorems::lemma_closes_of_tab(s.conns, r.tab);
                    let closes = closes_of_tab(s.conns, r.tab);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is Paint implies {
                        &&& out[k]->Paint_width <= viewport_of(s, out[k]->Paint_tab).width
                        &&& out[k]->Paint_height <= viewport_of(s, out[k]->Paint_tab).height
                        &&& out[k]->Paint_buffer < ring_size()
                    } by {
                        if k > 0 {
                            assert(out[k] == closes[k - 1]);
                        }
                    }
                } else {
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is Paint implies {
                        &&& out[k]->Paint_width <= viewport_of(s, out[k]->Paint_tab).width
                        &&& out[k]->Paint_height <= viewport_of(s, out[k]->Paint_tab).height
                        &&& out[k]->Paint_buffer < ring_size()
                    } by {
                        assert(k == 0);
                    }
                }
            }
        },
        _ => {
            lemma_no_paint_but_gpu(rules, urls, fetch, s, e);
        },
    }
}

/// **`theorem_input_only_to_own_tab`** (item 5.18).
pub proof fn theorem_input_only_to_own_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, input: UserInput)
    ensures
        crate::statements::input_only_to_own_tab_statement(rules, urls, fetch, s, tab, input),
{
}

/// **`theorem_viewport_only_to_own_tab`** (item 5.18).
pub proof fn theorem_viewport_only_to_own_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, width: u64, height: u64, scale: u64)
    ensures
        crate::statements::viewport_only_to_own_tab_statement(rules, urls, fetch, s, tab, width, height, scale),
{
    let v = Viewport { width, height, scale };
    let s1 = step(rules, urls, fetch, s, Event::Resize { tab, width, height, scale }).0;
    let vs = s.viewports.filter(|x: TabViewport| x.tab != tab);
    assert(s1.viewports == vs.push(TabViewport { tab, viewport: v }));
    // The new entry is the only one of `tab`, and the others are the old ones
    // of their tabs, in order.
    assert forall|j: int| 0 <= j < vs.len() implies (#[trigger] vs[j]).tab != tab by {
        s.viewports.lemma_filter_pred(|x: TabViewport| x.tab != tab, j);
    }
    lemma_find_viewport_last(vs, tab, v, 0);
    assert forall|t: nat| t != tab implies viewport_of(s1, t) == viewport_of(s, t) by {
        lemma_find_viewport_other(s.viewports, tab, v, t);
    }
}

/// [`find_viewport`] over entries of other tabs, then the new one.
proof fn lemma_find_viewport_last(vs: Seq<TabViewport>, tab: nat, v: Viewport, i: nat)
    requires
        i <= vs.len(),
        forall|j: int| 0 <= j < vs.len() ==> (#[trigger] vs[j]).tab != tab,
    ensures
        find_viewport(vs.push(TabViewport { tab, viewport: v }), tab, i) == Some(v),
    decreases vs.len() - i,
{
    let w = vs.push(TabViewport { tab, viewport: v });
    if i < vs.len() {
        assert(w[i as int] == vs[i as int]);
        lemma_find_viewport_last(vs, tab, v, i + 1);
    } else {
        assert(w[i as int].tab == tab);
    }
}

/// [`find_viewport`] of another tab after [`set_viewport`] of `tab`: as
/// before.
proof fn lemma_find_viewport_other(vs: Seq<TabViewport>, tab: nat, v: Viewport, t: nat)
    requires
        t != tab,
    ensures
        find_viewport(set_viewport(vs, tab, v), t, 0) == find_viewport(vs, t, 0),
    decreases vs.len(),
{
    reveal(Seq::filter);
    if vs.len() > 0 {
        let x = vs[0];
        let rest = vs.drop_first();
        assert(vs =~= seq![x] + rest);
        let p = |x: TabViewport| x.tab != tab;
        assert(set_viewport(vs, tab, v) == vs.filter(p).push(TabViewport { tab, viewport: v }));
        assert(set_viewport(rest, tab, v) == rest.filter(p).push(TabViewport { tab, viewport: v }));
        rest.lemma_filter_prepend(x, p);
        assert((seq![x] + rest).filter(p) == vs.filter(p));
        lemma_find_viewport_other(rest, tab, v, t);
        lemma_find_viewport_shift(set_viewport(rest, tab, v), x, t);
        lemma_find_viewport_shift(rest, x, t);
        if x.tab != tab {
            assert(set_viewport(vs, tab, v) =~= seq![x] + set_viewport(rest, tab, v));
            assert(find_viewport(set_viewport(vs, tab, v), t, 0) == find_viewport(seq![x] + set_viewport(rest, tab, v), t, 0));
        } else {
            assert(set_viewport(vs, tab, v) =~= set_viewport(rest, tab, v));
            assert(find_viewport(vs, t, 0) == find_viewport(seq![x] + rest, t, 0));
        }
    } else {
        assert(set_viewport(vs, tab, v) =~= seq![TabViewport { tab, viewport: v }]);
        assert(find_viewport(seq![TabViewport { tab, viewport: v }], t, 1) is None);
        assert(find_viewport(vs, t, 0) is None);
    }
}

/// [`find_viewport`] of `seq![x] + w`.
proof fn lemma_find_viewport_shift(w: Seq<TabViewport>, x: TabViewport, t: nat)
    ensures
        find_viewport(seq![x] + w, t, 0) == if x.tab == t {
            Some(x.viewport)
        } else {
            find_viewport(w, t, 0)
        },
{
    let u = seq![x] + w;
    if x.tab != t {
        lemma_find_viewport_offset(w, x, t, 0);
    }
}

/// [`find_viewport`] in `seq![x] + w` from `i + 1` is that in `w` from `i`.
proof fn lemma_find_viewport_offset(w: Seq<TabViewport>, x: TabViewport, t: nat, i: nat)
    requires
        i <= w.len(),
    ensures
        find_viewport(seq![x] + w, t, i + 1) == find_viewport(w, t, i),
    decreases w.len() - i,
{
    let u = seq![x] + w;
    if i < w.len() {
        assert(u[i as int + 1] == w[i as int]);
        lemma_find_viewport_offset(w, x, t, i + 1);
    }
}

/// The pair outputs of [`replace_outputs`].
pub proof fn lemma_replace_outputs_pairs(old: nat, id: nat, viewport: Option<Viewport>, commit: Seq<u8>)
    ensures
        ({
            let out = replace_outputs(old, id, viewport, commit);
            &&& out.contains(Output::Spawn { id, policy: Policy::Gpu })
            &&& out.contains(Output::Spawn { id, policy: Policy::Renderer })
            &&& forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is Spawn ==> out[k]->Spawn_id == id
            &&& forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToGpu ==> out[k]->ToGpu_id == id
        }),
{
    let out = replace_outputs(old, id, viewport, commit);
    assert(out[1] == Output::Spawn { id, policy: Policy::Gpu });
    assert(out[2] == Output::Spawn { id, policy: Policy::Renderer });
}

/// [`theorem_channel_only_own_tab`] for an `OpenTab`.
proof fn lemma_channel_open_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, url: Seq<u32>, script: Option<Seq<u8>>)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        crate::statements::channel_only_own_tab_statement(rules, urls, fetch, s, Event::OpenTab { url, script }),
{
    let out = open_tab(rules, urls, fetch, s, url, script).1;
    let id = s.next_id;
    if let Some(lock) = lock_of_url(urls, url, id) {
        assert(out[0] == Output::Spawn { id, policy: Policy::Gpu });
        assert(out[1] == Output::Spawn { id, policy: Policy::Renderer });
        assert(out.contains(out[0]) && out.contains(out[1]));
        if script is None {
            let rn = Renderer { committed: false, id, tab: id, url, lock, pending: None };
            let sp = State { renderers: s.renderers.push(rn), next_id: id + 1, ..s };
            crate::invariant::lemma_open_tab_push_wf(rules, urls, s, url, lock, false);
            lemma_begin_no_surface(rules, urls, fetch, sp, id, url);
            let ob = begin_navigation(rules, urls, fetch, sp, id, url).1;
            assert(out == seq![Output::Spawn { id, policy: Policy::Gpu }, Output::Spawn { id, policy: Policy::Renderer }] + ob);
            assert forall|k: int| 0 <= k < out.len() && k >= 2 implies !((#[trigger] out[k]) is Spawn || out[k] is ToGpu) by {
                assert(out[k] == ob[k - 2]);
            }
        } else {
            assert(out.len() == 3);
        }
    }
}

/// [`theorem_channel_only_own_tab`] for a `Net` event.
proof fn lemma_channel_net(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        crate::statements::channel_only_own_tab_statement(rules, urls, fetch, s, Event::Net { conn, input }),
{
    crate::net_wf::lemma_net_target(s, conn);
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        crate::net_theorems::lemma_net_mid(rules, urls, fetch, s, conn, input, i, nav);
        let s1 = crate::net_theorems::net_mid(rules, fetch, s, conn, input, i, nav);
        crate::net_theorems::lemma_carry_out_renderer_outputs(urls, s1, c.tab, nav.partition, Some(conn), actions);
        assert(step(rules, urls, fetch, s, Event::Net { conn, input }).1 == carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions).1);
    }
}

/// [`theorem_channel_only_own_tab`] for item 5.18's events.
proof fn lemma_channel_surface(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        e is FromGpu || e is Resize || e is Input,
    ensures
        crate::statements::channel_only_own_tab_statement(rules, urls, fetch, s, e),
{
    let out = step(rules, urls, fetch, s, e).1;
    match e {
        Event::FromGpu { id, bytes } => {
            crate::surface_rel::lemma_from_gpu_shape(s, id, bytes);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                if crate::surface_rel::gpu_kills(s.renderers[i], bytes) {
                    lemma_closes_no_surface(s.conns, s.renderers[i].tab);
                    lemma_no_surface_concat(seq![Output::Kill { id }], closes_of_tab(s.conns, s.renderers[i].tab));
                }
            }
        },
        Event::Resize { tab, width, height, scale } => {
            if let Some(i) = find_by_tab(s.renderers, tab, 0) {
                assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Spawn) by {
                    assert(k == 0 || k == 1);
                }
            }
        },
        _ => {},
    }
}

/// **`theorem_channel_only_own_tab`** (item 5.18).
pub proof fn theorem_channel_only_own_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::channel_only_own_tab_statement(rules, urls, fetch, s, e),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    match e {
        Event::FromRenderer { id, bytes } => {
            lemma_from_renderer_no_surface(rules, urls, fetch, s, id, bytes);
        },
        Event::OpenTab { url, script } => {
            lemma_channel_open_tab(rules, urls, fetch, s, url, script);
        },
        Event::NavigateTab { tab, url } => {
            lemma_begin_no_surface(rules, urls, fetch, s, tab, url);
        },
        Event::Net { conn, input } => {
            lemma_channel_net(rules, urls, fetch, s, conn, input);
        },
        Event::RendererExited { id } => {
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                lemma_closes_no_surface(s.conns, s.renderers[i].tab);
            }
        },
        Event::Tick { .. } | Event::SubNet { .. } => {
            lemma_subfetch_events_no_surface(rules, urls, fetch, s, e);
        },
        _ => {
            lemma_channel_surface(rules, urls, fetch, s, e);
        },
    }
}

} // verus!

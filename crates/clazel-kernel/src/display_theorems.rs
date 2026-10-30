//! Phase 4 item 4.12's theorems, stated in `statements.rs`: what the user
//! sees of a tab is what that tab's renderer displayed, labelled with the
//! tab and the URL the kernel committed there
//! (`theorem_show_only_own_tab`, `theorem_address_bar_integrity`), and a
//! committed document is the fetched response's body, whole and in order
//! (`theorem_body_is_the_response`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// No output of `out` is a `Show`.
pub open spec fn no_show(out: Seq<Output>) -> bool {
    forall|k: int| 0 <= k < out.len() ==> !((#[trigger] out[k]) is Show)
}

/// The outputs of `begin_navigation` show nothing.
proof fn lemma_begin_no_show(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        no_show(begin_navigation(rules, urls, fetch, s, tab, url).1),
{
    crate::net_theorems::lemma_begin_outputs(rules, urls, fetch, s, tab, url);
    let out = begin_navigation(rules, urls, fetch, s, tab, url).1;
    assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Show) by {
        match out[k] {
            Output::Show { .. } => {},
            _ => {},
        }
    }
}

/// The `Close`s of a tab show nothing.
proof fn lemma_closes_no_show(conns: Seq<Connection>, tab: nat)
    ensures
        no_show(closes_of_tab(conns, tab)),
{
    crate::net_theorems::lemma_closes_of_tab(conns, tab);
    let out = closes_of_tab(conns, tab);
    assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Show) by {
        match out[k] {
            Output::Close { .. } => {},
            _ => {},
        }
    }
}

/// `seq![o] + rest` shows nothing if neither does.
proof fn lemma_cons_no_show(o: Output, rest: Seq<Output>)
    requires
        !(o is Show),
        no_show(rest),
    ensures
        no_show(seq![o] + rest),
{
    let out = seq![o] + rest;
    assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Show) by {
        if k > 0 {
            assert(out[k] == rest[k - 1]);
        }
    }
}

/// A renderer's message other than `Display` shows nothing: it is answered
/// with replies to the sender, or starts a navigation.
proof fn lemma_handle_no_show(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
        !(m is Display),
    ensures
        no_show(handle_message(rules, urls, fetch, s, r, m).1),
{
    let out = handle_message(rules, urls, fetch, s, r, m).1;
    match m {
        clazel_ipc::message::spec::Message::Navigate { url } => {
            if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                if let Some(resolved) = (urls.resolve)(r.url, relative) {
                    if lock_of_url(urls, resolved, s.next_id) is Some {
                        lemma_begin_no_show(rules, urls, fetch, s, r.tab, resolved);
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
                lemma_storage_call_no_show(s, r, m);
            }
        },
        _ => {},
    }
}

/// A `localStorage` call answers only with a reply, or nothing.
proof fn lemma_storage_call_no_show(s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    ensures
        no_show(storage_call(s, r, m).1),
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

/// The outputs of every event but a renderer's frame show nothing.
proof fn lemma_other_events_no_show(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
        !(e is FromRenderer),
    ensures
        no_show(step(rules, urls, fetch, s, e).1),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    let out = step(rules, urls, fetch, s, e).1;
    match e {
        Event::OpenTab { url, script } => {
            let id = s.next_id;
            if let Some(lock) = lock_of_url(urls, url, id) {
                if script is None {
                    let rn = Renderer { committed: false, id, tab: id, url, lock, pending: None };
                    let sp = State { renderers: s.renderers.push(rn), next_id: id + 1, ..s };
                    crate::invariant::lemma_open_tab_push_wf(rules, urls, s, url, lock, false);
                    lemma_begin_no_show(rules, urls, fetch, sp, id, url);
                    lemma_cons_no_show(Output::Spawn { id, policy: Policy::Renderer }, begin_navigation(rules, urls, fetch, sp, id, url).1);
                }
            }
        },
        Event::NavigateTab { tab, url } => {
            lemma_begin_no_show(rules, urls, fetch, s, tab, url);
        },
        Event::Net { conn, input } => {
            crate::net_theorems::theorem_net_only_to_tab(rules, urls, fetch, s, conn, input);
            if net_target(s, conn) is Some {
                assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Show) by {
                    match out[k] {
                        Output::Show { .. } => {},
                        _ => {},
                    }
                }
            }
        },
        Event::RendererExited { id } => {
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                lemma_closes_no_show(s.conns, s.renderers[i].tab);
            }
        },
        _ => {},
    }
}

/// **`theorem_show_only_own_tab`** (item 4.12).
pub proof fn theorem_show_only_own_tab(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::show_only_own_tab_statement(rules, urls, fetch, s, e),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    let (s1, out) = step(rules, urls, fetch, s, e);
    match e {
        Event::FromRenderer { id, bytes } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let r = s.renderers[i];
                match accepted_message(r, bytes) {
                    None => {
                        lemma_closes_no_show(s.conns, r.tab);
                        lemma_cons_no_show(Output::Kill { id }, closes_of_tab(s.conns, r.tab));
                    },
                    Some(m) => {
                        if !(m is Display) {
                            lemma_handle_no_show(rules, urls, fetch, s, r, m);
                        }
                    },
                }
            }
        },
        _ => {
            lemma_other_events_no_show(rules, urls, fetch, s, e);
        },
    }
}

/// **`theorem_address_bar_integrity`** (item 4.12).
pub proof fn theorem_address_bar_integrity(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::address_bar_integrity_statement(rules, urls, fetch, s, id, bytes),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    let out = step(rules, urls, fetch, s, Event::FromRenderer { id, bytes }).1;
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        match accepted_message(r, bytes) {
            None => {
                lemma_closes_no_show(s.conns, r.tab);
                lemma_cons_no_show(Output::Kill { id }, closes_of_tab(s.conns, r.tab));
            },
            Some(m) => {
                if m is Display {
                    assert(r.committed);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is Show implies exists|j: int|
                        0 <= j < s.renderers.len() && s.renderers[j].id == id && s.renderers[j].committed && out[k]->Show_url == s.renderers[j].url
                            && out[k]->Show_tab == s.renderers[j].tab by {
                        assert(k == 0);
                        assert(s.renderers[i].id == id);
                    }
                } else {
                    lemma_handle_no_show(rules, urls, fetch, s, r, m);
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// `theorem_body_is_the_response`.
// ---------------------------------------------------------------------

/// The `Body` messages [`body_frames`] writes, in order.
pub open spec fn body_messages(body: Seq<u8>) -> Seq<clazel_ipc::message::spec::Message>
    decreases body.len(),
{
    if body.len() == 0 {
        seq![]
    } else if body.len() <= clazel_ipc::message::spec::max_body_chunk() {
        seq![clazel_ipc::message::spec::Message::Body { bytes: body }]
    } else {
        seq![clazel_ipc::message::spec::Message::Body { bytes: body.take(clazel_ipc::message::spec::max_body_chunk() as int) }] + body_messages(
            body.skip(clazel_ipc::message::spec::max_body_chunk() as int),
        )
    }
}

/// The frame of a message that can be sent is read back as that message,
/// followed by whatever the rest of the octets hold.
pub proof fn lemma_decode_frames_cons(m: clazel_ipc::message::spec::Message, rest: Seq<u8>)
    requires
        frame_of(m) is Some,
    ensures
        reply_frame(m) == frame_of(m)->Some_0,
        crate::statements::decode_frames(reply_frame(m) + rest) == match crate::statements::decode_frames(rest) {
            Some(ms) => Some(seq![m] + ms),
            None => None,
        },
{
    let p = clazel_ipc::message::spec::encode_message(m);
    let f = clazel_ipc::frame::spec::encode_frame(p);
    let b = f + rest;
    clazel_ipc::frame::lemmas::lemma_decode_encode_frame(p);
    clazel_ipc::message::lemmas::lemma_decode_encode_framed(m);
    clazel_ipc::cbor::lemmas::lemma_be_bytes_len(p.len(), 4);
    assert(f.subrange(0, 4) =~= b.take(4));
    let n = clazel_ipc::frame::spec::payload_length(f.subrange(0, 4))->Some_0;
    assert(f.len() == 4 + n);
    assert(b.take((4 + n) as int) =~= f);
    assert(b.skip((4 + n) as int) =~= rest);
}

/// One step of [`body_frames`] and [`body_messages`] for a body longer than
/// one piece.
proof fn lemma_body_unfold(body: Seq<u8>)
    requires
        body.len() > clazel_ipc::message::spec::max_body_chunk(),
    ensures
        body_frames(body) == reply_frame(clazel_ipc::message::spec::Message::Body { bytes: body.take(clazel_ipc::message::spec::max_body_chunk() as int) })
            + body_frames(body.skip(clazel_ipc::message::spec::max_body_chunk() as int)),
        body_messages(body) == seq![clazel_ipc::message::spec::Message::Body { bytes: body.take(clazel_ipc::message::spec::max_body_chunk() as int) }]
            + body_messages(body.skip(clazel_ipc::message::spec::max_body_chunk() as int)),
{
}

/// [`body_frames`] and [`body_messages`] of a body of at most one piece.
proof fn lemma_body_short(body: Seq<u8>)
    requires
        0 < body.len() <= clazel_ipc::message::spec::max_body_chunk(),
    ensures
        body_frames(body) == reply_frame(clazel_ipc::message::spec::Message::Body { bytes: body }),
        body_messages(body) == seq![clazel_ipc::message::spec::Message::Body { bytes: body }],
{
}

/// The `Body` frames of `body` are read back as its `Body` messages.
pub proof fn lemma_body_frames(body: Seq<u8>, rest: Seq<u8>)
    ensures
        crate::statements::decode_frames(body_frames(body) + rest) == match crate::statements::decode_frames(rest) {
            Some(ms) => Some(body_messages(body) + ms),
            None => None,
        },
    decreases body.len(),
{
    let c = clazel_ipc::message::spec::max_body_chunk();
    if body.len() == 0 {
        assert(body_frames(body) == Seq::<u8>::empty());
        assert(body_messages(body) == Seq::<clazel_ipc::message::spec::Message>::empty());
        assert(body_frames(body) + rest =~= rest);
        if let Some(ms) = crate::statements::decode_frames(rest) {
            assert(body_messages(body) + ms =~= ms);
        }
    } else if body.len() <= c {
        lemma_body_short(body);
        clazel_ipc::message::lemmas::lemma_body_fits_frame(body);
        lemma_decode_frames_cons(clazel_ipc::message::spec::Message::Body { bytes: body }, rest);
    } else {
        let head = body.take(c as int);
        let tail = body.skip(c as int);
        let m = clazel_ipc::message::spec::Message::Body { bytes: head };
        lemma_body_unfold(body);
        clazel_ipc::message::lemmas::lemma_body_fits_frame(head);
        lemma_body_frames(tail, rest);
        let hf = reply_frame(m);
        assert(body_frames(body) + rest =~= hf + (body_frames(tail) + rest));
        lemma_decode_frames_cons(m, body_frames(tail) + rest);
        if let Some(ms) = crate::statements::decode_frames(rest) {
            assert(seq![m] + (body_messages(tail) + ms) =~= body_messages(body) + ms);
        }
    }
}

/// The `Body` messages of `body`, then `BodyEnd`, carry `body`.
pub proof fn lemma_body_of(body: Seq<u8>)
    ensures
        crate::statements::body_of(body_messages(body) + seq![clazel_ipc::message::spec::Message::BodyEnd]) == Some(body),
    decreases body.len(),
{
    let c = clazel_ipc::message::spec::max_body_chunk();
    let end = seq![clazel_ipc::message::spec::Message::BodyEnd];
    assert(crate::statements::body_of(end) == Some(Seq::<u8>::empty())) by {
        reveal_with_fuel(crate::statements::body_of, 2);
    }
    if body.len() == 0 {
        assert(body_messages(body) + end =~= end);
    } else if body.len() <= c {
        let ms = body_messages(body) + end;
        assert(ms.drop_first() =~= end);
        assert(body + Seq::<u8>::empty() =~= body);
    } else {
        let head = body.take(c as int);
        let tail = body.skip(c as int);
        lemma_body_of(tail);
        let ms = body_messages(body) + end;
        assert(ms =~= seq![clazel_ipc::message::spec::Message::Body { bytes: head }] + (body_messages(tail) + end));
        assert(ms.drop_first() =~= body_messages(tail) + end);
        assert(head + tail =~= body);
    }
}

/// `BodyEnd` can be sent, and so can `Error` with each of the kernel's codes
/// (evaluated).
pub proof fn lemma_fixed_frames()
    ensures
        frame_of(clazel_ipc::message::spec::Message::BodyEnd) is Some,
        frame_of(clazel_ipc::message::spec::Message::Error { code: error_bad_url() }) is Some,
        frame_of(clazel_ipc::message::spec::Message::Error { code: error_encode() }) is Some,
        frame_of(clazel_ipc::message::spec::Message::Error { code: error_fetch() }) is Some,
        error_frame(error_encode()) == frame_of(clazel_ipc::message::spec::Message::Error { code: error_encode() })->Some_0,
{
    assert(frame_of(clazel_ipc::message::spec::Message::BodyEnd) is Some) by (compute_only);
    assert(frame_of(clazel_ipc::message::spec::Message::Error { code: 3 }) is Some) by (compute_only);
    assert(frame_of(clazel_ipc::message::spec::Message::Error { code: 4 }) is Some) by (compute_only);
    assert(frame_of(clazel_ipc::message::spec::Message::Error { code: 5 }) is Some) by (compute_only);
}

/// What a renderer reads from the frames that commit `doc` at `url`: the
/// `Commit` and the document's body, if the `Commit` fits a frame; otherwise
/// the first message is the `Error` that replaces it.
pub proof fn lemma_commit_frames(url: Seq<u32>, doc: Document)
    ensures
        ({
            let c = clazel_ipc::message::spec::Message::Commit { url: clazel_encoding::utf8::spec::utf8_encode(url), content_type: doc.content_type, kind: doc.kind };
            if frame_of(c) is Some {
                crate::statements::committed_document(commit_frames(url, doc)) == Some((c, doc.body))
            } else {
                crate::statements::decode_frames(commit_frames(url, doc)) matches Some(ms) ==> ms.len() > 0 && !(ms[0] is Commit)
            }
        }),
{
    let c = clazel_ipc::message::spec::Message::Commit { url: clazel_encoding::utf8::spec::utf8_encode(url), content_type: doc.content_type, kind: doc.kind };
    let cf = reply_frame(c);
    let bf = body_frames(doc.body);
    let ef = reply_frame(clazel_ipc::message::spec::Message::BodyEnd);
    let end = seq![clazel_ipc::message::spec::Message::BodyEnd];
    lemma_fixed_frames();
    assert(commit_frames(url, doc) =~= cf + (bf + ef));
    lemma_decode_frames_cons(clazel_ipc::message::spec::Message::BodyEnd, Seq::<u8>::empty());
    assert(ef + Seq::<u8>::empty() =~= ef);
    assert(crate::statements::decode_frames(Seq::<u8>::empty()) == Some(Seq::<clazel_ipc::message::spec::Message>::empty()));
    assert(seq![clazel_ipc::message::spec::Message::BodyEnd] + Seq::<clazel_ipc::message::spec::Message>::empty() =~= end);
    lemma_body_frames(doc.body, ef);
    if frame_of(c) is Some {
        lemma_decode_frames_cons(c, bf + ef);
        let ms = seq![c] + (body_messages(doc.body) + end);
        assert(crate::statements::decode_frames(commit_frames(url, doc)) == Some(ms));
        assert(ms.drop_first() =~= body_messages(doc.body) + end);
        lemma_body_of(doc.body);
    } else {
        let e = clazel_ipc::message::spec::Message::Error { code: error_encode() };
        assert(cf == error_frame(error_encode()));
        lemma_decode_frames_cons(e, bf + ef);
    }
}

/// The octets of the `ToRenderer` outputs of a fetch's step: an `Error` with
/// a code of a failed navigation, or the frames that commit a response the
/// transducer finished with.
pub open spec fn net_frames_ok(bytes: Seq<u8>, actions: Seq<NetAction>) -> bool {
    ||| bytes == reply_frame(clazel_ipc::message::spec::Message::Error { code: error_bad_url() })
    ||| bytes == reply_frame(clazel_ipc::message::spec::Message::Error { code: error_fetch() })
    ||| exists|a: int|
        0 <= a < actions.len() && (#[trigger] actions[a]) is Done && bytes == commit_frames(
            clazel_url::url::spec::url_serializer(actions[a]->Done_url, false),
            response_document(actions[a]->Done_response),
        )
}

/// Every `ToRenderer` output of [`carry_out`] is one of [`net_frames_ok`].
pub proof fn lemma_carry_out_frames(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    ensures
        ({
            let out = carry_out(urls, s, tab, partition, cur, actions).1;
            forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer ==> net_frames_ok(out[k]->ToRenderer_bytes, actions)
        }),
    decreases actions.len(),
{
    let out = carry_out(urls, s, tab, partition, cur, actions).1;
    if actions.len() > 0 {
        let rest = actions.drop_first();
        assert forall|a: int| 0 <= a < rest.len() implies rest[a] == actions[a + 1] by {}
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let (s1, id, o1) = open_connection(s, tab, partition, Endpoint { host, port, tls });
                lemma_carry_out_frames(urls, s1, tab, partition, Some(id), rest);
                let o2 = carry_out(urls, s1, tab, partition, Some(id), rest).1;
                assert(out == o1 + o2);
                assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies net_frames_ok(out[k]->ToRenderer_bytes, actions) by {
                    if k >= o1.len() {
                        assert(out[k] == o2[k - o1.len()]);
                        lemma_frames_ok_shift(out[k]->ToRenderer_bytes, actions);
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                if let Some(c) = cur {
                    lemma_carry_out_frames(urls, s, tab, partition, cur, rest);
                    let o2 = carry_out(urls, s, tab, partition, cur, rest).1;
                    assert(out == seq![Output::Send { conn: c, bytes }] + o2);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies net_frames_ok(out[k]->ToRenderer_bytes, actions) by {
                        assert(out[k] == o2[k - 1]);
                        lemma_frames_ok_shift(out[k]->ToRenderer_bytes, actions);
                    }
                } else {
                    lemma_carry_out_frames(urls, s, tab, partition, cur, rest);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies net_frames_ok(out[k]->ToRenderer_bytes, actions) by {
                        lemma_frames_ok_shift(out[k]->ToRenderer_bytes, actions);
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Close => {
                if let Some(c) = cur {
                    let sc = State { conns: without_conn(s.conns, c), ..s };
                    lemma_carry_out_frames(urls, sc, tab, partition, None, rest);
                    let o2 = carry_out(urls, sc, tab, partition, None, rest).1;
                    assert(out == seq![Output::Close { conn: c }] + o2);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies net_frames_ok(out[k]->ToRenderer_bytes, actions) by {
                        assert(out[k] == o2[k - 1]);
                        lemma_frames_ok_shift(out[k]->ToRenderer_bytes, actions);
                    }
                } else {
                    lemma_carry_out_frames(urls, s, tab, partition, cur, rest);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies net_frames_ok(out[k]->ToRenderer_bytes, actions) by {
                        lemma_frames_ok_shift(out[k]->ToRenderer_bytes, actions);
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                let href = clazel_url::url::spec::url_serializer(url, false);
                lemma_commit_navigation_frames(urls, s, tab, href, response_document(response));
                assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies net_frames_ok(out[k]->ToRenderer_bytes, actions) by {
                    if out[k]->ToRenderer_bytes == commit_frames(href, response_document(response)) {
                        assert(actions[0] is Done);
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                let (s1, closes) = close_tab_conns(s, tab);
                lemma_closes_no_renderer(s.conns, tab);
                if let Some(i) = find_by_tab(s1.renderers, tab, 0) {
                    let fo = fail_navigation(s1, i, s1.renderers[i], error_fetch()).1;
                    assert(out == closes + fo);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies net_frames_ok(out[k]->ToRenderer_bytes, actions) by {
                        if k >= closes.len() {
                            assert(out[k] == fo[k - closes.len()]);
                        }
                    }
                }
            },
        }
    }
}

/// The `Close`s of a tab are no `ToRenderer`.
proof fn lemma_closes_no_renderer(conns: Seq<Connection>, tab: nat)
    ensures
        forall|k: int| 0 <= k < closes_of_tab(conns, tab).len() ==> !((#[trigger] closes_of_tab(conns, tab)[k]) is ToRenderer),
{
    crate::net_theorems::lemma_closes_of_tab(conns, tab);
    assert forall|k: int| 0 <= k < closes_of_tab(conns, tab).len() implies !((#[trigger] closes_of_tab(conns, tab)[k]) is ToRenderer) by {
        match closes_of_tab(conns, tab)[k] {
            Output::Close { .. } => {},
            _ => {},
        }
    }
}

/// [`net_frames_ok`] for the actions after the first holds for all of them.
proof fn lemma_frames_ok_shift(bytes: Seq<u8>, actions: Seq<NetAction>)
    requires
        actions.len() > 0,
        net_frames_ok(bytes, actions.drop_first()),
    ensures
        net_frames_ok(bytes, actions),
{
    let rest = actions.drop_first();
    if exists|a: int|
        0 <= a < rest.len() && (#[trigger] rest[a]) is Done && bytes == commit_frames(
            clazel_url::url::spec::url_serializer(rest[a]->Done_url, false),
            response_document(rest[a]->Done_response),
        ) {
        let a = choose|a: int|
            0 <= a < rest.len() && (#[trigger] rest[a]) is Done && bytes == commit_frames(
                clazel_url::url::spec::url_serializer(rest[a]->Done_url, false),
                response_document(rest[a]->Done_response),
            );
        assert(actions[a + 1] == rest[a]);
    }
}

/// The `ToRenderer` outputs of [`commit_navigation`] are the commit of the
/// document, or the `Error` of a URL the kernel refuses.
proof fn lemma_commit_navigation_frames(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, doc: Document)
    ensures
        ({
            let out = commit_navigation(urls, s, tab, href, doc).1;
            forall|k: int|
                0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer ==> out[k]->ToRenderer_bytes == commit_frames(href, doc)
                    || out[k]->ToRenderer_bytes == reply_frame(clazel_ipc::message::spec::Message::Error { code: error_bad_url() })
        }),
{
    let out = commit_navigation(urls, s, tab, href, doc).1;
    let (s1, closes) = close_tab_conns(s, tab);
    lemma_closes_no_renderer(s.conns, tab);
    if let Some(i) = find_by_tab(s1.renderers, tab, 0) {
        let o2 = if scalar_url(href) && lock_of_url(urls, href, s1.next_id) is Some {
            navigate_tab(urls, s1, tab, href, doc).1
        } else {
            fail_navigation(s1, i, s1.renderers[i], error_bad_url()).1
        };
        assert(out == closes + o2);
        assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies out[k]->ToRenderer_bytes == commit_frames(href, doc)
            || out[k]->ToRenderer_bytes == reply_frame(clazel_ipc::message::spec::Message::Error { code: error_bad_url() }) by {
            if k >= closes.len() {
                assert(out[k] == o2[k - closes.len()]);
            }
        }
    }
}

/// What the `Error` frames of a failed navigation are read as: one message,
/// not a `Commit`.
proof fn lemma_error_frames_not_commit(code: u64)
    requires
        code == error_bad_url() || code == error_fetch(),
    ensures
        crate::statements::decode_frames(reply_frame(clazel_ipc::message::spec::Message::Error { code })) == Some(
            seq![clazel_ipc::message::spec::Message::Error { code }],
        ),
{
    lemma_fixed_frames();
    let e = clazel_ipc::message::spec::Message::Error { code };
    lemma_decode_frames_cons(e, Seq::<u8>::empty());
    assert(reply_frame(e) + Seq::<u8>::empty() =~= reply_frame(e));
    assert(crate::statements::decode_frames(Seq::<u8>::empty()) == Some(Seq::<clazel_ipc::message::spec::Message>::empty()));
    assert(seq![e] + Seq::<clazel_ipc::message::spec::Message>::empty() =~= seq![e]);
}

/// **`theorem_body_is_the_response`** (item 4.12).
pub proof fn theorem_body_is_the_response(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    ensures
        crate::statements::body_is_the_response_statement(rules, urls, fetch, s, conn, input),
{
    let out = step(rules, urls, fetch, s, Event::Net { conn, input }).1;
    if let Some((c, i, nav)) = net_target(s, conn) {
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
        assert(out == carry_out(urls, s1, c.tab, nav.partition, Some(conn), actions).1);
        lemma_carry_out_frames(urls, s1, c.tab, nav.partition, Some(conn), actions);
        lemma_error_frames_not_commit(error_bad_url());
        lemma_error_frames_not_commit(error_fetch());
        assert forall|k: int|
            0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer && (crate::statements::decode_frames(out[k]->ToRenderer_bytes) matches Some(ms) && ms.len() > 0
                && ms[0] is Commit) implies exists|url: clazel_url::url::spec::Url, response: clazel_http::message::spec::Response|
            #![trigger response_document(response), clazel_url::url::spec::url_serializer(url, false)]
            {
                &&& net_target(s, conn) matches Some((_, _, nav)) && net_transducer_step(fetch, s, nav, input).1.contains(
                    clazel_fetch::transducer::spec::Action::Done { url, response },
                )
                &&& crate::statements::committed_document(out[k]->ToRenderer_bytes) == Some(
                    (
                        clazel_ipc::message::spec::Message::Commit {
                            url: clazel_encoding::utf8::spec::utf8_encode(clazel_url::url::spec::url_serializer(url, false)),
                            content_type: response_document(response).content_type,
                            kind: kind_document(),
                        },
                        response.body,
                    ),
                )
            } by {
            let b = out[k]->ToRenderer_bytes;
            let a = choose|a: int|
                0 <= a < actions.len() && (#[trigger] actions[a]) is Done && b == commit_frames(
                    clazel_url::url::spec::url_serializer(actions[a]->Done_url, false),
                    response_document(actions[a]->Done_response),
                );
            let url = actions[a]->Done_url;
            let response = actions[a]->Done_response;
            let href = clazel_url::url::spec::url_serializer(url, false);
            let doc = response_document(response);
            lemma_commit_frames(href, doc);
            assert(actions[a] == clazel_fetch::transducer::spec::Action::Done { url, response });
            assert(actions.contains(actions[a]));
            assert(response_document(response).content_type == doc.content_type);
            assert(clazel_url::url::spec::url_serializer(url, false) == href);
        }
    }
}

} // verus!

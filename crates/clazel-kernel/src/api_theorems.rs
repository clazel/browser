//! Item 7.16's `fetch()` and XHR: `theorem_cors_read` and
//! `theorem_forbidden_headers` (statements in `statements.rs`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`sub_actions`] gives only connection outputs (`SubConnect`, `SubSend`,
/// `SubClose`): never a frame to a renderer.
pub proof fn lemma_sub_actions_no_frames(id: nat, serial: nat, request: u64, script: bool, hop: nat, actions: Seq<NetAction>)
    ensures
        forall|k: int|
            0 <= k < sub_actions(id, serial, request, script, hop, actions).1.len() ==> !((#[trigger] sub_actions(id, serial, request, script, hop, actions).1[k]) is ToRenderer),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                lemma_sub_actions_no_frames(id, serial, request, script, hop + 1, rest);
                let (h, out, end) = sub_actions(id, serial, request, script, hop + 1, rest);
                let all = seq![Output::SubConnect { renderer: id, serial, hop: hop + 1, host, port, tls }] + out;
                assert forall|k: int| 0 <= k < all.len() implies !((#[trigger] all[k]) is ToRenderer) by {
                    if k > 0 {
                        assert(all[k] == out[k - 1]);
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_sub_actions_no_frames(id, serial, request, script, hop, rest);
                let (h, out, end) = sub_actions(id, serial, request, script, hop, rest);
                let all = seq![Output::SubSend { renderer: id, serial, hop, bytes }] + out;
                assert forall|k: int| 0 <= k < all.len() implies !((#[trigger] all[k]) is ToRenderer) by {
                    if k > 0 {
                        assert(all[k] == out[k - 1]);
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Close => {
                lemma_sub_actions_no_frames(id, serial, request, script, hop, rest);
                let (h, out, end) = sub_actions(id, serial, request, script, hop, rest);
                let all = seq![Output::SubClose { renderer: id, serial, hop }] + out;
                assert forall|k: int| 0 <= k < all.len() implies !((#[trigger] all[k]) is ToRenderer) by {
                    if k > 0 {
                        assert(all[k] == out[k - 1]);
                    }
                }
            },
            _ => {},
        }
    }
}

/// What [`api_end`] gives: `FetchFailed`, an opaque response, or the frames
/// of the response the fetch ended with, which the renderer may read.
pub proof fn lemma_api_end_cases(fetch: FetchFns, lock: clazel_origin::spec::Origin, request: u64, mode: u64, tainted: bool, actions: Seq<NetAction>)
    ensures
        ({
            let b = api_end(fetch, lock, request, mode, tainted, actions);
            b == fetch_failed_frame(request) || b == fetch_opaque_frames(request) || crate::statements::readable_end(fetch, lock, mode, tainted, request, actions, b)
        }),
{
}

/// **`theorem_cors_read`** (phase-7.md item 7.16).
pub proof fn theorem_cors_read(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    renderer: nat,
    serial: nat,
    hop: nat,
    input: NetInput,
)
    ensures
        crate::statements::cors_read_statement(rules, urls, fetch, s, renderer, serial, hop, input),
{
    let out = step(rules, urls, fetch, s, Event::SubNet { renderer, serial, hop, input }).1;
    if let Some(f) = subnet_target(s, renderer, serial) {
        if f.api is Some {
            crate::subfetch_rel::lemma_subnet_target_key(s, renderer, serial);
            if subfetch_live(s, f) && hop != 0 && f.hop == hop {
                let (fs, actions, ops) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, subfetch_jar(fetch, s, f), s.now);
                let (h, out0, end) = sub_actions(renderer, serial, f.request, f.script, hop, actions);
                lemma_sub_actions_no_frames(renderer, serial, f.request, f.script, hop, actions);
                lemma_api_end_cases(fetch, f.lock, f.request, f.api->Some_0, fs.req.origin_tainted, actions);
                let end2 = api_finish(fetch, f, fs, actions, end);
                match end2 {
                    None => {
                        assert(out == out0);
                    },
                    Some(frames) => {
                        assert(end is Some);
                        assert(frames == api_end(fetch, f.lock, f.request, f.api->Some_0, fs.req.origin_tainted, actions));
                        assert(out == out0 + seq![Output::ToRenderer { id: f.renderer, bytes: frames }]);
                        assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies {
                            &&& out[k]->ToRenderer_id == renderer
                            &&& (out[k]->ToRenderer_bytes == fetch_failed_frame(f.request) || out[k]->ToRenderer_bytes == fetch_opaque_frames(f.request)
                                || crate::statements::readable_end(fetch, f.lock, f.api->Some_0, fs.req.origin_tainted, f.request, actions, out[k]->ToRenderer_bytes))
                        } by {
                            if k < out0.len() {
                                assert(out[k] == out0[k]);
                            } else {
                                assert(out[k] == Output::ToRenderer { id: f.renderer, bytes: frames });
                            }
                        }
                    },
                }
            }
        }
    }
}

/// The frames [`sub_actions`] ends with are those of the first ending
/// action: a sheet's or script's frames of its response for `Done`, the
/// failure frame for `Fail`, none if no action ends the fetch.
pub proof fn lemma_sub_actions_end_action(id: nat, serial: nat, request: u64, script: bool, hop: nat, actions: Seq<NetAction>)
    ensures
        ({
            let end = sub_actions(id, serial, request, script, hop, actions).2;
            match end_action(actions) {
                None => end is None,
                Some(clazel_fetch::transducer::spec::Action::Done { url, response }) => end == Some(sub_frames(script, request, response_document(response))),
                Some(_) => end == Some(sub_failed_frame(script, request)),
            }
        }),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { .. } => lemma_sub_actions_end_action(id, serial, request, script, hop + 1, rest),
            clazel_fetch::transducer::spec::Action::Send(_) => lemma_sub_actions_end_action(id, serial, request, script, hop, rest),
            clazel_fetch::transducer::spec::Action::Close => lemma_sub_actions_end_action(id, serial, request, script, hop, rest),
            _ => {},
        }
    }
}

/// [`orb_end`] reads the actions only through their first ending action.
pub proof fn lemma_orb_end_by_end_action(fetch: FetchFns, f: SubFetch, fs: FetchState, a: Seq<NetAction>, b: Seq<NetAction>, end: Option<Seq<u8>>)
    requires
        end_action(a) == end_action(b),
    ensures
        orb_end(fetch, f, fs, a, end) == orb_end(fetch, f, fs, b, end),
{
    reveal(orb_end);
}

/// [`api_end`] reads the actions only through their first ending action.
pub proof fn lemma_api_end_by_end_action(
    fetch: FetchFns,
    lock: clazel_origin::spec::Origin,
    request: u64,
    mode: u64,
    tainted: bool,
    a: Seq<NetAction>,
    b: Seq<NetAction>,
)
    requires
        end_action(a) == end_action(b),
    ensures
        api_end(fetch, lock, request, mode, tainted, a) == api_end(fetch, lock, request, mode, tainted, b),
{
}

/// The frames a "no-cors" sub-fetch ends with ([`api_finish`] of the frames
/// [`sub_actions`] gave) are its failure frame, or the fetch ended with a
/// response that is basic or that ORB allows.
pub proof fn lemma_orb_finish(fetch: FetchFns, f: SubFetch, fs: FetchState, id: nat, serial: nat, hop: nat, actions: Seq<NetAction>)
    requires
        f.api is None || f.api == Some(mode_no_cors()),
    ensures
        ({
            let end = sub_actions(id, serial, f.request, f.script, hop, actions).2;
            api_finish(fetch, f, fs, actions, end) matches Some(frames) ==> (frames == failed_frame_of(f) || crate::statements::orb_passed(
                fetch,
                f.lock,
                fs.req.origin_tainted,
                actions,
            ))
        }),
{
    reveal(orb_end);
    lemma_sub_actions_end_action(id, serial, f.request, f.script, hop, actions);
}

/// **`theorem_orb`** (phase-7.md item 7.16).
pub proof fn theorem_orb(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    renderer: nat,
    serial: nat,
    hop: nat,
    input: NetInput,
)
    ensures
        crate::statements::orb_statement(rules, urls, fetch, s, renderer, serial, hop, input),
{
    let out = step(rules, urls, fetch, s, Event::SubNet { renderer, serial, hop, input }).1;
    if let Some(f) = subnet_target(s, renderer, serial) {
        if f.api is None || f.api == Some(mode_no_cors()) {
            crate::subfetch_rel::lemma_subnet_target_key(s, renderer, serial);
            if subfetch_live(s, f) && hop != 0 && f.hop == hop {
                let (fs, actions, ops) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, subfetch_jar(fetch, s, f), s.now);
                let (h, out0, end) = sub_actions(renderer, serial, f.request, f.script, hop, actions);
                lemma_sub_actions_no_frames(renderer, serial, f.request, f.script, hop, actions);
                lemma_orb_finish(fetch, f, fs, renderer, serial, hop, actions);
                let end2 = api_finish(fetch, f, fs, actions, end);
                match end2 {
                    None => {
                        assert(out == out0);
                    },
                    Some(frames) => {
                        assert(out == out0 + seq![Output::ToRenderer { id: f.renderer, bytes: frames }]);
                        assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies {
                            &&& out[k]->ToRenderer_id == renderer
                            &&& (out[k]->ToRenderer_bytes == failed_frame_of(f) || crate::statements::orb_passed(fetch, f.lock, fs.req.origin_tainted, actions))
                        } by {
                            if k < out0.len() {
                                assert(out[k] == out0[k]);
                            } else {
                                assert(out[k] == Output::ToRenderer { id: f.renderer, bytes: frames });
                            }
                        }
                    },
                }
            }
        }
    }
}

/// A request on the wire was built ([`clazel_fetch::request::spec::req_ok`]),
/// so its page headers are all ones this client may send.
pub proof fn lemma_wire_headers_ok(url: clazel_url::url::spec::Url, req: clazel_fetch::request::spec::Req, cookie: Seq<u8>, bytes: Seq<u8>)
    requires
        clazel_fetch::transducer::contract::is_wire_request(url, req, cookie, bytes),
    ensures
        clazel_fetch::request::spec::author_headers_ok(req.headers),
        crate::statements::header_safe_wire(bytes),
{
    assert(clazel_fetch::request::spec::request_for_req(url, req) is Some);
    assert(clazel_fetch::request::spec::req_ok(req));
}

/// **`theorem_forbidden_headers`** (phase-7.md item 7.16).
pub proof fn theorem_forbidden_headers(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::forbidden_headers_statement(rules, urls, fetch, s, e),
{
    let out = step(rules, urls, fetch, s, e).1;
    if fetch.urls.rules == rules {
        crate::subfetch_theorems::theorem_subfetch_credentials(rules, urls, fetch, s, e);
        if let Event::Net { conn, input } = e {
            crate::net_theorems::theorem_wire_cookies(rules, urls, fetch, s, conn, input);
        }
        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
            Output::SubSend { bytes, .. } => crate::statements::header_safe_wire(bytes),
            Output::Send { bytes, .. } => e is Net ==> crate::statements::header_safe_wire(bytes),
            _ => true,
        } by {
            match out[k] {
                Output::SubSend { bytes, .. } => {
                    if let Event::SubNet { renderer, serial, hop, input } = e {
                        let f = subnet_target(s, renderer, serial)->Some_0;
                        let jar = if credentialed(fetch, f.lock, f.fetch.url) { s.jar } else { Seq::<clazel_cookie::storage::spec::Cookie>::empty() };
                        let c = clazel_fetch::transducer::contract::carried(
                            f.fetch.url,
                            f.fetch.req,
                            clazel_cookie::storage::spec::retrieve_cookie_string(
                                rules,
                                jar,
                                (fetch.urls.request_url)(f.fetch.url),
                                clazel_fetch::transducer::spec::request_context(fetch.urls, f.fetch),
                                s.now,
                            ),
                        );
                        lemma_wire_headers_ok(f.fetch.url, f.fetch.req, c, bytes);
                    }
                },
                Output::Send { bytes, .. } => {
                    if let Event::Net { conn, input } = e {
                        let (c0, i0, nav) = net_target(s, conn)->Some_0;
                        let c = clazel_fetch::transducer::contract::carried(
                            nav.fetch.url,
                            nav.fetch.req,
                            clazel_cookie::storage::spec::retrieve_cookie_string(
                                rules,
                                s.jar,
                                (fetch.urls.request_url)(nav.fetch.url),
                                clazel_fetch::transducer::spec::request_context(fetch.urls, nav.fetch),
                                s.now,
                            ),
                        );
                        lemma_wire_headers_ok(nav.fetch.url, nav.fetch.req, c, bytes);
                    }
                },
                _ => {},
            }
        }
    }
}

} // verus!

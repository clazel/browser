//! Item 7.16's `Fetch` ([`fetch_api`]) through the facts the other proofs
//! need of a renderer's sub-fetch request: its shape (only the sub-fetch
//! tables change; every output is for the sender), and the noninterference
//! facts of `subfetch_rel.rs` for `FetchStyle` and `FetchScript`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The sub-fetch a `Fetch` starts, when it starts one.
pub open spec fn api_entry(
    rules: Seq<clazel_psl::spec::Rule>,
    s: State,
    r: Renderer,
    request: u64,
    mode: u64,
    fs: FetchState,
    hop: nat,
) -> SubFetch {
    SubFetch {
        renderer: r.id,
        lock: r.lock,
        serial: subcount_of(s.subcounts, r.id, r.lock).0,
        request,
        script: false,
        tab: r.tab,
        fetch: fs,
        hop,
        started: s.now,
        partition: crate::domain::domain_of_renderer(rules, r),
        ended: false,
        api: Some(mode),
    }
}

/// What a `Fetch` does: the state is unchanged, or its sub-fetch tables
/// are, and its counts set; every output is for the sender.
pub proof fn lemma_fetch_api_shape(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    r: Renderer,
    request: u64,
    method: Seq<u8>,
    url: Seq<u8>,
    content_type: Seq<u8>,
    body: Seq<u8>,
    mode: u64,
    headers: Seq<Seq<u8>>,
)
    ensures
        ({
            let (s1, out) = fetch_api(rules, urls, fetch, s, r, request, method, url, content_type, body, mode, headers);
            &&& s1 == State { subfetches: s1.subfetches, subcounts: s1.subcounts, ..s }
            &&& crate::subfetch_rel::outputs_of(out, r.id)
        }),
{
    let refused = seq![Output::ToRenderer { id: r.id, bytes: fetch_failed_frame(request) }];
    assert(crate::subfetch_rel::outputs_of(refused, r.id));
    if let Some(req) = api_request(r, method, content_type, body, mode, headers) {
        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                if let Some(parsed) = (fetch.parse)(resolved) {
                    let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
                    let (fs, actions) = clazel_fetch::transducer::spec::start_req(parsed, req);
                    let (hop, o, end) = sub_actions(r.id, serial, request, false, 0, actions);
                    crate::subfetch_rel::lemma_sub_actions_of(r.id, serial, request, false, 0, actions);
                    let f = api_entry(rules, s, r, request, mode, fs, 0);
                    if let Some(frames) = api_finish(fetch, f, fs, actions, end) {
                        crate::subfetch_rel::lemma_outputs_of_concat(o, seq![Output::ToRenderer { id: r.id, bytes: frames }], r.id);
                    }
                }
            }
        }
    }
}

/// A `Fetch` of a renderer of `d`, in two runs whose sub-fetches and counts
/// of `d` agree, at the same time: the same outputs, and the tables of `d`
/// still agree (as [`crate::subfetch_rel::lemma_fetch_sub_domain`]).
pub proof fn lemma_fetch_api_domain(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    r: Renderer,
    request: u64,
    method: Seq<u8>,
    url: Seq<u8>,
    content_type: Seq<u8>,
    body: Seq<u8>,
    mode: u64,
    headers: Seq<Seq<u8>>,
)
    requires
        crate::domain::domain_of_renderer(rules, r) == d,
        crate::domain::subfetches_of_domain(rules, s1.subfetches, d) == crate::domain::subfetches_of_domain(rules, s2.subfetches, d),
        crate::domain::subcounts_of_domain(rules, s1.subcounts, d) == crate::domain::subcounts_of_domain(rules, s2.subcounts, d),
        s1.now == s2.now,
    ensures
        fetch_api(rules, urls, fetch, s1, r, request, method, url, content_type, body, mode, headers).1 == fetch_api(
            rules,
            urls,
            fetch,
            s2,
            r,
            request,
            method,
            url,
            content_type,
            body,
            mode,
            headers,
        ).1,
        crate::domain::subfetches_of_domain(rules, fetch_api(rules, urls, fetch, s1, r, request, method, url, content_type, body, mode, headers).0.subfetches, d)
            == crate::domain::subfetches_of_domain(
            rules,
            fetch_api(rules, urls, fetch, s2, r, request, method, url, content_type, body, mode, headers).0.subfetches,
            d,
        ),
        crate::domain::subcounts_of_domain(rules, fetch_api(rules, urls, fetch, s1, r, request, method, url, content_type, body, mode, headers).0.subcounts, d)
            == crate::domain::subcounts_of_domain(
            rules,
            fetch_api(rules, urls, fetch, s2, r, request, method, url, content_type, body, mode, headers).0.subcounts,
            d,
        ),
{
    crate::subfetch_rel::lemma_live_domain(rules, s1.subfetches, r.id, r.lock, d);
    crate::subfetch_rel::lemma_live_domain(rules, s2.subfetches, r.id, r.lock, d);
    crate::subfetch_rel::lemma_subcount_of_domain(rules, s1.subcounts, r.id, r.lock, d);
    crate::subfetch_rel::lemma_subcount_of_domain(rules, s2.subcounts, r.id, r.lock, d);
    let (serial, in_document) = subcount_of(s1.subcounts, r.id, r.lock);
    crate::subfetch_rel::lemma_set_subcount_domain(rules, s1.subcounts, s2.subcounts, r.id, r.lock, serial + 1, in_document + 1, d);
    if let Some(req) = api_request(r, method, content_type, body, mode, headers) {
        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                if let Some(parsed) = (fetch.parse)(resolved) {
                    let (fs, actions) = clazel_fetch::transducer::spec::start_req(parsed, req);
                    let (hop, o, end) = sub_actions(r.id, serial, request, false, 0, actions);
                    let f = api_entry(rules, s1, r, request, mode, fs, hop);
                    crate::subfetch_rel::lemma_push_domain(rules, s1.subfetches, f, d);
                    crate::subfetch_rel::lemma_push_domain(rules, s2.subfetches, f, d);
                }
            }
        }
    }
}

/// A `Fetch` of a renderer of another domain leaves `d`'s tables as they
/// are (as [`crate::subfetch_rel::lemma_fetch_sub_other`]).
pub proof fn lemma_fetch_api_other(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s: State,
    r: Renderer,
    request: u64,
    method: Seq<u8>,
    url: Seq<u8>,
    content_type: Seq<u8>,
    body: Seq<u8>,
    mode: u64,
    headers: Seq<Seq<u8>>,
)
    requires
        crate::domain::domain_of_renderer(rules, r) != d,
    ensures
        crate::domain::subfetches_of_domain(rules, fetch_api(rules, urls, fetch, s, r, request, method, url, content_type, body, mode, headers).0.subfetches, d)
            == crate::domain::subfetches_of_domain(rules, s.subfetches, d),
        crate::domain::subcounts_of_domain(rules, fetch_api(rules, urls, fetch, s, r, request, method, url, content_type, body, mode, headers).0.subcounts, d)
            == crate::domain::subcounts_of_domain(rules, s.subcounts, d),
{
    let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
    crate::subfetch_rel::lemma_set_subcount_domain(rules, s.subcounts, s.subcounts, r.id, r.lock, serial + 1, in_document + 1, d);
    if let Some(req) = api_request(r, method, content_type, body, mode, headers) {
        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                if let Some(parsed) = (fetch.parse)(resolved) {
                    let (fs, actions) = clazel_fetch::transducer::spec::start_req(parsed, req);
                    let (hop, o, end) = sub_actions(r.id, serial, request, false, 0, actions);
                    let f = api_entry(rules, s, r, request, mode, fs, hop);
                    crate::subfetch_rel::lemma_push_domain(rules, s.subfetches, f, d);
                }
            }
        }
    }
}


/// A renderer's `Fetch` message, handled: [`lemma_fetch_api_shape`] in terms
/// of [`handle_message`].
pub proof fn lemma_api_msg_shape(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    requires
        m is Fetch,
    ensures
        handle_message(rules, urls, fetch, s, r, m).0 == (State {
            subfetches: handle_message(rules, urls, fetch, s, r, m).0.subfetches,
            subcounts: handle_message(rules, urls, fetch, s, r, m).0.subcounts,
            ..s
        }),
        crate::subfetch_rel::outputs_of(handle_message(rules, urls, fetch, s, r, m).1, r.id),
{
    if let clazel_ipc::message::spec::Message::Fetch { request, method, url, content_type, body, mode, headers } = m {
        lemma_fetch_api_shape(rules, urls, fetch, s, r, request, method, url, content_type, body, mode, headers);
    }
}

/// A renderer's `Fetch` message, handled: [`lemma_fetch_api_other`].
pub proof fn lemma_api_msg_other(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s: State,
    r: Renderer,
    m: clazel_ipc::message::spec::Message,
)
    requires
        m is Fetch,
        crate::domain::domain_of_renderer(rules, r) != d,
    ensures
        crate::domain::subfetches_of_domain(rules, handle_message(rules, urls, fetch, s, r, m).0.subfetches, d) == crate::domain::subfetches_of_domain(rules, s.subfetches, d),
        crate::domain::subcounts_of_domain(rules, handle_message(rules, urls, fetch, s, r, m).0.subcounts, d) == crate::domain::subcounts_of_domain(rules, s.subcounts, d),
{
    if let clazel_ipc::message::spec::Message::Fetch { request, method, url, content_type, body, mode, headers } = m {
        lemma_fetch_api_other(rules, urls, fetch, d, s, r, request, method, url, content_type, body, mode, headers);
    }
}

/// A renderer's `Fetch` message in two runs: [`lemma_fetch_api_domain`].
pub proof fn lemma_api_msg_domain(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    r: Renderer,
    m: clazel_ipc::message::spec::Message,
)
    requires
        m is Fetch,
        crate::domain::domain_of_renderer(rules, r) == d,
        crate::domain::subfetches_of_domain(rules, s1.subfetches, d) == crate::domain::subfetches_of_domain(rules, s2.subfetches, d),
        crate::domain::subcounts_of_domain(rules, s1.subcounts, d) == crate::domain::subcounts_of_domain(rules, s2.subcounts, d),
        s1.now == s2.now,
    ensures
        handle_message(rules, urls, fetch, s1, r, m).1 == handle_message(rules, urls, fetch, s2, r, m).1,
        crate::domain::subfetches_of_domain(rules, handle_message(rules, urls, fetch, s1, r, m).0.subfetches, d)
            == crate::domain::subfetches_of_domain(rules, handle_message(rules, urls, fetch, s2, r, m).0.subfetches, d),
        crate::domain::subcounts_of_domain(rules, handle_message(rules, urls, fetch, s1, r, m).0.subcounts, d)
            == crate::domain::subcounts_of_domain(rules, handle_message(rules, urls, fetch, s2, r, m).0.subcounts, d),
{
    if let clazel_ipc::message::spec::Message::Fetch { request, method, url, content_type, body, mode, headers } = m {
        lemma_fetch_api_domain(rules, urls, fetch, d, s1, s2, r, request, method, url, content_type, body, mode, headers);
    }
}

} // verus!

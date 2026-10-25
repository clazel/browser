//! Proofs of the theorems stated in [`super::contract`], for every
//! [`HttpFns`] and [`UrlFns`]:
//!
//! - [`theorem_requests_bounded`]: at most 21 connections and 21 requests
//!   per fetch, whatever the shell reports;
//! - [`theorem_redirects_bounded`] and
//!   [`theorem_url_changes_only_by_redirect`]: the redirect count stays at
//!   most 20 and the URL changes only to an HTTP(S) URL, one redirect at a
//!   time;
//! - [`theorem_sends_are_requests`]: every `Send` is the request for the
//!   current URL;
//! - [`theorem_silent_until_decided`]: no action on bytes until the parser
//!   has decided;
//! - [`theorem_wire_cookies`] and [`theorem_jar_frame`]: the jar reaches the
//!   wire only as the `Cookie` field value that RFC 6265bis §5.8.3 gives,
//!   and a step's jar operations are only retrieval's step 5 and §5.7
//!   storage of the response's own `Set-Cookie` lines;
//! - [`theorem_ops_name_request`]: every jar operation names the current
//!   request's URL and context and the step's time;
//! - [`theorem_jar_only_in_sends`]: the next state, the jar operations and
//!   every action but a `Send`'s octets do not depend on the jar;
//! - [`theorem_split_invariant`]: for a parser that is `prefix_stable`, how
//!   the bytes are split does not matter. (The real parser is
//!   prefix-stable: `real::theorem_real_prefix_stable`.)

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


// ===========================================================================
// Counting.
// ===========================================================================

/// Counts add over concatenation.
pub proof fn lemma_count_concat(a: Seq<Action>, b: Seq<Action>)
    ensures
        super::contract::count_sends(a + b) == super::contract::count_sends(a) + super::contract::count_sends(b),
        super::contract::count_connects(a + b) == super::contract::count_connects(a) + super::contract::count_connects(b),
    decreases b.len()
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_count_concat(a, b.drop_last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// The counts of a list of one action.
pub proof fn lemma_count_one(x: Action)
    ensures
        super::contract::count_sends(seq![x]) == if x is Send { 1nat } else { 0nat },
        super::contract::count_connects(seq![x]) == if x is Connect { 1nat } else { 0nat },
{
    assert(seq![x].drop_last() =~= Seq::<Action>::empty());
    assert(seq![x].last() == x);
    assert(super::contract::count_sends(Seq::<Action>::empty()) == 0);
    assert(super::contract::count_connects(Seq::<Action>::empty()) == 0);
    reveal_with_fuel(super::contract::count_sends, 2);
    reveal_with_fuel(super::contract::count_connects, 2);
}

/// The counts of `close_if(open)` are zero.
pub proof fn lemma_count_close_if(open: bool)
    ensures
        super::contract::count_sends(close_if(open)) == 0,
        super::contract::count_connects(close_if(open)) == 0,
{
    if open {
        lemma_count_one(Action::Close);
    }
}

// ===========================================================================
// Budgets: what a state may still emit.
// ===========================================================================

/// How many more `Send`s a state may give.
pub open spec fn send_budget(s: State) -> int {
    match s.phase {
        Phase::Connecting => 21 - s.redirects,
        Phase::Reading { received: _ } => 20 - s.redirects,
        Phase::Finished => 0,
    }
}

/// How many more `Connect`s a state may give.
pub open spec fn connect_budget(s: State) -> int {
    match s.phase {
        Phase::Connecting => 20 - s.redirects,
        Phase::Reading { received: _ } => 20 - s.redirects,
        Phase::Finished => 0,
    }
}

/// `begin` for the request after `redirects` redirects.
pub proof fn lemma_begin_budget(url: Url, redirects: nat, tainted: bool)
    requires
        redirects <= 20,
    ensures
        begin(url, redirects, tainted).0.redirects == redirects,
        super::contract::count_sends(begin(url, redirects, tainted).1) + send_budget(begin(url, redirects, tainted).0) <= 21 - redirects,
        super::contract::count_connects(begin(url, redirects, tainted).1) + connect_budget(begin(url, redirects, tainted).0) <= 21 - redirects,
        begin(url, redirects, tainted).1.len() == 1,
        !(begin(url, redirects, tainted).1[0] is Send),
{
    let b = begin(url, redirects, tainted);
    lemma_count_one(b.1[0]);
    assert(b.1 =~= seq![b.1[0]]);
}

/// `close_if(open) + seq![x]`.
pub proof fn lemma_count_closing(open: bool, x: Action)
    ensures
        super::contract::count_sends(close_if(open) + seq![x]) == super::contract::count_sends(seq![x]),
        super::contract::count_connects(close_if(open) + seq![x]) == super::contract::count_connects(seq![x]),
{
    lemma_count_concat(close_if(open), seq![x]);
    lemma_count_close_if(open);
}

/// `fail` emits nothing countable and ends.
pub proof fn lemma_fail_budget(s: State, reason: Reason, open: bool)
    ensures
        super::contract::count_sends(fail(s, reason, open).1) == 0,
        super::contract::count_connects(fail(s, reason, open).1) == 0,
        send_budget(fail(s, reason, open).0) == 0,
        connect_budget(fail(s, reason, open).0) == 0,
        fail(s, reason, open).0.redirects == s.redirects,
        fail(s, reason, open).0.url == s.url,
{
    lemma_count_closing(open, Action::Fail(reason));
    lemma_count_one(Action::Fail(reason));
}

/// `on_final` from a reading state.
pub proof fn lemma_on_final_budget(urls: UrlFns, s: State, response: Response, open: bool, now: int)
    requires
        s.redirects <= 20,
        s.phase is Reading,
    ensures
        on_final(urls, s, response, open, now).0.redirects <= 20,
        super::contract::count_sends(on_final(urls, s, response, open, now).1) + send_budget(on_final(urls, s, response, open, now).0) <= send_budget(s),
        super::contract::count_connects(on_final(urls, s, response, open, now).1) + connect_budget(on_final(urls, s, response, open, now).0) <= connect_budget(s),
{
    match location_url(urls, response, s.url) {
        LocationUrl::Null => {
            lemma_count_closing(open, Action::Done { url: s.url, response: response });
            lemma_count_one(Action::Done { url: s.url, response: response });
        },
        LocationUrl::Failure => {
            lemma_fail_budget(s, Reason::RedirectLocation, open);
        },
        LocationUrl::Url(location) => {
            if !is_http_s_scheme(location.scheme) {
                lemma_fail_budget(s, Reason::RedirectScheme, open);
            } else if s.redirects == max_redirects() {
                lemma_fail_budget(s, Reason::RedirectLimit, open);
            } else {
                let t = s.tainted || !clazel_origin::spec::same_site(urls.rules, (urls.origin)(s.url), (urls.origin)(location));
                let next = begin(location, s.redirects + 1, t);
                lemma_begin_budget(location, s.redirects + 1, t);
                lemma_count_concat(close_if(open), next.1);
                lemma_count_close_if(open);
            }
        },
    }
}

/// One step never raises what may still be emitted, and keeps the count
/// at most 20.
pub proof fn lemma_step_budget(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int)
    requires
        s.redirects <= 20,
    ensures
        step(http, urls, s, input, jar, now).0.redirects <= 20,
        super::contract::count_sends(step(http, urls, s, input, jar, now).1) + send_budget(step(http, urls, s, input, jar, now).0) <= send_budget(s),
        super::contract::count_connects(step(http, urls, s, input, jar, now).1) + connect_budget(step(http, urls, s, input, jar, now).0) <= connect_budget(s),
{
    match s.phase {
        Phase::Finished => {
            assert(super::contract::count_sends(Seq::<Action>::empty()) == 0);
            assert(super::contract::count_connects(Seq::<Action>::empty()) == 0);
        },
        Phase::Connecting => match input {
            Input::Connected => match crate::request::spec::request_bytes(s.url) {
                Some(plain) => {
                    lemma_count_one(Action::Send(wire_bytes(s.url, cookie_string(urls, s, jar, now), plain)));
                },
                None => lemma_fail_budget(s, Reason::NotFetched, true),
            },
            Input::Bytes(_) => lemma_fail_budget(s, Reason::Shell, true),
            Input::Closed => lemma_fail_budget(s, Reason::Network, false),
            Input::Error => lemma_fail_budget(s, Reason::Network, false),
        },
        Phase::Reading { received } => match input {
            Input::Connected => lemma_fail_budget(s, Reason::Shell, true),
            Input::Bytes(bytes) => match settle(http, received + bytes) {
                Settled::Wait(rest) => {
                    assert(super::contract::count_sends(Seq::<Action>::empty()) == 0);
                    assert(super::contract::count_connects(Seq::<Action>::empty()) == 0);
                },
                Settled::Final(response) => lemma_on_final_budget(urls, s, response, true, now),
                Settled::Bad(reason) => lemma_fail_budget(s, reason, true),
            },
            Input::Closed => match settle_at_close(http, received) {
                Settled::Final(response) => lemma_on_final_budget(urls, s, response, false, now),
                Settled::Bad(reason) => lemma_fail_budget(s, reason, false),
                Settled::Wait(_) => lemma_fail_budget(s, Reason::Incomplete, false),
            },
            Input::Error => lemma_fail_budget(s, Reason::Network, true),
        },
    }
}

/// Over any steps.
pub proof fn lemma_run_budget(http: HttpFns, urls: UrlFns, s: State, given: Seq<Given>)
    requires
        s.redirects <= 20,
    ensures
        run(http, urls, s, given).0.redirects <= 20,
        super::contract::count_sends(run(http, urls, s, given).1) + send_budget(run(http, urls, s, given).0) <= send_budget(s),
        super::contract::count_connects(run(http, urls, s, given).1) + connect_budget(run(http, urls, s, given).0) <= connect_budget(s),
    decreases given.len()
{
    if given.len() == 0 {
        assert(super::contract::count_sends(Seq::<Action>::empty()) == 0);
        assert(super::contract::count_connects(Seq::<Action>::empty()) == 0);
    } else {
        let g = given[0];
        let first = step(http, urls, s, g.input, g.jar, g.now);
        lemma_step_budget(http, urls, s, g.input, g.jar, g.now);
        lemma_run_budget(http, urls, first.0, given.drop_first());
        lemma_count_concat(first.1, run(http, urls, first.0, given.drop_first()).1);
    }
}

/// Budgets are never negative in a state with at most 20 redirects.
pub proof fn lemma_budget_nonnegative(s: State)
    requires
        s.redirects <= 20,
    ensures
        send_budget(s) >= 0,
        connect_budget(s) >= 0,
{
}

/// **Totality**: a fetch opens at most 21 connections and sends at most
/// 21 requests, whatever the inputs, jars and times.
pub proof fn theorem_requests_bounded(http: HttpFns, urls: UrlFns, url: Url, given: Seq<Given>)
    ensures
        super::contract::requests_bounded(http, urls, url, given),
{
    let s0 = start(url);
    lemma_begin_budget(url, 0, false);
    lemma_run_budget(http, urls, s0.0, given);
    lemma_budget_nonnegative(run(http, urls, s0.0, given).0);
    lemma_count_concat(s0.1, run(http, urls, s0.0, given).1);
}

/// **The redirect count stays at most 20.**
pub proof fn theorem_redirects_bounded(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int)
    ensures
        super::contract::redirects_bounded(http, urls, s, input, jar, now),
{
    if s.redirects <= 20 {
        lemma_step_budget(http, urls, s, input, jar, now);
    }
}

// ===========================================================================
// The URL and the requests.
// ===========================================================================

/// `on_final` keeps the URL or redirects.
pub proof fn lemma_on_final_url(urls: UrlFns, s: State, response: Response, open: bool, now: int)
    ensures
        ({
            let next = on_final(urls, s, response, open, now).0;
            next.url == s.url && next.redirects == s.redirects
                || next.redirects == s.redirects + 1 && is_http_s_scheme(next.url.scheme)
        }),
{
}

/// **The current URL changes only by a redirect.**
pub proof fn theorem_url_changes_only_by_redirect(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int)
    ensures
        super::contract::url_changes_only_by_redirect(http, urls, s, input, jar, now),
{
    match s.phase {
        Phase::Reading { received } => match input {
            Input::Bytes(bytes) => match settle(http, received + bytes) {
                Settled::Final(response) => lemma_on_final_url(urls, s, response, true, now),
                _ => {},
            },
            Input::Closed => match settle_at_close(http, received) {
                Settled::Final(response) => lemma_on_final_url(urls, s, response, false, now),
                _ => {},
            },
            _ => {},
        },
        _ => {},
    }
}

/// No `Send` in `a`.
pub open spec fn no_sends(a: Seq<Action>) -> bool {
    forall|k: int| 0 <= k < a.len() ==> !(#[trigger] a[k] is Send)
}

/// `close_if(open) + rest` has no `Send` if `rest` has none.
pub proof fn lemma_no_sends_closing(open: bool, rest: Seq<Action>)
    requires
        no_sends(rest),
    ensures
        no_sends(close_if(open) + rest),
{
    let a = close_if(open) + rest;
    assert forall|k: int| 0 <= k < a.len() implies !(#[trigger] a[k] is Send) by {
        if k < close_if(open).len() {
            assert(a[k] == close_if(open)[k]);
        } else {
            assert(a[k] == rest[k - close_if(open).len()]);
        }
    }
}

/// `on_final` sends nothing.
pub proof fn lemma_on_final_no_sends(urls: UrlFns, s: State, response: Response, open: bool, now: int)
    ensures
        no_sends(on_final(urls, s, response, open, now).1),
        on_final(urls, s, response, open, now).1.len() > 0,
{
    match location_url(urls, response, s.url) {
        LocationUrl::Null => {
            lemma_no_sends_closing(open, seq![Action::Done { url: s.url, response: response }]);
        },
        LocationUrl::Failure => {
            lemma_no_sends_closing(open, seq![Action::Fail(Reason::RedirectLocation)]);
        },
        LocationUrl::Url(location) => {
            if !is_http_s_scheme(location.scheme) {
                lemma_no_sends_closing(open, seq![Action::Fail(Reason::RedirectScheme)]);
            } else if s.redirects == max_redirects() {
                lemma_no_sends_closing(open, seq![Action::Fail(Reason::RedirectLimit)]);
            } else {
                let t = s.tainted || !clazel_origin::spec::same_site(urls.rules, (urls.origin)(s.url), (urls.origin)(location));
                let next = begin(location, s.redirects + 1, t);
                assert(no_sends(next.1));
                lemma_no_sends_closing(open, next.1);
            }
        },
    }
}

/// `fail` sends nothing.
pub proof fn lemma_fail_no_sends(s: State, reason: Reason, open: bool)
    ensures
        no_sends(fail(s, reason, open).1),
        fail(s, reason, open).1.len() > 0,
{
    lemma_no_sends_closing(open, seq![Action::Fail(reason)]);
}

/// The only step that sends: from `Connecting`, on `Connected`, for a URL
/// whose request is built. Every other step sends nothing.
pub proof fn lemma_sends_only_on_connected(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int)
    ensures
        !(s.phase is Connecting && input is Connected && crate::request::spec::request_bytes(s.url) is Some) ==> no_sends(step(http, urls, s, input, jar, now).1),
{
    match s.phase {
        Phase::Finished => {},
        Phase::Connecting => match input {
            Input::Connected => match crate::request::spec::request_bytes(s.url) {
                Some(_) => {},
                None => lemma_fail_no_sends(s, Reason::NotFetched, true),
            },
            Input::Bytes(_) => lemma_fail_no_sends(s, Reason::Shell, true),
            Input::Closed => lemma_fail_no_sends(s, Reason::Network, false),
            Input::Error => lemma_fail_no_sends(s, Reason::Network, false),
        },
        Phase::Reading { received } => match input {
            Input::Connected => lemma_fail_no_sends(s, Reason::Shell, true),
            Input::Bytes(bytes) => match settle(http, received + bytes) {
                Settled::Wait(rest) => {},
                Settled::Final(response) => lemma_on_final_no_sends(urls, s, response, true, now),
                Settled::Bad(reason) => lemma_fail_no_sends(s, reason, true),
            },
            Input::Closed => match settle_at_close(http, received) {
                Settled::Final(response) => lemma_on_final_no_sends(urls, s, response, false, now),
                Settled::Bad(reason) => lemma_fail_no_sends(s, reason, false),
                Settled::Wait(_) => lemma_fail_no_sends(s, Reason::Incomplete, false),
            },
            Input::Error => lemma_fail_no_sends(s, Reason::Network, true),
        },
    }
}

/// **Every `Send` is the request for the current URL.**
pub proof fn theorem_sends_are_requests(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int)
    ensures
        super::contract::sends_are_requests(http, urls, s, input, jar, now),
{
    lemma_sends_only_on_connected(http, urls, s, input, jar, now);
}

// ===========================================================================
// Decisions and the bytes.
// ===========================================================================

/// `settle` waits only on octets the parser has not decided.
pub proof fn lemma_settle_wait(http: HttpFns, received: Seq<u8>)
    ensures
        match settle(http, received) {
            Settled::Wait(rest) => (http.parse)(rest) is Incomplete,
            _ => true,
        },
    decreases received.len()
{
    match (http.parse)(received) {
        clazel_http::message::spec::Parse::Done { response, rest } => {
            if crate::request::spec::is_interim(response.status_line.status) && rest.len() < received.len() {
                lemma_settle_wait(http, rest);
            }
        },
        _ => {},
    }
}

/// **No action until the parser decides.**
pub proof fn theorem_silent_until_decided(http: HttpFns, urls: UrlFns, s: State, bytes: Seq<u8>, jar: Seq<Cookie>, now: int)
    ensures
        super::contract::silent_until_decided(http, urls, s, bytes, jar, now),
{
    match s.phase {
        Phase::Reading { received } => {
            lemma_settle_wait(http, received + bytes);
            match settle(http, received + bytes) {
                Settled::Final(response) => lemma_on_final_no_sends(urls, s, response, true, now),
                Settled::Bad(reason) => lemma_fail_no_sends(s, reason, true),
                Settled::Wait(_) => {},
            }
        },
        _ => {},
    }
}

/// For a prefix-stable parser, `settle` on more octets: a decision stays,
/// and a wait continues from what was left.
pub proof fn lemma_settle_extend(http: HttpFns, x: Seq<u8>, b: Seq<u8>)
    requires
        super::contract::prefix_stable(http),
    ensures
        match settle(http, x) {
            Settled::Wait(r) => settle(http, x + b) == settle(http, r + b),
            other => settle(http, x + b) == other,
        },
    decreases x.len()
{
    let p = (http.parse)(x);
    let q = (http.parse)(x + b);
    match p {
        clazel_http::message::spec::Parse::Done { response, rest } => {
            assert(q == (clazel_http::message::spec::Parse::Done { response: response, rest: rest + b }));
            if crate::request::spec::is_interim(response.status_line.status) {
                if rest.len() < x.len() {
                    lemma_settle_extend(http, rest, b);
                }
            }
        },
        clazel_http::message::spec::Parse::Invalid => {
            assert(q is Invalid);
        },
        clazel_http::message::spec::Parse::Unsupported => {
            assert(q is Unsupported);
        },
        clazel_http::message::spec::Parse::Incomplete => {},
    }
}

/// **The split does not matter**, for a prefix-stable parser.
pub proof fn theorem_split_invariant(http: HttpFns, urls: UrlFns, s: State, a: Seq<u8>, b: Seq<u8>, jar: Seq<Cookie>, now: int)
    requires
        super::contract::prefix_stable(http),
    ensures
        super::contract::split_invariant(http, urls, s, a, b, jar, now),
{
    match s.phase {
        Phase::Reading { received } => {
            assert(received + a + b =~= received + (a + b));
            lemma_settle_extend(http, received + a, b);
            match settle(http, received + a) {
                Settled::Final(response) => lemma_on_final_no_sends(urls, s, response, true, now),
                Settled::Bad(reason) => lemma_fail_no_sends(s, reason, true),
                Settled::Wait(_) => {},
            }
        },
        _ => {},
    }
}

// ===========================================================================
// Cookies.
// ===========================================================================

/// The request with no cookie-string is the plain request.
pub proof fn lemma_no_cookie_is_plain(url: Url)
    ensures
        crate::request::spec::request_bytes_cookie(url, seq![]) == crate::request::spec::request_bytes(url),
{
    match crate::request::spec::request_for(url) {
        Some(r) => {
            assert(crate::request::spec::cookie_field_lines(seq![]) =~= Seq::<clazel_http::field::spec::FieldLine>::empty());
            assert(r.fields + crate::request::spec::cookie_field_lines(seq![]) =~= r.fields);
        },
        None => {},
    }
}

/// A request that was built is a wire request: valid, serialized, and
/// differing from the cookie-less request only by the `Cookie` field.
pub proof fn lemma_wire_request(url: Url, cookie: Seq<u8>, bytes: Seq<u8>)
    requires
        crate::request::spec::request_bytes_cookie(url, cookie) == Some(bytes),
    ensures
        super::contract::is_wire_request(url, cookie, bytes),
{
}

/// The bytes a request is sent as carry the cookie-string, or none.
pub proof fn lemma_wire_bytes(url: Url, cookie: Seq<u8>, plain: Seq<u8>)
    requires
        crate::request::spec::request_bytes(url) == Some(plain),
    ensures
        super::contract::is_wire_request(url, super::contract::carried(url, cookie), wire_bytes(url, cookie, plain)),
{
    match crate::request::spec::request_bytes_cookie(url, cookie) {
        Some(bytes) => lemma_wire_request(url, cookie, bytes),
        None => {
            lemma_no_cookie_is_plain(url);
            lemma_wire_request(url, seq![], plain);
        },
    }
}

/// **The jar reaches the wire only as the `Cookie` field**: every `Send`
/// is the request for the current URL with the cookie-string of §5.8.3's
/// retrieval from the jar the step is given (or none), and nothing else of
/// it comes from the jar.
pub proof fn theorem_wire_cookies(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int)
    ensures
        super::contract::wire_cookies(http, urls, s, input, jar, now),
{
    theorem_sends_are_requests(http, urls, s, input, jar, now);
    let cs = cookie_string(urls, s, jar, now);
    assert forall|k: int| 0 <= k < step(http, urls, s, input, jar, now).1.len() implies match #[trigger] step(http, urls, s, input, jar, now).1[k] {
        Action::Send(bytes) => super::contract::is_wire_request(s.url, super::contract::carried(s.url, cs), bytes),
        _ => true,
    } by {
        match step(http, urls, s, input, jar, now).1[k] {
            Action::Send(bytes) => {
                let plain = crate::request::spec::request_bytes(s.url)->Some_0;
                assert(bytes == wire_bytes(s.url, cs, plain));
                lemma_wire_bytes(s.url, cs, plain);
            },
            _ => {},
        }
    }
}

/// **A step's jar operations are only the retrieval for the request it
/// builds, and the storage of a final response's own `Set-Cookie` lines.**
pub proof fn theorem_jar_frame(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int)
    ensures
        super::contract::jar_frame(http, urls, s, input, jar, now),
{
    match s.phase {
        Phase::Finished => {},
        Phase::Connecting => match input {
            Input::Connected => match crate::request::spec::request_bytes(s.url) {
                Some(_) => {},
                None => {
                    assert(seq![retrieval_op(urls, s, now)] + Seq::<JarOp>::empty() =~= seq![retrieval_op(urls, s, now)]);
                },
            },
            _ => {},
        },
        Phase::Reading { received } => match input {
            Input::Bytes(bytes) => match settle(http, received + bytes) {
                Settled::Final(response) => lemma_on_final_ops(urls, s, response, true, now),
                _ => {},
            },
            Input::Closed => match settle_at_close(http, received) {
                Settled::Final(response) => lemma_on_final_ops(urls, s, response, false, now),
                _ => {},
            },
            _ => {},
        },
    }
}

/// `on_final`'s operations are those of the response.
pub proof fn lemma_on_final_ops(urls: UrlFns, s: State, response: Response, open: bool, now: int)
    ensures
        on_final(urls, s, response, open, now).2 == response_ops(urls, s, response, now),
{
    let ops = response_ops(urls, s, response, now);
    assert(ops + Seq::<JarOp>::empty() =~= ops);
}

/// Every operation of `stored_ops` names the request it is given.
pub proof fn lemma_stored_ops_name(lines: Seq<Seq<u8>>, url: RequestUrl, ctx: RequestContext, now: int)
    ensures
        forall|k: int| 0 <= k < stored_ops(lines, url, ctx, now).len() ==> match #[trigger] stored_ops(lines, url, ctx, now)[k] {
            JarOp::Stored { url: u, ctx: c, now: t, .. } => u == url && c == ctx && t == now,
            _ => false,
        },
    decreases lines.len()
{
    if lines.len() > 0 {
        lemma_stored_ops_name(lines.drop_first(), url, ctx, now);
        let head = seq![JarOp::Stored { line: lines[0], url: url, ctx: ctx, now: now }];
        let tail = stored_ops(lines.drop_first(), url, ctx, now);
        assert forall|k: int| 0 <= k < (head + tail).len() implies match #[trigger] (head + tail)[k] {
            JarOp::Stored { url: u, ctx: c, now: t, .. } => u == url && c == ctx && t == now,
            _ => false,
        } by {
            if k > 0 {
                assert((head + tail)[k] == tail[k - 1]);
            }
        }
    }
}

/// **Every jar operation names the current request**: its URL, its
/// context, and the step's time.
pub proof fn theorem_ops_name_request(http: HttpFns, urls: UrlFns, s: State, input: Input, jar: Seq<Cookie>, now: int)
    ensures
        super::contract::step_ops_name_request(http, urls, s, input, jar, now),
{
    theorem_jar_frame(http, urls, s, input, jar, now);
    let ops = step(http, urls, s, input, jar, now).2;
    match s.phase {
        Phase::Reading { received } => match input {
            Input::Bytes(bytes) => match settle(http, received + bytes) {
                Settled::Final(response) => lemma_stored_ops_name(set_cookie_values(response), (urls.request_url)(s.url), request_context(urls, s), now),
                _ => {},
            },
            Input::Closed => match settle_at_close(http, received) {
                Settled::Final(response) => lemma_stored_ops_name(set_cookie_values(response), (urls.request_url)(s.url), request_context(urls, s), now),
                _ => {},
            },
            _ => {},
        },
        _ => {},
    }
}

/// **The jar is read only for the `Send`s.**
pub proof fn theorem_jar_only_in_sends(http: HttpFns, urls: UrlFns, s: State, input: Input, ja: Seq<Cookie>, jb: Seq<Cookie>, now: int)
    ensures
        super::contract::jar_only_in_sends(http, urls, s, input, ja, jb, now),
{
    let a = step(http, urls, s, input, ja, now);
    let b = step(http, urls, s, input, jb, now);
    if s.phase is Connecting && input is Connected && crate::request::spec::request_bytes(s.url) is Some {
        assert(a.1.len() == 1 && b.1.len() == 1);
        assert(a.1[0] is Send && b.1[0] is Send);
    } else {
        assert(a == b);
    }
}

} // verus!

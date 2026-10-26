//! Counterexamples (item 2.11): the statements of the plan that the proof
//! found false, each shown in Verus, and the narrowest correction that
//! `noninterference.rs` and `statements.rs` state instead.
//!
//! 1. [`example_dead_tab_breaks_noninterference`]: without `user_tabs_open`,
//!    `theorem_cookie_noninterference` is false. A renderer of one domain
//!    that sends a frame the kernel cannot decode is killed and its tab is
//!    closed; the purge drops that frame, so in the purged run the tab is
//!    still open (and its connections), and a later `Net` for the connection
//!    of the navigation the user made while the tab was open steps its fetch
//!    to a commit of a document in the observer's domain, which the first run
//!    does not. (Before item 3.7 a
//!    later `NavigateTab` of the user to the closed tab did the same: a
//!    navigation committed at once. A `NavigateTab` to a closed tab no longer
//!    shows anything to the observer, since it only starts a fetch, so it is
//!    the `Net` clause of `user_tabs_open` the example shows necessary;
//!    the `NavigateTab` clause is kept, and the proof uses it.)
//! 2. [`example_public_suffix_overlay_crosses_roots`]: **unreachable in the
//!    kernel since a document on a public-suffix host is cookie-averse**
//!    (`cookie_averse`, `spec.rs`); kept as the record of why. Without that
//!    choice the theorem would be false. RFC 6265bis §5.7 step 16 ("Leave
//!    Secure Cookies Alone") asks whether the jar holds a secure cookie of
//!    the same name whose domain domain-matches the new cookie's domain or the
//!    other way round, over the whole jar. For a host-only cookie of a public
//!    suffix such as `co.uk` (allowed by step 9) and a cookie to be set for
//!    `x.a.co.uk`, the match crosses cookie roots (`co.uk` and `a.co.uk`), so
//!    what a renderer on `x.a.co.uk` can set would depend on what a renderer
//!    on `co.uk` did. The kernel never creates such a cookie (no cookie with
//!    a public-suffix domain enters the jar: `jar_no_public_suffix`, part of
//!    `kernel_wf`), so the scan never crosses a root.
//! 3. [`example_retrieval_changes_jar`]: the plan's "the jar is unchanged or
//!    6265bis storage applied" omits §5.8.3 step 5.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// 1. A closed tab.
// ---------------------------------------------------------------------

/// URL functions under which every URL has the opaque origin 0.
pub open spec fn ce_urls() -> UrlFns {
    UrlFns {
        origin_of: |u: Seq<u32>| Some(clazel_origin::spec::Origin::Opaque(0nat)),
        path_of: |u: Seq<u32>| Seq::<u8>::empty(),
        resolve: |b: Seq<u32>, i: Seq<u32>| None::<Seq<u32>>,
    }
}

/// The transducer under which the counterexample runs: the real response
/// parser, the transducer examples' stand-in URL functions, and a parser that
/// reads every navigation URL as `http://a/a`.
pub open spec fn ce_fetch() -> FetchFns {
    FetchFns {
        http: clazel_fetch::transducer::real::real_http(),
        urls: clazel_fetch::transducer::examples::example_urls(),
        parse: |u: Seq<u32>| Some(clazel_fetch::transducer::examples::url_a(None)),
    }
}

/// `HTTP/1.1 304 X`, `Location: /b`, `Content-Length: 0` and the empty line: a
/// final response that is not a redirect (a row of the transducer's examples,
/// `lemma_transducer_06`).
#[verifier::opaque]
pub open spec fn ce_response() -> Seq<u8> {
    seq![
        0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x33, 0x30, 0x34, 0x20, 0x58, 0x0D, 0x0A, 0x4C, 0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x3A, 0x20, 0x2F, 0x62, 0x0D, 0x0A,
        0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x4C, 0x65, 0x6E, 0x67, 0x74, 0x68, 0x3A, 0x20, 0x30, 0x0D, 0x0A, 0x0D, 0x0A
    ]
}

/// Open a tab, navigate it (the user types a URL; the kernel opens the
/// connection 0), have its renderer send an undecodable frame (empty), which
/// closes the tab and its connection, then report that connection open and
/// the response arriving.
pub open spec fn ce_trace() -> Seq<Event> {
    seq![ce_ev0(), ce_ev1(), ce_ev2(), ce_ev3(), ce_ev4()]
}

/// The user opens a tab.
pub open spec fn ce_ev0() -> Event {
    Event::OpenTab { url: Seq::<u32>::empty(), script: Seq::<u8>::empty() }
}

/// The user navigates it.
pub open spec fn ce_ev1() -> Event {
    Event::NavigateTab { tab: 0, url: Seq::<u32>::empty() }
}

/// Its renderer sends an undecodable frame.
pub open spec fn ce_ev2() -> Event {
    Event::FromRenderer { id: 0, bytes: Seq::<u8>::empty() }
}

/// The shell reports the connection open.
pub open spec fn ce_ev3() -> Event {
    Event::Net { conn: 0, input: clazel_fetch::transducer::spec::Input::Connected }
}

/// ... and the response arriving.
pub open spec fn ce_ev4() -> Event {
    Event::Net { conn: 0, input: clazel_fetch::transducer::spec::Input::Bytes(ce_response()) }
}

/// The trace, split.
pub proof fn lemma_ce_trace_shape()
    ensures
        ce_trace()[0] == ce_ev0() && ce_trace()[1] == ce_ev1() && ce_trace()[2] == ce_ev2() && ce_trace()[3] == ce_ev3() && ce_trace()[4] == ce_ev4(),
        ce_trace().drop_first() =~= seq![ce_ev1(), ce_ev2(), ce_ev3(), ce_ev4()],
        ce_trace().drop_first().drop_first() =~= seq![ce_ev2(), ce_ev3(), ce_ev4()],
        ce_trace().drop_first().drop_first().drop_first() =~= seq![ce_ev3(), ce_ev4()],
        ce_trace().drop_first().drop_first().drop_first().drop_first() =~= seq![ce_ev4()],
{
}

/// The transducer's step on the response, from the state that has sent the
/// request for `http://a/a`, with an empty jar at time 0.
pub open spec fn ce_step2() -> (clazel_fetch::transducer::spec::State, Seq<clazel_fetch::transducer::spec::Action>, Seq<clazel_fetch::transducer::spec::JarOp>) {
    clazel_fetch::transducer::spec::step(
        clazel_fetch::transducer::real::real_http(),
        clazel_fetch::transducer::examples::example_urls(),
        clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Reading { received: Seq::<u8>::empty() }),
        clazel_fetch::transducer::spec::Input::Bytes(ce_response()),
        Seq::<clazel_cookie::storage::spec::Cookie>::empty(),
        0,
    )
}

/// The fetch is one under which the counterexample runs: it parses every
/// navigation URL as `http://a/a` here, and, from the state that has just
/// started that fetch with an empty jar at time 0, sends a request on
/// `Connected`, and on the response of [`ce_response`] closes and ends with
/// `Done` for that URL and an empty body, with no jar operation. (Stated of
/// the fetch parameter, so the proofs about the kernel never see the real
/// response parser.)
pub open spec fn ce_fetch_ok(fetch: FetchFns) -> bool {
    let ua = clazel_fetch::transducer::examples::url_a(None);
    let st0 = clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Connecting);
    let st1 = clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Reading { received: Seq::<u8>::empty() });
    &&& (fetch.parse)(Seq::<u32>::empty()) == Some(ua)
    &&& ({
        let (fs1, a1, ops1) = clazel_fetch::transducer::spec::step(
            fetch.http,
            fetch.urls,
            st0,
            clazel_fetch::transducer::spec::Input::Connected,
            Seq::<clazel_cookie::storage::spec::Cookie>::empty(),
            0,
        );
        fs1 == st1 && a1.len() == 1 && a1[0] is Send && ops1.len() == 1 && ops1[0] is Retrieved
    })
    &&& ({
        let (fs2, a2, ops2) = clazel_fetch::transducer::spec::step(
            fetch.http,
            fetch.urls,
            st1,
            clazel_fetch::transducer::spec::Input::Bytes(ce_response()),
            Seq::<clazel_cookie::storage::spec::Cookie>::empty(),
            0,
        );
        a2.len() == 2 && a2[0] is Close && a2[1] is Done && a2[1]->Done_url == ua && a2[1]->Done_response.body == Seq::<u8>::empty() && ops2 == Seq::<clazel_fetch::transducer::spec::JarOp>::empty()
    })
}

/// `start` on `http://a/a` connects.
pub proof fn lemma_ce_start()
    ensures
        clazel_fetch::transducer::spec::start(clazel_fetch::transducer::examples::url_a(None))
            == (
            clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Connecting),
            seq![clazel_fetch::transducer::spec::Action::Connect { host: seq![0x61u8], port: 80, tls: false }],
        ),
{
    let ua = clazel_fetch::transducer::examples::url_a(None);
    let st = clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Connecting);
    let host = clazel_url::host::spec::Host::Domain(seq![0x61u32]);
    assert(clazel_url::host::spec::host_serializer(host) == seq![0x61u32]);
    assert(clazel_fetch::request::spec::all_ascii(seq![0x61u32])) by (compute_only);
    assert(clazel_fetch::request::spec::connect_to(ua) == Some((seq![0x61u8], 80nat))) by {
        assert(clazel_fetch::request::spec::ascii_octets(seq![0x61u32]) =~= Some(seq![0x61u8]));
    }
    clazel_fetch::transducer::examples::lemma_transducer_14();
    assert(clazel_fetch::request::spec::request_bytes(ua) is Some) by {
        if clazel_fetch::request::spec::request_bytes(ua) is None {
            assert(clazel_fetch::transducer::examples::ex_step(None, 0nat, clazel_fetch::transducer::spec::Phase::Connecting, clazel_fetch::transducer::spec::Input::Connected).1.len() == 2);
        }
    }
}

/// The real transducer is such a fetch, with the transducer examples' stand-in
/// URL functions and a parser that reads every URL as `http://a/a` (each step
/// evaluated by Verus on the real response parser).
pub proof fn lemma_ce_fetch_ok()
    ensures
        ce_fetch_ok(ce_fetch()),
{
    reveal(ce_response);
    let st = clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Connecting);
    let rd = clazel_fetch::transducer::spec::Phase::Reading { received: Seq::<u8>::empty() };
    let st1 = clazel_fetch::transducer::examples::state_a(None, 0, rd);
    clazel_fetch::transducer::examples::lemma_transducer_14();
    assert(clazel_fetch::request::spec::request_bytes(clazel_fetch::transducer::examples::url_a(None)) is Some) by {
        lemma_ce_start();
    }
    assert(clazel_fetch::transducer::spec::step(
        clazel_fetch::transducer::real::real_http(),
        clazel_fetch::transducer::examples::example_urls(),
        st,
        clazel_fetch::transducer::spec::Input::Connected,
        Seq::<clazel_cookie::storage::spec::Cookie>::empty(),
        0,
    ).0 == st1);
    assert(ce_step2().1.len() == 2 && ce_step2().1[0] is Close && ce_step2().1[1] is Done) by (compute_only);
    assert(ce_step2().1[1]->Done_url == clazel_fetch::transducer::examples::url_a(None) && ce_step2().1[1]->Done_response.body == Seq::<u8>::empty()) by (compute_only);
    assert(ce_step2().2 == Seq::<clazel_fetch::transducer::spec::JarOp>::empty()) by (compute_only);
}

/// `http://a/a`.
pub open spec fn ce_href() -> Seq<u32> {
    seq![0x68u32, 0x74, 0x74, 0x70, 0x3A, 0x2F, 0x2F, 0x61, 0x2F, 0x61]
}

/// The URL serializer on `http://a/a` gives that string, which is a string of
/// scalar values (shown without evaluating the host serializer, whose
/// IPv4 arm Verus's evaluator cannot get through).
pub proof fn lemma_ce_href()
    ensures
        clazel_url::url::spec::url_serializer(clazel_fetch::transducer::examples::url_a(None), false) == ce_href(),
        scalar_url(ce_href()),
{
    let ua = clazel_fetch::transducer::examples::url_a(None);
    let host = clazel_url::host::spec::Host::Domain(seq![0x61u32]);
    assert(clazel_url::host::spec::host_serializer(host) == seq![0x61u32]);
    reveal_with_fuel(clazel_url::url::spec::serialize_segments, 3);
    assert(clazel_url::url::spec::url_path_serializer(ua.path) =~= seq![0x2Fu32, 0x61]);
    assert(!clazel_url::url::spec::includes_credentials(ua));
    assert(clazel_url::url::spec::url_serializer(ua, false) =~= ce_href());
    assert(scalar_url(ce_href())) by (compute_only);
}

// ---------------------------------------------------------------------
// Evaluating the kernel's steps on the counterexample.
// ---------------------------------------------------------------------

/// `carry_out` of a lone `Connect` opens the connection.
pub proof fn lemma_co_connect(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, host: Seq<u8>, port: nat, tls: bool)
    ensures
        carry_out(urls, s, tab, partition, None, seq![NetAction::Connect { host, port, tls }])
            == (
            State { conns: s.conns.push(Connection { id: s.next_conn, tab, endpoint: Endpoint { host, port, tls }, partition }), next_conn: s.next_conn + 1, ..s },
            seq![Output::Connect { conn: s.next_conn, host, port, tls }],
        ),
{
    let acts = seq![NetAction::Connect { host, port, tls }];
    assert(acts.drop_first() =~= Seq::<NetAction>::empty());
    let ep = Endpoint { host, port, tls };
    let (sa, id, oa) = open_connection(s, tab, partition, ep);
    assert(carry_out(urls, sa, tab, partition, Some(id), Seq::<NetAction>::empty()) == (sa, Seq::<Output>::empty()));
    assert(oa + Seq::<Output>::empty() =~= oa);
}

/// `carry_out` of a lone `Send` on a connection sends.
pub proof fn lemma_co_send(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, c: nat, bytes: Seq<u8>)
    ensures
        carry_out(urls, s, tab, partition, Some(c), seq![NetAction::Send(bytes)]) == (s, seq![Output::Send { conn: c, bytes }]),
{
    let acts = seq![NetAction::Send(bytes)];
    assert(acts.drop_first() =~= Seq::<NetAction>::empty());
    assert(carry_out(urls, s, tab, partition, Some(c), Seq::<NetAction>::empty()) == (s, Seq::<Output>::empty()));
    assert(seq![Output::Send { conn: c, bytes }] + Seq::<Output>::empty() =~= seq![Output::Send { conn: c, bytes }]);
}

/// `carry_out` of `Close` then `Done` closes the connection, then commits.
pub proof fn lemma_co_close_done(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, c: nat, url: clazel_url::url::spec::Url, response: clazel_fetch::transducer::spec::Response)
    ensures
        carry_out(urls, s, tab, partition, Some(c), seq![NetAction::Close, NetAction::Done { url, response }])
            == (
            commit_navigation(urls, State { conns: without_conn(s.conns, c), ..s }, tab, clazel_url::url::spec::url_serializer(url, false), response.body).0,
            seq![Output::Close { conn: c }] + commit_navigation(urls, State { conns: without_conn(s.conns, c), ..s }, tab, clazel_url::url::spec::url_serializer(url, false), response.body).1,
        ),
{
    let acts = seq![NetAction::Close, NetAction::Done { url, response }];
    let rest = acts.drop_first();
    assert(rest =~= seq![NetAction::Done { url, response }]);
    let sa = State { conns: without_conn(s.conns, c), ..s };
    assert(carry_out(urls, sa, tab, partition, None, rest) == commit_navigation(urls, sa, tab, clazel_url::url::spec::url_serializer(url, false), response.body));
}

/// `begin_navigation` for a tab that is open, with a URL that has a lock and
/// parses, and no connection of the tab: records the navigation and carries
/// out `start`'s actions.
pub proof fn lemma_co_begin(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>, i: int, parsed: clazel_url::url::spec::Url)
    requires
        find_by_tab(s.renderers, tab, 0) == Some(i),
        lock_of_url(urls, url, s.next_id) is Some,
        (fetch.parse)(url) == Some(parsed),
        s.conns =~= Seq::<Connection>::empty(),
    ensures
        ({
            let old = s.renderers[i];
            let nav = Navigation { url, fetch: clazel_fetch::transducer::spec::start(parsed).0, partition: crate::domain::domain_of_renderer(rules, old) };
            let u = State { renderers: s.renderers.update(i, Renderer { pending: Some(nav), ..old }), ..s };
            begin_navigation(rules, urls, fetch, s, tab, url) == carry_out(urls, u, tab, nav.partition, None, clazel_fetch::transducer::spec::start(parsed).1)
        }),
{
    reveal(Seq::filter);
    assert(without_tab(Seq::<Connection>::empty(), tab) =~= Seq::<Connection>::empty());
    assert(closes_of_tab(Seq::<Connection>::empty(), tab) =~= Seq::<Output>::empty());
    let (s0, closes) = close_tab_conns(s, tab);
    assert(s0 == s);
    let (s2, out) = carry_out(
        urls,
        State { renderers: s.renderers.update(i, Renderer { pending: Some(Navigation { url, fetch: clazel_fetch::transducer::spec::start(parsed).0, partition: crate::domain::domain_of_renderer(rules, s.renderers[i]) }), ..s.renderers[i] }), ..s },
        tab,
        crate::domain::domain_of_renderer(rules, s.renderers[i]),
        None,
        clazel_fetch::transducer::spec::start(parsed).1,
    );
    assert(closes + out =~= out);
}

/// `net` for an open connection whose tab is navigating, with the jar
/// operations applied and the connection kept.
pub proof fn lemma_co_net(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput, c: Connection, i: int, nav: Navigation)
    requires
        net_target(s, conn) == Some((c, i, nav)),
        !(input is Closed || input is Error),
    ensures
        ({
            let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
            net(rules, urls, fetch, s, conn, input)
                == carry_out(
                urls,
                State { jar: apply_net_ops(rules, s.jar, ops), renderers: s.renderers.update(i, Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..s.renderers[i] }), ..s },
                c.tab,
                nav.partition,
                Some(conn),
                actions,
            )
        }),
{
}

/// The renderer the first event opens.
pub open spec fn ce_r0() -> Renderer {
    Renderer { id: 0, tab: 0, url: Seq::<u32>::empty(), lock: clazel_origin::spec::Origin::Opaque(0nat), pending: None }
}

/// The navigation the second event starts.
pub open spec fn ce_nav0() -> Navigation {
    Navigation {
        url: Seq::<u32>::empty(),
        fetch: clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Connecting),
        partition: crate::domain::Domain::Opaque(0nat),
    }
}

/// The navigation after the request is sent.
pub open spec fn ce_nav1() -> Navigation {
    Navigation { fetch: clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Reading { received: Seq::<u8>::empty() }), ..ce_nav0() }
}

/// The connection the second event opens.
pub open spec fn ce_c0() -> Connection {
    Connection {
        id: 0,
        tab: 0,
        endpoint: Endpoint { host: seq![0x61u8], port: 80, tls: false },
        partition: crate::domain::Domain::Opaque(0nat),
    }
}

/// A state of the kernel with these renderers and connections, its
/// counters 1 and (the number of connections opened) `nc`, an empty jar at
/// time 0.
pub open spec fn ce_state(rs: Seq<Renderer>, cs: Seq<Connection>, nid: nat, nc: nat) -> State {
    State { renderers: rs, jar: Seq::<clazel_cookie::storage::spec::Cookie>::empty(), storage: Map::empty(), next_id: nid, conns: cs, next_conn: nc, now: 0 }
}

/// Filtering one element.
pub proof fn lemma_filter_one<A>(x: A, p: spec_fn(A) -> bool)
    ensures
        p(x) ==> seq![x].filter(p) =~= seq![x],
        !p(x) ==> seq![x].filter(p) =~= Seq::<A>::empty(),
{
    reveal(Seq::filter);
    assert(seq![x].drop_last() =~= Seq::<A>::empty());
    assert(Seq::<A>::empty().filter(p) =~= Seq::<A>::empty());
    assert(seq![x].last() == x);
}

/// A commit to another origin, with no connection to close, spawns a
/// renderer.
pub proof fn lemma_co_commit_spawn(urls: UrlFns, s: State, tab: nat, href: Seq<u32>, body: Seq<u8>, i: int, l: clazel_origin::spec::Origin)
    requires
        s.conns =~= Seq::<Connection>::empty(),
        find_by_tab(s.renderers, tab, 0) == Some(i),
        scalar_url(href),
        lock_of_url(urls, href, s.next_id) == Some(l),
        !(l is Tuple && l == s.renderers[i].lock),
    ensures
        ({
            let old = s.renderers[i];
            commit_navigation(urls, s, tab, href, body)
                == (
                State { renderers: s.renderers.update(i, Renderer { id: s.next_id, tab, url: href, lock: l, pending: None }), next_id: s.next_id + 1, ..s },
                seq![
                    Output::Kill { id: old.id },
                    Output::Spawn { id: s.next_id, policy: Policy::Renderer },
                    Output::ToRenderer { id: s.next_id, bytes: commit_frame(href, body) },
                ],
            )
        }),
{
    reveal(Seq::filter);
    assert(without_tab(Seq::<Connection>::empty(), tab) =~= Seq::<Connection>::empty());
    assert(closes_of_tab(Seq::<Connection>::empty(), tab) =~= Seq::<Output>::empty());
    let (s0, closes) = close_tab_conns(s, tab);
    assert(s0 == s);
    let out = navigate_tab(urls, s, tab, href, body).1;
    assert(closes + out =~= out);
}

/// The first event opens the tab.
pub proof fn lemma_ce_e0(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        step(rules, ce_urls(), fetch, init_state(), ce_ev0()).0 == ce_state(seq![ce_r0()], Seq::<Connection>::empty(), 1, 0),
        step(rules, ce_urls(), fetch, init_state(), ce_ev0()).1.len() == 2,
        step(rules, ce_urls(), fetch, init_state(), ce_ev0()).1[0] is Spawn && step(rules, ce_urls(), fetch, init_state(), ce_ev0()).1[1] is ToRenderer,
{
    assert(lock_of_url(ce_urls(), Seq::<u32>::empty(), 0) == Some(clazel_origin::spec::Origin::Opaque(0nat)));
    assert(step(rules, ce_urls(), fetch, init_state(), ce_ev0()).0.renderers =~= seq![ce_r0()]);
    assert(step(rules, ce_urls(), fetch, init_state(), ce_ev0()).0 == ce_state(seq![ce_r0()], Seq::<Connection>::empty(), 1, 0));
}

/// The second event starts the fetch: a connection opens.
pub proof fn lemma_ce_e1(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        step(rules, ce_urls(), fetch, ce_state(seq![ce_r0()], Seq::<Connection>::empty(), 1, 0), ce_ev1()).0
            == ce_state(seq![Renderer { pending: Some(ce_nav0()), ..ce_r0() }], seq![ce_c0()], 1, 1),
        step(rules, ce_urls(), fetch, ce_state(seq![ce_r0()], Seq::<Connection>::empty(), 1, 0), ce_ev1()).1
            == seq![Output::Connect { conn: 0, host: seq![0x61u8], port: 80, tls: false }],
        step(rules, ce_urls(), fetch, ce_state(seq![ce_r0()], Seq::<Connection>::empty(), 1, 0), ce_ev1())
            == (
            ce_state(seq![Renderer { pending: Some(ce_nav0()), ..ce_r0() }], seq![ce_c0()], 1, 1),
            seq![Output::Connect { conn: 0, host: seq![0x61u8], port: 80, tls: false }],
        ),
{
    lemma_ce_start();
    let urls = ce_urls();
    let s1 = ce_state(seq![ce_r0()], Seq::<Connection>::empty(), 1, 0);
    let ua = clazel_fetch::transducer::examples::url_a(None);
    assert(lock_of_url(urls, Seq::<u32>::empty(), 1) == Some(clazel_origin::spec::Origin::Opaque(1nat)));
    assert((fetch.parse)(Seq::<u32>::empty()) == Some(ua));
    assert(find_by_tab(s1.renderers, 0, 0) == Some(0int));
    assert(ce_ev1() == (Event::NavigateTab { tab: 0, url: Seq::<u32>::empty() }));
    lemma_co_begin(rules, urls, fetch, s1, 0, Seq::<u32>::empty(), 0, ua);
    let st0 = clazel_fetch::transducer::examples::state_a(None, 0, clazel_fetch::transducer::spec::Phase::Connecting);
    assert(clazel_fetch::transducer::spec::start(ua) == (st0, seq![NetAction::Connect { host: seq![0x61u8], port: 80, tls: false }]));
    assert(crate::domain::domain_of_renderer(rules, ce_r0()) == crate::domain::Domain::Opaque(0nat));
    let u = State { renderers: s1.renderers.update(0, Renderer { pending: Some(ce_nav0()), ..ce_r0() }), ..s1 };
    lemma_co_connect(urls, u, 0, crate::domain::Domain::Opaque(0nat), seq![0x61u8], 80, false);
    assert(u.conns =~= Seq::<Connection>::empty());
    assert(u.conns.push(ce_c0()) =~= seq![ce_c0()]);
    assert(u.renderers =~= seq![Renderer { pending: Some(ce_nav0()), ..ce_r0() }]);
    assert(step(rules, urls, fetch, s1, ce_ev1()) == begin_navigation(rules, urls, fetch, s1, 0, Seq::<u32>::empty()));
}

/// The empty frame does not decode.
pub proof fn lemma_ce_decode_none()
    ensures
        decode_renderer_frame(Seq::<u8>::empty()) is None,
{
    assert(decode_renderer_frame(Seq::<u8>::empty()) is None);
}

/// The third event, an undecodable frame, kills the renderer and closes its
/// connection.
pub proof fn lemma_ce_e2(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        step(rules, ce_urls(), fetch, ce_state(seq![Renderer { pending: Some(ce_nav0()), ..ce_r0() }], seq![ce_c0()], 1, 1), ce_ev2())
            == (ce_state(Seq::<Renderer>::empty(), Seq::<Connection>::empty(), 1, 1), seq![Output::Kill { id: 0 }, Output::Close { conn: 0 }]),
{
    let s2 = ce_state(seq![Renderer { pending: Some(ce_nav0()), ..ce_r0() }], seq![ce_c0()], 1, 1);
    assert(decode_renderer_frame(Seq::<u8>::empty()) is None);
    assert(find_by_id(s2.renderers, 0, 0) == Some(0int));
    lemma_filter_one(ce_c0(), |c: Connection| c.tab != 0);
    assert(without_tab(seq![ce_c0()], 0) =~= Seq::<Connection>::empty());
    assert(seq![ce_c0()].drop_first() =~= Seq::<Connection>::empty());
    assert(closes_of_tab(Seq::<Connection>::empty(), 0) =~= Seq::<Output>::empty());
    assert(ce_c0().tab == 0);
    assert(closes_of_tab(seq![ce_c0()], 0) =~= seq![Output::Close { conn: 0 }] + Seq::<Output>::empty());
    assert(seq![Output::Close { conn: 0 }] + Seq::<Output>::empty() =~= seq![Output::Close { conn: 0 }]);
    assert(ce_ev2() == (Event::FromRenderer { id: 0, bytes: Seq::<u8>::empty() }));
    assert(s2.renderers.remove(0) =~= Seq::<Renderer>::empty());
}

/// A `Net` event on a connection the kernel does not have changes nothing.
pub proof fn lemma_ce_ignored(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns, k: int)
    requires
        k == 3 || k == 4,
    ensures
        step(rules, ce_urls(), fetch, ce_state(Seq::<Renderer>::empty(), Seq::<Connection>::empty(), 1, 1), ce_trace()[k]).0 == ce_state(Seq::<Renderer>::empty(), Seq::<Connection>::empty(), 1, 1),
        step(rules, ce_urls(), fetch, ce_state(Seq::<Renderer>::empty(), Seq::<Connection>::empty(), 1, 1), ce_trace()[k]).1 =~= Seq::<Output>::empty(),
{
    assert(find_conn(Seq::<Connection>::empty(), 0, 0) is None);
}

/// In the purged run the connection is open: `Connected` sends the request.
pub proof fn lemma_ce_e3(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        step(rules, ce_urls(), fetch, ce_state(seq![Renderer { pending: Some(ce_nav0()), ..ce_r0() }], seq![ce_c0()], 1, 1), ce_ev3()).0
            == ce_state(seq![Renderer { pending: Some(ce_nav1()), ..ce_r0() }], seq![ce_c0()], 1, 1),
{
    let urls = ce_urls();
    let s2 = ce_state(seq![Renderer { pending: Some(ce_nav0()), ..ce_r0() }], seq![ce_c0()], 1, 1);
    assert(find_conn(s2.conns, 0, 0) == Some(0int));
    assert(find_by_tab(s2.renderers, 0, 0) == Some(0int));
    assert(net_target(s2, 0) == Some((ce_c0(), 0int, ce_nav0())));
    let input = clazel_fetch::transducer::spec::Input::Connected;
    assert(ce_ev3() == (Event::Net { conn: 0, input }));
    lemma_co_net(rules, urls, fetch, s2, 0, input, ce_c0(), 0, ce_nav0());
    let (fs1, a1, ops1) = net_transducer_step(fetch, s2, ce_nav0(), input);
    assert(fs1 == ce_nav1().fetch && a1.len() == 1 && a1[0] is Send && ops1.len() == 1 && ops1[0] is Retrieved);
    lemma_apply_retrieval_empty(rules, ops1);
    assert(a1 =~= seq![NetAction::Send(a1[0]->Send_0)]);
    let mid = State { jar: apply_net_ops(rules, s2.jar, ops1), renderers: s2.renderers.update(0, Renderer { pending: Some(Navigation { fetch: fs1, ..ce_nav0() }), ..s2.renderers[0] }), ..s2 };
    lemma_co_send(urls, mid, 0, ce_nav0().partition, 0, a1[0]->Send_0);
    assert(mid.renderers =~= seq![Renderer { pending: Some(ce_nav1()), ..ce_r0() }]);
    assert(mid.jar =~= Seq::<clazel_cookie::storage::spec::Cookie>::empty());
    assert(mid == ce_state(seq![Renderer { pending: Some(ce_nav1()), ..ce_r0() }], seq![ce_c0()], 1, 1));
}

/// ... and the response makes the transducer close and end: the navigation
/// commits into a new renderer of the observer's domain.
pub proof fn lemma_ce_e4(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        step(rules, ce_urls(), fetch, ce_state(seq![Renderer { pending: Some(ce_nav1()), ..ce_r0() }], seq![ce_c0()], 1, 1), ce_ev4()).0.renderers
            == seq![Renderer { id: 1, tab: 0, url: ce_href(), lock: clazel_origin::spec::Origin::Opaque(1nat), pending: None }],
        step(rules, ce_urls(), fetch, ce_state(seq![Renderer { pending: Some(ce_nav1()), ..ce_r0() }], seq![ce_c0()], 1, 1), ce_ev4()).1.len() == 4,
        step(rules, ce_urls(), fetch, ce_state(seq![Renderer { pending: Some(ce_nav1()), ..ce_r0() }], seq![ce_c0()], 1, 1), ce_ev4()).1[2] == (Output::Spawn { id: 1, policy: Policy::Renderer }),
{
    lemma_ce_href();
    let urls = ce_urls();
    let u3 = ce_state(seq![Renderer { pending: Some(ce_nav1()), ..ce_r0() }], seq![ce_c0()], 1, 1);
    let ua = clazel_fetch::transducer::examples::url_a(None);
    assert(find_conn(u3.conns, 0, 0) == Some(0int));
    assert(find_by_tab(u3.renderers, 0, 0) == Some(0int));
    assert(net_target(u3, 0) == Some((ce_c0(), 0int, ce_nav1())));
    let input = clazel_fetch::transducer::spec::Input::Bytes(ce_response());
    assert(ce_ev4() == (Event::Net { conn: 0, input }));
    lemma_co_net(rules, urls, fetch, u3, 0, input, ce_c0(), 0, ce_nav1());
    let (fs2, a2, ops2) = net_transducer_step(fetch, u3, ce_nav1(), input);
    assert(a2.len() == 2 && a2[0] is Close && a2[1] is Done && a2[1]->Done_url == ua && a2[1]->Done_response.body == Seq::<u8>::empty() && ops2 =~= Seq::<clazel_fetch::transducer::spec::JarOp>::empty());
    assert(a2 =~= seq![NetAction::Close, NetAction::Done { url: ua, response: a2[1]->Done_response }]);
    assert(apply_net_ops(rules, u3.jar, ops2) == u3.jar);
    let mid = State { jar: u3.jar, renderers: u3.renderers.update(0, Renderer { pending: Some(Navigation { fetch: fs2, ..ce_nav1() }), ..u3.renderers[0] }), ..u3 };
    lemma_co_close_done(urls, mid, 0, ce_nav1().partition, 0, ua, a2[1]->Done_response);
    lemma_filter_one(ce_c0(), |c: Connection| c.id != 0);
    assert(without_conn(seq![ce_c0()], 0) =~= Seq::<Connection>::empty());
    let m2 = State { conns: without_conn(mid.conns, 0), ..mid };
    assert(m2.conns =~= Seq::<Connection>::empty());
    assert(lock_of_url(urls, ce_href(), 1) == Some(clazel_origin::spec::Origin::Opaque(1nat)));
    assert(find_by_tab(m2.renderers, 0, 0) == Some(0int));
    lemma_co_commit_spawn(urls, m2, 0, ce_href(), Seq::<u8>::empty(), 0, clazel_origin::spec::Origin::Opaque(1nat));
    let out = commit_navigation(urls, m2, 0, ce_href(), Seq::<u8>::empty()).1;
    assert(out.len() == 3 && out[1] == (Output::Spawn { id: 1, policy: Policy::Renderer }));
}

/// The states of the original run.
pub open spec fn ce_s1() -> State {
    ce_state(seq![ce_r0()], Seq::<Connection>::empty(), 1, 0)
}

/// ... after the second event.
pub open spec fn ce_s2() -> State {
    ce_state(seq![Renderer { pending: Some(ce_nav0()), ..ce_r0() }], seq![ce_c0()], 1, 1)
}

/// ... after the third.
pub open spec fn ce_s3() -> State {
    ce_state(Seq::<Renderer>::empty(), Seq::<Connection>::empty(), 1, 1)
}

/// One step of `user_tabs_open`.
pub proof fn lemma_user_tabs_open_cons(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, t: Seq<Event>)
    requires
        t.len() > 0,
        crate::noninterference::user_tabs_open(rules, urls, fetch, s, t),
    ensures
        crate::noninterference::user_tabs_open(rules, urls, fetch, step(rules, urls, fetch, s, t[0]).0, t.drop_first()),
        t[0] is Net ==> net_target(s, t[0]->Net_conn) is Some,
{
}

/// One step of `ipurge`.
pub proof fn lemma_ipurge_cons(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, d: crate::domain::Domain, t: Seq<Event>)
    requires
        t.len() > 0,
    ensures
        crate::domain::ipurge(rules, urls, fetch, s, d, t)
            == (match crate::domain::ipurge_event(rules, urls, s, d, t[0]) {
            Some(pe) => seq![pe],
            None => Seq::<Event>::empty(),
        }) + crate::domain::ipurge(rules, urls, fetch, step(rules, urls, fetch, s, t[0]).0, d, t.drop_first()),
{
}

/// The empty trace purges to nothing.
pub proof fn lemma_ipurge_empty(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, d: crate::domain::Domain)
    ensures
        crate::domain::ipurge(rules, urls, fetch, s, d, Seq::<Event>::empty()) =~= Seq::<Event>::empty(),
{
}

/// The trace is not one the shell may report: its fourth event names a
/// connection that is not open.
#[verifier::spinoff_prover]
pub proof fn lemma_ce_not_user_tabs_open(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        !crate::noninterference::user_tabs_open(rules, ce_urls(), fetch, init_state(), ce_trace()),
{
    lemma_ce_trace_shape();
    lemma_ce_e0(rules, fetch);
    lemma_ce_e1(rules, fetch);
    lemma_ce_e2(rules, fetch);
    let (urls, t) = (ce_urls(), ce_trace());
    let (e0, e1, e2, e3, e4) = (ce_ev0(), ce_ev1(), ce_ev2(), ce_ev3(), ce_ev4());
    let t1 = t.drop_first();
    let t2 = t1.drop_first();
    let t3 = t2.drop_first();
    assert(t1 =~= seq![e1, e2, e3, e4]);
    assert(t2 =~= seq![e2, e3, e4]);
    assert(t3 =~= seq![e3, e4]);
    assert(find_conn(ce_s3().conns, 0, 0) is None);
    if crate::noninterference::user_tabs_open(rules, urls, fetch, init_state(), t) {
        lemma_user_tabs_open_cons(rules, urls, fetch, init_state(), t);
        lemma_user_tabs_open_cons(rules, urls, fetch, ce_s1(), t1);
        lemma_user_tabs_open_cons(rules, urls, fetch, ce_s2(), t2);
        lemma_user_tabs_open_cons(rules, urls, fetch, ce_s3(), t3);
        assert(e3 is Net);
        assert(net_target(ce_s3(), 0) is None);
    }
}

/// Nothing the first event outputs is addressed to the observer.
pub proof fn lemma_ce_unaddr0(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        crate::noninterference::outputs_for(rules, crate::domain::Domain::Opaque(1nat), init_state(), ce_s1(), step(rules, ce_urls(), fetch, init_state(), ce_ev0()).1) == Seq::<Output>::empty(),
{
    lemma_ce_e0(rules, fetch);
    let d = crate::domain::Domain::Opaque(1nat);
    let (s0, s1) = (init_state(), ce_s1());
    assert(crate::domain::domain_of_renderer(rules, ce_r0()) == crate::domain::Domain::Opaque(0nat));
    let o0 = step(rules, ce_urls(), fetch, s0, ce_ev0()).1;
    assert forall|k: int| 0 <= k < o0.len() implies !crate::noninterference::addressed_to(rules, d, s0, s1, #[trigger] o0[k]) by {
        if crate::noninterference::addressed_to(rules, d, s0, s1, o0[k]) {
            let q = choose|q: Renderer| (s0.renderers.contains(q) || s1.renderers.contains(q)) && q.id == crate::domain::output_id(o0[k]) && crate::domain::domain_of_renderer(rules, q) == d;
            assert(s1.renderers.contains(q));
            assert(q == ce_r0());
        }
    }
    crate::unwind_base::lemma_filter_none(o0, |o: Output| crate::noninterference::addressed_to(rules, d, s0, s1, o));
}

/// ... the second ...
pub proof fn lemma_ce_unaddr1(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        crate::noninterference::outputs_for(rules, crate::domain::Domain::Opaque(1nat), ce_s1(), ce_s2(), seq![Output::Connect { conn: 0, host: seq![0x61u8], port: 80, tls: false }]) == Seq::<Output>::empty(),
{
    lemma_ce_e1(rules, fetch);
    let d = crate::domain::Domain::Opaque(1nat);
    let o1 = seq![Output::Connect { conn: 0, host: seq![0x61u8], port: 80, tls: false }];
    assert forall|k: int| 0 <= k < o1.len() implies !crate::noninterference::addressed_to(rules, d, ce_s1(), ce_s2(), #[trigger] o1[k]) by {}
    crate::unwind_base::lemma_filter_none(o1, |o: Output| crate::noninterference::addressed_to(rules, d, ce_s1(), ce_s2(), o));
}

/// ... and the third.
pub proof fn lemma_ce_unaddr2(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        crate::noninterference::outputs_for(rules, crate::domain::Domain::Opaque(1nat), ce_s2(), ce_s3(), seq![Output::Kill { id: 0 }, Output::Close { conn: 0 }]) == Seq::<Output>::empty(),
{
    lemma_ce_e2(rules, fetch);
    let d = crate::domain::Domain::Opaque(1nat);
    let (s2, s3) = (ce_s2(), ce_s3());
    let r0n = Renderer { pending: Some(ce_nav0()), ..ce_r0() };
    assert(crate::domain::domain_of_renderer(rules, r0n) == crate::domain::Domain::Opaque(0nat));
    let o2 = seq![Output::Kill { id: 0 }, Output::Close { conn: 0 }];
    assert forall|k: int| 0 <= k < o2.len() implies !crate::noninterference::addressed_to(rules, d, s2, s3, #[trigger] o2[k]) by {
        if crate::noninterference::addressed_to(rules, d, s2, s3, o2[k]) {
            let q = choose|q: Renderer| (s2.renderers.contains(q) || s3.renderers.contains(q)) && q.id == crate::domain::output_id(o2[k]) && crate::domain::domain_of_renderer(rules, q) == d;
            assert(s2.renderers.contains(q));
            assert(q == r0n);
        }
    }
    crate::unwind_base::lemma_filter_none(o2, |o: Output| crate::noninterference::addressed_to(rules, d, s2, s3, o));
}

/// No renderer of `s` is in the domain `d`.
pub open spec fn no_d(rules: Seq<clazel_psl::spec::Rule>, d: crate::domain::Domain, s: State) -> bool {
    forall|i: int| 0 <= i < s.renderers.len() ==> crate::domain::domain_of_renderer(rules, #[trigger] s.renderers[i]) != d
}

/// A step between states with no renderer in `d` sends `d` nothing.
pub proof fn lemma_outputs_for_quiet(rules: Seq<clazel_psl::spec::Rule>, d: crate::domain::Domain, s: State, sb: State, out: Seq<Output>)
    requires
        no_d(rules, d, s),
        no_d(rules, d, sb),
    ensures
        crate::noninterference::outputs_for(rules, d, s, sb, out) == Seq::<Output>::empty(),
{
    assert forall|k: int| 0 <= k < out.len() implies !crate::noninterference::addressed_to(rules, d, s, sb, #[trigger] out[k]) by {
        if crate::noninterference::addressed_to(rules, d, s, sb, out[k]) {
            let r = choose|r: Renderer| (s.renderers.contains(r) || sb.renderers.contains(r)) && r.id == crate::domain::output_id(out[k]) && crate::domain::domain_of_renderer(rules, r) == d;
            if s.renderers.contains(r) {
                let i = choose|i: int| 0 <= i < s.renderers.len() && s.renderers[i] == r;
            } else {
                let i = choose|i: int| 0 <= i < sb.renderers.len() && sb.renderers[i] == r;
            }
        }
    }
    crate::unwind_base::lemma_filter_none(out, |o: Output| crate::noninterference::addressed_to(rules, d, s, sb, o));
}

/// Every state along the run of `t` from `s` has no renderer in `d`.
pub open spec fn quiet(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s: State, t: Seq<Event>) -> bool
    decreases t.len(),
{
    no_d(rules, d, s) && (t.len() == 0 || quiet(rules, urls, fetch, d, step(rules, urls, fetch, s, t[0]).0, t.drop_first()))
}

/// A quiet run sends `d` nothing.
pub proof fn lemma_run_quiet(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s: State, t: Seq<Event>)
    requires
        quiet(rules, urls, fetch, d, s, t),
    ensures
        crate::noninterference::run_outputs_for(rules, urls, fetch, d, s, t) == Seq::<Output>::empty(),
    decreases t.len(),
{
    if t.len() > 0 {
        let sb = step(rules, urls, fetch, s, t[0]).0;
        lemma_run_quiet(rules, urls, fetch, d, sb, t.drop_first());
        lemma_outputs_for_quiet(rules, d, s, sb, step(rules, urls, fetch, s, t[0]).1);
        assert(Seq::<Output>::empty() + Seq::<Output>::empty() =~= Seq::<Output>::empty());
    }
}

/// One step of a quiet run.
pub proof fn lemma_quiet_step(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s: State, t: Seq<Event>, sb: State)
    requires
        t.len() > 0,
        no_d(rules, d, s),
        step(rules, urls, fetch, s, t[0]).0 == sb,
        quiet(rules, urls, fetch, d, sb, t.drop_first()),
    ensures
        quiet(rules, urls, fetch, d, s, t),
{
}

/// The states of the original run have no renderer in the observer's domain.
pub proof fn lemma_ce_no_d(rules: Seq<clazel_psl::spec::Rule>)
    ensures
        no_d(rules, crate::domain::Domain::Opaque(1nat), init_state()),
        no_d(rules, crate::domain::Domain::Opaque(1nat), ce_s1()),
        no_d(rules, crate::domain::Domain::Opaque(1nat), ce_s2()),
        no_d(rules, crate::domain::Domain::Opaque(1nat), ce_s3()),
{
    assert(crate::domain::domain_of_renderer(rules, ce_r0()) == crate::domain::Domain::Opaque(0nat));
    assert(crate::domain::domain_of_renderer(rules, Renderer { pending: Some(ce_nav0()), ..ce_r0() }) == crate::domain::Domain::Opaque(0nat));
}

/// The original run of [`ce_trace`] is quiet.
pub proof fn lemma_ce_quiet(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        quiet(rules, ce_urls(), fetch, crate::domain::Domain::Opaque(1nat), init_state(), ce_trace()),
{
    lemma_ce_trace_shape();
    lemma_ce_no_d(rules);
    lemma_ce_e0(rules, fetch);
    lemma_ce_e1(rules, fetch);
    lemma_ce_e2(rules, fetch);
    lemma_ce_ignored(rules, fetch, 3);
    lemma_ce_ignored(rules, fetch, 4);
    let (urls, d) = (ce_urls(), crate::domain::Domain::Opaque(1nat));
    let t = ce_trace();
    let t1 = t.drop_first();
    let t2 = t1.drop_first();
    let t3 = t2.drop_first();
    let t4 = t3.drop_first();
    let t5 = t4.drop_first();
    assert(t1 =~= seq![ce_ev1(), ce_ev2(), ce_ev3(), ce_ev4()]);
    assert(t2 =~= seq![ce_ev2(), ce_ev3(), ce_ev4()]);
    assert(t3 =~= seq![ce_ev3(), ce_ev4()]);
    assert(t4 =~= seq![ce_ev4()]);
    assert(t5 =~= Seq::<Event>::empty());
    assert(quiet(rules, urls, fetch, d, ce_s3(), t5));
    assert(step(rules, urls, fetch, ce_s3(), t4[0]).0 == ce_s3() && step(rules, urls, fetch, ce_s3(), t3[0]).0 == ce_s3());
    assert(step(rules, urls, fetch, ce_s2(), t2[0]).0 == ce_s3() && step(rules, urls, fetch, ce_s1(), t1[0]).0 == ce_s2() && step(rules, urls, fetch, init_state(), t[0]).0 == ce_s1());
    lemma_quiet_step(rules, urls, fetch, d, ce_s3(), t4, ce_s3());
    lemma_quiet_step(rules, urls, fetch, d, ce_s3(), t3, ce_s3());
    lemma_quiet_step(rules, urls, fetch, d, ce_s2(), t2, ce_s3());
    lemma_quiet_step(rules, urls, fetch, d, ce_s1(), t1, ce_s2());
    lemma_quiet_step(rules, urls, fetch, d, init_state(), t, ce_s1());
}

/// ... and so sends the observer nothing.
pub proof fn lemma_ce_run_all(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        crate::noninterference::run_outputs_for(rules, ce_urls(), fetch, crate::domain::Domain::Opaque(1nat), init_state(), ce_trace()).len() == 0,
{
    lemma_ce_quiet(rules, fetch);
    lemma_run_quiet(rules, ce_urls(), fetch, crate::domain::Domain::Opaque(1nat), init_state(), ce_trace());
}

/// The original run of [`ce_trace`] sends nothing to the observer, and the
/// trace is not one the shell may report.
pub proof fn lemma_ce_real(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        ({
            let urls = ce_urls();
            let t = ce_trace();
            let d = crate::domain::Domain::Opaque(1nat);
            !crate::noninterference::user_tabs_open(rules, urls, fetch, init_state(), t) && crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), t).len() == 0
        }),
{
    lemma_ce_not_user_tabs_open(rules, fetch);
    lemma_ce_run_all(rules, fetch);
}

/// The purge from after the third event keeps the two network events.
#[verifier::spinoff_prover]
pub proof fn lemma_ce_purge_tail(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        crate::domain::ipurge(rules, ce_urls(), fetch, ce_s3(), crate::domain::Domain::Opaque(1nat), seq![ce_ev3(), ce_ev4()]) =~= seq![ce_ev3(), ce_ev4()],
{
    lemma_ce_ignored(rules, fetch, 3);
    lemma_ce_ignored(rules, fetch, 4);
    let (urls, d, s3) = (ce_urls(), crate::domain::Domain::Opaque(1nat), ce_s3());
    assert(step(rules, urls, fetch, s3, ce_ev3()).0 == s3 && step(rules, urls, fetch, s3, ce_ev4()).0 == s3);
    assert(crate::domain::ipurge_event(rules, urls, s3, d, ce_ev3()) == Some(ce_ev3()));
    assert(crate::domain::ipurge_event(rules, urls, s3, d, ce_ev4()) == Some(ce_ev4()));
    lemma_ipurge_cons(rules, urls, fetch, s3, d, seq![ce_ev3(), ce_ev4()]);
    assert(seq![ce_ev3(), ce_ev4()].drop_first() =~= seq![ce_ev4()]);
    lemma_ipurge_cons(rules, urls, fetch, s3, d, seq![ce_ev4()]);
    assert(seq![ce_ev4()].drop_first() =~= Seq::<Event>::empty());
    lemma_ipurge_empty(rules, urls, fetch, s3, d);
    assert(seq![ce_ev3()] + (seq![ce_ev4()] + Seq::<Event>::empty()) =~= seq![ce_ev3(), ce_ev4()]);
}

/// ... and from after the second drops the frame.
#[verifier::spinoff_prover]
pub proof fn lemma_ce_purge_from2(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        crate::domain::ipurge(rules, ce_urls(), fetch, ce_s2(), crate::domain::Domain::Opaque(1nat), seq![ce_ev2(), ce_ev3(), ce_ev4()]) =~= seq![ce_ev3(), ce_ev4()],
{
    lemma_ce_purge_tail(rules, fetch);
    lemma_ce_e2(rules, fetch);
    let (urls, d, s2) = (ce_urls(), crate::domain::Domain::Opaque(1nat), ce_s2());
    assert(step(rules, urls, fetch, s2, ce_ev2()).0 == ce_s3());
    assert(crate::domain::event_domain(rules, s2, ce_ev2()) == Some(crate::domain::Domain::Opaque(0nat)));
    assert(crate::domain::declassified(urls, s2, ce_ev2()) is None);
    assert(crate::domain::ipurge_event(rules, urls, s2, d, ce_ev2()) is None);
    lemma_ipurge_cons(rules, urls, fetch, s2, d, seq![ce_ev2(), ce_ev3(), ce_ev4()]);
    assert(seq![ce_ev2(), ce_ev3(), ce_ev4()].drop_first() =~= seq![ce_ev3(), ce_ev4()]);
    assert(Seq::<Event>::empty() + seq![ce_ev3(), ce_ev4()] =~= seq![ce_ev3(), ce_ev4()]);
}

/// ... and from after the first.
#[verifier::spinoff_prover]
pub proof fn lemma_ce_purge_from1(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        crate::domain::ipurge(rules, ce_urls(), fetch, ce_s1(), crate::domain::Domain::Opaque(1nat), seq![ce_ev1(), ce_ev2(), ce_ev3(), ce_ev4()]) =~= seq![ce_ev1(), ce_ev3(), ce_ev4()],
{
    lemma_ce_purge_from2(rules, fetch);
    lemma_ce_e1(rules, fetch);
    let (urls, d, s1) = (ce_urls(), crate::domain::Domain::Opaque(1nat), ce_s1());
    assert(step(rules, urls, fetch, s1, ce_ev1()).0 == ce_s2());
    assert(crate::domain::ipurge_event(rules, urls, s1, d, ce_ev1()) == Some(ce_ev1()));
    lemma_ipurge_cons(rules, urls, fetch, s1, d, seq![ce_ev1(), ce_ev2(), ce_ev3(), ce_ev4()]);
    assert(seq![ce_ev1(), ce_ev2(), ce_ev3(), ce_ev4()].drop_first() =~= seq![ce_ev2(), ce_ev3(), ce_ev4()]);
    assert(seq![ce_ev1()] + seq![ce_ev3(), ce_ev4()] =~= seq![ce_ev1(), ce_ev3(), ce_ev4()]);
}

/// The purge of [`ce_trace`] drops the renderer's frame.
#[verifier::spinoff_prover]
pub proof fn lemma_ce_purge(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        crate::domain::purge(rules, ce_urls(), fetch, crate::domain::Domain::Opaque(1nat), ce_trace()) =~= seq![ce_ev0(), ce_ev1(), ce_ev3(), ce_ev4()],
{
    lemma_ce_trace_shape();
    lemma_ce_purge_from1(rules, fetch);
    lemma_ce_e0(rules, fetch);
    let (urls, d, s0) = (ce_urls(), crate::domain::Domain::Opaque(1nat), init_state());
    assert(step(rules, urls, fetch, s0, ce_ev0()).0 == ce_s1());
    assert(crate::domain::ipurge_event(rules, urls, s0, d, ce_ev0()) == Some(ce_ev0()));
    lemma_ipurge_cons(rules, urls, fetch, s0, d, ce_trace());
    assert(ce_trace().drop_first() =~= seq![ce_ev1(), ce_ev2(), ce_ev3(), ce_ev4()]);
    assert(seq![ce_ev0()] + seq![ce_ev1(), ce_ev3(), ce_ev4()] =~= seq![ce_ev0(), ce_ev1(), ce_ev3(), ce_ev4()]);
}

/// The purged run sends the observer the commit.
#[verifier::spinoff_prover]
pub proof fn lemma_ce_purged(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns)
    requires
        ce_fetch_ok(fetch),
    ensures
        ({
            let urls = ce_urls();
                    let t = ce_trace();
            let d = crate::domain::Domain::Opaque(1nat);
            crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), crate::domain::purge(rules, urls, fetch, d, t)).len() > 0
        }),
{
    lemma_ce_trace_shape();
    lemma_ce_purge(rules, fetch);
    lemma_ce_e0(rules, fetch);
    lemma_ce_e1(rules, fetch);
    lemma_ce_e3(rules, fetch);
    lemma_ce_e4(rules, fetch);
    let urls = ce_urls();
    let t = ce_trace();
    let d = crate::domain::Domain::Opaque(1nat);
    let (s0, s1, s2) = (init_state(), ce_s1(), ce_s2());
    let u3 = ce_state(seq![Renderer { pending: Some(ce_nav1()), ..ce_r0() }], seq![ce_c0()], 1, 1);
    let (e0, e1, e3, e4) = (ce_ev0(), ce_ev1(), ce_ev3(), ce_ev4());
    assert(step(rules, urls, fetch, s0, e0).0 == s1);
    assert(step(rules, urls, fetch, s1, e1).0 == s2);
    assert(step(rules, urls, fetch, s2, e3).0 == u3);
    let (u4, q4) = step(rules, urls, fetch, u3, e4);
    assert(u4.renderers[0] == (Renderer { id: 1, tab: 0, url: ce_href(), lock: clazel_origin::spec::Origin::Opaque(1nat), pending: None }));
    assert(crate::domain::domain_of_renderer(rules, u4.renderers[0]) == d);
    assert(crate::noninterference::addressed_to(rules, d, u3, u4, q4[2])) by {
        assert(u4.renderers.contains(u4.renderers[0]));
    }
    let p = seq![e0, e1, e3, e4];
    assert(p =~= seq![e0] + seq![e1, e3, e4]);
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s0, e0, seq![e1, e3, e4]);
    assert(seq![e1, e3, e4] =~= seq![e1] + seq![e3, e4]);
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s1, e1, seq![e3, e4]);
    assert(seq![e3, e4] =~= seq![e3] + seq![e4]);
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s2, e3, seq![e4]);
    assert(seq![e4] =~= seq![e4] + Seq::<Event>::empty());
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, u3, e4, Seq::<Event>::empty());
    assert(crate::noninterference::outputs_for(rules, d, u3, u4, q4).contains(q4[2])) by {
        lemma_filter_contains_elem(q4, |o: Output| crate::noninterference::addressed_to(rules, d, u3, u4, o), 2);
    }
    assert(crate::noninterference::run_outputs_for(rules, urls, fetch, d, u4, Seq::<Event>::empty()) =~= Seq::<Output>::empty());
    assert(crate::noninterference::run_outputs_for(rules, urls, fetch, d, u3, seq![e4]).len() > 0);
    assert(crate::noninterference::run_outputs_for(rules, urls, fetch, d, s2, seq![e3, e4]).len() > 0);
    assert(crate::noninterference::run_outputs_for(rules, urls, fetch, d, s1, seq![e1, e3, e4]).len() > 0);
    assert(crate::noninterference::run_outputs_for(rules, urls, fetch, d, s0, p).len() > 0);
    assert(p =~= crate::domain::purge(rules, urls, fetch, d, t));
}

/// **Counterexample 1** (restated over `Net` events, item 3.7). For the
/// observer `Opaque(1)` (the renderer the purged run spawns): every
/// `NavigateTab` of the trace names an open tab, but its `Net` events name a
/// connection that is closed, and the outputs to the observer differ between
/// the trace and its purge. In the trace the renderer's undecodable frame
/// closes the tab and its connection, so both events are ignored; the purge
/// drops that frame, so the connection is still open when the shell reports
/// on it, the transducer sends its request and reads the response, and the
/// navigation commits into the observer's domain. So `user_tabs_open` needs
/// its clause for `Net` events.
pub proof fn example_dead_tab_breaks_noninterference(rules: Seq<clazel_psl::spec::Rule>)
    ensures
        ({
            let urls = ce_urls();
            let fetch = ce_fetch();
                    let t = ce_trace();
            let d = crate::domain::Domain::Opaque(1nat);
            !crate::noninterference::user_tabs_open(rules, urls, fetch, init_state(), t) && crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), t)
                != crate::noninterference::run_outputs_for(rules, urls, fetch, d, init_state(), crate::domain::purge(rules, urls, fetch, d, t))
        }),
{
    lemma_ce_fetch_ok();
    lemma_ce_real(rules, ce_fetch());
    lemma_ce_purged(rules, ce_fetch());
}

/// A retrieval on the empty jar leaves it empty, so the jar the purged run
/// applies a step's operations to stays empty.
pub proof fn lemma_apply_retrieval_empty(rules: Seq<clazel_psl::spec::Rule>, ops: Seq<clazel_fetch::transducer::spec::JarOp>)
    requires
        ops.len() == 1,
        ops[0] is Retrieved,
    ensures
        apply_net_ops(rules, Seq::<clazel_cookie::storage::spec::Cookie>::empty(), ops) =~= Seq::<clazel_cookie::storage::spec::Cookie>::empty(),
{
    reveal(Seq::filter);
    let jar = Seq::<clazel_cookie::storage::spec::Cookie>::empty();
    assert(ops.drop_first() =~= Seq::<clazel_fetch::transducer::spec::JarOp>::empty());
    assert(apply_net_ops(rules, apply_net_op(rules, jar, ops[0]), Seq::<clazel_fetch::transducer::spec::JarOp>::empty()) == apply_net_op(rules, jar, ops[0]));
    assert(apply_net_ops(rules, jar, ops) == apply_net_op(rules, jar, ops[0]));
    let (url, ctx, now) = (ops[0]->Retrieved_url, ops[0]->Retrieved_ctx, ops[0]->Retrieved_now);
    assert(clazel_cookie::storage::spec::evict_expired(jar, now) =~= jar);
    assert(clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now) =~= jar) by {
        if let Some(h) = url.host {
            assert(jar.map_values(clazel_cookie::storage::spec::update_last_access_time(rules, url, ctx, h, now)) =~= jar);
        }
    }
}

/// An accepted element is in the filter.
pub proof fn lemma_filter_contains_elem<A>(s: Seq<A>, p: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.len(),
        p(s[i]),
    ensures
        s.filter(p).contains(s[i]),
{
    super::projection::lemma_filter_remove_at(s, i, p);
    let k = s.subrange(0, i).filter(p).len() as int;
    assert(s.filter(p)[k] == s[i]);
}

// ---------------------------------------------------------------------
// 2. A public-suffix host-only cookie and "Leave Secure Cookies Alone".
// ---------------------------------------------------------------------

/// A secure-only host-only cookie for the host `co.uk`, which is a public
/// suffix: RFC 6265bis §5.7 step 9 lets a request to `co.uk` itself set it.
pub open spec fn ce_secure_co_uk_cookie() -> clazel_cookie::storage::spec::Cookie {
    clazel_cookie::storage::spec::Cookie {
        secure_only_flag: true,
        ..clazel_cookie::storage::examples::cookie(
            clazel_cookie::storage::examples::s_a(),
            clazel_cookie::storage::examples::s_1(),
            clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_co_uk()),
            true,
            clazel_cookie::storage::examples::p_root(),
            1,
        )
    }
}

/// **Counterexample 2 (now unreachable in the kernel: a document on a
/// public-suffix host is cookie-averse, so no cookie with a public-suffix
/// domain is ever created).** Two jars that agree on every cookie under the root
/// `a.co.uk` (they have none), one of which holds the secure host-only cookie
/// `a` of the public suffix `co.uk` (root `co.uk`, not `a.co.uk`): §5.7 step
/// 16 finds that cookie overlaid by an insecure `a` to be set for the domain
/// `x.a.co.uk` (root `a.co.uk`), and finds nothing in the other jar. So what a
/// renderer on `x.a.co.uk` may store depends on a cookie under another root,
/// and `theorem_cookie_noninterference` fails for traces with a renderer on
/// the host `co.uk`.
pub proof fn example_public_suffix_overlay_crosses_roots()
    ensures
        clazel_cookie::storage::spec::cookie_root_of(clazel_cookie::storage::examples::rules(), ce_secure_co_uk_cookie()) == clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_co_uk()),
        clazel_cookie::storage::spec::cookie_root(clazel_cookie::storage::examples::rules(), clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_x_a_co_uk())) == clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_a_co_uk()),
        clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_co_uk()) != clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_a_co_uk()),
        !clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(Seq::<clazel_cookie::storage::spec::Cookie>::empty(), clazel_cookie::storage::examples::s_a(), clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_x_a_co_uk()), clazel_cookie::storage::examples::p_root()),
        clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(seq![ce_secure_co_uk_cookie()], clazel_cookie::storage::examples::s_a(), clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_x_a_co_uk()), clazel_cookie::storage::examples::p_root()),
{
    clazel_cookie::storage::examples::example_cookie_root();
    assert(clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_co_uk()) != clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_a_co_uk())) by (compute_only);
    assert(clazel_cookie::storage::spec::canonical_domain_matches(clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_x_a_co_uk()), clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_co_uk()))) by (compute_only);
    assert(clazel_cookie::matching::spec::path_matches(clazel_cookie::storage::examples::p_root(), clazel_cookie::storage::examples::p_root())) by (compute_only);
    let jar_b = seq![ce_secure_co_uk_cookie()];
    assert(jar_b[0].name == clazel_cookie::storage::examples::s_a() && jar_b[0].secure_only_flag);
    assert(jar_b[0].domain == clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_co_uk()));
    assert(jar_b[0].path == clazel_cookie::storage::examples::p_root());
    assert(clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(jar_b, clazel_cookie::storage::examples::s_a(), clazel_cookie::storage::examples::host(clazel_cookie::storage::examples::s_x_a_co_uk()), clazel_cookie::storage::examples::p_root()));
}

// ---------------------------------------------------------------------
// 3. A retrieval changes the jar.
// ---------------------------------------------------------------------

/// **Counterexample 3.** A `document.cookie` getter for `https://a.com/x`
/// at time 9 over a jar whose first cookie it returns changes that cookie's
/// last-access-time (§5.8.3 step 5): the jar after the retrieval is not the
/// jar. The plan's "unchanged or 6265bis storage" has no case for this.
pub proof fn example_retrieval_changes_jar()
    ensures
        clazel_cookie::storage::spec::jar_after_retrieval(
            clazel_cookie::storage::examples::rules(),
            clazel_cookie::storage::examples::jar_one_matching(),
            clazel_cookie::storage::examples::https_url(clazel_cookie::storage::examples::s_a_com(), clazel_cookie::storage::examples::p_x()),
            clazel_cookie::storage::examples::document_call(),
            9,
        )[0].last_access_time == 9,
        clazel_cookie::storage::examples::jar_one_matching()[0].last_access_time == 0,
{
    reveal(Seq::filter);
    assert(clazel_cookie::storage::spec::jar_after_retrieval(
        clazel_cookie::storage::examples::rules(),
        clazel_cookie::storage::examples::jar_one_matching(),
        clazel_cookie::storage::examples::https_url(clazel_cookie::storage::examples::s_a_com(), clazel_cookie::storage::examples::p_x()),
        clazel_cookie::storage::examples::document_call(),
        9,
    )[0].last_access_time == 9) by (compute_only);
    assert(clazel_cookie::storage::examples::jar_one_matching()[0].last_access_time == 0) by (compute_only);
}

} // verus!

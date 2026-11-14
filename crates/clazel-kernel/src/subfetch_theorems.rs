//! Item 5.19's theorems: `theorem_subfetch_only_to_requester`,
//! `theorem_subfetch_credentials`, `theorem_subfetch_ownership` (the second
//! half of `theorem_connection_ownership`), `theorem_subfetch_limits` and
//! `theorem_commit_ends_subfetches`, with the statements in `statements.rs`.
//!
//! Every event but a `FetchStyle`, a `SubNet` and a `Tick` leaves the
//! sub-fetch tables as they were up to ending entries and resetting
//! document counts ([`tables_kept`]) and outputs nothing on a sub-fetch
//! connection ([`sub_free`]). A reachable state's table has each key once
//! and each entry's serial below its renderer's counter
//! ([`subfetch_tables_wf`]), which is what lets the ownership theorem read
//! an entry back by its key.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// What the other events do to the tables and the sub-fetch connections.
// ---------------------------------------------------------------------

/// No output is on a sub-fetch connection.
pub open spec fn sub_free(out: Seq<Output>) -> bool {
    forall|k: int| 0 <= k < out.len() ==> !((#[trigger] out[k]) is SubConnect || out[k] is SubSend || out[k] is SubClose)
}

/// `fs1` is `fs` with, at most, some entries ended.
pub open spec fn table_kept(fs: Seq<SubFetch>, fs1: Seq<SubFetch>) -> bool {
    &&& fs1.len() == fs.len()
    &&& forall|j: int|
        0 <= j < fs.len() ==> {
            &&& (#[trigger] fs1[j]).renderer == fs[j].renderer && fs1[j].lock == fs[j].lock && fs1[j].serial == fs[j].serial
            &&& fs1[j].tab == fs[j].tab && fs1[j].partition == fs[j].partition
            &&& (fs[j].ended ==> fs1[j].ended)
        }
}

/// `cs1` is `cs` with, at most, some document counts lowered.
pub open spec fn counts_kept(cs: Seq<SubCount>, cs1: Seq<SubCount>) -> bool {
    &&& cs1.len() == cs.len()
    &&& forall|j: int|
        0 <= j < cs.len() ==> (#[trigger] cs1[j]).renderer == cs[j].renderer && cs1[j].lock == cs[j].lock && cs1[j].serial == cs[j].serial
            && cs1[j].in_document <= cs[j].in_document
}

/// Both tables kept.
pub open spec fn tables_kept(s: State, s1: State) -> bool {
    table_kept(s.subfetches, s1.subfetches) && counts_kept(s.subcounts, s1.subcounts)
}

/// The event is a `FetchStyle` the kernel accepts from a live renderer.
pub open spec fn is_fetch_style(s: State, e: Event) -> bool {
    e matches Event::FromRenderer { id, bytes } && find_by_id(s.renderers, id, 0) matches Some(i) && accepted_message(s.renderers[i], bytes) matches Some(m)
        && m is FetchStyle
}

/// [`sub_free`] of a concatenation.
pub proof fn lemma_sub_free_concat(a: Seq<Output>, b: Seq<Output>)
    requires
        sub_free(a),
        sub_free(b),
    ensures
        sub_free(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies !((#[trigger] (a + b)[k]) is SubConnect || (a + b)[k] is SubSend || (a + b)[k] is SubClose) by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// The closes of a tab's connections are no sub-fetch outputs.
pub proof fn lemma_closes_sub_free(conns: Seq<Connection>, tab: nat)
    ensures
        sub_free(closes_of_tab(conns, tab)),
{
    crate::net_theorems::lemma_closes_of_tab(conns, tab);
    let c = closes_of_tab(conns, tab);
    assert forall|k: int| 0 <= k < c.len() implies !((#[trigger] c[k]) is SubConnect || c[k] is SubSend || c[k] is SubClose) by {
        match c[k] {
            Output::Close { .. } => {},
            _ => {},
        }
    }
}

/// `navigate_tab` keeps the tables (it ends the old document's entries and
/// resets its count) and outputs nothing on a sub-fetch connection.
pub proof fn lemma_navigate_tab_tables(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, doc: Document)
    ensures
        tables_kept(s, navigate_tab(urls, s, tab, url, doc).0),
        sub_free(navigate_tab(urls, s, tab, url, doc).1),
{
    let (s1, out) = navigate_tab(urls, s, tab, url, doc);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        let old = s.renderers[i];
        if let Some(lock) = lock_of_url(urls, url, s.next_id) {
            if lock is Tuple && lock == old.lock {
                assert(out.len() == 1 && out[0] is ToRenderer);
            } else {
                let o = replace_outputs(old.id, s.next_id, find_viewport(s.viewports, tab, 0), commit_frames(url, doc));
                assert(sub_free(o)) by {
                    assert forall|k: int| 0 <= k < o.len() implies !((#[trigger] o[k]) is SubConnect || o[k] is SubSend || o[k] is SubClose) by {
                        match find_viewport(s.viewports, tab, 0) {
                            None => {
                                assert(o.len() == 4);
                            },
                            Some(v) => {
                                assert(o.len() == 6);
                            },
                        }
                    }
                }
            }
        }
    }
}

/// `carry_out` keeps the tables and outputs nothing on a sub-fetch
/// connection.
pub proof fn lemma_carry_out_tables(urls: UrlFns, s: State, tab: nat, partition: crate::domain::Domain, cur: Option<nat>, actions: Seq<NetAction>)
    ensures
        tables_kept(s, carry_out(urls, s, tab, partition, cur, actions).0),
        sub_free(carry_out(urls, s, tab, partition, cur, actions).1),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { host, port, tls } => {
                let ep = Endpoint { host, port, tls };
                let (s1, id, out) = open_connection(s, tab, partition, ep);
                lemma_carry_out_tables(urls, s1, tab, partition, Some(id), rest);
                lemma_sub_free_concat(out, carry_out(urls, s1, tab, partition, Some(id), rest).1);
            },
            clazel_fetch::transducer::spec::Action::Send(bytes) => {
                lemma_carry_out_tables(urls, s, tab, partition, cur, rest);
                if let Some(c) = cur {
                    lemma_sub_free_concat(seq![Output::Send { conn: c, bytes }], carry_out(urls, s, tab, partition, cur, rest).1);
                }
            },
            clazel_fetch::transducer::spec::Action::Close => match cur {
                Some(c) => {
                    let s0 = State { conns: without_conn(s.conns, c), ..s };
                    lemma_carry_out_tables(urls, s0, tab, partition, None, rest);
                    lemma_sub_free_concat(seq![Output::Close { conn: c }], carry_out(urls, s0, tab, partition, None, rest).1);
                },
                None => {
                    lemma_carry_out_tables(urls, s, tab, partition, cur, rest);
                },
            },
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                let href = clazel_url::url::spec::url_serializer(url, false);
                let doc = response_document(response);
                let (s1, closes) = close_tab_conns(s, tab);
                lemma_closes_sub_free(s.conns, tab);
                if let Some(i) = find_by_tab(s1.renderers, tab, 0) {
                    if scalar_url(href) && lock_of_url(urls, href, s1.next_id) is Some {
                        lemma_navigate_tab_tables(urls, s1, tab, href, doc);
                        lemma_sub_free_concat(closes, navigate_tab(urls, s1, tab, href, doc).1);
                    } else {
                        lemma_sub_free_concat(closes, fail_navigation(s1, i, s1.renderers[i], error_bad_url()).1);
                    }
                }
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {
                let (s1, closes) = close_tab_conns(s, tab);
                lemma_closes_sub_free(s.conns, tab);
                if let Some(i) = find_by_tab(s1.renderers, tab, 0) {
                    lemma_sub_free_concat(closes, fail_navigation(s1, i, s1.renderers[i], error_fetch()).1);
                }
            },
        }
    }
}

/// `begin_navigation` keeps the tables and outputs nothing on a sub-fetch
/// connection.
pub proof fn lemma_begin_tables(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>)
    ensures
        tables_kept(s, begin_navigation(rules, urls, fetch, s, tab, url).0),
        sub_free(begin_navigation(rules, urls, fetch, s, tab, url).1),
{
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        if lock_of_url(urls, url, s.next_id) is Some {
            let (s0, closes) = close_tab_conns(s, tab);
            lemma_closes_sub_free(s.conns, tab);
            let old = s0.renderers[i];
            match (fetch.parse)(url) {
                None => {
                    lemma_sub_free_concat(closes, fail_navigation(s0, i, old, error_bad_url()).1);
                },
                Some(parsed) => {
                    let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                    let nav = Navigation { url, fetch: fs, partition: crate::domain::domain_of_renderer(rules, old) };
                    let s1 = State { renderers: s0.renderers.update(i, Renderer { pending: Some(nav), ..old }), ..s0 };
                    lemma_carry_out_tables(urls, s1, tab, nav.partition, None, actions);
                    lemma_sub_free_concat(closes, carry_out(urls, s1, tab, nav.partition, None, actions).1);
                },
            }
        }
    }
}

/// A renderer's message other than an accepted `FetchStyle` keeps the
/// tables and outputs nothing on a sub-fetch connection.
#[verifier::spinoff_prover]
pub proof fn lemma_from_renderer_tables(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        !is_fetch_style(s, Event::FromRenderer { id, bytes }),
    ensures
        tables_kept(s, from_renderer(rules, urls, fetch, s, id, bytes).0),
        sub_free(from_renderer(rules, urls, fetch, s, id, bytes).1),
{
    let (s1, out) = from_renderer(rules, urls, fetch, s, id, bytes);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        match accepted_message(r, bytes) {
            None => {
                lemma_closes_sub_free(s.conns, r.tab);
                lemma_sub_free_concat(seq![Output::Kill { id }], closes_of_tab(s.conns, r.tab));
            },
            Some(m) => {
                assert((s1, out) == handle_message(rules, urls, fetch, s, r, m));
                lemma_handle_message_tables(rules, urls, fetch, s, r, m);
            },
        }
    }
}

/// [`lemma_from_renderer_tables`] for a message that decoded.
#[verifier::spinoff_prover]
pub proof fn lemma_handle_message_tables(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    requires
        !(m is FetchStyle),
    ensures
        tables_kept(s, handle_message(rules, urls, fetch, s, r, m).0),
        sub_free(handle_message(rules, urls, fetch, s, r, m).1),
{
    let (s1, out) = handle_message(rules, urls, fetch, s, r, m);
    if let clazel_ipc::message::spec::Message::Navigate { url } = m {
        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                if lock_of_url(urls, resolved, s.next_id) is Some {
                    lemma_begin_tables(rules, urls, fetch, s, r.tab, resolved);
                }
            }
        }
    } else if m is StorageGetItem || m is StorageSetItem || m is StorageRemoveItem || m is StorageClear || m is StorageKey || m is StorageLength {
        if !(r.lock is Opaque) {
            crate::lock::lemma_storage_call_frame(s, r, m);
            lemma_storage_call_tables(s, r, m);
        }
    }
}

/// A storage call keeps the tables and answers with one frame.
pub proof fn lemma_storage_call_tables(s: State, r: Renderer, m: clazel_ipc::message::spec::Message)
    ensures
        storage_call(s, r, m).0.subfetches == s.subfetches,
        storage_call(s, r, m).0.subcounts == s.subcounts,
        sub_free(storage_call(s, r, m).1),
{
    let out = storage_call(s, r, m).1;
    assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is SubConnect || out[k] is SubSend || out[k] is SubClose) by {
        assert(out.len() == 1 && out[0] is ToRenderer);
    }
}

/// `OpenTab` keeps the tables and outputs nothing on a sub-fetch
/// connection.
#[verifier::spinoff_prover]
pub proof fn lemma_open_tab_tables(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, url: Seq<u32>, script: Option<Seq<u8>>)
    ensures
        tables_kept(s, open_tab(rules, urls, fetch, s, url, script).0),
        sub_free(open_tab(rules, urls, fetch, s, url, script).1),
{
    let id = s.next_id;
    if let Some(lock) = lock_of_url(urls, url, id) {
        if script is None {
            let s0 = State { renderers: s.renderers.push(Renderer { committed: false, id, tab: id, url, lock, pending: None }), next_id: id + 1, ..s };
            lemma_begin_tables(rules, urls, fetch, s0, id, url);
            lemma_sub_free_concat(
                seq![Output::Spawn { id, policy: Policy::Gpu }, Output::Spawn { id, policy: Policy::Renderer }],
                begin_navigation(rules, urls, fetch, s0, id, url).1,
            );
        } else {
            let out = open_tab(rules, urls, fetch, s, url, script).1;
            assert(out.len() == 3);
        }
    }
}

/// A `Net` event keeps the tables and outputs nothing on a sub-fetch
/// connection.
#[verifier::spinoff_prover]
pub proof fn lemma_net_tables(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    ensures
        tables_kept(s, net(rules, urls, fetch, s, conn, input).0),
        sub_free(net(rules, urls, fetch, s, conn, input).1),
{
    if let Some((c, i, nav)) = net_target(s, conn) {
        let (fs, actions, ops) = net_transducer_step(fetch, s, nav, input);
        let conns = if input is Closed || input is Error { without_conn(s.conns, conn) } else { s.conns };
        let s0 = State {
            jar: apply_net_ops(rules, s.jar, ops),
            conns,
            renderers: s.renderers.update(i, Renderer { pending: Some(Navigation { fetch: fs, ..nav }), ..s.renderers[i] }),
            ..s
        };
        lemma_carry_out_tables(urls, s0, c.tab, nav.partition, Some(conn), actions);
    }
}

/// **Every event but a `FetchStyle`, a `SubNet` and a `Tick` keeps the
/// sub-fetch tables and outputs nothing on a sub-fetch connection.**
#[verifier::spinoff_prover]
pub proof fn lemma_step_tables(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        !(e is SubNet || e is Tick || is_fetch_style(s, e)),
    ensures
        tables_kept(s, step(rules, urls, fetch, s, e).0),
        sub_free(step(rules, urls, fetch, s, e).1),
{
    match e {
        Event::FromRenderer { id, bytes } => lemma_from_renderer_tables(rules, urls, fetch, s, id, bytes),
        Event::OpenTab { url, script } => lemma_open_tab_tables(rules, urls, fetch, s, url, script),
        Event::NavigateTab { tab, url } => lemma_begin_tables(rules, urls, fetch, s, tab, url),
        Event::Net { conn, input } => lemma_net_tables(rules, urls, fetch, s, conn, input),
        Event::RendererExited { id } => {
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                lemma_closes_sub_free(s.conns, s.renderers[i].tab);
            }
        },
        Event::FromGpu { id, bytes } => {
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                lemma_closes_sub_free(s.conns, s.renderers[i].tab);
                lemma_sub_free_concat(seq![Output::Kill { id }], closes_of_tab(s.conns, s.renderers[i].tab));
            }
        },
        Event::Resize { tab, width, height, scale } => {
            let out = step(rules, urls, fetch, s, e).1;
            assert(out.len() == 0 || out.len() == 2);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------
// Counting.
// ---------------------------------------------------------------------

/// A kept table has no more live entries of a key than before.
pub proof fn lemma_kept_live(fs: Seq<SubFetch>, fs1: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin)
    requires
        table_kept(fs, fs1),
    ensures
        live_subfetches(fs1, id, lock) <= live_subfetches(fs, id, lock),
    decreases fs.len(),
{
    if fs.len() > 0 {
        assert(table_kept(fs.drop_first(), fs1.drop_first())) by {
            assert forall|j: int| 0 <= j < fs.drop_first().len() implies (#[trigger] fs1.drop_first()[j]) == fs1[j + 1] && fs.drop_first()[j] == fs[j + 1] by {}
        }
        lemma_kept_live(fs.drop_first(), fs1.drop_first(), id, lock);
    }
}

/// A kept count table has the same counters and no larger document counts.
pub proof fn lemma_kept_subcount(cs: Seq<SubCount>, cs1: Seq<SubCount>, id: nat, lock: clazel_origin::spec::Origin)
    requires
        counts_kept(cs, cs1),
    ensures
        subcount_of(cs1, id, lock).0 == subcount_of(cs, id, lock).0,
        subcount_of(cs1, id, lock).1 <= subcount_of(cs, id, lock).1,
    decreases cs.len(),
{
    if cs.len() > 0 {
        assert(counts_kept(cs.drop_first(), cs1.drop_first())) by {
            assert forall|j: int| 0 <= j < cs.drop_first().len() implies (#[trigger] cs1.drop_first()[j]) == cs1[j + 1] && cs.drop_first()[j] == cs[j + 1] by {}
        }
        lemma_kept_subcount(cs.drop_first(), cs1.drop_first(), id, lock);
    }
}

/// The live entries of a key after a push.
pub proof fn lemma_live_push(fs: Seq<SubFetch>, n: SubFetch, id: nat, lock: clazel_origin::spec::Origin)
    ensures
        live_subfetches(fs.push(n), id, lock) == live_subfetches(fs, id, lock) + (if n.renderer == id && n.lock == lock && !n.ended { 1nat } else { 0nat }),
    decreases fs.len(),
{
    if fs.len() == 0 {
        assert(fs.push(n).drop_first() =~= Seq::<SubFetch>::empty());
        assert(fs.push(n)[0] == n);
        assert(live_subfetches(Seq::<SubFetch>::empty(), id, lock) == 0);
    } else {
        assert(fs.push(n).drop_first() =~= fs.drop_first().push(n));
        assert(fs.push(n)[0] == fs[0]);
        lemma_live_push(fs.drop_first(), n, id, lock);
    }
}

/// A key's counts in a table without that key, after a push.
pub proof fn lemma_subcount_push(cs: Seq<SubCount>, n: SubCount, id: nat, lock: clazel_origin::spec::Origin)
    ensures
        (forall|j: int| 0 <= j < cs.len() ==> !((#[trigger] cs[j]).renderer == id && cs[j].lock == lock)) ==> subcount_of(cs.push(n), id, lock) == (if n.renderer
            == id && n.lock == lock { (n.serial, n.in_document) } else { (0nat, 0nat) }),
        !(n.renderer == id && n.lock == lock) ==> subcount_of(cs.push(n), id, lock) == subcount_of(cs, id, lock),
    decreases cs.len(),
{
    if cs.len() == 0 {
        assert(cs.push(n).drop_first() =~= Seq::<SubCount>::empty());
        assert(cs.push(n)[0] == n);
        assert(subcount_of(Seq::<SubCount>::empty(), id, lock) == (0nat, 0nat));
    } else {
        let t = cs.drop_first();
        assert(cs.push(n).drop_first() =~= t.push(n));
        assert(cs.push(n)[0] == cs[0]);
        lemma_subcount_push(t, n, id, lock);
        if cs[0].renderer == id && cs[0].lock == lock {
            assert(subcount_of(cs.push(n), id, lock) == (cs[0].serial, cs[0].in_document));
        } else {
            assert(subcount_of(cs.push(n), id, lock) == subcount_of(t.push(n), id, lock));
            assert(subcount_of(cs, id, lock) == subcount_of(t, id, lock));
        }
        if forall|j: int| 0 <= j < cs.len() ==> !((#[trigger] cs[j]).renderer == id && cs[j].lock == lock) {
            assert(!(cs[0].renderer == id && cs[0].lock == lock));
            assert forall|j: int| 0 <= j < cs.drop_first().len() implies !((#[trigger] cs.drop_first()[j]).renderer == id && cs.drop_first()[j].lock == lock) by {
                assert(cs.drop_first()[j] == cs[j + 1]);
            }
        }
    }
}

/// Filtering out one key keeps the counts of every other.
pub proof fn lemma_subcount_filter(cs: Seq<SubCount>, id: nat, lock: clazel_origin::spec::Origin, x: nat, y: clazel_origin::spec::Origin)
    requires
        !(x == id && y == lock),
    ensures
        subcount_of(cs.filter(|c: SubCount| !(c.renderer == id && c.lock == lock)), x, y) == subcount_of(cs, x, y),
    decreases cs.len(),
{
    let p = |c: SubCount| !(c.renderer == id && c.lock == lock);
    if cs.len() > 0 {
        let c = cs[0];
        let t = cs.drop_first();
        assert(cs =~= seq![c] + t);
        t.lemma_filter_prepend(c, p);
        lemma_subcount_filter(t, id, lock, x, y);
        let ft = t.filter(p);
        if p(c) {
            assert((seq![c] + ft)[0] == c);
            assert((seq![c] + ft).drop_first() =~= ft);
        }
    } else {
        reveal(Seq::filter);
    }
}

/// The counts after [`set_subcount`].
pub proof fn lemma_subcount_set(cs: Seq<SubCount>, id: nat, lock: clazel_origin::spec::Origin, serial: nat, in_document: nat, x: nat, y: clazel_origin::spec::Origin)
    ensures
        subcount_of(set_subcount(cs, id, lock, serial, in_document), x, y) == (if x == id && y == lock { (serial, in_document) } else { subcount_of(cs, x, y) }),
{
    let p = |c: SubCount| !(c.renderer == id && c.lock == lock);
    let f = cs.filter(p);
    let n = SubCount { renderer: id, lock, serial, in_document };
    lemma_subcount_push(f, n, x, y);
    if x == id && y == lock {
        assert forall|j: int| 0 <= j < f.len() implies !((#[trigger] f[j]).renderer == x && f[j].lock == y) by {
            cs.lemma_filter_pred(p, j);
        }
    } else {
        lemma_subcount_filter(cs, id, lock, x, y);
    }
}

// ---------------------------------------------------------------------
// The table by key.
// ---------------------------------------------------------------------

/// Each key occurs at most once in the table.
pub open spec fn keys_unique(fs: Seq<SubFetch>) -> bool
    decreases fs.len(),
{
    fs.len() == 0 || (subfetch_of(fs.drop_first(), fs[0].renderer, fs[0].lock, fs[0].serial) is None && keys_unique(fs.drop_first()))
}

/// Each entry's serial is below its renderer's counter.
pub open spec fn serials_below(fs: Seq<SubFetch>, cs: Seq<SubCount>) -> bool {
    forall|j: int| 0 <= j < fs.len() ==> (#[trigger] fs[j]).serial < subcount_of(cs, fs[j].renderer, fs[j].lock).0
}

/// The invariant of the sub-fetch tables.
pub open spec fn subfetch_tables_wf(s: State) -> bool {
    keys_unique(s.subfetches) && serials_below(s.subfetches, s.subcounts)
}

/// Every element of `a` is in `b`.
pub open spec fn elems_in(a: Seq<SubFetch>, b: Seq<SubFetch>) -> bool {
    forall|j: int| 0 <= j < a.len() ==> b.contains(#[trigger] a[j])
}

/// A key is absent exactly when no entry has it.
pub proof fn lemma_of_none(fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, serial: nat)
    ensures
        subfetch_of(fs, id, lock, serial) is None <==> forall|j: int| 0 <= j < fs.len() ==> !subfetch_is(#[trigger] fs[j], id, lock, serial),
    decreases fs.len(),
{
    if fs.len() > 0 {
        lemma_of_none(fs.drop_first(), id, lock, serial);
        if subfetch_of(fs, id, lock, serial) is None {
            assert forall|j: int| 0 <= j < fs.len() implies !subfetch_is(#[trigger] fs[j], id, lock, serial) by {
                if j > 0 {
                    assert(fs[j] == fs.drop_first()[j - 1]);
                }
            }
        } else if forall|j: int| 0 <= j < fs.len() ==> !subfetch_is(#[trigger] fs[j], id, lock, serial) {
            assert(!subfetch_is(fs[0], id, lock, serial));
            assert forall|j: int| 0 <= j < fs.drop_first().len() implies !subfetch_is(#[trigger] fs.drop_first()[j], id, lock, serial) by {
                assert(fs.drop_first()[j] == fs[j + 1]);
            }
        }
    }
}

/// In a table with each key once, an entry is the one read by its key.
pub proof fn lemma_unique_of(fs: Seq<SubFetch>, j: int)
    requires
        keys_unique(fs),
        0 <= j < fs.len(),
    ensures
        subfetch_of(fs, fs[j].renderer, fs[j].lock, fs[j].serial) == Some(fs[j]),
    decreases fs.len(),
{
    if j > 0 {
        let t = fs.drop_first();
        assert(fs[j] == t[j - 1]);
        lemma_unique_of(t, j - 1);
        if subfetch_is(fs[0], fs[j].renderer, fs[j].lock, fs[j].serial) {
            lemma_of_none(t, fs[0].renderer, fs[0].lock, fs[0].serial);
            assert(subfetch_is(t[j - 1], fs[0].renderer, fs[0].lock, fs[0].serial));
        }
    }
}

/// [`lemma_unique_of`] by membership.
pub proof fn lemma_unique_contains(fs: Seq<SubFetch>, x: SubFetch)
    requires
        keys_unique(fs),
        fs.contains(x),
    ensures
        subfetch_of(fs, x.renderer, x.lock, x.serial) == Some(x),
{
    let j = choose|j: int| 0 <= j < fs.len() && fs[j] == x;
    lemma_unique_of(fs, j);
}

/// A kept table keeps each key once.
pub proof fn lemma_kept_unique(fs: Seq<SubFetch>, fs1: Seq<SubFetch>)
    requires
        table_kept(fs, fs1),
        keys_unique(fs),
    ensures
        keys_unique(fs1),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let t = fs.drop_first();
        let t1 = fs1.drop_first();
        assert(table_kept(t, t1)) by {
            assert forall|j: int| 0 <= j < t.len() implies (#[trigger] t1[j]) == fs1[j + 1] && t[j] == fs[j + 1] by {}
        }
        lemma_kept_unique(t, t1);
        lemma_of_none(t, fs[0].renderer, fs[0].lock, fs[0].serial);
        lemma_of_none(t1, fs1[0].renderer, fs1[0].lock, fs1[0].serial);
        assert forall|j: int| 0 <= j < t1.len() implies !subfetch_is(#[trigger] t1[j], fs1[0].renderer, fs1[0].lock, fs1[0].serial) by {
            assert(!subfetch_is(t[j], fs[0].renderer, fs[0].lock, fs[0].serial));
        }
    }
}

/// A kept table keeps the serials below their kept counters.
pub proof fn lemma_kept_below(fs: Seq<SubFetch>, fs1: Seq<SubFetch>, cs: Seq<SubCount>, cs1: Seq<SubCount>)
    requires
        table_kept(fs, fs1),
        counts_kept(cs, cs1),
        serials_below(fs, cs),
    ensures
        serials_below(fs1, cs1),
{
    assert forall|j: int| 0 <= j < fs1.len() implies (#[trigger] fs1[j]).serial < subcount_of(cs1, fs1[j].renderer, fs1[j].lock).0 by {
        lemma_kept_subcount(cs, cs1, fs1[j].renderer, fs1[j].lock);
        assert(fs[j].serial < subcount_of(cs, fs[j].renderer, fs[j].lock).0);
    }
}

/// A subset of a table with each key once has each key once, if it keeps
/// the order of [`drop_subfetch`] and [`sweep`]: a head and a subset of the
/// tail.
pub proof fn lemma_cons_unique(x: SubFetch, t: Seq<SubFetch>, a: Seq<SubFetch>)
    requires
        subfetch_of(t, x.renderer, x.lock, x.serial) is None,
        elems_in(a, t),
        keys_unique(a),
    ensures
        keys_unique(seq![x] + a),
        elems_in(seq![x] + a, seq![x] + t),
{
    let xa = seq![x] + a;
    assert(xa[0] == x);
    assert(xa.drop_first() =~= a);
    lemma_of_none(t, x.renderer, x.lock, x.serial);
    lemma_of_none(a, x.renderer, x.lock, x.serial);
    assert forall|j: int| 0 <= j < a.len() implies !subfetch_is(#[trigger] a[j], x.renderer, x.lock, x.serial) by {
        assert(t.contains(a[j]));
    }
    assert forall|j: int| 0 <= j < xa.len() implies (seq![x] + t).contains(#[trigger] xa[j]) by {
        if j == 0 {
            assert((seq![x] + t)[0] == x);
        } else {
            assert(xa[j] == a[j - 1]);
            let m = choose|m: int| 0 <= m < t.len() && t[m] == a[j - 1];
            assert((seq![x] + t)[m + 1] == t[m]);
        }
    }
}

/// [`elems_in`] into a longer table.
pub proof fn lemma_elems_in_cons(a: Seq<SubFetch>, x: SubFetch, t: Seq<SubFetch>)
    requires
        elems_in(a, t),
    ensures
        elems_in(a, seq![x] + t),
{
    assert forall|j: int| 0 <= j < a.len() implies (seq![x] + t).contains(#[trigger] a[j]) by {
        let m = choose|m: int| 0 <= m < t.len() && t[m] == a[j];
        assert((seq![x] + t)[m + 1] == t[m]);
    }
}

/// Dropping an entry keeps each key once and adds no entry, nor any live
/// one.
pub proof fn lemma_drop_table(fs: Seq<SubFetch>, g: SubFetch, id: nat, lock: clazel_origin::spec::Origin)
    requires
        keys_unique(fs),
    ensures
        keys_unique(drop_subfetch(fs, g)),
        elems_in(drop_subfetch(fs, g), fs),
        live_subfetches(drop_subfetch(fs, g), id, lock) <= live_subfetches(fs, id, lock),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs =~= seq![x] + t);
        if subfetch_is(x, g.renderer, g.lock, g.serial) {
            assert forall|j: int| 0 <= j < t.len() implies fs.contains(#[trigger] t[j]) by {
                assert(fs[j + 1] == t[j]);
            }
        } else {
            lemma_drop_table(t, g, id, lock);
            let a = drop_subfetch(t, g);
            lemma_cons_unique(x, t, a);
            assert((seq![x] + a).drop_first() =~= a);
        }
    }
}

/// [`sweep`] keeps each key once and adds no entry, nor any live one.
pub proof fn lemma_sweep_table(s: State, fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin)
    requires
        keys_unique(fs),
    ensures
        keys_unique(sweep(s, fs).0),
        elems_in(sweep(s, fs).0, fs),
        live_subfetches(sweep(s, fs).0, id, lock) <= live_subfetches(fs, id, lock),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs =~= seq![x] + t);
        lemma_sweep_table(s, t, id, lock);
        let a = sweep(s, t).0;
        if !subfetch_live(s, x) || s.now >= x.started + subfetch_timeout() {
            lemma_elems_in_cons(a, x, t);
        } else {
            lemma_cons_unique(x, t, a);
            assert((seq![x] + a).drop_first() =~= a);
            assert((seq![x] + a)[0] == x);
        }
    }
}

/// [`replace_subfetch`] of an entry by one with the same key, tab, partition
/// and end keeps the table.
pub proof fn lemma_replace_kept(fs: Seq<SubFetch>, f: SubFetch, g: SubFetch)
    requires
        subfetch_of(fs, g.renderer, g.lock, g.serial) == Some(f),
        g.renderer == f.renderer && g.lock == f.lock && g.serial == f.serial && g.tab == f.tab && g.partition == f.partition && g.ended == f.ended,
    ensures
        table_kept(fs, replace_subfetch(fs, g)),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        let r = replace_subfetch(fs, g);
        if subfetch_is(x, g.renderer, g.lock, g.serial) {
            assert forall|j: int| 0 <= j < fs.len() implies {
                &&& (#[trigger] r[j]).renderer == fs[j].renderer && r[j].lock == fs[j].lock && r[j].serial == fs[j].serial
                &&& r[j].tab == fs[j].tab && r[j].partition == fs[j].partition
                &&& (fs[j].ended ==> r[j].ended)
            } by {
                if j > 0 {
                    assert(r[j] == t[j - 1]);
                }
            }
        } else {
            lemma_replace_kept(t, f, g);
            let rt = replace_subfetch(t, g);
            assert forall|j: int| 0 <= j < fs.len() implies {
                &&& (#[trigger] r[j]).renderer == fs[j].renderer && r[j].lock == fs[j].lock && r[j].serial == fs[j].serial
                &&& r[j].tab == fs[j].tab && r[j].partition == fs[j].partition
                &&& (fs[j].ended ==> r[j].ended)
            } by {
                if j > 0 {
                    assert(r[j] == rt[j - 1]);
                    assert(fs[j] == t[j - 1]);
                }
            }
        }
    }
}

/// Pushing an entry whose key is absent keeps each key once.
pub proof fn lemma_push_unique(fs: Seq<SubFetch>, n: SubFetch)
    requires
        keys_unique(fs),
        subfetch_of(fs, n.renderer, n.lock, n.serial) is None,
    ensures
        keys_unique(fs.push(n)),
    decreases fs.len(),
{
    if fs.len() == 0 {
        assert(fs.push(n).drop_first() =~= Seq::<SubFetch>::empty());
        assert(keys_unique(Seq::<SubFetch>::empty()));
        assert(subfetch_of(Seq::<SubFetch>::empty(), n.renderer, n.lock, n.serial) is None);
        assert(fs.push(n)[0] == n);
    } else {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs.push(n).drop_first() =~= t.push(n));
        assert(fs.push(n)[0] == x);
        lemma_of_none(fs, n.renderer, n.lock, n.serial);
        lemma_of_none(t, n.renderer, n.lock, n.serial);
        assert forall|j: int| 0 <= j < t.len() implies !subfetch_is(#[trigger] t[j], n.renderer, n.lock, n.serial) by {
            assert(t[j] == fs[j + 1]);
        }
        lemma_push_unique(t, n);
        lemma_of_none(t, x.renderer, x.lock, x.serial);
        lemma_of_none(t.push(n), x.renderer, x.lock, x.serial);
        assert(!subfetch_is(fs[0], n.renderer, n.lock, n.serial));
        assert forall|j: int| 0 <= j < t.push(n).len() implies !subfetch_is(#[trigger] t.push(n)[j], x.renderer, x.lock, x.serial) by {
            if j < t.len() {
                assert(t.push(n)[j] == t[j]);
            }
        }
        assert(subfetch_of(t.push(n), x.renderer, x.lock, x.serial) is None);
        assert(keys_unique(t.push(n)));
    }
}

/// The initial state satisfies the tables' invariant.
pub proof fn lemma_init_tables_wf()
    ensures
        subfetch_tables_wf(init_state()),
{
}

/// What a `SubNet` does to the tables: a kept table or one entry dropped,
/// and the counts unchanged.
pub proof fn lemma_sub_net_tables(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns, s: State, renderer: nat, serial: nat, hop: nat, input: NetInput, id: nat, lock: clazel_origin::spec::Origin)
    requires
        keys_unique(s.subfetches),
    ensures
        ({
            let s1 = sub_net(rules, fetch, s, renderer, serial, hop, input).0;
            &&& s1.subcounts == s.subcounts
            &&& keys_unique(s1.subfetches)
            &&& live_subfetches(s1.subfetches, id, lock) <= live_subfetches(s.subfetches, id, lock)
            &&& forall|j: int|
                0 <= j < s1.subfetches.len() ==> owned_by_key(s.subfetches, #[trigger] s1.subfetches[j])
        }),
{
    let s1 = sub_net(rules, fetch, s, renderer, serial, hop, input).0;
    lemma_subnet_key_facts(s, renderer, serial);
    if let Some(f) = subnet_target(s, renderer, serial) {
        if subfetch_live(s, f) && hop != 0 && f.hop == hop {
            let (fsa, actions, ops) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, subfetch_jar(fetch, s, f), s.now);
            let (h, out, end) = sub_actions(renderer, serial, f.request, hop, actions);
            let g = SubFetch { fetch: fsa, hop: h, ..f };
            if end is Some {
                lemma_drop_table(s.subfetches, g, id, lock);
                let d = drop_subfetch(s.subfetches, g);
                assert forall|j: int| 0 <= j < d.len() implies owned_by_key(s.subfetches, #[trigger] d[j]) by {
                    assert(s.subfetches.contains(d[j]));
                    lemma_unique_contains(s.subfetches, d[j]);
                }
            } else {
                lemma_replace_kept(s.subfetches, f, g);
                let r = replace_subfetch(s.subfetches, g);
                lemma_kept_unique(s.subfetches, r);
                lemma_kept_live(s.subfetches, r, id, lock);
                assert forall|j: int| 0 <= j < r.len() implies owned_by_key(s.subfetches, #[trigger] r[j]) by {
                    lemma_unique_of(s.subfetches, j);
                }
            }
        } else {
            lemma_kept_identity(s.subfetches);
        }
    } else {
        lemma_kept_identity(s.subfetches);
    }
    if s1.subfetches == s.subfetches {
        assert forall|j: int| 0 <= j < s1.subfetches.len() implies owned_by_key(s.subfetches, #[trigger] s1.subfetches[j]) by {
            lemma_unique_of(s.subfetches, j);
        }
    }
}

/// `x`'s key reads an entry of `fs` with `x`'s tab and partition.
pub open spec fn owned_by_key(fs: Seq<SubFetch>, x: SubFetch) -> bool {
    subfetch_of(fs, x.renderer, x.lock, x.serial) matches Some(f0) && f0.tab == x.tab && f0.partition == x.partition
}

/// A table is kept by itself.
pub proof fn lemma_kept_identity(fs: Seq<SubFetch>)
    ensures
        table_kept(fs, fs),
{
}

/// The key of the sub-fetch a `SubNet` is about.
pub proof fn lemma_subnet_key_facts(s: State, renderer: nat, serial: nat)
    ensures
        subnet_target(s, renderer, serial) matches Some(f) ==> (find_by_id(s.renderers, renderer, 0) matches Some(i) && subfetch_of(
            s.subfetches,
            f.renderer,
            f.lock,
            f.serial,
        ) == Some(f) && f.renderer == renderer && f.serial == serial && f.lock == s.renderers[i].lock),
{
    crate::subfetch_rel::lemma_subnet_target_key(s, renderer, serial);
}

/// What a `FetchStyle` does to the tables.
pub proof fn lemma_fetch_style_tables(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    r: Renderer,
    request: u64,
    url: Seq<u8>,
    id: nat,
    lock: clazel_origin::spec::Origin,
)
    ensures
        ({
            let s1 = fetch_style(rules, urls, fetch, s, r, request, url).0;
            let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
            &&& s1 == s || {
                &&& serial < max_subfetch_serial()
                &&& live_subfetches(s.subfetches, r.id, r.lock) < max_subfetches_at_once()
                &&& in_document < max_subfetches_per_document()
                &&& s1.subcounts == set_subcount(s.subcounts, r.id, r.lock, serial + 1, in_document + 1)
                &&& (s1.subfetches == s.subfetches || exists|n: SubFetch|
                    #![trigger s.subfetches.push(n)]
                    s1.subfetches == s.subfetches.push(n) && n.renderer == r.id && n.lock == r.lock && n.serial == serial && n.tab == r.tab && n.partition
                        == crate::domain::domain_of_renderer(rules, r) && !n.ended)
            }
        }),
{
}

/// **The tables' invariant holds after every step.**
pub proof fn lemma_step_tables_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        subfetch_tables_wf(s),
    ensures
        subfetch_tables_wf(step(rules, urls, fetch, s, e).0),
{
    let s1 = step(rules, urls, fetch, s, e).0;
    if is_fetch_style(s, e) {
        let id = e->FromRenderer_id;
        let i = find_by_id(s.renderers, id, 0)->Some_0;
        let r = s.renderers[i];
        let m = accepted_message(r, e->FromRenderer_bytes)->Some_0;
        let request = m->FetchStyle_request;
        let url = m->FetchStyle_url;
        assert(s1 == fetch_style(rules, urls, fetch, s, r, request, url).0);
        lemma_fetch_style_tables(rules, urls, fetch, s, r, request, url, r.id, r.lock);
        if s1 != s {
            let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
            assert forall|j: int| 0 <= j < s1.subfetches.len() implies (#[trigger] s1.subfetches[j]).serial < subcount_of(
                s1.subcounts,
                s1.subfetches[j].renderer,
                s1.subfetches[j].lock,
            ).0 by {
                lemma_subcount_set(s.subcounts, r.id, r.lock, serial + 1, in_document + 1, s1.subfetches[j].renderer, s1.subfetches[j].lock);
                if j < s.subfetches.len() {
                    assert(s1.subfetches[j] == s.subfetches[j]);
                }
            }
            if s1.subfetches != s.subfetches {
                let n = choose|n: SubFetch|
                    #![trigger s.subfetches.push(n)]
                    s1.subfetches == s.subfetches.push(n) && n.renderer == r.id && n.lock == r.lock && n.serial == serial && n.tab == r.tab && n.partition
                        == crate::domain::domain_of_renderer(rules, r) && !n.ended;
                lemma_of_none(s.subfetches, n.renderer, n.lock, n.serial);
                assert forall|j: int| 0 <= j < s.subfetches.len() implies !subfetch_is(#[trigger] s.subfetches[j], n.renderer, n.lock, n.serial) by {
                    assert(s.subfetches[j].serial < subcount_of(s.subcounts, s.subfetches[j].renderer, s.subfetches[j].lock).0);
                }
                lemma_push_unique(s.subfetches, n);
            }
        }
    } else {
        match e {
            Event::SubNet { renderer, serial, hop, input } => {
                lemma_sub_net_tables(rules, fetch, s, renderer, serial, hop, input, 0, arbitrary_lock());
                assert forall|j: int| 0 <= j < s1.subfetches.len() implies (#[trigger] s1.subfetches[j]).serial < subcount_of(
                    s1.subcounts,
                    s1.subfetches[j].renderer,
                    s1.subfetches[j].lock,
                ).0 by {
                    let f0 = subfetch_of(s.subfetches, s1.subfetches[j].renderer, s1.subfetches[j].lock, s1.subfetches[j].serial)->Some_0;
                    crate::subfetch_rel::lemma_subfetch_of_key(s.subfetches, s1.subfetches[j].renderer, s1.subfetches[j].lock, s1.subfetches[j].serial);
                    lemma_of_member(s.subfetches, s1.subfetches[j].renderer, s1.subfetches[j].lock, s1.subfetches[j].serial);
                    let m = choose|m: int| 0 <= m < s.subfetches.len() && s.subfetches[m] == f0;
                    assert(s.subfetches[m].serial < subcount_of(s.subcounts, s.subfetches[m].renderer, s.subfetches[m].lock).0);
                }
            },
            Event::Tick { time } => {
                crate::subfetch_rel::lemma_tick_all_shape(s, time);
                let t = tick(s, time).0;
                lemma_sweep_table(t, s.subfetches, 0, arbitrary_lock());
                let a = sweep(t, s.subfetches).0;
                assert forall|j: int| 0 <= j < a.len() implies (#[trigger] a[j]).serial < subcount_of(s1.subcounts, a[j].renderer, a[j].lock).0 by {
                    let m = choose|m: int| 0 <= m < s.subfetches.len() && s.subfetches[m] == a[j];
                    assert(s.subfetches[m].serial < subcount_of(s.subcounts, s.subfetches[m].renderer, s.subfetches[m].lock).0);
                }
            },
            _ => {
                lemma_step_tables(rules, urls, fetch, s, e);
                lemma_kept_unique(s.subfetches, s1.subfetches);
                lemma_kept_below(s.subfetches, s1.subfetches, s.subcounts, s1.subcounts);
            },
        }
    }
}

/// Some lock, for the lemmas whose live-count conclusion is not used.
pub open spec fn arbitrary_lock() -> clazel_origin::spec::Origin {
    clazel_origin::spec::Origin::Opaque(0)
}

/// The entry read by a key is in the table.
pub proof fn lemma_of_member(fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, serial: nat)
    ensures
        subfetch_of(fs, id, lock, serial) matches Some(f) ==> fs.contains(f),
    decreases fs.len(),
{
    if fs.len() > 0 {
        lemma_of_member(fs.drop_first(), id, lock, serial);
        if !subfetch_is(fs[0], id, lock, serial) {
            if let Some(f) = subfetch_of(fs, id, lock, serial) {
                let m = choose|m: int| 0 <= m < fs.drop_first().len() && fs.drop_first()[m] == f;
                assert(fs[m + 1] == f);
            }
        } else {
            assert(fs[0] == fs[0]);
        }
    }
}

/// The invariant along a run.
pub proof fn lemma_run_tables_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, t: Seq<Event>)
    requires
        subfetch_tables_wf(s),
    ensures
        subfetch_tables_wf(run_state(rules, urls, fetch, s, t)),
    decreases t.len(),
{
    if t.len() > 0 {
        lemma_step_tables_wf(rules, urls, fetch, s, t[0]);
        lemma_run_tables_wf(rules, urls, fetch, step(rules, urls, fetch, s, t[0]).0, t.drop_first());
    }
}

/// **Every reachable state satisfies the tables' invariant.**
pub proof fn lemma_reachable_tables_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        subfetch_tables_wf(s),
{
    lemma_init_tables_wf();
    let t = choose|t: Seq<Event>| run_state(rules, urls, fetch, init_state(), t) == s;
    lemma_run_tables_wf(rules, urls, fetch, init_state(), t);
}

// ---------------------------------------------------------------------
// A sub-fetch's frames and sends.
// ---------------------------------------------------------------------

/// The frames a sub-fetch's actions end with are `StyleFailed`, or a sheet's
/// `StyleResponse`, `StyleBody` and `StyleEnd`.
pub proof fn lemma_sub_actions_end(id: nat, serial: nat, request: u64, hop: nat, actions: Seq<NetAction>)
    ensures
        sub_actions(id, serial, request, hop, actions).2 matches Some(x) ==> (x == style_failed_frame(request) || exists|doc: Document|
            x == #[trigger] style_frames(request, doc)),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { .. } => lemma_sub_actions_end(id, serial, request, hop + 1, rest),
            clazel_fetch::transducer::spec::Action::Send(_) => lemma_sub_actions_end(id, serial, request, hop, rest),
            clazel_fetch::transducer::spec::Action::Close => lemma_sub_actions_end(id, serial, request, hop, rest),
            clazel_fetch::transducer::spec::Action::Done { url, response } => {
                let doc = response_document(response);
                assert(sub_actions(id, serial, request, hop, actions).2 == Some(style_frames(request, doc)));
            },
            clazel_fetch::transducer::spec::Action::Fail(_) => {},
        }
    }
}

/// Actions with no `Send` give no `SubSend`.
pub proof fn lemma_sub_actions_no_send(id: nat, serial: nat, request: u64, hop: nat, actions: Seq<NetAction>)
    requires
        clazel_fetch::transducer::theorems::no_sends(actions),
    ensures
        forall|k: int| 0 <= k < sub_actions(id, serial, request, hop, actions).1.len() ==> !((#[trigger] sub_actions(id, serial, request, hop, actions).1[k]) is SubSend),
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        assert(clazel_fetch::transducer::theorems::no_sends(rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies !(#[trigger] rest[k] is Send) by {
                assert(rest[k] == actions[k + 1]);
            }
        }
        assert(!(actions[0] is Send));
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { .. } => lemma_sub_actions_no_send(id, serial, request, hop + 1, rest),
            clazel_fetch::transducer::spec::Action::Close => lemma_sub_actions_no_send(id, serial, request, hop, rest),
            _ => {},
        }
    }
}

/// A `FetchStyle` sends nothing on a sub-fetch connection: the transducer's
/// `start` only asks for a connection, or fails.
pub proof fn lemma_fetch_style_no_send(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, request: u64, url: Seq<u8>)
    ensures
        forall|k: int|
            0 <= k < fetch_style(rules, urls, fetch, s, r, request, url).1.len() ==> !((#[trigger] fetch_style(rules, urls, fetch, s, r, request, url).1[k]) is SubSend),
{
    let out = fetch_style(rules, urls, fetch, s, r, request, url).1;
    let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
    if !(live_subfetches(s.subfetches, r.id, r.lock) >= max_subfetches_at_once() || in_document >= max_subfetches_per_document() || serial
        >= max_subfetch_serial()) {
        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                if let Some(parsed) = (fetch.parse)(resolved) {
                    let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                    assert(clazel_fetch::transducer::theorems::no_sends(actions)) by {
                        reveal_with_fuel(clazel_fetch::transducer::spec::begin, 1);
                        assert(actions.len() == 1);
                    }
                    lemma_sub_actions_no_send(r.id, serial, request, 0, actions);
                    let o = sub_actions(r.id, serial, request, 0, actions).1;
                    assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is SubSend) by {
                        if k < o.len() {
                            assert(out[k] == o[k]);
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// The theorems.
// ---------------------------------------------------------------------

/// **`theorem_subfetch_only_to_requester`.**
pub proof fn theorem_subfetch_only_to_requester(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        crate::statements::subfetch_only_to_requester_statement(rules, urls, fetch, s, e),
{
    let out = step(rules, urls, fetch, s, e).1;
    match e {
        Event::SubNet { renderer, serial, hop, input } => {
            lemma_subnet_key_facts(s, renderer, serial);
            if let Some(f) = subnet_target(s, renderer, serial) {
                if subfetch_live(s, f) && hop != 0 && f.hop == hop {
                    let (fsa, actions, ops) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, subfetch_jar(fetch, s, f), s.now);
                    let (h, o, end) = sub_actions(renderer, serial, f.request, hop, actions);
                    crate::subfetch_rel::lemma_sub_actions_outputs(renderer, serial, f.request, hop, actions);
                    lemma_sub_actions_end(renderer, serial, f.request, hop, actions);
                    assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies {
                        &&& out[k]->ToRenderer_id == renderer
                        &&& subfetch_live(s, f)
                        &&& (out[k]->ToRenderer_bytes == style_failed_frame(f.request) || exists|doc: Document|
                            out[k]->ToRenderer_bytes == #[trigger] style_frames(f.request, doc))
                    } by {
                        if k < o.len() {
                            assert(out[k] == o[k]);
                        }
                    }
                }
            }
        },
        Event::Tick { time } => {
            crate::subfetch_rel::lemma_tick_all_shape(s, time);
            assert forall|k: int| 0 <= k < out.len() && (#[trigger] out[k]) is ToRenderer implies exists|j: int|
                0 <= j < s.subfetches.len() && s.subfetches[j].renderer == out[k]->ToRenderer_id && subfetch_live(tick(s, time).0, s.subfetches[j])
                    && out[k]->ToRenderer_bytes == style_failed_frame(s.subfetches[j].request) by {
                match out[k] {
                    Output::ToRenderer { .. } => {},
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

/// [`theorem_subfetch_credentials`] for a `SubNet`.
#[verifier::spinoff_prover]
pub proof fn lemma_credentials_subnet(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, renderer: nat, serial: nat, hop: nat, input: NetInput)
    ensures
        crate::statements::subfetch_credentials_statement(rules, urls, fetch, s, Event::SubNet { renderer, serial, hop, input }),
{
    let e = Event::SubNet { renderer, serial, hop, input };
    let out = step(rules, urls, fetch, s, e).1;
        lemma_subnet_key_facts(s, renderer, serial);
        if let Some(f) = subnet_target(s, renderer, serial) {
            if subfetch_live(s, f) && hop != 0 && f.hop == hop {
                let jar = subfetch_jar(fetch, s, f);
                let (fsa, actions, ops) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, jar, s.now);
                let (h, o, end) = sub_actions(renderer, serial, f.request, hop, actions);
                clazel_fetch::transducer::theorems::lemma_sends_only_on_connected(fetch.http, fetch.urls, f.fetch, input, jar, s.now);
                clazel_fetch::transducer::theorems::theorem_wire_cookies(fetch.http, fetch.urls, f.fetch, input, jar, s.now);
                if clazel_fetch::transducer::theorems::no_sends(actions) {
                    lemma_sub_actions_no_send(renderer, serial, f.request, hop, actions);
                    assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is SubSend) by {
                        if k < o.len() {
                            assert(out[k] == o[k]);
                        }
                    }
                } else {
                    let bytes = actions[0]->Send_0;
                    assert(actions == seq![clazel_fetch::transducer::spec::Action::Send(bytes)]);
                    assert(actions.drop_first() =~= Seq::<NetAction>::empty());
                    assert(sub_actions(renderer, serial, f.request, hop, Seq::<NetAction>::empty()) == (hop, Seq::<Output>::empty(), None::<Seq<u8>>));
                    assert(seq![Output::SubSend { renderer, serial, hop, bytes }] + Seq::<Output>::empty() =~= seq![Output::SubSend { renderer, serial, hop, bytes }]);
                    assert(o == seq![Output::SubSend { renderer, serial, hop, bytes }]);
                    assert(end is None);
                    assert(out == o);
                }
            }
        }
}

/// **`theorem_subfetch_credentials`** (5.0(h), with item 3.6's
/// `theorem_wire_cookies` carried through).
pub proof fn theorem_subfetch_credentials(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    ensures
        crate::statements::subfetch_credentials_statement(rules, urls, fetch, s, e),
{
    let out = step(rules, urls, fetch, s, e).1;
    if is_fetch_style(s, e) {
        let i = find_by_id(s.renderers, e->FromRenderer_id, 0)->Some_0;
        let r = s.renderers[i];
        let m = accepted_message(r, e->FromRenderer_bytes)->Some_0;
        assert(out == fetch_style(rules, urls, fetch, s, r, m->FetchStyle_request, m->FetchStyle_url).1);
        lemma_fetch_style_no_send(rules, urls, fetch, s, r, m->FetchStyle_request, m->FetchStyle_url);
    } else {
        match e {
            Event::SubNet { renderer, serial, hop, input } => {
                lemma_credentials_subnet(rules, urls, fetch, s, renderer, serial, hop, input);
            },
            Event::Tick { time } => {
                crate::subfetch_rel::lemma_tick_all_shape(s, time);
                assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is SubSend) by {
                    match out[k] {
                        Output::SubSend { .. } => {},
                        _ => {},
                    }
                }
            },
            _ => {
                lemma_step_tables(rules, urls, fetch, s, e);
            },
        }
    }
}

/// **`theorem_connection_ownership`, the second half** (item 5.19): see
/// [`crate::statements::subfetch_ownership_statement`].
pub proof fn theorem_subfetch_ownership(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::subfetch_ownership_statement(rules, urls, fetch, s, e),
{
    lemma_reachable_tables_wf(rules, urls, fetch, s);
    if is_fetch_style(s, e) {
        lemma_ownership_fetch_style(rules, urls, fetch, s, e);
    } else {
        lemma_ownership_other(rules, urls, fetch, s, e);
    }
}

/// [`theorem_subfetch_ownership`] for an accepted `FetchStyle`.
#[verifier::spinoff_prover]
pub proof fn lemma_ownership_fetch_style(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        subfetch_tables_wf(s),
        is_fetch_style(s, e),
    ensures
        crate::statements::subfetch_ownership_statement(rules, urls, fetch, s, e),
{
    let (s1, out) = step(rules, urls, fetch, s, e);
    let id = e->FromRenderer_id;
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    let i = find_by_id(s.renderers, id, 0)->Some_0;
    let r = s.renderers[i];
    let m = accepted_message(r, e->FromRenderer_bytes)->Some_0;
    let request = m->FetchStyle_request;
    let url = m->FetchStyle_url;
    assert((s1, out) == fetch_style(rules, urls, fetch, s, r, request, url));
    crate::subfetch_rel::lemma_fetch_style_shape(rules, urls, fetch, s, r, request, url);
    lemma_fetch_style_tables(rules, urls, fetch, s, r, request, url, r.id, r.lock);
    assert forall|k: int| 0 <= k < out.len() && ((#[trigger] out[k]) is SubConnect || out[k] is SubSend || out[k] is SubClose) implies crate::domain::output_id(out[k]) == id by {
        match out[k] {
            Output::SubConnect { .. } => {},
            Output::SubSend { .. } => {},
            Output::SubClose { .. } => {},
            _ => {},
        }
    }
    let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
    assert forall|j: int| 0 <= j < s1.subfetches.len() implies match subfetch_of(
        s.subfetches,
        (#[trigger] s1.subfetches[j]).renderer,
        s1.subfetches[j].lock,
        s1.subfetches[j].serial,
    ) {
        Some(f) => s1.subfetches[j].tab == f.tab && s1.subfetches[j].partition == f.partition,
        None => e matches Event::FromRenderer { id, .. } && s1.subfetches[j].renderer == id && exists|i: int|
            0 <= i < s.renderers.len() && s.renderers[i].id == id && s1.subfetches[j].lock == s.renderers[i].lock && s1.subfetches[j].tab
                == s.renderers[i].tab && s1.subfetches[j].partition == crate::domain::domain_of_renderer(rules, s.renderers[i]),
    } by {
        if j < s.subfetches.len() {
            assert(s1.subfetches[j] == s.subfetches[j]);
            lemma_unique_of(s.subfetches, j);
        } else {
            let n = choose|n: SubFetch|
                #![trigger s.subfetches.push(n)]
                s1.subfetches == s.subfetches.push(n) && n.renderer == r.id && n.lock == r.lock && n.serial == serial && n.tab == r.tab && n.partition
                    == crate::domain::domain_of_renderer(rules, r) && !n.ended;
            assert(s1.subfetches[j] == n);
            lemma_of_none(s.subfetches, n.renderer, n.lock, n.serial);
            assert forall|q: int| 0 <= q < s.subfetches.len() implies !subfetch_is(#[trigger] s.subfetches[q], n.renderer, n.lock, n.serial) by {
                assert(s.subfetches[q].serial < subcount_of(s.subcounts, s.subfetches[q].renderer, s.subfetches[q].lock).0);
            }
        }
    }
}

/// [`theorem_subfetch_ownership`] for every other event.
#[verifier::spinoff_prover]
pub proof fn lemma_ownership_other(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        subfetch_tables_wf(s),
        !is_fetch_style(s, e),
    ensures
        crate::statements::subfetch_ownership_statement(rules, urls, fetch, s, e),
{
    let (s1, out) = step(rules, urls, fetch, s, e);
    match e {
        Event::SubNet { renderer, serial, hop, input } => {
            crate::subfetch_rel::lemma_sub_net_shape(rules, fetch, s, renderer, serial, hop, input);
            lemma_sub_net_tables(rules, fetch, s, renderer, serial, hop, input, 0, arbitrary_lock());
            assert forall|k: int| 0 <= k < out.len() && ((#[trigger] out[k]) is SubConnect || out[k] is SubSend || out[k] is SubClose) implies crate::domain::output_id(out[k]) == renderer by {
                match out[k] {
                    Output::SubConnect { .. } => {},
                    Output::SubSend { .. } => {},
                    Output::SubClose { .. } => {},
                    _ => {},
                }
            }
            assert forall|j: int| 0 <= j < s1.subfetches.len() implies owned_by_key(s.subfetches, #[trigger] s1.subfetches[j]) by {}
        },
        Event::Tick { time } => {
            crate::subfetch_rel::lemma_tick_all_shape(s, time);
            let t = tick(s, time).0;
            lemma_sweep_table(t, s.subfetches, 0, arbitrary_lock());
            assert forall|k: int| 0 <= k < out.len() && ((#[trigger] out[k]) is SubConnect || out[k] is SubSend || out[k] is SubClose) implies exists|j: int|
                0 <= j < s.subfetches.len() && s.subfetches[j].renderer == crate::domain::output_id(out[k]) by {
                match out[k] {
                    Output::SubClose { .. } => {},
                    _ => {},
                }
            }
            assert forall|j: int| 0 <= j < s1.subfetches.len() implies owned_by_key(s.subfetches, #[trigger] s1.subfetches[j]) by {
                lemma_unique_contains(s.subfetches, s1.subfetches[j]);
            }
        },
        _ => {
            lemma_step_tables(rules, urls, fetch, s, e);
            assert forall|j: int| 0 <= j < s1.subfetches.len() implies owned_by_key(s.subfetches, #[trigger] s1.subfetches[j]) by {
                lemma_unique_of(s.subfetches, j);
            }
        },
    }

}

/// **`theorem_subfetch_limits`.**
pub proof fn theorem_subfetch_limits(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    s: State,
    e: Event,
    id: nat,
    lock: clazel_origin::spec::Origin,
)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::subfetch_limits_statement(rules, urls, fetch, s, e, id, lock),
{
    lemma_reachable_tables_wf(rules, urls, fetch, s);
    let s1 = step(rules, urls, fetch, s, e).0;
    if is_fetch_style(s, e) {
        let i = find_by_id(s.renderers, e->FromRenderer_id, 0)->Some_0;
        let r = s.renderers[i];
        let m = accepted_message(r, e->FromRenderer_bytes)->Some_0;
        let request = m->FetchStyle_request;
        let url = m->FetchStyle_url;
        assert(s1 == fetch_style(rules, urls, fetch, s, r, request, url).0);
        lemma_fetch_style_tables(rules, urls, fetch, s, r, request, url, id, lock);
        if s1 != s {
            let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
            lemma_subcount_set(s.subcounts, r.id, r.lock, serial + 1, in_document + 1, id, lock);
            if s1.subfetches != s.subfetches {
                let n = choose|n: SubFetch|
                    #![trigger s.subfetches.push(n)]
                    s1.subfetches == s.subfetches.push(n) && n.renderer == r.id && n.lock == r.lock && n.serial == serial && n.tab == r.tab && n.partition
                        == crate::domain::domain_of_renderer(rules, r) && !n.ended;
                lemma_live_push(s.subfetches, n, id, lock);
            }
        }
    } else {
        match e {
            Event::SubNet { renderer, serial, hop, input } => {
                lemma_sub_net_tables(rules, fetch, s, renderer, serial, hop, input, id, lock);
            },
            Event::Tick { time } => {
                crate::subfetch_rel::lemma_tick_all_shape(s, time);
                lemma_sweep_table(tick(s, time).0, s.subfetches, id, lock);
            },
            _ => {
                lemma_step_tables(rules, urls, fetch, s, e);
                lemma_kept_live(s.subfetches, s1.subfetches, id, lock);
                lemma_kept_subcount(s.subcounts, s1.subcounts, id, lock);
            },
        }
    }
}

/// **`theorem_commit_ends_subfetches`.**
pub proof fn theorem_commit_ends_subfetches(urls: UrlFns, s: State, tab: nat, url: Seq<u32>, doc: Document)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
    ensures
        crate::statements::commit_ends_subfetches_statement(urls, s, tab, url, doc),
{
    let s1 = navigate_tab(urls, s, tab, url, doc).0;
    crate::invariant::lemma_find_by_tab(s.renderers, tab, 0);
    if let Some(i) = find_by_tab(s.renderers, tab, 0) {
        let old = s.renderers[i];
        if let Some(lock) = lock_of_url(urls, url, s.next_id) {
            if lock is Tuple && lock == old.lock {
                assert forall|j: int| 0 <= j < s1.subfetches.len() && (#[trigger] s1.subfetches[j]).renderer == old.id && s1.subfetches[j].lock == old.lock && s1 != s implies !subfetch_live(s1, s1.subfetches[j]) by {
                    assert(s1.subfetches[j].ended);
                }
            } else {
                assert forall|j: int| 0 <= j < s1.subfetches.len() && (#[trigger] s1.subfetches[j]).renderer == old.id && s1.subfetches[j].lock == old.lock && s1 != s implies !subfetch_live(s1, s1.subfetches[j]) by {
                    crate::invariant::lemma_find_by_id(s1.renderers, old.id, 0);
                    if let Some(k) = find_by_id(s1.renderers, old.id, 0) {
                        if k == i {
                            assert(s1.renderers[k].id == s.next_id);
                        } else {
                            assert(s1.renderers[k] == s.renderers[k]);
                            if k < i {
                                assert(s.renderers[k].id != s.renderers[i].id);
                            } else {
                                assert(s.renderers[i].id != s.renderers[k].id);
                            }
                        }
                    }
                }
            }
        }
    }
}

} // verus!

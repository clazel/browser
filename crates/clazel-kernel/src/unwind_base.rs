//! Small facts the unwinding lemmas of item 2.11 use: the renderer table as
//! a set, outputs addressed to a domain, and the preservation of "no
//! public-suffix domain in the jar".

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The renderer table as a set.
// ---------------------------------------------------------------------

/// A renderer in a well-formed table is at some index, and its id names that index.
pub proof fn lemma_contains_index(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, x: Renderer, i: int)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        rs.contains(x),
        0 <= i < rs.len(),
        rs[i].id == x.id,
    ensures
        rs[i] == x,
{
    let m = choose|m: int| 0 <= m < rs.len() && rs[m] == x;
    crate::lock::lemma_ids_distinct(urls, rs, next_id, m, i);
}

/// Removing index `i` keeps exactly the renderers whose id is not that of `i`.
pub proof fn lemma_remove_contains(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, i: int, x: Renderer)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        0 <= i < rs.len(),
    ensures
        rs.remove(i).contains(x) == (rs.contains(x) && x.id != rs[i].id),
{
    let r2 = rs.remove(i);
    if r2.contains(x) {
        let b = choose|b: int| 0 <= b < r2.len() && r2[b] == x;
        let m = if b < i { b } else { b + 1 };
        assert(r2[b] == rs[m]);
        assert(rs.contains(x));
        if x.id == rs[i].id {
            crate::lock::lemma_ids_distinct(urls, rs, next_id, m, i);
        }
    }
    if rs.contains(x) && x.id != rs[i].id {
        let m = choose|m: int| 0 <= m < rs.len() && rs[m] == x;
        let b = if m < i { m } else { m - 1 };
        assert(m != i);
        assert(r2[b] == rs[m]);
    }
}

/// Replacing index `i` by `r` leaves `r` and the renderers whose id is not that of `i`.
pub proof fn lemma_update_contains(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, i: int, r: Renderer, x: Renderer)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        0 <= i < rs.len(),
    ensures
        rs.update(i, r).contains(x) == (x == r || (rs.contains(x) && x.id != rs[i].id)),
{
    let r2 = rs.update(i, r);
    if r2.contains(x) {
        let b = choose|b: int| 0 <= b < r2.len() && r2[b] == x;
        if b != i {
            assert(r2[b] == rs[b]);
            assert(rs.contains(x));
            if x.id == rs[i].id {
                crate::lock::lemma_ids_distinct(urls, rs, next_id, b, i);
            }
        } else {
            assert(x == r);
        }
    }
    if x == r {
        assert(r2[i] == r);
    }
    if rs.contains(x) && x.id != rs[i].id {
        let m = choose|m: int| 0 <= m < rs.len() && rs[m] == x;
        assert(m != i);
        assert(r2[m] == rs[m]);
    }
}

/// Pushing `r` leaves `r` and the old renderers.
pub proof fn lemma_push_contains(rs: Seq<Renderer>, r: Renderer, x: Renderer)
    ensures
        rs.push(r).contains(x) == (x == r || rs.contains(x)),
{
    if rs.push(r).contains(x) {
        let b = choose|b: int| 0 <= b < rs.push(r).len() && rs.push(r)[b] == x;
        if b < rs.len() {
            assert(rs[b] == x);
        }
    }
    if x == r {
        assert(rs.push(r)[rs.len() as int] == r);
    }
    if rs.contains(x) {
        let m = choose|m: int| 0 <= m < rs.len() && rs[m] == x;
        assert(rs.push(r)[m] == x);
    }
}

/// Two renderers of a well-formed table with the same id are equal.
pub proof fn lemma_same_id_same_renderer(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, x: Renderer, y: Renderer)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        rs.contains(x),
        rs.contains(y),
        x.id == y.id,
    ensures
        x == y,
{
    let i = choose|i: int| 0 <= i < rs.len() && rs[i] == x;
    lemma_contains_index(urls, rs, next_id, y, i);
}

/// Two renderers of a well-formed table with the same tab are equal.
pub proof fn lemma_same_tab_same_renderer(urls: UrlFns, rs: Seq<Renderer>, next_id: nat, x: Renderer, y: Renderer)
    requires
        crate::invariant::renderers_wf(urls, rs, next_id),
        rs.contains(x),
        rs.contains(y),
        x.tab == y.tab,
    ensures
        x == y,
{
    let i = choose|i: int| 0 <= i < rs.len() && rs[i] == x;
    let j = choose|j: int| 0 <= j < rs.len() && rs[j] == y;
    if i < j {
        assert(rs[i].tab != rs[j].tab);
    } else if j < i {
        assert(rs[j].tab != rs[i].tab);
    }
}

/// A renderer of the table is found by its id, at an index holding it.
pub proof fn lemma_find_contained(urls: UrlFns, s: State, x: Renderer)
    requires
        crate::invariant::renderers_wf(urls, s.renderers, s.next_id),
        s.renderers.contains(x),
    ensures
        find_by_id(s.renderers, x.id, 0) is Some,
        s.renderers[find_by_id(s.renderers, x.id, 0)->Some_0] == x,
        find_by_tab(s.renderers, x.tab, 0) is Some,
        s.renderers[find_by_tab(s.renderers, x.tab, 0)->Some_0] == x,
{
    crate::invariant::lemma_find_by_id(s.renderers, x.id, 0);
    crate::invariant::lemma_find_by_tab(s.renderers, x.tab, 0);
    let m = choose|m: int| 0 <= m < s.renderers.len() && s.renderers[m] == x;
    match find_by_id(s.renderers, x.id, 0) {
        Some(k) => {
            lemma_contains_index(urls, s.renderers, s.next_id, x, k);
        },
        None => {
            assert(s.renderers[m].id == x.id);
        },
    }
    match find_by_tab(s.renderers, x.tab, 0) {
        Some(k) => {
            assert(s.renderers.contains(s.renderers[k]));
            lemma_same_tab_same_renderer(urls, s.renderers, s.next_id, s.renderers[k], x);
        },
        None => {
            assert(s.renderers[m].tab == x.tab);
        },
    }
}

/// The renderer found by id is contained.
pub proof fn lemma_found_contained(s: State, id: nat)
    ensures
        find_by_id(s.renderers, id, 0) matches Some(i) ==> (0 <= i < s.renderers.len() && s.renderers[i].id == id && s.renderers.contains(s.renderers[i])),
        find_by_tab(s.renderers, id, 0) matches Some(i) ==> (0 <= i < s.renderers.len() && s.renderers[i].tab == id && s.renderers.contains(s.renderers[i])),
{
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    crate::invariant::lemma_find_by_tab(s.renderers, id, 0);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        assert(s.renderers.contains(s.renderers[i]));
    }
    if let Some(i) = find_by_tab(s.renderers, id, 0) {
        assert(s.renderers.contains(s.renderers[i]));
    }
}

// ---------------------------------------------------------------------
// Filters by pointwise equal predicates.
// ---------------------------------------------------------------------

/// Filtering by predicates that agree on the elements gives the same result.
pub proof fn lemma_filter_pointwise<A>(s: Seq<A>, p: spec_fn(A) -> bool, q: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() ==> p(#[trigger] s[i]) == q(s[i]),
    ensures
        s.filter(p) == s.filter(q),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies p(#[trigger] t[i]) == q(t[i]) by {
            assert(s[i] == t[i]);
        }
        lemma_filter_pointwise(t, p, q);
        assert(s[s.len() - 1] == s.last());
    }
}

/// Filtering by a predicate that rejects every element gives the empty sequence.
pub proof fn lemma_filter_none<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() ==> !p(#[trigger] s[i]),
    ensures
        s.filter(p) == Seq::<A>::empty(),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies !p(#[trigger] t[i]) by {
            assert(s[i] == t[i]);
        }
        lemma_filter_none(t, p);
        assert(s[s.len() - 1] == s.last());
    }
}

// ---------------------------------------------------------------------
// Outputs addressed to a domain.
// ---------------------------------------------------------------------

/// The renderers of domain `d` are the same in two related states, so an
/// output is addressed to `d` in one step exactly when it is in the other.
pub proof fn lemma_addressed_same(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    s1b: State,
    s2b: State,
    o: Output,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::rel(rules, urls, d, s1b, s2b),
    ensures
        crate::noninterference::addressed_to(rules, d, s1, s1b, o) == crate::noninterference::addressed_to(rules, d, s2, s2b, o),
{
    if crate::noninterference::addressed_to(rules, d, s1, s1b, o) {
        let r = choose|r: Renderer| (s1.renderers.contains(r) || s1b.renderers.contains(r)) && r.id == crate::domain::output_id(o) && crate::domain::domain_of_renderer(rules, r) == d;
        if s1.renderers.contains(r) {
            let i = choose|i: int| 0 <= i < s1.renderers.len() && s1.renderers[i] == r;
            assert(s2.renderers.contains(r));
        } else {
            let i = choose|i: int| 0 <= i < s1b.renderers.len() && s1b.renderers[i] == r;
            assert(s2b.renderers.contains(r));
        }
    }
    if crate::noninterference::addressed_to(rules, d, s2, s2b, o) {
        let r = choose|r: Renderer| (s2.renderers.contains(r) || s2b.renderers.contains(r)) && r.id == crate::domain::output_id(o) && crate::domain::domain_of_renderer(rules, r) == d;
        if s2.renderers.contains(r) {
            let i = choose|i: int| 0 <= i < s2.renderers.len() && s2.renderers[i] == r;
            assert(s1.renderers.contains(s2.renderers[i]));
        } else {
            let i = choose|i: int| 0 <= i < s2b.renderers.len() && s2b.renderers[i] == r;
            assert(s1b.renderers.contains(s2b.renderers[i]));
        }
    }
}

/// Equal outputs of related steps are addressed to `d` alike.
pub proof fn lemma_outputs_for_same(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    s1b: State,
    s2b: State,
    out: Seq<Output>,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::noninterference::rel(rules, urls, d, s1b, s2b),
    ensures
        crate::noninterference::outputs_for(rules, d, s1, s1b, out) == crate::noninterference::outputs_for(rules, d, s2, s2b, out),
{
    assert forall|i: int| 0 <= i < out.len() implies (|o: Output| crate::noninterference::addressed_to(rules, d, s1, s1b, o))(#[trigger] out[i]) == (|o: Output| crate::noninterference::addressed_to(
        rules,
        d,
        s2,
        s2b,
        o,
    ))(out[i]) by {
        lemma_addressed_same(rules, urls, d, s1, s2, s1b, s2b, out[i]);
    }
    lemma_filter_pointwise(out, |o: Output| crate::noninterference::addressed_to(rules, d, s1, s1b, o), |o: Output| crate::noninterference::addressed_to(rules, d, s2, s2b, o));
}

// ---------------------------------------------------------------------
// No public-suffix domain in the jar.
// ---------------------------------------------------------------------

/// The domain of a cookie that storage creates for a request host that is not
/// a public suffix is not one either.
pub proof fn lemma_new_cookie_domain(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    received: clazel_cookie::set_cookie::spec::SetCookie,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    new: clazel_cookie::storage::spec::Cookie,
)
    requires
        url.host == Some(host),
        host.name.len() > 0,
        host.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, host.name),
        clazel_cookie::storage::spec::create_a_cookie(rules, jar, url, ctx, received, now) == Some(new),
    ensures
        new.domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, new.domain.name),
{
    let domain_attribute = match clazel_cookie::storage::spec::last_domain_within_1024(received.attributes) {
        Some(d) => d,
        None => seq![],
    };
    let r9 = clazel_cookie::storage::spec::step_9_domain_attribute(rules, host, domain_attribute);
    assert(r9 is Some);
    let da = r9->Some_0;
    let r10 = clazel_cookie::storage::spec::step_10_domain(host, da);
    assert(r10 is Some);
    let (domain, host_only) = r10->Some_0;
    assert(new.domain == domain);
    clazel_cookie::storage::isolation::lemma_step_9_10_domain(rules, host, domain_attribute, da, domain, host_only);
}

/// Storage with a request host that is not a public suffix keeps the jar
/// free of public-suffix domains.
pub proof fn lemma_store_no_public_suffix(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    s: Seq<u8>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        host.name.len() > 0,
        host.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, host.name),
        crate::invariant::jar_no_public_suffix(rules, jar),
    ensures
        crate::invariant::jar_no_public_suffix(rules, clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, s, url, ctx, now)),
{
    let live = clazel_cookie::storage::spec::evict_expired(jar, now);
    let any_root = clazel_cookie::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, jar, now, any_root);
    assert forall|i: int| 0 <= i < live.len() implies (#[trigger] live[i]).domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, live[i].domain.name) by {
        assert(live.contains(live[i]));
        assert(jar.contains(live[i]));
        let k = choose|k: int| 0 <= k < jar.len() && jar[k] == live[i];
    }
    if let Some(received) = clazel_cookie::set_cookie::spec::parse_a_set_cookie_string(s, url.path, now) {
        if let Some(new) = clazel_cookie::storage::spec::create_a_cookie(rules, live, url, ctx, received, now) {
            lemma_new_cookie_domain(rules, live, url, ctx, received, now, host, new);
            let ins = clazel_cookie::storage::spec::insert_a_cookie(live, new);
            let e = clazel_cookie::storage::spec::evict_expired(ins, now);
            let z = clazel_cookie::storage::spec::evict_over_limit(rules, e, clazel_cookie::storage::spec::cookie_root_of(rules, new));
            clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, ins, now, any_root);
            clazel_cookie::storage::isolation::lemma_evict_over_limit_props(rules, e, clazel_cookie::storage::spec::cookie_root_of(rules, new));
            assert forall|i: int| 0 <= i < z.len() implies (#[trigger] z[i]).domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, z[i].domain.name) by {
                assert(z.contains(z[i]));
                assert(e.contains(z[i]));
                assert(ins.contains(z[i]));
                lemma_insert_contains(live, new, z[i]);
            }
        }
    }
}

/// A cookie of `insert_a_cookie(jar, new)` is `new` or was in `jar`.
pub proof fn lemma_insert_contains(jar: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, x: clazel_cookie::storage::spec::Cookie)
    requires
        clazel_cookie::storage::spec::insert_a_cookie(jar, new).contains(x),
    ensures
        x == new || jar.contains(x),
{
    let ins = clazel_cookie::storage::spec::insert_a_cookie(jar, new);
    let k = choose|k: int| 0 <= k < ins.len() && ins[k] == x;
    match clazel_cookie::storage::spec::find_old_cookie(jar, new) {
        Some(i) => {
            clazel_cookie::storage::lemmas::lemma_find_old_cookie_from(jar, new, 0);
            jar.remove_ensures(i);
            let wo = jar.remove(i);
            if k < wo.len() {
                assert(wo[k] == x);
                assert(wo.contains(x));
                let m = if k < i { k } else { k + 1 };
                assert(jar[m] == x);
            }
        },
        None => {
            if k < jar.len() {
                assert(jar[k] == x);
            }
        },
    }
}

/// `navigate_tab` and `begin_navigation` leave the jar, storage and time alone.
///
/// Stage 2 of the join writes this proof.
pub proof fn lemma_navigation_frame(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, tab: nat, url: Seq<u32>, script: Seq<u8>)
    ensures
        navigate_tab(urls, s, tab, url, script).0.jar == s.jar,
        navigate_tab(urls, s, tab, url, script).0.storage == s.storage,
        navigate_tab(urls, s, tab, url, script).0.now == s.now,
        begin_navigation(rules, urls, fetch, s, tab, url).0.jar == s.jar,
        begin_navigation(rules, urls, fetch, s, tab, url).0.storage == s.storage,
        begin_navigation(rules, urls, fetch, s, tab, url).0.now == s.now,
        begin_navigation(rules, urls, fetch, s, tab, url).0.next_id == s.next_id,
{
}

/// What a `Net` changes of the state besides the renderers and connections:
/// the jar takes the jar operations of the transducer's step if the event is
/// about an open connection, and nothing else (storage, time, the id counter)
/// changes.
///
/// Stage 2 of the join writes this proof.
pub proof fn lemma_net_frame(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, conn: nat, input: NetInput)
    ensures
        net(rules, urls, fetch, s, conn, input).0.jar == (match net_target(s, conn) {
            Some((_, _, nav)) => apply_net_ops(rules, s.jar, net_transducer_step(fetch, s, nav, input).2),
            None => s.jar,
        }),
        net(rules, urls, fetch, s, conn, input).0.storage == s.storage,
        net(rules, urls, fetch, s, conn, input).0.now == s.now,
{
}

/// Every step keeps the jar free of public-suffix domains, from a state
/// with no renderer on a public-suffix host.
pub proof fn lemma_jar_no_public_suffix_step(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        crate::invariant::jar_no_public_suffix(rules, step(rules, urls, fetch, s, e).0.jar),
{
    let any_root = clazel_cookie::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    match e {
        Event::Tick { time } => {
            let now = if time > s.now { time } else { s.now };
            let live = clazel_cookie::storage::spec::evict_expired(s.jar, now);
            clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, s.jar, now, any_root);
            assert forall|i: int| 0 <= i < live.len() implies (#[trigger] live[i]).domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, live[i].domain.name) by {
                assert(live.contains(live[i]));
                assert(s.jar.contains(live[i]));
                let k = choose|k: int| 0 <= k < s.jar.len() && s.jar[k] == live[i];
            }
        },
        Event::FromRenderer { id, bytes } => {
            crate::invariant::lemma_find_by_id(s.renderers, id, 0);
            if let Some(i) = find_by_id(s.renderers, id, 0) {
                let r = s.renderers[i];
                if let Some(m) = decode_renderer_frame(bytes) {
                    crate::lock::lemma_storage_call_frame(s, r, m);
                    match m {
                        clazel_ipc::message::spec::Message::CookieGet => {
                            if !cookie_averse(rules, r.lock) {
                                let url = request_url_of(urls, r);
                                let live = clazel_cookie::storage::spec::evict_expired(s.jar, s.now);
                                let host = lock_host(r.lock);
                                assert(url.host == host);
                                let f = |c: clazel_cookie::storage::spec::Cookie| c;
                                // The retrieval maps only the last-access-time.
                                if let Some(h) = url.host {
                                    let mapped = clazel_cookie::storage::spec::jar_after_retrieval(rules, s.jar, url, document_context(r.lock), s.now);
                                    clazel_cookie::storage::isolation::lemma_evict_expired_props(rules, s.jar, s.now, any_root);
                                    assert forall|k: int| 0 <= k < mapped.len() implies (#[trigger] mapped[k]).domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(
                                        rules,
                                        mapped[k].domain.name,
                                    ) by {
                                        let g = clazel_cookie::storage::spec::update_last_access_time(rules, url, document_context(r.lock), h, s.now);
                                        assert(mapped[k] == g(live[k]));
                                        assert(live.contains(live[k]));
                                        assert(s.jar.contains(live[k]));
                                        let q = choose|q: int| 0 <= q < s.jar.len() && s.jar[q] == live[k];
                                        if clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, document_context(r.lock), h, live[k]) {
                                            assert(g(live[k]) == clazel_cookie::storage::spec::with_last_access_time(live[k], s.now));
                                        } else {
                                            assert(g(live[k]) == live[k]);
                                        }
                                    }
                                }
                            }
                        },
                        clazel_ipc::message::spec::Message::CookieSet { cookie_string } => {
                            if !cookie_averse(rules, r.lock) {
                                crate::cookie_theorems::lemma_tuple_lock_host(urls, s.renderers, s.next_id, i);
                                crate::invariant::lemma_request_url_host_nonempty(rules, urls, r);
                                let url = request_url_of(urls, r);
                                let h = lock_host(r.lock)->Some_0;
                                // A document on a public-suffix host is cookie-averse.
                                assert(h.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, h.name));
                                lemma_store_no_public_suffix(rules, s.jar, cookie_string, url, document_context(r.lock), s.now, h);
                            }
                        },
                        clazel_ipc::message::spec::Message::Navigate { url } => {
                            if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                                if let Some(resolved) = (urls.resolve)(r.url, relative) {
                                    if lock_of_url(urls, resolved, s.next_id) is Some {
                                        lemma_navigation_frame(rules, urls, fetch, s, r.tab, resolved, seq![]);
                                    }
                                }
                            }
                        },
                        _ => {},
                    }
                }
            }
        },
        Event::Net { conn, input } => {
            lemma_net_frame(rules, urls, fetch, s, conn, input);
            if let Some((_, _, nav)) = net_target(s, conn) {
                crate::invariant::lemma_apply_net_ops_wf(rules, s.jar, net_transducer_step(fetch, s, nav, input).2);
            }
        },
        _ => {},
    }
}

} // verus!

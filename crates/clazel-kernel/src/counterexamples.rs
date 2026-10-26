//! Counterexamples (item 2.11): the statements of the plan that the proof
//! found false, each shown in Verus, and the narrowest correction that
//! `noninterference.rs` and `statements.rs` state instead.
//!
//! 1. [`example_dead_tab_breaks_noninterference`]: without `user_tabs_open`,
//!    `theorem_cookie_noninterference` is false. A renderer of one domain
//!    that sends a frame the kernel cannot decode is killed and its tab is
//!    closed; the purge drops that frame, so in the purged run the tab is
//!    still open, and a later `Fetched` for that tab (the fetch of a
//!    navigation the user made while the tab was open) commits a document in
//!    the observer's domain, which the first run does not. (Before item 3.7 a
//!    later `NavigateTab` of the user to the closed tab did the same: a
//!    navigation committed at once. A `NavigateTab` to a closed tab no longer
//!    shows anything to the observer, since it only starts a fetch, so it is
//!    the `Fetched` clause of `user_tabs_open` the example shows necessary;
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

/// The fetch under which the counterexample runs: it answers with the URL it
/// was started for and the octets delivered as the body, and sets no cookie.
pub open spec fn ce_fetch() -> FetchFns {
    FetchFns { run: |u: Seq<u32>, n: Seq<u8>| FetchRun { result: FetchResult::Done { url: u, body: n }, stores: Seq::<HttpStore>::empty() } }
}

/// Open a tab, navigate it (the user types a URL; the kernel asks for the
/// fetch), have its renderer send an undecodable frame (empty), then report
/// the fetch of the tab, which is closed by then.
pub open spec fn ce_trace() -> Seq<Event> {
    seq![
        Event::OpenTab { url: Seq::<u32>::empty(), script: Seq::<u8>::empty() },
        Event::NavigateTab { tab: 0, url: Seq::<u32>::empty() },
        Event::FromRenderer { id: 0, bytes: Seq::<u8>::empty() },
        Event::Fetched { tab: 0, outcome: NetOutcome { url: Seq::<u32>::empty(), net: Seq::<u8>::empty() } },
    ]
}

/// The renderer after the first event of [`ce_trace`].
pub open spec fn ce_renderer0() -> Renderer {
    Renderer { id: 0, tab: 0, url: Seq::<u32>::empty(), lock: clazel_origin::spec::Origin::Opaque(0nat), pending: None }
}

/// **Counterexample 1.** For the observer `Opaque(1)` (the renderer the
/// purged run spawns): every `NavigateTab` of the trace names an open tab, but
/// its `Fetched` names a closed one, and the outputs to the observer differ
/// between the trace and its purge. (In the trace the renderer's undecodable
/// frame closes the tab, so the fetch is ignored; the purge drops that frame,
/// so the tab is still open when the fetch is reported, and it commits into
/// the observer's domain.)
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
    let urls = ce_urls();
    let fetch = ce_fetch();
    let t = ce_trace();
    let d = crate::domain::Domain::Opaque(1nat);
    let e0 = t[0];
    let e1 = t[1];
    let e2 = t[2];
    let e3 = t[3];
    let s0 = init_state();
    let r0 = ce_renderer0();
    let empty_u: Seq<u32> = Seq::<u32>::empty();
    assert(lock_of_url(urls, empty_u, 0) == Some(clazel_origin::spec::Origin::Opaque(0nat)));
    assert(lock_of_url(urls, empty_u, 1) == Some(clazel_origin::spec::Origin::Opaque(1nat)));
    let (s1, o0) = step(rules, urls, fetch, s0, e0);
    assert(s1.renderers =~= seq![r0]);
    assert(s1.next_id == 1);
    assert(find_by_tab(s1.renderers, 0, 0) == Some(0int));
    let (s2, o1) = step(rules, urls, fetch, s1, e1);
    let r0p = Renderer { pending: Some(empty_u), ..r0 };
    assert(s2.renderers =~= seq![r0p]);
    assert(o1 =~= seq![Output::Fetch { tab: 0, url: empty_u }]);
    assert(decode_renderer_frame(Seq::<u8>::empty()) is None);
    assert(find_by_id(s2.renderers, 0, 0) == Some(0int));
    let (s3, o2) = step(rules, urls, fetch, s2, e2);
    assert(s3.renderers =~= Seq::<Renderer>::empty());
    assert(o2 =~= seq![Output::Kill { id: 0 }]);
    assert(find_by_tab(s3.renderers, 0, 0) is None);
    let (s4, o3) = step(rules, urls, fetch, s3, e3);
    assert(s4 == s3 && o3 =~= Seq::<Output>::empty());
    // The trace is not one the shell reports: the last event names a closed tab.
    let t1 = t.drop_first();
    let t2 = t1.drop_first();
    let t3 = t2.drop_first();
    let t4 = t3.drop_first();
    assert(t1 =~= seq![e1, e2, e3]);
    assert(t2 =~= seq![e2, e3]);
    assert(t3 =~= seq![e3]);
    assert(t4 =~= Seq::<Event>::empty());
    assert(step(rules, urls, fetch, s0, t[0]).0 == s1);
    assert(step(rules, urls, fetch, s1, t1[0]).0 == s2);
    assert(step(rules, urls, fetch, s2, t2[0]).0 == s3);
    assert(step(rules, urls, fetch, s3, t3[0]).0 == s4);
    assert(!crate::noninterference::user_tabs_open(rules, urls, fetch, s0, t)) by {
        reveal_with_fuel(crate::noninterference::user_tabs_open, 5);
    }
    // The original run sends nothing to d: its only renderer is Opaque(0).
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s0, e0, seq![e1, e2, e3]);
    assert(seq![e1, e2, e3] =~= seq![e1] + seq![e2, e3]);
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s1, e1, seq![e2, e3]);
    assert(seq![e2, e3] =~= seq![e2] + seq![e3]);
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s2, e2, seq![e3]);
    assert(seq![e3] =~= seq![e3] + Seq::<Event>::empty());
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s3, e3, Seq::<Event>::empty());
    reveal(Seq::filter);
    assert(crate::domain::domain_of_renderer(rules, r0) == crate::domain::Domain::Opaque(0nat));
    assert(crate::domain::domain_of_renderer(rules, r0p) == crate::domain::Domain::Opaque(0nat));
    assert forall|k: int| 0 <= k < o0.len() implies !crate::noninterference::addressed_to(rules, d, s0, s1, #[trigger] o0[k]) by {
        if crate::noninterference::addressed_to(rules, d, s0, s1, o0[k]) {
            let q = choose|q: Renderer| (s0.renderers.contains(q) || s1.renderers.contains(q)) && q.id == crate::domain::output_id(o0[k]) && crate::domain::domain_of_renderer(rules, q) == d;
            assert(s1.renderers.contains(q));
            assert(q == r0);
        }
    }
    crate::unwind_base::lemma_filter_none(o0, |o: Output| crate::noninterference::addressed_to(rules, d, s0, s1, o));
    assert forall|k: int| 0 <= k < o1.len() implies !crate::noninterference::addressed_to(rules, d, s1, s2, #[trigger] o1[k]) by {}
    crate::unwind_base::lemma_filter_none(o1, |o: Output| crate::noninterference::addressed_to(rules, d, s1, s2, o));
    assert forall|k: int| 0 <= k < o2.len() implies !crate::noninterference::addressed_to(rules, d, s2, s3, #[trigger] o2[k]) by {
        if crate::noninterference::addressed_to(rules, d, s2, s3, o2[k]) {
            let q = choose|q: Renderer| (s2.renderers.contains(q) || s3.renderers.contains(q)) && q.id == crate::domain::output_id(o2[k]) && crate::domain::domain_of_renderer(rules, q) == d;
            assert(s2.renderers.contains(q));
            assert(q == r0p);
        }
    }
    crate::unwind_base::lemma_filter_none(o2, |o: Output| crate::noninterference::addressed_to(rules, d, s2, s3, o));
    assert(crate::noninterference::run_outputs_for(rules, urls, fetch, d, s0, t) =~= Seq::<Output>::empty());
    // The purge drops the frame.
    assert(crate::domain::event_domain(rules, s2, e2) == Some(crate::domain::Domain::Opaque(0nat)));
    assert(crate::domain::declassified(urls, s2, e2) is None);
    assert(crate::domain::ipurge_event(rules, urls, s2, d, e2) is None);
    assert(crate::domain::ipurge_event(rules, urls, s0, d, e0) == Some(e0));
    assert(crate::domain::ipurge_event(rules, urls, s1, d, e1) == Some(e1));
    assert(crate::domain::ipurge_event(rules, urls, s3, d, e3) == Some(e3));
    let p = crate::domain::purge(rules, urls, fetch, d, t);
    assert(crate::domain::ipurge(rules, urls, fetch, s3, d, seq![e3]) =~= seq![e3]) by {
        assert(seq![e3].drop_first() =~= Seq::<Event>::empty());
        assert(seq![e3][0] == e3);
        assert(step(rules, urls, fetch, s3, e3).0 == s4);
        reveal_with_fuel(crate::domain::ipurge, 3);
    }
    assert(crate::domain::ipurge(rules, urls, fetch, s2, d, seq![e2, e3]) =~= seq![e3]) by {
        assert(seq![e2, e3].drop_first() =~= seq![e3]);
        assert(seq![e2, e3][0] == e2);
        reveal_with_fuel(crate::domain::ipurge, 3);
    }
    assert(crate::domain::ipurge(rules, urls, fetch, s1, d, seq![e1, e2, e3]) =~= seq![e1, e3]) by {
        assert(seq![e1, e2, e3].drop_first() =~= seq![e2, e3]);
        assert(seq![e1, e2, e3][0] == e1);
        reveal_with_fuel(crate::domain::ipurge, 3);
    }
    assert(p =~= seq![e0, e1, e3]) by {
        assert(t.drop_first() =~= seq![e1, e2, e3]);
        assert(t[0] == e0);
        reveal_with_fuel(crate::domain::ipurge, 3);
    }
    // The purged run: the renderer 0 is still there when the fetch is reported,
    // and commits into the observer's domain.
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s0, e0, seq![e1, e3]);
    assert(seq![e1, e3] =~= seq![e1] + seq![e3]);
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s1, e1, seq![e3]);
    let (s4p, o3p) = step(rules, urls, fetch, s2, e3);
    assert(find_by_tab(s2.renderers, 0, 0) == Some(0int));
    assert(fetched_run(fetch, s2, 0, NetOutcome { url: empty_u, net: Seq::<u8>::empty() }) is Some);
    assert(o3p.len() == 3 && o3p[1] == (Output::Spawn { id: 1, policy: Policy::Renderer }));
    let r1 = Renderer { id: 1, tab: 0, url: empty_u, lock: clazel_origin::spec::Origin::Opaque(1nat), pending: None };
    assert(s4p.renderers =~= seq![r1]);
    assert(crate::domain::domain_of_renderer(rules, r1) == d);
    assert(crate::noninterference::addressed_to(rules, d, s2, s4p, o3p[1])) by {
        assert(s4p.renderers[0] == r1);
        assert(s4p.renderers.contains(r1));
    }
    crate::ni_theorem::lemma_run_outputs_cons(rules, urls, fetch, d, s2, e3, Seq::<Event>::empty());
    assert(crate::noninterference::outputs_for(rules, d, s2, s4p, o3p).contains(o3p[1])) by {
        lemma_filter_contains_elem(o3p, |o: Output| crate::noninterference::addressed_to(rules, d, s2, s4p, o), 1);
    }
    assert(crate::noninterference::run_outputs_for(rules, urls, fetch, d, s0, p).len() > 0);
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

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

/// `HTTP/1.1 204 No Content` and an empty header section.
pub open spec fn ce_response() -> Seq<u8> {
    seq![0x48u8, 0x54, 0x54, 0x50, 0x2F, 0x31, 0x2E, 0x31, 0x20, 0x32, 0x30, 0x34, 0x20, 0x4E, 0x6F, 0x20, 0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x0D, 0x0A, 0x0D, 0x0A]
}

/// Open a tab, navigate it (the user types a URL; the kernel opens the
/// connection 0), have its renderer send an undecodable frame (empty), which
/// closes the tab and its connection, then report that connection open and
/// the response arriving.
pub open spec fn ce_trace() -> Seq<Event> {
    seq![
        Event::OpenTab { url: Seq::<u32>::empty(), script: Seq::<u8>::empty() },
        Event::NavigateTab { tab: 0, url: Seq::<u32>::empty() },
        Event::FromRenderer { id: 0, bytes: Seq::<u8>::empty() },
        Event::Net { conn: 0, input: clazel_fetch::transducer::spec::Input::Connected },
        Event::Net { conn: 0, input: clazel_fetch::transducer::spec::Input::Bytes(ce_response()) },
    ]
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
///
/// Stage 2 of the join writes this proof.
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

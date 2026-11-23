//! Item 7.16's URL updates (`UpdateUrl`, `pushState` and `replaceState`):
//! the facts about a domain's document URLs that the noninterference proof
//! needs (they mirror 5.18's titles, `surface_rel.rs`), the invariant
//! [`crate::invariant::doc_urls_wf`], and `theorem_url_update_same_origin`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The document URLs of a domain.
// ---------------------------------------------------------------------

/// Forgetting a document URL commutes with taking a domain's.
pub proof fn lemma_doc_urls_forget_commute(rules: Seq<clazel_psl::spec::Rule>, ds: Seq<DocUrl>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    ensures
        crate::domain::doc_urls_of_domain(rules, forget_doc_url(ds, id, lock), d) == forget_doc_url(crate::domain::doc_urls_of_domain(rules, ds, d), id, lock),
{
    crate::surface_rel::lemma_filter_commute(
        ds,
        |x: DocUrl| !(x.id == id && x.lock == lock),
        |x: DocUrl| crate::domain::domain_of_lock(rules, x.lock) == d,
    );
}

/// Forgetting a document URL under a lock of another domain does not change
/// the domain's.
pub proof fn lemma_doc_urls_forget_other(rules: Seq<clazel_psl::spec::Rule>, ds: Seq<DocUrl>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) != d,
    ensures
        crate::domain::doc_urls_of_domain(rules, forget_doc_url(ds, id, lock), d) == crate::domain::doc_urls_of_domain(rules, ds, d),
{
    lemma_doc_urls_forget_commute(rules, ds, id, lock, d);
    let dd = crate::domain::doc_urls_of_domain(rules, ds, d);
    let keep = |x: DocUrl| !(x.id == id && x.lock == lock);
    let ind = |x: DocUrl| crate::domain::domain_of_lock(rules, x.lock) == d;
    assert forall|i: int| 0 <= i < dd.len() implies keep(#[trigger] dd[i]) by {
        ds.lemma_filter_pred(ind, i);
    }
    crate::surface_rel::lemma_filter_all(dd, keep);
}

/// Setting a document URL under a lock of another domain does not change
/// the domain's.
pub proof fn lemma_doc_urls_set_other(rules: Seq<clazel_psl::spec::Rule>, ds: Seq<DocUrl>, id: nat, lock: clazel_origin::spec::Origin, url: Seq<u32>, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) != d,
    ensures
        crate::domain::doc_urls_of_domain(rules, set_doc_url(ds, id, lock, url), d) == crate::domain::doc_urls_of_domain(rules, ds, d),
{
    lemma_doc_urls_forget_other(rules, ds, id, lock, d);
    crate::surface_rel::lemma_filter_push(forget_doc_url(ds, id, lock), DocUrl { id, lock, url }, |x: DocUrl| crate::domain::domain_of_lock(rules, x.lock) == d);
}

/// Forgetting the same document URL in two runs whose domain's agree keeps
/// them agreeing.
pub proof fn lemma_doc_urls_forget_same(
    rules: Seq<clazel_psl::spec::Rule>,
    ds1: Seq<DocUrl>,
    ds2: Seq<DocUrl>,
    id: nat,
    lock: clazel_origin::spec::Origin,
    d: crate::domain::Domain,
)
    requires
        crate::domain::doc_urls_of_domain(rules, ds1, d) == crate::domain::doc_urls_of_domain(rules, ds2, d),
    ensures
        crate::domain::doc_urls_of_domain(rules, forget_doc_url(ds1, id, lock), d) == crate::domain::doc_urls_of_domain(rules, forget_doc_url(ds2, id, lock), d),
{
    lemma_doc_urls_forget_commute(rules, ds1, id, lock, d);
    lemma_doc_urls_forget_commute(rules, ds2, id, lock, d);
}

/// Setting the same document URL in two runs whose domain's agree keeps
/// them agreeing.
pub proof fn lemma_doc_urls_set_same(
    rules: Seq<clazel_psl::spec::Rule>,
    ds1: Seq<DocUrl>,
    ds2: Seq<DocUrl>,
    id: nat,
    lock: clazel_origin::spec::Origin,
    url: Seq<u32>,
    d: crate::domain::Domain,
)
    requires
        crate::domain::doc_urls_of_domain(rules, ds1, d) == crate::domain::doc_urls_of_domain(rules, ds2, d),
    ensures
        crate::domain::doc_urls_of_domain(rules, set_doc_url(ds1, id, lock, url), d) == crate::domain::doc_urls_of_domain(rules, set_doc_url(ds2, id, lock, url), d),
{
    lemma_doc_urls_forget_same(rules, ds1, ds2, id, lock, d);
    let ind = |x: DocUrl| crate::domain::domain_of_lock(rules, x.lock) == d;
    crate::surface_rel::lemma_filter_push(forget_doc_url(ds1, id, lock), DocUrl { id, lock, url }, ind);
    crate::surface_rel::lemma_filter_push(forget_doc_url(ds2, id, lock), DocUrl { id, lock, url }, ind);
}

/// The document URL of a renderer of domain `d` is read from `d`'s entries
/// alone.
pub proof fn lemma_doc_url_of_domain(rules: Seq<clazel_psl::spec::Rule>, ds: Seq<DocUrl>, r: Renderer, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_renderer(rules, r) == d,
    ensures
        doc_url_of(ds, r) == doc_url_of(crate::domain::doc_urls_of_domain(rules, ds, d), r),
    decreases ds.len(),
{
    let ind = |x: DocUrl| crate::domain::domain_of_lock(rules, x.lock) == d;
    if ds.len() > 0 {
        let x = ds[0];
        let rest = ds.drop_first();
        assert(ds =~= seq![x] + rest);
        rest.lemma_filter_prepend(x, ind);
        lemma_doc_url_of_domain(rules, rest, r, d);
        let fr = rest.filter(ind);
        if ind(x) {
            assert(ds.filter(ind) == seq![x] + fr);
            assert((seq![x] + fr)[0] == x);
            assert((seq![x] + fr).drop_first() =~= fr);
        } else {
            assert(ds.filter(ind) =~= fr);
            assert(!(x.id == r.id && x.lock == r.lock));
        }
    } else {
        reveal(Seq::filter);
    }
}

/// Related states give a renderer of `d` the same document URL.
pub proof fn lemma_doc_url_of_rel(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, r: Renderer)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::domain_of_renderer(rules, r) == d,
    ensures
        doc_url_of(s1.doc_urls, r) == doc_url_of(s2.doc_urls, r),
{
    lemma_doc_url_of_domain(rules, s1.doc_urls, r, d);
    lemma_doc_url_of_domain(rules, s2.doc_urls, r, d);
}

/// [`doc_url_of`] reads only a renderer's id, lock and committed URL.
pub proof fn lemma_doc_url_of_fields(ds: Seq<DocUrl>, r1: Renderer, r2: Renderer)
    requires
        r1.id == r2.id,
        r1.lock == r2.lock,
        r1.url == r2.url,
    ensures
        doc_url_of(ds, r1) == doc_url_of(ds, r2),
    decreases ds.len(),
{
    if ds.len() > 0 {
        lemma_doc_url_of_fields(ds.drop_first(), r1, r2);
    }
}

// ---------------------------------------------------------------------
// The invariant.
// ---------------------------------------------------------------------

/// Forgetting an entry keeps [`crate::invariant::doc_urls_wf`].
pub proof fn lemma_doc_urls_wf_forget(urls: UrlFns, ds: Seq<DocUrl>, id: nat, lock: clazel_origin::spec::Origin)
    requires
        crate::invariant::doc_urls_wf(urls, ds),
    ensures
        crate::invariant::doc_urls_wf(urls, forget_doc_url(ds, id, lock)),
{
    let f = forget_doc_url(ds, id, lock);
    assert forall|k: int| 0 <= k < f.len() implies (#[trigger] f[k]).lock is Tuple && lock_of_url(urls, f[k].url, f[k].id) == Some(f[k].lock) by {
        assert(f.contains(f[k]));
        clazel_cookie::storage::isolation::lemma_filter_elem(ds, |x: DocUrl| !(x.id == id && x.lock == lock), f[k]);
    }
}

/// Setting an entry under a tuple lock that is the URL's lock keeps
/// [`crate::invariant::doc_urls_wf`].
pub proof fn lemma_doc_urls_wf_set(urls: UrlFns, ds: Seq<DocUrl>, id: nat, lock: clazel_origin::spec::Origin, url: Seq<u32>)
    requires
        crate::invariant::doc_urls_wf(urls, ds),
        lock is Tuple,
        lock_of_url(urls, url, id) == Some(lock),
    ensures
        crate::invariant::doc_urls_wf(urls, set_doc_url(ds, id, lock, url)),
{
    lemma_doc_urls_wf_forget(urls, ds, id, lock);
    let f = forget_doc_url(ds, id, lock);
    let g = f.push(DocUrl { id, lock, url });
    assert forall|k: int| 0 <= k < g.len() implies (#[trigger] g[k]).lock is Tuple && lock_of_url(urls, g[k].url, g[k].id) == Some(g[k].lock) by {
        if k < f.len() {
            assert(g[k] == f[k]);
        }
    }
}

/// `update_url` keeps [`crate::invariant::kernel_wf`]: it changes only the
/// document URLs, by a set that passed the check.
pub proof fn lemma_update_url_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, r: Renderer, url: Seq<u8>)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        crate::invariant::kernel_wf(rules, urls, update_url(urls, s, r, url).0),
{
    if url.len() > 0 {
        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                if r.lock is Tuple && lock_of_url(urls, resolved, r.id) == Some(r.lock) {
                    lemma_doc_urls_wf_set(urls, s.doc_urls, r.id, r.lock, resolved);
                }
            }
        }
    }
}

/// The shape of `update_url`: no output; the state unchanged, or its
/// document URLs set under `r`'s id and lock to a URL whose origin is `r`'s
/// tuple lock.
pub proof fn lemma_update_url_shape(urls: UrlFns, s: State, r: Renderer, url: Seq<u8>)
    ensures
        update_url(urls, s, r, url).1.len() == 0,
        update_url(urls, s, r, url).0 == s || exists|u: Seq<u32>|
            #![trigger set_doc_url(s.doc_urls, r.id, r.lock, u)]
            update_url(urls, s, r, url).0 == (State { doc_urls: set_doc_url(s.doc_urls, r.id, r.lock, u), ..s }) && r.lock is Tuple && (urls.origin_of)(u) == Some(r.lock),
{
    if url.len() > 0 {
        if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
            if let Some(resolved) = (urls.resolve)(r.url, relative) {
                if r.lock is Tuple && lock_of_url(urls, resolved, r.id) == Some(r.lock) {
                    // `lock_of_url` of a URL with a tuple lock is its origin.
                    let o = (urls.origin_of)(resolved)->Some_0;
                    assert((urls.origin_of)(resolved) is Some);
                    assert(o == r.lock);
                    assert(update_url(urls, s, r, url).0 == (State { doc_urls: set_doc_url(s.doc_urls, r.id, r.lock, resolved), ..s }));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// `theorem_url_update_same_origin`.
// ---------------------------------------------------------------------

/// In a well-formed state, every renderer's document URL has its lock.
pub proof fn lemma_address_bar_origin_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        crate::statements::address_bar_origin_statement(urls, s),
{
    assert forall|i: int| 0 <= i < s.renderers.len() implies lock_of_url(urls, doc_url_of(s.doc_urls, #[trigger] s.renderers[i]), s.renderers[i].id) == Some(
        s.renderers[i].lock,
    ) by {
        lemma_doc_url_of_wf(urls, s.doc_urls, s.renderers[i]);
    }
}

/// [`doc_url_of`] is an entry's URL, under the renderer's id and lock, or
/// the renderer's committed URL.
pub proof fn lemma_doc_url_of_wf(urls: UrlFns, ds: Seq<DocUrl>, r: Renderer)
    requires
        crate::invariant::doc_urls_wf(urls, ds),
        lock_of_url(urls, r.url, r.id) == Some(r.lock),
    ensures
        lock_of_url(urls, doc_url_of(ds, r), r.id) == Some(r.lock),
    decreases ds.len(),
{
    if ds.len() > 0 {
        if !(ds[0].id == r.id && ds[0].lock == r.lock) {
            let rest = ds.drop_first();
            assert forall|k: int| 0 <= k < rest.len() implies (#[trigger] rest[k]).lock is Tuple && lock_of_url(urls, rest[k].url, rest[k].id) == Some(rest[k].lock) by {
                assert(rest[k] == ds[k + 1]);
            }
            lemma_doc_url_of_wf(urls, rest, r);
        }
    }
}

/// **`theorem_url_update_same_origin`** (phase-7.md item 7.16): an
/// `UpdateUrl` changes only the sender's document URL, to a URL of its own
/// tuple origin, and in every reachable state the address bar's URL of
/// every renderer has the renderer's lock.
pub proof fn theorem_url_update_same_origin(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        reachable(rules, urls, fetch, s),
    ensures
        crate::statements::url_update_same_origin_statement(rules, urls, fetch, s, id, bytes),
        crate::statements::address_bar_origin_statement(urls, s),
{
    crate::invariant::lemma_reachable_wf(rules, urls, fetch, s);
    lemma_address_bar_origin_wf(rules, urls, s);
    crate::invariant::lemma_find_by_id(s.renderers, id, 0);
    if let Some(i) = find_by_id(s.renderers, id, 0) {
        let r = s.renderers[i];
        if let Some(clazel_ipc::message::spec::Message::UpdateUrl { replace, url }) = accepted_message(r, bytes) {
            assert(r.committed);
            assert(r.id == id);
            lemma_update_url_shape(urls, s, r, url);
        }
    }
}

} // verus!

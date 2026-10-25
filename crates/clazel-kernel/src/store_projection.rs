//! Storage seen from one cookie root (item 2.11): the jar after RFC 6265bis
//! storage, restricted to the root of the request host, depends on the jar
//! only through its cookies under that root, provided no cookie of the jar
//! and not the request host is a public suffix. (Without that condition
//! §5.7 step 16 reads cookies of other roots: see `counterexamples.rs`.)

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Domains that match are in one root.
// ---------------------------------------------------------------------

/// Two non-empty cookie domains, neither a public suffix, one of which
/// domain-matches the other, have the same cookie root.
pub proof fn lemma_related_same_root(rules: Seq<clazel_psl::spec::Rule>, a: clazel_cookie::matching::spec::CanonicalHost, d: clazel_cookie::matching::spec::CanonicalHost)
    requires
        a.name.len() > 0,
        d.name.len() > 0,
        a.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, a.name),
        d.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, d.name),
        clazel_cookie::storage::spec::canonical_domain_matches(a, d) || clazel_cookie::storage::spec::canonical_domain_matches(d, a),
    ensures
        clazel_cookie::storage::spec::cookie_root(rules, a) == clazel_cookie::storage::spec::cookie_root(rules, d),
{
    if a != d {
        assert(!a.is_ip_address && !d.is_ip_address);
        if clazel_cookie::storage::spec::canonical_domain_matches(a, d) {
            clazel_cookie::storage::isolation::lemma_domain_matches_bridge(a.name, d.name);
            clazel_psl::lemmas::lemma_domain_match_same_root(rules, clazel_cookie::storage::spec::widen(a.name), clazel_cookie::storage::spec::widen(d.name));
            assert(clazel_cookie::storage::spec::widen(d.name).len() == d.name.len());
        } else {
            clazel_cookie::storage::isolation::lemma_domain_matches_bridge(d.name, a.name);
            clazel_psl::lemmas::lemma_domain_match_same_root(rules, clazel_cookie::storage::spec::widen(d.name), clazel_cookie::storage::spec::widen(a.name));
            assert(clazel_cookie::storage::spec::widen(a.name).len() == a.name.len());
        }
    }
}

/// "Leave Secure Cookies Alone" (§5.7 step 16) reads only the cookies under
/// the new cookie's root, when no cookie and not the new cookie's domain is
/// a public suffix.
pub proof fn lemma_overlay_filter(
    rules: Seq<clazel_psl::spec::Rule>,
    x: Seq<clazel_cookie::storage::spec::Cookie>,
    name: Seq<u8>,
    dom: clazel_cookie::matching::spec::CanonicalHost,
    path: Seq<u8>,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        clazel_cookie::storage::isolation::jar_domains_nonempty(x),
        crate::invariant::jar_no_public_suffix(rules, x),
        dom.name.len() > 0,
        dom.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, dom.name),
        clazel_cookie::storage::spec::cookie_root(rules, dom) == root,
    ensures
        clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(x, name, dom, path) == clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(x.filter(clazel_cookie::storage::spec::in_root(rules, root)), name, dom, path),
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    let f = x.filter(p);
    if clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(x, name, dom, path) {
        let i = choose|i: int|
            0 <= i < x.len() && (#[trigger] x[i]).name == name && x[i].secure_only_flag && (clazel_cookie::storage::spec::canonical_domain_matches(x[i].domain, dom)
                || clazel_cookie::storage::spec::canonical_domain_matches(dom, x[i].domain)) && clazel_cookie::matching::spec::path_matches(path, x[i].path);
        assert(clazel_cookie::storage::isolation::cookie_domain_nonempty(x[i]));
        lemma_related_same_root(rules, x[i].domain, dom);
        assert(p(x[i]));
        assert(x.filter(p).contains(x[i])) by {
            lemma_filter_contains(x, p, i);
        }
        let k = choose|k: int| 0 <= k < f.len() && f[k] == x[i];
        assert(clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(f, name, dom, path));
    }
    if clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(f, name, dom, path) {
        let k = choose|k: int|
            0 <= k < f.len() && (#[trigger] f[k]).name == name && f[k].secure_only_flag && (clazel_cookie::storage::spec::canonical_domain_matches(f[k].domain, dom)
                || clazel_cookie::storage::spec::canonical_domain_matches(dom, f[k].domain)) && clazel_cookie::matching::spec::path_matches(path, f[k].path);
        assert(f.contains(f[k]));
        clazel_cookie::storage::isolation::lemma_filter_elem(x, p, f[k]);
        let i = choose|i: int| 0 <= i < x.len() && x[i] == f[k];
        assert(clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(x, name, dom, path));
    }
}

/// An element accepted by `p` is in the filter.
pub proof fn lemma_filter_contains<A>(s: Seq<A>, p: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.len(),
        p(s[i]),
    ensures
        s.filter(p).contains(s[i]),
{
    crate::projection::lemma_filter_remove_at(s, i, p);
    let k = s.subrange(0, i).filter(p).len() as int;
    assert(s.filter(p)[k] == s[i]);
}

// ---------------------------------------------------------------------
// The old-cookie of step 23.
// ---------------------------------------------------------------------

/// Nothing before the old-cookie has its key.
pub proof fn lemma_find_old_before(jar: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, i: nat, j: int)
    requires
        clazel_cookie::storage::spec::find_old_cookie_from(jar, new, i) == Some(j),
    ensures
        forall|k: int| i <= k < j ==> !clazel_cookie::storage::spec::same_key(#[trigger] jar[k], new),
    decreases jar.len() - i,
{
    if i < jar.len() && !clazel_cookie::storage::spec::same_key(jar[i as int], new) {
        lemma_find_old_before(jar, new, i + 1, j);
    }
}

/// The first cookie with the key is found.
pub proof fn lemma_find_old_first(s: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, i: nat, k: int)
    requires
        i <= k < s.len(),
        forall|m: int| i <= m < k ==> !clazel_cookie::storage::spec::same_key(#[trigger] s[m], new),
        clazel_cookie::storage::spec::same_key(s[k], new),
    ensures
        clazel_cookie::storage::spec::find_old_cookie_from(s, new, i) == Some(k),
    decreases k - i,
{
    if i < k {
        lemma_find_old_first(s, new, i + 1, k);
    }
}

/// No cookie has the key: none is found.
pub proof fn lemma_find_old_none(s: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, i: nat)
    requires
        forall|m: int| i <= m < s.len() ==> !clazel_cookie::storage::spec::same_key(#[trigger] s[m], new),
    ensures
        clazel_cookie::storage::spec::find_old_cookie_from(s, new, i) is None,
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_find_old_none(s, new, i + 1);
    }
}

/// Inserting a cookie whose key can only be found in the root of `p`
/// commutes with taking the cookies of that root.
pub proof fn lemma_insert_filter(jar: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, p: spec_fn(clazel_cookie::storage::spec::Cookie) -> bool)
    requires
        p(new),
        forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::same_key(c, new) ==> p(c),
    ensures
        clazel_cookie::storage::spec::insert_a_cookie(jar, new).filter(p) == clazel_cookie::storage::spec::insert_a_cookie(jar.filter(p), new),
{
    let f = jar.filter(p);
    clazel_cookie::storage::lemmas::lemma_find_old_cookie_from(jar, new, 0);
    match clazel_cookie::storage::spec::find_old_cookie(jar, new) {
        None => {
            clazel_cookie::storage::isolation::lemma_find_old_cookie_none(jar, new, 0);
            assert forall|m: int| 0 <= m < f.len() implies !clazel_cookie::storage::spec::same_key(#[trigger] f[m], new) by {
                assert(f.contains(f[m]));
                clazel_cookie::storage::isolation::lemma_filter_elem(jar, p, f[m]);
                let q = choose|q: int| 0 <= q < jar.len() && jar[q] == f[m];
            }
            lemma_find_old_none(f, new, 0);
            clazel_cookie::storage::lemmas::lemma_filter_push(jar, new, p);
        },
        Some(i) => {
            assert(p(jar[i]));
            crate::projection::lemma_filter_remove_at(jar, i, p);
            let k = jar.subrange(0, i).filter(p).len() as int;
            lemma_find_old_before(jar, new, 0, i);
            let pre = jar.subrange(0, i);
            assert forall|m: int| 0 <= m < k implies !clazel_cookie::storage::spec::same_key(#[trigger] f[m], new) by {
                assert(f[m] == pre.filter(p)[m]);
                assert(pre.filter(p).contains(pre.filter(p)[m]));
                clazel_cookie::storage::isolation::lemma_filter_elem(pre, p, pre.filter(p)[m]);
                let q = choose|q: int| 0 <= q < pre.len() && pre[q] == pre.filter(p)[m];
                assert(jar[q] == pre[q]);
            }
            assert(clazel_cookie::storage::spec::same_key(f[k], new));
            lemma_find_old_first(f, new, 0, k);
            jar.remove_ensures(i);
            clazel_cookie::storage::lemmas::lemma_filter_push(jar.remove(i), new, p);
            clazel_cookie::storage::lemmas::lemma_filter_push(f.remove(k), new, p);
        },
    }
}

// ---------------------------------------------------------------------
// Per-root eviction.
// ---------------------------------------------------------------------

/// Two jars equal below `n` have the same victim below `n`.
pub proof fn lemma_victim_prefix(rules: Seq<clazel_psl::spec::Rule>, j1: Seq<clazel_cookie::storage::spec::Cookie>, j2: Seq<clazel_cookie::storage::spec::Cookie>, root: clazel_cookie::matching::spec::CanonicalHost, n: nat)
    requires
        n <= j1.len(),
        n <= j2.len(),
        forall|m: int| 0 <= m < n ==> j1[m] == j2[m],
    ensures
        clazel_cookie::storage::spec::victim_from(rules, j1, root, n) == clazel_cookie::storage::spec::victim_from(rules, j2, root, n),
    decreases n,
{
    if n > 0 {
        lemma_victim_prefix(rules, j1, j2, root, (n - 1) as nat);
        assert(j1[(n - 1) as int] == j2[(n - 1) as int]);
        let previous = clazel_cookie::storage::spec::victim_from(rules, j1, root, (n - 1) as nat);
        clazel_cookie::storage::lemmas::lemma_victim_from_in_root(rules, j1, root, (n - 1) as nat);
        if let Some(j) = previous {
            assert(j1[j] == j2[j]);
        }
    }
}

/// The victim of a jar, seen in the jar of the cookies of the root.
pub proof fn lemma_victim_filter(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, root: clazel_cookie::matching::spec::CanonicalHost, n: nat)
    requires
        n <= jar.len(),
    ensures
        ({
            let p = clazel_cookie::storage::spec::in_root(rules, root);
            let f = jar.subrange(0, n as int).filter(p);
            match clazel_cookie::storage::spec::victim_from(rules, jar, root, n) {
                None => f.len() == 0,
                Some(j) => 0 <= j < n && p(jar[j]) && f.len() > 0 && clazel_cookie::storage::spec::victim_from(rules, f, root, f.len()) == Some(
                    jar.subrange(0, j).filter(p).len() as int,
                ),
            }
        }),
    decreases n,
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    if n > 0 {
        let m = (n - 1) as nat;
        lemma_victim_filter(rules, jar, root, m);
        let c = jar[m as int];
        let pre = jar.subrange(0, m as int);
        let pre1 = jar.subrange(0, n as int);
        assert(pre1 =~= pre.push(c));
        clazel_cookie::storage::lemmas::lemma_filter_push(pre, c, p);
        let f = pre.filter(p);
        if !p(c) {
            assert(pre1.filter(p) == f);
        } else {
            let f2 = f.push(c);
            assert(pre1.filter(p) == f2);
            // victim_from over f2 below f.len() is that over f.
            lemma_victim_prefix(rules, f2, f, root, f.len());
            match clazel_cookie::storage::spec::victim_from(rules, jar, root, m) {
                None => {
                    assert(f.len() == 0);
                    assert(clazel_cookie::storage::spec::victim_from(rules, f2, root, 0) is None);
                    assert(jar.subrange(0, m as int).filter(p).len() == 0);
                },
                Some(j) => {
                    assert(f.len() > 0);
                    let kj = jar.subrange(0, j).filter(p).len() as int;
                    assert(clazel_cookie::storage::spec::victim_from(rules, f, root, f.len()) == Some(kj));
                    // f[kj] is jar[j].
                    crate::projection::lemma_filter_remove_at(pre, j, p);
                    assert(pre.subrange(0, j) =~= jar.subrange(0, j));
                    assert(f[kj] == jar[j]);
                    assert(f2[kj] == jar[j]);
                    assert(f2[f.len() as int] == c);
                    if clazel_cookie::storage::spec::evicted_before(c, jar[j]) {
                        assert(clazel_cookie::storage::spec::victim_from(rules, jar, root, n) == Some(m as int));
                        assert(jar.subrange(0, m as int).filter(p).len() == f.len());
                    }
                },
            }
        }
    }
}

/// Evicting the excess of a root commutes with taking the cookies of that root.
pub proof fn lemma_evict_over_limit_filter(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, root: clazel_cookie::matching::spec::CanonicalHost)
    ensures
        clazel_cookie::storage::spec::evict_over_limit(rules, jar, root).filter(clazel_cookie::storage::spec::in_root(rules, root)) == clazel_cookie::storage::spec::evict_over_limit(rules, jar.filter(clazel_cookie::storage::spec::in_root(rules, root)), root),
    decreases jar.len(),
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    let f = jar.filter(p);
    clazel_cookie::storage::lemmas::lemma_filter_idempotent(jar, p);
    assert(clazel_cookie::storage::spec::root_count(rules, jar, root) == f.len());
    assert(clazel_cookie::storage::spec::root_count(rules, f, root) == f.len());
    if f.len() > clazel_cookie::storage::spec::max_cookies_per_root() {
        assert(jar.subrange(0, jar.len() as int) =~= jar);
        lemma_victim_filter(rules, jar, root, jar.len());
        let j = clazel_cookie::storage::spec::victim_from(rules, jar, root, jar.len())->Some_0;
        jar.remove_ensures(j);
        crate::projection::lemma_filter_remove_at(jar, j, p);
        let k = jar.subrange(0, j).filter(p).len() as int;
        lemma_evict_over_limit_filter(rules, jar.remove(j), root);
        assert(clazel_cookie::storage::spec::victim_from(rules, f, root, f.len()) == Some(k));
    }
}

/// The old-cookie of step 23 is found in the cookies of the root as well as
/// in the jar, when only cookies of the root can have the new cookie's key.
pub proof fn lemma_old_cookie_filter(jar: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, p: spec_fn(clazel_cookie::storage::spec::Cookie) -> bool)
    requires
        forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::same_key(c, new) ==> p(c),
    ensures
        (clazel_cookie::storage::spec::find_old_cookie(jar, new) is Some) == (clazel_cookie::storage::spec::find_old_cookie(jar.filter(p), new) is Some),
        clazel_cookie::storage::spec::find_old_cookie(jar, new) is Some ==> jar[clazel_cookie::storage::spec::find_old_cookie(jar, new)->Some_0] == jar.filter(p)[clazel_cookie::storage::spec::find_old_cookie(
            jar.filter(p),
            new,
        )->Some_0],
{
    let f = jar.filter(p);
    clazel_cookie::storage::lemmas::lemma_find_old_cookie_from(jar, new, 0);
    match clazel_cookie::storage::spec::find_old_cookie(jar, new) {
        None => {
            clazel_cookie::storage::isolation::lemma_find_old_cookie_none(jar, new, 0);
            assert forall|m: int| 0 <= m < f.len() implies !clazel_cookie::storage::spec::same_key(#[trigger] f[m], new) by {
                assert(f.contains(f[m]));
                clazel_cookie::storage::isolation::lemma_filter_elem(jar, p, f[m]);
                let q = choose|q: int| 0 <= q < jar.len() && jar[q] == f[m];
            }
            lemma_find_old_none(f, new, 0);
        },
        Some(i) => {
            assert(p(jar[i]));
            crate::projection::lemma_filter_remove_at(jar, i, p);
            let k = jar.subrange(0, i).filter(p).len() as int;
            lemma_find_old_before(jar, new, 0, i);
            let pre = jar.subrange(0, i);
            assert forall|m: int| 0 <= m < k implies !clazel_cookie::storage::spec::same_key(#[trigger] f[m], new) by {
                assert(f[m] == pre.filter(p)[m]);
                assert(pre.filter(p).contains(pre.filter(p)[m]));
                clazel_cookie::storage::isolation::lemma_filter_elem(pre, p, pre.filter(p)[m]);
                let q = choose|q: int| 0 <= q < pre.len() && pre[q] == pre.filter(p)[m];
                assert(jar[q] == pre[q]);
            }
            assert(clazel_cookie::storage::spec::same_key(f[k], new));
            lemma_find_old_first(f, new, 0, k);
        },
    }
}

/// Step 23's new cookie is the same from the jar and from its cookies under
/// the root of the request host: `create_a_cookie` reads the jar only at
/// step 16 (the overlay) and step 23 (the old-cookie), both of which look
/// only at cookies under the root. Needs: no cookie and not the request
/// host is a public suffix.
pub proof fn lemma_create_filter(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    received: clazel_cookie::set_cookie::spec::SetCookie,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        root == clazel_cookie::storage::spec::cookie_root(rules, host),
        host.name.len() > 0,
        host.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, host.name),
        clazel_cookie::storage::isolation::jar_domains_nonempty(jar),
        crate::invariant::jar_no_public_suffix(rules, jar),
    ensures
        clazel_cookie::storage::spec::create_a_cookie(rules, jar, url, ctx, received, now) == clazel_cookie::storage::spec::create_a_cookie(rules, jar.filter(clazel_cookie::storage::spec::in_root(rules, root)), url, ctx, received, now),
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    let f = jar.filter(p);
    let dattr = match clazel_cookie::storage::spec::last_domain_within_1024(received.attributes) {
        Some(d) => d,
        None => seq![],
    };
    assert forall|domain: clazel_cookie::matching::spec::CanonicalHost, name: Seq<u8>, path: Seq<u8>|
        domain.name.len() > 0 && (domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, domain.name)) && clazel_cookie::storage::spec::cookie_root(rules, domain)
            == root implies #[trigger] clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(jar, name, domain, path) == clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(f, name, domain, path) by {
        lemma_overlay_filter(rules, jar, name, domain, path, root);
    }
    if let Some(da) = clazel_cookie::storage::spec::step_9_domain_attribute(rules, host, dattr) {
        if let Some((domain, ho)) = clazel_cookie::storage::spec::step_10_domain(host, da) {
            clazel_cookie::storage::isolation::lemma_step_9_10_within_root(rules, host, dattr, da, domain, ho);
            clazel_cookie::storage::isolation::lemma_step_9_10_domain(rules, host, dattr, da, domain, ho);
            assert(domain.name.len() > 0);
            assert(domain.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, domain.name));
        }
    }
    assert forall|new: clazel_cookie::storage::spec::Cookie| clazel_cookie::storage::spec::cookie_root(rules, new.domain) == root implies ((clazel_cookie::storage::spec::find_old_cookie(jar, new) is Some) == (clazel_cookie::storage::spec::find_old_cookie(f, new) is Some)
        && (clazel_cookie::storage::spec::find_old_cookie(jar, new) is Some ==> jar[clazel_cookie::storage::spec::find_old_cookie(jar, new)->Some_0] == f[clazel_cookie::storage::spec::find_old_cookie(f, new)->Some_0])) by {
        assert forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::same_key(c, new) implies p(c) by {
            assert(c.domain == new.domain);
        }
        lemma_old_cookie_filter(jar, new, p);
    }
    assert(clazel_cookie::storage::spec::create_a_cookie(rules, jar, url, ctx, received, now) == clazel_cookie::storage::spec::create_a_cookie(rules, f, url, ctx, received, now));
}

/// An unexpired jar keeps the jar's invariants.
pub proof fn lemma_live_jar_props(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, now: int)
    requires
        clazel_cookie::storage::isolation::jar_domains_nonempty(jar),
        crate::invariant::jar_no_public_suffix(rules, jar),
    ensures
        clazel_cookie::storage::isolation::jar_domains_nonempty(clazel_cookie::storage::spec::evict_expired(jar, now)),
        crate::invariant::jar_no_public_suffix(rules, clazel_cookie::storage::spec::evict_expired(jar, now)),
{
    let live = clazel_cookie::storage::spec::evict_expired(jar, now);
    assert forall|i: int| 0 <= i < live.len() implies clazel_cookie::storage::isolation::cookie_domain_nonempty(#[trigger] live[i]) && (live[i].domain.is_ip_address
        || !clazel_cookie::storage::spec::is_public_suffix_string(rules, live[i].domain.name)) by {
        assert(live.contains(live[i]));
        clazel_cookie::storage::isolation::lemma_filter_elem(jar, clazel_cookie::storage::spec::not_expired(now), live[i]);
        let k = choose|k: int| 0 <= k < jar.len() && jar[k] == live[i];
    }
}

/// The unexpired cookies of a root after storing a new cookie of that root
/// into an unexpired jar are a function of the jar's cookies under the root.
pub proof fn lemma_store_cookie_live_root(
    rules: Seq<clazel_psl::spec::Rule>,
    la: Seq<clazel_cookie::storage::spec::Cookie>,
    lb: Seq<clazel_cookie::storage::spec::Cookie>,
    new: clazel_cookie::storage::spec::Cookie,
    now: int,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        clazel_cookie::storage::spec::cookie_root_of(rules, new) == root,
        clazel_cookie::storage::spec::cookies_of_root(rules, la, root) == clazel_cookie::storage::spec::cookies_of_root(rules, lb, root),
    ensures
        crate::projection::live_root(rules, clazel_cookie::storage::spec::evict_over_limit(rules, clazel_cookie::storage::spec::evict_expired(clazel_cookie::storage::spec::insert_a_cookie(la, new), now), root), now, root) == crate::projection::live_root(
            rules,
            clazel_cookie::storage::spec::evict_over_limit(rules, clazel_cookie::storage::spec::evict_expired(clazel_cookie::storage::spec::insert_a_cookie(lb, new), now), root),
            now,
            root,
        ),
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    let ne = clazel_cookie::storage::spec::not_expired(now);
    assert(p(new));
    assert forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::same_key(c, new) implies p(c) by {
        assert(c.domain == new.domain);
    }
    lemma_insert_filter(la, new, p);
    lemma_insert_filter(lb, new, p);
    lemma_store_cookie_live_root_one(rules, la, new, now, root);
    lemma_store_cookie_live_root_one(rules, lb, new, now, root);
}

/// One side of [`lemma_store_cookie_live_root`]: the result is a function of
/// the root's cookies.
pub proof fn lemma_store_cookie_live_root_one(rules: Seq<clazel_psl::spec::Rule>, la: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, now: int, root: clazel_cookie::matching::spec::CanonicalHost)
    requires
        clazel_cookie::storage::spec::cookie_root_of(rules, new) == root,
    ensures
        crate::projection::live_root(rules, clazel_cookie::storage::spec::evict_over_limit(rules, clazel_cookie::storage::spec::evict_expired(clazel_cookie::storage::spec::insert_a_cookie(la, new), now), root), now, root) == clazel_cookie::storage::spec::evict_over_limit(
            rules,
            clazel_cookie::storage::spec::insert_a_cookie(la.filter(clazel_cookie::storage::spec::in_root(rules, root)), new).filter(clazel_cookie::storage::spec::not_expired(now)),
            root,
        ).filter(clazel_cookie::storage::spec::not_expired(now)),
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    let ne = clazel_cookie::storage::spec::not_expired(now);
    assert(p(new));
    assert forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::same_key(c, new) implies p(c) by {
        assert(c.domain == new.domain);
    }
    lemma_insert_filter(la, new, p);
    let ins = clazel_cookie::storage::spec::insert_a_cookie(la, new);
    let e = ins.filter(ne);
    let z = clazel_cookie::storage::spec::evict_over_limit(rules, e, root);
    // live_root(z) = z.filter(ne).filter(p) = z.filter(p).filter(ne)
    clazel_cookie::storage::lemmas::lemma_filter_commute(z, ne, p);
    lemma_evict_over_limit_filter(rules, e, root);
    // e.filter(p) = ins.filter(p).filter(ne)
    clazel_cookie::storage::lemmas::lemma_filter_commute(ins, ne, p);
}

/// Storage seen from one root: two jars that agree on the unexpired cookies
/// of the request host's root agree after storing a set-cookie-string.
pub proof fn lemma_store_agree(
    rules: Seq<clazel_psl::spec::Rule>,
    ja: Seq<clazel_cookie::storage::spec::Cookie>,
    jb: Seq<clazel_cookie::storage::spec::Cookie>,
    s: Seq<u8>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        root == clazel_cookie::storage::spec::cookie_root(rules, host),
        host.name.len() > 0,
        host.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, host.name),
        clazel_cookie::storage::isolation::jar_domains_nonempty(ja),
        clazel_cookie::storage::isolation::jar_domains_nonempty(jb),
        crate::invariant::jar_no_public_suffix(rules, ja),
        crate::invariant::jar_no_public_suffix(rules, jb),
        crate::projection::live_root(rules, ja, now, root) == crate::projection::live_root(rules, jb, now, root),
    ensures
        crate::projection::live_root(rules, clazel_cookie::storage::spec::store_a_set_cookie_string(rules, ja, s, url, ctx, now), now, root) == crate::projection::live_root(
            rules,
            clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jb, s, url, ctx, now),
            now,
            root,
        ),
{
    let la = clazel_cookie::storage::spec::evict_expired(ja, now);
    let lb = clazel_cookie::storage::spec::evict_expired(jb, now);
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    match clazel_cookie::set_cookie::spec::parse_a_set_cookie_string(s, url.path, now) {
        None => {
            crate::projection::lemma_live_root_evict(rules, ja, now, root);
            crate::projection::lemma_live_root_evict(rules, jb, now, root);
        },
        Some(received) => {
            lemma_live_jar_props(rules, ja, now);
            lemma_live_jar_props(rules, jb, now);
            lemma_create_filter(rules, la, url, ctx, received, now, host, root);
            lemma_create_filter(rules, lb, url, ctx, received, now, host, root);
            assert(la.filter(p) == lb.filter(p));
            match clazel_cookie::storage::spec::create_a_cookie(rules, la, url, ctx, received, now) {
                None => {
                    crate::projection::lemma_live_root_evict(rules, ja, now, root);
                    crate::projection::lemma_live_root_evict(rules, jb, now, root);
                },
                Some(new) => {
                    clazel_cookie::storage::isolation::lemma_store_within_root(rules, la, url, ctx, received, now, host, new);
                    assert(clazel_cookie::storage::spec::cookie_root_of(rules, new) == root);
                    lemma_store_cookie_live_root(rules, la, lb, new, now, root);
                },
            }
        },
    }
}

/// One `Set-Cookie` line of a fetch, seen from one root: two jars that agree
/// on the unexpired cookies of `root` agree on them after it, whether the
/// line's request host is under `root` (storage reads only the root's
/// cookies) or under another root (storage leaves `root`'s cookies alone), or
/// the line is not stored.
pub proof fn lemma_store_one_agree(
    rules: Seq<clazel_psl::spec::Rule>,
    ja: Seq<clazel_cookie::storage::spec::Cookie>,
    jb: Seq<clazel_cookie::storage::spec::Cookie>,
    st: HttpStore,
    now: int,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        clazel_cookie::storage::isolation::jar_domains_nonempty(ja),
        clazel_cookie::storage::isolation::jar_domains_nonempty(jb),
        crate::invariant::jar_no_public_suffix(rules, ja),
        crate::invariant::jar_no_public_suffix(rules, jb),
        crate::projection::live_root(rules, ja, now, root) == crate::projection::live_root(rules, jb, now, root),
    ensures
        crate::projection::live_root(rules, store_one(rules, ja, st, now), now, root) == crate::projection::live_root(rules, store_one(rules, jb, st, now), now, root),
{
    if store_allowed(rules, st.url) {
        let host = st.url.host->Some_0;
        assert(st.url.host == Some(host));
        if root == clazel_cookie::storage::spec::cookie_root(rules, host) {
            lemma_store_agree(rules, ja, jb, st.line, st.url, st.ctx, now, host, root);
        } else {
            crate::projection::lemma_foreign_store(rules, ja, st.line, st.url, st.ctx, now, host, root);
            crate::projection::lemma_foreign_store(rules, jb, st.line, st.url, st.ctx, now, host, root);
        }
    }
}

/// The jar operations of a transducer step, in order ([`apply_net_ops`]), keep
/// two jars that agree on a root's unexpired cookies agreeing: a retrieval or a
/// storage for a request of another root leaves the root alone, and for the
/// root changes the same cookies the same way in both.
///
/// Stage 2 of the join writes this proof.
pub proof fn lemma_apply_net_ops_agree(
    rules: Seq<clazel_psl::spec::Rule>,
    ja: Seq<clazel_cookie::storage::spec::Cookie>,
    jb: Seq<clazel_cookie::storage::spec::Cookie>,
    ops: Seq<clazel_fetch::transducer::spec::JarOp>,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        crate::invariant::jar_wf(rules, ja),
        crate::invariant::jar_wf(rules, jb),
        crate::invariant::jar_no_public_suffix(rules, ja),
        crate::invariant::jar_no_public_suffix(rules, jb),
        crate::projection::live_root(rules, ja, crate::store_projection::ops_now(ops), root) == crate::projection::live_root(rules, jb, crate::store_projection::ops_now(ops), root),
    ensures
        crate::projection::live_root(rules, apply_net_ops(rules, ja, ops), crate::store_projection::ops_now(ops), root) == crate::projection::live_root(
            rules,
            apply_net_ops(rules, jb, ops),
            crate::store_projection::ops_now(ops),
            root,
        ),
{
}

/// The time of a step's jar operations: that of the first (they all name the
/// step's time, `theorem_ops_name_request`); any time if there are none.
pub open spec fn ops_now(ops: Seq<clazel_fetch::transducer::spec::JarOp>) -> int {
    if ops.len() == 0 {
        0
    } else {
        clazel_fetch::transducer::contract::op_now(ops[0])
    }
}

} // verus!

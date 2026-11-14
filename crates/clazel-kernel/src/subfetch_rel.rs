//! Item 5.19's part of the proofs about the kernel's step: the sub-fetch
//! table read and updated by key, a sub-fetch's actions and jar operations,
//! and the unwinding lemmas of item 2.11's noninterference for `SubNet`.
//!
//! `rel` (`noninterference.rs`) holds the two runs to the same sub-fetches
//! and counts under the observer's locks. Every entry carries its renderer's
//! lock and is read and changed only by key (renderer, lock, serial), so the
//! entries of another domain, which the purge's runs do not share, never
//! decide what happens to the observer's. A sub-fetch's jar operations are
//! applied only when its request is same-origin with its renderer's lock
//! ([`credentialed`]), so they name the lock's host: another domain's touch
//! only its own cookie root.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The table, by key, and a domain's part of it.
// ---------------------------------------------------------------------

/// The domain predicate of the sub-fetch table.
pub open spec fn in_domain(rules: Seq<clazel_psl::spec::Rule>, d: crate::domain::Domain) -> spec_fn(SubFetch) -> bool {
    |x: SubFetch| crate::domain::domain_of_lock(rules, x.lock) == d
}

/// Prepending to a domain's part.
proof fn lemma_sub_prepend(rules: Seq<clazel_psl::spec::Rule>, x: SubFetch, t: Seq<SubFetch>, d: crate::domain::Domain)
    ensures
        crate::domain::subfetches_of_domain(rules, seq![x] + t, d) == (if crate::domain::domain_of_lock(rules, x.lock) == d {
            seq![x] + crate::domain::subfetches_of_domain(rules, t, d)
        } else {
            crate::domain::subfetches_of_domain(rules, t, d)
        }),
{
    t.lemma_filter_prepend(x, |y: SubFetch| crate::domain::domain_of_lock(rules, y.lock) == d);
}

/// A key of `d`'s is read the same in the table and in `d`'s part of it.
pub proof fn lemma_subfetch_of_domain(rules: Seq<clazel_psl::spec::Rule>, fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, serial: nat, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) == d,
    ensures
        subfetch_of(fs, id, lock, serial) == subfetch_of(crate::domain::subfetches_of_domain(rules, fs, d), id, lock, serial),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs =~= seq![x] + t);
        lemma_sub_prepend(rules, x, t, d);
        lemma_subfetch_of_domain(rules, t, id, lock, serial, d);
        let ft = crate::domain::subfetches_of_domain(rules, t, d);
        if crate::domain::domain_of_lock(rules, x.lock) == d {
            assert((seq![x] + ft)[0] == x);
            assert((seq![x] + ft).drop_first() =~= ft);
        }
    } else {
        reveal(Seq::filter);
    }
}

/// The entry [`subfetch_of`] finds has the key it was asked for.
pub proof fn lemma_subfetch_of_key(fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, serial: nat)
    ensures
        subfetch_of(fs, id, lock, serial) matches Some(f) ==> subfetch_is(f, id, lock, serial),
    decreases fs.len(),
{
    if fs.len() > 0 {
        lemma_subfetch_of_key(fs.drop_first(), id, lock, serial);
    }
}

/// The sub-fetch a `SubNet` is about is its renderer's, under the renderer's
/// lock.
pub proof fn lemma_subnet_target_key(s: State, renderer: nat, serial: nat)
    ensures
        match subnet_target(s, renderer, serial) {
            Some(f) => f.renderer == renderer && f.serial == serial && match find_by_id(s.renderers, renderer, 0) {
                Some(i) => f.lock == s.renderers[i].lock,
                None => false,
            },
            None => true,
        },
{
    if let Some(i) = find_by_id(s.renderers, renderer, 0) {
        lemma_subfetch_of_key(s.subfetches, renderer, s.renderers[i].lock, serial);
    }
}

/// Replacing the first entry of a key commutes with taking a domain's part:
/// for a key of `d`, both runs replace the same entry of `d`'s part; for a
/// key of another domain, `d`'s part is unchanged.
pub proof fn lemma_replace_domain(rules: Seq<clazel_psl::spec::Rule>, fs: Seq<SubFetch>, f: SubFetch, d: crate::domain::Domain)
    ensures
        crate::domain::domain_of_lock(rules, f.lock) == d ==> crate::domain::subfetches_of_domain(rules, replace_subfetch(fs, f), d) == replace_subfetch(
            crate::domain::subfetches_of_domain(rules, fs, d),
            f,
        ),
        crate::domain::domain_of_lock(rules, f.lock) != d ==> crate::domain::subfetches_of_domain(rules, replace_subfetch(fs, f), d)
            == crate::domain::subfetches_of_domain(rules, fs, d),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs =~= seq![x] + t);
        lemma_sub_prepend(rules, x, t, d);
        lemma_replace_domain(rules, t, f, d);
        lemma_sub_prepend(rules, f, t, d);
        lemma_sub_prepend(rules, x, replace_subfetch(t, f), d);
        let ft = crate::domain::subfetches_of_domain(rules, t, d);
        if subfetch_is(x, f.renderer, f.lock, f.serial) {
            assert(replace_subfetch(fs, f) == seq![f] + t);
            if crate::domain::domain_of_lock(rules, x.lock) == d {
                assert((seq![x] + ft)[0] == x);
                assert((seq![x] + ft).drop_first() =~= ft);
            }
        } else {
            assert(replace_subfetch(fs, f) == seq![x] + replace_subfetch(t, f));
            if crate::domain::domain_of_lock(rules, x.lock) == d {
                assert((seq![x] + ft)[0] == x);
                assert((seq![x] + ft).drop_first() =~= ft);
            }
        }
    } else {
        reveal(Seq::filter);
    }
}

/// Dropping the first entry of a key commutes with taking a domain's part,
/// as [`lemma_replace_domain`].
pub proof fn lemma_drop_domain(rules: Seq<clazel_psl::spec::Rule>, fs: Seq<SubFetch>, f: SubFetch, d: crate::domain::Domain)
    ensures
        crate::domain::domain_of_lock(rules, f.lock) == d ==> crate::domain::subfetches_of_domain(rules, drop_subfetch(fs, f), d) == drop_subfetch(
            crate::domain::subfetches_of_domain(rules, fs, d),
            f,
        ),
        crate::domain::domain_of_lock(rules, f.lock) != d ==> crate::domain::subfetches_of_domain(rules, drop_subfetch(fs, f), d)
            == crate::domain::subfetches_of_domain(rules, fs, d),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs =~= seq![x] + t);
        lemma_sub_prepend(rules, x, t, d);
        lemma_drop_domain(rules, t, f, d);
        lemma_sub_prepend(rules, x, drop_subfetch(t, f), d);
        let ft = crate::domain::subfetches_of_domain(rules, t, d);
        if crate::domain::domain_of_lock(rules, x.lock) == d {
            assert((seq![x] + ft)[0] == x);
            assert((seq![x] + ft).drop_first() =~= ft);
        }
        if !subfetch_is(x, f.renderer, f.lock, f.serial) {
            assert(drop_subfetch(fs, f) == seq![x] + drop_subfetch(t, f));
        }
    } else {
        reveal(Seq::filter);
    }
}

/// Adding an entry at the end, to a domain's part.
pub proof fn lemma_push_domain(rules: Seq<clazel_psl::spec::Rule>, fs: Seq<SubFetch>, f: SubFetch, d: crate::domain::Domain)
    ensures
        crate::domain::subfetches_of_domain(rules, fs.push(f), d) == if crate::domain::domain_of_lock(rules, f.lock) == d {
            crate::domain::subfetches_of_domain(rules, fs, d).push(f)
        } else {
            crate::domain::subfetches_of_domain(rules, fs, d)
        },
{
    crate::surface_rel::lemma_filter_push(fs, f, |x: SubFetch| crate::domain::domain_of_lock(rules, x.lock) == d);
}

/// A map that keeps every entry's lock commutes with taking a domain's
/// part.
pub proof fn lemma_map_domain<A>(s: Seq<A>, g: spec_fn(A) -> A, p: spec_fn(A) -> bool)
    requires
        forall|x: A| #[trigger] p(g(x)) == p(x),
    ensures
        s.map_values(g).filter(p) == s.filter(p).map_values(g),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        lemma_map_domain(t, g, p);
        assert(s.map_values(g).drop_last() =~= t.map_values(g));
        assert(s.map_values(g).last() == g(s.last()));
        if p(s.last()) {
            assert(s.filter(p) == t.filter(p).push(s.last()));
            assert(t.filter(p).push(s.last()).map_values(g) =~= t.filter(p).map_values(g).push(g(s.last())));
        }
    } else {
        assert(s.map_values(g) =~= Seq::<A>::empty());
    }
}

/// A commit's ending of a renderer's sub-fetches, in two runs whose
/// sub-fetches of `d` agree, keeps them agreeing.
pub proof fn lemma_end_domain(rules: Seq<clazel_psl::spec::Rule>, f1: Seq<SubFetch>, f2: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    ensures
        crate::domain::subfetches_of_domain(rules, f1, d) == crate::domain::subfetches_of_domain(rules, f2, d) ==> crate::domain::subfetches_of_domain(
            rules,
            end_subfetches(f1, id, lock),
            d,
        ) == crate::domain::subfetches_of_domain(rules, end_subfetches(f2, id, lock), d),
{
    let g = |f: SubFetch| if f.renderer == id && f.lock == lock { SubFetch { ended: true, ..f } } else { f };
    let p = |x: SubFetch| crate::domain::domain_of_lock(rules, x.lock) == d;
    assert forall|x: SubFetch| #[trigger] p(g(x)) == p(x) by {}
    lemma_map_domain(f1, g, p);
    lemma_map_domain(f2, g, p);
}

/// A commit's new document count, in two runs whose counts of `d` agree,
/// keeps them agreeing.
pub proof fn lemma_new_document_domain(rules: Seq<clazel_psl::spec::Rule>, c1: Seq<SubCount>, c2: Seq<SubCount>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    ensures
        crate::domain::subcounts_of_domain(rules, c1, d) == crate::domain::subcounts_of_domain(rules, c2, d) ==> crate::domain::subcounts_of_domain(
            rules,
            new_document_counts(c1, id, lock),
            d,
        ) == crate::domain::subcounts_of_domain(rules, new_document_counts(c2, id, lock), d),
{
    let g = |c: SubCount| if c.renderer == id && c.lock == lock { SubCount { in_document: 0, ..c } } else { c };
    let p = |x: SubCount| crate::domain::domain_of_lock(rules, x.lock) == d;
    assert forall|x: SubCount| #[trigger] p(g(x)) == p(x) by {}
    lemma_map_domain(c1, g, p);
    lemma_map_domain(c2, g, p);
}

// ---------------------------------------------------------------------
// Counts.
// ---------------------------------------------------------------------

/// A key of `d`'s is counted the same in the counts and in `d`'s part.
pub proof fn lemma_subcount_of_domain(rules: Seq<clazel_psl::spec::Rule>, cs: Seq<SubCount>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) == d,
    ensures
        subcount_of(cs, id, lock) == subcount_of(crate::domain::subcounts_of_domain(rules, cs, d), id, lock),
    decreases cs.len(),
{
    let p = |y: SubCount| crate::domain::domain_of_lock(rules, y.lock) == d;
    if cs.len() > 0 {
        let x = cs[0];
        let t = cs.drop_first();
        assert(cs =~= seq![x] + t);
        t.lemma_filter_prepend(x, p);
        lemma_subcount_of_domain(rules, t, id, lock, d);
        let ft = t.filter(p);
        if p(x) {
            assert((seq![x] + ft)[0] == x);
            assert((seq![x] + ft).drop_first() =~= ft);
        }
    } else {
        reveal(Seq::filter);
    }
}

/// Setting a count of `d`'s in two runs whose counts of `d` agree keeps them
/// agreeing; setting one of another domain changes none of `d`'s.
pub proof fn lemma_set_subcount_domain(
    rules: Seq<clazel_psl::spec::Rule>,
    c1: Seq<SubCount>,
    c2: Seq<SubCount>,
    id: nat,
    lock: clazel_origin::spec::Origin,
    serial: nat,
    in_document: nat,
    d: crate::domain::Domain,
)
    ensures
        crate::domain::subcounts_of_domain(rules, c1, d) == crate::domain::subcounts_of_domain(rules, c2, d) ==> crate::domain::subcounts_of_domain(
            rules,
            set_subcount(c1, id, lock, serial, in_document),
            d,
        ) == crate::domain::subcounts_of_domain(rules, set_subcount(c2, id, lock, serial, in_document), d),
        crate::domain::domain_of_lock(rules, lock) != d ==> crate::domain::subcounts_of_domain(rules, set_subcount(c1, id, lock, serial, in_document), d)
            == crate::domain::subcounts_of_domain(rules, c1, d),
{
    let keep = |c: SubCount| !(c.renderer == id && c.lock == lock);
    let ind = |c: SubCount| crate::domain::domain_of_lock(rules, c.lock) == d;
    let e = SubCount { renderer: id, lock, serial, in_document };
    crate::surface_rel::lemma_filter_commute(c1, keep, ind);
    crate::surface_rel::lemma_filter_commute(c2, keep, ind);
    crate::surface_rel::lemma_filter_push(c1.filter(keep), e, ind);
    crate::surface_rel::lemma_filter_push(c2.filter(keep), e, ind);
    if crate::domain::domain_of_lock(rules, lock) != d {
        let cd = c1.filter(ind);
        assert forall|i: int| 0 <= i < cd.len() implies keep(#[trigger] cd[i]) by {
            c1.lemma_filter_pred(ind, i);
        }
        crate::surface_rel::lemma_filter_all(cd, keep);
    }
}

// ---------------------------------------------------------------------
// A sub-fetch's actions.
// ---------------------------------------------------------------------

/// The outputs of [`sub_actions`] are its sub-fetch's connection outputs.
pub proof fn lemma_sub_actions_outputs(id: nat, serial: nat, request: u64, hop: nat, actions: Seq<NetAction>)
    ensures
        forall|k: int|
            0 <= k < sub_actions(id, serial, request, hop, actions).1.len() ==> match #[trigger] sub_actions(id, serial, request, hop, actions).1[k] {
                Output::SubConnect { renderer, serial: y, .. } => renderer == id && y == serial,
                Output::SubSend { renderer, serial: y, .. } => renderer == id && y == serial,
                Output::SubClose { renderer, serial: y, .. } => renderer == id && y == serial,
                _ => false,
            },
    decreases actions.len(),
{
    if actions.len() > 0 {
        let rest = actions.drop_first();
        match actions[0] {
            clazel_fetch::transducer::spec::Action::Connect { .. } => lemma_sub_actions_outputs(id, serial, request, hop + 1, rest),
            clazel_fetch::transducer::spec::Action::Send(_) | clazel_fetch::transducer::spec::Action::Close => lemma_sub_actions_outputs(
                id,
                serial,
                request,
                hop,
                rest,
            ),
            _ => {},
        }
        let out = sub_actions(id, serial, request, hop, actions).1;
        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
            Output::SubConnect { renderer, serial: y, .. } => renderer == id && y == serial,
            Output::SubSend { renderer, serial: y, .. } => renderer == id && y == serial,
            Output::SubClose { renderer, serial: y, .. } => renderer == id && y == serial,
            _ => false,
        } by {
            match actions[0] {
                clazel_fetch::transducer::spec::Action::Connect { .. } => {
                    if k > 0 {
                        assert(out[k] == sub_actions(id, serial, request, hop + 1, rest).1[k - 1]);
                    }
                },
                clazel_fetch::transducer::spec::Action::Send(_) | clazel_fetch::transducer::spec::Action::Close => {
                    if k > 0 {
                        assert(out[k] == sub_actions(id, serial, request, hop, rest).1[k - 1]);
                    }
                },
                _ => {},
            }
        }
    }
}

/// Two action lists that differ only in the octets of their `Send`s give
/// the same connection, the same end, and outputs that differ only in the
/// octets of their `SubSend`s (none renderer-bound).
pub proof fn lemma_sub_actions_same_but_sends(id: nat, serial: nat, request: u64, hop: nat, a: Seq<NetAction>, b: Seq<NetAction>)
    requires
        clazel_fetch::transducer::contract::same_but_sends(a, b),
    ensures
        sub_actions(id, serial, request, hop, a).0 == sub_actions(id, serial, request, hop, b).0,
        sub_actions(id, serial, request, hop, a).2 == sub_actions(id, serial, request, hop, b).2,
    decreases a.len(),
{
    if a.len() > 0 {
        let (ra, rb) = (a.drop_first(), b.drop_first());
        assert(clazel_fetch::transducer::contract::same_but_sends(ra, rb)) by {
            assert forall|k: int| 0 <= k < ra.len() implies (#[trigger] ra[k] is Send && rb[k] is Send) || ra[k] == rb[k] by {
                assert(ra[k] == a[k + 1] && rb[k] == b[k + 1]);
            }
        }
        assert((a[0] is Send && b[0] is Send) || a[0] == b[0]);
        match a[0] {
            clazel_fetch::transducer::spec::Action::Connect { .. } => lemma_sub_actions_same_but_sends(id, serial, request, hop + 1, ra, rb),
            _ => lemma_sub_actions_same_but_sends(id, serial, request, hop, ra, rb),
        }
    }
}

/// Every renderer-bound output of a `SubNet` is the `ToRenderer` of its end.
pub proof fn lemma_renderer_outs_sub(out: Seq<Output>, id: nat, serial: nat, request: u64, hop: nat, actions: Seq<NetAction>)
    requires
        out == sub_actions(id, serial, request, hop, actions).1,
    ensures
        crate::noninterference::renderer_outs(out) == Seq::<Output>::empty(),
{
    lemma_sub_actions_outputs(id, serial, request, hop, actions);
    crate::unwind_base::lemma_filter_none(out, |o: Output| crate::noninterference::renderer_bound(o));
}

// ---------------------------------------------------------------------
// A sub-fetch's jar operations.
// ---------------------------------------------------------------------

/// Every operation names the request URL `url`.
pub open spec fn ops_name(ops: Seq<clazel_fetch::transducer::spec::JarOp>, url: clazel_cookie::storage::spec::RequestUrl, now: int) -> bool {
    forall|k: int| 0 <= k < ops.len() ==> match #[trigger] ops[k] {
        clazel_fetch::transducer::spec::JarOp::Retrieved { url: u, now: t, .. } => u == url && t == now,
        clazel_fetch::transducer::spec::JarOp::Stored { url: u, now: t, .. } => u == url && t == now,
    }
}

/// Operations naming a host of another cookie root leave a root's live
/// cookies as they are.
pub proof fn lemma_ops_foreign(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    ops: Seq<clazel_fetch::transducer::spec::JarOp>,
    url: clazel_cookie::storage::spec::RequestUrl,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    other: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        ops_name(ops, url, now),
        url.host == Some(host),
        other != clazel_cookie::storage::spec::cookie_root(rules, host),
        crate::invariant::jar_wf(rules, jar),
        crate::invariant::jar_no_public_suffix(rules, jar),
    ensures
        crate::projection::live_root(rules, apply_net_ops(rules, jar, ops), now, other) == crate::projection::live_root(rules, jar, now, other),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let rest = ops.drop_first();
        assert(ops_name(rest, url, now)) by {
            assert forall|k: int| 0 <= k < rest.len() implies match #[trigger] rest[k] {
                clazel_fetch::transducer::spec::JarOp::Retrieved { url: u, now: t, .. } => u == url && t == now,
                clazel_fetch::transducer::spec::JarOp::Stored { url: u, now: t, .. } => u == url && t == now,
            } by {
                assert(rest[k] == ops[k + 1]);
            }
        }
        let jar1 = apply_net_op(rules, jar, ops[0]);
        crate::net_wf::lemma_apply_net_op_wf(rules, jar, ops[0]);
        match ops[0] {
            clazel_fetch::transducer::spec::JarOp::Retrieved { url: u, ctx, now: t } => {
                crate::projection::lemma_foreign_retrieval(rules, jar, url, ctx, now, host, other);
            },
            clazel_fetch::transducer::spec::JarOp::Stored { line, url: u, ctx, now: t } => {
                if store_allowed(rules, url) {
                    crate::projection::lemma_foreign_store(rules, jar, line, url, ctx, now, host, other);
                }
            },
        }
        lemma_ops_foreign(rules, jar1, rest, url, now, host, other);
    }
}

/// Operations naming a host of `root`, applied to two jars whose live
/// cookies of `root` agree, keep them agreeing.
pub proof fn lemma_ops_agree(
    rules: Seq<clazel_psl::spec::Rule>,
    ja: Seq<clazel_cookie::storage::spec::Cookie>,
    jb: Seq<clazel_cookie::storage::spec::Cookie>,
    ops: Seq<clazel_fetch::transducer::spec::JarOp>,
    url: clazel_cookie::storage::spec::RequestUrl,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        ops_name(ops, url, now),
        url.host == Some(host),
        root == clazel_cookie::storage::spec::cookie_root(rules, host),
        crate::invariant::jar_wf(rules, ja),
        crate::invariant::jar_wf(rules, jb),
        crate::invariant::jar_no_public_suffix(rules, ja),
        crate::invariant::jar_no_public_suffix(rules, jb),
        crate::projection::live_root(rules, ja, now, root) == crate::projection::live_root(rules, jb, now, root),
    ensures
        crate::projection::live_root(rules, apply_net_ops(rules, ja, ops), now, root) == crate::projection::live_root(rules, apply_net_ops(rules, jb, ops), now, root),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let rest = ops.drop_first();
        assert(ops_name(rest, url, now)) by {
            assert forall|k: int| 0 <= k < rest.len() implies match #[trigger] rest[k] {
                clazel_fetch::transducer::spec::JarOp::Retrieved { url: u, now: t, .. } => u == url && t == now,
                clazel_fetch::transducer::spec::JarOp::Stored { url: u, now: t, .. } => u == url && t == now,
            } by {
                assert(rest[k] == ops[k + 1]);
            }
        }
        let ja1 = apply_net_op(rules, ja, ops[0]);
        let jb1 = apply_net_op(rules, jb, ops[0]);
        crate::net_wf::lemma_apply_net_op_wf(rules, ja, ops[0]);
        crate::net_wf::lemma_apply_net_op_wf(rules, jb, ops[0]);
        match ops[0] {
            clazel_fetch::transducer::spec::JarOp::Retrieved { url: u, ctx, now: t } => {
                crate::retrieval_projection::lemma_retrieval_jar_agree(rules, ja, jb, url, ctx, now, host, root);
            },
            clazel_fetch::transducer::spec::JarOp::Stored { line, url: u, ctx, now: t } => {
                if store_allowed(rules, url) {
                    crate::store_projection::lemma_store_agree(rules, ja, jb, line, url, ctx, now, host, root);
                }
            },
        }
        lemma_ops_agree(rules, ja1, jb1, rest, url, now, host, root);
    }
}

// ---------------------------------------------------------------------
// The step's facts for `SubNet`.
// ---------------------------------------------------------------------

/// A `SubNet` keeps the state well formed: it changes only the sub-fetch
/// table and, for a credentialed request, the jar by the transducer's jar
/// operations.
pub proof fn lemma_sub_net_wf(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, renderer: nat, serial: nat, hop: nat, input: NetInput)
    requires
        crate::invariant::kernel_wf(rules, urls, s),
    ensures
        crate::invariant::kernel_wf(rules, urls, sub_net(rules, fetch, s, renderer, serial, hop, input).0),
{
    if let Some(f) = subnet_target(s, renderer, serial) {
        if subfetch_live(s, f) && hop != 0 && f.hop == hop {
            let ops = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, subfetch_jar(fetch, s, f), s.now).2;
            crate::net_wf::lemma_apply_net_ops_wf(rules, s.jar, ops);
        }
    }
}

/// `Resize`, `Input` and `SubNet` change no connection of a navigation and
/// name none.
pub proof fn lemma_subfetch_events_own_none(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, e: Event)
    requires
        e is Resize || e is Input || e is SubNet || e is Tick,
    ensures
        crate::net_theorems::own_none(s, step(rules, urls, fetch, s, e).0, step(rules, urls, fetch, s, e).1),
{
    let (s1, out) = step(rules, urls, fetch, s, e);
    match e {
        Event::Tick { time } => {
            lemma_tick_all_shape(s, time);
        },
        Event::SubNet { renderer, serial, hop, input } => {
            if let Some(f) = subnet_target(s, renderer, serial) {
                if subfetch_live(s, f) && hop != 0 && f.hop == hop {
                    let actions = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, subfetch_jar(fetch, s, f), s.now).1;
                    let (h, o, end) = sub_actions(renderer, serial, f.request, hop, actions);
                    lemma_sub_actions_outputs(renderer, serial, f.request, hop, actions);
                    assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Connect || out[k] is Send || out[k] is Close) by {
                        if k < o.len() {
                            assert(out[k] == o[k]);
                        }
                    }
                }
            }
        },
        Event::Resize { tab, .. } => {
            assert forall|k: int| 0 <= k < out.len() implies !((#[trigger] out[k]) is Connect || out[k] is Send || out[k] is Close) by {
                if find_by_tab(s.renderers, tab, 0) is Some {
                    assert(k == 0 || k == 1);
                }
            }
        },
        _ => {},
    }
}

/// Every output of `out` is a `ToRenderer` to `x` or a sub-fetch connection
/// output of `x`.
pub open spec fn outputs_of(out: Seq<Output>, x: nat) -> bool {
    forall|k: int|
        0 <= k < out.len() ==> match #[trigger] out[k] {
            Output::ToRenderer { id, .. } => id == x,
            Output::SubConnect { renderer, .. } => renderer == x,
            Output::SubSend { renderer, .. } => renderer == x,
            Output::SubClose { renderer, .. } => renderer == x,
            _ => false,
        }
}

/// [`outputs_of`] of a concatenation.
pub proof fn lemma_outputs_of_concat(a: Seq<Output>, b: Seq<Output>, x: nat)
    requires
        outputs_of(a, x),
        outputs_of(b, x),
    ensures
        outputs_of(a + b, x),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies match #[trigger] (a + b)[k] {
        Output::ToRenderer { id, .. } => id == x,
        Output::SubConnect { renderer, .. } => renderer == x,
        Output::SubSend { renderer, .. } => renderer == x,
        Output::SubClose { renderer, .. } => renderer == x,
        _ => false,
    } by {
        if k < a.len() {
            assert((a + b)[k] == a[k]);
        } else {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// [`sub_actions`]'s outputs are its renderer's.
pub proof fn lemma_sub_actions_of(id: nat, serial: nat, request: u64, hop: nat, actions: Seq<NetAction>)
    ensures
        outputs_of(sub_actions(id, serial, request, hop, actions).1, id),
{
    lemma_sub_actions_outputs(id, serial, request, hop, actions);
}

/// What a `FetchStyle` changes and sends: only the sub-fetch table and
/// counts, and only to its sender.
pub proof fn lemma_fetch_style_shape(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, s: State, r: Renderer, request: u64, url: Seq<u8>)
    ensures
        ({
            let (s1, out) = fetch_style(rules, urls, fetch, s, r, request, url);
            &&& s1 == State { subfetches: s1.subfetches, subcounts: s1.subcounts, ..s }
            &&& outputs_of(out, r.id)
        }),
{
    let (s1, out) = fetch_style(rules, urls, fetch, s, r, request, url);
    assert(outputs_of(reply(r, clazel_ipc::message::spec::Message::StyleFailed { request }), r.id));
    if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
        if let Some(resolved) = (urls.resolve)(r.url, relative) {
            if let Some(parsed) = (fetch.parse)(resolved) {
                let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
                let actions = clazel_fetch::transducer::spec::start(parsed).1;
                let (hop, o, end) = sub_actions(r.id, serial, request, 0, actions);
                lemma_sub_actions_of(r.id, serial, request, 0, actions);
                if let Some(frames) = end {
                    lemma_outputs_of_concat(o, seq![Output::ToRenderer { id: r.id, bytes: frames }], r.id);
                }
            }
        }
    }
}

/// What a `SubNet` changes and sends: only the sub-fetch table and the jar,
/// and only to the renderer it is about.
pub proof fn lemma_sub_net_shape(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns, s: State, renderer: nat, serial: nat, hop: nat, input: NetInput)
    ensures
        ({
            let (s1, out) = sub_net(rules, fetch, s, renderer, serial, hop, input);
            &&& s1 == State { subfetches: s1.subfetches, jar: s1.jar, ..s }
            &&& outputs_of(out, renderer)
        }),
{
    lemma_subnet_target_key(s, renderer, serial);
    if let Some(f) = subnet_target(s, renderer, serial) {
        if subfetch_live(s, f) && hop != 0 && f.hop == hop {
            let actions = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, subfetch_jar(fetch, s, f), s.now).1;
            let (h, o, end) = sub_actions(renderer, serial, f.request, hop, actions);
            lemma_sub_actions_of(renderer, serial, f.request, hop, actions);
            if let Some(frames) = end {
                lemma_outputs_of_concat(o, seq![Output::ToRenderer { id: renderer, bytes: frames }], renderer);
            }
        }
    }
}

/// Every output of [`sweep`] is a `SubClose` or the `StyleFailed` of a live
/// sub-fetch of the table, to its renderer.
pub open spec fn sweep_outputs_ok(s: State, fs: Seq<SubFetch>, out: Seq<Output>) -> bool {
    forall|k: int|
        0 <= k < out.len() ==> match #[trigger] out[k] {
            Output::SubClose { renderer, .. } => exists|j: int| 0 <= j < fs.len() && fs[j].renderer == renderer,
            Output::ToRenderer { id, bytes } => exists|j: int|
                0 <= j < fs.len() && fs[j].renderer == id && subfetch_live(s, fs[j]) && bytes == style_failed_frame(fs[j].request),
            _ => false,
        }
}

/// [`sweep`]'s outputs.
pub proof fn lemma_sweep_shape(s: State, fs: Seq<SubFetch>)
    ensures
        sweep_outputs_ok(s, fs, sweep(s, fs).1),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let f = fs[0];
        let t = fs.drop_first();
        lemma_sweep_shape(s, t);
        let (rest, o) = sweep(s, t);
        let out = sweep(s, fs).1;
        let close = if f.hop > 0 { seq![Output::SubClose { renderer: f.renderer, serial: f.serial, hop: f.hop }] } else { Seq::<Output>::empty() };
        let failed = seq![Output::ToRenderer { id: f.renderer, bytes: style_failed_frame(f.request) }];
        assert forall|k: int| 0 <= k < out.len() implies match #[trigger] out[k] {
            Output::SubClose { renderer, .. } => exists|j: int| 0 <= j < fs.len() && fs[j].renderer == renderer,
            Output::ToRenderer { id, bytes } => exists|j: int|
                0 <= j < fs.len() && fs[j].renderer == id && subfetch_live(s, fs[j]) && bytes == style_failed_frame(fs[j].request),
            _ => false,
        } by {
            let pre = if !subfetch_live(s, f) {
                close
            } else if s.now >= f.started + subfetch_timeout() {
                close + failed
            } else {
                Seq::<Output>::empty()
            };
            assert(out == pre + o);
            if k < pre.len() {
                assert(out[k] == pre[k]);
                assert(fs[0] == f);
            } else {
                assert(out[k] == o[k - pre.len()]);
                match out[k] {
                    Output::SubClose { renderer, .. } => {
                        let j = choose|j: int| 0 <= j < t.len() && t[j].renderer == renderer;
                        assert(fs[j + 1] == t[j]);
                    },
                    Output::ToRenderer { id, bytes } => {
                        let j = choose|j: int| 0 <= j < t.len() && t[j].renderer == id && subfetch_live(s, t[j]) && bytes == style_failed_frame(t[j].request);
                        assert(fs[j + 1] == t[j]);
                    },
                    _ => {},
                }
            }
        }
    }
}

/// A `Tick` changes the sub-fetch table, the jar and the time, and sends
/// only [`sweep`]'s outputs.
pub proof fn lemma_tick_all_shape(s: State, time: int)
    ensures
        ({
            let (s1, out) = tick_all(s, time);
            let t = tick(s, time).0;
            &&& s1 == State { subfetches: s1.subfetches, ..t }
            &&& t == State { jar: t.jar, now: t.now, ..s }
            &&& sweep_outputs_ok(t, s.subfetches, out)
        }),
{
    let t = tick(s, time).0;
    lemma_sweep_shape(t, t.subfetches);
}

// ---------------------------------------------------------------------
// Noninterference over `SubNet`.
// ---------------------------------------------------------------------

/// The state a live `SubNet` leaves, given the transducer step it took.
pub open spec fn sub_net_after(rules: Seq<clazel_psl::spec::Rule>, fetch: FetchFns, s: State, f: SubFetch, renderer: nat, serial: nat, hop: nat, input: NetInput) -> (
    Seq<SubFetch>,
    Seq<clazel_cookie::storage::spec::Cookie>,
) {
    let cred = credentialed(fetch, f.lock, f.fetch.url);
    let (fs, actions, ops) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, subfetch_jar(fetch, s, f), s.now);
    let (h, out, end) = sub_actions(renderer, serial, f.request, hop, actions);
    (sub_finish(s.subfetches, SubFetch { fetch: fs, hop: h, ..f }, out, end).0, if cred { apply_net_ops(rules, s.jar, ops) } else { s.jar })
}

/// A `SubNet` of a renderer of `d`: related states, and the same
/// renderer-bound outputs in both runs.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_d_subnet(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    renderer: nat,
    serial: nat,
    hop: nat,
    input: NetInput,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        crate::domain::event_domain(rules, s1, Event::SubNet { renderer, serial, hop, input }) == Some(d),
    ensures
        crate::noninterference::renderer_outs(step(rules, urls, fetch, s1, Event::SubNet { renderer, serial, hop, input }).1)
            == crate::noninterference::renderer_outs(step(rules, urls, fetch, s2, Event::SubNet { renderer, serial, hop, input }).1),
        crate::noninterference::rel(
            rules,
            urls,
            d,
            step(rules, urls, fetch, s1, Event::SubNet { renderer, serial, hop, input }).0,
            step(rules, urls, fetch, s2, Event::SubNet { renderer, serial, hop, input }).0,
        ),
{
    let e = Event::SubNet { renderer, serial, hop, input };
    let bytes = Seq::<u8>::empty();
    assert(crate::domain::event_domain(rules, s1, Event::FromRenderer { id: renderer, bytes }) == Some(d));
    crate::unwinding_d::lemma_d_sender(rules, urls, d, s1, s2, renderer, bytes);
    let i1 = find_by_id(s1.renderers, renderer, 0)->Some_0;
    let i2 = find_by_id(s2.renderers, renderer, 0)->Some_0;
    let r = s1.renderers[i1];
    assert(s2.renderers[i2] == r);
    lemma_subfetch_of_domain(rules, s1.subfetches, renderer, r.lock, serial, d);
    lemma_subfetch_of_domain(rules, s2.subfetches, renderer, r.lock, serial, d);
    assert(subnet_target(s1, renderer, serial) == subnet_target(s2, renderer, serial));
    let (s1b, o1) = step(rules, urls, fetch, s1, e);
    let (s2b, o2) = step(rules, urls, fetch, s2, e);
    lemma_subnet_target_key(s1, renderer, serial);
    match subnet_target(s1, renderer, serial) {
        None => {},
        Some(f) => {
            lemma_live_agree(rules, urls, d, s1, s2, f);
            assert(subfetch_live(s1, f) == subfetch_live(s2, f));
            if subfetch_live(s1, f) && hop != 0 && f.hop == hop {
                crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
                crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s2, e);
                let cred = credentialed(fetch, f.lock, f.fetch.url);
                let ja = subfetch_jar(fetch, s1, f);
                let jb = subfetch_jar(fetch, s2, f);
                clazel_fetch::transducer::theorems::theorem_jar_only_in_sends(fetch.http, fetch.urls, f.fetch, input, ja, jb, s1.now);
                clazel_fetch::transducer::theorems::theorem_ops_name_request(fetch.http, fetch.urls, f.fetch, input, ja, s1.now);
                let (fsa, aa, opsa) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, ja, s1.now);
                let (fsb, ab, opsb) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, jb, s2.now);
                lemma_sub_actions_same_but_sends(renderer, serial, f.request, hop, aa, ab);
                let (ha, outa, enda) = sub_actions(renderer, serial, f.request, hop, aa);
                let (hb, outb, endb) = sub_actions(renderer, serial, f.request, hop, ab);
                lemma_renderer_outs_sub(outa, renderer, serial, f.request, hop, aa);
                lemma_renderer_outs_sub(outb, renderer, serial, f.request, hop, ab);
                let g = SubFetch { fetch: fsa, hop: ha, ..f };
                if let Some(frames) = enda {
                    crate::net_rel::lemma_renderer_outs_concat(outa, seq![Output::ToRenderer { id: renderer, bytes: frames }]);
                    crate::net_rel::lemma_renderer_outs_concat(outb, seq![Output::ToRenderer { id: renderer, bytes: frames }]);
                    lemma_drop_domain(rules, s1.subfetches, g, d);
                    lemma_drop_domain(rules, s2.subfetches, g, d);
                } else {
                    lemma_replace_domain(rules, s1.subfetches, g, d);
                    lemma_replace_domain(rules, s2.subfetches, g, d);
                }
                // The jar: a credentialed request names the lock's host, in `d`'s root.
                if cred {
                    if let crate::domain::Domain::Root(root) = d {
                        let url = (fetch.urls.request_url)(f.fetch.url);
                        assert(r.lock is Tuple);
                        let h = lock_host(r.lock)->Some_0;
                        crate::unwinding_d::lemma_domain_of_tuple(rules, urls, s1, i1, d);
                        assert(url.host == Some(h));
                        assert(ops_name(opsa, url, s1.now)) by {
                            assert forall|k: int| 0 <= k < opsa.len() implies match #[trigger] opsa[k] {
                                clazel_fetch::transducer::spec::JarOp::Retrieved { url: u, now: t, .. } => u == url && t == s1.now,
                                clazel_fetch::transducer::spec::JarOp::Stored { url: u, now: t, .. } => u == url && t == s1.now,
                            } by {
                                match opsa[k] {
                                    clazel_fetch::transducer::spec::JarOp::Retrieved { .. } => {},
                                    clazel_fetch::transducer::spec::JarOp::Stored { .. } => {},
                                }
                            }
                        }
                        lemma_ops_agree(rules, s1.jar, s2.jar, opsa, url, s1.now, h, root);
                    }
                }
                crate::net_rel::lemma_rel_conn_ext(s1, s2, s1b, s2b);
                assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
                    let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
                }
                crate::unwinding::lemma_rel_from_sets(rules, urls, d, s1b, s2b);
            }
        },
    }
}

/// The outputs of a `SubNet` of renderer `s1.renderers[i1]`, of another
/// domain than `d`, are addressed to none of `d`'s.
#[verifier::spinoff_prover]
pub proof fn lemma_subnet_not_d(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s1: State,
    renderer: nat,
    serial: nat,
    hop: nat,
    input: NetInput,
    i1: int,
)
    requires
        crate::invariant::renderers_wf(urls, s1.renderers, s1.next_id),
        0 <= i1 < s1.renderers.len(),
        s1.renderers[i1].id == renderer,
        crate::domain::domain_of_renderer(rules, s1.renderers[i1]) != d,
    ensures
        ({
            let (s1b, out1) = step(rules, urls, fetch, s1, Event::SubNet { renderer, serial, hop, input });
            crate::noninterference::outputs_for(rules, d, s1, s1b, out1) == Seq::<Output>::empty()
        }),
{
    let r = s1.renderers[i1];
    let (s1b, out1) = step(rules, urls, fetch, s1, Event::SubNet { renderer, serial, hop, input });
    lemma_sub_net_shape(rules, fetch, s1, renderer, serial, hop, input);
    assert(s1.renderers.contains(r));
    assert forall|k: int| 0 <= k < out1.len() implies !crate::noninterference::addressed_to(rules, d, s1, s1b, #[trigger] out1[k]) by {
        if crate::noninterference::addressed_to(rules, d, s1, s1b, out1[k]) {
            let q = choose|q: Renderer|
                (s1.renderers.contains(q) || s1b.renderers.contains(q)) && (if out1[k] is Show || out1[k] is Paint {
                    q.tab == crate::domain::output_id(out1[k])
                } else {
                    q.id == crate::domain::output_id(out1[k])
                }) && crate::domain::domain_of_renderer(rules, q) == d;
            crate::unwind_base::lemma_same_id_same_renderer(urls, s1.renderers, s1.next_id, q, r);
        }
    }
    crate::unwind_base::lemma_filter_none(out1, |o: Output| crate::noninterference::addressed_to(rules, d, s1, s1b, o));
}

/// A `SubNet` of a renderer of another domain: nothing is sent to `d`, and
/// the state stays related to the other run's.
#[verifier::spinoff_prover]
#[verifier::rlimit(60)]
pub proof fn lemma_local_respect_subnet(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, e: Event)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        e is SubNet,
        crate::domain::event_domain(rules, s1, e) matches Some(d2) && d2 != d,
    ensures
        crate::noninterference::local_respect_statement(rules, urls, fetch, d, s1, s2, e),
{
    let renderer = e->SubNet_renderer;
    let serial = e->SubNet_serial;
    let hop = e->SubNet_hop;
    let input = e->SubNet_input;
    assert(e == (Event::SubNet { renderer, serial, hop, input }));
    let d2 = crate::domain::event_domain(rules, s1, e)->Some_0;
    let bytes = Seq::<u8>::empty();
    assert(crate::domain::event_domain(rules, s1, Event::FromRenderer { id: renderer, bytes }) == Some(d2));
    crate::unwinding_b::lemma_b_sender(rules, urls, d, s1, s2, renderer, bytes, d2);
    let i1 = find_by_id(s1.renderers, renderer, 0)->Some_0;
    let r = s1.renderers[i1];
    let (s1b, out1) = step(rules, urls, fetch, s1, e);
    lemma_subnet_not_d(rules, urls, fetch, d, s1, renderer, serial, hop, input, i1);
    lemma_subnet_target_key(s1, renderer, serial);
    if !(subnet_target(s1, renderer, serial) matches Some(f) && subfetch_live(s1, f) && hop != 0 && f.hop == hop) {
        assert(s1b == s1);
    }
    if let Some(f) = subnet_target(s1, renderer, serial) {
        if subfetch_live(s1, f) && hop != 0 && f.hop == hop {
            crate::invariant::lemma_step_preserves_wf(rules, urls, fetch, s1, e);
            let ja = subfetch_jar(fetch, s1, f);
            let (fsa, aa, opsa) = clazel_fetch::transducer::spec::step(fetch.http, fetch.urls, f.fetch, input, ja, s1.now);
            let (ha, outa, enda) = sub_actions(renderer, serial, f.request, hop, aa);
            lemma_sub_actions_outputs(renderer, serial, f.request, hop, aa);
            // `f` is `r`'s: its lock is `r`'s, of `d2`.
            crate::invariant::lemma_find_by_id(s1.renderers, renderer, 0);
            assert(f.lock == r.lock);
            assert(s1.renderers.contains(r));
            let g = SubFetch { fetch: fsa, hop: ha, ..f };
            if enda is Some {
                lemma_drop_domain(rules, s1.subfetches, g, d);
            } else {
                lemma_replace_domain(rules, s1.subfetches, g, d);
            }
            if credentialed(fetch, f.lock, f.fetch.url) {
                if let crate::domain::Domain::Root(root) = d {
                    clazel_fetch::transducer::theorems::theorem_ops_name_request(fetch.http, fetch.urls, f.fetch, input, ja, s1.now);
                    let url = (fetch.urls.request_url)(f.fetch.url);
                    assert(r.lock is Tuple);
                    crate::unwinding_d::lemma_domain_of_tuple(rules, urls, s1, i1, d2);
                    let h = lock_host(r.lock)->Some_0;
                    assert(url.host == Some(h));
                    assert(ops_name(opsa, url, s1.now)) by {
                        assert forall|k: int| 0 <= k < opsa.len() implies match #[trigger] opsa[k] {
                            clazel_fetch::transducer::spec::JarOp::Retrieved { url: u, now: t, .. } => u == url && t == s1.now,
                            clazel_fetch::transducer::spec::JarOp::Stored { url: u, now: t, .. } => u == url && t == s1.now,
                        } by {
                            match opsa[k] {
                                clazel_fetch::transducer::spec::JarOp::Retrieved { .. } => {},
                                clazel_fetch::transducer::spec::JarOp::Stored { .. } => {},
                            }
                        }
                    }
                    assert(root != clazel_cookie::storage::spec::cookie_root(rules, h));
                    lemma_ops_foreign(rules, s1.jar, opsa, url, s1.now, h, root);
                }
            }
            crate::net_rel::lemma_rel_conn_ext(s1, s2, s1b, s2);
            assert forall|x: Renderer| s1b.renderers.contains(x) implies s2.renderers.contains(x) by {
                let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
            }
            crate::unwinding::lemma_rel_from_sets(rules, urls, d, s1b, s2);
        }
    }
}

// ---------------------------------------------------------------------
// Noninterference over `FetchStyle`.
// ---------------------------------------------------------------------

/// A key of `d`'s is counted live the same in the table and in `d`'s part.
pub proof fn lemma_live_domain(rules: Seq<clazel_psl::spec::Rule>, fs: Seq<SubFetch>, id: nat, lock: clazel_origin::spec::Origin, d: crate::domain::Domain)
    requires
        crate::domain::domain_of_lock(rules, lock) == d,
    ensures
        live_subfetches(fs, id, lock) == live_subfetches(crate::domain::subfetches_of_domain(rules, fs, d), id, lock),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs =~= seq![x] + t);
        lemma_sub_prepend(rules, x, t, d);
        lemma_live_domain(rules, t, id, lock, d);
        let ft = crate::domain::subfetches_of_domain(rules, t, d);
        if crate::domain::domain_of_lock(rules, x.lock) == d {
            assert((seq![x] + ft)[0] == x);
            assert((seq![x] + ft).drop_first() =~= ft);
        }
    } else {
        reveal(Seq::filter);
    }
}

/// A `FetchStyle` of a renderer of `d`, in two runs whose sub-fetches and
/// counts of `d` agree, at the same time: the same outputs, and the tables
/// of `d` still agree.
pub proof fn lemma_fetch_style_domain(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    fetch: FetchFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    r: Renderer,
    request: u64,
    url: Seq<u8>,
)
    requires
        crate::domain::domain_of_renderer(rules, r) == d,
        crate::domain::subfetches_of_domain(rules, s1.subfetches, d) == crate::domain::subfetches_of_domain(rules, s2.subfetches, d),
        crate::domain::subcounts_of_domain(rules, s1.subcounts, d) == crate::domain::subcounts_of_domain(rules, s2.subcounts, d),
        s1.now == s2.now,
    ensures
        fetch_style(rules, urls, fetch, s1, r, request, url).1 == fetch_style(rules, urls, fetch, s2, r, request, url).1,
        crate::domain::subfetches_of_domain(rules, fetch_style(rules, urls, fetch, s1, r, request, url).0.subfetches, d)
            == crate::domain::subfetches_of_domain(rules, fetch_style(rules, urls, fetch, s2, r, request, url).0.subfetches, d),
        crate::domain::subcounts_of_domain(rules, fetch_style(rules, urls, fetch, s1, r, request, url).0.subcounts, d)
            == crate::domain::subcounts_of_domain(rules, fetch_style(rules, urls, fetch, s2, r, request, url).0.subcounts, d),
{
    lemma_live_domain(rules, s1.subfetches, r.id, r.lock, d);
    lemma_live_domain(rules, s2.subfetches, r.id, r.lock, d);
    lemma_subcount_of_domain(rules, s1.subcounts, r.id, r.lock, d);
    lemma_subcount_of_domain(rules, s2.subcounts, r.id, r.lock, d);
    let (serial, in_document) = subcount_of(s1.subcounts, r.id, r.lock);
    lemma_set_subcount_domain(rules, s1.subcounts, s2.subcounts, r.id, r.lock, serial + 1, in_document + 1, d);
    if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
        if let Some(resolved) = (urls.resolve)(r.url, relative) {
            if let Some(parsed) = (fetch.parse)(resolved) {
                let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                let (hop, o, end) = sub_actions(r.id, serial, request, 0, actions);
                let f = SubFetch {
                    renderer: r.id,
                    lock: r.lock,
                    serial,
                    request,
                    tab: r.tab,
                    fetch: fs,
                    hop,
                    started: s1.now,
                    partition: crate::domain::domain_of_renderer(rules, r),
                    ended: false,
                };
                lemma_push_domain(rules, s1.subfetches, f, d);
                lemma_push_domain(rules, s2.subfetches, f, d);
            }
        }
    }
}

/// A `FetchStyle` of a renderer of another domain leaves `d`'s tables as
/// they are.
pub proof fn lemma_fetch_style_other(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s: State, r: Renderer, request: u64, url: Seq<u8>)
    requires
        crate::domain::domain_of_renderer(rules, r) != d,
    ensures
        crate::domain::subfetches_of_domain(rules, fetch_style(rules, urls, fetch, s, r, request, url).0.subfetches, d)
            == crate::domain::subfetches_of_domain(rules, s.subfetches, d),
        crate::domain::subcounts_of_domain(rules, fetch_style(rules, urls, fetch, s, r, request, url).0.subcounts, d)
            == crate::domain::subcounts_of_domain(rules, s.subcounts, d),
{
    let (serial, in_document) = subcount_of(s.subcounts, r.id, r.lock);
    lemma_set_subcount_domain(rules, s.subcounts, s.subcounts, r.id, r.lock, serial + 1, in_document + 1, d);
    if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
        if let Some(resolved) = (urls.resolve)(r.url, relative) {
            if let Some(parsed) = (fetch.parse)(resolved) {
                let (fs, actions) = clazel_fetch::transducer::spec::start(parsed);
                let (hop, o, end) = sub_actions(r.id, serial, request, 0, actions);
                let f = SubFetch {
                    renderer: r.id,
                    lock: r.lock,
                    serial,
                    request,
                    tab: r.tab,
                    fetch: fs,
                    hop,
                    started: s.now,
                    partition: crate::domain::domain_of_renderer(rules, r),
                    ended: false,
                };
                lemma_push_domain(rules, s.subfetches, f, d);
            }
        }
    }
}

// ---------------------------------------------------------------------
// Noninterference over `Tick`.
// ---------------------------------------------------------------------

/// Whether a `Tick` keeps sub-fetch `f`: live, and not yet timed out.
pub open spec fn kept_at(s: State, f: SubFetch) -> bool {
    subfetch_live(s, f) && !(s.now >= f.started + subfetch_timeout())
}

/// [`sweep`]'s table is the table filtered by [`kept_at`].
pub proof fn lemma_sweep_kept(s: State, fs: Seq<SubFetch>)
    ensures
        sweep(s, fs).0 == fs.filter(|f: SubFetch| kept_at(s, f)),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs =~= seq![x] + t);
        lemma_sweep_kept(s, t);
        t.lemma_filter_prepend(x, |f: SubFetch| kept_at(s, f));
    } else {
        reveal(Seq::filter);
    }
}

/// A sub-fetch of `d` is live in both related states, or in neither.
pub proof fn lemma_live_agree(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, t1: State, t2: State, f: SubFetch)
    requires
        crate::noninterference::rel(rules, urls, d, t1, t2),
        crate::domain::domain_of_lock(rules, f.lock) == d,
    ensures
        subfetch_live(t1, f) == subfetch_live(t2, f),
{
    crate::unwind_base::lemma_found_contained(t1, f.renderer);
    crate::unwind_base::lemma_found_contained(t2, f.renderer);
    if let Some(i1) = find_by_id(t1.renderers, f.renderer, 0) {
        let x = t1.renderers[i1];
        assert(t2.renderers.contains(x));
        crate::unwind_base::lemma_find_contained(urls, t2, x);
    } else if let Some(i2) = find_by_id(t2.renderers, f.renderer, 0) {
        let y = t2.renderers[i2];
        if y.lock == f.lock {
            assert(crate::domain::domain_of_renderer(rules, y) == d);
            assert(t1.renderers.contains(y));
            crate::unwind_base::lemma_find_contained(urls, t1, y);
        }
    }
}

/// Two sequences whose elements two predicates agree on filter the same.
pub proof fn lemma_filter_agree<A>(s: Seq<A>, p: spec_fn(A) -> bool, q: spec_fn(A) -> bool)
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
            assert(t[i] == s[i]);
        }
        lemma_filter_agree(t, p, q);
        assert(p(s[s.len() - 1]) == q(s[s.len() - 1]));
    }
}

/// The `StyleFailed`s a `Tick` sends to `d`'s renderers: for each sub-fetch
/// of `d` that is live and timed out, in order.
pub open spec fn d_failures(rules: Seq<clazel_psl::spec::Rule>, s: State, fs: Seq<SubFetch>, d: crate::domain::Domain) -> Seq<Output>
    decreases fs.len(),
{
    if fs.len() == 0 {
        seq![]
    } else {
        let f = fs[0];
        (if crate::domain::domain_of_lock(rules, f.lock) == d && subfetch_live(s, f) && s.now >= f.started + subfetch_timeout() {
            seq![Output::ToRenderer { id: f.renderer, bytes: style_failed_frame(f.request) }]
        } else {
            seq![]
        }) + d_failures(rules, s, fs.drop_first(), d)
    }
}

/// [`d_failures`] reads only `d`'s part of the table.
pub proof fn lemma_d_failures_domain(rules: Seq<clazel_psl::spec::Rule>, s: State, fs: Seq<SubFetch>, d: crate::domain::Domain)
    ensures
        d_failures(rules, s, fs, d) == d_failures(rules, s, crate::domain::subfetches_of_domain(rules, fs, d), d),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let x = fs[0];
        let t = fs.drop_first();
        assert(fs =~= seq![x] + t);
        lemma_sub_prepend(rules, x, t, d);
        lemma_d_failures_domain(rules, s, t, d);
        let ft = crate::domain::subfetches_of_domain(rules, t, d);
        if crate::domain::domain_of_lock(rules, x.lock) == d {
            assert((seq![x] + ft)[0] == x);
            assert((seq![x] + ft).drop_first() =~= ft);
        } else {
            assert(d_failures(rules, s, fs, d) =~= d_failures(rules, s, t, d));
        }
    } else {
        reveal(Seq::filter);
    }
}

/// [`d_failures`] of `d`'s sub-fetches is the same in related states.
pub proof fn lemma_d_failures_agree(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, t1: State, t2: State, fs: Seq<SubFetch>)
    requires
        crate::noninterference::rel(rules, urls, d, t1, t2),
        forall|i: int| 0 <= i < fs.len() ==> crate::domain::domain_of_lock(rules, (#[trigger] fs[i]).lock) == d,
    ensures
        d_failures(rules, t1, fs, d) == d_failures(rules, t2, fs, d),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let t = fs.drop_first();
        assert forall|i: int| 0 <= i < t.len() implies crate::domain::domain_of_lock(rules, (#[trigger] t[i]).lock) == d by {
            assert(t[i] == fs[i + 1]);
        }
        lemma_d_failures_agree(rules, urls, d, t1, t2, t);
        lemma_live_agree(rules, urls, d, t1, t2, fs[0]);
    }
}

/// What a `Tick`'s sweep sends to `d` is [`d_failures`].
#[verifier::spinoff_prover]
pub proof fn lemma_sweep_outputs_for(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s: State, sb: State, t: State, fs: Seq<SubFetch>)
    requires
        crate::invariant::renderers_wf(urls, t.renderers, t.next_id),
        s.renderers == t.renderers,
        sb.renderers == t.renderers,
    ensures
        crate::noninterference::outputs_for(rules, d, s, sb, sweep(t, fs).1) == d_failures(rules, t, fs, d),
    decreases fs.len(),
{
    let ad = |o: Output| crate::noninterference::addressed_to(rules, d, s, sb, o);
    if fs.len() > 0 {
        let f = fs[0];
        let rest = fs.drop_first();
        lemma_sweep_outputs_for(rules, urls, d, s, sb, t, rest);
        let o = sweep(t, rest).1;
        let close = if f.hop > 0 { seq![Output::SubClose { renderer: f.renderer, serial: f.serial, hop: f.hop }] } else { Seq::<Output>::empty() };
        let failed = seq![Output::ToRenderer { id: f.renderer, bytes: style_failed_frame(f.request) }];
        let pre = if !subfetch_live(t, f) {
            close
        } else if t.now >= f.started + subfetch_timeout() {
            close + failed
        } else {
            Seq::<Output>::empty()
        };
        assert(sweep(t, fs).1 == pre + o);
        Seq::filter_distributes_over_add(pre, o, ad);
        crate::unwind_base::lemma_filter_none(close, ad);
        if subfetch_live(t, f) && t.now >= f.started + subfetch_timeout() {
            Seq::filter_distributes_over_add(close, failed, ad);
            crate::unwind_base::lemma_found_contained(t, f.renderer);
            let i = find_by_id(t.renderers, f.renderer, 0)->Some_0;
            let x = t.renderers[i];
            assert(x.lock == f.lock && x.id == f.renderer);
            if crate::domain::domain_of_lock(rules, f.lock) == d {
                assert(ad(failed[0])) by {
                    assert(s.renderers.contains(x));
                    assert(crate::domain::domain_of_renderer(rules, x) == d);
                    assert(crate::domain::output_id(failed[0]) == x.id);
                }
                crate::surface_rel::lemma_filter_all(failed, ad);
            } else {
                assert(!ad(failed[0])) by {
                    if ad(failed[0]) {
                        let q = choose|q: Renderer|
                            (s.renderers.contains(q) || sb.renderers.contains(q)) && q.id == f.renderer && crate::domain::domain_of_renderer(rules, q) == d;
                        crate::unwind_base::lemma_same_id_same_renderer(urls, t.renderers, t.next_id, q, x);
                    }
                }
                crate::unwind_base::lemma_filter_none(failed, ad);
            }
        }
    } else {
        reveal(Seq::filter);
    }
}

/// `Tick` from related states: related states, and the same outputs to
/// `d`.
#[verifier::spinoff_prover]
pub proof fn lemma_tick_all_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, fetch: FetchFns, d: crate::domain::Domain, s1: State, s2: State, time: int)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        crate::noninterference::rel(rules, urls, d, tick_all(s1, time).0, tick_all(s2, time).0),
        crate::noninterference::outputs_for(rules, d, s1, tick_all(s1, time).0, tick_all(s1, time).1) == crate::noninterference::outputs_for(
            rules,
            d,
            s2,
            tick_all(s2, time).0,
            tick_all(s2, time).1,
        ),
{
    crate::unwinding::lemma_tick_consistency(rules, urls, fetch, d, s1, s2, time);
    let t1 = tick(s1, time).0;
    let t2 = tick(s2, time).0;
    let (s1b, o1) = tick_all(s1, time);
    let (s2b, o2) = tick_all(s2, time);
    // The outputs.
    lemma_sweep_outputs_for(rules, urls, d, s1, s1b, t1, t1.subfetches);
    lemma_sweep_outputs_for(rules, urls, d, s2, s2b, t2, t2.subfetches);
    lemma_d_failures_domain(rules, t1, t1.subfetches, d);
    lemma_d_failures_domain(rules, t2, t2.subfetches, d);
    let fd = crate::domain::subfetches_of_domain(rules, t1.subfetches, d);
    assert forall|i: int| 0 <= i < fd.len() implies crate::domain::domain_of_lock(rules, (#[trigger] fd[i]).lock) == d by {
        t1.subfetches.lemma_filter_pred(|x: SubFetch| crate::domain::domain_of_lock(rules, x.lock) == d, i);
    }
    lemma_d_failures_agree(rules, urls, d, t1, t2, fd);
    // The table.
    let ind = |x: SubFetch| crate::domain::domain_of_lock(rules, x.lock) == d;
    let k1 = |f: SubFetch| kept_at(t1, f);
    let k2 = |f: SubFetch| kept_at(t2, f);
    lemma_sweep_kept(t1, t1.subfetches);
    lemma_sweep_kept(t2, t2.subfetches);
    crate::surface_rel::lemma_filter_commute(t1.subfetches, k1, ind);
    crate::surface_rel::lemma_filter_commute(t2.subfetches, k2, ind);
    assert forall|i: int| 0 <= i < fd.len() implies k1(#[trigger] fd[i]) == k2(fd[i]) by {
        lemma_live_agree(rules, urls, d, t1, t2, fd[i]);
    }
    lemma_filter_agree(fd, k1, k2);
    crate::net_rel::lemma_rel_conn_ext(t1, t2, s1b, s2b);
    assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
        let k = choose|k: int| 0 <= k < t1.renderers.len() && t1.renderers[k] == x;
    }
    crate::unwinding::lemma_rel_from_sets(rules, urls, d, s1b, s2b);
}

} // verus!

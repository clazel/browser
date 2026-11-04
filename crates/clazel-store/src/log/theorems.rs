//! The design note's theorems 1 to 3 (3.10a.0, "The theorems this gives"),
//! in [`super::spec`]'s terms. Theorem 4 (quota) comes with its own spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A list longer than `ts` whose log is a prefix of `ts`'s log does not
/// fit: its next record would run past the end.
proof fn lemma_no_longer(identity: Seq<u8>, ts: Seq<Seq<Op>>, u: Seq<Seq<Op>>)
    requires
        log_ok(ts),
        fits(identity, encode_log(identity, ts), u),
        u.len() > ts.len(),
    ensures
        false,
{
    let file = encode_log(identity, ts);
    let n = ts.len();
    assert(file.is_prefix_of(file));
    super::lemmas::lemma_fits_agree(identity, file, u, ts);
    super::lemmas::lemma_encode_log_take(identity, u, n + 1);
    let un = u.take((n + 1) as int);
    assert(un.drop_last() =~= u.take(n as int));
    let rec = encode_record((n + 1) as nat, un.last());
    assert(encode_log(identity, un) == file + rec);
    lemma_prefix_trans(encode_log(identity, un), encode_log(identity, u), file);
    let body = record_body((n + 1) as nat, un.last());
    super::lemmas::lemma_tlv_len(
        clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE),
        body + clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(body)),
    );
}

/// Theorem 2: the whole file written from `ts` recovers `ts`.
pub proof fn theorem_whole(identity: Seq<u8>, ts: Seq<Seq<Op>>)
    requires
        identity_ok(identity),
        log_ok(ts),
    ensures
        recovered(identity, encode_log(identity, ts)) == Some(ts),
{
    let file = encode_log(identity, ts);
    super::lemmas::lemma_encode_log_take(identity, ts, 0);
    assert(ts.take(0) =~= Seq::<Seq<Op>>::empty());
    assert(file.is_prefix_of(file));
    assert(fits(identity, file, ts));
    assert forall|u: Seq<Seq<Op>>| #[trigger] fits(identity, file, u) implies u.len() <= ts.len() by {
        if u.len() > ts.len() {
            lemma_no_longer(identity, ts, u);
        }
    }
    super::lemmas::lemma_longest_fit_unique(identity, file, ts);
}

/// The largest `k <= j` for which the log of the first `k` transactions of
/// `ts` is a prefix of `p` (0 when none is, which a header prefix rules
/// out).
spec fn best(identity: Seq<u8>, ts: Seq<Seq<Op>>, p: Seq<u8>, j: nat) -> nat
    decreases j,
{
    if j == 0 || encode_log(identity, ts.take(j as int)).is_prefix_of(p) {
        j
    } else {
        best(identity, ts, p, (j - 1) as nat)
    }
}

/// [`best`] is a `k <= j` whose log is a prefix (given the header is), and
/// no larger `k <= j` has one.
proof fn lemma_best(identity: Seq<u8>, ts: Seq<Seq<Op>>, p: Seq<u8>, j: nat)
    requires
        j <= ts.len(),
        encode_header(identity).is_prefix_of(p),
    ensures
        best(identity, ts, p, j) <= j,
        encode_log(identity, ts.take(best(identity, ts, p, j) as int)).is_prefix_of(p),
        forall|k: nat|
            best(identity, ts, p, j) < k <= j ==> !#[trigger] encode_log(identity, ts.take(k as int)).is_prefix_of(p),
    decreases j,
{
    if j == 0 {
        assert(ts.take(0) =~= Seq::<Seq<Op>>::empty());
    } else if !encode_log(identity, ts.take(j as int)).is_prefix_of(p) {
        lemma_best(identity, ts, p, (j - 1) as nat);
    }
}

/// `a` a prefix of `b`, and `b` of `c`, make `a` a prefix of `c`.
proof fn lemma_prefix_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        a.is_prefix_of(b),
        b.is_prefix_of(c),
    ensures
        a.is_prefix_of(c),
{
    assert(c.subrange(0, a.len() as int) =~= b.subrange(0, a.len() as int));
}

/// Theorem 1: every prefix `p` of the file written from `ts` that holds the
/// header recovers the first `k` transactions of `ts`, for some `k`. (A
/// prefix shorter than the header is refused.)
pub proof fn theorem_prefix(identity: Seq<u8>, ts: Seq<Seq<Op>>, p: Seq<u8>)
    requires
        identity_ok(identity),
        log_ok(ts),
        p.is_prefix_of(encode_log(identity, ts)),
        encode_header(identity).is_prefix_of(p),
    ensures
        exists|k: nat| k <= ts.len() && recovered(identity, p) == Some(#[trigger] ts.take(k as int)),
{
    let file = encode_log(identity, ts);
    let k = best(identity, ts, p, ts.len());
    lemma_best(identity, ts, p, ts.len());
    let v = ts.take(k as int);
    assert(file.is_prefix_of(file));
    assert(fits(identity, file, ts));
    super::lemmas::lemma_fits_take(identity, file, ts, k);
    assert(fits(identity, p, v));
    assert forall|u: Seq<Seq<Op>>| #[trigger] fits(identity, p, u) implies u.len() <= v.len() by {
        lemma_prefix_trans(encode_log(identity, u), p, file);
        assert(fits(identity, file, u));
        if u.len() > ts.len() {
            lemma_no_longer(identity, ts, u);
        } else if u.len() > k {
            super::lemmas::lemma_fits_agree(identity, file, ts, u);
            let j = u.len();
            assert(ts.take(j as int) == u);
            assert(!encode_log(identity, ts.take(j as int)).is_prefix_of(p));
        }
    }
    super::lemmas::lemma_longest_fit_unique(identity, p, v);
    assert(recovered(identity, p) == Some(ts.take(k as int)));
}

/// Theorem 3: a compaction of a state holds that state.
pub proof fn theorem_compaction(identity: Seq<u8>, s: State, file: Seq<u8>)
    requires
        identity_ok(identity),
        compaction_of(identity, s, file),
    ensures
        file_state(identity, file) == Some(s),
{
    let ts = choose|ts: Seq<Seq<Op>>| log_ok(ts) && file == #[trigger] encode_log(identity, ts) && apply_log(ts) == s;
    theorem_whole(identity, ts);
}

} // verus!

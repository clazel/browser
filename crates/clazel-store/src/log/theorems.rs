//! The design note's theorems 1 to 3 (3.10a.0, "The theorems this gives"),
//! in [`super::spec`]'s terms. Theorem 4 (quota) is stated here over the
//! spec, and [`super::bucket`]'s `commit` is proven to meet it.

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


/// Theorem 4: committing under a quota leaves a bucket within it, or, when
/// the transaction is refused, exactly as it was.
pub proof fn theorem_quota(s: State, ops: Seq<Op>, quota: nat)
    ensures
        admits(s, ops, quota) ==> usage(commit_state(s, ops, quota)) <= quota,
        !admits(s, ops, quota) ==> commit_state(s, ops, quota) == s,
{
}


// ---------------------------------------------------------------------------
// The records: round trip, canonicity and refusal
// ---------------------------------------------------------------------------

/// A log is at least one octet per transaction: no record is empty.
proof fn lemma_log_len(identity: Seq<u8>, u: Seq<Seq<Op>>)
    ensures
        encode_log(identity, u).len() >= u.len(),
    decreases u.len(),
{
    if u.len() > 0 {
        lemma_log_len(identity, u.drop_last());
        let body = record_body(u.len(), u.last());
        super::lemmas::lemma_tlv_len(
            clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE),
            body + clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(body)),
        );
    }
}

/// Some list that fits is longest, when no list longer than `n` fits and
/// the file holds the header.
proof fn lemma_longest_exists(identity: Seq<u8>, file: Seq<u8>, n: nat)
    requires
        encode_header(identity).is_prefix_of(file),
        forall|u: Seq<Seq<Op>>| #[trigger] fits(identity, file, u) ==> u.len() <= n,
    ensures
        exists|v: Seq<Seq<Op>>| longest_fit(identity, file, v),
    decreases n,
{
    if exists|u: Seq<Seq<Op>>| #[trigger] fits(identity, file, u) && u.len() == n {
        let u = choose|u: Seq<Seq<Op>>| #[trigger] fits(identity, file, u) && u.len() == n;
        assert(longest_fit(identity, file, u));
    } else if n == 0 {
        let e = Seq::<Seq<Op>>::empty();
        assert(encode_log(identity, e) == encode_header(identity));
        assert(fits(identity, file, e));
    } else {
        assert forall|u: Seq<Seq<Op>>| #[trigger] fits(identity, file, u) implies u.len() <= (n - 1) as nat by {
            if u.len() == n {
                assert(fits(identity, file, u) && u.len() == n);
            }
        }
        lemma_longest_exists(identity, file, (n - 1) as nat);
    }
}

/// When the file holds the header of a valid identity, what is recovered
/// is a longest list that fits.
pub proof fn lemma_recovered(identity: Seq<u8>, file: Seq<u8>)
    requires
        identity_ok(identity),
        encode_header(identity).is_prefix_of(file),
    ensures
        recovered(identity, file) matches Some(v) && longest_fit(identity, file, v),
{
    assert forall|u: Seq<Seq<Op>>| #[trigger] fits(identity, file, u) implies u.len() <= file.len() by {
        lemma_log_len(identity, u);
    }
    lemma_longest_exists(identity, file, file.len());
}

/// Round trip: the log of valid transactions `ts`, followed by any octets
/// at all, recovers `ts` and perhaps more (the octets after it may hold
/// further records). With nothing after it, exactly `ts`
/// ([`theorem_whole`]).
pub proof fn theorem_round_trip(identity: Seq<u8>, ts: Seq<Seq<Op>>, rest: Seq<u8>)
    requires
        identity_ok(identity),
        log_ok(ts),
    ensures
        recovered(identity, encode_log(identity, ts) + rest) matches Some(v) && ts.len() <= v.len() && v.take(
            ts.len() as int,
        ) == ts,
{
    let log = encode_log(identity, ts);
    let file = log + rest;
    assert(log.is_prefix_of(file)) by {
        assert(file.subrange(0, log.len() as int) =~= log);
    }
    super::lemmas::lemma_encode_log_take(identity, ts, 0);
    assert(ts.take(0) =~= Seq::<Seq<Op>>::empty());
    lemma_prefix_trans(encode_header(identity), log, file);
    lemma_recovered(identity, file);
    let v = recovered(identity, file).unwrap();
    assert(fits(identity, file, ts));
    super::lemmas::lemma_fits_agree(identity, file, v, ts);
}

/// Canonicity: encoding what was recovered gives the file's own octets, a
/// prefix of the file, and the transactions are valid. (DER has one
/// encoding per value, so nothing else could have been read.)
pub proof fn theorem_canonical(identity: Seq<u8>, file: Seq<u8>)
    ensures
        recovered(identity, file) matches Some(v) ==> log_ok(v) && encode_log(identity, v).is_prefix_of(file),
{
    if recovered(identity, file) is Some {
        lemma_recovered(identity, file);
    }
}

/// Refusal: a file is refused exactly when the identity is over its limit
/// or the file does not start with the header; and the octets after what is
/// recovered never start a valid next record, so nothing is half read.
pub proof fn theorem_refusal(identity: Seq<u8>, file: Seq<u8>)
    ensures
        (recovered(identity, file) is None) == (!identity_ok(identity) || !encode_header(identity).is_prefix_of(file)),
        recovered(identity, file) matches Some(v) ==> forall|t: Seq<Op>|
            transaction_ok(v.len() + 1, t) ==> !(#[trigger] encode_log(identity, v.push(t))).is_prefix_of(file),
{
    if recovered(identity, file) is Some {
        lemma_recovered(identity, file);
        let v = recovered(identity, file).unwrap();
        assert forall|t: Seq<Op>| transaction_ok(v.len() + 1, t) implies !(#[trigger] encode_log(
            identity,
            v.push(t),
        )).is_prefix_of(file) by {
            let n = v.push(t);
            if encode_log(identity, n).is_prefix_of(file) {
                assert forall|i: int| 0 <= i < n.len() implies transaction_ok((i + 1) as nat, #[trigger] n[i]) by {
                    if i < v.len() {
                        assert(n[i] == v[i]);
                    }
                }
                assert(fits(identity, file, n));
            }
        }
    }
}

} // verus!

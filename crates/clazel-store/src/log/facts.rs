//! Small proven facts over concrete inputs, about the parts of the spec
//! that Verus cannot evaluate (maps, `choose`, quantifiers). Each says what
//! one definition must do on one input, read from the design note, so a
//! changed definition makes a fact false: `mutations.json`'s certificates
//! name them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A key "a".
pub open spec fn ka() -> Seq<u8> {
    seq![0x61u8]
}

/// A key "b".
pub open spec fn kb() -> Seq<u8> {
    seq![0x62u8]
}

/// A value "x".
pub open spec fn vx() -> Seq<u8> {
    seq![0x78u8]
}

/// A longer value "yz".
pub open spec fn vy() -> Seq<u8> {
    seq![0x79u8, 0x7a]
}

/// The state with key "a" of bottle 1 set to "x".
pub open spec fn one() -> State {
    Map::<(nat, Seq<u8>), Seq<u8>>::empty().insert((1nat, ka()), vx())
}

/// The state with key "a" set to "x" in bottles 1 and 2.
pub open spec fn two() -> State {
    one().insert((2nat, ka()), vx())
}

/// A put sets its key of its bottle to its value.
pub proof fn fact_put()
    ensures
        apply_op(Map::empty(), Op::Put { bottle: 1, key: ka(), value: vx() }).dom().contains((1nat, ka())),
        apply_op(Map::empty(), Op::Put { bottle: 1, key: ka(), value: vx() })[(1nat, ka())] == vx(),
{
}

/// A delete removes its key, and only its key.
pub proof fn fact_delete()
    ensures
        !apply_op(one(), Op::Delete { bottle: 1, key: ka() }).dom().contains((1nat, ka())),
        apply_op(one(), Op::Delete { bottle: 2, key: ka() }).dom().contains((1nat, ka())),
{
    assert(((1nat, ka())) != ((2nat, ka())));
}

/// A clear removes its bottle's keys, and only those.
pub proof fn fact_clear()
    ensures
        !apply_op(two(), Op::Clear { bottle: 1 }).dom().contains((1nat, ka())),
        apply_op(two(), Op::Clear { bottle: 1 }).dom().contains((2nat, ka())),
{
}

/// A transaction applies its operations in order, and a log its
/// transactions, so the later put wins.
pub proof fn fact_order()
    ensures
        apply_transaction(
            Map::empty(),
            seq![Op::Put { bottle: 1, key: ka(), value: vx() }, Op::Put { bottle: 1, key: ka(), value: vy() }],
        )[(1nat, ka())] == vy(),
        apply_log(
            seq![seq![Op::Put { bottle: 1, key: ka(), value: vx() }], seq![Op::Put { bottle: 1, key: ka(), value: vy() }]],
        )[(1nat, ka())] == vy(),
{
    let p = Op::Put { bottle: 1, key: ka(), value: vx() };
    let q = Op::Put { bottle: 1, key: ka(), value: vy() };
    let e = Map::<(nat, Seq<u8>), Seq<u8>>::empty();
    assert(seq![p, q].drop_last() =~= seq![p]);
    assert(seq![p].drop_last() =~= Seq::<Op>::empty());
    assert(seq![q].drop_last() =~= Seq::<Op>::empty());
    let ts = seq![seq![p], seq![q]];
    assert(ts.drop_last() =~= seq![seq![p]]);
    assert(seq![seq![p]].drop_last() =~= Seq::<Seq<Op>>::empty());
    assert(apply_transaction(e, seq![p]) == apply_op(apply_transaction(e, Seq::<Op>::empty()), p));
    assert(apply_transaction(e, seq![p, q]) == apply_op(apply_transaction(e, seq![p]), q));
    assert(apply_log(seq![seq![p]]) == apply_transaction(apply_log(Seq::<Seq<Op>>::empty()), seq![p]));
    assert(apply_log(ts) == apply_transaction(apply_log(seq![seq![p]]), seq![q]));
    assert(apply_transaction(apply_log(seq![seq![p]]), seq![q]) == apply_op(
        apply_transaction(apply_log(seq![seq![p]]), Seq::<Op>::empty()),
        q,
    ));
}

/// A later entry replaces an earlier one with the same key.
pub proof fn fact_entries()
    ensures
        entries_state(seq![(1nat, ka(), vx()), (1nat, ka(), vy())])[(1nat, ka())] == vy(),
{
    let es = seq![(1nat, ka(), vx()), (1nat, ka(), vy())];
    assert(es.drop_last() =~= seq![(1nat, ka(), vx())]);
}

/// An entry counts its key's and its value's octets.
pub proof fn fact_entry_size()
    ensures
        entry_size((1nat, ka()), vy()) == 3,
{
}

/// Usage: nothing for an empty bucket, and the sizes of the entries.
pub proof fn fact_usage()
    ensures
        usage(Map::<(nat, Seq<u8>), Seq<u8>>::empty()) == 0,
        usage(one()) == 2,
{
    let e = Map::<(nat, Seq<u8>), Seq<u8>>::empty();
    broadcast use vstd::set::lemma_set_empty_len;

    assert(e.dom() =~= Set::<(nat, Seq<u8>)>::empty());
    super::bucket::lemma_usage_insert(e, (1nat, ka()), vx());
}

/// The quota: a state exactly at it is admitted, and one over it is not,
/// and a refused transaction leaves the state as it was while an admitted
/// one applies.
pub proof fn fact_quota()
    ensures
        admits(one(), seq![], 2),
        !admits(one(), seq![], 1),
        commit_state(one(), seq![Op::Delete { bottle: 1, key: ka() }], 0) == Map::<(nat, Seq<u8>), Seq<u8>>::empty(),
        commit_state(Map::empty(), seq![Op::Put { bottle: 1, key: ka(), value: vx() }], 1) == Map::<(nat, Seq<u8>), Seq<u8>>::empty(),
{
    let e = Map::<(nat, Seq<u8>), Seq<u8>>::empty();
    fact_usage();
    assert(apply_transaction(one(), Seq::<Op>::empty()) == one());
    let d = Op::Delete { bottle: 1, key: ka() };
    assert(seq![d].drop_last() =~= Seq::<Op>::empty());
    assert(apply_transaction(one(), seq![d]) == apply_op(one(), d));
    assert(apply_op(one(), d) =~= e);
    let p = Op::Put { bottle: 1, key: ka(), value: vx() };
    assert(seq![p].drop_last() =~= Seq::<Op>::empty());
    assert(apply_transaction(e, Seq::<Op>::empty()) == e);
    assert(apply_transaction(e, seq![p]) == apply_op(apply_transaction(e, seq![p].drop_last()), seq![p].last()));
    assert(apply_transaction(e, seq![p]) == apply_op(e, p));
    assert(apply_op(e, p) =~= one());
}

/// The limits, as the design note states them: 64 MiB per record, 4096
/// octets of identity, and bottles and commits of 32 and 64 bits.
pub proof fn fact_limits()
    ensures
        max_record_len() == 67_108_864,
        max_identity_len() == 4096,
        identity_ok(Seq::new(4096, |i: int| 0u8)),
        !identity_ok(Seq::new(4097, |i: int| 0u8)),
{
}

/// What makes a transaction valid: a commit from 1 to 2^64 - 1 and bottles
/// below 2^32.
pub proof fn fact_transaction()
    ensures
        transaction_ok(1, seq![]),
        !transaction_ok(0, seq![]),
        !transaction_ok(0x1_0000_0000_0000_0000, seq![]),
        !transaction_ok(1, seq![Op::Clear { bottle: 0x1_0000_0000 }]),
        log_ok(seq![seq![]]),
{
    clazel_der::lemmas::lemma_pow256_8();
    super::examples::example_empty_record();
    let c = seq![Op::Clear { bottle: 0x1_0000_0000 }];
    assert(op_bottle(c[0]) == 0x1_0000_0000);
    let l = seq![Seq::<Op>::empty()];
    assert(l[0] =~= seq![]);
    assert(encode_record(1, l[0]).len() <= max_record_len()) by {
        assert(l[0] == Seq::<Op>::empty());
    }
}

/// A log's first record has commit 1.
pub proof fn fact_log()
    ensures
        encode_log(seq![], seq![Seq::<Op>::empty()]) == encode_header(seq![]) + encode_record(1, seq![]),
{
    let l = seq![Seq::<Op>::empty()];
    assert(l.drop_last() =~= Seq::<Seq<Op>>::empty());
    assert(l.last() =~= Seq::<Op>::empty());
    assert(encode_log(seq![], Seq::<Seq<Op>>::empty()) == encode_header(seq![]));
    assert(encode_log(seq![], l) == encode_log(seq![], l.drop_last()) + encode_record(1, l.last()));
}

/// The state with keys "a" and "b" of bottle 1.
pub open spec fn ab() -> State {
    one().insert((1nat, kb()), vx())
}

/// A scan's result, for [`ab`] with no bounds: both entries in order.
pub open spec fn ab_scan() -> Seq<(Seq<u8>, Seq<u8>)> {
    seq![(ka(), vx()), (kb(), vx())]
}

/// `key_less` facts the scan facts below use.
pub proof fn lemma_ab_order()
    ensures
        key_less(ka(), kb()),
        !key_less(kb(), ka()),
        !key_less(ka(), seq![]),
        !key_less(kb(), seq![]),
{
    assert(key_less(ka(), kb())) by (compute_only);
    assert(!key_less(kb(), ka())) by (compute_only);
    assert(!key_less(ka(), seq![])) by (compute_only);
    assert(!key_less(kb(), seq![])) by (compute_only);
}

/// What a scan is: every entry of the bottle in the range, in key order,
/// with its value, and of that bottle.
pub proof fn fact_scan()
    ensures
        is_scan(ab(), 1, seq![], None, ab_scan()),
        !is_scan(ab(), 1, seq![], None, seq![(kb(), vx()), (ka(), vx())]),
        !is_scan(ab(), 1, seq![], None, seq![(ka(), vx())]),
        !is_scan(ab(), 2, seq![], None, ab_scan()),
        !is_scan(ab(), 1, seq![], None, seq![(ka(), vy()), (kb(), vx())]),
        !is_scan(ab(), 1, seq![], Some(kb()), ab_scan()),
{
    lemma_ab_order();
    let o = ab_scan();
    assert(o[0].0 == ka() && o[1].0 == kb());
    assert forall|i: int, j: int| 0 <= i < j < o.len() implies key_less(#[trigger] o[i].0, #[trigger] o[j].0) by {
        assert(i == 0 && j == 1);
    }
    assert forall|i: int| 0 <= i < o.len() implies {
        &&& in_range(#[trigger] o[i].0, seq![], None)
        &&& ab().dom().contains((1nat, o[i].0))
        &&& ab()[(1nat, o[i].0)] == o[i].1
    } by {
        assert(ka() != kb());
        assert(((1nat, ka())) != ((1nat, kb())));
    }
    assert forall|k: Seq<u8>| #[trigger] ab().dom().contains((1nat, k)) && in_range(k, seq![], None) implies exists|i: int|
        0 <= i < o.len() && #[trigger] o[i].0 == k by {
        if k == ka() {
            assert(o[0].0 == k);
        } else {
            assert(k == kb());
            assert(o[1].0 == k);
        }
    }
    // Out of order.
    let r = seq![(kb(), vx()), (ka(), vx())];
    assert(r[0].0 == kb() && r[1].0 == ka());
    assert(!key_less(r[0].0, r[1].0));
    // An entry missing.
    let m = seq![(ka(), vx())];
    assert(ab().dom().contains((1nat, kb())));
    assert(in_range(kb(), seq![], None));
    if is_scan(ab(), 1, seq![], None, m) {
        let i = choose|i: int| 0 <= i < m.len() && #[trigger] m[i].0 == kb();
        assert(i == 0);
        assert(ka() != kb()) by {
            assert(ka()[0] != kb()[0]);
        }
    }
    // Another bottle.
    assert(!ab().dom().contains((2nat, ka())));
    assert(o[0].0 == ka());
    // A wrong value.
    let w = seq![(ka(), vy()), (kb(), vx())];
    assert(w[0].1 == vy() && w[0].0 == ka());
    assert(ab()[(1nat, ka())] == vx()) by {
        assert(((1nat, ka())) != ((1nat, kb()))) by {
            assert(ka()[0] != kb()[0]);
        }
    }
    assert(vx() != vy()) by {
        assert(vx().len() != vy().len());
    }
    // Past the upper bound.
    assert(!key_less(kb(), kb())) by (compute_only);
    assert(!in_range(o[1].0, seq![], Some(kb())));
}


// ---------------------------------------------------------------------------
// The record limit, at its exact boundary
// ---------------------------------------------------------------------------

/// A TLV with a one-octet tag and contents from 2^24 to 2^32 octets takes six
/// octets more than its contents: one for the tag, and five for the length.
proof fn lemma_big_tlv(tag: clazel_der::spec::Tag, c: Seq<u8>)
    requires
        tag.number < 31,
        0x100_0000 <= c.len() < 0x1_0000_0000,
    ensures
        clazel_der::spec::encode_tlv(tag, c).len() == c.len() + 6,
{
    clazel_der::lemmas::lemma_be_bytes_len(c.len(), 4);
    assert(clazel_der::spec::length_octets(c.len()) == 4);
}

/// A put of `n` zero octets under an empty key in bottle 0.
pub open spec fn big(n: nat) -> Op {
    Op::Put { bottle: 0, key: seq![], value: Seq::new(n, |i: int| 0u8) }
}

/// Commit 1 of one big put takes 38 octets more than the value.
pub proof fn lemma_big_record(n: nat)
    requires
        0x100_0000 <= n <= 0x800_0000,
    ensures
        encode_record(1, seq![big(n)]).len() == n + 38,
        transaction_ok(1, seq![big(n)]) == (n + 38 <= max_record_len()),
{
    clazel_der::lemmas::lemma_pow256_8();
    let v = Seq::new(n, |i: int| 0u8);
    let op = big(n);
    let universal = clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING);
    let seq_tag = clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE);
    assert(encode_number(0).len() == 3) by (compute_only);
    assert(encode_number(1).len() == 3) by (compute_only);
    assert(clazel_der::spec::encode_octet_string(Seq::<u8>::empty()).len() == 2) by (compute_only);
    lemma_big_tlv(universal, v);
    let contents = encode_number(0) + clazel_der::spec::encode_octet_string(Seq::<u8>::empty())
        + clazel_der::spec::encode_octet_string(v);
    assert(contents.len() == n + 11);
    lemma_big_tlv(clazel_der::spec::context_specific(0, true), contents);
    assert(encode_op(op).len() == n + 17);
    let ops = seq![op];
    assert(ops.drop_last() =~= Seq::<Op>::empty());
    assert(ops.last() == op);
    assert(encode_ops(Seq::<Op>::empty()) =~= Seq::<u8>::empty());
    assert(encode_ops(ops) =~= encode_op(op));
    lemma_big_tlv(seq_tag, encode_op(op));
    let body = record_body(1, ops);
    assert(body.len() == n + 26);
    let check = crate::crc32c::spec::crc32c(body);
    assert(check.len() == 4);
    let octets = clazel_der::spec::encode_octet_string(check);
    assert(clazel_der::spec::encode_length(4) == seq![4u8]);
    assert(octets.len() == 6);
    lemma_big_tlv(seq_tag, body + octets);
    assert(encode_record(1, ops).len() == n + 38);
    assert forall|i: int| 0 <= i < ops.len() implies op_bottle(#[trigger] ops[i]) < clazel_der::spec::pow256(4) by {
        assert(ops[i] == op);
    }
}

/// A record of exactly 64 MiB is valid, and one octet more is not.
pub proof fn fact_record_limit()
    ensures
        encode_record(1, seq![big(67_108_826)]).len() == max_record_len(),
        transaction_ok(1, seq![big(67_108_826)]),
        encode_record(1, seq![big(67_108_827)]).len() == max_record_len() + 1,
        !transaction_ok(1, seq![big(67_108_827)]),
{
    lemma_big_record(67_108_826);
    lemma_big_record(67_108_827);
}

// ---------------------------------------------------------------------------
// The clauses of a scan, one at a time
// ---------------------------------------------------------------------------

/// Two results with keys "a" and "b" meet every clause of a scan of
/// [`ab`] but the one about values, with no upper bound or with "b" as it
/// (except that "b" itself is not in that range).
pub proof fn lemma_scan_shape(o: Seq<(Seq<u8>, Seq<u8>)>)
    requires
        o.len() == 2,
        o[0].0 == ka(),
        o[1].0 == kb(),
    ensures
        forall|i: int, j: int| 0 <= i < j < o.len() ==> key_less(#[trigger] o[i].0, #[trigger] o[j].0),
        forall|i: int|
            0 <= i < o.len() ==> {
                &&& in_range(#[trigger] o[i].0, seq![], None)
                &&& ab().dom().contains((1nat, o[i].0))
            },
        forall|k: Seq<u8>|
            #[trigger] ab().dom().contains((1nat, k)) && in_range(k, seq![], None) ==> exists|i: int|
                0 <= i < o.len() && #[trigger] o[i].0 == k,
        forall|k: Seq<u8>|
            #[trigger] ab().dom().contains((1nat, k)) && in_range(k, seq![], Some(kb())) ==> exists|i: int|
                0 <= i < o.len() && #[trigger] o[i].0 == k,
{
    lemma_ab_order();
    assert forall|i: int, j: int| 0 <= i < j < o.len() implies key_less(#[trigger] o[i].0, #[trigger] o[j].0) by {
        assert(i == 0 && j == 1);
    }
    assert forall|k: Seq<u8>| #[trigger] ab().dom().contains((1nat, k)) implies exists|i: int|
        0 <= i < o.len() && #[trigger] o[i].0 == k by {
        if k == ka() {
            assert(o[0].0 == k);
        } else {
            assert(k == kb());
            assert(o[1].0 == k);
        }
    }
}

/// A result outside the bucket's bottle is not a scan, even when its value is
/// what the map holds there (which is unspecified).
pub proof fn fact_other_bottle()
    ensures
        !is_scan(ab(), 2, seq![], None, seq![(ka(), ab()[(2nat, ka())])]),
{
    let o = seq![(ka(), ab()[(2nat, ka())])];
    assert(!ab().dom().contains((2nat, ka())));
    assert(o[0].0 == ka());
}

/// The clauses [`fact_other_bottle`]'s result does meet: only the one about
/// the bottle fails.
pub proof fn lemma_other_bottle_shape()
    ensures
        forall|i: int, j: int|
            0 <= i < j < seq![(ka(), ab()[(2nat, ka())])].len() ==> key_less(
                #[trigger] seq![(ka(), ab()[(2nat, ka())])][i].0,
                #[trigger] seq![(ka(), ab()[(2nat, ka())])][j].0,
            ),
        in_range(ka(), seq![], None),
        forall|k: Seq<u8>| !(#[trigger] ab().dom().contains((2nat, k))),
{
    lemma_ab_order();
    assert forall|k: Seq<u8>| !(#[trigger] ab().dom().contains((2nat, k))) by {
    }
}

} // verus!

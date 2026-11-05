//! Lemmas behind recovery: the encodings in [`super::spec`] can be told
//! apart from the front. Two encodings that begin the same octets, each
//! followed by anything, are the same value, and so two valid transaction
//! lists that both fit a file agree as far as the shorter one goes. That
//! is what makes [`recovered`]'s `choose` pick exactly one list.
//!
//! Every lemma rests on `clazel-der`'s proof that a TLV reads back as the
//! tag and contents that were written ([`lemma_peel`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A TLV's contents are no longer than its encoding, which is never empty.
pub proof fn lemma_tlv_len(tag: clazel_der::spec::Tag, c: Seq<u8>)
    ensures
        c.len() < clazel_der::spec::encode_tlv(tag, c).len(),
{
    let n = c.len();
    if n < 128 {
        assert(clazel_der::spec::encode_length(n).len() == 1);
    } else {
        assert(clazel_der::spec::encode_length(n).len() >= 1);
    }
}

/// Two TLVs that start the same octets are the same TLV, and what follows
/// them is the same.
pub proof fn lemma_peel(
    t1: clazel_der::spec::Tag,
    c1: Seq<u8>,
    r1: Seq<u8>,
    t2: clazel_der::spec::Tag,
    c2: Seq<u8>,
    r2: Seq<u8>,
)
    requires
        clazel_der::spec::tlv_ok(t1, c1),
        clazel_der::spec::tlv_ok(t2, c2),
        clazel_der::spec::encode_tlv(t1, c1) + r1 == clazel_der::spec::encode_tlv(t2, c2) + r2,
    ensures
        t1 == t2,
        c1 == c2,
        r1 == r2,
{
    let e1 = clazel_der::spec::encode_tlv(t1, c1);
    let e2 = clazel_der::spec::encode_tlv(t2, c2);
    let b = e1 + r1;
    assert(b.subrange(0, e1.len() as int) =~= e1);
    assert(b.subrange(0, e2.len() as int) =~= e2);
    clazel_der::lemmas_tlv::lemma_read_tlv_encode_tlv(t1, c1, b, 0, b.len());
    clazel_der::lemmas_tlv::lemma_read_tlv_encode_tlv(t2, c2, b, 0, b.len());
    assert(c1 =~= c2);
    assert(e1 == e2);
    assert(r1 =~= b.skip(e1.len() as int));
    assert(r2 =~= b.skip(e2.len() as int));
}

/// Two numbers below 2^64 whose INTEGERs start the same octets are equal.
pub proof fn lemma_peel_number(n1: nat, r1: Seq<u8>, n2: nat, r2: Seq<u8>)
    requires
        n1 < clazel_der::spec::pow256(8),
        n2 < clazel_der::spec::pow256(8),
        encode_number(n1) + r1 == encode_number(n2) + r2,
    ensures
        n1 == n2,
        r1 == r2,
{
    clazel_der::lemmas::lemma_pow256_8();
    let m1 = clazel_der::spec::be_bytes(n1, 8);
    let m2 = clazel_der::spec::be_bytes(n2, 8);
    clazel_der::lemmas::lemma_be_bytes_len(n1, 8);
    clazel_der::lemmas::lemma_be_bytes_len(n2, 8);
    clazel_der::lemmas_typed::lemma_integer_unsigned_contents(m1);
    clazel_der::lemmas_typed::lemma_integer_unsigned_contents(m2);
    clazel_der::lemmas::lemma_be_value_of_be_bytes(n1, 8);
    clazel_der::lemmas::lemma_be_value_of_be_bytes(n2, 8);
    let tag = clazel_der::spec::universal_primitive(clazel_der::spec::INTEGER);
    lemma_peel(
        tag,
        clazel_der::spec::integer_unsigned_contents(m1),
        r1,
        tag,
        clazel_der::spec::integer_unsigned_contents(m2),
        r2,
    );
}

/// Two OCTET STRINGs that start the same octets are equal.
pub proof fn lemma_peel_octets(s1: Seq<u8>, r1: Seq<u8>, s2: Seq<u8>, r2: Seq<u8>)
    requires
        s1.len() < clazel_der::spec::pow256(8),
        s2.len() < clazel_der::spec::pow256(8),
        clazel_der::spec::encode_octet_string(s1) + r1 == clazel_der::spec::encode_octet_string(s2) + r2,
    ensures
        s1 == s2,
        r1 == r2,
{
    let tag = clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING);
    lemma_peel(tag, s1, r1, tag, s2, r2);
}

/// What is inside an operation's context tag.
pub open spec fn op_contents(op: Op) -> Seq<u8> {
    match op {
        Op::Put { bottle, key, value } => encode_number(bottle) + clazel_der::spec::encode_octet_string(key)
            + clazel_der::spec::encode_octet_string(value),
        Op::Delete { bottle, key } => encode_number(bottle) + clazel_der::spec::encode_octet_string(key),
        Op::Clear { bottle } => encode_number(bottle),
    }
}

/// The context tag number of an operation.
pub open spec fn op_tag(op: Op) -> u32 {
    match op {
        Op::Put { .. } => 0,
        Op::Delete { .. } => 1,
        Op::Clear { .. } => 2,
    }
}

/// [`encode_op`] is a context tag around [`op_contents`].
pub proof fn lemma_encode_op(op: Op)
    ensures
        encode_op(op) == clazel_der::spec::encode_tlv(
            clazel_der::spec::context_specific(op_tag(op), true),
            op_contents(op),
        ),
        op_contents(op).len() < encode_op(op).len(),
{
    lemma_tlv_len(clazel_der::spec::context_specific(op_tag(op), true), op_contents(op));
}

/// Two operations, with bottles below 2^64, whose encodings start the same
/// octets (fewer than 2^64 of them) are equal.
pub proof fn lemma_peel_op(a: Op, r1: Seq<u8>, b: Op, r2: Seq<u8>)
    requires
        op_bottle(a) < clazel_der::spec::pow256(8),
        op_bottle(b) < clazel_der::spec::pow256(8),
        (encode_op(a) + r1).len() < clazel_der::spec::pow256(8),
        encode_op(a) + r1 == encode_op(b) + r2,
    ensures
        a == b,
        r1 == r2,
{
    lemma_encode_op(a);
    lemma_encode_op(b);
    let ca = op_contents(a);
    let cb = op_contents(b);
    assert((encode_op(b) + r2).len() == (encode_op(a) + r1).len());
    lemma_peel(
        clazel_der::spec::context_specific(op_tag(a), true),
        ca,
        r1,
        clazel_der::spec::context_specific(op_tag(b), true),
        cb,
        r2,
    );
    assert(op_tag(a) == op_tag(b));
    let e = Seq::<u8>::empty();
    match (a, b) {
        (Op::Put { bottle: ba, key: ka, value: va }, Op::Put { bottle: bb, key: kb, value: vb }) => {
            let oka = clazel_der::spec::encode_octet_string(ka);
            let ova = clazel_der::spec::encode_octet_string(va);
            let okb = clazel_der::spec::encode_octet_string(kb);
            let ovb = clazel_der::spec::encode_octet_string(vb);
            assert(ca =~= encode_number(ba) + (oka + ova));
            assert(cb =~= encode_number(bb) + (okb + ovb));
            lemma_peel_number(ba, oka + ova, bb, okb + ovb);
            lemma_tlv_len(clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING), ka);
            lemma_tlv_len(clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING), kb);
            lemma_tlv_len(clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING), va);
            lemma_tlv_len(clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING), vb);
            lemma_peel_octets(ka, ova, kb, ovb);
            assert(ova + e =~= ova);
            assert(ovb + e =~= ovb);
            lemma_peel_octets(va, e, vb, e);
        },
        (Op::Delete { bottle: ba, key: ka }, Op::Delete { bottle: bb, key: kb }) => {
            let oka = clazel_der::spec::encode_octet_string(ka);
            let okb = clazel_der::spec::encode_octet_string(kb);
            lemma_peel_number(ba, oka, bb, okb);
            lemma_tlv_len(clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING), ka);
            lemma_tlv_len(clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING), kb);
            assert(oka + e =~= oka);
            assert(okb + e =~= okb);
            lemma_peel_octets(ka, e, kb, e);
        },
        (Op::Clear { bottle: ba }, Op::Clear { bottle: bb }) => {
            assert(encode_number(ba) + e =~= encode_number(ba));
            assert(encode_number(bb) + e =~= encode_number(bb));
            lemma_peel_number(ba, e, bb, e);
        },
        // op_tag(a) == op_tag(b): the alternatives match.
        _ => {},
    }
}

/// [`encode_ops`] read from the front: the first operation, then the rest.
pub proof fn lemma_encode_ops_front(s: Seq<Op>)
    requires
        s.len() > 0,
    ensures
        encode_ops(s) == encode_op(s[0]) + encode_ops(s.drop_first()),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<Op>::empty());
        assert(s.drop_first() =~= Seq::<Op>::empty());
        assert(encode_ops(s) =~= encode_op(s[0]) + encode_ops(s.drop_first()));
    } else {
        let d = s.drop_last();
        lemma_encode_ops_front(d);
        assert(d.drop_first() =~= s.drop_first().drop_last());
        assert(s.drop_first().last() == s.last());
        assert(d[0] == s[0]);
        assert(encode_ops(s) =~= encode_op(s[0]) + encode_ops(s.drop_first()));
    }
}

/// Every bottle of `ops` below 2^64.
pub open spec fn bottles_ok(ops: Seq<Op>) -> bool {
    forall|i: int| 0 <= i < ops.len() ==> op_bottle(#[trigger] ops[i]) < clazel_der::spec::pow256(8)
}

/// Two lists of operations with the same encoding (fewer than 2^64 octets)
/// are the same list.
pub proof fn lemma_ops_injective(a: Seq<Op>, b: Seq<Op>)
    requires
        bottles_ok(a),
        bottles_ok(b),
        encode_ops(a).len() < clazel_der::spec::pow256(8),
        encode_ops(a) == encode_ops(b),
    ensures
        a == b,
    decreases a.len(),
{
    if a.len() == 0 {
        assert(encode_ops(a) =~= Seq::<u8>::empty());
        if b.len() > 0 {
            lemma_encode_ops_front(b);
            lemma_encode_op(b[0]);
        }
        assert(a =~= b);
    } else {
        lemma_encode_ops_front(a);
        lemma_encode_op(a[0]);
        if b.len() == 0 {
            assert(encode_ops(b) =~= Seq::<u8>::empty());
        } else {
            lemma_encode_ops_front(b);
            lemma_peel_op(a[0], encode_ops(a.drop_first()), b[0], encode_ops(b.drop_first()));
            assert forall|i: int| 0 <= i < a.drop_first().len() implies op_bottle(
                #[trigger] a.drop_first()[i],
            ) < clazel_der::spec::pow256(8) by {
                assert(a.drop_first()[i] == a[i + 1]);
            }
            assert forall|i: int| 0 <= i < b.drop_first().len() implies op_bottle(
                #[trigger] b.drop_first()[i],
            ) < clazel_der::spec::pow256(8) by {
                assert(b.drop_first()[i] == b[i + 1]);
            }
            lemma_ops_injective(a.drop_first(), b.drop_first());
            assert(a =~= seq![a[0]] + a.drop_first());
            assert(b =~= seq![b[0]] + b.drop_first());
        }
    }
}

/// A valid transaction's bottles are below 2^64, and its record's pieces
/// are short enough to be TLV contents.
pub proof fn lemma_transaction_ok_bounds(commit: nat, ops: Seq<Op>)
    requires
        transaction_ok(commit, ops),
    ensures
        bottles_ok(ops),
        encode_ops(ops).len() < max_record_len(),
        record_body(commit, ops).len() < max_record_len(),
{
    clazel_der::lemmas::lemma_pow256_8();
    assert forall|i: int| 0 <= i < ops.len() implies op_bottle(#[trigger] ops[i]) < clazel_der::spec::pow256(8) by {
        assert(op_bottle(ops[i]) < clazel_der::spec::pow256(4));
    }
    let body = record_body(commit, ops);
    let check = clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(body));
    lemma_tlv_len(clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE), body + check);
    lemma_tlv_len(clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE), encode_ops(ops));
}

/// Two valid records with the same commit number that start the same
/// octets hold the same transaction, and what follows them is the same.
pub proof fn lemma_record_injective(commit: nat, a: Seq<Op>, r1: Seq<u8>, b: Seq<Op>, r2: Seq<u8>)
    requires
        transaction_ok(commit, a),
        transaction_ok(commit, b),
        encode_record(commit, a) + r1 == encode_record(commit, b) + r2,
    ensures
        a == b,
        r1 == r2,
{
    clazel_der::lemmas::lemma_pow256_8();
    lemma_transaction_ok_bounds(commit, a);
    lemma_transaction_ok_bounds(commit, b);
    let ba = record_body(commit, a);
    let bb = record_body(commit, b);
    let ka = clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(ba));
    let kb = clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(bb));
    let seq_tag = clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE);
    lemma_tlv_len(seq_tag, ba + ka);
    lemma_tlv_len(seq_tag, bb + kb);
    lemma_peel(seq_tag, ba + ka, r1, seq_tag, bb + kb, r2);
    // Inside: the commit, then the operations' SEQUENCE.
    let n = encode_number(commit);
    let sa = clazel_der::spec::encode_sequence(encode_ops(a));
    let sb = clazel_der::spec::encode_sequence(encode_ops(b));
    assert(ba + ka =~= n + (sa + ka));
    assert(bb + kb =~= n + (sb + kb));
    lemma_peel_number(commit, sa + ka, commit, sb + kb);
    lemma_peel(seq_tag, encode_ops(a), ka, seq_tag, encode_ops(b), kb);
    lemma_ops_injective(a, b);
}

// ---------------------------------------------------------------------------
// Lists that fit a file
// ---------------------------------------------------------------------------

/// A shorter list's log is a prefix of a longer one's.
pub proof fn lemma_encode_log_take(identity: Seq<u8>, ts: Seq<Seq<Op>>, k: nat)
    requires
        k <= ts.len(),
    ensures
        encode_log(identity, ts.take(k as int)).is_prefix_of(encode_log(identity, ts)),
    decreases ts.len() - k,
{
    if k == ts.len() {
        assert(ts.take(k as int) =~= ts);
    } else {
        lemma_encode_log_take(identity, ts, k + 1);
        let t = ts.take(k as int + 1);
        assert(t.drop_last() =~= ts.take(k as int));
    }
}

/// A prefix of a list that fits also fits.
pub proof fn lemma_fits_take(identity: Seq<u8>, file: Seq<u8>, ts: Seq<Seq<Op>>, k: nat)
    requires
        fits(identity, file, ts),
        k <= ts.len(),
    ensures
        fits(identity, file, ts.take(k as int)),
{
    lemma_encode_log_take(identity, ts, k);
    let t = ts.take(k as int);
    assert forall|i: int| 0 <= i < t.len() implies transaction_ok((i + 1) as nat, #[trigger] t[i]) by {
        assert(t[i] == ts[i]);
    }
}

/// What follows a prefix `head` of a file starts with `x` when `head + x` is
/// a prefix too.
pub proof fn lemma_prefix_split(head: Seq<u8>, x: Seq<u8>, file: Seq<u8>)
    requires
        (head + x).is_prefix_of(file),
    ensures
        x + file.skip((head.len() + x.len()) as int) == file.skip(head.len() as int),
{
    assert(file.subrange(0, (head + x).len() as int) =~= head + x);
    assert forall|i: int| 0 <= i < x.len() implies #[trigger] x[i] == file.skip(head.len() as int)[i] by {
        assert((head + x)[head.len() + i] == x[i]);
        assert(file.subrange(0, (head + x).len() as int)[head.len() + i] == file[head.len() + i]);
    }
    assert(x + file.skip((head.len() + x.len()) as int) =~= file.skip(head.len() as int));
}

/// Two lists that fit the same file agree as far as the shorter one goes.
pub proof fn lemma_fits_agree(identity: Seq<u8>, file: Seq<u8>, u: Seq<Seq<Op>>, ts: Seq<Seq<Op>>)
    requires
        fits(identity, file, u),
        fits(identity, file, ts),
        ts.len() <= u.len(),
    ensures
        u.take(ts.len() as int) == ts,
    decreases ts.len(),
{
    let k = ts.len();
    if k == 0 {
        assert(u.take(0) =~= ts);
    } else {
        let d = ts.drop_last();
        lemma_fits_take(identity, file, ts, (k - 1) as nat);
        assert(ts.take(k - 1) =~= d);
        lemma_fits_agree(identity, file, u, d);
        lemma_fits_take(identity, file, u, k);
        let uk = u.take(k as int);
        assert(uk.drop_last() =~= u.take(k - 1));
        // Both logs are the same header and records, then record k.
        let head = encode_log(identity, d);
        let ra = encode_record(k, ts.last());
        let rb = encode_record(k, uk.last());
        assert(encode_log(identity, ts) == head + ra);
        assert(encode_log(identity, uk) == head + rb);
        lemma_prefix_split(head, ra, file);
        lemma_prefix_split(head, rb, file);
        let r1 = file.skip((head.len() + ra.len()) as int);
        let r2 = file.skip((head.len() + rb.len()) as int);
        assert(ra + r1 == rb + r2);
        assert(transaction_ok(k, ts[k - 1]));
        assert(transaction_ok(k, uk[k - 1]));
        lemma_record_injective(k, ts.last(), r1, uk.last(), r2);
        assert(uk =~= ts);
    }
}

/// A list that fits and that no longer list beats is the one
/// [`recovered`] picks.
pub proof fn lemma_longest_fit_unique(identity: Seq<u8>, file: Seq<u8>, ts: Seq<Seq<Op>>)
    requires
        longest_fit(identity, file, ts),
    ensures
        (choose|v: Seq<Seq<Op>>| longest_fit(identity, file, v)) == ts,
{
    let v = choose|v: Seq<Seq<Op>>| longest_fit(identity, file, v);
    assert(longest_fit(identity, file, v));
    assert(v.len() <= ts.len());
    assert(ts.len() <= v.len());
    lemma_fits_agree(identity, file, v, ts);
    assert(v.take(ts.len() as int) =~= v);
}

} // verus!

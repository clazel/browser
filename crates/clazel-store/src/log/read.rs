//! The executable recovery, proven to meet [`super::contract`]'s
//! `recover_ensures`.
//!
//! It reads the file from the front, one record at a time, with
//! `clazel-der`'s proven readers, and stops at the first record it cannot
//! read. A record it reads is trusted only once it has been re-encoded
//! with [`super::exec::encode_record`] and compared with the file, octet
//! for octet, so the check value and DER's one-encoding rule need no
//! separate proof. What the readers must be proven to do is the other
//! direction: on the octets of a genuine record they return its
//! operations. Each reader takes the value it is expected to find as a
//! ghost argument and promises to return it whenever its encoding is
//! really there.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The octets `x` are at `pos` in `b`.
pub open spec fn at(b: Seq<u8>, pos: nat, x: Seq<u8>) -> bool {
    pos + x.len() <= b.len() && b.subrange(pos as int, (pos + x.len()) as int) == x
}

/// `x + y` at `pos` is `x` at `pos` and `y` after it.
proof fn lemma_at_split(b: Seq<u8>, pos: nat, x: Seq<u8>, y: Seq<u8>)
    requires
        at(b, pos, x + y),
    ensures
        at(b, pos, x),
        at(b, pos + x.len(), y),
{
    let s = b.subrange(pos as int, (pos + (x + y).len()) as int);
    assert(b.subrange(pos as int, (pos + x.len()) as int) =~= s.subrange(0, x.len() as int));
    assert(s.subrange(0, x.len() as int) =~= x);
    assert(b.subrange((pos + x.len()) as int, (pos + x.len() + y.len()) as int) =~= s.subrange(x.len() as int, s.len() as int));
    assert(s.subrange(x.len() as int, s.len() as int) =~= y);
}

/// Contents equal to `x` at `[cs, ce)` put `x` at `cs`.
proof fn lemma_at_range(b: Seq<u8>, cs: nat, ce: nat, x: Seq<u8>)
    requires
        cs <= ce,
        ce <= b.len(),
        b.subrange(cs as int, ce as int) =~= x,
    ensures
        at(b, cs, x),
        cs + x.len() == ce,
{
}

/// Whether two slices hold the same octets.
pub(crate) fn same(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        let x = match a.get(i) {
            Some(&x) => x,
            None => return false,
        };
        let y = match b.get(i) {
            Some(&y) => y,
            None => return false,
        };
        if x != y {
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(a@ =~= b@);
    true
}

/// A bottle number at `pos`, before `end`: the INTEGER and where it stops.
/// Whenever the INTEGER of a number `e` below 2^32 is there, it returns
/// `e` and the position after it.
fn read_bottle(b: &[u8], pos: usize, end: usize, Ghost(e): Ghost<nat>) -> (r: Option<(u32, usize)>)
    requires
        end <= b.len(),
    ensures
        match r {
            Some((_, next)) => pos < next && next <= end,
            None => true,
        },
        (e < clazel_der::spec::pow256(4) && pos + encode_number(e).len() <= end && at(b@, pos as nat, encode_number(e)))
            ==> r == Some((e as u32, (pos + encode_number(e).len()) as usize)),
{
    let ghost hyp = e < clazel_der::spec::pow256(4) && pos + encode_number(e).len() <= end && at(
        b@,
        pos as nat,
        encode_number(e),
    );
    let ghost m = clazel_der::spec::be_bytes(e, 8);
    proof {
        clazel_der::lemmas::lemma_pow256_8();
        clazel_der::lemmas_typed::lemma_encode_integer_read_integer(b@, pos as nat, end as nat);
        if hyp {
            clazel_der::lemmas::lemma_be_bytes_len(e, 8);
            clazel_der::lemmas_typed::lemma_integer_unsigned_contents(m);
            clazel_der::lemmas_typed::lemma_read_integer_encode_integer_unsigned(m, b@, pos as nat, end as nat);
            clazel_der::lemmas::lemma_be_value_of_be_bytes(e, 8);
        }
    }
    let (negative, ms, me, next) = clazel_der::decode::read_integer(b, pos, end)?;
    let ghost mag = b@.subrange(ms as int, me as int);
    proof {
        if hyp {
            assert(clazel_der::spec::be_value(mag) == e);
            if me - ms >= 5 {
                assert(mag[0] == b@[ms as int]);
                clazel_der::lemmas_tlv::lemma_be_value_leading_nonzero(mag);
                clazel_der::lemmas_tlv::lemma_pow256_monotone(4, (mag.len() - 1) as nat);
            }
        }
    }
    if negative {
        return None;
    }
    // ms <= me.
    let len = me.saturating_sub(ms);
    if len > 4 {
        return None;
    }
    let mut v: u64 = 0;
    let mut k: usize = 0;
    assert(b@.subrange(ms as int, ms as int) =~= Seq::<u8>::empty());
    while k < len
        invariant
            k <= len,
            len <= 4,
            ms + len == me,
            me <= b.len(),
            v as nat == clazel_der::spec::be_value(b@.subrange(ms as int, ms + k)),
            (v as nat) < clazel_der::spec::pow256(k as nat),
        decreases len - k,
    {
        // Never saturates: ms + k < me <= b.len().
        let index = ms.saturating_add(k);
        let octet = match b.get(index) {
            Some(&o) => o,
            None => return None,
        };
        proof {
            let s = b@.subrange(ms as int, ms + k + 1);
            assert(s.drop_last() =~= b@.subrange(ms as int, ms + k));
            assert(s.last() == octet);
            assert(clazel_der::spec::pow256((k + 1) as nat) == 256 * clazel_der::spec::pow256(k as nat));
            clazel_der::lemmas::lemma_pow256_8();
            clazel_der::lemmas_tlv::lemma_pow256_monotone((k + 1) as nat, 4);
        }
        // v < 256^k <= 2^24, so neither step overflows.
        v = v.saturating_mul(256).saturating_add(octet as u64);
        k = k.saturating_add(1);
    }
    proof {
        assert(b@.subrange(ms as int, ms + k) =~= mag);
        clazel_der::lemmas_tlv::lemma_pow256_monotone(len as nat, 4);
    }
    // v < 256^len <= 2^32.
    let bottle = v as u32;
    Some((bottle, next))
}

/// An OCTET STRING at `pos`, before `end`: its contents, borrowed from `b`,
/// and where it stops. Whenever the encoding of `e` is there, it returns
/// `e` and the position after it.
fn read_octets(b: &[u8], pos: usize, end: usize, Ghost(e): Ghost<Seq<u8>>) -> (r: Option<(&[u8], usize)>)
    requires
        end <= b.len(),
    ensures
        match r {
            Some((_, next)) => pos < next && next <= end,
            None => true,
        },
        (pos + clazel_der::spec::encode_octet_string(e).len() <= end && at(
            b@,
            pos as nat,
            clazel_der::spec::encode_octet_string(e),
        )) ==> (r matches Some((s, next)) && s@ == e && next == pos + clazel_der::spec::encode_octet_string(e).len()),
{
    proof {
        clazel_der::lemmas::lemma_pow256_8();
        clazel_der::lemmas::lemma_read_tlv_bounds(b@, pos as nat, end as nat);
        let enc = clazel_der::spec::encode_octet_string(e);
        if pos + enc.len() <= end && at(b@, pos as nat, enc) {
            super::lemmas::lemma_tlv_len(clazel_der::spec::universal_primitive(clazel_der::spec::OCTET_STRING), e);
            clazel_der::lemmas_typed::lemma_read_octets_encode_octets(
                clazel_der::spec::OCTET_STRING,
                e,
                b@,
                pos as nat,
                end as nat,
            );
        }
    }
    let (cs, ce) = clazel_der::decode::read_octet_string(b, pos, end)?;
    Some((vstd::slice::slice_subrange(b, cs, ce), ce))
}

/// One operation at `pos`, before `end`, borrowing its key and value from
/// `b`, and where it stops. Whenever the encoding of `e` (with a bottle
/// below 2^32) is there, it returns `e` and the position after it.
fn read_op<'a>(b: &'a [u8], pos: usize, end: usize, Ghost(e): Ghost<Op>) -> (r: Option<(super::exec::OpRef<'a>, usize)>)
    requires
        end <= b.len(),
    ensures
        match r {
            Some((_, next)) => pos < next && next <= end,
            None => true,
        },
        (op_bottle(e) < clazel_der::spec::pow256(4) && pos + encode_op(e).len() <= end && at(b@, pos as nat, encode_op(e)))
            ==> (r matches Some((op, next)) && op@ == e && next == pos + encode_op(e).len()),
{
    let ghost hyp = op_bottle(e) < clazel_der::spec::pow256(4) && pos + encode_op(e).len() <= end && at(
        b@,
        pos as nat,
        encode_op(e),
    );
    let ghost c = super::lemmas::op_contents(e);
    let ghost tag = clazel_der::spec::context_specific(super::lemmas::op_tag(e), true);
    proof {
        clazel_der::lemmas::lemma_pow256_8();
        clazel_der::lemmas::lemma_read_tlv_bounds(b@, pos as nat, end as nat);
        super::lemmas::lemma_encode_op(e);
        if hyp {
            clazel_der::lemmas_tlv::lemma_read_tlv_encode_tlv(tag, c, b@, pos as nat, end as nat);
        }
    }
    let t = clazel_der::decode::read_tlv(b, pos, end)?;
    let ghost cs = t.cstart as nat;
    proof {
        if hyp {
            lemma_at_range(b@, cs, t.cend as nat, c);
            let n = encode_number(op_bottle(e));
            match e {
                Op::Put { key, value, .. } => {
                    let ok = clazel_der::spec::encode_octet_string(key);
                    let ov = clazel_der::spec::encode_octet_string(value);
                    assert(c =~= n + (ok + ov));
                    lemma_at_split(b@, cs, n, ok + ov);
                    lemma_at_split(b@, cs + n.len(), ok, ov);
                },
                Op::Delete { key, .. } => {
                    lemma_at_split(b@, cs, n, clazel_der::spec::encode_octet_string(key));
                },
                Op::Clear { .. } => {
                    assert(c == n);
                },
            }
        }
    }
    let number = match t.tag.class {
        clazel_der::spec::Class::ContextSpecific if t.tag.constructed => t.tag.number,
        _ => return None,
    };
    let (bottle, p1) = read_bottle(b, t.cstart, t.cend, Ghost(op_bottle(e)))?;
    if number == 2 {
        proof {
            if hyp {
                assert(e is Clear);
            }
        }
        if p1 != t.cend {
            return None;
        }
        return Some((super::exec::OpRef::Clear { bottle }, t.cend));
    }
    if number == 1 {
        let ghost key = match e {
            Op::Delete { key, .. } => key,
            _ => Seq::empty(),
        };
        proof {
            if hyp {
                assert(e is Delete);
            }
        }
        let (k, p2) = read_octets(b, p1, t.cend, Ghost(key))?;
        if p2 != t.cend {
            return None;
        }
        return Some((super::exec::OpRef::Delete { bottle, key: k }, t.cend));
    }
    if number == 0 {
        let ghost (key, value) = match e {
            Op::Put { key, value, .. } => (key, value),
            _ => (Seq::empty(), Seq::empty()),
        };
        proof {
            if hyp {
                assert(e is Put);
            }
        }
        let (k, p2) = read_octets(b, p1, t.cend, Ghost(key))?;
        let (v, p3) = read_octets(b, p2, t.cend, Ghost(value))?;
        if p3 != t.cend {
            return None;
        }
        return Some((super::exec::OpRef::Put { bottle, key: k, value: v }, t.cend));
    }
    None
}

/// Every bottle of `ops` below 2^32.
pub open spec fn bottles_below_32(ops: Seq<Op>) -> bool {
    forall|i: int| 0 <= i < ops.len() ==> op_bottle(#[trigger] ops[i]) < clazel_der::spec::pow256(4)
}

/// The operations filling `[pos, end)`. Whenever those octets are the
/// encoding of `e` (with bottles below 2^32), it returns `e`.
fn read_ops<'a>(b: &'a [u8], pos: usize, end: usize, Ghost(e): Ghost<Seq<Op>>) -> (r: Option<Vec<super::exec::OpRef<'a>>>)
    requires
        pos <= end,
        end <= b.len(),
    ensures
        (bottles_below_32(e) && b@.subrange(pos as int, end as int) == encode_ops(e)) ==> (r matches Some(v)
            && super::exec::ops_view(v@) == e),
{
    let ghost hyp = bottles_below_32(e) && b@.subrange(pos as int, end as int) == encode_ops(e);
    let mut out: Vec<super::exec::OpRef<'a>> = Vec::new();
    let mut p = pos;
    let ghost mut k: nat = 0;
    proof {
        assert(e.skip(0) =~= e);
        assert(super::exec::ops_view(out@) =~= e.take(0));
    }
    while p < end
        invariant
            pos <= p <= end,
            end <= b.len(),
            hyp == (bottles_below_32(e) && b@.subrange(pos as int, end as int) == encode_ops(e)),
            hyp ==> k <= e.len(),
            hyp ==> super::exec::ops_view(out@) == e.take(k as int),
            hyp ==> b@.subrange(p as int, end as int) == encode_ops(e.skip(k as int)),
        decreases end - p,
    {
        let ghost rest = e.skip(k as int);
        let ghost next_op = if k < e.len() { e[k as int] } else { Op::Clear { bottle: 0 } };
        proof {
            if hyp {
                if rest.len() == 0 {
                    assert(encode_ops(rest) =~= Seq::<u8>::empty());
                }
                assert(rest.len() > 0);
                super::lemmas::lemma_encode_ops_front(rest);
                assert(rest[0] == next_op);
                assert(rest.drop_first() =~= e.skip((k + 1) as int));
                lemma_at_range(b@, p as nat, end as nat, encode_ops(rest));
                lemma_at_split(b@, p as nat, encode_op(next_op), encode_ops(e.skip((k + 1) as int)));
                assert(op_bottle(e[k as int]) < clazel_der::spec::pow256(4));
                assert(op_bottle(next_op) < clazel_der::spec::pow256(4));
                assert(p + encode_ops(rest).len() == end);
                assert(encode_ops(rest) == encode_op(next_op) + encode_ops(e.skip((k + 1) as int)));
                assert(p + encode_op(next_op).len() <= end);
                assert(at(b@, p as nat, encode_op(next_op)));
            }
        }
        let (op, q) = read_op(b, p, end, Ghost(next_op))?;
        out.push(op);
        proof {
            if hyp {
                assert(e.take((k + 1) as int) =~= e.take(k as int).push(next_op));
                assert(super::exec::ops_view(out@) =~= e.take((k + 1) as int));
                let tail = encode_ops(e.skip((k + 1) as int));
                assert(b@.subrange(q as int, end as int) =~= tail);
                k = k + 1;
            }
        }
        p = q;
    }
    proof {
        if hyp {
            assert(b@.subrange(p as int, end as int) =~= Seq::<u8>::empty());
            let rest = e.skip(k as int);
            if rest.len() > 0 {
                super::lemmas::lemma_encode_ops_front(rest);
                super::lemmas::lemma_encode_op(rest[0]);
            }
            assert(k == e.len());
            assert(e.take(k as int) =~= e);
        }
    }
    Some(out)
}

/// The record with commit number `commit` at `pos`: its operations,
/// borrowed from `b`, and where it stops. What it returns is a valid
/// transaction whose record is exactly the octets read; and whenever the
/// record of a valid transaction `e` is there, it returns `e`.
fn read_record<'a>(b: &'a [u8], pos: usize, commit: u64, Ghost(e): Ghost<Seq<Op>>) -> (r: Option<
    (Vec<super::exec::OpRef<'a>>, usize),
>)
    ensures
        match r {
            Some((v, next)) => {
                &&& pos < next
                &&& next <= b.len()
                &&& b@.subrange(pos as int, next as int) == encode_record(commit as nat, super::exec::ops_view(v@))
                &&& transaction_ok(commit as nat, super::exec::ops_view(v@))
            },
            None => true,
        },
        (transaction_ok(commit as nat, e) && at(b@, pos as nat, encode_record(commit as nat, e))) ==> (r matches Some((v, _))
            && super::exec::ops_view(v@) == e),
{
    let ghost hyp = transaction_ok(commit as nat, e) && at(b@, pos as nat, encode_record(commit as nat, e));
    let ghost body = record_body(commit as nat, e);
    let ghost check = clazel_der::spec::encode_octet_string(crate::crc32c::spec::crc32c(body));
    let ghost n = encode_number(commit as nat);
    let ghost os = clazel_der::spec::encode_sequence(encode_ops(e));
    proof {
        clazel_der::lemmas::lemma_pow256_8();
        if hyp {
            super::lemmas::lemma_transaction_ok_bounds(commit as nat, e);
            let seq_tag = clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE);
            super::lemmas::lemma_tlv_len(seq_tag, body + check);
            clazel_der::lemmas_typed::lemma_expect_sequence_encode_sequence(body + check, b@, pos as nat, b@.len());
        }
    }
    let (cs, ce) = clazel_der::decode::expect_sequence(b, pos, b.len())?;
    proof {
        if hyp {
            lemma_at_range(b@, cs as nat, ce as nat, body + check);
            assert(body + check =~= n + (os + check));
            lemma_at_split(b@, cs as nat, n, os + check);
            lemma_at_split(b@, (cs + n.len()) as nat, os, check);
            clazel_der::lemmas::lemma_be_bytes_len(commit as nat, 8);
            clazel_der::lemmas_typed::lemma_integer_unsigned_contents(clazel_der::spec::be_bytes(commit as nat, 8));
            clazel_der::lemmas_tlv::lemma_read_tlv_encode_tlv(
                clazel_der::spec::universal_primitive(clazel_der::spec::INTEGER),
                clazel_der::spec::integer_unsigned_contents(clazel_der::spec::be_bytes(commit as nat, 8)),
                b@,
                cs as nat,
                ce as nat,
            );
        }
    }
    let skip = clazel_der::decode::read_tlv(b, cs, ce)?;
    proof {
        if hyp {
            clazel_der::lemmas_typed::lemma_expect_sequence_encode_sequence(encode_ops(e), b@, skip.cend as nat, ce as nat);
        }
    }
    let (ops_start, ops_end) = clazel_der::decode::expect_sequence(b, skip.cend, ce)?;
    proof {
        if hyp {
            assert forall|i: int| 0 <= i < e.len() implies op_bottle(#[trigger] e[i]) < clazel_der::spec::pow256(4) by {}
        }
    }
    let ops = read_ops(b, ops_start, ops_end, Ghost(e))?;
    let record = super::exec::encode_record(commit, ops.as_slice())?;
    if record.len() > b.len().saturating_sub(pos) || pos > b.len() {
        return None;
    }
    // pos + record.len() <= b.len(): never saturates.
    let next = pos.saturating_add(record.len());
    if !same(record.as_slice(), vstd::slice::slice_subrange(b, pos, next)) {
        return None;
    }
    proof {
        super::lemmas::lemma_tlv_len(
            clazel_der::spec::universal_constructed(clazel_der::spec::SEQUENCE),
            record_body(commit as nat, super::exec::ops_view(ops@)) + clazel_der::spec::encode_octet_string(
                crate::crc32c::spec::crc32c(record_body(commit as nat, super::exec::ops_view(ops@))),
            ),
        );
    }
    Some((ops, next))
}

/// When a longer list fits, its next transaction is valid and its record
/// follows the log of the list recovered so far.
proof fn lemma_next_record(identity: Seq<u8>, file: Seq<u8>, done: Seq<Seq<Op>>, w: Seq<Seq<Op>>)
    requires
        fits(identity, file, done),
        fits(identity, file, w),
        w.len() > done.len(),
    ensures
        transaction_ok((done.len() + 1) as nat, w[done.len() as int]),
        at(file, encode_log(identity, done).len(), encode_record((done.len() + 1) as nat, w[done.len() as int])),
{
    let k = done.len();
    super::lemmas::lemma_fits_agree(identity, file, w, done);
    super::lemmas::lemma_fits_take(identity, file, w, (k + 1) as nat);
    let wk = w.take((k + 1) as int);
    assert(wk.drop_last() =~= w.take(k as int));
    let e = w[k as int];
    assert(wk.last() == e);
    let head = encode_log(identity, done);
    let rec = encode_record((k + 1) as nat, e);
    assert(encode_log(identity, wk) == head + rec);
    assert(file.subrange(0, (head + rec).len() as int) =~= head + rec);
    assert(at(file, 0, head + rec));
    lemma_at_split(file, 0, head, rec);
}

/// A valid next transaction whose record follows the log extends the list
/// that fits.
proof fn lemma_extend(identity: Seq<u8>, file: Seq<u8>, done: Seq<Seq<Op>>, x: Seq<Op>, next: nat)
    requires
        fits(identity, file, done),
        transaction_ok((done.len() + 1) as nat, x),
        encode_log(identity, done).len() < next,
        next <= file.len(),
        file.subrange(encode_log(identity, done).len() as int, next as int) == encode_record((done.len() + 1) as nat, x),
    ensures
        fits(identity, file, done.push(x)),
        next == encode_log(identity, done.push(x)).len(),
{
    let now = done.push(x);
    let head = encode_log(identity, done);
    let rec = encode_record((done.len() + 1) as nat, x);
    assert(now.drop_last() =~= done);
    assert(encode_log(identity, now) == head + rec);
    assert(file.subrange(0, head.len() as int) =~= head);
    assert(file.subrange(0, next as int) =~= head + rec);
    assert forall|i: int| 0 <= i < now.len() implies transaction_ok((i + 1) as nat, #[trigger] now[i]) by {
        if i < done.len() {
            assert(now[i] == done[i]);
        }
    }
}

/// The transaction lists the executable lists stand for.
pub open spec fn log_view(ts: Seq<Vec<super::exec::OpRef>>) -> Seq<Seq<Op>> {
    ts.map_values(|v: Vec<super::exec::OpRef>| super::exec::ops_view(v@))
}

/// The view of an optional recovery; `None` is a refused file.
pub open spec fn recovery_view(r: Option<Vec<Vec<super::exec::OpRef>>>) -> Option<Seq<Seq<Op>>> {
    match r {
        Some(ts) => Some(log_view(ts@)),
        None => None,
    }
}

/// What opening `file` as the log of bucket `identity` recovers: the
/// transactions of the longest run of valid records after the header,
/// borrowing their keys and values from `file`, or `None` when the identity
/// is over its limit or the file does not start with its header.
pub fn recover<'a>(identity: &[u8], file: &'a [u8]) -> (r: Option<Vec<Vec<super::exec::OpRef<'a>>>>)
    ensures
        super::contract::recover_ensures(identity@, file@, recovery_view(r)),
{
    if identity.len() > 4096 {
        return None;
    }
    let header = super::exec::encode_header(identity);
    if header.len() > file.len() {
        return None;
    }
    if !same(header.as_slice(), vstd::slice::slice_subrange(file, 0, header.len())) {
        return None;
    }
    let mut ts: Vec<Vec<super::exec::OpRef<'a>>> = Vec::new();
    let mut pos = header.len();
    let mut count: u64 = 0;
    proof {
        assert(log_view(ts@) =~= Seq::<Seq<Op>>::empty());
        assert(encode_log(identity@, log_view(ts@)) == encode_header(identity@));
    }
    loop
        invariant
            pos <= file.len(),
            count as nat == ts@.len(),
            fits(identity@, file@, log_view(ts@)),
            pos as nat == encode_log(identity@, log_view(ts@)).len(),
        ensures
            fits(identity@, file@, log_view(ts@)),
            forall|u: Seq<Seq<Op>>| #[trigger] fits(identity@, file@, u) ==> u.len() <= ts@.len(),
        decreases file.len() - pos,
    {
        let ghost done = log_view(ts@);
        let ghost longer = exists|u: Seq<Seq<Op>>| #[trigger] fits(identity@, file@, u) && u.len() > count;
        let ghost witness = choose|u: Seq<Seq<Op>>| #[trigger] fits(identity@, file@, u) && u.len() > count;
        let ghost e = if longer { witness[count as int] } else { Seq::empty() };
        proof {
            if longer {
                lemma_next_record(identity@, file@, done, witness);
            }
        }
        if count == u64::MAX {
            proof {
                clazel_der::lemmas::lemma_pow256_8();
                assert forall|u: Seq<Seq<Op>>| #[trigger] fits(identity@, file@, u) implies u.len() <= ts@.len() by {
                    if u.len() > ts@.len() {
                        assert(transaction_ok((count + 1) as nat, u[count as int]));
                    }
                }
            }
            break;
        }
        // Never saturates: count < u64::MAX.
        let commit = count.saturating_add(1);
        match read_record(file, pos, commit, Ghost(e)) {
            None => {
                proof {
                    assert(!longer);
                    assert forall|u: Seq<Seq<Op>>| #[trigger] fits(identity@, file@, u) implies u.len() <= ts@.len() by {
                        if u.len() > ts@.len() {
                            assert(longer);
                        }
                    }
                }
                break;
            },
            Some((ops, next)) => {
                let ghost x = super::exec::ops_view(ops@);
                ts.push(ops);
                proof {
                    assert(log_view(ts@) =~= done.push(x));
                    lemma_extend(identity@, file@, done, x, next as nat);
                }
                pos = next;
                count = commit;
            },
        }
    }
    proof {
        super::lemmas::lemma_longest_fit_unique(identity@, file@, log_view(ts@));
    }
    Some(ts)
}

} // verus!

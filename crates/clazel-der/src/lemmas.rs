//! Facts proven about the spec itself ([`super::spec`]). They are evidence
//! that the transcription is right, not part of what the implementation
//! must meet. The ones that matter are listed in `README.md`: no over-read
//! ([`lemma_read_tlv_no_overread`] and the typed readers'), the round trip
//! ([`lemma_read_tlv_encode_tlv`]), canonicity ([`lemma_encode_read_tlv`]
//! and the typed ones), the bounded reservation
//! ([`lemma_oid_components_bound`], [`lemma_encode_tlv_len`]) and the
//! shortest length ([`lemma_encode_length_shortest`],
//! [`lemma_read_length_encode_length`], [`lemma_encode_read_length`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Network byte order.
// ---------------------------------------------------------------------------

/// Eight octets hold exactly the values of a `u64`.
pub proof fn lemma_pow256_8()
    ensures
        pow256(8) == 0x1_0000_0000_0000_0000,
        pow256(7) == 0x100_0000_0000_0000,
        pow256(6) == 0x1_0000_0000_0000,
        pow256(5) == 0x100_0000_0000,
        pow256(4) == 0x1_0000_0000,
        pow256(3) == 0x100_0000,
        pow256(2) == 0x1_0000,
        pow256(1) == 256,
{
    assert(pow256(8) == 0x1_0000_0000_0000_0000) by (compute_only);
    assert(pow256(7) == 0x100_0000_0000_0000) by (compute_only);
    assert(pow256(6) == 0x1_0000_0000_0000) by (compute_only);
    assert(pow256(5) == 0x100_0000_0000) by (compute_only);
    assert(pow256(4) == 0x1_0000_0000) by (compute_only);
    assert(pow256(3) == 0x100_0000) by (compute_only);
    assert(pow256(2) == 0x1_0000) by (compute_only);
    assert(pow256(1) == 256) by (compute_only);
}

/// 256^n is at least 1.
pub proof fn lemma_pow256_positive(n: nat)
    ensures
        pow256(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow256_positive((n - 1) as nat);
    }
}

/// Up to eight octets fit in a `u64`.
pub proof fn lemma_pow256_at_most_8(n: nat)
    requires
        n <= 8,
    ensures
        pow256(n) <= 0x1_0000_0000_0000_0000,
    decreases 8 - n,
{
    if n < 8 {
        lemma_pow256_at_most_8(n + 1);
        lemma_pow256_positive(n);
        assert(pow256(n + 1) == 256 * pow256(n));
    } else {
        lemma_pow256_8();
    }
}

/// `n` octets spell a number below 256^n.
pub proof fn lemma_be_value_bound(s: Seq<u8>)
    ensures
        be_value(s) < pow256(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_be_value_bound(s.drop_last());
        assert(be_value(s) == be_value(s.drop_last()) * 256 + s.last() as nat);
        assert(pow256(s.len()) == 256 * pow256((s.len() - 1) as nat));
    }
}

/// `be_bytes(v, w)` has `w` octets.
pub proof fn lemma_be_bytes_len(v: nat, w: nat)
    ensures
        be_bytes(v, w).len() == w,
    decreases w,
{
    if w > 0 {
        lemma_be_bytes_len(v / 256, (w - 1) as nat);
    }
}

/// Reading back what [`be_bytes`] wrote: any `v` below 256^w survives.
pub proof fn lemma_be_value_of_be_bytes(v: nat, w: nat)
    requires
        v < pow256(w),
    ensures
        be_value(be_bytes(v, w)) == v,
    decreases w,
{
    if w > 0 {
        let rest = be_bytes(v / 256, (w - 1) as nat);
        assert(pow256(w) == 256 * pow256((w - 1) as nat));
        assert(v / 256 < pow256((w - 1) as nat));
        lemma_be_value_of_be_bytes(v / 256, (w - 1) as nat);
        lemma_be_bytes_len(v / 256, (w - 1) as nat);
        let s = rest.push((v % 256) as u8);
        assert(s.drop_last() =~= rest);
        assert(s.last() == (v % 256) as u8);
        assert(be_value(s) == be_value(rest) * 256 + (v % 256) as nat);
        assert(v == (v / 256) * 256 + v % 256);
    }
}

/// Writing what [`be_value`] read: `s` is spelled back octet for octet.
pub proof fn lemma_be_bytes_of_be_value(s: Seq<u8>)
    ensures
        be_bytes(be_value(s), s.len()) =~= s,
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_be_bytes_of_be_value(d);
        let v = be_value(s);
        assert(v == be_value(d) * 256 + s.last() as nat);
        assert(v / 256 == be_value(d)) by (nonlinear_arith)
            requires
                v == be_value(d) * 256 + s.last() as nat,
                s.last() < 256,
        ;
        assert(v % 256 == s.last() as nat) by (nonlinear_arith)
            requires
                v == be_value(d) * 256 + s.last() as nat,
                s.last() < 256,
        ;
        assert(be_bytes(v, s.len()) =~= be_bytes(v / 256, d.len()).push((v % 256) as u8));
        assert(d.push(s.last()) =~= s);
    }
}

// ---------------------------------------------------------------------------
// Base 128 series.
// ---------------------------------------------------------------------------

/// Appending an octet to a series: the number shifts by one digit.
pub proof fn lemma_base128_push(s: Seq<u8>, x: u8)
    ensures
        base128(s.push(x)) == base128(s) * 128 + (x % 128) as nat,
{
    assert(s.push(x).drop_last() =~= s);
}

/// A longer series spells a number at least as large: the later digits only
/// append. (This is what lets a reader stop at once on a number that is too
/// large: nothing that follows makes it smaller.)
pub proof fn lemma_base128_monotone(b: Seq<u8>, start: int, i: int, j: int)
    requires
        0 <= start <= i <= j <= b.len(),
    ensures
        base128(b.subrange(start, i)) <= base128(b.subrange(start, j)),
    decreases j - i,
{
    if i < j {
        lemma_base128_monotone(b, start, i, j - 1);
        assert(b.subrange(start, j) =~= b.subrange(start, j - 1).push(b[j - 1]));
        lemma_base128_push(b.subrange(start, j - 1), b[j - 1]);
    }
}

/// If every octet of `b[start..i)` has bit 8 set, the series that starts at
/// `start` ends where the one that starts at `i` does.
pub proof fn lemma_series_end_skip(b: Seq<u8>, start: nat, i: nat, end: nat)
    requires
        start <= i,
        forall|k: int| start <= k < i ==> #[trigger] b[k] >= 128,
    ensures
        series_end(b, start, end) == series_end(b, i, end),
    decreases i - start,
{
    if start < i {
        if start < end {
            assert(b[start as int] >= 128);
        }
        lemma_series_end_skip(b, start + 1, i, end);
    }
}

/// A series that ends ends at an index in `[i, end)` (re-export of the fact
/// the spec's termination proof uses).
pub proof fn lemma_series_end_in_range(b: Seq<u8>, i: nat, end: nat)
    ensures
        match series_end(b, i, end) {
            Some(j) => i <= j && j < end && b[j as int] < 128,
            None => true,
        },
    decreases end - i,
{
    if i < end && b[i as int] >= 128 {
        lemma_series_end_in_range(b, i + 1, end);
    }
}


/// Shifting a sequence by `k` shifts where a series ends.
pub proof fn lemma_series_end_shift(b: Seq<u8>, k: nat, s: nat, e: nat)
    requires
        k <= e <= b.len(),
    ensures
        series_end(b, s + k, e) == match series_end(b.skip(k as int), s, (e - k) as nat) {
            Some(j) => Some(j + k),
            None => None,
        },
    decreases e - k - s,
{
    if s < e - k {
        assert(b.skip(k as int)[s as int] == b[(s + k) as int]);
        if b[(s + k) as int] >= 128 {
            lemma_series_end_shift(b, k, s + 1, e);
        }
    }
}

/// One step of [`subidentifiers`] on the suffix of `c` from `i`: the first
/// series ends at `j`, and what follows is the suffix from `j + 1`.
pub proof fn lemma_subidentifiers_step(c: Seq<u8>, i: nat)
    requires
        i < c.len(),
    ensures
        subidentifiers(c.skip(i as int)) == match series_end(c, i, c.len()) {
            None => None,
            Some(j) => {
                let v = base128(c.subrange(i as int, j as int + 1));
                if c[i as int] == 128 {
                    None
                } else if v >= 0x1_0000_0000_0000_0000 {
                    None
                } else {
                    match subidentifiers(c.skip(j as int + 1)) {
                        None => None,
                        Some(rest) => Some(seq![v] + rest),
                    }
                }
            },
        },
{
    let rest = c.skip(i as int);
    lemma_series_end_shift(c, i, 0, c.len());
    assert(rest.len() == c.len() - i);
    assert(rest[0] == c[i as int]);
    lemma_series_end_in_range(c, i, c.len());
    if let Some(j) = series_end(c, i, c.len()) {
        let j2 = (j - i) as nat;
        assert(series_end(rest, 0, rest.len()) == Some(j2));
        assert(rest.subrange(0, j2 as int + 1) =~= c.subrange(i as int, j as int + 1));
        assert(rest.skip(j2 as int + 1) =~= c.skip(j as int + 1));
    }
}

/// An empty suffix has no subidentifiers.
pub proof fn lemma_subidentifiers_empty(c: Seq<u8>)
    requires
        c.len() == 0,
    ensures
        subidentifiers(c) == Some(Seq::<nat>::empty()),
{
}

// ---------------------------------------------------------------------------
// Where a reader stops.
// ---------------------------------------------------------------------------

/// The identifier octets that were read are at least one, lie inside
/// `[pos, end)`, and the tag number is one the decoder accepts.
pub proof fn lemma_read_identifier_bounds(b: Seq<u8>, pos: nat, end: nat)
    ensures
        match read_identifier(b, pos, end) {
            Some((tag, n)) => n >= 1 && pos + n <= end && tag.number <= MAX_TAG_NUMBER,
            None => true,
        },
{
    if pos < end && b[pos as int] % 32 == 31 {
        lemma_series_end_in_range(b, pos + 1, end);
    }
}

/// The length octets that were read are at least one and lie inside
/// `[pos, end)`.
pub proof fn lemma_read_length_bounds(b: Seq<u8>, pos: nat, end: nat)
    ensures
        match read_length(b, pos, end) {
            Some((v, n)) => n >= 1 && pos + n <= end,
            None => true,
        },
{
}

/// A value read starts after `pos`, its contents lie inside `[pos, end)`,
/// and its tag number is one the decoder accepts.
pub proof fn lemma_read_tlv_bounds(b: Seq<u8>, pos: nat, end: nat)
    ensures
        match read_tlv(b, pos, end) {
            Some(t) => pos < t.cstart && t.cstart <= t.cend && t.cend <= end && t.tag.number <= MAX_TAG_NUMBER,
            None => true,
        },
{
    lemma_read_identifier_bounds(b, pos, end);
    if let Some((tag, id_len)) = read_identifier(b, pos, end) {
        lemma_read_length_bounds(b, pos + id_len, end);
    }
}


// ---------------------------------------------------------------------------
// The sizes of what the encoder writes.
// ---------------------------------------------------------------------------

/// The identifier octets of an acceptable tag are one to three.
pub proof fn lemma_encode_identifier_len(tag: Tag)
    requires
        tag.number <= MAX_TAG_NUMBER,
    ensures
        1 <= encode_identifier(tag).len() <= 3,
{
}

/// The length octets of a length below 2^64 are one to nine.
pub proof fn lemma_encode_length_len(len: nat)
    requires
        len < pow256(8),
    ensures
        1 <= encode_length(len).len() <= 9,
{
    lemma_pow256_8();
    if len >= 128 {
        lemma_be_bytes_len(len, length_octets(len));
    }
}

/// The encoding of a value is its contents and at most 12 octets more: the
/// encoder never writes more than it was given plus a header.
pub proof fn lemma_encode_tlv_len(tag: Tag, contents: Seq<u8>)
    requires
        tlv_ok(tag, contents),
    ensures
        encode_tlv(tag, contents).len() <= contents.len() + 12,
{
    lemma_encode_identifier_len(tag);
    lemma_encode_length_len(contents.len());
}

// ---------------------------------------------------------------------------
// Subidentifiers.
// ---------------------------------------------------------------------------

/// `encode_subidentifiers` of a concatenation is the concatenation of the
/// `encode_subidentifiers`.
pub proof fn lemma_encode_subidentifiers_append(a: Seq<nat>, c: Seq<nat>)
    ensures
        encode_subidentifiers(a + c) =~= encode_subidentifiers(a) + encode_subidentifiers(c),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a + c =~= c);
    } else {
        lemma_encode_subidentifiers_append(a.drop_first(), c);
        assert((a + c).drop_first() =~= a.drop_first() + c);
        assert((a + c)[0] == a[0]);
        assert(encode_subidentifier(a[0]) + (encode_subidentifiers(a.drop_first()) + encode_subidentifiers(c))
            =~= (encode_subidentifier(a[0]) + encode_subidentifiers(a.drop_first())) + encode_subidentifiers(c));
    }
}

/// One subidentifier's encoding.
pub proof fn lemma_encode_subidentifiers_single(v: nat)
    ensures
        encode_subidentifiers(seq![v]) =~= encode_subidentifier(v),
{
    let e = Seq::<nat>::empty();
    assert(seq![v].len() == 1);
    assert(seq![v][0] == v);
    assert(seq![v].drop_first() =~= e);
    assert(encode_subidentifiers(e) =~= Seq::<u8>::empty());
    assert(encode_subidentifier(v) + Seq::<u8>::empty() =~= encode_subidentifier(v));
}

} // verus!

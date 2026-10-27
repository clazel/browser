//! No over-read: every reader consults only the bytes of the value it
//! reads, `[pos, cend)`, and never a byte at or after `end`. Stated as: if a
//! reader succeeds on `b1`, then it succeeds with the same result on any
//! other input `b2` (and any other end) that agrees with `b1` on the bytes
//! the value occupies. The bytes after the value, and after `end`, are
//! free. Evidence that the transcription is right, not part of what the
//! implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `b1` and `b2` hold the same octets at every index in `[lo, hi)`.
pub open spec fn agree(b1: Seq<u8>, b2: Seq<u8>, lo: nat, hi: nat) -> bool {
    forall|k: int| lo <= k < hi ==> #[trigger] b1[k] == #[trigger] b2[k]
}

/// A series that ends at `j` in `b1` ends there in `b2`, if the two agree
/// up to `j` and `j` is before the second input's end.
pub proof fn lemma_series_end_agree(b1: Seq<u8>, b2: Seq<u8>, i: nat, e1: nat, e2: nat, j: nat)
    requires
        series_end(b1, i, e1) == Some(j),
        j < e2,
        agree(b1, b2, i, j + 1),
    ensures
        series_end(b2, i, e2) == Some(j),
    decreases j - i,
{
    super::lemmas::lemma_series_end_in_range(b1, i, e1);
    if i < j {
        assert(b1[i as int] == b2[i as int]);
        lemma_series_end_agree(b1, b2, i + 1, e1, e2, j);
    } else {
        assert(b1[i as int] == b2[i as int]);
    }
}

/// An identifier read from `b1` reads the same from `b2` when the two agree
/// on the identifier octets.
pub proof fn lemma_read_identifier_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_identifier(b1, pos, e1) is Some,
        pos + read_identifier(b1, pos, e1).unwrap().1 <= e2,
        agree(b1, b2, pos, pos + read_identifier(b1, pos, e1).unwrap().1),
    ensures
        read_identifier(b2, pos, e2) == read_identifier(b1, pos, e1),
{
    super::lemmas::lemma_read_identifier_bounds(b1, pos, e1);
    let (tag, n) = read_identifier(b1, pos, e1).unwrap();
    assert(b1[pos as int] == b2[pos as int]);
    if b1[pos as int] % 32 == 31 {
        super::lemmas::lemma_series_end_in_range(b1, pos + 1, e1);
        let j = series_end(b1, pos + 1, e1).unwrap();
        assert(j + 1 == pos + n);
        lemma_series_end_agree(b1, b2, pos + 1, e1, e2, j);
        assert(b1.subrange(pos as int + 1, j as int + 1) =~= b2.subrange(pos as int + 1, j as int + 1));
        assert(b1[pos as int + 1] == b2[pos as int + 1]);
    }
}

/// A length read from `b1` reads the same from `b2` when the two agree on
/// the length octets.
pub proof fn lemma_read_length_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_length(b1, pos, e1) is Some,
        pos + read_length(b1, pos, e1).unwrap().1 <= e2,
        agree(b1, b2, pos, pos + read_length(b1, pos, e1).unwrap().1),
    ensures
        read_length(b2, pos, e2) == read_length(b1, pos, e1),
{
    super::lemmas::lemma_read_length_bounds(b1, pos, e1);
    let (v, n) = read_length(b1, pos, e1).unwrap();
    assert(b1[pos as int] == b2[pos as int]);
    if b1[pos as int] >= 128 {
        let k = (b1[pos as int] - 128) as nat;
        assert(n == 1 + k);
        assert(b1[pos as int + 1] == b2[pos as int + 1]);
        assert(b1.subrange(pos as int + 1, pos as int + 1 + k as int) =~= b2.subrange(pos as int + 1, pos as int + 1 + k as int));
    }
}

/// A value read from `b1` reads the same from `b2` when the two agree on
/// the bytes the value occupies, `[pos, cend)`: the decoder consults no
/// byte after the length it read, and none at or after `end`.
pub proof fn lemma_read_tlv_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_tlv(b1, pos, e1) is Some,
        read_tlv(b1, pos, e1).unwrap().cend <= e2,
        agree(b1, b2, pos, read_tlv(b1, pos, e1).unwrap().cend),
    ensures
        read_tlv(b2, pos, e2) == read_tlv(b1, pos, e1),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    let t = read_tlv(b1, pos, e1).unwrap();
    super::lemmas::lemma_read_identifier_bounds(b1, pos, e1);
    let (tag, id_len) = read_identifier(b1, pos, e1).unwrap();
    lemma_read_identifier_no_overread(b1, b2, pos, e1, e2);
    super::lemmas::lemma_read_length_bounds(b1, pos + id_len, e1);
    let (len, len_len) = read_length(b1, pos + id_len, e1).unwrap();
    lemma_read_length_no_overread(b1, b2, pos + id_len, e1, e2);
}

/// The result of reading a value depends only on the bytes in `[pos,
/// end)`: two inputs that agree there give the same result, success or
/// failure.
pub proof fn lemma_read_tlv_within_end(b1: Seq<u8>, b2: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b1.len(),
        end <= b2.len(),
        agree(b1, b2, pos, end),
    ensures
        read_tlv(b2, pos, end) == read_tlv(b1, pos, end),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, end);
    super::lemmas::lemma_read_tlv_bounds(b2, pos, end);
    if read_tlv(b1, pos, end) is Some {
        lemma_read_tlv_no_overread(b1, b2, pos, end, end);
    } else if read_tlv(b2, pos, end) is Some {
        assert(forall|k: int| pos <= k < end ==> b2[k] == b1[k]);
        lemma_read_tlv_no_overread(b2, b1, pos, end, end);
    }
}

/// The contents of a value read from `b1` are the same octets in `b2`.
pub proof fn lemma_contents_agree(b1: Seq<u8>, b2: Seq<u8>, cstart: nat, cend: nat)
    requires
        cstart <= cend <= b1.len(),
        cend <= b2.len(),
        agree(b1, b2, cstart, cend),
    ensures
        b1.subrange(cstart as int, cend as int) =~= b2.subrange(cstart as int, cend as int),
{
}

/// A BOOLEAN read from `b1` reads the same from `b2` when the two agree on
/// the octets it occupies.
pub proof fn lemma_read_boolean_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_boolean(b1, pos, e1) is Some,
        read_boolean(b1, pos, e1).unwrap().1 <= e2,
        agree(b1, b2, pos, read_boolean(b1, pos, e1).unwrap().1),
    ensures
        read_boolean(b2, pos, e2) == read_boolean(b1, pos, e1),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    let t = read_tlv(b1, pos, e1).unwrap();
    lemma_read_tlv_no_overread(b1, b2, pos, e1, e2);
    lemma_contents_agree(b1, b2, t.cstart, t.cend);
}

/// An INTEGER read from `b1` reads the same from `b2` when the two agree on
/// the octets it occupies.
pub proof fn lemma_read_integer_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_integer(b1, pos, e1) is Some,
        read_integer(b1, pos, e1).unwrap().3 <= e2,
        agree(b1, b2, pos, read_integer(b1, pos, e1).unwrap().3),
    ensures
        read_integer(b2, pos, e2) == read_integer(b1, pos, e1),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    let t = read_tlv(b1, pos, e1).unwrap();
    lemma_read_tlv_no_overread(b1, b2, pos, e1, e2);
    lemma_contents_agree(b1, b2, t.cstart, t.cend);
}

/// A BIT STRING read from `b1` reads the same from `b2` when the two agree
/// on the octets it occupies.
pub proof fn lemma_read_bit_string_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_bit_string(b1, pos, e1) is Some,
        read_bit_string(b1, pos, e1).unwrap().3 <= e2,
        agree(b1, b2, pos, read_bit_string(b1, pos, e1).unwrap().3),
    ensures
        read_bit_string(b2, pos, e2) == read_bit_string(b1, pos, e1),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    let t = read_tlv(b1, pos, e1).unwrap();
    lemma_read_tlv_no_overread(b1, b2, pos, e1, e2);
    lemma_contents_agree(b1, b2, t.cstart, t.cend);
}

/// A string (or OCTET STRING) read from `b1` reads the same from `b2` when
/// the two agree on the octets it occupies.
pub proof fn lemma_read_octets_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat, number: u32)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_octets(b1, pos, e1, number) is Some,
        read_octets(b1, pos, e1, number).unwrap().1 <= e2,
        agree(b1, b2, pos, read_octets(b1, pos, e1, number).unwrap().1),
    ensures
        read_octets(b2, pos, e2, number) == read_octets(b1, pos, e1, number),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    lemma_read_tlv_no_overread(b1, b2, pos, e1, e2);
}

/// A NULL read from `b1` reads the same from `b2` when the two agree on the
/// octets it occupies.
pub proof fn lemma_read_null_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_null(b1, pos, e1) is Some,
        read_null(b1, pos, e1).unwrap() <= e2,
        agree(b1, b2, pos, read_null(b1, pos, e1).unwrap()),
    ensures
        read_null(b2, pos, e2) == read_null(b1, pos, e1),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    lemma_read_tlv_no_overread(b1, b2, pos, e1, e2);
}

/// An OBJECT IDENTIFIER read from `b1` reads the same from `b2` when the
/// two agree on the octets it occupies.
pub proof fn lemma_read_oid_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_oid(b1, pos, e1) is Some,
        read_oid(b1, pos, e1).unwrap().1 <= e2,
        agree(b1, b2, pos, read_oid(b1, pos, e1).unwrap().1),
    ensures
        read_oid(b2, pos, e2) == read_oid(b1, pos, e1),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    let t = read_tlv(b1, pos, e1).unwrap();
    lemma_read_tlv_no_overread(b1, b2, pos, e1, e2);
    lemma_contents_agree(b1, b2, t.cstart, t.cend);
}

/// A SEQUENCE or SET (or any universal constructed value) read from `b1`
/// reads the same from `b2` when the two agree on the octets it occupies.
pub proof fn lemma_expect_constructed_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat, number: u32)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        expect_constructed(b1, pos, e1, number) is Some,
        expect_constructed(b1, pos, e1, number).unwrap().1 <= e2,
        agree(b1, b2, pos, expect_constructed(b1, pos, e1, number).unwrap().1),
    ensures
        expect_constructed(b2, pos, e2, number) == expect_constructed(b1, pos, e1, number),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    lemma_read_tlv_no_overread(b1, b2, pos, e1, e2);
}

/// An OPTIONAL context-specific component that is present in `b1` is
/// present, the same, in `b2` when the two agree on the octets it occupies.
pub proof fn lemma_read_optional_context_no_overread(b1: Seq<u8>, b2: Seq<u8>, pos: nat, e1: nat, e2: nat, number: u32)
    requires
        e1 <= b1.len(),
        e2 <= b2.len(),
        read_optional_context(b1, pos, e1, number) matches Some(Some(_)),
        read_optional_context(b1, pos, e1, number).unwrap().unwrap().2 <= e2,
        agree(b1, b2, pos, read_optional_context(b1, pos, e1, number).unwrap().unwrap().2),
    ensures
        read_optional_context(b2, pos, e2, number) == read_optional_context(b1, pos, e1, number),
{
    super::lemmas::lemma_read_tlv_bounds(b1, pos, e1);
    super::lemmas::lemma_read_identifier_bounds(b1, pos, e1);
    let t = read_tlv(b1, pos, e1).unwrap();
    lemma_read_tlv_no_overread(b1, b2, pos, e1, e2);
    lemma_read_identifier_no_overread(b1, b2, pos, e1, e2);
}

} // verus!

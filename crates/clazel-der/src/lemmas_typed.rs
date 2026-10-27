//! Facts proven about the typed readers and encoders of the spec
//! ([`super::spec`]): for each universal type, reading what the encoder
//! wrote gives back the value (round trip), and encoding what the reader
//! read gives back the original bytes (DER canonicity, so no two byte strings
//! are accepted as the same value). Each canonicity lemma states its class
//! in its postcondition: the INTEGERs it covers are the non-negative ones.
//! Evidence that the transcription is right, not part of what the
//! implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// BOOLEAN.
// ---------------------------------------------------------------------------

/// A BOOLEAN's contents are the one octet the encoder writes.
pub proof fn lemma_boolean_contents(v: bool)
    ensures
        boolean_contents(seq![if v { 0xFFu8 } else { 0x00u8 }]) == Some(v),
{
}

/// Reading what [`encode_boolean`] wrote.
pub proof fn lemma_read_boolean_encode_boolean(v: bool, b: Seq<u8>, pos: nat, end: nat)
    requires
        pos + encode_boolean(v).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_boolean(v).len()) as int) =~= encode_boolean(v),
    ensures
        read_boolean(b, pos, end) == Some((v, (pos + encode_boolean(v).len()) as nat)),
{
    super::lemmas::lemma_pow256_8();
    let contents = seq![if v { 0xFFu8 } else { 0x00u8 }];
    let tag = universal_primitive(BOOLEAN);
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(tag, contents, b, pos, end);
    lemma_boolean_contents(v);
}

/// Writing what [`read_boolean`] read: the bytes are the encoding of the
/// value that was read.
pub proof fn lemma_encode_boolean_read_boolean(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_boolean(b, pos, end) {
            Some((v, next)) => next <= end && b.subrange(pos as int, next as int) =~= encode_boolean(v),
            None => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
    if let Some((v, next)) = read_boolean(b, pos, end) {
        let t = read_tlv(b, pos, end).unwrap();
        let c = b.subrange(t.cstart as int, t.cend as int);
        assert(c =~= seq![if v { 0xFFu8 } else { 0x00u8 }]);
    }
}

// ---------------------------------------------------------------------------
// INTEGER.
// ---------------------------------------------------------------------------

/// One octet spells itself.
pub proof fn lemma_be_value_single(x: u8)
    ensures
        be_value(seq![x]) == x as nat,
{
    assert(seq![x].drop_last() =~= Seq::<u8>::empty());
    assert(be_value(Seq::<u8>::empty()) == 0);
}

/// Leading zeros do not change the number an octet string spells.
pub proof fn lemma_strip_leading_zeros_value(m: Seq<u8>)
    ensures
        be_value(strip_leading_zeros(m)) == be_value(m),
        strip_leading_zeros(m).len() <= m.len(),
        strip_leading_zeros(m).len() >= 1 ==> strip_leading_zeros(m)[0] != 0,
    decreases m.len(),
{
    if m.len() > 0 && m[0] == 0 {
        let d = m.skip(1);
        lemma_strip_leading_zeros_value(d);
        assert(d =~= m.drop_first());
        lemma_be_value_leading_zero_skip(m);
    }
}

/// An octet string with a zero first octet spells the same number as the
/// rest.
pub proof fn lemma_be_value_leading_zero_skip(m: Seq<u8>)
    requires
        m.len() >= 1,
        m[0] == 0,
    ensures
        be_value(m) == be_value(m.skip(1)),
    decreases m.len(),
{
    if m.len() > 1 {
        let d = m.drop_last();
        assert(d[0] == 0);
        lemma_be_value_leading_zero_skip(d);
        assert(d.skip(1) =~= m.skip(1).drop_last());
        assert(m.skip(1).last() == m.last());
        assert(m.skip(1).len() >= 1);
    } else {
        assert(m.skip(1) =~= Seq::<u8>::empty());
        assert(m.drop_last() =~= Seq::<u8>::empty());
    }
}

/// The contents the encoder writes for a non-negative number are a valid
/// INTEGER, non-negative, and their magnitude (the octets after a padding
/// zero, if any) spells the same number.
pub proof fn lemma_integer_unsigned_contents(m: Seq<u8>)
    ensures
        ({
            let c = integer_unsigned_contents(m);
            &&& integer_contents_ok(c)
            &&& c[0] < 128
            &&& c.len() <= m.len() + 1
            &&& integer_value(c) == be_value(m) as int
            &&& (if c.len() >= 2 && c[0] == 0 {
                be_value(c.skip(1)) == be_value(m)
            } else {
                be_value(c) == be_value(m)
            })
        }),
{
    lemma_strip_leading_zeros_value(m);
    let s = strip_leading_zeros(m);
    let c = integer_unsigned_contents(m);
    if s.len() == 0 {
        assert(c =~= seq![0u8]);
        assert(be_value(s) == 0) by {
            assert(s =~= Seq::<u8>::empty());
        }
        lemma_be_value_single(0);
        assert(be_value(c) == 0);
        assert(be_value(c) == be_value(m));
    } else if s[0] >= 128 {
        assert(c =~= seq![0u8] + s);
        assert(c.len() >= 2);
        assert(c[1] == s[0]);
        assert(c.skip(1) =~= s);
        lemma_be_value_leading_zero_skip(c);
        assert(be_value(c.skip(1)) == be_value(m));
        assert(be_value(c) == be_value(m));
    } else {
        assert(c =~= s);
        assert(be_value(c) == be_value(m));
    }
    assert(c[0] < 128);
    // The value is non-negative, so the two's complement number is the
    // octets' number.
    assert(integer_value(c) == be_value(c) as int);
}

/// Reading what [`encode_integer_unsigned`] wrote: a non-negative INTEGER
/// whose magnitude octets (a single `0x00` for zero, otherwise with no
/// leading zero) spell the number that was encoded.
pub proof fn lemma_read_integer_encode_integer_unsigned(m: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        integer_unsigned_contents(m).len() < pow256(8),
        pos + encode_integer_unsigned(m).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_integer_unsigned(m).len()) as int) =~= encode_integer_unsigned(m),
    ensures
        match read_integer(b, pos, end) {
            Some((negative, ms, me, next)) => {
                &&& !negative
                &&& ms <= me
                &&& me == next
                &&& next == pos + encode_integer_unsigned(m).len()
                &&& be_value(b.subrange(ms as int, me as int)) == be_value(m)
                &&& (me - ms >= 2 ==> b[ms as int] != 0)
            },
            None => false,
        },
{
    super::lemmas::lemma_pow256_8();
    lemma_integer_unsigned_contents(m);
    let c = integer_unsigned_contents(m);
    let tag = universal_primitive(INTEGER);
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(tag, c, b, pos, end);
    lemma_strip_leading_zeros_value(m);
    let s = strip_leading_zeros(m);
    let il = encode_identifier(tag).len();
    let ll = encode_length(c.len()).len();
    let cstart = pos + il + ll;
    let cend = cstart + c.len();
    let bc = b.subrange(cstart as int, cend as int);
    assert(bc =~= c);
    if c.len() >= 2 && c[0] == 0 {
        assert(b.subrange(cstart as int + 1, cend as int) =~= c.skip(1));
        assert(c.skip(1) =~= s);
        assert(b[cstart as int + 1] == c[1]);
        assert(c[1] == s[0]);
    } else {
        assert(b.subrange(cstart as int, cend as int) =~= c);
        if c.len() >= 2 {
            assert(b[cstart as int] == c[0]);
        }
    }
}

/// Writing what [`read_integer`] read, for the non-negative INTEGERs: the
/// bytes are the encoding of the magnitude that was read, and the value (the
/// two's complement number of the contents) is the number the magnitude
/// spells. For a negative INTEGER the lemma states only that the value is
/// negative.
pub proof fn lemma_encode_integer_read_integer(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_integer(b, pos, end) {
            Some((negative, ms, me, next)) => {
                &&& next <= end
                &&& ms <= me
                &&& me == next
                &&& pos < ms
                &&& (negative ==> {
                    let t = read_tlv(b, pos, end).unwrap();
                    integer_value(b.subrange(t.cstart as int, t.cend as int)) < 0
                })
                &&& (!negative ==> {
                    let t = read_tlv(b, pos, end).unwrap();
                    &&& integer_value(b.subrange(t.cstart as int, t.cend as int)) == be_value(b.subrange(ms as int, me as int)) as int
                    &&& b.subrange(pos as int, next as int) =~= encode_integer_unsigned(b.subrange(ms as int, me as int))
                })
            },
            None => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
    super::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some((negative, ms, me, next)) = read_integer(b, pos, end) {
        let t = read_tlv(b, pos, end).unwrap();
        let c = b.subrange(t.cstart as int, t.cend as int);
        assert(c[0] == b[t.cstart as int]);
        if negative {
            super::lemmas::lemma_be_value_bound(c);
        } else {
            assert(integer_value(c) == be_value(c) as int);
            let mag = b.subrange(ms as int, me as int);
            if c.len() >= 2 && c[0] == 0 {
                assert(c[1] >= 128);
                assert(mag =~= c.skip(1));
                assert(mag[0] == c[1]);
                lemma_be_value_leading_zero_skip(c);
                assert(strip_leading_zeros(mag) =~= mag);
                assert(integer_unsigned_contents(mag) =~= seq![0u8] + mag);
                assert(seq![0u8] + mag =~= c);
            } else {
                assert(mag =~= c);
                if c[0] == 0 {
                    // The single octet 0x00: the number zero.
                    assert(c.len() == 1);
                    assert(c =~= seq![0u8]);
                    assert(mag.drop_first() =~= Seq::<u8>::empty());
                    assert(strip_leading_zeros(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
                    assert(strip_leading_zeros(mag) =~= Seq::<u8>::empty());
                    assert(integer_unsigned_contents(mag) =~= seq![0u8]);
                } else {
                    assert(strip_leading_zeros(mag) =~= mag);
                    assert(integer_unsigned_contents(mag) =~= mag);
                }
            }
            assert(integer_unsigned_contents(mag) =~= c);
        }
    }
}

// ---------------------------------------------------------------------------
// BIT STRING.
// ---------------------------------------------------------------------------

/// Whether `unused` and `bits` make the contents of a DER BIT STRING.
pub open spec fn bit_string_ok(unused: u8, bits: Seq<u8>) -> bool {
    bit_string_contents_ok(seq![unused] + bits)
}

/// Reading what [`encode_bit_string`] wrote.
pub proof fn lemma_read_bit_string_encode_bit_string(unused: u8, bits: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        bit_string_ok(unused, bits),
        bits.len() + 1 < pow256(8),
        pos + encode_bit_string(unused, bits).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_bit_string(unused, bits).len()) as int) =~= encode_bit_string(unused, bits),
    ensures
        match read_bit_string(b, pos, end) {
            Some((u, ms, me, next)) => {
                &&& u == unused
                &&& next == pos + encode_bit_string(unused, bits).len()
                &&& b.subrange(ms as int, me as int) =~= bits
            },
            None => false,
        },
{
    let c = seq![unused] + bits;
    let tag = universal_primitive(BIT_STRING);
    assert(tlv_ok(tag, c));
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(tag, c, b, pos, end);
    let il = encode_identifier(tag).len();
    let ll = encode_length(c.len()).len();
    let cstart = pos + il + ll;
    let bc = b.subrange(cstart as int, (cstart + c.len()) as int);
    assert(bc =~= c);
    assert(b.subrange(cstart as int + 1, (cstart + c.len()) as int) =~= bits) by {
        assert forall|i: int| 0 <= i < bits.len() implies #[trigger] b.subrange(cstart as int + 1, (cstart + c.len()) as int)[i]
            == bits[i] by {
            assert(bc[1 + i] == c[1 + i]);
            assert(c[1 + i] == bits[i]);
        }
    }
    assert(c[0] == unused);
    if c.len() >= 2 {
        assert(bc.last() == c.last());
    }
}

/// Writing what [`read_bit_string`] read: the bits' octets and unused count
/// make a valid BIT STRING, and the bytes are its encoding.
pub proof fn lemma_encode_bit_string_read_bit_string(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_bit_string(b, pos, end) {
            Some((u, ms, me, next)) => {
                &&& bit_string_ok(u, b.subrange(ms as int, me as int))
                &&& next <= end
                &&& b.subrange(pos as int, next as int) =~= encode_bit_string(u, b.subrange(ms as int, me as int))
            },
            None => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
    if let Some((u, ms, me, next)) = read_bit_string(b, pos, end) {
        let t = read_tlv(b, pos, end).unwrap();
        let c = b.subrange(t.cstart as int, t.cend as int);
        assert(c[0] == u);
        assert(b.subrange(ms as int, me as int) =~= c.skip(1));
        assert(c =~= seq![u] + b.subrange(ms as int, me as int));
    }
}

// ---------------------------------------------------------------------------
// OCTET STRING and the character string types.
// ---------------------------------------------------------------------------

/// Reading what [`encode_octets`] wrote (an OCTET STRING, UTF8String,
/// PrintableString, IA5String, UTCTime or GeneralizedTime).
pub proof fn lemma_read_octets_encode_octets(number: u32, s: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        number <= MAX_TAG_NUMBER,
        s.len() < pow256(8),
        pos + encode_octets(number, s).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_octets(number, s).len()) as int) =~= encode_octets(number, s),
    ensures
        match read_octets(b, pos, end, number) {
            Some((cs, ce)) => ce == pos + encode_octets(number, s).len() && b.subrange(cs as int, ce as int) =~= s,
            None => false,
        },
{
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(universal_primitive(number), s, b, pos, end);
}

/// Writing what [`read_octets`] read.
pub proof fn lemma_encode_octets_read_octets(b: Seq<u8>, pos: nat, end: nat, number: u32)
    requires
        end <= b.len(),
    ensures
        match read_octets(b, pos, end, number) {
            Some((cs, ce)) => {
                &&& ce <= end
                &&& b.subrange(pos as int, ce as int) =~= encode_octets(number, b.subrange(cs as int, ce as int))
            },
            None => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
}

/// A constructed string is rejected (§10.2): where a value's tag has bit 6
/// set, no string reader returns it.
pub proof fn lemma_read_octets_rejects_constructed(b: Seq<u8>, pos: nat, end: nat, number: u32)
    requires
        read_tlv(b, pos, end) is Some,
        read_tlv(b, pos, end).unwrap().tag.constructed,
    ensures
        read_octets(b, pos, end, number) is None,
{
}

// ---------------------------------------------------------------------------
// NULL.
// ---------------------------------------------------------------------------

/// Reading what [`encode_null`] wrote.
pub proof fn lemma_read_null_encode_null(b: Seq<u8>, pos: nat, end: nat)
    requires
        pos + 2 <= end,
        end <= b.len(),
        b.subrange(pos as int, pos as int + 2) =~= encode_null(),
    ensures
        read_null(b, pos, end) == Some((pos + 2) as nat),
{
    super::lemmas::lemma_pow256_8();
    assert(encode_null() =~= seq![5u8, 0u8]) by {
        assert(encode_identifier(universal_primitive(NULL)) =~= seq![5u8]);
        assert(encode_length(0) =~= seq![0u8]);
    }
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(universal_primitive(NULL), seq![], b, pos, end);
}

/// Writing what [`read_null`] read: `05 00`, and nothing else.
pub proof fn lemma_encode_null_read_null(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_null(b, pos, end) {
            Some(next) => next == pos + 2 && next <= end && b.subrange(pos as int, next as int) =~= encode_null(),
            None => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
    super::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some(next) = read_null(b, pos, end) {
        let t = read_tlv(b, pos, end).unwrap();
        assert(b.subrange(t.cstart as int, t.cend as int) =~= Seq::<u8>::empty());
        assert(encode_null() =~= seq![5u8, 0u8]) by {
            assert(encode_identifier(universal_primitive(NULL)) =~= seq![5u8]);
            assert(encode_length(0) =~= seq![0u8]);
        }
    }
}

// ---------------------------------------------------------------------------
// OBJECT IDENTIFIER.
// ---------------------------------------------------------------------------

/// Reading what [`encode_oid`] wrote: every valid list of components
/// survives.
pub proof fn lemma_read_oid_encode_oid(arcs: Seq<nat>, b: Seq<u8>, pos: nat, end: nat)
    requires
        oid_valid(arcs),
        oid_contents(arcs).len() < pow256(8),
        pos + encode_oid(arcs).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_oid(arcs).len()) as int) =~= encode_oid(arcs),
    ensures
        read_oid(b, pos, end) == Some((arcs, (pos + encode_oid(arcs).len()) as nat)),
{
    let tag = universal_primitive(OBJECT_IDENTIFIER);
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(tag, oid_contents(arcs), b, pos, end);
    super::lemmas_oid::lemma_oid_components_oid_contents(arcs);
}

/// Writing what [`read_oid`] read: the components are valid, and the bytes
/// are their encoding. There are no more components than contents octets
/// plus one.
pub proof fn lemma_encode_oid_read_oid(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match read_oid(b, pos, end) {
            Some((arcs, next)) => {
                &&& oid_valid(arcs)
                &&& next <= end
                &&& b.subrange(pos as int, next as int) =~= encode_oid(arcs)
                &&& arcs.len() <= next - pos
            },
            None => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
    super::lemmas::lemma_read_tlv_bounds(b, pos, end);
    if let Some((arcs, next)) = read_oid(b, pos, end) {
        let t = read_tlv(b, pos, end).unwrap();
        let c = b.subrange(t.cstart as int, t.cend as int);
        super::lemmas_oid::lemma_oid_contents_oid_components(c);
        assert(c.len() + 1 <= next - pos);
    }
}

// ---------------------------------------------------------------------------
// SEQUENCE, SET, and context-specific tags.
// ---------------------------------------------------------------------------

/// Reading what [`encode_sequence`] wrote: the contents range holds exactly
/// the contents.
pub proof fn lemma_expect_sequence_encode_sequence(contents: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        contents.len() < pow256(8),
        pos + encode_sequence(contents).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_sequence(contents).len()) as int) =~= encode_sequence(contents),
    ensures
        match expect_sequence(b, pos, end) {
            Some((cs, ce)) => ce == pos + encode_sequence(contents).len() && b.subrange(cs as int, ce as int) =~= contents,
            None => false,
        },
{
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(universal_constructed(SEQUENCE), contents, b, pos, end);
}

/// Writing what [`expect_sequence`] read.
pub proof fn lemma_encode_sequence_expect_sequence(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match expect_sequence(b, pos, end) {
            Some((cs, ce)) => ce <= end && b.subrange(pos as int, ce as int) =~= encode_sequence(b.subrange(cs as int, ce as int)),
            None => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
}

/// Reading what [`encode_set`] wrote.
pub proof fn lemma_expect_set_encode_set(contents: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        contents.len() < pow256(8),
        pos + encode_set(contents).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_set(contents).len()) as int) =~= encode_set(contents),
    ensures
        match expect_set(b, pos, end) {
            Some((cs, ce)) => ce == pos + encode_set(contents).len() && b.subrange(cs as int, ce as int) =~= contents,
            None => false,
        },
{
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(universal_constructed(SET), contents, b, pos, end);
}

/// Writing what [`expect_set`] read.
pub proof fn lemma_encode_set_expect_set(b: Seq<u8>, pos: nat, end: nat)
    requires
        end <= b.len(),
    ensures
        match expect_set(b, pos, end) {
            Some((cs, ce)) => ce <= end && b.subrange(pos as int, ce as int) =~= encode_set(b.subrange(cs as int, ce as int)),
            None => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
}

/// Reading what [`encode_context`] wrote: the component is present, with
/// the form and contents that were written (§8.14.3 and §8.14.4).
pub proof fn lemma_read_optional_context_encode_context(number: u32, constructed: bool, contents: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        number <= MAX_TAG_NUMBER,
        contents.len() < pow256(8),
        pos + encode_context(number, constructed, contents).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_context(number, constructed, contents).len()) as int) =~= encode_context(
            number,
            constructed,
            contents,
        ),
    ensures
        match read_optional_context(b, pos, end, number) {
            Some(Some((c, cs, ce))) => {
                &&& c == constructed
                &&& ce == pos + encode_context(number, constructed, contents).len()
                &&& b.subrange(cs as int, ce as int) =~= contents
            },
            _ => false,
        },
{
    let tag = context_specific(number, constructed);
    super::lemmas_tlv::lemma_read_tlv_encode_tlv(tag, contents, b, pos, end);
    super::lemmas_tlv::lemma_read_identifier_encode_identifier(tag, b, pos, end);
}

/// Reading what [`encode_context`] wrote as an EXPLICIT tag (§8.14.3, always
/// constructed): the inner range holds the one complete encoding.
pub proof fn lemma_read_optional_explicit_encode_context(number: u32, contents: Seq<u8>, b: Seq<u8>, pos: nat, end: nat)
    requires
        number <= MAX_TAG_NUMBER,
        contents.len() < pow256(8),
        pos + encode_context(number, true, contents).len() <= end,
        end <= b.len(),
        b.subrange(pos as int, (pos + encode_context(number, true, contents).len()) as int) =~= encode_context(number, true, contents),
    ensures
        match read_optional_explicit(b, pos, end, number) {
            Some(Some((cs, ce))) => {
                &&& ce == pos + encode_context(number, true, contents).len()
                &&& b.subrange(cs as int, ce as int) =~= contents
            },
            _ => false,
        },
{
    lemma_read_optional_context_encode_context(number, true, contents, b, pos, end);
}

/// Writing what [`read_optional_context`] read, when it found the
/// component.
pub proof fn lemma_encode_context_read_optional_context(b: Seq<u8>, pos: nat, end: nat, number: u32)
    requires
        end <= b.len(),
    ensures
        match read_optional_context(b, pos, end, number) {
            Some(Some((c, cs, ce))) => {
                &&& number <= MAX_TAG_NUMBER
                &&& ce <= end
                &&& b.subrange(pos as int, ce as int) =~= encode_context(number, c, b.subrange(cs as int, ce as int))
            },
            _ => true,
        },
{
    super::lemmas_tlv::lemma_encode_tlv_read_tlv(b, pos, end);
    super::lemmas::lemma_read_tlv_bounds(b, pos, end);
    super::lemmas::lemma_read_identifier_bounds(b, pos, end);
}

/// A component is absent when nothing is left, and when the next value has
/// another tag.
pub proof fn lemma_read_optional_context_absent(b: Seq<u8>, pos: nat, end: nat, number: u32)
    ensures
        pos >= end ==> read_optional_context(b, pos, end, number) == Some(None::<(bool, nat, nat)>),
        (match read_identifier(b, pos, end) {
            Some((tag, _)) => !(tag.class == Class::ContextSpecific && tag.number == number),
            None => false,
        }) ==> read_optional_context(b, pos, end, number) == Some(None::<(bool, nat, nat)>),
{
}


/// Writing what [`read_optional_explicit`] read, when it found the
/// component: the bytes are the encoding of a constructed `[number]` around
/// the inner range (§8.14.3).
pub proof fn lemma_encode_context_read_optional_explicit(b: Seq<u8>, pos: nat, end: nat, number: u32)
    requires
        end <= b.len(),
    ensures
        match read_optional_explicit(b, pos, end, number) {
            Some(Some((cs, ce))) => {
                &&& number <= MAX_TAG_NUMBER
                &&& ce <= end
                &&& b.subrange(pos as int, ce as int) =~= encode_context(number, true, b.subrange(cs as int, ce as int))
            },
            _ => true,
        },
{
    lemma_encode_context_read_optional_context(b, pos, end, number);
}

} // verus!

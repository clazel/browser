//! The executable encoder, proven to meet [`super::contract`].
//!
//! It writes the DER encoding of a value (clauses 8, 10 and 11): the
//! identifier octets, the length in the fewest octets, and the contents.
//! Every function follows the spec function of the same name in
//! [`super::spec`]. None reserves memory ahead of the bytes it writes.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Append the `width` octets spelling `value` base 256, most significant
/// first ([`be_bytes`]'s recursion).
pub(crate) fn push_be(out: &mut Vec<u8>, value: u64, width: usize)
    requires
        width <= 8,
        (value as nat) < pow256(width as nat),
    ensures
        final(out)@ =~= old(out)@ + be_bytes(value as nat, width as nat),
    decreases width,
{
    if width == 0 {
        assert(be_bytes(value as nat, 0) =~= Seq::<u8>::empty());
        return;
    }
    // Never saturates: width >= 1.
    let before = width.saturating_sub(1);
    assert(pow256(width as nat) == 256 * pow256(before as nat));
    push_be(out, value / 256, before);
    out.push((value % 256) as u8);
    assert(out@ =~= old(out)@ + be_bytes(value as nat, width as nat));
}

/// Table 1: the value of bits 8 and 7 for a class.
fn class_bits_exec(class: Class) -> (b: u8)
    ensures
        b == class_bits(class),
{
    match class {
        Class::Universal => 0,
        Class::Application => 1,
        Class::ContextSpecific => 2,
        Class::Private => 3,
    }
}

/// §8.1.2: append the identifier octets of `tag`.
pub(crate) fn push_identifier(out: &mut Vec<u8>, tag: Tag)
    requires
        tag.number <= MAX_TAG_NUMBER,
    ensures
        final(out)@ =~= old(out)@ + encode_identifier(tag),
{
    // class_bits <= 3 and the constructed bit is 32, so this is at most
    // 3 * 64 + 32 = 224 and never saturates.
    let first = class_bits_exec(tag.class).saturating_mul(64).saturating_add(if tag.constructed {
        32
    } else {
        0
    });
    if tag.number < 31 {
        // 8.1.2.2. number < 31, so first + number <= 254.
        out.push(first.saturating_add(tag.number as u8));
    } else if tag.number < 128 {
        // 8.1.2.4, one subsequent octet. first + 31 <= 255.
        out.push(first.saturating_add(31));
        out.push(tag.number as u8);
    } else {
        // 8.1.2.4, two subsequent octets: number <= 16383, so
        // number / 128 <= 127 and 128 + number / 128 <= 255.
        out.push(first.saturating_add(31));
        out.push(128u32.saturating_add(tag.number / 128) as u8);
        out.push((tag.number % 128) as u8);
    }
    assert(out@ =~= old(out)@ + encode_identifier(tag));
}

/// §8.1.3, §10.1: append the length octets of `len`: the short form for 127
/// or less, otherwise the long form in the fewest octets.
pub(crate) fn push_length(out: &mut Vec<u8>, len: usize)
    ensures
        final(out)@ =~= old(out)@ + super::spec::encode_length(len as nat),
{
    proof {
        super::lemmas::lemma_pow256_8();
    }
    if len < 128 {
        // 8.1.3.4.
        out.push(len as u8);
        return;
    }
    // 8.1.3.5. `len` is at most 2^64 - 1 (usize is at most 64 bits).
    let l = len as u64;
    let w: usize = if l < 0x100 {
        1
    } else if l < 0x1_0000 {
        2
    } else if l < 0x100_0000 {
        3
    } else if l < 0x1_0000_0000 {
        4
    } else if l < 0x100_0000_0000 {
        5
    } else if l < 0x1_0000_0000_0000 {
        6
    } else if l < 0x100_0000_0000_0000 {
        7
    } else {
        8
    };
    assert(w as nat == length_octets(len as nat));
    // w <= 8, so 128 + w <= 136.
    out.push(128u8.saturating_add(w as u8));
    push_be(out, l, w);
    assert(out@ =~= old(out)@ + super::spec::encode_length(len as nat));
}

/// §8.1.3, §10.1: the length octets of `len`, in the shortest form.
pub fn encode_length(len: usize) -> (out: Vec<u8>)
    ensures
        super::contract::encode_length_ensures(len as nat, out@),
{
    let mut out: Vec<u8> = Vec::new();
    push_length(&mut out, len);
    assert(out@ =~= Seq::<u8>::empty() + super::spec::encode_length(len as nat));
    out
}

/// §8.1.1.1: the encoding of a value with the given tag and contents:
/// identifier octets, length octets, contents octets. The output is the
/// contents and at most 12 octets more.
pub fn encode_tlv(tag: Tag, contents: &[u8]) -> (out: Vec<u8>)
    requires
        super::contract::encode_tlv_requires(tag),
    ensures
        super::contract::encode_tlv_ensures(tag, contents@, out@),
        super::contract::encode_alloc_ensures(contents@.len(), out@.len()),
{
    // A slice is shorter than 2^64 octets: usize is at most 64 bits.
    let _len64 = contents.len() as u64;
    proof {
        super::lemmas::lemma_pow256_8();
        assert(_len64 as nat == contents@.len());
        assert(tlv_ok(tag, contents@));
    }
    let mut out: Vec<u8> = Vec::new();
    push_identifier(&mut out, tag);
    push_length(&mut out, contents.len());
    out.extend_from_slice(contents);
    proof {
        super::lemmas::lemma_encode_tlv_len(tag, contents@);
        assert(out@ =~= super::spec::encode_tlv(tag, contents@));
    }
    out
}

/// §8.2.2, §11.1: a BOOLEAN.
pub fn encode_boolean(v: bool) -> (out: Vec<u8>)
    ensures
        out@ =~= super::spec::encode_boolean(v),
{
    let contents: [u8; 1] = [if v {
        0xFF
    } else {
        0x00
    }];
    proof {
        assert(contents@ =~= seq![if v { 0xFFu8 } else { 0x00u8 }]);
    }
    encode_tlv(Tag { class: Class::Universal, constructed: false, number: BOOLEAN }, &contents)
}

/// §8.7.2: a primitive OCTET STRING.
pub fn encode_octet_string(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ =~= super::spec::encode_octet_string(s@),
        super::contract::encode_alloc_ensures(s@.len(), out@.len()),
{
    encode_tlv(Tag { class: Class::Universal, constructed: false, number: OCTET_STRING }, s)
}

/// A primitive value of the universal type `number` (UTF8String,
/// PrintableString, IA5String, UTCTime, GeneralizedTime).
pub fn encode_octets(number: u32, s: &[u8]) -> (out: Vec<u8>)
    requires
        number <= MAX_TAG_NUMBER,
    ensures
        out@ =~= super::spec::encode_octets(number, s@),
        super::contract::encode_alloc_ensures(s@.len(), out@.len()),
{
    encode_tlv(Tag { class: Class::Universal, constructed: false, number }, s)
}

/// §8.8: NULL, `05 00`.
pub fn encode_null() -> (out: Vec<u8>)
    ensures
        out@ =~= super::spec::encode_null(),
{
    let empty: [u8; 0] = [];
    proof {
        assert(empty@ =~= Seq::<u8>::empty());
    }
    encode_tlv(Tag { class: Class::Universal, constructed: false, number: NULL }, &empty)
}

/// §8.6.2: a primitive BIT STRING: `unused` is the number of unused bits (0
/// to 7) of the last octet of `bits`, which are zero, and zero when `bits`
/// is empty.
pub fn encode_bit_string(unused: u8, bits: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ =~= super::spec::encode_bit_string(unused, bits@),
        super::contract::encode_alloc_ensures(bits@.len() + 1, out@.len()),
{
    let mut contents: Vec<u8> = Vec::new();
    contents.push(unused);
    contents.extend_from_slice(bits);
    proof {
        assert(contents@ =~= seq![unused] + bits@);
    }
    encode_tlv(Tag { class: Class::Universal, constructed: false, number: BIT_STRING }, contents.as_slice())
}

/// §8.9.1: a SEQUENCE whose contents are the concatenated encodings of its
/// components.
pub fn encode_sequence(contents: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ =~= super::spec::encode_sequence(contents@),
        super::contract::encode_alloc_ensures(contents@.len(), out@.len()),
{
    encode_tlv(Tag { class: Class::Universal, constructed: true, number: SEQUENCE }, contents)
}

/// §8.11.1: a SET whose contents are the concatenated encodings of its
/// components, in the order given.
pub fn encode_set(contents: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ =~= super::spec::encode_set(contents@),
        super::contract::encode_alloc_ensures(contents@.len(), out@.len()),
{
    encode_tlv(Tag { class: Class::Universal, constructed: true, number: SET }, contents)
}

/// §8.14: a value with the context-specific tag `[number]` and the given
/// contents: for EXPLICIT tagging, `constructed` and the contents one
/// complete encoding; for IMPLICIT tagging, the base encoding's form and
/// contents.
pub fn encode_context(number: u32, constructed: bool, contents: &[u8]) -> (out: Vec<u8>)
    requires
        number <= MAX_TAG_NUMBER,
    ensures
        out@ =~= super::spec::encode_context(number, constructed, contents@),
        super::contract::encode_alloc_ensures(contents@.len(), out@.len()),
{
    encode_tlv(Tag { class: Class::ContextSpecific, constructed, number }, contents)
}

/// The contents octets of the INTEGER whose value is the number the octets
/// `m` spell (non-negative): leading zero octets removed, one zero octet for
/// zero, and a zero octet in front of a first octet with bit 8 set.
pub(crate) fn integer_unsigned_contents_exec(m: &[u8]) -> (c: Vec<u8>)
    ensures
        c@ =~= integer_unsigned_contents(m@),
        c@.len() <= m@.len() + 1,
{
    let mut k: usize = 0;
    proof {
        assert(m@.skip(0) =~= m@);
    }
    while k < m.len() && super::decode::octet_at(m, k) == 0
        invariant
            k <= m.len(),
            strip_leading_zeros(m@) =~= strip_leading_zeros(m@.skip(k as int)),
        decreases m.len() - k,
    {
        proof {
            assert(m@.skip(k as int).drop_first() =~= m@.skip(k as int + 1));
        }
        // Never saturates: k < m.len().
        k = k.saturating_add(1);
    }
    proof {
        if k == m.len() {
            assert(m@.skip(k as int) =~= Seq::<u8>::empty());
        }
    }
    let mut c: Vec<u8> = Vec::new();
    if k == m.len() {
        c.push(0);
        return c;
    }
    let first = match m.get(k) {
        Some(&b) => b,
        None => 0,
    };
    if first >= 128 {
        c.push(0);
    }
    let ghost before = c@;
    c.extend_from_slice(vstd::slice::slice_subrange(m, k, m.len()));
    proof {
        assert(m@.skip(k as int) =~= m@.subrange(k as int, m@.len() as int));
        assert(strip_leading_zeros(m@.skip(k as int)) =~= m@.skip(k as int));
    }
    c
}

/// §8.3: the INTEGER whose value is the number the octets `magnitude` spell
/// (non-negative, most significant octet first, leading zeros allowed). The
/// output is at most 13 octets more than `magnitude`.
pub fn encode_integer_unsigned(magnitude: &[u8]) -> (out: Vec<u8>)
    ensures
        super::contract::encode_integer_unsigned_ensures(magnitude@, out@),
        out@.len() <= magnitude@.len() + 13,
{
    let contents = integer_unsigned_contents_exec(magnitude);
    encode_tlv(Tag { class: Class::Universal, constructed: false, number: INTEGER }, contents.as_slice())
}

/// §8.19.2: append the digits of `w` base 128, most significant first, each
/// with bit 8 set ([`subidentifier_prefix`]'s recursion; at most ten digits
/// for a `u64`).
fn push_prefix(out: &mut Vec<u8>, w: u64)
    ensures
        final(out)@ =~= old(out)@ + subidentifier_prefix(w as nat),
    decreases w,
{
    if w == 0 {
        assert(subidentifier_prefix(0) =~= Seq::<u8>::empty());
        return;
    }
    push_prefix(out, w / 128);
    // w % 128 <= 127, so 128 + w % 128 <= 255.
    out.push(128u8.saturating_add((w % 128) as u8));
    assert(out@ =~= old(out)@ + subidentifier_prefix(w as nat));
}

/// §8.19.2: append the subidentifier `v` in the fewest possible octets.
fn push_subidentifier(out: &mut Vec<u8>, v: u64)
    ensures
        final(out)@ =~= old(out)@ + encode_subidentifier(v as nat),
{
    push_prefix(out, v / 128);
    out.push((v % 128) as u8);
}

/// §8.19: an OBJECT IDENTIFIER with the given components. The first is 0, 1
/// or 2; the second is below 40 unless the first is 2; `40 * first + second`
/// and every other component fit a `u64`.
pub fn encode_oid(arcs: &[u64]) -> (out: Vec<u8>)
    requires
        super::contract::encode_oid_requires(super::decode::nats(arcs@)),
    ensures
        super::contract::encode_oid_ensures(super::decode::nats(arcs@), out@),
{
    let a0 = match arcs.first() {
        Some(&a) => a,
        None => return Vec::new(),
    };
    let a1 = match arcs.get(1) {
        Some(&a) => a,
        None => return Vec::new(),
    };
    // oid_valid: 40 * a0 + a1 < 2^64, so neither operation saturates.
    let first = a0.saturating_mul(40).saturating_add(a1);
    let mut contents: Vec<u8> = Vec::new();
    push_subidentifier(&mut contents, first);
    let ghost n = super::decode::nats(arcs@);
    proof {
        assert(n.subrange(2, 2) =~= Seq::<nat>::empty());
        assert(seq![first as nat] + n.subrange(2, 2) =~= seq![first as nat]);
        super::lemmas::lemma_encode_subidentifiers_single(first as nat);
    }
    let mut k: usize = 2;
    while k < arcs.len()
        invariant
            2 <= k <= arcs.len(),
            n == super::decode::nats(arcs@),
            first as nat == 40 * n[0] + n[1],
            contents@ =~= encode_subidentifiers(seq![first as nat] + n.subrange(2, k as int)),
        decreases arcs.len() - k,
    {
        let a = match arcs.get(k) {
            Some(&a) => a,
            None => return Vec::new(),
        };
        let ghost before = contents@;
        push_subidentifier(&mut contents, a);
        proof {
            let prefix = seq![first as nat] + n.subrange(2, k as int);
            super::lemmas::lemma_encode_subidentifiers_append(prefix, seq![a as nat]);
            super::lemmas::lemma_encode_subidentifiers_single(a as nat);
            assert(prefix + seq![a as nat] =~= seq![first as nat] + n.subrange(2, k as int + 1));
        }
        // Never saturates: k < arcs.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(n.subrange(2, arcs@.len() as int) =~= n.skip(2));
        assert(contents@ =~= oid_contents(n));
    }
    encode_tlv(Tag { class: Class::Universal, constructed: false, number: OBJECT_IDENTIFIER }, contents.as_slice())
}

/// The `DigestInfo` of RFC 8017 §9.2: `SEQUENCE { SEQUENCE { algorithm OID,
/// parameters NULL }, digest OCTET STRING }`.
pub fn encode_digest_info(arcs: &[u64], digest: &[u8]) -> (out: Vec<u8>)
    requires
        super::contract::encode_oid_requires(super::decode::nats(arcs@)),
    ensures
        out@ =~= super::spec::encode_digest_info(super::decode::nats(arcs@), digest@),
{
    let oid = encode_oid(arcs);
    let null = encode_null();
    let mut algorithm = oid;
    algorithm.extend_from_slice(null.as_slice());
    let algorithm = encode_sequence(algorithm.as_slice());
    let octets = encode_octet_string(digest);
    let mut body = algorithm;
    body.extend_from_slice(octets.as_slice());
    encode_sequence(body.as_slice())
}

} // verus!

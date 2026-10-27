//! The executable decoder, proven to meet [`super::contract`].
//!
//! Each function follows the spec function of the same name in
//! [`super::spec`] step by step (the clause comments and quotes live there).
//! Every reader is a cursor: it takes the input, a position and an end with
//! `end <= input.len()`, and returns where the value it read stops. None of
//! them reserves memory for a declared length: they return ranges, and the
//! one that builds a vector ([`read_oid`]) pushes only components it has
//! read.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A data value's extent: the exec twin of [`super::spec::Tlv`], whose
/// view it is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tlv {
    /// The tag from the identifier octets.
    pub tag: Tag,
    /// Index of the first contents octet.
    pub cstart: usize,
    /// Index after the last contents octet, which is where the value ends.
    pub cend: usize,
}

impl View for Tlv {
    type V = super::spec::Tlv;

    open spec fn view(&self) -> super::spec::Tlv {
        super::spec::Tlv { tag: self.tag, cstart: self.cstart as nat, cend: self.cend as nat }
    }
}

/// The spec view of an optional extent.
pub open spec fn view_tlv(r: Option<Tlv>) -> Option<super::spec::Tlv> {
    match r {
        Some(t) => Some(t@),
        None => None,
    }
}

/// The spec view of a tag and a length in octets.
pub open spec fn view_tag_len(r: Option<(Tag, usize)>) -> Option<(Tag, nat)> {
    match r {
        Some((t, n)) => Some((t, n as nat)),
        None => None,
    }
}

/// The spec view of a length and the number of length octets.
pub open spec fn view_length(r: Option<(u64, usize)>) -> Option<(nat, nat)> {
    match r {
        Some((v, n)) => Some((v as nat, n as nat)),
        None => None,
    }
}

/// The spec view of a pair of positions.
pub open spec fn view_range(r: Option<(usize, usize)>) -> Option<(nat, nat)> {
    match r {
        Some((a, b)) => Some((a as nat, b as nat)),
        None => None,
    }
}

/// §8.1.3.5: the `width` octets at `pos` as an unsigned integer base 256.
/// The recursion is [`be_value`]'s: the last octet is the least
/// significant.
pub(crate) fn read_be(input: &[u8], pos: usize, width: usize) -> (value: u64)
    requires
        width <= 8,
        pos + width <= input.len(),
    ensures
        value as nat == be_value(input@.subrange(pos as int, pos as int + width as int)),
    decreases width,
{
    if width == 0 {
        assert(input@.subrange(pos as int, pos as int) =~= Seq::<u8>::empty());
        return 0;
    }
    let ghost whole = input@.subrange(pos as int, pos as int + width as int);
    let ghost init = input@.subrange(pos as int, pos as int + width as int - 1);
    assert(whole.drop_last() =~= init);
    // Never saturates: width >= 1.
    let before = width.saturating_sub(1);
    let high = read_be(input, pos, before);
    proof {
        super::lemmas::lemma_be_value_bound(init);
        super::lemmas::lemma_pow256_at_most_8(width as nat);
        assert(pow256(width as nat) == 256 * pow256(before as nat));
        assert(high as nat * 256 + 255 <= 0xFFFF_FFFF_FFFF_FFFF);
    }
    // Never saturates: pos + width <= input.len(), so the index is in range.
    let index = pos.saturating_add(before);
    let last = match input.get(index) {
        Some(&b) => b,
        None => 0,
    };
    assert(whole.last() == input@[index as int]);
    // Never saturates: high * 256 + last <= 2^64 - 1 (shown above).
    high.saturating_mul(256).saturating_add(last as u64)
}

/// §8.1.2.4.2 and §8.19.2: the series of octets at `start` (bit 8 set on
/// every octet but the last) and the number its low seven bits spell
/// ([`base128`]), if that number is at most `limit`. Returns the number and
/// the index of the last octet of the series. `None` when there is no last
/// octet in `[start, end)`, or when the number exceeds `limit`; the spec
/// functions that call it answer `None` in both cases.
pub(crate) fn read_series(input: &[u8], start: usize, end: usize, limit: u64) -> (r: Option<(u64, usize)>)
    requires
        end <= input.len(),
    ensures
        match r {
            Some((v, j)) => {
                &&& series_end(input@, start as nat, end as nat) == Some(j as nat)
                &&& v as nat == base128(input@.subrange(start as int, j as int + 1))
                &&& v <= limit
            },
            None => match series_end(input@, start as nat, end as nat) {
                Some(j) => base128(input@.subrange(start as int, j as int + 1)) > limit,
                None => true,
            },
        },
{
    if start >= end {
        return None;
    }
    let mut i = start;
    let mut acc: u128 = 0;
    proof {
        assert(input@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
    }
    while i < end
        invariant
            start <= i <= end,
            end <= input.len(),
            acc <= limit as u128,
            acc as nat == base128(input@.subrange(start as int, i as int)),
            forall|k: int| start <= k < i ==> #[trigger] input@[k] >= 128,
        decreases end - i,
    {
        let o = match input.get(i) {
            Some(&b) => b,
            None => return None,
        };
        let ghost before = input@.subrange(start as int, i as int);
        let ghost after = input@.subrange(start as int, i as int + 1);
        proof {
            assert(after =~= before.push(o));
            super::lemmas::lemma_base128_push(before, o);
        }
        // acc <= limit < 2^64, so acc * 128 + 127 < 2^71 and this never
        // saturates.
        let acc2 = acc.saturating_mul(128).saturating_add((o % 128) as u128);
        if acc2 > limit as u128 {
            proof {
                super::lemmas::lemma_series_end_skip(input@, start as nat, i as nat, end as nat);
                super::lemmas::lemma_series_end_in_range(input@, i as nat, end as nat);
                if let Some(j) = series_end(input@, i as nat, end as nat) {
                    super::lemmas::lemma_base128_monotone(input@, start as int, i as int + 1, j as int + 1);
                }
            }
            return None;
        }
        if o >= 128 {
            acc = acc2;
            // Never saturates: i < end.
            i = i.saturating_add(1);
        } else {
            proof {
                super::lemmas::lemma_series_end_skip(input@, start as nat, i as nat, end as nat);
            }
            return Some((acc2 as u64, i));
        }
    }
    proof {
        super::lemmas::lemma_series_end_skip(input@, start as nat, i as nat, end as nat);
    }
    None
}

/// Table 1: the class encoded by bits 8 and 7.
fn class_of(bits: u8) -> (c: Class)
    ensures
        c == class_from_bits(bits),
{
    if bits == 0 {
        Class::Universal
    } else if bits == 1 {
        Class::Application
    } else if bits == 2 {
        Class::ContextSpecific
    } else {
        Class::Private
    }
}

/// §8.1.2: the identifier octets at `pos`: the tag and their number.
pub fn read_identifier(input: &[u8], pos: usize, end: usize) -> (r: Option<(Tag, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_identifier_ensures(input@, pos as nat, end as nat, view_tag_len(r)),
{
    if pos >= end {
        return None;
    }
    let o = match input.get(pos) {
        Some(&b) => b,
        None => return None,
    };
    let class = class_of(o / 64);
    let constructed = (o / 32) % 2 == 1;
    if o % 32 != 31 {
        // 1.
        return Some((Tag { class, constructed, number: (o % 32) as u32 }, 1));
    }
    // 2. Never saturates: pos < end <= input.len().
    let first = pos.saturating_add(1);
    let (number, j) = read_series(input, first, end, MAX_TAG_NUMBER as u64)?;
    proof {
        super::lemmas::lemma_series_end_in_range(input@, first as nat, end as nat);
    }
    // 8.1.2.4.2 c): the first subsequent octet is at `first <= j < end`.
    match input.get(first) {
        Some(&f) => {
            if f % 128 == 0 {
                return None;
            }
        },
        None => return None,
    }
    if number < 31 {
        return None;
    }
    // number <= MAX_TAG_NUMBER, so this is exact. j < end <= input.len() and
    // j >= first > pos: the length is j + 1 - pos, never saturating.
    Some((Tag { class, constructed, number: number as u32 }, j.saturating_add(1).saturating_sub(pos)))
}

/// §8.1.3 and §10.1: the length octets at `pos`: the length and their
/// number.
pub fn read_length(input: &[u8], pos: usize, end: usize) -> (r: Option<(u64, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_length_ensures(input@, pos as nat, end as nat, view_length(r)),
{
    if pos >= end {
        return None;
    }
    let f = match input.get(pos) {
        Some(&b) => b,
        None => return None,
    };
    if f < 128 {
        // 1.
        return Some((f as u64, 1));
    }
    if f == 128 {
        // 2.
        return None;
    }
    if f == 255 {
        // 3.
        return None;
    }
    // 4. Never saturates: f >= 128.
    let n = f.saturating_sub(128) as usize;
    if n > 8 {
        return None;
    }
    // end > pos, so this is end - pos - 1 exactly.
    let rest = end.saturating_sub(pos).saturating_sub(1);
    if n > rest {
        return None;
    }
    // Never saturates: pos + 1 <= end.
    let first = pos.saturating_add(1);
    match input.get(first) {
        Some(&b) => {
            if b == 0 {
                return None;
            }
        },
        None => return None,
    }
    let v = read_be(input, first, n);
    if v < 128 {
        return None;
    }
    // Never saturates: n <= 8.
    Some((v, n.saturating_add(1)))
}

/// §8.1.1.1: the identifier octets, the length octets, and the contents
/// octets inside `[pos, end)`.
pub fn read_tlv(input: &[u8], pos: usize, end: usize) -> (r: Option<Tlv>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_tlv_ensures(input@, pos as nat, end as nat, view_tlv(r)),
        match r {
            Some(t) => pos < t.cstart && t.cstart <= t.cend && t.cend <= end,
            None => true,
        },
{
    proof {
        super::lemmas::lemma_read_tlv_bounds(input@, pos as nat, end as nat);
    }
    let (tag, id_len) = read_identifier(input, pos, end)?;
    // pos < end and id_len octets were read inside [pos, end).
    let after_id = pos.saturating_add(id_len);
    let (len, len_len) = read_length(input, after_id, end)?;
    // The length octets lie inside [after_id, end).
    let cstart = after_id.saturating_add(len_len);
    // cstart <= end, so this is end - cstart exactly.
    let room = end.saturating_sub(cstart);
    if len > room as u64 {
        return None;
    }
    // len <= room, so this is exact and never saturates.
    let cend = cstart.saturating_add(len as usize);
    Some(Tlv { tag, cstart, cend })
}

/// The end of contents: nothing is left in `[pos, end)`.
pub fn expect_end(pos: usize, end: usize) -> (r: bool)
    ensures
        super::contract::expect_end_ensures(pos as nat, end as nat, r),
{
    pos == end
}


/// Whether `tag` is the universal type `number`, in the given form.
fn is_universal(tag: Tag, constructed: bool, number: u32) -> (r: bool)
    ensures
        r == (tag == Tag { class: Class::Universal, constructed, number }),
{
    match tag.class {
        Class::Universal => tag.constructed == constructed && tag.number == number,
        _ => false,
    }
}

/// The octet at `index`, or 0 where there is none (the callers' bounds make
/// that unreachable).
pub(crate) fn octet_at(input: &[u8], index: usize) -> (o: u8)
    ensures
        index < input@.len() ==> o == input@[index as int],
{
    match input.get(index) {
        Some(&b) => b,
        None => 0,
    }
}

/// The spec view of a value and the next position.
pub open spec fn view_bool(r: Option<(bool, usize)>) -> Option<(bool, nat)> {
    match r {
        Some((v, n)) => Some((v, n as nat)),
        None => None,
    }
}

/// The spec view of a sign, a range and the next position.
pub open spec fn view_integer(r: Option<(bool, usize, usize, usize)>) -> Option<(bool, nat, nat, nat)> {
    match r {
        Some((v, a, b, n)) => Some((v, a as nat, b as nat, n as nat)),
        None => None,
    }
}

/// The spec view of an unused-bits count, a range and the next position.
pub open spec fn view_bit_string(r: Option<(u8, usize, usize, usize)>) -> Option<(u8, nat, nat, nat)> {
    match r {
        Some((v, a, b, n)) => Some((v, a as nat, b as nat, n as nat)),
        None => None,
    }
}

/// The spec view of a position.
pub open spec fn view_pos(r: Option<usize>) -> Option<nat> {
    match r {
        Some(n) => Some(n as nat),
        None => None,
    }
}

/// The spec view of an optional component's extent.
pub open spec fn view_optional(r: Option<Option<(bool, usize, usize)>>) -> Option<Option<(bool, nat, nat)>> {
    match r {
        Some(Some((c, a, b))) => Some(Some((c, a as nat, b as nat))),
        Some(None) => Some(None),
        None => None,
    }
}

/// The spec view of an optional explicitly tagged component's range.
pub open spec fn view_optional_range(r: Option<Option<(usize, usize)>>) -> Option<Option<(nat, nat)>> {
    match r {
        Some(Some((a, b))) => Some(Some((a as nat, b as nat))),
        Some(None) => Some(None),
        None => None,
    }
}

/// §8.2, §11.1: a BOOLEAN at `pos`: its value and the next position.
pub fn read_boolean(input: &[u8], pos: usize, end: usize) -> (r: Option<(bool, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_boolean_ensures(input@, pos as nat, end as nat, view_bool(r)),
{
    let t = read_tlv(input, pos, end)?;
    // 8.2.1: primitive.
    if !is_universal(t.tag, false, BOOLEAN) {
        return None;
    }
    // cstart <= cend, so this is the number of contents octets exactly.
    if t.cend.saturating_sub(t.cstart) != 1 {
        return None;
    }
    let o = octet_at(input, t.cstart);
    proof {
        let c = input@.subrange(t.cstart as int, t.cend as int);
        assert(c[0] == input@[t.cstart as int]);
    }
    if o == 0 {
        Some((false, t.cend))
    } else if o == 255 {
        Some((true, t.cend))
    } else {
        None
    }
}

/// §8.3: an INTEGER at `pos`: whether it is negative, the range of its
/// magnitude octets, and the next position.
pub fn read_integer(input: &[u8], pos: usize, end: usize) -> (r: Option<(bool, usize, usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_integer_ensures(input@, pos as nat, end as nat, view_integer(r)),
{
    let t = read_tlv(input, pos, end)?;
    if !is_universal(t.tag, false, INTEGER) {
        return None;
    }
    let len = t.cend.saturating_sub(t.cstart);
    // 8.3.1: one or more octets.
    if len == 0 {
        return None;
    }
    let first = octet_at(input, t.cstart);
    proof {
        let c = input@.subrange(t.cstart as int, t.cend as int);
        assert(c[0] == input@[t.cstart as int]);
    }
    // Never saturates: cstart < cend <= input.len().
    let second_index = t.cstart.saturating_add(1);
    if len >= 2 {
        let second = octet_at(input, second_index);
        proof {
            let c = input@.subrange(t.cstart as int, t.cend as int);
            assert(c[1] == input@[second_index as int]);
        }
        // 8.3.2.
        if (first == 255 && second >= 128) || (first == 0 && second < 128) {
            return None;
        }
    }
    let negative = first >= 128;
    let start = if len >= 2 && first == 0 {
        second_index
    } else {
        t.cstart
    };
    Some((negative, start, t.cend, t.cend))
}

/// 2 to the power of a number of unused bits.
fn pow2_unused_exec(u: u8) -> (p: u32)
    ensures
        p as nat == pow2_unused(u),
{
    if u == 0 {
        1
    } else if u == 1 {
        2
    } else if u == 2 {
        4
    } else if u == 3 {
        8
    } else if u == 4 {
        16
    } else if u == 5 {
        32
    } else if u == 6 {
        64
    } else {
        128
    }
}

/// §8.6, §11.2: a BIT STRING at `pos`: the number of unused bits, the range
/// of the octets that hold the bits, and the next position.
pub fn read_bit_string(input: &[u8], pos: usize, end: usize) -> (r: Option<(u8, usize, usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_bit_string_ensures(input@, pos as nat, end as nat, view_bit_string(r)),
{
    let t = read_tlv(input, pos, end)?;
    if !is_universal(t.tag, false, BIT_STRING) {
        return None;
    }
    let len = t.cend.saturating_sub(t.cstart);
    if len == 0 {
        return None;
    }
    let unused = octet_at(input, t.cstart);
    proof {
        let c = input@.subrange(t.cstart as int, t.cend as int);
        assert(c[0] == input@[t.cstart as int]);
    }
    // 8.6.2.2.
    if unused > 7 {
        return None;
    }
    if len == 1 {
        // 8.6.2.3.
        if unused != 0 {
            return None;
        }
    } else {
        // 11.2.1. Never saturates: cstart < cend.
        let last_index = t.cend.saturating_sub(1);
        let last = octet_at(input, last_index);
        proof {
            let c = input@.subrange(t.cstart as int, t.cend as int);
            assert(c.last() == input@[last_index as int]);
        }
        let p = pow2_unused_exec(unused);
        if !(last as u32).is_multiple_of(p) {
            return None;
        }
    }
    // Never saturates: cstart < cend.
    Some((unused, t.cstart.saturating_add(1), t.cend, t.cend))
}

/// §8.7, §10.2: a primitive value of the universal type `number` taken as
/// octets: the contents range.
pub fn read_octets(input: &[u8], pos: usize, end: usize, number: u32) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_octets_ensures(input@, pos as nat, end as nat, number, view_range(r)),
{
    let t = read_tlv(input, pos, end)?;
    if is_universal(t.tag, false, number) {
        Some((t.cstart, t.cend))
    } else {
        None
    }
}

/// An OCTET STRING (§8.7).
pub fn read_octet_string(input: &[u8], pos: usize, end: usize) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        view_range(r) == super::spec::read_octet_string(input@, pos as nat, end as nat),
{
    read_octets(input, pos, end, OCTET_STRING)
}

/// A UTF8String (its octets; the character rules are X.509's).
pub fn read_utf8_string(input: &[u8], pos: usize, end: usize) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        view_range(r) == super::spec::read_utf8_string(input@, pos as nat, end as nat),
{
    read_octets(input, pos, end, UTF8_STRING)
}

/// A PrintableString (its octets).
pub fn read_printable_string(input: &[u8], pos: usize, end: usize) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        view_range(r) == super::spec::read_printable_string(input@, pos as nat, end as nat),
{
    read_octets(input, pos, end, PRINTABLE_STRING)
}

/// An IA5String (its octets).
pub fn read_ia5_string(input: &[u8], pos: usize, end: usize) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        view_range(r) == super::spec::read_ia5_string(input@, pos as nat, end as nat),
{
    read_octets(input, pos, end, IA5_STRING)
}

/// A UTCTime (its octets).
pub fn read_utc_time(input: &[u8], pos: usize, end: usize) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        view_range(r) == super::spec::read_utc_time(input@, pos as nat, end as nat),
{
    read_octets(input, pos, end, UTC_TIME)
}

/// A GeneralizedTime (its octets).
pub fn read_generalized_time(input: &[u8], pos: usize, end: usize) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        view_range(r) == super::spec::read_generalized_time(input@, pos as nat, end as nat),
{
    read_octets(input, pos, end, GENERALIZED_TIME)
}

/// §8.8: a NULL at `pos`: the next position.
pub fn read_null(input: &[u8], pos: usize, end: usize) -> (r: Option<usize>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_null_ensures(input@, pos as nat, end as nat, view_pos(r)),
{
    let t = read_tlv(input, pos, end)?;
    if is_universal(t.tag, false, NULL) && t.cstart == t.cend {
        Some(t.cend)
    } else {
        None
    }
}

/// §8.9, §8.11: a value whose tag is the universal constructed type
/// `number`: its contents range.
pub fn expect_constructed(input: &[u8], pos: usize, end: usize, number: u32) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::expect_constructed_ensures(input@, pos as nat, end as nat, number, view_range(r)),
{
    let t = read_tlv(input, pos, end)?;
    if is_universal(t.tag, true, number) {
        Some((t.cstart, t.cend))
    } else {
        None
    }
}

/// A SEQUENCE or SEQUENCE OF (§8.9, §8.10): its contents range.
pub fn expect_sequence(input: &[u8], pos: usize, end: usize) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        view_range(r) == super::spec::expect_sequence(input@, pos as nat, end as nat),
{
    expect_constructed(input, pos, end, SEQUENCE)
}

/// A SET or SET OF (§8.11, §8.12): its contents range.
pub fn expect_set(input: &[u8], pos: usize, end: usize) -> (r: Option<(usize, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        view_range(r) == super::spec::expect_set(input@, pos as nat, end as nat),
{
    expect_constructed(input, pos, end, SET)
}

/// An OPTIONAL component with the context-specific tag `[number]` (§8.14).
pub fn read_optional_context(input: &[u8], pos: usize, end: usize, number: u32) -> (r: Option<
    Option<(bool, usize, usize)>,
>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_optional_context_ensures(input@, pos as nat, end as nat, number, view_optional(r)),
{
    if pos >= end {
        return Some(None);
    }
    let (tag, _) = read_identifier(input, pos, end)?;
    match tag.class {
        Class::ContextSpecific => {
            if tag.number == number {
                let t = read_tlv(input, pos, end)?;
                Some(Some((tag.constructed, t.cstart, t.cend)))
            } else {
                Some(None)
            }
        },
        _ => Some(None),
    }
}

/// As [`read_optional_context`] for an EXPLICIT tag (§8.14.3): the inner
/// range, which must be constructed.
pub fn read_optional_explicit(input: &[u8], pos: usize, end: usize, number: u32) -> (r: Option<Option<(usize, usize)>>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_optional_explicit_ensures(input@, pos as nat, end as nat, number, view_optional_range(r)),
{
    match read_optional_context(input, pos, end, number)? {
        None => Some(None),
        Some((constructed, cstart, cend)) => {
            if constructed {
                Some(Some((cstart, cend)))
            } else {
                None
            }
        },
    }
}


/// The components of an object identifier as spec numbers.
pub open spec fn nats(s: Seq<u64>) -> Seq<nat> {
    s.map_values(|x: u64| x as nat)
}

/// An optional list with a prefix put in front of it.
pub open spec fn prepend(p: Seq<nat>, o: Option<Seq<nat>>) -> Option<Seq<nat>> {
    match o {
        Some(r) => Some(p + r),
        None => None,
    }
}

/// The spec view of the components and the next position.
pub open spec fn view_oid(r: Option<(Vec<u64>, usize)>) -> Option<(Seq<nat>, nat)> {
    match r {
        Some((v, n)) => Some((nats(v@), n as nat)),
        None => None,
    }
}

/// The number of components, when there are any.
pub open spec fn oid_len(r: Option<(Vec<u64>, usize)>) -> Option<nat> {
    match r {
        Some((v, _)) => Some(v@.len()),
        None => None,
    }
}

/// §8.19.2: the subidentifiers of `c`, one `u64` each. Pushes only values it
/// has read: no more than there are octets.
fn subidentifiers_exec(c: &[u8]) -> (r: Option<Vec<u64>>)
    ensures
        match r {
            Some(v) => subidentifiers(c@) == Some(nats(v@)) && v@.len() <= c@.len(),
            None => subidentifiers(c@) is None,
        },
{
    let mut subs: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(c@.skip(0) =~= c@);
        assert(nats(subs@) =~= Seq::<nat>::empty());
        match subidentifiers(c@) {
            Some(r) => assert(Seq::<nat>::empty() + r =~= r),
            None => {},
        }
    }
    while i < c.len()
        invariant
            i <= c.len(),
            subs@.len() <= i,
            subidentifiers(c@) == prepend(nats(subs@), subidentifiers(c@.skip(i as int))),
        decreases c.len() - i,
    {
        proof {
            super::lemmas::lemma_subidentifiers_step(c@, i as nat);
            super::lemmas::lemma_series_end_in_range(c@, i as nat, c.len() as nat);
        }
        // 8.19.2: the leading octet of a subidentifier is not 80.
        if octet_at(c, i) == 128 {
            return None;
        }
        let (v, j) = read_series(c, i, c.len(), u64::MAX)?;
        let ghost old_subs = subs@;
        subs.push(v);
        proof {
            // The subidentifiers from `i` are `v` and then those from `j + 1`.
            let rest = c@.skip(j as int + 1);
            match subidentifiers(rest) {
                Some(r) => {
                    assert(nats(subs@) =~= nats(old_subs).push(v as nat));
                    assert(nats(old_subs) + (seq![v as nat] + r) =~= nats(subs@) + r);
                },
                None => {},
            }
        }
        // Never saturates: j < c.len().
        i = j.saturating_add(1);
    }
    proof {
        assert(c@.skip(i as int).len() == 0);
        super::lemmas::lemma_subidentifiers_empty(c@.skip(i as int));
        assert(nats(subs@) + Seq::<nat>::empty() =~= nats(subs@));
    }
    Some(subs)
}

/// §8.19: an OBJECT IDENTIFIER at `pos`: its components and the next
/// position. The vector holds one component per subidentifier, plus one:
/// never more than the contents octets plus one.
pub fn read_oid(input: &[u8], pos: usize, end: usize) -> (r: Option<(Vec<u64>, usize)>)
    requires
        super::contract::read_requires(input@.len(), end as nat),
    ensures
        super::contract::read_oid_ensures(input@, pos as nat, end as nat, view_oid(r)),
        super::contract::read_oid_alloc_ensures(input@, pos as nat, end as nat, oid_len(r)),
{
    let t = read_tlv(input, pos, end)?;
    // 8.19.1: primitive.
    if !is_universal(t.tag, false, OBJECT_IDENTIFIER) {
        return None;
    }
    let c = vstd::slice::slice_subrange(input, t.cstart, t.cend);
    let subs = subidentifiers_exec(c)?;
    // 8.19.3: at least one subidentifier.
    let first = match subs.first() {
        Some(&f) => f,
        None => return None,
    };
    // 8.19.4: the first subidentifier is (X * 40) + Y.
    let (x, y): (u64, u64) = if first < 40 {
        (0, first)
    } else if first < 80 {
        (1, first.saturating_sub(40))
    } else {
        (2, first.saturating_sub(80))
    };
    let mut arcs: Vec<u64> = Vec::new();
    arcs.push(x);
    arcs.push(y);
    let mut k: usize = 1;
    proof {
        assert(nats(arcs@) =~= seq![x as nat, y as nat]);
        assert(nats(subs@).subrange(1, 1) =~= Seq::<nat>::empty());
    }
    // 8.19.5: the others are the remaining components.
    while k < subs.len()
        invariant
            1 <= k <= subs.len(),
            nats(arcs@) =~= seq![x as nat, y as nat] + nats(subs@).subrange(1, k as int),
            arcs@.len() == k + 1,
        decreases subs.len() - k,
    {
        let s = match subs.get(k) {
            Some(&s) => s,
            None => return None,
        };
        let ghost before = nats(arcs@);
        arcs.push(s);
        proof {
            assert(nats(arcs@) =~= before.push(s as nat));
            assert(nats(subs@).subrange(1, k as int + 1) =~= nats(subs@).subrange(1, k as int).push(s as nat));
            assert(seq![x as nat, y as nat] + nats(subs@).subrange(1, k as int + 1) =~= (seq![x as nat, y as nat] + nats(
                subs@,
            ).subrange(1, k as int)).push(s as nat));
        }
        // Never saturates: k < subs.len().
        k = k.saturating_add(1);
    }
    proof {
        assert(nats(subs@).subrange(1, subs.len() as int) =~= nats(subs@).skip(1));
    }
    Some((arcs, t.cend))
}

} // verus!

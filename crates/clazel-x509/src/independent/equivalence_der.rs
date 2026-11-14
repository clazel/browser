//! `independent/der.rs` against `clazel_der::spec`: one encoding, object
//! identifiers, and the list of encodings in a constructed value. The domain
//! these lemmas state is explained in `equivalence.rs`.
//!
//! The two read differently. `clazel-der` is a cursor over one buffer;
//! `der.rs` splits a slice into a list of [`Tlv`](super::der::Tlv)s. So every
//! statement here is about `read_tlv(b, pos, end)` and the slice
//! `sl(b, pos, end)`, and [`tlv_view`] says the two describe one encoding.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::der as i;
#[cfg(verus_only)]
use clazel_der::spec as d;

verus! {

/// The octets `[pos, end)` of `b`.
pub open spec fn sl(b: Seq<u8>, pos: nat, end: nat) -> Seq<u8> {
    b.subrange(pos as int, end as int)
}

/// `[pos, end)` is a range of `b`.
pub open spec fn wf(b: Seq<u8>, pos: nat, end: nat) -> bool {
    pos <= end && end <= b.len()
}

/// A length no input reaches: an input is a slice in memory.
pub open spec fn two64() -> nat {
    0x1_0000_0000_0000_0000
}

/// `clazel-der`'s limit on a tag number, which `der.rs` does not have.
pub open spec fn tag_fits(u: i::Tlv) -> bool {
    u.number <= 16383
}

/// Universal 0, which `der.rs` refuses and `clazel-der` reads.
pub open spec fn tag_is_reserved(t: d::Tag) -> bool {
    t.class == d::Class::Universal && t.number == 0
}

/// `t` at `pos` of `b` and `u` are one encoding.
pub open spec fn tlv_view(b: Seq<u8>, pos: nat, t: d::Tlv, u: i::Tlv) -> bool {
    &&& u.class == d::class_bits(t.tag.class) as nat
    &&& u.constructed == t.tag.constructed
    &&& u.number == t.tag.number as nat
    &&& u.contents == sl(b, t.cstart, t.cend)
    &&& u.encoding == sl(b, pos, t.cend)
}

// ---------------------------------------------------------------------
// Identifier octets.
// ---------------------------------------------------------------------

/// A series of `clazel-der` over `b` is one over the slice.
pub proof fn lemma_series_slice(b: Seq<u8>, pos: nat, end: nat, k: nat)
    requires
        wf(b, pos, end),
        pos + k <= end,
    ensures
        d::series_end(b, pos + k, end) == match d::series_end(sl(b, pos, end), k, (end - pos) as nat) {
            Some(j) => Some(j + pos),
            None => None,
        },
    decreases end - pos - k,
{
    let s = sl(b, pos, end);
    if pos + k < end {
        assert(s[k as int] == b[(pos + k) as int]);
        if b[(pos + k) as int] >= 128 {
            lemma_series_slice(b, pos, end, k + 1);
        }
    }
}

/// 8.1.2.4.2's subsequent octets, from `at` on, spell the number from `from`.
pub proof fn lemma_high_run(s: Seq<u8>, from: nat, at: nat, acc: nat)
    requires
        1 <= from < at <= s.len(),
        acc == d::base128(s.subrange(from as int, at as int)),
    ensures
        i::high_tag_number(s, at, acc) == match d::series_end(s, at, s.len()) {
            None => None::<(nat, nat)>,
            Some(j) => Some((d::base128(s.subrange(from as int, j as int + 1)), j + 1)),
        },
    decreases s.len() - at,
{
    if at < s.len() {
        let octet = s[at as int];
        let next = acc * 128 + (octet % 128) as nat;
        assert(s.subrange(from as int, at as int + 1).drop_last() =~= s.subrange(from as int, at as int));
        assert(s.subrange(from as int, at as int + 1).last() == octet);
        assert(next == d::base128(s.subrange(from as int, at as int + 1)));
        if octet >= 128 {
            lemma_high_run(s, from, at + 1, next);
        }
    }
}

/// The high-tag-number form, from the first subsequent octet.
pub proof fn lemma_high_tag(s: Seq<u8>)
    requires
        s.len() >= 1,
    ensures
        i::high_tag_number(s, 1, 0) == match d::series_end(s, 1, s.len()) {
            None => None::<(nat, nat)>,
            Some(j) => if s[1] % 128 == 0 {
                None
            } else {
                Some((d::base128(s.subrange(1, j as int + 1)), j + 1))
            },
        },
{
    if s.len() > 1 {
        let octet = s[1];
        if octet % 128 == 0 {
            if octet >= 128 {
                // Both refuse, whichever way the series ends.
                assert(i::high_tag_number(s, 1, 0) is None);
            }
        } else {
            let next = 0 * 128 + (octet % 128) as nat;
            assert(s.subrange(1, 2).drop_last() =~= Seq::<u8>::empty());
            assert(s.subrange(1, 2).last() == octet);
            assert(d::base128(Seq::<u8>::empty()) == 0);
            assert(next == d::base128(s.subrange(1, 2)));
            if octet >= 128 {
                lemma_high_run(s, 1, 2, next);
            }
        }
    }
}

/// Identifier octets: `clazel-der` reads what `der.rs` reads, except a number
/// over its limit.
pub proof fn lemma_identifier(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
    ensures
        match d::read_identifier(b, pos, end) {
            Some((tag, n)) => i::parse_identifier(sl(b, pos, end)) == Some(
                i::Identifier {
                    class: d::class_bits(tag.class) as nat,
                    constructed: tag.constructed,
                    number: tag.number as nat,
                    size: n,
                },
            ),
            None => match i::parse_identifier(sl(b, pos, end)) {
                Some(id) => id.number > 16383,
                None => true,
            },
        },
{
    let s = sl(b, pos, end);
    if pos < end {
        let o = b[pos as int];
        assert(s[0] == o);
        clazel_der::lemmas_tlv::lemma_class_from_bits_roundtrip(o / 64);
        if o % 32 == 31 {
            lemma_high_tag(s);
            lemma_series_slice(b, pos, end, 1);
            if let Some(j) = d::series_end(s, 1, s.len()) {
                clazel_der::lemmas::lemma_series_end_in_range(s, 1, s.len());
                assert(s[1] == b[pos as int + 1]);
                assert(b.subrange(pos as int + 1, (j + pos) as int + 1) =~= s.subrange(1, j as int + 1));
            }
        }
    }
}

// ---------------------------------------------------------------------
// Length octets.
// ---------------------------------------------------------------------

/// 8.1.3.5's number, written two ways.
pub proof fn lemma_big_endian(s: Seq<u8>, at: nat, count: nat)
    requires
        at + count <= s.len(),
    ensures
        i::big_endian(s, at, count) == d::be_value(s.subrange(at as int, (at + count) as int)),
    decreases count,
{
    let r = s.subrange(at as int, (at + count) as int);
    if count > 0 {
        lemma_big_endian(s, at, (count - 1) as nat);
        assert(r.drop_last() =~= s.subrange(at as int, (at + count - 1) as int));
        assert(r.last() == s[(at + count - 1) as int]);
    } else {
        assert(r =~= Seq::<u8>::empty());
    }
}

/// Length octets. `clazel-der` stops at eight subsequent octets; a length
/// that needs more is longer than any input.
pub proof fn lemma_length(b: Seq<u8>, pos: nat, end: nat, at: nat)
    requires
        wf(b, pos, end),
        at >= 1,
        pos + at <= end,
        end - pos < two64(),
    ensures
        match d::read_length(b, pos + at, end) {
            Some((len, n)) => i::parse_length(sl(b, pos, end), at) == Some((len, at + n)),
            None => match i::parse_length(sl(b, pos, end), at) {
                Some((len, start)) => start + len > end - pos,
                None => true,
            },
        },
{
    let s = sl(b, pos, end);
    let p = pos + at;
    if p < end {
        let f = b[p as int];
        assert(s[at as int] == f);
        if f >= 128 && f != 128 && f != 255 {
            let n = (f - 128) as nat;
            if at + 1 + n <= s.len() {
                assert(s[(at + 1) as int] == b[p as int + 1]);
                lemma_big_endian(s, at + 1, n);
                let r = b.subrange(p as int + 1, p as int + 1 + n as int);
                assert(s.subrange((at + 1) as int, (at + 1 + n) as int) =~= r);
                if n > 8 && b[p as int + 1] != 0 {
                    // Nine octets with a nonzero first one are at least 2^64.
                    assert(r[0] == b[p as int + 1]);
                    clazel_der::lemmas_tlv::lemma_be_value_leading_nonzero(r);
                    clazel_der::lemmas_tlv::lemma_pow256_monotone(8, (n - 1) as nat);
                    clazel_der::lemmas::lemma_pow256_8();
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// One encoding.
// ---------------------------------------------------------------------

/// **One encoding.** `read_tlv` and `parse_tlv` read the same encoding,
/// except universal 0 (`der.rs` refuses it) and a tag number over 16383
/// (`clazel-der` refuses it). A long-form length of more than eight octets is
/// not a third exception: it is longer than any input.
pub proof fn lemma_tlv(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
    ensures
        match d::read_tlv(b, pos, end) {
            Some(t) => {
                &&& pos < t.cstart <= t.cend <= end
                &&& !tag_is_reserved(t.tag) ==> {
                    &&& i::parse_tlv(sl(b, pos, end)) is Some
                    &&& tlv_view(b, pos, t, i::parse_tlv(sl(b, pos, end))->Some_0)
                }
            },
            None => match i::parse_tlv(sl(b, pos, end)) {
                Some(u) => !tag_fits(u),
                None => true,
            },
        },
{
    let s = sl(b, pos, end);
    lemma_identifier(b, pos, end);
    clazel_der::lemmas::lemma_read_tlv_bounds(b, pos, end);
    match d::read_identifier(b, pos, end) {
        None => {},
        Some((tag, id_len)) => {
            clazel_der::lemmas::lemma_read_identifier_bounds(b, pos, end);
            lemma_length(b, pos, end, id_len);
            assert(i::parse_identifier(s)->Some_0.size == id_len);
            match d::read_length(b, pos + id_len, end) {
                None => {},
                Some((len, len_len)) => {
                    clazel_der::lemmas::lemma_read_length_bounds(b, pos + id_len, end);
                    let cstart = pos + id_len + len_len;
                    if cstart + len <= end && !tag_is_reserved(tag) {
                        let t = d::read_tlv(b, pos, end)->Some_0;
                        let u = i::parse_tlv(s)->Some_0;
                        assert(t.cstart == cstart);
                        assert(t.cend == cstart + len);
                        lemma_class_universal(tag);
                        assert(s.subrange((id_len + len_len) as int, (id_len + len_len + len) as int)
                            =~= sl(b, t.cstart, t.cend));
                        assert(s.subrange(0, (id_len + len_len + len) as int) =~= sl(b, pos, t.cend));
                    }
                },
            }
        },
    }
}

/// Table 1's class 0 is `Universal`.
pub proof fn lemma_class_universal(tag: d::Tag)
    ensures
        (d::class_bits(tag.class) == 0) == (tag.class == d::Class::Universal),
{
}

// ---------------------------------------------------------------------
// The list of encodings in a constructed value.
// ---------------------------------------------------------------------

/// No octets are no encodings.
pub proof fn lemma_tlvs_empty(b: Seq<u8>, pos: nat)
    requires
        pos <= b.len(),
    ensures
        i::parse_tlvs(sl(b, pos, pos)) == Some(Seq::<i::Tlv>::empty()),
{
    assert(sl(b, pos, pos).len() == 0);
}

/// `parse_tlvs` from what `clazel-der` read: one more at the front.
pub proof fn lemma_tlvs_cons(b: Seq<u8>, pos: nat, end: nat, r: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        i::parse_tlvs(sl(b, d::read_tlv(b, pos, end)->Some_0.cend, end)) == Some(r),
    ensures
        i::parse_tlv(sl(b, pos, end)) is Some,
        i::parse_tlvs(sl(b, pos, end)) == Some(seq![i::parse_tlv(sl(b, pos, end))->Some_0] + r),
{
    lemma_tlv(b, pos, end);
    let s = sl(b, pos, end);
    let t = d::read_tlv(b, pos, end)->Some_0;
    let u = i::parse_tlv(s)->Some_0;
    assert(u.encoding.len() == t.cend - pos);
    assert(s.subrange(u.encoding.len() as int, s.len() as int) =~= sl(b, t.cend, end));
}

/// What `parse_tlvs` split, `clazel-der` reads one at a time.
pub proof fn lemma_tlvs_head(b: Seq<u8>, pos: nat, end: nat, e: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_tlvs(sl(b, pos, end)) == Some(e),
        e.len() > 0,
        tag_fits(e[0]),
    ensures
        d::read_tlv(b, pos, end) is Some,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        tlv_view(b, pos, d::read_tlv(b, pos, end)->Some_0, e[0]),
        i::parse_tlv(sl(b, pos, end)) == Some(e[0]),
        i::parse_tlvs(sl(b, d::read_tlv(b, pos, end)->Some_0.cend, end)) == Some(e.skip(1)),
{
    let s = sl(b, pos, end);
    lemma_tlv(b, pos, end);
    let u = i::parse_tlv(s)->Some_0;
    let rest = i::parse_tlvs(s.subrange(u.encoding.len() as int, s.len() as int))->Some_0;
    assert(e =~= seq![u] + rest);
    assert(e[0] == u);
    assert(e.skip(1) =~= rest);
    lemma_parse_tlv_not_reserved(s);
    let t = d::read_tlv(b, pos, end)->Some_0;
    assert(u.encoding.len() == t.cend - pos);
    assert(s.subrange(u.encoding.len() as int, s.len() as int) =~= sl(b, t.cend, end));
}

/// X.680 Table 1: what `parse_tlv` reads is not universal 0.
pub proof fn lemma_parse_tlv_not_reserved(s: Seq<u8>)
    requires
        i::parse_tlv(s) is Some,
    ensures
        !(i::parse_tlv(s)->Some_0.class == 0 && i::parse_tlv(s)->Some_0.number == 0),
{
}

/// A list of encodings has no octets exactly when it is empty.
pub proof fn lemma_tlvs_none_left(b: Seq<u8>, pos: nat, end: nat, e: Seq<i::Tlv>)
    requires
        wf(b, pos, end),
        i::parse_tlvs(sl(b, pos, end)) == Some(e),
    ensures
        (e.len() == 0) == (pos == end),
{
    let s = sl(b, pos, end);
    if pos < end {
        assert(s.len() > 0);
        assert(e.len() > 0);
    }
}

/// `parse_single` is `parse_tlv` with nothing after it.
pub proof fn lemma_single(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        d::read_tlv(b, pos, end) is Some,
        d::read_tlv(b, pos, end)->Some_0.cend == end,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
    ensures
        i::parse_single(sl(b, pos, end)) is Some,
        tlv_view(b, pos, d::read_tlv(b, pos, end)->Some_0, i::parse_single(sl(b, pos, end))->Some_0),
{
    lemma_tlv(b, pos, end);
}

/// The other way.
pub proof fn lemma_single_back(b: Seq<u8>, pos: nat, end: nat, u: i::Tlv)
    requires
        wf(b, pos, end),
        end - pos < two64(),
        i::parse_single(sl(b, pos, end)) == Some(u),
        tag_fits(u),
    ensures
        d::read_tlv(b, pos, end) is Some,
        d::read_tlv(b, pos, end)->Some_0.cend == end,
        !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag),
        tlv_view(b, pos, d::read_tlv(b, pos, end)->Some_0, u),
{
    lemma_tlv(b, pos, end);
    lemma_parse_tlv_not_reserved(sl(b, pos, end));
    assert(u.encoding.len() == end - pos);
}

// ---------------------------------------------------------------------
// Object identifiers.
// ---------------------------------------------------------------------

/// Every subidentifier fits `clazel-der`'s limit.
pub open spec fn subs_fit(v: Seq<nat>) -> bool {
    forall|k: int| 0 <= k < v.len() ==> #[trigger] v[k] < two64()
}

/// **`clazel-der`'s limit on a subidentifier**, on the components of an object
/// identifier: the first subidentifier is X*40 + Y (8.19.4).
pub open spec fn oid_fits(o: Seq<nat>) -> bool {
    &&& o.len() >= 2
    &&& o[0] * 40 + o[1] < two64()
    &&& forall|k: int| 2 <= k < o.len() ==> #[trigger] o[k] < two64()
}

/// 8.19.2's series, from `at` on, spells the number from `from`.
pub proof fn lemma_sub_run(c: Seq<u8>, from: nat, at: nat, partial: nat)
    requires
        from < at <= c.len(),
        partial == d::base128(c.subrange(from as int, at as int)),
    ensures
        i::subidentifiers(c, at, partial, true) == match d::series_end(c, at, c.len()) {
            None => None::<Seq<nat>>,
            Some(j) => match i::subidentifiers(c, j + 1, 0, false) {
                None => None,
                Some(rest) => Some(seq![d::base128(c.subrange(from as int, j as int + 1))] + rest),
            },
        },
    decreases c.len() - at,
{
    if at < c.len() {
        let octet = c[at as int];
        let next = partial * 128 + (octet % 128) as nat;
        assert(c.subrange(from as int, at as int + 1).drop_last() =~= c.subrange(from as int, at as int));
        assert(c.subrange(from as int, at as int + 1).last() == octet);
        assert(next == d::base128(c.subrange(from as int, at as int + 1)));
        if octet >= 128 {
            lemma_sub_run(c, from, at + 1, next);
        }
    }
}

/// The subidentifiers of a suffix, read both ways.
pub proof fn lemma_subidentifiers(c: Seq<u8>, at: nat)
    requires
        at <= c.len(),
    ensures
        match d::subidentifiers(c.skip(at as int)) {
            Some(v) => i::subidentifiers(c, at, 0, false) == Some(v) && subs_fit(v),
            None => match i::subidentifiers(c, at, 0, false) {
                Some(v) => !subs_fit(v),
                None => true,
            },
        },
    decreases c.len() - at,
{
    if at >= c.len() {
        assert(c.skip(at as int) =~= Seq::<u8>::empty());
        assert(d::subidentifiers(Seq::<u8>::empty()) == Some(Seq::<nat>::empty()));
        assert(subs_fit(Seq::<nat>::empty()));
    } else {
        clazel_der::lemmas::lemma_subidentifiers_step(c, at);
        clazel_der::lemmas_oid::lemma_series_end_props(c, at, c.len());
        let octet = c[at as int];
        let value = 0 * 128 + (octet % 128) as nat;
        assert(c.subrange(at as int, at as int + 1).drop_last() =~= Seq::<u8>::empty());
        assert(c.subrange(at as int, at as int + 1).last() == octet);
        assert(d::base128(Seq::<u8>::empty()) == 0);
        assert(value == d::base128(c.subrange(at as int, at as int + 1)));
        if octet >= 128 {
            lemma_sub_run(c, at, at + 1, value);
        }
        if let Some(j) = d::series_end(c, at, c.len()) {
            if octet < 128 {
                assert(j == at);
            }
            let v = d::base128(c.subrange(at as int, j as int + 1));
            lemma_subidentifiers(c, j + 1);
            if octet != 0x80 {
                match i::subidentifiers(c, j + 1, 0, false) {
                    Some(rest) => {
                        let all = seq![v] + rest;
                        assert(all[0] == v);
                        assert(forall|k: int| 0 <= k < rest.len() ==> #[trigger] rest[k] == all[k + 1]);
                        if d::subidentifiers(c.skip(j as int + 1)) is Some && v < two64() {
                            assert(subs_fit(all));
                        }
                        if !subs_fit(rest) {
                            let k = choose|k: int| 0 <= k < rest.len() && !(#[trigger] rest[k] < two64());
                            assert(all[k + 1] == rest[k]);
                        }
                    },
                    None => {},
                }
            }
        }
    }
}

/// 8.19: the two transcriptions give one list of components.
pub proof fn lemma_oid_contents(c: Seq<u8>)
    ensures
        match d::oid_components(c) {
            Some(o) => i::object_identifier_contents(c) == Some(o) && oid_fits(o),
            None => match i::object_identifier_contents(c) {
                Some(o) => !oid_fits(o),
                None => true,
            },
        },
{
    assert(c.skip(0) =~= c);
    lemma_subidentifiers(c, 0);
    if let Some(subs) = i::subidentifiers(c, 0, 0, false) {
        if subs.len() > 0 {
            let o = i::first_two_components(subs[0]) + subs.subrange(1, subs.len() as int);
            let (x, y) = d::first_components(subs[0]);
            assert(i::first_two_components(subs[0]) =~= seq![x, y]);
            assert(o[0] == x);
            assert(o[1] == y);
            assert(x * 40 + y == subs[0]);
            assert(forall|k: int| 2 <= k < o.len() ==> #[trigger] o[k] == subs[k - 1]);
            if !subs_fit(subs) {
                let k = choose|k: int| 0 <= k < subs.len() && !(#[trigger] subs[k] < two64());
                if k > 0 {
                    assert(o[k + 1] == subs[k]);
                }
            } else {
                assert(subs[0] < two64());
            }
            if d::subidentifiers(c) is Some {
                assert(seq![x, y] + subs.skip(1) =~= o);
            }
        }
    }
}

/// `has_tag` of a universal type is `clazel-der`'s tag test.
pub proof fn lemma_has_universal_tag(b: Seq<u8>, pos: nat, t: d::Tlv, u: i::Tlv, number: u32, constructed: bool)
    requires
        tlv_view(b, pos, t, u),
    ensures
        i::has_tag(u, 0, number as nat, constructed) == (t.tag == (d::Tag {
            class: d::Class::Universal,
            constructed,
            number,
        })),
{
    lemma_class_universal(t.tag);
}

/// An OBJECT IDENTIFIER at `pos`, read both ways.
pub proof fn lemma_read_oid(b: Seq<u8>, pos: nat, end: nat)
    requires
        wf(b, pos, end),
        end - pos < two64(),
    ensures
        match d::read_oid(b, pos, end) {
            Some((o, n)) => {
                &&& i::parse_tlv(sl(b, pos, end)) is Some
                &&& i::decode_object_identifier(i::parse_tlv(sl(b, pos, end))->Some_0) == Some(o)
                &&& d::read_tlv(b, pos, end) is Some
                &&& d::read_tlv(b, pos, end)->Some_0.cend == n
                &&& !tag_is_reserved(d::read_tlv(b, pos, end)->Some_0.tag)
                &&& pos < n <= end
                &&& oid_fits(o)
            },
            None => match i::parse_tlv(sl(b, pos, end)) {
                Some(u) => match i::decode_object_identifier(u) {
                    Some(o) => !oid_fits(o),
                    None => true,
                },
                None => true,
            },
        },
{
    lemma_tlv(b, pos, end);
    if let Some(t) = d::read_tlv(b, pos, end) {
        let c = sl(b, t.cstart, t.cend);
        lemma_oid_contents(c);
        if !tag_is_reserved(t.tag) {
            let u = i::parse_tlv(sl(b, pos, end))->Some_0;
            lemma_has_universal_tag(b, pos, t, u, d::OBJECT_IDENTIFIER, false);
        }
    }
}

// ---------------------------------------------------------------------
// BIT STRING and INTEGER.
// ---------------------------------------------------------------------

/// The two tests of a BIT STRING's contents, and its value.
pub proof fn lemma_bit_string_contents(c: Seq<u8>)
    ensures
        d::bit_string_contents_ok(c) == (i::bit_string_contents(c) is Some),
        d::bit_string_contents_ok(c) ==> i::bit_string_contents(c)->Some_0 == (i::BitString {
            octets: c.subrange(1, c.len() as int),
            unused: c[0] as nat,
        }),
{
    if c.len() >= 1 {
        let octets = c.subrange(1, c.len() as int);
        if c[0] <= 7 {
            assert(i::bit_weight(c[0] as nat) == d::pow2_unused(c[0]));
            if c.len() >= 2 {
                assert(octets[(octets.len() - 1) as int] == c.last());
            }
        }
    }
}

/// `power_256` is `pow256`.
pub proof fn lemma_power_256(n: nat)
    ensures
        i::power_256(n) == d::pow256(n),
    decreases n,
{
    if n > 0 {
        lemma_power_256((n - 1) as nat);
    }
}

/// `magnitude` is `be_value` of a prefix.
pub proof fn lemma_magnitude(c: Seq<u8>, count: nat)
    requires
        count <= c.len(),
    ensures
        i::magnitude(c, count) == d::be_value(c.subrange(0, count as int)),
    decreases count,
{
    let r = c.subrange(0, count as int);
    if count > 0 {
        lemma_magnitude(c, (count - 1) as nat);
        assert(r.drop_last() =~= c.subrange(0, count - 1));
        assert(r.last() == c[count - 1]);
    } else {
        assert(r =~= Seq::<u8>::empty());
    }
}

/// The two tests of an INTEGER's contents, and its value.
pub proof fn lemma_integer_contents(c: Seq<u8>)
    ensures
        d::integer_contents_ok(c) == (i::integer_contents(c) is Some),
        d::integer_contents_ok(c) ==> i::integer_contents(c) == Some(d::integer_value(c)),
{
    if c.len() >= 1 {
        lemma_magnitude(c, c.len());
        assert(c.subrange(0, c.len() as int) =~= c);
        lemma_power_256(c.len());
    }
}

/// `be_value` is at least its first octet's weight.
pub proof fn lemma_be_lower(r: Seq<u8>)
    requires
        r.len() >= 1,
    ensures
        d::be_value(r) >= r[0] * d::pow256((r.len() - 1) as nat),
    decreases r.len(),
{
    if r.len() == 1 {
        assert(r.drop_last() =~= Seq::<u8>::empty());
        assert(d::pow256(0) == 1);
        assert(r.last() == r[0]);
        assert(d::be_value(Seq::<u8>::empty()) == 0);
        assert(d::be_value(r) == r[0] as nat);
        assert((r.len() - 1) as nat == 0);
        assert(r[0] * d::pow256(0) == r[0] as int);
    } else {
        let e = r.drop_last();
        assert(e[0] == r[0]);
        lemma_be_lower(e);
        let p = d::pow256((r.len() - 2) as nat);
        let x = r[0] as int;
        let v = d::be_value(e) as int;
        assert(d::pow256((r.len() - 1) as nat) == 256 * p);
        assert(x * (256 * p) == (x * p) * 256) by (nonlinear_arith);
        assert(v * 256 >= (x * p) * 256) by (nonlinear_arith)
            requires
                v >= x * p,
        ;
        assert(d::be_value(r) == d::be_value(e) * 256 + r.last() as nat);
        assert(x * d::pow256((r.len() - 1) as nat) == (x * p) * 256);
    }
}

/// A leading zero octet does not change `be_value`.
pub proof fn lemma_be_skip_zero(c: Seq<u8>)
    requires
        c.len() >= 2,
        c[0] == 0,
    ensures
        d::be_value(c) == d::be_value(c.skip(1)),
    decreases c.len(),
{
    let e = c.drop_last();
    if c.len() == 2 {
        assert(e.drop_last() =~= Seq::<u8>::empty());
        assert(e.last() == 0);
        assert(c.skip(1).drop_last() =~= Seq::<u8>::empty());
        assert(c.skip(1).last() == c.last());
        assert(d::be_value(Seq::<u8>::empty()) == 0);
        assert(d::be_value(e) == d::be_value(e.drop_last()) * 256 + e.last() as nat);
        assert(d::be_value(e) == 0);
        assert(d::be_value(c) == d::be_value(e) * 256 + c.last() as nat);
        assert(d::be_value(c.skip(1)) == d::be_value(c.skip(1).drop_last()) * 256 + c.skip(1).last() as nat);
    } else {
        assert(e[0] == 0);
        lemma_be_skip_zero(e);
        assert(c.skip(1).drop_last() =~= e.skip(1));
        assert(c.skip(1).last() == c.last());
        assert(d::be_value(c) == d::be_value(e) * 256 + c.last() as nat);
        assert(d::be_value(c.skip(1)) == d::be_value(c.skip(1).drop_last()) * 256 + c.skip(1).last() as nat);
    }
}

/// 8.3.3: bit 8 of the first octet is the sign.
pub proof fn lemma_integer_sign(c: Seq<u8>)
    requires
        c.len() >= 1,
    ensures
        (d::integer_value(c) < 0) == (c[0] >= 128),
{
    if c[0] >= 128 {
        clazel_der::lemmas::lemma_be_value_bound(c);
    }
}

/// **A DER INTEGER's size follows from its value:** `n` octets hold the values
/// below 2^(8n-1), so a non-negative value below that takes at most `n`
/// octets (8.3.2).
pub proof fn lemma_integer_size(c: Seq<u8>, n: nat)
    requires
        n >= 1,
        d::integer_contents_ok(c),
        d::integer_value(c) >= 0,
        d::integer_value(c) < 128 * d::pow256((n - 1) as nat),
    ensures
        c.len() <= n,
{
    if c.len() > n {
        lemma_integer_sign(c);
        if c[0] == 0 {
            assert(c[1] >= 128);
            lemma_be_skip_zero(c);
            let r = c.skip(1);
            assert(r[0] == c[1]);
            lemma_be_lower(r);
            clazel_der::lemmas_tlv::lemma_pow256_monotone((n - 1) as nat, (r.len() - 1) as nat);
            let p = d::pow256((r.len() - 1) as nat) as int;
            let q = d::pow256((n - 1) as nat) as int;
            let x = r[0] as int;
            assert(x * p >= 128 * q) by (nonlinear_arith)
                requires
                    x >= 128,
                    p >= q,
                    q >= 0,
            ;
        } else {
            clazel_der::lemmas_tlv::lemma_be_value_leading_nonzero(c);
            clazel_der::lemmas_tlv::lemma_pow256_monotone(n, (c.len() - 1) as nat);
            clazel_der::lemmas::lemma_pow256_positive((n - 1) as nat);
            assert(d::pow256(n) == 256 * d::pow256((n - 1) as nat));
        }
    }
}

} // verus!

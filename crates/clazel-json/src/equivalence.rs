//! Proof that the independent transcription from RFC 8259
//! ([`super::independent`]) and the primary spec ([`super::spec`]) accept
//! the same texts and construct the same value, up to one stated relation.
//!
//! # The theorem
//!
//! [`theorem_json_text_equivalent`]: for every text (a `Seq<u32>`),
//! `json_parse(text) == prim_of(json_text(text))`, where `prim_of` maps a
//! missing value to a missing value and a value `v` to [`to_prim`]`(v)`.
//! So the two accept exactly the same texts, and where they accept,
//! [`to_prim`] carries RFC 8259's value to ECMA-262's.
//!
//! # The relation `to_prim`
//!
//! It is the identity on `null`, `true`, `false`, numbers (the source
//! text), the shape of arrays (element by element) and of objects (member
//! by member, order and duplicates kept), and it differs in one place:
//!
//! - **Strings.** RFC 8259 §7 reads a string as code points, and two `\u`
//!   escapes that name a surrogate pair as the one code point they encode;
//!   ECMA-262 reads it as UTF-16 code units. `to_prim` is the UTF-16
//!   encoding of the code points ([`utf16_of`]). It is not injective: the
//!   text `"𝄞"` is the one code point U+1D11E to RFC 8259, and
//!   `"\uD834` then the lone code point U+DD1E`"` is two (lone surrogates
//!   are code points a text may contain, §8.2 calling their meaning
//!   unpredictable), yet both are the same two code units
//!   ([`lemma_to_prim_not_injective`]). The relation is exactly "same code
//!   units"; no input is accepted by one and rejected by the other.
//!
//! # Where the two standards differ, and what this file shows about it
//!
//! - **Accepted texts.** None found. RFC 8259 and ECMA-404 give the same
//!   grammar (RFC 8259 §1 says so), and the theorem is the proof that this
//!   crate's two transcriptions agree on it, including `ws` (U+0020,
//!   U+0009, U+000A, U+000D only), numbers (no leading zero, `.` and `e`
//!   need digits, no `+` prefix), `unescaped` (U+0020 and above except
//!   `"` and `\`, surrogates included) and `escape`.
//! - **Top level.** RFC 8259 §2 (any value) and ECMA-262's `JSON.parse`
//!   (any value) agree; RFC 4627's object-or-array rule is not used.
//! - **Duplicate names.** RFC 8259 §4 leaves them unpredictable; both
//!   transcriptions keep every member. ECMA-262's heap overwrites; that is
//!   not modelled in either.
//! - **Nesting.** RFC 8259 §9 allows a limit; both use 512
//!   ([`lemma_same_nesting_limit`]).
//! - **Termination guards.** Both transcriptions refuse a repetition
//!   that would not advance (`parse_elements`' length test; `array_rest`'s
//!   `p2 > pos`). The proof shows neither ever fires: see
//!   [`lemma_value_progress`] and its siblings, and the `done.len() <= pos`
//!   invariants below.
//!
//! No difference showed the primary spec wrong; `spec.rs` is unchanged.
//!
//! # How the proof is organised
//!
//! The two transcriptions differ in where they put `ws`: `spec.rs` skips
//! it before a token; RFC 8259's `begin-array`, `end-array` and the other
//! structural tokens carry it on both sides, so an array's matched text
//! includes the `ws` after its `]`. Positions are therefore related by
//! [`rel_value`]: the RFC's end position and the primary's agree *after
//! skipping `ws`*, which is all anything downstream looks at.

#[cfg(verus_only)]
use super::independent as r;
#[cfg(verus_only)]
use super::spec as p;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The relation between the two value types.
// ---------------------------------------------------------------------

/// The UTF-16 encoding of a sequence of code points (each at most
/// U+10FFFF), by `UTF16EncodeCodePoint` (ECMA-262), concatenated.
pub open spec fn utf16_of(v: Seq<u32>) -> Seq<u16>
    decreases v.len(),
{
    if v.len() == 0 {
        Seq::empty()
    } else {
        utf16_of(v.drop_last()) + p::utf16_encode_code_point(v.last())
    }
}

/// RFC 8259's value, read as ECMA-262's: strings go from code points to
/// code units, everything else keeps its shape.
pub open spec fn to_prim(v: r::Json8259) -> p::JsonValue
    decreases v,
{
    match v {
        r::Json8259::False => p::JsonValue::Bool(false),
        r::Json8259::Null => p::JsonValue::Null,
        r::Json8259::True => p::JsonValue::Bool(true),
        r::Json8259::Number(t) => p::JsonValue::Number(t),
        r::Json8259::String(u) => p::JsonValue::String(utf16_of(u)),
        r::Json8259::Array(a) => p::JsonValue::Array(
            Seq::new(a.len(), |i: int| if 0 <= i < a.len() { to_prim(a[i]) } else { p::JsonValue::Null }),
        ),
        r::Json8259::Object(ms) => p::JsonValue::Object(
            Seq::new(
                ms.len(),
                |i: int|
                    if 0 <= i < ms.len() {
                        p::JsonMember { key: utf16_of(ms[i].name), value: to_prim(ms[i].value) }
                    } else {
                        p::JsonMember { key: Seq::empty(), value: p::JsonValue::Null }
                    },
            ),
        ),
    }
}

/// `to_prim` over a sequence of elements. Opaque so that the loops below
/// do not unfold its `Seq::new`.
#[verifier::opaque]
pub open spec fn prim_items(a: Seq<r::Json8259>) -> Seq<p::JsonValue> {
    Seq::new(a.len(), |i: int| if 0 <= i < a.len() { to_prim(a[i]) } else { p::JsonValue::Null })
}

/// One member, read as ECMA-262's.
pub open spec fn prim_member(m: r::Member8259) -> p::JsonMember {
    p::JsonMember { key: utf16_of(m.name), value: to_prim(m.value) }
}

/// `prim_member` over a sequence of members. Opaque, as `prim_items`.
#[verifier::opaque]
pub open spec fn prim_members(ms: Seq<r::Member8259>) -> Seq<p::JsonMember> {
    Seq::new(
        ms.len(),
        |i: int|
            if 0 <= i < ms.len() {
                prim_member(ms[i])
            } else {
                p::JsonMember { key: Seq::empty(), value: p::JsonValue::Null }
            },
    )
}

/// `json_parse`'s answer as RFC 8259's value would be read.
pub open spec fn prim_of(o: Option<r::Json8259>) -> Option<p::JsonValue> {
    match o {
        Some(v) => Some(to_prim(v)),
        None => None,
    }
}

proof fn lemma_prim_items_empty()
    ensures
        prim_items(Seq::<r::Json8259>::empty()) == Seq::<p::JsonValue>::empty(),
{
    reveal(prim_items);
    assert(prim_items(Seq::<r::Json8259>::empty()) =~= Seq::<p::JsonValue>::empty());
}

proof fn lemma_prim_items_push(a: Seq<r::Json8259>, v: r::Json8259)
    ensures
        prim_items(a.push(v)) == prim_items(a).push(to_prim(v)),
{
    reveal(prim_items);
    assert(prim_items(a.push(v)) =~= prim_items(a).push(to_prim(v)));
}

proof fn lemma_prim_members_empty()
    ensures
        prim_members(Seq::<r::Member8259>::empty()) == Seq::<p::JsonMember>::empty(),
{
    reveal(prim_members);
    assert(prim_members(Seq::<r::Member8259>::empty()) =~= Seq::<p::JsonMember>::empty());
}

proof fn lemma_prim_members_push(ms: Seq<r::Member8259>, m: r::Member8259)
    ensures
        prim_members(ms.push(m)) == prim_members(ms).push(prim_member(m)),
{
    reveal(prim_members);
    assert(prim_members(ms.push(m)) =~= prim_members(ms).push(prim_member(m)));
}

proof fn lemma_to_prim_array(a: Seq<r::Json8259>)
    ensures
        to_prim(r::Json8259::Array(a)) == p::JsonValue::Array(prim_items(a)),
{
    reveal(prim_items);
    reveal_with_fuel(to_prim, 2);
    match to_prim(r::Json8259::Array(a)) {
        p::JsonValue::Array(sq) => {
            assert(sq =~= prim_items(a));
        },
        _ => {
            assert(false);
        },
    }
}

proof fn lemma_to_prim_object(ms: Seq<r::Member8259>)
    ensures
        to_prim(r::Json8259::Object(ms)) == p::JsonValue::Object(prim_members(ms)),
{
    reveal(prim_members);
    reveal_with_fuel(to_prim, 2);
    match to_prim(r::Json8259::Object(ms)) {
        p::JsonValue::Object(sq) => {
            assert(sq =~= prim_members(ms));
        },
        _ => {
            assert(false);
        },
    }
}

proof fn lemma_utf16_of_empty()
    ensures
        utf16_of(Seq::<u32>::empty()) == Seq::<u16>::empty(),
{
}

proof fn lemma_utf16_of_push(v: Seq<u32>, c: u32)
    ensures
        utf16_of(v.push(c)) == utf16_of(v) + p::utf16_encode_code_point(c),
{
    assert(v.push(c).drop_last() == v);
    assert(v.push(c).last() == c);
}

/// RFC 8259 §3 and §7: the code units a surrogate pair of `\u` escapes
/// makes, in either reading.
proof fn lemma_pair_units(hi: nat, lo: nat)
    requires
        r::is_high(hi),
        r::is_low(lo),
    ensures
        r::pair_code_point(hi, lo) <= 0x10FFFF,
        r::pair_code_point(hi, lo) > 0xFFFF,
        p::utf16_encode_code_point(r::pair_code_point(hi, lo) as u32) == seq![hi as u16, lo as u16],
{
    let cp = r::pair_code_point(hi, lo);
    assert(cp == 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00));
    assert((cp - 0x10000) / 0x400 == hi - 0xD800) by (nonlinear_arith)
        requires
            cp == 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00),
            0xDC00 <= lo <= 0xDFFF,
    ;
    assert((cp - 0x10000) % 0x400 == lo - 0xDC00) by (nonlinear_arith)
        requires
            cp == 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00),
            0xDC00 <= lo <= 0xDFFF,
    ;
    assert(p::utf16_encode_code_point(cp as u32) =~= seq![hi as u16, lo as u16]);
}

/// The nesting bound is the same number in both.
pub proof fn lemma_same_nesting_limit()
    ensures
        r::nesting_limit() == p::max_depth(),
{
}

// ---------------------------------------------------------------------
// ws, digits, numbers.
// ---------------------------------------------------------------------

/// `c` is not a `ws` code point at `q` (including when `q` is past the end).
pub open spec fn not_ws_at(s: Seq<u32>, q: nat) -> bool {
    !(r::char_at(s, q, 0x20) || r::char_at(s, q, 0x09) || r::char_at(s, q, 0x0A) || r::char_at(s, q, 0x0D))
}

proof fn lemma_ws_stop(s: Seq<u32>, pos: nat)
    ensures
        r::ws(s, pos) >= pos,
        not_ws_at(s, r::ws(s, pos)),
    decreases s.len() - pos,
{
    reveal_with_fuel(r::ws, 1);
    if !not_ws_at(s, pos) {
        lemma_ws_stop(s, pos + 1);
    }
}

proof fn lemma_ws_fixed(s: Seq<u32>, q: nat)
    requires
        not_ws_at(s, q),
    ensures
        r::ws(s, q) == q,
{
    reveal_with_fuel(r::ws, 1);
}

proof fn lemma_ws_idem(s: Seq<u32>, pos: nat)
    ensures
        r::ws(s, r::ws(s, pos)) == r::ws(s, pos),
{
    lemma_ws_stop(s, pos);
    lemma_ws_fixed(s, r::ws(s, pos));
}

/// The two `ws` productions are the same function.
proof fn lemma_ws_eq(s: Seq<u32>, pos: nat)
    ensures
        r::ws(s, pos) == p::skip_ws(s, pos),
    decreases s.len() - pos,
{
    reveal_with_fuel(r::ws, 1);
    reveal_with_fuel(p::skip_ws, 1);
    if !not_ws_at(s, pos) {
        lemma_ws_eq(s, pos + 1);
    }
}

/// A structural token at a position that is not `ws` consumes the `ws` after it.
proof fn lemma_structural(s: Seq<u32>, pos: nat, c: u32)
    requires
        c != 0x20 && c != 0x09 && c != 0x0A && c != 0x0D,
    ensures
        r::structural(s, pos, c) is Some <==> r::char_at(s, r::ws(s, pos), c),
        r::structural(s, pos, c) is Some ==> r::structural(s, pos, c)->Some_0 == r::ws(s, r::ws(s, pos) + 1),
        r::structural(s, pos, c) is Some ==> r::structural(s, pos, c)->Some_0 > pos,
        r::structural(s, pos, c) is Some ==> not_ws_at(s, r::structural(s, pos, c)->Some_0),
{
    lemma_ws_stop(s, pos);
    if r::char_at(s, r::ws(s, pos), c) {
        lemma_ws_stop(s, r::ws(s, pos) + 1);
    }
}

proof fn lemma_digits_eq(s: Seq<u32>, pos: nat)
    ensures
        r::digits(s, pos) == p::skip_digits(s, pos),
        r::digits(s, pos) >= pos,
    decreases s.len() - pos,
{
    reveal_with_fuel(r::digits, 1);
    reveal_with_fuel(p::skip_digits, 1);
    if pos < s.len() && r::digit(s[pos as int]) {
        lemma_digits_eq(s, pos + 1);
    }
}

/// `number` is the same production in both, at every position.
proof fn lemma_number_eq(s: Seq<u32>, pos: nat)
    ensures
        r::number(s, pos) == p::parse_number(s, pos),
        r::number(s, pos) is Some ==> r::number(s, pos)->Some_0 > pos,
{
    assert forall|x: nat| r::digits(s, x) == p::skip_digits(s, x) && r::digits(s, x) >= x by {
        lemma_digits_eq(s, x);
    }
}

/// `4HEXDIG` is `hex hex hex hex`.
proof fn lemma_hex_eq(s: Seq<u32>, pos: nat)
    ensures
        r::four_hexdig(s, pos) == p::hex4(s, pos),
{
    assert forall|c: u32| r::hexdig(c) == p::hex_value(c) by {}
}

// ---------------------------------------------------------------------
// Strings.
// ---------------------------------------------------------------------

proof fn lemma_escape_eq(c: u32)
    ensures
        r::simple_escape(c) is Some <==> p::escape_unit(c) is Some,
        r::simple_escape(c) is Some ==> r::simple_escape(c)->Some_0 == p::escape_unit(c)->Some_0 as u32,
        r::simple_escape(c) is Some ==> r::simple_escape(c)->Some_0 <= 0xFFFF,
{
}

/// `*char` and the primary's `characters` agree, given the same string so
/// far (as code points and as code units).
proof fn lemma_chars_equiv(s: Seq<u32>, pos: nat, acc: Seq<u32>)
    ensures
        p::parse_characters(s, pos, utf16_of(acc)) == match r::chars(s, pos, acc) {
            Some((u, q)) => if r::char_at(s, q, 0x22) {
                Some((utf16_of(u), q + 1))
            } else {
                None
            },
            None => None,
        },
        r::chars(s, pos, acc) is Some ==> r::chars(s, pos, acc)->Some_0.1 >= pos,
    decreases s.len() - pos,
{
    reveal_with_fuel(r::chars, 1);
    reveal_with_fuel(p::parse_characters, 1);
    if pos >= s.len() {
    } else {
        let c = s[pos as int];
        if c == 0x22 {
        } else if c == 0x5C {
            if pos + 1 >= s.len() {
            } else {
                let e = s[pos as int + 1];
                lemma_hex_eq(s, pos + 2);
                if e == 0x75 {
                    match r::four_hexdig(s, pos + 2) {
                        None => {},
                        Some(n) => {
                            assert(n <= 0xFFFF);
                            let rest = r::u_escape(s, pos + 6);
                            if r::is_high(n) && rest is Some && r::is_low(rest->Some_0) {
                                let m = rest->Some_0;
                                lemma_pair_units(n, m);
                                lemma_utf16_of_push(acc, r::pair_code_point(n, m) as u32);
                                // The primary reads the pair as two `\u` escapes.
                                lemma_hex_eq(s, pos + 8);
                                reveal_with_fuel(p::parse_characters, 2);
                                assert(utf16_of(acc).push(n as u16).push(m as u16) =~= utf16_of(
                                    acc.push(r::pair_code_point(n, m) as u32),
                                ));
                                lemma_chars_equiv(s, pos + 12, acc.push(r::pair_code_point(n, m) as u32));
                            } else {
                                lemma_utf16_of_push(acc, n as u32);
                                assert(utf16_of(acc).push(n as u16) =~= utf16_of(acc.push(n as u32)));
                                lemma_chars_equiv(s, pos + 6, acc.push(n as u32));
                            }
                        },
                    }
                } else {
                    lemma_escape_eq(e);
                    if r::simple_escape(e) is Some {
                        let u = r::simple_escape(e)->Some_0;
                        lemma_utf16_of_push(acc, u);
                        assert(utf16_of(acc).push(u as u16) =~= utf16_of(acc.push(u)));
                        lemma_chars_equiv(s, pos + 2, acc.push(u));
                    }
                }
            }
        } else if c < 0x20 {
        } else if c > 0x10FFFF {
        } else {
            lemma_utf16_of_push(acc, c);
            lemma_chars_equiv(s, pos + 1, acc.push(c));
        }
    }
}

/// `string` is the same production in both; the value differs only by
/// `utf16_of`, and the end is the same.
proof fn lemma_string_equiv(s: Seq<u32>, pos: nat)
    ensures
        p::parse_string(s, pos) == match r::string(s, pos) {
            Some((u, q)) => Some((utf16_of(u), q)),
            None => None,
        },
        r::string(s, pos) is Some ==> r::string(s, pos)->Some_0.1 > pos,
{
    if r::char_at(s, pos, 0x22) {
        lemma_chars_equiv(s, pos + 1, Seq::empty());
    }
}

// ---------------------------------------------------------------------
// Values: the relation, and what the independent parser's results satisfy.
// ---------------------------------------------------------------------

/// The independent transcription's result and the primary's agree: both
/// fail, or both succeed with a value related by `to_prim` and positions
/// that agree after skipping `ws` (the independent `end-array` and
/// `end-object` consume the `ws` after them).
pub open spec fn rel_value(a: Option<(r::Json8259, nat)>, b: Option<(p::JsonValue, nat)>, s: Seq<u32>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some((v, x)), Some((w, y))) => to_prim(v) == w && r::ws(s, x) == p::skip_ws(s, y),
        _ => false,
    }
}

/// An array result as a value result.
pub open spec fn wrap_arr(o: Option<(Seq<r::Json8259>, nat)>) -> Option<(r::Json8259, nat)> {
    match o {
        Some((a, x)) => Some((r::Json8259::Array(a), x)),
        None => None,
    }
}

/// An object result as a value result.
pub open spec fn wrap_obj(o: Option<(Seq<r::Member8259>, nat)>) -> Option<(r::Json8259, nat)> {
    match o {
        Some((m, x)) => Some((r::Json8259::Object(m), x)),
        None => None,
    }
}

/// The independent transcription's reading of the elements from the one
/// at `pv` on, after the elements `done`.
pub open spec fn elements_mine(s: Seq<u32>, pv: nat, e: nat, done: Seq<r::Json8259>) -> Option<(Seq<r::Json8259>, nat)> {
    match r::value(s, pv, e) {
        Some((v, p2)) => r::array_rest(s, p2, e, done.push(v)),
        None => None,
    }
}

/// The same for members.
pub open spec fn members_mine(s: Seq<u32>, pv: nat, e: nat, done: Seq<r::Member8259>) -> Option<(Seq<r::Member8259>, nat)> {
    match r::member(s, pv, e) {
        Some((m, p3)) => r::object_rest(s, p3, e, done.push(m)),
        None => None,
    }
}

/// A code point that can begin a `value`.
pub open spec fn starts_value(c: u32) -> bool {
    c == 0x66 || c == 0x6E || c == 0x74 || c == 0x7B || c == 0x5B || c == 0x22 || c == 0x2D || (0x30 <= c <= 0x39)
}

proof fn lemma_prim_items_len(a: Seq<r::Json8259>)
    ensures
        prim_items(a).len() == a.len(),
{
    reveal(prim_items);
}

proof fn lemma_prim_members_len(a: Seq<r::Member8259>)
    ensures
        prim_members(a).len() == a.len(),
{
    reveal(prim_members);
}

proof fn lemma_literals_same()
    ensures
        r::true_lit() == p::lit_true(),
        r::false_lit() == p::lit_false(),
        r::null_lit() == p::lit_null(),
{
    assert(r::true_lit() =~= p::lit_true());
    assert(r::false_lit() =~= p::lit_false());
    assert(r::null_lit() =~= p::lit_null());
}

/// A literal at `pos` starts with its first code point.
proof fn lemma_literal_heads(s: Seq<u32>, pos: nat)
    ensures
        r::literal_at(s, pos, r::false_lit()) ==> r::char_at(s, pos, 0x66),
        r::literal_at(s, pos, r::null_lit()) ==> r::char_at(s, pos, 0x6E),
        r::literal_at(s, pos, r::true_lit()) ==> r::char_at(s, pos, 0x74),
{
    if r::literal_at(s, pos, r::false_lit()) {
        assert(s.subrange(pos as int, (pos + 5) as int)[0] == s[pos as int]);
    }
    if r::literal_at(s, pos, r::null_lit()) {
        assert(s.subrange(pos as int, (pos + 4) as int)[0] == s[pos as int]);
    }
    if r::literal_at(s, pos, r::true_lit()) {
        assert(s.subrange(pos as int, (pos + 4) as int)[0] == s[pos as int]);
    }
}

proof fn lemma_object_none(s: Seq<u32>, pos: nat, d: nat)
    requires
        not_ws_at(s, pos),
        !r::char_at(s, pos, 0x7B),
    ensures
        r::object(s, pos, d) is None,
{
    reveal_with_fuel(r::object, 1);
    lemma_ws_fixed(s, pos);
}

proof fn lemma_array_none(s: Seq<u32>, pos: nat, d: nat)
    requires
        not_ws_at(s, pos),
        !r::char_at(s, pos, 0x5B),
    ensures
        r::array(s, pos, d) is None,
{
    reveal_with_fuel(r::array, 1);
    lemma_ws_fixed(s, pos);
}

proof fn lemma_number_none(s: Seq<u32>, pos: nat)
    requires
        !r::char_at(s, pos, 0x2D),
        !(pos < s.len() && r::digit(s[pos as int])),
    ensures
        r::number(s, pos) is None,
{
}

proof fn lemma_string_none(s: Seq<u32>, pos: nat)
    requires
        !r::char_at(s, pos, 0x22),
    ensures
        r::string(s, pos) is None,
{
}

/// No alternative of `value` matches where no `value` can begin.
proof fn lemma_value_none(s: Seq<u32>, pos: nat, d: nat)
    requires
        not_ws_at(s, pos),
        pos >= s.len() || !starts_value(s[pos as int]),
    ensures
        r::value(s, pos, d) is None,
{
    reveal_with_fuel(r::value, 1);
    lemma_literal_heads(s, pos);
    lemma_object_none(s, pos, d);
    lemma_array_none(s, pos, d);
    lemma_number_none(s, pos);
    lemma_string_none(s, pos);
}

// ---------------------------------------------------------------------
// Progress: a value, member or list consumes at least one code point.
// ---------------------------------------------------------------------

proof fn lemma_value_progress(s: Seq<u32>, pos: nat, d: nat)
    ensures
        r::value(s, pos, d) is Some ==> r::value(s, pos, d)->Some_0.1 > pos,
    decreases d, 2int,
{
    reveal_with_fuel(r::value, 1);
    lemma_object_progress(s, pos, d);
    lemma_array_progress(s, pos, d);
    lemma_number_eq(s, pos);
    lemma_string_equiv(s, pos);
}

proof fn lemma_object_progress(s: Seq<u32>, pos: nat, d: nat)
    ensures
        r::object(s, pos, d) is Some ==> r::object(s, pos, d)->Some_0.1 > pos,
    decreases d, 1int,
{
    reveal_with_fuel(r::object, 1);
    if d > 0 {
        lemma_structural(s, pos, 0x7B);
        if let Some(p1) = r::begin_object(s, pos) {
            lemma_structural(s, p1, 0x7D);
            if let Some((m, p2)) = r::member(s, p1, (d - 1) as nat) {
                lemma_member_progress(s, p1, (d - 1) as nat);
                lemma_object_rest_ge(s, p2, (d - 1) as nat, seq![m]);
            }
        }
    }
}

proof fn lemma_array_progress(s: Seq<u32>, pos: nat, d: nat)
    ensures
        r::array(s, pos, d) is Some ==> r::array(s, pos, d)->Some_0.1 > pos,
    decreases d, 1int,
{
    reveal_with_fuel(r::array, 1);
    if d > 0 {
        lemma_structural(s, pos, 0x5B);
        if let Some(p1) = r::begin_array(s, pos) {
            lemma_structural(s, p1, 0x5D);
            if let Some((v, p2)) = r::value(s, p1, (d - 1) as nat) {
                lemma_value_progress(s, p1, (d - 1) as nat);
                lemma_array_rest_ge(s, p2, (d - 1) as nat, seq![v]);
            }
        }
    }
}

proof fn lemma_member_progress(s: Seq<u32>, pos: nat, e: nat)
    ensures
        r::member(s, pos, e) is Some ==> r::member(s, pos, e)->Some_0.1 > pos,
    decreases e, 3int,
{
    lemma_string_equiv(s, pos);
    if let Some((n, p1)) = r::string(s, pos) {
        lemma_structural(s, p1, 0x3A);
        if let Some(p2) = r::name_separator(s, p1) {
            lemma_value_progress(s, p2, e);
        }
    }
}

proof fn lemma_array_rest_ge(s: Seq<u32>, pos: nat, e: nat, done: Seq<r::Json8259>)
    ensures
        r::array_rest(s, pos, e, done) is Some ==> r::array_rest(s, pos, e, done)->Some_0.1 >= pos,
    decreases e, 4int, s.len() - done.len(),
{
    reveal_with_fuel(r::array_rest, 1);
    if done.len() < s.len() {
        lemma_structural(s, pos, 0x2C);
        lemma_structural(s, pos, 0x5D);
        if let Some(p1) = r::value_separator(s, pos) {
            lemma_value_progress(s, p1, e);
            if let Some((v, p2)) = r::value(s, p1, e) {
                lemma_array_rest_ge(s, p2, e, done.push(v));
            }
        }
    }
}

proof fn lemma_object_rest_ge(s: Seq<u32>, pos: nat, e: nat, done: Seq<r::Member8259>)
    ensures
        r::object_rest(s, pos, e, done) is Some ==> r::object_rest(s, pos, e, done)->Some_0.1 >= pos,
    decreases e, 4int, s.len() - done.len(),
{
    reveal_with_fuel(r::object_rest, 1);
    if done.len() < s.len() {
        lemma_structural(s, pos, 0x2C);
        lemma_structural(s, pos, 0x7D);
        if let Some(p1) = r::value_separator(s, pos) {
            lemma_member_progress(s, p1, e);
            if let Some((m, p2)) = r::member(s, p1, e) {
                lemma_object_rest_ge(s, p2, e, done.push(m));
            }
        }
    }
}

// ---------------------------------------------------------------------
// Values: equivalence.
// ---------------------------------------------------------------------

/// `value` is the same production in both at every position that is not
/// `ws`: the same failures, the same values up to `to_prim`, the same ends
/// up to `ws`.
pub proof fn lemma_value_equiv(s: Seq<u32>, pos: nat, d: nat)
    requires
        not_ws_at(s, pos),
    ensures
        rel_value(r::value(s, pos, d), p::parse_value(s, pos, d), s),
    decreases d, 5int,
{
    reveal_with_fuel(r::value, 1);
    reveal_with_fuel(p::parse_value, 1);
    lemma_literal_heads(s, pos);
    lemma_literals_same();
    assert forall|x: nat| r::ws(s, x) == p::skip_ws(s, x) by {
        lemma_ws_eq(s, x);
    }
    if pos >= s.len() {
        lemma_value_none(s, pos, d);
    } else {
        let c = s[pos as int];
        if c == 0x7B {
            lemma_object_equiv(s, pos, d);
            lemma_array_none(s, pos, d);
            lemma_number_none(s, pos);
            lemma_string_none(s, pos);
        } else if c == 0x5B {
            lemma_array_equiv(s, pos, d);
            lemma_object_none(s, pos, d);
            lemma_number_none(s, pos);
            lemma_string_none(s, pos);
        } else if c == 0x22 {
            lemma_string_equiv(s, pos);
            lemma_object_none(s, pos, d);
            lemma_array_none(s, pos, d);
            lemma_number_none(s, pos);
        } else if c == 0x2D || p::is_digit(c) {
            lemma_number_eq(s, pos);
            lemma_object_none(s, pos, d);
            lemma_array_none(s, pos, d);
            lemma_string_none(s, pos);
        } else {
            lemma_object_none(s, pos, d);
            lemma_array_none(s, pos, d);
            lemma_number_none(s, pos);
            lemma_string_none(s, pos);
        }
    }
}

/// `array` against `parse_array`.
pub proof fn lemma_array_equiv(s: Seq<u32>, pos: nat, d: nat)
    requires
        r::char_at(s, pos, 0x5B),
    ensures
        rel_value(wrap_arr(r::array(s, pos, d)), p::parse_array(s, pos, d), s),
    decreases d, 4int,
{
    reveal_with_fuel(r::array, 1);
    reveal_with_fuel(p::parse_array, 1);
    assert forall|x: nat| r::ws(s, x) == p::skip_ws(s, x) by {
        lemma_ws_eq(s, x);
    }
    if d > 0 {
        lemma_ws_fixed(s, pos);
        lemma_structural(s, pos, 0x5B);
        let p1 = r::ws(s, pos + 1);
        lemma_ws_stop(s, pos + 1);
        lemma_ws_idem(s, pos + 1);
        let e = (d - 1) as nat;
        if p::is_at(s, p1, 0x5D) {
            lemma_value_none(s, p1, e);
            lemma_structural(s, p1, 0x5D);
            lemma_ws_fixed(s, p1);
            lemma_ws_idem(s, p1 + 1);
            lemma_to_prim_array(Seq::empty());
            lemma_prim_items_empty();
        } else {
            lemma_structural(s, p1, 0x5D);
            lemma_ws_fixed(s, p1);
            lemma_elements_equiv(s, p1, e, Seq::empty());
            lemma_prim_items_empty();
            if let Some((v, p2)) = r::value(s, p1, e) {
                assert(seq![v] =~= Seq::<r::Json8259>::empty().push(v));
            }
        }
    }
}

/// The elements of an array, one `value-separator value` at a time.
pub proof fn lemma_elements_equiv(s: Seq<u32>, pv: nat, e: nat, done: Seq<r::Json8259>)
    requires
        not_ws_at(s, pv),
        done.len() <= pv,
    ensures
        rel_value(wrap_arr(elements_mine(s, pv, e, done)), p::parse_elements(s, pv, e, prim_items(done)), s),
    decreases e + 1, 3int, s.len() - done.len(),
{
    reveal_with_fuel(p::parse_elements, 1);
    lemma_prim_items_len(done);
    assert forall|x: nat| r::ws(s, x) == p::skip_ws(s, x) by {
        lemma_ws_eq(s, x);
    }
    if done.len() >= s.len() {
        lemma_value_none(s, pv, e);
    } else {
        lemma_value_equiv(s, pv, e);
        if let Some((v, p2)) = r::value(s, pv, e) {
            lemma_value_progress(s, pv, e);
            lemma_ws_stop(s, p2);
            lemma_ws_idem(s, p2);
            let wp = r::ws(s, p2);
            lemma_prim_items_push(done, v);
            reveal_with_fuel(r::array_rest, 1);
            lemma_structural(s, p2, 0x2C);
            lemma_structural(s, p2, 0x5D);
            if p::is_at(s, wp, 0x2C) {
                let p1 = r::ws(s, wp + 1);
                lemma_ws_stop(s, wp + 1);
                if let Some((v2, p3)) = r::value(s, p1, e) {
                    lemma_value_progress(s, p1, e);
                }
                lemma_elements_equiv(s, p1, e, done.push(v));
            } else if p::is_at(s, wp, 0x5D) {
                lemma_ws_idem(s, wp + 1);
                lemma_to_prim_array(done.push(v));
                lemma_prim_items_push(done, v);
            }
        }
    }
}

/// `object` against `parse_object`.
pub proof fn lemma_object_equiv(s: Seq<u32>, pos: nat, d: nat)
    requires
        r::char_at(s, pos, 0x7B),
    ensures
        rel_value(wrap_obj(r::object(s, pos, d)), p::parse_object(s, pos, d), s),
    decreases d, 4int,
{
    reveal_with_fuel(r::object, 1);
    reveal_with_fuel(p::parse_object, 1);
    assert forall|x: nat| r::ws(s, x) == p::skip_ws(s, x) by {
        lemma_ws_eq(s, x);
    }
    if d > 0 {
        lemma_ws_fixed(s, pos);
        lemma_structural(s, pos, 0x7B);
        let p1 = r::ws(s, pos + 1);
        lemma_ws_stop(s, pos + 1);
        lemma_ws_idem(s, pos + 1);
        let e = (d - 1) as nat;
        if p::is_at(s, p1, 0x7D) {
            reveal_with_fuel(r::member, 1);
            lemma_string_none(s, p1);
            lemma_structural(s, p1, 0x7D);
            lemma_ws_fixed(s, p1);
            lemma_ws_idem(s, p1 + 1);
            lemma_to_prim_object(Seq::empty());
            lemma_prim_members_empty();
        } else {
            reveal_with_fuel(r::member, 1);
            lemma_structural(s, p1, 0x7D);
            lemma_ws_fixed(s, p1);
            lemma_members_equiv(s, p1, e, Seq::empty());
            lemma_prim_members_empty();
            if let Some((m, p2)) = r::member(s, p1, e) {
                assert(seq![m] =~= Seq::<r::Member8259>::empty().push(m));
            }
        }
    }
}

/// The members of an object.
pub proof fn lemma_members_equiv(s: Seq<u32>, pv: nat, e: nat, done: Seq<r::Member8259>)
    requires
        done.len() <= pv,
    ensures
        rel_value(wrap_obj(members_mine(s, pv, e, done)), p::parse_members(s, pv, e, prim_members(done)), s),
    decreases e + 1, 3int, s.len() - done.len(),
{
    reveal_with_fuel(p::parse_members, 1);
    reveal_with_fuel(r::member, 1);
    lemma_prim_members_len(done);
    assert forall|x: nat| r::ws(s, x) == p::skip_ws(s, x) by {
        lemma_ws_eq(s, x);
    }
    lemma_string_equiv(s, pv);
    if done.len() >= s.len() {
        lemma_string_none(s, pv);
    } else {
        if let Some((n, p1)) = r::string(s, pv) {
            lemma_ws_stop(s, p1);
            lemma_structural(s, p1, 0x3A);
            if p::is_at(s, r::ws(s, p1), 0x3A) {
                let p2 = r::ws(s, r::ws(s, p1) + 1);
                lemma_ws_stop(s, r::ws(s, p1) + 1);
                lemma_value_equiv(s, p2, e);
                if let Some((v, p3)) = r::value(s, p2, e) {
                    lemma_value_progress(s, p2, e);
                    lemma_ws_stop(s, p3);
                    lemma_ws_idem(s, p3);
                    let wr = r::ws(s, p3);
                    let m = r::Member8259 { name: n, value: v };
                    lemma_prim_members_push(done, m);
                    reveal_with_fuel(r::object_rest, 1);
                    lemma_structural(s, p3, 0x2C);
                    lemma_structural(s, p3, 0x7D);
                    if p::is_at(s, wr, 0x2C) {
                        let p1b = r::ws(s, wr + 1);
                        lemma_ws_stop(s, wr + 1);
                        if let Some((m2, p4)) = r::member(s, p1b, e) {
                            lemma_member_progress(s, p1b, e);
                        }
                        lemma_members_equiv(s, p1b, e, done.push(m));
                    } else if p::is_at(s, wr, 0x7D) {
                        lemma_ws_idem(s, wr + 1);
                        lemma_to_prim_object(done.push(m));
                        lemma_prim_members_push(done, m);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------

/// **Equivalence.** For every text, the primary spec's `json_parse` is
/// RFC 8259's `JSON-text`, read through `to_prim`: it fails exactly when
/// `json_text` fails, and otherwise constructs the value `json_text` does,
/// with strings as UTF-16 code units rather than code points.
pub proof fn theorem_json_text_equivalent(text: Seq<u32>)
    ensures
        p::json_parse(text) == prim_of(r::json_text(text)),
{
    lemma_ws_stop(text, 0);
    lemma_ws_eq(text, 0);
    lemma_value_equiv(text, r::ws(text, 0), r::nesting_limit());
    lemma_same_nesting_limit();
    if let Some((v, x)) = r::value(text, r::ws(text, 0), r::nesting_limit()) {
        lemma_ws_eq(text, x);
        if let Some((w, y)) = p::parse_value(text, p::skip_ws(text, 0), p::max_depth()) {
            lemma_ws_eq(text, y);
        }
    }
}

/// The relation is not an identity on strings, and that is all it does:
/// the one code point U+1D11E and the two lone surrogate code points
/// U+D834 U+DD1E are different RFC 8259 strings with the same code units
/// (`"𝄞"` is the first, and a `\uD834` escape followed by a
/// literal U+DD1E is the second).
pub proof fn lemma_to_prim_not_injective()
    ensures
        r::Json8259::String(seq![0x1D11Eu32]) != r::Json8259::String(seq![0xD834u32, 0xDD1E]),
        to_prim(r::Json8259::String(seq![0x1D11Eu32])) == to_prim(r::Json8259::String(seq![0xD834u32, 0xDD1E])),
{
    let a = seq![0x1D11Eu32];
    let b = seq![0xD834u32, 0xDD1E];
    assert(a.len() != b.len());
    lemma_utf16_of_push(Seq::empty(), 0x1D11E);
    assert(a =~= Seq::<u32>::empty().push(0x1D11E));
    lemma_utf16_of_push(Seq::empty(), 0xD834);
    assert(b.drop_last() =~= Seq::<u32>::empty().push(0xD834));
    lemma_utf16_of_push(Seq::<u32>::empty().push(0xD834), 0xDD1E);
    assert(b =~= Seq::<u32>::empty().push(0xD834).push(0xDD1E));
    assert(utf16_of(a) =~= utf16_of(b));
}

} // verus!

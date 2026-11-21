//! The executable parser, proven to meet [`super::contract`].
//!
//! The code has the shape of the spec's productions in [`super::spec`]: a
//! function per production, the same order of tests, and the same
//! accumulators. Recursion goes only through nested arrays and objects
//! (at most `max_depth()` deep); the loop over the elements of an array or
//! the members of an object is a loop.

#[allow(unused_imports)]
use super::spec::*;
use super::tree::{Json, Member};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// What a position result means in the spec's terms.
pub open spec fn opt_pos(r: Option<usize>) -> Option<nat> {
    match r {
        Some(p) => Some(p as nat),
        None => None,
    }
}

/// What a string result means in the spec's terms.
pub open spec fn str_res(r: Option<(Vec<u16>, usize)>) -> Option<(Seq<u16>, nat)> {
    match r {
        Some((u, p)) => Some((u@, p as nat)),
        None => None,
    }
}

/// What a value result means in the spec's terms.
pub open spec fn val_res(r: Option<(Json, usize)>) -> Option<(JsonValue, nat)> {
    match r {
        Some((j, p)) => Some((j@, p as nat)),
        None => None,
    }
}

/// The meaning of a sequence of trees, as in the `Array` case of
/// [`Json::view`]. Opaque, so that the loops below do not unfold its
/// `Seq::new`; the lemmas that follow reveal it.
#[verifier::opaque]
pub open spec fn items_view(v: Seq<Json>) -> Seq<JsonValue> {
    Seq::new(v.len(), |i: int| if 0 <= i < v.len() { v[i].view() } else { JsonValue::Null })
}

/// The meaning of a sequence of members, as in the `Object` case of
/// [`Json::view`]. Opaque for the same reason.
#[verifier::opaque]
pub open spec fn members_view(v: Seq<Member>) -> Seq<JsonMember> {
    Seq::new(
        v.len(),
        |i: int|
            if 0 <= i < v.len() {
                JsonMember { key: v[i].key@, value: v[i].value.view() }
            } else {
                JsonMember { key: Seq::empty(), value: JsonValue::Null }
            },
    )
}

proof fn lemma_items_view_len(v: Seq<Json>)
    ensures
        items_view(v).len() == v.len(),
{
    reveal(items_view);
}

proof fn lemma_members_view_len(v: Seq<Member>)
    ensures
        members_view(v).len() == v.len(),
{
    reveal(members_view);
}

proof fn lemma_items_view_empty()
    ensures
        items_view(Seq::<Json>::empty()) == Seq::<JsonValue>::empty(),
{
    reveal(items_view);
    assert(items_view(Seq::<Json>::empty()) =~= Seq::<JsonValue>::empty());
}

proof fn lemma_members_view_empty()
    ensures
        members_view(Seq::<Member>::empty()) == Seq::<JsonMember>::empty(),
{
    reveal(members_view);
    assert(members_view(Seq::<Member>::empty()) =~= Seq::<JsonMember>::empty());
}

proof fn lemma_items_view_push(v: Seq<Json>, x: Json)
    ensures
        items_view(v.push(x)) == items_view(v).push(x.view()),
{
    reveal(items_view);
    assert(items_view(v.push(x)) =~= items_view(v).push(x.view()));
}

proof fn lemma_members_view_push(v: Seq<Member>, x: Member)
    ensures
        members_view(v.push(x)) == members_view(v).push(JsonMember { key: x.key@, value: x.value.view() }),
{
    reveal(members_view);
    assert(members_view(v.push(x)) =~= members_view(v).push(JsonMember { key: x.key@, value: x.value.view() }));
}

proof fn lemma_array_view(items: Vec<Json>)
    ensures
        Json::Array(items).view() == JsonValue::Array(items_view(items@)),
{
    reveal(items_view);
    reveal_with_fuel(<Json as View>::view, 2);
    match Json::Array(items).view() {
        JsonValue::Array(sq) => {
            assert(sq =~= items_view(items@));
        },
        _ => {
            assert(false);
        },
    }
}

proof fn lemma_object_view(members: Vec<Member>)
    ensures
        Json::Object(members).view() == JsonValue::Object(members_view(members@)),
{
    reveal(members_view);
    reveal_with_fuel(<Json as View>::view, 2);
    match Json::Object(members).view() {
        JsonValue::Object(sq) => {
            assert(sq =~= members_view(members@));
        },
        _ => {
            assert(false);
        },
    }
}

// ---------------------------------------------------------------------
// Code points.
// ---------------------------------------------------------------------

/// ECMA-404 `ws`.
fn is_ws(c: u32) -> (r: bool)
    ensures
        r == super::spec::is_ws(c),
{
    c == 0x09 || c == 0x0A || c == 0x0D || c == 0x20
}

/// ECMA-404 `digit`.
fn is_digit(c: u32) -> (r: bool)
    ensures
        r == super::spec::is_digit(c),
{
    (0x30..=0x39).contains(&c)
}

/// ECMA-404 `onenine`.
fn is_onenine(c: u32) -> (r: bool)
    ensures
        r == super::spec::is_onenine(c),
{
    (0x31..=0x39).contains(&c)
}

/// ECMA-404 `hex`.
fn hex_value(c: u32) -> (r: Option<u32>)
    ensures
        match r {
            Some(n) => super::spec::hex_value(c) == Some(n as nat) && n < 16,
            None => super::spec::hex_value(c) is None,
        },
{
    if (0x30..=0x39).contains(&c) {
        // Never saturates: c >= 0x30.
        Some(c.saturating_sub(0x30))
    } else if (0x41..=0x46).contains(&c) {
        Some(c.saturating_sub(0x41).saturating_add(10))
    } else if (0x61..=0x66).contains(&c) {
        Some(c.saturating_sub(0x61).saturating_add(10))
    } else {
        None
    }
}

/// The code point at `pos` is `c`.
fn at(input: &[u32], pos: usize, c: u32) -> (r: bool)
    ensures
        r == is_at(input@, pos as nat, c),
        r ==> pos < input.len(),
{
    match input.get(pos) {
        Some(&x) => x == c,
        None => false,
    }
}

// ---------------------------------------------------------------------
// ws and digits.
// ---------------------------------------------------------------------

/// The position after the longest run of `ws` from `pos`.
fn skip_ws(input: &[u32], pos: usize) -> (r: usize)
    requires
        pos <= input.len(),
    ensures
        pos <= r <= input.len(),
        r as nat == super::spec::skip_ws(input@, pos as nat),
{
    let mut p = pos;
    loop
        invariant
            pos <= p <= input.len(),
            super::spec::skip_ws(input@, pos as nat) == super::spec::skip_ws(input@, p as nat),
        ensures
            pos <= p <= input.len(),
            super::spec::skip_ws(input@, pos as nat) == p as nat,
        decreases input.len() - p,
    {
        match input.get(p) {
            Some(&c) if is_ws(c) => {
                // Never saturates: p < input.len().
                p = p.saturating_add(1);
            },
            _ => {
                break ;
            },
        }
    }
    p
}

/// The position after the longest run of digits from `pos`.
fn skip_digits(input: &[u32], pos: usize) -> (r: usize)
    requires
        pos <= input.len(),
    ensures
        pos <= r <= input.len(),
        r as nat == super::spec::skip_digits(input@, pos as nat),
{
    let mut p = pos;
    loop
        invariant
            pos <= p <= input.len(),
            super::spec::skip_digits(input@, pos as nat) == super::spec::skip_digits(input@, p as nat),
        ensures
            pos <= p <= input.len(),
            super::spec::skip_digits(input@, pos as nat) == p as nat,
        decreases input.len() - p,
    {
        match input.get(p) {
            Some(&c) if is_digit(c) => {
                // Never saturates: p < input.len().
                p = p.saturating_add(1);
            },
            _ => {
                break ;
            },
        }
    }
    p
}

// ---------------------------------------------------------------------
// Numbers.
// ---------------------------------------------------------------------

/// ECMA-404 `integer`.
fn parse_integer(input: &[u32], pos: usize) -> (r: Option<usize>)
    requires
        pos <= input.len(),
    ensures
        opt_pos(r) == super::spec::parse_integer(input@, pos as nat),
        r matches Some(p) ==> pos <= p <= input.len(),
{
    let p = if at(input, pos, 0x2D) {
        pos.saturating_add(1)
    } else {
        pos
    };
    if at(input, p, 0x30) {
        Some(p.saturating_add(1))
    } else {
        match input.get(p) {
            Some(&c) => {
                if is_onenine(c) {
                    Some(skip_digits(input, p.saturating_add(1)))
                } else {
                    None
                }
            },
            None => None,
        }
    }
}

/// ECMA-404 `fraction`.
fn parse_fraction(input: &[u32], pos: usize) -> (r: Option<usize>)
    requires
        pos <= input.len(),
    ensures
        opt_pos(r) == super::spec::parse_fraction(input@, pos as nat),
        r matches Some(p) ==> pos <= p <= input.len(),
{
    if at(input, pos, 0x2E) {
        let start = pos.saturating_add(1);
        let q = skip_digits(input, start);
        if q > start {
            Some(q)
        } else {
            None
        }
    } else {
        Some(pos)
    }
}

/// ECMA-404 `exponent`.
fn parse_exponent(input: &[u32], pos: usize) -> (r: Option<usize>)
    requires
        pos <= input.len(),
    ensures
        opt_pos(r) == super::spec::parse_exponent(input@, pos as nat),
        r matches Some(p) ==> pos <= p <= input.len(),
{
    if at(input, pos, 0x45) || at(input, pos, 0x65) {
        let after_e = pos.saturating_add(1);
        let p = if at(input, after_e, 0x2B) || at(input, after_e, 0x2D) {
            after_e.saturating_add(1)
        } else {
            after_e
        };
        let q = skip_digits(input, p);
        if q > p {
            Some(q)
        } else {
            None
        }
    } else {
        Some(pos)
    }
}

/// ECMA-404 `number`.
fn parse_number(input: &[u32], pos: usize) -> (r: Option<usize>)
    requires
        pos <= input.len(),
    ensures
        opt_pos(r) == super::spec::parse_number(input@, pos as nat),
        r matches Some(p) ==> pos <= p <= input.len(),
{
    match parse_integer(input, pos) {
        None => None,
        Some(p1) => match parse_fraction(input, p1) {
            None => None,
            Some(p2) => parse_exponent(input, p2),
        },
    }
}

// ---------------------------------------------------------------------
// Strings.
// ---------------------------------------------------------------------

/// The code unit a one-character escape stands for.
fn escape_unit(e: u32) -> (r: Option<u16>)
    ensures
        r == super::spec::escape_unit(e),
{
    if e == 0x22 {
        Some(0x22)
    } else if e == 0x5C {
        Some(0x5C)
    } else if e == 0x2F {
        Some(0x2F)
    } else if e == 0x62 {
        Some(0x08)
    } else if e == 0x66 {
        Some(0x0C)
    } else if e == 0x6E {
        Some(0x0A)
    } else if e == 0x72 {
        Some(0x0D)
    } else if e == 0x74 {
        Some(0x09)
    } else {
        None
    }
}

/// The value of the four hex digits at `pos`.
fn hex4(input: &[u32], pos: usize) -> (r: Option<u32>)
    requires
        pos <= input.len(),
    ensures
        match r {
            Some(n) => super::spec::hex4(input@, pos as nat) == Some(n as nat) && n <= 0xFFFF && pos + 4 <= input.len(),
            None => super::spec::hex4(input@, pos as nat) is None,
        },
{
    if input.len().saturating_sub(pos) < 4 {
        return None;
    }
    // pos + 4 <= input.len(), so none of the indices below saturates.
    let a = match input.get(pos) {
        Some(&c) => hex_value(c),
        None => None,
    };
    let b = match input.get(pos.saturating_add(1)) {
        Some(&c) => hex_value(c),
        None => None,
    };
    let c = match input.get(pos.saturating_add(2)) {
        Some(&c) => hex_value(c),
        None => None,
    };
    let d = match input.get(pos.saturating_add(3)) {
        Some(&c) => hex_value(c),
        None => None,
    };
    match (a, b, c, d) {
        (Some(a), Some(b), Some(c), Some(d)) => Some(
            a.saturating_mul(4096).saturating_add(b.saturating_mul(256)).saturating_add(c.saturating_mul(16)).saturating_add(d),
        ),
        _ => None,
    }
}

/// ECMA-404 `string`: `pos` is the position of the opening quotation mark.
fn parse_string(input: &[u32], pos: usize) -> (r: Option<(Vec<u16>, usize)>)
    requires
        pos <= input.len(),
    ensures
        str_res(r) == super::spec::parse_string(input@, pos as nat),
        r matches Some((_, p)) ==> p <= input.len(),
{
    if !at(input, pos, 0x22) {
        return None;
    }
    let mut acc: Vec<u16> = Vec::new();
    // Never saturates: pos < input.len().
    let mut p = pos.saturating_add(1);
    loop
        invariant
            p <= input.len(),
            super::spec::parse_string(input@, pos as nat) == super::spec::parse_characters(
                input@,
                p as nat,
                acc@,
            ),
        decreases input.len() - p,
    {
        let c = match input.get(p) {
            Some(&c) => c,
            None => {
                return None;
            },
        };
        if c == 0x22 {
            // Never saturates: p < input.len().
            return Some((acc, p.saturating_add(1)));
        } else if c == 0x5C {
            let e = match input.get(p.saturating_add(1)) {
                Some(&e) => e,
                None => {
                    return None;
                },
            };
            if e == 0x75 {
                // p + 1 < input.len(), so p + 2 <= input.len().
                match hex4(input, p.saturating_add(2)) {
                    Some(n) => {
                        acc.push(n as u16);
                        p = p.saturating_add(6);
                    },
                    None => {
                        return None;
                    },
                }
            } else {
                match escape_unit(e) {
                    Some(u) => {
                        acc.push(u);
                        p = p.saturating_add(2);
                    },
                    None => {
                        return None;
                    },
                }
            }
        } else if !(0x20..=0x10FFFF).contains(&c) {
            // A control character, or not a code point.
            return None;
        } else {
            super::quote::push_utf16(&mut acc, c);
            // Never saturates: p < input.len().
            p = p.saturating_add(1);
        }
    }
}

// ---------------------------------------------------------------------
// Literals.
// ---------------------------------------------------------------------

proof fn lemma_matches_at_4(s: Seq<u32>, pos: nat, a: u32, b: u32, c: u32, d: u32)
    ensures
        matches_at(s, pos, seq![a, b, c, d]) <==> (is_at(s, pos, a) && is_at(s, pos + 1, b) && is_at(s, pos + 2, c)
            && is_at(s, pos + 3, d)),
{
    if is_at(s, pos, a) && is_at(s, pos + 1, b) && is_at(s, pos + 2, c) && is_at(s, pos + 3, d) {
        assert(s.subrange(pos as int, (pos + 4) as int) =~= seq![a, b, c, d]);
    }
    if matches_at(s, pos, seq![a, b, c, d]) {
        let t = s.subrange(pos as int, (pos + 4) as int);
        assert(t[0] == a && t[1] == b && t[2] == c && t[3] == d);
        assert(s[pos as int] == t[0]);
        assert(s[pos as int + 1] == t[1]);
        assert(s[pos as int + 2] == t[2]);
        assert(s[pos as int + 3] == t[3]);
    }
}

proof fn lemma_matches_at_5(s: Seq<u32>, pos: nat, a: u32, b: u32, c: u32, d: u32, e: u32)
    ensures
        matches_at(s, pos, seq![a, b, c, d, e]) <==> (is_at(s, pos, a) && is_at(s, pos + 1, b) && is_at(s, pos + 2, c)
            && is_at(s, pos + 3, d) && is_at(s, pos + 4, e)),
{
    if is_at(s, pos, a) && is_at(s, pos + 1, b) && is_at(s, pos + 2, c) && is_at(s, pos + 3, d) && is_at(
        s,
        pos + 4,
        e,
    ) {
        assert(s.subrange(pos as int, (pos + 5) as int) =~= seq![a, b, c, d, e]);
    }
    if matches_at(s, pos, seq![a, b, c, d, e]) {
        let t = s.subrange(pos as int, (pos + 5) as int);
        assert(t[0] == a && t[1] == b && t[2] == c && t[3] == d && t[4] == e);
        assert(s[pos as int] == t[0]);
        assert(s[pos as int + 1] == t[1]);
        assert(s[pos as int + 2] == t[2]);
        assert(s[pos as int + 3] == t[3]);
        assert(s[pos as int + 4] == t[4]);
    }
}

/// The literal `true` occurs at `pos`.
fn matches_true(input: &[u32], pos: usize) -> (r: bool)
    requires
        pos <= input.len(),
    ensures
        r == matches_at(input@, pos as nat, lit_true()),
{
    proof {
        lemma_matches_at_4(input@, pos as nat, 0x74, 0x72, 0x75, 0x65);
    }
    // Each test runs only after the one before it found a code point, so
    // the next index is at most input.len().
    at(input, pos, 0x74) && at(input, pos.saturating_add(1), 0x72) && at(input, pos.saturating_add(2), 0x75) && at(
        input,
        pos.saturating_add(3),
        0x65,
    )
}

/// The literal `false` occurs at `pos`.
fn matches_false(input: &[u32], pos: usize) -> (r: bool)
    requires
        pos <= input.len(),
    ensures
        r == matches_at(input@, pos as nat, lit_false()),
{
    proof {
        lemma_matches_at_5(input@, pos as nat, 0x66, 0x61, 0x6C, 0x73, 0x65);
    }
    at(input, pos, 0x66) && at(input, pos.saturating_add(1), 0x61) && at(input, pos.saturating_add(2), 0x6C) && at(
        input,
        pos.saturating_add(3),
        0x73,
    ) && at(input, pos.saturating_add(4), 0x65)
}

/// The literal `null` occurs at `pos`.
fn matches_null(input: &[u32], pos: usize) -> (r: bool)
    requires
        pos <= input.len(),
    ensures
        r == matches_at(input@, pos as nat, lit_null()),
{
    proof {
        lemma_matches_at_4(input@, pos as nat, 0x6E, 0x75, 0x6C, 0x6C);
    }
    at(input, pos, 0x6E) && at(input, pos.saturating_add(1), 0x75) && at(input, pos.saturating_add(2), 0x6C) && at(
        input,
        pos.saturating_add(3),
        0x6C,
    )
}

/// A copy of `input[start..end]`.
fn copy_range(input: &[u32], start: usize, end: usize) -> (r: Vec<u32>)
    requires
        start <= end <= input.len(),
    ensures
        r@ == input@.subrange(start as int, end as int),
{
    let mut t: Vec<u32> = Vec::new();
    let mut j = start;
    proof {
        assert(t@ =~= input@.subrange(start as int, start as int));
    }
    while j < end
        invariant
            start <= j <= end,
            end <= input.len(),
            t@ == input@.subrange(start as int, j as int),
        decreases end - j,
    {
        match input.get(j) {
            Some(&x) => {
                t.push(x);
            },
            None => {
                // `get` is `None` only past the end, and j < end <= input.len().
                proof {
                    assert(false);
                }
            },
        }
        proof {
            assert(t@ =~= input@.subrange(start as int, j as int + 1));
        }
        // Never saturates: j < end.
        j = j.saturating_add(1);
    }
    t
}

// ---------------------------------------------------------------------
// One-step unfoldings of the spec's loops, each proven on its own so the
// loops below need no fuel.
// ---------------------------------------------------------------------

proof fn lemma_elements_guard(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonValue>)
    requires
        acc.len() >= s.len(),
    ensures
        super::spec::parse_elements(s, pos, levels, acc) is None,
{
    reveal_with_fuel(super::spec::parse_elements, 2);
}

proof fn lemma_elements_value_none(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonValue>)
    requires
        acc.len() < s.len(),
        super::spec::parse_value(s, pos, levels) is None,
    ensures
        super::spec::parse_elements(s, pos, levels, acc) is None,
{
    reveal_with_fuel(super::spec::parse_elements, 2);
}

proof fn lemma_elements_comma(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonValue>, v: JsonValue, p1: nat)
    requires
        acc.len() < s.len(),
        super::spec::parse_value(s, pos, levels) == Some((v, p1)),
        is_at(s, super::spec::skip_ws(s, p1), 0x2C),
    ensures
        super::spec::parse_elements(s, pos, levels, acc) == super::spec::parse_elements(
            s,
            super::spec::skip_ws(s, super::spec::skip_ws(s, p1) + 1),
            levels,
            acc.push(v),
        ),
{
    reveal_with_fuel(super::spec::parse_elements, 2);
}

proof fn lemma_elements_close(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonValue>, v: JsonValue, p1: nat)
    requires
        acc.len() < s.len(),
        super::spec::parse_value(s, pos, levels) == Some((v, p1)),
        is_at(s, super::spec::skip_ws(s, p1), 0x5D),
    ensures
        super::spec::parse_elements(s, pos, levels, acc) == Some((JsonValue::Array(acc.push(v)), super::spec::skip_ws(s, p1) + 1)),
{
    reveal_with_fuel(super::spec::parse_elements, 2);
}

proof fn lemma_elements_stray(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonValue>, v: JsonValue, p1: nat)
    requires
        acc.len() < s.len(),
        super::spec::parse_value(s, pos, levels) == Some((v, p1)),
        !is_at(s, super::spec::skip_ws(s, p1), 0x2C),
        !is_at(s, super::spec::skip_ws(s, p1), 0x5D),
    ensures
        super::spec::parse_elements(s, pos, levels, acc) is None,
{
    reveal_with_fuel(super::spec::parse_elements, 2);
}

proof fn lemma_members_guard(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonMember>)
    requires
        acc.len() >= s.len(),
    ensures
        super::spec::parse_members(s, pos, levels, acc) is None,
{
    reveal_with_fuel(super::spec::parse_members, 2);
}

proof fn lemma_members_key_none(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonMember>)
    requires
        acc.len() < s.len(),
        super::spec::parse_string(s, pos) is None,
    ensures
        super::spec::parse_members(s, pos, levels, acc) is None,
{
    reveal_with_fuel(super::spec::parse_members, 2);
}

proof fn lemma_members_no_colon(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonMember>, key: Seq<u16>, p1: nat)
    requires
        acc.len() < s.len(),
        super::spec::parse_string(s, pos) == Some((key, p1)),
        !is_at(s, super::spec::skip_ws(s, p1), 0x3A),
    ensures
        super::spec::parse_members(s, pos, levels, acc) is None,
{
    reveal_with_fuel(super::spec::parse_members, 2);
}

proof fn lemma_members_value_none(s: Seq<u32>, pos: nat, levels: nat, acc: Seq<JsonMember>, key: Seq<u16>, p1: nat)
    requires
        acc.len() < s.len(),
        super::spec::parse_string(s, pos) == Some((key, p1)),
        is_at(s, super::spec::skip_ws(s, p1), 0x3A),
        super::spec::parse_value(s, super::spec::skip_ws(s, super::spec::skip_ws(s, p1) + 1), levels) is None,
    ensures
        super::spec::parse_members(s, pos, levels, acc) is None,
{
    reveal_with_fuel(super::spec::parse_members, 2);
}

proof fn lemma_members_comma(
    s: Seq<u32>,
    pos: nat,
    levels: nat,
    acc: Seq<JsonMember>,
    key: Seq<u16>,
    p1: nat,
    v: JsonValue,
    p2: nat,
)
    requires
        acc.len() < s.len(),
        super::spec::parse_string(s, pos) == Some((key, p1)),
        is_at(s, super::spec::skip_ws(s, p1), 0x3A),
        super::spec::parse_value(s, super::spec::skip_ws(s, super::spec::skip_ws(s, p1) + 1), levels) == Some((v, p2)),
        is_at(s, super::spec::skip_ws(s, p2), 0x2C),
    ensures
        super::spec::parse_members(s, pos, levels, acc) == super::spec::parse_members(
            s,
            super::spec::skip_ws(s, super::spec::skip_ws(s, p2) + 1),
            levels,
            acc.push(JsonMember { key: key, value: v }),
        ),
{
    reveal_with_fuel(super::spec::parse_members, 2);
}

proof fn lemma_members_close(
    s: Seq<u32>,
    pos: nat,
    levels: nat,
    acc: Seq<JsonMember>,
    key: Seq<u16>,
    p1: nat,
    v: JsonValue,
    p2: nat,
)
    requires
        acc.len() < s.len(),
        super::spec::parse_string(s, pos) == Some((key, p1)),
        is_at(s, super::spec::skip_ws(s, p1), 0x3A),
        super::spec::parse_value(s, super::spec::skip_ws(s, super::spec::skip_ws(s, p1) + 1), levels) == Some((v, p2)),
        is_at(s, super::spec::skip_ws(s, p2), 0x7D),
    ensures
        super::spec::parse_members(s, pos, levels, acc) == Some(
            (JsonValue::Object(acc.push(JsonMember { key: key, value: v })), super::spec::skip_ws(s, p2) + 1),
        ),
{
    reveal_with_fuel(super::spec::parse_members, 2);
}

proof fn lemma_members_stray(
    s: Seq<u32>,
    pos: nat,
    levels: nat,
    acc: Seq<JsonMember>,
    key: Seq<u16>,
    p1: nat,
    v: JsonValue,
    p2: nat,
)
    requires
        acc.len() < s.len(),
        super::spec::parse_string(s, pos) == Some((key, p1)),
        is_at(s, super::spec::skip_ws(s, p1), 0x3A),
        super::spec::parse_value(s, super::spec::skip_ws(s, super::spec::skip_ws(s, p1) + 1), levels) == Some((v, p2)),
        !is_at(s, super::spec::skip_ws(s, p2), 0x2C),
        !is_at(s, super::spec::skip_ws(s, p2), 0x7D),
    ensures
        super::spec::parse_members(s, pos, levels, acc) is None,
{
    reveal_with_fuel(super::spec::parse_members, 2);
}

// ---------------------------------------------------------------------
// Values, arrays and objects.
// ---------------------------------------------------------------------

/// ECMA-404 `string` as a `value`.
fn parse_string_value(input: &[u32], pos: usize) -> (r: Option<(Json, usize)>)
    requires
        pos <= input.len(),
    ensures
        val_res(r) == (match super::spec::parse_string(input@, pos as nat) {
            Some((u, p)) => Some((JsonValue::String(u), p)),
            None => None,
        }),
        r matches Some((_, p)) ==> p <= input.len(),
{
    let (u, p) = parse_string(input, pos)?;
    Some((Json::String(u), p))
}

/// ECMA-404 `number` as a `value`: the value is the literal's text.
fn parse_number_value(input: &[u32], pos: usize) -> (r: Option<(Json, usize)>)
    requires
        pos <= input.len(),
    ensures
        val_res(r) == (match super::spec::parse_number(input@, pos as nat) {
            Some(p) => Some((JsonValue::Number(input@.subrange(pos as int, p as int)), p)),
            None => None,
        }),
        r matches Some((_, p)) ==> p <= input.len(),
{
    match parse_number(input, pos) {
        Some(p) => {
            let text = copy_range(input, pos, p);
            Some((Json::Number(text), p))
        },
        None => None,
    }
}

/// `true`, `false` and `null` as a `value`.
fn parse_literal_value(input: &[u32], pos: usize) -> (r: Option<(Json, usize)>)
    requires
        pos <= input.len(),
    ensures
        val_res(r) == (if matches_at(input@, pos as nat, lit_true()) {
            Some((JsonValue::Bool(true), pos as nat + 4))
        } else if matches_at(input@, pos as nat, lit_false()) {
            Some((JsonValue::Bool(false), pos as nat + 5))
        } else if matches_at(input@, pos as nat, lit_null()) {
            Some((JsonValue::Null, pos as nat + 4))
        } else {
            None
        }),
        r matches Some((_, p)) ==> p <= input.len(),
{
    if matches_true(input, pos) {
        // Never saturates: 4 code points occur at pos.
        Some((Json::Bool(true), pos.saturating_add(4)))
    } else if matches_false(input, pos) {
        Some((Json::Bool(false), pos.saturating_add(5)))
    } else if matches_null(input, pos) {
        Some((Json::Null, pos.saturating_add(4)))
    } else {
        None
    }
}

/// ECMA-404 `value`: `pos` is the position of its first code point.
fn parse_value(input: &[u32], pos: usize, levels: usize) -> (r: Option<(Json, usize)>)
    requires
        pos <= input.len(),
    ensures
        val_res(r) == super::spec::parse_value(input@, pos as nat, levels as nat),
        r matches Some((_, p)) ==> p <= input.len(),
    decreases levels, 3int,
{
    let c = match input.get(pos) {
        Some(&c) => c,
        None => {
            return None;
        },
    };
    if c == 0x7B {
        parse_object(input, pos, levels)
    } else if c == 0x5B {
        parse_array(input, pos, levels)
    } else if c == 0x22 {
        parse_string_value(input, pos)
    } else if c == 0x2D || is_digit(c) {
        parse_number_value(input, pos)
    } else {
        parse_literal_value(input, pos)
    }
}

/// ECMA-404 `array`: `pos` is the position of the "[".
fn parse_array(input: &[u32], pos: usize, levels: usize) -> (r: Option<(Json, usize)>)
    requires
        pos < input.len(),
    ensures
        val_res(r) == super::spec::parse_array(input@, pos as nat, levels as nat),
        r matches Some((_, p)) ==> p <= input.len(),
    decreases levels, 2int,
{
    if levels == 0 {
        return None;
    }
    // Never saturates: pos < input.len().
    let p = skip_ws(input, pos.saturating_add(1));
    if at(input, p, 0x5D) {
        let empty: Vec<Json> = Vec::new();
        proof {
            lemma_array_view(empty);
            lemma_items_view_empty();
        }
        Some((Json::Array(empty), p.saturating_add(1)))
    } else {
        parse_elements(input, p, levels.saturating_sub(1))
    }
}

/// The `elements` of an array, from none read yet: `pos` is the position of
/// the first element's value.
fn parse_elements(input: &[u32], pos: usize, levels: usize) -> (r: Option<(Json, usize)>)
    requires
        pos <= input.len(),
    ensures
        val_res(r) == super::spec::parse_elements(input@, pos as nat, levels as nat, Seq::empty()),
        r matches Some((_, p)) ==> p <= input.len(),
    decreases levels, 4int,
{
    let mut acc: Vec<Json> = Vec::new();
    proof {
        lemma_items_view_empty();
    }
    let mut p = pos;
    loop
        invariant
            p <= input.len(),
            super::spec::parse_elements(input@, pos as nat, levels as nat, Seq::empty())
                == super::spec::parse_elements(input@, p as nat, levels as nat, items_view(acc@)),
        decreases input.len() - acc.len(),
    {
        let ghost before = acc@;
        proof {
            lemma_items_view_len(before);
        }
        // The spec's measure guard.
        if acc.len() >= input.len() {
            proof {
                lemma_elements_guard(input@, p as nat, levels as nat, items_view(before));
            }
            return None;
        }
        match parse_value(input, p, levels) {
            None => {
                proof {
                    lemma_elements_value_none(input@, p as nat, levels as nat, items_view(before));
                }
                return None;
            },
            Some((v, p1)) => {
                let q = skip_ws(input, p1);
                if at(input, q, 0x2C) {
                    // Never saturates: q < input.len().
                    let q2 = skip_ws(input, q.saturating_add(1));
                    proof {
                        lemma_items_view_push(before, v);
                        lemma_elements_comma(input@, p as nat, levels as nat, items_view(before), v.view(), p1 as nat);
                    }
                    acc.push(v);
                    p = q2;
                } else if at(input, q, 0x5D) {
                    proof {
                        lemma_items_view_push(before, v);
                        lemma_elements_close(input@, p as nat, levels as nat, items_view(before), v.view(), p1 as nat);
                    }
                    acc.push(v);
                    proof {
                        lemma_array_view(acc);
                    }
                    return Some((Json::Array(acc), q.saturating_add(1)));
                } else {
                    proof {
                        lemma_elements_stray(input@, p as nat, levels as nat, items_view(before), v.view(), p1 as nat);
                    }
                    return None;
                }
            },
        }
    }
}

/// ECMA-404 `object`: `pos` is the position of the "{".
fn parse_object(input: &[u32], pos: usize, levels: usize) -> (r: Option<(Json, usize)>)
    requires
        pos < input.len(),
    ensures
        val_res(r) == super::spec::parse_object(input@, pos as nat, levels as nat),
        r matches Some((_, p)) ==> p <= input.len(),
    decreases levels, 2int,
{
    if levels == 0 {
        return None;
    }
    // Never saturates: pos < input.len().
    let p = skip_ws(input, pos.saturating_add(1));
    if at(input, p, 0x7D) {
        let empty: Vec<Member> = Vec::new();
        proof {
            lemma_object_view(empty);
            lemma_members_view_empty();
        }
        Some((Json::Object(empty), p.saturating_add(1)))
    } else {
        parse_members(input, p, levels.saturating_sub(1))
    }
}

/// The `members` of an object, from none read yet: `pos` is the position of
/// the first member's string.
fn parse_members(input: &[u32], pos: usize, levels: usize) -> (r: Option<(Json, usize)>)
    requires
        pos <= input.len(),
    ensures
        val_res(r) == super::spec::parse_members(input@, pos as nat, levels as nat, Seq::empty()),
        r matches Some((_, p)) ==> p <= input.len(),
    decreases levels, 4int,
{
    let mut acc: Vec<Member> = Vec::new();
    proof {
        lemma_members_view_empty();
    }
    let mut p = pos;
    loop
        invariant
            p <= input.len(),
            super::spec::parse_members(input@, pos as nat, levels as nat, Seq::empty())
                == super::spec::parse_members(input@, p as nat, levels as nat, members_view(acc@)),
        decreases input.len() - acc.len(),
    {
        let ghost before = acc@;
        proof {
            lemma_members_view_len(before);
        }
        // The spec's measure guard.
        if acc.len() >= input.len() {
            proof {
                lemma_members_guard(input@, p as nat, levels as nat, members_view(before));
            }
            return None;
        }
        match parse_string(input, p) {
            None => {
                proof {
                    lemma_members_key_none(input@, p as nat, levels as nat, members_view(before));
                }
                return None;
            },
            Some((key, p1)) => {
                let q = skip_ws(input, p1);
                if !at(input, q, 0x3A) {
                    proof {
                        lemma_members_no_colon(input@, p as nat, levels as nat, members_view(before), key@, p1 as nat);
                    }
                    return None;
                }
                // Never saturates: q < input.len().
                let start = skip_ws(input, q.saturating_add(1));
                match parse_value(input, start, levels) {
                    None => {
                        proof {
                            lemma_members_value_none(
                                input@,
                                p as nat,
                                levels as nat,
                                members_view(before),
                                key@,
                                p1 as nat,
                            );
                        }
                        return None;
                    },
                    Some((v, p2)) => {
                        let r = skip_ws(input, p2);
                        let ghost kv = key@;
                        let ghost vv = v.view();
                        let m = Member { key, value: v };
                        if at(input, r, 0x2C) {
                            // Never saturates: r < input.len().
                            let next = skip_ws(input, r.saturating_add(1));
                            proof {
                                lemma_members_view_push(before, m);
                                lemma_members_comma(
                                    input@,
                                    p as nat,
                                    levels as nat,
                                    members_view(before),
                                    kv,
                                    p1 as nat,
                                    vv,
                                    p2 as nat,
                                );
                            }
                            acc.push(m);
                            p = next;
                        } else if at(input, r, 0x7D) {
                            proof {
                                lemma_members_view_push(before, m);
                                lemma_members_close(
                                    input@,
                                    p as nat,
                                    levels as nat,
                                    members_view(before),
                                    kv,
                                    p1 as nat,
                                    vv,
                                    p2 as nat,
                                );
                            }
                            acc.push(m);
                            proof {
                                lemma_object_view(acc);
                            }
                            return Some((Json::Object(acc), r.saturating_add(1)));
                        } else {
                            proof {
                                lemma_members_stray(
                                    input@,
                                    p as nat,
                                    levels as nat,
                                    members_view(before),
                                    kv,
                                    p1 as nat,
                                    vv,
                                    p2 as nat,
                                );
                            }
                            return None;
                        }
                    },
                }
            },
        }
    }
}

/// ECMA-404 JSON text, as `JSON.parse` reads it: `None` is a SyntaxError.
pub fn parse(input: &[u32]) -> (r: Option<Json>)
    ensures
        super::contract::parse_ensures(input@, match r {
            Some(j) => Some(j@),
            None => None,
        }),
{
    // ws value ws
    let start = skip_ws(input, 0);
    match parse_value(input, start, 512) {
        None => None,
        Some((v, p)) => {
            let end = skip_ws(input, p);
            if end == input.len() {
                Some(v)
            } else {
                None
            }
        },
    }
}

} // verus!

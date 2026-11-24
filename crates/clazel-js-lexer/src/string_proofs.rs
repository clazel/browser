//! Lemmas about [`super::spec`]'s string literal relations that the proofs
//! of [`super::exec`]'s string scanner use: a `StringCharacter` has one
//! length and one value, and no character starts with the closing quote.

#[cfg(verus_only)]
use super::equivalence::*;
#[cfg(verus_only)]
use super::independent::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An `EscapeSequence` (after the backslash) has one length and one value.
pub proof fn lemma_escape_det(s: Seq<u32>, i: int, m1: int, m2: int, v1: Seq<u16>, v2: Seq<u16>)
    requires
        escape_sequence_sv(s, i, m1, v1),
        escape_sequence_sv(s, i, m2, v2),
    ensures
        m1 == m2,
        v1 =~= v2,
{
    lemma_unicode_escape_equiv(s, i, m1);
    lemma_unicode_escape_equiv(s, i, m2);
    if hex_escape_sequence(s, i, m1) {
        lemma_hex_escape(s, i, m1);
    }
    if hex_escape_sequence(s, i, m2) {
        lemma_hex_escape(s, i, m2);
    }
}

/// A `HexEscapeSequence` that starts at `i`.
pub proof fn lemma_hex_escape(s: Seq<u32>, i: int, m: int)
    requires
        hex_escape_sequence(s, i, m),
    ensures
        m == i + 3,
        hex_digits_mv(s, i + 1, m) == hex_digit_value(s[i + 1]) * 16 + hex_digit_value(s[i + 2]),
{
    reveal_with_fuel(hex_digits_mv, 3);
}

/// A `LineTerminatorSequence` has one length.
pub proof fn lemma_lts_det(s: Seq<u32>, i: int, m1: int, m2: int)
    requires
        line_terminator_sequence(s, i, m1),
        line_terminator_sequence(s, i, m2),
    ensures
        m1 == m2,
{
}

/// An `EscapeSequence` never starts with a `LineTerminator`.
pub proof fn lemma_escape_not_lt(s: Seq<u32>, i: int, m: int, v: Seq<u16>)
    requires
        0 <= i < s.len(),
        is_line_terminator(s[i]),
    ensures
        !escape_sequence_sv(s, i, m, v),
{
    lemma_is_lit(s, i, i + 2, seq!['u', '{']);
}

/// A `StringCharacter` has one length and one value.
pub proof fn lemma_string_char_det(
    s: Seq<u32>,
    i: int,
    m1: int,
    m2: int,
    q: u32,
    v1: Seq<u16>,
    v2: Seq<u16>,
)
    requires
        string_character_sv(s, i, m1, q, v1),
        string_character_sv(s, i, m2, q, v2),
    ensures
        m1 == m2,
        v1 =~= v2,
{
    if s[i] == 0x5C {
        if line_continuation(s, i, m1) && line_continuation(s, i, m2) {
            lemma_lts_det(s, i + 1, m1, m2);
        } else if line_continuation(s, i, m1) {
            lemma_escape_not_lt(s, i + 1, m2, v2);
        } else if line_continuation(s, i, m2) {
            lemma_escape_not_lt(s, i + 1, m1, v1);
        } else {
            lemma_escape_det(s, i + 1, m1, m2, v1, v2);
        }
    }
}

/// No `StringCharacter` starts with the quote that closes the string.
pub proof fn lemma_quote_starts_no_char(s: Seq<u32>, i: int, q: u32)
    requires
        0 <= i < s.len(),
        s[i] == q,
        q == 0x22 || q == 0x27,
    ensures
        forall|m: int, v: Seq<u16>| !string_character_sv(s, i, m, q, v),
{
}

/// `StringCharacters?` over `[a, p)`: empty, or characters with value `v`.
pub open spec fn sc(s: Seq<u32>, a: int, p: int, q: u32, v: Seq<u16>) -> bool {
    (p == a && v.len() == 0) || string_characters_sv(s, a, p, q, v)
}

/// A character after characters.
pub proof fn lemma_sc_append(s: Seq<u32>, a: int, p: int, p2: int, q: u32, v: Seq<u16>, w: Seq<u16>)
    requires
        sc(s, a, p, q, v),
        p < p2,
        string_character_sv(s, p, p2, q, w),
    ensures
        string_characters_sv(s, a, p2, q, v + w),
    decreases p - a,
{
    if p == a {
        assert(v + w =~= w);
    } else {
        if string_character_sv(s, a, p, q, v) {
            assert(string_characters_sv(s, p, p2, q, w));
            assert(string_characters_sv(s, a, p2, q, v + Seq::<u16>::empty() + w) || true);
        }
        if !string_character_sv(s, a, p, q, v) {
            let (k, v1, v2) = choose|k: int, v1: Seq<u16>, v2: Seq<u16>| #![auto]
                a < k < p && string_character_sv(s, a, k, q, v1) && string_characters_sv(
                    s,
                    k,
                    p,
                    q,
                    v2,
                ) && v =~= v1 + v2;
            lemma_sc_append(s, k, p, p2, q, v2, w);
            assert(string_characters_sv(s, a, p2, q, v1 + (v2 + w)));
            assert(v + w =~= v1 + (v2 + w));
        }
    }
}

/// What the string scanner knows at `j` after scanning the characters from
/// `a`: they are `StringCharacters?` with value `units`; every derivation of
/// longer characters from `a` goes through the character at `j`; and no
/// derivation of characters from `a` ends before `j` at the quote.
pub open spec fn str_inv(s: Seq<u32>, a: int, j: int, q: u32, units: Seq<u16>) -> bool {
    a <= j && sc(s, a, j, q, units) && (forall|p: int, v: Seq<u16>|
        p > j && #[trigger] sc(s, a, p, q, v) ==> exists|v2: Seq<u16>|
            sc(s, j, p, q, v2) && v =~= units + v2) && (forall|p: int, v: Seq<u16>|
        a <= p < j && #[trigger] sc(s, a, p, q, v) ==> s[p] != q)
}

/// Nothing scanned yet.
pub proof fn lemma_str_init(s: Seq<u32>, a: int, q: u32)
    ensures
        str_inv(s, a, a, q, Seq::<u16>::empty()),
{
    assert(sc(s, a, a, q, Seq::<u16>::empty()));
    assert forall|p: int, v: Seq<u16>| p > a && #[trigger] sc(s, a, p, q, v) implies exists|
        v2: Seq<u16>,
    | sc(s, a, p, q, v2) && v =~= Seq::<u16>::empty() + v2 by {
        assert(v =~= Seq::<u16>::empty() + v);
    }
}

/// A character after the scanned characters: the invariant holds at its end.
pub proof fn lemma_str_step(s: Seq<u32>, a: int, j: int, e: int, q: u32, units: Seq<u16>, w: Seq<u16>)
    requires
        str_inv(s, a, j, q, units),
        j < e,
        j < s.len(),
        s[j] != q,
        string_character_sv(s, j, e, q, w),
    ensures
        str_inv(s, a, e, q, units + w),
{
    lemma_sc_append(s, a, j, e, q, units, w);
    assert forall|p: int, v: Seq<u16>| p > e && #[trigger] sc(s, a, p, q, v) implies exists|
        v3: Seq<u16>,
    | sc(s, e, p, q, v3) && v =~= (units + w) + v3 by {
        let v2 = choose|v2: Seq<u16>| sc(s, j, p, q, v2) && v =~= units + v2;
        if string_character_sv(s, j, p, q, v2) {
            lemma_string_char_det(s, j, e, p, q, w, v2);
        } else {
            let (kk, v1, v3) = choose|kk: int, v1: Seq<u16>, v3: Seq<u16>| #![auto]
                j < kk < p && string_character_sv(s, j, kk, q, v1) && string_characters_sv(
                    s,
                    kk,
                    p,
                    q,
                    v3,
                ) && v2 =~= v1 + v3;
            lemma_string_char_det(s, j, e, kk, q, w, v1);
            assert(sc(s, e, p, q, v3));
            assert(v =~= (units + w) + v3);
        }
    }
    assert forall|p: int, v: Seq<u16>| a <= p < e && #[trigger] sc(s, a, p, q, v) implies s[p]
        != q by {
        if p > j {
            let v2 = choose|v2: Seq<u16>| sc(s, j, p, q, v2) && v =~= units + v2;
            if string_character_sv(s, j, p, q, v2) {
                lemma_string_char_det(s, j, e, p, q, w, v2);
            } else {
                let (kk, v1, v3) = choose|kk: int, v1: Seq<u16>, v3: Seq<u16>| #![auto]
                    j < kk < p && string_character_sv(s, j, kk, q, v1) && string_characters_sv(
                        s,
                        kk,
                        p,
                        q,
                        v3,
                    ) && v2 =~= v1 + v3;
                lemma_string_char_det(s, j, e, kk, q, w, v1);
            }
        }
    }
}

/// A backslash escape's SV does not depend on the quote.
pub proof fn lemma_esc_q_free(s: Seq<u32>, i: int, m: int, q1: u32, q2: u32, v: Seq<u16>)
    requires
        0 <= i < s.len(),
        s[i] == 0x5C,
        string_character_sv(s, i, m, q1, v),
    ensures
        string_character_sv(s, i, m, q2, v),
{
}

/// No character starts at `j`, which is not the closing quote: the string
/// literal does not end anywhere.
pub proof fn lemma_str_no_char(s: Seq<u32>, a: int, j: int, q: u32, units: Seq<u16>, k: int)
    requires
        str_inv(s, a, j, q, units),
        a == k + 1,
        0 <= k < s.len(),
        s[k] == q,
        q == 0x22 || q == 0x27,
        !(j < s.len() && s[j] == q),
        forall|m: int, v: Seq<u16>| !string_character_sv(s, j, m, q, v),
    ensures
        forall|jj: int| !string_literal(s, k, jj),
{
    assert forall|jj: int| !string_literal(s, k, jj) by {
        if string_literal(s, k, jj) {
            let v = choose|v: Seq<u16>| string_literal_sv(s, k, jj, v);
            let p = jj - 1;
            let v2 = if jj == k + 2 {
                Seq::<u16>::empty()
            } else {
                v
            };
            assert(sc(s, a, p, q, v2));
            if p > j {
                let v3 = choose|v3: Seq<u16>| sc(s, j, p, q, v3) && v2 =~= units + v3;
                assert(string_characters_sv(s, j, p, q, v3));
                if !string_character_sv(s, j, p, q, v3) {
                    let (kk, v1, v4) = choose|kk: int, v1: Seq<u16>, v4: Seq<u16>| #![auto]
                        j < kk < p && string_character_sv(s, j, kk, q, v1)
                            && string_characters_sv(s, kk, p, q, v4) && v3 =~= v1 + v4;
                }
            }
        }
    }
}

/// The closing quote at `j`: the literal ends right after it, and is the
/// only literal that starts at `k`.
pub proof fn lemma_str_quote(s: Seq<u32>, a: int, j: int, q: u32, units: Seq<u16>, k: int)
    requires
        str_inv(s, a, j, q, units),
        a == k + 1,
        0 <= k < s.len(),
        s[k] == q,
        q == 0x22 || q == 0x27,
        j < s.len(),
        s[j] == q,
    ensures
        string_literal_sv(s, k, j + 1, units),
        forall|jj: int| string_literal(s, k, jj) ==> jj == j + 1,
{
    lemma_quote_starts_no_char(s, j, q);
    if j > a {
        assert(string_characters_sv(s, a, j, q, units));
    }
    assert forall|jj: int| string_literal(s, k, jj) implies jj == j + 1 by {
        let v = choose|v: Seq<u16>| string_literal_sv(s, k, jj, v);
        let p = jj - 1;
        let v2 = if jj == k + 2 {
            Seq::<u16>::empty()
        } else {
            v
        };
        assert(sc(s, a, p, q, v2));
        if p > j {
            let v3 = choose|v3: Seq<u16>| sc(s, j, p, q, v3) && v2 =~= units + v3;
            assert(string_characters_sv(s, j, p, q, v3));
            if !string_character_sv(s, j, p, q, v3) {
                let (kk, v1, v4) = choose|kk: int, v1: Seq<u16>, v4: Seq<u16>| #![auto]
                    j < kk < p && string_character_sv(s, j, kk, q, v1) && string_characters_sv(
                        s,
                        kk,
                        p,
                        q,
                        v4,
                    ) && v3 =~= v1 + v4;
            }
        }
    }
}

} // verus!

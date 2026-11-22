//! Lemmas for the proofs of `exec::scan_regexp` and
//! `exec::scan_regexp_class` (§12.9.5): the closing `/` of a regular
//! expression literal, and the closing `]` of a class, are unique.
//!
//! [`super::spec`]'s `regexp_chars` and `regexp_class_chars` are built left
//! to right, one character at a time, so two derivations of a body from the
//! same start could in principle end at different `/`. Here the scan that
//! the executable lexer performs is written as two functions of the source
//! text alone ([`class_scan`], [`body_scan`]); every derivation of a class
//! or a body is shown to *walk* along them (a character, or a class, or a
//! backslash sequence, takes the scan from its start to its end), so the
//! end of a class (the first `]` that is not escaped) and the closing `/`
//! of a literal (the first `/` that is not escaped and not in a class) are
//! determined.
//!
//! Nothing here changes [`super::spec`]; these are facts about it.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The end of a class whose `[` is just before `j`: the index after the
/// first `]` reached from `j` that is not the second code point of a
/// backslash sequence, if every code point before it is a
/// `RegularExpressionClassChar`.
pub open spec fn class_scan(s: Seq<u32>, j: int) -> Option<int>
    decreases s.len() - j,
{
    if j < 0 || j >= s.len() {
        None
    } else if s[j] == 0x5D {
        Some(j + 1)
    } else if s[j] == 0x5C {
        if j + 1 < s.len() && is_regexp_non_terminator(s[j + 1]) {
            class_scan(s, j + 2)
        } else {
            None
        }
    } else if is_regexp_non_terminator(s[j]) {
        class_scan(s, j + 1)
    } else {
        None
    }
}

/// The end of the one `RegularExpressionChar` (or, for `/`, none) that
/// starts at `k`.
pub open spec fn rx_next(s: Seq<u32>, k: int) -> Option<int> {
    if k < 0 || k >= s.len() {
        None
    } else if s[k] == 0x5C {
        if k + 1 < s.len() && is_regexp_non_terminator(s[k + 1]) {
            Some(k + 2)
        } else {
            None
        }
    } else if s[k] == 0x5B {
        class_scan(s, k + 1)
    } else if s[k] == 0x2F {
        None
    } else if is_regexp_non_terminator(s[k]) {
        Some(k + 1)
    } else {
        None
    }
}

/// The index of the closing `/` reached from `a`: the first `/` that starts
/// no `RegularExpressionChar`, if every character before it is one.
pub open spec fn body_scan(s: Seq<u32>, a: int) -> Option<int>
    decreases s.len() - a,
{
    if a < 0 || a >= s.len() {
        None
    } else if s[a] == 0x2F {
        Some(a)
    } else {
        match rx_next(s, a) {
            Some(e) => if a < e && e <= s.len() {
                body_scan(s, e)
            } else {
                None
            },
            None => None,
        }
    }
}

/// A class scan that ends, ends after where it started and inside the text.
pub proof fn lemma_class_scan_bound(s: Seq<u32>, j: int)
    requires
        0 <= j,
    ensures
        match class_scan(s, j) {
            Some(e) => j < e <= s.len(),
            None => true,
        },
    decreases s.len() - j,
{
    if j < s.len() && s[j] != 0x5D {
        if s[j] == 0x5C {
            if j + 1 < s.len() && is_regexp_non_terminator(s[j + 1]) {
                lemma_class_scan_bound(s, j + 2);
            }
        } else if is_regexp_non_terminator(s[j]) {
            lemma_class_scan_bound(s, j + 1);
        }
    }
}

/// A character's end is after its start and inside the text.
pub proof fn lemma_rx_next_bound(s: Seq<u32>, k: int)
    requires
        0 <= k,
    ensures
        match rx_next(s, k) {
            Some(e) => k < e <= s.len(),
            None => true,
        },
{
    if k < s.len() && s[k] == 0x5B {
        lemma_class_scan_bound(s, k + 1);
    }
}

/// `body_scan` steps over a character: where a character starts and is not
/// `/`, the scan from there is the scan from its end.
pub proof fn lemma_body_scan_step(s: Seq<u32>, k: int, e: int)
    requires
        0 <= k < s.len(),
        s[k] != 0x2F,
        rx_next(s, k) == Some(e),
    ensures
        body_scan(s, k) == body_scan(s, e),
{
    lemma_rx_next_bound(s, k);
}

/// A class's characters are walked over by `class_scan`.
pub proof fn lemma_class_chars_walk(s: Seq<u32>, a: int, b: int)
    requires
        regexp_class_chars(s, a, b),
    ensures
        class_scan(s, a) == class_scan(s, b),
    decreases b - a,
{
    if a != b {
        let k = choose|k: int|
            a <= k < b && regexp_class_chars(s, a, k) && regexp_class_char(s, k, b);
        lemma_class_chars_walk(s, a, k);
        // The last character takes the scan from `k` to `b`.
        assert(k < s.len());
    }
}

/// The end of a class is where `class_scan` says.
pub proof fn lemma_class_scan_of_class(s: Seq<u32>, k: int, j: int)
    requires
        regexp_class(s, k, j),
    ensures
        class_scan(s, k + 1) == Some(j),
{
    lemma_class_chars_walk(s, k + 1, j - 1);
    assert(s[j - 1] == 0x5D);
    assert(class_scan(s, j - 1) == Some(j));
}

/// A `RegularExpressionChar` is where `rx_next` says, and is not `/`.
pub proof fn lemma_rx_next_of_char(s: Seq<u32>, k: int, j: int)
    requires
        regexp_char(s, k, j),
    ensures
        s[k] != 0x2F,
        rx_next(s, k) == Some(j),
{
    if regexp_class(s, k, j) {
        lemma_class_scan_of_class(s, k, j);
    }
}

/// A `RegularExpressionFirstChar` is where `rx_next` says, and is neither
/// `/` nor `*`.
pub proof fn lemma_rx_next_of_first(s: Seq<u32>, k: int, j: int)
    requires
        regexp_first_char(s, k, j),
    ensures
        s[k] != 0x2F,
        s[k] != 0x2A,
        rx_next(s, k) == Some(j),
{
    if regexp_class(s, k, j) {
        lemma_class_scan_of_class(s, k, j);
    }
}

/// A body's characters are walked over by `body_scan`.
pub proof fn lemma_chars_walk(s: Seq<u32>, a: int, b: int)
    requires
        regexp_chars(s, a, b),
    ensures
        body_scan(s, a) == body_scan(s, b),
    decreases b - a,
{
    if a != b {
        let k = choose|k: int| a <= k < b && regexp_chars(s, a, k) && regexp_char(s, k, b);
        lemma_chars_walk(s, a, k);
        lemma_rx_next_of_char(s, k, b);
        lemma_body_scan_step(s, k, b);
    }
}

/// A body that is followed by `/` ends where `body_scan` says.
pub proof fn lemma_body_scan_of_body(s: Seq<u32>, i: int, b: int)
    requires
        regexp_body(s, i, b),
        b < s.len(),
        s[b] == 0x2F,
    ensures
        body_scan(s, i) == Some(b),
        s[i] != 0x2F,
        s[i] != 0x2A,
{
    let k = choose|k: int| i < k <= b && regexp_first_char(s, i, k) && regexp_chars(s, k, b);
    lemma_rx_next_of_first(s, i, k);
    lemma_body_scan_step(s, i, k);
    lemma_chars_walk(s, k, b);
}

/// What a literal's body says of the scan: the closing `/` is the one
/// `body_scan` finds, and the body does not start with `/` or `*`.
pub proof fn lemma_literal_scan(s: Seq<u32>, i: int, j: int, b: int)
    requires
        regexp_literal(s, i, j, b),
    ensures
        body_scan(s, i + 1) == Some(b),
        s[i + 1] != 0x2F,
        s[i + 1] != 0x2A,
{
    lemma_body_scan_of_body(s, i + 1, b);
}

/// No literal starts at `k` if `body_scan` finds no closing `/`.
pub proof fn lemma_no_literal(s: Seq<u32>, k: int)
    requires
        body_scan(s, k + 1) is None,
    ensures
        forall|b2: int, j2: int| !#[trigger] regexp_literal(s, k, j2, b2),
{
    assert forall|b2: int, j2: int| !#[trigger] regexp_literal(s, k, j2, b2) by {
        if regexp_literal(s, k, j2, b2) {
            lemma_literal_scan(s, k, j2, b2);
        }
    }
}

/// The closing `/` of a regular expression literal is unique.
pub proof fn lemma_literal_unique(s: Seq<u32>, i: int, j1: int, b1: int, j2: int, b2: int)
    requires
        regexp_literal(s, i, j1, b1),
        regexp_literal(s, i, j2, b2),
    ensures
        b1 == b2,
{
    lemma_literal_scan(s, i, j1, b1);
    lemma_literal_scan(s, i, j2, b2);
}

/// A class gains a character.
pub proof fn lemma_class_chars_ext(s: Seq<u32>, a: int, j: int, j2: int)
    requires
        regexp_class_chars(s, a, j),
        regexp_class_char(s, j, j2),
    ensures
        regexp_class_chars(s, a, j2),
{
    assert(a <= j);
}

/// A body (its characters after the first) gains a character.
pub proof fn lemma_chars_ext(s: Seq<u32>, a: int, j: int, j2: int)
    requires
        regexp_chars(s, a, j),
        regexp_char(s, j, j2),
    ensures
        regexp_chars(s, a, j2),
{
    assert(a <= j);
}

/// A body, or the start of one, extends by one `RegularExpressionChar`: the
/// loop invariant of `scan_regexp`. `j == i` is the start (nothing is
/// consumed), where the character must be a `RegularExpressionFirstChar`.
pub proof fn lemma_body_extend(s: Seq<u32>, i: int, j: int, j2: int)
    requires
        i <= j,
        j == i || regexp_body(s, i, j),
        regexp_char(s, j, j2),
        j == i ==> s[j] != 0x2A,
    ensures
        regexp_body(s, i, j2),
{
    if j == i {
        assert(regexp_first_char(s, i, j2));
        assert(regexp_chars(s, j2, j2));
    } else {
        let k = choose|k: int| i < k <= j && regexp_first_char(s, i, k) && regexp_chars(s, k, j);
        lemma_chars_ext(s, k, j, j2);
    }
}

} // verus!

//! A second, independent transcription of "get an encoding" (Encoding
//! §4.2), proven equal to [`super::spec`].
//!
//! The only text is the Encoding Standard's (with Infra's definitions), so
//! this is a same-text transcription. Its reading differs in form:
//!
//! - whitespace is trimmed by peeling one code point at a time off the
//!   front, then off the back, rather than by finding the first and last
//!   positions that are not whitespace;
//! - the label is lowercased once, and looked up as "some row's label
//!   equals it" (the table's labels are lowercase, §4.2's note: "ASCII-
//!   lowercasing its name yields one of its labels", and every label in the
//!   table is written in lowercase), rather than as the first row that is
//!   an ASCII case-insensitive match.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Peel ASCII whitespace off the front.
pub open spec fn trim_front(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() > 0 && is_ascii_whitespace(s[0]) {
        trim_front(s.subrange(1, s.len() as int))
    } else {
        s
    }
}

/// Peel ASCII whitespace off the back.
pub open spec fn trim_back(s: Seq<u32>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() > 0 && is_ascii_whitespace(s.last()) {
        trim_back(s.drop_last())
    } else {
        s
    }
}

/// "Get an encoding": trim, lowercase, and find the row with that label.
pub open spec fn lookup(label: Seq<u32>) -> Option<Encoding> {
    let key = ascii_lowercase(trim_back(trim_front(label)));
    if exists|i: int| 0 <= i < label_count() && #[trigger] row_label(i) == key {
        Some(row_encoding(choose|i: int| 0 <= i < label_count() && #[trigger] row_label(i) == key))
    } else {
        None
    }
}

proof fn lemma_trim_front(s: Seq<u32>, i: nat)
    requires
        i <= s.len(),
    ensures
        trim_front(s.subrange(i as int, s.len() as int)) == s.subrange(
            skip_leading(s, i) as int,
            s.len() as int,
        ),
        i <= skip_leading(s, i) <= s.len(),
    decreases s.len() - i,
{
    let t = s.subrange(i as int, s.len() as int);
    if i < s.len() && is_ascii_whitespace(s[i as int]) {
        lemma_trim_front(s, i + 1);
        assert(t.subrange(1, t.len() as int) =~= s.subrange((i + 1) as int, s.len() as int));
    }
}

proof fn lemma_skip_trailing_le(s: Seq<u32>, j: nat)
    ensures
        skip_trailing(s, j) <= j,
    decreases j,
{
    if j > 0 && j <= s.len() && is_ascii_whitespace(s[j - 1]) {
        lemma_skip_trailing_le(s, (j - 1) as nat);
    }
}

proof fn lemma_trim_back(s: Seq<u32>, a: nat, j: nat)
    requires
        a <= j <= s.len(),
    ensures
        trim_back(s.subrange(a as int, j as int)) == if a < skip_trailing(s, j) {
            s.subrange(a as int, skip_trailing(s, j) as int)
        } else {
            Seq::<u32>::empty()
        },
    decreases j,
{
    let t = s.subrange(a as int, j as int);
    lemma_skip_trailing_le(s, j);
    if a < j {
        if is_ascii_whitespace(s[j - 1]) {
            lemma_trim_back(s, a, (j - 1) as nat);
            assert(t.drop_last() =~= s.subrange(a as int, j - 1));
        }
    } else {
        assert(t =~= Seq::<u32>::empty());
        assert(trim_back(t) == t);
    }
}

/// Trimming front then back is "strip leading and trailing ASCII
/// whitespace".
pub proof fn lemma_trim(s: Seq<u32>)
    ensures
        trim_back(trim_front(s)) == strip_leading_and_trailing_ascii_whitespace(s),
{
    lemma_trim_front(s, 0);
    assert(s.subrange(0, s.len() as int) =~= s);
    let start = skip_leading(s, 0);
    lemma_trim_back(s, start, s.len());
}

proof fn lemma_no_match(label: Seq<u32>, k: nat, i: int)
    requires
        first_match(label, k) is None,
        k <= i < label_count(),
    ensures
        !ascii_case_insensitive_match(label, row_label(i)),
    decreases i - k,
{
    if k < i {
        lemma_no_match(label, k + 1, i);
    }
}

proof fn lemma_first_match_found(label: Seq<u32>, k: nat)
    requires
        first_match(label, k) is Some,
    ensures
        ({
            let i = first_match(label, k)->0;
            i < label_count() && ascii_case_insensitive_match(label, row_label(i as int))
        }),
    decreases label_count() - k,
{
    if k < label_count() && !ascii_case_insensitive_match(label, row_label(k as int)) {
        lemma_first_match_found(label, k + 1);
    }
}

/// The second transcription equals the spec on every label.
pub proof fn lemma_equals_get_an_encoding(label: Seq<u32>)
    ensures
        lookup(label) == get_an_encoding(label),
{
    lemma_trim(label);
    let l = strip_leading_and_trailing_ascii_whitespace(label);
    let key = ascii_lowercase(l);
    super::lemmas::lemma_table();
    if exists|i: int| 0 <= i < label_count() && #[trigger] row_label(i) == key {
        let i = choose|i: int| 0 <= i < label_count() && #[trigger] row_label(i) == key;
        super::lemmas::lemma_row_lowercase(i);
        assert(ascii_case_insensitive_match(l, row_label(i)));
        if first_match(l, 0) is None {
            lemma_no_match(l, 0, i);
        }
        lemma_first_match_found(l, 0);
        let f = first_match(l, 0)->0;
        super::lemmas::lemma_row_lowercase(f as int);
        super::lemmas::lemma_labels_distinct(i, f as int);
    } else {
        if first_match(l, 0) is Some {
            lemma_first_match_found(l, 0);
            let f = first_match(l, 0)->0;
            super::lemmas::lemma_row_lowercase(f as int);
            assert(row_label(f as int) == key);
        }
    }
}

} // verus!

//! The executable "get an encoding" and name lookup, proven to meet
//! [`super::contract`]. Step comments live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::data::*;

verus! {

/// The encoding numbered `n` in the order of the table.
pub fn from_number(n: u8) -> (e: Encoding)
    ensures
        e == encoding_from_number(n as int),
{
    match n {
        0 => Encoding::Utf8,
        1 => Encoding::Ibm866,
        2 => Encoding::Iso8859_2,
        3 => Encoding::Iso8859_3,
        4 => Encoding::Iso8859_4,
        5 => Encoding::Iso8859_5,
        6 => Encoding::Iso8859_6,
        7 => Encoding::Iso8859_7,
        8 => Encoding::Iso8859_8,
        9 => Encoding::Iso8859_8I,
        10 => Encoding::Iso8859_10,
        11 => Encoding::Iso8859_13,
        12 => Encoding::Iso8859_14,
        13 => Encoding::Iso8859_15,
        14 => Encoding::Iso8859_16,
        15 => Encoding::Koi8R,
        16 => Encoding::Koi8U,
        17 => Encoding::Macintosh,
        18 => Encoding::Windows874,
        19 => Encoding::Windows1250,
        20 => Encoding::Windows1251,
        21 => Encoding::Windows1252,
        22 => Encoding::Windows1253,
        23 => Encoding::Windows1254,
        24 => Encoding::Windows1255,
        25 => Encoding::Windows1256,
        26 => Encoding::Windows1257,
        27 => Encoding::Windows1258,
        28 => Encoding::XMacCyrillic,
        29 => Encoding::Gbk,
        30 => Encoding::Gb18030,
        31 => Encoding::Big5,
        32 => Encoding::EucJp,
        33 => Encoding::Iso2022Jp,
        34 => Encoding::ShiftJis,
        35 => Encoding::EucKr,
        36 => Encoding::Replacement,
        37 => Encoding::Utf16Be,
        38 => Encoding::Utf16Le,
        _ => Encoding::XUserDefined,
    }
}

/// The number of encoding `e` in the order of the table.
pub fn number(e: Encoding) -> (n: u8)
    ensures
        n as nat == encoding_number(e),
{
    match e {
        Encoding::Utf8 => 0,
        Encoding::Ibm866 => 1,
        Encoding::Iso8859_2 => 2,
        Encoding::Iso8859_3 => 3,
        Encoding::Iso8859_4 => 4,
        Encoding::Iso8859_5 => 5,
        Encoding::Iso8859_6 => 6,
        Encoding::Iso8859_7 => 7,
        Encoding::Iso8859_8 => 8,
        Encoding::Iso8859_8I => 9,
        Encoding::Iso8859_10 => 10,
        Encoding::Iso8859_13 => 11,
        Encoding::Iso8859_14 => 12,
        Encoding::Iso8859_15 => 13,
        Encoding::Iso8859_16 => 14,
        Encoding::Koi8R => 15,
        Encoding::Koi8U => 16,
        Encoding::Macintosh => 17,
        Encoding::Windows874 => 18,
        Encoding::Windows1250 => 19,
        Encoding::Windows1251 => 20,
        Encoding::Windows1252 => 21,
        Encoding::Windows1253 => 22,
        Encoding::Windows1254 => 23,
        Encoding::Windows1255 => 24,
        Encoding::Windows1256 => 25,
        Encoding::Windows1257 => 26,
        Encoding::Windows1258 => 27,
        Encoding::XMacCyrillic => 28,
        Encoding::Gbk => 29,
        Encoding::Gb18030 => 30,
        Encoding::Big5 => 31,
        Encoding::EucJp => 32,
        Encoding::Iso2022Jp => 33,
        Encoding::ShiftJis => 34,
        Encoding::EucKr => 35,
        Encoding::Replacement => 36,
        Encoding::Utf16Be => 37,
        Encoding::Utf16Le => 38,
        Encoding::XUserDefined => 39,
    }
}

/// ASCII lowercase of one code point.
fn lower(c: u32) -> (r: u32)
    ensures
        r == ascii_lower(c),
{
    if (0x41..=0x5A).contains(&c) {
        proof {
            assert(0x41 <= c <= 0x5A ==> c | 0x20 == c + 0x20) by (bit_vector);
        }
        c | 0x20
    } else {
        c
    }
}

/// The first position from `i` of a code point that is not ASCII
/// whitespace.
fn skip_leading_exec(s: &[u32]) -> (r: usize)
    ensures
        r as nat == skip_leading(s@, 0),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            skip_leading(s@, 0) == skip_leading(s@, i as nat),
        decreases s.len() - i,
    {
        // `get` cannot fail: i < s.len().
        let c = match s.get(i) {
            Some(c) => *c,
            None => 0,
        };
        if !(c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20) {
            return i;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    i
}

/// One past the last code point that is not ASCII whitespace.
fn skip_trailing_exec(s: &[u32]) -> (r: usize)
    ensures
        r as nat == skip_trailing(s@, s@.len()),
        r <= s.len(),
{
    let mut j: usize = s.len();
    while j > 0
        invariant
            j <= s.len(),
            skip_trailing(s@, s@.len()) == skip_trailing(s@, j as nat),
        decreases j,
    {
        // `get` cannot fail: 0 < j <= s.len().
        let c = match s.get(j.saturating_sub(1)) {
            Some(c) => *c,
            None => 0,
        };
        if !(c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20) {
            return j;
        }
        j = j.saturating_sub(1);
    }
    j
}

/// When no row before `r` matches, the first match from 0 is the first
/// match from `r`.
proof fn lemma_first_match_skip(label: Seq<u32>, k: nat, r: nat)
    requires
        k <= r,
        forall|j: int| k <= j < r ==> !ascii_case_insensitive_match(label, #[trigger] row_label(j)),
    ensures
        first_match(label, k) == first_match(label, r),
    decreases r - k,
{
    if k < r {
        lemma_first_match_skip(label, k + 1, r);
    }
}

/// Whether `s[start..end]` is an ASCII case-insensitive match for row `r`'s
/// label.
fn row_matches(s: &[u32], start: usize, end: usize, r: usize) -> (b: bool)
    requires
        start <= end <= s.len(),
        r < label_count(),
    ensures
        b == ascii_case_insensitive_match(s@.subrange(start as int, end as int), row_label(r as int)),
{
    let ghost l = s@.subrange(start as int, end as int);
    proof {
        super::lemmas::lemma_table();
        super::lemmas::lemma_row_label(r as int);
        super::lemmas::lemma_row_lowercase(r as int);
    }
    let row_start = label_start_at_exec(r) as usize;
    let len = label_len_at_exec(r) as usize;
    // Never saturates: start <= end.
    if end.saturating_sub(start) != len {
        proof {
            assert(ascii_lowercase(l).len() != ascii_lowercase(row_label(r as int)).len());
        }
        return false;
    }
    let mut k: usize = 0;
    while k < len
        invariant
            start <= end <= s.len(),
            end - start == len,
            len == row_label(r as int).len(),
            row_start == label_start_at(r as int),
            ascii_lowercase(row_label(r as int)) == row_label(r as int),
            super::lemmas::table_ok(),
            r < super::lemmas::rows(),
            row_label(r as int).len() == super::lemmas::ln()[r as int],
            row_start == super::lemmas::st()[r as int],
            l == s@.subrange(start as int, end as int),
            k <= len,
            forall|t: int| 0 <= t < k ==> #[trigger] ascii_lower(l[t]) == row_label(r as int)[t],
        decreases len - k,
    {
        // `get` cannot fail: start + k < end <= s.len().
        let c = match s.get(start.saturating_add(k)) {
            Some(c) => lower(*c),
            None => 0,
        };
        proof {
            super::lemmas::lemma_row_char(r as int, k as int);
        }
        let want = label_chars_at_exec(row_start.saturating_add(k)) as u32;
        if c != want {
            proof {
                assert(ascii_lowercase(l)[k as int] != ascii_lowercase(row_label(r as int))[k as int]);
            }
            return false;
        }
        // Never saturates: k < len.
        k = k.saturating_add(1);
    }
    proof {
        assert(ascii_lowercase(l) =~= ascii_lowercase(row_label(r as int)));
    }
    true
}

/// "Get an encoding" (Encoding §4.2) from the string `label`; `None` is
/// failure.
pub fn get_an_encoding(label: &[u32]) -> (r: Option<Encoding>)
    ensures
        super::contract::get_an_encoding_ensures(label@, r),
{
    let start = skip_leading_exec(label);
    let end = skip_trailing_exec(label);
    let (start, end) = if start < end {
        (start, end)
    } else {
        (0, 0)
    };
    let ghost l = strip_leading_and_trailing_ascii_whitespace(label@);
    proof {
        if !(skip_leading(label@, 0) < skip_trailing(label@, label@.len())) {
            assert(label@.subrange(0, 0) =~= Seq::<u32>::empty());
        }
    }
    assert(l == label@.subrange(start as int, end as int));
    proof {
        super::lemmas::lemma_table();
    }
    let mut r: usize = 0;
    while r < LABEL_START_LEN
        invariant
            start <= end <= label.len(),
            l == label@.subrange(start as int, end as int),
            l == strip_leading_and_trailing_ascii_whitespace(label@),
            r <= label_count(),
            label_count() == LABEL_START_LEN,
            forall|j: int| 0 <= j < r ==> !ascii_case_insensitive_match(l, #[trigger] row_label(j)),
        decreases LABEL_START_LEN - r,
    {
        if row_matches(label, start, end, r) {
            proof {
                lemma_first_match_skip(l, 0, r as nat);
                assert(first_match(l, r as nat) == Some(r as nat));
                assert(l == strip_leading_and_trailing_ascii_whitespace(label@));
                assert(super::spec::get_an_encoding(label@) == Some(row_encoding(r as int)));
            }
            let e = from_number(label_encoding_at_exec(r));
            assert(e == row_encoding(r as int));
            return Some(e);
        }
        // Never saturates: r < LABEL_START_LEN.
        r = r.saturating_add(1);
    }
    proof {
        lemma_first_match_skip(l, 0, r as nat);
    }
    None
}

/// An encoding's name, as the table gives it (ASCII bytes).
pub fn name(e: Encoding) -> (out: Vec<u8>)
    ensures
        super::contract::name_ensures(e, out@),
{
    let n = number(e) as usize;
    let start = name_start_at_exec(n) as usize;
    let len = name_len_at_exec(n) as usize;
    let mut out: Vec<u8> = Vec::new();
    let mut k: usize = 0;
    while k < len
        invariant
            n as nat == encoding_number(e),
            start == name_start_at(n as int),
            len == name_len_at(n as int),
            k <= len,
            out@.len() == k,
            forall|t: int| 0 <= t < k ==> #[trigger] out@[t] as u32 == super::spec::name(e)[t],
        decreases len - k,
    {
        proof {
            super::lemmas::lemma_table();
            super::lemmas::lemma_name_char(e, k as int);
        }
        out.push(label_chars_at_exec(start.saturating_add(k)));
        // Never saturates: k < len.
        k = k.saturating_add(1);
    }
    proof {
        assert(out@.map_values(|b: u8| b as u32) =~= super::spec::name(e));
    }
    out
}

} // verus!

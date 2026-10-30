//! Executable-style specification of the Encoding Standard's encodings,
//! their names and labels, and "get an encoding" (§4.2), transcribed from
//! the standard. Nothing here runs; it defines what "correct" means.
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - The table of §4.2 is the generated [`super::data`], read from the
//!   standard's own `encodings.json` (the same table, in the form the
//!   standard publishes for machines; its derivation is stated in that
//!   file's header). A label row is a label and the encoding it is listed
//!   under. The rows are sorted by label rather than grouped by encoding,
//!   which changes no result: "get an encoding" asks whether the label
//!   matches *any* row, and the labels are distinct
//!   (`lemmas::lemma_labels_distinct`).
//! - "Return the corresponding encoding" for "any of the labels" is
//!   [`first_match`], the first matching row. With distinct labels the
//!   first match is the only one, so this is the same encoding.
//! - A string is `Seq<u32>`, a sequence of code points (Infra §4.6). The
//!   labels are ASCII, so a label row compares as the code points of its
//!   bytes.
//! - "failure" is `None`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The encodings of §4.2, in the order of the standard's table (the order
/// of `encodings.json`, which the generator checks): variant `n` is the
/// encoding numbered `n` in [`super::data`].
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Encoding {
    /// UTF-8 (§4.2 "The Encoding")
    Utf8,
    /// IBM866
    Ibm866,
    /// ISO-8859-2
    Iso8859_2,
    /// ISO-8859-3
    Iso8859_3,
    /// ISO-8859-4
    Iso8859_4,
    /// ISO-8859-5
    Iso8859_5,
    /// ISO-8859-6
    Iso8859_6,
    /// ISO-8859-7
    Iso8859_7,
    /// ISO-8859-8
    Iso8859_8,
    /// ISO-8859-8-I
    Iso8859_8I,
    /// ISO-8859-10
    Iso8859_10,
    /// ISO-8859-13
    Iso8859_13,
    /// ISO-8859-14
    Iso8859_14,
    /// ISO-8859-15
    Iso8859_15,
    /// ISO-8859-16
    Iso8859_16,
    /// KOI8-R
    Koi8R,
    /// KOI8-U
    Koi8U,
    /// macintosh
    Macintosh,
    /// windows-874
    Windows874,
    /// windows-1250
    Windows1250,
    /// windows-1251
    Windows1251,
    /// windows-1252
    Windows1252,
    /// windows-1253
    Windows1253,
    /// windows-1254
    Windows1254,
    /// windows-1255
    Windows1255,
    /// windows-1256
    Windows1256,
    /// windows-1257
    Windows1257,
    /// windows-1258
    Windows1258,
    /// x-mac-cyrillic
    XMacCyrillic,
    /// GBK
    Gbk,
    /// gb18030
    Gb18030,
    /// Big5
    Big5,
    /// EUC-JP
    EucJp,
    /// ISO-2022-JP
    Iso2022Jp,
    /// Shift_JIS
    ShiftJis,
    /// EUC-KR
    EucKr,
    /// replacement
    Replacement,
    /// UTF-16BE
    Utf16Be,
    /// UTF-16LE
    Utf16Le,
    /// x-user-defined
    XUserDefined,
}

/// The number of encodings in the table of §4.2.
pub open spec fn encoding_count() -> nat {
    40
}

/// The encoding numbered `n` (`n < 40`) in the order of the table.
pub open spec fn encoding_from_number(n: int) -> Encoding {
    if n == 0 { Encoding::Utf8 }
    else if n == 1 { Encoding::Ibm866 }
    else if n == 2 { Encoding::Iso8859_2 }
    else if n == 3 { Encoding::Iso8859_3 }
    else if n == 4 { Encoding::Iso8859_4 }
    else if n == 5 { Encoding::Iso8859_5 }
    else if n == 6 { Encoding::Iso8859_6 }
    else if n == 7 { Encoding::Iso8859_7 }
    else if n == 8 { Encoding::Iso8859_8 }
    else if n == 9 { Encoding::Iso8859_8I }
    else if n == 10 { Encoding::Iso8859_10 }
    else if n == 11 { Encoding::Iso8859_13 }
    else if n == 12 { Encoding::Iso8859_14 }
    else if n == 13 { Encoding::Iso8859_15 }
    else if n == 14 { Encoding::Iso8859_16 }
    else if n == 15 { Encoding::Koi8R }
    else if n == 16 { Encoding::Koi8U }
    else if n == 17 { Encoding::Macintosh }
    else if n == 18 { Encoding::Windows874 }
    else if n == 19 { Encoding::Windows1250 }
    else if n == 20 { Encoding::Windows1251 }
    else if n == 21 { Encoding::Windows1252 }
    else if n == 22 { Encoding::Windows1253 }
    else if n == 23 { Encoding::Windows1254 }
    else if n == 24 { Encoding::Windows1255 }
    else if n == 25 { Encoding::Windows1256 }
    else if n == 26 { Encoding::Windows1257 }
    else if n == 27 { Encoding::Windows1258 }
    else if n == 28 { Encoding::XMacCyrillic }
    else if n == 29 { Encoding::Gbk }
    else if n == 30 { Encoding::Gb18030 }
    else if n == 31 { Encoding::Big5 }
    else if n == 32 { Encoding::EucJp }
    else if n == 33 { Encoding::Iso2022Jp }
    else if n == 34 { Encoding::ShiftJis }
    else if n == 35 { Encoding::EucKr }
    else if n == 36 { Encoding::Replacement }
    else if n == 37 { Encoding::Utf16Be }
    else if n == 38 { Encoding::Utf16Le }
    else { Encoding::XUserDefined }
}

/// The number of encoding `e` in the order of the table: the inverse of
/// [`encoding_from_number`].
pub open spec fn encoding_number(e: Encoding) -> nat {
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

/// The number of label rows.
pub open spec fn label_count() -> nat {
    super::data::LABEL_START_LEN as nat
}

/// The code points of `len` characters of the table's character array
/// from `start`.
pub open spec fn chars(start: int, len: nat) -> Seq<u32> {
    Seq::new(len, |k: int| super::data::label_chars_at(start + k) as u32)
}

/// Label row `i`'s label.
pub open spec fn row_label(i: int) -> Seq<u32> {
    chars(super::data::label_start_at(i) as int, super::data::label_len_at(i) as nat)
}

/// Label row `i`'s encoding.
pub open spec fn row_encoding(i: int) -> Encoding {
    encoding_from_number(super::data::label_encoding_at(i) as int)
}

/// An encoding's name (§4.2: "Each encoding has one or more labels and a
/// name"), as the table gives it.
pub open spec fn name(e: Encoding) -> Seq<u32> {
    chars(super::data::name_start_at(encoding_number(e) as int) as int, super::data::name_len_at(encoding_number(e) as int) as nat)
}

/// ASCII whitespace (Infra §4.6): U+0009 TAB, U+000A LF, U+000C FF, U+000D
/// CR, or U+0020 SPACE.
pub open spec fn is_ascii_whitespace(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// The position of the first code point of `s` at or after `i` that is not
/// ASCII whitespace, or `s.len()`.
pub open spec fn skip_leading(s: Seq<u32>, i: nat) -> nat
    decreases s.len() - i,
{
    if i < s.len() && is_ascii_whitespace(s[i as int]) {
        skip_leading(s, i + 1)
    } else {
        i
    }
}

/// One past the last code point of `s` before `j` that is not ASCII
/// whitespace, or 0.
pub open spec fn skip_trailing(s: Seq<u32>, j: nat) -> nat
    decreases j,
{
    if j > 0 && j <= s.len() && is_ascii_whitespace(s[j - 1]) {
        skip_trailing(s, (j - 1) as nat)
    } else {
        j
    }
}

/// "Strip leading and trailing ASCII whitespace" (Infra §4.6): "remove any
/// ASCII whitespace from the start and end" of `s`.
pub open spec fn strip_leading_and_trailing_ascii_whitespace(s: Seq<u32>) -> Seq<u32> {
    let start = skip_leading(s, 0);
    let end = skip_trailing(s, s.len());
    if start < end {
        s.subrange(start as int, end as int)
    } else {
        seq![]
    }
}

/// ASCII lowercase of one code point (Infra §4.6: "replace all ASCII upper
/// alphas in the string with their corresponding code point in ASCII lower
/// alpha").
pub open spec fn ascii_lower(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A { (c + 0x20) as u32 } else { c }
}

/// "ASCII lowercase" (Infra §4.6) of a string.
pub open spec fn ascii_lowercase(s: Seq<u32>) -> Seq<u32> {
    s.map_values(|c: u32| ascii_lower(c))
}

/// "A string A is an ASCII case-insensitive match for a string B, if the
/// ASCII lowercase of A is the ASCII lowercase of B" (Infra §4.6).
pub open spec fn ascii_case_insensitive_match(a: Seq<u32>, b: Seq<u32>) -> bool {
    ascii_lowercase(a) == ascii_lowercase(b)
}

/// The first label row at or after `i` whose label `label` matches.
pub open spec fn first_match(label: Seq<u32>, i: nat) -> Option<nat>
    decreases label_count() - i,
{
    if i >= label_count() {
        None
    } else if ascii_case_insensitive_match(label, row_label(i as int)) {
        Some(i)
    } else {
        first_match(label, i + 1)
    }
}

/// "Get an encoding" (§4.2, <https://encoding.spec.whatwg.org/#concept-encoding-get>)
/// from the string `label`. `None` is failure.
pub open spec fn get_an_encoding(label: Seq<u32>) -> Option<Encoding> {
    // 1. "Remove any leading and trailing ASCII whitespace from label."
    let label = strip_leading_and_trailing_ascii_whitespace(label);
    // 2. "If label is an ASCII case-insensitive match for any of the labels
    //    listed in the table below, then return the corresponding encoding;
    //    otherwise return failure."
    match first_match(label, 0) {
        Some(i) => Some(row_encoding(i as int)),
        None => None,
    }
}

} // verus!

//! The byte-level `trim_str_whitespace` against `str::trim_matches` with
//! `is_str_whitespace`, for every Unicode scalar value at the start, at the
//! end, alone and doubled, and for the digit-radix helper's callers.

use clazel_js_number::parse::{is_str_whitespace, string_to_number, trim_str_whitespace};

fn same(s: &str) {
    let want = s.trim_matches(is_str_whitespace).as_bytes();
    assert_eq!(trim_str_whitespace(s.as_bytes()), want, "trim of {s:?}");
}

#[test]
fn trim_matches_str_trim_for_every_scalar() {
    let step = if cfg!(miri) { 4099 } else { 1 };
    let mut cp: u32 = 0;
    while cp <= 0x0010_FFFF {
        if let Some(c) = char::from_u32(cp) {
            same(&c.to_string());
            same(&format!("{c}{c}"));
            same(&format!("{c}1"));
            same(&format!("1{c}"));
            same(&format!("{c}1{c}"));
            same(&format!(" {c} 12.5{c}\t{c}"));
        }
        cp = cp.saturating_add(step);
    }
    same("");
    same("\u{2028}\u{2029}\u{FEFF}\u{A0}\u{3000}x\u{1680}\u{200A}");
}

#[test]
fn whitespace_set_is_what_the_spec_lists() {
    for s in [
        "\u{9}7",
        "\u{A}7",
        "\u{B}7",
        "\u{C}7",
        "\u{D}7",
        " 7",
        "\u{A0}7",
        "\u{1680}7",
        "\u{2000}7",
        "\u{200A}7",
        "\u{2028}7",
        "\u{2029}7",
        "\u{202F}7",
        "\u{205F}7",
        "\u{3000}7",
        "\u{FEFF}7",
        "7\u{3000}",
    ] {
        assert!(string_to_number(s).to_bits() == 7f64.to_bits(), "{s:?}");
    }
    // Not whitespace: ZWSP (U+200B), the Mongolian vowel separator, NEL.
    for s in ["\u{200B}7", "\u{180E}7", "\u{85}7", "7\u{200B}"] {
        assert!(string_to_number(s).is_nan(), "{s:?}");
    }
}

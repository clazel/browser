//! The serializer's escaping, against CSSOM §2.1 "serialize an identifier" and "serialize a
//! string", on selectors built by hand (so that the parser is not in the loop), and its
//! hand-copied table of non-ASCII ident code points against the one in CSS Syntax and
//! against `clazel-css`'s tokenizer.
//!
//! CSSOM "serialize an identifier", for each character of the identifier, in order:
//! 1. U+0000: U+FFFD.
//! 2. U+0001 to U+001F, or U+007F: "escaped as code point", which is `\`, the code point in
//!    lowercase hexadecimal with no leading zeros, and a space.
//! 3. The first character, 0 to 9: escaped as code point.
//! 4. The second character, 0 to 9, when the first is `-`: escaped as code point.
//! 5. The first character, `-`, with no second character: `\-`.
//! 6. A non-ASCII ident code point, `-`, `_`, 0 to 9, A to Z, a to z: the character itself.
//! 7. Otherwise `\` and the character.
//!
//! "Serialize a string": `"`, then for each character: U+0000 as U+FFFD; U+0001 to U+001F and
//! U+007F escaped as code point; `"` and `\` as `\` and themselves; else itself; then `"`.

use clazel_css::tokenizer::exec::{ExecToken, tokenize_all};
use clazel_selectors::exec_serialize::serialize;
use clazel_selectors::exec_types::{
    ExecAttrTest, ExecComplex, ExecRange, ExecSelectors, ExecSimple,
};
use clazel_selectors::spec::{AttrMatcher, CaseFlag, NsPrefix};

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// A selector of one simple selector.
fn single(simple: ExecSimple) -> ExecSelectors {
    ExecSelectors {
        simples: vec![simple],
        compounds: vec![ExecRange { lo: 0, hi: 1 }],
        combinators: vec![],
        complexes: vec![ExecComplex {
            compounds: ExecRange { lo: 0, hi: 1 },
            combinators: ExecRange { lo: 0, hi: 0 },
        }],
        lists: vec![ExecRange { lo: 0, hi: 1 }],
    }
}

/// `.name` serialized, without the dot.
fn ident(name: &[u32]) -> Vec<u32> {
    let out = serialize(&single(ExecSimple::Class {
        name: name.to_vec(),
    }));
    assert_eq!(
        out.first(),
        Some(&0x2E),
        "the class selector starts with a dot"
    );
    out.get(1..).expect("a dot").to_vec()
}

/// `[a=value]` serialized, between `[a=` and `]`.
fn string(value: &[u32]) -> Vec<u32> {
    let out = serialize(&single(ExecSimple::Attribute {
        ns: NsPrefix::Absent,
        name: cps("a"),
        test: Some(ExecAttrTest {
            matcher: AttrMatcher::Equals,
            value: value.to_vec(),
            flag: None,
        }),
    }));
    let want_head = cps("[a=");
    assert_eq!(out.get(..3), Some(want_head.as_slice()));
    assert_eq!(out.last(), Some(&0x5D));
    out.get(3..out.len() - 1).expect("brackets").to_vec()
}

fn text(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

#[test]
fn identifiers_are_escaped_as_cssom_says() {
    // (identifier, serialization): the rule of the module comment that gives it.
    let cases: &[(&str, &str)] = &[
        ("a", "a"),
        ("Abc-def_9", "Abc-def_9"),
        ("_x", "_x"),
        ("-x", "-x"),
        ("--", "--"),
        ("--1", "--1"),
        ("-_", "-_"),
        // 3: a digit first.
        ("1a", "\\31 a"),
        ("0", "\\30 "),
        ("9z", "\\39 z"),
        ("123", "\\31 23"),
        // A digit later is itself.
        ("a1", "a1"),
        ("a-1", "a-1"),
        // 4: a digit second, after `-`.
        ("-1", "-\\31 "),
        ("-9a", "-\\39 a"),
        ("-123", "-\\31 23"),
        // ... but only second, and only after `-`.
        ("-a1", "-a1"),
        ("_1", "_1"),
        // 5: a lone `-`, then escaped; with more after it, plain.
        ("-", "\\-"),
        ("-a", "-a"),
        // 2: controls and DEL as code points, lowercase hex without leading zeros.
        ("\u{1}", "\\1 "),
        ("a\u{1}b", "a\\1 b"),
        ("\u{9}", "\\9 "),
        ("\u{a}", "\\a "),
        ("\u{1b}x", "\\1b x"),
        ("a\u{1f}", "a\\1f "),
        ("\u{7f}", "\\7f "),
        ("x\u{7f}y", "x\\7f y"),
        // 1: NUL as U+FFFD.
        ("\u{0}", "\u{fffd}"),
        ("a\u{0}b", "a\u{fffd}b"),
        // 6: non-ASCII ident code points as themselves.
        ("\u{e9}", "\u{e9}"),
        ("\u{b7}", "\u{b7}"),
        ("\u{65e5}\u{672c}", "\u{65e5}\u{672c}"),
        ("\u{1f600}", "\u{1f600}"),
        ("a\u{200c}b", "a\u{200c}b"),
        // 7: anything else is escaped as the character, ASCII punctuation and white space...
        ("a b", "a\\ b"),
        (" ", "\\ "),
        ("a.b", "a\\.b"),
        ("a#b", "a\\#b"),
        ("a:b", "a\\:b"),
        ("a\\b", "a\\\\b"),
        ("a\"b", "a\\\"b"),
        ("a'b", "a\\'b"),
        ("a(b)", "a\\(b\\)"),
        ("a/b", "a\\/b"),
        ("a@b", "a\\@b"),
        ("!", "\\!"),
        ("~", "\\~"),
        ("a\u{7e}", "a\\~"),
        // ... and non-ASCII that is not an ident code point (not a code point escape).
        ("\u{80}", "\\\u{80}"),
        ("\u{b6}", "\\\u{b6}"),
        ("\u{d7}", "\\\u{d7}"),
        ("\u{f7}", "\\\u{f7}"),
        ("a\u{2028}", "a\\\u{2028}"),
        ("\u{e000}", "\\\u{e000}"),
        // The empty identifier.
        ("", ""),
    ];
    let mut wrong: Vec<String> = Vec::new();
    for (input, expected) in cases {
        let got = text(&ident(&cps(input)));
        if got != *expected {
            wrong.push(format!("{input:?}: got {got:?}, expected {expected:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn every_name_position_uses_the_identifier_rules() {
    // The identifier rules apply to a type, an ID, a class and an attribute name alike.
    let none = NsPrefix::Absent;
    let type_ = serialize(&single(ExecSimple::Type {
        ns: none,
        name: cps("1 a"),
    }));
    assert_eq!(text(&type_), "\\31 \\ a");
    let id = serialize(&single(ExecSimple::Id { name: cps("-1") }));
    assert_eq!(text(&id), "#-\\31 ");
    let attr = serialize(&single(ExecSimple::Attribute {
        ns: NsPrefix::Any,
        name: cps("a b"),
        test: None,
    }));
    assert_eq!(text(&attr), "[*|a\\ b]");
}

#[test]
fn strings_are_escaped_as_cssom_says() {
    let cases: &[(&str, &str)] = &[
        ("", "\"\""),
        ("b", "\"b\""),
        ("b c", "\"b c\""),
        // `"` and `\` are escaped as the character.
        ("a\"b", "\"a\\\"b\""),
        ("a\\b", "\"a\\\\b\""),
        ("\"", "\"\\\"\""),
        ("\\", "\"\\\\\""),
        // `'` is itself.
        ("a'b", "\"a'b\""),
        // NUL is U+FFFD.
        ("a\u{0}b", "\"a\u{fffd}b\""),
        // Controls and DEL as code points, lowercase hex, a trailing space.
        ("\u{1}", "\"\\1 \""),
        ("a\u{9}b", "\"a\\9 b\""),
        ("a\u{a}b", "\"a\\a b\""),
        ("\u{d}", "\"\\d \""),
        ("\u{1b}", "\"\\1b \""),
        ("\u{1f}", "\"\\1f \""),
        ("\u{7f}", "\"\\7f \""),
        // U+0020 and U+0080 are not controls here.
        (" ", "\" \""),
        ("\u{80}", "\"\u{80}\""),
        ("\u{9f}", "\"\u{9f}\""),
        // Digits, `-` and punctuation are themselves, unlike in an identifier.
        ("1-2.3:4", "\"1-2.3:4\""),
        ("\u{e9}\u{1f600}", "\"\u{e9}\u{1f600}\""),
    ];
    let mut wrong: Vec<String> = Vec::new();
    for (input, expected) in cases {
        let got = text(&string(&cps(input)));
        if got != *expected {
            wrong.push(format!("{input:?}: got {got:?}, expected {expected:?}"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn attribute_flags_and_matchers_are_written_out() {
    // The serialization of an attribute selector is `[` name matcher string flag `]`, with
    // `i` and `s` after a space (CSSOM §6.7.2; the `s` flag as spec.rs notes).
    let matchers = [
        (AttrMatcher::Equals, "="),
        (AttrMatcher::Includes, "~="),
        (AttrMatcher::DashMatch, "|="),
        (AttrMatcher::Prefix, "^="),
        (AttrMatcher::Suffix, "$="),
        (AttrMatcher::Substring, "*="),
    ];
    let flags = [
        (None, ""),
        (Some(CaseFlag::I), " i"),
        (Some(CaseFlag::S), " s"),
    ];
    for (m, mt) in matchers {
        for (f, ft) in flags {
            let out = serialize(&single(ExecSimple::Attribute {
                ns: NsPrefix::Absent,
                name: cps("x"),
                test: Some(ExecAttrTest {
                    matcher: m,
                    value: cps("v"),
                    flag: f,
                }),
            }));
            assert_eq!(text(&out), format!("[x{mt}\"v\"{ft}]"));
        }
    }
}

// ------------------------------------------------------------------------------------
// The table of non-ASCII ident code points
// ------------------------------------------------------------------------------------

/// CSS Syntax Level 3 §4.2 "non-ASCII ident code point", as the standard lists them (the
/// last range is "greater than or equal to U+10000"; the UA's tokenizer stops at U+10FFFF,
/// the last code point).
const NON_ASCII_IDENT: &[(u32, u32)] = &[
    (0xB7, 0xB7),
    (0xC0, 0xD6),
    (0xD8, 0xF6),
    (0xF8, 0x37D),
    (0x37F, 0x1FFF),
    (0x200C, 0x200D),
    (0x203F, 0x2040),
    (0x2070, 0x218F),
    (0x2C00, 0x2FEF),
    (0x3001, 0xD7FF),
    (0xF900, 0xFDCF),
    (0xFDF0, 0xFFFD),
    (0x1_0000, 0x10_FFFF),
];

fn in_standard_table(c: u32) -> bool {
    NON_ASCII_IDENT
        .iter()
        .any(|&(lo, hi)| (lo..=hi).contains(&c))
}

/// True if the serializer leaves `c` as it is where an identifier continues (index 1 of
/// `a`+`c`), false if it escapes it.
fn serializer_keeps(c: u32) -> bool {
    let out = ident(&[0x61, c]);
    if out == [0x61, c] {
        true
    } else {
        assert_eq!(
            out,
            [0x61, 0x5C, c],
            "U+{c:04X} is kept or escaped as the character"
        );
        false
    }
}

/// True if the tokenizer reads `c` as an ident code point after `a`, and as an ident-start
/// one at the start: one ident token holding both.
fn tokenizer_reads_ident(c: u32) -> bool {
    let start = tokenize_all(&[c]);
    let starts = matches!(start.first(), Some(ExecToken::Ident { value }) if value == &[c]);
    let cont = tokenize_all(&[0x61, c]);
    let continues = matches!(cont.first(), Some(ExecToken::Ident { value }) if value == &[0x61, c]);
    // Every non-ASCII ident code point is an ident-start code point too (§4.2).
    assert_eq!(starts, continues, "U+{c:04X}: start and continue differ");
    starts
}

#[test]
fn the_range_table_agrees_with_the_standard_and_the_tokenizer_at_every_boundary() {
    let mut points: Vec<u32> = Vec::new();
    for &(lo, hi) in NON_ASCII_IDENT {
        for edge in [lo, hi] {
            for d in [-2i64, -1, 0, 1, 2] {
                let c = i64::from(edge) + d;
                if (0x80..=0x10_FFFF).contains(&c) {
                    points.push(u32::try_from(c).expect("in range"));
                }
            }
        }
    }
    // The surrogates are not code points; the ends of the range around them are.
    points.retain(|c| !(0xD800..=0xDFFF).contains(c));
    // Every code point of the C1 and Latin-1 blocks, where the table is the most broken up.
    points.extend(0x80..=0x100);
    points.sort_unstable();
    points.dedup();
    let mut wrong: Vec<String> = Vec::new();
    for c in points {
        let table = in_standard_table(c);
        let ser = serializer_keeps(c);
        let tok = tokenizer_reads_ident(c);
        if !(table == ser && ser == tok) {
            wrong.push(format!(
                "U+{c:04X}: standard {table}, serializer {ser}, tokenizer {tok}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

#[test]
fn the_range_table_agrees_with_the_standard_on_every_code_point() {
    // Under Miri a stride of the code points, to finish in about a minute
    // (docs/VERIFICATION.md): the boundary test above takes the same code path at each edge.
    let stride: u32 = if cfg!(miri) { 4099 } else { 1 };
    let mut c = 0x80u32;
    let mut wrong: Vec<String> = Vec::new();
    while c <= 0x10_FFFF {
        if !(0xD800..=0xDFFF).contains(&c) && serializer_keeps(c) != in_standard_table(c) {
            wrong.push(format!("U+{c:04X}"));
        }
        c = c.saturating_add(stride);
    }
    assert!(wrong.is_empty(), "{}", wrong.join(" "));
    // ASCII: only letters, digits, `-` and `_` stay (digits and `-` also have rules by position,
    // tested above); every other printable ASCII character is escaped as itself.
    for c in 0x21u32..0x7F {
        let kept = (0x30..=0x39).contains(&c)
            || (0x41..=0x5A).contains(&c)
            || (0x61..=0x7A).contains(&c)
            || c == 0x2D
            || c == 0x5F;
        assert_eq!(serializer_keeps(c), kept, "U+{c:04X}");
    }
}

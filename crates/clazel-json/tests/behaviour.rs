//! Behaviour of the executable parser and quoter on concrete texts. The
//! proofs say they equal `spec.rs`; these tests are a check of the spec
//! itself against what JSON texts are known to mean, until the conformance
//! suites (JSONTestSuite, Test262's `built-ins/JSON`) are vendored.

use clazel_json::parse::parse;
use clazel_json::quote::quote;
use clazel_json::tree::Json;

/// A size for a stress test: under Miri, which interprets every step, one
/// hundredth of it (the full sizes run in the normal test job).
fn scaled(n: usize) -> usize {
    if cfg!(miri) { n / 100 } else { n }
}

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// A JSON string value as the code points `JSON.parse` would be given.
fn code_points(units: &[u16]) -> Vec<u32> {
    char::decode_utf16(units.iter().copied())
        .map(|r| match r {
            Ok(c) => u32::from(c),
            Err(e) => u32::from(e.unpaired_surrogate()),
        })
        .collect()
}

fn units_text(units: &[u16]) -> String {
    String::from_utf16_lossy(&quote(units))
}

/// The value as compact JSON text, strings through `quote`, numbers as
/// their source text.
fn render(j: &Json) -> String {
    match j {
        Json::Null => "null".to_string(),
        Json::Bool(b) => b.to_string(),
        Json::Number(t) => t
            .iter()
            .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect(),
        Json::String(u) => units_text(u),
        Json::Array(items) => {
            let parts: Vec<String> = items.iter().map(render).collect();
            format!("[{}]", parts.join(","))
        }
        Json::Object(members) => {
            let parts: Vec<String> = members
                .iter()
                .map(|m| format!("{}:{}", units_text(&m.key), render(&m.value)))
                .collect();
            format!("{{{}}}", parts.join(","))
        }
    }
}

fn parsed(text: &str) -> Option<String> {
    parse(&scalars(text)).map(|j| render(&j))
}

#[test]
fn valid_texts() {
    let cases: &[(&str, &str)] = &[
        ("null", "null"),
        (" \t\r\ntrue \n", "true"),
        ("false", "false"),
        ("0", "0"),
        ("-0", "-0"),
        ("-12.5e+3", "-12.5e+3"),
        ("1E-2", "1E-2"),
        ("[]", "[]"),
        ("[ ]", "[]"),
        ("{}", "{}"),
        ("{ }", "{}"),
        ("[1, 2 ,3]", "[1,2,3]"),
        ("[[],[[]],{}]", "[[],[[]],{}]"),
        (
            r#"{"a":1,"b":[true,null],"a":2}"#,
            r#"{"a":1,"b":[true,null],"a":2}"#,
        ),
        (r#"{ "a" : { "b" : "c" } }"#, r#"{"a":{"b":"c"}}"#),
        (r#""""#, r#""""#),
        (r#""a\/b""#, r#""a/b""#),
        (r#""\u00e9\u00E9""#, "\"\u{e9}\u{e9}\""),
        (r#""\ud83d\ude00""#, "\"\u{1f600}\""),
        (r#""\ud800""#, r#""\ud800""#),
        ("\"\u{1f600}\"", "\"\u{1f600}\""),
        ("\"\u{7f}\u{80}\"", "\"\u{7f}\u{80}\""),
    ];
    for (text, want) in cases {
        assert_eq!(parsed(text).as_deref(), Some(*want), "{text:?}");
    }
}

#[test]
fn invalid_texts() {
    let cases: &[&str] = &[
        "",
        " ",
        "nul",
        "nulll",
        "True",
        "01",
        "-",
        "+1",
        ".5",
        "1.",
        "1e",
        "1e+",
        "0x10",
        "1 2",
        "[",
        "[1,]",
        "[,1]",
        "[1 2]",
        "]",
        "{",
        "{,}",
        r#"{"a"}"#,
        r#"{"a":}"#,
        r#"{"a":1,}"#,
        r#"{a:1}"#,
        r#"{"a" 1}"#,
        "'a'",
        r#""a"#,
        "\"a\nb\"",
        "\"\u{1f}\"",
        r#""\x""#,
        r#""\u12""#,
        r#""\u12G4""#,
        r#""\"#,
        "\u{c}1",
        "\u{b}1",
        "\u{feff}1",
        "\u{a0}1",
    ];
    for text in cases {
        assert_eq!(parsed(text), None, "{text:?}");
    }
}

#[test]
fn a_value_above_the_code_point_range_is_an_error() {
    assert!(parse(&[0x22, 0x110000, 0x22]).is_none());
    assert!(parse(&[0x31, 0x110000]).is_none());
}

#[test]
fn nesting_is_bounded() {
    let nested = |depth: usize, open: &str, close: &str| {
        let mut t = String::new();
        for _ in 0..depth {
            t.push_str(open);
        }
        t.push('1');
        for _ in 0..depth {
            t.push_str(close);
        }
        t
    };
    assert!(parsed(&nested(512, "[", "]")).is_some());
    assert!(parsed(&nested(513, "[", "]")).is_none());
    assert!(parsed(&nested(512, r#"{"a":"#, "}")).is_some());
    assert!(parsed(&nested(513, r#"{"a":"#, "}")).is_none());
    // A text far past the bound is refused without deep recursion.
    assert!(parsed(&"[".repeat(scaled(1_000_000))).is_none());
}

#[test]
fn long_texts() {
    let mut array = String::from("[");
    let mut object = String::from("{");
    for i in 0..scaled(100_000) {
        if i > 0 {
            array.push(',');
            object.push(',');
        }
        array.push_str(&i.to_string());
        object.push_str(&format!("\"k{i}\":{i}"));
    }
    array.push(']');
    object.push('}');
    assert_eq!(parsed(&array).as_deref(), Some(array.as_str()));
    assert_eq!(parsed(&object).as_deref(), Some(object.as_str()));
    let long = format!("\"{}\"", "x".repeat(scaled(1_000_000)));
    assert_eq!(parsed(&long).as_deref(), Some(long.as_str()));
}

#[test]
fn quoting() {
    let cases: &[(&[u16], &str)] = &[
        (&[], "\"\""),
        (&[0x61, 0x22, 0x5C], "\"a\\\"\\\\\""),
        (&[0x08, 0x09, 0x0A, 0x0C, 0x0D], "\"\\b\\t\\n\\f\\r\""),
        (&[0x00, 0x1F], "\"\\u0000\\u001f\""),
        (&[0x7F, 0x2F], "\"\u{7f}/\""),
        (&[0xD83D, 0xDE00], "\"\u{1f600}\""),
        (&[0xD83D], "\"\\ud83d\""),
        (&[0xDE00], "\"\\ude00\""),
        (&[0xDE00, 0xD83D], "\"\\ude00\\ud83d\""),
        (&[0xD83D, 0x61], "\"\\ud83da\""),
    ];
    for (units, want) in cases {
        let got = String::from_utf16_lossy(&quote(units));
        assert_eq!(&got, want, "{units:04x?}");
    }
}

/// `JSON.parse(JSON.stringify(s))` is `s`: for random strings, lone
/// surrogates and pairs included, the quoted form parses back to them.
#[test]
fn quote_then_parse_is_identity() {
    let mut state: u64 = 0x2545_F491_4F6C_DD1D;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..scaled(20_000) {
        let len = (next() % 12) as usize;
        let units: Vec<u16> = (0..len)
            .map(|_| match next() % 6 {
                0 => (next() % 0x20) as u16,
                1 => 0xD800 + (next() % 0x800) as u16,
                2 => [0x22, 0x5C, 0x2F]
                    .get((next() % 3) as usize)
                    .copied()
                    .unwrap_or(0x22),
                3 => 0xD800 + (next() % 0x400) as u16,
                4 => 0xDC00 + (next() % 0x400) as u16,
                _ => (next() % 0xD000) as u16,
            })
            .collect();
        let text = code_points(&quote(&units));
        let back = match parse(&text) {
            Some(Json::String(u)) => Some(u),
            _ => None,
        };
        assert_eq!(back.as_ref(), Some(&units), "{units:04x?}");
    }
}

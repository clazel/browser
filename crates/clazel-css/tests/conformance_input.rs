//! The input byte stream against the outside world (phase-5.md items 5.2 and 5.4).
//!
//! The proofs show the code equals `input/spec.rs`. This file checks both against
//! `css-parsing-tests`' `stylesheet_bytes.json`, which neither was written from. Each of
//! its results is a list of rules and the name of the encoding used. The rules need the
//! parser (item 5.4), so only the encoding is compared here.

use clazel_css::input::exec::{decode_stylesheet, fallback_encoding};
use clazel_encoding::hooks::decode::bom_sniff;
use clazel_encoding::labels::exec::{get_an_encoding, name};
use clazel_encoding::labels::spec::Encoding;
use syntax::Json;

/// The `css-parsing-tests` table.
mod syntax {
    use Json::{Bool, List, Null, Num, Obj, Str};

    /// A value of the suite's JSON, as the converter wrote it.
    #[derive(Debug, PartialEq)]
    pub enum Json {
        Null,
        Bool(bool),
        Num(&'static str),
        Str(&'static str),
        List(&'static [Json]),
        Obj(&'static [(&'static str, Json)]),
    }

    /// One case.
    pub struct Case {
        pub file: &'static str,
        pub index: usize,
        pub input: Json,
        pub expected: Json,
    }

    include!("generated/css_parsing_tests.rs");

    /// The table.
    pub fn cases() -> &'static [Case] {
        CASES
    }
}

/// The string under `key`, if the input has one that is not null.
fn field(input: &Json, key: &str) -> Option<&'static str> {
    let Json::Obj(fields) = input else {
        return None;
    };
    fields.iter().find_map(|(k, v)| match v {
        Json::Str(s) if *k == key => Some(*s),
        _ => None,
    })
}

/// The suite writes bytes as a string of the code points of their values.
fn bytes(text: &str) -> Vec<u8> {
    text.chars()
        .map(|c| u8::try_from(u32::from(c)).unwrap_or(0))
        .collect()
}

fn code_points(text: &str) -> Vec<u32> {
    text.chars().map(u32::from).collect()
}

/// The encoding "decode" uses, and whether it could decode with it. "Decode" takes a byte
/// order mark over the fallback, so that is the encoding the suite names.
fn used(input: &Json) -> (Encoding, bool) {
    let sheet = bytes(field(input, "css_bytes").unwrap_or_default());
    let protocol = field(input, "protocol_encoding").map(code_points);
    let environment =
        field(input, "environment_encoding").and_then(|l| get_an_encoding(&code_points(l)));
    let fallback = fallback_encoding(&sheet, protocol.as_deref(), environment);
    let decoded = decode_stylesheet(&sheet, protocol.as_deref(), environment);
    (bom_sniff(&sheet).unwrap_or(fallback), decoded.is_some())
}

#[test]
fn stylesheet_bytes_encodings() {
    let (mut pass, mut fail, mut total) = (0usize, 0usize, 0usize);
    for case in syntax::cases()
        .iter()
        .filter(|c| c.file == "stylesheet_bytes.json")
    {
        total = total.saturating_add(1);
        let (encoding, decoded) = used(&case.input);
        let expected = match case.expected {
            Json::List([_, Json::Str(expected)]) => Some(*expected),
            _ => None,
        };
        let actual = name(encoding);
        if decoded && expected.is_some_and(|e| actual.eq_ignore_ascii_case(e.as_bytes())) {
            pass = pass.saturating_add(1);
        } else {
            println!(
                "FAILED stylesheet_bytes.json {}: {encoding:?} against {expected:?}",
                case.index
            );
            fail = fail.saturating_add(1);
        }
    }
    println!(
        "clazel-conformance: suite=\"css-parsing-tests stylesheet_bytes encodings\" pass={pass} xfail=0 fail={fail} total={total}"
    );
    assert_eq!(fail, 0);
    assert_eq!(total, 28);
}

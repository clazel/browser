//! `css-parsing-tests`, as vendored in `servo/rust-cssparser`: CSS Syntax cases,
//! as a table of (file, index in the file, input, expected result).
//!
//! Each file is a JSON array of input and expected result, in turn. There are no
//! `clazel-css` types yet (phase-5.md item 5.2), so the table keeps the values as
//! they are, and the conformance test maps them. Every value is checked here
//! against the suite's README, with the three differences listed in `SOURCE.md`, so
//! a changed upstream file fails the conversion instead of being half-read.

use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "An+B.json",
    "component_value_list.json",
    "declaration_list.json",
    "one_component_value.json",
    "one_declaration.json",
    "one_rule.json",
    "rule_list.json",
    "stylesheet.json",
    "stylesheet_bytes.json",
    "urange.json",
];

/// The tokens written as a string of more than one character.
const LONG_TOKENS: &[&str] = &["~=", "|=", "^=", "$=", "*=", "<!--", "-->"];

/// What may follow `"error"`.
const ERRORS: &[&str] = &[
    "bad-string",
    "bad-url",
    ")",
    "]",
    "}",
    "empty",
    "extra-input",
    "invalid",
];

/// `"integer"` or `"number"`, the type flag of a numeric token.
fn is_type_flag(s: &str) -> bool {
    s == "integer" || s == "number"
}

/// A component value, or an error in its place.
fn check_value(v: &Value) -> Result<(), String> {
    let bad = || Err(format!("not a component value: {v}"));
    match v {
        Value::String(s) if s.chars().count() == 1 || LONG_TOKENS.contains(&s.as_str()) => Ok(()),
        Value::Array(items) => {
            let [Value::String(head), rest @ ..] = items.as_slice() else {
                return bad();
            };
            match (head.as_str(), rest) {
                ("ident" | "at-keyword" | "string" | "url", [Value::String(_)]) => Ok(()),
                ("hash", [Value::String(_), Value::String(t)])
                    if t == "id" || t == "unrestricted" =>
                {
                    Ok(())
                }
                (
                    "number" | "percentage",
                    [Value::String(_), Value::Number(_), Value::String(t)],
                ) if is_type_flag(t) => Ok(()),
                (
                    "dimension",
                    [
                        Value::String(_),
                        Value::Number(_),
                        Value::String(t),
                        Value::String(_),
                    ],
                ) if is_type_flag(t) => Ok(()),
                ("{}" | "[]" | "()", body) => body.iter().try_for_each(check_value),
                ("function", [Value::String(_), body @ ..]) => {
                    body.iter().try_for_each(check_value)
                }
                ("error", [Value::String(e)]) if ERRORS.contains(&e.as_str()) => Ok(()),
                _ => bad(),
            }
        }
        _ => bad(),
    }
}

/// A JSON array, each item of which passes `check`.
fn check_list(v: &Value, check: fn(&Value) -> Result<(), String>) -> Result<(), String> {
    v.as_array()
        .ok_or_else(|| format!("not an array: {v}"))?
        .iter()
        .try_for_each(check)
}

/// An array of component values.
fn check_values(v: &Value) -> Result<(), String> {
    check_list(v, check_value)
}

fn is_error(v: &Value) -> bool {
    matches!(v.as_array().map(Vec::as_slice), Some([Value::String(h), _]) if h == "error")
        && check_value(v).is_ok()
}

fn is_at_rule(v: &Value) -> Result<bool, String> {
    let Some([Value::String(head), Value::String(_), prelude, block]) =
        v.as_array().map(Vec::as_slice)
    else {
        return Ok(false);
    };
    if head != "at-rule" {
        return Ok(false);
    }
    check_values(prelude)?;
    if !block.is_null() {
        check_values(block)?;
    }
    Ok(true)
}

/// A qualified rule or at-rule, or an error in its place.
fn check_rule(v: &Value) -> Result<(), String> {
    if is_error(v) || is_at_rule(v)? {
        return Ok(());
    }
    match v.as_array().map(Vec::as_slice) {
        Some([Value::String(head), prelude, block]) if head == "qualified rule" => {
            check_values(prelude)?;
            check_values(block)
        }
        _ => Err(format!("not a rule: {v}")),
    }
}

/// A declaration, or an error in its place.
fn check_declaration(v: &Value) -> Result<(), String> {
    if is_error(v) {
        return Ok(());
    }
    match v.as_array().map(Vec::as_slice) {
        Some([Value::String(head), Value::String(_), value, Value::Bool(_)])
            if head == "declaration" =>
        {
            check_values(value)
        }
        _ => Err(format!("not a declaration: {v}")),
    }
}

/// A declaration or rule, or an error in its place. The README allows no qualified
/// rule here, but the file has one (`SOURCE.md`).
fn check_list_item(v: &Value) -> Result<(), String> {
    check_declaration(v).or_else(|_| check_rule(v))
}

/// `null`, or two integers.
fn check_pair(v: &Value) -> Result<(), String> {
    match v {
        Value::Null => Ok(()),
        Value::Array(items) => match items.as_slice() {
            [a, b] if a.is_i64() && b.is_i64() => Ok(()),
            _ => Err(format!("not two integers: {v}")),
        },
        _ => Err(format!("neither null nor two integers: {v}")),
    }
}

/// `stylesheet_bytes.json`'s result: the rules, then the encoding's name.
fn check_rules_and_encoding(v: &Value) -> Result<(), String> {
    match v.as_array().map(Vec::as_slice) {
        Some([rules, Value::String(_)]) => check_list(rules, check_rule),
        _ => Err(format!("not [rules, encoding]: {v}")),
    }
}

/// `stylesheet_bytes.json`'s input: `css_bytes`, whose code points are bytes, and
/// the optional labels and comment.
fn check_bytes_input(v: &Value) -> Result<(), String> {
    let fields = v.as_object().ok_or_else(|| format!("not an object: {v}"))?;
    let bytes = fields
        .get("css_bytes")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("no css_bytes string: {v}"))?;
    if let Some(c) = bytes.chars().find(|&c| u32::from(c) > 0xFF) {
        return Err(format!("U+{:04X} in css_bytes is not a byte", u32::from(c)));
    }
    for (key, field) in fields {
        let known = match key.as_str() {
            "css_bytes" => true,
            "comment" => field.is_string(),
            "protocol_encoding" | "environment_encoding" => field.is_string() || field.is_null(),
            _ => false,
        };
        if !known {
            return Err(format!("field {key}: {field}"));
        }
    }
    Ok(())
}

/// Check one case of the file called `name`.
fn check_case(name: &str, input: &Value, expected: &Value) -> Result<(), String> {
    if name == "stylesheet_bytes.json" {
        check_bytes_input(input)?;
        return check_rules_and_encoding(expected);
    }
    if !input.is_string() {
        return Err(format!("input is not a string: {input}"));
    }
    match name {
        "An+B.json" => check_pair(expected),
        "component_value_list.json" => check_values(expected),
        "declaration_list.json" => check_list(expected, check_list_item),
        "one_component_value.json" => check_value(expected),
        "one_declaration.json" => check_declaration(expected),
        "one_rule.json" => check_rule(expected),
        "rule_list.json" | "stylesheet.json" => check_list(expected, check_rule),
        "urange.json" => check_list(expected, check_pair),
        _ => Err(format!("no rule for {name}")),
    }
}

/// `v` as a Rust expression over the test's `Json` type.
fn write_value(out: &mut String, v: &Value) -> Result<(), String> {
    let quoted = |s: &str| s.escape_default().to_string();
    match v {
        Value::Null => out.push_str("Null"),
        Value::Bool(b) => write!(out, "Bool({b})").map_err(|e| e.to_string())?,
        Value::Number(n) => write!(out, "Num(\"{n}\")").map_err(|e| e.to_string())?,
        Value::String(s) => write!(out, "Str(\"{}\")", quoted(s)).map_err(|e| e.to_string())?,
        Value::Array(items) => {
            out.push_str("List(&[");
            for (k, item) in items.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                write_value(out, item)?;
            }
            out.push_str("])");
        }
        Value::Object(fields) => {
            out.push_str("Obj(&[");
            for (k, (key, field)) in fields.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                write!(out, "(\"{}\", ", quoted(key)).map_err(|e| e.to_string())?;
                write_value(out, field)?;
                out.push(')');
            }
            out.push_str("])");
        }
    }
    Ok(())
}

pub fn convert(dir: &Path) -> Result<String, String> {
    let mut out = String::from(
        "// @generated by `cargo xtask testdata` from tests/data/css-parsing-tests/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/css_parsing_tests.rs) produces.\n\
         // Source, commit and license: tests/data/css-parsing-tests/SOURCE.md.\n\
         const CASES: &[Case] = &[\n",
    );
    for name in FILES {
        let text = std::fs::read_to_string(dir.join(name)).map_err(|e| format!("{name}: {e}"))?;
        let rows: Value = serde_json::from_str(&text).map_err(|e| format!("{name}: {e}"))?;
        let rows = rows
            .as_array()
            .ok_or_else(|| format!("{name}: not a JSON array"))?;
        let (pairs, rest) = rows.as_chunks::<2>();
        if !rest.is_empty() {
            return Err(format!("{name}: an input with no expected result"));
        }
        for (index, [input, expected]) in pairs.iter().enumerate() {
            check_case(name, input, expected).map_err(|e| format!("{name}: case {index}: {e}"))?;
            write!(out, "    Case {{ file: \"{name}\", index: {index}, input: ")
                .map_err(|e| e.to_string())?;
            write_value(&mut out, input)?;
            out.push_str(", expected: ");
            write_value(&mut out, expected)?;
            out.push_str(" },\n");
        }
    }
    out.push_str("];\n");
    Ok(out)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::{check_case, check_value, write_value};

    #[test]
    fn values_are_checked_against_the_grammar() {
        assert!(check_value(&json!(" ")).is_ok());
        assert!(check_value(&json!("-->")).is_ok());
        assert!(check_value(&json!(["ident", "red"])).is_ok());
        assert!(check_value(&json!(["hash", "a", "id"])).is_ok());
        assert!(check_value(&json!(["number", "1", 1, "integer"])).is_ok());
        assert!(check_value(&json!(["dimension", "1", 1, "number", "px"])).is_ok());
        assert!(check_value(&json!(["function", "f", ["ident", "a"], " "])).is_ok());
        assert!(check_value(&json!(["()", ["error", "bad-url"]])).is_ok());

        assert!(check_value(&json!("red")).is_err());
        assert!(check_value(&json!(["ident"])).is_err());
        assert!(check_value(&json!(["hash", "a", "other"])).is_err());
        assert!(check_value(&json!(["number", "1", "1", "integer"])).is_err());
        assert!(check_value(&json!(["unicode-range", 1, 2])).is_err());
        assert!(check_value(&json!(["error", "new-kind"])).is_err());
        assert!(check_value(&json!(["()", ["ident"]])).is_err());
    }

    #[test]
    fn each_file_has_its_own_result_shape() {
        let at_rule = json!(["at-rule", "a", [], null]);
        let qualified = json!(["qualified rule", [], []]);
        let declaration = json!(["declaration", "a", [], false]);
        let input = json!("x");
        for ok in [&at_rule, &qualified] {
            assert!(check_case("one_rule.json", &input, ok).is_ok());
        }
        assert!(check_case("one_rule.json", &input, &declaration).is_err());
        assert!(check_case("one_declaration.json", &input, &declaration).is_ok());
        assert!(check_case("one_declaration.json", &input, &at_rule).is_err());
        assert!(check_case("declaration_list.json", &input, &json!([at_rule])).is_ok());
        assert!(check_case("declaration_list.json", &input, &json!([qualified])).is_ok());
        assert!(check_case("declaration_list.json", &input, &json!(["a"])).is_err());
        assert!(check_case("An+B.json", &input, &json!([2, 1])).is_ok());
        assert!(check_case("An+B.json", &input, &json!(null)).is_ok());
        assert!(check_case("An+B.json", &input, &json!([2])).is_err());
        assert!(check_case("urange.json", &input, &json!([[1, 2], null])).is_ok());
        assert!(check_case("new.json", &input, &json!(null)).is_err());
    }

    #[test]
    fn bytes_inputs_are_bytes_with_known_fields() {
        let result = json!([[], "utf-8"]);
        let file = "stylesheet_bytes.json";
        assert!(check_case(file, &json!({"css_bytes": "\u{FF}"}), &result).is_ok());
        let labelled = json!({"css_bytes": "", "protocol_encoding": null, "comment": "c"});
        assert!(check_case(file, &labelled, &result).is_ok());
        assert!(check_case(file, &json!({"css_bytes": "\u{100}"}), &result).is_err());
        assert!(check_case(file, &json!({"css_bytes": "", "new": 1}), &result).is_err());
        assert!(check_case(file, &json!({}), &result).is_err());
        assert!(check_case(file, &json!({"css_bytes": ""}), &json!([])).is_err());
    }

    #[test]
    fn values_become_rust_literals() -> Result<(), String> {
        let mut out = String::new();
        write_value(&mut out, &json!(["a\"\n\u{e9}\u{0}", 1, 1.5, true, null]))?;
        assert_eq!(
            out,
            "List(&[Str(\"a\\\"\\n\\u{e9}\\u{0}\"), Num(\"1\"), Num(\"1.5\"), Bool(true), Null])"
        );
        Ok(())
    }
}

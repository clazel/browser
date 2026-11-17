//! Unit tests of the executable lexer: what [`next_input_element`] and
//! [`next_token`] return on small inputs, positive and negative, each the
//! result that ECMA-262 2026 §12 and Annex B.1.1 (as `src/spec.rs`
//! transcribes them) determine. These are evidence for the agreement with
//! the spec that is not proven (see `src/exec.rs`).

use clazel_js_lexer::api::{Element, Next, Step, Value};
use clazel_js_lexer::exec::{next_input_element, next_token};
use clazel_js_lexer::spec::{ElementKind, Goal, LexError, TemplateKind};

const DIV: Goal = Goal::InputElementDiv;
const RE: Goal = Goal::InputElementRegExp;
const RE_TAIL: Goal = Goal::InputElementRegExpOrTemplateTail;
const TAIL: Goal = Goal::InputElementTemplateTail;
const START: Goal = Goal::InputElementHashbangOrRegExp;

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn kind_name(k: ElementKind) -> &'static str {
    match k {
        ElementKind::WhiteSpace => "WhiteSpace",
        ElementKind::LineTerminator => "LineTerminator",
        ElementKind::Comment => "Comment",
        ElementKind::HashbangComment => "HashbangComment",
        ElementKind::IdentifierName => "IdentifierName",
        ElementKind::PrivateIdentifier => "PrivateIdentifier",
        ElementKind::Punctuator => "Punctuator",
        ElementKind::NumericLiteral => "NumericLiteral",
        ElementKind::StringLiteral => "StringLiteral",
        ElementKind::Template(TemplateKind::NoSubstitution) => "NoSubstitutionTemplate",
        ElementKind::Template(TemplateKind::Head) => "TemplateHead",
        ElementKind::Template(TemplateKind::Middle) => "TemplateMiddle",
        ElementKind::Template(TemplateKind::Tail) => "TemplateTail",
        ElementKind::DivPunctuator => "DivPunctuator",
        ElementKind::RightBracePunctuator => "RightBracePunctuator",
        ElementKind::RegularExpressionLiteral => "RegularExpressionLiteral",
    }
}

fn error_name(e: LexError) -> &'static str {
    match e {
        LexError::NoInputElement => "NoInputElement",
        LexError::IdentifierAfterNumericLiteral => "IdentifierAfterNumericLiteral",
        LexError::InvalidIdentifierEscape => "InvalidIdentifierEscape",
    }
}

/// The first input element of `src` (an error if there is none).
fn first_of(src: &[u32], pos: usize, goal: Goal, html: bool) -> Result<Element, String> {
    match next_input_element(src, pos, goal, html) {
        Ok(Step::Element(el)) => Ok(el),
        Ok(Step::Eof) => Err(format!("{src:?} at {pos}: Eof")),
        Err(e) => Err(format!("{src:?} at {pos}: {}", error_name(e))),
    }
}

/// The first element of `s` is `kind` and is `len` code points long.
fn expect(s: &str, goal: Goal, html: bool, kind: &str, len: usize) -> Result<Element, String> {
    let el = first_of(&cps(s), 0, goal, html).map_err(|e| format!("{s:?}: {e}, want {kind}"))?;
    if kind_name(el.kind) == kind && el.start == 0 && el.end == len {
        Ok(el)
    } else {
        Err(format!(
            "{s:?}: got {} [0, {}), want {kind} [0, {len})",
            kind_name(el.kind),
            el.end
        ))
    }
}

/// The first element of `s` is the error `err`.
fn expect_err(s: &str, goal: Goal, html: bool, err: LexError) -> Result<(), String> {
    match next_input_element(&cps(s), 0, goal, html) {
        Err(e) if e == err => Ok(()),
        Err(e) => Err(format!(
            "{s:?}: got {}, want {}",
            error_name(e),
            error_name(err)
        )),
        Ok(Step::Element(el)) => Err(format!(
            "{s:?}: got {} [0, {}), want {}",
            kind_name(el.kind),
            el.end,
            error_name(err)
        )),
        Ok(Step::Eof) => Err(format!("{s:?}: Eof")),
    }
}

/// All input elements of `s` in one goal, as (kind, start, end).
fn all(s: &str, goal: Goal, html: bool) -> Result<Vec<(&'static str, usize, usize)>, String> {
    let src = cps(s);
    let mut out = Vec::new();
    let mut pos = 0;
    loop {
        match next_input_element(&src, pos, goal, html) {
            Ok(Step::Eof) => return Ok(out),
            Ok(Step::Element(el)) => {
                out.push((kind_name(el.kind), el.start, el.end));
                pos = el.end;
            }
            Err(e) => return Err(format!("{s:?} at {pos}: {}", error_name(e))),
        }
    }
}

fn name(el: &Element) -> Result<(Vec<u32>, bool), String> {
    match &el.value {
        Value::Name {
            code_points,
            escaped,
        } => Ok((code_points.clone(), *escaped)),
        _ => Err("not a name".into()),
    }
}

fn string(el: &Element) -> Result<Vec<u16>, String> {
    match &el.value {
        Value::String { units } => Ok(units.clone()),
        _ => Err("not a string".into()),
    }
}

fn template(el: &Element) -> Result<(Option<Vec<u16>>, Vec<u16>), String> {
    match &el.value {
        Value::Template { cooked, raw } => Ok((cooked.clone(), raw.clone())),
        _ => Err("not a template".into()),
    }
}

fn numeric(el: &Element) -> Result<(bool, bool), String> {
    match el.value {
        Value::Numeric { bigint, legacy } => Ok((bigint, legacy)),
        _ => Err("not a number".into()),
    }
}

#[test]
fn white_space_and_line_terminators() -> Result<(), String> {
    for s in [
        "\t", "\u{B}", "\u{C}", " ", "\u{A0}", "\u{FEFF}", "\u{1680}", "\u{2000}", "\u{200A}",
        "\u{202F}", "\u{205F}", "\u{3000}",
    ] {
        expect(s, DIV, true, "WhiteSpace", 1)?;
    }
    for s in ["\n", "\r", "\u{2028}", "\u{2029}"] {
        expect(s, DIV, false, "LineTerminator", 1)?;
    }
    // <CR><LF> is two LineTerminator elements (§12.3: LineTerminator is one
    // code point; LineTerminatorSequence is for comments and literals).
    expect("\r\n", DIV, false, "LineTerminator", 1)?;
    // U+180E has been Cf, not Zs, since Unicode 6.3.
    expect_err("\u{180E}", DIV, true, LexError::NoInputElement)?;
    expect_err("\u{200B}", DIV, true, LexError::NoInputElement)?;
    Ok(())
}

#[test]
fn comments() -> Result<(), String> {
    assert_eq!(
        all("// x\ny", DIV, true)?,
        vec![
            ("Comment", 0, 4),
            ("LineTerminator", 4, 5),
            ("IdentifierName", 5, 6)
        ]
    );
    expect("/* a */b", DIV, true, "Comment", 7)?;
    expect("/* a */b", DIV, false, "Comment", 7)?;
    expect("/***/", DIV, false, "Comment", 5)?;
    expect("/**/", RE, false, "Comment", 4)?;
    expect("/* a \n b */", DIV, false, "Comment", 11)?;
    // An unterminated `/*` is no comment; the longest element is then `/`
    // where the goal has DivPunctuator, and nothing where it does not.
    expect("/* a", DIV, false, "DivPunctuator", 1)?;
    expect_err("/* a", RE, false, LexError::NoInputElement)?;
    // A code point above U+10FFFF is no SourceCharacter: a single-line
    // comment ends before it, a multi-line comment cannot hold it.
    let mut src = cps("// a");
    src.push(0x11_0000);
    assert_eq!(first_of(&src, 0, DIV, false)?.end, 4);
    assert!(matches!(
        next_input_element(&src, 4, DIV, false),
        Err(LexError::NoInputElement)
    ));
    let mut src = cps("/* a");
    src.push(0x11_0000);
    src.extend(cps("*/"));
    assert!(matches!(
        next_input_element(&src, 0, RE, false),
        Err(LexError::NoInputElement)
    ));
    Ok(())
}

#[test]
fn hashbang() -> Result<(), String> {
    expect("#!/usr/bin/env node\nx", START, true, "HashbangComment", 19)?;
    // Only at the start of the source text, and only in its goal.
    expect_err("#!x", DIV, true, LexError::NoInputElement)?;
    assert!(matches!(
        next_input_element(&cps(" #!x"), 1, START, true),
        Err(LexError::NoInputElement)
    ));
    Ok(())
}

#[test]
fn html_like_comments() -> Result<(), String> {
    // SingleLineHTMLOpenComment, in a Script only.
    expect("<!-- x\ny", DIV, true, "Comment", 6)?;
    expect("<!-- x", DIV, false, "Punctuator", 1)?;
    // SingleLineHTMLCloseComment: a line terminator, then the comment.
    assert_eq!(
        all("x\n--> y\nz", DIV, true)?,
        vec![
            ("IdentifierName", 0, 1),
            ("Comment", 1, 7),
            ("LineTerminator", 7, 8),
            ("IdentifierName", 8, 9)
        ]
    );
    expect("\r\n  /* a */ /*b*/ --> c", DIV, true, "Comment", 23)?;
    expect("\n--> c", DIV, false, "LineTerminator", 1)?;
    // A delimited comment holding a line terminator stops it.
    expect("\n/*\n*/-->", DIV, true, "LineTerminator", 1)?;
    // Annex B MultiLineComment: one holding a line terminator may be
    // followed by an HTMLCloseComment.
    expect("/*\n*/ --> c\nd", DIV, true, "Comment", 11)?;
    expect("/* */ --> c", DIV, true, "Comment", 5)?;
    // HTMLCloseComment at the start of InputElementHashbangOrRegExp.
    expect("--> c\nd", START, true, "Comment", 5)?;
    expect("  /**/ --> c", START, true, "Comment", 12)?;
    expect("--> c", DIV, true, "Punctuator", 2)?;
    expect("--> c", START, false, "Punctuator", 2)?;
    Ok(())
}

#[test]
fn identifiers() -> Result<(), String> {
    let el = expect("abc d", DIV, true, "IdentifierName", 3)?;
    assert_eq!(name(&el)?, (cps("abc"), false));
    let el = expect("$_a1", DIV, true, "IdentifierName", 4)?;
    assert_eq!(name(&el)?, (cps("$_a1"), false));
    let el = expect("\\u0061b", DIV, true, "IdentifierName", 7)?;
    assert_eq!(name(&el)?, (cps("ab"), true));
    let el = expect("a\\u{62}\\u{0000063}", DIV, true, "IdentifierName", 18)?;
    assert_eq!(name(&el)?, (cps("abc"), true));
    let el = expect("a\\u0030", DIV, true, "IdentifierName", 7)?;
    assert_eq!(name(&el)?, (cps("a0"), true));
    // §12.7.1.1: an escape must name an IdentifierStartChar (first) or an
    // IdentifierPartChar.
    expect_err("\\u0030a", DIV, true, LexError::InvalidIdentifierEscape)?;
    expect_err("a\\u002D", DIV, true, LexError::InvalidIdentifierEscape)?;
    expect_err("\\u{1F600}", DIV, true, LexError::InvalidIdentifierEscape)?;
    expect_err("\\uD800", DIV, true, LexError::InvalidIdentifierEscape)?;
    // Malformed escapes are not part of the name.
    expect("a\\u00", DIV, true, "IdentifierName", 1)?;
    expect("a\\u{110000}", DIV, true, "IdentifierName", 1)?;
    expect_err("\\u{}", DIV, true, LexError::NoInputElement)?;
    expect_err("\\x41", DIV, true, LexError::NoInputElement)?;
    // Reserved words are names; the parser decides (§12.7.2).
    expect("while", DIV, true, "IdentifierName", 5)?;
    // Private names.
    let el = expect("#foo.x", DIV, true, "PrivateIdentifier", 4)?;
    assert_eq!(name(&el)?, (cps("foo"), false));
    let el = expect("#\\u0061", DIV, true, "PrivateIdentifier", 7)?;
    assert_eq!(name(&el)?, (cps("a"), true));
    expect_err("#", DIV, true, LexError::NoInputElement)?;
    expect_err("# a", DIV, true, LexError::NoInputElement)?;
    expect_err("#\\u0030", DIV, true, LexError::InvalidIdentifierEscape)?;
    Ok(())
}

#[test]
fn unicode_identifiers() -> Result<(), String> {
    let el = expect("café x", DIV, true, "IdentifierName", 4)?;
    assert_eq!(name(&el)?, (cps("café"), false));
    // U+212E is Other_ID_Start.
    expect("\u{212E}", DIV, true, "IdentifierName", 1)?;
    expect("日本語", DIV, true, "IdentifierName", 3)?;
    // U+10400, outside the BMP.
    expect("\u{10400}", DIV, true, "IdentifierName", 1)?;
    // U+0300 (a combining mark) is ID_Continue but not ID_Start.
    expect("a\u{300}", DIV, true, "IdentifierName", 2)?;
    expect_err("\u{300}", DIV, true, LexError::NoInputElement)?;
    // ZWNJ and ZWJ are ID_Continue (since Unicode 15.1).
    expect("a\u{200C}\u{200D}", DIV, true, "IdentifierName", 3)?;
    expect("a\\u200D", DIV, true, "IdentifierName", 7)?;
    // Arabic-Indic digits continue a name but do not start one.
    expect("a\u{661}", DIV, true, "IdentifierName", 2)?;
    expect_err("\u{661}", DIV, true, LexError::NoInputElement)?;
    // Emoji are neither.
    expect_err("\u{1F600}", DIV, true, LexError::NoInputElement)?;
    expect("a\u{1F600}", DIV, true, "IdentifierName", 1)?;
    Ok(())
}

#[test]
fn punctuators() -> Result<(), String> {
    for (s, n) in [
        ("{", 1),
        ("(", 1),
        (")", 1),
        ("[", 1),
        ("]", 1),
        (".", 1),
        ("...", 3),
        ("..", 1),
        (";", 1),
        (",", 1),
        ("<", 1),
        ("<=", 2),
        ("<<", 2),
        ("<<=", 3),
        (">", 1),
        (">=", 2),
        (">>", 2),
        (">>=", 3),
        (">>>", 3),
        (">>>=", 4),
        ("=", 1),
        ("==", 2),
        ("===", 3),
        ("====", 3),
        ("=>", 2),
        ("!", 1),
        ("!=", 2),
        ("!==", 3),
        ("+", 1),
        ("++", 2),
        ("+=", 2),
        ("+++", 2),
        ("-", 1),
        ("--", 2),
        ("-=", 2),
        ("*", 1),
        ("*=", 2),
        ("**", 2),
        ("**=", 3),
        ("%", 1),
        ("%=", 2),
        ("&", 1),
        ("&&", 2),
        ("&=", 2),
        ("&&=", 3),
        ("|", 1),
        ("||", 2),
        ("|=", 2),
        ("||=", 3),
        ("^", 1),
        ("^=", 2),
        ("~", 1),
        ("?", 1),
        ("??", 2),
        ("??=", 3),
        ("?.", 2),
        ("?.a", 2),
        (":", 1),
    ] {
        expect(s, DIV, true, "Punctuator", n)?;
    }
    // OptionalChainingPunctuator :: ?. [lookahead ∉ DecimalDigit]
    expect("?.5:1", DIV, true, "Punctuator", 1)?;
    expect("/", DIV, true, "DivPunctuator", 1)?;
    expect("/=", DIV, true, "DivPunctuator", 2)?;
    expect("/=", TAIL, true, "DivPunctuator", 2)?;
    expect("}", DIV, true, "RightBracePunctuator", 1)?;
    expect("}", RE, true, "RightBracePunctuator", 1)?;
    expect_err("@", DIV, true, LexError::NoInputElement)?;
    Ok(())
}

#[test]
fn numeric_literals() -> Result<(), String> {
    for (s, n, bigint, legacy) in [
        ("0", 1, false, false),
        ("0;", 1, false, false),
        ("123", 3, false, false),
        ("1_000_000", 9, false, false),
        ("1.5", 3, false, false),
        ("1.", 2, false, false),
        ("1.e3", 4, false, false),
        ("0.e3", 4, false, false),
        (".5", 2, false, false),
        (".5e-3", 5, false, false),
        ("1E+10", 5, false, false),
        ("1_0.0_1e1_0", 11, false, false),
        ("0.5", 3, false, false),
        ("0x1F", 4, false, false),
        ("0XdEaD_bEeF", 11, false, false),
        ("0b1010", 6, false, false),
        ("0o17", 4, false, false),
        ("1n", 2, true, false),
        ("0n", 2, true, false),
        ("1_0n", 4, true, false),
        ("0x1Fn", 5, true, false),
        ("0b1n", 4, true, false),
        ("07", 2, false, true),
        ("0777", 4, false, true),
        ("08", 2, false, true),
        ("019", 3, false, true),
        ("08.5", 4, false, true),
        ("09e1", 4, false, true),
        // A LegacyOctalIntegerLiteral is not a DecimalIntegerLiteral: `07.5`
        // is `07` then `.5`.
        ("07.5", 2, false, true),
        ("1..toString", 2, false, false),
        ("1 in", 1, false, false),
    ] {
        let el = expect(s, DIV, true, "NumericLiteral", n)?;
        assert_eq!(numeric(&el)?, (bigint, legacy), "{s:?}");
    }
    // §12.9.3: no IdentifierStart or DecimalDigit right after.
    for s in [
        "3in", "1n2", "0x", "0b2", "0b12", "0xg", "1e", "1e+", "1_", "1__0", "0_1", "1._5", "08n",
        "07n", "00n", "1.5n", "07e1", "1$", "1\\u0061", "1é",
    ] {
        expect_err(s, DIV, true, LexError::IdentifierAfterNumericLiteral)?;
    }
    // A malformed escape after a number is not an IdentifierStart.
    expect("1\\u00", DIV, true, "NumericLiteral", 1)?;
    Ok(())
}

#[test]
fn string_literals() -> Result<(), String> {
    let el = expect("\"abc\"x", DIV, true, "StringLiteral", 5)?;
    assert_eq!(string(&el)?, units("abc"));
    let el = expect("''", DIV, true, "StringLiteral", 2)?;
    assert_eq!(string(&el)?, units(""));
    for (s, v) in [
        ("'a\\nb'", "a\nb"),
        ("'\\b\\f\\n\\r\\t\\v'", "\u{8}\u{c}\n\r\t\u{b}"),
        ("'\\'\\\"\\\\'", "'\"\\"),
        ("'\\x41'", "A"),
        ("'\\u0041'", "A"),
        ("'\\u{1F600}'", "\u{1F600}"),
        ("'\u{1F600}'", "\u{1F600}"),
        ("'\\0'", "\0"),
        ("'\\08'", "\08"),
        ("'\\101'", "A"),
        ("'\\1010'", "A0"),
        ("'\\377'", "\u{ff}"),
        ("'\\400'", " 0"),
        ("'\\47'", "'"),
        ("'\\7'", "\u{7}"),
        ("'\\8\\9'", "89"),
        ("'\\a\\q'", "aq"),
        ("'a\\\nb'", "ab"),
        ("'a\\\r\nb'", "ab"),
        ("'a\\\u{2028}b'", "ab"),
        ("'a\u{2028}b'", "a\u{2028}b"),
        ("\"'\"", "'"),
    ] {
        let el = expect(s, DIV, true, "StringLiteral", cps(s).len())?;
        assert_eq!(string(&el)?, units(v), "{s:?}");
    }
    let el = expect("'\\uD800'", DIV, true, "StringLiteral", 8)?;
    assert_eq!(string(&el)?, vec![0xD800]);
    for s in [
        "'abc",
        "'a\nb'",
        "'a\rb'",
        "'\\x4'",
        "'\\xg0'",
        "'\\u004'",
        "'\\u{110000}'",
        "'\\u{}'",
        "'\\",
        "\"a'",
    ] {
        expect_err(s, DIV, true, LexError::NoInputElement)?;
    }
    Ok(())
}

#[test]
fn templates() -> Result<(), String> {
    let el = expect("`abc`", DIV, true, "NoSubstitutionTemplate", 5)?;
    assert_eq!(template(&el)?, (Some(units("abc")), units("abc")));
    let el = expect("`a${b}`", DIV, true, "TemplateHead", 4)?;
    assert_eq!(template(&el)?, (Some(units("a")), units("a")));
    let el = expect("``", DIV, true, "NoSubstitutionTemplate", 2)?;
    assert_eq!(template(&el)?, (Some(units("")), units("")));
    let el = expect("`$`", DIV, true, "NoSubstitutionTemplate", 3)?;
    assert_eq!(template(&el)?, (Some(units("$")), units("$")));
    let el = expect("`a\\n`", DIV, true, "NoSubstitutionTemplate", 5)?;
    assert_eq!(template(&el)?, (Some(units("a\n")), units("a\\n")));
    let el = expect("`\r\n\r`", DIV, true, "NoSubstitutionTemplate", 5)?;
    assert_eq!(template(&el)?, (Some(units("\n\n")), units("\n\n")));
    let el = expect("`\\\r\n`", DIV, true, "NoSubstitutionTemplate", 5)?;
    assert_eq!(template(&el)?, (Some(units("")), units("\\\n")));
    let el = expect("`\\u{1F600}`", DIV, true, "NoSubstitutionTemplate", 11)?;
    assert_eq!(
        template(&el)?,
        (Some(units("\u{1F600}")), units("\\u{1F600}"))
    );
    // NotEscapeSequence: the TV is undefined, the TRV is the source.
    for (s, raw) in [
        ("`\\unicode`", "\\unicode"),
        ("`\\u{`", "\\u{"),
        ("`\\u{}`", "\\u{}"),
        ("`\\u{110000}`", "\\u{110000}"),
        ("`\\u{12`", "\\u{12"),
        ("`\\u12`", "\\u12"),
        ("`\\x`", "\\x"),
        ("`\\x1`", "\\x1"),
        ("`\\xg`", "\\xg"),
        ("`\\1`", "\\1"),
        ("`\\01`", "\\01"),
        ("`\\8`", "\\8"),
    ] {
        let el = expect(s, DIV, true, "NoSubstitutionTemplate", cps(s).len())?;
        assert_eq!(template(&el)?, (None, units(raw)), "{s:?}");
    }
    let el = expect("`\\0`", DIV, true, "NoSubstitutionTemplate", 4)?;
    assert_eq!(template(&el)?, (Some(units("\0")), units("\\0")));
    let el = expect("}a`", TAIL, true, "TemplateTail", 3)?;
    assert_eq!(template(&el)?, (Some(units("a")), units("a")));
    expect("}a${", RE_TAIL, true, "TemplateMiddle", 4)?;
    expect("}", DIV, true, "RightBracePunctuator", 1)?;
    expect_err("}", TAIL, true, LexError::NoInputElement)?;
    expect_err("`abc", DIV, true, LexError::NoInputElement)?;
    expect_err("`\\", DIV, true, LexError::NoInputElement)?;
    Ok(())
}

#[test]
fn regular_expressions() -> Result<(), String> {
    let el = expect("/ab+c/gi.x", RE, true, "RegularExpressionLiteral", 8)?;
    assert!(matches!(el.value, Value::RegExp { body_end: 5 }));
    expect("/[/]/", RE, true, "RegularExpressionLiteral", 5)?;
    expect("/[\\]/]/", RE, true, "RegularExpressionLiteral", 7)?;
    expect("/a\\/b/", RE, true, "RegularExpressionLiteral", 6)?;
    expect("/=/", RE, true, "RegularExpressionLiteral", 3)?;
    expect("/=/", DIV, true, "DivPunctuator", 2)?;
    expect("/a/", START, true, "RegularExpressionLiteral", 3)?;
    expect("/a/", RE_TAIL, true, "RegularExpressionLiteral", 3)?;
    expect("/a/\\u0067", RE, true, "RegularExpressionLiteral", 3)?;
    expect("/a/ü", RE, true, "RegularExpressionLiteral", 4)?;
    for s in ["/a", "/a\n/", "/[a/", "/a\\\n/", "/*a/", "/"] {
        expect_err(s, RE, true, LexError::NoInputElement)?;
    }
    Ok(())
}

/// The tokens of `src` in `goal` from 0, as (start, newline_before), and
/// the final `Eof`'s flag.
fn tokens(src: &[u32], goal: Goal) -> Result<(Vec<(usize, bool)>, bool), String> {
    let mut pos = 0;
    let mut seen = Vec::new();
    loop {
        match next_token(src, pos, goal, true) {
            Ok(Next::Token(tok)) => {
                assert!(tok.element.start >= pos);
                seen.push((tok.element.start, tok.newline_before));
                pos = tok.element.end;
            }
            Ok(Next::Eof { newline_before }) => return Ok((seen, newline_before)),
            Err(e) => return Err(format!("at {pos}: {}", error_name(e))),
        }
    }
}

#[test]
fn tokens_and_line_terminators() -> Result<(), String> {
    let src = cps("a /* x */ b\n/*\n*/c // d\n\u{2028}e");
    assert_eq!(
        tokens(&src, DIV)?,
        (vec![(0, false), (10, false), (17, true), (25, true)], false)
    );
    assert_eq!(tokens(&cps("x /*\n*/"), DIV)?, (vec![(0, false)], true));
    assert_eq!(tokens(&cps(""), DIV)?, (vec![], false));
    assert!(matches!(
        next_token(&cps("  @"), 0, DIV, true),
        Err(LexError::NoInputElement)
    ));
    Ok(())
}

/// Every input of up to three code points from an alphabet that reaches
/// every branch's first code point gives a result, at every position, and
/// an element is a non-empty range at the position (what Verus proves, run
/// here as well so that Miri sees each branch execute).
#[test]
fn small_inputs_are_total() {
    const ALPHABET: &[u32] = &[
        0x09,
        0x0A,
        0x0D,
        0x20,
        0x21,
        0x22,
        0x23,
        0x24,
        0x27,
        0x2A,
        0x2B,
        0x2D,
        0x2E,
        0x2F,
        0x30,
        0x31,
        0x38,
        0x3C,
        0x3D,
        0x3E,
        0x3F,
        0x5B,
        0x5C,
        0x5D,
        0x5F,
        0x60,
        0x61,
        0x6E,
        0x75,
        0x78,
        0x7B,
        0x7D,
        0xE9,
        0x2028,
        0xFEFF,
        0x1_F600,
        0x11_0000,
        u32::MAX,
    ];
    const GOALS: [Goal; 5] = [DIV, RE, RE_TAIL, TAIL, START];
    // Under Miri a stride of the inputs (it interprets every step); the
    // full set natively.
    let stride = if cfg!(miri) { 331 } else { 1 };
    let mut inputs: Vec<Vec<u32>> = ALPHABET.iter().map(|&a| vec![a]).collect();
    for &a in ALPHABET {
        for &b in ALPHABET {
            inputs.push(vec![a, b]);
            for &c in ALPHABET {
                inputs.push(vec![a, b, c]);
            }
        }
    }
    let mut checked = 0;
    for src in inputs.iter().step_by(stride) {
        for goal in GOALS {
            for html in [false, true] {
                for pos in 0..=src.len() {
                    match next_input_element(src, pos, goal, html) {
                        Ok(Step::Eof) => assert_eq!(pos, src.len()),
                        Ok(Step::Element(el)) => {
                            assert!(el.start == pos && pos < el.end && el.end <= src.len());
                        }
                        Err(_) => assert!(pos < src.len()),
                    }
                    if let Ok(Next::Token(tok)) = next_token(src, pos, goal, html) {
                        assert!(pos <= tok.element.start && tok.element.end <= src.len());
                    }
                }
            }
        }
        checked += 1;
    }
    assert!(checked > 0);
}

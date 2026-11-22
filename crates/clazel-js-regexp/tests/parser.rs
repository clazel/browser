//! The pattern parser on hand-written patterns: what each mode accepts and
//! rejects (ECMA-262 §22.2.1†, §22.2.1.1†, Annex B §B.1.2†), the tree it
//! builds, and its depth bound. Test262's tests are in `conformance_test262.rs`.

use clazel_js_regexp::ast::{
    Alternative, Atom, ClassContents, ClassEscape, ClassItem, ClassSetExpr, ClassSetItem,
    ClassSetOperand, Property, Quantifier, TermKind,
};
use clazel_js_regexp::{ErrorKind, Flags, MAX_DEPTH, Pattern, parse};

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn run(pattern: &str, flags: &str) -> Result<Pattern, ErrorKind> {
    let f = Flags::parse(&units(flags)).map_err(|_| ErrorKind::InvalidEscape)?;
    parse(&units(pattern), f).map_err(|e| e.kind)
}

/// Patterns that must parse, as `(pattern, flags)`.
const ACCEPT: &[(&str, &str)] = &[
    // Without `u` or `v`: Annex B.
    ("", ""),
    ("a|b|", ""),
    ("a{", ""),
    ("a{,5}", ""),
    ("{", ""),
    ("}", ""),
    ("]", ""),
    ("x{1}", ""),
    ("x{1,}", ""),
    ("x{1,2}?", ""),
    ("\\1", ""),
    ("(a)\\1", ""),
    ("(a)\\2", ""),
    ("\\8", ""),
    ("\\08", ""),
    ("\\00", ""),
    ("\\377", ""),
    ("[\\d-x]", ""),
    ("[a-\\d]", ""),
    ("[\\d-\\w]", ""),
    ("\\c", ""),
    ("\\c1", ""),
    ("[\\c]", ""),
    ("[\\c1]", ""),
    ("[\\c_]", ""),
    ("\\ca", ""),
    ("(?=a)*", ""),
    ("(?!a){2}", ""),
    ("\\k", ""),
    ("\\k<a>", ""),
    ("[\\k]", ""),
    ("(?<n>a)\\k<n>", ""),
    ("\\k<n>(?<n>a)", ""),
    ("(?<a>x)|(?<a>y)", ""),
    ("(?:(?<a>x)|(?<a>y))(?<b>z)", ""),
    ("(?<a>x)|(?:(?<a>y)|(?<a>z))", ""),
    ("\\u{3}", ""),
    ("\\u12", ""),
    ("\\x1", ""),
    ("\\p{L}", ""),
    ("\\_", ""),
    ("\\-", ""),
    ("[\\B]", ""),
    ("[\\-]", ""),
    ("\\/", ""),
    ("(?i:a)", ""),
    ("(?i-s:a)", ""),
    ("(?-i:a)", ""),
    ("(?i-:a)", ""),
    ("(?ims-:a)", ""),
    ("(?<=a)b", ""),
    ("(?<!a)b", ""),
    ("^$\\b\\B", ""),
    ("a*?b+?c??", ""),
    ("[]", ""),
    ("[^]", ""),
    ("[a-]", ""),
    ("[-a]", ""),
    ("[--a]", ""),
    ("[+--]", ""),
    ("\\uD83D\\uDE00", ""),
    ("\u{1F600}", ""),
    ("(?<\u{1D49C}>x)", ""),
    // With `u`.
    ("\\u{1F600}", "u"),
    ("\\uD83D\\uDE00", "u"),
    ("\\uD83D", "u"),
    ("\\/", "u"),
    ("\\^\\$\\\\\\.\\*\\+\\?\\(\\)\\[\\]\\{\\}\\|", "u"),
    ("\\p{L}", "u"),
    ("\\P{Lu}", "u"),
    ("\\p{Script=Greek}", "u"),
    ("\\p{scx=Latn}", "u"),
    ("\\p{gc=Lu}", "u"),
    ("\\p{General_Category=Uppercase_Letter}", "u"),
    ("\\p{Alphabetic}\\p{Any}\\p{ASCII}", "u"),
    ("[\\b]", "u"),
    ("[\\-]", "u"),
    ("\\0", "u"),
    ("[\\0]", "u"),
    ("(a)\\1", "u"),
    ("(?<a>x)\\k<a>", "u"),
    ("\\k<a>(?<a>x)", "u"),
    ("[\\p{L}\\d]", "u"),
    ("[a-z]", "u"),
    ("\\cA", "u"),
    ("[\\cA]", "u"),
    ("\u{1F600}+", "u"),
    ("[\u{1F600}-\u{1F64F}]", "u"),
    ("\\x41\\u0041", "u"),
    // With `v`.
    ("[a&&b]", "v"),
    ("[a--b]", "v"),
    ("[a&&b&&c]", "v"),
    ("[\\q{abc|d}]", "v"),
    ("[\\q{}]", "v"),
    ("[\\q{a|b}]", "v"),
    ("[[a-z]--[aeiou]]", "v"),
    ("[[a-z]&&[^aeiou]]", "v"),
    ("[^[a-z]]", "v"),
    ("[^\\q{a|b}]", "v"),
    ("\\p{RGI_Emoji}", "v"),
    ("[\\p{RGI_Emoji}--\\q{x}]", "v"),
    ("[\\p{L}--\\p{Lu}]", "v"),
    ("[\\&\\-\\!]", "v"),
    ("[a-z0-9_]", "v"),
    ("[]", "v"),
    ("[^]", "v"),
    ("[ab\\d\\q{xyz}[c-d]]", "v"),
    ("(?<a>x)\\k<a>", "v"),
    ("[\\b\\n\\x41\\u{41}\\/\\\\]", "v"),
    ("[a b]", "v"),
    ("[\\d&&\\w]", "v"),
];

/// Patterns that must be rejected, with the error they give.
const REJECT: &[(&str, &str, ErrorKind)] = &[
    ("(", "", ErrorKind::UnterminatedGroup),
    (")", "", ErrorKind::UnmatchedCloseParen),
    ("a)", "", ErrorKind::UnmatchedCloseParen),
    ("(a", "", ErrorKind::UnterminatedGroup),
    ("[", "", ErrorKind::UnterminatedClass),
    ("[a", "", ErrorKind::UnterminatedClass),
    ("[a-", "", ErrorKind::UnterminatedClass),
    ("*", "", ErrorKind::NothingToRepeat),
    ("+a", "", ErrorKind::NothingToRepeat),
    ("a**", "", ErrorKind::NothingToRepeat),
    ("a+*", "", ErrorKind::NothingToRepeat),
    ("(?:*)", "", ErrorKind::NothingToRepeat),
    ("|*", "", ErrorKind::NothingToRepeat),
    ("{1}", "", ErrorKind::InvalidBracedQuantifier),
    ("{1,}", "", ErrorKind::InvalidBracedQuantifier),
    ("{1,2}", "", ErrorKind::InvalidBracedQuantifier),
    ("a{1}{2}", "", ErrorKind::InvalidBracedQuantifier),
    ("a|{1}", "", ErrorKind::InvalidBracedQuantifier),
    ("a{2,1}", "", ErrorKind::QuantifierOutOfOrder),
    (
        "a{100000000000000000000,99999999999999999999}",
        "",
        ErrorKind::QuantifierOutOfOrder,
    ),
    ("a{2,1}", "u", ErrorKind::QuantifierOutOfOrder),
    ("^*", "", ErrorKind::NothingToRepeat),
    ("$+", "", ErrorKind::NothingToRepeat),
    ("\\b?", "", ErrorKind::NothingToRepeat),
    ("\\B{2}", "", ErrorKind::InvalidBracedQuantifier),
    ("\\B*", "", ErrorKind::NothingToRepeat),
    ("(?<=a)*", "", ErrorKind::NothingToRepeat),
    ("(?<!a)?", "", ErrorKind::NothingToRepeat),
    ("(?=a)*", "u", ErrorKind::NothingToRepeat),
    ("(?!a)?", "u", ErrorKind::NothingToRepeat),
    ("\\", "", ErrorKind::TrailingBackslash),
    ("[\\", "", ErrorKind::TrailingBackslash),
    ("(?<a>x)(?<a>y)", "", ErrorKind::DuplicateGroupName),
    ("(?<a>(?<a>x))", "", ErrorKind::DuplicateGroupName),
    ("(?<a>x)(?:(?<a>y)|z)", "", ErrorKind::DuplicateGroupName),
    ("(?:(?<a>x)|y)(?<a>z)", "", ErrorKind::DuplicateGroupName),
    ("(?<a>x)(?<a>y)", "u", ErrorKind::DuplicateGroupName),
    ("(?<a>x)\\k<b>", "", ErrorKind::UndeclaredGroupName),
    ("\\k<b>(?<a>x)", "", ErrorKind::UndeclaredGroupName),
    ("\\k<a>", "u", ErrorKind::UndeclaredGroupName),
    ("(?<a>x)\\k", "", ErrorKind::MissingGroupName),
    ("(?<a>x)\\k<", "", ErrorKind::InvalidGroupName),
    ("\\k", "u", ErrorKind::MissingGroupName),
    ("(?<a>x)[\\k]", "", ErrorKind::InvalidEscape),
    ("(?<1a>x)", "", ErrorKind::InvalidGroupName),
    ("(?<>x)", "", ErrorKind::InvalidGroupName),
    ("(?<a-b>x)", "", ErrorKind::InvalidGroupName),
    ("(?<a", "", ErrorKind::InvalidGroupName),
    ("(?<\\u{31}>x)", "", ErrorKind::InvalidGroupName),
    ("(?<\\uD83D>x)", "", ErrorKind::InvalidGroupName),
    ("(?<\\u12>x)", "", ErrorKind::InvalidUnicodeEscape),
    ("[b-a]", "", ErrorKind::RangeOutOfOrder),
    ("[\\u0062-\\u0061]", "", ErrorKind::RangeOutOfOrder),
    ("[b-a]", "u", ErrorKind::RangeOutOfOrder),
    ("[\u{1F64F}-\u{1F600}]", "u", ErrorKind::RangeOutOfOrder),
    ("(?a)", "", ErrorKind::InvalidGroupSpecifier),
    ("(?i)", "", ErrorKind::InvalidGroupSpecifier),
    ("(?", "", ErrorKind::InvalidGroupSpecifier),
    ("(?i", "", ErrorKind::InvalidGroupSpecifier),
    ("(?ii:a)", "", ErrorKind::InvalidModifiers),
    ("(?-ii:a)", "", ErrorKind::InvalidModifiers),
    ("(?i-i:a)", "", ErrorKind::InvalidModifiers),
    ("(?-:a)", "", ErrorKind::InvalidModifiers),
    ("(?I:a)", "", ErrorKind::InvalidGroupSpecifier),
    ("(?i-m-s:a)", "", ErrorKind::InvalidGroupSpecifier),
    ("{", "u", ErrorKind::LoneBracket),
    ("}", "u", ErrorKind::LoneBracket),
    ("]", "u", ErrorKind::LoneBracket),
    ("a{", "u", ErrorKind::LoneBracket),
    ("a{,5}", "u", ErrorKind::LoneBracket),
    ("\\-", "u", ErrorKind::InvalidEscape),
    ("\\_", "u", ErrorKind::InvalidEscape),
    ("\\a", "u", ErrorKind::InvalidEscape),
    ("\\1", "u", ErrorKind::InvalidDecimalEscape),
    ("(a)\\2", "u", ErrorKind::InvalidDecimalEscape),
    ("\\00", "u", ErrorKind::InvalidDecimalEscape),
    ("\\08", "u", ErrorKind::InvalidDecimalEscape),
    ("[\\1]", "u", ErrorKind::InvalidDecimalEscape),
    ("[\\8]", "u", ErrorKind::InvalidDecimalEscape),
    ("\\c", "u", ErrorKind::InvalidControlEscape),
    ("[\\c]", "u", ErrorKind::InvalidControlEscape),
    ("[\\c1]", "u", ErrorKind::InvalidControlEscape),
    ("\\x1", "u", ErrorKind::InvalidUnicodeEscape),
    ("\\u12", "u", ErrorKind::InvalidUnicodeEscape),
    ("\\u{}", "u", ErrorKind::InvalidUnicodeEscape),
    ("\\u{110000}", "u", ErrorKind::InvalidUnicodeEscape),
    ("\\u{1", "u", ErrorKind::InvalidUnicodeEscape),
    ("[\\d-a]", "u", ErrorKind::ClassEscapeInRange),
    ("[a-\\d]", "u", ErrorKind::ClassEscapeInRange),
    ("[\\p{L}-a]", "u", ErrorKind::ClassEscapeInRange),
    ("[\\B]", "u", ErrorKind::InvalidEscape),
    ("\\p", "u", ErrorKind::InvalidProperty),
    ("\\p{", "u", ErrorKind::InvalidProperty),
    ("\\p{L", "u", ErrorKind::InvalidProperty),
    ("\\p{}", "u", ErrorKind::InvalidProperty),
    ("\\p{Foo}", "u", ErrorKind::InvalidProperty),
    ("\\p{lu}", "u", ErrorKind::InvalidProperty),
    ("\\p{Script}", "u", ErrorKind::InvalidProperty),
    ("\\p{Lu=Lu}", "u", ErrorKind::InvalidProperty),
    ("\\p{gc=Foo}", "u", ErrorKind::InvalidProperty),
    ("\\p{gc=}", "u", ErrorKind::InvalidProperty),
    ("\\p{=Lu}", "u", ErrorKind::InvalidProperty),
    ("\\p{L=a=b}", "u", ErrorKind::InvalidProperty),
    ("\\p{ L}", "u", ErrorKind::InvalidProperty),
    ("\\p{RGI_Emoji}", "u", ErrorKind::InvalidProperty),
    ("[a&&b--c]", "v", ErrorKind::InvalidClassSetOperation),
    ("[a--b&&c]", "v", ErrorKind::InvalidClassSetOperation),
    ("[ab&&c]", "v", ErrorKind::InvalidClassSetOperation),
    ("[a&&bc]", "v", ErrorKind::InvalidClassSetOperation),
    ("[a-z&&b]", "v", ErrorKind::InvalidClassSetOperation),
    ("[a-z--b]", "v", ErrorKind::InvalidClassSetOperation),
    ("[a&&&b]", "v", ErrorKind::InvalidClassSetOperation),
    ("[a&&b-c]", "v", ErrorKind::InvalidClassSetOperation),
    ("[(]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[)]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[{]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[/]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[|]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[-]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[a-]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[&&]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[!!]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[a##]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[b-a]", "v", ErrorKind::RangeOutOfOrder),
    ("[a-\\d]", "v", ErrorKind::ClassEscapeInRange),
    ("[^\\q{ab}]", "v", ErrorKind::NegatedClassMayContainStrings),
    ("[^\\q{}]", "v", ErrorKind::NegatedClassMayContainStrings),
    (
        "[^\\p{RGI_Emoji}]",
        "v",
        ErrorKind::NegatedClassMayContainStrings,
    ),
    (
        "[^[\\q{ab}]]",
        "v",
        ErrorKind::NegatedClassMayContainStrings,
    ),
    (
        "[[^\\q{ab}]]",
        "v",
        ErrorKind::NegatedClassMayContainStrings,
    ),
    (
        "\\P{RGI_Emoji}",
        "v",
        ErrorKind::NegatedClassMayContainStrings,
    ),
    ("[\\q{a", "v", ErrorKind::InvalidClassStringDisjunction),
    ("[\\q{a[}]", "v", ErrorKind::InvalidClassSetCharacter),
    ("[a", "v", ErrorKind::UnterminatedClass),
    ("[a&&", "v", ErrorKind::UnterminatedClass),
    ("[[a]", "v", ErrorKind::UnterminatedClass),
];

#[test]
fn accepts() -> Result<(), String> {
    let mut bad = Vec::new();
    for (pattern, flags) in ACCEPT {
        if let Err(kind) = run(pattern, flags) {
            bad.push(format!("/{pattern}/{flags} rejected: {kind:?}"));
        }
    }
    if bad.is_empty() {
        Ok(())
    } else {
        Err(bad.join("\n"))
    }
}

#[test]
fn rejects() -> Result<(), String> {
    let mut bad = Vec::new();
    for (pattern, flags, want) in REJECT {
        match run(pattern, flags) {
            Ok(_) => bad.push(format!("/{pattern}/{flags} accepted, want {want:?}")),
            Err(kind) if kind != *want => {
                bad.push(format!("/{pattern}/{flags}: {kind:?}, want {want:?}"));
            }
            Err(_) => {}
        }
    }
    if bad.is_empty() {
        Ok(())
    } else {
        Err(bad.join("\n"))
    }
}

fn only_terms(p: &Pattern) -> Result<&Alternative, String> {
    match p.disjunction.alternatives.as_slice() {
        [one] => Ok(one),
        other => Err(format!("{} alternatives", other.len())),
    }
}

fn atom_at(a: &Alternative, i: usize) -> Result<&Atom, String> {
    match a.terms.get(i).map(|t| &t.kind) {
        Some(TermKind::Atom(atom)) => Ok(atom),
        other => Err(format!("term {i}: {other:?}")),
    }
}

#[test]
fn groups_and_names() -> Result<(), String> {
    let p = run("(a)(?:b)(?<n>c)(?<m>d)", "").map_err(|e| format!("{e:?}"))?;
    assert_eq!(p.capture_count, 3);
    let names: Vec<(String, u32)> = p
        .group_names
        .iter()
        .map(|(n, i)| (n.iter().filter_map(|&c| char::from_u32(c)).collect(), *i))
        .collect();
    assert_eq!(names, [("n".to_string(), 2), ("m".to_string(), 3)]);
    let alt = only_terms(&p)?;
    let Atom::Group(g) = atom_at(alt, 1)? else {
        return Err("not a group".into());
    };
    assert_eq!(g.index, None);
    Ok(())
}

#[test]
fn duplicate_names_in_alternatives_are_both_listed() -> Result<(), String> {
    let p = run("(?<a>x)|(?<a>y)", "").map_err(|e| format!("{e:?}"))?;
    assert_eq!(p.capture_count, 2);
    assert_eq!(p.group_names.len(), 2);
    Ok(())
}

#[test]
fn quantifiers() -> Result<(), String> {
    let p = run("a*b+?c{2,}d{3}e{4,5}?f?", "").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    let q = |i: usize| alt.terms.get(i).and_then(|t| t.quantifier);
    assert_eq!(
        q(0),
        Some(Quantifier {
            min: 0,
            max: None,
            greedy: true
        })
    );
    assert_eq!(
        q(1),
        Some(Quantifier {
            min: 1,
            max: None,
            greedy: false
        })
    );
    assert_eq!(
        q(2),
        Some(Quantifier {
            min: 2,
            max: None,
            greedy: true
        })
    );
    assert_eq!(
        q(3),
        Some(Quantifier {
            min: 3,
            max: Some(3),
            greedy: true
        })
    );
    assert_eq!(
        q(4),
        Some(Quantifier {
            min: 4,
            max: Some(5),
            greedy: false
        })
    );
    assert_eq!(
        q(5),
        Some(Quantifier {
            min: 0,
            max: Some(1),
            greedy: true
        })
    );
    // A huge bound saturates.
    let p = run("a{99999999999999999999999}", "").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    assert_eq!(
        alt.terms.first().and_then(|t| t.quantifier).map(|q| q.min),
        Some(u64::MAX)
    );
    // An Annex B lookahead is quantifiable.
    let p = run("(?=a)+", "").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    assert!(matches!(
        alt.terms.first(),
        Some(t) if matches!(t.kind, TermKind::Look(_)) && t.quantifier.is_some()
    ));
    Ok(())
}

#[test]
fn legacy_escapes() -> Result<(), String> {
    let chars = |pattern: &str| -> Result<Vec<Atom>, String> {
        let p = run(pattern, "").map_err(|e| format!("{e:?}"))?;
        let alt = only_terms(&p)?;
        (0..alt.terms.len())
            .map(|i| atom_at(alt, i).cloned())
            .collect()
    };
    assert_eq!(chars("\\0")?, [Atom::Char(0)]);
    assert_eq!(chars("\\1")?, [Atom::Char(1)]);
    assert_eq!(chars("\\12")?, [Atom::Char(10)]);
    assert_eq!(chars("\\377")?, [Atom::Char(255)]);
    // Only two digits when the first is 4 to 7.
    assert_eq!(
        chars("\\400")?,
        [Atom::Char(0o40), Atom::Char(u32::from(b'0'))]
    );
    assert_eq!(chars("\\08")?, [Atom::Char(0), Atom::Char(u32::from(b'8'))]);
    assert_eq!(chars("\\8")?, [Atom::Char(u32::from(b'8'))]);
    assert_eq!(chars("(a)\\1")?.get(1), Some(&Atom::BackReference(1)));
    // `\10` with one group is an octal escape; with ten it is a backreference.
    assert_eq!(chars("(a)\\10")?.get(1), Some(&Atom::Char(8)));
    assert_eq!(
        chars("()()()()()()()()()()\\10")?.get(10),
        Some(&Atom::BackReference(10))
    );
    assert_eq!(
        chars("\\c")?,
        [Atom::Char(0x5C), Atom::Char(u32::from(b'c'))]
    );
    assert_eq!(chars("\\cj")?, [Atom::Char(10)]);
    assert_eq!(
        chars("\\x4")?,
        [Atom::Char(u32::from(b'x')), Atom::Char(u32::from(b'4'))]
    );
    assert_eq!(
        chars("\\u004")?,
        [
            Atom::Char(u32::from(b'u')),
            Atom::Char(u32::from(b'0')),
            Atom::Char(u32::from(b'0')),
            Atom::Char(u32::from(b'4')),
        ]
    );
    Ok(())
}

#[test]
fn unicode_mode_reads_code_points() -> Result<(), String> {
    let p = run("\u{1F600}\\uD83D\\uDE00\\u{1F600}", "u").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    for i in 0..3 {
        assert_eq!(atom_at(alt, i)?, &Atom::Char(0x1F600));
    }
    // Without `u` the pair is two characters.
    let p = run("\u{1F600}", "").map_err(|e| format!("{e:?}"))?;
    assert_eq!(only_terms(&p)?.terms.len(), 2);
    Ok(())
}

#[test]
fn classes() -> Result<(), String> {
    let p = run("[a-c\\d-x\\b]", "").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    let Atom::Class(c) = atom_at(alt, 0)? else {
        return Err("not a class".into());
    };
    assert!(!c.negated);
    assert_eq!(
        c.contents,
        ClassContents::Ranges(vec![
            ClassItem::Range(u32::from(b'a'), u32::from(b'c')),
            ClassItem::Escape(ClassEscape::Digit),
            ClassItem::Char(u32::from(b'-')),
            ClassItem::Char(u32::from(b'x')),
            ClassItem::Char(8),
        ])
    );
    Ok(())
}

#[test]
fn properties() -> Result<(), String> {
    let p = run("\\p{Lu}\\P{sc=Latn}\\p{Alpha}", "u").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    assert_eq!(
        atom_at(alt, 0)?,
        &Atom::Escape(ClassEscape::Property {
            negated: false,
            property: Property::GeneralCategory("Lu".into())
        })
    );
    assert_eq!(
        atom_at(alt, 1)?,
        &Atom::Escape(ClassEscape::Property {
            negated: true,
            property: Property::Script("Latn".into())
        })
    );
    assert_eq!(
        atom_at(alt, 2)?,
        &Atom::Escape(ClassEscape::Property {
            negated: false,
            property: Property::Binary("Alpha".into())
        })
    );
    Ok(())
}

#[test]
fn class_set_expressions() -> Result<(), String> {
    let p = run("[a-c\\q{xy|z}[d]]", "v").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    let Atom::Class(c) = atom_at(alt, 0)? else {
        return Err("not a class".into());
    };
    let ClassContents::Set(ClassSetExpr::Union(items)) = &c.contents else {
        return Err("not a union".into());
    };
    assert_eq!(items.len(), 3);
    assert_eq!(items.first(), Some(&ClassSetItem::Range(97, 99)));
    assert_eq!(
        items.get(1),
        Some(&ClassSetItem::Operand(ClassSetOperand::Strings(vec![
            vec![120, 121],
            vec![122]
        ])))
    );
    let p = run("[a&&b&&c]", "v").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    let Atom::Class(c) = atom_at(alt, 0)? else {
        return Err("not a class".into());
    };
    assert!(matches!(
        &c.contents,
        ClassContents::Set(ClassSetExpr::Intersection(ops)) if ops.len() == 3
    ));
    let p = run("[a--b]", "v").map_err(|e| format!("{e:?}"))?;
    let alt = only_terms(&p)?;
    let Atom::Class(c) = atom_at(alt, 0)? else {
        return Err("not a class".into());
    };
    assert!(matches!(
        &c.contents,
        ClassContents::Set(ClassSetExpr::Subtraction(ops)) if ops.len() == 2
    ));
    Ok(())
}

#[test]
fn flags() {
    let f = |s: &str| Flags::parse(&units(s));
    assert!(f("dgimsuy").is_ok());
    assert!(f("dgimsvy").is_ok());
    assert!(f("").is_ok());
    assert!(f("a").is_err());
    assert!(f("gg").is_err());
    assert!(f("uv").is_err());
    assert!(f("G").is_err());
    assert!(f("\\u0067").is_err());
}

#[test]
fn depth_is_bounded() {
    for (open, close, body, flags) in [
        ("(", ")", "a", ""),
        ("(?:", ")", "a", "u"),
        ("(?=", ")", "a", ""),
        ("(?<=", ")", "a", ""),
        ("[", "]", "a", "v"),
    ] {
        let at = |depth: usize| open.repeat(depth) + body + &close.repeat(depth);
        // A class opens one level per `[`, and the pattern's own disjunction
        // one more for a group; a class at the top level also opens one.
        let ok = at(MAX_DEPTH.saturating_sub(2));
        assert!(run(&ok, flags).is_ok(), "{open} at {}", MAX_DEPTH - 2);
        let deep = at(MAX_DEPTH.saturating_add(10));
        assert_eq!(
            run(&deep, flags).err(),
            Some(ErrorKind::TooDeep),
            "{open} at {}",
            MAX_DEPTH + 10
        );
        // Far deeper than any stack could take, still an error.
        let huge = at(if cfg!(miri) { 1_000 } else { 200_000 });
        assert_eq!(run(&huge, flags).err(), Some(ErrorKind::TooDeep));
    }
}

#[test]
fn many_groups_and_alternatives() -> Result<(), String> {
    // Under Miri, which is about a hundred times slower, a tenth of the size.
    let n: u32 = if cfg!(miri) { 100 } else { 5000 };
    let count = usize::try_from(n).map_err(|e| e.to_string())?;
    let many = "(a)".repeat(count);
    let p = run(&many, "").map_err(|e| format!("{e:?}"))?;
    assert_eq!(p.capture_count, n);
    let alts = vec!["x"; count].join("|");
    let p = run(&alts, "").map_err(|e| format!("{e:?}"))?;
    assert_eq!(p.disjunction.alternatives.len(), count);
    // Distinct names, many of them.
    let named: String = (0..n / 2).map(|i| format!("(?<n{i}>a)")).collect();
    assert!(run(&named, "").is_ok());
    Ok(())
}

#[test]
fn script_names_plug_in() {
    struct Latin;
    impl clazel_js_regexp::Names for Latin {
        fn is_script(&self, value: &str) -> bool {
            value == "Latn" || value == "Latin"
        }
    }
    let f = Flags {
        unicode: true,
        ..Flags::default()
    };
    assert!(clazel_js_regexp::parse_with(&units("\\p{sc=Latin}"), f, &Latin).is_ok());
    assert!(clazel_js_regexp::parse_with(&units("\\p{sc=Greek}"), f, &Latin).is_err());
    assert!(clazel_js_regexp::parse_with(&units("\\p{scx=Greek}"), f, &Latin).is_err());
}

/// Every pattern of up to three code units over an alphabet of the
/// grammar's punctuation, in every mode: the parser returns, and what it
/// accepts has a well-formed tree. A stride under Miri keeps it near a minute.
#[test]
fn small_patterns_do_not_panic() {
    const ALPHABET: &[u16] = &[
        0x28, 0x29, 0x5B, 0x5D, 0x7B, 0x7D, 0x5C, 0x5E, 0x24, 0x2E, 0x2A, 0x2B, 0x3F, 0x7C, 0x2D,
        0x2C, 0x3A, 0x3C, 0x3E, 0x3D, 0x21, 0x26, 0x61, 0x30, 0x31, 0x6B, 0x70, 0x75, 0x63, 0x71,
        0x78, 0xD83D, 0xDE00,
    ];
    let stride: usize = if cfg!(miri) { 211 } else { 1 };
    let modes = [
        Flags::default(),
        Flags {
            unicode: true,
            ..Flags::default()
        },
        Flags {
            unicode_sets: true,
            ..Flags::default()
        },
    ];
    // Each position is empty or one unit; after an empty one, all are.
    let options: Vec<Option<u16>> = std::iter::once(None)
        .chain(ALPHABET.iter().map(|&u| Some(u)))
        .collect();
    let mut counter: usize = 0;
    for a in &options {
        for b in &options {
            for c in &options {
                if (a.is_none() && b.is_some()) || (b.is_none() && c.is_some()) {
                    continue;
                }
                counter = counter.saturating_add(1);
                if !counter.is_multiple_of(stride) {
                    continue;
                }
                let pattern: Vec<u16> = [a, b, c].into_iter().flatten().copied().collect();
                for f in modes {
                    if let Ok(p) = parse(&pattern, f) {
                        assert!(usize::try_from(p.capture_count).is_ok_and(|n| n <= pattern.len()));
                        assert!(!p.disjunction.alternatives.is_empty());
                    }
                }
            }
        }
    }
}

//! The generated tables (`src/tables.rs`) against the vendored Unicode 18.0.0
//! files (`tests/data/ucd-regexp/`, phase-7.md item 7.1).
//!
//! This file is the generator: [`render`] writes the whole of `src/tables.rs`
//! from the UCD, and the test `tables_are_current` fails if the committed file
//! differs from what it writes. To rewrite the file after changing this
//! generator or the data, run
//! `CLAZEL_WRITE_TABLES=1 cargo test -p clazel-js-regexp --test tables`
//! and then `cargo fmt -p clazel-js-regexp` (the output is already what rustfmt
//! writes, so the second step changes nothing; the test is what says so).
//!
//! What it derives, and from which file:
//!
//! - `SIMPLE_FOLD`: Simple Case Folding, the `C` and `S` rows of
//!   `CaseFolding.txt` (ECMA-262's `Canonicalize` with `u` or `v`, §22.2.2.7.3†),
//!   and `SIMPLE_FOLD_INVERSE`, the same pairs sorted by their second element.
//! - `UPPER`: `toUppercase` of a BMP code point where the result is one BMP
//!   code point, different from the argument, and not an ASCII letter for a
//!   non-ASCII argument (`Canonicalize` without `u` or `v`): the full
//!   unconditional mapping of `SpecialCasing.txt` where it has one, else the
//!   simple uppercase of `UnicodeData.txt`. `UPPER_INVERSE` likewise.
//! - `GENERAL_CATEGORY`: the ranges of `DerivedGeneralCategory.txt`, every
//!   code point covered, a gap being `Cn`.
//! - One table per binary property of ECMA-262's list, from
//!   `PropList.txt`, `DerivedCoreProperties.txt`, `DerivedNormalizationProps.txt`,
//!   `DerivedBinaryProperties.txt` or `emoji-data.txt` (the first that lists it).
//!
//! The other tests are independent checks of the committed tables: the
//! categories against `UnicodeData.txt` (a different file from the one the
//! table is made from), and spot checks of the case mappings.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;

use clazel_js_regexp::props::BINARY_PROPERTIES;
use clazel_js_regexp::tables;
use clazel_js_regexp::unicode::{canonicalize, equivalents, simple_fold};

const LAST: u32 = 0x10FFFF;

/// The thirty general categories, in the order of the table's index.
const CATEGORIES: [&str; 30] = [
    "Lu", "Ll", "Lt", "Lm", "Lo", "Mn", "Mc", "Me", "Nd", "Nl", "No", "Pc", "Pd", "Ps", "Pe", "Pi",
    "Pf", "Po", "Sm", "Sc", "Sk", "So", "Zs", "Zl", "Zp", "Cc", "Cf", "Cs", "Co", "Cn",
];

const CN: u8 = 29;

fn data(file: &str) -> Result<String, String> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/ucd-regexp")
        .join(file);
    std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))
}

/// The `;`-separated fields of each line of a UCD file, comments removed.
fn rows(text: &str) -> Vec<Vec<String>> {
    text.lines()
        .map(|l| l.split('#').next().unwrap_or_default())
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.split(';').map(|f| f.trim().to_string()).collect())
        .collect()
}

fn hex(s: &str) -> Result<u32, String> {
    u32::from_str_radix(s.trim(), 16).map_err(|e| format!("{s:?}: {e}"))
}

fn range(s: &str) -> Result<(u32, u32), String> {
    match s.split_once("..") {
        Some((a, b)) => Ok((hex(a)?, hex(b)?)),
        None => hex(s).map(|c| (c, c)),
    }
}

/// Sorted, disjoint, with touching ranges merged.
fn merge(mut r: Vec<(u32, u32)>) -> Vec<(u32, u32)> {
    r.sort_unstable();
    let mut out: Vec<(u32, u32)> = Vec::new();
    for (a, b) in r {
        match out.last_mut() {
            Some(last) if a <= last.1.saturating_add(1) => last.1 = last.1.max(b),
            _ => out.push((a, b)),
        }
    }
    out
}

fn property_ranges(files: &[String], name: &str) -> Result<Vec<(u32, u32)>, String> {
    for text in files {
        let mut found = Vec::new();
        for row in rows(text) {
            if let (Some(r), Some(n)) = (row.first(), row.get(1))
                && n == name
            {
                found.push(range(r)?);
            }
        }
        if !found.is_empty() {
            return Ok(merge(found));
        }
    }
    Err(format!("{name}: in no file"))
}

fn pairs(out: &mut String, name: &str, doc: &str, list: &[(u32, u32)]) {
    let _ = writeln!(out, "/// {doc}");
    // rustfmt puts an array on one line if its elements take at most 60
    // characters; the generator writes what rustfmt would.
    let one: Vec<String> = list
        .iter()
        .map(|(a, b)| format!("({a:#X}, {b:#X})"))
        .collect();
    let joined = one.join(", ");
    if joined.len() <= 60 {
        let line = format!("pub static {name}: &[(u32, u32)] = &[{joined}];");
        if line.len() <= 100 {
            let _ = writeln!(out, "{line}\n");
        } else {
            let _ = writeln!(
                out,
                "pub static {name}: &[(u32, u32)] =\n    &[{joined}];\n"
            );
        }
    } else {
        let _ = writeln!(out, "pub static {name}: &[(u32, u32)] = &[");
        for (a, b) in list {
            let _ = writeln!(out, "    ({a:#X}, {b:#X}),");
        }
        out.push_str("];\n\n");
    }
}

fn fold_table() -> Result<Vec<(u32, u32)>, String> {
    let mut v = Vec::new();
    for row in rows(&data("CaseFolding.txt")?) {
        if let [code, status, mapping, ..] = row.as_slice()
            && (status == "C" || status == "S")
        {
            v.push((hex(code)?, hex(mapping)?));
        }
    }
    v.sort_unstable();
    Ok(v)
}

fn upper_table() -> Result<Vec<(u32, u32)>, String> {
    // Unconditional full mappings of SpecialCasing.txt: code; lower; title;
    // upper; (condition;)?
    let mut special: BTreeMap<u32, Vec<u32>> = BTreeMap::new();
    for row in rows(&data("SpecialCasing.txt")?) {
        if let [code, _, _, upper, rest @ ..] = row.as_slice() {
            let conditional = rest.iter().any(|f| !f.is_empty());
            if !conditional {
                let u = upper
                    .split_whitespace()
                    .map(hex)
                    .collect::<Result<Vec<_>, _>>()?;
                special.insert(hex(code)?, u);
            }
        }
    }
    let mut simple: BTreeMap<u32, u32> = BTreeMap::new();
    for line in data("UnicodeData.txt")?.lines() {
        let f: Vec<&str> = line.split(';').collect();
        if let (Some(code), Some(up)) = (f.first(), f.get(12))
            && !up.is_empty()
        {
            simple.insert(hex(code)?, hex(up)?);
        }
    }
    let mut v = Vec::new();
    for c in 0..=0xFFFFu32 {
        let result = match special.get(&c) {
            Some(u) => u.clone(),
            None => vec![simple.get(&c).copied().unwrap_or(c)],
        };
        if let [y] = result.as_slice() {
            let y = *y;
            if y != c && y <= 0xFFFF && !(c >= 128 && y < 128) {
                v.push((c, y));
            }
        }
    }
    Ok(v)
}

fn category_table() -> Result<Vec<(u32, u32, u8)>, String> {
    let mut v: Vec<(u32, u32, u8)> = Vec::new();
    for row in rows(&data("DerivedGeneralCategory.txt")?) {
        if let [r, cat, ..] = row.as_slice() {
            let idx = CATEGORIES
                .iter()
                .position(|c| c == cat)
                .ok_or_else(|| format!("category {cat}"))?;
            let (a, b) = range(r)?;
            v.push((a, b, u8::try_from(idx).map_err(|e| e.to_string())?));
        }
    }
    v.sort_unstable();
    let mut out: Vec<(u32, u32, u8)> = Vec::new();
    let mut next = 0u32;
    let mut push = |a: u32, b: u32, c: u8| match out.last_mut() {
        Some(last) if last.2 == c && last.1.saturating_add(1) == a => last.1 = b,
        _ => out.push((a, b, c)),
    };
    for (a, b, c) in v {
        if a < next {
            return Err(format!("overlap at {a:X}"));
        }
        if a > next {
            push(next, a.saturating_sub(1), CN);
        }
        push(a, b, c);
        next = b.saturating_add(1);
    }
    if next <= LAST {
        push(next, LAST, CN);
    }
    Ok(out)
}

/// The text of `src/tables.rs`.
fn render() -> Result<String, String> {
    let mut out = String::new();
    out.push_str(
        "//! Unicode 18.0.0 tables for case folding, `\\p{..}` and `\\w`: generated.\n\
//!\n\
//! @generated by `tests/tables.rs` (`CLAZEL_WRITE_TABLES=1 cargo test -p\n\
//! clazel-js-regexp --test tables`) from `tests/data/ucd-regexp/` (source,\n\
//! commit and license: `SOURCE.md` there). Do not edit by hand: the test\n\
//! `tables_are_current` fails if this file differs from what the generator\n\
//! writes. What each table holds and which file it comes from is in the\n\
//! header of that test file.\n\n",
    );
    let fold = fold_table()?;
    pairs(
        &mut out,
        "SIMPLE_FOLD",
        "Simple Case Folding (CaseFolding.txt, statuses C and S): code point, folded, sorted by code point.",
        &fold,
    );
    let mut inv: Vec<(u32, u32)> = fold.iter().map(|&(a, b)| (b, a)).collect();
    inv.sort_unstable();
    pairs(
        &mut out,
        "SIMPLE_FOLD_INVERSE",
        "`SIMPLE_FOLD` as (folded, code point), sorted.",
        &inv,
    );
    let upper = upper_table()?;
    pairs(
        &mut out,
        "UPPER",
        "toUppercase of a BMP code point where it is one different BMP code point, and not ASCII for a non-ASCII argument: code point, upper case, sorted by code point.",
        &upper,
    );
    let mut inv: Vec<(u32, u32)> = upper.iter().map(|&(a, b)| (b, a)).collect();
    inv.sort_unstable();
    pairs(
        &mut out,
        "UPPER_INVERSE",
        "`UPPER` as (upper case, code point), sorted.",
        &inv,
    );
    let cats = category_table()?;
    out.push_str("/// The general categories, in the order of the index in `GENERAL_CATEGORY`.\n");
    out.push_str("pub static CATEGORY_NAMES: [&str; 30] = [\n");
    for line in CATEGORIES.chunks(16) {
        let items: Vec<String> = line.iter().map(|c| format!("\"{c}\"")).collect();
        let _ = writeln!(out, "    {},", items.join(", "));
    }
    out.push_str("];\n\n");
    out.push_str("/// General_Category (DerivedGeneralCategory.txt): first, last, index into `CATEGORY_NAMES`. Sorted, disjoint, covers U+0000 to U+10FFFF.\n");
    out.push_str("pub static GENERAL_CATEGORY: &[(u32, u32, u8)] = &[\n");
    for (a, b, c) in &cats {
        let _ = writeln!(out, "    ({a:#X}, {b:#X}, {c}),");
    }
    out.push_str("];\n\n");

    let files: Vec<String> = [
        "PropList.txt",
        "DerivedCoreProperties.txt",
        "DerivedNormalizationProps.txt",
        "DerivedBinaryProperties.txt",
        "emoji-data.txt",
    ]
    .iter()
    .map(|f| data(f))
    .collect::<Result<_, _>>()?;
    let mut names: Vec<String> = BINARY_PROPERTIES
        .iter()
        .map(|(full, _)| String::from_utf8_lossy(full).into_owned())
        .filter(|n| !matches!(n.as_str(), "Any" | "ASCII" | "Assigned"))
        .collect();
    names.sort();
    for n in &names {
        let r = property_ranges(&files, n)?;
        pairs(
            &mut out,
            &format!("BINARY_{}", n.to_ascii_uppercase()),
            &format!("The code points with the binary property {n}, as ranges."),
            &r,
        );
    }
    out.push_str("/// The binary properties of ECMA-262's list that need a table, by canonical name (`Any`, `ASCII` and `Assigned` need none).\n");
    out.push_str("pub static BINARY: &[(&str, &[(u32, u32)])] = &[\n");
    for n in &names {
        let up = n.to_ascii_uppercase();
        let line = format!("    (\"{n}\", BINARY_{up}),");
        // rustfmt breaks a tuple whose contents take more than 60 characters.
        if line.len() <= 100 && format!("\"{n}\", BINARY_{up}").len() <= 60 {
            let _ = writeln!(out, "{line}");
        } else {
            let _ = writeln!(out, "    (\n        \"{n}\",\n        BINARY_{up},\n    ),");
        }
    }
    out.push_str("];\n");
    Ok(out)
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn tables_are_current() -> Result<(), String> {
    let want = render()?;
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/tables.rs");
    if std::env::var_os("CLAZEL_WRITE_TABLES").is_some() {
        std::fs::write(&path, &want).map_err(|e| e.to_string())?;
        return Ok(());
    }
    let have = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
    if have == want {
        println!("clazel-conformance: suite=\"generated tables\" pass=1 xfail=0 fail=0 total=1");
        Ok(())
    } else {
        Err(
            "src/tables.rs differs from the generator's output; see the header of tests/tables.rs"
                .into(),
        )
    }
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn categories_agree_with_unicode_data() -> Result<(), String> {
    // UnicodeData.txt lists each assigned code point, or a range between a
    // `<.., First>` and `<.., Last>` pair; every other code point is Cn.
    let total = usize::try_from(LAST)
        .map_err(|e| e.to_string())?
        .saturating_add(1);
    let mut expect: Vec<u8> = vec![CN; total];
    let mut first: Option<u32> = None;
    for line in data("UnicodeData.txt")?.lines() {
        let f: Vec<&str> = line.split(';').collect();
        let (Some(code), Some(name), Some(cat)) = (f.first(), f.get(1), f.get(2)) else {
            continue;
        };
        let c = hex(code)?;
        let idx = u8::try_from(
            CATEGORIES
                .iter()
                .position(|x| x == cat)
                .ok_or_else(|| format!("category {cat}"))?,
        )
        .map_err(|e| e.to_string())?;
        if name.ends_with(", First>") {
            first = Some(c);
            continue;
        }
        let lo = if name.ends_with(", Last>") {
            first.take().unwrap_or(c)
        } else {
            c
        };
        for x in lo..=c {
            if let Some(slot) = expect.get_mut(usize::try_from(x).map_err(|e| e.to_string())?) {
                *slot = idx;
            }
        }
    }
    let mut bad = 0u32;
    let mut at = 0u32;
    for &(a, b, c) in tables::GENERAL_CATEGORY {
        if a != at {
            return Err(format!("gap before {a:X}"));
        }
        for x in a..=b {
            let want = expect.get(usize::try_from(x).map_err(|e| e.to_string())?);
            if want != Some(&c) {
                bad = bad.saturating_add(1);
            }
        }
        at = b.saturating_add(1);
    }
    if at != LAST.saturating_add(1) {
        return Err("does not reach U+10FFFF".into());
    }
    let all = LAST.saturating_add(1);
    println!(
        "clazel-conformance: suite=\"general category vs UnicodeData.txt\" pass={} xfail=0 fail={bad} total={all}",
        all.saturating_sub(bad)
    );
    assert_eq!(bad, 0);
    Ok(())
}

#[test]
fn tables_are_sorted() {
    for t in [
        tables::SIMPLE_FOLD,
        tables::SIMPLE_FOLD_INVERSE,
        tables::UPPER,
        tables::UPPER_INVERSE,
    ] {
        assert!(!t.is_empty());
        assert!(t.windows(2).all(|w| match w {
            [a, b] => a < b,
            _ => true,
        }));
    }
    assert!(!tables::BINARY.is_empty());
    for (_, t) in tables::BINARY {
        assert!(t.windows(2).all(|w| match w {
            [a, b] => a.0 <= a.1 && a.1 < b.0,
            _ => true,
        }));
    }
}

#[test]
fn spot_checks_of_the_mappings() {
    // Canonicalize with u: simple case folding.
    assert_eq!(simple_fold(0x41), 0x61);
    assert_eq!(simple_fold(0x61), 0x61);
    assert_eq!(simple_fold(0xDF), 0xDF, "sharp s has only a full folding");
    assert_eq!(simple_fold(0x1E9E), 0xDF, "capital sharp s folds simply");
    assert_eq!(simple_fold(0x17F), 0x73, "long s folds to s");
    assert_eq!(simple_fold(0x212A), 0x6B, "kelvin folds to k");
    assert_eq!(simple_fold(0x130), 0x130, "dotted I: only T and F rows");
    assert_eq!(simple_fold(0x1C5), 0x1C6);
    assert_eq!(simple_fold(0x10400), 0x10428);
    assert_eq!(simple_fold(0x10FFFF), 0x10FFFF);
    // Canonicalize without u: toUppercase of the code unit.
    assert_eq!(canonicalize(0x61, false), 0x41);
    assert_eq!(canonicalize(0x41, false), 0x41);
    assert_eq!(canonicalize(0xE9, false), 0xC9);
    assert_eq!(canonicalize(0xDF, false), 0xDF, "uppercase is two units");
    assert_eq!(canonicalize(0x17F, false), 0x17F, "S would be ASCII");
    assert_eq!(canonicalize(0x131, false), 0x131, "I would be ASCII");
    assert_eq!(canonicalize(0x3C3, false), 0x3A3);
    assert_eq!(canonicalize(0x3C2, false), 0x3A3, "final sigma");
    assert_eq!(canonicalize(0x1C5, false), 0x1C4);
    assert_eq!(canonicalize(0xD801, false), 0xD801, "a lone surrogate");
    assert_eq!(canonicalize(0x212A, false), 0x212A);
}

/// How many code points to skip between checks: every one natively, a stride
/// under Miri.
fn stride() -> usize {
    if cfg!(miri) { 61 } else { 1 }
}

#[test]
fn equivalents_invert_canonicalize() {
    // For every character, its equivalence class (what the matcher compares
    // class members and backreferences by) holds it, and holds exactly the
    // characters with its canonical form.
    let mut out = Vec::new();
    for unicode in [false, true] {
        let top = if unicode { 0x10FFFFu32 } else { 0xFFFF };
        for c in (0..=top).step_by(stride()) {
            let cc = canonicalize(c, unicode);
            equivalents(cc, unicode, &mut out);
            assert!(
                out.contains(&c),
                "{c:X} (unicode: {unicode}) is not in the class of {cc:X}"
            );
            for &a in &out {
                assert_eq!(canonicalize(a, unicode), cc, "{a:X} in the class of {cc:X}");
            }
            assert!(out.len() <= 6, "{cc:X} has {} equivalents", out.len());
        }
    }
}

#[test]
fn simple_folding_is_idempotent_and_canonicalize_unit_is_in_range() {
    for c in (0..=0x10FFFFu32).step_by(stride()) {
        let f = simple_fold(c);
        assert_eq!(simple_fold(f), f, "{c:X}");
        if c <= 0xFFFF {
            let u = canonicalize(c, false);
            assert!(u <= 0xFFFF);
            assert!(c < 128 || u >= 128, "{c:X} became ASCII");
        }
    }
}

#[test]
fn word_characters_with_u_and_i_are_the_two_extras() {
    // §22.2.2.9† WordCharacters: the extras are the characters that are not
    // basic word characters but whose Canonicalize is. The matcher hard-codes
    // them (U+017F and U+212A).
    let basic = |c: u32| matches!(c, 0x30..=0x39 | 0x41..=0x5A | 0x61..=0x7A | 0x5F);
    let mut extras = Vec::new();
    for c in (0..=0x10FFFFu32).step_by(if cfg!(miri) { 1 << 12 } else { 1 }) {
        if !basic(c) && basic(simple_fold(c)) {
            extras.push(c);
        }
    }
    if !cfg!(miri) {
        assert_eq!(extras, vec![0x17F, 0x212A]);
    }
    // Without u the canonical form of a non-ASCII unit is never ASCII.
    assert!(
        (0x80..=0xFFFFu32)
            .step_by(stride())
            .all(|c| !basic(canonicalize(c, false)))
    );
}

#[test]
fn every_property_name_resolves() {
    use clazel_js_regexp::props::{BINARY_NAMES, GENERAL_CATEGORY_VALUES};
    use clazel_js_regexp::unicode::{binary_property, category_mask};
    for n in GENERAL_CATEGORY_VALUES {
        let n = String::from_utf8_lossy(n);
        assert!(category_mask(&n).is_some(), "{n}");
    }
    for n in BINARY_NAMES {
        let n = String::from_utf8_lossy(n);
        assert!(binary_property(&n).is_some(), "{n}");
    }
    assert!(category_mask("Latin").is_none());
    assert!(binary_property("Latin").is_none());
}

#[test]
fn category_groups_are_unions_of_their_members() {
    use clazel_js_regexp::unicode::{category_mask, general_category};
    let m = |n: &str| category_mask(n).unwrap_or(0);
    assert_eq!(m("L"), m("Lu") | m("Ll") | m("Lt") | m("Lm") | m("Lo"));
    assert_eq!(m("LC"), m("Lu") | m("Ll") | m("Lt"));
    assert_eq!(m("M"), m("Mn") | m("Mc") | m("Me"));
    assert_eq!(m("N"), m("Nd") | m("Nl") | m("No"));
    assert_eq!(m("Z"), m("Zs") | m("Zl") | m("Zp"));
    assert_eq!(
        m("P"),
        m("Pc") | m("Pd") | m("Ps") | m("Pe") | m("Pi") | m("Pf") | m("Po")
    );
    assert_eq!(m("S"), m("Sm") | m("Sc") | m("Sk") | m("So"));
    assert_eq!(m("C"), m("Cc") | m("Cf") | m("Cs") | m("Co") | m("Cn"));
    // Together the thirty are every bit of a 30-bit mask, and the table
    // yields one of them for every code point.
    let all = m("L") | m("M") | m("N") | m("P") | m("S") | m("Z") | m("C");
    assert_eq!(all, 0x3FFF_FFFF);
    assert_eq!(general_category(0x41), 0);
    assert_eq!(general_category(0x378), 29);
    assert_eq!(general_category(0x10FFFF), 29);
}

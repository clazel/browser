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
//! - `SCRIPTS`: for each `Script` value of `PropertyValueAliases.txt` (`sc`
//!   rows: short name, long name, any further alias), its code points under
//!   `Script` (`Scripts.txt`; `Unknown` is every code point the file does not
//!   list) and under `Script_Extensions` (`ScriptExtensions.txt`: the rows
//!   that name the script, plus the code points of the script that no row
//!   lists, whose extensions are their script alone).
//! - `STRING_PROPERTIES`: the properties of strings of UTS #51 (ED-27), from
//!   `emoji-sequences.txt` and `emoji-zwj-sequences.txt`: the code points a
//!   property holds as one-character strings (ranges), and its strings of two
//!   or more (as Rust strings); `RGI_Emoji` is the union of the other six.
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

/// `a` without the code points of `b`; both sorted and disjoint.
fn subtract(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    for &(lo, hi) in a {
        let mut cur = lo;
        let mut done = false;
        for &(blo, bhi) in b {
            if bhi < cur {
                continue;
            }
            if blo > hi {
                break;
            }
            if blo > cur {
                out.push((cur, blo.saturating_sub(1)));
            }
            if bhi >= hi {
                done = true;
                break;
            }
            cur = bhi.saturating_add(1);
        }
        if !done {
            out.push((cur, hi));
        }
    }
    out
}

/// One `Script` value as the generator sees it.
struct ScriptData {
    /// The long name.
    long: String,
    /// Short name, long name, further aliases (`PropertyValueAliases.txt`).
    names: Vec<String>,
    sc: Vec<(u32, u32)>,
    scx: Vec<(u32, u32)>,
}

fn scripts() -> Result<Vec<ScriptData>, String> {
    // The values: `sc ; Short ; Long [; Alias]`.
    let mut values: Vec<Vec<String>> = rows(&data("PropertyValueAliases.txt")?)
        .into_iter()
        .filter(|r| r.first().is_some_and(|p| p == "sc"))
        .map(|r| r.into_iter().skip(1).collect())
        .collect();
    values.sort_by(|a, b| a.get(1).cmp(&b.get(1)));
    let long_of_short: BTreeMap<String, String> = values
        .iter()
        .filter_map(|v| Some((v.first()?.clone(), v.get(1)?.clone())))
        .collect();
    // Scripts.txt: ranges by long name.
    let mut sc: BTreeMap<String, Vec<(u32, u32)>> = BTreeMap::new();
    for row in rows(&data("Scripts.txt")?) {
        if let [r, long, ..] = row.as_slice() {
            if !long_of_short.values().any(|l| l == long) {
                return Err(format!("Scripts.txt: {long} is not an sc value"));
            }
            sc.entry(long.clone()).or_default().push(range(r)?);
        }
    }
    let sc: BTreeMap<String, Vec<(u32, u32)>> =
        sc.into_iter().map(|(k, v)| (k, merge(v))).collect();
    let listed = merge(sc.values().flatten().copied().collect());
    let unknown = subtract(&[(0, LAST)], &listed);
    // ScriptExtensions.txt: rows naming scripts by short name.
    let mut ext: BTreeMap<String, Vec<(u32, u32)>> = BTreeMap::new();
    let mut ext_listed = Vec::new();
    for row in rows(&data("ScriptExtensions.txt")?) {
        if let [r, list, ..] = row.as_slice() {
            let rg = range(r)?;
            ext_listed.push(rg);
            for short in list.split_whitespace() {
                let long = long_of_short
                    .get(short)
                    .ok_or_else(|| format!("ScriptExtensions.txt: {short} is not an sc value"))?;
                ext.entry(long.clone()).or_default().push(rg);
            }
        }
    }
    let ext_listed = merge(ext_listed);
    let mut out = Vec::new();
    for v in values {
        let long = v.get(1).ok_or("sc row without a long name")?.clone();
        let own = if long == "Unknown" {
            unknown.clone()
        } else {
            sc.get(&long).cloned().unwrap_or_default()
        };
        let mut x = subtract(&own, &ext_listed);
        x.extend(ext.get(&long).cloned().unwrap_or_default());
        // A name that is both short and long (`Ahom`) is listed once.
        let mut names: Vec<String> = Vec::new();
        for n in v {
            if !names.contains(&n) {
                names.push(n);
            }
        }
        out.push(ScriptData {
            long,
            names,
            scx: merge(x),
            sc: own,
        });
    }
    Ok(out)
}

/// The text of the script tables, as rustfmt writes it.
fn render_scripts(out: &mut String) -> Result<(), String> {
    let all = scripts()?;
    for s in &all {
        let long = &s.long;
        let up = long.to_ascii_uppercase();
        pairs(
            out,
            &format!("SCRIPT_{up}"),
            &format!("The code points whose Script is {long}."),
            &s.sc,
        );
        if s.scx != s.sc {
            pairs(
                out,
                &format!("SCRIPT_EXT_{up}"),
                &format!("The code points whose Script_Extensions include {long}."),
                &s.scx,
            );
        }
    }
    out.push_str("/// A value of the `Script` property.\n");
    out.push_str("#[derive(Debug, Clone, Copy)]\npub struct Script {\n");
    out.push_str("    /// Every name of the value: short name, long name, further aliases.\n");
    out.push_str("    pub names: &'static [&'static str],\n");
    out.push_str("    /// The code points with `Script` this value.\n");
    out.push_str("    pub sc: &'static [(u32, u32)],\n");
    out.push_str("    /// The code points whose `Script_Extensions` include this value.\n");
    out.push_str("    pub scx: &'static [(u32, u32)],\n}\n\n");
    out.push_str("/// The `Script` values of `PropertyValueAliases.txt`, by long name.\n");
    out.push_str("pub static SCRIPTS: &[Script] = &[\n");
    for s in &all {
        let long = &s.long;
        let up = long.to_ascii_uppercase();
        let names: Vec<String> = s.names.iter().map(|n| format!("\"{n}\"")).collect();
        let ext = if s.scx == s.sc {
            format!("SCRIPT_{up}")
        } else {
            format!("SCRIPT_EXT_{up}")
        };
        let _ = writeln!(
            out,
            "    Script {{\n        names: &[{}],\n        sc: SCRIPT_{up},\n        scx: {ext},\n    }},",
            names.join(", ")
        );
    }
    out.push_str("];\n\n");
    Ok(())
}

/// The six sequence types and where each is listed.
const STRING_TYPES: [(&str, &str); 6] = [
    ("Basic_Emoji", "emoji-sequences.txt"),
    ("Emoji_Keycap_Sequence", "emoji-sequences.txt"),
    ("RGI_Emoji_Flag_Sequence", "emoji-sequences.txt"),
    ("RGI_Emoji_Modifier_Sequence", "emoji-sequences.txt"),
    ("RGI_Emoji_Tag_Sequence", "emoji-sequences.txt"),
    ("RGI_Emoji_ZWJ_Sequence", "emoji-zwj-sequences.txt"),
];

type Strings = (Vec<(u32, u32)>, Vec<Vec<u32>>);

/// A property of strings: its one-character members as ranges, and its
/// longer strings in file order.
fn string_property(name: &str, file: &str) -> Result<Strings, String> {
    let mut chars = Vec::new();
    let mut strings: Vec<Vec<u32>> = Vec::new();
    for row in rows(&data(file)?) {
        if let [cps, ty, ..] = row.as_slice()
            && ty == name
        {
            if cps.contains(' ') {
                let s: Vec<u32> = cps.split(' ').map(hex).collect::<Result<_, _>>()?;
                if strings.contains(&s) {
                    return Err(format!("{name}: {cps} twice"));
                }
                strings.push(s);
            } else {
                chars.push(range(cps)?);
            }
        }
    }
    Ok((merge(chars), strings))
}

fn render_strings(out: &mut String) -> Result<(), String> {
    let mut with_chars = 0usize;
    for (name, file) in STRING_TYPES {
        let (chars, strings) = string_property(name, file)?;
        if strings.is_empty() {
            return Err(format!("{name}: no sequences"));
        }
        let up = name.to_ascii_uppercase();
        if !chars.is_empty() {
            with_chars = with_chars.saturating_add(1);
            if name != "Basic_Emoji" {
                return Err(format!("{name}: one-character members"));
            }
        }
        pairs(
            out,
            &format!("STRING_CHARS_{up}"),
            &format!("The one-character members of {name}, as ranges."),
            &chars,
        );
        let _ = writeln!(
            out,
            "/// The members of {name} of two or more code points, in the order of the file.\npub static STRINGS_{up}: &[&str] = &["
        );
        for s in &strings {
            let lit: String = s.iter().map(|c| format!("\\u{{{c:X}}}")).collect();
            let _ = writeln!(out, "    \"{lit}\",");
        }
        out.push_str("];\n\n");
    }
    if with_chars != 1 {
        return Err("only Basic_Emoji has one-character members".into());
    }
    out.push_str("/// A property of strings (UTS #51 ED-27, for `\\p{..}` with `v`).\n");
    out.push_str("#[derive(Debug, Clone, Copy)]\npub struct StringProperty {\n");
    out.push_str("    /// The name (the short name is the same).\n");
    out.push_str("    pub name: &'static str,\n");
    out.push_str("    /// Its one-character members.\n");
    out.push_str("    pub chars: &'static [(u32, u32)],\n");
    out.push_str("    /// Its longer members, as several lists (their union).\n");
    out.push_str("    pub strings: &'static [&'static [&'static str]],\n}\n\n");
    out.push_str(
        "/// The properties of strings; `RGI_Emoji` is the union of the six sequence types.\n",
    );
    out.push_str("pub static STRING_PROPERTIES: &[StringProperty] = &[\n");
    for (name, _) in STRING_TYPES {
        let up = name.to_ascii_uppercase();
        let _ = writeln!(
            out,
            "    StringProperty {{\n        name: \"{name}\",\n        chars: STRING_CHARS_{up},\n        strings: &[STRINGS_{up}],\n    }},"
        );
    }
    let all: Vec<String> = STRING_TYPES
        .iter()
        .map(|(n, _)| format!("            STRINGS_{},", n.to_ascii_uppercase()))
        .collect();
    let _ = writeln!(
        out,
        "    StringProperty {{\n        name: \"RGI_Emoji\",\n        chars: STRING_CHARS_BASIC_EMOJI,\n        strings: &[\n{}\n        ],\n    }},",
        all.join("\n")
    );
    out.push_str("];\n");
    Ok(())
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
    out.push_str("];\n\n");
    render_scripts(&mut out)?;
    render_strings(&mut out)?;
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

// ---------------------------------------------------------------------------
// Script, Script_Extensions and the properties of strings.

#[test]
fn every_script_name_resolves() -> Result<(), String> {
    use clazel_js_regexp::props::UcdScripts;
    use clazel_js_regexp::unicode::script_property;
    use clazel_js_regexp::{Flags, Names, compile, parse};
    let u = Flags {
        unicode: true,
        ..Flags::default()
    };
    // Every name in the generated table, and the table's own consistency.
    let mut seen = std::collections::BTreeSet::new();
    for s in tables::SCRIPTS {
        assert!(!s.names.is_empty(), "{:?}", s.names);
        for n in s.names {
            assert!(seen.insert(*n), "{n} names two scripts");
            for ext in [false, true] {
                assert!(script_property(n, ext).is_some(), "{n}");
            }
            assert!(UcdScripts.is_script(n));
            for prop in ["sc", "Script", "scx", "Script_Extensions"] {
                let text: Vec<u16> = format!("\\p{{{prop}={n}}}").encode_utf16().collect();
                let pat = parse(&text, u).map_err(|e| format!("{prop}={n}: {e}"))?;
                compile(&pat, u).map_err(|e| format!("{prop}={n}: {e}"))?;
            }
        }
        for table in [s.sc, s.scx] {
            for w in table.windows(2) {
                if let [a, b] = w {
                    assert!(a.1.saturating_add(1) < b.0, "{:?}: {a:?} {b:?}", s.names);
                }
            }
            assert!(table.iter().all(|&(a, b)| a <= b && b <= LAST));
        }
    }
    // Case, spelling and neighbours are not names.
    for n in ["latin", "LATIN", "Latn ", "Latin_", "Klingon", "Zzzzz", ""] {
        assert!(script_property(n, false).is_none(), "{n:?}");
        assert!(!UcdScripts.is_script(n));
    }
    // Spot checks of well-known names.
    for n in [
        "Latin",
        "Latn",
        "Greek",
        "Grek",
        "Common",
        "Zyyy",
        "Inherited",
        "Zinh",
        "Qaai",
        "Unknown",
        "Zzzz",
        "Hrkt",
        "Han",
        "Hani",
        "Nko",
        "Nkoo",
    ] {
        assert!(seen.contains(n), "{n}");
    }
    assert!(tables::SCRIPTS.len() > 150);
    Ok(())
}

/// The scripts and extensions the files give each code point, read again and
/// without the generator's helpers: `Script` as a name per code point (a gap
/// is `Unknown`), `Script_Extensions` as the short names of each row.
#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn scripts_agree_with_the_ucd_for_every_code_point() -> Result<(), String> {
    use clazel_js_regexp::unicode::script_property;
    let n = LAST as usize + 1;
    let mut long_of_short: BTreeMap<String, String> = BTreeMap::new();
    for line in data("PropertyValueAliases.txt")?.lines() {
        let body = line.split('#').next().unwrap_or("");
        let f: Vec<&str> = body.split(';').map(str::trim).collect();
        if let [kind, short, long, ..] = f.as_slice()
            && *kind == "sc"
        {
            long_of_short.insert((*short).to_string(), (*long).to_string());
        }
    }
    let longs: Vec<&String> = long_of_short.values().collect();
    let mut sc: Vec<&str> = vec!["Unknown"; n];
    for line in data("Scripts.txt")?.lines() {
        let body = line.split('#').next().unwrap_or("");
        if let Some((r, name)) = body.split_once(';') {
            let (a, b) = range(r.trim())?;
            let name = longs
                .iter()
                .find(|l| l.as_str() == name.trim())
                .ok_or_else(|| name.to_string())?;
            for cp in a..=b {
                let slot = sc.get_mut(cp as usize).ok_or("range")?;
                if *slot != "Unknown" {
                    return Err(format!("{cp:X} listed twice"));
                }
                *slot = name.as_str();
            }
        }
    }
    let mut scx: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for line in data("ScriptExtensions.txt")?.lines() {
        let body = line.split('#').next().unwrap_or("");
        if let Some((r, names)) = body.split_once(';') {
            let (a, b) = range(r.trim())?;
            let list: Vec<String> = names
                .split_whitespace()
                .map(|s| long_of_short.get(s).cloned().ok_or_else(|| s.to_string()))
                .collect::<Result<_, _>>()?;
            for cp in a..=b {
                scx.insert(cp as usize, list.clone());
            }
        }
    }
    // Every code point is in the table of its script and of each of its
    // extensions; and the tables hold no more than that (their sizes add up
    // to exactly the code points, and the (code point, script) pairs).
    let mut pairs_expected = 0usize;
    for cp in 0..n {
        let c = u32::try_from(cp).map_err(|e| e.to_string())?;
        let own = sc.get(cp).copied().unwrap_or("Unknown");
        let in_sc = script_property(own, false).ok_or_else(|| own.to_string())?;
        if !in_sc.contains(c) {
            return Err(format!("{c:X}: not in Script={own}"));
        }
        let list = scx
            .get(&cp)
            .cloned()
            .unwrap_or_else(|| vec![own.to_string()]);
        pairs_expected = pairs_expected.saturating_add(list.len());
        for l in &list {
            let p = script_property(l, true).ok_or_else(|| l.clone())?;
            if !p.contains(c) {
                return Err(format!("{c:X}: not in Script_Extensions={l}"));
            }
        }
    }
    let size = |t: &[(u32, u32)]| {
        t.iter()
            .map(|&(a, b)| usize::try_from(b.saturating_sub(a)).map_or(0, |d| d.saturating_add(1)))
            .fold(0usize, usize::saturating_add)
    };
    let sc_total: usize = tables::SCRIPTS.iter().map(|s| size(s.sc)).sum();
    let scx_total: usize = tables::SCRIPTS.iter().map(|s| size(s.scx)).sum();
    if sc_total != n {
        return Err(format!(
            "Script tables hold {sc_total} code points, not {n}"
        ));
    }
    if scx_total != pairs_expected {
        return Err(format!(
            "Script_Extensions tables hold {scx_total} pairs, the files give {pairs_expected}"
        ));
    }
    println!(
        "clazel-conformance: suite=\"UCD scripts per code point\" pass={n} xfail=0 fail=0 total={n}"
    );
    Ok(())
}

/// The sequences of the emoji files, read again, against the tables.
#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn string_properties_agree_with_the_emoji_files() -> Result<(), String> {
    use clazel_js_regexp::props::STRING_PROPERTIES as NAMES;
    use clazel_js_regexp::unicode::{StringSet, string_property};
    use std::collections::BTreeSet;
    type Members = (BTreeSet<u32>, BTreeSet<Vec<u32>>);
    let mut by_type: BTreeMap<String, Members> = BTreeMap::new();
    for file in ["emoji-sequences.txt", "emoji-zwj-sequences.txt"] {
        for row in rows(&data(file)?) {
            if let [cps, ty, ..] = row.as_slice() {
                let e = by_type.entry(ty.clone()).or_default();
                if cps.contains(' ') {
                    let s: Vec<u32> = cps.split(' ').map(hex).collect::<Result<_, _>>()?;
                    e.1.insert(s);
                } else {
                    let (a, b) = range(cps)?;
                    e.0.extend(a..=b);
                }
            }
        }
    }
    assert_eq!(by_type.len(), 6, "{:?}", by_type.keys());
    let members = |set: &StringSet| -> Members {
        let chars = (0..=LAST).filter(|&c| set.chars.contains(c)).collect();
        (chars, set.strings.iter().cloned().collect())
    };
    let mut union: Members = Members::default();
    for (ty, want) in &by_type {
        let set = string_property(ty).ok_or_else(|| ty.clone())?;
        let got = members(&set);
        if &got != want {
            return Err(format!("{ty}: the table differs from the file"));
        }
        if set.strings.len() != got.1.len() {
            return Err(format!("{ty}: a string twice"));
        }
        union.0.extend(want.0.iter());
        union.1.extend(want.1.iter().cloned());
        assert!(want.1.iter().all(|s| s.len() >= 2));
    }
    let all = string_property("RGI_Emoji").ok_or("RGI_Emoji")?;
    if members(&all) != union {
        return Err("RGI_Emoji is not the union of the six".into());
    }
    assert_eq!(
        all.strings.len(),
        union.1.len(),
        "RGI_Emoji repeats a string"
    );
    for name in NAMES {
        let name = String::from_utf8_lossy(name);
        assert!(string_property(&name).is_some(), "{name}");
    }
    assert!(string_property("Emoji").is_none());
    assert!(string_property("basic_emoji").is_none());
    assert!(union.1.len() > 2500, "{}", union.1.len());
    Ok(())
}

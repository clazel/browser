//! The property names `\p{..}` accepts (`src/props.rs`) against the vendored
//! Unicode 18.0.0 files (`tests/data/ucd-regexp/`, phase-7.md item 7.1), and
//! the `Script` check the parser takes through [`Names`], read from the same
//! files.
//!
//! - **Suite "UCD General_Category values"**: the `gc` rows of
//!   `PropertyValueAliases.txt` and the parser's list are the same set of
//!   names; each is accepted as `\p{gc=..}` and as a lone name. A unit is a
//!   name.
//! - **Suite "UCD binary properties"**: each property of ECMA-262's table that
//!   Unicode defines is a row of `PropertyAliases.txt` with the table's
//!   canonical name and alias (`ASCII`, `Any` and `Assigned` are the
//!   standard's own). A unit is a property.
//! - **Suite "UCD properties of strings"**: each is a type of
//!   `emoji-sequences.txt` or `emoji-zwj-sequences.txt` (`RGI_Emoji` is their
//!   union). A unit is a property.
//! - **Suite "UCD script names"**: every `sc` value is accepted by `\p{sc=..}`
//!   and `\p{scx=..}` with the script table read from the file, and a name
//!   that is not one is not. A unit is a name.

use clazel_js_regexp::props::{
    BINARY_NAMES, BINARY_PROPERTIES, GENERAL_CATEGORY_VALUES, STRING_PROPERTIES,
    is_binary_property, is_general_category, is_string_property,
};
use clazel_js_regexp::{Flags, Names, parse, parse_with};
use std::collections::BTreeSet;
use std::path::PathBuf;

fn data(file: &str) -> Result<String, String> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/data/ucd-regexp")
        .join(file);
    std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))
}

/// The rows of a UCD file: the `;`-separated fields of each line, comments
/// removed.
fn rows(text: &str) -> Vec<Vec<String>> {
    text.lines()
        .map(|l| l.split('#').next().unwrap_or_default())
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.split(';').map(|f| f.trim().to_string()).collect())
        .collect()
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn u_flags() -> Flags {
    Flags {
        unicode: true,
        ..Flags::default()
    }
}

fn v_flags() -> Flags {
    Flags {
        unicode_sets: true,
        ..Flags::default()
    }
}

struct Scripts(BTreeSet<String>);

impl Names for Scripts {
    fn is_script(&self, value: &str) -> bool {
        self.0.contains(value)
    }
}

fn report(suite: &str, bad: &[String], total: usize) {
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={} xfail=0 fail={} total={total}",
        total.saturating_sub(bad.len()),
        bad.len()
    );
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn general_category_values() -> Result<(), String> {
    let aliases = data("PropertyValueAliases.txt")?;
    let ucd: BTreeSet<String> = rows(&aliases)
        .into_iter()
        .filter(|r| r.first().is_some_and(|p| p == "gc"))
        .flat_map(|r| r.into_iter().skip(1))
        .collect();
    let ours: BTreeSet<String> = GENERAL_CATEGORY_VALUES.iter().map(|s| text(s)).collect();
    let mut bad = Vec::new();
    for n in ucd.difference(&ours) {
        bad.push(format!("{n}: in the UCD, not in props.rs"));
    }
    for n in ours.difference(&ucd) {
        bad.push(format!("{n}: in props.rs, not in the UCD"));
    }
    for n in &ucd {
        for text in [
            format!("\\p{{gc={n}}}"),
            format!("\\p{{General_Category={n}}}"),
            format!("\\p{{{n}}}"),
        ] {
            if parse(&units(&text), u_flags()).is_err() {
                bad.push(format!("{text} is rejected"));
            }
        }
        if !is_general_category(n.as_bytes()) {
            bad.push(format!("{n}: is_general_category is false"));
        }
    }
    report("UCD General_Category values", &bad, ucd.len());
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    assert!(ucd.len() > 60);
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn binary_properties() -> Result<(), String> {
    let aliases = data("PropertyAliases.txt")?;
    let table = rows(&aliases);
    let mut bad = Vec::new();
    // The membership test is the list.
    let listed: BTreeSet<String> = BINARY_PROPERTIES
        .iter()
        .flat_map(|(a, b)| [text(a), text(b)])
        .collect();
    let names: BTreeSet<String> = BINARY_NAMES.iter().map(|n| text(n)).collect();
    if listed != names {
        bad.push("BINARY_NAMES is not the names of BINARY_PROPERTIES".into());
    }
    for &(full, alias) in BINARY_PROPERTIES {
        let (full, alias) = (text(full), text(alias));
        let (full, alias) = (full.as_str(), alias.as_str());
        let standards_own = matches!(full, "ASCII" | "Any" | "Assigned");
        let in_ucd = table
            .iter()
            .any(|r| r.iter().any(|f| f == full) && r.iter().any(|f| f == alias));
        if !standards_own && !in_ucd {
            bad.push(format!(
                "{full} ({alias}): no such row in PropertyAliases.txt"
            ));
        }
        for name in [full, alias] {
            if !is_binary_property(name.as_bytes())
                || parse(&units(&format!("\\p{{{name}}}")), u_flags()).is_err()
            {
                bad.push(format!("{name} is rejected"));
            }
        }
    }
    // Spot checks of what is not accepted: case, loose matching, non-binary.
    for name in [
        "alphabetic",
        "ALPHABETIC",
        "Alpha_betic",
        "Script",
        "Letter_Number_x",
        "RGI_Emoji",
    ] {
        if parse(&units(&format!("\\p{{{name}}}")), u_flags()).is_ok() {
            bad.push(format!("{name} is accepted"));
        }
    }
    report("UCD binary properties", &bad, BINARY_PROPERTIES.len());
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn properties_of_strings() -> Result<(), String> {
    let mut types: BTreeSet<String> = BTreeSet::new();
    for file in ["emoji-sequences.txt", "emoji-zwj-sequences.txt"] {
        for r in rows(&data(file)?) {
            if let Some(t) = r.get(1) {
                types.insert(t.clone());
            }
        }
    }
    let mut bad = Vec::new();
    for &name in STRING_PROPERTIES {
        let name = text(name);
        let name = name.as_str();
        if name != "RGI_Emoji" && !types.contains(name) {
            bad.push(format!("{name}: not a type in the emoji sequence files"));
        }
        if !is_string_property(name.as_bytes()) {
            bad.push(format!("{name}: is_string_property is false"));
        }
        let p = format!("\\p{{{name}}}");
        if parse(&units(&p), v_flags()).is_err() {
            bad.push(format!("{p} is rejected with v"));
        }
        if parse(&units(&p), u_flags()).is_ok() {
            bad.push(format!("{p} is accepted with u"));
        }
        let neg = format!("\\P{{{name}}}");
        if parse(&units(&neg), v_flags()).is_ok() {
            bad.push(format!("{neg} is accepted"));
        }
    }
    report("UCD properties of strings", &bad, STRING_PROPERTIES.len());
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn script_names() -> Result<(), String> {
    let aliases = data("PropertyValueAliases.txt")?;
    let scripts: BTreeSet<String> = rows(&aliases)
        .into_iter()
        .filter(|r| r.first().is_some_and(|p| p == "sc"))
        .flat_map(|r| r.into_iter().skip(1))
        .collect();
    let names = Scripts(scripts.clone());
    let mut bad = Vec::new();
    for s in &scripts {
        for prop in ["sc", "Script", "scx", "Script_Extensions"] {
            let text = format!("\\p{{{prop}={s}}}");
            if parse_with(&units(&text), u_flags(), &names).is_err() {
                bad.push(format!("{text} is rejected"));
            }
        }
    }
    for s in ["Latin_", "latin", "Klingon", "Zzzzz"] {
        let text = format!("\\p{{sc={s}}}");
        if parse_with(&units(&text), u_flags(), &names).is_ok() {
            bad.push(format!("{text} is accepted"));
        }
    }
    // The generated table (what `parse` uses) holds the same names.
    let ours: BTreeSet<String> = clazel_js_regexp::tables::SCRIPTS
        .iter()
        .flat_map(|s| s.names.iter().map(|n| (*n).to_string()))
        .collect();
    for n in scripts.difference(&ours) {
        bad.push(format!("{n}: in the UCD, not in tables::SCRIPTS"));
    }
    for n in ours.difference(&scripts) {
        bad.push(format!("{n}: in tables::SCRIPTS, not in the UCD"));
    }
    for s in &scripts {
        let text = format!("\\p{{sc={s}}}");
        if parse(&units(&text), u_flags()).is_err() {
            bad.push(format!("{text} is rejected by parse"));
        }
    }
    report("UCD script names", &bad, scripts.len());
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    assert!(scripts.len() > 150);
    Ok(())
}

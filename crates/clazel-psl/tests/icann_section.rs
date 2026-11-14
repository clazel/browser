//! The list's ICANN section (`clazel_psl::exec::is_icann_public_suffix_exec`),
//! against a second reading of `public_suffix_list.dat` that is none of
//! `xtask/src/psl.rs`'s code: the file is cut at the section's end marker, and
//! each side's entries must give the answer their section says.

use clazel_psl::data::{PSL_ICANN_RULES_LEN, PSL_RULES_LEN};
use clazel_psl::exec::{is_icann_public_suffix_exec, is_public_suffix_exec};

const LIST: &str = include_str!("../data/publicsuffix-5dd321ff/public_suffix_list.dat");

/// The entries of `text`: the first word of each line that holds a rule.
fn entries(text: &str) -> Vec<&str> {
    text.lines()
        .filter_map(|line| line.split_whitespace().next())
        .filter(|word| !word.starts_with("//"))
        .collect()
}

fn sections() -> Result<(Vec<&'static str>, Vec<&'static str>), String> {
    let (icann, private) = LIST
        .split_once("===END ICANN DOMAINS===")
        .ok_or("no end marker")?;
    Ok((entries(icann), entries(private)))
}

fn wide(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// An ASCII entry that names one suffix: no wildcard, no exception.
fn plain(entry: &str) -> bool {
    entry.is_ascii() && !entry.starts_with('*') && !entry.starts_with('!')
}

#[test]
#[cfg_attr(miri, ignore = "scans the 300 kB list")]
fn the_generated_count_is_the_sections_length() -> Result<(), String> {
    let (icann, private) = sections()?;
    assert_eq!(icann.len(), PSL_ICANN_RULES_LEN);
    assert_eq!(icann.len().saturating_add(private.len()), PSL_RULES_LEN);
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "looks up every entry of the list")]
fn every_icann_entry_is_an_icann_public_suffix() -> Result<(), String> {
    let (icann, _) = sections()?;
    for entry in icann.into_iter().filter(|e| plain(e)) {
        assert!(is_icann_public_suffix_exec(&wide(entry)), "{entry}");
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "looks up every entry of the list")]
fn a_private_entry_is_a_public_suffix_but_not_an_icann_one() -> Result<(), String> {
    let (icann, private) = sections()?;
    // An ICANN wildcard covers a private entry directly under it.
    let covered = |entry: &str| {
        entry
            .split_once('.')
            .is_some_and(|(_, parent)| icann.contains(&format!("*.{parent}").as_str()))
    };
    let mut checked = 0usize;
    for entry in private.into_iter().filter(|e| plain(e)) {
        if !icann.contains(&entry) && !covered(entry) {
            assert!(is_public_suffix_exec(&wide(entry)), "{entry}");
            assert!(!is_icann_public_suffix_exec(&wide(entry)), "{entry}");
            checked = checked.saturating_add(1);
        }
    }
    assert!(checked > 3000, "{checked}");
    Ok(())
}

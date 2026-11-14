//! The tokenizer's non-ASCII ident code points against the standard's table, on both sides
//! of every boundary and, outside Miri, for every code point.
//!
//! `src/tokenizer/spec.rs` writes the 15 ranges of "non-ASCII ident code point" in one
//! expression, so a typo in a bound is a single wrong constant; the spec's examples
//! check one code point of it. This file has the table again, copied by hand from the
//! standard and not from `spec.rs`, and runs the executable tokenizer on the code points
//! around each bound.
//!
//! The table is CSS Syntax Module Level 3 §4.2 at the commit the specs are pinned to
//! (`w3c/csswg-drafts` `c410ee5e4d2afe6d8b2e8ce53723b8d1eb3b5b67`,
//! `css-syntax-3/Overview.bs`, the definition `non-ASCII ident code point`): "A code
//! point whose value is any of: U+00B7; between U+00C0 and U+00D6; between U+00D8 and
//! U+00F6; between U+00F8 and U+037D; between U+037F and U+1FFF; U+200C; U+200D; U+203F;
//! U+2040; between U+2070 and U+218F; between U+2C00 and U+2FEF; between U+3001 and
//! U+D7FF; between U+F900 and U+FDCF; between U+FDF0 and U+FFFD; greater than or equal
//! to U+10000. All of these ranges are inclusive." (The last is bounded by U+10FFFF, the
//! largest code point.)
//!
//! A code point is read two ways, both through `tokenize_all`:
//! - alone, where an "ident-start code point" (§4.2: a letter, a non-ASCII ident code
//!   point or `_`) makes an ident token (§4.3.4 "consume an ident-like token"), and
//!   any other non-ASCII code point is a delim token (§4.3.1 "anything else");
//! - after `a`, where an "ident code point" keeps the ident going (§4.3.11 "consume an
//!   ident sequence"), and any other stops it before the code point.
//!
//! Surrogates are not read: "filter code points" (§3.3) replaces them with U+FFFD, so the
//! tokenizer never sees one.

use clazel_css::tokenizer::exec::{ExecToken, tokenize_all};

/// The inclusive ranges of the standard's table, as `(first, last)`.
const TABLE: &[(u32, u32)] = &[
    (0x00B7, 0x00B7),
    (0x00C0, 0x00D6),
    (0x00D8, 0x00F6),
    (0x00F8, 0x037D),
    (0x037F, 0x1FFF),
    (0x200C, 0x200C),
    (0x200D, 0x200D),
    (0x203F, 0x203F),
    (0x2040, 0x2040),
    (0x2070, 0x218F),
    (0x2C00, 0x2FEF),
    (0x3001, 0xD7FF),
    (0xF900, 0xFDCF),
    (0xFDF0, 0xFFFD),
    (0x1_0000, 0x10_FFFF),
];

const MAX: u32 = 0x10_FFFF;

fn in_table(c: u32) -> bool {
    TABLE
        .iter()
        .any(|(first, last)| (*first..=*last).contains(&c))
}

/// `Ok` if the tokenizer reads `c` as the standard says; `Err` says what it did.
fn check(c: u32) -> Result<(), String> {
    let alone = tokenize_all(&[c]);
    let after_a = tokenize_all(&[0x61, c]);
    let (want_alone, want_after) = if in_table(c) {
        (
            vec![ExecToken::Ident { value: vec![c] }, ExecToken::Eof],
            vec![
                ExecToken::Ident {
                    value: vec![0x61, c],
                },
                ExecToken::Eof,
            ],
        )
    } else {
        (
            vec![ExecToken::Delim { value: c }, ExecToken::Eof],
            vec![
                ExecToken::Ident { value: vec![0x61] },
                ExecToken::Delim { value: c },
                ExecToken::Eof,
            ],
        )
    };
    if alone != want_alone {
        return Err(format!(
            "U+{c:04X} alone: got {alone:?}, want {want_alone:?}"
        ));
    }
    if after_a != want_after {
        return Err(format!(
            "U+{c:04X} after a: got {after_a:?}, want {want_after:?}"
        ));
    }
    Ok(())
}

fn is_surrogate(c: u32) -> bool {
    (0xD800..=0xDFFF).contains(&c)
}

/// The code points at and next to every bound of the table: each range's first and last,
/// and the code points just outside them, so a bound that is one too high or too low
/// either way is on the list.
fn around_bounds() -> Vec<u32> {
    let mut points = Vec::new();
    for (first, last) in TABLE {
        for edge in [*first, *last] {
            for c in [edge.saturating_sub(1), edge, edge.saturating_add(1)] {
                if c >= 0x80 && c <= MAX && !is_surrogate(c) {
                    points.push(c);
                }
            }
        }
    }
    points.sort_unstable();
    points.dedup();
    points
}

#[test]
fn both_sides_of_every_boundary() {
    let points = around_bounds();
    // 15 ranges, 2 edges each, 3 code points each, less the overlaps and the code
    // points below U+0080.
    assert!(points.len() > 60, "{} points", points.len());
    let errors: Vec<String> = points.iter().filter_map(|c| check(*c).err()).collect();
    assert!(errors.is_empty(), "{errors:#?}");
}

/// Under Miri the tokenizer is interpreted, about a thousand times slower, so only the
/// boundaries (the test above) are run there; every other run checks every code point.
#[test]
#[cfg_attr(miri, ignore)]
fn every_non_ascii_code_point() {
    let mut errors = Vec::new();
    let mut count = 0usize;
    for c in 0x80..=MAX {
        if is_surrogate(c) {
            continue;
        }
        count = count.saturating_add(1);
        if let Err(error) = check(c) {
            errors.push(error);
        }
    }
    // U+0080 to U+10FFFF is 1,114,112 - 128 code points, less 2,048 surrogates.
    assert_eq!(count, 1_114_112 - 128 - 2_048);
    assert!(
        errors.is_empty(),
        "{} wrong, first {:#?}",
        errors.len(),
        errors.iter().take(10).collect::<Vec<_>>()
    );
}

/// The table has the 15 entries the standard lists, in order and not touching except
/// where the standard's own neighbours do (U+200C and U+200D; U+203F and U+2040), so a
/// slip in the table above is caught here and not by a confusing failure there.
#[test]
fn table_is_the_standards() {
    assert_eq!(TABLE.len(), 15);
    for pair in TABLE.windows(2) {
        let [(_, last), (next_first, _)] = pair else {
            unreachable!("windows(2)")
        };
        assert!(last < next_first);
    }
    for (first, last) in TABLE {
        assert!(first <= last);
    }
}

//! The `ID_Start` and `ID_Continue` tables (`src/unicode_data.rs`, generated
//! from Unicode 18.0.0 by `xtask/src/js_idents.rs`) and their lookups: the
//! shape the bisection relies on, a property Unicode guarantees, and known
//! code points. Nothing about the tables is proven (`src/unicode.rs`).

use clazel_js_lexer::unicode::{Range, id_continue_non_ascii, id_start_non_ascii};
use clazel_js_lexer::unicode_data::{ID_CONTINUE, ID_START};

/// Sorted, disjoint, non-empty rows, all within U+0080..U+10FFFF.
fn well_formed(table: &[Range]) {
    let mut previous: Option<u32> = None;
    for row in table {
        assert!(0x80 <= row.first && row.first <= row.last && row.last <= 0x10_FFFF);
        if let Some(p) = previous {
            // Maximal ranges: not even adjacent.
            assert!(p.saturating_add(1) < row.first);
        }
        previous = Some(row.last);
    }
}

#[test]
fn tables_are_sorted_and_disjoint() {
    well_formed(&ID_START);
    well_formed(&ID_CONTINUE);
}

/// Every lookup agrees with a linear scan of its table, and `ID_Start` is a
/// subset of `ID_Continue` (Unicode's stability policy for identifiers).
#[test]
fn lookups_agree_with_the_tables() {
    let in_table = |table: &[Range], c: u32| table.iter().any(|r| r.first <= c && c <= r.last);
    // Each linear scan reads about 800 rows, so natively every 7th code
    // point (all of them would take minutes in a debug build) plus every
    // row's ends; under Miri, which interprets each step, a wider stride of
    // both.
    let (stride, row_stride) = if cfg!(miri) { (40_009, 97) } else { (7, 1) };
    let mut points: Vec<u32> = (0..=0x11_0000u32).step_by(stride).collect();
    for row in ID_START
        .iter()
        .chain(ID_CONTINUE.iter())
        .step_by(row_stride)
    {
        points.extend([
            row.first.saturating_sub(1),
            row.first,
            row.last,
            row.last.saturating_add(1),
        ]);
    }
    for c in points {
        let start = id_start_non_ascii(c);
        let cont = id_continue_non_ascii(c);
        assert_eq!(start, c >= 0x80 && in_table(&ID_START, c), "U+{c:04X}");
        assert_eq!(cont, c >= 0x80 && in_table(&ID_CONTINUE, c), "U+{c:04X}");
        assert!(!start || cont, "U+{c:04X} is ID_Start but not ID_Continue");
    }
}

#[test]
fn known_code_points() {
    for c in [0xE9, 0xAA, 0x212E, 0x65E5, 0x1_0400, 0x2_0000, 0x3_134A] {
        assert!(id_start_non_ascii(c), "U+{c:04X} is ID_Start");
    }
    for c in [0x300, 0x661, 0x200C, 0x200D, 0xB7, 0x1369] {
        assert!(!id_start_non_ascii(c), "U+{c:04X} is not ID_Start");
        assert!(id_continue_non_ascii(c), "U+{c:04X} is ID_Continue");
    }
    for c in [
        0x7F, 0x80, 0xA0, 0xD7, 0x2028, 0x2E2F, 0xD800, 0xFEFF, 0x1_F600, 0x10_FFFF, 0x11_0000,
    ] {
        assert!(!id_continue_non_ascii(c), "U+{c:04X} is not ID_Continue");
    }
    // ASCII is not in the tables (the spec defines it).
    for c in 0..0x80 {
        assert!(!id_start_non_ascii(c) && !id_continue_non_ascii(c));
    }
}

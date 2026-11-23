//! The `ID_Start` and `ID_Continue` tables (`src/unicode_data.rs`, generated
//! from Unicode 18.0.0 by `xtask/src/js_idents.rs`) and their lookups: the
//! shape the bisection relies on, a property Unicode guarantees, and known
//! code points, and a second derivation from the file. `src/unicode.rs`
//! proves the lookups are the spec's predicates; that the tables are the
//! Unicode properties is checked here, not proven.

use clazel_js_lexer::unicode::{Range, id_continue_non_ascii, id_start_non_ascii};
use clazel_js_lexer::unicode_data::{
    ID_CONTINUE_LEN, ID_START_LEN, id_continue_at_exec, id_start_at_exec,
};

/// The rows of `ID_Start`, through the accessor the lookups use.
fn id_start_rows() -> Vec<Range> {
    (0..ID_START_LEN).map(id_start_at_exec).collect()
}

/// The rows of `ID_Continue`.
fn id_continue_rows() -> Vec<Range> {
    (0..ID_CONTINUE_LEN).map(id_continue_at_exec).collect()
}

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
    well_formed(&id_start_rows());
    well_formed(&id_continue_rows());
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
    let (id_start, id_continue) = (id_start_rows(), id_continue_rows());
    for row in id_start
        .iter()
        .chain(id_continue.iter())
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
        assert_eq!(start, c >= 0x80 && in_table(&id_start, c), "U+{c:04X}");
        assert_eq!(cont, c >= 0x80 && in_table(&id_continue, c), "U+{c:04X}");
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

/// A second derivation of the two properties from `DerivedCoreProperties.txt`
/// (the file the generator reads), with a parser of its own that shares no
/// code with `xtask`: a bitmap per property over every code point. Every
/// code point U+0080..U+10FFFF is compared with both lookups, each way: a
/// code point the file lists must be found, and one it does not list must
/// not be.
#[test]
#[cfg_attr(miri, ignore = "reads files")]
fn lookups_equal_the_file_for_every_code_point() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../clazel-js-regexp/tests/data/ucd-regexp/DerivedCoreProperties.txt");
    let text = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(!text.is_empty(), "cannot read {}", path.display());
    let mut start = vec![false; 0x11_0000];
    let mut cont = vec![false; 0x11_0000];
    for line in text.lines() {
        // `<hex>[..<hex>] ; <Property> # comment`
        let body = line.split('#').next().unwrap_or("");
        let Some((cps, prop)) = body.split_once(';') else {
            continue;
        };
        let (cps, prop) = (cps.trim(), prop.trim());
        let bitmap = match prop {
            "ID_Start" => &mut start,
            "ID_Continue" => &mut cont,
            _ => continue,
        };
        let (lo, hi) = match cps.split_once("..") {
            Some((a, b)) => (a, b),
            None => (cps, cps),
        };
        let (Ok(lo), Ok(hi)) = (usize::from_str_radix(lo, 16), usize::from_str_radix(hi, 16))
        else {
            assert!(line.is_empty(), "not a hex range: {line}");
            continue;
        };
        let Some(slots) = bitmap.get_mut(lo..=hi) else {
            assert!(line.is_empty(), "range outside U+10FFFF: {line}");
            continue;
        };
        slots.fill(true);
    }
    // The file lists both properties (ASCII letters are the first rows).
    let at = |bitmap: &[bool], c: usize| bitmap.get(c).copied().unwrap_or(false);
    assert!(at(&start, 0x41) && at(&cont, 0x30) && at(&cont, 0x5F) && !at(&start, 0x5F));
    for (i, (&s, &c)) in (0u32..).zip(start.iter().zip(cont.iter())) {
        if i < 0x80 {
            continue;
        }
        assert_eq!(id_start_non_ascii(i), s, "ID_Start U+{i:04X}");
        assert_eq!(id_continue_non_ascii(i), c, "ID_Continue U+{i:04X}");
    }
}

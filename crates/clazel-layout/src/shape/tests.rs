//! Unit tests of the kerning passes from the OpenType chapters' pair
//! kerning examples: gpos, "Example 4: PairPosFormat1 Subtable" and
//! "Example 5: PairPosFormat2 Subtable", each wrapped in the smallest
//! `GPOS` table that lists it as the `DFLT` script's `kern` feature.

use clazel_font::Error;
use clazel_font::kern::Kern;
use clazel_font::layout::Gpos;

use super::kerning::{self, PairSource};
use super::{Script, UnitGlyph};

/// Big-endian bytes of `words`.
fn words(words: &[u16]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_be_bytes()).collect()
}

/// A `GPOS` 1.0 table whose `DFLT` script's default LangSys has one
/// feature, `kern`, with one lookup of type 2 holding `subtable`.
fn gpos_with(subtable: &[u16]) -> Vec<u8> {
    let mut w = vec![
        1, 0, 10, 30, 44, // header: version 1.0, ScriptList, FeatureList, LookupList
        // ScriptList (at 10): one ScriptRecord, DFLT at 8.
        1, 0x4446, 0x4C54, 8, // Script (at 18): defaultLangSys at 4, no LangSysRecords.
        4, 0, // LangSys (at 22): no lookupOrder, no required feature, feature 0.
        0, 0xFFFF, 1, 0, // FeatureList (at 30): one FeatureRecord, kern at 8.
        1, 0x6B65, 0x726E, 8, // Feature (at 38): no params, lookup 0.
        0, 1, 0, // LookupList (at 44): one lookup at 4.
        1, 4, // Lookup (at 48): type 2, flag 0, one subtable at 8.
        2, 0, 1, 8,
    ];
    w.extend_from_slice(subtable);
    words(&w)
}

/// gpos, Example 4: PairPosFormat1 kerning "Po" and "To" (P 0x2D, T 0x31,
/// o 0x59): `valueRecord1.xAdvance` -30 and -40, `valueRecord2.xPlacement`
/// -20 and -25.
const EXAMPLE_4: &[u16] = &[
    1, 0x1E, 0x0004, 0x0001, 2, 0x0E, 0x16, // PairPosFormat1
    1, 0x59, 0xFFE2, 0xFFEC, // PairSet for P
    1, 0x59, 0xFFD8, 0xFFE7, // PairSet for T
    1, 2, 0x2D, 0x31, // Coverage
];

/// gpos, Example 5: PairPosFormat2, v, w, y (0x46, 0x47, 0x49) before
/// period or comma (0x6A, 0x6B): `valueRecord1.xAdvance` -50, no second
/// record (`valueFormat2` 0).
const EXAMPLE_5: &[u16] = &[
    2, 0x18, 0x0004, 0x0000, 0x22, 0x32, 2, 2, // PairPosFormat2
    0, 0, 0, 0xFFCE, // class1Records
    1, 3, 0x46, 0x47, 0x49, // Coverage
    2, 2, 0x46, 0x47, 1, 0x49, 0x49, 1, // LowercaseClassDef
    2, 1, 0x6A, 0x6B, 1, // PunctuationClassDef
];

/// A run of `glyphs`, each with advance 500, the ones in `marks` being
/// marks with advance 0.
fn run(glyphs: &[u16], marks: &[usize]) -> Vec<UnitGlyph> {
    glyphs
        .iter()
        .enumerate()
        .map(|(i, &glyph)| {
            let mark = marks.contains(&i);
            UnitGlyph {
                glyph,
                cluster: i,
                mark,
                x_advance: if mark { 0 } else { 500 },
                x_offset: 0,
                y_offset: 0,
            }
        })
        .collect()
}

/// (advance, x offset) of each glyph.
fn positions(glyphs: &[UnitGlyph]) -> Vec<(i32, i32)> {
    glyphs.iter().map(|g| (g.x_advance, g.x_offset)).collect()
}

fn gpos_source(table: &[u8]) -> Result<PairSource<'_>, Error> {
    let gpos = Gpos::parse(table)?;
    let lookups = gpos.kern_lookups(Script::Latin.tag())?;
    assert_eq!(lookups, [0], "latn is not listed, so DFLT's kern feature");
    Ok(PairSource::Gpos(gpos, lookups))
}

#[test]
fn example_4_po_and_to() -> Result<(), Error> {
    let table = gpos_with(EXAMPLE_4);
    let source = gpos_source(&table)?;
    // "Po To": P o space T o.
    let mut g = run(&[0x2D, 0x59, 0x03, 0x31, 0x59], &[]);
    kerning::apply(&mut g, &source);
    assert_eq!(
        positions(&g),
        [(470, 0), (500, -20), (500, 0), (460, 0), (500, -25)]
    );
    Ok(())
}

#[test]
fn example_4_resumes_after_a_positioned_second_glyph() -> Result<(), Error> {
    let table = gpos_with(EXAMPLE_4);
    let source = gpos_source(&table)?;
    // P o T o: after (P, o), whose second record is non-zero, the pass
    // resumes at T, not at o, and (T, o) is kerned.
    let mut g = run(&[0x2D, 0x59, 0x31, 0x59], &[]);
    kerning::apply(&mut g, &source);
    assert_eq!(positions(&g), [(470, 0), (500, -20), (460, 0), (500, -25)]);
    // P T o: (P, T) is not a pair, so the pass moves to T.
    let mut g = run(&[0x2D, 0x31, 0x59], &[]);
    kerning::apply(&mut g, &source);
    assert_eq!(positions(&g), [(500, 0), (460, 0), (500, -25)]);
    Ok(())
}

#[test]
fn example_4_skips_marks() -> Result<(), Error> {
    let table = gpos_with(EXAMPLE_4);
    let source = gpos_source(&table)?;
    // P, a combining mark, o: P is kerned against o; the mark keeps its
    // zero advance and no offset.
    let mut g = run(&[0x2D, 0x100, 0x59], &[1]);
    kerning::apply(&mut g, &source);
    assert_eq!(positions(&g), [(470, 0), (0, 0), (500, -20)]);
    // A run that starts with a mark starts pairing at its first base.
    let mut g = run(&[0x100, 0x31, 0x59], &[0]);
    kerning::apply(&mut g, &source);
    assert_eq!(positions(&g), [(0, 0), (460, 0), (500, -25)]);
    Ok(())
}

#[test]
fn example_5_class_pairs() -> Result<(), Error> {
    let table = gpos_with(EXAMPLE_5);
    let source = gpos_source(&table)?;
    // "y.w,v x": every lowercase-punctuation pair gets -50; the second
    // record is empty, so (comma, v) is tried next and is not covered.
    let mut g = run(&[0x49, 0x6A, 0x47, 0x6B, 0x46, 0x03, 0x48], &[]);
    kerning::apply(&mut g, &source);
    let advances: Vec<i32> = g.iter().map(|g| g.x_advance).collect();
    assert_eq!(advances, [450, 500, 450, 500, 500, 500, 500]);
    assert!(g.iter().all(|g| g.x_offset == 0 && g.y_offset == 0));
    // Two lookups would apply one after the other; one lookup applies once.
    let mut g = run(&[0x46, 0x6A], &[]);
    kerning::apply(&mut g, &source);
    assert_eq!(positions(&g), [(450, 0), (500, 0)]);
    Ok(())
}

/// A version 0 `kern` table with one horizontal format 0 subtable of
/// `pairs`, sorted by (left, right) as chapter `kern` requires.
fn kern_table(pairs: &[(u16, u16, i16)]) -> Vec<u8> {
    let n = u16::try_from(pairs.len()).unwrap_or(0);
    let mut d = words(&[0, 1]);
    let length = n.saturating_mul(6).saturating_add(14);
    d.extend(words(&[0, length, 1, n, 0, 0, 0]));
    for &(l, r, v) in pairs {
        d.extend(words(&[l, r]));
        d.extend_from_slice(&v.to_be_bytes());
    }
    d
}

#[test]
fn kern_table_goes_to_the_first_advance() -> Result<(), Error> {
    // The pairs of Example 4 as a kern table.
    let table = kern_table(&[(0x2D, 0x59, -30), (0x31, 0x59, -40)]);
    let source = PairSource::Kern(Kern::parse(&table)?);
    let mut g = run(&[0x2D, 0x59, 0x31, 0x100, 0x59, 0x59], &[3]);
    kerning::apply(&mut g, &source);
    assert_eq!(
        positions(&g),
        [(470, 0), (500, 0), (460, 0), (0, 0), (500, 0), (500, 0)]
    );
    Ok(())
}

#[test]
fn no_source_no_kerning() {
    let mut g = run(&[0x2D, 0x59], &[]);
    kerning::apply(&mut g, &PairSource::None);
    assert_eq!(positions(&g), [(500, 0), (500, 0)]);
}

#[test]
fn empty_and_single_runs() -> Result<(), Error> {
    let table = gpos_with(EXAMPLE_4);
    let source = gpos_source(&table)?;
    let mut g = run(&[], &[]);
    kerning::apply(&mut g, &source);
    assert!(g.is_empty());
    let mut g = run(&[0x2D], &[]);
    kerning::apply(&mut g, &source);
    assert_eq!(positions(&g), [(500, 0)]);
    let mut g = run(&[0x100, 0x100], &[0, 1]);
    kerning::apply(&mut g, &source);
    assert_eq!(positions(&g), [(0, 0), (0, 0)]);
    Ok(())
}

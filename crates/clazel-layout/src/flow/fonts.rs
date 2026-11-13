//! What formatting reads of fonts: an element's font metrics and a run's
//! shaped glyphs, as a parameter ([`TextFns`]) (phase-5.md item 5.14).
//!
//! Sources: CSS 2.1 §10.8.1 ("A to mean that height (for a given font at a
//! given size) and D the depth"; `line-height: normal`, "a 'reasonable'
//! value based on the font of the element"), §10.6.1 (the content area);
//! CSS Fonts 3 §5.2's *first available font* (item 5.10); HTML §15.5.6's
//! "average character width" and "maximum character width" (`block.rs`);
//! OpenType's `hhea` and `OS/2` tables (item 5.9).
//!
//! Modelling choices:
//!
//! - **Fonts are a parameter**, as computed style is for the box tree
//!   (item 5.13's `StyleFns`), so formatting is tested with a font whose
//!   every advance is known ([`BoxFont`]) and runs in the browser over real
//!   faces ([`FaceFonts`]).
//! - **A and D** (§10.8.1) are the first available font's: `OS/2`'s
//!   `sTypoAscender` and `sTypoDescender` when its `fsSelection` has
//!   `USE_TYPO_METRICS`, else `hhea`'s `ascender` and `descender`, and the
//!   same table's line gap. CSS 2.1's note recommends the `OS/2` typo
//!   metrics always; it is a note, and engines read `hhea` unless
//!   `USE_TYPO_METRICS` is set, which is what the reference rendering of
//!   item 5.25 will compare against.
//! - **`line-height: normal`** is `A + D + line gap` of the first available
//!   font (§10.8.1 recommends "between 1.0 to 1.2"; this is what engines
//!   use, and it is 1.164 for DejaVu Serif).
//! - **One font per inline box** for A and D: §10.8.1 asks for each glyph's
//!   own font's A and D, and a glyph from a fallback face would then move
//!   the box; here an inline box's A and D are its first available font's
//!   whatever face draws its glyphs (listed).
//! - **The x-height** (for `vertical-align: middle`) is `OS/2`'s `sxHeight`
//!   when the table has it, else half the font size.
//! - **Character widths** (HTML §15.5.6): the average is the advance of
//!   U+0030 DIGIT ZERO (CSS Values 4's `ch`), since `clazel-font` does not
//!   read `OS/2`'s `xAvgCharWidth`; the maximum is `hhea`'s
//!   `advanceWidthMax`.
//! - **A run is shaped as a whole**, in one face per character as item
//!   5.10's §5.4 matching picks it, each maximal stretch of one face shaped
//!   by item 5.11's shaper; kerning is therefore within a stretch only.

use clazel_font::Face;
use clazel_style::cascade::computed::{ComputedStyle, Family as StyleFamily, FontStyle};

use crate::fonts::{
    Choice, FaceId, Family, FontQuery, FontStyle as FaceStyle, FontTable, Generic, Generics,
    face_for_char, first_available_font,
};
use crate::shape::{Script, Shaper, fixed::to_26_6};

/// An element's font metrics at its used size, in 1/64 px.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct FontMetrics {
    /// A, the height above the baseline.
    pub ascent: i32,
    /// D, the depth below the baseline (positive downwards).
    pub descent: i32,
    /// The line gap that `line-height: normal` adds.
    pub line_gap: i32,
    /// The x-height.
    pub x_height: i32,
    /// The average character width (the advance of `0`).
    pub average: i32,
    /// The maximum character width.
    pub maximum: i32,
    /// The top of an underline, below the baseline (positive downwards):
    /// the `post` table's `underlinePosition` negated (item 5.16).
    pub underline_position: i32,
    /// An underline's thickness: `post`'s `underlineThickness` (item 5.16).
    pub underline_thickness: i32,
}

/// One shaped glyph, in 1/64 px.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ShapedGlyph {
    /// The face that draws it, numbered as the [`TextFns`] numbers faces.
    pub face: u32,
    /// Its glyph id in that face.
    pub id: u16,
    /// The byte offset, in the shaped text, of the character it draws.
    pub cluster: usize,
    /// Its advance.
    pub advance: i32,
    /// Its offset from its pen position, right.
    pub x_offset: i32,
    /// Its offset from the baseline, down.
    pub y_offset: i32,
}

/// Fonts as formatting reads them.
pub trait TextFns {
    /// The metrics of the first available font of an element with computed
    /// style `style`, at its used font size.
    fn metrics(&self, style: &ComputedStyle) -> FontMetrics;

    /// `text` shaped in the fonts of an element with computed style
    /// `style`: its glyphs in logical order, each with the byte offset of
    /// the character it draws.
    fn shape(&self, style: &ComputedStyle, text: &str) -> Vec<ShapedGlyph>;
}

/// A font whose every glyph is a square of one em, with the metrics of
/// WPT's Ahem font (ascent 0.8 em, descent 0.2 em, no line gap; x-height
/// 0.8 em), except that combining marks and U+200B ZERO WIDTH SPACE have
/// no advance. Every glyph is id 1 of face 0. For tests, whose expected
/// geometry can then be worked out by hand.
#[derive(Debug, Clone, Copy, Default)]
pub struct BoxFont;

impl BoxFont {
    /// The descent at size `size`: a fifth of it, rounded down.
    fn descent(size: i32) -> i32 {
        size.max(0).div_euclid(5)
    }
}

impl TextFns for BoxFont {
    fn metrics(&self, style: &ComputedStyle) -> FontMetrics {
        let size = style.font_size.max(0);
        let descent = BoxFont::descent(size);
        let ascent = size.saturating_sub(descent);
        FontMetrics {
            ascent,
            descent,
            line_gap: 0,
            x_height: ascent,
            average: size,
            maximum: size,
            // A tenth of an em below the baseline and a tenth thick, so that
            // tests' decorations are whole pixels at 10px.
            underline_position: size.div_euclid(10),
            underline_thickness: size.div_euclid(10),
        }
    }

    fn shape(&self, style: &ComputedStyle, text: &str) -> Vec<ShapedGlyph> {
        let size = style.font_size.max(0);
        text.char_indices()
            .map(|(cluster, c)| {
                let zero = c == '\u{200B}' || crate::shape::is_combining_mark(c);
                ShapedGlyph {
                    face: 0,
                    id: 1,
                    cluster,
                    advance: if zero { 0 } else { size },
                    x_offset: 0,
                    y_offset: 0,
                }
            })
            .collect()
    }
}

/// Real faces: a font table (item 5.10) over `clazel-font` faces indexed
/// like it, the generic families, and the computed style's family lists
/// (`ComputedTable::families`, which `ComputedStyle::font_family` indexes).
/// Face numbers are the table's [`FaceId`]s.
#[derive(Debug, Clone, Copy)]
pub struct FaceFonts<'a> {
    /// The font table.
    pub table: &'a FontTable,
    /// The generic families.
    pub generics: &'a Generics,
    /// The faces, indexed like the table.
    pub faces: &'a [Face<'a>],
    /// The computed family lists.
    pub families: &'a [Vec<StyleFamily>],
}

/// A computed family list as item 5.10's matching reads it. A generic
/// family this phase does not map (`cursive`, `fantasy`, `system-ui`, …) is
/// a family name, which no face has (`fonts/mod.rs`).
fn families(list: &[StyleFamily]) -> Vec<Family> {
    list.iter()
        .map(|f| match f {
            StyleFamily::Name(n) => {
                Family::Named(n.iter().filter_map(|&c| char::from_u32(c)).collect())
            }
            StyleFamily::Generic("serif") => Family::Generic(Generic::Serif),
            StyleFamily::Generic("sans-serif") => Family::Generic(Generic::SansSerif),
            StyleFamily::Generic("monospace") => Family::Generic(Generic::Monospace),
            StyleFamily::Generic(other) => Family::Named((*other).to_owned()),
        })
        .collect()
}

/// `font-weight` as a number from 1 to 1000.
fn weight(style: &ComputedStyle) -> u16 {
    u16::try_from(style.font_weight.round().clamp(1, 1000)).unwrap_or(400)
}

/// `font-style` as item 5.10's matching reads it.
fn face_style(style: &ComputedStyle) -> FaceStyle {
    match style.font_style {
        FontStyle::Normal => FaceStyle::Normal,
        FontStyle::Italic => FaceStyle::Italic,
        FontStyle::Oblique(_) => FaceStyle::Oblique,
    }
}

impl FaceFonts<'_> {
    /// The face with id `id`.
    fn face(&self, id: FaceId) -> Option<&Face<'_>> {
        self.faces.get(id.0)
    }

    /// `style`'s family list as item 5.10 reads it.
    fn query_families(&self, style: &ComputedStyle) -> Vec<Family> {
        families(
            self.families
                .get(style.font_family)
                .map_or(&[][..], Vec::as_slice),
        )
    }

    /// Font units of `face` to 1/64 px at `size`.
    fn scale(face: &Face<'_>, v: i32, size: i32) -> i32 {
        to_26_6(v, size, face.units_per_em())
    }
}

impl TextFns for FaceFonts<'_> {
    fn metrics(&self, style: &ComputedStyle) -> FontMetrics {
        let size = style.font_size.max(0);
        let fam = self.query_families(style);
        let q = FontQuery {
            families: &fam,
            weight: weight(style),
            stretch: crate::fonts::table::STRETCH_NORMAL,
            style: face_style(style),
        };
        let Some(face) = first_available_font(self.table, self.generics, &q, self.faces)
            .and_then(|id| self.face(id))
        else {
            // No face at all: an em box, as BoxFont has.
            return BoxFont.metrics(style);
        };
        let os2 = face.os2().ok().flatten();
        let (a, d, gap) = match os2 {
            Some(o) if o.use_typo_metrics() => (
                i32::from(o.typo_ascender),
                i32::from(o.typo_descender),
                i32::from(o.typo_line_gap),
            ),
            _ => (
                i32::from(face.hhea.ascender),
                i32::from(face.hhea.descender),
                i32::from(face.hhea.line_gap),
            ),
        };
        let s = |v: i32| FaceFonts::scale(face, v, size);
        let x_height = os2
            .and_then(|o| o.x_height)
            .map_or(size.div_euclid(2), |x| s(i32::from(x)));
        let zero = face
            .glyph_index('0')
            .ok()
            .flatten()
            .and_then(|g| face.advance_width(g).ok())
            .map_or(size.div_euclid(2), |w| s(i32::from(w)));
        // `post`'s "underlinePosition: the suggested distance of the top of
        // the underline from the baseline (negative values indicate below
        // baseline)"; without a `post` table, half the descent below the
        // baseline and a sixteenth of an em thick (item 5.16).
        let (underline_position, underline_thickness) = match face.post().ok().flatten() {
            Some(p) => (
                s(i32::from(p.underline_position)).saturating_neg(),
                s(i32::from(p.underline_thickness)).max(0),
            ),
            None => (s(d).saturating_neg().div_euclid(2), size.div_euclid(16)),
        };
        FontMetrics {
            ascent: s(a),
            // `descender` is negative below the baseline.
            descent: s(d).saturating_neg(),
            line_gap: s(gap).max(0),
            x_height,
            average: zero,
            maximum: s(i32::from(face.hhea.advance_width_max)),
            underline_position,
            underline_thickness,
        }
    }

    fn shape(&self, style: &ComputedStyle, text: &str) -> Vec<ShapedGlyph> {
        let size = style.font_size.max(0);
        let fam = self.query_families(style);
        let q = FontQuery {
            families: &fam,
            weight: weight(style),
            stretch: crate::fonts::table::STRETCH_NORMAL,
            style: face_style(style),
        };
        // Each character's face (§5.2 and §5.4), then each maximal stretch
        // of one face shaped on its own.
        let mut stretches: Vec<(usize, usize, Option<FaceId>)> = Vec::new();
        for (i, c) in text.char_indices() {
            let face = match face_for_char(self.table, self.generics, &q, c, self.faces) {
                Choice::Face(id) | Choice::NotDef(id) => Some(id),
                Choice::Nothing => None,
            };
            let end = i.saturating_add(c.len_utf8());
            match stretches.last_mut() {
                Some(last) if last.2 == face => last.1 = end,
                _ => stretches.push((i, end, face)),
            }
        }
        let mut out = Vec::new();
        for (start, end, face) in stretches {
            let Some(piece) = text.get(start..end) else {
                continue;
            };
            let Some(f) = face.and_then(|id| self.face(id)) else {
                // No face: an em per character, glyph 0.
                out.extend(
                    BoxFont
                        .shape(style, piece)
                        .into_iter()
                        .map(|g| ShapedGlyph {
                            id: 0,
                            cluster: g.cluster.saturating_add(start),
                            ..g
                        }),
                );
                continue;
            };
            let face_no = face.map_or(0, |id| u32::try_from(id.0).unwrap_or(u32::MAX));
            let run = Shaper::new(*f, Script::of_text(piece)).shape_at(piece, size);
            let mut pen = 0i32;
            for g in &run.glyphs {
                out.push(ShapedGlyph {
                    face: face_no,
                    id: g.glyph,
                    cluster: g.cluster.saturating_add(start),
                    advance: g.advance,
                    x_offset: g.x.saturating_sub(pen),
                    // Item 5.11's y is up; ours is down.
                    y_offset: g.y.saturating_neg(),
                });
                pen = pen.saturating_add(g.advance);
            }
        }
        out
    }
}

//! Differential test of `clazel-font` against two independent engines,
//! `ttf-parser` and `read-fonts` (phase-5.md items 5.9 and 5.10).
//!
//! Three suites, each printing one `clazel-conformance:` line
//! (`xtask/src/conformance.rs`):
//!
//! - **vendored fonts**: every font under `tests/data/`, every face of each.
//!   A unit is one check: a table record, a metric, a `cmap` entry, a glyph's
//!   advance and side bearing, a glyph's raw description, a glyph's outline,
//!   a glyph's 26.6 path and its well-formedness,
//!   a `kern` pair, a `GPOS` pair adjustment.
//! - **system fonts**: the same checks on every font file under the runner's
//!   font directories (ignored under Miri, which forbids opening files). Its
//!   counts depend on the machine.
//! - **mutated fonts**: 10,000 fonts made by changing one to four bytes of a
//!   vendored font (seeded, so the same every run). A unit is one mutant: it
//!   passes if every check agrees, is an expected failure if every
//!   disagreement is of an expected kind, and fails otherwise.
//!
//! What is compared: the table directory (tag, checksum, offset, length of
//! every record); `head.unitsPerEm`, `hhea` ascender, descender, line gap and
//! `numberOfHMetrics`, `maxp.numGlyphs`; `OS/2` weight, typo metrics,
//! `USE_TYPO_METRICS` and x and cap heights; `post` underline and fixed
//! pitch; the decoding of every UTF-16BE `name` record; every code point the
//! chosen `cmap` subtable describes, looked up in that same subtable by each
//! engine; every glyph's advance and left side bearing; every glyph's raw
//! description against `read-fonts` (a simple glyph's contour ends and
//! points, a composite's component records) and its flattened outline
//! against `ttf-parser`'s, segment by segment, after turning our quadratic
//! contours into segments with `ttf-parser`'s own rule; every glyph's 26.6
//! path (item 5.10) at one of four sizes, which must be well formed, against
//! `ttf-parser`'s outline scaled to that size, contour by contour as cycles
//! of lines and quadratics (a glyph is one more unit for this, and one for
//! well-formedness); every pair of every
//! `kern` format 0 subtable; and, for each `kern`-feature lookup of the
//! `latn` and `DFLT` scripts, the pair adjustment of every pair from a set
//! of glyphs.
//!
//! Expected differences are listed in [`EXPECTED`] with their reasons;
//! each is counted separately and none counts as a pass.

mod dejavu {
    include!("generated/fonts_dejavu.rs");
}
mod fontations {
    include!("generated/fonts_fontations.rs");
}
mod source_code_pro {
    include!("generated/fonts_source_code_pro.rs");
}
mod source_serif {
    include!("generated/fonts_source_serif.rs");
}

use std::collections::BTreeMap;

use clazel_font::glyf::{Component, Glyph, Outline, Placement};
use clazel_font::layout::{PairValue, ValueRecord};
use clazel_font::outline::{Path, PathPoint, try_glyph_path};
use clazel_font::{Error, Face, Tag, file::FontFile};
use read_fonts::TableProvider;
use read_fonts::types::{GlyphId, GlyphId16};

/// Every expected kind of difference, and why it is expected.
const EXPECTED: &[(&str, &str)] = &[
    (
        "cff-face",
        "a CFF face is unsupported by decision 5.0(c) (C1); both engines read it",
    ),
    (
        "ttf-parser-scaled-offset",
        "ttf-parser ignores SCALED_COMPONENT_OFFSET and never transforms a component's offset; \
         the glyf chapter applies the transform when that flag is set",
    ),
    (
        "ttf-parser-point-matching",
        "ttf-parser does not read point-matching arguments (ARGS_ARE_XY_VALUES clear) at all, \
         so it misreads the rest of such a component record",
    ),
    (
        "ttf-parser-single-point",
        "ttf-parser draws a simple glyph with exactly one point as empty, also as a component",
    ),
    (
        "ttf-parser-lone-off-curve",
        "a contour of exactly one point, off-curve: ttf-parser draws nothing for it; our 26.6 \
         path (item 5.10) keeps it as a quadratic from the implied on-curve point (the point \
         itself) back to itself, which covers no area. Only the path comparison counts it",
    ),
    (
        "ttf-parser-missing-component",
        "ttf-parser skips a component whose glyph cannot be read and draws the rest; we refuse \
         the glyph (item 5.10 draws it empty)",
    ),
    (
        "i16-wrap",
        "ttf-parser and read-fonts accumulate glyph coordinates in i16 with wrapping; we use \
         i32, so a glyph whose points leave -32768..=32767 differs",
    ),
    (
        "depth",
        "ttf-parser follows components 32 deep; our bound is MAX_COMPONENT_DEPTH (8)",
    ),
    (
        "ttf-parser-format4-high-glyph",
        "ttf-parser adds a format 4 idDelta to a glyphIdArray value as i16 and drops a negative \
         result, so glyph IDs 0x8000 and above reached through glyphIdArray map to nothing; \
         read-fonts and we map them (the chapter's idDelta arithmetic is modulo 65536)",
    ),
    (
        "reference-panic",
        "on mutated bytes only: ttf-parser 0.25.1 panics in a debug build when an offset plus a \
         length passes u32::MAX (a debug_assert in Stream::read_bytes, parser.rs line 770); \
         a panic whose location is in our crate is a failure",
    ),
    (
        "unordered",
        "on mutated bytes only: a cmap subtable, kern format 0 subtable or GPOS array that the \
         chapters require to be sorted is not; each engine's bisection then finds a different \
         element (ours always returns an element that is really there, or none)",
    ),
    (
        "nested-transform",
        "a transformed component inside a transformed component: we round to whole font units \
         at each level, ttf-parser composes the matrices in f32, so the points can differ by \
         more than the one unit allowed for a single transform",
    ),
    (
        "ttf-parser-name-storage",
        "on mutated bytes only: ttf-parser starts the name table's string storage no earlier \
         than the end of the name records, whatever storageOffset says; we use storageOffset as \
         the name chapter defines it (\"Offset to start of string storage (from start of \
         table)\")",
    ),
    (
        "ttf-parser-scale-flags",
        "on mutated bytes only: a component sets more than one of WE_HAVE_A_SCALE, \
         WE_HAVE_AN_X_AND_Y_SCALE and WE_HAVE_A_TWO_BY_TWO, which the glyf chapter says are \
         mutually exclusive; ttf-parser tests WE_HAVE_A_TWO_BY_TWO first, we and read-fonts \
         follow the chapter's pseudo-code (WE_HAVE_A_SCALE first)",
    ),
    (
        "acceptance",
        "on mutated bytes only: one side refuses a table, glyph or face the other reads. We \
         refuse what the chapters make malformed (a repeat count past the last point, \
         endPtsOfContours not increasing, a decreasing loca pair, hmtx shorter than its counts, \
         unknown versions); the engines recover or read differently. Counted per refusing side \
         in the printed breakdown",
    ),
];

/// Counts for one suite, by kind.
#[derive(Default)]
struct Tally {
    pass: u64,
    xfail: BTreeMap<&'static str, u64>,
    fail: u64,
    messages: Vec<String>,
}

impl Tally {
    fn ok(&mut self) {
        self.pass = self.pass.saturating_add(1);
    }

    /// A difference: expected if `kind` is listed, else a failure.
    fn diff(&mut self, kind: Option<&'static str>, msg: impl FnOnce() -> String) {
        match kind {
            Some(k) if EXPECTED.iter().any(|(e, _)| *e == k) => {
                let n = self.xfail.entry(k).or_insert(0);
                *n = n.saturating_add(1);
            }
            _ => {
                self.fail = self.fail.saturating_add(1);
                if self.messages.len() < 40 {
                    self.messages.push(msg());
                }
            }
        }
    }

    /// `pass` if `same`, else a difference of `kind`.
    fn check(&mut self, same: bool, kind: Option<&'static str>, msg: impl FnOnce() -> String) {
        if same {
            self.ok();
        } else {
            self.diff(kind, msg);
        }
    }

    fn xfail_total(&self) -> u64 {
        self.xfail.values().fold(0u64, |a, b| a.saturating_add(*b))
    }

    fn report(&self, suite: &str) {
        let total = self
            .pass
            .saturating_add(self.xfail_total())
            .saturating_add(self.fail);
        println!(
            "clazel-conformance: suite=\"{suite}\" pass={} xfail={} fail={} total={total}",
            self.pass,
            self.xfail_total(),
            self.fail
        );
        for (k, n) in &self.xfail {
            println!("  expected difference {k}: {n}");
        }
        for m in &self.messages {
            println!("  FAIL {m}");
        }
    }
}

/// How much of a face to compare.
#[derive(Clone, Copy)]
struct Budget {
    /// Compare every `glyph_stride`-th glyph.
    glyph_stride: usize,
    /// At most this many glyphs.
    max_glyphs: usize,
    /// At most this many `cmap` code points.
    max_code_points: usize,
    /// At most this many glyphs in the GPOS pair set (pairs are its square).
    gpos_glyphs: usize,
    /// Compare every `pair_stride`-th `kern` pair.
    pair_stride: usize,
    /// At most this many faces of a collection.
    max_faces: u32,
}

const FULL: Budget = Budget {
    glyph_stride: 1,
    max_glyphs: usize::MAX,
    max_code_points: 300_000,
    gpos_glyphs: 160,
    pair_stride: 1,
    max_faces: 64,
};

/// Under Miri, which runs about a hundred times slower, a stride sized to
/// keep the vendored suite near a minute: it is there for undefined
/// behaviour on the paths the checks take, and the full suite runs in the
/// normal test job.
const MIRI: Budget = Budget {
    glyph_stride: 211,
    max_glyphs: 12,
    max_code_points: 150,
    gpos_glyphs: 4,
    pair_stride: 97,
    max_faces: 2,
};

/// For a mutant: enough to reach every table, small enough for 10,000.
const MUTANT: Budget = Budget {
    glyph_stride: 1,
    max_glyphs: 48,
    max_code_points: 1_200,
    gpos_glyphs: 20,
    pair_stride: 13,
    max_faces: 2,
};

/// A segment of `ttf-parser`'s outline builder.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Seg {
    Move(f32, f32),
    Line(f32, f32),
    Quad(f32, f32, f32, f32),
    Close,
}

#[derive(Default)]
struct Segs(Vec<Seg>);

impl ttf_parser::OutlineBuilder for Segs {
    fn move_to(&mut self, x: f32, y: f32) {
        self.0.push(Seg::Move(x, y));
    }
    fn line_to(&mut self, x: f32, y: f32) {
        self.0.push(Seg::Line(x, y));
    }
    fn quad_to(&mut self, x1: f32, y1: f32, x: f32, y: f32) {
        self.0.push(Seg::Quad(x1, y1, x, y));
    }
    fn curve_to(&mut self, _: f32, _: f32, _: f32, _: f32, _: f32, _: f32) {}
    fn close(&mut self) {
        self.0.push(Seg::Close);
    }
}

/// `ttf-parser`'s `Point::lerp`.
fn lerp(a: (f32, f32), b: (f32, f32)) -> (f32, f32) {
    (a.0 + 0.5 * (b.0 - a.0), a.1 + 0.5 * (b.1 - a.1))
}

/// Our outline as `ttf-parser`'s builder turns contours into segments
/// (`glyf.rs`, `Builder::push_point` and `finish_contour`, transcribed).
fn segments(o: &Outline) -> Vec<Seg> {
    let mut out = Vec::new();
    let mut start = 0usize;
    for &end in &o.contour_ends {
        let mut first_on: Option<(f32, f32)> = None;
        let mut first_off: Option<(f32, f32)> = None;
        let mut last_off: Option<(f32, f32)> = None;
        for p in o.points.get(start..end).unwrap_or_default() {
            let q = (p.x as f32, p.y as f32);
            if first_on.is_none() {
                if p.on_curve {
                    first_on = Some(q);
                    out.push(Seg::Move(q.0, q.1));
                } else if let Some(off) = first_off {
                    let mid = lerp(off, q);
                    first_on = Some(mid);
                    last_off = Some(q);
                    out.push(Seg::Move(mid.0, mid.1));
                } else {
                    first_off = Some(q);
                }
            } else {
                match (last_off, p.on_curve) {
                    (Some(off), true) => {
                        last_off = None;
                        out.push(Seg::Quad(off.0, off.1, q.0, q.1));
                    }
                    (Some(off), false) => {
                        last_off = Some(q);
                        let mid = lerp(off, q);
                        out.push(Seg::Quad(off.0, off.1, mid.0, mid.1));
                    }
                    (None, true) => out.push(Seg::Line(q.0, q.1)),
                    (None, false) => last_off = Some(q),
                }
            }
        }
        if let (Some(o1), Some(o2)) = (first_off, last_off) {
            last_off = None;
            let mid = lerp(o2, o1);
            out.push(Seg::Quad(o2.0, o2.1, mid.0, mid.1));
        }
        if let (Some(p), Some(o1)) = (first_on, first_off) {
            out.push(Seg::Quad(o1.0, o1.1, p.0, p.1));
        } else if let (Some(p), Some(o2)) = (first_on, last_off) {
            out.push(Seg::Quad(o2.0, o2.1, p.0, p.1));
        } else if let Some(p) = first_on {
            out.push(Seg::Line(p.0, p.1));
        }
        out.push(Seg::Close);
        start = end;
    }
    out
}

/// Whether two segment lists agree, within `tol` on every coordinate.
fn same_segments(a: &[Seg], b: &[Seg], tol: f32) -> bool {
    let near = |x: f32, y: f32| (x - y).abs() <= tol;
    a.len() == b.len()
        && a.iter().zip(b).all(|(s, t)| match (s, t) {
            (Seg::Move(a, b), Seg::Move(c, d)) | (Seg::Line(a, b), Seg::Line(c, d)) => {
                near(*a, *c) && near(*b, *d)
            }
            (Seg::Quad(a, b, c, d), Seg::Quad(e, f, g, h)) => {
                near(*a, *e) && near(*b, *f) && near(*c, *g) && near(*d, *h)
            }
            (Seg::Close, Seg::Close) => true,
            _ => false,
        })
}

/// What a glyph's component tree contains, for classifying differences.
#[derive(Default)]
struct Tree {
    transformed: bool,
    /// The most transformed components on one path from the glyph down.
    transform_depth: u8,
    scaled_offset: bool,
    point_matching: bool,
    unreadable: bool,
    /// A simple glyph in the tree has exactly one point.
    single_point: bool,
    /// A component sets more than one scale flag.
    scale_flags: bool,
    depth: u8,
}

fn tree(face: &Face<'_>, glyph: u16, depth: u8, t: &mut Tree) {
    tree_at(face, glyph, depth, 0, t);
}

fn tree_at(face: &Face<'_>, glyph: u16, depth: u8, transforms: u8, t: &mut Tree) {
    t.depth = t.depth.max(depth);
    t.transform_depth = t.transform_depth.max(transforms);
    if depth > 40 {
        return;
    }
    match face.glyph(glyph) {
        Ok(Glyph::Composite(c)) => {
            for comp in c.components() {
                let Ok(comp) = comp else {
                    t.unreadable = true;
                    return;
                };
                let Component {
                    placement,
                    transform,
                    glyph: child,
                    ..
                } = comp;
                let scales = comp.flags
                    & (clazel_font::glyf::component_flags::WE_HAVE_A_SCALE
                        | clazel_font::glyf::component_flags::WE_HAVE_AN_X_AND_Y_SCALE
                        | clazel_font::glyf::component_flags::WE_HAVE_A_TWO_BY_TWO);
                if scales.count_ones() > 1 {
                    t.scale_flags = true;
                }
                let transformed = transform != clazel_font::glyf::Transform::IDENTITY;
                if transformed {
                    t.transformed = true;
                    if comp.scaled_offset()
                        && matches!(placement, Placement::Offset(x, y) if (x, y) != (0, 0))
                    {
                        t.scaled_offset = true;
                    }
                }
                if matches!(placement, Placement::Points(..)) {
                    t.point_matching = true;
                }
                let below = transforms.saturating_add(u8::from(transformed));
                tree_at(face, child, depth.saturating_add(1), below, t);
            }
        }
        Ok(Glyph::Simple(s)) => {
            if s.num_points() == 1 {
                t.single_point = true;
            }
        }
        Ok(Glyph::Empty) => {}
        Err(_) => t.unreadable = true,
    }
}

/// The glyphs to sample for `GPOS` pairs: those of printable ASCII and
/// Latin-1, then the lowest glyph IDs, at most `n`.
fn sample_glyphs(face: &Face<'_>, n: usize) -> Vec<u16> {
    let mut out: Vec<u16> = (0x20u32..0x180)
        .filter_map(char::from_u32)
        .filter_map(|c| face.glyph_index(c).ok().flatten())
        .collect();
    out.extend(0..face.num_glyphs().min(64));
    out.sort_unstable();
    out.dedup();
    out.truncate(n);
    out
}

fn ours_value(v: &ValueRecord) -> [i16; 4] {
    [v.x_placement, v.y_placement, v.x_advance, v.y_advance]
}

fn ttf_value(v: &ttf_parser::gpos::ValueRecord<'_>) -> [i16; 4] {
    [v.x_placement, v.y_placement, v.x_advance, v.y_advance]
}

fn rf_value(v: &read_fonts::tables::gpos::ValueRecord<'_>) -> [i16; 4] {
    [
        v.x_placement().unwrap_or(0),
        v.y_placement().unwrap_or(0),
        v.x_advance().unwrap_or(0),
        v.y_advance().unwrap_or(0),
    ]
}

/// `ttf-parser`'s pair adjustment for lookup `l`: the first subtable that
/// applies.
fn ttf_pair(
    gpos: &ttf_parser::opentype_layout::LayoutTable<'_>,
    l: u16,
    a: u16,
    b: u16,
) -> Option<[[i16; 4]; 2]> {
    use ttf_parser::gpos::{PairAdjustment, PositioningSubtable};
    let lookup = gpos.lookups.get(l)?;
    for j in 0..lookup.subtables.len() {
        let Some(PositioningSubtable::Pair(p)) = lookup.subtables.get::<PositioningSubtable>(j)
        else {
            continue;
        };
        let (ga, gb) = (ttf_parser::GlyphId(a), ttf_parser::GlyphId(b));
        match p {
            PairAdjustment::Format1 { coverage, sets } => {
                if let Some(set) = coverage.get(ga).and_then(|i| sets.get(i))
                    && let Some((v1, v2)) = set.get(gb)
                {
                    return Some([ttf_value(&v1), ttf_value(&v2)]);
                }
            }
            PairAdjustment::Format2 {
                coverage,
                classes,
                matrix,
            } => {
                if coverage.get(ga).is_some()
                    && let Some((v1, v2)) = matrix.get((classes.0.get(ga), classes.1.get(gb)))
                {
                    return Some([ttf_value(&v1), ttf_value(&v2)]);
                }
            }
        }
    }
    None
}

/// `read-fonts`' pair adjustment for lookup `l`, the same way.
fn rf_pair(
    gpos: &read_fonts::tables::gpos::Gpos<'_>,
    l: u16,
    a: u16,
    b: u16,
) -> Option<[[i16; 4]; 2]> {
    use read_fonts::tables::gpos::{PairPos, PositionSubtables};
    let lookup = gpos
        .lookup_list()
        .ok()?
        .lookups()
        .get(usize::from(l))
        .ok()?;
    let PositionSubtables::Pair(subtables) = lookup.subtables().ok()? else {
        return None;
    };
    let (ga, gb) = (GlyphId16::new(a), GlyphId16::new(b));
    for p in subtables.iter() {
        let Ok(p) = p else { continue };
        match p {
            PairPos::Format1(f) => {
                let Some(i) = f.coverage().ok().and_then(|c| c.get(ga)) else {
                    continue;
                };
                let Ok(set) = f.pair_sets().get(usize::from(i)) else {
                    continue;
                };
                if let Some(r) = set.find_pair_value_record(gb) {
                    return Some([rf_value(r.value_record1()), rf_value(r.value_record2())]);
                }
            }
            PairPos::Format2(f) => {
                if f.coverage().ok().and_then(|c| c.get(ga)).is_none() {
                    continue;
                }
                let (Ok(c1), Ok(c2)) = (f.class_def1(), f.class_def2()) else {
                    continue;
                };
                if let Some([v1, v2]) = f.class_value_records().get(c1.get(ga), c2.get(gb)) {
                    return Some([rf_value(&v1), rf_value(&v2)]);
                }
            }
        }
    }
    None
}

/// Compare one font file.
fn compare_file(data: &[u8], name: &str, budget: Budget, t: &mut Tally) {
    let ours = FontFile::parse(data);
    let ttf_faces = ttf_parser::fonts_in_collection(data).unwrap_or(1);
    let rf = read_fonts::FileRef::new(data);
    let ttf_ok = ttf_parser::RawFace::parse(data, 0).is_ok();
    let Ok(file) = ours else {
        t.check(!ttf_ok && rf.is_err(), Some("acceptance"), || {
            format!("{name}: we refuse the file ({ours:?}), an engine reads it")
        });
        return;
    };
    t.check(file.num_faces() == ttf_faces, Some("acceptance"), || {
        format!("{name}: {} faces, ttf-parser {ttf_faces}", file.num_faces())
    });
    for index in 0..file.num_faces().min(budget.max_faces) {
        compare_directory(data, &file, index, name, t);
        compare_face(data, index, name, budget, t);
    }
}

fn compare_directory(data: &[u8], file: &FontFile<'_>, index: u32, name: &str, t: &mut Tally) {
    let ours = file.directory(index);
    let ttf = ttf_parser::RawFace::parse(data, index);
    let rf = read_fonts::FontRef::from_index(data, index);
    let (Ok(d), Ok(ttf), Ok(rf)) = (ours, ttf, rf) else {
        t.diff(Some("acceptance"), || {
            format!("{name}#{index}: directory acceptance differs")
        });
        return;
    };
    let rf_records = rf.table_directory.table_records();
    t.check(
        usize::from(d.num_tables()) == usize::from(ttf.table_records.len())
            && usize::from(d.num_tables()) == rf_records.len(),
        None,
        || format!("{name}#{index}: numTables {}", d.num_tables()),
    );
    for i in 0..d.num_tables() {
        let Ok(r) = d.record(i) else {
            t.diff(None, || format!("{name}#{index}: record {i} unreadable"));
            continue;
        };
        let theirs = ttf.table_records.get(i);
        let same_ttf = theirs.is_some_and(|x| {
            x.tag.to_bytes() == r.tag.0
                && x.offset == r.offset
                && x.length == r.length
                && x.check_sum == r.checksum
        });
        let same_rf = rf_records.get(usize::from(i)).is_some_and(|x| {
            x.tag().to_be_bytes() == r.tag.0
                && x.offset() == r.offset
                && x.length() == r.length
                && x.checksum() == r.checksum
        });
        t.check(same_ttf && same_rf, None, || {
            format!("{name}#{index}: record {i} {r:?}")
        });
    }
}

fn compare_face(data: &[u8], index: u32, name: &str, budget: Budget, t: &mut Tally) {
    let ours = Face::parse(data, index);
    let ttf = ttf_parser::Face::parse(data, index);
    let rf = read_fonts::FontRef::from_index(data, index);
    let face = match ours {
        Ok(f) => f,
        Err(Error::CffOutlines) => {
            t.diff(Some("cff-face"), String::new);
            return;
        }
        Err(e) => {
            // ttf-parser needs only head, hhea and maxp; we also need the
            // TrueType outline tables and cmap, so a face without them is a
            // face we do not open.
            let missing = matches!(e, Error::MissingTable(_)) && ttf.is_err();
            t.check(ttf.is_err() || missing, Some("acceptance"), || {
                format!("{name}#{index}: we refuse the face ({e}), ttf-parser opens it")
            });
            return;
        }
    };
    let (Ok(ttf), Ok(rf)) = (ttf, rf) else {
        t.diff(Some("acceptance"), || {
            format!("{name}#{index}: an engine refuses a face we open")
        });
        return;
    };
    let tt = ttf.tables();
    let ctx = |what: &str| format!("{name}#{index}: {what}");

    // Metrics.
    t.check(face.units_per_em() == tt.head.units_per_em, None, || {
        ctx("unitsPerEm")
    });
    t.check(
        (
            face.hhea.ascender,
            face.hhea.descender,
            face.hhea.line_gap,
            face.hhea.number_of_h_metrics,
        ) == (
            tt.hhea.ascender,
            tt.hhea.descender,
            tt.hhea.line_gap,
            tt.hhea.number_of_metrics,
        ),
        None,
        || ctx("hhea"),
    );
    t.check(
        face.num_glyphs() == tt.maxp.number_of_glyphs.get(),
        None,
        || ctx("numGlyphs"),
    );
    if let Ok(head) = rf.head() {
        t.check(head.units_per_em() == face.units_per_em(), None, || {
            ctx("read-fonts unitsPerEm")
        });
    }
    compare_os2_post_name(&face, &ttf, &rf, &ctx, t);
    compare_cmap(&face, &ttf, &rf, budget, &ctx, t);
    compare_glyphs(&face, &ttf, &rf, budget, &ctx, t);
    compare_kern(&face, &ttf, &rf, budget, &ctx, t);
    compare_gpos(&face, &ttf, &rf, budget, &ctx, t);
}

fn compare_os2_post_name(
    face: &Face<'_>,
    ttf: &ttf_parser::Face<'_>,
    rf: &read_fonts::FontRef<'_>,
    ctx: &dyn Fn(&str) -> String,
    t: &mut Tally,
) {
    let tt = ttf.tables();
    match (face.os2(), tt.os2) {
        (Ok(Some(o)), Some(x)) => t.check(
            o.weight_class == x.weight().to_number()
                && o.typo_ascender == x.typographic_ascender()
                && o.typo_descender == x.typographic_descender()
                && o.typo_line_gap == x.typographic_line_gap()
                && o.use_typo_metrics() == x.use_typographic_metrics()
                && o.x_height == x.x_height()
                && o.cap_height == x.capital_height()
                && o.strikeout_size == x.strikeout_metrics().thickness
                && o.strikeout_position == x.strikeout_metrics().position,
            None,
            || ctx("OS/2"),
        ),
        (Ok(None), None) => t.ok(),
        _ => t.diff(Some("acceptance"), || ctx("OS/2 acceptance")),
    }
    match (face.post(), tt.post) {
        (Ok(Some(p)), Some(x)) => t.check(
            p.underline_position == x.underline_metrics.position
                && p.underline_thickness == x.underline_metrics.thickness
                && p.is_fixed_pitch == x.is_monospaced,
            None,
            || ctx("post"),
        ),
        (Ok(None), None) => t.ok(),
        _ => t.diff(Some("acceptance"), || ctx("post acceptance")),
    }
    // Every UTF-16BE name record: our decoding against ttf-parser's (it
    // decodes the same records: platform 0, and 3 with encodings 0, 1, 10),
    // and our record fields against read-fonts'.
    let (Ok(Some(n)), Some(x)) = (face.name(), tt.name) else {
        return;
    };
    let rf_name = rf.name().ok();
    let records_end = 6usize.saturating_add(usize::from(n.count()).saturating_mul(12));
    let clamped = usize::from(n.storage_offset()) < records_end;
    let storage_kind = clamped.then_some("ttf-parser-name-storage");
    for i in 0..n.count() {
        let Ok(r) = n.record(i) else { continue };
        let theirs = x.names.get(i);
        // ttf-parser's `Names::get` reports no record whose platform it
        // does not know (above 4) or whose string lies outside the table.
        let ttf_skips = r.platform_id > 4 || n.string_bytes(&r).is_err();
        let fields = theirs.map_or(ttf_skips, |y| {
            (y.encoding_id, y.language_id, y.name_id) == (r.encoding_id, r.language_id, r.name_id)
        });
        let rf_fields = rf_name
            .as_ref()
            .and_then(|rn| rn.name_record().get(usize::from(i)))
            .is_some_and(|y| {
                (
                    y.platform_id(),
                    y.encoding_id(),
                    y.language_id(),
                    y.name_id().to_u16(),
                ) == (r.platform_id, r.encoding_id, r.language_id, r.name_id)
            });
        t.check(fields && rf_fields, storage_kind, || {
            ctx(&format!("name record {i}"))
        });
        if r.is_utf16be()
            && let (Ok(bytes), Some(y)) = (n.string_bytes(&r), theirs)
            && y.is_unicode()
            && let Some(s) = y.to_string()
        {
            t.check(
                clazel_font::name::decode_utf16be(bytes) == s,
                storage_kind,
                || ctx(&format!("name string {i}")),
            );
        }
    }
}

fn compare_cmap(
    face: &Face<'_>,
    ttf: &ttf_parser::Face<'_>,
    rf: &read_fonts::FontRef<'_>,
    budget: Budget,
    ctx: &dyn Fn(&str) -> String,
    t: &mut Tally,
) {
    let Some((index, sub)) = face.cmap() else {
        return;
    };
    let ttf_sub = ttf.tables().cmap.and_then(|c| c.subtables.get(index));
    let rf_cmap = rf.cmap().ok();
    let rf_sub = rf_cmap.as_ref().and_then(|c| {
        c.encoding_records()
            .get(usize::from(index))
            .and_then(|r| r.subtable(c.offset_data()).ok())
    });
    let mut codes = Vec::new();
    let _ = sub.ranges(|a, b| {
        let mut c = a;
        while c <= b && codes.len() < budget.max_code_points {
            codes.push(c);
            let Some(n) = c.checked_add(1) else { break };
            c = n;
        }
    });
    if cfg!(miri) {
        codes.retain(|c| c % 7 == 0);
    }
    let ordered = sub.is_ordered().unwrap_or(false);
    for c in codes {
        let ours = sub.map(c);
        let theirs = ttf_sub
            .and_then(|s| s.glyph_index(c))
            .map(|g| g.0)
            .filter(|&g| g != 0);
        let rf_g = rf_sub
            .as_ref()
            .and_then(|s| s.map_codepoint(c))
            .and_then(|g| u16::try_from(g.to_u32()).ok())
            .filter(|&g| g != 0);
        let high = matches!(sub, clazel_font::cmap::Subtable::Format4(_))
            && theirs.is_none()
            && matches!(ours, Ok(Some(g)) if g >= 0x8000)
            && ours == Ok(rf_g);
        let kind = if high {
            Some("ttf-parser-format4-high-glyph")
        } else if !ordered {
            Some("unordered")
        } else {
            None
        };
        t.check(ours == Ok(theirs) && ours == Ok(rf_g), kind, || {
            ctx(&format!(
                "cmap U+{c:04X}: ours {ours:?}, ttf-parser {theirs:?}, read-fonts {rf_g:?}"
            ))
        });
    }
}

/// The defined component flags: every bit but the reserved 0xE010.
const DEFINED_COMPONENT_FLAGS: u16 = !0xE010;

/// Our raw glyph against read-fonts': `None` if they agree, else a
/// description.
fn raw_glyph_differs(
    ours: &Result<Glyph<'_>, Error>,
    rf: Option<read_fonts::tables::glyf::Glyph<'_>>,
) -> Option<String> {
    use read_fonts::tables::glyf::{Anchor, Glyph as G};
    match (ours, rf) {
        (Ok(Glyph::Empty), None) => None,
        (Ok(Glyph::Simple(s)), Some(G::Simple(r))) => {
            let ends: Vec<u16> = (0..s.num_contours())
                .filter_map(|i| s.end_point(i).ok())
                .collect();
            let r_ends: Vec<u16> = r.end_pts_of_contours().iter().map(|e| e.get()).collect();
            let pts: Vec<(i16, i16, bool)> = s
                .points()
                .filter_map(Result::ok)
                .map(|p| (p.x as i16, p.y as i16, p.on_curve))
                .collect();
            let r_pts: Vec<(i16, i16, bool)> = r.points().map(|p| (p.x, p.y, p.on_curve)).collect();
            (ends != r_ends || pts != r_pts)
                .then(|| format!("simple glyph: {} vs {} points", pts.len(), r_pts.len()))
        }
        (Ok(Glyph::Composite(c)), Some(G::Composite(r))) => {
            let ours: Vec<_> = c.components().filter_map(Result::ok).collect();
            let theirs: Vec<_> = r.components().collect();
            let same = ours.len() == theirs.len()
                && ours.iter().zip(&theirs).all(|(a, b)| {
                    let placement = match b.anchor {
                        Anchor::Offset { x, y } => Placement::Offset(i32::from(x), i32::from(y)),
                        Anchor::Point { base, component } => Placement::Points(base, component),
                    };
                    // Bits 4, 13, 14 and 15 are reserved ("set to 0"); read-fonts
                    // drops them, so only the defined bits are compared.
                    a.flags & DEFINED_COMPONENT_FLAGS == b.flags.bits() & DEFINED_COMPONENT_FLAGS
                        && a.glyph == b.glyph.to_u16()
                        && a.placement == placement
                        && [
                            a.transform.xx,
                            a.transform.yx,
                            a.transform.xy,
                            a.transform.yy,
                        ] == [
                            b.transform.xx,
                            b.transform.yx,
                            b.transform.xy,
                            b.transform.yy,
                        ]
                        .map(|f| f.to_bits())
                });
            (!same).then(|| format!("composite: {} vs {} components", ours.len(), theirs.len()))
        }
        (Err(e), r) => Some(format!(
            "ours {e}, read-fonts {}",
            if r.is_some() { "reads it" } else { "empty" }
        )),
        (_, _) => Some("glyph kinds differ".to_owned()),
    }
}

fn compare_glyphs(
    face: &Face<'_>,
    ttf: &ttf_parser::Face<'_>,
    rf: &read_fonts::FontRef<'_>,
    budget: Budget,
    ctx: &dyn Fn(&str) -> String,
    t: &mut Tally,
) {
    let rf_hmtx = rf.hmtx().ok();
    let rf_loca = rf.loca(None).ok();
    let rf_glyf = rf.glyf().ok();
    let glyphs = (0..face.num_glyphs())
        .step_by(budget.glyph_stride)
        .take(budget.max_glyphs);
    for g in glyphs {
        // Metrics.
        let adv = face.advance_width(g).ok();
        let lsb = face.left_side_bearing(g).ok();
        let gid = ttf_parser::GlyphId(g);
        let rf_adv = rf_hmtx
            .as_ref()
            .and_then(|h| h.advance(GlyphId::new(u32::from(g))));
        let rf_lsb = rf_hmtx
            .as_ref()
            .and_then(|h| h.side_bearing(GlyphId::new(u32::from(g))));
        t.check(
            adv == ttf.glyph_hor_advance(gid)
                && lsb == ttf.glyph_hor_side_bearing(gid)
                && adv == rf_adv
                && lsb == rf_lsb,
            None,
            || ctx(&format!("glyph {g} metrics: {adv:?} {lsb:?}")),
        );

        // Raw description against read-fonts.
        let ours = face.glyph(g);
        let rf_g = match (&rf_loca, &rf_glyf) {
            (Some(l), Some(gl)) => l.get_glyf(GlyphId::new(u32::from(g)), gl),
            _ => Err(read_fonts::ReadError::OutOfBounds),
        };
        let mut shape = Tree::default();
        tree(face, g, 0, &mut shape);
        match rf_g {
            Ok(r) => {
                let differs = raw_glyph_differs(&ours, r.clone());
                let wrapped = matches!(&ours, Ok(Glyph::Simple(s)) if s.points().filter_map(Result::ok).any(|p| i16::try_from(p.x).is_err() || i16::try_from(p.y).is_err()));
                let kind = if ours.is_err() {
                    Some("acceptance")
                } else if wrapped {
                    Some("i16-wrap")
                } else {
                    None
                };
                t.check(differs.is_none(), kind, || {
                    ctx(&format!("glyph {g} raw: {}", differs.unwrap_or_default()))
                });
            }
            Err(_) => t.check(ours.is_err(), Some("acceptance"), || {
                ctx(&format!("glyph {g}: read-fonts refuses it"))
            }),
        }

        // Flattened outline against ttf-parser.
        let ours = face.outline(g);
        let mut theirs = Segs::default();
        let drawn = ttf.outline_glyph(gid, &mut theirs).is_some();
        let theirs = if drawn { theirs.0 } else { Vec::new() };
        // Why the engines may disagree on this glyph, if they may.
        let shape_kind = if shape.point_matching {
            Some("ttf-parser-point-matching")
        } else if shape.scaled_offset {
            Some("ttf-parser-scaled-offset")
        } else if shape.transform_depth > 1 {
            Some("nested-transform")
        } else if shape.scale_flags {
            Some("ttf-parser-scale-flags")
        } else if shape.single_point {
            Some("ttf-parser-single-point")
        } else {
            None
        };
        let err_kind = |e: &Error| match e {
            Error::ComponentDepth if shape.depth < 32 && drawn => Some("depth"),
            _ if shape.unreadable && drawn => Some("ttf-parser-missing-component"),
            _ if shape.point_matching => Some("ttf-parser-point-matching"),
            _ => Some("acceptance"),
        };
        match &ours {
            Ok(o) => {
                let mine = segments(o);
                let tol = if shape.transformed { 1.0 } else { 0.0 };
                let kind = shape_kind.or_else(|| {
                    o.points
                        .iter()
                        .any(|p| i16::try_from(p.x).is_err() || i16::try_from(p.y).is_err())
                        .then_some("i16-wrap")
                });
                t.check(same_segments(&mine, &theirs, tol), kind, || {
                    ctx(&format!(
                        "glyph {g} outline: {} vs {} segments",
                        mine.len(),
                        theirs.len()
                    ))
                });
            }
            Err(e) => {
                t.check(!drawn, err_kind(e), || {
                    ctx(&format!("glyph {g} outline: ours {e}, ttf-parser draws it"))
                });
            }
        }

        // The glyph as a 26.6 path (item 5.10) against ttf-parser's outline
        // scaled to the same size, one size per glyph in turn. The path must
        // be well formed whatever the glyph; where we draw nothing (a
        // flattening error, or coordinates past i32 in 26.6), ttf-parser
        // must draw nothing either, with the same expected kinds as above.
        let size = usize::from(g)
            .checked_rem(SIZES.len())
            .and_then(|i| SIZES.get(i))
            .copied()
            .unwrap_or(1024);
        let path = face.path(g, size);
        t.check(path.is_well_formed(), None, || {
            ctx(&format!(
                "glyph {g} path at {size}/64 px is not well formed"
            ))
        });
        let scale = size as f32 / f32::from(face.units_per_em());
        match try_glyph_path(face, g, size) {
            Ok(_) => {
                let kind = shape_kind.or_else(|| {
                    ours.as_ref()
                        .is_ok_and(|o| {
                            o.points
                                .iter()
                                .any(|p| i16::try_from(p.x).is_err() || i16::try_from(p.y).is_err())
                        })
                        .then_some("i16-wrap")
                });
                // Rounding a point to 1/64 px moves it by at most half a
                // unit, and an implied point by at most one; a transformed
                // component's points are rounded to whole font units first.
                let tol = 1.01 + if shape.transformed { scale } else { 0.0 };
                let lone = path
                    .contours()
                    .any(|c| matches!(c, [p, q] if p.on_curve && !q.on_curve && (p.x, p.y) == (q.x, q.y)));
                let kind = kind.or_else(|| lone.then_some("ttf-parser-lone-off-curve"));
                let mine = path_cycles(&path);
                let theirs = scaled_cycles(&theirs, scale);
                t.check(same_cycles(&mine, &theirs, tol), kind, || {
                    ctx(&format!(
                        "glyph {g} path at {size}/64 px: {} vs {} contours",
                        mine.len(),
                        theirs.len()
                    ))
                });
            }
            Err(e) => {
                t.check(path.points.is_empty() && !drawn, err_kind(&e), || {
                    ctx(&format!("glyph {g} path: ours {e}, ttf-parser draws it"))
                });
            }
        }
    }
}

/// The sizes the 26.6 paths are compared at, in 1/64 px per em: 9, 16,
/// 37.5 and 200 px.
const SIZES: [i32; 4] = [576, 1024, 2400, 12_800];

/// A segment of a closed contour: a line to a point, or a quadratic
/// Bézier through a control point to a point.
#[derive(Debug, Clone, Copy)]
enum Step {
    Line(f32, f32),
    Quad(f32, f32, f32, f32),
}

/// Our path as cycles of segments, one per contour, from its on-curve
/// start; the closing line is explicit, as ttf-parser draws it.
fn path_cycles(path: &Path) -> Vec<Vec<Step>> {
    path.contours()
        .map(|c| {
            let f = |p: &PathPoint| (p.x as f32, p.y as f32);
            let mut out = Vec::new();
            let mut i = 1usize;
            while i <= c.len() {
                let next = i.saturating_add(1);
                match c.get(i).or(c.first()) {
                    Some(p) if p.on_curve || i == c.len() => {
                        let (x, y) = f(p);
                        out.push(Step::Line(x, y));
                        i = next;
                    }
                    Some(ctrl) => {
                        let (cx, cy) = f(ctrl);
                        let end = c.get(next).or(c.first()).map(f).unwrap_or((cx, cy));
                        out.push(Step::Quad(cx, cy, end.0, end.1));
                        i = next.saturating_add(1);
                    }
                    None => break,
                }
            }
            out
        })
        .collect()
}

/// ttf-parser's segments as cycles, scaled from font units to 26.6.
fn scaled_cycles(segs: &[Seg], k: f32) -> Vec<Vec<Step>> {
    let mut out = Vec::new();
    let mut current = Vec::new();
    for s in segs {
        match *s {
            Seg::Move(..) => current = Vec::new(),
            Seg::Line(x, y) => current.push(Step::Line(x * k, y * k)),
            Seg::Quad(a, b, x, y) => current.push(Step::Quad(a * k, b * k, x * k, y * k)),
            Seg::Close => out.push(std::mem::take(&mut current)),
        }
    }
    out
}

/// Whether two lists of cycles agree contour by contour, each pair equal
/// up to where the cycle starts, within `tol` on every coordinate.
fn same_cycles(a: &[Vec<Step>], b: &[Vec<Step>], tol: f32) -> bool {
    let near = |x: f32, y: f32| (x - y).abs() <= tol;
    let same = |s: &Step, t: &Step| match (s, t) {
        (Step::Line(a, b), Step::Line(c, d)) => near(*a, *c) && near(*b, *d),
        (Step::Quad(a, b, c, d), Step::Quad(e, f, g, h)) => {
            near(*a, *e) && near(*b, *f) && near(*c, *g) && near(*d, *h)
        }
        _ => false,
    };
    a.len() == b.len()
        && a.iter().zip(b).all(|(x, y)| {
            x.len() == y.len()
                && (x.is_empty()
                    || (0..y.len()).any(|r| {
                        x.iter()
                            .zip(y.iter().cycle().skip(r))
                            .all(|(s, t)| same(s, t))
                    }))
        })
}

fn compare_kern(
    face: &Face<'_>,
    ttf: &ttf_parser::Face<'_>,
    rf: &read_fonts::FontRef<'_>,
    budget: Budget,
    ctx: &dyn Fn(&str) -> String,
    t: &mut Tally,
) {
    let Ok(Some(kern)) = face.kern() else {
        return;
    };
    let ttf_subs: Vec<_> = ttf
        .tables()
        .kern
        .map(|k| k.subtables.into_iter().collect())
        .unwrap_or_default();
    let rf_kern = rf.kern().ok();
    let rf_subs: Vec<_> = rf_kern
        .as_ref()
        .map(|k| k.subtables().collect::<Vec<_>>())
        .unwrap_or_default();
    let mut index = 0usize;
    let _ = kern.subtables(|s| {
        let i = index;
        index = index.saturating_add(1);
        if s.format() != 0 {
            return Ok(());
        }
        let mut pairs = Vec::new();
        kern.format0_pairs(s, |l, r, v| pairs.push((l, r, v)))?;
        let key = |&(l, r, _): &(u16, u16, i16)| (u32::from(l) << 16) | u32::from(r);
        let sorted = pairs.windows(2).all(|w| match w {
            [a, b] => key(a) < key(b),
            _ => true,
        });
        for (l, r, v) in pairs.into_iter().step_by(budget.pair_stride) {
            let ours = kern.format0_value(s, l, r).ok().flatten();
            let theirs = ttf_subs
                .get(i)
                .and_then(|x| x.glyphs_kerning(ttf_parser::GlyphId(l), ttf_parser::GlyphId(r)));
            let rf_v = rf_subs.get(i).and_then(|x| x.as_ref().ok()).and_then(|x| match x.kind() {
                Ok(read_fonts::tables::kern::SubtableKind::Format0(f)) => {
                    f.kerning(GlyphId::new(u32::from(l)), GlyphId::new(u32::from(r)))
                }
                _ => None,
            });
            t.check(
                ours == Some(v) && theirs == Some(v) && rf_v == Some(i32::from(v)),
                (!sorted).then_some("unordered"),
                || ctx(&format!("kern {l},{r}: listed {v}, ours {ours:?}, ttf-parser {theirs:?}, read-fonts {rf_v:?}")),
            );
        }
        Ok(())
    });
}

fn compare_gpos(
    face: &Face<'_>,
    ttf: &ttf_parser::Face<'_>,
    rf: &read_fonts::FontRef<'_>,
    budget: Budget,
    ctx: &dyn Fn(&str) -> String,
    t: &mut Tally,
) {
    let Ok(Some(gpos)) = face.gpos() else {
        return;
    };
    let mut lookups = Vec::new();
    for script in [Tag(*b"latn"), Tag(*b"DFLT")] {
        lookups.extend(gpos.kern_lookups(script).unwrap_or_default());
    }
    lookups.sort_unstable();
    lookups.dedup();
    let (Some(ttf_gpos), Ok(rf_gpos)) = (ttf.tables().gpos, rf.gpos()) else {
        return;
    };
    let glyphs = sample_glyphs(face, budget.gpos_glyphs);
    for &l in &lookups {
        let ordered = gpos.lookup_is_ordered(l).unwrap_or(false);
        for &a in &glyphs {
            for &b in &glyphs {
                let result = gpos.pair_adjustment(l, a, b);
                let refused = result.is_err();
                let ours = result
                    .ok()
                    .flatten()
                    .map(|PairValue { first, second }| [ours_value(&first), ours_value(&second)]);
                let theirs = ttf_pair(&ttf_gpos, l, a, b);
                let rf_v = rf_pair(&rf_gpos, l, a, b);
                let kind = if refused {
                    Some("acceptance")
                } else if !ordered {
                    Some("unordered")
                } else {
                    None
                };
                t.check(ours == theirs && ours == rf_v, kind, || {
                    ctx(&format!("GPOS lookup {l} pair {a},{b}: ours {ours:?}, ttf-parser {theirs:?}, read-fonts {rf_v:?}"))
                });
            }
        }
    }
}

/// Every vendored font.
fn vendored() -> Vec<(&'static str, &'static [u8])> {
    let mut out = Vec::new();
    out.extend(dejavu::FONTS.iter().map(|c| (c.file, c.bytes)));
    out.extend(source_serif::FONTS.iter().map(|c| (c.file, c.bytes)));
    out.extend(source_code_pro::FONTS.iter().map(|c| (c.file, c.bytes)));
    out.extend(fontations::FONTS.iter().map(|c| (c.file, c.bytes)));
    out
}

#[test]
fn vendored_fonts() {
    let budget = if cfg!(miri) { MIRI } else { FULL };
    let mut t = Tally::default();
    for (name, data) in vendored() {
        compare_file(data, name, budget, &mut t);
    }
    for c in dejavu::FONTS
        .iter()
        .map(|c| (c.file, c.sha256))
        .chain(source_serif::FONTS.iter().map(|c| (c.file, c.sha256)))
        .chain(source_code_pro::FONTS.iter().map(|c| (c.file, c.sha256)))
        .chain(fontations::FONTS.iter().map(|c| (c.file, c.sha256)))
    {
        println!("  font {} sha256 {}", c.0, c.1);
    }
    t.report("vendored fonts vs ttf-parser and read-fonts");
    assert!(t.fail == 0, "{} unexpected differences", t.fail);
    // Every vendored font is read: no acceptance difference is expected.
    assert!(!t.xfail.contains_key("acceptance"));
}

/// Font directories by OS, read without enumeration services (5.0(c), S1).
const SYSTEM_DIRS: &[&str] = &[
    "/System/Library/Fonts",
    "/Library/Fonts",
    "/usr/share/fonts",
    "/usr/local/share/fonts",
    "C:\\Windows\\Fonts",
];

fn font_files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>, depth: u8) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() && depth < 6 {
            font_files(&p, out, depth.saturating_add(1));
        } else if p.extension().and_then(|e| e.to_str()).is_some_and(|e| {
            ["ttf", "otf", "ttc", "otc"].contains(&e.to_ascii_lowercase().as_str())
        }) {
            out.push(p);
        }
    }
}

#[test]
#[cfg_attr(miri, ignore = "opens files, which Miri's isolation forbids")]
fn system_fonts() {
    let mut files = Vec::new();
    for d in SYSTEM_DIRS {
        font_files(std::path::Path::new(d), &mut files, 0);
    }
    // Per face at most 3,000 glyphs and 100 GPOS glyphs, so a large CJK
    // collection does not dominate; files over 64 MB are skipped.
    let budget = Budget {
        max_glyphs: 3_000,
        max_code_points: 70_000,
        gpos_glyphs: 100,
        max_faces: 32,
        ..FULL
    };
    let mut t = Tally::default();
    let mut read = 0usize;
    for f in &files {
        let Ok(data) = std::fs::read(f) else { continue };
        if data.len() > 64 << 20 {
            continue;
        }
        read = read.saturating_add(1);
        compare_file(&data, &f.display().to_string(), budget, &mut t);
    }
    println!("system font files read: {read}");
    t.report("system fonts vs ttf-parser and read-fonts");
    assert!(t.fail == 0, "{} unexpected differences", t.fail);
}

/// xorshift64*, seeded: the same mutants every run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n.max(1)).unwrap_or(1);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }
}

/// One to four byte changes: in the table directory, in the first 256 bytes
/// of a table, or anywhere.
fn mutate(base: &[u8], rng: &mut Rng) -> Vec<u8> {
    let mut d = base.to_vec();
    let records: Vec<(usize, usize)> = FontFile::parse(base)
        .ok()
        .and_then(|f| f.directory(0).ok())
        .map(|dir| {
            (0..dir.num_tables())
                .filter_map(|i| dir.record(i).ok())
                .map(|r| (r.offset as usize, r.length as usize))
                .collect()
        })
        .unwrap_or_default();
    let changes = 1usize.saturating_add(rng.below(4));
    for _ in 0..changes {
        let at = match rng.below(10) {
            0..=2 => rng.below(12usize.saturating_add(records.len().saturating_mul(16))),
            3..=7 if !records.is_empty() => {
                let (off, len) = records
                    .get(rng.below(records.len()))
                    .copied()
                    .unwrap_or((0, 0));
                off.saturating_add(rng.below(len.min(256)))
            }
            _ => rng.below(d.len()),
        };
        let v = match rng.below(4) {
            0 => 0,
            1 => 0xFF,
            2 => d.get(at).map_or(0, |b| b ^ (1 << rng.below(8))),
            _ => (rng.next() & 0xFF) as u8,
        };
        if let Some(b) = d.get_mut(at) {
            *b = v;
        }
    }
    d
}

thread_local! {
    /// The source file of the last panic on this thread.
    static PANIC_AT: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

#[test]
fn mutated_fonts() {
    // Under Miri, 12 mutants of the small fontations fonts: enough to run
    // every parser on damaged input, within about a minute.
    let (count, bases): (usize, Vec<(&str, &[u8])>) = if cfg!(miri) {
        (
            12,
            fontations::FONTS
                .iter()
                .map(|c| (c.file, c.bytes))
                .collect(),
        )
    } else {
        (10_000, vendored())
    };
    // Record where a panic happened, quietly on this thread (the default hook
    // still reports panics on other threads).
    let previous = std::sync::Arc::new(std::panic::take_hook());
    let chained = std::sync::Arc::clone(&previous);
    std::panic::set_hook(Box::new(move |info| {
        if std::thread::current().name() == Some("mutated_fonts") {
            let at = info.location().map(|l| l.file().to_owned());
            PANIC_AT.with(|p| *p.borrow_mut() = at);
        } else {
            chained(info);
        }
    }));
    let mut rng = Rng(0x00C1_A2E1_F047_5EED);
    let mut units = Tally::default();
    let mut kinds: BTreeMap<&'static str, u64> = BTreeMap::new();
    for i in 0..count {
        let (name, base) = bases
            .get(i % bases.len().max(1))
            .copied()
            .unwrap_or(("", &[]));
        let m = mutate(base, &mut rng);
        let mut t = Tally::default();
        let label = format!("mutant {i} of {name}");
        let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut inner = Tally::default();
            compare_file(&m, &label, MUTANT, &mut inner);
            inner
        }));
        match run {
            Ok(inner) => t = inner,
            Err(_) => {
                let at = PANIC_AT.with(|p| p.borrow_mut().take()).unwrap_or_default();
                let theirs = at.contains("ttf-parser-") || at.contains("read-fonts-");
                t.diff(theirs.then_some("reference-panic"), || {
                    format!("{label}: panic at {at}")
                });
            }
        }
        for (k, n) in &t.xfail {
            let e = kinds.entry(k).or_insert(0);
            *e = e.saturating_add(*n);
        }
        if t.fail > 0 {
            units.diff(None, || t.messages.first().cloned().unwrap_or_default());
        } else if t.xfail_total() > 0 {
            // Name the mutant's first expected kind, for the per-kind count.
            let k = t.xfail.keys().next().copied().unwrap_or("acceptance");
            units.diff(Some(k), String::new);
        } else {
            units.ok();
        }
    }
    drop(std::panic::take_hook());
    std::panic::set_hook(Box::new(move |info| previous(info)));
    units.report("10,000 mutated fonts vs ttf-parser and read-fonts");
    for (k, n) in &kinds {
        println!("  checks of kind {k} across mutants: {n}");
    }
    assert!(
        units.fail == 0,
        "{} mutants with unexpected differences",
        units.fail
    );
}

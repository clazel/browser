//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! Each harness runs a parser on **every** byte string up to a stated length
//! (a symbolic array and a symbolic length), or on a larger symbolic buffer
//! at symbolic offsets so that offsets and counts near the end of a slice
//! are covered. Kani checks that no panic, arithmetic overflow, or read
//! outside a slice is reachable, and its unwinding assertions check that
//! every loop finishes within the stated bound (a loop that could run
//! longer fails the harness). The bounds are in each harness's name and
//! comment, and in the crate's README.
//!
//! What is not covered, and why:
//!
//! - A simple glyph can declare up to 65,536 points in a few bytes (flag
//!   repeats with "same" coordinates take no bytes). Its decoder is
//!   checked one step at a time on **any** state ([`glyf_point_step`]), which
//!   is the loop body for every point count; whole glyphs of up to 20 bytes
//!   are checked to their first point ([`glyf_glyph_any_20`]). Component
//!   records are likewise checked one step at a time from any state
//!   ([`glyf_component_step`]), the loop body for every component count.
//! - Not done: these harnesses time out (40 minutes) or exhaust memory locally
//!   even at very small bounds, so they are not in the crate. Each is
//!   covered only by unit tests and the differential test:
//!   - `loca` with `glyf` flattened to an outline (`Face::outline`);
//!   - `name` lookup with UTF-16BE decoding of the chosen record (the
//!     decoder alone is [`name_decode_any_8`]);
//!   - `GPOS` from the table header: the `kern` lookups of a script and the
//!     pair adjustment of a lookup (one PairPos subtable is
//!     [`pair_pos_48`]; Coverage and ClassDef are
//!     [`coverage_class_def_128`]);
//!   - `Face::parse` (each table it reads has its own harness);
//!   - item 5.10's whole-contour and whole-path conversions
//!     (`outline::contour::push_contour` on a contour of 2 points, and
//!     `outline::path_from_outline` on an outline of 2 points in 2
//!     contours, each asserting `Path::is_well_formed`): both ran past 20
//!     minutes locally; one of 4 points ran out of memory at 10 GB after
//!     10.5 minutes. What they would check is covered by
//!     [`outline_contour_start`] (the start is on-curve) and
//!     [`outline_contour_step`] (each step keeps no two consecutive
//!     off-curve points), which give well-formedness for every length by
//!     induction over the loop, by [`outline_scale_any`] and
//!     [`outline_midpoint_any`] for the arithmetic, and by the unit tests
//!     and the differential test, which checks every glyph's path is well
//!     formed.

use crate::Tag;
use crate::cmap::{Cmap, Subtable};
use crate::file::{Collection, FontFile, TableDirectory};
use crate::glyf::{self, Glyph, PointDecoder};
use crate::head::{Head, LocaFormat};
use crate::hhea::Hhea;
use crate::hmtx::Hmtx;
use crate::kern::Kern;
use crate::layout::{ClassDef, Coverage, pair_pos_apply};
use crate::loca::Loca;
use crate::maxp::Maxp;
use crate::name;
use crate::os2::Os2;
use crate::outline::{PathPoint, contour};
use crate::post::Post;

/// A symbolic byte string of length at most `N`.
fn bytes<const N: usize>(data: &[u8; N]) -> &[u8] {
    let len: usize = kani::any();
    kani::assume(len <= N);
    data.get(..len).unwrap_or(&[])
}

/// The readers, on any 8 bytes and any offset and length.
#[kani::proof]
fn read_any_8() {
    let data: [u8; 8] = kani::any();
    let d = bytes(&data);
    let at: usize = kani::any();
    let len: usize = kani::any();
    let _ = crate::read::u16_at(d, at);
    let _ = crate::read::u32_at(d, at);
    let _ = crate::read::i8_at(d, at);
    let _ = crate::read::slice(d, at, len);
    let _ = crate::read::element(at, len, kani::any());
}

/// The table directory and collection header, on every file of up to 44
/// bytes (a header and two table records), with each record's table and
/// checksum (at most 8 words).
#[kani::proof]
#[kani::unwind(12)]
fn directory_any_44() {
    let data: [u8; 44] = kani::any();
    let d = bytes(&data);
    if let Ok(file) = FontFile::parse(d) {
        let index: u32 = kani::any();
        if let Ok(dir) = file.directory(index) {
            let i: u16 = kani::any();
            if let Ok(r) = dir.record(i) {
                let _ = dir.record_data(&r);
                let _ = dir.checksum_matches(&r);
            }
            let _ = dir.find(Tag::HEAD);
        }
    }
}

/// A directory and a collection header at symbolic offsets in a 4 KiB
/// file: records and tables whose offset plus length passes the end, or
/// overflows, are refused without a read outside the file.
#[kani::proof]
#[kani::unwind(3)]
fn directory_offsets_4k() {
    let data: [u8; 4096] = kani::any();
    let at: usize = kani::any();
    if let Ok(dir) = TableDirectory::parse_at(&data, at) {
        let i: u16 = kani::any();
        kani::assume(i < dir.num_tables());
        if let Ok(r) = dir.record(i) {
            let _ = dir.record_data(&r);
        }
    }
    if let Ok(c) = Collection::parse(&data) {
        let _ = c.directory(kani::any());
    }
}

/// The fixed-size tables, on every byte string of up to 104 bytes (more
/// than `OS/2` version 5's 100).
#[kani::proof]
fn fixed_tables_any_104() {
    let data: [u8; 104] = kani::any();
    let d = bytes(&data);
    let _ = Head::parse(d);
    let _ = Hhea::parse(d);
    let _ = Maxp::parse(d);
    let _ = Post::parse(d);
    if let Ok(o) = Os2::parse(d) {
        let _ = o.use_typo_metrics();
    }
}

/// `hmtx` on any 4 KiB table, any counts and any glyph: reads near the end
/// of the table and for every glyph index.
#[kani::proof]
fn hmtx_any_counts_4k() {
    let data: [u8; 4096] = kani::any();
    let d = bytes(&data);
    if let Ok(h) = Hmtx::parse(d, kani::any(), kani::any()) {
        let g: u16 = kani::any();
        let _ = h.advance(g);
        let _ = h.left_side_bearing(g);
    }
}

/// `loca` on any 4 KiB table, either format, any glyph count and glyph.
#[kani::proof]
fn loca_any_4k() {
    let data: [u8; 4096] = kani::any();
    let d = bytes(&data);
    let format = if kani::any() {
        LocaFormat::Short
    } else {
        LocaFormat::Long
    };
    if let Ok(l) = Loca::parse(d, format, kani::any()) {
        let _ = l.glyph_range(kani::any());
    }
}

/// One step of the simple-glyph point decoder from **any** state: any
/// positions, flag, repeat count, coordinates and points left, over any 64
/// bytes. This is the loop body for every point of every simple glyph.
#[kani::proof]
fn glyf_point_step() {
    let data: [u8; 64] = kani::any();
    let mut d = PointDecoder {
        data: &data,
        flags_at: kani::any(),
        x_at: kani::any(),
        y_at: kani::any(),
        flag: kani::any(),
        repeats: kani::any(),
        x: kani::any(),
        y: kani::any(),
        left: kani::any(),
    };
    let _ = d.step();
}

/// Every glyph description of up to 20 bytes: the header and the dispatch;
/// for a simple glyph, `endPtsOfContours` (at most 5), the flag walk over
/// the up to 6 bytes left after one contour's arrays (flags, repeat counts
/// and both coordinate sizes), any contour end and the first point. The
/// rest of the points are the decoder's steps, `glyf_point_step`; a
/// composite's records are `glyf_component_step`.
#[kani::proof]
#[kani::unwind(8)]
fn glyf_glyph_any_20() {
    let data: [u8; 20] = kani::any();
    let d = bytes(&data);
    match Glyph::parse(d) {
        Ok(Glyph::Simple(s)) => {
            let _ = s.points().next();
            let _ = s.end_point(kani::any());
        }
        Ok(Glyph::Composite(c)) => {
            let _ = c.components().next();
        }
        _ => {}
    }
}

/// One component record read from **any** state over any 20 bytes (a
/// record is at most 16): every combination of `ARG_1_AND_2_ARE_WORDS`,
/// `ARGS_ARE_XY_VALUES`, the three scale forms and `MORE_COMPONENTS`, at
/// any position, including past the end. This is the body of the
/// `Components` loop, for every component count; it has no loop itself.
#[kani::proof]
fn glyf_component_step() {
    let data: [u8; 20] = kani::any();
    let mut c = glyf::Components {
        data: bytes(&data),
        at: kani::any(),
        done: kani::any(),
    };
    if let Ok(Some(comp)) = c.step() {
        let _ = comp.scaled_offset();
    }
}

/// A component transform on any matrix and any point.
#[kani::proof]
fn glyf_transform_any() {
    let t = glyf::Transform {
        xx: kani::any(),
        yx: kani::any(),
        xy: kani::any(),
        yy: kani::any(),
    };
    let _ = t.apply(kani::any(), kani::any());
}

/// `cmap` on every table of up to 28 bytes: the header, the encoding
/// records (at most 2) and the subtable choice, which parses each Unicode
/// record's subtable. Lookups, ranges and the order check on a subtable
/// are `cmap_subtable_any_24` (any subtable of up to 24 bytes; one reached
/// here can be up to 27, since an offset may point back into the header).
#[kani::proof]
#[kani::unwind(6)]
fn cmap_any_28() {
    let data: [u8; 28] = kani::any();
    let d = bytes(&data);
    if let Ok(c) = Cmap::parse(d) {
        let _ = c.best_subtable();
    }
}

/// Every `cmap` subtable of up to 24 bytes, of any format (format 6 with up
/// to 7 entries, format 4 with 1 segment): a lookup of any character. The
/// ranges are `cmap_ranges_any_24` and the order check `cmap_order_any_24`.
#[kani::proof]
#[kani::unwind(9)]
fn cmap_subtable_any_24() {
    let data: [u8; 24] = kani::any();
    if let Ok(s) = Subtable::parse(bytes(&data)) {
        let _ = s.map(kani::any());
    }
}

/// The ranges of every `cmap` subtable of up to 24 bytes.
#[kani::proof]
#[kani::unwind(9)]
fn cmap_ranges_any_24() {
    let data: [u8; 24] = kani::any();
    if let Ok(s) = Subtable::parse(bytes(&data)) {
        let _ = s.ranges(|_, _| {});
    }
}

/// The order check on every `cmap` subtable of up to 24 bytes.
#[kani::proof]
#[kani::unwind(9)]
fn cmap_order_any_24() {
    let data: [u8; 24] = kani::any();
    if let Ok(s) = Subtable::parse(bytes(&data)) {
        let _ = s.is_ordered();
    }
}

/// `cmap` format 4 and 12 lookups of any character in any 128-byte subtable:
/// any segment or group count, so the bisection's reads near the end of
/// the arrays are covered (at most 7 halvings).
#[kani::proof]
#[kani::unwind(8)]
fn cmap_lookup_128() {
    let data: [u8; 128] = kani::any();
    let d = bytes(&data);
    if let Ok(s @ (Subtable::Format4(_) | Subtable::Format12(_) | Subtable::Format6(_))) =
        Subtable::parse(d)
    {
        let _ = s.map(kani::any());
    }
}

/// UTF-16BE decoding of every byte string of up to 8 bytes.
#[kani::proof]
#[kani::unwind(6)]
fn name_decode_any_8() {
    let data: [u8; 8] = kani::any();
    let _ = name::decode_utf16be(bytes(&data));
}

/// `kern` on every table of up to 32 bytes: the kerning of any pair, over
/// every subtable (at most 4, or 1 with 2 pairs) and its pairs.
#[kani::proof]
#[kani::unwind(7)]
fn kern_any_32() {
    let data: [u8; 32] = kani::any();
    let d = bytes(&data);
    if let Ok(k) = Kern::parse(d) {
        let _ = k.kerning(kani::any(), kani::any());
    }
}

/// `kern` format 0 lookups of any pair in any 128-byte table: any `nPairs`,
/// so the bisection's reads near the end are covered.
#[kani::proof]
#[kani::unwind(8)]
fn kern_lookup_128() {
    let data: [u8; 128] = kani::any();
    if let Ok(k) = Kern::parse(&data) {
        let s = crate::kern::Subtable {
            offset: 4,
            length: kani::any(),
            coverage: kani::any(),
        };
        let _ = k.format0_value(&s, kani::any(), kani::any());
    }
}

/// Coverage and ClassDef lookups of any glyph in any 128-byte table.
#[kani::proof]
#[kani::unwind(8)]
fn coverage_class_def_128() {
    let data: [u8; 128] = kani::any();
    let g: u16 = kani::any();
    let _ = Coverage::new(&data).index(g);
    let _ = ClassDef::new(&data).class(g);
}

/// A PairPos subtable of either format applied to any pair, in any 48-byte
/// subtable: room for a format 2 header, a Coverage table, two ClassDefs
/// and class records, or a format 1 PairSet with its records.
#[kani::proof]
#[kani::unwind(7)]
fn pair_pos_48() {
    let data: [u8; 48] = kani::any();
    let _ = pair_pos_apply(&data, kani::any(), kani::any());
}

// Item 5.10: outlines in 26.6. Each harness checks one operation, as
// above; the whole path (`try_glyph_path`) is these operations composed
// over `glyf::outline`, whose flattening is not a harness (see the module
// comment, "Not done").

/// Scaling any coordinate in font units at any size and any `unitsPerEm`
/// (0 included, which `head` refuses): never a panic or an overflow, and a
/// result only for a size that is not negative.
#[kani::proof]
fn outline_scale_any() {
    let v: i32 = kani::any();
    let size: i32 = kani::any();
    let upem: u16 = kani::any();
    if crate::outline::scale::scale(v, size, upem).is_ok() {
        assert!(size >= 0 && upem > 0);
    }
}

/// The implied point between any two coordinates lies between them.
#[kani::proof]
fn outline_midpoint_any() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    let m = crate::outline::scale::midpoint(a, b);
    assert!(m >= a.min(b) && m <= a.max(b));
}

/// One step of the contour conversion from **any** state: any previous
/// point and any next point. The step appends the point, after an implied
/// on-curve point exactly when both are off-curve, so no two consecutive
/// points it leaves are off-curve. This is the loop body of
/// `contour::push_contour` for every contour length.
#[kani::proof]
#[kani::unwind(4)]
fn outline_contour_step() {
    let any_point = || PathPoint {
        x: kani::any(),
        y: kani::any(),
        on_curve: kani::any(),
    };
    let previous = any_point();
    let p = any_point();
    let mut out = vec![previous];
    contour::push_point(&previous, &p, &mut out);
    assert!(out.last() == Some(&p));
    assert!(
        out.len()
            == if previous.on_curve || p.on_curve {
                2
            } else {
                3
            }
    );
    assert!(
        out.windows(2)
            .all(|w| matches!(w, [a, b] if a.on_curve || b.on_curve))
    );
}

/// The start of a contour from **any** first and last point: always
/// on-curve, and the first or last point itself whenever that is on-curve.
/// With [`outline_contour_step`], which keeps "no two consecutive off-curve
/// points" for every point appended after it, this gives a well-formed
/// contour of every length, by induction over the loop.
#[kani::proof]
fn outline_contour_start() {
    let any_point = || PathPoint {
        x: kani::any(),
        y: kani::any(),
        on_curve: kani::any(),
    };
    let first = any_point();
    let last = any_point();
    let start = contour::contour_start(&first, &last);
    assert!(start.on_curve);
    if first.on_curve {
        assert!(start == first);
    } else if last.on_curve {
        assert!(start == last);
    }
}

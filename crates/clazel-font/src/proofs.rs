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
//!   is the loop body for every point count, and whole glyphs of up to 14
//!   bytes are checked for their first 4 points ([`glyf_glyph_any_14`]).
//! - Flattening is checked with smaller limits than the stated ones (depth
//!   1, 2 components, 2 points; [`outline_loca_glyf`]): the code is the
//!   same, the limits are only compared against counters.
//! - `Face::parse` is checked on inputs of up to 24 bytes, which are too
//!   short for a whole face, so its success path is covered by the tables'
//!   harnesses and the differential test, not by this one.

use crate::cmap::{Cmap, Subtable};
use crate::file::{Collection, FontFile, TableDirectory};
use crate::glyf::{self, Glyf, Glyph, Limits, PointDecoder};
use crate::head::{Head, LocaFormat};
use crate::hhea::Hhea;
use crate::hmtx::Hmtx;
use crate::kern::Kern;
use crate::layout::{ClassDef, Coverage, Gpos, pair_pos_apply};
use crate::loca::Loca;
use crate::maxp::Maxp;
use crate::name::{self, Name};
use crate::os2::Os2;
use crate::post::Post;
use crate::{Face, Tag};

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

/// Every glyph description of up to 14 bytes: the header, a simple glyph's
/// flag walk and its first 4 points and contour ends, or a composite's
/// component record (the transform itself is `glyf_transform_any`).
#[kani::proof]
#[kani::unwind(15)]
fn glyf_glyph_any_14() {
    let data: [u8; 14] = kani::any();
    let d = bytes(&data);
    match Glyph::parse(d) {
        Ok(Glyph::Simple(s)) => {
            let mut points = s.points();
            for _ in 0..4 {
                if points.next().is_none() {
                    break;
                }
            }
            let _ = s.end_point(kani::any());
        }
        Ok(Glyph::Composite(c)) => {
            for comp in c.components() {
                if let Ok(comp) = comp {
                    let _ = comp.scaled_offset();
                }
            }
        }
        _ => {}
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

/// `loca` with `glyf` on a symbolic glyph index: any short `loca` of three
/// glyphs and any `glyf` of up to 12 bytes, flattened with limits depth 1,
/// 2 components and 2 points (so composites, nesting past the bound,
/// cycles and point matching are all reached).
#[kani::proof]
#[kani::unwind(4)]
fn outline_loca_glyf() {
    let loca_bytes: [u8; 8] = kani::any();
    let glyf_bytes: [u8; 12] = kani::any();
    let g = bytes(&glyf_bytes);
    if let Ok(loca) = Loca::parse(&loca_bytes, LocaFormat::Short, 3) {
        let glyf = Glyf::new(g);
        let glyph: u16 = kani::any();
        let _ = glyf.glyph(&loca, glyph);
        let limits = Limits {
            depth: 1,
            components: 2,
            points: 2,
        };
        let _ = glyf::outline_within(&glyf, &loca, glyph, limits);
    }
}

/// `cmap` on every table of up to 40 bytes: the header, the subtable
/// choice (at most 4 records), a lookup of any character, the ranges and
/// the order check.
#[kani::proof]
#[kani::unwind(6)]
fn cmap_any_28() {
    let data: [u8; 28] = kani::any();
    let d = bytes(&data);
    if let Ok(c) = Cmap::parse(d) {
        if let Ok(Some((_, s))) = c.best_subtable() {
            let _ = s.map(kani::any());
            let _ = s.ranges(|_, _| {});
            let _ = s.is_ordered();
        }
    }
}

/// `cmap` format 4 and 12 lookups of any character in any 512-byte subtable:
/// any segment or group count, so the bisection's reads near the end of
/// the arrays are covered (at most 10 halvings).
#[kani::proof]
#[kani::unwind(11)]
fn cmap_lookup_512() {
    let data: [u8; 512] = kani::any();
    let d = bytes(&data);
    if let Ok(s @ (Subtable::Format4(_) | Subtable::Format12(_) | Subtable::Format6(_))) =
        Subtable::parse(d)
    {
        let _ = s.map(kani::any());
    }
}

/// `name` on every table of up to 16 bytes: any record, its string's bytes,
/// and a lookup of any name ID (at most 1 record, whose string, anywhere in
/// the table, is decoded).
#[kani::proof]
#[kani::unwind(9)]
fn name_any_16() {
    let data: [u8; 16] = kani::any();
    let d = bytes(&data);
    if let Ok(n) = Name::parse(d) {
        if let Ok(r) = n.record(kani::any()) {
            let _ = n.string_bytes(&r);
        }
        let _ = n.get(kani::any());
    }
}

/// UTF-16BE decoding of every byte string of up to 8 bytes.
#[kani::proof]
#[kani::unwind(6)]
fn name_decode_any_8() {
    let data: [u8; 8] = kani::any();
    let _ = name::decode_utf16be(bytes(&data));
}

/// `kern` on every table of up to 40 bytes: the kerning of any pair, over
/// every subtable (at most 6) and its pairs.
#[kani::proof]
#[kani::unwind(8)]
fn kern_any_40() {
    let data: [u8; 40] = kani::any();
    let d = bytes(&data);
    if let Ok(k) = Kern::parse(d) {
        let _ = k.kerning(kani::any(), kani::any());
    }
}

/// `kern` format 0 lookups of any pair in any 512-byte table: any `nPairs`,
/// so the bisection's reads near the end are covered.
#[kani::proof]
#[kani::unwind(11)]
fn kern_lookup_512() {
    let data: [u8; 512] = kani::any();
    if let Ok(k) = Kern::parse(&data) {
        let s = crate::kern::Subtable {
            offset: 4,
            length: kani::any(),
            coverage: kani::any(),
        };
        let _ = k.format0_value(&s, kani::any(), kani::any());
    }
}

/// Coverage and ClassDef lookups of any glyph in any 512-byte table.
#[kani::proof]
#[kani::unwind(11)]
fn coverage_class_def_512() {
    let data: [u8; 512] = kani::any();
    let g: u16 = kani::any();
    let _ = Coverage::new(&data).index(g);
    let _ = ClassDef::new(&data).class(g);
}

/// A PairPos subtable of either format applied to any pair, in any 512-byte
/// subtable.
#[kani::proof]
#[kani::unwind(11)]
fn pair_pos_512() {
    let data: [u8; 512] = kani::any();
    let _ = pair_pos_apply(&data, kani::any(), kani::any());
}

/// `GPOS` on every table of up to 16 bytes: the `kern` lookups of any
/// script.
#[kani::proof]
#[kani::unwind(6)]
fn gpos_kern_lookups_any_16() {
    let data: [u8; 16] = kani::any();
    if let Ok(g) = Gpos::parse(bytes(&data)) {
        let _ = g.kern_lookups(Tag(kani::any()));
    }
}

/// `GPOS` on every table of up to 16 bytes: the pair adjustment of any
/// lookup for any pair (a PairPos subtable itself is `pair_pos_512`).
#[kani::proof]
#[kani::unwind(6)]
fn gpos_pair_adjustment_any_16() {
    let data: [u8; 16] = kani::any();
    if let Ok(g) = Gpos::parse(bytes(&data)) {
        let _ = g.pair_adjustment(kani::any(), kani::any(), kani::any());
    }
}

/// `Face::parse` on every file of up to 24 bytes (too short for a face; see
/// the module comment).
#[kani::proof]
#[kani::unwind(6)]
fn face_any_24() {
    let data: [u8; 24] = kani::any();
    let _ = Face::parse(bytes(&data), kani::any());
}

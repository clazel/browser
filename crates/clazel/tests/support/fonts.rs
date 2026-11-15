//! Malicious fonts for item 5.26 (`hostile_graphics.rs`): DejaVu Serif with one
//! thing broken, as the item lists them. Each function edits the font's bytes in
//! place, following the OpenType table directory (OpenType 1.9.1, "Organization
//! of an OpenType font": the offset table, then 16-byte table records of tag,
//! checksum, offset and length), and gives `None` if the font is not shaped as
//! expected. Checksums are not fixed up: our reader does not check them.
//!
//! Glyph edits are made to the glyph of `x`, which the hostile page draws.

use clazel_font::Face;

fn be16(b: &[u8], at: usize) -> Option<u16> {
    Some(u16::from_be_bytes(
        b.get(at..at.checked_add(2)?)?.try_into().ok()?,
    ))
}

fn be32(b: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_be_bytes(
        b.get(at..at.checked_add(4)?)?.try_into().ok()?,
    ))
}

fn put16(b: &mut [u8], at: usize, v: u16) -> Option<()> {
    b.get_mut(at..at.checked_add(2)?)?
        .copy_from_slice(&v.to_be_bytes());
    Some(())
}

fn put32(b: &mut [u8], at: usize, v: u32) -> Option<()> {
    b.get_mut(at..at.checked_add(4)?)?
        .copy_from_slice(&v.to_be_bytes());
    Some(())
}

/// The table record of `tag`: where its offset field is, and the table's offset.
fn record(b: &[u8], tag: &[u8; 4]) -> Option<(usize, usize)> {
    let n = usize::from(be16(b, 4)?);
    (0..n).find_map(|i| {
        let at = 12usize.checked_add(i.checked_mul(16)?)?;
        (b.get(at..at.checked_add(4)?)? == tag).then_some(())?;
        let field = at.checked_add(8)?;
        Some((field, usize::try_from(be32(b, field)?).ok()?))
    })
}

fn table(b: &[u8], tag: &[u8; 4]) -> Option<usize> {
    record(b, tag).map(|(_, offset)| offset)
}

/// The glyph of `x`.
fn glyph_x(b: &[u8]) -> Option<u16> {
    Face::parse(b, 0).ok()?.glyph_index('x').ok().flatten()
}

/// Where `loca` entry `i` is, and how to read and write it (`head`'s
/// `indexToLocFormat`: 0 short, offsets halved; 1 long).
struct Loca {
    at: usize,
    long: bool,
}

impl Loca {
    fn of(b: &[u8]) -> Option<Loca> {
        let head = table(b, b"head")?;
        Some(Loca {
            at: table(b, b"loca")?,
            long: be16(b, head.checked_add(50)?)? == 1,
        })
    }

    fn get(&self, b: &[u8], i: u16) -> Option<usize> {
        let i = usize::from(i);
        if self.long {
            usize::try_from(be32(b, self.at.checked_add(i.checked_mul(4)?)?)?).ok()
        } else {
            usize::from(be16(b, self.at.checked_add(i.checked_mul(2)?)?)?).checked_mul(2)
        }
    }

    fn set(&self, b: &mut [u8], i: u16, v: usize) -> Option<()> {
        let i = usize::from(i);
        if self.long {
            put32(
                b,
                self.at.checked_add(i.checked_mul(4)?)?,
                u32::try_from(v).ok()?,
            )
        } else {
            put16(
                b,
                self.at.checked_add(i.checked_mul(2)?)?,
                u16::try_from(v / 2).ok()?,
            )
        }
    }
}

/// Where glyph `g`'s data starts in the file, and its length.
fn glyph_data(b: &[u8], g: u16) -> Option<(usize, usize)> {
    let loca = Loca::of(b)?;
    let (start, end) = (loca.get(b, g)?, loca.get(b, g.checked_add(1)?)?);
    Some((
        table(b, b"glyf")?.checked_add(start)?,
        end.checked_sub(start)?,
    ))
}

/// `glyf`'s offset points far past the end of the file.
pub fn offsets_past_the_end(b: &mut [u8]) -> Option<()> {
    let (field, _) = record(b, b"glyf")?;
    let past = u32::try_from(b.len()).ok()?.checked_add(4096)?;
    put32(b, field, past)
}

/// `loca` is placed over `glyf`: the two tables overlap.
pub fn overlapping_tables(b: &mut [u8]) -> Option<()> {
    let glyf = u32::try_from(table(b, b"glyf")?).ok()?;
    let (field, _) = record(b, b"loca")?;
    put32(b, field, glyf)
}

/// The `loca` entries around `x`'s glyph are swapped, so offsets go down.
pub fn loca_not_monotone(b: &mut [u8]) -> Option<()> {
    let g = glyph_x(b)?;
    let loca = Loca::of(b)?;
    let (here, next) = (loca.get(b, g)?, loca.get(b, g.checked_add(1)?)?);
    (here < next).then_some(())?;
    loca.set(b, g, next)?;
    loca.set(b, g.checked_add(1)?, here)
}

/// `x`'s glyph is a composite whose one component is itself (`glyf`: a negative
/// contour count, the bounding box, then flags `ARG_1_AND_2_ARE_WORDS |
/// ARGS_ARE_XY_VALUES`, the glyph index, two zero offsets).
pub fn composite_containing_itself(b: &mut [u8]) -> Option<()> {
    let g = glyph_x(b)?;
    let (at, len) = glyph_data(b, g)?;
    (len >= 18).then_some(())?;
    let words: [u16; 9] = [0xFFFF, 0, 0, 100, 100, 0x0003, g, 0, 0];
    for (i, w) in words.iter().enumerate() {
        put16(b, at.checked_add(i.checked_mul(2)?)?, *w)?;
    }
    Some(())
}

/// `x`'s glyph claims 32,767 contours in its few bytes.
pub fn contours_32767(b: &mut [u8]) -> Option<()> {
    let g = glyph_x(b)?;
    let (at, len) = glyph_data(b, g)?;
    (len >= 10).then_some(())?;
    put16(b, at, 32_767)
}

/// In the format 4 `cmap` subtable, the second segment starts where the first
/// does, so the two overlap.
pub fn overlapping_cmap_segments(b: &mut [u8]) -> Option<()> {
    let cmap = table(b, b"cmap")?;
    let n = usize::from(be16(b, cmap.checked_add(2)?)?);
    let sub = (0..n).find_map(|i| {
        let rec = cmap.checked_add(4)?.checked_add(i.checked_mul(8)?)?;
        let sub = cmap.checked_add(usize::try_from(be32(b, rec.checked_add(4)?)?).ok()?)?;
        (be16(b, sub)? == 4).then_some(sub)
    })?;
    let seg_x2 = usize::from(be16(b, sub.checked_add(6)?)?);
    (seg_x2 >= 4).then_some(())?;
    let starts = sub.checked_add(14)?.checked_add(seg_x2)?.checked_add(2)?;
    let first = be16(b, starts)?;
    put16(b, starts.checked_add(2)?, first)
}

/// `maxp.numGlyphs` says 65,535, far more than `loca` holds.
pub fn num_glyphs_disagreeing(b: &mut [u8]) -> Option<()> {
    let maxp = table(b, b"maxp")?;
    put16(b, maxp.checked_add(4)?, 0xFFFF)
}

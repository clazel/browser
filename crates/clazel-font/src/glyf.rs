//! `glyf`, glyph data (OpenType 1.9, chapter `glyf`; Apple's manual,
//! "'glyf' table").
//!
//! <https://learn.microsoft.com/en-us/typography/opentype/otspec190/glyf>.
//!
//! A glyph is decoded only when asked for. [`Glyph::parse`] reads the glyph
//! header and checks that a simple glyph's arrays fit its bytes, without
//! allocating; [`SimpleGlyph::points`] then decodes points one at a time,
//! and [`CompositeGlyph::components`] reads component records one at a time.
//! [`outline`] flattens a glyph and its components into one [`Outline`],
//! within [`MAX_COMPONENT_DEPTH`], [`MAX_COMPONENTS`] and [`MAX_POINTS`].
//!
//! Instructions are skipped by their length and never interpreted, and the
//! phantom points the chapter mentions (which come from hinting and
//! metrics) are not modelled: point matching may name only real points.

use crate::loca::Loca;
use crate::read::{add, i8_at, i16_at, slice, tail, u8_at, u16_at};
use crate::{Error, Tag};

/// How deeply composites may nest: a glyph's components are at depth 1,
/// theirs at depth 2, and so on. The chapter sets no minimum ("There is no
/// minimum nesting depth that must be supported") and says the graph "must
/// be acyclic"; a cycle exceeds any depth, so this bound also ends cycles.
pub const MAX_COMPONENT_DEPTH: u8 = 8;
/// How many component references one flattened outline may follow in all,
/// at every depth together. With the depth bound this keeps a glyph that
/// references a composite many times, which references another many times,
/// from multiplying.
pub const MAX_COMPONENTS: usize = 1024;
/// How many points one flattened outline may hold: one more than the
/// largest point number a `uint16` can name (`endPtsOfContours`, and the
/// point-matching arguments).
pub const MAX_POINTS: usize = 65_536;

/// Simple Glyph Flags (chapter `glyf`, "Simple Glyph Flags").
pub mod simple_flags {
    /// `ON_CURVE_POINT`, bit 0.
    pub const ON_CURVE_POINT: u8 = 0x01;
    /// `X_SHORT_VECTOR`, bit 1.
    pub const X_SHORT_VECTOR: u8 = 0x02;
    /// `Y_SHORT_VECTOR`, bit 2.
    pub const Y_SHORT_VECTOR: u8 = 0x04;
    /// `REPEAT_FLAG`, bit 3.
    pub const REPEAT_FLAG: u8 = 0x08;
    /// `X_IS_SAME_OR_POSITIVE_X_SHORT_VECTOR`, bit 4.
    pub const X_IS_SAME_OR_POSITIVE: u8 = 0x10;
    /// `Y_IS_SAME_OR_POSITIVE_Y_SHORT_VECTOR`, bit 5.
    pub const Y_IS_SAME_OR_POSITIVE: u8 = 0x20;
}

/// Component Glyph Flags (chapter `glyf`, "Component Glyph Flags").
pub mod component_flags {
    /// `ARG_1_AND_2_ARE_WORDS`, bit 0.
    pub const ARG_1_AND_2_ARE_WORDS: u16 = 0x0001;
    /// `ARGS_ARE_XY_VALUES`, bit 1.
    pub const ARGS_ARE_XY_VALUES: u16 = 0x0002;
    /// `ROUND_XY_TO_GRID`, bit 2 (grid-fitting; ignored: no hinting).
    pub const ROUND_XY_TO_GRID: u16 = 0x0004;
    /// `WE_HAVE_A_SCALE`, bit 3.
    pub const WE_HAVE_A_SCALE: u16 = 0x0008;
    /// `MORE_COMPONENTS`, bit 5.
    pub const MORE_COMPONENTS: u16 = 0x0020;
    /// `WE_HAVE_AN_X_AND_Y_SCALE`, bit 6.
    pub const WE_HAVE_AN_X_AND_Y_SCALE: u16 = 0x0040;
    /// `WE_HAVE_A_TWO_BY_TWO`, bit 7.
    pub const WE_HAVE_A_TWO_BY_TWO: u16 = 0x0080;
    /// `WE_HAVE_INSTRUCTIONS`, bit 8 (skipped: never interpreted).
    pub const WE_HAVE_INSTRUCTIONS: u16 = 0x0100;
    /// `USE_MY_METRICS`, bit 9.
    pub const USE_MY_METRICS: u16 = 0x0200;
    /// `SCALED_COMPONENT_OFFSET`, bit 11.
    pub const SCALED_COMPONENT_OFFSET: u16 = 0x0800;
    /// `UNSCALED_COMPONENT_OFFSET`, bit 12.
    pub const UNSCALED_COMPONENT_OFFSET: u16 = 0x1000;
}

use component_flags as cf;
use simple_flags as sf;

/// Size of the glyph header: `numberOfContours`, `xMin`, `yMin`, `xMax`,
/// `yMax` (int16 each).
const HEADER: usize = 10;

/// One point of a glyph, in font units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Point {
    /// x-coordinate.
    pub x: i32,
    /// y-coordinate.
    pub y: i32,
    /// `ON_CURVE_POINT`: "If set, the point is on the curve; otherwise, it
    /// is off the curve" (a quadratic control point).
    pub on_curve: bool,
}

/// A glyph's description, as `loca` locates it in `glyf`.
#[derive(Debug, Clone, Copy)]
pub enum Glyph<'a> {
    /// Equal `loca` offsets: no outline ("the first and second offsets
    /// should have the same value").
    Empty,
    /// `numberOfContours` ≥ 0.
    Simple(SimpleGlyph<'a>),
    /// `numberOfContours` < 0 ("A numberOfContours value of -1 is
    /// recommended to indicate a composite glyph"; any negative value is
    /// read as one).
    Composite(CompositeGlyph<'a>),
}

/// The `glyf` table.
#[derive(Debug, Clone, Copy)]
pub struct Glyf<'a> {
    data: &'a [u8],
}

impl<'a> Glyf<'a> {
    /// The table; its glyphs are checked when read.
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
    }

    /// Glyph `glyph`, located by `loca`: its range must lie in `glyf`.
    pub fn glyph(&self, loca: &Loca<'_>, glyph: u16) -> Result<Glyph<'a>, Error> {
        let (start, end) = loca.glyph_range(glyph)?;
        let len = end
            .checked_sub(start)
            .ok_or(Error::InvalidValue(Tag::LOCA))?;
        Glyph::parse(slice(self.data, start, len)?)
    }
}

impl<'a> Glyph<'a> {
    /// Parse one glyph's bytes: the header, then a simple or composite
    /// description.
    pub fn parse(data: &'a [u8]) -> Result<Self, Error> {
        if data.is_empty() {
            return Ok(Self::Empty);
        }
        let contours = i16_at(data, 0)?;
        let bbox = [
            i16_at(data, 2)?,
            i16_at(data, 4)?,
            i16_at(data, 6)?,
            i16_at(data, 8)?,
        ];
        match u16::try_from(contours) {
            Ok(n) => SimpleGlyph::parse(data, n, bbox).map(Self::Simple),
            Err(_) => Ok(Self::Composite(CompositeGlyph {
                bbox,
                data: tail(data, HEADER)?,
            })),
        }
    }
}

/// A simple glyph whose arrays have been checked to fit its bytes.
#[derive(Debug, Clone, Copy)]
pub struct SimpleGlyph<'a> {
    /// The glyph's bytes, header included.
    data: &'a [u8],
    /// `xMin`, `yMin`, `xMax`, `yMax`.
    pub bbox: [i16; 4],
    /// `numberOfContours`.
    num_contours: u16,
    /// "The number of points is determined by the last entry in the
    /// endPtsOfContours array" (0 if there are no contours).
    num_points: usize,
    /// Where `flags` starts.
    flags_at: usize,
    /// Where `xCoordinates` starts.
    x_at: usize,
    /// Where `yCoordinates` starts.
    y_at: usize,
}

/// Bytes a coordinate takes, for a flag's short-vector and same bits: one
/// if short, none if "the same as the previous", else two.
fn coordinate_size(flag: u8, short: u8, same: u8) -> usize {
    if flag & short != 0 {
        1
    } else if flag & same != 0 {
        0
    } else {
        2
    }
}

impl<'a> SimpleGlyph<'a> {
    /// "Simple Glyph Table": `endPtsOfContours[numberOfContours]`,
    /// `instructionLength`, `instructions` (skipped), then the packed
    /// `flags`, `xCoordinates` and `yCoordinates`, whose sizes "must be
    /// determined by parsing the flags array entries": this reads every
    /// flag once (with its repeats) to find where the coordinate arrays
    /// start and checks that both fit.
    ///
    /// `endPtsOfContours` must be "in increasing numeric order"; a pair that
    /// does not increase is refused, since it would make a contour with no
    /// points. A `REPEAT_FLAG` count that runs past the last point is refused
    /// too: the flags would describe points the glyph does not have.
    fn parse(data: &'a [u8], num_contours: u16, bbox: [i16; 4]) -> Result<Self, Error> {
        let ends_len = usize::from(num_contours)
            .checked_mul(2)
            .ok_or(Error::Overflow)?;
        let ends = slice(data, HEADER, ends_len)?;
        let mut previous: Option<u16> = None;
        let (pairs, _) = ends.as_chunks::<2>();
        for pair in pairs {
            let end = u16::from_be_bytes(*pair);
            if previous.is_some_and(|p| end <= p) {
                return Err(Error::InvalidValue(Tag::GLYF));
            }
            previous = Some(end);
        }
        let num_points = previous.map_or(0, |last| usize::from(last).saturating_add(1));
        let instructions_at = add(HEADER, ends_len)?;
        let instruction_length = u16_at(data, instructions_at)?;
        let flags_at = add(add(instructions_at, 2)?, usize::from(instruction_length))?;

        // Walk the flags: one flag byte (and a repeat count byte if
        // REPEAT_FLAG) covers 1 + count points.
        let mut at = flags_at;
        let mut points = 0usize;
        let mut x_len = 0usize;
        let mut y_len = 0usize;
        while points < num_points {
            let flag = u8_at(data, at)?;
            at = add(at, 1)?;
            let mut times = 1usize;
            if flag & sf::REPEAT_FLAG != 0 {
                times = add(times, usize::from(u8_at(data, at)?))?;
                at = add(at, 1)?;
            }
            points = add(points, times)?;
            if points > num_points {
                return Err(Error::InvalidValue(Tag::GLYF));
            }
            let x = coordinate_size(flag, sf::X_SHORT_VECTOR, sf::X_IS_SAME_OR_POSITIVE);
            let y = coordinate_size(flag, sf::Y_SHORT_VECTOR, sf::Y_IS_SAME_OR_POSITIVE);
            x_len = add(x_len, x.checked_mul(times).ok_or(Error::Overflow)?)?;
            y_len = add(y_len, y.checked_mul(times).ok_or(Error::Overflow)?)?;
        }
        let x_at = at;
        let y_at = add(x_at, x_len)?;
        if add(y_at, y_len)? > data.len() {
            return Err(Error::Truncated);
        }
        Ok(Self {
            data,
            bbox,
            num_contours,
            num_points,
            flags_at,
            x_at,
            y_at,
        })
    }

    /// `numberOfContours`.
    pub fn num_contours(&self) -> u16 {
        self.num_contours
    }

    /// The number of points.
    pub fn num_points(&self) -> usize {
        self.num_points
    }

    /// `endPtsOfContours[index]`: the point index of contour `index`'s last
    /// point.
    pub fn end_point(&self, index: u16) -> Result<u16, Error> {
        if index >= self.num_contours {
            return Err(Error::Truncated);
        }
        let at = add(
            HEADER,
            usize::from(index).checked_mul(2).ok_or(Error::Overflow)?,
        )?;
        u16_at(self.data, at)
    }

    /// The points, in order: "Coordinate for the first point is relative
    /// to (0,0); others are relative to previous point."
    pub fn points(&self) -> PointDecoder<'a> {
        PointDecoder {
            data: self.data,
            flags_at: self.flags_at,
            x_at: self.x_at,
            y_at: self.y_at,
            flag: 0,
            repeats: 0,
            x: 0,
            y: 0,
            left: self.num_points,
        }
    }
}

/// Decodes a simple glyph's points one at a time. Its fields are the whole
/// state, so one step ([`PointDecoder::step`]) can be checked on any state
/// (the Kani harness `glyf_point_step` does).
#[derive(Debug, Clone, Copy)]
pub struct PointDecoder<'a> {
    pub(crate) data: &'a [u8],
    /// Next flag byte.
    pub(crate) flags_at: usize,
    /// Next x-coordinate byte.
    pub(crate) x_at: usize,
    /// Next y-coordinate byte.
    pub(crate) y_at: usize,
    /// The current flag.
    pub(crate) flag: u8,
    /// How many more points reuse `flag` ("the number of additional times
    /// this flag byte is to be repeated").
    pub(crate) repeats: u8,
    /// The previous point's coordinates.
    pub(crate) x: i32,
    pub(crate) y: i32,
    /// Points still to decode.
    pub(crate) left: usize,
}

/// One coordinate delta: "If X_SHORT_VECTOR is set, this bit describes the
/// sign of the value, with 1 equalling positive and 0 negative. If
/// X_SHORT_VECTOR is not set and this bit is set, then the current
/// x-coordinate is the same as the previous x-coordinate. If X_SHORT_VECTOR
/// is not set and this bit is also not set, the current x-coordinate is a
/// signed 16-bit delta vector." (And the same for y.)
fn delta(data: &[u8], at: &mut usize, flag: u8, short: u8, same: u8) -> Result<i32, Error> {
    if flag & short != 0 {
        let b = i32::from(u8_at(data, *at)?);
        *at = add(*at, 1)?;
        Ok(if flag & same != 0 {
            b
        } else {
            b.wrapping_neg()
        })
    } else if flag & same != 0 {
        Ok(0)
    } else {
        let v = i32::from(i16_at(data, *at)?);
        *at = add(*at, 2)?;
        Ok(v)
    }
}

impl PointDecoder<'_> {
    /// Decode the next point, or `Ok(None)` after the last.
    pub fn step(&mut self) -> Result<Option<Point>, Error> {
        if self.left == 0 {
            return Ok(None);
        }
        if self.repeats > 0 {
            self.repeats = self.repeats.saturating_sub(1);
        } else {
            self.flag = u8_at(self.data, self.flags_at)?;
            self.flags_at = add(self.flags_at, 1)?;
            if self.flag & sf::REPEAT_FLAG != 0 {
                self.repeats = u8_at(self.data, self.flags_at)?;
                self.flags_at = add(self.flags_at, 1)?;
            }
        }
        let flag = self.flag;
        let dx = delta(
            self.data,
            &mut self.x_at,
            flag,
            sf::X_SHORT_VECTOR,
            sf::X_IS_SAME_OR_POSITIVE,
        )?;
        let dy = delta(
            self.data,
            &mut self.y_at,
            flag,
            sf::Y_SHORT_VECTOR,
            sf::Y_IS_SAME_OR_POSITIVE,
        )?;
        // At most 65,536 points of deltas in -32,768..=32,767 sum to a
        // value inside i32, so these never fail on a glyph `parse` accepted;
        // they are checked anyway.
        self.x = self.x.checked_add(dx).ok_or(Error::Overflow)?;
        self.y = self.y.checked_add(dy).ok_or(Error::Overflow)?;
        self.left = self.left.saturating_sub(1);
        Ok(Some(Point {
            x: self.x,
            y: self.y,
            on_curve: flag & sf::ON_CURVE_POINT != 0,
        }))
    }
}

impl Iterator for PointDecoder<'_> {
    type Item = Result<Point, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.step() {
            Ok(Some(p)) => Some(Ok(p)),
            Ok(None) => None,
            Err(e) => {
                self.left = 0;
                Some(Err(e))
            }
        }
    }
}

/// A composite glyph: its header and its component records.
#[derive(Debug, Clone, Copy)]
pub struct CompositeGlyph<'a> {
    /// `xMin`, `yMin`, `xMax`, `yMax`.
    pub bbox: [i16; 4],
    /// The bytes after the header: component records, then instructions.
    data: &'a [u8],
}

impl<'a> CompositeGlyph<'a> {
    /// The component records, read one at a time.
    pub fn components(&self) -> Components<'a> {
        Components {
            data: self.data,
            at: 0,
            done: false,
        }
    }
}

/// How a component is placed: "by specifying a vector offset … or by
/// specifying one control point from the child's outline that is aligned
/// with a specified control point in the parent".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Placement {
    /// `ARGS_ARE_XY_VALUES` set: `(argument1, argument2)` is "an offset
    /// vector (x, y)", signed.
    Offset(i32, i32),
    /// `ARGS_ARE_XY_VALUES` clear: "Argument1 is a point number in the
    /// parent glyph … and Argument2 is a point number … from the child",
    /// unsigned.
    Points(u16, u16),
}

/// A component's linear transformation, `F2DOT14` values (raw, 1.0 is
/// 16384). Apple's manual, "'glyf' table", Table 19a: `a` = `xscale`,
/// `b` = `scale01`, `c` = `scale10`, `d` = `yscale`, and a point (x, y) of
/// the component becomes (a·x + c·y, b·x + d·y) before it is offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Transform {
    /// `xscale` (`a`).
    pub xx: i16,
    /// `scale01` (`b`).
    pub yx: i16,
    /// `scale10` (`c`).
    pub xy: i16,
    /// `yscale` (`d`).
    pub yy: i16,
}

/// `F2DOT14` 1.0.
const ONE: i16 = 16_384;

impl Transform {
    /// "Otherwise, scale = 1.0."
    pub const IDENTITY: Self = Self {
        xx: ONE,
        yx: 0,
        xy: 0,
        yy: ONE,
    };

    /// Apply to (x, y), rounding each coordinate to the nearest font unit,
    /// half away from zero.
    pub fn apply(&self, x: i32, y: i32) -> Result<(i32, i32), Error> {
        let (x, y) = (i64::from(x), i64::from(y));
        let term = |s: i16, v: i64| i64::from(s).checked_mul(v).ok_or(Error::Overflow);
        let nx = term(self.xx, x)?
            .checked_add(term(self.xy, y)?)
            .ok_or(Error::Overflow)?;
        let ny = term(self.yx, x)?
            .checked_add(term(self.yy, y)?)
            .ok_or(Error::Overflow)?;
        Ok((round_f2dot14(nx)?, round_f2dot14(ny)?))
    }
}

/// `v / 16384`, rounded half away from zero, as an `i32`.
fn round_f2dot14(v: i64) -> Result<i32, Error> {
    let magnitude = v.unsigned_abs().checked_add(8_192).ok_or(Error::Overflow)? / 16_384;
    let magnitude = i64::try_from(magnitude).map_err(|_| Error::Overflow)?;
    let signed = if v < 0 {
        magnitude.wrapping_neg()
    } else {
        magnitude
    };
    i32::try_from(signed).map_err(|_| Error::Overflow)
}

/// One component record ("Component Glyph Table").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Component {
    /// `flags`.
    pub flags: u16,
    /// `glyphIndex`: "glyph index of component".
    pub glyph: u16,
    /// `argument1` and `argument2`.
    pub placement: Placement,
    /// The transformation option, or identity.
    pub transform: Transform,
}

impl Component {
    /// Whether the offset is transformed: "If the SCALED_COMPONENT_OFFSET
    /// flag is set, then the x and y offset values are deemed to be in the
    /// component glyph's coordinate system, and the scale transformation is
    /// applied to both values." Neither flag, or both ("invalid; the
    /// rasterizer should use its default behavior"), is the default, which
    /// "On Microsoft and Apple platforms … is the same as when the
    /// UNSCALED_COMPONENT_OFFSET flag is set".
    pub fn scaled_offset(&self) -> bool {
        self.flags & cf::SCALED_COMPONENT_OFFSET != 0
            && self.flags & cf::UNSCALED_COMPONENT_OFFSET == 0
    }
}

/// Reads component records one at a time, following the chapter's
/// pseudo-code: `flags`, `glyphIndex`, two arguments ("if ( flags &
/// ARG_1_AND_2_ARE_WORDS) { (int16 or FWORD) argument1; (int16 or FWORD)
/// argument2; } else { uint16 arg1and2; /* (arg1 << 8) | arg2 */ }"), then
/// one, two or four `F2DOT14` values, "while ( flags & MORE_COMPONENTS )".
/// The instructions that may follow are not read.
#[derive(Debug, Clone, Copy)]
pub struct Components<'a> {
    pub(crate) data: &'a [u8],
    pub(crate) at: usize,
    pub(crate) done: bool,
}

impl Components<'_> {
    /// Read the next component, or `Ok(None)` after the one without
    /// `MORE_COMPONENTS`.
    pub fn step(&mut self) -> Result<Option<Component>, Error> {
        if self.done {
            return Ok(None);
        }
        let d = self.data;
        let mut at = self.at;
        let flags = u16_at(d, at)?;
        let glyph = u16_at(d, add(at, 2)?)?;
        at = add(at, 4)?;
        let words = flags & cf::ARG_1_AND_2_ARE_WORDS != 0;
        let xy = flags & cf::ARGS_ARE_XY_VALUES != 0;
        let placement = match (words, xy) {
            (true, true) => Placement::Offset(
                i32::from(i16_at(d, at)?),
                i32::from(i16_at(d, add(at, 2)?)?),
            ),
            (true, false) => Placement::Points(u16_at(d, at)?, u16_at(d, add(at, 2)?)?),
            (false, true) => {
                Placement::Offset(i32::from(i8_at(d, at)?), i32::from(i8_at(d, add(at, 1)?)?))
            }
            (false, false) => {
                Placement::Points(u16::from(u8_at(d, at)?), u16::from(u8_at(d, add(at, 1)?)?))
            }
        };
        at = add(at, if words { 4 } else { 2 })?;
        // "The WE_HAVE_A_SCALE, WE_HAVE_AN_X_AND_Y_SCALE and
        // WE_HAVE_A_TWO_BY_TWO flags are mutually exclusive"; when several
        // are set we follow the pseudo-code's `if … else if` order.
        let transform = if flags & cf::WE_HAVE_A_SCALE != 0 {
            let s = i16_at(d, at)?;
            at = add(at, 2)?;
            Transform {
                xx: s,
                yx: 0,
                xy: 0,
                yy: s,
            }
        } else if flags & cf::WE_HAVE_AN_X_AND_Y_SCALE != 0 {
            let t = Transform {
                xx: i16_at(d, at)?,
                yx: 0,
                xy: 0,
                yy: i16_at(d, add(at, 2)?)?,
            };
            at = add(at, 4)?;
            t
        } else if flags & cf::WE_HAVE_A_TWO_BY_TWO != 0 {
            let t = Transform {
                xx: i16_at(d, at)?,
                yx: i16_at(d, add(at, 2)?)?,
                xy: i16_at(d, add(at, 4)?)?,
                yy: i16_at(d, add(at, 6)?)?,
            };
            at = add(at, 8)?;
            t
        } else {
            Transform::IDENTITY
        };
        self.at = at;
        self.done = flags & cf::MORE_COMPONENTS == 0;
        Ok(Some(Component {
            flags,
            glyph,
            placement,
            transform,
        }))
    }
}

impl Iterator for Components<'_> {
    type Item = Result<Component, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.step() {
            Ok(Some(c)) => Some(Ok(c)),
            Ok(None) => None,
            Err(e) => {
                self.done = true;
                Some(Err(e))
            }
        }
    }
}

/// A glyph flattened to quadratic contours: every component's points,
/// transformed and placed, renumbered "to follow sequentially after all
/// points previously incorporated into the parent".
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Outline {
    /// All points, contour after contour.
    pub points: Vec<Point>,
    /// Where each contour ends in `points` (exclusive), in order.
    pub contour_ends: Vec<usize>,
}

/// The bounds of a flattening. [`outline`] uses [`Limits::STATED`]; a
/// Kani harness can run the same code with smaller ones (none does yet:
/// see `src/proofs.rs`).
#[derive(Debug, Clone, Copy)]
pub(crate) struct Limits {
    pub(crate) depth: u8,
    pub(crate) components: usize,
    pub(crate) points: usize,
}

impl Limits {
    /// [`MAX_COMPONENT_DEPTH`], [`MAX_COMPONENTS`], [`MAX_POINTS`].
    pub(crate) const STATED: Self = Self {
        depth: MAX_COMPONENT_DEPTH,
        components: MAX_COMPONENTS,
        points: MAX_POINTS,
    };
}

/// What a flattening has used so far of its bounds.
struct Budget {
    limits: Limits,
    components: usize,
}

/// Flatten glyph `glyph` into an [`Outline`].
pub fn outline(glyf: &Glyf<'_>, loca: &Loca<'_>, glyph: u16) -> Result<Outline, Error> {
    outline_within(glyf, loca, glyph, Limits::STATED)
}

/// [`outline`] with the given bounds.
pub(crate) fn outline_within(
    glyf: &Glyf<'_>,
    loca: &Loca<'_>,
    glyph: u16,
    limits: Limits,
) -> Result<Outline, Error> {
    let mut out = Outline::default();
    let mut budget = Budget {
        limits,
        components: 0,
    };
    append(glyf, loca, glyph, 0, &mut budget, &mut out)?;
    Ok(out)
}

/// Append glyph `glyph`, at nesting depth `depth`, to `out`.
fn append(
    glyf: &Glyf<'_>,
    loca: &Loca<'_>,
    glyph: u16,
    depth: u8,
    budget: &mut Budget,
    out: &mut Outline,
) -> Result<(), Error> {
    match glyf.glyph(loca, glyph)? {
        Glyph::Empty => Ok(()),
        Glyph::Simple(s) => {
            let base = out.points.len();
            if add(base, s.num_points())? > budget.limits.points {
                return Err(Error::PointCount);
            }
            for p in s.points() {
                out.points.push(p?);
            }
            for i in 0..s.num_contours() {
                let end = add(add(base, usize::from(s.end_point(i)?))?, 1)?;
                out.contour_ends.push(end);
            }
            Ok(())
        }
        Glyph::Composite(c) => {
            let depth = depth.checked_add(1).ok_or(Error::ComponentDepth)?;
            if depth > budget.limits.depth {
                return Err(Error::ComponentDepth);
            }
            for component in c.components() {
                let component = component?;
                budget.components = add(budget.components, 1)?;
                if budget.components > budget.limits.components {
                    return Err(Error::ComponentCount);
                }
                let base = out.points.len();
                append(glyf, loca, component.glyph, depth, budget, out)?;
                place(&component, base, out)?;
            }
            Ok(())
        }
    }
}

/// Transform and offset the points from `base` on, which are the child
/// `component` just appended.
fn place(component: &Component, base: usize, out: &mut Outline) -> Result<(), Error> {
    let t = component.transform;
    let child = out.points.get_mut(base..).ok_or(Error::Truncated)?;
    if t != Transform::IDENTITY {
        for p in child.iter_mut() {
            (p.x, p.y) = t.apply(p.x, p.y)?;
        }
    }
    let (dx, dy) = match component.placement {
        Placement::Offset(x, y) if component.scaled_offset() => t.apply(x, y)?,
        Placement::Offset(x, y) => (x, y),
        // "the transformation is applied to the child's point before the
        // points are aligned": the child's points are already transformed.
        Placement::Points(parent, child_point) => {
            let p = out
                .points
                .get(..base)
                .and_then(|ps| ps.get(usize::from(parent)))
                .ok_or(Error::AnchorPoint)?;
            let c = out
                .points
                .get(base..)
                .and_then(|ps| ps.get(usize::from(child_point)))
                .ok_or(Error::AnchorPoint)?;
            (
                p.x.checked_sub(c.x).ok_or(Error::Overflow)?,
                p.y.checked_sub(c.y).ok_or(Error::Overflow)?,
            )
        }
    };
    if (dx, dy) != (0, 0) {
        for p in out.points.get_mut(base..).ok_or(Error::Truncated)? {
            p.x = p.x.checked_add(dx).ok_or(Error::Overflow)?;
            p.y = p.y.checked_add(dy).ok_or(Error::Overflow)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::head::LocaFormat;

    /// A simple glyph from the chapter's encoding rules: one contour of
    /// four points, flags with a repeat, short positive and negative
    /// vectors, a "same" coordinate and a 16-bit delta.
    fn square() -> Vec<u8> {
        let mut g = vec![0, 1, 0, 0, 0, 0, 0, 0, 0, 0];
        g.extend_from_slice(&[0, 3]); // endPtsOfContours: [3]
        g.extend_from_slice(&[0, 1, 0xAA]); // one byte of instructions, skipped
        // Point 0: on, x short positive (10), y 16-bit (0).
        // Points 1, 2: on, x same, y short positive (20), by REPEAT_FLAG 1.
        // Point 3: off, x short negative (-10), y same.
        g.extend_from_slice(&[0x13, 0x3D, 1, 0x22]);
        g.extend_from_slice(&[10, 10]); // x: +10, then point 3's -10
        g.extend_from_slice(&[0, 0, 20, 20]); // y: 0 (int16), +20, +20
        g
    }

    #[test]
    fn simple_glyph_flags_and_vectors() -> Result<(), Error> {
        let g = square();
        let Glyph::Simple(s) = Glyph::parse(&g)? else {
            return Err(Error::Truncated);
        };
        assert_eq!(
            (s.num_contours(), s.num_points(), s.end_point(0)?),
            (1, 4, 3)
        );
        let points: Vec<Point> = s.points().collect::<Result<_, _>>()?;
        let expect = [
            (10, 0, true),
            (10, 20, true),
            (10, 40, true),
            (0, 40, false),
        ];
        for (p, (x, y, on)) in points.iter().zip(expect) {
            assert_eq!((p.x, p.y, p.on_curve), (x, y, on));
        }
        assert_eq!(points.len(), 4);
        // A repeat that runs past the last point is refused.
        let mut bad = g.clone();
        if let Some(b) = bad.get_mut(17) {
            *b = 5;
        }
        assert_eq!(
            Glyph::parse(&bad).err(),
            Some(Error::InvalidValue(Tag::GLYF))
        );
        // Coordinates past the end of the glyph are refused.
        bad = g;
        bad.pop();
        assert_eq!(Glyph::parse(&bad).err(), Some(Error::Truncated));
        Ok(())
    }

    /// `glyf` with glyph 0 the square and glyph 1 a composite of it twice:
    /// once scaled by 0.5 and offset (scaled offset), once placed by
    /// matching its point 0 to the first copy's point 2.
    fn composite_font() -> (Vec<u8>, Vec<u8>) {
        let mut glyf = square();
        // Short `loca` offsets are halved, so glyphs start at even offsets
        // ("the local offsets should be word aligned").
        glyf.push(0);
        let start = u16::try_from(glyf.len()).unwrap_or(0);
        glyf.extend_from_slice(&[0xFF, 0xFF, 0, 0, 0, 0, 0, 0, 0, 0]);
        // ARGS_ARE_XY_VALUES | WE_HAVE_A_SCALE | MORE_COMPONENTS |
        // SCALED_COMPONENT_OFFSET; glyph 0; offset (100, -4); scale 0.5.
        glyf.extend_from_slice(&[0x08, 0x2A, 0, 0, 100, 0xFC, 0x20, 0x00]);
        // Point matching (no ARGS_ARE_XY_VALUES): parent point 2, child 0.
        glyf.extend_from_slice(&[0x00, 0x00, 0, 0, 2, 0]);
        let end = u16::try_from(glyf.len()).unwrap_or(0);
        let loca = [0, start / 2, end / 2]
            .iter()
            .flat_map(|v: &u16| v.to_be_bytes())
            .collect();
        (glyf, loca)
    }

    #[test]
    fn composite_scale_offset_and_point_matching() -> Result<(), Error> {
        let (glyf_bytes, loca_bytes) = composite_font();
        let loca = Loca::parse(&loca_bytes, LocaFormat::Short, 2)?;
        let glyf = Glyf::new(&glyf_bytes);
        let o = outline(&glyf, &loca, 1)?;
        let xy: Vec<(i32, i32)> = o.points.iter().map(|p| (p.x, p.y)).collect();
        // First copy: (x, y) / 2 + (100, -4) / 2.
        // Second copy: unscaled, moved so its point 0 (10, 0) lands on the
        // first copy's point 2 (55, 18).
        assert_eq!(
            xy,
            [
                (55, -2),
                (55, 8),
                (55, 18),
                (50, 18),
                (55, 18),
                (55, 38),
                (55, 58),
                (45, 58)
            ]
        );
        assert_eq!(o.contour_ends, [4, 8]);
        Ok(())
    }

    #[test]
    fn cycles_end_at_the_depth_bound() -> Result<(), Error> {
        // Glyph 0 is a composite of itself.
        let mut glyf_bytes = vec![0xFF, 0xFF, 0, 0, 0, 0, 0, 0, 0, 0];
        glyf_bytes.extend_from_slice(&[0x00, 0x02, 0, 0, 0, 0]);
        let loca_bytes = [0, 0, 0, 8];
        let loca = Loca::parse(&loca_bytes, LocaFormat::Short, 1)?;
        let glyf = Glyf::new(&glyf_bytes);
        assert_eq!(outline(&glyf, &loca, 0).err(), Some(Error::ComponentDepth));
        Ok(())
    }

    #[test]
    fn transform_rounds_half_away_from_zero() -> Result<(), Error> {
        let half = Transform {
            xx: 8192,
            yx: 0,
            xy: 0,
            yy: 8192,
        };
        assert_eq!(half.apply(3, -3)?, (2, -2));
        assert_eq!(half.apply(1, -1)?, (1, -1));
        assert_eq!(
            Transform::IDENTITY.apply(i32::MAX, i32::MIN)?,
            (i32::MAX, i32::MIN)
        );
        // Two of 2.0 overflow i32.
        let two = Transform {
            xx: i16::MIN,
            yx: 0,
            xy: i16::MIN,
            yy: 0,
        };
        assert_eq!(two.apply(i32::MIN, i32::MIN).err(), Some(Error::Overflow));
        Ok(())
    }
}

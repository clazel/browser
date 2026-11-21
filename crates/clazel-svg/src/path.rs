//! Path data (SVG 2 section 9.3) for the commands in scope, turned into the
//! edges of a polygon in device space.
//!
//! In scope: `M`/`m` (9.3.3), `Z`/`z` (9.3.4), `L`/`l`, `H`/`h`, `V`/`v`
//! (9.3.5), with the grammar of 9.3.9. Any other command letter (the curves
//! 9.3.6 to 9.3.8) is [`Error::Unsupported`]; data that does not match the
//! grammar is [`Error::Malformed`]. Section 9.5.4 says to render a path up
//! to its first error: this decoder refuses the whole image instead (listed
//! choice 6 in `lib.rs`).
//!
//! The polygon is the path's subpaths, each implicitly closed for filling
//! (section 13.4: a fill closes open subpaths), as a list of [`Edge`]s.

use crate::limits::{MAX_EDGES, MAX_NUMBER};
use crate::map::Map;
use crate::num::{number, starts_number};
use clazel_image_shape::Error;

/// A line segment in device space (1/256 pixel).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct Edge {
    pub x0: i32,
    pub y0: i32,
    pub x1: i32,
    pub y1: i32,
}

/// The edges of one path.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Edges {
    list: [Edge; MAX_EDGES],
    len: usize,
}

impl Edges {
    pub(crate) fn new() -> Edges {
        Edges {
            list: [Edge::default(); MAX_EDGES],
            len: 0,
        }
    }

    pub(crate) fn clear(&mut self) {
        self.len = 0;
    }

    /// The edges so far.
    pub(crate) fn as_slice(&self) -> &[Edge] {
        self.list.get(..self.len).unwrap_or(&[])
    }

    fn push(&mut self, e: Edge) -> Result<(), Error> {
        let slot = self
            .list
            .get_mut(self.len)
            .ok_or(Error::Unsupported("too many path segments"))?;
        *slot = e;
        self.len = self.len.saturating_add(1);
        Ok(())
    }
}

/// The pen: current point and the initial point of the subpath, both in
/// user space (fixed point).
struct Pen<'a> {
    map: &'a Map,
    edges: &'a mut Edges,
    start: (i64, i64),
    cur: (i64, i64),
}

fn out_of_range() -> Error {
    Error::Unsupported("a coordinate out of range")
}

impl Pen<'_> {
    /// An edge from `cur` to `to`; the pen moves to `to`. Zero-length
    /// edges are not stored (they cover nothing).
    fn line_to(&mut self, to: (i64, i64)) -> Result<(), Error> {
        let (x0, y0) = self.map.apply(self.cur.0, self.cur.1)?;
        let (x1, y1) = self.map.apply(to.0, to.1)?;
        if (x0, y0) != (x1, y1) {
            self.edges.push(Edge { x0, y0, x1, y1 })?;
        }
        self.cur = to;
        Ok(())
    }

    /// Section 9.3.4: "An automatic straight line is drawn from the current
    /// point to the initial point of the current subpath."
    fn close(&mut self) -> Result<(), Error> {
        self.line_to(self.start)
    }

    /// A point `(x, y)` away from the pen if `relative`, else absolute;
    /// within 2^20 in user space.
    fn target(&self, relative: bool, x: i64, y: i64) -> Result<(i64, i64), Error> {
        let (bx, by) = if relative { self.cur } else { (0, 0) };
        let nx = bx.checked_add(x).ok_or_else(out_of_range)?;
        let ny = by.checked_add(y).ok_or_else(out_of_range)?;
        if nx.unsigned_abs() > MAX_NUMBER.unsigned_abs()
            || ny.unsigned_abs() > MAX_NUMBER.unsigned_abs()
        {
            return Err(out_of_range());
        }
        Ok((nx, ny))
    }
}

pub(crate) fn is_wsp(b: Option<&u8>) -> bool {
    matches!(b, Some(0x09 | 0x20 | 0x0A | 0x0C | 0x0D))
}

pub(crate) fn skip_wsp(d: &[u8], mut p: usize) -> usize {
    while is_wsp(d.get(p)) {
        p = p.saturating_add(1);
    }
    p
}

/// A number that must be there.
fn need(d: &[u8], p: usize, what: &'static str) -> Result<(i64, usize), Error> {
    number(d, p)?.ok_or(Error::Malformed(what))
}

/// `comma_wsp?` then whether a number follows: `Some(position of it)`, or
/// `None` with the sequence over (a comma with no number after it is
/// malformed: 9.3.9's `comma_wsp?` sits only between two items).
fn next_item(d: &[u8], p: usize) -> Result<Option<usize>, Error> {
    let mut q = skip_wsp(d, p);
    let mut comma = false;
    if d.get(q) == Some(&b',') {
        comma = true;
        q = skip_wsp(d, q.saturating_add(1));
    }
    if starts_number(d.get(q)) {
        Ok(Some(q))
    } else if comma {
        Err(Error::Malformed("a comma with no number after it"))
    } else {
        Ok(None)
    }
}

/// `coordinate comma_wsp? coordinate`, from `p`.
fn pair(d: &[u8], p: usize) -> Result<((i64, i64), usize), Error> {
    let (x, q) = need(d, p, "a coordinate was expected")?;
    let q = next_item(d, q)?.ok_or(Error::Malformed("a pair with one coordinate"))?;
    let (y, q) = need(d, q, "a coordinate was expected")?;
    Ok(((x, y), q))
}

/// Reads path data `d` into `edges` through `map`.
///
/// SVG 2 section 9.3.9, `svg_path::= wsp* (moveto (wsp* drawto_command)*)?
/// wsp*`: empty data is an empty path (it "disables rendering"); otherwise
/// the first command is a moveto (9.3.3: "A path data segment (if there is
/// one) must begin with a "moveto" command"); a relative `m` first is read
/// as absolute because the pen starts at (0, 0).
pub(crate) fn parse(d: &[u8], map: &Map, edges: &mut Edges) -> Result<(), Error> {
    edges.clear();
    let mut pen = Pen {
        map,
        edges,
        start: (0, 0),
        cur: (0, 0),
    };
    let mut p = skip_wsp(d, 0);
    let mut first = true;
    while let Some(&cmd) = d.get(p) {
        p = p.saturating_add(1);
        let relative = cmd.is_ascii_lowercase();
        match cmd {
            b'M' | b'm' => {
                // 9.3.3: the pairs after the first are implicit linetos,
                // relative if the moveto is.
                p = skip_wsp(d, p);
                let ((x, y), q) = pair(d, p)?;
                // The moveto ends the subpath before it (closed for fill).
                pen.close()?;
                let to = pen.target(relative && !first, x, y)?;
                pen.start = to;
                pen.cur = to;
                p = q;
                while let Some(q) = next_item(d, p)? {
                    let ((x, y), q) = pair(d, q)?;
                    let to = pen.target(relative, x, y)?;
                    pen.line_to(to)?;
                    p = q;
                }
            }
            _ if first => return Err(Error::Malformed("path data must begin with a moveto")),
            b'Z' | b'z' => pen.close()?,
            b'L' | b'l' => {
                p = skip_wsp(d, p);
                let mut at = Some(p);
                while let Some(q) = at {
                    let ((x, y), q) = pair(d, q)?;
                    let to = pen.target(relative, x, y)?;
                    pen.line_to(to)?;
                    p = q;
                    at = next_item(d, p)?;
                }
            }
            b'H' | b'h' | b'V' | b'v' => {
                // 9.3.5: equivalent to `L` with 0 for the other coordinate.
                let horizontal = cmd == b'H' || cmd == b'h';
                p = skip_wsp(d, p);
                let mut at = Some(p);
                while let Some(q) = at {
                    let (v, q) = need(d, q, "a coordinate was expected")?;
                    let to = if relative {
                        let (x, y) = if horizontal { (v, 0) } else { (0, v) };
                        pen.target(true, x, y)?
                    } else if horizontal {
                        pen.target(false, v, pen.cur.1)?
                    } else {
                        pen.target(false, pen.cur.0, v)?
                    };
                    pen.line_to(to)?;
                    p = q;
                    at = next_item(d, p)?;
                }
            }
            b'C' | b'c' | b'S' | b's' | b'Q' | b'q' | b'T' | b't' | b'A' | b'a' => {
                return Err(Error::Unsupported("a curve or arc path command"));
            }
            _ => return Err(Error::Malformed("an unknown path command")),
        }
        first = false;
        p = skip_wsp(d, p);
    }
    // The last subpath is closed for filling.
    pen.close()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::limits::ONE;
    use crate::map::ViewBox;

    /// Identity at 1 unit = 1 pixel on a 100 by 100 viewport.
    fn map() -> Result<Map, Error> {
        Map::new(
            ViewBox {
                x: 0,
                y: 0,
                w: 100 * ONE,
                h: 100 * ONE,
            },
            100,
            100,
        )
    }

    /// The edges as pixel-unit tuples.
    fn run(d: &str) -> Result<Vec<(i32, i32, i32, i32)>, Error> {
        let mut e = Edges::new();
        parse(d.as_bytes(), &map()?, &mut e)?;
        Ok(e.as_slice()
            .iter()
            .map(|e| (e.x0 / 256, e.y0 / 256, e.x1 / 256, e.y1 / 256))
            .collect())
    }

    #[test]
    fn triangle_of_hn() -> Result<(), Error> {
        assert_eq!(
            run("m2 27 14-29 14 29z")?,
            vec![(2, 27, 16, -2), (16, -2, 30, 27), (30, 27, 2, 27)]
        );
        Ok(())
    }

    #[test]
    fn square_with_relative_and_axis_commands() -> Result<(), Error> {
        let sq = vec![
            (4, 4, 10, 4),
            (10, 4, 10, 10),
            (10, 10, 4, 10),
            (4, 10, 4, 4),
        ];
        assert_eq!(run("m4 4h6v6h-6z")?, sq);
        assert_eq!(run("M4,4 H10 V10 H4 Z")?, sq);
        // Without the Z the closing edge is added all the same.
        assert_eq!(run("M4 4 L10 4 10 10 4 10")?, sq);
        // The implicit lineto after a relative moveto is relative.
        assert_eq!(run("m4 4 6 0 0 6 -6 0")?, sq);
        // A relative moveto first is absolute.
        assert_eq!(run("m 4 4 h6")?.len(), 2);
        Ok(())
    }

    #[test]
    fn subpaths_and_the_point_after_z() -> Result<(), Error> {
        // After a Z the next subpath starts at the same initial point.
        let e = run("M10 10 h10 v10 z h-5 v-5")?;
        assert_eq!(e.first(), Some(&(10, 10, 20, 10)));
        assert!(e.contains(&(10, 10, 5, 10)));
        Ok(())
    }

    #[test]
    fn empty_and_blank_data_is_an_empty_path() -> Result<(), Error> {
        assert_eq!(run("")?, vec![]);
        assert_eq!(run(" \t\n")?, vec![]);
        Ok(())
    }

    #[test]
    fn refusals() {
        for (d, unsup) in [
            ("L 1 2", false),
            ("M", false),
            ("M 1", false),
            ("M 1 2 3", false),
            ("M 1,2,", false),
            ("M 1 2 z 3", false),
            ("M 1 2 L", false),
            ("M 1 2 H", false),
            ("M 1 2 x", false),
            ("M 1 2 L 3, , 4", false),
            ("M 1. 2", false),
            ("M 1 2 C 1 2 3 4 5 6", true),
            ("M 1 2 c 1 2 3 4 5 6", true),
            ("M 1 2 S 1 2 3 4", true),
            ("M 1 2 Q 1 2 3 4", true),
            ("M 1 2 T 1 2", true),
            ("M 1 2 A 1 1 0 0 0 2 2", true),
            ("M 1e2 3", true),
            ("M 2000000 3", true),
        ] {
            let got = match run(d) {
                Err(Error::Unsupported(_)) => "unsupported",
                Err(Error::Malformed(_)) => "malformed",
                _ => "accepted",
            };
            assert_eq!(got, if unsup { "unsupported" } else { "malformed" }, "{d}");
        }
    }

    #[test]
    fn too_many_segments() {
        let mut d = String::from("M 0 0");
        for i in 0..=MAX_EDGES {
            d.push_str(&format!(" L {} {}", i % 90 + 1, (i * 7) % 90 + 1));
        }
        assert_eq!(run(&d), Err(Error::Unsupported("too many path segments")));
    }
}

//! The document: which elements and attributes are read, what each means,
//! and the two passes over it.
//!
//! The document is read **twice**. The first pass (`Pass::Validate`) builds
//! every path's edges and checks every attribute and every number, draws
//! nothing, and so decides whether the whole document is in scope. Only if
//! it is does the second pass (`Pass::Draw`) run, the same code with the
//! rasterizer switched on. That is how "anything else makes the image a
//! broken image, never a partial draw" holds: a document with a bad
//! last path never has its first path drawn.
//!
//! The grammar read (everything else is refused):
//!
//! ```text
//! document := BOM? XMLDecl? (comment | S)* svg
//! svg      := '<svg' attrs ('/>' | '>' (comment | S | path)* '</svg' S? '>')
//! path     := '<path' attrs ('/>' | '>' (comment | S)* '</path' S? '>')
//! ```
//!
//! `svg` attributes: `xmlns` (exactly the SVG namespace), `width`,
//! `height` (whole numbers of pixels, both required), `viewBox`. `path`
//! attributes: `d`, `fill`.

use crate::limits::ONE;
use crate::map::{Map, ViewBox};
use crate::num::number;
use crate::paint;
use crate::path::{self, Edges, skip_wsp};
use crate::raster;
use crate::xml::{Item, Read, Reader, Stop, Tag, malformed, unsupported};
use clazel_image_shape::{Error, MAX_SIDE, SizeError};

/// SVG 2 section 5.1.2: the namespace of SVG elements.
const SVG_NAMESPACE: &[u8] = b"http://www.w3.org/2000/svg";

/// What the `svg` element says.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Root {
    /// The `width` attribute: the intrinsic width in pixels (section 8.12).
    pub width: u32,
    /// The `height` attribute.
    pub height: u32,
    /// The `viewBox`, or `0 0 width height` without one.
    pub view_box: ViewBox,
}

/// `width` or `height`: ASCII digits only (no unit, no fraction: listed
/// choice 4), from 1 to `MAX_SIDE`.
pub(crate) fn dimension(value: &[u8], too_big: SizeError) -> Result<u32, Error> {
    if value.is_empty() || !value.iter().all(u8::is_ascii_digit) {
        return Err(Error::Unsupported(
            "a width or height that is not a whole number of pixels",
        ));
    }
    let mut n: u32 = 0;
    for &b in value {
        n = n
            .checked_mul(10)
            .and_then(|v| v.checked_add(u32::from(b.wrapping_sub(b'0'))))
            .ok_or(Error::Size(too_big))?;
        if n > MAX_SIDE {
            return Err(Error::Size(too_big));
        }
    }
    if n == 0 {
        return Err(Error::Size(SizeError::Empty));
    }
    Ok(n)
}

/// SVG 2 section 8.6: `[<min-x>,? <min-y>,? <width>,? <height>]`, "separated
/// by whitespace and/or a comma". A width or height that is not positive
/// is refused (the standard treats a negative one as absent and a zero
/// one as disabling rendering: listed choice 6).
pub(crate) fn view_box(value: &[u8]) -> Result<ViewBox, Error> {
    let mut v = [0i64; 4];
    let mut p = skip_wsp(value, 0);
    for (i, slot) in v.iter_mut().enumerate() {
        let (n, q) = number(value, p)?.ok_or(Error::Malformed("a viewBox needs four numbers"))?;
        *slot = n;
        p = q;
        if i < 3 {
            let mut r = skip_wsp(value, p);
            let spaced = r != p;
            let comma = value.get(r) == Some(&b',');
            if comma {
                r = skip_wsp(value, r.saturating_add(1));
            }
            if !spaced && !comma {
                return Err(Error::Malformed("viewBox numbers need a separator"));
            }
            p = r;
        }
    }
    if skip_wsp(value, p) != value.len() {
        return Err(Error::Malformed("a viewBox with more than four numbers"));
    }
    let [x, y, w, h] = v;
    if w <= 0 || h <= 0 {
        return Err(Error::Unsupported("a viewBox with no area"));
    }
    Ok(ViewBox { x, y, w, h })
}

/// The `svg` element's attributes.
fn root_attrs(tag: &Tag<'_>) -> Result<Root, Error> {
    let mut namespace = false;
    let (mut width, mut height, mut vb) = (None, None, None);
    for a in tag.attrs() {
        match a.name {
            b"xmlns" => {
                if a.value != SVG_NAMESPACE {
                    return Err(Error::Unsupported("a namespace that is not SVG's"));
                }
                namespace = true;
            }
            b"width" => width = Some(dimension(a.value, SizeError::TooWide)?),
            b"height" => height = Some(dimension(a.value, SizeError::TooTall)?),
            b"viewBox" => vb = Some(view_box(a.value)?),
            _ => return Err(Error::Unsupported("an attribute of svg that is not read")),
        }
    }
    if !namespace {
        return Err(Error::Malformed("svg without the xmlns attribute"));
    }
    let (Some(width), Some(height)) = (width, height) else {
        return Err(Error::Unsupported("svg without both width and height"));
    };
    let view_box = vb.unwrap_or(ViewBox {
        x: 0,
        y: 0,
        w: i64::from(width).saturating_mul(ONE),
        h: i64::from(height).saturating_mul(ONE),
    });
    Ok(Root {
        width,
        height,
        view_box,
    })
}

/// The prolog and the root's start tag: the root, and whether the tag
/// ended with `/>`. This is all `decode_config` reads.
pub(crate) fn read_root(rd: &mut Reader<'_>) -> Read<(Root, bool)> {
    rd.prolog()?;
    match rd.next_markup(true)? {
        Item::Start(tag) if tag.name == b"svg" => Ok((root_attrs(&tag)?, tag.empty)),
        Item::Start(_) => unsupported("a root element other than svg"),
        Item::End(_) => malformed("an end tag before the root"),
    }
}

/// Which pass.
pub(crate) enum Pass<'a> {
    /// Check everything, draw nothing.
    Validate,
    /// Draw into `pixels`, with `acc` as the rasterizer's scratch.
    Draw {
        pixels: &'a mut [u8],
        acc: &'a mut [u8],
    },
}

/// What a pass found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Scan {
    /// The document is valid so far and has not ended.
    Incomplete,
    /// The root element ended after this many bytes.
    Complete(usize),
}

/// A `path` element: `d` and `fill`, then (in the drawing pass) the fill.
fn path_element(
    tag: &Tag<'_>,
    map: &Map,
    size: (u32, u32),
    edges: &mut Edges,
    pass: &mut Pass<'_>,
) -> Result<(), Error> {
    let mut d: Option<&[u8]> = None;
    let mut rgb = paint::BLACK;
    for a in tag.attrs() {
        match a.name {
            b"d" => d = Some(a.value),
            b"fill" => rgb = paint::fill(a.value)?,
            _ => return Err(Error::Unsupported("an attribute of path that is not read")),
        }
    }
    // Section 9.3.2: `d` initially `none`: nothing to draw.
    match d {
        Some(d) => path::parse(d, map, edges)?,
        None => edges.clear(),
    }
    if let Pass::Draw { pixels, acc } = pass {
        raster::fill(edges.as_slice(), size.0, size.1, rgb, pixels, acc)?;
    }
    Ok(())
}

fn walk(doc: &[u8], size: (u32, u32), pass: &mut Pass<'_>) -> Read<usize> {
    let mut rd = Reader::new(doc);
    let (root, empty) = read_root(&mut rd)?;
    let map = Map::new(root.view_box, size.0, size.1)?;
    if let Pass::Draw { pixels, .. } = pass {
        pixels.fill(0);
    }
    if empty {
        return Ok(rd.pos());
    }
    let mut edges = Edges::new();
    loop {
        match rd.next_markup(false)? {
            Item::End(b"svg") => return Ok(rd.pos()),
            Item::End(_) => return malformed("an end tag that does not match"),
            Item::Start(tag) => {
                if tag.name != b"path" {
                    return unsupported("an element other than svg and path");
                }
                path_element(&tag, &map, size, &mut edges, pass)?;
                if !tag.empty {
                    match rd.next_markup(false)? {
                        Item::End(b"path") => {}
                        Item::End(_) => return malformed("an end tag that does not match"),
                        Item::Start(_) => return unsupported("an element inside path"),
                    }
                }
            }
        }
    }
}

/// One pass over `doc` (all the bytes held so far), for an image drawn at
/// `size` pixels.
pub(crate) fn run(doc: &[u8], size: (u32, u32), pass: &mut Pass<'_>) -> Result<Scan, Error> {
    match walk(doc, size, pass) {
        Ok(end) => Ok(Scan::Complete(end)),
        Err(Stop::Eof) => Ok(Scan::Incomplete),
        Err(Stop::Fail(e)) => Err(e),
    }
}

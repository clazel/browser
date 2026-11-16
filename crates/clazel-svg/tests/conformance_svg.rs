//! `clazel-svg` against Hacker News's two real files, a reference rasterizer
//! and a corpus of refusals (phase-6.md item 6.11a).
//!
//! 1. **HN's files** (`tests/fixtures/hn`, see its `SOURCE.md`), through the
//!    `Decoder` interface at the sizes HN draws them (`y18.svg` at 18 by 18,
//!    the intrinsic size; `triangle.svg` at 10 by 5, the `background-size:
//!    10px` of `site.css`, and at its intrinsic 32 by 16) and at others, with
//!    hand-checked pixels.
//! 2. **A reference rasterizer**: tiny-skia 0.12.0 (the rasterizer of resvg,
//!    written by others), drawing the same two paths. The path data is read
//!    here by a second, float-based reader written for the test, and the
//!    `viewBox` transform is SVG 2 section 8.2 transcribed again in `f32`,
//!    so the comparison covers the tokenizer, the path reader, the
//!    transform and the rasterizer, not just the last. The tolerance is
//!    stated at `TOLERANCE_*` below with the reason.
//! 3. **Every chunk size** gives the same pixels and the same `consumed`.
//! 4. **Refusals**: documents outside the scope, each refused with the right
//!    kind of error, and never a partial draw (the pixel buffer untouched).
//! 5. **Mutations**: every byte of both files replaced by a spread of values,
//!    and every prefix: never a panic, the invariant holds on every step,
//!    and the outcome is an image or an error.
//!
//! Written without `unwrap`, indexing or unchecked arithmetic, as the
//! workspace lints require of tests too: a helper returns `Err(String)` and
//! the test returns it.

use clazel_image_shape::{
    Buffers, Config, ConfigStatus, Decoder, Error, Format, FrameCount, Status, premultiply,
};
use clazel_svg::Svg;

const Y18: &[u8] = include_bytes!("fixtures/hn/y18.svg");
const TRIANGLE: &[u8] = include_bytes!("fixtures/hn/triangle.svg");

type R<T = ()> = Result<T, String>;

fn s<E: std::fmt::Debug>(e: E) -> String {
    format!("{e:?}")
}

fn usz(n: u32) -> usize {
    usize::try_from(n).unwrap_or(usize::MAX)
}

/// What a decode gave: the pixels (straight RGBA8) and the bytes consumed.
#[derive(Debug, PartialEq, Eq)]
struct Image {
    pixels: Vec<u8>,
    consumed: usize,
}

/// Decodes `doc` at `size` (or its intrinsic size) feeding `chunk` bytes at
/// a time, checking the invariant before and after every step. `Ok(None)` if
/// the stream ended (all bytes given) without a frame; `Err` is the
/// decoder's error as a `Result` inside, a test failure the outer one.
fn decode(
    doc: &[u8],
    size: Option<(u32, u32)>,
    chunk: usize,
    sentinel: u8,
) -> R<Result<Option<Image>, Error>> {
    let intrinsic = match Svg::decode_config(doc) {
        Ok(ConfigStatus::Ready(c)) => c,
        Ok(ConfigStatus::NeedMore) => return Ok(Ok(None)),
        Err(e) => return Ok(Err(e)),
    };
    assert_eq!(intrinsic.format(), Format::Svg);
    assert_eq!(intrinsic.frames(), FrameCount::Known(1));
    let config = match size {
        None => intrinsic,
        Some((w, h)) => match Config::new(Format::Svg, w, h, FrameCount::Known(1)) {
            Ok(c) => c,
            Err(e) => return Ok(Err(e)),
        },
    };
    let work_len = Svg::work_len(&config).map_err(s)?;
    let mut pixels = vec![sentinel; config.rgba_len().map_err(s)?];
    let mut work = vec![0xAB; work_len];
    let mut buffers = Buffers::new(&config, work_len, &mut pixels, &mut work).map_err(s)?;
    let mut svg = Svg::start(&config).map_err(s)?;
    assert!(svg.inv(&buffers));
    let mut at = 0usize;
    while at < doc.len() {
        let end = at.saturating_add(chunk).min(doc.len());
        let part = doc.get(at..end).ok_or("range")?;
        let result = svg.step(part, &mut buffers);
        assert!(svg.inv(&buffers), "the invariant after a step at {at}");
        let step = match result {
            Ok(step) => step,
            Err(e) => return Ok(Err(e)),
        };
        assert!(step.consumed <= part.len());
        match step.status {
            Status::NeedMore => {
                assert_eq!(step.consumed, part.len());
                at = end;
            }
            Status::FrameDone => {
                let consumed = at.saturating_add(step.consumed);
                // After the frame: no more.
                assert_eq!(svg.step(&[], &mut buffers), Err(Error::NoMoreFrames));
                return Ok(Ok(Some(Image {
                    pixels: buffers.pixels.to_vec(),
                    consumed,
                })));
            }
        }
    }
    Ok(Ok(None))
}

fn render(doc: &[u8], size: Option<(u32, u32)>) -> R<Image> {
    match decode(doc, size, usize::MAX, 0)? {
        Ok(Some(i)) => Ok(i),
        other => Err(format!("no image: {other:?}")),
    }
}

fn px(img: &Image, w: u32, x: u32, y: u32) -> R<[u8; 4]> {
    let i = usz(y)
        .saturating_mul(usz(w))
        .saturating_add(usz(x))
        .saturating_mul(4);
    let p = img
        .pixels
        .get(i..i.saturating_add(4))
        .ok_or("pixel out of range")?;
    p.try_into().map_err(s)
}

fn doc_end(doc: &[u8]) -> R<usize> {
    doc.iter()
        .position(|&b| b == b'>')
        .map(|p| p.saturating_add(1))
        .ok_or_else(|| "no >".to_string())
}

// ---- 1. HN's files ----

#[test]
fn configs_are_the_intrinsic_sizes() -> R {
    for (doc, w, h) in [(Y18, 18, 18), (TRIANGLE, 32, 32)] {
        let Ok(ConfigStatus::Ready(c)) = Svg::decode_config(doc) else {
            return Err("no config".into());
        };
        assert_eq!((c.format(), c.width(), c.height()), (Format::Svg, w, h));
        // Every proper prefix is "need more" until the root start tag is whole.
        let tag_end = doc_end(doc)?;
        for n in 0..tag_end {
            let prefix = doc.get(..n).ok_or("prefix")?;
            assert_eq!(
                Svg::decode_config(prefix),
                Ok(ConfigStatus::NeedMore),
                "{n}"
            );
        }
        // And a longer prefix gives the same config.
        for n in tag_end..=doc.len() {
            let prefix = doc.get(..n).ok_or("prefix")?;
            assert_eq!(Svg::decode_config(prefix), Ok(ConfigStatus::Ready(c)));
        }
    }
    Ok(())
}

#[test]
fn y18_at_its_size() -> R {
    let img = render(Y18, None)?;
    assert_eq!(img.consumed, Y18.len());
    assert_eq!(img.pixels.len(), 18 * 18 * 4);
    let orange = [255, 102, 0, 255];
    let white = [255, 255, 255, 255];
    // The orange square covers the whole image exactly (viewBox 4 4 188 188
    // is the square), so every corner is opaque orange.
    for (x, y) in [(0, 0), (17, 0), (0, 17), (17, 17)] {
        assert_eq!(px(&img, 18, x, y)?, orange, "{x},{y}");
    }
    // The glyph is the polygon (73.25 45.01) (96 92.4) (118.75 45.01) (138.3
    // 45.01) (103.99 109.5) (103.99 151) (88.01 151) (88.01 109.5) (53.69
    // 45.01), on the viewBox 4 4 188 188 at scale 18/188: pixel (6, 5) is
    // inside the left arm wholly, so pure white.
    assert_eq!(px(&img, 18, 6, 5)?, white);
    // The stem (user x 88 to 104, y 109.5 to 151, so pixel columns 8 and 9,
    // rows 11 to 13) is white but for its anti-aliased sides.
    let side = px(&img, 18, 8, 12)?;
    assert!(side[0] == 255 && (245..=252).contains(&side[1]), "{side:?}");
    // Below the glyph and left of it it is orange.
    assert_eq!(px(&img, 18, 4, 15)?, orange);
    assert_eq!(px(&img, 18, 9, 16)?, orange);
    // Every pixel is opaque (the white is over the orange).
    assert!(img.pixels.chunks(4).all(|p| p.get(3) == Some(&255)));
    Ok(())
}

#[test]
fn triangle_at_its_sizes() -> R {
    // Intrinsic 32 by 32 (the file says width 32, height 32, viewBox 0 0 32
    // 16): the viewBox is centred vertically, 32 by 16 at y = 8. The path
    // m2 27 14-29 14 29z is a triangle with apex (16, -2) and base y = 27 in
    // user space, so on the image its apex is at (16, 6) and its base at
    // y = 35, clipped to the 32 rows: the clip is the image, not the viewBox.
    let img = render(TRIANGLE, None)?;
    assert_eq!(img.pixels.len(), 32 * 32 * 4);
    // The middle of the bottom row is solid grey (below the viewBox: drawn).
    assert_eq!(px(&img, 32, 16, 31)?, [0x99, 0x99, 0x99, 255]);
    // The corners are outside the triangle; so is the row above its apex.
    assert_eq!(px(&img, 32, 0, 0)?, [0, 0, 0, 0]);
    assert_eq!(px(&img, 32, 31, 0)?, [0, 0, 0, 0]);
    assert_eq!(px(&img, 32, 0, 31)?, [0, 0, 0, 0]);
    for x in 0..32 {
        assert_eq!(px(&img, 32, x, 5)?, [0, 0, 0, 0], "above the apex");
    }
    // Left-right mirror symmetry about x = 16 (the sides are symmetric and
    // x = 16 is a pixel boundary): pixel x mirrors 31 - x. Rounding of the
    // two sides' crossings may differ by a grey level or so.
    for y in 0..32 {
        for x in 0..16 {
            let a = px(&img, 32, x, y)?;
            let b = px(&img, 32, 31 - x, y)?;
            for (p, q) in a.iter().zip(b.iter()) {
                assert!(p.abs_diff(*q) <= 2, "{x},{y}: {a:?} {b:?}");
            }
        }
    }
    // HN's size: `background-size: 10px` on an image of ratio 1:1 (its width and
    // height are both 32): 10 by 10. The arrow's base is the bottom row.
    let small = render(TRIANGLE, Some((10, 10)))?;
    assert_eq!(small.pixels.len(), 10 * 10 * 4);
    assert_eq!(px(&small, 10, 5, 9)?.get(3), Some(&255));
    assert_eq!(px(&small, 10, 0, 0)?, [0, 0, 0, 0]);
    assert_eq!(px(&small, 10, 9, 0)?, [0, 0, 0, 0]);
    Ok(())
}

#[test]
fn another_aspect_ratio_is_centred_with_transparent_bars() -> R {
    // The square logo into 40 by 20: the 20 by 20 image sits in the middle.
    let img = render(Y18, Some((40, 20)))?;
    for y in 0..20 {
        for x in 0..40 {
            let inside = (10..30).contains(&x);
            let p = px(&img, 40, x, y)?;
            if inside {
                assert_eq!(p.get(3), Some(&255), "{x},{y}");
            } else {
                assert_eq!(p, [0, 0, 0, 0], "{x},{y}");
            }
        }
    }
    // The same logo into 20 by 40: centred vertically.
    let img = render(Y18, Some((20, 40)))?;
    for x in 0..20 {
        assert_eq!(px(&img, 20, x, 9)?, [0, 0, 0, 0]);
        assert_eq!(px(&img, 20, x, 30)?, [0, 0, 0, 0]);
        assert_eq!(px(&img, 20, x, 10)?.get(3), Some(&255));
        assert_eq!(px(&img, 20, x, 29)?.get(3), Some(&255));
    }
    // The arrow's content is not clipped to its viewBox (section 3.11): into
    // 32 by 32 its base, below the viewBox, is drawn (see the test above).
    Ok(())
}

// ---- 2. The reference rasterizer ----

type Polygon = Vec<(f32, f32)>;

/// A cursor over path data for the reference reader.
struct Cur<'a> {
    b: &'a [u8],
    i: usize,
}

impl Cur<'_> {
    fn peek(&self) -> u8 {
        self.b.get(self.i).copied().unwrap_or(0)
    }
    fn bump(&mut self) {
        self.i = self.i.saturating_add(1);
    }
    fn skip(&mut self) {
        while matches!(self.peek(), b' ' | b',') {
            self.bump();
        }
    }
    fn num(&mut self) -> R<f32> {
        self.skip();
        let from = self.i;
        if matches!(self.peek(), b'-' | b'+') {
            self.bump();
        }
        while self.peek().is_ascii_digit() || self.peek() == b'.' {
            self.bump();
        }
        let text = self.b.get(from..self.i).ok_or("number range")?;
        std::str::from_utf8(text)
            .map_err(s)?
            .parse::<f32>()
            .map_err(s)
    }
    fn more(&mut self) -> bool {
        self.skip();
        let c = self.peek();
        c.is_ascii_digit() || matches!(c, b'-' | b'+' | b'.')
    }
}

/// The path data of one `path` element, read by a float reader written for
/// this test (not the crate's): polygons of absolute points, user space.
fn reference_polygons(d: &str) -> R<Vec<Polygon>> {
    let mut cur = Cur {
        b: d.as_bytes(),
        i: 0,
    };
    let mut polys: Vec<Polygon> = vec![];
    let mut pen = (0f32, 0f32);
    let mut start = pen;
    while cur.i < d.len() {
        let c = cur.peek();
        cur.bump();
        match c {
            b'M' | b'm' => {
                let mut first = true;
                loop {
                    let (x, y) = (cur.num()?, cur.num()?);
                    pen = if c == b'm' && !(polys.is_empty() && first) {
                        (pen.0 + x, pen.1 + y)
                    } else {
                        (x, y)
                    };
                    if first {
                        start = pen;
                        polys.push(vec![pen]);
                    } else {
                        polys.last_mut().ok_or("no polygon")?.push(pen);
                    }
                    first = false;
                    if !cur.more() {
                        break;
                    }
                }
            }
            b'L' | b'l' | b'H' | b'h' | b'V' | b'v' => loop {
                match c {
                    b'L' | b'l' => {
                        let (x, y) = (cur.num()?, cur.num()?);
                        pen = if c == b'l' {
                            (pen.0 + x, pen.1 + y)
                        } else {
                            (x, y)
                        };
                    }
                    b'H' | b'h' => {
                        let x = cur.num()?;
                        pen.0 = if c == b'h' { pen.0 + x } else { x };
                    }
                    _ => {
                        let y = cur.num()?;
                        pen.1 = if c == b'v' { pen.1 + y } else { y };
                    }
                }
                polys.last_mut().ok_or("no polygon")?.push(pen);
                if !cur.more() {
                    break;
                }
            },
            b'Z' | b'z' => pen = start,
            b' ' => {}
            other => return Err(format!("the reference reader has no command {other}")),
        }
    }
    Ok(polys)
}

/// One path of a file: its `d` and `fill`, read by plain string search.
fn path_elements(doc: &str) -> R<Vec<(String, [u8; 3])>> {
    let mut out = vec![];
    let mut rest = doc;
    while let Some(p) = rest.find("<path ") {
        rest = rest.get(p..).ok_or("rest")?;
        let end = rest.find('>').ok_or("no >")?;
        let tag = rest.get(..end).ok_or("tag")?;
        let attr = |name: &str| -> R<String> {
            let k = tag
                .find(&format!(" {name}=\""))
                .ok_or("no attribute")?
                .saturating_add(name.len())
                .saturating_add(3);
            let tail = tag.get(k..).ok_or("tail")?;
            Ok(tail
                .get(..tail.find('"').ok_or("no quote")?)
                .ok_or("v")?
                .to_string())
        };
        let fill = attr("fill")?;
        let hex = |t: &str| u8::from_str_radix(t, 16).map_err(s);
        let rgb = if fill.len() == 4 {
            let d =
                |i: usize| -> R<u8> { Ok(hex(fill.get(i..=i).ok_or("hex")?)?.saturating_mul(17)) };
            [d(1)?, d(2)?, d(3)?]
        } else {
            let h = |a: usize| hex(fill.get(a..a.saturating_add(2)).ok_or("hex")?);
            [h(1)?, h(3)?, h(5)?]
        };
        out.push((attr("d")?, rgb));
        rest = rest.get(end..).ok_or("rest")?;
    }
    Ok(out)
}

/// The reference render: tiny-skia fills the polygons with the `viewBox`
/// transform of SVG 2 section 8.2 (`xMidYMid meet`) in `f32`. Premultiplied
/// RGBA8.
fn reference(doc: &[u8], vb: [f32; 4], w: u32, h: u32) -> R<Vec<u8>> {
    use tiny_skia::{FillRule, Paint, PathBuilder, Pixmap, Transform};
    let doc = std::str::from_utf8(doc).map_err(s)?;
    let (ew, eh) = (w as f32, h as f32);
    let [vx, vy, vw, vh] = vb;
    let scale = (ew / vw).min(eh / vh);
    let tx = -vx * scale + (ew - vw * scale) / 2.0;
    let ty = -vy * scale + (eh - vh * scale) / 2.0;
    let mut pixmap = Pixmap::new(w, h).ok_or("pixmap")?;
    for (d, rgb) in path_elements(doc)? {
        let mut pb = PathBuilder::new();
        for poly in reference_polygons(&d)? {
            let (first, rest) = poly.split_first().ok_or("empty polygon")?;
            pb.move_to(first.0, first.1);
            for p in rest {
                pb.line_to(p.0, p.1);
            }
            pb.close();
        }
        let path = pb.finish().ok_or("path")?;
        let mut paint = Paint::default();
        paint.set_color_rgba8(rgb[0], rgb[1], rgb[2], 255);
        paint.anti_alias = true;
        let t = Transform::from_row(scale, 0.0, 0.0, scale, tx, ty);
        pixmap.fill_path(&path, &paint, FillRule::Winding, t, None);
    }
    Ok(pixmap.data().to_vec())
}

/// Statement of the tolerance against tiny-skia. Both engines sample
/// coverage (ours: 16 scanlines of exact horizontal overlap; tiny-skia: 4 by 4
/// supersampling, with its own rounding), so on an edge pixel they differ by
/// sampling error. Measured against the picture drawn 16 times larger and
/// averaged down (below), ours is within 6 of 255 at every size tried and
/// tiny-skia within 41, so the difference between the two is nearly all
/// tiny-skia's: the bound is 48, its worst case plus a margin. A pixel that
/// is wholly inside or outside (solid) in both must agree **exactly**.
const TOLERANCE_EDGE: u8 = 48;
/// Ours against the same picture drawn 16 times larger and averaged down
/// (the coverage, nearly exactly): our own sampling error, 16 scanlines per
/// pixel, is at most 1/16 of a pixel (16 of 255) plus rounding.
const TOLERANCE_TRUTH: u8 = 20;
/// The mean absolute difference over all channels of all pixels.
const TOLERANCE_MEAN: f64 = 1.0;

struct Diff {
    max: u8,
    mean: f64,
    edge_pixels: usize,
    interior_mismatches: usize,
}

/// `solids` are the pixels a wholly covered or uncovered pixel can be
/// (premultiplied): transparent and each fill colour, opaque. A pixel that is
/// solid in both images must be equal; any other is an edge pixel.
fn compare(ours_straight: &[u8], theirs: &[u8], solids: &[[u8; 4]]) -> Diff {
    let mut max = 0u8;
    let mut sum = 0u64;
    let mut edge_pixels = 0usize;
    let mut interior_mismatches = 0usize;
    for (a, b) in ours_straight
        .as_chunks::<4>()
        .0
        .iter()
        .zip(theirs.as_chunks::<4>().0.iter())
    {
        let a = premultiply(*a);
        let mut worst = 0u8;
        for (p, q) in a.iter().zip(b.iter()) {
            let d = p.abs_diff(*q);
            worst = worst.max(d);
            sum = sum.saturating_add(u64::from(d));
        }
        max = max.max(worst);
        let edge = !(solids.contains(&a) && solids.iter().any(|s| s.as_slice() == b.as_slice()));
        if edge {
            edge_pixels = edge_pixels.saturating_add(1);
        } else if worst != 0 {
            interior_mismatches = interior_mismatches.saturating_add(1);
        }
    }
    Diff {
        max,
        mean: sum as f64 / ours_straight.len() as f64,
        edge_pixels,
        interior_mismatches,
    }
}

/// The picture drawn at `k` times the size and averaged down (premultiplied):
/// the coverage to within the high-resolution image's own sampling, which is
/// `k` times finer. Used to say which of two engines is nearer the truth.
fn averaged(doc: &[u8], w: u32, h: u32, k: u32) -> R<Vec<u8>> {
    let hi = render(doc, Some((w.saturating_mul(k), h.saturating_mul(k))))?;
    let (wu, ku) = (usz(w), usz(k));
    let hi_w = wu.saturating_mul(ku);
    let mut out = vec![0u8; usz(w).saturating_mul(usz(h)).saturating_mul(4)];
    for y in 0..usz(h) {
        for x in 0..wu {
            let mut sum = [0u32; 4];
            for dy in 0..ku {
                for dx in 0..ku {
                    let hx = x.saturating_mul(ku).saturating_add(dx);
                    let hy = y.saturating_mul(ku).saturating_add(dy);
                    let i = hy.saturating_mul(hi_w).saturating_add(hx).saturating_mul(4);
                    let p = hi.pixels.get(i..i.saturating_add(4)).ok_or("hi")?;
                    let p = premultiply(p.try_into().map_err(s)?);
                    for (acc, v) in sum.iter_mut().zip(p) {
                        *acc = acc.saturating_add(u32::from(v));
                    }
                }
            }
            let n = k.saturating_mul(k);
            let o = y.saturating_mul(wu).saturating_add(x).saturating_mul(4);
            for (j, v) in sum.iter().enumerate() {
                let avg = v.saturating_add(n / 2) / n;
                if let Some(slot) = out.get_mut(o.saturating_add(j)) {
                    *slot = u8::try_from(avg).unwrap_or(255);
                }
            }
        }
    }
    Ok(out)
}

fn max_diff(a: &[u8], b: &[u8]) -> u8 {
    a.iter()
        .zip(b)
        .map(|(p, q)| p.abs_diff(*q))
        .max()
        .unwrap_or(0)
}

#[test]
fn against_tiny_skia() -> R {
    if cfg!(miri) {
        // tiny-skia's SIMD paths are not worth Miri's minutes; the
        // decoder's own tests below run under Miri.
        return Ok(());
    }
    type Case<'a> = (&'a str, &'a [u8], [f32; 4], &'a [[u8; 4]], &'a [(u32, u32)]);
    let cases: [Case; 2] = [
        (
            "y18",
            Y18,
            [4.0, 4.0, 188.0, 188.0],
            &[[0, 0, 0, 0], [255, 102, 0, 255], [255, 255, 255, 255]],
            &[
                (18, 18),
                (36, 36),
                (9, 9),
                (10, 10),
                (20, 20),
                (64, 64),
                (40, 20),
                (20, 40),
            ],
        ),
        (
            "triangle",
            TRIANGLE,
            [0.0, 0.0, 32.0, 16.0],
            &[[0, 0, 0, 0], [0x99, 0x99, 0x99, 255]],
            &[
                (32, 32),
                (10, 10),
                (20, 20),
                (64, 64),
                (16, 16),
                (12, 12),
                (40, 20),
                (20, 40),
                (64, 32),
            ],
        ),
    ];
    for (name, doc, vb, solids, sizes) in cases {
        for &(w, h) in sizes {
            let ours = render(doc, Some((w, h)))?;
            let theirs = reference(doc, vb, w, h)?;
            let d = compare(&ours.pixels, &theirs, solids);
            eprintln!(
                "{name} at {w}x{h}: max {} mean {:.3} edge pixels {} interior mismatches {}",
                d.max, d.mean, d.edge_pixels, d.interior_mismatches
            );
            // Which is nearer the truth (the same picture at 16 times the size,
            // averaged down)?
            let truth = averaged(doc, w, h, 16)?;
            let mut ours_p = ours.pixels.clone();
            clazel_image_shape::premultiply_in_place(&mut ours_p);
            let (ours_err, theirs_err) = (max_diff(&ours_p, &truth), max_diff(&theirs, &truth));
            eprintln!(
                "    against the 16x average: ours max {ours_err}, tiny-skia max {theirs_err}"
            );
            assert!(
                ours_err <= TOLERANCE_TRUTH,
                "{name} {w}x{h}: ours {ours_err}"
            );
            assert_eq!(d.interior_mismatches, 0, "{name} {w}x{h}");
            assert!(d.max <= TOLERANCE_EDGE, "{name} {w}x{h}: max {}", d.max);
            assert!(d.mean <= TOLERANCE_MEAN, "{name} {w}x{h}: mean {}", d.mean);
        }
    }
    Ok(())
}

// ---- 3. Chunk sizes ----

#[test]
fn every_chunk_size_gives_the_same_image() -> R {
    let stride = if cfg!(miri) { 37 } else { 1 };
    for doc in [Y18, TRIANGLE] {
        let whole = render(doc, None)?;
        for chunk in (1..=doc.len().saturating_add(1)).step_by(stride) {
            let got = decode(doc, None, chunk, 0xEE)?;
            assert_eq!(
                got,
                Ok(Some(Image {
                    pixels: whole.pixels.clone(),
                    consumed: whole.consumed
                })),
                "chunk {chunk}"
            );
        }
    }
    Ok(())
}

#[test]
fn bytes_after_the_root_are_not_consumed() -> R {
    for doc in [Y18, TRIANGLE] {
        let mut longer = doc.to_vec();
        longer.extend_from_slice(b"\n<!-- trailing -->\x00\xff garbage");
        let want = render(doc, None)?;
        for chunk in [1, 7, usize::MAX] {
            let img = decode(&longer, None, chunk, 0)?
                .map_err(s)?
                .ok_or("no image")?;
            assert_eq!(img.consumed, doc.len(), "chunk {chunk}");
            assert_eq!(img.pixels, want.pixels);
        }
    }
    Ok(())
}

#[test]
fn a_prefix_is_not_a_frame() -> R {
    for doc in [Y18, TRIANGLE] {
        for n in 0..doc.len() {
            let prefix = doc.get(..n).ok_or("prefix")?;
            assert_eq!(decode(prefix, None, 5, 0)?, Ok(None), "{n}");
        }
    }
    Ok(())
}

#[test]
fn same_image_whatever_the_buffers_held() -> R {
    // Dirty pixel and work buffers must not leak into the image.
    let a = decode(Y18, None, 16, 0x00)?;
    let b = decode(Y18, None, 16, 0xFF)?;
    assert_eq!(a, b);
    assert!(matches!(a, Ok(Some(_))));
    Ok(())
}

// ---- 4. Refusals ----

const HEAD: &str =
    "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"8\" height=\"8\" viewBox=\"0 0 8 8\">";

fn doc(body: &str) -> String {
    format!("{HEAD}{body}</svg>")
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Kind {
    Image,
    Unsupported,
    Malformed,
    Size,
}

fn classify(e: Error) -> Kind {
    match e {
        Error::Unsupported(_) => Kind::Unsupported,
        Error::Size(_) => Kind::Size,
        _ => Kind::Malformed,
    }
}

fn kind(d: &str) -> R<Kind> {
    // The pixel buffer starts as 0x5A: on an error it must still be 0x5A
    // (nothing drawn: not even the paths before the bad one).
    let config = match Svg::decode_config(d.as_bytes()) {
        Ok(ConfigStatus::Ready(c)) => c,
        Ok(ConfigStatus::NeedMore) => return Ok(Kind::Malformed),
        Err(e) => return Ok(classify(e)),
    };
    let work_len = Svg::work_len(&config).map_err(s)?;
    let mut pixels = vec![0x5A; config.rgba_len().map_err(s)?];
    let mut work = vec![0; work_len];
    let mut b = Buffers::new(&config, work_len, &mut pixels, &mut work).map_err(s)?;
    let mut svg = Svg::start(&config).map_err(s)?;
    let result = svg.step(d.as_bytes(), &mut b);
    assert!(svg.inv(&b));
    Ok(match result {
        Ok(st) if st.status == Status::FrameDone => Kind::Image,
        Ok(_) => Kind::Malformed,
        Err(e) => {
            assert!(
                b.pixels.iter().all(|&v| v == 0x5A),
                "{d}: an error after a draw"
            );
            assert_eq!(svg.step(b"x", &mut b), Err(Error::Spent));
            classify(e)
        }
    })
}

fn all_are(docs: &[String], want: Kind) -> R {
    for d in docs {
        assert_eq!(kind(d)?, want, "{d}");
    }
    Ok(())
}

#[test]
fn accepted_documents() -> R {
    all_are(
        &[
            doc(""),
            doc("<path/>"),
            doc("<path d=''/>"),
            doc("<path d=\"M1 1h6v6H1z\"/>"),
            doc("<path d=\"M1 1h6v6H1z\" fill=\"#abc\"></path>"),
            doc(
                "<path fill=\"#AABBCC\" d=\"M 1,1 L 7,1 7,7 Z\"/>\n<!-- two -->\n<path d=\"m0 0 1 1\"/>",
            ),
            doc("  <path\n\td=\"M1 1\n h6 v6\"\n\tfill='#000'\n/>  "),
            format!(
                "\u{feff}<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!-- a -->{}",
                doc("")
            ),
            "<svg width='3' height='3' xmlns='http://www.w3.org/2000/svg'/>".to_string(),
            "<svg height='3' width='3' xmlns='http://www.w3.org/2000/svg'></svg >".to_string(),
            // viewBox separators: spaces, commas, both.
            "<svg xmlns='http://www.w3.org/2000/svg' width='3' height='3' viewBox=' 0,0 , 8  8 '/>"
                .to_string(),
        ],
        Kind::Image,
    )
}

#[test]
fn refused_unsupported() -> R {
    let ns = "xmlns=\"http://www.w3.org/2000/svg\"";
    all_are(
        &[
            // Elements.
            doc("<g></g>"),
            doc("<circle/>"),
            doc("<rect/>"),
            doc("<defs/>"),
            doc("<style>p{}</style>"),
            doc("<linearGradient/>"),
            doc("<clipPath/>"),
            doc("<metadata/>"),
            doc("<path><g/></path>"),
            doc("<svg/>"),
            // Attributes.
            doc("<path d=\"M1 1\" stroke=\"#000\"/>"),
            doc("<path d=\"M1 1\" style=\"fill:red\"/>"),
            doc("<path d=\"M1 1\" transform=\"scale(2)\"/>"),
            doc("<path d=\"M1 1\" fill-rule=\"evenodd\"/>"),
            doc("<path d=\"M1 1\" id=\"a\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" preserveAspectRatio=\"none\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" style=\"\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" fill=\"#fff\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" version=\"1.1\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" viewBox=\"0 0 0 8\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" viewBox=\"0 0 -8 8\"/>"),
            format!("<svg {ns} height=\"8\"/>"),
            format!("<svg {ns} width=\"8\"/>"),
            format!("<svg {ns} width=\"8px\" height=\"8\"/>"),
            format!("<svg {ns} width=\"8.5\" height=\"8\"/>"),
            format!("<svg {ns} width=\"50%\" height=\"8\"/>"),
            format!("<svg {ns} width=\"\" height=\"8\"/>"),
            "<svg xmlns=\"http://www.w3.org/1999/xhtml\" width=\"8\" height=\"8\"/>".to_string(),
            // Path commands and numbers.
            doc("<path d=\"M1 1 C 2 2 3 3 4 4\"/>"),
            doc("<path d=\"M1 1 q 2 2 3 3\"/>"),
            doc("<path d=\"M1 1 a 1 1 0 0 0 2 2\"/>"),
            doc("<path d=\"M1 1 s 2 2 3 3\"/>"),
            doc("<path d=\"M1e0 1\"/>"),
            doc("<path d=\"M 5000000 1\"/>"),
            // Fill syntaxes.
            doc("<path d=\"M1 1\" fill=\"none\"/>"),
            doc("<path d=\"M1 1\" fill=\"red\"/>"),
            doc("<path d=\"M1 1\" fill=\"#ff\"/>"),
            doc("<path d=\"M1 1\" fill=\"#ffff\"/>"),
            doc("<path d=\"M1 1\" fill=\"rgb(1,2,3)\"/>"),
            doc("<path d=\"M1 1\" fill=\"url(#a)\"/>"),
            doc("<path d=\"M1 1\" fill=\" #fff\"/>"),
            doc("<path d=\"M1 1\" fill=\"\"/>"),
            // XML.
            format!("<!DOCTYPE svg>{}", doc("")),
            format!("<?xml-stylesheet href='a'?>{}", doc("")),
            doc("<![CDATA[x]]>"),
            doc("<?php ?>"),
            doc("text"),
            doc("&amp;"),
            doc("<path d=\"M1 1\" fill=\"&#35;fff\"/>"),
            format!("<svg:svg {ns} width=\"8\" height=\"8\"/>"),
            format!(
                "<svg {ns} xmlns:xlink=\"http://www.w3.org/1999/xlink\" width=\"8\" height=\"8\"/>"
            ),
            doc("<svg:path d=\"M1 1\"/>"),
            "<html/>".to_string(),
            // Too many attributes for the tokenizer to keep.
            format!("<svg {ns} width=\"8\" height=\"8\" a=\"1\" b=\"2\"/>"),
        ],
        Kind::Unsupported,
    )
}

#[test]
fn refused_malformed() -> R {
    let ns = "xmlns=\"http://www.w3.org/2000/svg\"";
    all_are(
        &[
            // XML.
            doc("</path>"),
            doc("<path></svg>"),
            doc("<path d=\"M1 1\"></g>"),
            doc("<path d=M1/>"),
            doc("<path d=\"M1 1\"fill=\"#000\"/>"),
            doc("<path d=\"M1 1\" d=\"M2 2\"/>"),
            doc("<path d=\"M1 1<\"/>"),
            doc("<path d/>"),
            doc("<path / >"),
            doc("<>"),
            doc("< path/>"),
            "\u{feff}x".to_string(),
            "GIF89a".to_string(),
            "<?xml version='1.0'?></svg>".to_string(),
            "<svg width=\"8\" height=\"8\"/>".to_string(),
            format!("<svg {ns} width=\"8\" height=\"8\" viewBox=\"0 0 8\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" viewBox=\"0 0 8 8 8\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" viewBox=\"0 0 8,\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" viewBox=\"0 0 8x 8\"/>"),
            format!("<svg {ns} width=\"8\" height=\"8\" viewBox=\"0 0-8 8\"/>"),
            // Path data.
            doc("<path d=\"L 1 1\"/>"),
            doc("<path d=\"1 1\"/>"),
            doc("<path d=\"M\"/>"),
            doc("<path d=\"M 1\"/>"),
            doc("<path d=\"M 1 2 3\"/>"),
            doc("<path d=\"M 1,2,\"/>"),
            doc("<path d=\"M 1 2 z 3\"/>"),
            doc("<path d=\"M 1 2 H\"/>"),
            doc("<path d=\"M 1 2 V 3 4 x\"/>"),
            doc("<path d=\"M 1. 2\"/>"),
            doc("<path d=\"M 1 2 L 3 4 5\"/>"),
            doc("<path d=\"M - 2\"/>"),
            doc("<path d=\"M 1 2 ; 3\"/>"),
            doc("<path d=\"M 1 2,,3 4\"/>"),
        ],
        Kind::Malformed,
    )
}

#[test]
fn refused_sizes() -> R {
    let ns = "xmlns=\"http://www.w3.org/2000/svg\"";
    all_are(
        &[
            format!("<svg {ns} width=\"0\" height=\"8\"/>"),
            format!("<svg {ns} width=\"8\" height=\"0\"/>"),
            format!("<svg {ns} width=\"16385\" height=\"8\"/>"),
            format!("<svg {ns} width=\"8\" height=\"16385\"/>"),
            format!("<svg {ns} width=\"99999999999\" height=\"8\"/>"),
            // Each side is allowed, the pixel count is not (2^26).
            format!("<svg {ns} width=\"16384\" height=\"16384\"/>"),
        ],
        Kind::Size,
    )
}

#[test]
fn nothing_is_drawn_when_a_later_path_is_bad() -> R {
    // The first path is fine and would cover the image; the second is out
    // of scope. kind() asserts the pixels are untouched.
    let a = doc("<path d=\"M0 0h8v8H0z\"/><path d=\"M0 0 C1 1 2 2 3 3\"/>");
    assert_eq!(kind(&a)?, Kind::Unsupported);
    let b = doc("<path d=\"M0 0h8v8H0z\"/><path d=\"M0 0 L\"/>");
    assert_eq!(kind(&b)?, Kind::Malformed);
    let c = doc("<path d=\"M0 0h8v8H0z\"/><g/>");
    assert_eq!(kind(&c)?, Kind::Unsupported);
    Ok(())
}

#[test]
fn limits() -> R {
    // 256 edges are allowed, 257 are not (the closing edge counts).
    let mut d = String::from("M 0 0");
    // Consecutive points differ (x alternates 1 and 7), so no edge is empty.
    for i in 0..255u32 {
        d.push_str(&format!(
            " L {} {}",
            if i % 2 == 0 { 7 } else { 1 },
            1 + i % 7
        ));
    }
    // 255 lines and the closing edge: 256.
    assert_eq!(kind(&doc(&format!("<path d=\"{d}\"/>")))?, Kind::Image);
    d.push_str(" L 1 4");
    assert_eq!(
        kind(&doc(&format!("<path d=\"{d}\"/>")))?,
        Kind::Unsupported
    );
    // A document over 8,192 bytes.
    let big = doc(&format!("<!--{}-->", "x".repeat(8200)));
    assert_eq!(kind(&big)?, Kind::Unsupported);
    // One of 8,192 bytes exactly is fine.
    let pad = 8192usize.saturating_sub(doc("<!---->").len());
    let exact = doc(&format!("<!--{}-->", "x".repeat(pad)));
    assert_eq!(exact.len(), 8192);
    assert_eq!(kind(&exact)?, Kind::Image);
    // Coordinates past 2^20 (here by adding relative ones) are refused, not wrapped.
    let huge = doc("<path d=\"M 1000000 0 l 100000 0 0 5\"/>");
    assert_eq!(kind(&huge)?, Kind::Unsupported);
    // A tiny viewBox magnifies past the device range.
    let tiny = "<svg xmlns='http://www.w3.org/2000/svg' width='16000' height='1' viewBox='0 0 0.0001 0.0001'><path d='M0 0 L 1000000 1000000 L 0 1000000'/></svg>";
    assert_eq!(kind(tiny)?, Kind::Unsupported);
    Ok(())
}

// ---- 5. Mutations and prefixes ----

#[test]
fn mutated_files_never_panic() -> R {
    let values: &[u8] = &[
        0, b'<', b'>', b'/', b'"', b'\'', b'=', b' ', b'-', b'.', b'0', b'9', b'M', b'z', b'#',
        b'&', b'e', 0xFF, 0xEF,
    ];
    let stride = if cfg!(miri) { 23 } else { 1 };
    let mut run = 0usize;
    let mut images = 0usize;
    for doc in [Y18, TRIANGLE] {
        for at in (0..doc.len()).step_by(stride) {
            for &v in values {
                let mut m = doc.to_vec();
                if let Some(slot) = m.get_mut(at) {
                    *slot = v;
                }
                for chunk in [1, 9, usize::MAX] {
                    run = run.saturating_add(1);
                    if let Ok(Ok(Some(_))) = decode(&m, None, chunk, 0x77) {
                        images = images.saturating_add(1);
                    }
                }
                // Deleting the byte, and inserting a value before it.
                let mut m = doc.to_vec();
                m.remove(at);
                decode(&m, None, 5, 0)?.ok();
                let mut m = doc.to_vec();
                m.insert(at, v);
                decode(&m, None, 5, 0)?.ok();
            }
        }
    }
    eprintln!("{run} mutants, {images} still images");
    assert!(run > 0);
    Ok(())
}

#[test]
fn mutants_are_consistent_across_chunk_sizes() -> R {
    // Whatever a mutant is, it is the same outcome at every chunk size
    // (image, error and consumed bytes).
    let stride = if cfg!(miri) { 41 } else { 3 };
    for doc in [Y18, TRIANGLE] {
        for at in (0..doc.len()).step_by(stride) {
            for v in *b"0q>-" {
                let mut m = doc.to_vec();
                if let Some(slot) = m.get_mut(at) {
                    *slot = v;
                }
                let a = decode(&m, None, usize::MAX, 0)?;
                for chunk in [1, 2, 13] {
                    assert_eq!(decode(&m, None, chunk, 0)?, a, "{at} {v} {chunk}");
                }
            }
        }
    }
    Ok(())
}

#[test]
fn rendering_sizes_up_to_the_limit_are_safe() -> R {
    // A 1 by 1 and the widest and tallest allowed.
    for (w, h) in [(1u32, 1u32), (16384, 1), (1, 16384), (2, 3)] {
        if cfg!(miri) && w.saturating_mul(h) > 100 {
            continue;
        }
        let img = render(TRIANGLE, Some((w, h)))?;
        assert_eq!(
            img.pixels.len(),
            usz(w).saturating_mul(usz(h)).saturating_mul(4)
        );
    }
    Ok(())
}

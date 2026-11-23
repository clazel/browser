//! Shared by the PNG tests: a PNG writer (chunks, CRC, zlib with stored
//! blocks, forward filters, Adam7 pass extraction, APNG), written for the
//! tests and independent of the decoder's code, the driver that runs a
//! stream through the `Decoder` interface, and the reference decode with the
//! `png` crate. Written to the workspace's lints (no indexing, no unchecked
//! arithmetic) like everything else.

use std::io::Cursor;

use clazel_deflate::stream::Inflater;
use clazel_image_shape::{Buffers, ConfigStatus, Decoder, Error, Status};
use clazel_png::{Blend, Dispose, FrameInfo, Png};

/// The decoder under test.
pub type Dec = Png<Inflater>;

/// A deterministic generator (xorshift64*).
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// A value below `n` (0 if `n` is 0).
    pub fn below(&mut self, n: usize) -> usize {
        let n64 = u64::try_from(n).unwrap_or(u64::MAX);
        usize::try_from(self.next().checked_rem(n64).unwrap_or(0)).unwrap_or(0)
    }

    pub fn byte(&mut self) -> u8 {
        u8::try_from(self.below(256)).unwrap_or(0)
    }
}

pub fn at<T: Copy + Default>(s: &[T], i: usize) -> T {
    s.get(i).copied().unwrap_or_default()
}

/// `u32` to `usize` (always fits where these tests run).
pub fn us(v: u32) -> usize {
    usize::try_from(v).unwrap_or(usize::MAX)
}

/// `a * b + c`, saturating.
pub fn mad(a: usize, b: usize, c: usize) -> usize {
    a.saturating_mul(b).saturating_add(c)
}

// ---------------------------------------------------------------- writing

pub fn crc32(bytes: &[u8]) -> u32 {
    let mut c = 0xFFFF_FFFFu32;
    for &b in bytes {
        c ^= u32::from(b);
        for _ in 0..8 {
            c = if c & 1 == 1 {
                0xEDB8_8320 ^ (c >> 1)
            } else {
                c >> 1
            };
        }
    }
    !c
}

pub fn adler32(bytes: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    for &x in bytes {
        a = a.wrapping_add(u32::from(x)) % 65521;
        b = b.wrapping_add(a) % 65521;
    }
    (b << 16) | a
}

/// A chunk: length, type, data, CRC.
pub fn chunk(ty: &[u8; 4], data: &[u8]) -> Vec<u8> {
    let mut v = u32::try_from(data.len())
        .unwrap_or(0)
        .to_be_bytes()
        .to_vec();
    v.extend_from_slice(ty);
    v.extend_from_slice(data);
    let mut c = ty.to_vec();
    c.extend_from_slice(data);
    v.extend_from_slice(&crc32(&c).to_be_bytes());
    v
}

/// A zlib stream of stored blocks (RFC 1950, RFC 1951 3.2.4).
pub fn zlib_stored(data: &[u8]) -> Vec<u8> {
    let mut v = vec![0x78, 0x01];
    let mut rest = data;
    loop {
        let n = rest.len().min(65535);
        let (now, later) = rest.split_at(n);
        let last = later.is_empty();
        v.push(u8::from(last));
        let len = u16::try_from(n).unwrap_or(0);
        v.extend_from_slice(&len.to_le_bytes());
        v.extend_from_slice(&(!len).to_le_bytes());
        v.extend_from_slice(now);
        rest = later;
        if last {
            break;
        }
    }
    v.extend_from_slice(&adler32(data).to_be_bytes());
    v
}

pub const SIG: [u8; 8] = [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A];

/// The image a test writes: samples of every pixel and how to write it.
#[derive(Clone)]
pub struct Img {
    pub w: u32,
    pub h: u32,
    /// 0, 2, 3, 4 or 6.
    pub ct: u8,
    pub depth: u8,
    pub interlaced: bool,
    /// `w * h * channels` samples, each below `2^depth`.
    pub samples: Vec<u16>,
    /// PLTE bytes (3 per entry), for colour type 3 (and 2 and 6 as a
    /// suggested palette when non-empty).
    pub palette: Vec<u8>,
    /// tRNS data, if any.
    pub trns: Option<Vec<u8>>,
    /// The filter of each scanline in write order, cycled; `[0]` for none.
    pub filters: Vec<u8>,
    /// Bytes per IDAT chunk (0 for one chunk).
    pub idat_size: usize,
    /// Ancillary chunks to add after IHDR.
    pub extras: Vec<Vec<u8>>,
}

pub fn channels(ct: u8) -> usize {
    match ct {
        2 => 3,
        4 => 2,
        6 => 4,
        _ => 1,
    }
}

/// Packs the samples of one row into bytes (7.2).
pub fn pack(row: &[u16], depth: u8) -> Vec<u8> {
    let mut out = Vec::new();
    match depth {
        16 => {
            for &s in row {
                out.extend_from_slice(&s.to_be_bytes());
            }
        }
        8 => out.extend(row.iter().map(|&s| u8::try_from(s).unwrap_or(0))),
        d => {
            let per = usize::from(8u8.checked_div(d).unwrap_or(1));
            for group in row.chunks(per) {
                let mut byte = 0u8;
                for (k, &s) in group.iter().enumerate() {
                    let used = usize::from(d).saturating_mul(k.saturating_add(1));
                    let shift = u32::try_from(8usize.saturating_sub(used)).unwrap_or(0);
                    byte |= u8::try_from(s).unwrap_or(0).wrapping_shl(shift);
                }
                out.push(byte);
            }
        }
    }
    out
}

/// The paeth predictor, written out as 9.4 words it.
fn paeth_pred(a: u8, b: u8, c: u8) -> u8 {
    let (a, b, c) = (i32::from(a), i32::from(b), i32::from(c));
    let p = a.saturating_add(b).saturating_sub(c);
    let (pa, pb, pc) = (p.abs_diff(a), p.abs_diff(b), p.abs_diff(c));
    let r = if pa <= pb && pa <= pc {
        a
    } else if pb <= pc {
        b
    } else {
        c
    };
    u8::try_from(r).unwrap_or(0)
}

/// Forward filter of one row (9.2 to 9.4).
pub fn filter_row(kind: u8, bpp: usize, raw: &[u8], prev: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(raw.len());
    for i in 0..raw.len() {
        let x = at(raw, i);
        let left = i.checked_sub(bpp);
        let a = left.map_or(0, |l| at(raw, l));
        let b = at(prev, i);
        let c = left.map_or(0, |l| at(prev, l));
        let p = match kind {
            1 => a,
            2 => b,
            3 => u8::try_from(u16::from(a).saturating_add(u16::from(b)) / 2).unwrap_or(0),
            4 => paeth_pred(a, b, c),
            _ => 0,
        };
        out.push(x.wrapping_sub(p));
    }
    out
}

/// Which of the seven passes the pixel at `(x, y)` is in (8.1), written as
/// the table of residues rather than as the decoder's start and step.
fn pass_of(x: u32, y: u32) -> usize {
    match (x % 8, y % 8) {
        (0, 0) => 0,
        (4, 0) => 1,
        (0, 4) | (4, 4) => 2,
        (2, 0) | (6, 0) | (2, 4) | (6, 4) => 3,
        (0, 2) | (2, 2) | (4, 2) | (6, 2) | (0, 6) | (2, 6) | (4, 6) | (6, 6) => 4,
        (1 | 3 | 5 | 7, _) if y.is_multiple_of(2) => 5,
        _ => 6,
    }
}

/// The scanlines of an image as the datastream's decompressed bytes: filter
/// bytes and filtered rows, in pass order for an interlaced image.
pub fn scanlines(img: &Img) -> Vec<u8> {
    let ch = channels(img.ct);
    let bpp = usize::from(img.depth).saturating_mul(ch).div_ceil(8).max(1);
    let px = |x: u32, y: u32| -> Vec<u16> {
        let base = mad(mad(us(y), us(img.w), us(x)), ch, 0);
        (0..ch)
            .map(|k| at(&img.samples, base.saturating_add(k)))
            .collect()
    };
    let passes: Vec<Vec<Vec<u16>>> = if img.interlaced {
        (0..7)
            .map(|p| {
                (0..img.h)
                    .map(|y| {
                        (0..img.w)
                            .filter(|&x| pass_of(x, y) == p)
                            .flat_map(|x| px(x, y))
                            .collect::<Vec<u16>>()
                    })
                    .filter(|row| !row.is_empty())
                    .collect()
            })
            .collect()
    } else {
        vec![
            (0..img.h)
                .map(|y| (0..img.w).flat_map(|x| px(x, y)).collect())
                .collect(),
        ]
    };
    let mut out = Vec::new();
    let mut n = 0usize;
    for rows in passes {
        let mut prev: Vec<u8> = Vec::new();
        for row in rows {
            let raw = pack(&row, img.depth);
            if prev.len() != raw.len() {
                prev = vec![0; raw.len()];
            }
            let kind = at(&img.filters, n.checked_rem(img.filters.len()).unwrap_or(0));
            n = n.saturating_add(1);
            out.push(kind);
            out.extend(filter_row(kind, bpp, &raw, &prev));
            prev = raw;
        }
    }
    out
}

pub fn ihdr(img: &Img) -> Vec<u8> {
    let mut d = Vec::new();
    d.extend_from_slice(&img.w.to_be_bytes());
    d.extend_from_slice(&img.h.to_be_bytes());
    d.extend_from_slice(&[img.depth, img.ct, 0, 0, u8::from(img.interlaced)]);
    chunk(b"IHDR", &d)
}

/// IDAT chunks (or fdAT, with their sequence numbers from `seq`) of a zlib
/// stream, in pieces of `size` bytes (0 for one).
pub fn data_chunks(z: &[u8], size: usize, mut seq: Option<&mut u32>) -> Vec<u8> {
    let mut out = Vec::new();
    let size = if size == 0 { z.len().max(1) } else { size };
    for piece in z.chunks(size) {
        match seq.as_deref_mut() {
            None => out.extend(chunk(b"IDAT", piece)),
            Some(s) => {
                let mut d = s.to_be_bytes().to_vec();
                *s = s.saturating_add(1);
                d.extend_from_slice(piece);
                out.extend(chunk(b"fdAT", &d));
            }
        }
    }
    out
}

/// A whole datastream for one image.
pub fn png_bytes(img: &Img) -> Vec<u8> {
    let mut v = SIG.to_vec();
    v.extend(ihdr(img));
    for e in &img.extras {
        v.extend_from_slice(e);
    }
    if !img.palette.is_empty() {
        v.extend(chunk(b"PLTE", &img.palette));
    }
    if let Some(t) = &img.trns {
        v.extend(chunk(b"tRNS", t));
    }
    v.extend(data_chunks(
        &zlib_stored(&scanlines(img)),
        img.idat_size,
        None,
    ));
    v.extend(chunk(b"IEND", &[]));
    v
}

/// One frame of an APNG.
#[derive(Clone)]
pub struct FrameSpec {
    pub x: u32,
    pub y: u32,
    pub img: Img,
    pub delay: (u16, u16),
    pub dispose: u8,
    pub blend: u8,
}

pub fn fctl(seq: u32, f: &FrameSpec) -> Vec<u8> {
    let mut d = seq.to_be_bytes().to_vec();
    d.extend_from_slice(&f.img.w.to_be_bytes());
    d.extend_from_slice(&f.img.h.to_be_bytes());
    d.extend_from_slice(&f.x.to_be_bytes());
    d.extend_from_slice(&f.y.to_be_bytes());
    d.extend_from_slice(&f.delay.0.to_be_bytes());
    d.extend_from_slice(&f.delay.1.to_be_bytes());
    d.extend_from_slice(&[f.dispose, f.blend]);
    chunk(b"fcTL", &d)
}

/// An APNG: `base` is the default image (the canvas size); if `default_frame`
/// is given it is the fcTL of the default image (so it is the first frame of
/// the animation); `frames` follow in fdAT chunks.
pub fn apng_bytes(base: &Img, default_frame: Option<&FrameSpec>, frames: &[FrameSpec]) -> Vec<u8> {
    let mut v = SIG.to_vec();
    v.extend(ihdr(base));
    let count = frames
        .len()
        .saturating_add(usize::from(default_frame.is_some()));
    let mut actl = u32::try_from(count).unwrap_or(0).to_be_bytes().to_vec();
    actl.extend_from_slice(&0u32.to_be_bytes());
    v.extend(chunk(b"acTL", &actl));
    if !base.palette.is_empty() {
        v.extend(chunk(b"PLTE", &base.palette));
    }
    if let Some(t) = &base.trns {
        v.extend(chunk(b"tRNS", t));
    }
    let mut seq = 0u32;
    if let Some(f) = default_frame {
        v.extend(fctl(seq, f));
        seq = seq.saturating_add(1);
    }
    v.extend(data_chunks(
        &zlib_stored(&scanlines(base)),
        base.idat_size,
        None,
    ));
    for f in frames {
        v.extend(fctl(seq, f));
        seq = seq.saturating_add(1);
        v.extend(data_chunks(
            &zlib_stored(&scanlines(&f.img)),
            f.img.idat_size,
            Some(&mut seq),
        ));
    }
    v.extend(chunk(b"IEND", &[]));
    v
}

/// A random image of the given kind, with palette and tRNS where the
/// colour type has them (`with_trns`).
pub fn random_img(
    rng: &mut Rng,
    w: u32,
    h: u32,
    ct: u8,
    depth: u8,
    interlaced: bool,
    with_trns: bool,
) -> Img {
    let ch = channels(ct);
    let max = 1usize.checked_shl(u32::from(depth)).unwrap_or(1);
    let count = mad(us(w), us(h), 0).saturating_mul(ch);
    let entries = if ct == 3 {
        max.min(256).min(rng.below(256).saturating_add(1))
    } else {
        0
    };
    let samples: Vec<u16> = (0..count)
        .map(|_| {
            let limit = if ct == 3 { entries } else { max };
            u16::try_from(rng.below(limit)).unwrap_or(0)
        })
        .collect();
    let palette: Vec<u8> = if ct == 3 {
        (0..entries.saturating_mul(3)).map(|_| rng.byte()).collect()
    } else {
        Vec::new()
    };
    let trns = if !with_trns {
        None
    } else {
        match ct {
            0 => {
                // A value that occurs, so some pixels are transparent.
                let key = at(&samples, rng.below(samples.len()));
                Some(key.to_be_bytes().to_vec())
            }
            2 => {
                let i = rng.below(samples.len() / 3).saturating_mul(3);
                let mut d = Vec::new();
                for k in 0..3 {
                    d.extend_from_slice(&at(&samples, i.saturating_add(k)).to_be_bytes());
                }
                Some(d)
            }
            3 => {
                let n = rng.below(entries.saturating_add(1));
                Some((0..n).map(|_| rng.byte()).collect())
            }
            _ => None,
        }
    };
    Img {
        w,
        h,
        ct,
        depth,
        interlaced,
        samples,
        palette,
        trns,
        filters: vec![0],
        idat_size: 0,
        extras: Vec::new(),
    }
}

/// Every (colour type, depth) PNG allows (11.2.1, Table 11.1).
pub const KINDS: &[(u8, u8)] = &[
    (0, 1),
    (0, 2),
    (0, 4),
    (0, 8),
    (0, 16),
    (2, 8),
    (2, 16),
    (3, 1),
    (3, 2),
    (3, 4),
    (3, 8),
    (4, 8),
    (4, 16),
    (6, 8),
    (6, 16),
];

// ---------------------------------------------------------------- driving

pub const CANARY: u8 = 0xEE;

/// Canvases over this many bytes are not decoded by the tests (a mutated
/// IHDR can ask for 256 MiB).
pub const TOO_LARGE: usize = 8 << 20;

/// How a decode ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum End {
    /// IEND, after every frame.
    Iend,
    /// An error (the frames before it were completed).
    Error(String),
    /// The input ran out.
    Truncated,
}

/// What the decoder gave for a stream.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decoded {
    pub width: u32,
    pub height: u32,
    /// Each completed frame: its facts and the canvas after it.
    pub frames: Vec<(FrameInfo, Vec<u8>)>,
    pub end: End,
}

/// Decodes `bytes` through the shared interface in chunks of `chunk` bytes
/// (with an empty chunk between each pair if `empties`), checking the
/// invariant and the contract on every step.
pub fn decode(bytes: &[u8], chunk: usize, empties: bool) -> Result<Decoded, String> {
    let head = bytes.get(..bytes.len().min(40)).unwrap_or(bytes);
    let config = match Dec::decode_config(head) {
        Ok(ConfigStatus::Ready(c)) => c,
        Ok(ConfigStatus::NeedMore) => return Err("the input ends inside the header".into()),
        Err(e) => return Err(format!("{e:?}")),
    };
    // A longer prefix gives the same config.
    if let Ok(ConfigStatus::Ready(c2)) = Dec::decode_config(bytes) {
        assert_eq!(c2, config);
    }
    let plen = config.rgba_len().map_err(|e| format!("{e:?}"))?;
    if plen > TOO_LARGE {
        return Err("too large for the test".into());
    }
    let wlen = Dec::work_len(&config).map_err(|e| format!("{e:?}"))?;
    let mut pixels = vec![CANARY; plen.saturating_add(3)];
    let mut work = vec![CANARY; wlen.saturating_add(3)];
    let mut state = Box::new(Dec::start(&config).map_err(|e| format!("{e:?}"))?);
    let mut frames = Vec::new();
    let mut end = End::Truncated;
    {
        let mut buffers =
            Buffers::new(&config, wlen, &mut pixels, &mut work).map_err(|e| format!("{e:?}"))?;
        assert!(state.inv(&buffers));
        let mut pos = 0usize;
        let mut empty_turn = false;
        'feed: while pos < bytes.len() {
            let take = if empties && empty_turn {
                0
            } else {
                chunk.min(bytes.len().saturating_sub(pos))
            };
            empty_turn = !empty_turn;
            let part = bytes
                .get(pos..pos.saturating_add(take))
                .ok_or("chunk out of range")?;
            let result = state.step(part, &mut buffers);
            assert!(state.inv(&buffers), "invariant lost at byte {pos}");
            match result {
                Ok(step) => {
                    assert!(step.consumed <= part.len());
                    match step.status {
                        Status::NeedMore => {
                            assert_eq!(step.consumed, part.len());
                            pos = pos.saturating_add(take);
                        }
                        Status::FrameDone => {
                            let info = *state.frame().ok_or("FrameDone without a frame")?;
                            frames.push((info, buffers.pixels.to_vec()));
                            pos = pos.saturating_add(step.consumed);
                        }
                    }
                }
                Err(Error::NoMoreFrames) => {
                    end = End::Iend;
                    break 'feed;
                }
                Err(e) => {
                    end = End::Error(format!("{e:?}"));
                    // After an error the decoder is spent.
                    assert_eq!(state.step(&[], &mut buffers).err(), Some(Error::Spent));
                    break 'feed;
                }
            }
        }
    }
    // Nothing outside the buffers was written.
    assert!(
        pixels
            .get(plen..)
            .is_some_and(|s| s.iter().all(|&b| b == CANARY))
    );
    assert!(
        work.get(wlen..)
            .is_some_and(|s| s.iter().all(|&b| b == CANARY))
    );
    Ok(Decoded {
        width: config.width(),
        height: config.height(),
        frames,
        end,
    })
}

// -------------------------------------------------------------- reference

/// A frame as the `png` crate gives it: its own pixels as RGBA8, and its
/// control chunk if it has one.
pub struct RefFrame {
    pub fc: Option<png::FrameControl>,
    pub w: u32,
    pub h: u32,
    pub rgba: Vec<u8>,
}

pub struct Reference {
    pub width: u32,
    pub height: u32,
    pub frames: Vec<RefFrame>,
    /// Every frame decoded and the stream read to its end.
    pub complete: bool,
}

/// Decodes with the `png` crate, expanding to 8-bit samples and alpha
/// (`EXPAND | STRIP_16`), and converts every frame to RGBA8.
pub fn reference(bytes: &[u8]) -> Result<Reference, String> {
    let mut decoder = png::Decoder::new(Cursor::new(bytes));
    decoder.set_transformations(png::Transformations::EXPAND | png::Transformations::STRIP_16);
    let mut reader = decoder.read_info().map_err(|e| e.to_string())?;
    let (width, height) = reader.info().size();
    let total = match reader.info().animation_control {
        None => 1,
        Some(a) => a
            .num_frames
            .saturating_add(u32::from(reader.info().frame_control.is_none())),
    };
    let mut frames = Vec::new();
    let mut complete = true;
    for _ in 0..total {
        let mut buf = vec![0; reader.output_buffer_size().ok_or("too big")?];
        let Ok(info) = reader.next_frame(&mut buf) else {
            complete = false;
            break;
        };
        let fc = reader.info().frame_control;
        let n = mad(us(info.width), us(info.height), 0);
        let mut rgba = Vec::with_capacity(n.saturating_mul(4));
        let ch = match info.color_type {
            png::ColorType::Grayscale => 1,
            png::ColorType::GrayscaleAlpha => 2,
            png::ColorType::Rgb => 3,
            png::ColorType::Rgba => 4,
            png::ColorType::Indexed => return Err("indexed output".into()),
        };
        if info.bit_depth != png::BitDepth::Eight {
            return Err("output is not 8 bits".into());
        }
        // png 0.18.1 writes the pixels of an interlaced frame with the stride of
        // the canvas, not of the frame (in `next_frame`, `expand_pass` is given
        // `info().width`), while it writes a frame that is not interlaced with its
        // own: so a frame narrower than the canvas has its rows spread out.
        // This adapter reads each pixel from where png put it.
        let stride = if reader.info().interlaced {
            us(width)
        } else {
            us(info.width)
        };
        for i in 0..n {
            let row = i.checked_div(us(info.width)).unwrap_or(0);
            let col = i.checked_rem(us(info.width)).unwrap_or(0);
            let base = mad(row, stride, col);
            let p = |k: usize| at(&buf, mad(base, ch, k));
            rgba.extend_from_slice(&match ch {
                1 => [p(0), p(0), p(0), 255],
                2 => [p(0), p(0), p(0), p(1)],
                3 => [p(0), p(1), p(2), 255],
                _ => [p(0), p(1), p(2), p(3)],
            });
        }
        frames.push(RefFrame {
            fc,
            w: info.width,
            h: info.height,
            rgba,
        });
    }
    if complete && reader.finish().is_err() {
        complete = false;
    }
    Ok(Reference {
        width,
        height,
        frames,
        complete,
    })
}

/// The undo of a frame: its region, its `dispose_op` and the canvas before it.
struct Undo {
    x: u32,
    y: u32,
    w: u32,
    h: u32,
    op: png::DisposeOp,
    saved: Vec<u8>,
}

fn px(buf: &[u8], i: usize) -> [u8; 4] {
    [
        at(buf, i),
        at(buf, i.saturating_add(1)),
        at(buf, i.saturating_add(2)),
        at(buf, i.saturating_add(3)),
    ]
}

/// The canvas after each frame, composited from the reference's frames: 4.9
/// and 11.3.6.3 written out again from the specification's words, with the
/// rounding of `pixel::over` stated in the decoder's documentation.
pub fn composite(r: &Reference) -> Vec<Vec<u8>> {
    let cw = us(r.width);
    let mut canvas = vec![0u8; mad(cw, us(r.height), 0).saturating_mul(4)];
    let mut out = Vec::new();
    let mut undo: Option<Undo> = None;
    let mut animated_seen = false;
    let mut hidden_default = false;
    for (n, f) in r.frames.iter().enumerate() {
        if n > 0 {
            if hidden_default {
                canvas.fill(0);
                hidden_default = false;
            } else if let Some(u) = &undo {
                match u.op {
                    png::DisposeOp::None => {}
                    png::DisposeOp::Background => region(&mut canvas, cw, u, None),
                    png::DisposeOp::Previous => region(&mut canvas, cw, u, Some(&u.saved)),
                }
            }
        }
        let (x, y, w, h, dispose, blend, animated) = match f.fc {
            Some(c) => (
                c.x_offset,
                c.y_offset,
                c.width,
                c.height,
                c.dispose_op,
                c.blend_op,
                true,
            ),
            None => (
                0,
                0,
                r.width,
                r.height,
                png::DisposeOp::None,
                png::BlendOp::Source,
                false,
            ),
        };
        let mut dispose = dispose;
        if animated {
            if !animated_seen && dispose == png::DisposeOp::Previous {
                dispose = png::DisposeOp::Background;
            }
            animated_seen = true;
        } else {
            hidden_default = true;
        }
        let saved = canvas.clone();
        for j in 0..h {
            for i in 0..w {
                let src_at = mad(us(j), us(w), us(i)).saturating_mul(4);
                let dst_at =
                    mad(us(y.saturating_add(j)), cw, us(x.saturating_add(i))).saturating_mul(4);
                let src = px(&f.rgba, src_at);
                let dst = px(&canvas, dst_at);
                let new = match blend {
                    png::BlendOp::Source => src,
                    png::BlendOp::Over => over(src, dst),
                };
                for (k, v) in new.iter().enumerate() {
                    if let Some(s) = canvas.get_mut(dst_at.saturating_add(k)) {
                        *s = *v;
                    }
                }
            }
        }
        out.push(canvas.clone());
        undo = Some(Undo {
            x,
            y,
            w,
            h,
            op: dispose,
            saved,
        });
    }
    out
}

fn region(canvas: &mut [u8], cw: usize, u: &Undo, from: Option<&[u8]>) {
    for j in 0..u.h {
        for i in 0..u.w {
            let p = mad(us(u.y.saturating_add(j)), cw, us(u.x.saturating_add(i))).saturating_mul(4);
            for k in 0..4 {
                let at_k = p.saturating_add(k);
                let v = from.map_or(0, |s| at(s, at_k));
                if let Some(s) = canvas.get_mut(at_k) {
                    *s = v;
                }
            }
        }
    }
}

/// The OVER operation as `pixel::over` documents it, written again.
pub fn over(src: [u8; 4], dst: [u8; 4]) -> [u8; 4] {
    let sa = u64::from(src[3]);
    let da = u64::from(dst[3]);
    if sa == 255 {
        return src;
    }
    if sa == 0 {
        return dst;
    }
    let inv = 255u64.saturating_sub(sa);
    let behind = da.saturating_mul(inv).saturating_add(127) / 255;
    let alpha = sa.saturating_add(behind).min(255);
    let channel = |s: u8, d: u8| {
        let num = u64::from(s)
            .saturating_mul(sa)
            .saturating_mul(255)
            .saturating_add(u64::from(d).saturating_mul(da).saturating_mul(inv));
        let den = alpha.saturating_mul(255);
        let v = num.saturating_add(den / 2).checked_div(den).unwrap_or(0);
        u8::try_from(v.min(255)).unwrap_or(255)
    };
    [
        channel(src[0], dst[0]),
        channel(src[1], dst[1]),
        channel(src[2], dst[2]),
        u8::try_from(alpha).unwrap_or(255),
    ]
}

/// A frame's facts in the reference's terms, for comparing.
pub fn same_facts(info: &FrameInfo, f: &RefFrame) -> bool {
    match f.fc {
        None => !info.animated && info.width == f.w && info.height == f.h,
        Some(c) => {
            info.animated
                && (info.x, info.y, info.width, info.height)
                    == (c.x_offset, c.y_offset, c.width, c.height)
                && (info.delay_num, info.delay_den) == (c.delay_num, c.delay_den)
                && matches!(
                    (info.dispose, c.dispose_op),
                    (Dispose::None, png::DisposeOp::None)
                        | (Dispose::Background, png::DisposeOp::Background)
                        | (Dispose::Previous, png::DisposeOp::Previous)
                )
                && matches!(
                    (info.blend, c.blend_op),
                    (Blend::Source, png::BlendOp::Source) | (Blend::Over, png::BlendOp::Over)
                )
        }
    }
}

/// Compares a decode with the reference's: the size, the frames (facts and
/// composited pixels, exactly). `Ok` or what differs; whether both accept
/// the stream is the caller's to check.
pub fn compare(ours: &Decoded, r: &Reference) -> Result<(), String> {
    if (ours.width, ours.height) != (r.width, r.height) {
        return Err("sizes differ".into());
    }
    let canvases = composite(r);
    if ours.frames.len() != r.frames.len() {
        return Err(format!(
            "frame counts differ: {} and {} (ours ends {:?}, the reference complete: {})",
            ours.frames.len(),
            r.frames.len(),
            ours.end,
            r.complete
        ));
    }
    for (i, ((info, pixels), (rf, canvas))) in ours
        .frames
        .iter()
        .zip(r.frames.iter().zip(canvases.iter()))
        .enumerate()
    {
        if !same_facts(info, rf) {
            return Err(format!("frame {i}: facts differ: {info:?} and {:?}", rf.fc));
        }
        if pixels != canvas {
            let first = pixels.iter().zip(canvas.iter()).position(|(a, b)| a != b);
            return Err(format!("frame {i}: pixels differ, first at byte {first:?}"));
        }
    }
    Ok(())
}

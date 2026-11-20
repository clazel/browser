//! The WebP container (RFC 9649 section 2) as a byte-at-a-time state
//! machine, driving the lossless decoder of `vp8l.rs` and compositing the
//! frames of an animation; implements [`clazel_image_shape::Decoder`].
//!
//! Citations are to RFC 9649 by section; the listed choices are in `lib.rs`.

use clazel_image_shape::{
    Buffers, Config, ConfigStatus, Decoder, Error, Format, FrameCount, Status, Step,
};

use crate::compose::blend_row;
use crate::vp8l::Vp8l;
use crate::work::{Parts, work_len};

fn bad(why: &'static str) -> Error {
    Error::Malformed(why)
}

/// How a frame's transparent pixels meet the canvas (section 2.7.1.1,
/// "Blending method (B)").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Blend {
    /// 0: alpha-blend the frame over the canvas.
    Alpha,
    /// 1: overwrite the frame's rectangle.
    Overwrite,
}

/// What happens to the canvas after a frame is shown (section 2.7.1.1,
/// "Disposal method (D)").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dispose {
    /// 0: leave the canvas as it is.
    None,
    /// 1: fill the frame's rectangle with the background. Listed choice:
    /// transparent black, as browsers do, not the `ANIM` chunk's colour.
    Background,
}

/// The facts of a frame, as the stream gives them; read them after
/// [`Status::FrameDone`] with [`Webp::frame`]. A still image's one frame
/// covers the canvas, with a duration of 0, [`Blend::Overwrite`] and
/// [`Dispose::None`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrameInfo {
    /// Left edge on the canvas (twice the stored `Frame X`).
    pub left: u32,
    /// Top edge on the canvas.
    pub top: u32,
    /// Width in pixels.
    pub width: u32,
    /// Height in pixels.
    pub height: u32,
    /// How long to show the frame, in milliseconds (0 is implementation
    /// defined: 6.19's policy).
    pub duration_ms: u32,
    /// The blending method.
    pub blend: Blend,
    /// The disposal method.
    pub dispose: Dispose,
}

/// The global animation parameters of an `ANIM` chunk (section 2.7.1.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Animation {
    /// The background colour hint, red, green, blue, alpha (the chunk has it
    /// in the order blue, green, red, alpha). Not used for compositing.
    pub background: [u8; 4],
    /// The loop count; 0 means forever. Not used here (6.19's policy).
    pub loops: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Phase {
    /// The 12 bytes `RIFF`, size, `WEBP`, gathered.
    Riff,
    /// A chunk header, 8 bytes, gathered.
    ChunkHdr,
    /// The first 10 bytes of the `VP8X` payload, gathered.
    Vp8x,
    /// The first 6 bytes of an `ANIM` payload, gathered.
    Anim,
    /// The first 16 bytes of an `ANMF` payload, gathered.
    Anmf,
    /// A `VP8L` payload, to the lossless decoder.
    Payload,
    /// The rest of a payload to skip.
    Skip,
    /// The padding byte after an odd-sized chunk.
    Pad,
    /// The end of the RIFF data or a still image's frame: no more frames.
    Ended,
    /// An error happened.
    Spent,
}

/// What one byte did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Event {
    Continue,
    Frame,
    End,
}

/// The WebP decoder's state: fixed-size, no allocation.
#[derive(Debug, Clone, Copy)]
pub struct Webp {
    config: Config,
    /// The file is an animation (the config says its frame count is not
    /// known): the work buffer has a frame buffer.
    animated: bool,
    phase: Phase,
    hold: [u8; 16],
    have: u8,
    /// Bytes of the RIFF payload not yet read, of the current chunk's
    /// payload, and of the current `ANMF` chunk's frame data.
    riff_left: u32,
    chunk_left: u32,
    anmf_left: u32,
    /// The current chunk has a padding byte after it.
    padded: bool,
    /// Inside the frame data of an `ANMF` chunk.
    in_anmf: bool,
    /// No chunk has been read yet.
    first_chunk: bool,
    /// An `ANIM` chunk was read.
    seen_anim: bool,
    anim: Animation,
    /// The current frame's bitstream was decoded into the frame buffer.
    have_image: bool,
    /// The frame being read (animations), and the last one completed.
    cur: FrameInfo,
    last: FrameInfo,
    has_frame: bool,
    frames: u32,
    vp8l: Vp8l,
}

impl Webp {
    /// The last completed frame's facts, if there is one. After
    /// `Status::FrameDone` it is that frame's.
    pub fn frame(&self) -> Option<&FrameInfo> {
        self.has_frame.then_some(&self.last)
    }

    /// The animation's global parameters, once its `ANIM` chunk was read.
    pub fn animation(&self) -> Option<&Animation> {
        self.seen_anim.then_some(&self.anim)
    }

    /// How many frames were completed.
    pub fn frames_done(&self) -> u32 {
        self.frames
    }

    fn fail(&mut self, e: Error) -> Error {
        self.phase = Phase::Spent;
        e
    }

    fn hold_at(&self, i: usize) -> u8 {
        self.hold.get(i).copied().unwrap_or(0)
    }

    fn u32_at(&self, i: usize) -> u32 {
        u32::from_le_bytes([
            self.hold_at(i),
            self.hold_at(i.saturating_add(1)),
            self.hold_at(i.saturating_add(2)),
            self.hold_at(i.saturating_add(3)),
        ])
    }

    /// A 24-bit little-endian value (section 2.7: `uint24`).
    fn u24_at(&self, i: usize) -> u32 {
        u32::from_le_bytes([
            self.hold_at(i),
            self.hold_at(i.saturating_add(1)),
            self.hold_at(i.saturating_add(2)),
            0,
        ])
    }

    /// Stores `b` in `hold`; true when `need` bytes are there (and `have`
    /// goes back to 0).
    fn gather(&mut self, b: u8, need: u8) -> bool {
        if let Some(slot) = self.hold.get_mut(usize::from(self.have)) {
            *slot = b;
        }
        self.have = self.have.saturating_add(1);
        if self.have >= need {
            self.have = 0;
            true
        } else {
            false
        }
    }

    /// The canvas size in pixels.
    fn canvas(&self) -> (u32, u32) {
        (self.config.width(), self.config.height())
    }

    /// One byte of the stream.
    pub(crate) fn byte(&mut self, b: u8, parts: &mut Parts<'_>) -> Result<Event, Error> {
        if self.phase == Phase::Riff {
            // Section 2.4: `RIFF`, the file size ("starting at offset 8",
            // so counting `WEBP`), `WEBP`.
            if self.gather(b, 12) {
                if self.hold.get(..4) != Some(b"RIFF") || self.hold.get(8..12) != Some(b"WEBP") {
                    return Err(bad("not a RIFF WEBP file"));
                }
                self.riff_left = self
                    .u32_at(4)
                    .checked_sub(4)
                    .ok_or(bad("a RIFF size too small to hold WEBP"))?;
                if self.riff_left == 0 {
                    return Err(bad("a WebP file with no chunks"));
                }
                self.phase = Phase::ChunkHdr;
            }
            return Ok(Event::Continue);
        }
        self.riff_left = self
            .riff_left
            .checked_sub(1)
            .ok_or(bad("bytes past the end of the RIFF data"))?;
        if self.in_anmf {
            self.anmf_left = self
                .anmf_left
                .checked_sub(1)
                .ok_or(bad("bytes past the end of the frame data"))?;
        }
        let event = self.dispatch(b, parts)?;
        if self.riff_left == 0 {
            // The RIFF data is used up (section 2.4: trailing data is
            // ignored).
            return match event {
                Event::Frame => {
                    self.phase = Phase::Ended;
                    Ok(Event::Frame)
                }
                _ if self.frames == 0 => Err(bad("a WebP file with no image data")),
                _ => {
                    self.phase = Phase::Ended;
                    Ok(Event::End)
                }
            };
        }
        Ok(event)
    }

    fn dispatch(&mut self, b: u8, parts: &mut Parts<'_>) -> Result<Event, Error> {
        match self.phase {
            Phase::ChunkHdr => {
                if self.gather(b, 8) {
                    return self.chunk_header(parts);
                }
                Ok(Event::Continue)
            }
            Phase::Pad => self.sub_done(parts),
            Phase::Vp8x | Phase::Anim | Phase::Anmf | Phase::Payload | Phase::Skip => {
                self.chunk_left = self
                    .chunk_left
                    .checked_sub(1)
                    .ok_or(bad("bytes past the end of a chunk"))?;
                let phase = self.phase;
                match phase {
                    Phase::Payload => return self.payload_byte(b, parts),
                    Phase::Vp8x => {
                        if self.gather(b, 10) {
                            self.on_vp8x(parts)?;
                        }
                    }
                    Phase::Anim => {
                        if self.gather(b, 6) {
                            self.on_anim();
                        }
                    }
                    Phase::Anmf if self.gather(b, 16) => return self.on_anmf(),
                    _ => {}
                }
                if self.chunk_left == 0 {
                    return self.chunk_end(parts);
                }
                // The rest of a gathered payload is skipped.
                if matches!(self.phase, Phase::Vp8x | Phase::Anim) && self.have == 0 {
                    self.phase = Phase::Skip;
                }
                Ok(Event::Continue)
            }
            Phase::Riff | Phase::Ended | Phase::Spent => Err(bad("a byte in a finished decoder")),
        }
    }

    /// A chunk header is complete (section 2.3: FourCC, size).
    fn chunk_header(&mut self, parts: &mut Parts<'_>) -> Result<Event, Error> {
        let size = self.u32_at(4);
        let mut fourcc = [0u8; 4];
        for (i, f) in fourcc.iter_mut().enumerate() {
            *f = self.hold_at(i);
        }
        // The payload and its padding byte must fit in what contains the
        // chunk (the RIFF data, or an ANMF chunk's frame data).
        let total = size
            .checked_add(size & 1)
            .ok_or(bad("a chunk size overflow"))?;
        let limit = if self.in_anmf {
            self.anmf_left
        } else {
            self.riff_left
        };
        if total > limit {
            return Err(bad("a chunk that extends past what contains it"));
        }
        self.chunk_left = size;
        self.padded = size & 1 == 1;
        let first = self.first_chunk;
        self.first_chunk = false;
        // Section 2.7: "'VP8X' ... MUST appear in the order described".
        match &fourcc {
            b"VP8X" => {
                if !first {
                    return Err(bad("a VP8X chunk that is not the first chunk"));
                }
                if size < 10 {
                    return Err(bad("a VP8X chunk of under 10 bytes"));
                }
                self.phase = Phase::Vp8x;
                return Ok(Event::Continue);
            }
            _ if first && self.animated => {
                return Err(bad("an animation whose first chunk is not VP8X"));
            }
            b"VP8L" | b"VP8 " if first => {}
            _ if first => return Err(bad("the first chunk is not VP8X, VP8 or VP8L")),
            _ => {}
        }
        match &fourcc {
            // Sections 2.5 and 2.6; lossy decoding is item 6.9.
            b"VP8 " if self.animated && !self.in_anmf => {
                Err(bad("image data outside a frame in an animation"))
            }
            b"VP8 " => Err(Error::Unsupported(
                "lossy WebP (a VP8 chunk): decoding it is item 6.9",
            )),
            b"VP8L" if self.animated && !self.in_anmf => {
                Err(bad("image data outside a frame in an animation"))
            }
            b"VP8L" => {
                if self.have_image {
                    return Err(bad("two bitstreams in one frame"));
                }
                if size == 0 {
                    return Err(bad("an empty VP8L chunk"));
                }
                let (w, h) = if self.animated {
                    (self.cur.width, self.cur.height)
                } else {
                    self.canvas()
                };
                self.vp8l = Vp8l::new(w, h);
                self.phase = Phase::Payload;
                Ok(Event::Continue)
            }
            // Section 2.7.1.1: `ANIM` "MUST appear if the Animation flag is
            // set"; "If the Animation flag is not set and this chunk is
            // present, it MUST be ignored".
            b"ANIM" if self.animated && !self.in_anmf => {
                if size < 6 {
                    return Err(bad("an ANIM chunk of under 6 bytes"));
                }
                self.phase = Phase::Anim;
                Ok(Event::Continue)
            }
            b"ANMF" if self.animated && !self.in_anmf => {
                if !self.seen_anim {
                    return Err(bad("an ANMF chunk before the ANIM chunk"));
                }
                // The frame data is padded chunks, so an ANMF chunk's size
                // is even (section 2.7.1.1's note); 16 is the header.
                if size < 16 || size & 1 == 1 {
                    return Err(bad("an ANMF chunk that is odd or under 16 bytes"));
                }
                self.phase = Phase::Anmf;
                Ok(Event::Continue)
            }
            // `ALPH`, `ICCP`, `EXIF`, `XMP ` and unknown chunks are skipped
            // (sections 2.7.1.2 to 2.7.1.6); `ALPH` belongs to `VP8 `
            // (item 6.9) and "A frame containing a 'VP8L' Chunk SHOULD NOT
            // contain this chunk".
            _ => {
                if self.animated && !self.in_anmf && &fourcc == b"ALPH" {
                    return Err(bad("an ALPH chunk outside a frame in an animation"));
                }
                self.phase = Phase::Skip;
                if self.chunk_left == 0 {
                    // Nothing to skip: the chunk is over (an empty chunk has
                    // no padding byte).
                    self.padded = false;
                    return self.sub_done(parts);
                }
                Ok(Event::Continue)
            }
        }
    }

    /// The `VP8X` payload's first 10 bytes are in (section 2.7, Figure 7):
    /// flags, 3 reserved bytes, canvas width and height minus one.
    fn on_vp8x(&mut self, parts: &mut Parts<'_>) -> Result<(), Error> {
        let flags = self.hold_at(0);
        let animation = flags & 0x02 != 0;
        let w = self.u24_at(4).saturating_add(1);
        let h = self.u24_at(7).saturating_add(1);
        if (w, h) != self.canvas() {
            return Err(bad("the VP8X canvas is not the size the config says"));
        }
        if animation != self.animated {
            return Err(bad("the VP8X animation flag is not what the config says"));
        }
        if self.animated {
            // The canvas starts transparent black (listed choice).
            parts.pixels.fill(0);
        }
        Ok(())
    }

    /// The `ANIM` payload's first 6 bytes (section 2.7.1.1, Figure 8).
    fn on_anim(&mut self) {
        self.anim = Animation {
            background: [
                self.hold_at(2),
                self.hold_at(1),
                self.hold_at(0),
                self.hold_at(3),
            ],
            loops: u16::from_le_bytes([self.hold_at(4), self.hold_at(5)]),
        };
        self.seen_anim = true;
    }

    /// The `ANMF` payload's first 16 bytes (section 2.7.1.1, Figure 9).
    fn on_anmf(&mut self) -> Result<Event, Error> {
        let left = self.u24_at(0).saturating_mul(2);
        let top = self.u24_at(3).saturating_mul(2);
        let width = self.u24_at(6).saturating_add(1);
        let height = self.u24_at(9).saturating_add(1);
        let flags = self.hold_at(15);
        let (cw, ch) = self.canvas();
        // Section 2.7.2: "VP8X.canvasWidth >= frame_right MUST be TRUE".
        if left.saturating_add(width) > cw || top.saturating_add(height) > ch {
            return Err(bad("a frame that extends past the canvas"));
        }
        self.cur = FrameInfo {
            left,
            top,
            width,
            height,
            duration_ms: self.u24_at(12),
            blend: if flags & 2 != 0 {
                Blend::Overwrite
            } else {
                Blend::Alpha
            },
            dispose: if flags & 1 != 0 {
                Dispose::Background
            } else {
                Dispose::None
            },
        };
        self.have_image = false;
        self.in_anmf = true;
        self.anmf_left = self.chunk_left;
        self.chunk_left = 0;
        self.padded = false;
        self.phase = Phase::ChunkHdr;
        if self.anmf_left == 0 {
            return Err(bad("a frame with no image data"));
        }
        Ok(Event::Continue)
    }

    /// One byte of a `VP8L` payload.
    fn payload_byte(&mut self, b: u8, parts: &mut Parts<'_>) -> Result<Event, Error> {
        let last = self.chunk_left == 0;
        self.vp8l.push(b, last);
        let done = if self.animated {
            let bytes = usize::try_from(self.cur.width)
                .ok()
                .and_then(|w| w.checked_mul(usize::try_from(self.cur.height).ok()?))
                .and_then(|n| n.checked_mul(4))
                .ok_or(bad("a frame size overflow"))?;
            let target = parts
                .frame
                .get_mut(..bytes)
                .ok_or(bad("a frame larger than the canvas"))?;
            self.vp8l.advance(&mut parts.scratch, target)?
        } else {
            self.vp8l.advance(&mut parts.scratch, &mut *parts.pixels)?
        };
        if !done {
            if last {
                return Err(bad("the VP8L data ends before the image is complete"));
            }
            return Ok(Event::Continue);
        }
        if !self.animated {
            // A still image: its frame is the canvas.
            let (width, height) = self.canvas();
            self.last = FrameInfo {
                left: 0,
                top: 0,
                width,
                height,
                duration_ms: 0,
                blend: Blend::Overwrite,
                dispose: Dispose::None,
            };
            self.has_frame = true;
            self.frames = 1;
            self.phase = Phase::Ended;
            return Ok(Event::Frame);
        }
        self.have_image = true;
        if self.chunk_left == 0 {
            self.chunk_end(parts)
        } else {
            self.phase = Phase::Skip;
            Ok(Event::Continue)
        }
    }

    /// A chunk's payload is used up: its padding byte, or what is next.
    fn chunk_end(&mut self, parts: &mut Parts<'_>) -> Result<Event, Error> {
        if self.padded {
            self.padded = false;
            self.phase = Phase::Pad;
            Ok(Event::Continue)
        } else {
            self.sub_done(parts)
        }
    }

    /// A chunk with its padding is used up: the next chunk header, or the
    /// end of a frame.
    fn sub_done(&mut self, parts: &mut Parts<'_>) -> Result<Event, Error> {
        self.phase = Phase::ChunkHdr;
        if self.in_anmf && self.anmf_left == 0 {
            return self.finish_frame(parts);
        }
        Ok(Event::Continue)
    }

    /// The frame data of an `ANMF` chunk is used up: dispose of the previous
    /// frame, then draw this one (section 2.7.2: "Before rendering each
    /// frame, the previous frame's Disposal method is applied").
    fn finish_frame(&mut self, parts: &mut Parts<'_>) -> Result<Event, Error> {
        if !self.have_image {
            return Err(bad("a frame with no image data"));
        }
        let (cw, _) = self.canvas();
        let cw = usize::try_from(cw).map_err(|_| bad("a canvas width overflow"))?;
        if self.has_frame && self.last.dispose == Dispose::Background {
            let f = self.last;
            for row in 0..usize::try_from(f.height).unwrap_or(0) {
                if let Some(span) = row_span(f.left, f.top, f.width, row, cw)
                    && let Some(px) = parts.pixels.get_mut(span)
                {
                    px.fill(0);
                }
            }
        }
        let f = self.cur;
        let fw = usize::try_from(f.width).map_err(|_| bad("a frame width overflow"))?;
        for row in 0..usize::try_from(f.height).unwrap_or(0) {
            let src = fw
                .checked_mul(row)
                .and_then(|o| o.checked_mul(4))
                .and_then(|o| parts.frame.get(o..o.checked_add(fw.checked_mul(4)?)?));
            let dst = row_span(f.left, f.top, f.width, row, cw)
                .and_then(|span| parts.pixels.get_mut(span));
            let (Some(src), Some(dst)) = (src, dst) else {
                return Err(bad("a frame row outside the buffers"));
            };
            match f.blend {
                Blend::Overwrite => dst.copy_from_slice(src),
                Blend::Alpha => blend_row(dst, src),
            }
        }
        self.last = f;
        self.has_frame = true;
        self.frames = self.frames.saturating_add(1);
        self.have_image = false;
        self.in_anmf = false;
        Ok(Event::Frame)
    }

    /// The invariant of the parts of the state that index.
    fn state_inv(&self, groups: usize) -> bool {
        let (cw, ch) = self.canvas();
        self.phase == Phase::Spent
            || (self.have <= 16
                && self.chunk_left.saturating_add(u32::from(self.padded))
                    <= if self.in_anmf {
                        self.anmf_left
                    } else {
                        self.riff_left
                    }
                && (!self.in_anmf || self.anmf_left <= self.riff_left)
                && self.cur.left.saturating_add(self.cur.width) <= cw
                && self.cur.top.saturating_add(self.cur.height) <= ch
                && self.last.left.saturating_add(self.last.width) <= cw
                && self.last.top.saturating_add(self.last.height) <= ch
                && self.vp8l.inv(groups))
    }
}

/// The byte range of row `row` of a frame at (`left`, `top`) of `width`
/// pixels in a canvas `cw` pixels wide.
fn row_span(
    left: u32,
    top: u32,
    width: u32,
    row: usize,
    cw: usize,
) -> Option<std::ops::Range<usize>> {
    let y = usize::try_from(top).ok()?.checked_add(row)?;
    let start = y
        .checked_mul(cw)?
        .checked_add(usize::try_from(left).ok()?)?
        .checked_mul(4)?;
    let end = start.checked_add(usize::try_from(width).ok()?.checked_mul(4)?)?;
    Some(start..end)
}

/// Whether `prefix` (the first bytes of a file) agrees with `want` at `at`:
/// `Ok(true)` if all of `want` is there and equal, `Ok(false)` if the prefix
/// ends first, an error if a byte differs.
fn matches_at(prefix: &[u8], at: usize, want: &[u8]) -> Result<bool, Error> {
    for (i, w) in want.iter().enumerate() {
        match prefix.get(at.saturating_add(i)) {
            Some(b) if b == w => {}
            Some(_) => return Err(bad("not a WebP file")),
            None => return Ok(false),
        }
    }
    Ok(true)
}

/// A little-endian `u16` of `prefix` at `at`, if it is there.
fn le16(prefix: &[u8], at: usize) -> Option<u16> {
    prefix
        .get(at..)?
        .first_chunk::<2>()
        .copied()
        .map(u16::from_le_bytes)
}

/// A 24-bit little-endian value of `prefix` at `at`, if it is there.
fn le24(prefix: &[u8], at: usize) -> Option<u32> {
    let [a, b, c] = *prefix.get(at..)?.first_chunk::<3>()?;
    Some(u32::from_le_bytes([a, b, c, 0]))
}

impl Decoder for Webp {
    fn decode_config(prefix: &[u8]) -> Result<ConfigStatus, Error> {
        // Section 2.4: `RIFF`, 4 bytes of size, `WEBP`; section 2.3: the
        // first chunk's FourCC and size.
        let more = Ok(ConfigStatus::NeedMore);
        if !matches_at(prefix, 0, b"RIFF")? | !matches_at(prefix, 8, b"WEBP")? {
            return more;
        }
        // The first chunk is `VP8X`, `VP8L` or `VP8 ` (section 2.5 to 2.7):
        // all begin `VP8`.
        if !matches_at(prefix, 12, b"VP8")? {
            return more;
        }
        let Some(&kind) = prefix.get(15) else {
            return more;
        };
        let Some(size) = prefix
            .get(16..)
            .and_then(|s| s.first_chunk::<4>())
            .copied()
            .map(u32::from_le_bytes)
        else {
            return more;
        };
        let ready = |w: u32, h: u32, frames: FrameCount| -> Result<ConfigStatus, Error> {
            Ok(ConfigStatus::Ready(Config::new(
                Format::Webp,
                w,
                h,
                frames,
            )?))
        };
        match kind {
            // Section 2.7, Figure 7: flags, 3 reserved bytes, canvas width
            // and height minus one, 24 bits each.
            b'X' => {
                if size < 10 {
                    return Err(bad("a VP8X chunk of under 10 bytes"));
                }
                let (Some(flags), Some(w), Some(h)) =
                    (prefix.get(20).copied(), le24(prefix, 24), le24(prefix, 27))
                else {
                    return more;
                };
                let frames = if flags & 0x02 != 0 {
                    FrameCount::Unknown
                } else {
                    FrameCount::Known(1)
                };
                ready(w.saturating_add(1), h.saturating_add(1), frames)
            }
            // Section 3.4: the signature 0x2f, then 14 bits of width minus
            // one and 14 of height minus one, 1 of alpha, 3 of version.
            b'L' => {
                if let Some(&sig) = prefix.get(20)
                    && sig != 0x2F
                {
                    return Err(bad("the VP8L signature byte is not 0x2f"));
                }
                let Some(b) = prefix.get(21..).and_then(|s| s.first_chunk::<4>()) else {
                    return more;
                };
                let v = u32::from_le_bytes(*b);
                if v >> 29 != 0 {
                    return Err(bad("a VP8L version other than 0"));
                }
                ready(
                    (v & 0x3FFF).saturating_add(1),
                    ((v >> 14) & 0x3FFF).saturating_add(1),
                    FrameCount::Known(1),
                )
            }
            // RFC 6386 section 9.1: a 3-byte frame tag (bit 0 clear is a key
            // frame), the start code 9d 01 2a, then 14 bits of width and 14
            // of height (the top two bits of each are a scale).
            b' ' => {
                if let Some(&tag) = prefix.get(20)
                    && tag & 1 != 0
                {
                    return Err(bad("a VP8 frame that is not a key frame"));
                }
                if !matches_at(prefix, 23, &[0x9D, 0x01, 0x2A])? {
                    return more;
                }
                let (Some(w), Some(h)) = (le16(prefix, 26), le16(prefix, 28)) else {
                    return more;
                };
                ready(
                    u32::from(w & 0x3FFF),
                    u32::from(h & 0x3FFF),
                    FrameCount::Known(1),
                )
            }
            _ => Err(bad("the first chunk is not VP8X, VP8 or VP8L")),
        }
    }

    fn work_len(config: &Config) -> Result<usize, Error> {
        let animated = matches!(config.frames(), FrameCount::Unknown);
        work_len(config.width(), config.height(), animated).ok_or(bad("work buffer size overflow"))
    }

    fn start(config: &Config) -> Result<Webp, Error> {
        if config.format() != Format::Webp {
            return Err(Error::Unsupported("not a WebP config"));
        }
        config.rgba_len()?;
        let blank = FrameInfo {
            left: 0,
            top: 0,
            width: 0,
            height: 0,
            duration_ms: 0,
            blend: Blend::Overwrite,
            dispose: Dispose::None,
        };
        Ok(Webp {
            config: *config,
            animated: matches!(config.frames(), FrameCount::Unknown),
            phase: Phase::Riff,
            hold: [0; 16],
            have: 0,
            riff_left: 0,
            chunk_left: 0,
            anmf_left: 0,
            padded: false,
            in_anmf: false,
            first_chunk: true,
            seen_anim: false,
            anim: Animation {
                background: [0; 4],
                loops: 0,
            },
            have_image: false,
            cur: blank,
            last: blank,
            has_frame: false,
            frames: 0,
            vp8l: Vp8l::new(0, 0),
        })
    }

    fn config(&self) -> &Config {
        &self.config
    }

    fn step(&mut self, chunk: &[u8], buffers: &mut Buffers<'_>) -> Result<Step, Error> {
        match self.phase {
            Phase::Spent => return Err(Error::Spent),
            Phase::Ended => return Err(Error::NoMoreFrames),
            _ => {}
        }
        let (cw, ch) = self.canvas();
        let Some(mut parts) = Parts::new(
            &mut *buffers.pixels,
            &mut *buffers.work,
            cw,
            ch,
            self.animated,
        ) else {
            return Err(self.fail(Error::Buffers));
        };
        for (i, &b) in chunk.iter().enumerate() {
            match self.byte(b, &mut parts) {
                Ok(Event::Continue) => {}
                Ok(Event::Frame) => {
                    return Ok(Step {
                        consumed: i.saturating_add(1),
                        status: Status::FrameDone,
                    });
                }
                Ok(Event::End) => return Err(Error::NoMoreFrames),
                Err(e) => return Err(self.fail(e)),
            }
        }
        Ok(Step {
            consumed: chunk.len(),
            status: Status::NeedMore,
        })
    }

    fn inv(&self, buffers: &Buffers<'_>) -> bool {
        let Ok(plen) = self.config.rgba_len() else {
            return false;
        };
        let Some(wlen) = work_len(self.config.width(), self.config.height(), self.animated) else {
            return false;
        };
        let groups = crate::work::group_cap(self.config.width(), self.config.height())
            .and_then(|c| c.checked_mul(crate::work::GROUP_BYTES))
            .unwrap_or(0);
        buffers.pixels.len() == plen && buffers.work.len() == wlen && self.state_inv(groups)
    }
}

/// Any state of a decoder of a 2 by 2 canvas in `phase`, which is not the
/// lossless payload (that is `vp8l.rs`'s harnesses), every other field
/// symbolic: the harness assumes `inv` on top. One phase per harness: with
/// the phase symbolic too, CBMC ran out of memory (over 4 GB).
#[cfg(kani)]
pub(crate) fn any_webp(phase: Phase) -> Option<Webp> {
    let frames = if kani::any() {
        FrameCount::Unknown
    } else {
        FrameCount::Known(1)
    };
    let config = Config::new(Format::Webp, 2, 2, frames).ok()?;
    let mut w = Webp::start(&config).ok()?;
    w.phase = phase;
    w.hold = kani::any();
    w.have = kani::any();
    w.riff_left = kani::any();
    w.chunk_left = kani::any();
    w.anmf_left = kani::any();
    w.padded = kani::any();
    w.in_anmf = kani::any();
    w.first_chunk = kani::any();
    w.seen_anim = kani::any();
    w.have_image = kani::any();
    w.has_frame = kani::any();
    w.frames = kani::any();
    let any_frame = || FrameInfo {
        left: kani::any(),
        top: kani::any(),
        width: kani::any(),
        height: kani::any(),
        duration_ms: kani::any(),
        blend: if kani::any() {
            Blend::Alpha
        } else {
            Blend::Overwrite
        },
        dispose: if kani::any() {
            Dispose::Background
        } else {
            Dispose::None
        },
    };
    w.cur = any_frame();
    w.last = any_frame();
    Some(w)
}

#[cfg(kani)]
impl Webp {
    /// The file is an animation (for the harnesses).
    pub(crate) fn kani_animated(&self) -> bool {
        self.animated
    }

    /// The invariant of the state (for the harnesses).
    pub(crate) fn kani_inv(&self, groups: usize) -> bool {
        self.state_inv(groups)
    }
}

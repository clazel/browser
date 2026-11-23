//! The PNG decoder: a state machine over the chunks of a datastream (PNG 3rd
//! edition, 5 "Datastream structure"), implementing
//! [`clazel_image_shape::Decoder`].
//!
//! Citations are to the PNG Specification, Third Edition, by section, as in
//! `lib.rs`'s header; the listed choices are there too.
//!
//! # Shape
//!
//! `step` feeds the chunk to [`Png::advance`] until it is used up, a frame is
//! complete or the stream ends. `advance` does one phase's work on the front of
//! the input and uses **at least one byte** of a non-empty input. The phases
//! are the signature (5.2), a chunk's length and type (5.3), its data (kept,
//! skipped, or run through the zlib engine) and its CRC (5.3, 5.5).
//!
//! Image data (IDAT, fdAT) is the zlib stream of the scanlines (10): the
//! engine writes straight into the scanline buffer `cur`; a full scanline is
//! unfiltered (9), converted to RGBA (6, 13.12, 13.16) pixel by pixel and
//! blended into the canvas (4.9, 11.3.6), which is the pixel buffer.

use clazel_image_shape::{
    Buffers, Config, ConfigStatus, Decoder, Error, Format, FrameCount, Status, Step,
};

use crate::adam7;
use crate::crc;
use crate::engine::Engine;
use crate::pixel::{ColorType, Layout, Trns};
use crate::work::{self, Parts};

mod image;

/// 5.2: the eight bytes every PNG datastream starts with.
const SIGNATURE: [u8; 8] = [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A];

/// 11.2.1: the data of IHDR is 13 bytes.
const IHDR_LEN: u32 = 13;

/// 11.3.6.2: the data of fcTL is 26 bytes.
const FCTL_LEN: u32 = 26;

/// The most a gathered chunk holds: fcTL.
const HOLD: usize = 26;

/// 5.3: "the length ... shall not exceed 2^31 - 1".
const MAX_CHUNK: u32 = 0x7FFF_FFFF;

/// 11.3.6.3: what to do with the frame's region of the output buffer before
/// the next frame is drawn (`dispose_op`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dispose {
    /// 0, `APNG_DISPOSE_OP_NONE`: leave it.
    None,
    /// 1, `APNG_DISPOSE_OP_BACKGROUND`: clear it to fully transparent black.
    Background,
    /// 2, `APNG_DISPOSE_OP_PREVIOUS`: restore what it held before the frame.
    Previous,
}

/// 11.3.6.3: how a frame is combined with the output buffer (`blend_op`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Blend {
    /// 0, `APNG_BLEND_OP_SOURCE`: the frame overwrites its region.
    Source,
    /// 1, `APNG_BLEND_OP_OVER`: the frame is composited over it by alpha.
    Over,
}

/// The facts of a frame: the `fcTL` chunk's (11.3.6.2), or for an image with
/// none, the whole canvas. Read after [`Status::FrameDone`] with
/// [`Png::frame`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrameInfo {
    /// Column of the frame's left edge on the canvas.
    pub x: u32,
    /// Row of the frame's top edge on the canvas.
    pub y: u32,
    /// Width of the frame in pixels (1 to the canvas's, with `x`).
    pub width: u32,
    /// Height of the frame in pixels.
    pub height: u32,
    /// Numerator of the frame's delay in seconds (`delay_num`).
    pub delay_num: u16,
    /// Denominator of the delay; 0 means 100 (11.3.6.2).
    pub delay_den: u16,
    /// What happens to the frame's region before the next frame.
    pub dispose: Dispose,
    /// How the frame is combined with the canvas.
    pub blend: Blend,
    /// The frame is one of the animation's (it has an `fcTL`); false for an
    /// image with no animation, and for the default image of an APNG that
    /// is not part of its animation (4.9.1).
    pub animated: bool,
}

/// What `acTL` says (11.3.6.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Animation {
    /// `num_frames`: the frames of the animation (at least 1).
    pub frames: u32,
    /// `num_plays`: how often it plays, 0 for forever.
    pub plays: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// The 8 signature bytes, gathered.
    Signature,
    /// A chunk's length and type, 8 bytes, gathered.
    Header,
    /// `need` bytes of a chunk's data kept in `hold`.
    Gather,
    /// A chunk's data used for nothing.
    Skip,
    /// PLTE's data, into the palette.
    Palette,
    /// A palette image's tRNS data, into the palette's alphas.
    Trns,
    /// IDAT's or fdAT's image data.
    Data,
    /// A chunk's 4 CRC bytes, gathered.
    Crc,
    /// IEND was read: no more frames.
    Ended,
    /// An error happened.
    Spent,
}

/// The chunks that mean something here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Ihdr,
    Plte,
    Trns,
    Idat,
    Iend,
    Actl,
    Fctl,
    Fdat,
    /// Anything else: an ancillary chunk read and ignored (an unknown
    /// critical one is refused at its header).
    Other,
}

/// Whether the IDAT chunks have begun (they must be consecutive, 5.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Idat {
    NotYet,
    Open,
    Closed,
}

/// Where the current frame's image data is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Stage {
    /// No frame's data has begun.
    Idle,
    /// Scanlines are being received.
    Active,
    /// The frame is complete; more data chunks of it are skipped.
    Finished,
}

/// What one `advance` did besides using bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Event {
    Continue,
    Frame,
    End,
}

/// The PNG decoder's state: fixed-size, no allocation.
pub struct Png<E: Engine = clazel_deflate::stream::Inflater> {
    config: Config,
    phase: Phase,
    // The chunk being read.
    kind: Kind,
    len: u32,
    at: u32,
    crc: u32,
    hold: [u8; HOLD],
    have: u8,
    need: u8,
    // What IHDR, PLTE, tRNS and acTL said.
    header_done: bool,
    layout: Layout,
    interlaced: bool,
    trns: Trns,
    palette_len: u16,
    seen_plte: bool,
    seen_trns: bool,
    idat: Idat,
    animation: Option<Animation>,
    next_seq: u32,
    fctl_seen: u32,
    pending: Option<FrameInfo>,
    // The frame being decoded.
    frame: FrameInfo,
    has_frame: bool,
    stage: Stage,
    /// The kind of chunk (IDAT or fdAT) the current frame's data is in.
    data_kind: Kind,
    report: bool,
    engine: E,
    pass: u8,
    row: u32,
    row_have: u32,
    pass_w: u32,
    pass_h: u32,
    row_len: u32,
    rows_done: bool,
    // The canvas between frames.
    frames_done: u32,
    anim_begun: u32,
    default_hidden: bool,
    prev_dispose: Dispose,
    prev_rect: (u32, u32, u32, u32),
}

fn bad(why: &'static str) -> Error {
    Error::Malformed(why)
}

/// The big-endian `u32` at `at` of `bytes` (7.1), 0 past the end.
fn be32(bytes: &[u8], at: usize) -> u32 {
    bytes
        .get(at..at.saturating_add(4))
        .and_then(|s| <[u8; 4]>::try_from(s).ok())
        .map_or(0, u32::from_be_bytes)
}

/// The big-endian `u16` at `at` of `bytes`, 0 past the end.
fn be16(bytes: &[u8], at: usize) -> u16 {
    bytes
        .get(at..at.saturating_add(2))
        .and_then(|s| <[u8; 2]>::try_from(s).ok())
        .map_or(0, u16::from_be_bytes)
}

/// 5.3 and 5.4: the kind of a chunk type.
fn classify(t: [u8; 4]) -> Kind {
    match &t {
        b"IHDR" => Kind::Ihdr,
        b"PLTE" => Kind::Plte,
        b"tRNS" => Kind::Trns,
        b"IDAT" => Kind::Idat,
        b"IEND" => Kind::Iend,
        b"acTL" => Kind::Actl,
        b"fcTL" => Kind::Fctl,
        b"fdAT" => Kind::Fdat,
        _ => Kind::Other,
    }
}

impl<E: Engine> Png<E> {
    /// The decoded frame's facts, once its data has begun (the one a
    /// [`Status::FrameDone`] is for).
    pub fn frame(&self) -> Option<&FrameInfo> {
        self.has_frame.then_some(&self.frame)
    }

    /// What `acTL` said, if it has been read.
    pub fn animation(&self) -> Option<Animation> {
        self.animation
    }

    /// Poisons the decoder and says why.
    fn fail(&mut self, e: Error) -> Error {
        self.phase = Phase::Spent;
        e
    }

    fn canvas_width(&self) -> u32 {
        self.config.width()
    }

    fn canvas_height(&self) -> u32 {
        self.config.height()
    }

    fn hold_at(&self, i: usize) -> u8 {
        self.hold.get(i).copied().unwrap_or(0)
    }

    /// Takes bytes of `input` into `hold` until `need` are held; returns how
    /// many it took.
    fn gather(&mut self, input: &[u8], need: u8) -> usize {
        let want = usize::from(need.saturating_sub(self.have));
        let n = want.min(input.len());
        for &b in input.get(..n).unwrap_or(&[]) {
            if let Some(slot) = self.hold.get_mut(usize::from(self.have)) {
                *slot = b;
            }
            self.have = self.have.saturating_add(1);
        }
        n
    }

    /// Starts a chunk of this length and type (just gathered in `hold`).
    fn chunk_start(&mut self) -> Result<(), Error> {
        let len = be32(&self.hold, 0);
        let t = [
            self.hold_at(4),
            self.hold_at(5),
            self.hold_at(6),
            self.hold_at(7),
        ];
        // 5.3: the length is at most 2^31 - 1; 5.4: the type is four ASCII
        // letters.
        if len > MAX_CHUNK {
            return Err(bad("chunk length over 2^31 - 1"));
        }
        if !t.iter().all(u8::is_ascii_alphabetic) {
            return Err(bad("chunk type is not four letters"));
        }
        self.crc = crc::update(crc::INIT, &t);
        self.len = len;
        self.at = 0;
        self.have = 0;
        let kind = classify(t);
        // 5.6: IHDR is the first chunk.
        let first = !self.has_header();
        if first && (kind != Kind::Ihdr || len != IHDR_LEN) {
            return Err(bad("the first chunk is not an IHDR of 13 bytes"));
        }
        // 5.6: the IDAT chunks are consecutive; and so are an image's fdATs.
        // Any other chunk ends the data of the frame (which must be complete).
        if kind != Kind::Idat && kind != Kind::Fdat {
            match self.stage {
                Stage::Active => return Err(bad("image data ended before the image")),
                Stage::Finished => self.stage = Stage::Idle,
                Stage::Idle => {}
            }
            if self.idat == Idat::Open {
                self.idat = Idat::Closed;
            }
        }
        self.kind = kind;
        let critical = t.first().is_some_and(|b| b & 0x20 == 0);
        let next = match kind {
            // 11.2.1: IHDR once, 13 bytes.
            Kind::Ihdr => {
                if !first {
                    return Err(bad("a second IHDR"));
                }
                self.gather_of(IHDR_LEN)
            }
            // 11.2.2: PLTE, 3 to 768 bytes, a multiple of 3, not for colour
            // types 0 and 4, once, before IDAT (and so before tRNS' use).
            Kind::Plte => {
                if self.seen_plte || self.idat != Idat::NotYet {
                    return Err(bad("PLTE twice or after the image data"));
                }
                if matches!(self.layout.color, ColorType::Gray | ColorType::GrayAlpha) {
                    return Err(bad("PLTE in a greyscale image"));
                }
                if len == 0 || len > 768 || !len.is_multiple_of(3) {
                    return Err(bad("PLTE length"));
                }
                self.seen_plte = true;
                // At most the palette's capacity (256, the most PLTE can
                // hold; the proofs use an engine with fewer): entries past it
                // are not stored.
                self.palette_len =
                    u16::try_from((len / 3).min(u32::try_from(E::PALETTE_ENTRIES).unwrap_or(0)))
                        .unwrap_or(0);
                if self.layout.color == ColorType::Indexed {
                    Phase::Palette
                } else {
                    // 11.2.2: a suggested palette of a truecolour image.
                    Phase::Skip
                }
            }
            // 11.3.1: tRNS once, before IDAT; not with an alpha channel.
            Kind::Trns => {
                if self.seen_trns || self.idat != Idat::NotYet {
                    return Err(bad("tRNS twice or after the image data"));
                }
                self.seen_trns = true;
                match self.layout.color {
                    // 11.3.1: 2 bytes for colour type 0, 6 for colour type 2.
                    ColorType::Gray if len == 2 => self.gather_of(2),
                    ColorType::Rgb if len == 6 => self.gather_of(6),
                    ColorType::Gray | ColorType::Rgb => {
                        return Err(bad("tRNS has the wrong length for the colour type"));
                    }
                    ColorType::Indexed => {
                        // 11.3.1: no more alpha values than palette entries,
                        // and after PLTE.
                        if !self.seen_plte || len > u32::from(self.palette_len) {
                            return Err(bad("tRNS before PLTE or longer than it"));
                        }
                        if len == 0 { Phase::Crc } else { Phase::Trns }
                    }
                    ColorType::GrayAlpha | ColorType::Rgba => {
                        return Err(bad("tRNS in an image with an alpha channel"));
                    }
                }
            }
            // 11.2.3: IDAT. A palette image needs its PLTE first (11.2.2).
            Kind::Idat => {
                if self.idat == Idat::Closed {
                    return Err(bad("IDAT chunks are not consecutive"));
                }
                if self.layout.color == ColorType::Indexed && !self.seen_plte {
                    return Err(bad("a palette image with no PLTE"));
                }
                self.idat = Idat::Open;
                if len == 0 { Phase::Crc } else { Phase::Data }
            }
            // 11.2.4: IEND is empty.
            Kind::Iend => {
                if len != 0 {
                    return Err(bad("IEND has data"));
                }
                Phase::Crc
            }
            // 11.3.6.1: acTL, 8 bytes, once, before IDAT.
            Kind::Actl => {
                if len != 8 || self.animation.is_some() || self.idat != Idat::NotYet {
                    return Err(bad("acTL: wrong length, twice, or after IDAT"));
                }
                self.gather_of(8)
            }
            // 11.3.6.2: fcTL, 26 bytes; without an acTL it is not part of an
            // animation and is skipped (listed choice).
            Kind::Fctl => {
                if self.animation.is_none() {
                    self.skip_or_crc()
                } else if len != FCTL_LEN {
                    return Err(bad("fcTL is not 26 bytes"));
                } else {
                    self.gather_of(FCTL_LEN)
                }
            }
            // 11.3.6.3: fdAT, a sequence number then image data; skipped
            // without an acTL, refused before the default image.
            Kind::Fdat => {
                if self.animation.is_none() {
                    self.skip_or_crc()
                } else if self.stage != Stage::Idle && self.data_kind != Kind::Fdat {
                    // 11.3.6.3: an fdAT follows an fcTL, not the default image's IDAT.
                    return Err(bad("fdAT in the data of the default image"));
                } else if self.idat == Idat::NotYet || len < 4 {
                    return Err(bad("fdAT before IDAT or shorter than 4 bytes"));
                } else {
                    self.gather_of(4)
                }
            }
            Kind::Other => {
                // 5.4 and 13.2: an unknown critical chunk is an error; every
                // ancillary one this decoder does not use is skipped, among
                // them gAMA, cHRM, iCCP, sRGB and cICP (listed).
                if critical {
                    return Err(Error::Unsupported("an unknown critical chunk"));
                }
                self.skip_or_crc()
            }
        };
        self.phase = next;
        Ok(())
    }

    /// The phase that gathers a chunk's `n` bytes, `n` at most 26.
    fn gather_of(&mut self, n: u32) -> Phase {
        self.need = u8::try_from(n).unwrap_or(0);
        Phase::Gather
    }

    fn skip_or_crc(&self) -> Phase {
        if self.len == 0 {
            Phase::Crc
        } else {
            Phase::Skip
        }
    }

    /// Whether IHDR has been read.
    fn has_header(&self) -> bool {
        self.header_done
    }

    /// A gathered chunk is complete: use what it said.
    fn gathered(&mut self, parts: &mut Parts<'_>) -> Result<(), Error> {
        match self.kind {
            Kind::Ihdr => self.read_ihdr(parts)?,
            Kind::Actl => {
                // 11.3.6.1: at least one frame (and at most 2^31 - 1).
                let frames = be32(&self.hold, 0);
                if frames == 0 || frames > MAX_CHUNK {
                    return Err(bad("acTL: num_frames is 0 or over 2^31 - 1"));
                }
                self.animation = Some(Animation {
                    frames,
                    plays: be32(&self.hold, 4),
                });
            }
            Kind::Fctl => self.read_fctl()?,
            Kind::Trns => {
                // 11.3.1 (listed in `pixel.rs`): below 16 bits the low byte.
                let value = |at: usize| {
                    let v = be16(&self.hold, at);
                    if self.layout.depth < 16 { v & 0xFF } else { v }
                };
                self.trns = match self.layout.color {
                    ColorType::Gray => Trns::Gray(value(0)),
                    _ => Trns::Rgb(value(0), value(2), value(4)),
                };
            }
            Kind::Fdat => {
                // 11.3.6.3 and 4.9.2: sequence numbers count from 0 over
                // fcTL and fdAT together, each one more than the last.
                if be32(&self.hold, 0) != self.next_seq {
                    return Err(bad("fdAT sequence number out of order"));
                }
                self.next_seq = self.next_seq.saturating_add(1);
            }
            _ => {}
        }
        self.have = 0;
        self.phase = if self.at >= self.len {
            Phase::Crc
        } else {
            Phase::Data
        };
        Ok(())
    }

    /// 11.2.1: IHDR's thirteen bytes.
    fn read_ihdr(&mut self, parts: &mut Parts<'_>) -> Result<(), Error> {
        let (w, h) = (be32(&self.hold, 0), be32(&self.hold, 4));
        let (depth, code, compression, filter, interlace) = (
            self.hold_at(8),
            self.hold_at(9),
            self.hold_at(10),
            self.hold_at(11),
            self.hold_at(12),
        );
        // The config came from the same bytes; the stream and it must agree.
        if w != self.canvas_width() || h != self.canvas_height() {
            return Err(bad("IHDR differs from the config"));
        }
        let color =
            ColorType::from_code(code).ok_or(bad("IHDR: colour type is not 0, 2, 3, 4 or 6"))?;
        // 11.2.1, Table 11.1.
        if !color.allows(depth) {
            return Err(bad("IHDR: bit depth not allowed for the colour type"));
        }
        // 11.2.1: compression method 0 (zlib) and filter method 0 only;
        // interlace method 0 (none) or 1 (Adam7).
        if compression != 0 || filter != 0 || interlace > 1 {
            return Err(bad("IHDR: unknown compression, filter or interlace method"));
        }
        self.layout = Layout { color, depth };
        self.interlaced = interlace == 1;
        self.header_done = true;
        // Every palette entry is opaque black until PLTE and tRNS say more
        // (the listed choice for an index past the entries).
        for (i, b) in parts.palette.iter_mut().enumerate() {
            *b = if i % 4 == 3 { 255 } else { 0 };
        }
        Ok(())
    }

    /// 11.3.6.2: fcTL's twenty-six bytes.
    fn read_fctl(&mut self) -> Result<(), Error> {
        let seq = be32(&self.hold, 0);
        let (width, height) = (be32(&self.hold, 4), be32(&self.hold, 8));
        let (x, y) = (be32(&self.hold, 12), be32(&self.hold, 16));
        let dispose = match self.hold_at(24) {
            0 => Dispose::None,
            1 => Dispose::Background,
            2 => Dispose::Previous,
            _ => return Err(bad("fcTL: dispose_op is not 0, 1 or 2")),
        };
        let blend = match self.hold_at(25) {
            0 => Blend::Source,
            1 => Blend::Over,
            _ => return Err(bad("fcTL: blend_op is not 0 or 1")),
        };
        if seq != self.next_seq {
            return Err(bad("fcTL sequence number out of order"));
        }
        self.next_seq = self.next_seq.saturating_add(1);
        // 11.3.6.2: the frame is at least 1 by 1 and inside the canvas.
        let right = x.checked_add(width);
        let bottom = y.checked_add(height);
        if width == 0
            || height == 0
            || right.is_none_or(|r| r > self.canvas_width())
            || bottom.is_none_or(|b| b > self.canvas_height())
        {
            return Err(bad("fcTL: the frame is empty or outside the canvas"));
        }
        // 11.3.6.2: the fcTL of the default image covers the whole canvas.
        if self.idat == Idat::NotYet
            && (x != 0 || y != 0 || width != self.canvas_width() || height != self.canvas_height())
        {
            return Err(bad("fcTL of the default image does not cover the canvas"));
        }
        // 11.3.6.1: no more frames than acTL says; one fcTL per frame.
        let frames = self.animation.map_or(0, |a| a.frames);
        self.fctl_seen = self.fctl_seen.saturating_add(1);
        if self.fctl_seen > frames || self.pending.is_some() {
            return Err(bad("fcTL: more frames than acTL says, or two in a row"));
        }
        self.pending = Some(FrameInfo {
            x,
            y,
            width,
            height,
            delay_num: be16(&self.hold, 20),
            delay_den: be16(&self.hold, 22),
            dispose,
            blend,
            animated: true,
        });
        Ok(())
    }

    /// A chunk's CRC is read: check it and finish the chunk.
    fn chunk_end(&mut self) -> Result<Event, Error> {
        // 5.5: the CRC of the type and data, 4 bytes.
        if be32(&self.hold, 0) != crc::finish(self.crc) {
            return Err(bad("a chunk's CRC does not match"));
        }
        self.have = 0;
        self.phase = Phase::Header;
        match self.kind {
            Kind::Iend => {
                // 11.2.4 and 5.6: IEND ends the datastream; the image must
                // have been complete, and no fcTL left without its data.
                if self.frames_done == 0 || self.pending.is_some() {
                    return Err(bad("IEND before the image data was complete"));
                }
                self.phase = Phase::Ended;
                Ok(Event::End)
            }
            Kind::Idat | Kind::Fdat if self.report => {
                // The frame's pixels are final, and the chunk that finished
                // them has had its CRC checked.
                self.report = false;
                self.frames_done = self.frames_done.saturating_add(1);
                Ok(Event::Frame)
            }
            _ => Ok(Event::Continue),
        }
    }

    /// One phase's work on the front of `input`; returns the bytes used
    /// (at least 1 if `input` is not empty) and what happened.
    pub(crate) fn advance(
        &mut self,
        input: &[u8],
        parts: &mut Parts<'_>,
    ) -> Result<(usize, Event), Error> {
        match self.phase {
            Phase::Signature => {
                // 5.2: the signature, checked byte by byte.
                let mut used = 0usize;
                for &b in input {
                    let expect = SIGNATURE.get(usize::from(self.have)).copied();
                    if Some(b) != expect {
                        return Err(bad("not a PNG signature"));
                    }
                    used = used.saturating_add(1);
                    self.have = self.have.saturating_add(1);
                    if usize::from(self.have) >= SIGNATURE.len() {
                        self.have = 0;
                        self.phase = Phase::Header;
                        break;
                    }
                }
                Ok((used, Event::Continue))
            }
            Phase::Header => {
                let n = self.gather(input, 8);
                if self.have >= 8 {
                    self.chunk_start()?;
                }
                Ok((n, Event::Continue))
            }
            Phase::Gather => {
                let n = self.gather(input, self.need);
                self.crc = crc::update(self.crc, input.get(..n).unwrap_or(&[]));
                self.at = self.at.saturating_add(u32::try_from(n).unwrap_or(0));
                if self.have >= self.need {
                    self.gathered(parts)?;
                }
                Ok((n, Event::Continue))
            }
            Phase::Skip | Phase::Palette | Phase::Trns | Phase::Data => {
                let left = usize::try_from(self.len.saturating_sub(self.at)).unwrap_or(0);
                let n = left.min(input.len());
                let part = input.get(..n).unwrap_or(&[]);
                self.crc = crc::update(self.crc, part);
                match self.phase {
                    Phase::Palette => self.palette_bytes(part, parts, false),
                    Phase::Trns => self.palette_bytes(part, parts, true),
                    Phase::Data => self.image_bytes(part, parts)?,
                    _ => {}
                }
                self.at = self.at.saturating_add(u32::try_from(n).unwrap_or(0));
                if self.at >= self.len {
                    self.phase = Phase::Crc;
                    self.have = 0;
                }
                Ok((n, Event::Continue))
            }
            Phase::Crc => {
                let n = self.gather(input, 4);
                if self.have >= 4 {
                    let ev = self.chunk_end()?;
                    return Ok((n, ev));
                }
                Ok((n, Event::Continue))
            }
            Phase::Ended => Err(Error::NoMoreFrames),
            Phase::Spent => Err(Error::Spent),
        }
    }

    /// 11.2.2 and 11.3.1: bytes of PLTE (three per entry: R, G, B) or of a
    /// palette image's tRNS (one alpha per entry) into the palette, where
    /// entry `i` is at `4 * i`.
    fn palette_bytes(&mut self, part: &[u8], parts: &mut Parts<'_>, alpha: bool) {
        let mut at = usize::try_from(self.at).unwrap_or(usize::MAX);
        for &b in part {
            let (entry, channel) = if alpha { (at, 3) } else { (at / 3, at % 3) };
            let slot = entry.saturating_mul(4).saturating_add(channel);
            if let Some(s) = parts.palette.get_mut(slot) {
                *s = b;
            }
            at = at.saturating_add(1);
        }
    }

    /// The invariant of the state alone (the buffers' lengths are
    /// [`Decoder::inv`]'s). What `step` needs so that every index and
    /// counter is in range; `Phase::Spent` and `Phase::Ended` need nothing.
    pub(crate) fn state_inv(&self) -> bool {
        let (w, h) = (self.canvas_width(), self.canvas_height());
        let inside = |x: u32, y: u32, fw: u32, fh: u32| {
            x.checked_add(fw).is_some_and(|r| r <= w) && y.checked_add(fh).is_some_and(|b| b <= h)
        };
        let frame_ok =
            |f: &FrameInfo| f.width >= 1 && f.height >= 1 && inside(f.x, f.y, f.width, f.height);
        let (px, py, pw, ph) = self.prev_rect;
        let phase_ok = match self.phase {
            Phase::Signature | Phase::Header => self.have < 8,
            Phase::Gather => self.have < self.need && usize::from(self.need) <= HOLD,
            Phase::Crc => self.have < 4,
            Phase::Skip => self.at < self.len,
            Phase::Palette => self.at < self.len && self.kind == Kind::Plte,
            Phase::Trns => self.at < self.len && self.kind == Kind::Trns,
            Phase::Data => self.at < self.len && matches!(self.kind, Kind::Idat | Kind::Fdat),
            Phase::Ended | Phase::Spent => true,
        };
        let stage_ok = match self.stage {
            Stage::Active if !self.rows_done => self.has_frame && self.scan_inv(),
            Stage::Active => self.has_frame,
            Stage::Idle | Stage::Finished => true,
        };
        phase_ok
            && self.at <= self.len
            && self.layout.color.allows(self.layout.depth)
            && usize::from(self.palette_len) <= E::PALETTE_ENTRIES
            && self.pending.as_ref().is_none_or(frame_ok)
            && (!self.has_frame || frame_ok(&self.frame))
            && inside(px, py, pw, ph)
            && stage_ok
    }

    /// The invariant of a frame being received: the pass, its size, and the
    /// row in it, with the scanline buffer holding a row.
    fn scan_inv(&self) -> bool {
        let Some(p) = adam7::pass(self.interlaced, self.pass) else {
            return false;
        };
        let (pw, ph) = p.size(self.frame.width, self.frame.height);
        let cap = work::row_cap(self.canvas_width());
        pw >= 1
            && ph >= 1
            && pw == self.pass_w
            && ph == self.pass_h
            && self.row_len == self.layout.row_bytes(pw)
            && usize::try_from(self.row_len).is_ok_and(|l| Some(l) <= cap)
            && self.row < ph
            && self.row_have <= self.row_len
    }
}

impl<E: Engine> Decoder for Png<E> {
    fn decode_config(prefix: &[u8]) -> Result<ConfigStatus, Error> {
        // 5.2 and 5.6: the signature, then IHDR first, 13 bytes of data
        // (11.2.1): length 0, 0, 0, 13 and type "IHDR" at bytes 8 to 15 and the
        // width and height at 16 to 23. Whatever of the prefix is there must
        // match.
        const HEAD: [u8; 16] = [
            0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0, 0, 0, 13, b'I', b'H', b'D', b'R',
        ];
        let n = prefix.len().min(HEAD.len());
        if prefix.get(..n) != HEAD.get(..n) {
            return Err(bad("not a PNG: signature or IHDR header"));
        }
        if prefix.len() < 24 {
            return Ok(ConfigStatus::NeedMore);
        }
        let config = Config::new(
            Format::Png,
            be32(prefix, 16),
            be32(prefix, 20),
            FrameCount::Unknown,
        )?;
        Ok(ConfigStatus::Ready(config))
    }

    fn work_len(config: &Config) -> Result<usize, Error> {
        work::work_len(config, E::WINDOW, E::PALETTE_ENTRIES)
            .ok_or(Error::Malformed("work buffer size overflow"))
    }

    fn start(config: &Config) -> Result<Png<E>, Error> {
        if config.format() != Format::Png {
            return Err(Error::Unsupported("not a PNG config"));
        }
        config.rgba_len()?;
        let empty = FrameInfo {
            x: 0,
            y: 0,
            width: 1,
            height: 1,
            delay_num: 0,
            delay_den: 0,
            dispose: Dispose::None,
            blend: Blend::Source,
            animated: false,
        };
        Ok(Png {
            config: *config,
            phase: Phase::Signature,
            kind: Kind::Other,
            len: 0,
            at: 0,
            crc: 0,
            hold: [0; HOLD],
            have: 0,
            need: 0,
            header_done: false,
            layout: Layout {
                color: ColorType::Gray,
                depth: 8,
            },
            interlaced: false,
            trns: Trns::None,
            palette_len: 0,
            seen_plte: false,
            seen_trns: false,
            idat: Idat::NotYet,
            animation: None,
            next_seq: 0,
            fctl_seen: 0,
            pending: None,
            frame: empty,
            has_frame: false,
            stage: Stage::Idle,
            data_kind: Kind::Other,
            report: false,
            engine: E::new(0),
            pass: 0,
            row: 0,
            row_have: 0,
            pass_w: 0,
            pass_h: 0,
            row_len: 0,
            rows_done: false,
            frames_done: 0,
            anim_begun: 0,
            default_hidden: false,
            prev_dispose: Dispose::None,
            prev_rect: (0, 0, 0, 0),
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
        let Some(mut parts) = Parts::new(
            &self.config,
            E::WINDOW,
            E::PALETTE_ENTRIES,
            &mut *buffers.pixels,
            &mut *buffers.work,
        ) else {
            return Err(self.fail(Error::Buffers));
        };
        let mut pos = 0usize;
        while pos < chunk.len() {
            let rest = chunk.get(pos..).unwrap_or(&[]);
            match self.advance(rest, &mut parts) {
                Ok((used, event)) => {
                    // `advance` uses at least a byte of a non-empty input.
                    if used == 0 || used > rest.len() {
                        return Err(self.fail(bad("no progress")));
                    }
                    pos = pos.saturating_add(used);
                    match event {
                        Event::Continue => {}
                        Event::Frame => {
                            return Ok(Step {
                                consumed: pos,
                                status: Status::FrameDone,
                            });
                        }
                        Event::End => return Err(Error::NoMoreFrames),
                    }
                }
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
        let Some(wlen) = work::work_len(&self.config, E::WINDOW, E::PALETTE_ENTRIES) else {
            return false;
        };
        buffers.pixels.len() == plen
            && buffers.work.len() == wlen
            && (matches!(self.phase, Phase::Spent | Phase::Ended) || self.state_inv())
    }
}

/// One of `options`, chosen symbolically.
#[cfg(kani)]
fn pick<T: Copy>(options: &[T]) -> Option<T> {
    let i: usize = kani::any();
    kani::assume(i < options.len());
    options.get(i).copied()
}

#[cfg(kani)]
fn any_frame_info() -> Option<FrameInfo> {
    Some(FrameInfo {
        x: kani::any(),
        y: kani::any(),
        width: kani::any(),
        height: kani::any(),
        delay_num: kani::any(),
        delay_den: kani::any(),
        dispose: pick(&[Dispose::None, Dispose::Background, Dispose::Previous])?,
        blend: pick(&[Blend::Source, Blend::Over])?,
        animated: kani::any(),
    })
}

/// Any state of a decoder of a 2 by 2 canvas, with `Phase` one of `phases`
/// and every other field symbolic (the harness assumes `inv` on top).
#[cfg(kani)]
fn any_png_in(phases: &[Phase]) -> Option<Png<crate::proofs::AnyEngine>> {
    // A canvas of exactly 2 by 2: the template compares the bytes of its
    // arrays past the buffers, and the model checker follows every access.
    let config = Config::new(Format::Png, 2, 2, FrameCount::Unknown).ok()?;
    let mut p = Png::<crate::proofs::AnyEngine>::start(&config).ok()?;
    p.phase = pick(phases)?;
    p.kind = pick(&[
        Kind::Ihdr,
        Kind::Plte,
        Kind::Trns,
        Kind::Idat,
        Kind::Iend,
        Kind::Actl,
        Kind::Fctl,
        Kind::Fdat,
        Kind::Other,
    ])?;
    p.len = kani::any();
    p.at = kani::any();
    p.crc = kani::any();
    p.hold = kani::any();
    p.have = kani::any();
    p.need = kani::any();
    p.header_done = kani::any();
    p.layout = Layout {
        color: pick(&[
            ColorType::Gray,
            ColorType::Rgb,
            ColorType::Indexed,
            ColorType::GrayAlpha,
            ColorType::Rgba,
        ])?,
        depth: kani::any(),
    };
    p.interlaced = kani::any();
    p.trns = match pick(&[0u8, 1, 2])? {
        0 => Trns::None,
        1 => Trns::Gray(kani::any()),
        _ => Trns::Rgb(kani::any(), kani::any(), kani::any()),
    };
    p.palette_len = kani::any();
    p.seen_plte = kani::any();
    p.seen_trns = kani::any();
    p.idat = pick(&[Idat::NotYet, Idat::Open, Idat::Closed])?;
    p.animation = if kani::any() {
        Some(Animation {
            frames: kani::any(),
            plays: kani::any(),
        })
    } else {
        None
    };
    p.next_seq = kani::any();
    p.fctl_seen = kani::any();
    p.pending = if kani::any() {
        Some(any_frame_info()?)
    } else {
        None
    };
    p.frame = any_frame_info()?;
    p.has_frame = kani::any();
    p.stage = pick(&[Stage::Idle, Stage::Active, Stage::Finished])?;
    p.data_kind = pick(&[Kind::Idat, Kind::Fdat, Kind::Other])?;
    p.report = kani::any();
    p.pass = kani::any();
    p.row = kani::any();
    p.row_have = kani::any();
    p.pass_w = kani::any();
    p.pass_h = kani::any();
    p.row_len = kani::any();
    p.rows_done = kani::any();
    p.frames_done = kani::any();
    p.anim_begun = kani::any();
    p.default_hidden = kani::any();
    p.prev_dispose = pick(&[Dispose::None, Dispose::Background, Dispose::Previous])?;
    p.prev_rect = (kani::any(), kani::any(), kani::any(), kani::any());
    Some(p)
}

/// Every phase.
#[cfg(kani)]
pub(crate) fn any_png() -> Option<Png<crate::proofs::AnyEngine>> {
    any_png_in(&[
        Phase::Signature,
        Phase::Header,
        Phase::Gather,
        Phase::Skip,
        Phase::Palette,
        Phase::Trns,
        Phase::Data,
        Phase::Crc,
        Phase::Ended,
        Phase::Spent,
    ])
}

/// Every phase but the image data's.
#[cfg(kani)]
pub(crate) fn any_png_control() -> Option<Png<crate::proofs::AnyEngine>> {
    any_png_in(&[
        Phase::Signature,
        Phase::Header,
        Phase::Gather,
        Phase::Skip,
        Phase::Palette,
        Phase::Trns,
        Phase::Crc,
    ])
}

/// The phase of image data.
#[cfg(kani)]
pub(crate) fn any_png_data() -> Option<Png<crate::proofs::AnyEngine>> {
    any_png_in(&[Phase::Data])
}

/// What the harnesses ask of a state.
#[cfg(kani)]
impl<E: Engine> Png<E> {
    /// No frame's data has begun.
    pub(crate) fn idle_stage(&self) -> bool {
        self.stage == Stage::Idle
    }

    /// A frame is being received.
    pub(crate) fn active_frame(&self) -> bool {
        self.stage == Stage::Active && self.has_frame
    }

    /// Makes the scanline buffer hold a whole scanline (its filter-type byte
    /// and `row_len` bytes), which is the state `feed` calls `finish_row` in
    /// and which the invariant (a scanline in progress is shorter) excludes.
    pub(crate) fn complete_row(&mut self) -> bool {
        if self.stage != Stage::Active || self.rows_done {
            return false;
        }
        self.row_have = self.row_len.saturating_add(1);
        true
    }
}

//! The GIF decoder: a byte-at-a-time state machine over the blocks of
//! GIF89a, implementing [`clazel_image_shape::Decoder`].
//!
//! Citations are to the GIF89a specification (CompuServe, 31 July 1990)
//! by section, as in `lib.rs`'s header; the listed choices are there too.

use clazel_image_shape::{
    Buffers, Config, ConfigStatus, Decoder, Error, Format, FrameCount, Status, Step,
};

use crate::lzw::{Fed, Lzw};
use crate::sink::Sink;
use crate::work::{FIXED, PALETTE, Parts};

/// What a frame's disposal method says to do with the canvas before the
/// next frame is drawn (GIF89a section 23, "Graphic Control Extension",
/// "Disposal Method"; values 4 to 7 are undefined there and are read as
/// [`Disposal::None`], a listed choice).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Disposal {
    /// 0: no disposal specified (the frame stays, as with `Keep`).
    None,
    /// 1: do not dispose; the frame stays.
    Keep,
    /// 2: restore the frame's area to the background. Listed choice: to
    /// transparent black, as browsers do, not to the logical screen
    /// descriptor's background colour.
    Background,
    /// 3: restore the canvas to what it was before the frame was drawn.
    Previous,
}

impl Disposal {
    /// The method for a 3-bit value of the Graphic Control Extension.
    fn from_bits(v: u8) -> Disposal {
        match v {
            1 => Disposal::Keep,
            2 => Disposal::Background,
            3 => Disposal::Previous,
            _ => Disposal::None,
        }
    }
}

/// What the Graphic Control Extension before a frame says (and what a frame
/// without one has: no delay, no transparency, no disposal).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Control {
    disposal: Disposal,
    delay_cs: u16,
    transparent: Option<u8>,
}

impl Control {
    const NONE: Control = Control {
        disposal: Disposal::None,
        delay_cs: 0,
        transparent: None,
    };
}

/// The facts of the frame last started, as the stream gives them; read
/// them after [`Status::FrameDone`] with [`Gif::frame`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FrameInfo {
    /// Left edge on the canvas (the image descriptor's).
    pub left: u16,
    /// Top edge on the canvas.
    pub top: u16,
    /// Width of the frame's own image (it may extend past the canvas; what
    /// does is not drawn).
    pub width: u16,
    /// Height of the frame's own image.
    pub height: u16,
    /// The rows were stored interlaced.
    pub interlaced: bool,
    /// The delay before the next frame, in hundredths of a second (0 if
    /// the frame had no control extension).
    pub delay_cs: u16,
    /// What happens to the canvas after the frame is shown.
    pub disposal: Disposal,
    /// The transparent colour index, if the frame has one.
    pub transparent: Option<u8>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// The six bytes `GIF89a` (or `GIF87a`), gathered in `hold`.
    Header,
    /// The logical screen descriptor, seven bytes, gathered.
    Screen,
    /// The global colour table, `count` of `global_len` bytes read.
    GlobalColours,
    /// The introducer of the next block: `,` image, `!` extension, `;`.
    Block,
    /// An extension's label.
    Extension,
    /// The block size of a Graphic Control Extension (4 if well formed).
    GceSize,
    /// The four bytes of a Graphic Control Extension, gathered.
    GceBody,
    /// The terminator of a Graphic Control Extension.
    GceEnd,
    /// The size byte of a sub-block of an extension to skip (0 ends them).
    SkipSize,
    /// `count` bytes of such a sub-block to skip.
    SkipData,
    /// An image descriptor, nine bytes, gathered.
    Descriptor,
    /// The local colour table, `count` of `local_len` bytes read.
    LocalColours,
    /// The LZW minimum code size.
    MinCode,
    /// The size byte of a sub-block of image data (0 ends the frame).
    DataSize,
    /// `count` bytes of image data left in this sub-block.
    Data,
    /// The frame is full or its end code was read: sub-block sizes, to the
    /// terminator that ends the frame.
    TailSize,
    /// `count` bytes of such a sub-block to skip.
    TailData,
    /// The trailer was read: no more frames.
    Ended,
    /// An error happened.
    Spent,
}

/// What one byte did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Event {
    Continue,
    Frame,
    Trailer,
}

/// The GIF decoder's state: fixed-size, no allocation.
#[derive(Debug, Clone, Copy)]
pub struct Gif {
    config: Config,
    phase: Phase,
    /// Bytes of a fixed-size structure gathered so far, and how many.
    hold: [u8; 9],
    have: u8,
    /// Bytes left of a sub-block, or bytes of a colour table read.
    count: u16,
    /// Bytes of the global colour table (0, or 3 times a power of two
    /// from 2 to 256) and of the local one.
    global_len: u16,
    local_len: u16,
    /// The current frame has a local colour table.
    use_local: bool,
    /// The control extension waiting for the next image.
    pending: Control,
    /// The current (or last) frame.
    frame: FrameInfo,
    /// A frame was started (so `frame` has meaning, and its disposal is
    /// due before the next one is drawn).
    has_frame: bool,
    /// The canvas was saved for the current frame's disposal.
    saved: bool,
    sink: Sink,
    lzw: Lzw,
    /// Frames completed.
    frames: u32,
}

impl Gif {
    /// The current or last frame's facts (as the stream gave them), if a
    /// frame was started. After `Status::FrameDone` it is that frame's.
    pub fn frame(&self) -> Option<&FrameInfo> {
        self.has_frame.then_some(&self.frame)
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

    fn u16_at(&self, i: usize) -> u16 {
        u16::from_le_bytes([self.hold_at(i), self.hold_at(i.saturating_add(1))])
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

    /// Copies colour table byte `b` to `table[count]`; true when `len`
    /// bytes are there.
    fn table_byte(count: &mut u16, len: u16, table: &mut [u8], b: u8) -> bool {
        if let Some(slot) = table.get_mut(usize::from(*count)) {
            *slot = b;
        }
        *count = count.saturating_add(1);
        *count >= len
    }

    /// Size in bytes of a colour table whose packed field has `bits` in its
    /// size bits: 3 * 2^(bits + 1) (GIF89a sections 18 and 19: "2^(N+1)
    /// entries").
    fn table_len(bits: u8) -> u16 {
        3u16.checked_shl(u32::from(bits & 7).saturating_add(1))
            .unwrap_or(0)
    }

    /// Sets the pixels of the current frame's rectangle, clipped to the
    /// canvas, to transparent black.
    fn clear_rect(&self, pixels: &mut [u8]) {
        let f = &self.frame;
        let cw = u32::from(self.sink.canvas_w);
        let ch = u32::from(self.sink.canvas_h);
        let x0 = u32::from(f.left).min(cw);
        let x1 = u32::from(f.left).saturating_add(u32::from(f.width)).min(cw);
        let y1 = u32::from(f.top).saturating_add(u32::from(f.height)).min(ch);
        for y in u32::from(f.top)..y1 {
            let row = y.checked_mul(cw);
            let bytes = |x: u32| {
                row.and_then(|r| r.checked_add(x))
                    .and_then(|p| usize::try_from(p).ok())
                    .and_then(|p| p.checked_mul(4))
            };
            if let (Some(s), Some(e)) = (bytes(x0), bytes(x1))
                && let Some(span) = pixels.get_mut(s..e)
            {
                span.fill(0);
            }
        }
    }

    /// Applies the disposal method of the frame before the one being
    /// started (GIF89a section 23: "the graphic is to be handled after
    /// being displayed").
    fn dispose(&mut self, parts: &mut Parts<'_>) {
        if !self.has_frame {
            return;
        }
        match self.frame.disposal {
            Disposal::Background => self.clear_rect(parts.pixels),
            Disposal::Previous => {
                if self.saved && parts.pixels.len() == parts.saved.len() {
                    parts.pixels.copy_from_slice(parts.saved);
                }
            }
            Disposal::None | Disposal::Keep => {}
        }
        self.saved = false;
    }

    /// The image descriptor is complete: GIF89a section 20.
    fn start_frame(&mut self, parts: &mut Parts<'_>) {
        let packed = self.hold_at(8);
        // The frame before this one is disposed of, then this one's
        // disposal is prepared.
        self.dispose(parts);
        let control = self.pending;
        self.pending = Control::NONE;
        self.frame = FrameInfo {
            left: self.u16_at(0),
            top: self.u16_at(2),
            width: self.u16_at(4),
            height: self.u16_at(6),
            interlaced: packed & 0x40 != 0,
            delay_cs: control.delay_cs,
            disposal: control.disposal,
            transparent: control.transparent,
        };
        self.has_frame = true;
        if self.frame.disposal == Disposal::Previous && parts.pixels.len() == parts.saved.len() {
            parts.saved.copy_from_slice(parts.pixels);
            self.saved = true;
        }
        let f = self.frame;
        self.sink = Sink::frame(
            (self.sink.canvas_w, self.sink.canvas_h),
            (f.left, f.top, f.width, f.height),
            f.interlaced,
            f.transparent,
        );
        self.use_local = packed & 0x80 != 0;
        self.local_len = if self.use_local {
            Self::table_len(packed)
        } else {
            0
        };
        self.count = 0;
        self.phase = if self.use_local {
            Phase::LocalColours
        } else {
            Phase::MinCode
        };
    }

    /// One byte of the stream.
    fn byte(&mut self, b: u8, parts: &mut Parts<'_>) -> Result<Event, &'static str> {
        match self.phase {
            // GIF89a section 17: "Header" ("GIF" and the version).
            Phase::Header => {
                if self.gather(b, 6) {
                    let sig = self.hold.get(..6);
                    if sig != Some(b"GIF89a") && sig != Some(b"GIF87a") {
                        return Err("not a GIF header");
                    }
                    self.phase = Phase::Screen;
                }
            }
            // GIF89a section 18: "Logical Screen Descriptor".
            Phase::Screen => {
                if self.gather(b, 7) {
                    if u32::from(self.u16_at(0)) != self.config.width()
                        || u32::from(self.u16_at(2)) != self.config.height()
                    {
                        return Err("the screen is not the size the config says");
                    }
                    // The canvas starts transparent black (listed choice:
                    // the background colour index is not used).
                    parts.pixels.fill(0);
                    let packed = self.hold_at(4);
                    self.global_len = if packed & 0x80 != 0 {
                        Self::table_len(packed)
                    } else {
                        0
                    };
                    self.count = 0;
                    self.phase = if self.global_len > 0 {
                        Phase::GlobalColours
                    } else {
                        Phase::Block
                    };
                }
            }
            // GIF89a section 19: "Global Color Table".
            Phase::GlobalColours => {
                if Self::table_byte(&mut self.count, self.global_len, parts.global, b) {
                    self.phase = Phase::Block;
                }
            }
            // GIF89a section 12 "Data Sub-blocks" and the block grammar of
            // Appendix B: an image (`,`), an extension (`!`) or the trailer.
            Phase::Block => match b {
                0x2C => self.phase = Phase::Descriptor,
                0x21 => self.phase = Phase::Extension,
                0x3B => {
                    // GIF89a section 27: "Trailer".
                    self.phase = Phase::Ended;
                    return Ok(Event::Trailer);
                }
                _ => return Err("not a block introducer"),
            },
            Phase::Extension => {
                // GIF89a section 23 labels the Graphic Control Extension
                // 0xF9. Every other extension (plain text 0x01, comment
                // 0xFE, application 0xFF, unknown) is skipped by its
                // sub-block sizes (sections 12 and 24 to 26).
                self.phase = if b == 0xF9 {
                    Phase::GceSize
                } else {
                    Phase::SkipSize
                };
            }
            Phase::GceSize => {
                if b == 4 {
                    self.phase = Phase::GceBody;
                } else if b == 0 {
                    self.phase = Phase::Block;
                } else {
                    // Not the 4 bytes section 23 requires: ignored like an
                    // unknown extension (listed choice).
                    self.count = u16::from(b);
                    self.phase = Phase::SkipData;
                }
            }
            // GIF89a section 23: packed fields (reserved 3 bits, disposal 3
            // bits, user input flag, transparency flag), delay time in
            // hundredths of a second (2 bytes), transparent colour index.
            Phase::GceBody => {
                if self.gather(b, 4) {
                    let packed = self.hold_at(0);
                    self.pending = Control {
                        disposal: Disposal::from_bits((packed >> 2) & 7),
                        delay_cs: self.u16_at(1),
                        transparent: (packed & 1 != 0).then(|| self.hold_at(3)),
                    };
                    self.phase = Phase::GceEnd;
                }
            }
            Phase::GceEnd => {
                if b == 0 {
                    self.phase = Phase::Block;
                } else {
                    // Section 23's block terminator is missing: what
                    // follows is a sub-block of this extension.
                    self.count = u16::from(b);
                    self.phase = Phase::SkipData;
                }
            }
            Phase::SkipSize => {
                if b == 0 {
                    self.phase = Phase::Block;
                } else {
                    self.count = u16::from(b);
                    self.phase = Phase::SkipData;
                }
            }
            Phase::SkipData => {
                self.count = self.count.saturating_sub(1);
                if self.count == 0 {
                    self.phase = Phase::SkipSize;
                }
            }
            // GIF89a section 20: "Image Descriptor".
            Phase::Descriptor => {
                if self.gather(b, 9) {
                    self.start_frame(parts);
                }
            }
            // GIF89a section 21: "Local Color Table".
            Phase::LocalColours => {
                if Self::table_byte(&mut self.count, self.local_len, parts.local, b) {
                    self.phase = Phase::MinCode;
                }
            }
            // GIF89a section 22 "Table Based Image Data": the LZW minimum
            // code size, then data sub-blocks.
            Phase::MinCode => {
                self.lzw = Lzw::new(b).ok_or("an LZW minimum code size outside 2 to 8")?;
                self.phase = if self.sink.remaining == 0 {
                    Phase::TailSize
                } else {
                    Phase::DataSize
                };
            }
            Phase::DataSize => {
                if b == 0 {
                    // The terminator: the frame is over, whole or not (a
                    // frame with too little data keeps what was decoded,
                    // listed choice).
                    return Ok(self.finish_frame());
                }
                self.count = u16::from(b);
                self.phase = Phase::Data;
            }
            Phase::Data => return self.data_byte(b, parts),
            Phase::TailSize => {
                if b == 0 {
                    return Ok(self.finish_frame());
                }
                self.count = u16::from(b);
                self.phase = Phase::TailData;
            }
            Phase::TailData => {
                self.count = self.count.saturating_sub(1);
                if self.count == 0 {
                    self.phase = Phase::TailSize;
                }
            }
            Phase::Ended => return Err("a byte after the trailer"),
            Phase::Spent => return Err("a byte after an error"),
        }
        Ok(Event::Continue)
    }

    /// One byte of image data.
    fn data_byte(&mut self, b: u8, parts: &mut Parts<'_>) -> Result<Event, &'static str> {
        self.count = self.count.saturating_sub(1);
        let (table, len) = if self.use_local {
            (&*parts.local, self.local_len)
        } else {
            (&*parts.global, self.global_len)
        };
        let palette = table.get(..usize::from(len)).unwrap_or(&[]);
        let pixels = &mut *parts.pixels;
        let sink = &mut self.sink;
        let fed = self.lzw.feed(b, &mut parts.tables, &mut |index| {
            sink.put(index, palette, pixels)
        })?;
        self.phase = match (fed, self.count) {
            (Fed::More, 0) => Phase::DataSize,
            (Fed::More, _) => Phase::Data,
            // The end code or a full frame: the rest of the data is
            // ignored up to the terminator ("pixel-data-too-much" files).
            (Fed::End | Fed::Full, 0) => Phase::TailSize,
            (Fed::End | Fed::Full, _) => Phase::TailData,
        };
        Ok(Event::Continue)
    }

    fn finish_frame(&mut self) -> Event {
        self.frames = self.frames.saturating_add(1);
        self.phase = Phase::Block;
        Event::Frame
    }

    /// The invariant of the whole state, without the buffers.
    fn state_inv(&self) -> bool {
        let need = match self.phase {
            Phase::Header => 6,
            Phase::Screen => 7,
            Phase::GceBody => 4,
            Phase::Descriptor => 9,
            _ => 1,
        };
        let counts = match self.phase {
            Phase::GlobalColours => self.count < self.global_len,
            Phase::LocalColours => self.count < self.local_len,
            Phase::SkipData | Phase::Data | Phase::TailData => self.count >= 1 && self.count <= 255,
            _ => true,
        };
        let data = match self.phase {
            Phase::DataSize | Phase::Data => self.sink.remaining > 0 && self.lzw.inv(),
            _ => true,
        };
        self.have < need
            && u32::from(self.sink.canvas_w) == self.config.width()
            && u32::from(self.sink.canvas_h) == self.config.height()
            && usize::from(self.global_len) <= PALETTE
            && self.global_len.is_multiple_of(3)
            && usize::from(self.local_len) <= PALETTE
            && self.local_len.is_multiple_of(3)
            && counts
            && data
            && self.sink.inv()
    }
}

impl Decoder for Gif {
    fn decode_config(prefix: &[u8]) -> Result<ConfigStatus, Error> {
        // GIF89a section 17: the signature `GIF` and a version, `87a` or
        // `89a`, then the logical screen's width and height (section 18).
        let n = prefix.len().min(6);
        let head = prefix.get(..n);
        let matches = |sig: &[u8; 6]| sig.get(..n) == head;
        if !(matches(b"GIF89a") || matches(b"GIF87a")) {
            return Err(Error::Malformed("not a GIF header"));
        }
        let le = |at: usize| {
            prefix
                .get(at..)?
                .first_chunk::<2>()
                .copied()
                .map(u16::from_le_bytes)
        };
        let (Some(w), Some(h)) = (le(6), le(8)) else {
            return Ok(ConfigStatus::NeedMore);
        };
        Ok(ConfigStatus::Ready(Config::new(
            Format::Gif,
            u32::from(w),
            u32::from(h),
            FrameCount::Unknown,
        )?))
    }

    fn work_len(config: &Config) -> Result<usize, Error> {
        FIXED
            .checked_add(config.rgba_len()?)
            .ok_or(Error::Malformed("work buffer size overflow"))
    }

    fn start(config: &Config) -> Result<Gif, Error> {
        if config.format() != Format::Gif {
            return Err(Error::Unsupported("not a GIF config"));
        }
        config.rgba_len()?;
        let too_big = Error::Unsupported("a canvas over 65535 pixels on a side");
        let w = u16::try_from(config.width()).map_err(|_| too_big)?;
        let h = u16::try_from(config.height()).map_err(|_| too_big)?;
        Ok(Gif {
            config: *config,
            phase: Phase::Header,
            hold: [0; 9],
            have: 0,
            count: 0,
            global_len: 0,
            local_len: 0,
            use_local: false,
            pending: Control::NONE,
            frame: FrameInfo {
                left: 0,
                top: 0,
                width: 0,
                height: 0,
                interlaced: false,
                delay_cs: 0,
                disposal: Disposal::None,
                transparent: None,
            },
            has_frame: false,
            saved: false,
            sink: Sink::idle(w, h),
            lzw: Lzw::idle(),
            frames: 0,
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
        let Some(mut parts) = Parts::new(&mut *buffers.pixels, &mut *buffers.work) else {
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
                Ok(Event::Trailer) => return Err(Error::NoMoreFrames),
                Err(why) => return Err(self.fail(Error::Malformed(why))),
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
        let Some(wlen) = FIXED.checked_add(plen) else {
            return false;
        };
        buffers.pixels.len() == plen
            && buffers.work.len() == wlen
            && (self.phase == Phase::Spent || self.state_inv())
    }
}

/// Any state of a decoder of a canvas at most 2 by 2, every field
/// symbolic: the harness assumes `inv` on top.
#[cfg(kani)]
pub(crate) fn any_gif() -> Option<Gif> {
    let width: u32 = kani::any();
    let height: u32 = kani::any();
    kani::assume(width <= 2 && height <= 2);
    let config = Config::new(Format::Gif, width, height, FrameCount::Unknown).ok()?;
    let mut gif = Gif::start(&config).ok()?;
    let which: u8 = kani::any();
    gif.phase = match which % 19 {
        0 => Phase::Header,
        1 => Phase::Screen,
        2 => Phase::GlobalColours,
        3 => Phase::Block,
        4 => Phase::Extension,
        5 => Phase::GceSize,
        6 => Phase::GceBody,
        7 => Phase::GceEnd,
        8 => Phase::SkipSize,
        9 => Phase::SkipData,
        10 => Phase::Descriptor,
        11 => Phase::LocalColours,
        12 => Phase::MinCode,
        13 => Phase::DataSize,
        14 => Phase::Data,
        15 => Phase::TailSize,
        16 => Phase::TailData,
        17 => Phase::Ended,
        _ => Phase::Spent,
    };
    gif.hold = kani::any();
    gif.have = kani::any();
    gif.count = kani::any();
    gif.global_len = kani::any();
    gif.local_len = kani::any();
    gif.use_local = kani::any();
    gif.pending = Control {
        disposal: Disposal::from_bits(kani::any()),
        delay_cs: kani::any(),
        transparent: if kani::any() { Some(kani::any()) } else { None },
    };
    gif.frame = FrameInfo {
        left: kani::any(),
        top: kani::any(),
        width: kani::any(),
        height: kani::any(),
        interlaced: kani::any(),
        delay_cs: kani::any(),
        disposal: Disposal::from_bits(kani::any()),
        transparent: if kani::any() { Some(kani::any()) } else { None },
    };
    gif.has_frame = kani::any();
    gif.saved = kani::any();
    gif.sink = Sink {
        canvas_w: gif.sink.canvas_w,
        canvas_h: gif.sink.canvas_h,
        left: kani::any(),
        top: kani::any(),
        width: kani::any(),
        height: kani::any(),
        interlaced: kani::any(),
        transparent: if kani::any() { Some(kani::any()) } else { None },
        x: kani::any(),
        y: kani::any(),
        pass: kani::any(),
        remaining: kani::any(),
    };
    gif.lzw = Lzw {
        min_size: kani::any(),
        code_size: kani::any(),
        next: kani::any(),
        prev: kani::any(),
        first: kani::any(),
        acc: kani::any(),
        nacc: kani::any(),
    };
    gif.frames = kani::any();
    Some(gif)
}

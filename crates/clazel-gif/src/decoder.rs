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

    /// One byte of the stream.
    ///
    /// STUB: the block grammar of GIF89a (see the phases above and the
    /// commented implementation in the next commit) is not written yet.
    fn byte(&mut self, _b: u8, _parts: &mut Parts<'_>) -> Result<Event, &'static str> {
        Err("not implemented")
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

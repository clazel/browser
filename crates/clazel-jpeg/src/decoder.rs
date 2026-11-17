//! The JPEG decoder: a byte-at-a-time state machine over the markers of
//! ITU-T T.81 Annex B and the entropy-coded segments of Annex F,
//! implementing [`clazel_image_shape::Decoder`].
//!
//! Citations are to T.81 (09/92) by clause, figure and table, as in
//! `lib.rs`'s header; the listed choices are there too.

use clazel_image_shape::{
    Buffers, Config, ConfigStatus, Decoder, Error, Format, FrameCount, Status, Step,
};

use crate::bits::BitReader;
use crate::block::{Block, ZIGZAG};
use crate::exif;
use crate::huffman::Table;
use crate::idct::idct;
use crate::markers::{Kind, kind};
use crate::output::{Plane, cmyk_to_rgb, orient, swaps, ycc_to_rgb, ycck_to_cmyk};

/// Components of a frame: T.81 B.2.2 allows 1 to 255; this decoder reads
/// 1 (gray), 3 (YCbCr or RGB) and 4 (CMYK or YCCK).
pub(crate) const MAX_COMPONENTS: usize = 4;

/// Bytes of a frame header's body kept: 6 fixed plus 3 per component.
const HOLD: usize = 6 + 3 * MAX_COMPONENTS;

/// The colour model of the components, from the markers and ids (what
/// libjpeg-turbo's `default_decompress_parms` decides).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Colour {
    /// One component: luminance.
    Gray,
    /// Three components: red, green, blue as they are.
    Rgb,
    /// Three components: Y, Cb, Cr (JFIF 1.02 §7).
    YCbCr,
    /// Four components: cyan, magenta, yellow, black (Adobe: inverted).
    Cmyk,
    /// Four components: Y, Cb, Cr and K (Adobe transform 2).
    Ycck,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// The `0xFF` of SOI.
    Soi0,
    /// The `0xD8` of SOI.
    Soi1,
    /// The `0xFF` that starts a marker (T.81 B.1.1.2).
    Marker0,
    /// The marker code, after any number of `0xFF` fill bytes.
    Marker1,
    /// High byte of a segment's length `L`.
    Len0,
    /// Low byte of `L`.
    Len1,
    /// The body of a segment, `seg_total - seg_pos` bytes left.
    Segment,
    /// An entropy-coded segment.
    Entropy,
    /// EOI was read and the frame is in the pixel buffer.
    Done,
    /// An error happened.
    Spent,
}

/// Where the entropy-coded segment of a scan is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScanState {
    /// Decoding blocks.
    Decoding,
    /// The restart interval is complete: only `RSTn` can follow.
    AwaitRestart,
    /// Every MCU of the scan is decoded: only a marker can follow.
    Complete,
}

/// One component of the frame (T.81 B.2.2 `Ci`, `Hi`, `Vi`, `Tqi`) and
/// where its samples are.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Comp {
    pub id: u8,
    pub h: u8,
    pub v: u8,
    pub tq: u8,
    /// Size in samples, `ceil(X * Hi / Hmax)` by `ceil(Y * Vi / Vmax)`
    /// (Equation A.1).
    pub width: u16,
    pub height: u16,
    /// Plane size in blocks: whole MCUs (`mcus_x * Hi` by `mcus_y * Vi`).
    pub blocks_w: u16,
    pub blocks_h: u16,
    /// Start of the plane in the work buffer.
    pub off: usize,
    /// The quantization table latched at the start of the scan, natural
    /// order.
    pub q: [u16; 64],
    /// Table selectors of the current scan.
    pub dc_sel: u8,
    pub ac_sel: u8,
    /// DC predictor (`PRED`, F.2.1.3.1).
    pub pred: i32,
    /// Every block of the plane was decoded by a scan.
    pub done: bool,
}

impl Comp {
    const EMPTY: Comp = Comp {
        id: 0,
        h: 1,
        v: 1,
        tq: 0,
        width: 0,
        height: 0,
        blocks_w: 0,
        blocks_h: 0,
        off: 0,
        q: [1; 64],
        dc_sel: 0,
        ac_sel: 0,
        pred: 0,
        done: false,
    };

    /// Samples from one row of the plane to the next.
    fn stride(&self) -> usize {
        usize::from(self.blocks_w).saturating_mul(8)
    }

    /// Bytes of the plane.
    fn plane_len(&self) -> Option<usize> {
        usize::from(self.blocks_w)
            .checked_mul(8)?
            .checked_mul(usize::from(self.blocks_h).checked_mul(8)?)
    }
}

/// The scan being decoded (T.81 B.2.3 and A.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Scan {
    /// Components in the scan, and their indexes in the frame.
    n: u8,
    comp: [u8; MAX_COMPONENTS],
    /// More than one component: the MCU holds `Hi * Vi` blocks of each.
    interleaved: bool,
    /// Blocks in an MCU.
    per_mcu: u8,
    /// MCUs per row and rows (A.2.2, or A.2.4 for one component).
    mcus_x: u16,
    mcus_y: u16,
    /// The MCU being decoded, and the block in it.
    mx: u16,
    my: u16,
    bi: u8,
    /// MCUs decoded since the last restart.
    in_interval: u16,
    /// The number of the next restart marker (`RSTm`, `m` = 0 to 7).
    next_rst: u8,
    state: ScanState,
}

/// The JPEG decoder's state: fixed-size, no allocation.
#[derive(Debug, Clone)]
pub struct Jpeg {
    config: Config,
    work_len: usize,
    phase: Phase,
    /// The marker of the segment being read, its body length and the bytes
    /// of it read (the length `L` of B.1.1.4 counts its own 2 bytes).
    marker: u8,
    len_hi: u8,
    seg_total: u16,
    seg_pos: u16,
    /// The first bytes of a SOF, SOS, DRI, APP0 or APP14 body.
    hold: [u8; HOLD],
    /// The first bytes of an APP1 body.
    exif: [u8; exif::MAX_BYTES],
    /// Quantization tables, natural order, and which are defined.
    qt: [[u16; 64]; 4],
    qt_def: [bool; 4],
    /// Huffman tables by class and destination (B.2.4.2).
    dc: [Option<Table>; 4],
    ac: [Option<Table>; 4],
    /// DQT being read: stage 0 expects `Pq|Tq`, 1 the 64 values.
    dq_stage: u8,
    dq_wide: bool,
    dq_tq: u8,
    dq_k: u8,
    dq_hi: Option<u8>,
    /// DHT being read: stage 0 expects `Tc|Th`, 1 the 16 counts, 2 the
    /// symbols.
    ht_stage: u8,
    ht_class: u8,
    ht_i: u16,
    ht_counts: [u8; 16],
    ht_syms: [u8; 256],
    ht_total: u16,
    /// DRI's restart interval (0: none).
    restart_interval: u16,
    /// A JFIF APP0 and an Adobe APP14 were seen; Adobe's transform byte.
    jfif: bool,
    adobe: Option<u8>,
    /// EXIF orientation of the first valid Exif APP1 before the frame,
    /// 1 if none.
    orientation: u8,
    seen_orientation: bool,
    /// The frame header.
    frame_set: bool,
    width: u16,
    height: u16,
    ncomp: u8,
    hmax: u8,
    vmax: u8,
    mcus_x: u16,
    mcus_y: u16,
    comps: [Comp; MAX_COMPONENTS],
    /// Bytes of the work buffer the planes use.
    planes_len: usize,
    scan: Scan,
    block: Block,
    bits: BitReader,
    /// An `0xFF` was just read in an entropy-coded segment.
    ff: bool,
}

/// Error shorthand.
fn bad<T>(why: &'static str) -> Result<T, Error> {
    Err(Error::Malformed(why))
}

/// `ceil(a / b)`.
fn ceil_div(a: usize, b: usize) -> Option<usize> {
    a.checked_add(b.checked_sub(1)?)?.checked_div(b)
}

/// The most the work buffer can need for a `w` by `h` image: four planes of
/// `(w + 31) * (h + 31)` samples (the planes are padded to whole MCUs, at
/// most 32 samples at sampling factors of 4).
fn plane_bound(w: u32, h: u32) -> Result<usize, Error> {
    let pad = |s: u32| s.checked_add(31).and_then(|v| usize::try_from(v).ok());
    pad(w)
        .zip(pad(h))
        .and_then(|(a, b)| a.checked_mul(b))
        .and_then(|p| p.checked_mul(MAX_COMPONENTS))
        .ok_or(Error::Malformed("work buffer size overflow"))
}

impl Jpeg {
    /// The colour model chosen from the markers and component ids
    /// (libjpeg-turbo's `default_decompress_parms`).
    pub fn colour(&self) -> Colour {
        match self.ncomp {
            1 => Colour::Gray,
            3 => {
                let id = |i: usize| self.comps.get(i).map_or(0, |c| c.id);
                if self.jfif {
                    Colour::YCbCr
                } else if let Some(t) = self.adobe {
                    if t == 0 { Colour::Rgb } else { Colour::YCbCr }
                } else if (id(0), id(1), id(2)) == (b'R', b'G', b'B') {
                    Colour::Rgb
                } else {
                    Colour::YCbCr
                }
            }
            _ => match self.adobe {
                Some(0) | None => Colour::Cmyk,
                Some(_) => Colour::Ycck,
            },
        }
    }

    /// The EXIF orientation applied (1 to 8).
    pub fn orientation(&self) -> u8 {
        self.orientation
    }

    fn fail(&mut self, e: Error) -> Error {
        self.phase = Phase::Spent;
        e
    }

    fn hold_at(&self, i: usize) -> u8 {
        self.hold.get(i).copied().unwrap_or(0)
    }

    fn u16_hold(&self, i: usize) -> u16 {
        u16::from_be_bytes([self.hold_at(i), self.hold_at(i.saturating_add(1))])
    }

    /// One byte of the stream. `Ok(true)` when EOI completed the frame.
    pub(crate) fn byte(&mut self, b: u8, work: &mut [u8]) -> Result<bool, Error> {
        if self.phase == Phase::Entropy {
            match self.entropy_byte(b, work)? {
                Some(m) => self.marker_code(m),
                None => Ok(false),
            }
        } else {
            self.control_byte(b)
        }
    }

    /// One byte of the stream in any phase but an entropy-coded segment.
    pub(crate) fn control_byte(&mut self, b: u8) -> Result<bool, Error> {
        match self.phase {
            // T.81 B.1.1.3: a compressed image starts with SOI.
            Phase::Soi0 => {
                if b != 0xFF {
                    return bad("not a JPEG: no SOI");
                }
                self.phase = Phase::Soi1;
            }
            Phase::Soi1 => {
                if b != 0xD8 {
                    return bad("not a JPEG: no SOI");
                }
                self.phase = Phase::Marker0;
            }
            // B.1.1.2: a marker is `0xFF` and a code, with any number of
            // `0xFF` fill bytes before the code.
            Phase::Marker0 => {
                if b != 0xFF {
                    return bad("expected a marker");
                }
                self.phase = Phase::Marker1;
            }
            Phase::Marker1 => {
                if b != 0xFF {
                    return self.marker_code(b);
                }
            }
            Phase::Len0 => {
                self.len_hi = b;
                self.phase = Phase::Len1;
            }
            Phase::Len1 => {
                let l = u16::from_be_bytes([self.len_hi, b]);
                // B.1.1.4: `L` counts its own two bytes.
                if l < 2 {
                    return bad("segment length under 2");
                }
                self.seg_total = l.saturating_sub(2);
                self.seg_pos = 0;
                self.phase = Phase::Segment;
                if self.seg_total == 0 {
                    self.end_segment()?;
                }
            }
            Phase::Segment => {
                self.segment_byte(b)?;
                self.seg_pos = self.seg_pos.saturating_add(1);
                if self.seg_pos >= self.seg_total {
                    self.end_segment()?;
                }
            }
            Phase::Entropy | Phase::Done | Phase::Spent => return bad("byte in a spent decoder"),
        }
        Ok(false)
    }

    /// A marker code was read (B.1.1.3, Table B.1). `Ok(true)` at EOI.
    fn marker_code(&mut self, m: u8) -> Result<bool, Error> {
        self.marker = m;
        match kind(m) {
            Kind::Standalone => self.phase = Phase::Marker0,
            Kind::Soi => return bad("a second SOI"),
            Kind::Eoi => {
                if !self.frame_set {
                    return bad("EOI before a frame");
                }
                let n = usize::from(self.ncomp);
                if !self.comps.iter().take(n).all(|c| c.done) {
                    return bad("a component has no scan data");
                }
                self.phase = Phase::Done;
                return Ok(true);
            }
            Kind::Frame => {
                if self.frame_set {
                    return bad("a second frame header");
                }
                self.phase = Phase::Len0;
            }
            Kind::Scan => {
                if !self.frame_set {
                    return bad("a scan before the frame header");
                }
                self.phase = Phase::Len0;
            }
            Kind::Read => {
                // Table definitions in progress belong to this segment.
                self.dq_stage = 0;
                self.ht_stage = 0;
                self.phase = Phase::Len0;
            }
            Kind::Skip => self.phase = Phase::Len0,
            Kind::Unsupported(why) => return Err(Error::Unsupported(why)),
            Kind::Invalid => return bad("an unknown or reserved marker"),
        }
        Ok(false)
    }

    /// One byte of a segment's body.
    fn segment_byte(&mut self, b: u8) -> Result<(), Error> {
        let pos = usize::from(self.seg_pos);
        match self.marker {
            0xC0 | 0xC1 | 0xDA | 0xDD | 0xE0 | 0xEE => {
                if let Some(s) = self.hold.get_mut(pos) {
                    *s = b;
                }
            }
            0xE1 => {
                if let Some(s) = self.exif.get_mut(pos) {
                    *s = b;
                }
            }
            0xDB => self.dqt_byte(b)?,
            0xC4 => self.dht_byte(b)?,
            _ => {}
        }
        Ok(())
    }

    /// One byte of a DQT body (B.2.4.1): `Pq|Tq`, then 64 values `Qk` in
    /// zig-zag order, one byte each or two when `Pq` is 1.
    fn dqt_byte(&mut self, b: u8) -> Result<(), Error> {
        if self.dq_stage == 0 {
            let (pq, tq) = (b >> 4, b & 15);
            if pq > 1 || tq > 3 {
                return bad("bad quantization table header");
            }
            self.dq_wide = pq == 1;
            self.dq_tq = tq;
            self.dq_k = 0;
            self.dq_hi = None;
            self.dq_stage = 1;
            if let Some(d) = self.qt_def.get_mut(usize::from(tq)) {
                *d = false;
            }
            return Ok(());
        }
        let v = if self.dq_wide {
            match self.dq_hi.take() {
                None => {
                    self.dq_hi = Some(b);
                    return Ok(());
                }
                Some(hi) => u16::from_be_bytes([hi, b]),
            }
        } else {
            u16::from(b)
        };
        let nat = ZIGZAG
            .get(usize::from(self.dq_k))
            .copied()
            .ok_or(Error::Malformed("quantization table index"))?;
        let slot = self
            .qt
            .get_mut(usize::from(self.dq_tq))
            .and_then(|t| t.get_mut(usize::from(nat)))
            .ok_or(Error::Malformed("quantization table index"))?;
        // Listed: a zero quantizer is accepted (it zeroes the coefficient).
        *slot = v;
        self.dq_k = self.dq_k.saturating_add(1);
        if self.dq_k >= 64 {
            if let Some(d) = self.qt_def.get_mut(usize::from(self.dq_tq)) {
                *d = true;
            }
            self.dq_stage = 0;
        }
        Ok(())
    }

    /// One byte of a DHT body (B.2.4.2): `Tc|Th`, 16 counts `Li`, then the
    /// `Vij` symbols.
    fn dht_byte(&mut self, b: u8) -> Result<(), Error> {
        match self.ht_stage {
            0 => {
                let (tc, th) = (b >> 4, b & 15);
                if tc > 1 || th > 3 {
                    return bad("bad Huffman table header");
                }
                self.ht_class = b;
                self.ht_i = 0;
                self.ht_total = 0;
                self.ht_stage = 1;
            }
            1 => {
                if let Some(c) = self.ht_counts.get_mut(usize::from(self.ht_i)) {
                    *c = b;
                }
                self.ht_total = self.ht_total.saturating_add(u16::from(b));
                self.ht_i = self.ht_i.saturating_add(1);
                if self.ht_i >= 16 {
                    if self.ht_total > 256 {
                        return bad("a Huffman table over 256 symbols");
                    }
                    self.ht_i = 0;
                    self.ht_stage = 2;
                    if self.ht_total == 0 {
                        self.dht_done()?;
                    }
                }
            }
            _ => {
                if let Some(s) = self.ht_syms.get_mut(usize::from(self.ht_i)) {
                    *s = b;
                }
                self.ht_i = self.ht_i.saturating_add(1);
                if self.ht_i >= self.ht_total {
                    self.dht_done()?;
                }
            }
        }
        Ok(())
    }

    /// A Huffman table is fully read: build it (Annex C) and store it.
    fn dht_done(&mut self) -> Result<(), Error> {
        let symbols = self
            .ht_syms
            .get(..usize::from(self.ht_total))
            .ok_or(Error::Malformed("Huffman symbols"))?;
        let dc = self.ht_class >> 4 == 0;
        let table = Table::build(&self.ht_counts, symbols, dc).map_err(Error::Malformed)?;
        let th = usize::from(self.ht_class & 15);
        let slot = if dc {
            self.dc.get_mut(th)
        } else {
            self.ac.get_mut(th)
        };
        *slot.ok_or(Error::Malformed("Huffman destination"))? = Some(table);
        self.ht_stage = 0;
        Ok(())
    }

    /// The last byte of a segment's body was read (or it had none).
    fn end_segment(&mut self) -> Result<(), Error> {
        let total = self.seg_total;
        match self.marker {
            0xC0 | 0xC1 => self.finish_frame()?,
            0xDA => return self.finish_scan_header(),
            0xDD => {
                // B.2.4.4: `Lr` = 4, then `Ri`.
                if total != 2 {
                    return bad("DRI of the wrong length");
                }
                self.restart_interval = self.u16_hold(0);
            }
            0xE0 => self.jfif = total >= 14 && self.hold.get(..5) == Some(b"JFIF\0"),
            0xEE => {
                if total >= 12 && self.hold.get(..5) == Some(b"Adobe") {
                    self.adobe = Some(self.hold_at(11));
                }
            }
            0xE1 => {
                if !self.frame_set && !self.seen_orientation {
                    let n = usize::from(total).min(exif::MAX_BYTES);
                    if let Some(o) = self.exif.get(..n).and_then(exif::orientation) {
                        self.orientation = o;
                        self.seen_orientation = true;
                    }
                }
            }
            0xDB if self.dq_stage != 0 => return bad("a quantization table cut short"),
            0xC4 if self.ht_stage != 0 => return bad("a Huffman table cut short"),
            _ => {}
        }
        self.phase = Phase::Marker0;
        Ok(())
    }

    /// The frame header is read (B.2.2, Figure B.3).
    fn finish_frame(&mut self) -> Result<(), Error> {
        let (p, y, x, nf) = (
            self.hold_at(0),
            self.u16_hold(1),
            self.u16_hold(3),
            usize::from(self.hold_at(5)),
        );
        if p != 8 {
            return Err(Error::Unsupported("a sample precision other than 8 bits"));
        }
        if nf == 0 {
            return bad("a frame with no components");
        }
        if !matches!(nf, 1 | 3 | 4) {
            return Err(Error::Unsupported("a component count other than 1, 3, 4"));
        }
        if usize::from(self.seg_total) != nf.saturating_mul(3).saturating_add(6) {
            return bad("frame header of the wrong length");
        }
        if x == 0 {
            return bad("an image of width 0");
        }
        if y == 0 {
            return bad("an image of height 0 (DNL is not supported)");
        }
        let (cw, ch) = if swaps(self.orientation) {
            (y, x)
        } else {
            (x, y)
        };
        if u32::from(cw) != self.config.width() || u32::from(ch) != self.config.height() {
            return bad("frame size differs from the config");
        }
        let mut comps = [Comp::EMPTY; MAX_COMPONENTS];
        let (mut hmax, mut vmax) = (1u8, 1u8);
        for (i, c) in comps.iter_mut().take(nf).enumerate() {
            let at = i.saturating_mul(3).saturating_add(6);
            let hv = self.hold_at(at.saturating_add(1));
            c.id = self.hold_at(at);
            c.h = hv >> 4;
            c.v = hv & 15;
            c.tq = self.hold_at(at.saturating_add(2));
            if !(1..=4).contains(&c.h) || !(1..=4).contains(&c.v) || c.tq > 3 {
                return bad("a sampling factor or table selector out of range");
            }
            hmax = hmax.max(c.h);
            vmax = vmax.max(c.v);
        }
        // Components must be told apart in a scan by their ids.
        for i in 0..nf {
            for j in 0..i {
                if comps.get(i).map(|c| c.id) == comps.get(j).map(|c| c.id) {
                    return bad("two components with one id");
                }
            }
        }
        let (xs, ys) = (usize::from(x), usize::from(y));
        let mcus_x = ceil_div(xs, 8 * usize::from(hmax)).ok_or(Error::Malformed("size"))?;
        let mcus_y = ceil_div(ys, 8 * usize::from(vmax)).ok_or(Error::Malformed("size"))?;
        let mut off = 0usize;
        for c in comps.iter_mut().take(nf) {
            if hmax.checked_rem(c.h) != Some(0) || vmax.checked_rem(c.v) != Some(0) {
                return Err(Error::Unsupported("fractional sampling ratios"));
            }
            let size = |n: usize, f: u8, max: u8| {
                ceil_div(n.checked_mul(usize::from(f))?, usize::from(max))
            };
            c.width = size(xs, c.h, hmax)
                .and_then(|v| u16::try_from(v).ok())
                .ok_or(Error::Malformed("size"))?;
            c.height = size(ys, c.v, vmax)
                .and_then(|v| u16::try_from(v).ok())
                .ok_or(Error::Malformed("size"))?;
            c.blocks_w = mcus_x
                .checked_mul(usize::from(c.h))
                .and_then(|v| u16::try_from(v).ok())
                .ok_or(Error::Malformed("size"))?;
            c.blocks_h = mcus_y
                .checked_mul(usize::from(c.v))
                .and_then(|v| u16::try_from(v).ok())
                .ok_or(Error::Malformed("size"))?;
            c.off = off;
            off = c
                .plane_len()
                .and_then(|l| off.checked_add(l))
                .ok_or(Error::Malformed("size"))?;
        }
        if off > self.work_len {
            return bad("planes do not fit the work buffer");
        }
        self.width = x;
        self.height = y;
        self.ncomp = u8::try_from(nf).map_err(|_| Error::Malformed("components"))?;
        self.hmax = hmax;
        self.vmax = vmax;
        self.mcus_x = u16::try_from(mcus_x).map_err(|_| Error::Malformed("size"))?;
        self.mcus_y = u16::try_from(mcus_y).map_err(|_| Error::Malformed("size"))?;
        self.comps = comps;
        self.planes_len = off;
        self.frame_set = true;
        Ok(())
    }

    /// The scan header is read (B.2.3, Figure B.4); the entropy-coded
    /// segment starts with the next byte.
    fn finish_scan_header(&mut self) -> Result<(), Error> {
        let ns = usize::from(self.hold_at(0));
        if ns == 0 || ns > usize::from(self.ncomp) {
            return bad("a scan with a wrong number of components");
        }
        if usize::from(self.seg_total) != ns.saturating_mul(2).saturating_add(4) {
            return bad("scan header of the wrong length");
        }
        // `Ss`, `Se`, `Ah`, `Al` follow; for sequential processes they are
        // 0, 63, 0, 0 (B.2.3, Table B.3) and libjpeg-turbo only warns
        // otherwise, so they are ignored.
        let mut scan = Scan {
            n: u8::try_from(ns).map_err(|_| Error::Malformed("components"))?,
            comp: [0; MAX_COMPONENTS],
            interleaved: ns > 1,
            per_mcu: 0,
            mcus_x: 0,
            mcus_y: 0,
            mx: 0,
            my: 0,
            bi: 0,
            in_interval: 0,
            next_rst: 0,
            state: ScanState::Decoding,
        };
        let mut blocks = 0usize;
        for j in 0..ns {
            let cs = self.hold_at(j.saturating_mul(2).saturating_add(1));
            let tdta = self.hold_at(j.saturating_mul(2).saturating_add(2));
            let ci = self
                .comps
                .iter()
                .take(usize::from(self.ncomp))
                .position(|c| c.id == cs)
                .ok_or(Error::Malformed("a scan names a component the frame lacks"))?;
            if scan.comp.iter().take(j).any(|&p| usize::from(p) == ci) {
                return bad("a component twice in a scan");
            }
            let (td, ta) = (tdta >> 4, tdta & 15);
            if td > 3 || ta > 3 {
                return bad("a Huffman table selector out of range");
            }
            if self.dc.get(usize::from(td)).is_none_or(|t| t.is_none())
                || self.ac.get(usize::from(ta)).is_none_or(|t| t.is_none())
            {
                return bad("a scan uses a Huffman table that was not defined");
            }
            let comp = self
                .comps
                .get_mut(ci)
                .ok_or(Error::Malformed("component"))?;
            if !self
                .qt_def
                .get(usize::from(comp.tq))
                .copied()
                .unwrap_or(false)
            {
                return bad("a scan uses a quantization table that was not defined");
            }
            comp.q = self
                .qt
                .get(usize::from(comp.tq))
                .copied()
                .unwrap_or([1; 64]);
            comp.dc_sel = td;
            comp.ac_sel = ta;
            comp.pred = 0;
            comp.done = false;
            blocks = blocks
                .checked_add(usize::from(comp.h).saturating_mul(usize::from(comp.v)))
                .ok_or(Error::Malformed("blocks"))?;
            if let Some(slot) = scan.comp.get_mut(j) {
                *slot = u8::try_from(ci).map_err(|_| Error::Malformed("component"))?;
            }
        }
        if scan.interleaved {
            // B.2.3: at most 10 blocks in an MCU.
            if blocks > 10 {
                return bad("more than 10 blocks in an MCU");
            }
            scan.per_mcu = u8::try_from(blocks).map_err(|_| Error::Malformed("blocks"))?;
            scan.mcus_x = self.mcus_x;
            scan.mcus_y = self.mcus_y;
        } else {
            // A.2.4: a single component is scanned block by block over its
            // own size, not padded to whole MCUs.
            let c = self
                .comps
                .get(usize::from(scan.comp.first().copied().unwrap_or(0)))
                .ok_or(Error::Malformed("component"))?;
            scan.per_mcu = 1;
            scan.mcus_x = u16::try_from(ceil_div(usize::from(c.width), 8).unwrap_or(0))
                .map_err(|_| Error::Malformed("size"))?;
            scan.mcus_y = u16::try_from(ceil_div(usize::from(c.height), 8).unwrap_or(0))
                .map_err(|_| Error::Malformed("size"))?;
        }
        self.scan = scan;
        self.block = Block::new();
        self.bits = BitReader::empty();
        self.ff = false;
        self.phase = Phase::Entropy;
        Ok(())
    }

    /// One byte of an entropy-coded segment (B.1.1.5, E.1.2): `Some(m)` if
    /// the byte ends the segment with marker `m` (not a restart marker).
    pub(crate) fn entropy_byte(&mut self, b: u8, work: &mut [u8]) -> Result<Option<u8>, Error> {
        if !self.ff {
            if b == 0xFF {
                self.ff = true;
            } else {
                self.data_byte(b, work)?;
            }
            return Ok(None);
        }
        match b {
            // B.1.1.5: `0xFF 0x00` is the data byte `0xFF`.
            0x00 => {
                self.ff = false;
                self.data_byte(0xFF, work)?;
            }
            // Fill bytes before a marker (B.1.1.2).
            0xFF => {}
            0xD0..=0xD7 => {
                self.ff = false;
                self.restart(b)?;
            }
            m => {
                self.ff = false;
                if self.scan.state != ScanState::Complete {
                    return bad("a marker inside the scan data");
                }
                return Ok(Some(m));
            }
        }
        Ok(None)
    }

    /// `RSTm` (E.1.2): resets the predictors and starts the next interval.
    fn restart(&mut self, m: u8) -> Result<(), Error> {
        if self.scan.state != ScanState::AwaitRestart {
            return bad("an unexpected restart marker");
        }
        if m != 0xD0u8.saturating_add(self.scan.next_rst) {
            return bad("restart markers out of order");
        }
        self.scan.next_rst = self.scan.next_rst.saturating_add(1) & 7;
        self.bits.clear();
        for c in self.comps.iter_mut() {
            c.pred = 0;
        }
        self.block = Block::new();
        self.scan.state = ScanState::Decoding;
        Ok(())
    }

    /// A data byte of the entropy-coded segment: its bits, one at a time,
    /// into the block decoder.
    fn data_byte(&mut self, b: u8, work: &mut [u8]) -> Result<(), Error> {
        if self.scan.state != ScanState::Decoding {
            // Extraneous bytes before the marker (a padded last byte, or
            // garbage): ignored, as libjpeg-turbo does with a warning.
            return Ok(());
        }
        self.bits.load(b);
        while self.scan.state == ScanState::Decoding {
            let Some(bit) = self.bits.next_bit() else {
                break;
            };
            self.block_bit(bit, work)?;
        }
        Ok(())
    }

    /// The frame index of the component and the block position of the
    /// block being decoded (A.2.3: blocks of an MCU in the order of the
    /// components in the scan, each `Hi` by `Vi` in raster order).
    fn current_block(&self) -> Option<(usize, usize, usize)> {
        let s = &self.scan;
        if !s.interleaved {
            let ci = usize::from(s.comp.first().copied()?);
            return Some((ci, usize::from(s.mx), usize::from(s.my)));
        }
        let mut rem = usize::from(s.bi);
        for slot in 0..usize::from(s.n) {
            let ci = usize::from(s.comp.get(slot).copied()?);
            let c = self.comps.get(ci)?;
            let (h, v) = (usize::from(c.h), usize::from(c.v));
            let n = h.checked_mul(v)?;
            if rem < n {
                let (by, bx) = (rem.checked_div(h)?, rem.checked_rem(h)?);
                return Some((
                    ci,
                    usize::from(s.mx).checked_mul(h)?.checked_add(bx)?,
                    usize::from(s.my).checked_mul(v)?.checked_add(by)?,
                ));
            }
            rem = rem.checked_sub(n)?;
        }
        None
    }

    /// One bit of the entropy-coded data: to the block decoder, and when it
    /// finishes a block, dequantize, transform, store, and move on.
    pub(crate) fn block_bit(&mut self, bit: u8, work: &mut [u8]) -> Result<(), Error> {
        let (ci, bx, by) = self
            .current_block()
            .ok_or(Error::Malformed("block position"))?;
        let comp = self.comps.get(ci).ok_or(Error::Malformed("component"))?;
        let (Some(Some(dc)), Some(Some(ac))) = (
            self.dc.get(usize::from(comp.dc_sel)),
            self.ac.get(usize::from(comp.ac_sel)),
        ) else {
            return bad("Huffman table missing");
        };
        let mut pred = comp.pred;
        let done = self
            .block
            .bit(bit, dc, ac, &mut pred)
            .map_err(Error::Malformed)?;
        let comp = self
            .comps
            .get_mut(ci)
            .ok_or(Error::Malformed("component"))?;
        comp.pred = pred;
        if !done {
            return Ok(());
        }
        self.store_block(ci, bx, by, work)
    }

    /// The block is complete: A.3.3's inverse DCT into the plane at block
    /// position `(bx, by)` of component `ci`, then on to the next block.
    fn store_block(
        &mut self,
        ci: usize,
        bx: usize,
        by: usize,
        work: &mut [u8],
    ) -> Result<(), Error> {
        let comp = self.comps.get(ci).ok_or(Error::Malformed("component"))?;
        let samples = idct(&self.block.coef, &comp.q).ok_or(Error::Malformed("IDCT overflow"))?;
        let (bw, bh) = (usize::from(comp.blocks_w), usize::from(comp.blocks_h));
        if bx >= bw || by >= bh {
            return bad("block outside the plane");
        }
        let stride = comp.stride();
        let origin = by
            .checked_mul(8)
            .and_then(|r| r.checked_mul(stride))
            .and_then(|r| r.checked_add(bx.checked_mul(8)?))
            .and_then(|r| r.checked_add(comp.off))
            .ok_or(Error::Malformed("plane position"))?;
        for (r, row) in samples.as_chunks::<8>().0.iter().enumerate() {
            let at = r
                .checked_mul(stride)
                .and_then(|d| d.checked_add(origin))
                .ok_or(Error::Malformed("plane position"))?;
            let end = at
                .checked_add(8)
                .ok_or(Error::Malformed("plane position"))?;
            work.get_mut(at..end)
                .ok_or(Error::Malformed("plane position"))?
                .copy_from_slice(row);
        }
        self.advance();
        Ok(())
    }

    /// Moves to the next block, MCU, restart interval or the end of the
    /// scan.
    fn advance(&mut self) {
        self.block = Block::new();
        let s = &mut self.scan;
        s.bi = s.bi.saturating_add(1);
        if s.bi < s.per_mcu {
            return;
        }
        s.bi = 0;
        s.mx = s.mx.saturating_add(1);
        if s.mx >= s.mcus_x {
            s.mx = 0;
            s.my = s.my.saturating_add(1);
        }
        s.in_interval = s.in_interval.saturating_add(1);
        if s.my >= s.mcus_y {
            s.state = ScanState::Complete;
            let n = usize::from(s.n);
            let picks = s.comp;
            for &ci in picks.iter().take(n) {
                if let Some(c) = self.comps.get_mut(usize::from(ci)) {
                    c.done = true;
                }
            }
        } else if self.restart_interval != 0 && s.in_interval >= self.restart_interval {
            // E.1.2: the interval is over; `RSTm` must follow.
            s.in_interval = 0;
            s.state = ScanState::AwaitRestart;
            self.bits.clear();
        }
    }

    /// The pixel at source position `(x, y)`: upsample, convert colour.
    fn pixel(
        &self,
        planes: &[Option<Plane<'_>>; MAX_COMPONENTS],
        x: usize,
        y: usize,
    ) -> Option<[u8; 4]> {
        let s = |i: usize| -> Option<u8> { planes.get(i).copied().flatten()?.sample(x, y) };
        let rgb = match self.colour() {
            Colour::Gray => {
                let g = s(0)?;
                [g, g, g]
            }
            Colour::Rgb => [s(0)?, s(1)?, s(2)?],
            Colour::YCbCr => ycc_to_rgb(s(0)?, s(1)?, s(2)?),
            Colour::Cmyk => cmyk_to_rgb(s(0)?, s(1)?, s(2)?, s(3)?),
            Colour::Ycck => {
                let [c, m, y, k] = ycck_to_cmyk(s(0)?, s(1)?, s(2)?, s(3)?);
                cmyk_to_rgb(c, m, y, k)
            }
        };
        let [r, g, b] = rgb;
        Some([r, g, b, 255])
    }

    /// After EOI: the planes become RGBA pixels (upsampling, colour
    /// conversion, orientation).
    pub(crate) fn render(&self, pixels: &mut [u8], work: &[u8]) -> Result<(), Error> {
        let (w, h) = (usize::from(self.width), usize::from(self.height));
        let o = self.orientation;
        let dw = if swaps(o) { h } else { w };
        let want = w
            .checked_mul(h)
            .and_then(|n| n.checked_mul(4))
            .ok_or(Error::Malformed("size"))?;
        if pixels.len() != want {
            return Err(Error::Buffers);
        }
        let mut planes: [Option<Plane<'_>>; MAX_COMPONENTS] = [None; MAX_COMPONENTS];
        for (slot, c) in planes
            .iter_mut()
            .zip(self.comps.iter().take(usize::from(self.ncomp)))
        {
            let len = c.plane_len().ok_or(Error::Malformed("size"))?;
            let end = c.off.checked_add(len).ok_or(Error::Malformed("size"))?;
            *slot = Some(Plane {
                data: work.get(c.off..end).ok_or(Error::Malformed("plane"))?,
                stride: c.stride(),
                width: usize::from(c.width),
                height: usize::from(c.height),
                hs: usize::from(self.hmax.checked_div(c.h).unwrap_or(1)),
                vs: usize::from(self.vmax.checked_div(c.v).unwrap_or(1)),
            });
        }
        for y in 0..h {
            for x in 0..w {
                let px = self
                    .pixel(&planes, x, y)
                    .ok_or(Error::Malformed("sample outside its plane"))?;
                let (dx, dy) = orient(o, w, h, x, y).ok_or(Error::Malformed("orientation"))?;
                let at = dy
                    .checked_mul(dw)
                    .and_then(|r| r.checked_add(dx))
                    .and_then(|p| p.checked_mul(4))
                    .ok_or(Error::Malformed("size"))?;
                let end = at.checked_add(4).ok_or(Error::Malformed("size"))?;
                pixels
                    .get_mut(at..end)
                    .ok_or(Error::Malformed("pixel position"))?
                    .copy_from_slice(&px);
            }
        }
        Ok(())
    }

    /// Everything in the state that `step` indexes with or counts by.
    pub(crate) fn state_inv(&self) -> bool {
        let comps_ok = !self.frame_set
            || (usize::from(self.ncomp) <= MAX_COMPONENTS
                && self.ncomp >= 1
                && self.planes_len <= self.work_len
                && self.comps.iter().take(usize::from(self.ncomp)).all(|c| {
                    (1..=4).contains(&c.h)
                        && (1..=4).contains(&c.v)
                        && c.tq <= 3
                        && c.plane_len()
                            .and_then(|l| c.off.checked_add(l))
                            .is_some_and(|e| e <= self.planes_len)
                }));
        let scan_ok = self.phase != Phase::Entropy
            || (self.frame_set
                && self.scan.n >= 1
                && self.scan.n <= self.ncomp
                && self
                    .scan
                    .comp
                    .iter()
                    .take(usize::from(self.scan.n))
                    .all(|&c| c < self.ncomp)
                && self.scan.per_mcu >= 1
                && self.scan.bi < self.scan.per_mcu
                && (self.scan.state == ScanState::Complete
                    || (self.scan.mx < self.scan.mcus_x && self.scan.my < self.scan.mcus_y)));
        self.bits.inv()
            && self.block.inv()
            && usize::from(self.seg_pos) <= usize::from(self.seg_total)
            && (1..=8).contains(&self.orientation)
            && comps_ok
            && scan_ok
    }
}

impl Decoder for Jpeg {
    fn decode_config(prefix: &[u8]) -> Result<ConfigStatus, Error> {
        crate::header::config(prefix)
    }

    fn work_len(config: &Config) -> Result<usize, Error> {
        plane_bound(config.width(), config.height())
    }

    fn start(config: &Config) -> Result<Jpeg, Error> {
        if config.format() != Format::Jpeg {
            return Err(Error::Unsupported("not a JPEG config"));
        }
        config.rgba_len()?;
        let work_len = Self::work_len(config)?;
        Ok(Jpeg {
            config: *config,
            work_len,
            phase: Phase::Soi0,
            marker: 0,
            len_hi: 0,
            seg_total: 0,
            seg_pos: 0,
            hold: [0; HOLD],
            exif: [0; exif::MAX_BYTES],
            qt: [[1; 64]; 4],
            qt_def: [false; 4],
            dc: [None; 4],
            ac: [None; 4],
            dq_stage: 0,
            dq_wide: false,
            dq_tq: 0,
            dq_k: 0,
            dq_hi: None,
            ht_stage: 0,
            ht_class: 0,
            ht_i: 0,
            ht_counts: [0; 16],
            ht_syms: [0; 256],
            ht_total: 0,
            restart_interval: 0,
            jfif: false,
            adobe: None,
            orientation: 1,
            seen_orientation: false,
            frame_set: false,
            width: 0,
            height: 0,
            ncomp: 0,
            hmax: 1,
            vmax: 1,
            mcus_x: 0,
            mcus_y: 0,
            comps: [Comp::EMPTY; MAX_COMPONENTS],
            planes_len: 0,
            scan: Scan {
                n: 0,
                comp: [0; MAX_COMPONENTS],
                interleaved: false,
                per_mcu: 0,
                mcus_x: 0,
                mcus_y: 0,
                mx: 0,
                my: 0,
                bi: 0,
                in_interval: 0,
                next_rst: 0,
                state: ScanState::Decoding,
            },
            block: Block::new(),
            bits: BitReader::empty(),
            ff: false,
        })
    }

    fn config(&self) -> &Config {
        &self.config
    }

    fn step(&mut self, chunk: &[u8], buffers: &mut Buffers<'_>) -> Result<Step, Error> {
        match self.phase {
            Phase::Spent => return Err(Error::Spent),
            Phase::Done => return Err(Error::NoMoreFrames),
            _ => {}
        }
        if buffers.work.len() != self.work_len {
            return Err(self.fail(Error::Buffers));
        }
        for (i, &b) in chunk.iter().enumerate() {
            match self.byte(b, buffers.work) {
                Ok(false) => {}
                Ok(true) => {
                    return match self.render(buffers.pixels, buffers.work) {
                        Ok(()) => Ok(Step {
                            consumed: i.saturating_add(1),
                            status: Status::FrameDone,
                        }),
                        Err(e) => Err(self.fail(e)),
                    };
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
        buffers.pixels.len() == plen
            && buffers.work.len() == self.work_len
            && Self::work_len(&self.config) == Ok(self.work_len)
            && (self.phase == Phase::Spent || self.state_inv())
    }
}

/// The frame count of every JPEG.
pub(crate) const FRAMES: FrameCount = FrameCount::Known(1);

#[cfg(kani)]
#[path = "decoder_proofs.rs"]
mod proofs;

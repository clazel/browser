//! The resumable decoder: RFC 1951 and RFC 1950 as a state machine that is
//! given input and output space in pieces of any size.
//!
//! [`Inflater::step`] reads from `src` and writes to `dst` until it needs
//! more of one or the other, and says which. It keeps the last 32 KiB of
//! output in a window the caller owns, so decoding allocates nothing after
//! [`Inflater::new`]. Every element of the format (a block header, a Huffman
//! code, a run of extra bits, a stored length) is read whole or not at all
//! and every other piece of progress is in `Phase`, so cutting the input
//! anywhere cannot change the result: [`super::contract::chunked_ensures`].
//!
//! The order of the checks is the order of [`super::spec`], which this
//! follows function by function (each handler's comment says which).

use super::adler;
use super::huffman::{Lookup, Table};
use super::spec::Error;

/// The size of the window the caller provides: RFC 1951 §3.2.5's largest
/// distance, 32,768.
pub const WINDOW_LEN: usize = 32768;

/// `WINDOW_LEN - 1`: the window is a ring indexed by output position.
const WINDOW_MASK: u64 = 32767;

/// What is being decoded.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Format {
    /// RFC 1951: blocks, nothing else.
    Raw,
    /// RFC 1950: header, blocks, Adler-32.
    Zlib,
}

/// Why [`Inflater::step`] returned.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Status {
    /// All of `src` was read; give it more.
    NeedInput,
    /// `dst` is full; give it more room.
    NeedOutput,
    /// The stream is complete.
    Done,
    /// The stream is wrong, or too long for the limit; every later step
    /// returns the same.
    Failed(Error),
    /// `window` is not [`WINDOW_LEN`] bytes. Nothing was read or written.
    BadWindow,
}

/// What a call to [`Inflater::step`] did.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Step {
    /// Bytes of `src` read.
    pub consumed: usize,
    /// Bytes written to `dst`.
    pub produced: usize,
    /// Why it stopped.
    pub status: Status,
}

/// Where the decoder is. Only the data that cannot be recomputed from the
/// bits already read is kept.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Phase {
    /// RFC 1950 §2.2: CMF and FLG.
    ZlibHeader,
    /// RFC 1951 §3.2.3: BFINAL and BTYPE.
    BlockHeader,
    /// §3.2.4: LEN and NLEN.
    StoredHeader,
    /// §3.2.4: this many bytes of literal data left.
    StoredCopy(u32),
    /// §3.2.7: HLIT, HDIST, HCLEN.
    DynCounts,
    /// §3.2.7: the code length code's lengths, the `ci`-th next.
    DynClLens,
    /// §3.2.7: a symbol of the code length code.
    DynLens,
    /// §3.2.7: the extra bits of code length symbol 16, 17 or 18.
    DynRepeat(u8),
    /// §3.2.3: a literal/length symbol.
    Data,
    /// §3.2.3: this literal is decided and waits for room in `dst`.
    Literal(u8),
    /// §3.2.5: the extra bits of this length symbol (257 to 285).
    LenExtra(u16),
    /// §3.2.5: the distance symbol of a match of this length.
    DistSym(u32),
    /// §3.2.5: the extra bits of this distance symbol (0 to 29), the match
    /// being this long.
    DistExtra(u32, u8),
    /// §3.2.3: copy this many more bytes from this far back.
    Copy(u32, u32),
    /// RFC 1950 §2.2: ADLER32.
    Trailer,
    /// Finished.
    Done,
    /// Failed.
    Failed(Error),
}

/// A resumable decoder. About 200 KiB, mostly its three code tables.
pub struct Inflater {
    format: Format,
    phase: Phase,
    /// The most output allowed, in bytes.
    limit: u64,
    /// Output so far.
    total_out: u64,
    /// Bits read from `src` and not used yet, first bit lowest. Between
    /// elements fewer than 8: a byte is only taken when an element needs
    /// bits it has not got.
    bitbuf: u64,
    nbits: u32,
    s1: u32,
    s2: u32,
    last_block: bool,
    hlit: usize,
    hdist: usize,
    hclen: usize,
    /// How many code length code lengths (in `DynClLens`) or code lengths
    /// (in `DynLens`) have been read.
    ci: usize,
    cl_lens: [u8; 19],
    lens: [u8; 320],
    lit: Table,
    dist: Table,
    cl: Table,
}

/// RFC 1951 §3.2.7: the order of the code length code's lengths.
const CL_ORDER: [u8; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

/// §3.2.5, first table: the smallest length of code 257 + i.
const LEN_BASE: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];

/// §3.2.5, first table: the extra bits of code 257 + i.
const LEN_EXTRA: [u8; 29] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0,
];

/// §3.2.5, second table: the smallest distance of code i.
const DIST_BASE: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];

/// §3.2.5, second table: the extra bits of code i.
const DIST_EXTRA: [u8; 30] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13,
];

fn get<T: Copy>(s: &[T], i: usize, default: T) -> T {
    s.get(i).copied().unwrap_or(default)
}

fn set<T>(s: &mut [T], i: usize, v: T) {
    if let Some(slot) = s.get_mut(i) {
        *slot = v;
    }
}

/// The buffers of one call.
struct Io<'a> {
    src: &'a [u8],
    si: usize,
    dst: &'a mut [u8],
    di: usize,
    window: &'a mut [u8],
}

/// Why a phase handler did not finish its element.
enum Halt {
    Input,
    Output,
    Fail(Error),
}

/// Which code a symbol is read with.
#[derive(Clone, Copy)]
enum Which {
    Lit,
    Dist,
    Cl,
}

/// Decoding one Huffman code.
enum Sym {
    Found(u16),
    NeedInput,
    Invalid,
}

impl Inflater {
    /// A decoder for `format` that fails with [`Error::OutputLimit`] rather
    /// than produce more than `limit` bytes.
    pub fn new(format: Format, limit: u64) -> Inflater {
        Inflater {
            format,
            phase: match format {
                Format::Raw => Phase::BlockHeader,
                Format::Zlib => Phase::ZlibHeader,
            },
            limit,
            total_out: 0,
            bitbuf: 0,
            nbits: 0,
            s1: 1,
            s2: 0,
            last_block: false,
            hlit: 0,
            hdist: 0,
            hclen: 0,
            ci: 0,
            cl_lens: [0; 19],
            lens: [0; 320],
            lit: Table::new(),
            dist: Table::new(),
            cl: Table::new(),
        }
    }

    /// Bytes produced so far.
    pub fn total_out(&self) -> u64 {
        self.total_out
    }

    /// The input has ended: if the stream is not complete it is
    /// [`Error::Truncated`] (or the error it had already hit).
    pub fn end_of_input(&mut self) -> Result<(), Error> {
        match self.phase {
            Phase::Done => Ok(()),
            Phase::Failed(e) => Err(e),
            _ => {
                self.phase = Phase::Failed(Error::Truncated);
                Err(Error::Truncated)
            }
        }
    }

    /// Decode as much as `src` and `dst` allow. `window` must be
    /// [`WINDOW_LEN`] bytes and the same buffer, untouched, on every call of
    /// one stream.
    pub fn step(&mut self, src: &[u8], dst: &mut [u8], window: &mut [u8]) -> Step {
        if window.len() != WINDOW_LEN {
            return Step {
                consumed: 0,
                produced: 0,
                status: Status::BadWindow,
            };
        }
        let mut io = Io {
            src,
            si: 0,
            dst,
            di: 0,
            window,
        };
        let status = self.run(&mut io);
        Step {
            consumed: io.si,
            produced: io.di,
            status,
        }
    }

    fn fail(&mut self, e: Error) -> Status {
        self.phase = Phase::Failed(e);
        Status::Failed(e)
    }

    /// Take one more byte of `src` into the bit buffer.
    fn pull(&mut self, io: &mut Io<'_>) -> bool {
        match io.src.get(io.si) {
            Some(&b) => {
                io.si = io.si.saturating_add(1);
                self.bitbuf |= u64::from(b) << self.nbits;
                self.nbits = self.nbits.saturating_add(8);
                true
            }
            None => false,
        }
    }

    /// Read a data element of `n` (at most 32) bits, first bit least
    /// significant (RFC 1951 §3.1.1). `None` if `src` ends first; the bytes
    /// it did take stay in the bit buffer.
    fn read(&mut self, io: &mut Io<'_>, n: u32) -> Option<u32> {
        while self.nbits < n {
            if !self.pull(io) {
                return None;
            }
        }
        let v = (self.bitbuf & (1u64 << n).saturating_sub(1)) as u32;
        self.bitbuf >>= n;
        self.nbits = self.nbits.saturating_sub(n);
        Some(v)
    }

    /// Read one Huffman code, most significant bit first.
    fn symbol(&mut self, io: &mut Io<'_>, which: Which) -> Sym {
        loop {
            let table = match which {
                Which::Lit => &self.lit,
                Which::Dist => &self.dist,
                Which::Cl => &self.cl,
            };
            match table.lookup(self.bitbuf, self.nbits) {
                Lookup::Found(sym, len) => {
                    self.bitbuf >>= len;
                    self.nbits = self.nbits.saturating_sub(u32::from(len));
                    return Sym::Found(sym);
                }
                Lookup::Invalid => return Sym::Invalid,
                Lookup::NeedMore => {
                    if !self.pull(io) {
                        return Sym::NeedInput;
                    }
                }
            }
        }
    }

    /// Append one byte of output to `dst`, the window and the checksum. The
    /// caller has checked there is room in `dst`.
    fn emit(&mut self, io: &mut Io<'_>, b: u8) {
        set(io.dst, io.di, b);
        io.di = io.di.saturating_add(1);
        let w = (self.total_out & WINDOW_MASK) as usize;
        set(io.window, w, b);
        self.total_out = self.total_out.saturating_add(1);
        let (a, c) = adler::update(self.s1, self.s2, &[b]);
        self.s1 = a;
        self.s2 = c;
    }

    /// The end of a block: the next block, or the end of the stream.
    fn block_end(&mut self) {
        if !self.last_block {
            self.phase = Phase::BlockHeader;
        } else if self.format == Format::Zlib {
            // "Any data which may appear after ADLER32 are not part of the
            // zlib stream": the trailer starts at the next byte, so the
            // rest of the current one is dropped.
            self.bitbuf = 0;
            self.nbits = 0;
            self.phase = Phase::Trailer;
        } else {
            self.phase = Phase::Done;
        }
    }

    fn run(&mut self, io: &mut Io<'_>) -> Status {
        loop {
            let result = match self.phase {
                Phase::Done => return Status::Done,
                Phase::Failed(e) => return Status::Failed(e),
                Phase::ZlibHeader => self.zlib_header(io),
                Phase::BlockHeader => self.block_header(io),
                Phase::StoredHeader => self.stored_header(io),
                Phase::StoredCopy(left) => self.stored_copy(io, left),
                Phase::DynCounts => self.dyn_counts(io),
                Phase::DynClLens => self.dyn_cl_lens(io),
                Phase::DynLens => self.dyn_lens(io),
                Phase::DynRepeat(sym) => self.dyn_repeat(io, sym),
                Phase::Data => self.data(io),
                Phase::Literal(b) => self.literal(io, b),
                Phase::LenExtra(sym) => self.len_extra(io, sym),
                Phase::DistSym(length) => self.dist_sym(io, length),
                Phase::DistExtra(length, d) => self.dist_extra(io, length, d),
                Phase::Copy(length, distance) => self.copy(io, length, distance),
                Phase::Trailer => self.trailer(io),
            };
            match result {
                Ok(()) => {}
                Err(Halt::Input) => return Status::NeedInput,
                Err(Halt::Output) => return Status::NeedOutput,
                Err(Halt::Fail(e)) => return self.fail(e),
            }
        }
    }

    /// RFC 1950 §2.2 and §2.3, as `spec::zlib_decompress`'s first checks.
    fn zlib_header(&mut self, io: &mut Io<'_>) -> Result<(), Halt> {
        let v = self.read(io, 16).ok_or(Halt::Input)?;
        let cmf = v & 0xFF;
        let flg = v >> 8;
        if cmf.saturating_mul(256).saturating_add(flg) % 31 != 0 {
            Err(Halt::Fail(Error::BadZlibCheck))
        } else if cmf % 16 != 8 {
            Err(Halt::Fail(Error::BadZlibMethod))
        } else if cmf / 16 > 7 {
            Err(Halt::Fail(Error::BadZlibWindow))
        } else if (flg / 32) % 2 == 1 {
            Err(Halt::Fail(Error::PresetDictionary))
        } else {
            self.phase = Phase::BlockHeader;
            Ok(())
        }
    }

    /// RFC 1951 §3.2.3: "3 header bits: first bit BFINAL, next 2 bits BTYPE".
    fn block_header(&mut self, io: &mut Io<'_>) -> Result<(), Halt> {
        let h = self.read(io, 3).ok_or(Halt::Input)?;
        self.last_block = h & 1 == 1;
        match h >> 1 {
            0 => {
                // §3.2.4: "Any bits of input up to the next byte boundary are
                // ignored." Fewer than 8 are buffered, all of them in the
                // current byte.
                self.bitbuf = 0;
                self.nbits = 0;
                self.phase = Phase::StoredHeader;
            }
            1 => {
                // §3.2.6: the fixed codes. Both are complete, so these cannot fail.
                let mut lens = [0u8; 288];
                let mut i = 0;
                while i < 288 {
                    set(&mut lens, i, fixed_lit_len(i));
                    i = i.saturating_add(1);
                }
                let _ = self.lit.build(&lens, false);
                let _ = self.dist.build(&[5u8; 32], false);
                self.phase = Phase::Data;
            }
            2 => self.phase = Phase::DynCounts,
            _ => return Err(Halt::Fail(Error::ReservedBlockType)),
        }
        Ok(())
    }

    /// §3.2.4, as `spec::stored_block`.
    fn stored_header(&mut self, io: &mut Io<'_>) -> Result<(), Halt> {
        let v = self.read(io, 32).ok_or(Halt::Input)?;
        let len = v & 0xFFFF;
        let nlen = v >> 16;
        if len.saturating_add(nlen) != 0xFFFF {
            return Err(Halt::Fail(Error::LengthComplementMismatch));
        }
        if self.total_out.saturating_add(u64::from(len)) > self.limit {
            return Err(Halt::Fail(Error::OutputLimit));
        }
        if len == 0 {
            self.block_end();
        } else {
            self.phase = Phase::StoredCopy(len);
        }
        Ok(())
    }

    fn stored_copy(&mut self, io: &mut Io<'_>, left: u32) -> Result<(), Halt> {
        let mut left = left;
        while left > 0 {
            let Some(&b) = io.src.get(io.si) else {
                self.phase = Phase::StoredCopy(left);
                return Err(Halt::Input);
            };
            if io.di >= io.dst.len() {
                self.phase = Phase::StoredCopy(left);
                return Err(Halt::Output);
            }
            io.si = io.si.saturating_add(1);
            self.emit(io, b);
            left = left.saturating_sub(1);
        }
        self.block_end();
        Ok(())
    }

    /// §3.2.7: "5 Bits: HLIT, 5 Bits: HDIST, 4 Bits: HCLEN".
    fn dyn_counts(&mut self, io: &mut Io<'_>) -> Result<(), Halt> {
        let v = self.read(io, 14).ok_or(Halt::Input)?;
        self.hlit = (v & 31) as usize + 257;
        self.hdist = ((v >> 5) & 31) as usize + 1;
        self.hclen = (v >> 10) as usize + 4;
        if self.hlit > 286 {
            return Err(Halt::Fail(Error::TooManyLengthCodes));
        }
        self.cl_lens = [0; 19];
        self.ci = 0;
        self.phase = Phase::DynClLens;
        Ok(())
    }

    /// §3.2.7: "(HCLEN + 4) x 3 bits: code lengths for the code length alphabet".
    fn dyn_cl_lens(&mut self, io: &mut Io<'_>) -> Result<(), Halt> {
        while self.ci < self.hclen {
            let v = self.read(io, 3).ok_or(Halt::Input)?;
            set(
                &mut self.cl_lens,
                usize::from(get(&CL_ORDER, self.ci, 0)),
                v as u8,
            );
            self.ci = self.ci.saturating_add(1);
        }
        if !self.cl.build(&self.cl_lens, false) {
            return Err(Halt::Fail(Error::BadCodeLengths));
        }
        self.ci = 0;
        self.phase = Phase::DynLens;
        Ok(())
    }

    /// §3.2.7: the code lengths of both alphabets, as one sequence.
    fn dyn_lens(&mut self, io: &mut Io<'_>) -> Result<(), Halt> {
        let total = self.hlit.saturating_add(self.hdist);
        while self.ci < total {
            match self.symbol(io, Which::Cl) {
                Sym::NeedInput => return Err(Halt::Input),
                Sym::Invalid => return Err(Halt::Fail(Error::InvalidCode)),
                Sym::Found(sym) => {
                    if sym < 16 {
                        set(&mut self.lens, self.ci, sym as u8);
                        self.ci = self.ci.saturating_add(1);
                    } else if sym == 16 && self.ci == 0 {
                        return Err(Halt::Fail(Error::RepeatWithoutPrevious));
                    } else {
                        self.phase = Phase::DynRepeat(sym as u8);
                        return Ok(());
                    }
                }
            }
        }
        self.finish_lengths()
    }

    /// The extra bits of code length symbol 16, 17 or 18, and the repeat.
    fn dyn_repeat(&mut self, io: &mut Io<'_>, sym: u8) -> Result<(), Halt> {
        let total = self.hlit.saturating_add(self.hdist);
        let (bits, base) = match sym {
            16 => (2, 3),
            17 => (3, 3),
            _ => (7, 11),
        };
        let e = self.read(io, bits).ok_or(Halt::Input)?;
        let r = (e as usize).saturating_add(base);
        if self.ci.saturating_add(r) > total {
            return Err(Halt::Fail(Error::RepeatTooLong));
        }
        let v = if sym == 16 {
            get(&self.lens, self.ci.saturating_sub(1), 0)
        } else {
            0
        };
        let mut k = 0;
        while k < r {
            set(&mut self.lens, self.ci, v);
            self.ci = self.ci.saturating_add(1);
            k = k.saturating_add(1);
        }
        // If the lengths are complete now, `dyn_lens` finishes them.
        self.phase = Phase::DynLens;
        Ok(())
    }

    /// All HLIT + HDIST code lengths are read: build the two codes.
    fn finish_lengths(&mut self) -> Result<(), Halt> {
        let lit_lens = self.lens.get(..self.hlit).unwrap_or(&[]);
        if get(lit_lens, 256, 0) == 0 {
            return Err(Halt::Fail(Error::NoEndOfBlock));
        }
        let total = self.hlit.saturating_add(self.hdist);
        let dist_lens = self.lens.get(self.hlit..total).unwrap_or(&[]);
        let lit_ok = self.lit.build(lit_lens, true);
        let dist_ok = self.dist.build(dist_lens, true);
        if !lit_ok || !dist_ok {
            return Err(Halt::Fail(Error::BadCodeLengths));
        }
        self.phase = Phase::Data;
        Ok(())
    }

    /// §3.2.3: "decode literal/length value from input stream".
    fn data(&mut self, io: &mut Io<'_>) -> Result<(), Halt> {
        match self.symbol(io, Which::Lit) {
            Sym::NeedInput => Err(Halt::Input),
            Sym::Invalid => Err(Halt::Fail(Error::InvalidCode)),
            Sym::Found(sym) => {
                if sym < 256 {
                    if self.total_out.saturating_add(1) > self.limit {
                        return Err(Halt::Fail(Error::OutputLimit));
                    }
                    self.phase = Phase::Literal(sym as u8);
                } else if sym == 256 {
                    self.block_end();
                } else if sym > 285 {
                    return Err(Halt::Fail(Error::InvalidSymbol));
                } else {
                    self.phase = Phase::LenExtra(sym);
                }
                Ok(())
            }
        }
    }

    fn literal(&mut self, io: &mut Io<'_>, b: u8) -> Result<(), Halt> {
        if io.di >= io.dst.len() {
            return Err(Halt::Output);
        }
        self.emit(io, b);
        self.phase = Phase::Data;
        Ok(())
    }

    fn len_extra(&mut self, io: &mut Io<'_>, sym: u16) -> Result<(), Halt> {
        let i = usize::from(sym).saturating_sub(257);
        let e = self
            .read(io, u32::from(get(&LEN_EXTRA, i, 0)))
            .ok_or(Halt::Input)?;
        let length = u32::from(get(&LEN_BASE, i, 0)).saturating_add(e);
        self.phase = Phase::DistSym(length);
        Ok(())
    }

    fn dist_sym(&mut self, io: &mut Io<'_>, length: u32) -> Result<(), Halt> {
        match self.symbol(io, Which::Dist) {
            Sym::NeedInput => Err(Halt::Input),
            Sym::Invalid => Err(Halt::Fail(Error::InvalidCode)),
            Sym::Found(d) => {
                if d > 29 {
                    return Err(Halt::Fail(Error::InvalidDistanceSymbol));
                }
                self.phase = Phase::DistExtra(length, d as u8);
                Ok(())
            }
        }
    }

    fn dist_extra(&mut self, io: &mut Io<'_>, length: u32, d: u8) -> Result<(), Halt> {
        let i = usize::from(d);
        let e = self
            .read(io, u32::from(get(&DIST_EXTRA, i, 0)))
            .ok_or(Halt::Input)?;
        let distance = u32::from(get(&DIST_BASE, i, 0)).saturating_add(e);
        if u64::from(distance) > self.total_out {
            return Err(Halt::Fail(Error::DistanceTooFar));
        }
        if self.total_out.saturating_add(u64::from(length)) > self.limit {
            return Err(Halt::Fail(Error::OutputLimit));
        }
        self.phase = Phase::Copy(length, distance);
        Ok(())
    }

    fn copy(&mut self, io: &mut Io<'_>, length: u32, distance: u32) -> Result<(), Halt> {
        let mut left = length;
        while left > 0 {
            if io.di >= io.dst.len() {
                self.phase = Phase::Copy(left, distance);
                return Err(Halt::Output);
            }
            let from = (self.total_out.saturating_sub(u64::from(distance)) & WINDOW_MASK) as usize;
            let b = get(io.window, from, 0);
            self.emit(io, b);
            left = left.saturating_sub(1);
        }
        self.phase = Phase::Data;
        Ok(())
    }

    /// RFC 1950 §2.2: ADLER32, "most-significant-byte first (network) order".
    fn trailer(&mut self, io: &mut Io<'_>) -> Result<(), Halt> {
        let v = self.read(io, 32).ok_or(Halt::Input)?;
        let stored = v.swap_bytes();
        if stored != (self.s2 << 16) | self.s1 {
            return Err(Halt::Fail(Error::AdlerMismatch));
        }
        self.phase = Phase::Done;
        Ok(())
    }
}

/// §3.2.6: the code length of literal/length symbol `sym`.
fn fixed_lit_len(sym: usize) -> u8 {
    if sym <= 143 {
        8
    } else if sym <= 255 {
        9
    } else if sym <= 279 {
        7
    } else {
        8
    }
}

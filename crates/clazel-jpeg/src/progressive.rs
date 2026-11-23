//! Progressive scans (phase-6.md item 6.6): ITU-T T.81 Annex G.
//!
//! A progressive frame (SOF2) is a sequence of scans, each decoding some of
//! the coefficients of the blocks of one or more components, to a point
//! transform `Al` (successive approximation) over a band `Ss..=Se` of
//! zig-zag positions (spectral selection). Four kinds exist (G.1.2,
//! Table G.1):
//!
//! - **DC first** (`Ss = 0`, `Ah = 0`, G.1.2.1, Figure G.2): the DC
//!   difference as in F.2.2.1, the coefficient shifted left by `Al`.
//! - **DC refinement** (`Ss = 0`, `Ah > 0`, G.1.2.1, Figure G.4): one bit
//!   per block, the coefficient's bit `Al`.
//! - **AC first** (`Ss > 0`, `Ah = 0`, G.1.2.2, Figure G.3): run/size
//!   symbols as in F.2.2.2 over the band, plus `EOBn` symbols that end `2^n
//!   + extra bits` blocks at once (the "EOB run").
//! - **AC refinement** (`Ss > 0`, `Ah > 0`, G.1.2.3, Figure G.7): for each
//!   coefficient that is already nonzero, one correction bit; for each
//!   newly nonzero coefficient (magnitude `2^Al`), a sign bit; runs and
//!   `EOBn` count the zero history only.
//!
//! The decoder here is a machine like [`crate::block::Block`]: one bit per
//! call, so it can stop between any two bits when a chunk ends. It works on
//! a copy of the block's 64 coefficients (natural order); the caller loads
//! the copy from the coefficient plane before the block's first bit and
//! stores it after the last.
//!
//! The coefficient plane is kept whole in the caller's work buffer, as
//! little-endian `i16`, 64 per block in raster order of blocks
//! (`block_base`). After the last scan [`finish_plane`] runs the inverse
//! DCT of every block into the 8-bit sample plane, **in the same memory**:
//! block rows are done from the last to the first and the sample plane
//! starts one block row's worth of samples past the end of the coefficients,
//! which is far enough that no write lands on a coefficient not yet read (the
//! argument is on [`finish_plane`]). So a component costs `2` bytes per padded
//! sample plus one block row, not `3`.
//!
//! Listed choices (see also `lib.rs`): the consistency of the point
//! transforms between scans (that a refinement scan's `Ah` is the `Al` of
//! the scan before it, G.1.1.1.1) is not checked, as libjpeg's is a warning
//! only: a refinement of a coefficient no first scan set only changes bits
//! that are zero. A run, `ZRL` or coefficient that passes the end of the
//! band is an error where libjpeg-turbo reads past it, as at the end of a
//! baseline block (`lib.rs`, choice 7), except that a `ZRL` that ends
//! exactly at or beyond `Se` ends the block quietly, as libjpeg does. A value
//! that does not fit 16 bits is an error.

use crate::block::{ZIGZAG, extend};
use crate::huffman::{Next, Table};
use crate::idct::idct;

/// The most scans of a progressive frame this decoder reads. libjpeg's
/// `jpeg_simple_progression` writes 10 for a colour image, mozjpeg's default
/// script and Photoshop's about the same; the cost of a scan is the blocks of
/// the image however little data it has (an `EOBn` run covers up to 32767
/// blocks per byte), so a never-ending sequence of scans is bounded here.
pub(crate) const MAX_SCANS: u16 = 100;

/// The four kinds of progressive scan (T.81 G.1.2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScanKind {
    /// `Ss = 0`, `Ah = 0`.
    DcFirst,
    /// `Ss = 0`, `Ah > 0`.
    DcRefine,
    /// `Ss > 0`, `Ah = 0`.
    AcFirst,
    /// `Ss > 0`, `Ah > 0`.
    AcRefine,
}

/// What the scan header (B.2.3, Table B.3) says, once checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Params {
    pub kind: ScanKind,
    /// First and last zig-zag position of the band (`Ss`, `Se`).
    pub ss: u8,
    pub se: u8,
    /// The point transform of this scan (`Al`).
    pub al: u8,
}

impl Params {
    /// The checks of Table B.3 for progressive DCT and of libjpeg-turbo's
    /// `start_pass` (`jdphuff.c`): a DC scan has `Se = 0`; an AC scan has
    /// `Ss <= Se <= 63` and one component; a refinement has `Al = Ah - 1`;
    /// `Al <= 13`.
    pub(crate) fn new(
        ss: u8,
        se: u8,
        ah: u8,
        al: u8,
        comps_in_scan: usize,
    ) -> Result<Params, &'static str> {
        if al > 13 {
            return Err("progressive scan: a point transform over 13");
        }
        if ah != 0 && ah.checked_sub(1) != Some(al) {
            return Err("progressive scan: Al is not Ah - 1");
        }
        let first = ah == 0;
        let kind = if ss == 0 {
            if se != 0 {
                return Err("progressive scan: a DC scan with Se over 0");
            }
            if first {
                ScanKind::DcFirst
            } else {
                ScanKind::DcRefine
            }
        } else {
            if ss > se || se > 63 {
                return Err("progressive scan: a band outside 1 to 63");
            }
            if comps_in_scan != 1 {
                return Err("progressive scan: an AC scan with several components");
            }
            if first {
                ScanKind::AcFirst
            } else {
                ScanKind::AcRefine
            }
        };
        Ok(Params { kind, ss, se, al })
    }
}

/// Where in the block's syntax the decoder is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Stage {
    /// Between blocks: [`Prog::begin`] is next.
    Idle,
    /// The Huffman code of `T`, the size category of a DC difference
    /// (Figure G.2: `DECODE`).
    DcCode,
    /// The `T` bits of the difference.
    DcBits,
    /// The one bit of a DC refinement (Figure G.4).
    DcBit,
    /// The Huffman code of `RS` (Figures G.3 and G.7).
    AcCode,
    /// The `SSSS` bits of an AC coefficient of a first scan.
    AcBits,
    /// The `R` extra bits of an `EOBn` symbol (G.1.2.2).
    EobBits,
    /// The sign bit of a coefficient a refinement scan makes nonzero
    /// (Figure G.7, `SSSS` is 1).
    SignBit,
    /// The correction bit of a coefficient already nonzero (Figure G.7).
    CorrBit,
}

/// What a refinement scan is doing between bits (Figure G.7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// Reading symbols.
    Symbol,
    /// Skipping zero-history coefficients (`R` of them) to place a new one
    /// (or, for `ZRL`, to skip 16), correcting the nonzero ones passed.
    Skip,
    /// In an EOB run: correcting every nonzero coefficient to `Se`.
    Eob,
}

/// One progressive block being decoded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Prog {
    p: Params,
    stage: Stage,
    mode: Mode,
    /// Huffman code read so far, `len` bits of it.
    code: u16,
    len: u8,
    /// Bits of the value being received, how many came, and their value.
    size: u8,
    got: u8,
    acc: u16,
    /// Zig-zag position of the next coefficient (`K`).
    k: u8,
    /// Zero-history coefficients left to skip before the new one (`R`), and
    /// the value the new one gets (0 for `ZRL`).
    run: u8,
    val: i16,
    /// Blocks left in the EOB run, not counting the one being decoded
    /// (`EOBRUN`). At most `2^14 + 2^14 - 1`.
    eobrun: u16,
    /// The coefficients of the block, natural order.
    pub blk: [i16; 64],
}

/// `1 << al` as an `i16`.
fn bit_of(al: u8) -> Option<i16> {
    1i16.checked_shl(u32::from(al))
}

/// The coefficient `v` with the point transform undone: `v * 2^al`, if it
/// fits 16 bits.
fn scaled(v: i32, al: u8) -> Result<i16, &'static str> {
    let f = 1i32.checked_shl(u32::from(al)).ok_or("point transform")?;
    let v = v.checked_mul(f).ok_or("coefficient out of range")?;
    i16::try_from(v).map_err(|_| "coefficient out of range")
}

impl Prog {
    /// A machine with no scan: idle, over zeros.
    pub(crate) const fn new() -> Prog {
        Prog {
            p: Params {
                kind: ScanKind::DcFirst,
                ss: 0,
                se: 0,
                al: 0,
            },
            stage: Stage::Idle,
            mode: Mode::Symbol,
            code: 0,
            len: 0,
            size: 0,
            got: 0,
            acc: 0,
            k: 0,
            run: 0,
            val: 0,
            eobrun: 0,
            blk: [0; 64],
        }
    }

    /// The start of a scan (or of a restart interval's first block): the
    /// EOB run is forgotten, no block is in progress.
    pub(crate) fn start_scan(&mut self, p: Params) {
        self.p = p;
        self.reset();
    }

    /// A restart marker (E.1.2): the EOB run ends with the interval.
    pub(crate) fn reset(&mut self) {
        self.stage = Stage::Idle;
        self.mode = Mode::Symbol;
        self.eobrun = 0;
    }

    /// Whether no block is in progress.
    pub(crate) fn idle(&self) -> bool {
        self.stage == Stage::Idle
    }

    /// The scan being decoded.
    pub(crate) fn params(&self) -> Params {
        self.p
    }

    /// The invariant: counters in their ranges, for the stage.
    pub(crate) fn inv(&self) -> bool {
        let band = match self.p.kind {
            ScanKind::DcFirst | ScanKind::DcRefine => self.p.ss == 0 && self.p.se == 0,
            ScanKind::AcFirst | ScanKind::AcRefine => {
                self.p.ss >= 1 && self.p.ss <= self.p.se && self.p.se <= 63
            }
        };
        let in_band = self.k <= self.p.se;
        band && self.p.al <= 13
            && self.len <= 16
            && self.size <= 15
            && self.got <= self.size
            && self.eobrun < 32768
            && match self.stage {
                Stage::Idle => true,
                Stage::DcCode => self.len < 16,
                Stage::DcBits => self.size >= 1 && self.got < self.size,
                Stage::DcBit => true,
                Stage::AcCode => self.len < 16 && in_band,
                Stage::AcBits => self.size >= 1 && self.got < self.size && in_band,
                Stage::EobBits => self.size >= 1 && self.size <= 14 && self.got < self.size,
                Stage::SignBit | Stage::CorrBit => in_band,
            }
    }

    /// A machine in `stage` of a scan of `kind`, counters symbolic within
    /// the invariant, for the harnesses.
    #[cfg(kani)]
    pub(crate) fn any_in(kind: ScanKind, stage: Stage) -> Prog {
        let ss: u8 = kani::any();
        let se: u8 = kani::any();
        let al: u8 = kani::any();
        let (ss, se) = match kind {
            ScanKind::DcFirst | ScanKind::DcRefine => (0, 0),
            _ => (ss, se),
        };
        let p = Params { kind, ss, se, al };
        let m = Prog {
            p,
            stage,
            mode: match kani::any::<u8>() % 3 {
                0 => Mode::Symbol,
                1 => Mode::Skip,
                _ => Mode::Eob,
            },
            code: kani::any(),
            len: kani::any(),
            size: kani::any(),
            got: kani::any(),
            acc: kani::any(),
            k: kani::any(),
            run: kani::any(),
            val: kani::any(),
            eobrun: kani::any(),
            blk: kani::any(),
        };
        kani::assume(m.inv());
        m
    }

    /// The stage, for the harnesses.
    #[cfg(kani)]
    pub(crate) const fn stage(&self) -> Stage {
        self.stage
    }

    /// Starts a block (the machine is idle and `blk` holds the block's
    /// coefficients so far). `Ok(true)` when the block needs no bits and is
    /// complete (a block inside an EOB run with nothing to correct), `blk`
    /// unchanged; `Ok(false)` when bits are needed.
    pub(crate) fn begin(&mut self) -> Result<bool, &'static str> {
        if self.stage != Stage::Idle {
            return Err("progressive scan: a block started inside a block");
        }
        self.code = 0;
        self.len = 0;
        self.k = self.p.ss;
        match self.p.kind {
            ScanKind::DcFirst => self.stage = Stage::DcCode,
            ScanKind::DcRefine => self.stage = Stage::DcBit,
            ScanKind::AcFirst => {
                // G.1.2.2, Figure G.3: "EOBRUN > 0: EOBRUN = EOBRUN - 1",
                // the block is all zero in the band.
                if self.eobrun > 0 {
                    self.eobrun = self.eobrun.saturating_sub(1);
                    return Ok(true);
                }
                self.stage = Stage::AcCode;
            }
            ScanKind::AcRefine => {
                self.run = 0;
                self.val = 0;
                if self.eobrun > 0 {
                    self.mode = Mode::Eob;
                    return self.refine_run();
                }
                self.mode = Mode::Symbol;
                self.stage = Stage::AcCode;
            }
        }
        Ok(false)
    }

    /// One bit of the block, with the tables of its component (`None` where
    /// the scan kind does not use one) and the component's DC predictor.
    /// `Ok(true)` when the block is complete (and the machine idle).
    pub(crate) fn bit(
        &mut self,
        bit: u8,
        dc: Option<&Table>,
        ac: Option<&Table>,
        pred: &mut i32,
    ) -> Result<bool, &'static str> {
        let done = match self.stage {
            Stage::Idle => return Err("progressive scan: a bit outside a block"),
            Stage::DcCode => {
                let t = dc.ok_or("progressive scan: no DC table")?;
                match t.step(self.code, self.len, bit) {
                    Next::More { code, len } => {
                        self.code = code;
                        self.len = len;
                        false
                    }
                    Next::Value(0) => self.dc_done(pred, 0)?,
                    Next::Value(s) if s <= 15 => {
                        self.stage = Stage::DcBits;
                        self.size = s;
                        self.got = 0;
                        self.acc = 0;
                        false
                    }
                    Next::Value(_) => return Err("DC size category over 15"),
                    Next::Bad => return Err("bad Huffman code in a DC coefficient"),
                }
            }
            Stage::DcBits => {
                self.push(bit)?;
                if self.got >= self.size {
                    let diff = extend(self.acc, self.size).ok_or("DC difference")?;
                    self.dc_done(pred, diff)?
                } else {
                    false
                }
            }
            Stage::DcBit => {
                // Figure G.4: "IF NEXTBIT = 1 THEN coefficient |= 1 << Al".
                if bit & 1 == 1 {
                    let b = bit_of(self.p.al).ok_or("point transform")?;
                    if let Some(c) = self.blk.first_mut() {
                        *c |= b;
                    }
                }
                true
            }
            Stage::AcCode => {
                let t = ac.ok_or("progressive scan: no AC table")?;
                match t.step(self.code, self.len, bit) {
                    Next::More { code, len } => {
                        self.code = code;
                        self.len = len;
                        false
                    }
                    Next::Value(rs) => self.ac_symbol(rs)?,
                    Next::Bad => return Err("bad Huffman code in an AC coefficient"),
                }
            }
            Stage::AcBits => {
                self.push(bit)?;
                if self.got >= self.size {
                    let v = extend(self.acc, self.size).ok_or("AC coefficient")?;
                    let v = scaled(v, self.p.al)?;
                    self.set(self.k, v)?;
                    self.k = self.k.checked_add(1).ok_or("coefficient index")?;
                    if self.k > self.p.se {
                        true
                    } else {
                        self.code_next();
                        false
                    }
                } else {
                    false
                }
            }
            Stage::EobBits => {
                self.push(bit)?;
                if self.got >= self.size {
                    self.eobrun = self
                        .eobrun
                        .checked_add(self.acc)
                        .ok_or("EOB run out of range")?;
                    self.eob_started()?
                } else {
                    false
                }
            }
            Stage::SignBit => {
                // Figure G.7: "IF NEXTBIT = 1 THEN value = p1 ELSE value =
                // m1".
                let p1 = bit_of(self.p.al).ok_or("point transform")?;
                self.val = if bit & 1 == 1 {
                    p1
                } else {
                    p1.checked_neg().ok_or("point transform")?
                };
                self.mode = Mode::Skip;
                self.refine_run()?
            }
            Stage::CorrBit => {
                // Figure G.7: a nonzero coefficient gets bit `Al` if the
                // bit is 1 and it does not have it yet, in the direction
                // of its sign.
                let p1 = bit_of(self.p.al).ok_or("point transform")?;
                let c = self.get(self.k)?;
                if bit & 1 == 1 && c & p1 == 0 {
                    let d = if c >= 0 {
                        p1
                    } else {
                        p1.checked_neg().ok_or("point transform")?
                    };
                    self.set(self.k, c.checked_add(d).ok_or("coefficient out of range")?)?;
                }
                self.k = self.k.checked_add(1).ok_or("coefficient index")?;
                self.refine_run()?
            }
        };
        if done {
            self.stage = Stage::Idle;
        }
        Ok(done)
    }

    /// Starts reading a Huffman code of an AC symbol.
    fn code_next(&mut self) {
        self.stage = Stage::AcCode;
        self.code = 0;
        self.len = 0;
    }

    /// One more bit of the value being received (`RECEIVE`, F.17).
    fn push(&mut self, bit: u8) -> Result<(), &'static str> {
        self.acc = self
            .acc
            .checked_mul(2)
            .and_then(|a| a.checked_add(u16::from(bit & 1)))
            .ok_or("bit count")?;
        self.got = self.got.checked_add(1).ok_or("bit count")?;
        Ok(())
    }

    /// Coefficient at zig-zag position `k`.
    fn get(&self, k: u8) -> Result<i16, &'static str> {
        let at = ZIGZAG.get(usize::from(k)).ok_or("coefficient index")?;
        self.blk
            .get(usize::from(*at))
            .copied()
            .ok_or("coefficient index")
    }

    /// Sets the coefficient at zig-zag position `k`.
    fn set(&mut self, k: u8, v: i16) -> Result<(), &'static str> {
        let at = ZIGZAG.get(usize::from(k)).ok_or("coefficient index")?;
        *self
            .blk
            .get_mut(usize::from(*at))
            .ok_or("coefficient index")? = v;
        Ok(())
    }

    /// The DC difference is known (Figure G.2): `DC = PRED + DIFF`, the
    /// coefficient is `DC` shifted left by `Al`.
    fn dc_done(&mut self, pred: &mut i32, diff: i32) -> Result<bool, &'static str> {
        *pred = pred.checked_add(diff).ok_or("DC out of range")?;
        let v = scaled(*pred, self.p.al)?;
        if let Some(c) = self.blk.first_mut() {
            *c = v;
        }
        Ok(true)
    }

    /// The symbol `RS` of an AC code (Figures G.3 and G.7).
    fn ac_symbol(&mut self, rs: u8) -> Result<bool, &'static str> {
        let (r, s) = (rs >> 4, rs & 15);
        if self.p.kind == ScanKind::AcFirst {
            if s == 0 {
                if r == 15 {
                    // ZRL: sixteen zeros.
                    self.k = self.k.checked_add(16).ok_or("coefficient index")?;
                    if self.k > self.p.se {
                        return Ok(true);
                    }
                    self.code_next();
                    return Ok(false);
                }
                // EOBn: `EOBRUN = 2^R + R more bits`; this block is the
                // first of the run.
                self.eobrun = 1u16.checked_shl(u32::from(r)).ok_or("EOB run")?;
                if r == 0 {
                    return self.eob_started();
                }
                self.stage = Stage::EobBits;
                self.size = r;
                self.got = 0;
                self.acc = 0;
                return Ok(false);
            }
            // `K = K + R`, then `SSSS` bits of the coefficient.
            self.k = self
                .k
                .checked_add(r)
                .filter(|&k| k <= self.p.se)
                .ok_or("run past the end of the band")?;
            self.stage = Stage::AcBits;
            self.size = s;
            self.got = 0;
            self.acc = 0;
            return Ok(false);
        }
        // Refinement.
        self.run = r;
        self.val = 0;
        if s == 0 {
            if r == 15 {
                // ZRL: skip 16 zero-history coefficients.
                self.mode = Mode::Skip;
                return self.refine_run();
            }
            self.eobrun = 1u16.checked_shl(u32::from(r)).ok_or("EOB run")?;
            if r == 0 {
                return self.eob_started();
            }
            self.stage = Stage::EobBits;
            self.size = r;
            self.got = 0;
            self.acc = 0;
            return Ok(false);
        }
        if s != 1 {
            return Err("a refinement symbol with a size over 1");
        }
        self.stage = Stage::SignBit;
        Ok(false)
    }

    /// An EOB run began in this block and `eobrun` counts it (its extra bits
    /// are in): a first scan is done with the block; a refinement goes on
    /// correcting to `Se`.
    fn eob_started(&mut self) -> Result<bool, &'static str> {
        if self.p.kind == ScanKind::AcFirst {
            self.eobrun = self.eobrun.checked_sub(1).ok_or("EOB run")?;
            return Ok(true);
        }
        self.mode = Mode::Eob;
        self.refine_run()
    }

    /// Figure G.7 between bits: runs on from `K` until a correction bit is
    /// needed (`Ok(false)`, stage `CorrBit`), the block is complete
    /// (`Ok(true)`), or the next symbol is wanted (`Ok(false)`, `AcCode`).
    fn refine_run(&mut self) -> Result<bool, &'static str> {
        match self.mode {
            Mode::Eob => {
                // "Correct every nonzero coefficient to Se", then the run
                // loses this block.
                while self.k <= self.p.se {
                    if self.get(self.k)? != 0 {
                        self.stage = Stage::CorrBit;
                        return Ok(false);
                    }
                    self.k = self.k.checked_add(1).ok_or("coefficient index")?;
                }
                self.eobrun = self.eobrun.checked_sub(1).ok_or("EOB run")?;
                Ok(true)
            }
            Mode::Skip => {
                // Pass the nonzero coefficients (correcting each) and skip
                // `run` zero ones; the next zero one gets `val`.
                while self.k <= self.p.se {
                    if self.get(self.k)? != 0 {
                        self.stage = Stage::CorrBit;
                        return Ok(false);
                    }
                    if self.run == 0 {
                        if self.val != 0 {
                            self.set(self.k, self.val)?;
                        }
                        self.val = 0;
                        self.k = self.k.checked_add(1).ok_or("coefficient index")?;
                        if self.k > self.p.se {
                            return Ok(true);
                        }
                        self.mode = Mode::Symbol;
                        self.code_next();
                        return Ok(false);
                    }
                    self.run = self.run.saturating_sub(1);
                    self.k = self.k.checked_add(1).ok_or("coefficient index")?;
                }
                if self.val != 0 {
                    return Err("a refined coefficient past the end of the band");
                }
                Ok(true)
            }
            Mode::Symbol => Err("progressive scan: no run to continue"),
        }
    }
}

// ----------------------------------------------------------- coefficients

/// Bytes of the coefficients of one block: 64 `i16`.
pub(crate) const BLOCK_BYTES: usize = 128;

/// Start in the work buffer of block `(bx, by)` of a plane of `bw` blocks
/// per row whose coefficients start at `off`.
pub(crate) fn block_base(off: usize, bw: usize, bx: usize, by: usize) -> Option<usize> {
    by.checked_mul(bw)?
        .checked_add(bx)?
        .checked_mul(BLOCK_BYTES)?
        .checked_add(off)
}

/// Bytes a component of `bw` by `bh` blocks needs: the coefficients and one
/// block row's samples (see [`finish_plane`]).
pub(crate) fn region_len(bw: usize, bh: usize) -> Option<usize> {
    bw.checked_mul(bh)?
        .checked_mul(BLOCK_BYTES)?
        .checked_add(bw.checked_mul(64)?)
}

/// Reads the block at `base` of the work buffer.
pub(crate) fn load(work: &[u8], base: usize, out: &mut [i16; 64]) -> Option<()> {
    let bytes = work.get(base..base.checked_add(BLOCK_BYTES)?)?;
    for (o, c) in out.iter_mut().zip(bytes.as_chunks::<2>().0) {
        *o = i16::from_le_bytes(*c);
    }
    Some(())
}

/// Writes the block at `base` of the work buffer.
pub(crate) fn store(work: &mut [u8], base: usize, blk: &[i16; 64]) -> Option<()> {
    let bytes = work.get_mut(base..base.checked_add(BLOCK_BYTES)?)?;
    for (c, v) in bytes.as_chunks_mut::<2>().0.iter_mut().zip(blk) {
        *c = v.to_le_bytes();
    }
    Some(())
}

/// After the last scan: the inverse DCT (A.3.3, dequantizing with `q`) of
/// every block of a plane of `bw` by `bh` blocks whose region starts at
/// `off`, into the 8-bit sample plane in the same region; returns where the
/// samples start (row stride `8 * bw`).
///
/// **In place.** Block `i` (raster order) has its coefficients at
/// `off + 128 i`; the samples go from `s0 = off + 64 * bw * (bh + 1)`, block
/// row `y` at `s0 + 64 * bw * y`. Block rows are done from `bh - 1` down to
/// 0, and a row is read before the samples of its own blocks are written
/// only if its coefficients end where or before its samples start: the
/// coefficients of row `y` end at `off + 128 * bw * (y + 1)` and its samples
/// start at `off + 64 * bw * (bh + 1 + y)`, and `64 * bw * (bh + 1 + y) >=
/// 128 * bw * (y + 1)` exactly when `bh >= y + 1`, true for every row. The
/// samples of row `y` also lie past the coefficients of every row before it
/// (those end earlier). So a write never lands on a coefficient not yet
/// read, and the last sample is at `off + 128 * bw * bh + 64 * bw`, the end
/// of [`region_len`].
pub(crate) fn finish_plane(
    work: &mut [u8],
    off: usize,
    bw: usize,
    bh: usize,
    q: &[u16; 64],
) -> Option<usize> {
    let stride = bw.checked_mul(8)?;
    let s0 = bw
        .checked_mul(64)?
        .checked_mul(bh.checked_add(1)?)?
        .checked_add(off)?;
    let mut blk = [0i16; 64];
    for by in (0..bh).rev() {
        for bx in 0..bw {
            load(work, block_base(off, bw, bx, by)?, &mut blk)?;
            let samples = idct(&blk, q)?;
            let origin = by
                .checked_mul(8)?
                .checked_mul(stride)?
                .checked_add(bx.checked_mul(8)?)?
                .checked_add(s0)?;
            for (r, row) in samples.as_chunks::<8>().0.iter().enumerate() {
                let at = r.checked_mul(stride)?.checked_add(origin)?;
                work.get_mut(at..at.checked_add(8)?)?.copy_from_slice(row);
            }
        }
    }
    Some(s0)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A table with the codes `0` for symbol `a` and `1` for `b`.
    fn two(a: u8, b: u8, dc: bool) -> Result<Table, &'static str> {
        let mut c = [0u8; 16];
        if let Some(x) = c.first_mut() {
            *x = 2;
        }
        Table::build(&c, &[a, b], dc)
    }

    fn run(
        m: &mut Prog,
        bits: &[u8],
        dc: &Table,
        ac: &Table,
        pred: &mut i32,
    ) -> Result<bool, &'static str> {
        let mut done = false;
        for &b in bits {
            assert!(m.inv());
            done = m.bit(b, Some(dc), Some(ac), pred)?;
            if done {
                break;
            }
        }
        Ok(done)
    }

    #[test]
    fn params_follow_table_b3() {
        assert_eq!(
            Params::new(0, 0, 0, 1, 3).map(|p| p.kind),
            Ok(ScanKind::DcFirst)
        );
        assert_eq!(
            Params::new(0, 0, 2, 1, 3).map(|p| p.kind),
            Ok(ScanKind::DcRefine)
        );
        assert_eq!(
            Params::new(1, 5, 0, 0, 1).map(|p| p.kind),
            Ok(ScanKind::AcFirst)
        );
        assert_eq!(
            Params::new(1, 63, 1, 0, 1).map(|p| p.kind),
            Ok(ScanKind::AcRefine)
        );
        // DC with Se, AC with two components, band backwards or past 63,
        // refinement that does not step down by one, Al over 13.
        assert!(Params::new(0, 1, 0, 0, 1).is_err());
        assert!(Params::new(1, 5, 0, 0, 2).is_err());
        assert!(Params::new(5, 1, 0, 0, 1).is_err());
        assert!(Params::new(1, 64, 0, 0, 1).is_err());
        assert!(Params::new(1, 5, 2, 0, 1).is_err());
        assert!(Params::new(0, 0, 0, 14, 1).is_err());
    }

    #[test]
    fn dc_first_shifts_the_difference() -> Result<(), &'static str> {
        // DC code 0: category 3 (3 bits follow); code 1: category 0.
        let dc = two(3, 0, true)?;
        let ac = two(0, 1, false)?;
        let mut m = Prog::new();
        m.start_scan(Params::new(0, 0, 0, 2, 1)?);
        assert_eq!(m.begin(), Ok(false));
        let mut pred = 10;
        // 101 = 5: pred 15, coefficient 15 << 2.
        assert_eq!(run(&mut m, &[0, 1, 0, 1], &dc, &ac, &mut pred), Ok(true));
        assert_eq!((pred, m.blk.first().copied()), (15, Some(60)));
        assert!(m.idle());
        Ok(())
    }

    #[test]
    fn dc_refine_sets_one_bit() -> Result<(), &'static str> {
        let dc = two(3, 0, true)?;
        let mut m = Prog::new();
        m.start_scan(Params::new(0, 0, 2, 1, 1)?);
        if let Some(c) = m.blk.first_mut() {
            *c = 8;
        }
        assert_eq!(m.begin(), Ok(false));
        let mut pred = 0;
        assert_eq!(m.bit(1, Some(&dc), None, &mut pred), Ok(true));
        assert_eq!(m.blk.first().copied(), Some(10));
        assert_eq!(m.begin(), Ok(false));
        assert_eq!(m.bit(0, Some(&dc), None, &mut pred), Ok(true));
        assert_eq!(m.blk.first().copied(), Some(10));
        Ok(())
    }

    #[test]
    fn an_eob_run_skips_whole_blocks() -> Result<(), &'static str> {
        // AC symbols: code 0 = 0x20 (EOB2: 4 + 2 bits), code 1 = 0x01.
        let ac = two(0x20, 0x01, false)?;
        let dc = two(0, 1, true)?;
        let mut m = Prog::new();
        m.start_scan(Params::new(1, 63, 0, 0, 1)?);
        assert_eq!(m.begin(), Ok(false));
        let mut pred = 0;
        // EOB2 with extra bits 01: run of 4 + 1 = 5 blocks, this is the 1st.
        assert_eq!(run(&mut m, &[0, 0, 1], &dc, &ac, &mut pred), Ok(true));
        for _ in 0..4 {
            assert_eq!(m.begin(), Ok(true));
        }
        // The run is spent: the sixth block needs bits.
        assert_eq!(m.begin(), Ok(false));
        // A restart ends the run.
        m.reset();
        assert_eq!(m.begin(), Ok(false));
        Ok(())
    }

    #[test]
    fn ac_first_places_scaled_coefficients() -> Result<(), &'static str> {
        // AC code 1 = run 0 size 1; code 0 = EOB.
        let ac = two(0x00, 0x01, false)?;
        let dc = two(0, 1, true)?;
        let mut m = Prog::new();
        m.start_scan(Params::new(1, 3, 0, 1, 1)?);
        assert_eq!(m.begin(), Ok(false));
        let mut pred = 0;
        // +1 at k = 1 (natural 1), -1 at k = 2 (natural 8), then k = 3 is
        // the last of the band: +1 ends the block with no EOB.
        let bits = [1, 1, 1, 0, 1, 1];
        assert_eq!(run(&mut m, &bits, &dc, &ac, &mut pred), Ok(true));
        assert_eq!(
            (m.blk.get(1), m.blk.get(8), m.blk.get(16)),
            (Some(&2), Some(&-2), Some(&2))
        );
        Ok(())
    }

    #[test]
    fn ac_refine_corrects_and_places() -> Result<(), &'static str> {
        // Code 1 = run 0 size 1 (a new coefficient), code 0 = EOB0.
        let ac = two(0x00, 0x01, false)?;
        let dc = two(0, 1, true)?;
        let mut m = Prog::new();
        m.start_scan(Params::new(1, 4, 1, 0, 1)?);
        // Natural positions of zig-zag 1, 2, 3, 4 are 1, 8, 16, 9: k = 1
        // holds 4 (positive), k = 3 holds -2.
        for (nat, v) in [(1usize, 4i16), (16, -2)] {
            if let Some(c) = m.blk.get_mut(nat) {
                *c = v;
            }
        }
        assert_eq!(m.begin(), Ok(false));
        let mut pred = 0;
        // Code 1 is the symbol (0, 1), then its sign bit 0 (-1). The run of 0
        // zeros first meets k = 1 (nonzero): correction bit 1, and 4 has no
        // bit 0 yet, so it becomes 5. k = 2 is zero and takes -1. Code 0 is
        // EOB0: in the run, k = 3 (-2) takes correction bit 1 and becomes
        // -3; k = 4 is zero.
        let bits = [1, 0, 1, 0, 1];
        assert_eq!(run(&mut m, &bits, &dc, &ac, &mut pred), Ok(true));
        assert_eq!(
            (m.blk.get(1), m.blk.get(8), m.blk.get(16), m.blk.get(9)),
            (Some(&5), Some(&-1), Some(&-3), Some(&0))
        );
        Ok(())
    }

    #[test]
    fn overflow_and_overruns_are_errors() -> Result<(), &'static str> {
        let dc = two(0, 1, true)?;
        // A run past the band end: AC code 1 = run 5 size 1 in a band of 3.
        let ac = two(0x00, 0x51, false)?;
        let mut m = Prog::new();
        m.start_scan(Params::new(1, 3, 0, 0, 1)?);
        assert_eq!(m.begin(), Ok(false));
        let mut pred = 0;
        assert!(run(&mut m, &[1], &dc, &ac, &mut pred).is_err());
        // A DC value that does not fit 16 bits after the shift: category 15
        // would need 15 bits; use pred near the limit.
        let dc = two(1, 0, true)?;
        let mut m = Prog::new();
        m.start_scan(Params::new(0, 0, 0, 13, 1)?);
        assert_eq!(m.begin(), Ok(false));
        let mut pred = 0;
        // Category 1 (code 0), bit 1: +1 << 13 fits; a second block with
        // pred 4: 4 << 13 does not.
        assert_eq!(
            run(&mut m, &[0, 1], &dc, &ac, &mut pred),
            Ok(true),
            "1 << 13"
        );
        pred = 3;
        assert_eq!(m.begin(), Ok(false));
        assert!(run(&mut m, &[0, 1], &dc, &ac, &mut pred).is_err());
        Ok(())
    }

    #[test]
    fn finish_plane_in_place_equals_a_separate_plane() -> Result<(), &'static str> {
        let q = [3u16; 64];
        for (bw, bh) in [(1usize, 1usize), (3, 1), (1, 3), (4, 3), (5, 5)] {
            let len = region_len(bw, bh).ok_or("size")?;
            let mut work = vec![0xAAu8; len];
            let mut blocks = Vec::new();
            for i in 0..bw.saturating_mul(bh) {
                let mut b = [0i16; 64];
                for (j, c) in b.iter_mut().enumerate() {
                    // A deterministic spread of small coefficients.
                    let v =
                        i32::try_from(i.saturating_mul(37).saturating_add(j.saturating_mul(11)))
                            .map_err(|_| "size")?
                            % 61;
                    *c = if j < 10 {
                        i16::try_from(v - 30).map_err(|_| "v")?
                    } else {
                        0
                    };
                }
                blocks.push(b);
            }
            for (i, b) in blocks.iter().enumerate() {
                let (bx, by) = (i % bw, i / bw);
                store(&mut work, block_base(0, bw, bx, by).ok_or("base")?, b).ok_or("store")?;
            }
            let s0 = finish_plane(&mut work, 0, bw, bh, &q).ok_or("finish")?;
            let stride = bw * 8;
            for (i, b) in blocks.iter().enumerate() {
                let (bx, by) = (i % bw, i / bw);
                let want = idct(b, &q).ok_or("idct")?;
                for r in 0..8 {
                    let at = s0 + (by * 8 + r) * stride + bx * 8;
                    assert_eq!(
                        work.get(at..at + 8),
                        want.get(r * 8..r * 8 + 8),
                        "{bw}x{bh} block {i} row {r}"
                    );
                }
            }
        }
        Ok(())
    }
}

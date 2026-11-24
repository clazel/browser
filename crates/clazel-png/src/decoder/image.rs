//! The image data of a frame: the zlib stream of the scanlines (PNG 3rd
//! edition 10.1, 10.2) through the engine, each scanline unfiltered (9) and
//! converted and blended into the canvas (6, 13.12, 13.16, 4.9, 11.3.6.3).

use std::ops::Range;

use clazel_image_shape::Error;

use super::{Blend, Dispose, FrameInfo, Kind, Png, Stage, bad};
use crate::adam7;
use crate::engine::{Engine, Outcome, Progress};
use crate::filter::unfilter;
use crate::pixel::{over, rgba};
use crate::work::Parts;

/// The bytes of the canvas of row `row`, columns `x` to `x + w` (4 bytes a
/// pixel), if they are in a canvas `canvas_w` wide.
fn span(canvas_w: u32, x: u32, row: u32, w: u32) -> Option<Range<usize>> {
    let start = usize::try_from(row)
        .ok()?
        .checked_mul(usize::try_from(canvas_w).ok()?)?
        .checked_add(usize::try_from(x).ok()?)?
        .checked_mul(4)?;
    let end = start.checked_add(usize::try_from(w).ok()?.checked_mul(4)?)?;
    Some(start..end)
}

/// What one round of [`Png::feed`] leaves to do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Flow {
    /// Another round.
    More,
    /// The bytes are used, or the zlib stream is done.
    Stop,
}

impl<E: Engine> Png<E> {
    /// Bytes of IDAT or fdAT data of the current chunk: begin the frame if
    /// this is its first, then feed the engine unless the frame is complete
    /// (more data chunks after the end of the zlib stream are skipped).
    pub(crate) fn image_bytes(&mut self, part: &[u8], parts: &mut Parts<'_>) -> Result<(), Error> {
        if self.stage == Stage::Idle {
            self.begin_frame(parts)?;
        }
        if self.stage == Stage::Active {
            self.feed(part, parts)?;
        }
        Ok(())
    }

    /// 4.9.1, 4.9.3, 4.9.4 and 11.3.6.3: starts the next frame. The first
    /// image begins on a canvas of fully transparent black; the previous
    /// frame's `dispose_op` is applied; a frame whose own `dispose_op` is
    /// "previous" has the canvas saved.
    pub(crate) fn begin_frame(&mut self, parts: &mut Parts<'_>) -> Result<(), Error> {
        let frame = match self.kind {
            // 11.3.6.2: the default image's fcTL, if there was one; else the
            // image is the whole canvas, blended as "source", not part of
            // an animation.
            Kind::Idat => self.pending.take().unwrap_or(FrameInfo {
                x: 0,
                y: 0,
                width: self.canvas_width(),
                height: self.canvas_height(),
                delay_num: 0,
                delay_den: 0,
                dispose: Dispose::None,
                blend: Blend::Source,
                animated: false,
            }),
            Kind::Fdat => self
                .pending
                .take()
                .ok_or(bad("fdAT data with no fcTL before it"))?,
            _ => return Err(bad("image data in a chunk that is not IDAT or fdAT")),
        };
        let cw = self.canvas_width();
        if self.frames_done == 0 || self.default_hidden {
            // 4.9.3: the output buffer starts, and (an animation that does
            // not include the default image) restarts, fully transparent.
            parts.pixels.fill(0);
            self.default_hidden = false;
        } else {
            // 11.3.6.3: the previous frame's `dispose_op`, on its region.
            let (x, y, w, h) = self.prev_rect;
            for j in 0..h {
                let Some(r) = span(cw, x, y.saturating_add(j), w) else {
                    return Err(bad("frame outside the canvas"));
                };
                match self.prev_dispose {
                    Dispose::None => {}
                    Dispose::Background => {
                        if let Some(s) = parts.pixels.get_mut(r) {
                            s.fill(0);
                        }
                    }
                    Dispose::Previous => {
                        if let (Some(d), Some(s)) =
                            (parts.pixels.get_mut(r.clone()), parts.saved.get(r))
                            && d.len() == s.len()
                        {
                            d.copy_from_slice(s);
                        }
                    }
                }
            }
        }
        let mut dispose = frame.dispose;
        if frame.animated {
            // 11.3.6.3: "APNG_DISPOSE_OP_PREVIOUS" of the first frame of the
            // animation is treated as "background".
            if self.anim_begun == 0 && dispose == Dispose::Previous {
                dispose = Dispose::Background;
            }
            self.anim_begun = self.anim_begun.saturating_add(1);
        } else {
            self.default_hidden = true;
        }
        if dispose == Dispose::Previous && parts.saved.len() == parts.pixels.len() {
            parts.saved.copy_from_slice(parts.pixels);
        }
        self.prev_dispose = dispose;
        self.prev_rect = (frame.x, frame.y, frame.width, frame.height);
        self.frame = frame;
        self.has_frame = true;
        self.data_kind = self.kind;
        // 10.2: the zlib stream's output is exactly the scanlines (with
        // their filter-type bytes) of every pass.
        let mut total = 0u64;
        for p in 0..adam7::pass_count(self.interlaced) {
            if let Some(pass) = adam7::pass(self.interlaced, p) {
                let (pw, ph) = pass.size(frame.width, frame.height);
                if pw > 0 {
                    let line = u64::from(self.layout.row_bytes(pw)).saturating_add(1);
                    total = total.saturating_add(line.saturating_mul(u64::from(ph)));
                }
            }
        }
        self.engine = E::new(total);
        self.stage = Stage::Active;
        self.rows_done = false;
        self.start_pass(0, parts);
        Ok(())
    }

    /// 8.1: moves to the first pass at or after `from` that has pixels (every
    /// pass of an image that is not interlaced, which has one), or to the end
    /// of the image. A pass's first scanline is filtered against a row of
    /// zeros (9.2).
    fn start_pass(&mut self, from: u8, parts: &mut Parts<'_>) {
        for p in from..adam7::pass_count(self.interlaced) {
            let Some(pass) = adam7::pass(self.interlaced, p) else {
                break;
            };
            let (pw, ph) = pass.size(self.frame.width, self.frame.height);
            if pw == 0 || ph == 0 {
                continue;
            }
            self.pass = p;
            self.pass_w = pw;
            self.pass_h = ph;
            self.row_len = self.layout.row_bytes(pw);
            self.row = 0;
            self.row_have = 0;
            let len = usize::try_from(self.row_len).unwrap_or(0);
            if let Some(prev) = parts.prev.get_mut(..len) {
                prev.fill(0);
            }
            return;
        }
        self.rows_done = true;
    }

    /// Gives the engine the bytes of a data chunk until they are used or the
    /// zlib stream is done. The engine writes straight into the scanline
    /// buffer; a scanline that is complete is finished before the next one.
    /// One round of the loop is [`Png::feed_once`], so that a proof of one
    /// round (`proofs.rs`) is a proof of the loop: every round takes the
    /// state to a state with the invariant and an active frame, or ends.
    pub(crate) fn feed(&mut self, part: &[u8], parts: &mut Parts<'_>) -> Result<(), Error> {
        let mut src = part;
        while let Flow::More = self.feed_once(&mut src, parts)? {}
        Ok(())
    }

    /// One round of [`Png::feed`]: one call of the engine on the front of
    /// `src` (which it shortens by what the engine used), the scanline it
    /// completed if any, and what the outcome means. In three parts that
    /// `proofs.rs` has one harness each for ([`Png::engine_round`], the
    /// scanline's [`Png::finish_row`], [`Png::round_end`]), the second only
    /// when the first filled the scanline.
    pub(crate) fn feed_once(
        &mut self,
        src: &mut &[u8],
        parts: &mut Parts<'_>,
    ) -> Result<Flow, Error> {
        let r = self.engine_round(src, parts)?;
        if self.row_is_full() {
            self.finish_row(parts)?;
        }
        self.round_end(r, src)
    }

    /// The scanline is complete (its filter-type byte and `row_len` bytes
    /// are in `cur`).
    pub(crate) fn row_is_full(&self) -> bool {
        let want = usize::try_from(self.row_len).unwrap_or(0).saturating_add(1);
        !self.rows_done && usize::try_from(self.row_have).unwrap_or(0) >= want
    }

    /// The engine's call of a round: it gets the rest of the scanline to
    /// write into (none once the image is complete) and what it used and
    /// wrote is counted.
    pub(crate) fn engine_round(
        &mut self,
        src: &mut &[u8],
        parts: &mut Parts<'_>,
    ) -> Result<Progress, Error> {
        let want = usize::try_from(self.row_len).unwrap_or(0).saturating_add(1);
        let (r, room) = if self.rows_done {
            // The image is complete; only the end of the stream (the
            // Adler-32) may follow, so the engine gets no room.
            let mut none: [u8; 0] = [];
            (self.engine.step(src, &mut none, parts.window), 0)
        } else {
            let have = usize::try_from(self.row_have).unwrap_or(0);
            let Some(dst) = parts.cur.get_mut(have..want) else {
                return Err(bad("scanline buffer"));
            };
            let room = dst.len();
            (self.engine.step(src, dst, parts.window), room)
        };
        if r.consumed > src.len() || r.produced > room {
            return Err(bad("the zlib engine broke its contract"));
        }
        *src = src.get(r.consumed..).unwrap_or(&[]);
        if !self.rows_done {
            let got = u32::try_from(r.produced).unwrap_or(0);
            self.row_have = self.row_have.saturating_add(got);
        }
        Ok(r)
    }

    /// What the engine's outcome of a round means: the end of the round's
    /// work, whether the loop goes on.
    pub(crate) fn round_end(&mut self, r: Progress, src: &[u8]) -> Result<Flow, Error> {
        match r.outcome {
            Outcome::Failed => return Err(bad("the zlib stream of the image is invalid")),
            Outcome::Done => {
                // 10.2: the stream ends exactly when the image does.
                if !self.rows_done {
                    return Err(bad("the image data ends before the image"));
                }
                self.stage = Stage::Finished;
                self.report = true;
                return Ok(Flow::Stop);
            }
            Outcome::NeedInput => {
                if src.is_empty() {
                    return Ok(Flow::Stop);
                }
            }
            Outcome::NeedOutput => {
                // With no room (the image is complete) the stream has
                // more output than the image holds.
                if self.rows_done && r.produced == 0 {
                    return Err(bad("more image data than the image holds"));
                }
            }
        }
        if r.consumed == 0 && r.produced == 0 {
            return Err(bad("the zlib engine made no progress"));
        }
        Ok(Flow::More)
    }

    /// 7.2, 9, 8: a complete scanline in `cur` (its filter-type byte, then
    /// its bytes) is unfiltered, its pixels placed, and the next scanline or
    /// pass begun. Only [`Png::next_row`] changes the state (the other two
    /// take `&self`), so a proof that it keeps the invariant is a proof of
    /// this.
    pub(crate) fn finish_row(&mut self, parts: &mut Parts<'_>) -> Result<(), Error> {
        self.unfilter_row(parts)?;
        self.place_row(parts)?;
        self.next_row(parts);
        Ok(())
    }

    /// 9.1 to 9.4: the scanline in `cur` unfiltered in place, against `prev`.
    pub(crate) fn unfilter_row(&self, parts: &mut Parts<'_>) -> Result<(), Error> {
        let len = usize::try_from(self.row_len).unwrap_or(0);
        let Some((filter, data)) = parts.cur.split_first_mut() else {
            return Err(bad("scanline buffer"));
        };
        let (Some(data), Some(prev)) = (data.get_mut(..len), parts.prev.get_mut(..len)) else {
            return Err(bad("scanline buffer"));
        };
        // 9.1: the filter type of the scanline, then 9.2 to 9.4.
        if !unfilter(*filter, self.layout.filter_bpp(), prev, data) {
            return Err(bad("a scanline's filter type is above 4"));
        }
        Ok(())
    }

    /// 8.1, 6, 4.9, 11.3.6.3: the pixels of the unfiltered scanline in `cur`
    /// converted and blended into the canvas.
    pub(crate) fn place_row(&self, parts: &mut Parts<'_>) -> Result<(), Error> {
        let len = usize::try_from(self.row_len).unwrap_or(0);
        let Some(data) = parts.cur.get(1..).and_then(|d| d.get(..len)) else {
            return Err(bad("scanline buffer"));
        };
        let Some(pass) = adam7::pass(self.interlaced, self.pass) else {
            return Err(bad("pass out of range"));
        };
        let cw = self.canvas_width();
        let y = self.frame.y.saturating_add(pass.row(self.row));
        // The scanline's pixels: pixel `i` of pass pixel row `row` is the image
        // pixel (x0 + i * dx, y0 + row * dy) of the frame (8.1).
        for i in 0..self.pass_w {
            let px = rgba(
                &self.layout,
                self.trns,
                parts.palette,
                data,
                usize::try_from(i).unwrap_or(0),
            );
            let x = self.frame.x.saturating_add(pass.column(i));
            let Some(dst) = span(cw, x, y, 1).and_then(|r| parts.pixels.get_mut(r)) else {
                return Err(bad("pixel outside the canvas"));
            };
            let old = [
                dst.first().copied().unwrap_or(0),
                dst.get(1).copied().unwrap_or(0),
                dst.get(2).copied().unwrap_or(0),
                dst.get(3).copied().unwrap_or(0),
            ];
            let new = match self.frame.blend {
                Blend::Source => px,
                Blend::Over => over(px, old),
            };
            for (slot, v) in dst.iter_mut().zip(new) {
                *slot = v;
            }
        }
        Ok(())
    }

    /// 9.2, 8: the next scanline is filtered against this one; moves to it,
    /// or to the next pass.
    pub(crate) fn next_row(&mut self, parts: &mut Parts<'_>) {
        let len = usize::try_from(self.row_len).unwrap_or(0);
        let data = parts.cur.get(1..).and_then(|d| d.get(..len));
        if let (Some(prev), Some(data)) = (parts.prev.get_mut(..len), data)
            && prev.len() == data.len()
        {
            prev.copy_from_slice(data);
        }
        self.row = self.row.saturating_add(1);
        self.row_have = 0;
        if self.row >= self.pass_h {
            self.start_pass(self.pass.saturating_add(1), parts);
        }
    }
}

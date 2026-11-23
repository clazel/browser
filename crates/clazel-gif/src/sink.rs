//! Where the colour indexes of a frame go: through the palette, along the
//! frame's rows (interlaced or not), onto the canvas.
//!
//! GIF89a Appendix E ("Interlace"): with the interlace flag, the rows are
//! stored in four passes: pass 1 every 8th row from row 0, pass 2 every 8th
//! from row 4, pass 3 every 4th from row 2, pass 4 every 2nd from row 1.

/// The first row of each pass (GIF89a Appendix E).
const START: [u16; 4] = [0, 4, 2, 1];

/// The step between the rows of each pass.
const STEP: [u16; 4] = [8, 8, 4, 2];

/// The position in a frame and what to do with each index.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Sink {
    /// The canvas's width in pixels.
    pub canvas_w: u16,
    /// The canvas's height in pixels.
    pub canvas_h: u16,
    /// The frame's left edge on the canvas.
    pub left: u16,
    /// The frame's top edge on the canvas.
    pub top: u16,
    /// The frame's width.
    pub width: u16,
    /// The frame's height.
    pub height: u16,
    /// Rows stored in four passes.
    pub interlaced: bool,
    /// The transparent index of the frame, if its control says so.
    pub transparent: Option<u8>,
    /// Column of the next index in the frame.
    pub x: u16,
    /// Row (in the picture, not in storage order) of the next index.
    pub y: u16,
    /// The interlace pass (0 to 3) `y` is in.
    pub pass: u8,
    /// Indexes the frame still wants: `width * height` at the start.
    pub remaining: u32,
}

impl Sink {
    /// A sink with nothing to do, for a canvas.
    pub(crate) fn idle(canvas_w: u16, canvas_h: u16) -> Sink {
        Sink {
            canvas_w,
            canvas_h,
            left: 0,
            top: 0,
            width: 0,
            height: 0,
            interlaced: false,
            transparent: None,
            x: 0,
            y: 0,
            pass: 0,
            remaining: 0,
        }
    }

    /// A sink for a frame at (`left`, `top`) of `width` by `height`.
    pub(crate) fn frame(
        canvas: (u16, u16),
        rect: (u16, u16, u16, u16),
        interlaced: bool,
        transparent: Option<u8>,
    ) -> Sink {
        let (left, top, width, height) = rect;
        Sink {
            canvas_w: canvas.0,
            canvas_h: canvas.1,
            left,
            top,
            width,
            height,
            interlaced,
            transparent,
            x: 0,
            y: 0,
            pass: 0,
            remaining: u32::from(width).saturating_mul(u32::from(height)),
        }
    }

    /// The invariant: when indexes are wanted the position is in the frame.
    pub(crate) fn inv(&self) -> bool {
        self.pass <= 3 && (self.remaining == 0 || (self.x < self.width && self.y < self.height))
    }

    /// Takes the colour `index` of the next pixel of the frame: through
    /// `palette` (RGB triples), onto `pixels` (the canvas, straight RGBA)
    /// unless the index is the transparent one, past the palette, or the
    /// pixel is outside the canvas (listed choices: such a pixel keeps what
    /// the canvas holds). Returns whether the frame wants more indexes.
    pub(crate) fn put(&mut self, index: u8, palette: &[u8], pixels: &mut [u8]) -> bool {
        if self.remaining == 0 {
            return false;
        }
        if self.transparent != Some(index) {
            self.paint(index, palette, pixels);
        }
        self.advance();
        self.remaining > 0
    }

    /// Draws the pixel at the current position, if it is on the canvas and
    /// the palette has the index.
    fn paint(&self, index: u8, palette: &[u8], pixels: &mut [u8]) {
        let cx = u32::from(self.left).saturating_add(u32::from(self.x));
        let cy = u32::from(self.top).saturating_add(u32::from(self.y));
        if cx >= u32::from(self.canvas_w) || cy >= u32::from(self.canvas_h) {
            return;
        }
        let at = usize::from(index).checked_mul(3);
        let rgb = at.and_then(|a| palette.get(a..a.checked_add(3)?));
        let offset = cy
            .checked_mul(u32::from(self.canvas_w))
            .and_then(|v| v.checked_add(cx))
            .and_then(|v| usize::try_from(v).ok())
            .and_then(|v| v.checked_mul(4));
        let dst = offset.and_then(|o| pixels.get_mut(o..o.checked_add(4)?));
        if let (Some([r, g, b]), Some(dst)) = (rgb, dst) {
            dst.copy_from_slice(&[*r, *g, *b, 255]);
        }
    }

    /// Moves to the next index's position, and ends the frame when all of
    /// them were taken.
    fn advance(&mut self) {
        self.remaining = self.remaining.saturating_sub(1);
        self.x = self.x.saturating_add(1);
        if self.x >= self.width {
            self.x = 0;
            if self.interlaced {
                self.next_interlaced_row();
            } else {
                self.y = self.y.saturating_add(1);
            }
        }
        if self.y >= self.height {
            // Past the last row. `remaining` is `width * height` less one
            // per pixel, so it is 0 here; if it is not, stop anyway.
            self.remaining = 0;
        }
        if self.remaining == 0 {
            self.x = 0;
            self.y = 0;
            self.pass = self.pass.min(3);
        }
    }

    /// The row after the current one in storage order. Passes that have no
    /// row in a short frame are skipped. Past pass 4, `y` is `height`.
    pub(crate) fn next_interlaced_row(&mut self) {
        let step = STEP.get(usize::from(self.pass)).copied().unwrap_or(8);
        self.y = self.y.saturating_add(step);
        // At most one move to the next pass per pass: a loop of a constant
        // bound, which the model checker unwinds exactly.
        for _ in 0..START.len() {
            if self.y < self.height {
                return;
            }
            let next = self.pass.saturating_add(1);
            match START.get(usize::from(next)) {
                Some(&start) => {
                    self.pass = next;
                    self.y = start;
                }
                None => {
                    self.y = self.height;
                    return;
                }
            }
        }
    }
}

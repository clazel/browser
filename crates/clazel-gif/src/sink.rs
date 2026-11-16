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
    ///
    /// STUB: implementation in a later commit; `inv` is what the harness
    /// `sink_put_any` states it keeps.
    pub(crate) fn put(&mut self, _index: u8, _palette: &[u8], _pixels: &mut [u8]) -> bool {
        false
    }

    /// The row after the current one in storage order (STUB).
    pub(crate) fn next_interlaced_row(&mut self) {}
}

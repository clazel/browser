//! Interlacing: the seven passes of Adam7 (PNG 3rd edition, 8 "Interlacing
//! and pass extraction", 8.1 "Interlace methods"), and the one pass of an
//! image that is not interlaced.
//!
//! A pass takes the pixels `(x0 + i * dx, y0 + j * dy)` of the image, for
//! `i` and `j` counting from 0, as long as they are inside it. Kani proves
//! (`proofs.rs`) for every width and height up to 2^14 that the pass sizes
//! add up to the image's, every pass pixel is inside the image, and every
//! image pixel is in exactly one pass.

/// One pass: its first pixel and its steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pass {
    /// Column of the pass's first pixel.
    pub x0: u32,
    /// Row of the pass's first pixel.
    pub y0: u32,
    /// Distance between the pass's pixels along a row.
    pub dx: u32,
    /// Distance between the pass's rows.
    pub dy: u32,
}

/// 8.1, Figure 8.1's pattern: the seven passes in order, as
/// `(x0, y0, dx, dy)`.
const ADAM7: [Pass; 7] = [
    Pass {
        x0: 0,
        y0: 0,
        dx: 8,
        dy: 8,
    },
    Pass {
        x0: 4,
        y0: 0,
        dx: 8,
        dy: 8,
    },
    Pass {
        x0: 0,
        y0: 4,
        dx: 4,
        dy: 8,
    },
    Pass {
        x0: 2,
        y0: 0,
        dx: 4,
        dy: 4,
    },
    Pass {
        x0: 0,
        y0: 2,
        dx: 2,
        dy: 4,
    },
    Pass {
        x0: 1,
        y0: 0,
        dx: 2,
        dy: 2,
    },
    Pass {
        x0: 0,
        y0: 1,
        dx: 1,
        dy: 2,
    },
];

/// 8.1 "interlace method 0": the whole image is one pass.
const WHOLE: Pass = Pass {
    x0: 0,
    y0: 0,
    dx: 1,
    dy: 1,
};

/// How many passes an image has: 7 interlaced (method 1), else 1.
pub const fn pass_count(interlaced: bool) -> u8 {
    if interlaced { 7 } else { 1 }
}

/// The `index`-th pass (from 0), if the image has that many.
pub fn pass(interlaced: bool, index: u8) -> Option<Pass> {
    if interlaced {
        ADAM7.get(usize::from(index)).copied()
    } else if index == 0 {
        Some(WHOLE)
    } else {
        None
    }
}

/// The number of pixels `start, start + step, ...` that are below `len`.
fn axis(len: u32, start: u32, step: u32) -> u32 {
    match len.checked_sub(start) {
        None | Some(0) => 0,
        Some(rest) => rest
            .saturating_add(step.saturating_sub(1))
            .checked_div(step)
            .unwrap_or(0),
    }
}

impl Pass {
    /// 8.1: the pass's width and height in pixels for an image of
    /// `width` by `height` (either may be 0, when the image is too small to
    /// have a pixel in this pass; such a pass has no scanlines at all).
    pub fn size(&self, width: u32, height: u32) -> (u32, u32) {
        let w = axis(width, self.x0, self.dx);
        let h = axis(height, self.y0, self.dy);
        if w == 0 || h == 0 { (0, 0) } else { (w, h) }
    }

    /// The image column of the pass's `i`-th pixel of a row.
    pub fn column(&self, i: u32) -> u32 {
        self.x0.saturating_add(i.saturating_mul(self.dx))
    }

    /// The image row of the pass's `j`-th scanline.
    pub fn row(&self, j: u32) -> u32 {
        self.y0.saturating_add(j.saturating_mul(self.dy))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn area(p: &Pass, w: u32, h: u32) -> u32 {
        let (pw, ph) = p.size(w, h);
        pw.saturating_mul(ph)
    }

    #[test]
    fn eight_by_eight_matches_the_spec_figure() {
        // 8.1: in an 8 by 8 image the passes have 1, 1, 2, 4, 8, 16, 32 pixels.
        let sizes: Vec<u32> = (0..7)
            .filter_map(|i| pass(true, i))
            .map(|p| area(&p, 8, 8))
            .collect();
        assert_eq!(sizes, [1, 1, 2, 4, 8, 16, 32]);
    }

    #[test]
    fn tiny_images_skip_passes() {
        assert_eq!(pass(true, 1).map(|p| p.size(4, 8)), Some((0, 0)));
        assert_eq!(pass(true, 1).map(|p| p.size(5, 1)), Some((1, 1)));
        assert_eq!(pass(false, 1), None);
        assert_eq!(pass(true, 7), None);
    }

    #[test]
    fn every_pixel_is_in_one_pass() {
        for w in 1..=19u32 {
            for h in 1..=19u32 {
                let mut hits = vec![0u8; usize::try_from(w.saturating_mul(h)).unwrap_or(0)];
                for i in 0..7 {
                    let Some(p) = pass(true, i) else { continue };
                    let (pw, ph) = p.size(w, h);
                    for j in 0..ph {
                        for k in 0..pw {
                            let (x, y) = (p.column(k), p.row(j));
                            assert!(x < w && y < h);
                            let at = usize::try_from(y.saturating_mul(w).saturating_add(x));
                            if let Some(n) = at.ok().and_then(|a| hits.get_mut(a)) {
                                *n = n.saturating_add(1);
                            }
                        }
                    }
                }
                assert!(hits.iter().all(|&n| n == 1), "{w}x{h}");
            }
        }
    }
}

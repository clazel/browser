//! Rectangles in device pixels, and the viewport.
//!
//! # Modelling choices
//!
//! - **Half-open integer rectangles**: a rectangle covers the pixels `(px, py)`
//!   with `x0 <= px < x1` and `y0 <= py < y1`. Display list items are whole device
//!   pixels (5.16), so nothing is drawn at a fraction of a pixel and nothing is
//!   antialiased but glyph masks, whose coverage is in their bytes.
//! - **`i32` corners, with every step checked.** A list that passed the validator
//!   has positions within ±2^23 and sizes up to 2^23 (`theorem_validated_bounds`),
//!   so a far edge is within ±2^24 and never overflows; a value outside that is
//!   still handled, by [`Error::Range`](crate::Error::Range), not by a panic.

/// The largest viewport side, in device pixels: 8192, which holds every display
/// shipped today at scale 2 (a 6K display is 6016 pixels wide).
pub const MAX_VIEWPORT_SIDE: u32 = 8192;

/// What the GPU process draws into: a target of `width` × `height` device pixels,
/// RGBA8, whose top left pixel is the list's `(0, 0)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Viewport {
    /// Width in device pixels, 1 to [`MAX_VIEWPORT_SIDE`].
    pub width: u32,
    /// Height in device pixels, 1 to [`MAX_VIEWPORT_SIDE`].
    pub height: u32,
}

impl Viewport {
    /// A viewport, if both sides are from 1 to [`MAX_VIEWPORT_SIDE`].
    pub fn new(width: u32, height: u32) -> Option<Viewport> {
        let ok = |side: u32| (1..=MAX_VIEWPORT_SIDE).contains(&side);
        (ok(width) && ok(height)).then_some(Viewport { width, height })
    }

    /// The bytes of an RGBA8 image of this size, rows packed.
    pub fn bytes(self) -> usize {
        // At most 8192 × 8192 × 4 = 2^28, which `usize` holds on every target
        // the crate builds for (32 bits and up).
        (self.width as usize)
            .saturating_mul(self.height as usize)
            .saturating_mul(4)
    }

    /// The whole target as a rectangle.
    pub fn rect(self) -> Rect {
        // Both sides are at most 8192, so they fit in `i32`.
        Rect {
            x0: 0,
            y0: 0,
            x1: i32::try_from(self.width).unwrap_or(0),
            y1: i32::try_from(self.height).unwrap_or(0),
        }
    }
}

/// A half-open rectangle of device pixels. Empty when `x0 >= x1` or `y0 >= y1`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rect {
    /// The left edge (included).
    pub x0: i32,
    /// The top edge (included).
    pub y0: i32,
    /// The right edge (excluded).
    pub x1: i32,
    /// The bottom edge (excluded).
    pub y1: i32,
}

impl Rect {
    /// The rectangle at `(x, y)` of the given size, or `None` if a far edge does
    /// not fit in `i32` (never for a list that passed the validator).
    pub fn at(x: i32, y: i32, width: u32, height: u32) -> Option<Rect> {
        let w = i32::try_from(width).ok()?;
        let h = i32::try_from(height).ok()?;
        Some(Rect {
            x0: x,
            y0: y,
            x1: x.checked_add(w)?,
            y1: y.checked_add(h)?,
        })
    }

    /// No pixel is inside.
    pub fn is_empty(self) -> bool {
        self.x0 >= self.x1 || self.y0 >= self.y1
    }

    /// The pixels inside both. Empty rectangles come out empty, with no
    /// arithmetic: only `min` and `max`.
    pub fn intersect(self, other: Rect) -> Rect {
        Rect {
            x0: self.x0.max(other.x0),
            y0: self.y0.max(other.y0),
            x1: self.x1.min(other.x1),
            y1: self.y1.min(other.y1),
        }
    }

    /// Every pixel of `self` is in `outer` (an empty `self` is in anything).
    pub fn within(self, outer: Rect) -> bool {
        self.is_empty()
            || (outer.x0 <= self.x0
                && outer.y0 <= self.y0
                && self.x1 <= outer.x1
                && self.y1 <= outer.y1)
    }

    /// The pixel `(px, py)` is inside.
    pub fn contains(self, px: i32, py: i32) -> bool {
        self.x0 <= px && px < self.x1 && self.y0 <= py && py < self.y1
    }
}

#[cfg(test)]
mod tests {
    use super::{MAX_VIEWPORT_SIDE, Rect, Viewport};

    #[test]
    fn viewport_sides_are_bounded() {
        assert!(Viewport::new(0, 1).is_none());
        assert!(Viewport::new(1, MAX_VIEWPORT_SIDE + 1).is_none());
        let v = Viewport::new(MAX_VIEWPORT_SIDE, 3);
        assert_eq!(v.map(Viewport::bytes), Some(8192 * 3 * 4));
    }

    #[test]
    fn rect_edges_are_checked() {
        assert_eq!(Rect::at(i32::MAX, 0, 1, 1), None);
        assert_eq!(Rect::at(0, 0, u32::MAX, 1), None);
        let r = Rect::at(-2, 3, 4, 5);
        assert_eq!(
            r,
            Some(Rect {
                x0: -2,
                y0: 3,
                x1: 2,
                y1: 8
            })
        );
    }

    #[test]
    fn intersection_and_containment() {
        let a = Rect {
            x0: 0,
            y0: 0,
            x1: 10,
            y1: 10,
        };
        let b = Rect {
            x0: 5,
            y0: -5,
            x1: 20,
            y1: 5,
        };
        let i = a.intersect(b);
        assert_eq!(
            i,
            Rect {
                x0: 5,
                y0: 0,
                x1: 10,
                y1: 5
            }
        );
        assert!(i.within(a) && i.within(b));
        let far = Rect {
            x0: 30,
            y0: 30,
            x1: 40,
            y1: 40,
        };
        assert!(a.intersect(far).is_empty());
        assert!(a.intersect(far).within(Rect {
            x0: 0,
            y0: 0,
            x1: 0,
            y1: 0
        }));
        assert!(a.contains(0, 9) && !a.contains(10, 0));
    }
}

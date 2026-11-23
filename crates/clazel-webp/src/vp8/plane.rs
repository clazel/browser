//! One plane of the frame being reconstructed (Y, U or V), with the
//! out-of-frame values of RFC 6386 section 12.
//!
//! "Usually such out-of-bounds pixels have an assumed value of 129 for
//! pixels to the left of the leftmost column of the visible frame and 127 for
//! pixels above the top row of the visible frame (including the special case
//! of the pixel above and to the left of the top-left pixel in the visible
//! frame)." So a position above the plane reads 127 whatever its column, and
//! a position left of the plane (on or below its first row) reads 129.

/// The value above the top row (section 12).
pub(crate) const ABOVE: u8 = 127;
/// The value left of the leftmost column (section 12).
pub(crate) const LEFT: u8 = 129;

/// A plane of `rows` rows of `stride` pixels, in a slice of exactly that
/// size (the caller cuts it so).
#[derive(Debug)]
pub(crate) struct Plane<'a> {
    data: &'a mut [u8],
    stride: usize,
}

impl<'a> Plane<'a> {
    /// A plane over `data`, `stride` pixels to a row.
    pub(crate) fn new(data: &'a mut [u8], stride: usize) -> Plane<'a> {
        Plane { data, stride }
    }

    /// The pixels in a row.
    pub(crate) fn stride(&self) -> usize {
        self.stride
    }

    fn index(&self, x: usize, y: usize) -> Option<usize> {
        if x >= self.stride {
            return None;
        }
        y.checked_mul(self.stride)?.checked_add(x)
    }

    /// The pixel at (`x`, `y`) inside the plane (0 if it is not there).
    pub(crate) fn at(&self, x: usize, y: usize) -> u8 {
        self.index(x, y)
            .and_then(|i| self.data.get(i))
            .copied()
            .unwrap_or(0)
    }

    /// The pixel at (`x`, `y`), where either may be one before the plane
    /// (`-1`): the border values of section 12 there. A position past the
    /// plane's right edge reads the last pixel of its row (the callers that
    /// reach it replace those pixels by rule, so this is only totality).
    pub(crate) fn get(&self, x: i32, y: i32) -> u8 {
        let Ok(y) = usize::try_from(y) else {
            return ABOVE;
        };
        let Ok(x) = usize::try_from(x) else {
            return LEFT;
        };
        self.at(x.min(self.stride.saturating_sub(1)), y)
    }

    /// Sets the pixel at (`x`, `y`); nothing if it is not there.
    pub(crate) fn set(&mut self, x: usize, y: usize, v: u8) {
        if let Some(slot) = self.index(x, y).and_then(|i| self.data.get_mut(i)) {
            *slot = v;
        }
    }
}

/// A coordinate as the signed type of [`Plane::get`].
pub(crate) fn coord(v: usize) -> i32 {
    i32::try_from(v).unwrap_or(i32::MAX)
}

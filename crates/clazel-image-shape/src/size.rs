//! The size limits of decision 6.0(j) and the checked size function.

/// The most pixels on a side (2^14).
pub const MAX_SIDE: u32 = 1 << 14;

/// The most pixels in an image (2^26).
pub const MAX_PIXELS: u64 = 1 << 26;

/// Bytes per pixel: straight RGBA8.
pub const BYTES_PER_PIXEL: usize = 4;

/// The most bytes of a frame's pixel buffer: 2^26 pixels of 4 bytes (2^28,
/// which fits a 32-bit `usize`).
pub const MAX_RGBA_BYTES: usize = 1 << 28;

/// Why a size is refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SizeError {
    /// A side is 0.
    Empty,
    /// Wider than [`MAX_SIDE`].
    TooWide,
    /// Taller than [`MAX_SIDE`].
    TooTall,
    /// More than [`MAX_PIXELS`] pixels.
    TooManyPixels,
}

/// The pixel count of a `width` by `height` image: both sides in
/// `1..=MAX_SIDE` and at most [`MAX_PIXELS`] pixels, else the first limit it
/// breaks, in the order of the variants of [`SizeError`].
pub fn pixel_count(width: u32, height: u32) -> Result<u64, SizeError> {
    if width == 0 || height == 0 {
        return Err(SizeError::Empty);
    }
    if width > MAX_SIDE {
        return Err(SizeError::TooWide);
    }
    if height > MAX_SIDE {
        return Err(SizeError::TooTall);
    }
    // Both sides are at most 2^14, so the product is at most 2^28: the
    // multiplication cannot fail, and is checked anyway.
    let pixels = u64::from(width)
        .checked_mul(u64::from(height))
        .ok_or(SizeError::TooManyPixels)?;
    if pixels > MAX_PIXELS {
        return Err(SizeError::TooManyPixels);
    }
    Ok(pixels)
}

/// The bytes of an RGBA8 buffer for a `width` by `height` image:
/// `4 * width * height`, under the limits of [`pixel_count`].
pub fn rgba_len(width: u32, height: u32) -> Result<usize, SizeError> {
    let pixels = pixel_count(width, height)?;
    let bytes = pixels
        .checked_mul(BYTES_PER_PIXEL as u64)
        .ok_or(SizeError::TooManyPixels)?;
    usize::try_from(bytes).map_err(|_| SizeError::TooManyPixels)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn limits() {
        assert_eq!(rgba_len(1, 1), Ok(4));
        assert_eq!(rgba_len(3, 2), Ok(24));
        assert_eq!(rgba_len(0, 5), Err(SizeError::Empty));
        assert_eq!(rgba_len(5, 0), Err(SizeError::Empty));
        assert_eq!(rgba_len(MAX_SIDE, 1), Ok(4 * MAX_SIDE as usize));
        assert_eq!(rgba_len(MAX_SIDE + 1, 1), Err(SizeError::TooWide));
        assert_eq!(rgba_len(1, MAX_SIDE + 1), Err(SizeError::TooTall));
        assert_eq!(rgba_len(u32::MAX, u32::MAX), Err(SizeError::TooWide));
        // 2^13 x 2^13 = 2^26 is the largest allowed square-ish image.
        assert_eq!(rgba_len(1 << 13, 1 << 13), Ok(MAX_RGBA_BYTES));
        assert_eq!(pixel_count(1 << 13, 1 << 13), Ok(MAX_PIXELS));
        // One pixel more than the limit: 2^14 x 2^12 is exactly 2^26, so
        // widen the short side.
        assert_eq!(pixel_count(MAX_SIDE, 1 << 12), Ok(MAX_PIXELS));
        assert_eq!(
            pixel_count(MAX_SIDE, (1 << 12) + 1),
            Err(SizeError::TooManyPixels)
        );
        assert_eq!(
            pixel_count(MAX_SIDE, MAX_SIDE),
            Err(SizeError::TooManyPixels)
        );
    }
}

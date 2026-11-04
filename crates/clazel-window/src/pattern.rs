//! A test pattern: something to look at until the GPU process draws (phase-5.md
//! item 5.17b). A gradient that shows the size and any stretching, a one-pixel
//! frame that shows the client area's exact edges, and a crosshair.

/// `width` by `height` pixels in rows from the top, each blue, green, red and an
/// unused byte. `shift` moves the gradient; `mark` is where the crosshair goes.
/// Empty if the size does not fit in memory.
pub fn test_pattern(width: u32, height: u32, shift: i32, mark: Option<(i32, i32)>) -> Vec<u8> {
    let bytes = u64::from(width)
        .checked_mul(u64::from(height))
        .and_then(|n| n.checked_mul(4))
        .and_then(|n| usize::try_from(n).ok());
    let Some(bytes) = bytes else {
        return Vec::new();
    };
    let mut pixels = vec![0u8; bytes];
    let row_bytes = usize::try_from(width).unwrap_or(0).saturating_mul(4);
    if row_bytes == 0 {
        return pixels;
    }
    for (y, row) in (0u32..).zip(pixels.chunks_exact_mut(row_bytes)) {
        let (row_pixels, _) = row.as_chunks_mut::<4>();
        for (x, pixel) in (0u32..).zip(row_pixels) {
            *pixel = colour_at(x, y, width, height, shift, mark);
        }
    }
    pixels
}

fn colour_at(
    x: u32,
    y: u32,
    width: u32,
    height: u32,
    shift: i32,
    mark: Option<(i32, i32)>,
) -> [u8; 4] {
    let on_frame =
        x == 0 || y == 0 || x == width.saturating_sub(1) || y == height.saturating_sub(1);
    if on_frame {
        return [255, 255, 255, 0];
    }
    if let Some((mx, my)) = mark
        && (i64::from(x) == i64::from(mx) || i64::from(y) == i64::from(my))
    {
        return [0, 255, 255, 0];
    }
    let blue = ramp(x, width);
    let green = ramp(y, height);
    let red = u8::try_from(shift.rem_euclid(256)).unwrap_or(0);
    [blue, green, red, 0]
}

/// `at` of `of` as 0 to 255.
fn ramp(at: u32, of: u32) -> u8 {
    let scaled = u64::from(at)
        .saturating_mul(255)
        .checked_div(u64::from(of))
        .unwrap_or(0);
    u8::try_from(scaled).unwrap_or(255)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_length_is_four_bytes_a_pixel() {
        assert_eq!(test_pattern(3, 2, 0, None).len(), 24);
        assert_eq!(test_pattern(0, 5, 0, None).len(), 0);
        assert_eq!(test_pattern(5, 0, 0, None).len(), 0);
    }

    #[test]
    fn the_corners_are_on_the_frame() {
        let p = test_pattern(4, 4, 0, None);
        assert_eq!(p.get(..4), Some(&[255, 255, 255, 0][..]));
        assert_eq!(p.get(60..64), Some(&[255, 255, 255, 0][..]));
    }

    #[test]
    fn the_mark_and_the_shift_show() {
        let plain = test_pattern(8, 8, 0, None);
        assert_ne!(plain, test_pattern(8, 8, 0, Some((3, 3))));
        assert_ne!(plain, test_pattern(8, 8, 90, None));
        // A negative shift still gives a colour, and a mark off the window nothing.
        assert_eq!(test_pattern(8, 8, -256, None), plain);
        assert_eq!(test_pattern(8, 8, 0, Some((-1, 99))), plain);
    }

    #[test]
    fn the_ramp_takes_any_inputs() {
        assert_eq!(ramp(0, 0), 0);
        assert_eq!(ramp(u32::MAX, 1), 255);
    }
}

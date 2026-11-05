//! A test pattern: something to look at until the GPU process draws (phase-5.md
//! item 5.17b). A gradient that shows the size and any stretching, a one-pixel
//! frame that shows the client area's exact edges, and a crosshair.

const WHITE: u32 = 0x00FF_FFFF;
const YELLOW: u32 = 0x00FF_FF00;

/// `width` by `height` pixels in rows from the top, each `0x00RRGGBB`. `shift`
/// moves the gradient; `mark` is where the crosshair goes. Empty if the size does
/// not fit in memory.
pub fn test_pattern(width: u32, height: u32, shift: i32, mark: Option<(i32, i32)>) -> Vec<u32> {
    let count = u64::from(width)
        .checked_mul(u64::from(height))
        .and_then(|n| usize::try_from(n).ok());
    let Some(count) = count else {
        return Vec::new();
    };
    let mut pixels = vec![0u32; count];
    let row_length = usize::try_from(width).unwrap_or(0);
    if row_length == 0 {
        return pixels;
    }
    for (y, row) in (0u32..).zip(pixels.chunks_exact_mut(row_length)) {
        for (x, pixel) in (0u32..).zip(row) {
            *pixel = colour_at(x, y, width, height, shift, mark);
        }
    }
    pixels
}

fn colour_at(x: u32, y: u32, width: u32, height: u32, shift: i32, mark: Option<(i32, i32)>) -> u32 {
    let on_frame =
        x == 0 || y == 0 || x == width.saturating_sub(1) || y == height.saturating_sub(1);
    if on_frame {
        return WHITE;
    }
    if let Some((mx, my)) = mark
        && (i64::from(x) == i64::from(mx) || i64::from(y) == i64::from(my))
    {
        return YELLOW;
    }
    let blue = ramp(x, width);
    let green = ramp(y, height);
    let red = u8::try_from(shift.rem_euclid(256)).unwrap_or(0);
    u32::from_le_bytes([blue, green, red, 0])
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
    fn the_length_is_one_entry_a_pixel() {
        assert_eq!(test_pattern(3, 2, 0, None).len(), 6);
        assert_eq!(test_pattern(0, 5, 0, None).len(), 0);
        assert_eq!(test_pattern(5, 0, 0, None).len(), 0);
    }

    #[test]
    fn the_corners_are_on_the_frame() {
        let p = test_pattern(4, 4, 0, None);
        assert_eq!(p.first(), Some(&WHITE));
        assert_eq!(p.last(), Some(&WHITE));
    }

    #[test]
    fn colours_are_in_rgb_order() {
        // Inside the frame, with the shift in red, x in blue and y in green.
        let p = test_pattern(3, 3, 0x12, None);
        assert_eq!(p.get(4), Some(&0x0012_5555));
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

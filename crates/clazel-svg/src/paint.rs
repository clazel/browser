//! The `fill` attribute (SVG 2 section 13.4.1) for the one syntax in scope:
//! CSS Color 4's hexadecimal notation, `#rgb` and `#rrggbb` (section 6.1,
//! "RGB Hexadecimal Notations"), opaque.

use clazel_image_shape::Error;

/// The initial value of `fill` is black (SVG 2 section 13.4.1).
pub(crate) const BLACK: [u8; 3] = [0, 0, 0];

fn hex(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b.wrapping_sub(b'0')),
        b'a'..=b'f' => Some(b.wrapping_sub(b'a').wrapping_add(10)),
        b'A'..=b'F' => Some(b.wrapping_sub(b'A').wrapping_add(10)),
        _ => None,
    }
}

/// `#rgb` is `#rrggbb` with each digit doubled (CSS Color 4 section 6.1).
pub(crate) fn fill(value: &[u8]) -> Result<[u8; 3], Error> {
    let unsupported = Error::Unsupported("a fill that is not #rgb or #rrggbb");
    let digits = value.strip_prefix(b"#").ok_or(unsupported)?;
    let mut v = [0u8; 6];
    let n = digits.len();
    if n != 3 && n != 6 {
        return Err(unsupported);
    }
    for (slot, &b) in v.iter_mut().zip(digits) {
        *slot = hex(b).ok_or(unsupported)?;
    }
    let [r, g, b, c, d, e] = v;
    let byte = |hi: u8, lo: u8| hi.wrapping_mul(16).wrapping_add(lo);
    Ok(if n == 3 {
        [byte(r, r), byte(g, g), byte(b, b)]
    } else {
        [byte(r, g), byte(b, c), byte(d, e)]
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hex_colours() {
        assert_eq!(fill(b"#f60"), Ok([0xff, 0x66, 0x00]));
        assert_eq!(fill(b"#FFFFFF"), Ok([255, 255, 255]));
        assert_eq!(fill(b"#999"), Ok([0x99, 0x99, 0x99]));
        assert_eq!(fill(b"#0a1B2c"), Ok([0x0a, 0x1b, 0x2c]));
        for bad in [
            "",
            "#",
            "#f",
            "#ff",
            "#ffff",
            "#fffff",
            "#fffffff",
            "f60",
            "#ggg",
            "red",
            "none",
            "#f60 ",
            " #f60",
            "#ff6600ff",
            "rgb(1,2,3)",
            "url(#a)",
        ] {
            assert!(
                matches!(fill(bad.as_bytes()), Err(Error::Unsupported(_))),
                "{bad}"
            );
        }
    }
}

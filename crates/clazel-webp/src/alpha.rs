//! The alpha plane of a lossy image: RFC 9649 section 2.7.1.2, the `ALPH`
//! chunk. Its first byte is `Rsv` (2 bits, "Readers MUST ignore this field"),
//! `P` (2 bits, preprocessing: informative, a decoder "is not required to use
//! this information in any specified way", so it is not used), `F` (2 bits,
//! the filtering method) and `C` (2 bits, the compression method); the rest of
//! the chunk is the alpha bitstream: `width * height` raw bytes if `C` is 0,
//! or the lossless format of section 3 without a header, if `C` is 1, whose
//! green channel is the alpha (`vp8l.rs` decodes it).
//!
//! The filtering is applied to the decoded plane here.

use clazel_image_shape::Error;

/// The two fields of the first byte this decoder uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct AlphaHeader {
    /// `F`: 0 none, 1 horizontal, 2 vertical, 3 gradient.
    pub(crate) filter: u8,
    /// `C`: 0 raw, 1 lossless.
    pub(crate) compression: u8,
}

/// The first byte of an `ALPH` chunk (Figure 10: `Rsv`, `P`, `F`, `C`, from
/// the high bits down). A compression method over 1 is an error (section
/// 2.7.1.2 defines 0 and 1).
pub(crate) fn parse_header(b: u8) -> Result<AlphaHeader, Error> {
    let compression = b & 3;
    if compression > 1 {
        return Err(Error::Malformed("an ALPH compression method over 1"));
    }
    Ok(AlphaHeader {
        filter: (b >> 2) & 3,
        compression,
    })
}

/// Undoes the filtering of section 2.7.1.2 on a plane of `width` by `height`
/// values, in place, in scan order: "alpha = (predictor + X) % 256", with
/// the predictor by method (0 none: 0; 1 horizontal: A, the pixel to the left;
/// 2 vertical: B, above; 3 gradient: `clip(A + B - C)`, C being above left)
/// and the special cases: "the top-left value at location (0, 0) uses 0 as
/// the predictor value"; "for horizontal or gradient filtering methods, the
/// left-most pixels at location (0, y) are predicted using the location (0,
/// y-1) just above"; "for vertical or gradient filtering methods, the
/// top-most pixels at location (x, 0) are predicted using the location (x-1,
/// 0) on the left".
pub(crate) fn unfilter(plane: &mut [u8], width: usize, filter: u8) {
    if filter == 0 || width == 0 {
        return;
    }
    for i in 0..plane.len() {
        let (x, y) = (
            i.checked_rem(width).unwrap_or(0),
            i.checked_div(width).unwrap_or(0),
        );
        let get = |j: Option<usize>| -> i32 {
            j.and_then(|j| plane.get(j)).copied().map_or(0, i32::from)
        };
        let left = (x > 0).then(|| i.wrapping_sub(1));
        let above = (y > 0).then(|| i.wrapping_sub(width));
        let corner = (x > 0 && y > 0).then(|| i.wrapping_sub(width).wrapping_sub(1));
        let predictor = match filter {
            1 => get(left.or(above)),
            2 => get(above.or(left)),
            _ => match (left, above) {
                (Some(_), Some(_)) => get(left)
                    .wrapping_add(get(above))
                    .wrapping_sub(get(corner))
                    .clamp(0, 255),
                (None, Some(_)) => get(above),
                (Some(_), None) => get(left),
                (None, None) => 0,
            },
        };
        if let Some(slot) = plane.get_mut(i) {
            *slot = slot.wrapping_add(predictor as u8);
        }
    }
}

/// Section 2.7.1.2: "the transparency information must be extracted from the
/// green channel of the ARGB quadruplet": copies the green byte of each of
/// `alpha.len()` pixels of the RGBA `rgba` to `alpha`.
pub(crate) fn green_to_alpha(rgba: &[u8], alpha: &mut [u8]) {
    for (a, px) in alpha.iter_mut().zip(rgba.as_chunks::<4>().0.iter()) {
        *a = px.get(1).copied().unwrap_or(0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_fields() {
        assert_eq!(
            parse_header(0b0001_1001),
            Ok(AlphaHeader {
                filter: 2,
                compression: 1
            })
        );
        // Rsv and P are not looked at.
        assert_eq!(
            parse_header(0b1111_0000),
            Ok(AlphaHeader {
                filter: 0,
                compression: 0
            })
        );
        assert!(parse_header(2).is_err());
        assert!(parse_header(3).is_err());
    }

    /// Filters a plane forwards (the encoder's side, written from the same
    /// text) and checks `unfilter` inverts it.
    #[test]
    fn unfilter_inverts() {
        let (w, h) = (5usize, 4usize);
        let plane: Vec<u8> = (0..w * h)
            .map(|i| u8::try_from(i.wrapping_mul(37) % 251).unwrap_or(0))
            .collect();
        for filter in 0u8..4 {
            let mut coded = plane.clone();
            for i in 0..plane.len() {
                let (x, y) = (i % w, i / w);
                let at = |j: usize| i32::from(plane.get(j).copied().unwrap_or(0));
                let a = at(i.wrapping_sub(1));
                let b = at(i.wrapping_sub(w));
                let c = at(i.wrapping_sub(w).wrapping_sub(1));
                let pred = match (filter, x > 0, y > 0) {
                    (0, _, _) | (_, false, false) => 0,
                    (1, true, _) | (3, true, false) | (2, true, false) => a,
                    (1, false, true) | (2, _, true) | (3, false, true) => b,
                    _ => (a + b - c).clamp(0, 255),
                };
                if let Some(s) = coded.get_mut(i) {
                    *s = s.wrapping_sub(pred as u8);
                }
            }
            unfilter(&mut coded, w, filter);
            assert_eq!(coded, plane, "filter {filter}");
        }
    }

    #[test]
    fn green() {
        let mut alpha = [0u8; 2];
        green_to_alpha(&[1, 2, 3, 4, 5, 6, 7, 8], &mut alpha);
        assert_eq!(alpha, [2, 6]);
    }
}

//! LZ77 prefix coding of lengths and distances, and the distance map
//! (RFC 9649 sections 3.6.2.2 and 3.6.2.2.1).

/// The offsets `(xi, yi)` of distance codes 1 to 120, from Figure 20 of
/// RFC 9649 (section 3.6.2.2.1, "Distance Code to Neighboring Pixel Offset
/// Mapping"). Code `c` is `DISTANCE_MAP[c - 1]`.
pub(crate) const DISTANCE_MAP: [(i8, i8); 120] = [
    (0, 1),
    (1, 0),
    (1, 1),
    (-1, 1),
    (0, 2),
    (2, 0),
    (1, 2),
    (-1, 2),
    (2, 1),
    (-2, 1),
    (2, 2),
    (-2, 2),
    (0, 3),
    (3, 0),
    (1, 3),
    (-1, 3),
    (3, 1),
    (-3, 1),
    (2, 3),
    (-2, 3),
    (3, 2),
    (-3, 2),
    (0, 4),
    (4, 0),
    (1, 4),
    (-1, 4),
    (4, 1),
    (-4, 1),
    (3, 3),
    (-3, 3),
    (2, 4),
    (-2, 4),
    (4, 2),
    (-4, 2),
    (0, 5),
    (3, 4),
    (-3, 4),
    (4, 3),
    (-4, 3),
    (5, 0),
    (1, 5),
    (-1, 5),
    (5, 1),
    (-5, 1),
    (2, 5),
    (-2, 5),
    (5, 2),
    (-5, 2),
    (4, 4),
    (-4, 4),
    (3, 5),
    (-3, 5),
    (5, 3),
    (-5, 3),
    (0, 6),
    (6, 0),
    (1, 6),
    (-1, 6),
    (6, 1),
    (-6, 1),
    (2, 6),
    (-2, 6),
    (6, 2),
    (-6, 2),
    (4, 5),
    (-4, 5),
    (5, 4),
    (-5, 4),
    (3, 6),
    (-3, 6),
    (6, 3),
    (-6, 3),
    (0, 7),
    (7, 0),
    (1, 7),
    (-1, 7),
    (5, 5),
    (-5, 5),
    (7, 1),
    (-7, 1),
    (4, 6),
    (-4, 6),
    (6, 4),
    (-6, 4),
    (2, 7),
    (-2, 7),
    (7, 2),
    (-7, 2),
    (3, 7),
    (-3, 7),
    (7, 3),
    (-7, 3),
    (5, 6),
    (-5, 6),
    (6, 5),
    (-6, 5),
    (8, 0),
    (4, 7),
    (-4, 7),
    (7, 4),
    (-7, 4),
    (8, 1),
    (8, 2),
    (6, 6),
    (-6, 6),
    (8, 3),
    (5, 7),
    (-5, 7),
    (7, 5),
    (-7, 5),
    (8, 4),
    (6, 7),
    (-6, 7),
    (7, 6),
    (-7, 6),
    (8, 5),
    (7, 7),
    (-7, 7),
    (8, 6),
    (8, 7),
];

/// The extra bits that follow a length or distance prefix code
/// (section 3.6.2.2): `(prefix_code - 2) >> 1` for codes of 4 and over,
/// none below.
pub(crate) fn extra_bits(prefix: u32) -> u8 {
    if prefix < 4 {
        0
    } else {
        u8::try_from(prefix.saturating_sub(2) >> 1).unwrap_or(0)
    }
}

/// The value (a length, or a distance code) of a prefix code with its extra
/// bits read (section 3.6.2.2's pseudocode):
///
/// ```text
/// if (prefix_code < 4) return prefix_code + 1;
/// int extra_bits = (prefix_code - 2) >> 1;
/// int offset = (2 + (prefix_code & 1)) << extra_bits;
/// return offset + ReadBits(extra_bits) + 1;
/// ```
pub(crate) fn value(prefix: u32, extra: u32) -> u32 {
    if prefix < 4 {
        return prefix.saturating_add(1);
    }
    let bits = u32::from(extra_bits(prefix));
    let offset = 2u32
        .saturating_add(prefix & 1)
        .checked_shl(bits)
        .unwrap_or(0);
    offset.saturating_add(extra).saturating_add(1)
}

/// The distance, in pixels back in scan-line order, of distance code `code`
/// (at least 1) in an image `xsize` pixels wide (section 3.6.2.2.1):
/// codes over 120 are the distance plus 120; the others go through the map
/// as `xi + yi * xsize`, and a result under 1 is 1.
pub(crate) fn distance(code: u32, xsize: u32) -> u32 {
    if code > 120 {
        return code.saturating_sub(120);
    }
    let at = usize::try_from(code.saturating_sub(1)).unwrap_or(0);
    let (xi, yi) = DISTANCE_MAP.get(at).copied().unwrap_or((0, 1));
    let d = i64::from(yi)
        .saturating_mul(i64::from(xsize))
        .saturating_add(i64::from(xi));
    u32::try_from(d.max(1)).unwrap_or(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn values() {
        assert_eq!(value(0, 0), 1);
        assert_eq!(value(3, 0), 4);
        // Table 4: 4 is 5..6 with 1 extra bit, 5 is 7..8, 6 is 9..12.
        assert_eq!((value(4, 0), value(4, 1)), (5, 6));
        assert_eq!((value(5, 0), value(5, 1)), (7, 8));
        assert_eq!((value(6, 0), value(6, 3)), (9, 12));
        assert_eq!((value(23, 0), value(23, 1023)), (3073, 4096));
        assert_eq!((value(38, 0), value(38, (1 << 18) - 1)), (524_289, 786_432));
        assert_eq!(
            (value(39, 0), value(39, (1 << 18) - 1)),
            (786_433, 1_048_576)
        );
        assert_eq!(extra_bits(39), 18);
        assert_eq!(extra_bits(23), 10);
    }

    #[test]
    fn map() {
        // Code 1 is the pixel above, 2 the one on the left, 3 the top left,
        // 4 the top right.
        assert_eq!(distance(1, 10), 10);
        assert_eq!(distance(2, 10), 1);
        assert_eq!(distance(3, 10), 11);
        assert_eq!(distance(4, 10), 9);
        // (-1, 1) at width 1 is 0, so 1.
        assert_eq!(distance(4, 1), 1);
        assert_eq!(distance(120, 100), 7 * 100 + 8);
        assert_eq!(distance(121, 100), 1);
        assert_eq!(distance(1000, 100), 880);
        assert_eq!(DISTANCE_MAP.len(), 120);
    }
}

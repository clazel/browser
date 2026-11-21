//! EXIF's Orientation tag, and nothing else of EXIF.
//!
//! The Exif 2.32 specification (CIPA DC-008-2019) §4.5.4 stores an APP1
//! segment as `Exif\0\0`, a TIFF header (byte order `II` or `MM`, the
//! number 42, the offset of the first IFD from the TIFF header), and IFD 0,
//! a count and 12-byte entries (tag, type, count, value). Tag 0x0112 is
//! Orientation, a SHORT of count 1 whose value is 1 to 8 (Table 6, §4.6.4).
//!
//! **Listed choice:** IFD 0 must lie within the first [`MAX_BYTES`] bytes
//! of the segment (the decoder keeps no more of it), and an Orientation of
//! any other type or count, or a value outside 1 to 8, is ignored (as 1).

/// The bytes of an APP1 segment the decoder looks at.
pub(crate) const MAX_BYTES: usize = 512;

/// The value of the Orientation tag in the Exif data of an APP1 segment's
/// body, if it has a valid one.
pub(crate) fn orientation(body: &[u8]) -> Option<u8> {
    let tiff = body.strip_prefix(b"Exif\0\0")?;
    let big = match tiff.get(..2)? {
        b"II" => false,
        b"MM" => true,
        _ => return None,
    };
    let u16_at = |o: usize| -> Option<u16> {
        let b = tiff.get(o..o.checked_add(2)?)?;
        let a = [*b.first()?, *b.get(1)?];
        Some(if big {
            u16::from_be_bytes(a)
        } else {
            u16::from_le_bytes(a)
        })
    };
    let u32_at = |o: usize| -> Option<u32> {
        let b = tiff.get(o..o.checked_add(4)?)?;
        let a = [*b.first()?, *b.get(1)?, *b.get(2)?, *b.get(3)?];
        Some(if big {
            u32::from_be_bytes(a)
        } else {
            u32::from_le_bytes(a)
        })
    };
    if u16_at(2)? != 42 {
        return None;
    }
    let ifd = usize::try_from(u32_at(4)?).ok()?;
    let count = usize::from(u16_at(ifd)?);
    for i in 0..count {
        let e = ifd.checked_add(2)?.checked_add(i.checked_mul(12)?)?;
        if u16_at(e)? == 0x0112 {
            let typ = u16_at(e.checked_add(2)?)?;
            let n = u32_at(e.checked_add(4)?)?;
            if typ != 3 || n != 1 {
                return None;
            }
            let v = u8::try_from(u16_at(e.checked_add(8)?)?).ok()?;
            return (1..=8).contains(&v).then_some(v);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An Exif body with one IFD entry of Orientation `v`, in either byte
    /// order, with `before` other entries first.
    fn exif(big: bool, v: u16, before: usize) -> Vec<u8> {
        let p16 = |x: u16| {
            if big {
                x.to_be_bytes()
            } else {
                x.to_le_bytes()
            }
        };
        let p32 = |x: u32| {
            if big {
                x.to_be_bytes()
            } else {
                x.to_le_bytes()
            }
        };
        let mut b = b"Exif\0\0".to_vec();
        b.extend(if big { b"MM" } else { b"II" });
        b.extend(p16(42));
        b.extend(p32(8));
        b.extend(p16(u16::try_from(before.saturating_add(1)).unwrap_or(0)));
        for i in 0..before {
            b.extend(p16(0x0100u16.saturating_add(u16::try_from(i).unwrap_or(0))));
            b.extend(p16(2));
            b.extend(p32(4));
            b.extend([0; 4]);
        }
        b.extend(p16(0x0112));
        b.extend(p16(3));
        b.extend(p32(1));
        b.extend(p16(v));
        b.extend([0; 2]);
        b
    }

    #[test]
    fn reads_both_byte_orders() {
        for big in [false, true] {
            for v in 1..=8u16 {
                assert_eq!(orientation(&exif(big, v, 0)), u8::try_from(v).ok());
                assert_eq!(orientation(&exif(big, v, 5)), u8::try_from(v).ok());
            }
        }
    }

    #[test]
    fn ignores_what_it_does_not_understand() {
        assert_eq!(orientation(&exif(false, 0, 0)), None);
        assert_eq!(orientation(&exif(false, 9, 0)), None);
        assert_eq!(orientation(b"Exif\0\0II"), None);
        assert_eq!(orientation(b"Exif\0\0"), None);
        assert_eq!(orientation(b"JFIF\0"), None);
        assert_eq!(orientation(&[]), None);
        // Truncated inside the entry.
        let full = exif(false, 6, 0);
        for n in 0..26 {
            let r = orientation(full.get(..n).unwrap_or(&[]));
            assert!(r.is_none(), "{n}");
        }
        assert_eq!(orientation(&full), Some(6));
    }
}

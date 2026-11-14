//! The files `clazel browse --headless OUT URL` writes (phase-5.md item 5.23): a
//! PPM, or a PNG whose deflate stream is stored (uncompressed) blocks, both
//! written here (CLAUDE.md rule 8: no image library).
//!
//! # Sources
//!
//! - **PPM**: Netpbm's `ppm` format (<https://netpbm.sourceforge.net/doc/ppm.html>):
//!   `P6`, whitespace, width, height, maxval 255, one whitespace byte, then RGB
//!   rows from the top.
//! - **PNG**: Portable Network Graphics (PNG) Specification (Third Edition), W3C
//!   Recommendation, 24 June 2025 (<https://www.w3.org/TR/2025/REC-png-3-20250624/>):
//!   §5.2 the signature; §5.3 chunk layout (length, type, data, CRC over type
//!   and data); §11.2.1 `IHDR`, §11.2.4 `IDAT`, §11.2.5 `IEND`; §7.3 filter type
//!   0 before each scanline; Annex D, the CRC-32 (polynomial 0xEDB88320,
//!   reflected, initial and final XOR 0xFFFFFFFF).
//! - **zlib**: RFC 1950 §2.2 (CMF 0x78: deflate, 32 KiB window; FLG 0x01 makes
//!   `CMF·256 + FLG` a multiple of 31; Adler-32 last, big-endian) and §8 (the
//!   Adler-32 algorithm).
//! - **deflate**: RFC 1951 §3.2.3 (block header: BFINAL, then BTYPE 00) and
//!   §3.2.4 (a stored block: to the byte boundary, LEN and NLEN little-endian,
//!   at most 65,535 bytes).
//!
//! # Modelling choices
//!
//! - **RGB, 8 bits, over white.** The GPU's pixels are RGBA8, premultiplied
//!   (`clazel_gpu::channel`); a file has no page behind it, so each pixel is
//!   composited over white: `c + (255 − a)`, clamped at 255 (a list may give a
//!   channel above its alpha, 5.17b). The window shows the same composite.
//! - **The bytes are data.** Nothing here reads them for anything but copying.

/// RGBA8, premultiplied, composited over white, as RGB.
pub fn rgb_over_white(rgba: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity((rgba.len() / 4).saturating_mul(3));
    for [r, g, b, a] in rgba.as_chunks::<4>().0 {
        // `!a` is 255 − a.
        out.extend([r, g, b].map(|c| c.saturating_add(!a)));
    }
    out
}

/// A binary PPM of `rgb`, `width` by `height`; `None` if the length is wrong.
pub fn ppm(width: u32, height: u32, rgb: &[u8]) -> Option<Vec<u8>> {
    if rgb.len() != rgb_len(width, height)? {
        return None;
    }
    let mut out = format!("P6\n{width} {height}\n255\n").into_bytes();
    out.extend_from_slice(rgb);
    Some(out)
}

fn rgb_len(width: u32, height: u32) -> Option<usize> {
    usize::try_from(width)
        .ok()?
        .checked_mul(usize::try_from(height).ok()?)?
        .checked_mul(3)
}

/// PNG Annex D's CRC-32 table.
fn crc_table() -> [u32; 256] {
    let mut table = [0u32; 256];
    for (n, slot) in (0u32..).zip(table.iter_mut()) {
        let mut c = n;
        for _ in 0..8 {
            c = if c & 1 == 1 {
                0xEDB8_8320 ^ (c >> 1)
            } else {
                c >> 1
            };
        }
        *slot = c;
    }
    table
}

/// PNG Annex D's CRC-32 of `bytes`.
pub fn crc32(bytes: &[u8]) -> u32 {
    let table = crc_table();
    let mut c = 0xFFFF_FFFFu32;
    for &b in bytes {
        let i = usize::from(u8::try_from((c ^ u32::from(b)) & 0xFF).unwrap_or(0));
        c = table.get(i).copied().unwrap_or(0) ^ (c >> 8);
    }
    c ^ 0xFFFF_FFFF
}

/// RFC 1950 §8's Adler-32 of `bytes`.
pub fn adler32(bytes: &[u8]) -> u32 {
    const BASE: u32 = 65_521;
    let (mut a, mut b) = (1u32, 0u32);
    for &x in bytes {
        // Both stay below BASE, so neither sum can overflow.
        a = a.saturating_add(u32::from(x)) % BASE;
        b = b.saturating_add(a) % BASE;
    }
    (b << 16) | a
}

/// One chunk: length, type, data, CRC of type and data (§5.3).
fn chunk(out: &mut Vec<u8>, kind: &[u8; 4], data: &[u8]) -> Option<()> {
    out.extend_from_slice(&u32::try_from(data.len()).ok()?.to_be_bytes());
    let start = out.len();
    out.extend_from_slice(kind);
    out.extend_from_slice(data);
    let crc = crc32(out.get(start..)?);
    out.extend_from_slice(&crc.to_be_bytes());
    Some(())
}

/// The largest stored block (RFC 1951 §3.2.4).
const STORED_MAX: usize = 65_535;

/// A zlib stream of stored deflate blocks holding `raw`.
fn zlib_stored(raw: &[u8]) -> Vec<u8> {
    let mut out = vec![0x78, 0x01];
    let blocks: Vec<&[u8]> = if raw.is_empty() {
        vec![raw]
    } else {
        raw.chunks(STORED_MAX).collect()
    };
    let last = blocks.len().saturating_sub(1);
    for (i, block) in blocks.into_iter().enumerate() {
        // BFINAL in bit 0, BTYPE 00 in bits 1 and 2; the rest pads to the byte.
        out.push(u8::from(i == last));
        let len = u16::try_from(block.len()).unwrap_or(u16::MAX);
        out.extend_from_slice(&len.to_le_bytes());
        out.extend_from_slice(&(!len).to_le_bytes());
        out.extend_from_slice(block);
    }
    out.extend_from_slice(&adler32(raw).to_be_bytes());
    out
}

/// A PNG of `rgb`, `width` by `height` (each 1 to 2^31 − 1), colour type 2, bit
/// depth 8, no interlace, every scanline with filter 0; `None` if the length is
/// wrong or a side is out of range.
pub fn png(width: u32, height: u32, rgb: &[u8]) -> Option<Vec<u8>> {
    let side = |s: u32| (1..=0x7FFF_FFFF).contains(&s);
    if !side(width) || !side(height) || rgb.len() != rgb_len(width, height)? {
        return None;
    }
    let row = usize::try_from(width).ok()?.checked_mul(3)?;
    let mut raw = Vec::with_capacity(rgb.len().checked_add(usize::try_from(height).ok()?)?);
    for line in rgb.chunks_exact(row) {
        raw.push(0);
        raw.extend_from_slice(line);
    }
    let mut out = vec![0x89, b'P', b'N', b'G', 0x0D, 0x0A, 0x1A, 0x0A];
    let mut ihdr = Vec::with_capacity(13);
    ihdr.extend_from_slice(&width.to_be_bytes());
    ihdr.extend_from_slice(&height.to_be_bytes());
    // Bit depth 8, colour type 2 (truecolour), compression 0, filter 0, interlace 0.
    ihdr.extend_from_slice(&[8, 2, 0, 0, 0]);
    chunk(&mut out, b"IHDR", &ihdr)?;
    chunk(&mut out, b"IDAT", &zlib_stored(&raw))?;
    chunk(&mut out, b"IEND", &[])?;
    Some(out)
}

/// Test-only: a decoder for what [`png`] writes, sharing nothing with it but
/// [`adler32`], for the unit tests below and `tests/browse_gpu.rs`.
#[cfg(test)]
pub mod check {
    use super::adler32;

    /// CRC-32 written again, bit by bit with no table, for the decoder below.
    pub fn crc_bitwise(bytes: &[u8]) -> u32 {
        let mut c = !0u32;
        for &b in bytes {
            c ^= u32::from(b);
            for _ in 0..8 {
                let low = c & 1;
                c = (c >> 1) ^ (0xEDB8_8320 & 0u32.wrapping_sub(low));
            }
        }
        !c
    }

    fn be(b: &[u8], at: usize) -> Option<u32> {
        Some(u32::from_be_bytes(
            b.get(at..at.checked_add(4)?)?.try_into().ok()?,
        ))
    }

    /// Decode a PNG this module could have written: check the signature, every
    /// chunk's CRC, the header, the zlib header, every stored block's LEN and
    /// NLEN, the Adler-32 and each scanline's filter byte; the RGB rows.
    pub fn decode_png(file: &[u8]) -> Option<(u32, u32, Vec<u8>)> {
        if file.get(..8)? != [0x89, b'P', b'N', b'G', 0x0D, 0x0A, 0x1A, 0x0A] {
            return None;
        }
        let (mut at, mut chunks) = (8usize, Vec::new());
        while at < file.len() {
            let len = usize::try_from(be(file, at)?).ok()?;
            let body = file.get(at.checked_add(4)?..at.checked_add(8)?.checked_add(len)?)?;
            let crc = be(file, at.checked_add(8)?.checked_add(len)?)?;
            if crc_bitwise(body) != crc {
                return None;
            }
            chunks.push((body.get(..4)?.to_vec(), body.get(4..)?.to_vec()));
            at = at.checked_add(12)?.checked_add(len)?;
        }
        let kinds: Vec<&[u8]> = chunks.iter().map(|(k, _)| k.as_slice()).collect();
        if kinds != [&b"IHDR"[..], b"IDAT", b"IEND"] {
            return None;
        }
        let ihdr = &chunks.first()?.1;
        let (w, h) = (be(ihdr, 0)?, be(ihdr, 4)?);
        if ihdr.get(8..)? != [8, 2, 0, 0, 0] || !chunks.get(2)?.1.is_empty() {
            return None;
        }
        let z = &chunks.get(1)?.1;
        // CMF 0x78, FLG 0x01: 0x7801 = 31 × 991.
        if z.get(..2)? != [0x78, 0x01] || 31u32.checked_mul(991) != Some(0x7801) {
            return None;
        }
        let le16 = |at: usize| {
            Some(u16::from_le_bytes(
                z.get(at..at.checked_add(2)?)?.try_into().ok()?,
            ))
        };
        let (mut at, mut raw) = (2usize, Vec::new());
        loop {
            let header = *z.get(at)?;
            let len = le16(at.checked_add(1)?)?;
            let nlen = le16(at.checked_add(3)?)?;
            if header & 0b110 != 0 || header >> 3 != 0 || nlen != !len {
                return None;
            }
            let start = at.checked_add(5)?;
            at = start.checked_add(usize::from(len))?;
            raw.extend_from_slice(z.get(start..at)?);
            if header & 1 == 1 {
                break;
            }
        }
        if be(z, at)? != adler32(&raw) || Some(z.len()) != at.checked_add(4) {
            return None;
        }
        let row = usize::try_from(w).ok()?.checked_mul(3)?.checked_add(1)?;
        if Some(raw.len()) != row.checked_mul(usize::try_from(h).ok()?) {
            return None;
        }
        let mut rgb = Vec::new();
        for line in raw.chunks_exact(row) {
            if *line.first()? != 0 {
                return None;
            }
            rgb.extend_from_slice(line.get(1..)?);
        }
        Some((w, h, rgb))
    }
}

#[cfg(test)]
mod tests {
    use super::check::{crc_bitwise, decode_png as decode};
    use super::{adler32, crc32, png, ppm, rgb_over_white};

    #[test]
    fn the_checksums_give_their_published_values() {
        // The CRC-32 check value of "123456789" (as in every CRC catalogue) and
        // the Adler-32 of "Wikipedia" (RFC 1950's algorithm, its usual example).
        assert_eq!(crc32(b"123456789"), 0xCBF4_3926);
        assert_eq!(crc_bitwise(b"123456789"), 0xCBF4_3926);
        assert_eq!(adler32(b"Wikipedia"), 0x11E6_0398);
        assert_eq!(adler32(b""), 1);
        assert_eq!(crc32(b"IEND"), 0xAE42_6082);
    }

    #[test]
    fn a_png_decodes_to_its_pixels() {
        let rgb: Vec<u8> = (0..3u32 * 2 * 3)
            .map(|i| u8::try_from(i * 11 % 256).unwrap_or(0))
            .collect();
        let file = png(3, 2, &rgb);
        assert_eq!(file.as_deref().and_then(decode), Some((3, 2, rgb)));
    }

    #[test]
    fn a_large_png_spans_several_stored_blocks() {
        // 200 × 120 × 3 + 120 filter bytes = 72,120 bytes: two blocks.
        let rgb: Vec<u8> = (0..200u32 * 120 * 3)
            .map(|i| u8::try_from(i % 251).unwrap_or(0))
            .collect();
        let file = png(200, 120, &rgb);
        assert!(file.as_ref().is_some_and(|f| f.len() > 72_120));
        assert_eq!(file.as_deref().and_then(decode), Some((200, 120, rgb)));
    }

    #[test]
    fn a_flipped_byte_fails_its_crc() {
        let Some(mut file) = png(1, 1, &[1, 2, 3]) else {
            unreachable!("a 1 by 1 PNG");
        };
        assert!(decode(&file).is_some());
        if let Some(b) = file.get_mut(20) {
            *b ^= 1;
        }
        assert!(decode(&file).is_none());
    }

    #[test]
    fn wrong_lengths_and_sides_are_refused() {
        assert_eq!(png(2, 2, &[0; 11]), None);
        assert_eq!(png(0, 1, &[]), None);
        assert_eq!(ppm(2, 1, &[0; 5]), None);
        assert_eq!(
            ppm(1, 1, &[1, 2, 3]),
            Some(b"P6\n1 1\n255\n\x01\x02\x03".to_vec())
        );
    }

    #[test]
    fn premultiplied_pixels_go_over_white() {
        // Transparent is white; opaque is itself; half-alpha black is grey; a
        // channel above its alpha clamps.
        let rgba = [0, 0, 0, 0, 10, 20, 30, 255, 0, 0, 0, 128, 0xff, 0, 0, 0x40];
        assert_eq!(
            rgb_over_white(&rgba),
            [255, 255, 255, 10, 20, 30, 127, 127, 127, 255, 191, 191]
        );
    }
}

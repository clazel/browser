//! `decode_config`: the size of the image, read from the first bytes.
//!
//! The same marker grammar as the step function (T.81 B.1.1.2 to B.1.1.4
//! and B.2.2), over a prefix kept whole by the caller. The size is the
//! frame header's, turned by the EXIF orientation if an Exif APP1 segment
//! with a valid Orientation precedes the frame header (a later one is
//! ignored, and so is it by the step function).

use clazel_image_shape::{Config, ConfigStatus, Error, Format};

use crate::exif;
use crate::markers::{Kind, kind};
use crate::output::swaps;

fn bad<T>(why: &'static str) -> Result<T, Error> {
    Err(Error::Malformed(why))
}

/// What `decode_config` says of `prefix`.
pub(crate) fn config(prefix: &[u8]) -> Result<ConfigStatus, Error> {
    // SOI, T.81 B.1.1.3.
    let soi = [0xFFu8, 0xD8];
    let n = prefix.len().min(2);
    if prefix.get(..n) != soi.get(..n) {
        return bad("not a JPEG: no SOI");
    }
    if n < 2 {
        return Ok(ConfigStatus::NeedMore);
    }
    let mut i = 2usize;
    let mut orientation: Option<u8> = None;
    loop {
        // A marker: `0xFF`, then fill `0xFF`s, then the code.
        match prefix.get(i) {
            None => return Ok(ConfigStatus::NeedMore),
            Some(0xFF) => {}
            Some(_) => return bad("expected a marker"),
        }
        i = i.saturating_add(1);
        let m = loop {
            let Some(&m) = prefix.get(i) else {
                return Ok(ConfigStatus::NeedMore);
            };
            i = i.saturating_add(1);
            if m != 0xFF {
                break m;
            }
        };
        match kind(m) {
            Kind::Standalone => continue,
            Kind::Soi => return bad("a second SOI"),
            Kind::Eoi => return bad("EOI before a frame"),
            Kind::Scan => return bad("a scan before the frame header"),
            Kind::Unsupported(why) => return Err(Error::Unsupported(why)),
            Kind::Invalid => return bad("an unknown or reserved marker"),
            Kind::Frame | Kind::Read | Kind::Skip => {}
        }
        let (Some(&hi), Some(&lo)) = (prefix.get(i), prefix.get(i.saturating_add(1))) else {
            return Ok(ConfigStatus::NeedMore);
        };
        let l = usize::from(u16::from_be_bytes([hi, lo]));
        if l < 2 {
            return bad("segment length under 2");
        }
        let body = i.saturating_add(2);
        let len = l.saturating_sub(2);
        if kind(m) == Kind::Frame {
            // B.2.2: `P`, `Y`, `X`, `Nf`, the first six bytes of the body.
            let Some(h) = prefix.get(body..body.saturating_add(6)) else {
                return Ok(ConfigStatus::NeedMore);
            };
            let at = |k: usize| h.get(k).copied().unwrap_or(0);
            let (p, y, x, nf) = (
                at(0),
                u16::from_be_bytes([at(1), at(2)]),
                u16::from_be_bytes([at(3), at(4)]),
                at(5),
            );
            if p != 8 {
                return Err(Error::Unsupported("a sample precision other than 8 bits"));
            }
            if nf == 0 {
                return bad("a frame with no components");
            }
            if !matches!(nf, 1 | 3 | 4) {
                return Err(Error::Unsupported("a component count other than 1, 3, 4"));
            }
            if x == 0 {
                return bad("an image of width 0");
            }
            if y == 0 {
                return bad("an image of height 0 (DNL is not supported)");
            }
            let (w, h) = if swaps(orientation.unwrap_or(1)) {
                (y, x)
            } else {
                (x, y)
            };
            return Ok(ConfigStatus::Ready(Config::new(
                Format::Jpeg,
                u32::from(w),
                u32::from(h),
                crate::decoder::FRAMES,
            )?));
        }
        if m == 0xE1 && orientation.is_none() {
            // Only the first bytes of the segment are looked at.
            let want = len.min(exif::MAX_BYTES);
            let Some(b) = prefix.get(body..body.saturating_add(want)) else {
                return Ok(ConfigStatus::NeedMore);
            };
            orientation = exif::orientation(b);
        }
        i = body.saturating_add(len);
    }
}

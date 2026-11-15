//! The GPU process's two channels besides the kernel's (items 5.18 and 5.23): the
//! **list socket**, renderer to GPU process, and the **surface socket**, GPU
//! process to host. Neither passes through the kernel, which carries no pixels and
//! no lists (5.18); both are socket pairs the host makes at `SpawnGpu` and hands
//! over by number.
//!
//! # Modelling choices
//!
//! - **A list is framed by its length**: 4 bytes, little-endian, then the list's
//!   bytes as `clazel_displaylist` encodes them, at most [`LIST_MAX`]. The IPC
//!   frame (`clazel_ipc`'s `MAX_FRAME`, 1 MiB) is too small for a list with masks
//!   (the validator allows 64 MiB of live coverage), and a list is not CBOR.
//! - **How buffers pass on macOS, until the Mach-port route exists.** The plan
//!   moves an IOSurface from the GPU process to the host with a Mach port
//!   (5.21, 5.21a), which needs new `clazel-sys` calls and a prototype nobody
//!   has built; on Linux it names a `memfd`, which macOS lacks. Until then the
//!   ring is the host's: three slots per GPU process, each a copy of a frame's
//!   pixels that the GPU process **sends** on the surface socket, then names
//!   in `FrameReady`. The kernel still decides which slot is shown under which
//!   URL; the host only shows a slot a `Paint` names. The cost is one copy of
//!   each frame through a socket and into the host's memory, which the plan's
//!   route avoids; the host reads the bytes as pixels, never as anything else.
//! - **A surface frame** is 12 bytes, three little-endian `u32`s (slot, width,
//!   height), then `width × height × 4` bytes of RGBA8, premultiplied, rows from
//!   the top (the GPU's target, `Backend::read_pixels`). Slots are 0 to
//!   [`SLOTS`] − 1 and sides 1 to 8192 ([`crate::geom::MAX_VIEWPORT_SIDE`]), so a
//!   frame is at most 256 MiB; the reader checks both before it allocates.

use std::io::{self, Read, Write};

use crate::geom::MAX_VIEWPORT_SIDE;

/// The largest list the GPU process reads, in bytes: 256 MiB.
pub const LIST_MAX: usize = 1 << 28;

/// The ring's slots per GPU process (the kernel's ring of 3, item 5.18).
pub const SLOTS: u32 = 3;

/// One frame's pixels on the surface socket.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SurfaceFrame {
    /// The ring slot, below [`SLOTS`].
    pub slot: u32,
    /// Width in device pixels.
    pub width: u32,
    /// Height in device pixels.
    pub height: u32,
    /// RGBA8, premultiplied, rows from the top, packed.
    pub pixels: Vec<u8>,
}

fn invalid(what: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, what.to_owned())
}

/// Fill `buf`, or `Ok(false)` if the stream ended before its first byte.
fn read_or_end<R: Read>(r: &mut R, buf: &mut [u8]) -> io::Result<bool> {
    let mut got = 0usize;
    while let Some(rest) = buf.get_mut(got..).filter(|b| !b.is_empty()) {
        match r.read(rest) {
            Ok(0) if got == 0 => return Ok(false),
            Ok(0) => return Err(io::ErrorKind::UnexpectedEof.into()),
            Ok(n) => got = got.saturating_add(n),
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(true)
}

fn le(b: &[u8], at: usize) -> u32 {
    let mut w = [0u8; 4];
    if let Some(s) = b.get(at..at.saturating_add(4)) {
        w.copy_from_slice(s);
    }
    u32::from_le_bytes(w)
}

/// Write one list.
pub fn write_list<W: Write>(w: &mut W, list: &[u8]) -> io::Result<()> {
    if list.len() > LIST_MAX {
        return Err(invalid("a list over LIST_MAX"));
    }
    let n = u32::try_from(list.len()).map_err(|_| invalid("a list over LIST_MAX"))?;
    w.write_all(&n.to_le_bytes())?;
    w.write_all(list)?;
    w.flush()
}

/// Read one list; `None` if the stream ended between lists.
pub fn read_list<R: Read>(r: &mut R) -> io::Result<Option<Vec<u8>>> {
    let mut head = [0u8; 4];
    if !read_or_end(r, &mut head)? {
        return Ok(None);
    }
    let n = usize::try_from(u32::from_le_bytes(head)).map_err(|_| invalid("length"))?;
    if n > LIST_MAX {
        return Err(invalid("a list over LIST_MAX"));
    }
    let mut list = vec![0u8; n];
    r.read_exact(&mut list)?;
    Ok(Some(list))
}

/// The bytes of a `width` by `height` frame, if the slot and sides are allowed.
pub fn frame_bytes(slot: u32, width: u32, height: u32) -> Option<usize> {
    let side = |s: u32| (1..=MAX_VIEWPORT_SIDE).contains(&s);
    if slot >= SLOTS || !side(width) || !side(height) {
        return None;
    }
    usize::try_from(width)
        .ok()?
        .checked_mul(usize::try_from(height).ok()?)?
        .checked_mul(4)
}

/// Write one frame's pixels.
pub fn write_surface<W: Write>(w: &mut W, frame: &SurfaceFrame) -> io::Result<()> {
    let n = frame_bytes(frame.slot, frame.width, frame.height)
        .ok_or_else(|| invalid("a surface frame's slot or size"))?;
    if frame.pixels.len() != n {
        return Err(invalid("a surface frame's length"));
    }
    let mut head = [0u8; 12];
    for (i, v) in [frame.slot, frame.width, frame.height]
        .into_iter()
        .enumerate()
    {
        let at = i.saturating_mul(4);
        if let Some(s) = head.get_mut(at..at.saturating_add(4)) {
            s.copy_from_slice(&v.to_le_bytes());
        }
    }
    w.write_all(&head)?;
    w.write_all(&frame.pixels)?;
    w.flush()
}

/// Read one frame's pixels; `None` if the stream ended between frames. The slot
/// and sides are checked before the pixels are allocated.
pub fn read_surface<R: Read>(r: &mut R) -> io::Result<Option<SurfaceFrame>> {
    let mut head = [0u8; 12];
    if !read_or_end(r, &mut head)? {
        return Ok(None);
    }
    let (slot, width, height) = (le(&head, 0), le(&head, 4), le(&head, 8));
    let n = frame_bytes(slot, width, height)
        .ok_or_else(|| invalid("a surface frame's slot or size"))?;
    let mut pixels = vec![0u8; n];
    r.read_exact(&mut pixels)?;
    Ok(Some(SurfaceFrame {
        slot,
        width,
        height,
        pixels,
    }))
}

#[cfg(test)]
mod tests {
    use super::{
        LIST_MAX, SurfaceFrame, frame_bytes, read_list, read_surface, write_list, write_surface,
    };

    #[test]
    fn lists_round_trip_and_end_cleanly() {
        let mut wire = Vec::new();
        assert!(write_list(&mut wire, b"abc").is_ok());
        assert!(write_list(&mut wire, b"").is_ok());
        let mut r = &wire[..];
        assert_eq!(read_list(&mut r).ok().flatten(), Some(b"abc".to_vec()));
        assert_eq!(read_list(&mut r).ok().flatten(), Some(Vec::new()));
        assert!(matches!(read_list(&mut r), Ok(None)));
    }

    #[test]
    fn a_cut_or_oversized_list_is_an_error() {
        let mut r = &[3u8, 0, 0, 0, b'a'][..];
        assert!(read_list(&mut r).is_err());
        let mut r = &[7u8, 0][..];
        assert!(read_list(&mut r).is_err());
        let over = u32::try_from(LIST_MAX).unwrap_or(0).saturating_add(1);
        let mut r = &over.to_le_bytes()[..];
        assert!(read_list(&mut r).is_err());
    }

    #[test]
    fn surface_frames_round_trip() {
        let frame = SurfaceFrame {
            slot: 2,
            width: 2,
            height: 1,
            pixels: vec![1, 2, 3, 4, 5, 6, 7, 8],
        };
        let mut wire = Vec::new();
        assert!(write_surface(&mut wire, &frame).is_ok());
        assert_eq!(wire.len(), 12 + 8);
        let mut r = &wire[..];
        assert_eq!(read_surface(&mut r).ok().flatten(), Some(frame));
        assert!(matches!(read_surface(&mut r), Ok(None)));
    }

    #[test]
    fn a_surface_header_is_checked_before_allocating() {
        assert_eq!(frame_bytes(0, 1, 1), Some(4));
        assert_eq!(frame_bytes(3, 1, 1), None);
        assert_eq!(frame_bytes(0, 0, 1), None);
        assert_eq!(frame_bytes(0, 8193, 1), None);
        assert_eq!(frame_bytes(0, 8192, 8192), Some(1 << 28));
        // A header naming slot 3, or a side of 2^31, is refused without reading on.
        for head in [[3u32, 1, 1], [0, 1 << 31, 1], [0, 1, 0]] {
            let wire: Vec<u8> = head.iter().flat_map(|v| v.to_le_bytes()).collect();
            let mut r = &wire[..];
            assert!(read_surface(&mut r).is_err(), "{head:?}");
        }
        // A wrong length is refused by the writer.
        let bad = SurfaceFrame {
            slot: 0,
            width: 2,
            height: 2,
            pixels: vec![0; 4],
        };
        assert!(write_surface(&mut Vec::new(), &bad).is_err());
    }
}

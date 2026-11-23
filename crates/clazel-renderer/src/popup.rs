//! The renderer's side of popups (phase-7.md item 7.16): the frame a
//! document's `window.open` and `target=_blank` send the kernel.
//!
//! The renderer only asks. It sends the URL as the script or the link wrote
//! it; the kernel resolves it against the committed URL, opens the tab only
//! if the kernel itself recorded a user input to this renderer a short while
//! before (`clazel-kernel`, `theorem_popup_needs_input`), and gives no
//! reply, so a refused popup looks like a tab that never loaded. Nothing in
//! the frame says that the user clicked: the kernel does not read the
//! renderer's word on it.

use std::io::{self, Write};

use clazel_ipc::message::codec::{Msg, encode_framed};

/// The frame of an `OpenTab` for `url`, or `None` if it does not fit a
/// frame.
pub fn open_tab_frame(url: &str) -> Option<Vec<u8>> {
    encode_framed(&Msg::OpenTab {
        url: url.as_bytes().to_vec(),
    })
}

/// Send an `OpenTab` for `url` on the kernel's socket.
///
/// # Errors
///
/// The socket's, or `InvalidInput` if the URL does not fit a frame.
pub fn send_open_tab<W: Write>(w: &mut W, url: &str) -> io::Result<()> {
    let frame = open_tab_frame(url)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "OpenTab over MAX_FRAME"))?;
    w.write_all(&frame)?;
    w.flush()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clazel_ipc::message::codec::decode_renderer_message;

    #[test]
    fn the_frame_is_an_open_tab_the_kernel_accepts_from_a_renderer() -> Result<(), String> {
        let frame = open_tab_frame("/popup?a=1").ok_or("does not fit a frame")?;
        // The frame's payload is the message, after the 4-octet length.
        let payload = frame.get(4..).ok_or("no payload")?;
        assert_eq!(
            decode_renderer_message(payload),
            Some(Msg::OpenTab {
                url: b"/popup?a=1".to_vec()
            })
        );
        Ok(())
    }

    #[test]
    fn send_writes_the_frame() -> Result<(), String> {
        let mut out = Vec::new();
        send_open_tab(&mut out, "http://example.test/").map_err(|e| e.to_string())?;
        assert_eq!(Some(out), open_tab_frame("http://example.test/"));
        Ok(())
    }

    #[test]
    fn a_url_over_a_frame_is_not_sent() {
        let long = "a".repeat(clazel_ipc::frame::spec::MAX_FRAME + 1);
        let mut out = Vec::new();
        let kind = send_open_tab(&mut out, &long).err().map(|e| e.kind());
        assert_eq!(kind, Some(io::ErrorKind::InvalidInput));
        assert!(out.is_empty());
    }
}

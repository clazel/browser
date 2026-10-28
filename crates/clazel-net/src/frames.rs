//! Whole frames off a socket: a 4-byte header, then the payload it announces.
//! The header's meaning (and the limit on the payload) is the caller's proven
//! function; this only moves octets.

use std::io::Read;

/// Read whole frames from `sock`, giving each (header included) to `on_frame`,
/// until the socket closes, `payload_length` refuses a header, or `on_frame`
/// returns false (then `None`). Otherwise why it ended.
pub fn read_frames(
    mut sock: impl Read,
    payload_length: fn(&[u8]) -> Option<usize>,
    mut on_frame: impl FnMut(Vec<u8>) -> bool,
) -> Option<String> {
    loop {
        let mut frame = vec![0u8; 4];
        if sock.read_exact(&mut frame).is_err() {
            return Some("closed its socket".to_owned());
        }
        let Some(len) = payload_length(&frame) else {
            let n = frame.iter().fold(0u64, |n, b| (n << 8) | u64::from(*b));
            return Some(format!("sent a frame over MAX_FRAME (announced {n} bytes)"));
        };
        let mut payload = vec![0u8; len];
        if sock.read_exact(&mut payload).is_err() {
            return Some("closed its socket inside a frame".to_owned());
        }
        frame.extend_from_slice(&payload);
        if !on_frame(frame) {
            return None;
        }
    }
}

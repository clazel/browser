//! The hostile renderer's frames (phase-2.md item 2.16).
//!
//! [`generate`] turns a seed into one frame that the kernel must refuse: a
//! frame cut short, one announcing more than `MAX_FRAME`, CBOR that is not
//! in shortest form, CBOR outside the profile (tags, maps, floats,
//! indefinite lengths), text that is not UTF-8, random bytes, a mutation of
//! a valid message, or a message only the kernel may send. The same seed
//! gives the same frame, so a failure reproduces from the seed alone.
//!
//! Every frame generated is checked against the real decoder before it is
//! returned: it must not decode to a renderer-to-kernel message (a frame
//! cut short or over `MAX_FRAME` is not a whole frame at all), so what the
//! kernel does with it is never "answer it". The generator is ours (a
//! SplitMix64 stream), not a library's.

use clazel_ipc::message::codec::{Msg, decode_framed, encode_message, is_from_renderer};
use std::io::{Read, Write};

/// A deterministic stream of numbers (SplitMix64).
pub struct Rng(u64);

impl Rng {
    /// The stream of `seed`.
    pub fn new(seed: u64) -> Rng {
        Rng(seed)
    }

    /// The next 64 bits.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A number below `n` (0 if `n` is 0).
    pub fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(u64::MAX);
        usize::try_from(self.next_u64().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }

    /// A byte.
    pub fn byte(&mut self) -> u8 {
        u8::try_from(self.next_u64() & 0xff).unwrap_or(0)
    }

    /// `n` bytes.
    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.byte()).collect()
    }

    /// Printable ASCII, up to `max` bytes.
    pub fn text(&mut self, max: usize) -> Vec<u8> {
        let n = self.below(max.saturating_add(1));
        (0..n)
            .map(|_| b' '.saturating_add(u8::try_from(self.below(95)).unwrap_or(0)))
            .collect()
    }
}

/// How a frame is hostile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    /// A valid frame cut short: the socket closes inside it.
    Truncated,
    /// A header announcing more than `MAX_FRAME`.
    Oversized,
    /// CBOR that is valid but not in shortest form.
    NonShortest,
    /// A CBOR tag (major type 6), a map, a float or an indefinite length, or a
    /// message tag the schema does not have.
    UnknownTag,
    /// A text string that is not UTF-8.
    InvalidUtf8,
    /// A well-formed frame of random bytes.
    RandomBytes,
    /// A valid message with some bytes flipped, deleted or inserted.
    Mutated,
    /// A valid message that only the kernel may send.
    KernelOnly,
}

impl Kind {
    /// Every kind.
    pub const ALL: [Kind; 8] = [
        Kind::Truncated,
        Kind::Oversized,
        Kind::NonShortest,
        Kind::UnknownTag,
        Kind::InvalidUtf8,
        Kind::RandomBytes,
        Kind::Mutated,
        Kind::KernelOnly,
    ];

    /// What the host logs when the renderer is gone, in the words of
    /// `clazel::Host`: the kernel kills a renderer on a frame it cannot
    /// decode, the host refuses an oversized frame from its header, and a
    /// socket that closes inside a frame is a closed socket.
    pub fn host_says(self) -> &'static str {
        match self {
            Kind::Truncated => "closed its socket",
            Kind::Oversized => "sent a frame over MAX_FRAME",
            _ => "killed by the kernel",
        }
    }
}

/// One hostile frame, and what it is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hostile {
    /// How it is hostile.
    pub kind: Kind,
    /// The bytes to put on the socket.
    pub bytes: Vec<u8>,
}

/// The frame of `payload`.
pub fn frame(payload: &[u8]) -> Vec<u8> {
    let len = u32::try_from(payload.len()).unwrap_or(u32::MAX);
    let mut f = len.to_be_bytes().to_vec();
    f.extend_from_slice(payload);
    f
}

/// A valid renderer-to-kernel message with random contents.
fn valid(rng: &mut Rng) -> Msg {
    match rng.below(9) {
        0 => Msg::CookieGet,
        1 => Msg::CookieSet {
            cookie_string: rng.text(24),
        },
        2 => Msg::StorageGetItem { key: rng.text(8) },
        3 => Msg::StorageSetItem {
            key: rng.text(8),
            value: rng.text(24),
        },
        4 => Msg::StorageRemoveItem { key: rng.text(8) },
        5 => Msg::StorageClear,
        6 => Msg::StorageKey {
            index: rng.next_u64(),
        },
        7 => Msg::StorageLength,
        _ => Msg::Navigate { url: rng.text(24) },
    }
}

/// `text` as a CBOR text string of at most 23 bytes; `shortest: false` writes
/// the length in a second byte.
fn cbor_text(text: &[u8], shortest: bool) -> Vec<u8> {
    let text = text.get(..23).unwrap_or(text);
    let n = u8::try_from(text.len()).unwrap_or(0);
    let mut out = if shortest {
        vec![0x60_u8.saturating_add(n)]
    } else {
        vec![0x78, n]
    };
    out.extend_from_slice(text);
    out
}

/// The payload of a frame of the given kind (the whole frame, for kinds that
/// are not about the payload).
fn build(kind: Kind, rng: &mut Rng) -> Vec<u8> {
    match kind {
        Kind::Truncated => {
            let whole = frame(&encode_message(&valid(rng)));
            let keep = rng.below(whole.len().saturating_sub(1)).saturating_add(1);
            whole.get(..keep).unwrap_or_default().to_vec()
        }
        Kind::Oversized => {
            let extra = u32::try_from(rng.below(0x7fff_0000)).unwrap_or(0);
            let announced = 0x0010_0001_u32.saturating_add(extra);
            let mut f = announced.to_be_bytes().to_vec();
            let n = rng.below(16);
            f.extend(rng.bytes(n));
            f
        }
        Kind::NonShortest => {
            let payload = match rng.below(5) {
                0 => vec![0x98, 0x01, 0x01],
                1 => vec![0x81, 0x18, 0x01],
                2 => [vec![0x82, 0x02], cbor_text(&rng.text(12), false)].concat(),
                3 => vec![0x82, 0x07, 0x1b, 0, 0, 0, 0, 0, 0, 0, 5],
                _ => vec![0x82, 0x07, 0x19, 0x00, 0x05],
            };
            frame(&payload)
        }
        Kind::UnknownTag => {
            let payload = match rng.below(6) {
                0 => vec![0x81, 0x18, 200],
                1 => vec![0x81, 0x00],
                2 => vec![0xc1, 0x81, 0x01],
                3 => vec![0xa1, 0x01, 0x01],
                4 => vec![0x9f, 0x01, 0xff],
                _ => vec![0x81, 0xfb, 0x3f, 0xf0, 0, 0, 0, 0, 0, 0],
            };
            frame(&payload)
        }
        Kind::InvalidUtf8 => {
            let bad = [0xff, 0xfe, 0xc0, 0x80, 0xed, 0xa0, 0x80]
                .get(rng.below(7))
                .copied();
            let text = [rng.text(4), vec![bad.unwrap_or(0xff)], rng.text(4)].concat();
            let tag = [0x02, 0x03, 0x05, 0x09].get(rng.below(4)).copied();
            frame(&[vec![0x82, tag.unwrap_or(2)], cbor_text(&text, true)].concat())
        }
        Kind::RandomBytes => {
            let n = rng.below(64);
            frame(&rng.bytes(n))
        }
        Kind::Mutated => {
            let mut payload = encode_message(&valid(rng));
            for _ in 0..rng.below(4).saturating_add(1) {
                let at = rng.below(payload.len());
                match rng.below(4) {
                    0 => {
                        let bit = 1_u8
                            .checked_shl(u32::try_from(rng.below(8)).unwrap_or(0))
                            .unwrap_or(1);
                        if let Some(b) = payload.get_mut(at) {
                            *b ^= bit;
                        }
                    }
                    1 => {
                        let v = rng.byte();
                        if let Some(b) = payload.get_mut(at) {
                            *b = v;
                        }
                    }
                    2 => {
                        if at < payload.len() {
                            payload.remove(at);
                        }
                    }
                    _ => {
                        let v = rng.byte();
                        payload.insert(at, v);
                    }
                }
            }
            frame(&payload)
        }
        Kind::KernelOnly => {
            let m = match rng.below(5) {
                0 => Msg::Commit {
                    url: rng.text(12),
                    content_type: rng.text(12),
                    kind: rng.next_u64(),
                },
                1 => Msg::CookieValue {
                    cookie_string: rng.text(12),
                },
                2 => Msg::StorageValue { value: None },
                3 => Msg::StorageLengthValue {
                    length: rng.next_u64(),
                },
                _ => Msg::Error {
                    code: rng.next_u64(),
                },
            };
            frame(&encode_message(&m))
        }
    }
}

/// Whether the kernel has to refuse `bytes`: they do not decode to a message
/// a renderer may send.
fn refused(bytes: &[u8]) -> bool {
    !decode_framed(bytes).is_some_and(|m| is_from_renderer(&m))
}

/// The hostile frame of `seed`: its kind and bytes are a function of the
/// seed alone.
pub fn generate(seed: u64) -> Hostile {
    let mut rng = Rng::new(seed);
    let kind = Kind::ALL
        .get(rng.below(Kind::ALL.len()))
        .copied()
        .unwrap_or(Kind::Oversized);
    for _ in 0..256 {
        let bytes = build(kind, &mut rng);
        // A mutation can land on another valid message; try again.
        if refused(&bytes) {
            return Hostile { kind, bytes };
        }
    }
    Hostile {
        kind: Kind::Oversized,
        bytes: vec![0xff; 4],
    }
}

/// Put the frame on the socket, then (unless the frame is cut short, which
/// ends in the socket closing) read until the kernel or host closes it.
pub fn attack<R: Read, W: Write>(h: &Hostile, r: &mut R, w: &mut W) -> std::io::Result<()> {
    w.write_all(&h.bytes)?;
    w.flush()?;
    if h.kind == Kind::Truncated {
        return Ok(());
    }
    let mut sink = [0u8; 256];
    while matches!(r.read(&mut sink), Ok(n) if n > 0) {}
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{Kind, generate, refused};
    use clazel_ipc::frame::codec::payload_length;
    use std::collections::HashSet;

    #[test]
    fn the_same_seed_gives_the_same_frame() {
        for seed in 0..64 {
            assert_eq!(generate(seed), generate(seed));
        }
    }

    #[test]
    fn every_kind_is_generated_and_every_frame_is_one_the_kernel_refuses() {
        let mut kinds = HashSet::new();
        // Miri runs the decoder slowly: fewer seeds, still every kind.
        let seeds = if cfg!(miri) { 200 } else { 4000 };
        for seed in 0..seeds {
            let h = generate(seed);
            kinds.insert(h.kind);
            assert!(refused(&h.bytes), "seed {seed}: {h:?}");
            // Not the fallback frame, which means no retry budget ran out.
            assert_ne!(h.bytes, vec![0xff; 4], "seed {seed}");
            match h.kind {
                Kind::Oversized => {
                    assert!(payload_length(h.bytes.get(..4).unwrap_or(&[])).is_none())
                }
                Kind::Truncated => assert!(
                    h.bytes.len() < 4
                        || payload_length(h.bytes.get(..4).unwrap_or(&[]))
                            .is_some_and(|n| n.saturating_add(4) > h.bytes.len())
                ),
                _ => {}
            }
        }
        assert_eq!(kinds.len(), Kind::ALL.len());
    }
}

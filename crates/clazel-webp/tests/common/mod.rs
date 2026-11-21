//! Shared by the WebP test targets: driving the decoder through the shared
//! interface, a deterministic generator, and byte mutations.

use clazel_image_shape::{Buffers, ConfigStatus, Decoder, Error, Status};
use clazel_webp::{FrameInfo, Webp};

/// How a decode ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum End {
    /// No more frames (the RIFF data ended, or a still image's one frame).
    Trailer,
    /// An error (the frames before it were completed).
    Error(String),
    /// The input ran out.
    Truncated,
}

/// What the decoder gave for a file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decoded {
    pub width: u32,
    pub height: u32,
    /// Each completed frame: its facts and the canvas after it.
    pub frames: Vec<(Option<FrameInfo>, Vec<u8>)>,
    pub end: End,
}

pub const CANARY: u8 = 0xEE;

/// Decodes `bytes` through the shared interface, in chunks of `chunk` bytes
/// (with an empty chunk between each pair if `empties`), checking the
/// invariant and the contract on every step.
pub fn decode(bytes: &[u8], chunk: usize, empties: bool) -> Result<Decoded, String> {
    let head = bytes.get(..bytes.len().min(64)).unwrap_or(bytes);
    let config = match Webp::decode_config(head) {
        Ok(ConfigStatus::Ready(c)) => c,
        Ok(ConfigStatus::NeedMore) => return Err("the input ends inside the header".into()),
        Err(e) => return Err(format!("{e:?}")),
    };
    // A longer prefix gives the same config.
    if let Ok(ConfigStatus::Ready(c2)) = Webp::decode_config(bytes) {
        assert_eq!(c2, config);
    }
    let plen = config.rgba_len().map_err(|e| format!("{e:?}"))?;
    let wlen = Webp::work_len(&config).map_err(|e| format!("{e:?}"))?;
    // A mutated header may name a canvas of gigabytes: not what is tested here.
    if plen > 8_000_000 || wlen > 24_000_000 {
        return Err("a canvas too big for the test".into());
    }
    let mut pixels = vec![CANARY; plen.saturating_add(3)];
    let mut work = vec![CANARY; wlen.saturating_add(3)];
    let mut state = Webp::start(&config).map_err(|e| format!("{e:?}"))?;
    let mut frames = Vec::new();
    let mut end = End::Truncated;
    {
        let mut buffers =
            Buffers::new(&config, wlen, &mut pixels, &mut work).map_err(|e| format!("{e:?}"))?;
        assert!(state.inv(&buffers));
        let mut pos = 0usize;
        let mut spent = false;
        let mut empty_turn = false;
        'feed: while pos < bytes.len() {
            let take = if empties && empty_turn {
                0
            } else {
                chunk.min(bytes.len().saturating_sub(pos))
            };
            empty_turn = !empty_turn;
            let part = bytes
                .get(pos..pos.saturating_add(take))
                .ok_or("chunk out of range")?;
            let result = state.step(part, &mut buffers);
            assert!(state.inv(&buffers), "invariant lost at byte {pos}");
            match result {
                Ok(step) => {
                    assert!(step.consumed <= part.len());
                    match step.status {
                        Status::NeedMore => {
                            assert_eq!(step.consumed, part.len());
                            pos = pos.saturating_add(take);
                        }
                        Status::FrameDone => {
                            frames.push((state.frame().copied(), buffers.pixels.to_vec()));
                            pos = pos.saturating_add(step.consumed);
                        }
                    }
                }
                Err(Error::NoMoreFrames) => {
                    end = End::Trailer;
                    break 'feed;
                }
                Err(e) => {
                    end = End::Error(format!("{e:?}"));
                    spent = true;
                    break 'feed;
                }
            }
        }
        if !spent && end == End::Truncated && pos >= bytes.len() {
            // Everything was used; a decoder at the end of its data says so.
            if let Err(Error::NoMoreFrames) = state.step(&[], &mut buffers) {
                end = End::Trailer;
            }
        }
        if spent {
            assert_eq!(state.step(&[0], &mut buffers), Err(Error::Spent));
            assert!(state.inv(&buffers));
        }
    }
    assert!(
        pixels
            .get(plen..)
            .is_some_and(|t| t.iter().all(|&b| b == CANARY))
    );
    assert!(
        work.get(wlen..)
            .is_some_and(|t| t.iter().all(|&b| b == CANARY))
    );
    Ok(Decoded {
        width: config.width(),
        height: config.height(),
        frames,
        end,
    })
}

/// A deterministic generator (xorshift64*).
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n.max(1)).unwrap_or(1);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }
}

/// One mutation of `bytes`, chosen by `rng`.
pub fn mutate(bytes: &[u8], rng: &mut Rng) -> Vec<u8> {
    let mut v = bytes.to_vec();
    for _ in 0..=rng.below(3) {
        let len = v.len().max(1);
        let at = rng.below(len);
        match rng.below(7) {
            0 => {
                if let Some(b) = v.get_mut(at) {
                    *b = u8::try_from(rng.below(256)).unwrap_or(0);
                }
            }
            1 => {
                if let Some(b) = v.get_mut(at) {
                    *b = if rng.below(2) == 0 { 0 } else { 255 };
                }
            }
            2 => v.truncate(at),
            3 => {
                let n = 1usize.saturating_add(rng.below(16));
                let end = at.saturating_add(n).min(v.len());
                if at < end {
                    v.drain(at..end);
                }
            }
            4 => {
                let n = 1usize.saturating_add(rng.below(16));
                let end = at.saturating_add(n).min(v.len());
                if let Some(run) = v.get(at..end).map(<[u8]>::to_vec) {
                    for (i, b) in run.iter().enumerate() {
                        v.insert(at.saturating_add(i), *b);
                    }
                }
            }
            5 => {
                for i in 0..4 {
                    if let Some(b) = v.get_mut(at.saturating_add(i)) {
                        *b = u8::try_from(rng.below(256)).unwrap_or(0);
                    }
                }
            }
            _ => {
                if let Some(b) = v.get_mut(at) {
                    *b ^= 1 << rng.below(8);
                }
            }
        }
    }
    v
}

/// What the reference decoder gave.
pub fn reference(bytes: &[u8]) -> Result<Decoded, String> {
    let mut d =
        image_webp::WebPDecoder::new(std::io::Cursor::new(bytes)).map_err(|e| format!("{e}"))?;
    let (w, h) = d.dimensions();
    let size = d.output_buffer_size().ok_or("size")?;
    let alpha = d.has_alpha();
    let rgba = |buf: &[u8]| -> Vec<u8> {
        if alpha {
            buf.to_vec()
        } else {
            buf.as_chunks::<3>()
                .0
                .iter()
                .flat_map(|c| c.iter().copied().chain([255]))
                .collect()
        }
    };
    let mut frames = Vec::new();
    let mut buf = vec![0u8; size];
    if d.is_animated() {
        let mut t = 0u32;
        while d.read_frame(&mut buf).is_ok() {
            t = t.saturating_add(1);
            frames.push((None, rgba(&buf)));
            if t > 100 {
                break;
            }
        }
    } else {
        d.read_image(&mut buf).map_err(|e| format!("{e}"))?;
        frames.push((None, rgba(&buf)));
    }
    Ok(Decoded {
        width: w,
        height: h,
        frames: frames
            .into_iter()
            .map(|(_, p): (Option<FrameInfo>, Vec<u8>)| (None, p))
            .collect(),
        end: End::Trailer,
    })
}

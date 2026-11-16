//! A toy decoder that implements the interface end to end, so the pattern
//! is shown to work: the raw format `width, height, pixels`.
//!
//! The stream is one byte of width (1 to 255), one byte of height (1 to
//! 255), then `4 * width * height` bytes of straight RGBA. One frame. The
//! work buffer is 4 bytes, where a pixel is staged until all four of its
//! bytes have arrived, so a chunk may end inside a pixel. It exists to
//! exercise the shape (config prefix, `NeedMore`, `FrameDone`, a work
//! buffer, `inv`) and to be the instantiation of the Kani template in
//! `proofs.rs`; no browser path reads it.

use crate::{Buffers, Config, ConfigStatus, Decoder, Error, Format, FrameCount, Status, Step};

/// The header: width and height, one byte each.
const HEADER: u8 = 2;

/// The bytes of a pixel, which is also the work buffer's length.
const PIXEL: usize = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// Reading the header or pixels.
    Run,
    /// The frame is complete.
    Done,
    /// An error happened.
    Spent,
}

/// The toy decoder's state: fixed-size, no allocation.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Toy {
    config: Config,
    phase: Phase,
    /// Header bytes still to skip (the stream is fed from byte 0).
    skip: u8,
    /// Bytes of the current pixel already in `work`.
    staged: usize,
    /// Bytes of `pixels` already written.
    written: usize,
}

impl Toy {
    /// Poisons the decoder and says why.
    fn fail(&mut self, e: Error) -> Error {
        self.phase = Phase::Spent;
        e
    }
}

impl Decoder for Toy {
    fn decode_config(prefix: &[u8]) -> Result<ConfigStatus, Error> {
        match (prefix.first(), prefix.get(1)) {
            (Some(&w), Some(&h)) => Ok(ConfigStatus::Ready(Config::new(
                Format::Raw,
                u32::from(w),
                u32::from(h),
                FrameCount::Known(1),
            )?)),
            _ => Ok(ConfigStatus::NeedMore),
        }
    }

    fn work_len(_config: &Config) -> Result<usize, Error> {
        Ok(PIXEL)
    }

    fn start(config: &Config) -> Result<Toy, Error> {
        if config.format() != Format::Raw || config.width() > 255 || config.height() > 255 {
            return Err(Error::Unsupported("not a raw image"));
        }
        config.rgba_len()?;
        Ok(Toy {
            config: *config,
            phase: Phase::Run,
            skip: HEADER,
            staged: 0,
            written: 0,
        })
    }

    fn config(&self) -> &Config {
        &self.config
    }

    fn step(&mut self, chunk: &[u8], buffers: &mut Buffers<'_>) -> Result<Step, Error> {
        match self.phase {
            Phase::Spent => return Err(Error::Spent),
            Phase::Done => return Err(Error::NoMoreFrames),
            Phase::Run => {}
        }
        let pixel_bytes = buffers.pixels.len();
        for (i, &byte) in chunk.iter().enumerate() {
            if self.skip > 0 {
                self.skip = self.skip.saturating_sub(1);
                continue;
            }
            match buffers.work.get_mut(self.staged) {
                Some(slot) => *slot = byte,
                None => return Err(self.fail(Error::Buffers)),
            }
            self.staged = self.staged.saturating_add(1);
            if self.staged < PIXEL {
                continue;
            }
            let end = self.written.saturating_add(PIXEL);
            match (
                buffers.work.get(..PIXEL),
                buffers.pixels.get_mut(self.written..end),
            ) {
                (Some(px), Some(dst)) if px.len() == dst.len() => dst.copy_from_slice(px),
                _ => return Err(self.fail(Error::Buffers)),
            }
            self.staged = 0;
            self.written = end;
            if self.written >= pixel_bytes {
                self.phase = Phase::Done;
                return Ok(Step {
                    consumed: i.saturating_add(1),
                    status: Status::FrameDone,
                });
            }
        }
        Ok(Step {
            consumed: chunk.len(),
            status: Status::NeedMore,
        })
    }

    fn inv(&self, buffers: &Buffers<'_>) -> bool {
        let Ok(plen) = self.config.rgba_len() else {
            return false;
        };
        buffers.pixels.len() == plen
            && buffers.work.len() == PIXEL
            && self.skip <= HEADER
            && self.staged < PIXEL
            && self.written.is_multiple_of(PIXEL)
            && self.written <= plen
            && match self.phase {
                Phase::Run => self.written < plen,
                Phase::Done => self.written == plen && self.staged == 0 && self.skip == 0,
                Phase::Spent => true,
            }
    }
}

/// Any state of a toy decoder of an image at most 2 by 2 (so 16 bytes of
/// pixels), every counter symbolic: the harness assumes `inv` on top.
#[cfg(kani)]
pub(crate) fn any_toy() -> Option<Toy> {
    let width: u32 = kani::any();
    let height: u32 = kani::any();
    kani::assume(width <= 2 && height <= 2);
    let config = Config::new(Format::Raw, width, height, FrameCount::Known(1)).ok()?;
    let phase = match kani::any::<u8>() % 3 {
        0 => Phase::Run,
        1 => Phase::Done,
        _ => Phase::Spent,
    };
    Some(Toy {
        config,
        phase,
        skip: kani::any(),
        staged: kani::any(),
        written: kani::any(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Decodes `stream` in chunks of `chunk_len` (0 means one empty chunk
    /// between every pair), through the public shape only.
    fn decode(stream: &[u8], chunk_len: usize) -> Result<(Config, Vec<u8>, usize), Error> {
        // decode_config on growing prefixes.
        let mut config = None;
        for n in 0..=stream.len() {
            if let ConfigStatus::Ready(c) = Toy::decode_config(stream.get(..n).unwrap_or(&[]))? {
                config = Some(c);
                break;
            }
        }
        let config = config.ok_or(Error::Truncated)?;
        let plen = config.rgba_len()?;
        let mut pixels = vec![0xEE; plen.saturating_add(3)];
        let mut work = vec![0xEE; PIXEL.saturating_add(1)];
        let mut buffers = Buffers::new(&config, Toy::work_len(&config)?, &mut pixels, &mut work)?;
        let mut state = Toy::start(&config)?;
        assert!(state.inv(&buffers));
        let mut rest = stream;
        let mut fed = 0usize;
        loop {
            let take = chunk_len.min(rest.len());
            let (chunk, after) = rest.split_at(take);
            let step = state.step(chunk, &mut buffers)?;
            assert!(state.inv(&buffers));
            assert!(step.consumed <= chunk.len());
            match step.status {
                Status::NeedMore => {
                    assert_eq!(step.consumed, chunk.len());
                    if after.is_empty() && chunk.is_empty() {
                        return Err(Error::Truncated);
                    }
                    fed = fed.saturating_add(chunk.len());
                    rest = after;
                }
                Status::FrameDone => {
                    let used = fed.saturating_add(step.consumed);
                    // Nothing past the buffers was touched.
                    assert!(
                        pixels
                            .get(plen..)
                            .is_some_and(|t| t.iter().all(|&b| b == 0xEE))
                    );
                    assert!(
                        work.get(PIXEL..)
                            .is_some_and(|t| t.iter().all(|&b| b == 0xEE))
                    );
                    pixels.truncate(plen);
                    return Ok((config, pixels, used));
                }
            }
        }
    }

    fn image() -> Vec<u8> {
        let mut v = vec![2, 2];
        v.extend((0..16u8).map(|i| i.saturating_mul(3).saturating_add(1)));
        v
    }

    #[test]
    fn decodes_at_every_chunk_size() -> Result<(), Error> {
        let stream = image();
        for chunk_len in 1..=stream.len() + 2 {
            let (config, pixels, used) = decode(&stream, chunk_len)?;
            assert_eq!((config.width(), config.height()), (2, 2));
            assert_eq!(config.frames(), FrameCount::Known(1));
            assert_eq!(
                Some(pixels.as_slice()),
                stream.get(2..),
                "chunk {chunk_len}"
            );
            assert_eq!(used, stream.len());
        }
        Ok(())
    }

    #[test]
    fn trailing_bytes_are_not_consumed() -> Result<(), Error> {
        let mut stream = image();
        stream.extend([9, 9, 9]);
        let (_, pixels, used) = decode(&stream, stream.len())?;
        assert_eq!(Some(pixels.as_slice()), stream.get(2..18));
        assert_eq!(used, 18);
        Ok(())
    }

    #[test]
    fn config_needs_two_bytes_and_obeys_limits() {
        assert_eq!(Toy::decode_config(&[]), Ok(ConfigStatus::NeedMore));
        assert_eq!(Toy::decode_config(&[5]), Ok(ConfigStatus::NeedMore));
        assert!(matches!(
            Toy::decode_config(&[0, 5]),
            Err(Error::Size(crate::SizeError::Empty))
        ));
        assert!(matches!(
            Toy::decode_config(&[255, 255, 1, 2, 3]),
            Ok(ConfigStatus::Ready(_))
        ));
    }

    #[test]
    fn truncated_stream_is_not_framedone() {
        let stream = image();
        assert_eq!(
            decode(stream.get(..17).unwrap_or(&[]), 4).err(),
            Some(Error::Truncated)
        );
    }

    #[test]
    fn after_the_frame() -> Result<(), Error> {
        let config = Config::new(Format::Raw, 1, 1, FrameCount::Known(1))?;
        let (mut p, mut w) = ([0u8; 4], [0u8; 4]);
        let mut b = Buffers::new(&config, 4, &mut p, &mut w)?;
        let mut s = Toy::start(&config)?;
        let step = s.step(&[1, 1, 5, 6, 7, 8, 99], &mut b)?;
        assert_eq!(
            step,
            Step {
                consumed: 6,
                status: Status::FrameDone
            }
        );
        assert_eq!(s.step(&[1], &mut b), Err(Error::NoMoreFrames));
        assert_eq!(b.pixels, [5, 6, 7, 8]);
        Ok(())
    }

    #[test]
    fn a_wrong_buffer_poisons() -> Result<(), Error> {
        let config = Config::new(Format::Raw, 1, 1, FrameCount::Known(1))?;
        // Not what Buffers::new gives: a work buffer of 2 bytes.
        let (mut p, mut w) = ([0u8; 4], [0u8; 2]);
        let mut b = Buffers {
            pixels: &mut p,
            work: &mut w,
        };
        let mut s = Toy::start(&config)?;
        assert!(!s.inv(&b));
        assert_eq!(s.step(&[1, 1, 5, 6, 7, 8], &mut b), Err(Error::Buffers));
        assert_eq!(s.step(&[1], &mut b), Err(Error::Spent));
        Ok(())
    }

    #[test]
    fn start_refuses_other_formats() -> Result<(), Error> {
        let config = Config::new(Format::Png, 1, 1, FrameCount::Unknown)?;
        assert!(matches!(Toy::start(&config), Err(Error::Unsupported(_))));
        Ok(())
    }

    #[test]
    fn config_new_refuses_over_limits() {
        assert!(matches!(
            Config::new(Format::Png, 16385, 1, FrameCount::Known(1)),
            Err(Error::Size(crate::SizeError::TooWide))
        ));
        assert!(matches!(
            Config::new(Format::Png, 1, 1, FrameCount::Known(0)),
            Err(Error::Malformed(_))
        ));
    }
}

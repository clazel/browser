//! The caller-owned buffers a decoder works in.

use crate::{Config, Error};

/// The pixel buffer and the work buffer of one decode, both owned by the
/// caller and sized from the [`Config`]; the decoder allocates nothing.
///
/// `pixels.len()` is exactly [`Config::rgba_len`] and `work.len()` exactly
/// the decoder's `work_len`; [`Buffers::new`] cuts them to that, so a
/// decoder's `inv` can say `==`.
#[derive(Debug)]
pub struct Buffers<'a> {
    /// Straight RGBA8, row-major, top row first.
    pub pixels: &'a mut [u8],
    /// Scratch space for the decoder, contents unspecified between calls
    /// except as the decoder's state says.
    pub work: &'a mut [u8],
}

impl<'a> Buffers<'a> {
    /// The buffers for `config` and a decoder whose `work_len` is
    /// `work_len`: the first `config.rgba_len()` bytes of `pixels` and the
    /// first `work_len` of `work`. [`Error::Buffers`] if either is shorter,
    /// [`Error::Size`] if the config's size is over a limit (never for a
    /// [`Config`] made by [`Config::new`]).
    pub fn new(
        config: &Config,
        work_len: usize,
        pixels: &'a mut [u8],
        work: &'a mut [u8],
    ) -> Result<Buffers<'a>, Error> {
        let plen = config.rgba_len()?;
        Ok(Buffers {
            pixels: pixels.get_mut(..plen).ok_or(Error::Buffers)?,
            work: work.get_mut(..work_len).ok_or(Error::Buffers)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Format, FrameCount};

    fn cfg() -> Result<Config, Error> {
        Config::new(Format::Raw, 2, 1, FrameCount::Known(1))
    }

    #[test]
    fn cuts_to_exact_sizes() -> Result<(), Error> {
        let (mut p, mut w) = ([0u8; 20], [0u8; 9]);
        let b = Buffers::new(&cfg()?, 4, &mut p, &mut w)?;
        assert_eq!((b.pixels.len(), b.work.len()), (8, 4));
        Ok(())
    }

    #[test]
    fn refuses_short() -> Result<(), Error> {
        let (mut p, mut w) = ([0u8; 7], [0u8; 9]);
        assert_eq!(
            Buffers::new(&cfg()?, 4, &mut p, &mut w).err(),
            Some(Error::Buffers)
        );
        let (mut p, mut w) = ([0u8; 8], [0u8; 3]);
        assert_eq!(
            Buffers::new(&cfg()?, 4, &mut p, &mut w).err(),
            Some(Error::Buffers)
        );
        Ok(())
    }
}

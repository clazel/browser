//! The decoder: `clazel_image_shape::Decoder` for the SVG in scope.
//!
//! SVG is not decoded in a stream: the whole document (at most
//! [`DOC_MAX`] bytes) is collected in the work buffer, and when the root
//! element's end tag arrives the document is read twice (see `scan.rs`): a
//! validating pass, then the drawing pass. `step` therefore says
//! `NeedMore` until the root element ends, then `FrameDone`, with
//! `consumed` the bytes up to and including its closing `>`. Bytes after
//! it are not read (listed choice 9).
//!
//! The work buffer is the document followed by the rasterizer's row
//! accumulator: `DOC_MAX + 4 * (width + 2)` bytes.
//!
//! The image is drawn at the size of the [`Config`] given to
//! [`Decoder::start`], which need not be the size `decode_config` reported
//! (the `width` and `height` attributes: the intrinsic size): the `viewBox`
//! is mapped to the whole of it by `preserveAspectRatio`'s default
//! (`scan.rs`, `map.rs`). A caller that wants the intrinsic size passes the
//! config `decode_config` gave back; one that scales (a `background-size`,
//! a device pixel ratio) builds `Config::new(Format::Svg, w, h, ..)`.

use crate::limits::DOC_MAX;
use crate::raster::acc_len;
use crate::scan::{Pass, Scan, read_root, run};
use crate::xml::{Reader, Stop};
use clazel_image_shape::{
    Buffers, Config, ConfigStatus, Decoder, Error, Format, FrameCount, Status, Step,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Phase {
    /// Collecting the document.
    Collect,
    /// The frame is complete.
    Done,
    /// An error happened.
    Spent,
}

/// The decoder's state: fixed-size, no allocation.
#[derive(Debug, Clone, Copy)]
pub struct Svg {
    pub(crate) config: Config,
    pub(crate) phase: Phase,
    /// Bytes of the document in `work`.
    pub(crate) len: usize,
}

impl Svg {
    fn collect(&mut self, chunk: &[u8], buffers: &mut Buffers<'_>) -> Result<Step, Error> {
        let (doc, acc) = buffers
            .work
            .split_at_mut_checked(DOC_MAX)
            .ok_or(Error::Buffers)?;
        let old = self.len;
        let room = DOC_MAX.saturating_sub(old);
        let take = chunk.len().min(room);
        let head = chunk.get(..take).ok_or(Error::Buffers)?;
        let end = old.checked_add(take).ok_or(Error::Buffers)?;
        let slot = doc.get_mut(old..end).ok_or(Error::Buffers)?;
        slot.copy_from_slice(head);
        self.len = end;
        // A document cannot end without a `>`: only read when one arrived.
        let mut result = Scan::Incomplete;
        let size = (self.config.width(), self.config.height());
        let held = doc.get(..end).ok_or(Error::Buffers)?;
        if head.contains(&b'>') {
            result = run(held, size, &mut Pass::Validate)?;
        }
        match result {
            Scan::Incomplete => {
                if take < chunk.len() {
                    return Err(Error::Unsupported("a document too large to keep"));
                }
                Ok(Step {
                    consumed: chunk.len(),
                    status: Status::NeedMore,
                })
            }
            Scan::Complete(n) => {
                let mut draw = Pass::Draw {
                    pixels: &mut *buffers.pixels,
                    acc,
                };
                // The same bytes, so the same end (checked, not assumed).
                if run(held, size, &mut draw)? != Scan::Complete(n) {
                    return Err(Error::Malformed("the two passes disagree"));
                }
                self.phase = Phase::Done;
                Ok(Step {
                    consumed: n.saturating_sub(old).min(take),
                    status: Status::FrameDone,
                })
            }
        }
    }
}

impl Decoder for Svg {
    /// Reads the prolog and the `svg` start tag: the config is the
    /// intrinsic size (`width` and `height`; SVG 2 section 8.12), one frame.
    fn decode_config(prefix: &[u8]) -> Result<ConfigStatus, Error> {
        let mut rd = Reader::new(prefix);
        match read_root(&mut rd) {
            Ok((root, _)) => Ok(ConfigStatus::Ready(Config::new(
                Format::Svg,
                root.width,
                root.height,
                FrameCount::Known(1),
            )?)),
            Err(Stop::Eof) => Ok(ConfigStatus::NeedMore),
            Err(Stop::Fail(e)) => Err(e),
        }
    }

    fn work_len(config: &Config) -> Result<usize, Error> {
        acc_len(config.width())
            .and_then(|a| a.checked_add(DOC_MAX))
            .ok_or(Error::Buffers)
    }

    fn start(config: &Config) -> Result<Svg, Error> {
        if config.format() != Format::Svg {
            return Err(Error::Unsupported("not an SVG config"));
        }
        config.rgba_len()?;
        Ok(Svg {
            config: *config,
            phase: Phase::Collect,
            len: 0,
        })
    }

    fn config(&self) -> &Config {
        &self.config
    }

    fn step(&mut self, chunk: &[u8], buffers: &mut Buffers<'_>) -> Result<Step, Error> {
        match self.phase {
            Phase::Collect => {}
            Phase::Done => return Err(Error::NoMoreFrames),
            Phase::Spent => return Err(Error::Spent),
        }
        let result = self.collect(chunk, buffers);
        if result.is_err() {
            self.phase = Phase::Spent;
        }
        result
    }

    fn inv(&self, buffers: &Buffers<'_>) -> bool {
        self.config.format() == Format::Svg
            && self.len <= DOC_MAX
            && self.config.rgba_len() == Ok(buffers.pixels.len())
            && Self::work_len(&self.config) == Ok(buffers.work.len())
    }
}

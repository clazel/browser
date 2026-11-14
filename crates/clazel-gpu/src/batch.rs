//! The shared batching: a validated list and a viewport to a [`Frame`].
//!
//! Every backend draws the same frame, so this is where list semantics become GPU
//! work, once.
//!
//! # Modelling choices
//!
//! - **Clips are scissor rectangles** (the plan). The clip stack holds the
//!   intersection of the viewport with every pushed clip; each draw carries the top
//!   of the stack as its scissor, and consecutive draws with the same scissor are one
//!   batch ([`Op::Draw`]). A quad is cut to the viewport on the CPU, so its corners
//!   are small integers, and not to the clip, which the scissor does.
//! - **Nothing is drawn under an empty clip**, and a quad that misses its clip is
//!   dropped, so no scissor is ever empty.
//! - **Uploads do not split batches**: an upload only writes atlas bytes no earlier
//!   draw reads (`atlas.rs`), so it may run before the draws of the open batch. A
//!   compaction replaces the store, so it closes the open batch first.
//! - **Defensive, not trusting**: a list that passed the validator never makes this
//!   module return an error (`theorem_validated_bounds`), but every step is checked
//!   anyway and returns an [`Error`] rather than panicking.

use clazel_displaylist::exec::ExecItem;

use crate::Error;
use crate::atlas::{Atlas, Change};
use crate::backend::{Frame, Op, Quad};
use crate::geom::{Rect, Viewport};

/// The deepest clip stack: `clazel_displaylist::spec::MAX_CLIP_DEPTH`.
pub const MAX_CLIP_DEPTH: usize = 256;

/// A frame being built.
#[derive(Debug)]
pub struct Builder {
    /// The viewport as a rectangle.
    screen: Rect,
    /// The effective clips, the viewport first.
    clips: Vec<Rect>,
    /// The batch being filled: its scissor and first quad.
    open: Option<(Rect, u32)>,
    /// What is built so far.
    frame: Frame,
}

impl Builder {
    /// An empty frame for a viewport.
    pub fn new(viewport: Viewport) -> Builder {
        let screen = viewport.rect();
        Builder {
            screen,
            clips: vec![screen],
            open: None,
            frame: Frame {
                viewport: Some(viewport),
                ..Frame::default()
            },
        }
    }

    /// The current clip.
    fn clip(&self) -> Result<Rect, Error> {
        self.clips.last().copied().ok_or(Error::Range)
    }

    /// Apply one item.
    pub fn step(&mut self, item: &ExecItem, atlas: &mut Atlas) -> Result<(), Error> {
        match item {
            ExecItem::FillRect {
                x,
                y,
                width,
                height,
                colour,
            } => {
                let rect = Rect::at(*x, *y, *width, *height).ok_or(Error::Range)?;
                self.draw(Quad {
                    rect,
                    origin_x: 0,
                    origin_y: 0,
                    offset: 0,
                    columns: 0,
                    colour: *colour,
                })
            }
            ExecItem::PushClip {
                x,
                y,
                width,
                height,
            } => {
                let rect = Rect::at(*x, *y, *width, *height).ok_or(Error::Range)?;
                self.push_clip(rect)
            }
            ExecItem::PopClip => self.pop_clip(),
            ExecItem::UploadMask {
                id,
                columns,
                rows,
                coverage,
            } => {
                let mut changes = Vec::new();
                atlas.upload(*id, *columns, *rows, coverage.clone(), &mut changes)?;
                self.apply(&changes, atlas)
            }
            ExecItem::DrawMask { id, x, y, colour } => {
                let entry = atlas.get(*id).ok_or(Error::Range)?;
                let rect = Rect::at(*x, *y, entry.columns.into(), entry.rows.into())
                    .ok_or(Error::Range)?;
                self.draw(Quad {
                    rect,
                    origin_x: *x,
                    origin_y: *y,
                    offset: entry.offset,
                    columns: entry.columns.into(),
                    colour: *colour,
                })
            }
            ExecItem::FreeMask { id } => atlas.free(*id),
        }
    }

    /// Intersect the clip with `rect`.
    pub fn push_clip(&mut self, rect: Rect) -> Result<(), Error> {
        if self.clips.len() > MAX_CLIP_DEPTH {
            return Err(Error::Range);
        }
        let clip = self.clip()?.intersect(rect);
        self.clips.push(clip);
        Ok(())
    }

    /// Undo the latest [`Builder::push_clip`]; the viewport is never popped.
    pub fn pop_clip(&mut self) -> Result<(), Error> {
        if self.clips.len() < 2 {
            return Err(Error::Range);
        }
        self.clips.pop();
        Ok(())
    }

    /// Turn atlas changes into operations, in order.
    fn apply(&mut self, changes: &[Change], atlas: &Atlas) -> Result<(), Error> {
        for change in changes {
            match change {
                Change::Resize { capacity } => {
                    self.close()?;
                    self.frame.ops.push(Op::Atlas {
                        capacity: *capacity,
                    });
                }
                Change::Upload { id } => {
                    // The slot is the coverage padded with zeros to whole words,
                    // and every upload's bytes start on a word too.
                    let entry = atlas.get(*id).ok_or(Error::Range)?;
                    let start = self.frame.bytes.len();
                    let len = usize::try_from(entry.size()).map_err(|_| Error::Range)?;
                    let end = start.checked_add(len).ok_or(Error::Range)?;
                    self.frame.bytes.extend_from_slice(&entry.coverage);
                    self.frame.bytes.resize(end, 0);
                    self.frame.ops.push(Op::Upload {
                        offset: entry.offset,
                        start,
                        len,
                    });
                }
            }
        }
        Ok(())
    }

    /// Add a quad under the current clip, cut to the viewport.
    pub fn draw(&mut self, mut quad: Quad) -> Result<(), Error> {
        let scissor = self.clip()?;
        let Some(rect) = visible(quad.rect, self.screen, scissor) else {
            return Ok(());
        };
        quad.rect = rect;
        let next = u32::try_from(self.frame.quads.len()).map_err(|_| Error::Range)?;
        match self.open {
            Some((open, _)) if open == scissor => {}
            _ => {
                self.close()?;
                self.open = Some((scissor, next));
            }
        }
        self.frame.quads.push(quad);
        Ok(())
    }

    /// End the open batch, if any.
    fn close(&mut self) -> Result<(), Error> {
        if let Some((scissor, first)) = self.open.take() {
            let end = u32::try_from(self.frame.quads.len()).map_err(|_| Error::Range)?;
            let count = end.checked_sub(first).ok_or(Error::Range)?;
            if count > 0 {
                self.frame.ops.push(Op::Draw {
                    scissor,
                    first,
                    count,
                });
            }
        }
        Ok(())
    }

    /// The finished frame. Every clip must have been popped.
    pub fn finish(mut self) -> Result<Frame, Error> {
        self.close()?;
        if self.clips.len() != 1 {
            return Err(Error::Range);
        }
        Ok(self.frame)
    }
}

/// A quad's rectangle cut to the viewport, if any of it shows under `scissor`:
/// then it is inside the viewport and not empty, and `scissor` is not empty.
pub fn visible(rect: Rect, screen: Rect, scissor: Rect) -> Option<Rect> {
    let cut = rect.intersect(screen);
    (!scissor.is_empty() && !cut.intersect(scissor).is_empty()).then_some(cut)
}

/// Build the frame for a list that passed the validator, updating the atlas.
pub fn build(items: &[ExecItem], viewport: Viewport, atlas: &mut Atlas) -> Result<Frame, Error> {
    let mut builder = Builder::new(viewport);
    for item in items {
        builder.step(item, atlas)?;
    }
    builder.finish()
}

#[cfg(test)]
mod tests {
    use clazel_displaylist::exec::ExecItem;

    use super::build;
    use crate::Error;
    use crate::atlas::Atlas;
    use crate::backend::Op;
    use crate::geom::{Rect, Viewport};

    fn fill(x: i32, y: i32, w: u32, h: u32) -> ExecItem {
        ExecItem::FillRect {
            x,
            y,
            width: w,
            height: h,
            colour: 0xff00_00ff,
        }
    }

    fn clip(x: i32, y: i32, w: u32, h: u32) -> ExecItem {
        ExecItem::PushClip {
            x,
            y,
            width: w,
            height: h,
        }
    }

    fn view() -> Result<Viewport, Error> {
        Viewport::new(16, 8).ok_or(Error::Range)
    }

    #[test]
    fn same_clip_draws_are_one_batch() -> Result<(), Error> {
        let items = [fill(0, 0, 4, 4), fill(2, 2, 4, 4), fill(8, 0, 1, 1)];
        let frame = build(&items, view()?, &mut Atlas::new())?;
        assert_eq!(
            frame.ops,
            vec![Op::Draw {
                scissor: Rect {
                    x0: 0,
                    y0: 0,
                    x1: 16,
                    y1: 8
                },
                first: 0,
                count: 3
            }]
        );
        Ok(())
    }

    #[test]
    fn a_clip_change_splits_batches_and_misses_are_dropped() -> Result<(), Error> {
        let items = [
            fill(0, 0, 4, 4),
            clip(1, 1, 2, 2),
            fill(0, 0, 4, 4),
            fill(10, 0, 4, 4), // misses the clip
            ExecItem::PopClip,
            fill(-100, -100, 1000, 1000), // cut to the viewport
        ];
        let frame = build(&items, view()?, &mut Atlas::new())?;
        let screen = Rect {
            x0: 0,
            y0: 0,
            x1: 16,
            y1: 8,
        };
        assert_eq!(
            frame.ops,
            vec![
                Op::Draw {
                    scissor: screen,
                    first: 0,
                    count: 1
                },
                Op::Draw {
                    scissor: Rect {
                        x0: 1,
                        y0: 1,
                        x1: 3,
                        y1: 3
                    },
                    first: 1,
                    count: 1
                },
                Op::Draw {
                    scissor: screen,
                    first: 2,
                    count: 1
                },
            ]
        );
        assert_eq!(frame.quads.get(2).map(|q| q.rect), Some(screen));
        Ok(())
    }

    #[test]
    fn an_empty_clip_draws_nothing_and_unbalanced_clips_fail() -> Result<(), Error> {
        let items = [clip(20, 20, 1, 1), fill(0, 0, 16, 8), ExecItem::PopClip];
        let frame = build(&items, view()?, &mut Atlas::new())?;
        assert!(frame.ops.is_empty() && frame.quads.is_empty());
        assert_eq!(
            build(&[clip(0, 0, 1, 1)], view()?, &mut Atlas::new()).map(|_| ()),
            Err(Error::Range)
        );
        assert_eq!(
            build(&[ExecItem::PopClip], view()?, &mut Atlas::new()).map(|_| ()),
            Err(Error::Range)
        );
        Ok(())
    }

    /// A compaction in the middle of a list: the draw before it is a batch of its
    /// own, closed before the store is replaced, and the moved mask is uploaded
    /// again before the draw after it. Small enough for Miri.
    #[test]
    fn a_compaction_closes_the_open_batch() -> Result<(), Error> {
        let mask = |id: u32| ExecItem::UploadMask {
            id,
            columns: 512,
            rows: 512,
            coverage: vec![1; 262_144],
        };
        let draw = |id: u32| ExecItem::DrawMask {
            id,
            x: 0,
            y: 0,
            colour: 0xffff_ffff,
        };
        let items = [
            mask(0),
            mask(1),
            mask(2),
            draw(1),
            ExecItem::FreeMask { id: 0 },
            mask(3),
            mask(4),
            draw(1),
        ];
        let frame = build(&items, view()?, &mut Atlas::new())?;
        let kinds: Vec<(&str, u32)> = frame
            .ops
            .iter()
            .map(|op| match op {
                Op::Atlas { capacity } => ("atlas", *capacity),
                Op::Upload { offset, .. } => ("upload", *offset),
                Op::Draw { first, .. } => ("draw", *first),
            })
            .collect();
        assert_eq!(
            kinds,
            vec![
                ("atlas", 1 << 20),
                ("upload", 0),
                ("upload", 262_144),
                ("upload", 524_288),
                ("upload", 786_432),
                ("draw", 0),
                ("atlas", 2 << 20),
                ("upload", 0),
                ("upload", 262_144),
                ("upload", 524_288),
                ("upload", 786_432),
                ("draw", 1),
            ]
        );
        assert_eq!(frame.quads.get(1).map(|q| q.offset), Some(0));
        Ok(())
    }

    #[test]
    fn masks_upload_then_draw_and_unknown_ids_fail() -> Result<(), Error> {
        let items = [
            ExecItem::UploadMask {
                id: 4,
                columns: 2,
                rows: 1,
                coverage: vec![10, 20],
            },
            ExecItem::DrawMask {
                id: 4,
                x: 3,
                y: 1,
                colour: 0xffff_ffff,
            },
        ];
        let frame = build(&items, view()?, &mut Atlas::new())?;
        assert_eq!(frame.bytes, vec![10, 20, 0, 0]);
        assert!(matches!(
            frame.ops.as_slice(),
            [
                Op::Atlas { .. },
                Op::Upload {
                    offset: 0,
                    start: 0,
                    len: 4
                },
                Op::Draw { count: 1, .. }
            ]
        ));
        assert_eq!(
            frame.quads.first().map(|q| (q.origin_x, q.columns)),
            Some((3, 2))
        );
        let unknown = [ExecItem::DrawMask {
            id: 5,
            x: 0,
            y: 0,
            colour: 0,
        }];
        assert_eq!(
            build(&unknown, view()?, &mut Atlas::new()).map(|_| ()),
            Err(Error::Range)
        );
        Ok(())
    }
}

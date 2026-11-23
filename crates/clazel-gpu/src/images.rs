//! The image store: where each live image's pixels live on the GPU (phase-6.md item
//! 6.12).
//!
//! # Modelling choices
//!
//! - **One linear store, as the glyph atlas is** ([`crate::atlas`]): a GPU buffer of
//!   bytes, and an image is `width × height × 4` bytes of premultiplied RGBA8 at an
//!   offset in it, rows from the top. This is the listed choice for "per-image
//!   textures, or an atlas": one store for every image, so draws of any image share a
//!   batch, and the fragment shader does the filtering itself (nearest or bilinear,
//!   `shaders/quad.frag`) from words it reads, with no sampler object, no texture
//!   object and no new foreign call in `clazel-sys` (which would need an audit). The
//!   cost is that the shader does a texture unit's work in 32-bit arithmetic, and that
//!   one buffer must hold the live images (below).
//! - **A bump allocator, compacted when full**, exactly as the atlas: an upload takes
//!   the bytes after the last one, a free only forgets the image, and when an upload
//!   does not fit every live image is moved to the start of a new, larger store. So
//!   an upload never overwrites pixels an earlier draw of the same frame reads.
//! - **Slots are `width × height × 4` bytes**, always whole words, so the copies the
//!   backends make (Metal's blits need multiples of 4) need no padding.
//! - **Capacity**: a power of two from [`MIN_CAPACITY`] (1 MiB) to [`MAX_CAPACITY`]
//!   (512 MiB, twice `clazel_displaylist::spec::MAX_IMAGE_BYTES`). The validator keeps
//!   at most 2^28 bytes of images live, counting the upload being validated, so a
//!   compaction always fits; if it did not (only if that guarantee were broken) the
//!   upload is [`Error::ImagesFull`] and the process ends. **A driver may refuse a
//!   buffer this large** (a storage buffer's range limit is the device's; lavapipe's
//!   has varied between Mesa versions): the backend's error then ends the process, as
//!   any backend failure does. Nothing here measured a store above 64 MiB.
//! - **A copy of each live image's pixels stays on the CPU**, shared with the frame
//!   that uploads it ([`Arc`]), so a compaction can upload it again. The GPU buffer is
//!   never read back. At most 2^28 bytes.
//! - **A hostile renderer can make its own GPU process slow**: uploading and freeing
//!   near the limit forces a compaction, which copies up to 2^28 bytes, per upload.

use std::sync::Arc;

use crate::Error;

/// The smallest store, in bytes.
pub const MIN_CAPACITY: u32 = 1 << 20;

/// The largest store, in bytes: twice `clazel_displaylist::spec::MAX_IMAGE_BYTES`.
pub const MAX_CAPACITY: u32 = 1 << 29;

/// How many ids there are: `clazel_displaylist::spec::MAX_IMAGES`.
pub const MAX_IMAGES: usize = 65_536;

/// A live image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// Its first byte in the store.
    pub offset: u32,
    /// Its width in pixels.
    pub width: u16,
    /// Its height in pixels.
    pub height: u16,
    /// Its pixels, `width × height × 4` bytes, kept for compaction.
    pub pixels: Arc<[u8]>,
}

impl Entry {
    /// Its size in bytes.
    pub fn size(&self) -> u32 {
        image_size(self.width, self.height)
    }
}

/// `width × height × 4`, saturating: at most 65,535² × 4 does not fit in `u32`, but
/// the validator allows sides of at most 2^14, which gives at most 2^30.
pub fn image_size(width: u16, height: u16) -> u32 {
    u32::from(width)
        .saturating_mul(u32::from(height))
        .saturating_mul(4)
}

/// What the backend must do to the store, in order with the draws.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Change {
    /// Write an image's pixels at its offset.
    Upload {
        /// The id, whose entry holds the bytes.
        id: u32,
    },
    /// Replace the store with a new, empty one of this many bytes; every live image
    /// follows as an [`Change::Upload`].
    Resize {
        /// The new capacity.
        capacity: u32,
    },
}

/// The images that live, and where.
#[derive(Debug)]
pub struct Images {
    /// The store's size, 0 until the first upload.
    capacity: u32,
    /// The first byte after the last placed image.
    top: u32,
    /// The bytes of all live images.
    live: u32,
    /// By id.
    table: Vec<Option<Entry>>,
}

impl Default for Images {
    fn default() -> Self {
        Images::new()
    }
}

impl Images {
    /// An empty store, with no buffer yet.
    pub fn new() -> Images {
        Images {
            capacity: 0,
            top: 0,
            live: 0,
            table: Vec::new(),
        }
    }

    /// The store's size.
    pub fn capacity(&self) -> u32 {
        self.capacity
    }

    /// The first free byte.
    pub fn top(&self) -> u32 {
        self.top
    }

    /// The live image with this id.
    pub fn get(&self, id: u32) -> Option<&Entry> {
        self.table.get(usize::try_from(id).ok()?)?.as_ref()
    }

    /// Keep an image under `id`, appending to `changes` what the backend must do.
    /// The id must not be live, and `pixels` must hold `width × height × 4` bytes.
    pub fn upload(
        &mut self,
        id: u32,
        width: u16,
        height: u16,
        pixels: Arc<[u8]>,
        changes: &mut Vec<Change>,
    ) -> Result<(), Error> {
        let index = usize::try_from(id).map_err(|_| Error::Range)?;
        if index >= MAX_IMAGES || self.get(id).is_some() {
            return Err(Error::Range);
        }
        let size = image_size(width, height);
        if usize::try_from(size).ok() != Some(pixels.len()) || size == 0 {
            return Err(Error::Range);
        }
        if self.table.len() <= index {
            self.table.resize(index.saturating_add(1), None);
        }
        let offset = match place(self.capacity, self.top, size) {
            Some(offset) => offset,
            None => {
                self.compact(size, changes)?;
                place(self.capacity, self.top, size).ok_or(Error::ImagesFull)?
            }
        };
        self.top = offset.checked_add(size).ok_or(Error::ImagesFull)?;
        self.live = self.live.checked_add(size).ok_or(Error::ImagesFull)?;
        let slot = self.table.get_mut(index).ok_or(Error::Range)?;
        *slot = Some(Entry {
            offset,
            width,
            height,
            pixels,
        });
        changes.push(Change::Upload { id });
        Ok(())
    }

    /// Forget a live image. Its bytes are reclaimed at the next compaction.
    pub fn free(&mut self, id: u32) -> Result<(), Error> {
        let index = usize::try_from(id).map_err(|_| Error::Range)?;
        let slot = self.table.get_mut(index).ok_or(Error::Range)?;
        let entry = slot.take().ok_or(Error::Range)?;
        self.live = self.live.checked_sub(entry.size()).ok_or(Error::Range)?;
        Ok(())
    }

    /// Move every live image to the start of a new store with room for `need` more
    /// bytes.
    fn compact(&mut self, need: u32, changes: &mut Vec<Change>) -> Result<(), Error> {
        let total = self.live.checked_add(need).ok_or(Error::ImagesFull)?;
        let capacity = grown_capacity(self.capacity, total).ok_or(Error::ImagesFull)?;
        changes.push(Change::Resize { capacity });
        let mut offset: u32 = 0;
        for (index, slot) in self.table.iter_mut().enumerate() {
            if let Some(entry) = slot {
                entry.offset = offset;
                offset = offset.checked_add(entry.size()).ok_or(Error::ImagesFull)?;
                let id = u32::try_from(index).map_err(|_| Error::Range)?;
                changes.push(Change::Upload { id });
            }
        }
        if offset != self.live {
            return Err(Error::Range);
        }
        self.capacity = capacity;
        self.top = offset;
        Ok(())
    }
}

/// Where an image of `size` bytes goes in a store of `capacity` bytes whose first
/// free byte is `top`, if it fits: `top` itself.
pub fn place(capacity: u32, top: u32, size: u32) -> Option<u32> {
    let end = top.checked_add(size)?;
    (end <= capacity).then_some(top)
}

/// The capacity after a compaction that must hold `total` bytes: the current one, at
/// least [`MIN_CAPACITY`], doubled until at least twice `total` or [`MAX_CAPACITY`].
/// `None` if even [`MAX_CAPACITY`] is too small.
pub fn grown_capacity(current: u32, total: u32) -> Option<u32> {
    if total > MAX_CAPACITY {
        return None;
    }
    let mut capacity = current.clamp(MIN_CAPACITY, MAX_CAPACITY);
    let want = total.saturating_mul(2);
    while capacity < want && capacity < MAX_CAPACITY {
        capacity = capacity.saturating_mul(2).min(MAX_CAPACITY);
    }
    (capacity >= total).then_some(capacity)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::{Change, Images, MAX_CAPACITY, MIN_CAPACITY, grown_capacity, image_size, place};
    use crate::Error;

    fn px(w: u16, h: u16) -> Arc<[u8]> {
        vec![
            7u8;
            usize::from(w)
                .saturating_mul(usize::from(h))
                .saturating_mul(4)
        ]
        .into()
    }

    #[test]
    fn the_first_upload_makes_a_store() -> Result<(), Error> {
        let mut images = Images::new();
        let mut changes = Vec::new();
        images.upload(3, 2, 2, px(2, 2), &mut changes)?;
        assert_eq!(
            changes,
            vec![
                Change::Resize {
                    capacity: MIN_CAPACITY
                },
                Change::Upload { id: 3 }
            ]
        );
        assert_eq!(images.top(), 16);
        assert_eq!(images.get(3).map(|e| e.offset), Some(0));
        // The next one follows it, with no resize.
        changes.clear();
        images.upload(0, 1, 1, px(1, 1), &mut changes)?;
        assert_eq!(changes, vec![Change::Upload { id: 0 }]);
        assert_eq!(images.get(0).map(|e| e.offset), Some(16));
        Ok(())
    }

    #[test]
    fn wrong_uploads_are_refused() -> Result<(), Error> {
        let mut images = Images::new();
        let mut changes = Vec::new();
        // Wrong length, an empty image, an id out of range, a live id.
        assert_eq!(
            images.upload(0, 2, 2, px(1, 1), &mut changes),
            Err(Error::Range)
        );
        assert_eq!(
            images.upload(0, 0, 2, Arc::from(Vec::new()), &mut changes),
            Err(Error::Range)
        );
        assert_eq!(
            images.upload(65_536, 1, 1, px(1, 1), &mut changes),
            Err(Error::Range)
        );
        images.upload(1, 1, 1, px(1, 1), &mut changes)?;
        assert_eq!(
            images.upload(1, 1, 1, px(1, 1), &mut changes),
            Err(Error::Range)
        );
        // Freeing what is not live.
        assert_eq!(images.free(2), Err(Error::Range));
        images.free(1)?;
        assert_eq!(images.free(1), Err(Error::Range));
        Ok(())
    }

    /// Freed and reused ids: the id may be uploaded again after a free, at a new
    /// place, and the freed bytes are reclaimed only by a compaction.
    #[test]
    fn a_freed_id_is_reused_at_a_new_place() -> Result<(), Error> {
        let mut images = Images::new();
        let mut changes = Vec::new();
        images.upload(5, 4, 4, px(4, 4), &mut changes)?;
        images.free(5)?;
        changes.clear();
        images.upload(5, 2, 2, px(2, 2), &mut changes)?;
        assert_eq!(changes, vec![Change::Upload { id: 5 }]);
        assert_eq!(images.get(5).map(|e| (e.offset, e.width)), Some((64, 2)));
        Ok(())
    }

    /// 512 × 512 images are 1 MiB each: the second does not fit the first store,
    /// and a free beforehand lets the compaction put the live one first.
    /// Ignored under Miri: 1 MiB of pixels in copies.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn a_full_store_is_compacted_in_id_order() -> Result<(), Error> {
        let mut images = Images::new();
        let mut changes = Vec::new();
        images.upload(2, 256, 256, px(256, 256), &mut changes)?; // 256 KiB
        images.upload(1, 512, 256, px(512, 256), &mut changes)?; // 512 KiB
        images.upload(0, 256, 256, px(256, 256), &mut changes)?; // 256 KiB: full
        assert_eq!(images.top(), MIN_CAPACITY);
        images.free(2)?;
        changes.clear();
        images.upload(3, 256, 256, px(256, 256), &mut changes)?;
        assert_eq!(
            changes,
            vec![
                Change::Resize {
                    capacity: 2 * MIN_CAPACITY
                },
                Change::Upload { id: 0 },
                Change::Upload { id: 1 },
                Change::Upload { id: 3 },
            ]
        );
        assert_eq!(images.get(0).map(|e| e.offset), Some(0));
        assert_eq!(images.get(1).map(|e| e.offset), Some(262_144));
        assert_eq!(images.get(3).map(|e| e.offset), Some(786_432));
        Ok(())
    }

    #[test]
    fn sizes_and_capacities() {
        assert_eq!(image_size(4096, 4096), 1 << 26);
        assert_eq!(image_size(16_384, 16_384), 1 << 30);
        assert_eq!(place(16, 8, 8), Some(8));
        assert_eq!(place(16, 8, 9), None);
        assert_eq!(place(16, u32::MAX, 2), None);
        assert_eq!(grown_capacity(0, 1), Some(MIN_CAPACITY));
        assert_eq!(grown_capacity(0, 1 << 28), Some(MAX_CAPACITY));
        assert_eq!(
            grown_capacity(MAX_CAPACITY, MAX_CAPACITY),
            Some(MAX_CAPACITY)
        );
        assert_eq!(grown_capacity(0, MAX_CAPACITY + 1), None);
        // Past what the validator allows live, the store is full: refused, with
        // no allocation (the store's own check, not the validator's).
        assert_eq!(grown_capacity(MIN_CAPACITY, u32::MAX), None);
    }
}

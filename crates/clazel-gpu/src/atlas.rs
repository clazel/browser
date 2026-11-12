//! The glyph atlas: where each live mask's coverage lives on the GPU.
//!
//! # Modelling choices
//!
//! - **One linear store, not a 2D texture.** The atlas is one GPU buffer of bytes,
//!   and a mask is `columns × rows` bytes at an offset in it, rows from the top.
//!   The fragment shader reads exactly one byte per pixel, at an index it computes
//!   in integers, so it needs no sampler, no filtering and no texture coordinates,
//!   and allocation is one-dimensional. The plan's "masks through a glyph atlas" is
//!   kept: every mask shares one store, so masks of every id draw in one batch.
//! - **A bump allocator, compacted when full.** An upload takes the bytes after the
//!   last one ([`Atlas::top`]); a free only forgets the mask. When an upload does
//!   not fit, every live mask is moved to the start, in id order, into a new
//!   buffer (the old one stays alive for draws already recorded). So no byte is
//!   written twice between compactions, and an upload never overwrites coverage an
//!   earlier draw of the same frame reads.
//! - **Slots are whole 4-byte words**: a mask's slot is its size rounded up to a
//!   multiple of 4 ([`slot_size`]), and uploads are padded with zeros to fill it,
//!   because Metal's buffer-to-buffer copies on macOS need offsets and sizes that
//!   are multiples of 4 (`copyFromBuffer:sourceOffset:toBuffer:destinationOffset:size:`),
//!   and Vulkan's `vkCmdCopyBuffer` is simplest so too.
//! - **Capacity**: a power of two from [`MIN_CAPACITY`] (1 MiB) to
//!   [`MAX_CAPACITY`] (128 MiB). The validator keeps at most 64 MiB of coverage
//!   live (`MAX_MASK_BYTES`) in at most 65,536 masks, so slots hold at most
//!   64 MiB + 3 × 65,536 bytes, which a compaction into `MAX_CAPACITY` always fits.
//!   A compaction grows the store until at least half of it is free, so a run of
//!   uploads after one costs no other. If it did not fit (only if the validator's
//!   guarantee were broken), the upload is
//!   [`Error::AtlasFull`](crate::Error::AtlasFull) and the process ends.
//! - **A copy of each live mask's coverage stays on the CPU**, at most 64 MiB, so
//!   that a compaction can upload it again. The GPU buffer is never read back.
//! - **A hostile renderer can make its own GPU process slow**: uploading and
//!   freeing near the limit forces a compaction, which copies up to 64 MiB, per
//!   upload. That only slows its own tab, which a large list can already do.

use crate::Error;

/// The smallest atlas, in bytes.
pub const MIN_CAPACITY: u32 = 1 << 20;

/// The largest atlas, in bytes: twice `clazel_displaylist::spec::MAX_MASK_BYTES`,
/// which leaves room for the slots' padding.
pub const MAX_CAPACITY: u32 = 1 << 27;

/// How many ids there are: `clazel_displaylist::spec::MAX_MASKS`.
pub const MAX_MASKS: usize = 65_536;

/// A live mask.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// Its first byte in the atlas.
    pub offset: u32,
    /// Its width in pixels.
    pub columns: u16,
    /// Its height in pixels.
    pub rows: u16,
    /// Its coverage, `columns × rows` bytes, kept for compaction.
    pub coverage: Vec<u8>,
}

impl Entry {
    /// Its slot's size in bytes: its size rounded up to a multiple of 4.
    pub fn size(&self) -> u32 {
        slot_size(self.columns, self.rows)
    }
}

/// `columns × rows`: at most 65,535² < 2^32, so it never overflows.
pub fn mask_size(columns: u16, rows: u16) -> u32 {
    u32::from(columns).saturating_mul(u32::from(rows))
}

/// A mask's slot: `columns × rows` rounded up to a multiple of 4, at most
/// 65,535² + 3 < 2^32.
pub fn slot_size(columns: u16, rows: u16) -> u32 {
    mask_size(columns, rows).saturating_add(3) & !3
}

/// What the backend must do to the atlas, in order with the draws.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Change {
    /// Write a mask's coverage at its offset.
    Upload {
        /// The id, whose entry holds the bytes.
        id: u32,
    },
    /// Replace the store with a new, empty one of this many bytes; every live mask
    /// follows as an [`Change::Upload`].
    Resize {
        /// The new capacity.
        capacity: u32,
    },
}

/// The masks that live, and where.
#[derive(Debug)]
pub struct Atlas {
    /// The store's size, 0 until the first upload.
    capacity: u32,
    /// The first byte after the last placed mask.
    top: u32,
    /// The bytes of all live masks.
    live: u32,
    /// By id.
    table: Vec<Option<Entry>>,
}

impl Default for Atlas {
    fn default() -> Self {
        Atlas::new()
    }
}

impl Atlas {
    /// An empty atlas, with no store yet.
    pub fn new() -> Atlas {
        Atlas {
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

    /// The live mask with this id.
    pub fn get(&self, id: u32) -> Option<&Entry> {
        self.table.get(usize::try_from(id).ok()?)?.as_ref()
    }

    /// Keep a mask under `id`, appending to `changes` what the backend must do.
    /// The id must not be live, and `coverage` must hold `columns × rows` bytes.
    pub fn upload(
        &mut self,
        id: u32,
        columns: u16,
        rows: u16,
        coverage: Vec<u8>,
        changes: &mut Vec<Change>,
    ) -> Result<(), Error> {
        let index = usize::try_from(id).map_err(|_| Error::Range)?;
        if index >= MAX_MASKS || self.get(id).is_some() {
            return Err(Error::Range);
        }
        let raw = mask_size(columns, rows);
        if usize::try_from(raw).ok() != Some(coverage.len()) || raw == 0 {
            return Err(Error::Range);
        }
        let size = slot_size(columns, rows);
        if self.table.len() <= index {
            self.table.resize(index.saturating_add(1), None);
        }
        let offset = match place(self.capacity, self.top, size) {
            Some(offset) => offset,
            None => {
                self.compact(size, changes)?;
                place(self.capacity, self.top, size).ok_or(Error::AtlasFull)?
            }
        };
        self.top = offset.checked_add(size).ok_or(Error::AtlasFull)?;
        self.live = self.live.checked_add(size).ok_or(Error::AtlasFull)?;
        let slot = self.table.get_mut(index).ok_or(Error::Range)?;
        *slot = Some(Entry {
            offset,
            columns,
            rows,
            coverage,
        });
        changes.push(Change::Upload { id });
        Ok(())
    }

    /// Forget a live mask. Its bytes are reclaimed at the next compaction.
    pub fn free(&mut self, id: u32) -> Result<(), Error> {
        let index = usize::try_from(id).map_err(|_| Error::Range)?;
        let slot = self.table.get_mut(index).ok_or(Error::Range)?;
        let entry = slot.take().ok_or(Error::Range)?;
        self.live = self.live.checked_sub(entry.size()).ok_or(Error::Range)?;
        Ok(())
    }

    /// Move every live mask to the start of a new store with room for `need` more
    /// bytes.
    fn compact(&mut self, need: u32, changes: &mut Vec<Change>) -> Result<(), Error> {
        let total = self.live.checked_add(need).ok_or(Error::AtlasFull)?;
        let capacity = grown_capacity(self.capacity, total).ok_or(Error::AtlasFull)?;
        changes.push(Change::Resize { capacity });
        let mut offset: u32 = 0;
        for (index, slot) in self.table.iter_mut().enumerate() {
            if let Some(entry) = slot {
                entry.offset = offset;
                offset = offset.checked_add(entry.size()).ok_or(Error::AtlasFull)?;
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

#[cfg(kani)]
impl Atlas {
    /// An atlas in any state, for a harness to constrain.
    pub(crate) fn for_proof(
        capacity: u32,
        top: u32,
        live: u32,
        table: Vec<Option<Entry>>,
    ) -> Atlas {
        Atlas {
            capacity,
            top,
            live,
            table,
        }
    }

    /// The table, for a harness.
    pub(crate) fn table_for_proof(&self) -> &[Option<Entry>] {
        &self.table
    }

    /// The live bytes, for a harness.
    pub(crate) fn live_for_proof(&self) -> u32 {
        self.live
    }
}

/// Where a mask of `size` bytes goes in a store of `capacity` bytes whose first
/// free byte is `top`, if it fits: `top` itself.
pub fn place(capacity: u32, top: u32, size: u32) -> Option<u32> {
    let end = top.checked_add(size)?;
    (end <= capacity).then_some(top)
}

/// The capacity after a compaction that must hold `total` bytes: the current one,
/// at least [`MIN_CAPACITY`], doubled until at least twice `total` or
/// [`MAX_CAPACITY`]. `None` if even [`MAX_CAPACITY`] is too small.
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

/// The atlas index of the pixel `(column, row)` of a mask at `offset` that is
/// `columns` wide: what the fragment shader computes. `None` if it would overflow.
pub fn texel_index(offset: u32, columns: u32, column: u32, row: u32) -> Option<u32> {
    offset
        .checked_add(row.checked_mul(columns)?)?
        .checked_add(column)
}

#[cfg(test)]
mod tests {
    use super::{Atlas, Change, MAX_CAPACITY, MIN_CAPACITY, grown_capacity, place, texel_index};
    use crate::Error;

    #[test]
    fn the_first_upload_makes_a_store() -> Result<(), Error> {
        let mut atlas = Atlas::new();
        let mut changes = Vec::new();
        atlas.upload(3, 2, 2, vec![1, 2, 3, 4], &mut changes)?;
        assert_eq!(
            changes,
            vec![
                Change::Resize {
                    capacity: MIN_CAPACITY
                },
                Change::Upload { id: 3 },
            ]
        );
        assert_eq!(atlas.get(3).map(|e| e.offset), Some(0));
        assert_eq!(atlas.top(), 4);
        atlas.upload(4, 3, 1, vec![1, 2, 3], &mut changes)?;
        assert_eq!(atlas.get(4).map(|e| (e.offset, e.size())), Some((4, 4)));
        assert_eq!(atlas.top(), 8);
        Ok(())
    }

    #[test]
    fn a_live_id_and_a_wrong_length_are_refused() -> Result<(), Error> {
        let mut atlas = Atlas::new();
        let mut changes = Vec::new();
        atlas.upload(0, 1, 1, vec![9], &mut changes)?;
        assert_eq!(
            atlas.upload(0, 1, 1, vec![9], &mut changes),
            Err(Error::Range)
        );
        assert_eq!(
            atlas.upload(1, 2, 1, vec![9], &mut changes),
            Err(Error::Range)
        );
        assert_eq!(
            atlas.upload(65_536, 1, 1, vec![9], &mut changes),
            Err(Error::Range)
        );
        assert_eq!(atlas.free(1), Err(Error::Range));
        atlas.free(0)?;
        assert_eq!(atlas.free(0), Err(Error::Range));
        Ok(())
    }

    #[test]
    fn a_full_store_is_compacted_in_id_order() -> Result<(), Error> {
        let mut atlas = Atlas::new();
        let mut changes = Vec::new();
        // Fill 1 MiB with four 256 KiB masks (512 × 512), free two, add one more.
        for id in 0..4 {
            atlas.upload(id, 512, 512, vec![id as u8; 262_144], &mut changes)?;
        }
        assert_eq!(atlas.capacity(), MIN_CAPACITY);
        atlas.free(0)?;
        atlas.free(2)?;
        changes.clear();
        atlas.upload(9, 512, 512, vec![9; 262_144], &mut changes)?;
        assert_eq!(
            changes,
            vec![
                Change::Resize {
                    capacity: 2 * MIN_CAPACITY
                },
                Change::Upload { id: 1 },
                Change::Upload { id: 3 },
                Change::Upload { id: 9 },
            ]
        );
        assert_eq!(atlas.get(1).map(|e| e.offset), Some(0));
        assert_eq!(atlas.get(3).map(|e| e.offset), Some(262_144));
        assert_eq!(atlas.get(9).map(|e| e.offset), Some(524_288));
        Ok(())
    }

    #[test]
    fn capacity_growth() {
        assert_eq!(grown_capacity(0, 1), Some(MIN_CAPACITY));
        assert_eq!(
            grown_capacity(MIN_CAPACITY, MIN_CAPACITY),
            Some(2 * MIN_CAPACITY)
        );
        assert_eq!(grown_capacity(0, MAX_CAPACITY), Some(MAX_CAPACITY));
        assert_eq!(grown_capacity(0, MAX_CAPACITY + 1), None);
        assert_eq!(grown_capacity(u32::MAX, 5), Some(MAX_CAPACITY));
        assert_eq!(super::slot_size(3, 3), 12);
        assert_eq!(super::slot_size(u16::MAX, u16::MAX), 4_294_836_228);
    }

    #[test]
    fn placing_and_indexing() {
        assert_eq!(place(10, 4, 6), Some(4));
        assert_eq!(place(10, 4, 7), None);
        assert_eq!(place(u32::MAX, u32::MAX, 1), None);
        assert_eq!(texel_index(10, 3, 2, 1), Some(15));
        assert_eq!(texel_index(u32::MAX, 3, 2, 1), None);
    }
}

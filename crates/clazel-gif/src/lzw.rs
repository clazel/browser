//! GIF's variable-code-size LZW decoder, one input byte at a time.
//!
//! GIF89a, Appendix F ("Image Data and Compression"): the image data is a
//! sequence of codes of 1 more bit than the *minimum code size* (2 to 8 in
//! practice), packed least significant bit first. The codes
//! `0 .. 2^min` are the colour indexes (the roots of the table), `2^min` is
//! the *clear code* and `2^min + 1` the *end-of-information code*; the
//! other codes are added to the table as the data is decoded. The code size
//! grows by one bit each time the table fills its current size, up to 12
//! bits.
//!
//! # Listed choices
//!
//! - **Full table, deferred clear.** GIF89a Appendix F says the encoder
//!   should emit a clear code when the table is full, and it does not say
//!   what a decoder does if it does not ("the decoder ... should ... clear
//!   the table"-style wording is about the clear code itself). Browsers keep
//!   decoding with the table as it is, 4096 entries and 12-bit codes, adding
//!   nothing, until a clear code comes (the "deferred clear" of Wuffs, libgif
//!   and `weezl`). So do we: when `next` has reached the table's size an
//!   entry is not added, and the code size stays at its maximum.
//! - **The first code after a clear** must be a root (`< 2^min`); any other
//!   is an error (the table is empty, so no other code has a meaning).
//! - **A code above the next free one** is an error. The next free code
//!   itself is the "K w K" case: the string of the previous code followed by
//!   its own first byte.
//! - **Minimum code sizes** 2 to 8 only (`MAX_MIN`); 8 is the most a colour
//!   index of 256 colours needs, 1 and 0 cannot hold a clear and end code
//!   with room to grow.
//! - **Nothing about the table's contents is trusted.** Every table access
//!   is checked, and a chain of prefixes is followed at most `TABLE_LEN`
//!   steps, so the decoder is safe over *any* contents of its three arrays
//!   (the Kani harness `lzw_any` says so); a table whose chains do not end
//!   at a root gives an error, never a panic. Correctness of the pixels,
//!   which does depend on the table being the one the decoder built, is the
//!   differential test's.
//!
//! The decoder is a state machine fed one byte at a time ([`Lzw::feed`]);
//! its output, colour indexes, goes to a sink, so no output buffer is needed
//! here. The three arrays live in the caller's work buffer ([`Tables`]).

/// Bits of the largest code (GIF89a: 12).
///
/// Under Kani the harnesses of `step` run with a 4-bit table (16 entries),
/// because a symbolic 4096-entry table and the chain walk's 4096 iterations
/// do not fit the model checker; the code is the same code with another
/// constant (README, "What Kani covers").
pub(crate) const TABLE_BITS: u8 = if cfg!(kani) { 4 } else { 12 };

/// Entries of the table: `2^TABLE_BITS`.
pub(crate) const TABLE_LEN: usize = if cfg!(kani) { 16 } else { 4096 };

/// The largest minimum code size accepted (8, or less under Kani where the
/// table is smaller, so that the roots, clear and end fit with room).
pub(crate) const MAX_MIN: u8 = if cfg!(kani) { 3 } else { 8 };

/// The smallest minimum code size accepted.
pub(crate) const MIN_MIN: u8 = 2;

/// `prev` when there is no previous code (after a clear).
pub(crate) const NONE: u16 = u16::MAX;

/// What `feed` says of a byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Fed {
    /// The byte was used; more may follow.
    More,
    /// The end-of-information code was read.
    End,
    /// The sink wanted no more indexes (the frame is full).
    Full,
}

/// The decoder's three arrays, cut from the work buffer: `prefix` holds
/// `TABLE_LEN` little-endian `u16`, `suffix` and `stack` `TABLE_LEN` bytes.
#[derive(Debug)]
pub(crate) struct Tables<'a> {
    /// Per code, the code of the string without its last byte.
    pub prefix: &'a mut [u8],
    /// Per code, the string's last byte.
    pub suffix: &'a mut [u8],
    /// Where a string is spelt out, last byte first.
    pub stack: &'a mut [u8],
}

impl Tables<'_> {
    fn prefix_of(&self, code: u16) -> Option<u16> {
        let at = usize::from(code).checked_mul(2)?;
        let end = at.checked_add(2)?;
        let b = self.prefix.get(at..end)?;
        Some(u16::from_le_bytes([*b.first()?, *b.get(1)?]))
    }

    fn set_prefix(&mut self, code: usize, value: u16) -> Option<()> {
        let at = code.checked_mul(2)?;
        let end = at.checked_add(2)?;
        self.prefix
            .get_mut(at..end)?
            .copy_from_slice(&value.to_le_bytes());
        Some(())
    }
}

/// The LZW decoder's scalar state. The arrays are in [`Tables`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Lzw {
    /// The minimum code size, `MIN_MIN..=MAX_MIN`.
    pub(crate) min_size: u8,
    /// Bits of the code being read, `min_size + 1 ..= TABLE_BITS`.
    pub(crate) code_size: u8,
    /// The next free code.
    pub(crate) next: u16,
    /// The previous code, or [`NONE`] after a clear.
    pub(crate) prev: u16,
    /// The first byte of the previous code's string.
    pub(crate) first: u8,
    /// Bits read but not yet used, least significant first.
    pub(crate) acc: u32,
    /// How many bits of `acc` are valid.
    pub(crate) nacc: u8,
}

impl Lzw {
    /// A decoder at the start of image data with this minimum code size,
    /// `None` outside `MIN_MIN..=MAX_MIN`.
    pub(crate) fn new(min_size: u8) -> Option<Lzw> {
        if !(MIN_MIN..=MAX_MIN).contains(&min_size) {
            return None;
        }
        let mut lzw = Lzw {
            min_size,
            code_size: min_size.checked_add(1)?,
            next: 0,
            prev: NONE,
            first: 0,
            acc: 0,
            nacc: 0,
        };
        lzw.reset();
        Some(lzw)
    }

    /// A placeholder state for a decoder that is not in image data (it
    /// satisfies [`Lzw::inv`]).
    pub(crate) fn idle() -> Lzw {
        Lzw {
            min_size: MIN_MIN,
            code_size: MIN_MIN.saturating_add(1),
            next: 6,
            prev: NONE,
            first: 0,
            acc: 0,
            nacc: 0,
        }
    }

    /// The clear code, `2^min_size` (0 if `min_size` is out of range).
    fn clear(&self) -> u16 {
        1u16.checked_shl(u32::from(self.min_size)).unwrap_or(0)
    }

    /// The end-of-information code, `2^min_size + 1`.
    fn end(&self) -> u16 {
        self.clear().saturating_add(1)
    }

    /// Back to the empty table (the effect of a clear code). The bits
    /// already read stay.
    fn reset(&mut self) {
        self.code_size = self.min_size.saturating_add(1);
        self.next = self.end().saturating_add(1);
        self.prev = NONE;
    }

    /// `2^bits` as a `u32` (0 past 31 bits, which no state has).
    fn pow2(bits: u8) -> u32 {
        1u32.checked_shl(u32::from(bits)).unwrap_or(0)
    }

    /// The invariant of the scalar state: every field in its range, so that
    /// codes, sizes and shifts are what the algorithm expects. It says
    /// nothing of the arrays' contents (none of them is trusted).
    pub(crate) fn inv(&self) -> bool {
        if !(MIN_MIN..=MAX_MIN).contains(&self.min_size) {
            return false;
        }
        let clear = self.clear();
        let end = self.end();
        let size = Self::pow2(self.code_size);
        let next = u32::from(self.next);
        self.code_size > self.min_size
            && self.code_size <= TABLE_BITS
            // Entries are `end + 1 ..= TABLE_LEN`, and the code size always
            // has room for the next free code (growing when it fills).
            && self.next > end
            && usize::from(self.next) <= TABLE_LEN
            && next <= size
            && (self.code_size == TABLE_BITS || next < size)
            && (self.prev == NONE
                || (self.prev < self.next && self.prev != clear && self.prev != end))
            && self.nacc < self.code_size
            && u64::from(self.acc) < u64::from(Self::pow2(self.nacc))
    }

    /// Uses one byte of image data, giving each colour index to `sink`,
    /// which says whether it wants more (`false`: the frame is full).
    /// `Ok(Fed::More)` consumed the byte entirely.
    ///
    /// Keeps [`Lzw::inv`] on `Ok(Fed::More)`, and does not panic or touch
    /// anything but `tables` and `self`, whatever `tables` holds.
    ///
    /// STUB: the statement above is what the harness `lzw_any` checks; the
    /// implementation follows in a later commit.
    pub(crate) fn feed(
        &mut self,
        _byte: u8,
        _tables: &mut Tables<'_>,
        _sink: &mut impl FnMut(u8) -> bool,
    ) -> Result<Fed, &'static str> {
        Err("not implemented")
    }
}

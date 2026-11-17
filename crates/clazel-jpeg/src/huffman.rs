//! Huffman tables: construction from a DHT segment and decoding, one bit
//! at a time.
//!
//! T.81 Annex C builds the code from the numbers of codes of each length
//! (`BITS`) and the symbols in order of increasing code length (`HUFFVAL`):
//! Figure C.1 (`Generate_size_table`), Figure C.2 (`Generate_code_table`).
//! Annex F.2.2.3 decodes it: Figure F.15 (`Generate_decoding_tables`, the
//! arrays `MINCODE`, `MAXCODE` and `VALPTR`) and Figure F.16 (`DECODE`),
//! which takes one bit at a time and so can stop between any two bits when
//! the input chunk ends.
//!
//! Listed choices: the code of all 1-bits is accepted (T.81 C.2 reserves it,
//! libjpeg-turbo accepts it); a DC table's symbols must be at most 15
//! (the largest `SSSS` libjpeg-turbo accepts; the baseline maximum is 11);
//! an AC table accepts every byte as a symbol.

/// The longest code, in bits (T.81 C.2: lengths 1 to 16).
pub(crate) const MAX_LEN: u8 = 16;

/// The most symbols a table holds (T.81 B.2.4.2: `Vij`, at most 256).
pub(crate) const MAX_SYMBOLS: usize = 256;

/// A table that passed construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Table {
    /// `HUFFVAL`, the first `total` entries.
    values: [u8; MAX_SYMBOLS],
    /// How many symbols the table has.
    total: u16,
    /// Figure F.15's `MINCODE`, indexed by code length 1 to 16.
    mincode: [u16; 17],
    /// Figure F.15's `MAXCODE`, indexed by length; -1 when no code has that
    /// length.
    maxcode: [i32; 17],
    /// Figure F.15's `VALPTR`: index in `values` of the first code of that
    /// length.
    valptr: [u16; 17],
}

/// What one more bit does to a code being read (Figure F.16).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Next {
    /// The code so far is a prefix; keep it and read another bit.
    More {
        /// The bits so far.
        code: u16,
        /// How many.
        len: u8,
    },
    /// The code is complete: this symbol.
    Value(u8),
    /// No code of any length matches.
    Bad,
}

impl Table {
    /// Figures C.1, C.2 and F.15 over `counts[l - 1]` codes of length `l`
    /// and the `symbols`, which must be exactly `sum(counts)` of them.
    /// `dc` tables take symbols of at most 15 only (listed choice).
    pub(crate) fn build(
        counts: &[u8; 16],
        symbols: &[u8],
        dc: bool,
    ) -> Result<Table, &'static str> {
        let total = counts
            .iter()
            .try_fold(0u16, |t, &c| t.checked_add(u16::from(c)))
            .ok_or("Huffman symbol count overflows")?;
        if usize::from(total) > MAX_SYMBOLS || usize::from(total) != symbols.len() {
            return Err("Huffman table: wrong number of symbols");
        }
        let mut values = [0u8; MAX_SYMBOLS];
        for (slot, &s) in values.iter_mut().zip(symbols) {
            if dc && s > 15 {
                return Err("DC Huffman table: symbol over 15");
            }
            *slot = s;
        }
        let mut table = Table {
            values,
            total,
            mincode: [0; 17],
            maxcode: [-1; 17],
            valptr: [0; 17],
        };
        // Figure C.2: codes are assigned in increasing order, and the code
        // is shifted left once for each increase of the length.
        let mut code: u32 = 0;
        let mut k: u16 = 0;
        for (len, &n) in (1u32..=16).zip(counts) {
            let l = usize::try_from(len).map_err(|_| "length")?;
            if let Some(v) = table.valptr.get_mut(l) {
                *v = k;
            }
            if n > 0
                && let Some(m) = table.mincode.get_mut(l)
            {
                *m = u16::try_from(code).map_err(|_| "Huffman code over 16 bits")?;
            }
            for _ in 0..n {
                // The code must fit in `len` bits, or the lengths promise
                // more codes than there are.
                if code >= 1u32.checked_shl(len).ok_or("length")? {
                    return Err("Huffman table: over-subscribed code lengths");
                }
                code = code.checked_add(1).ok_or("code")?;
                k = k.checked_add(1).ok_or("count")?;
            }
            if n > 0
                && let Some(m) = table.maxcode.get_mut(l)
            {
                *m = i32::try_from(code.checked_sub(1).ok_or("code")?).map_err(|_| "code")?;
            }
            code = code.checked_shl(1).ok_or("code")?;
        }
        Ok(table)
    }

    #[cfg(any(test, kani))]
    /// The invariant of a built table, what the harnesses assume of any
    /// table that passed [`Table::build`]: `total` symbols, and for every
    /// length with codes, the indexes `valptr + (code - mincode)` of its
    /// codes are below `total`.
    pub(crate) fn inv(&self) -> bool {
        if usize::from(self.total) > MAX_SYMBOLS {
            return false;
        }
        (1usize..=16).all(|l| {
            let (Some(&max), Some(&min), Some(&ptr)) =
                (self.maxcode.get(l), self.mincode.get(l), self.valptr.get(l))
            else {
                return false;
            };
            if max < 0 {
                return true;
            }
            // The last code of this length is the largest index.
            let span = i64::from(max).saturating_sub(i64::from(min));
            span >= 0 && i64::from(ptr).saturating_add(span) < i64::from(self.total)
        })
    }

    /// Figure F.16 (`DECODE`), one bit: appends `bit` to the code of `len`
    /// bits read so far and compares it with `MAXCODE`. Start with
    /// `code = 0` and `len = 0`.
    pub(crate) fn step(&self, code: u16, len: u8, bit: u8) -> Next {
        // F.16: `I = I + 1; CODE = (CODE << 1) + NEXTBIT`.
        let Some(l) = len.checked_add(1).filter(|&l| l <= MAX_LEN) else {
            return Next::Bad;
        };
        let Some(c) = code
            .checked_mul(2)
            .and_then(|c| c.checked_add(u16::from(bit & 1)))
        else {
            return Next::Bad;
        };
        let at = usize::from(l);
        let (Some(&max), Some(&min), Some(&ptr)) = (
            self.maxcode.get(at),
            self.mincode.get(at),
            self.valptr.get(at),
        ) else {
            return Next::Bad;
        };
        // F.16: `IF CODE > MAXCODE(I) GO TO the next bit`.
        if i32::from(c) > max {
            return if l == MAX_LEN {
                Next::Bad
            } else {
                Next::More { code: c, len: l }
            };
        }
        // F.16: `J = VALPTR(I); J = J + CODE - MINCODE(I); VALUE = HUFFVAL(J)`.
        let Some(j) = c
            .checked_sub(min)
            .and_then(|d| d.checked_add(ptr))
            .filter(|&j| j < self.total)
        else {
            return Next::Bad;
        };
        match self.values.get(usize::from(j)) {
            Some(&v) => Next::Value(v),
            None => Next::Bad,
        }
    }

    /// The symbols, for the harnesses.
    #[cfg(kani)]
    pub(crate) fn symbols(&self) -> &[u8] {
        self.values.get(..usize::from(self.total)).unwrap_or(&[])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// T.81 K.3.3.1's DC luminance table (Table K.3).
    const DC_LUM_COUNTS: [u8; 16] = [0, 1, 5, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0];
    const DC_LUM_SYMS: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    /// `counts` with `n` codes of length `len`, others none.
    fn counts(of: &[(usize, u8)]) -> [u8; 16] {
        let mut c = [0u8; 16];
        for &(len, n) in of {
            if let Some(slot) = c.get_mut(len.saturating_sub(1)) {
                *slot = n;
            }
        }
        c
    }

    fn decode(t: &Table, bits: &[u8]) -> Next {
        let (mut code, mut len) = (0, 0);
        let mut last = Next::Bad;
        for &b in bits {
            last = t.step(code, len, b);
            if let Next::More { code: c, len: l } = last {
                code = c;
                len = l;
            } else {
                break;
            }
        }
        last
    }

    #[test]
    fn k3_codes() -> Result<(), &'static str> {
        let t = Table::build(&DC_LUM_COUNTS, &DC_LUM_SYMS, true)?;
        assert!(t.inv());
        // Table K.3: category 0 is `00`, 1 is `010`, 2 is `011`, 3 is
        // `100`, 4 is `101`, 5 is `110`, 6 is `1110`, 11 is `111111110`.
        assert_eq!(decode(&t, &[0, 0]), Next::Value(0));
        assert_eq!(decode(&t, &[0, 1, 0]), Next::Value(1));
        assert_eq!(decode(&t, &[1, 1, 0]), Next::Value(5));
        assert_eq!(decode(&t, &[1, 1, 1, 0]), Next::Value(6));
        assert_eq!(decode(&t, &[1, 1, 1, 1, 1, 1, 1, 1, 0]), Next::Value(11));
        // A prefix is not a symbol yet.
        assert!(matches!(decode(&t, &[1, 1, 1]), Next::More { .. }));
        Ok(())
    }

    #[test]
    fn refuses_bad_tables() -> Result<(), &'static str> {
        // Three codes of length 1: over-subscribed.
        assert!(Table::build(&counts(&[(1, 3)]), &[0, 1, 2], false).is_err());
        // Symbol count disagrees with the counts.
        assert!(Table::build(&DC_LUM_COUNTS, &[0; 11], true).is_err());
        // A DC symbol over 15.
        let one = counts(&[(1, 1)]);
        assert!(Table::build(&one, &[16], true).is_err());
        assert!(Table::build(&one, &[16], false).is_ok());
        // Two codes of length 1 are complete (0 and 1); the all-ones code
        // is accepted.
        let t = Table::build(&counts(&[(1, 2)]), &[7, 9], false)?;
        assert_eq!(decode(&t, &[1]), Next::Value(9));
        // 257 symbols.
        assert!(Table::build(&counts(&[(16, 255), (15, 2)]), &[0; 257], false).is_err());
        // 256 symbols of length 16 are over-subscribed (only 2^16 codes
        // exist, but 256 fit: this one is fine).
        assert!(Table::build(&counts(&[(16, 255)]), &[0; 255], false).is_ok());
        Ok(())
    }

    #[test]
    fn unused_codes_are_bad() -> Result<(), &'static str> {
        // One code of length 1 (`0`): the bit 1 leads nowhere within 16.
        let t = Table::build(&counts(&[(1, 1)]), &[42], false)?;
        assert_eq!(decode(&t, &[0]), Next::Value(42));
        let mut last = Next::More { code: 0, len: 0 };
        let (mut code, mut len) = (0, 0);
        for _ in 0..16 {
            last = t.step(code, len, 1);
            if let Next::More { code: c, len: l } = last {
                code = c;
                len = l;
            }
        }
        assert_eq!(last, Next::Bad);
        Ok(())
    }
}

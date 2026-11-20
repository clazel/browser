//! Canonical prefix codes: construction from code lengths and decoding one
//! symbol at a time, without tables (RFC 9649 section 3.7).
//!
//! RFC 9649 section 3.7.1: "Most of the data is coded using a canonical
//! prefix code". The code of a symbol is its position among the symbols of
//! its length, sorted by symbol value, after all shorter codes; the first
//! bit read from the stream is the **most** significant bit of the code (the
//! DEFLATE convention, which libwebp's tables implement by reversing the
//! code). The decoder here is the classic one over per-length counts (as
//! zlib's `puff.c`): no table, so a code costs `2 * (alphabet + 16)` bytes
//! and decoding takes at most 15 steps.
//!
//! Listed choices, from libwebp's `VP8LBuildHuffmanTable` where the RFC says
//! less:
//! - a code with **all lengths zero** is an error (section 3.7.2.1.1's note
//!   says an empty code is coded as a single symbol 0, so a zero-symbol code
//!   is never valid);
//! - a code with **exactly one symbol** takes zero bits, whatever length
//!   (1 to 15) its entry has (section 3.7.2.1: "even when no bits are
//!   consumed when that single leaf node tree is used");
//! - every other code must be **complete**: the lengths fill the code space
//!   exactly (section 3.7.2.1: "The described tree must be a complete
//!   binary tree"); over-subscribed and incomplete codes are errors.
//!
//! A code is stored as `counts` (16 little-endian `u16`: the number of
//! symbols of each length 1 to 15, and entry 0 is 1 for the one-symbol code
//! and 0 otherwise) and `symbols` (little-endian `u16`, sorted by length and
//! then symbol value).

/// The longest code length: RFC 9649 section 3.7.2.1.2 ("Values [1..15]").
pub(crate) const MAX_LEN: u8 = 15;

/// Reads the `i`th little-endian `u16` of `b` (0 if out of range).
pub(crate) fn get16(b: &[u8], i: usize) -> u16 {
    i.checked_mul(2)
        .and_then(|o| b.get(o..o.checked_add(2)?))
        .and_then(|s| <[u8; 2]>::try_from(s).ok())
        .map_or(0, u16::from_le_bytes)
}

/// Writes the `i`th little-endian `u16` of `b`; false if out of range.
pub(crate) fn set16(b: &mut [u8], i: usize, v: u16) -> bool {
    let slot = i
        .checked_mul(2)
        .and_then(|o| b.get_mut(o..o.checked_add(2)?));
    match slot {
        Some(s) => {
            s.copy_from_slice(&v.to_le_bytes());
            true
        }
        None => false,
    }
}

/// Builds the code for `lens` (one length per symbol of the alphabet, each
/// 0 to 15) into `counts` (at least 32 bytes) and `symbols` (at least
/// `2 * lens.len()` bytes).
pub(crate) fn build(
    lens: &[u8],
    counts: &mut [u8],
    symbols: &mut [u8],
) -> Result<(), &'static str> {
    // The histogram of lengths.
    let mut hist = [0u16; 16];
    for &l in lens {
        match hist.get_mut(usize::from(l)) {
            Some(h) if l <= MAX_LEN => *h = h.saturating_add(1),
            _ => return Err("a prefix code length over 15"),
        }
    }
    let total = u16::try_from(lens.len()).map_err(|_| "an alphabet over 65535 symbols")?;
    let unused = hist.first().copied().unwrap_or(0);
    let used = total.saturating_sub(unused);
    if used == 0 {
        return Err("a prefix code with no symbols");
    }
    if used == 1 {
        // One symbol: zero bits (RFC 9649 section 3.7.2.1).
        let sym = lens.iter().position(|&l| l != 0).unwrap_or(0);
        for i in 0..16 {
            let v = u16::from(i == 0);
            if !set16(counts, i, v) {
                return Err("a counts array that is too small");
            }
        }
        if !set16(symbols, 0, u16::try_from(sym).unwrap_or(0)) {
            return Err("a symbol array that is too small");
        }
        return Ok(());
    }
    // Complete and not over-subscribed: the code space left after each
    // length, doubled at each step, ends at exactly 0.
    let mut left: i32 = 1;
    for &h in hist.iter().skip(1) {
        left = left.wrapping_mul(2).wrapping_sub(i32::from(h));
        if left < 0 {
            return Err("an over-subscribed prefix code");
        }
    }
    if left != 0 {
        return Err("an incomplete prefix code");
    }
    // The first slot of each length in `symbols`.
    let mut offset = [0u16; 16];
    let mut run = 0u16;
    for (len, &h) in hist.iter().enumerate().skip(1) {
        if let Some(o) = offset.get_mut(len) {
            *o = run;
        }
        run = run.saturating_add(h);
    }
    for (sym, &l) in lens.iter().enumerate() {
        if l == 0 {
            continue;
        }
        let Some(o) = offset.get_mut(usize::from(l)) else {
            return Err("a prefix code length over 15");
        };
        let at = usize::from(*o);
        *o = o.saturating_add(1);
        if !set16(symbols, at, u16::try_from(sym).unwrap_or(0)) {
            return Err("a symbol array that is too small");
        }
    }
    for (i, &h) in hist.iter().enumerate() {
        let v = if i == 0 { 0 } else { h };
        if !set16(counts, i, v) {
            return Err("a counts array that is too small");
        }
    }
    Ok(())
}

/// What one try at reading a symbol gave.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Decoded {
    /// The symbol and the bits its code took.
    Symbol(u16, u8),
    /// The code is longer than the `avail` bits given: more are needed.
    More,
    /// The bits match no code: the tables are not a built code.
    Invalid,
}

/// Decodes one symbol. `bits` holds the next bits of the stream, the next one
/// in bit 0, and `avail` of them (at most 32) are real.
pub(crate) fn decode(counts: &[u8], symbols: &[u8], bits: u32, avail: u8) -> Decoded {
    if get16(counts, 0) == 1 {
        return Decoded::Symbol(get16(symbols, 0), 0);
    }
    let mut code: u32 = 0;
    let mut first: u32 = 0;
    let mut index: u32 = 0;
    for len in 1..=MAX_LEN {
        if len > avail {
            return Decoded::More;
        }
        let bit = bits
            .checked_shr(u32::from(len).wrapping_sub(1))
            .unwrap_or(0)
            & 1;
        code |= bit;
        let count = u32::from(get16(counts, usize::from(len)));
        if code < first.wrapping_add(count) {
            let at = index.wrapping_add(code.wrapping_sub(first));
            let sym = usize::try_from(at).map_or(0, |a| get16(symbols, a));
            return Decoded::Symbol(sym, len);
        }
        index = index.wrapping_add(count);
        first = first.wrapping_add(count).wrapping_shl(1);
        code = code.wrapping_shl(1);
    }
    Decoded::Invalid
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_vec(lens: &[u8]) -> Result<(Vec<u8>, Vec<u8>), &'static str> {
        let mut counts = vec![0u8; 32];
        let mut symbols = vec![0u8; lens.len().max(1).saturating_mul(2)];
        build(lens, &mut counts, &mut symbols)?;
        Ok((counts, symbols))
    }

    #[test]
    fn rfc_style_example() {
        // Lengths 2, 1, 3, 3 (symbols 0 to 3): codes B=0, A=10, C=110, D=111
        // (symbol 1 has the shortest code, then 0, then 2 and 3).
        let (c, s) = build_vec(&[2, 1, 3, 3]).unwrap_or_default();
        // Bits are read first bit first: "0" is symbol 1.
        assert_eq!(decode(&c, &s, 0b0, 1), Decoded::Symbol(1, 1));
        // "10" first bit 1, second bit 0: bits value 0b01.
        assert_eq!(decode(&c, &s, 0b01, 2), Decoded::Symbol(0, 2));
        // "110": first, second, third bits 1,1,0: value 0b011.
        assert_eq!(decode(&c, &s, 0b011, 3), Decoded::Symbol(2, 3));
        // "111".
        assert_eq!(decode(&c, &s, 0b111, 3), Decoded::Symbol(3, 3));
        // Not enough bits.
        assert_eq!(decode(&c, &s, 0b1, 1), Decoded::More);
        assert_eq!(decode(&c, &s, 0b11, 2), Decoded::More);
    }

    #[test]
    fn single_symbol_takes_no_bits() {
        let (c, s) = build_vec(&[0, 0, 5, 0]).unwrap_or_default();
        assert_eq!(decode(&c, &s, 0, 0), Decoded::Symbol(2, 0));
        let (c, s) = build_vec(&[0, 0, 0, 15]).unwrap_or_default();
        assert_eq!(decode(&c, &s, 0xFFFF, 15), Decoded::Symbol(3, 0));
    }

    #[test]
    fn refuses_bad_codes() {
        assert!(build_vec(&[0, 0, 0]).is_err());
        assert!(build_vec(&[1, 1, 1]).is_err());
        assert!(build_vec(&[2, 2, 2]).is_err());
        assert!(build_vec(&[1, 2]).is_err());
        assert!(build_vec(&[16, 1]).is_err());
        assert!(build_vec(&[1, 1]).is_ok());
    }

    #[test]
    fn two_symbols_lower_first() {
        let (c, s) = build_vec(&[0, 1, 0, 1]).unwrap_or_default();
        assert_eq!(decode(&c, &s, 0, 1), Decoded::Symbol(1, 1));
        assert_eq!(decode(&c, &s, 1, 1), Decoded::Symbol(3, 1));
    }
}

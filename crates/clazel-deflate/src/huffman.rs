//! Canonical Huffman codes (RFC 1951 §3.2.2) as a 15-bit lookup table.
//!
//! [`Table::build`] checks a set of code lengths ([`spec::code_usable`]) and
//! fills a table of 32,768 entries, one for each way the next 15 bits of the
//! stream can be. Entry `k` is `symbol * 16 + length` of the code those bits
//! start with, or 0 if none does ([`contract::table_entry`]). A code is
//! read most significant bit first and the stream is read least significant
//! bit first, so the index holds the code's bits reversed.
//!
//! [`spec::code_usable`]: super::spec::code_usable
//! [`contract::table_entry`]: super::contract::table_entry

/// The longest code, in bits (RFC 1951 §3.2.2's `MAX_BITS`).
pub const MAX_BITS: usize = 15;

/// The table's size: one entry for each value of the next 15 bits.
pub const TABLE_LEN: usize = 32768;

/// The most symbols of any alphabet (the literal/length one, 288 with the
/// two fixed-code-only symbols).
pub const MAX_SYMBOLS: usize = 288;

/// What looking up the next bits of the stream found.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Lookup {
    /// The next code is for this symbol and is this many bits long.
    Found(u16, u8),
    /// The bits given are a prefix of no code decided yet: more are needed.
    NeedMore,
    /// 15 bits are available and no code of 1 to 15 bits is a prefix of them.
    Invalid,
}

/// A fast table for one code.
pub struct Table {
    /// [`TABLE_LEN`] entries.
    pub entries: Vec<u16>,
}

impl Default for Table {
    fn default() -> Table {
        Table::new()
    }
}

fn get<T: Copy>(s: &[T], i: usize, default: T) -> T {
    s.get(i).copied().unwrap_or(default)
}

fn set<T>(s: &mut [T], i: usize, v: T) {
    if let Some(slot) = s.get_mut(i) {
        *slot = v;
    }
}

/// The low `len` bits of `code`, in reverse order.
fn reverse(code: u32, len: usize) -> usize {
    let mut r: u32 = 0;
    let mut c = code;
    let mut i = 0;
    while i < len {
        r = (r << 1) | (c & 1);
        c >>= 1;
        i = i.saturating_add(1);
    }
    r as usize
}

impl Table {
    /// An empty table (every entry 0: no code).
    pub fn new() -> Table {
        Table {
            entries: vec![0; TABLE_LEN],
        }
    }

    /// Build the table for the code with these lengths (one per symbol, at
    /// most [`MAX_SYMBOLS`]). Returns whether the lengths are
    /// [`spec::code_usable`](super::spec::code_usable) with this
    /// `allow_incomplete`; if not the table is left empty.
    pub fn build(&mut self, lens: &[u8], allow_incomplete: bool) -> bool {
        for e in self.entries.iter_mut() {
            *e = 0;
        }
        if lens.len() > MAX_SYMBOLS {
            return false;
        }
        // RFC 1951 §3.2.2, step 1: bl_count.
        let mut count = [0u32; MAX_BITS + 1];
        for &l in lens {
            let l = usize::from(l);
            if l > MAX_BITS {
                return false;
            }
            if let Some(c) = count.get_mut(l) {
                *c = c.saturating_add(1);
            }
        }
        // "bl_count[0] = 0": codes of length 0 are not codes.
        set(&mut count, 0, 0);
        // Kraft's sum scaled by 2^15, and the number of codes.
        let mut kraft: u32 = 0;
        let mut used: u32 = 0;
        let mut bits = 1;
        while bits <= MAX_BITS {
            let c = get(&count, bits, 0);
            kraft = kraft.saturating_add(c.saturating_mul(1u32 << (MAX_BITS.saturating_sub(bits))));
            used = used.saturating_add(c);
            bits = bits.saturating_add(1);
        }
        let complete = kraft == 1u32 << MAX_BITS;
        let single = used == 0 || (used == 1 && get(&count, 1, 0) == 1);
        if !(complete || (allow_incomplete && single)) {
            return false;
        }
        // Step 2: next_code.
        let mut next = [0u32; MAX_BITS + 1];
        let mut code: u32 = 0;
        let mut bits = 1;
        while bits <= MAX_BITS {
            code = code
                .saturating_add(get(&count, bits.saturating_sub(1), 0))
                .saturating_mul(2);
            set(&mut next, bits, code);
            bits = bits.saturating_add(1);
        }
        // Step 3, shortest codes first so that a shorter code wins any index
        // a longer one would also claim (there is none for a usable code).
        let mut len = 1;
        while len <= MAX_BITS {
            let mut sym = 0;
            while sym < lens.len() {
                if usize::from(get(lens, sym, 0)) == len {
                    let c = get(&next, len, 0);
                    set(&mut next, len, c.saturating_add(1));
                    let mut idx = reverse(c, len);
                    let step = 1usize << len;
                    let entry = (sym << 4) | len;
                    while idx < TABLE_LEN {
                        if get(&self.entries, idx, 1) == 0 {
                            set(&mut self.entries, idx, entry as u16);
                        }
                        idx = idx.saturating_add(step);
                    }
                }
                sym = sym.saturating_add(1);
            }
            len = len.saturating_add(1);
        }
        true
    }

    /// Look up the code at the start of `bits` (the stream's next bits, the
    /// first in bit 0), of which `nbits` are valid and the rest 0.
    pub fn lookup(&self, bits: u64, nbits: u32) -> Lookup {
        let e = get(&self.entries, (bits & 0x7FFF) as usize, 0);
        let len = e & 15;
        if e != 0 && u32::from(len) <= nbits {
            Lookup::Found(e >> 4, len as u8)
        } else if nbits >= MAX_BITS as u32 {
            Lookup::Invalid
        } else {
            Lookup::NeedMore
        }
    }
}

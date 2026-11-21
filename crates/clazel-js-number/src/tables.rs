//! The powers-of-five tables of the fast paths, computed exactly from
//! [`Big`] the first time they are needed (a few milliseconds).
//!
//! Computing them, instead of pasting numbers, means no table can be
//! mistyped. A later step can emit them as a checked-in constant, as
//! `cargo xtask tables` does for IDNA; the differential tests are the
//! evidence either way. Each entry is a 128-bit `u128`:
//!
//! - `el[q - EL_MIN_Q]`, for the Eisel–Lemire parser: the 128 leading bits
//!   of `5^q`, normalised to have its top bit set. For `q >= 0` they are
//!   truncated; for `q < 0` they are `floor(2^b / 5^-q) + 1` with
//!   `b = z + 127` for `q >= -27` (exactly 128 bits) and `b = 2z + 128`
//!   below that (then shifted down to 128 bits, truncating), `z` the bit
//!   length of `5^-q`.
//!   (Lemire, "Number Parsing at a Gigabyte per Second", software: Practice
//!   and Experience 51(8), 2021, section 5 and the `fast_float` table script.)
//! - `pow5_split[i]`, for the shortest printer: the 125 leading bits of
//!   `5^i`. `pow5_inv_split[q]`: `floor(2^(pow5bits(q) - 1 + 125) / 5^q) + 1`.
//!   (Ulf Adams, "Ryu: fast float-to-string conversion", PLDI 2018, section
//!   3, `d2s_full_table.h`.)

use crate::bigint::Big;
use std::sync::OnceLock;

/// The smallest decimal exponent the Eisel–Lemire table covers.
pub const EL_MIN_Q: i64 = -342;
/// The largest decimal exponent the Eisel–Lemire table covers.
pub const EL_MAX_Q: i64 = 308;
/// Entries of `pow5_split`: `5^0` to `5^325`.
pub const POW5_SPLIT_LEN: u32 = 326;
/// Entries of `pow5_inv_split`: `q` from 0 to 341.
pub const POW5_INV_SPLIT_LEN: u32 = 342;
/// The bit width of the Ryu table entries.
pub const POW5_BITCOUNT: u32 = 125;

/// The computed tables.
pub struct Tables {
    /// Eisel–Lemire's `5^q`, for `q` in `EL_MIN_Q..=EL_MAX_Q`.
    pub el: Vec<u128>,
    /// Ryu's `5^i`, for `i < POW5_SPLIT_LEN`.
    pub pow5_split: Vec<u128>,
    /// Ryu's `5^-q` reciprocals, for `q < POW5_INV_SPLIT_LEN`.
    pub pow5_inv_split: Vec<u128>,
}

/// `ceil(log2(5^e))` for `e >= 1`, and 1 for `e = 0`: the bit length of
/// `5^e`, for `0 <= e <= 3528` (Ryu's `pow5bits`).
#[must_use]
pub fn pow5bits(e: u32) -> u32 {
    (e.saturating_mul(1_217_359) >> 19).saturating_add(1)
}

fn build_el() -> Vec<u128> {
    let mut out = Vec::new();
    let mut q = EL_MIN_Q;
    while q <= EL_MAX_Q {
        let k = u32::try_from(q.unsigned_abs()).unwrap_or(0);
        let p = Big::pow5(k);
        let v = if q >= 0 {
            let bl = p.bit_len();
            if bl > 128 {
                p.shr(bl.saturating_sub(128)).0.low_u128()
            } else {
                p.shl(128u64.saturating_sub(bl)).low_u128()
            }
        } else {
            // z: the least with 2^z >= 5^-q (5^-q is not a power of two).
            let z = p.bit_len();
            let b = if q >= -27 {
                z.saturating_add(127)
            } else {
                z.saturating_mul(2).saturating_add(128)
            };
            let (mut c, _) = Big::divrem(&Big::from_u64(1).shl(b), &p);
            c.add_small(1);
            let cl = c.bit_len();
            if cl > 128 {
                c.shr(cl.saturating_sub(128)).0.low_u128()
            } else {
                c.low_u128()
            }
        };
        out.push(v);
        q = q.saturating_add(1);
    }
    out
}

fn build_split() -> Vec<u128> {
    (0..POW5_SPLIT_LEN)
        .map(|i| {
            let p = Big::pow5(i);
            let bl = p.bit_len();
            let want = u64::from(POW5_BITCOUNT);
            if bl >= want {
                p.shr(bl.saturating_sub(want)).0.low_u128()
            } else {
                p.shl(want.saturating_sub(bl)).low_u128()
            }
        })
        .collect()
}

fn build_inv() -> Vec<u128> {
    (0..POW5_INV_SPLIT_LEN)
        .map(|q| {
            let p = Big::pow5(q);
            let sh = u64::from(pow5bits(q))
                .saturating_sub(1)
                .saturating_add(u64::from(POW5_BITCOUNT));
            let (mut c, _) = Big::divrem(&Big::from_u64(1).shl(sh), &p);
            c.add_small(1);
            c.low_u128()
        })
        .collect()
}

/// The tables, built on first use.
#[must_use]
pub fn tables() -> &'static Tables {
    static T: OnceLock<Tables> = OnceLock::new();
    T.get_or_init(|| Tables {
        el: build_el(),
        pow5_split: build_split(),
        pow5_inv_split: build_inv(),
    })
}

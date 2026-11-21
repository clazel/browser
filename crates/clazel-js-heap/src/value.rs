//! NaN-boxed values, exactly the layout of phase-7.md's "Shapes fixed here
//! for the JIT" (jit.md J.1), which `clazel-js-vm`'s `spec.rs` models
//! (`enc_*`, `decode`). A value is a `u64`.
//!
//! - A double is itself, with every NaN replaced by [`CANON_NAN`]. Then the
//!   top 16 bits of a double are at most `0xFFF8`, and
//!   `0xFFF8_0000_0000_0000` (the negative quiet NaN) is the only
//!   double-range pattern that is not a value.
//! - Everything else is a NaN-space pattern with a 16-bit tag in bits 48..63:
//!   - `0xFFF9` int32: bits 32..47 zero, the int32 in bits 0..31;
//!   - `0xFFFA` special: bits 0..47 are 0 undefined, 1 null, 2 false,
//!     3 true, 4 hole;
//!   - `0xFFFB` heap reference: generation (`u16`) in bits 32..47, arena
//!     index (`u32`) in bits 0..31;
//!   - `0xFFFC` raw: a 48-bit payload (frame header slots).
//!   - `0xFFFD..=0xFFFF` are reserved and not values.
//!
//! A [`Value`] can only hold a well-formed pattern: [`Value::from_bits`]
//! rejects the rest, so a pattern read back from a frame region is checked
//! once, at the boundary.

use crate::arena::Ref;

/// The canonical NaN, the only NaN a value may be.
pub const CANON_NAN: u64 = 0x7FF8_0000_0000_0000;

const TAG_INT32: u64 = 0xFFF9;
const TAG_SPECIAL: u64 = 0xFFFA;
const TAG_REF: u64 = 0xFFFB;
const TAG_RAW: u64 = 0xFFFC;

const SPECIAL_UNDEFINED: u64 = 0;
const SPECIAL_NULL: u64 = 1;
const SPECIAL_FALSE: u64 = 2;
const SPECIAL_TRUE: u64 = 3;
const SPECIAL_HOLE: u64 = 4;

const PAYLOAD_48: u64 = 0xFFFF_FFFF_FFFF;

/// A NaN-boxed value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Value(u64);

/// A value taken apart.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Decoded {
    /// A Number that is not an int32 value (or is one that was not boxed).
    Double(f64),
    /// An int32.
    Int32(i32),
    /// `undefined`.
    Undefined,
    /// `null`.
    Null,
    /// A boolean.
    Bool(bool),
    /// The hole: an uninitialized binding or an absent array element.
    Hole,
    /// A heap reference.
    Ref(Ref),
    /// A 48-bit raw payload.
    Raw(u64),
}

impl Value {
    /// `undefined`.
    pub const UNDEFINED: Self = Self((TAG_SPECIAL << 48) | SPECIAL_UNDEFINED);
    /// `null`.
    pub const NULL: Self = Self((TAG_SPECIAL << 48) | SPECIAL_NULL);
    /// `false`.
    pub const FALSE: Self = Self((TAG_SPECIAL << 48) | SPECIAL_FALSE);
    /// `true`.
    pub const TRUE: Self = Self((TAG_SPECIAL << 48) | SPECIAL_TRUE);
    /// The hole.
    pub const HOLE: Self = Self((TAG_SPECIAL << 48) | SPECIAL_HOLE);

    /// A Number, NaN canonicalized.
    #[must_use]
    pub fn double(x: f64) -> Self {
        if x.is_nan() {
            Self(CANON_NAN)
        } else {
            Self(x.to_bits())
        }
    }

    /// An int32.
    #[must_use]
    pub const fn int32(i: i32) -> Self {
        Self((TAG_INT32 << 48) | (i as u32 as u64))
    }

    /// A boolean.
    #[must_use]
    pub const fn boolean(b: bool) -> Self {
        if b { Self::TRUE } else { Self::FALSE }
    }

    /// A heap reference.
    #[must_use]
    pub const fn heap_ref(r: Ref) -> Self {
        Self((TAG_REF << 48) | ((r.generation as u64) << 32) | (r.index as u64))
    }

    /// A raw payload, or `None` if it does not fit in 48 bits.
    #[must_use]
    pub const fn raw(payload: u64) -> Option<Self> {
        if payload > PAYLOAD_48 {
            None
        } else {
            Some(Self((TAG_RAW << 48) | payload))
        }
    }

    /// The bits as a value, or `None` if the pattern is not a value.
    #[must_use]
    pub fn from_bits(bits: u64) -> Option<Self> {
        decode_bits(bits).map(|_| Self(bits))
    }

    /// The bits.
    #[must_use]
    pub const fn bits(self) -> u64 {
        self.0
    }

    /// Take the value apart. Total: a `Value` is always well formed, so the
    /// fallback is unreachable (`from_bits` is the only way in from bits).
    #[must_use]
    pub fn decode(self) -> Decoded {
        decode_bits(self.0).unwrap_or(Decoded::Undefined)
    }

    /// The value is a heap reference: its reference.
    #[must_use]
    pub fn as_ref(self) -> Option<Ref> {
        match self.decode() {
            Decoded::Ref(r) => Some(r),
            _ => None,
        }
    }
}

/// Decode a bit pattern; `None` if it is not a value.
#[must_use]
pub fn decode_bits(v: u64) -> Option<Decoded> {
    let tag = v >> 48;
    if tag < TAG_INT32 {
        let x = f64::from_bits(v);
        // A NaN other than the canonical one is not a value.
        return if x.is_nan() && v != CANON_NAN {
            None
        } else {
            Some(Decoded::Double(x))
        };
    }
    let low32 = v & 0xFFFF_FFFF;
    let mid16 = (v >> 32) & 0xFFFF;
    match tag {
        TAG_INT32 if mid16 == 0 => Some(Decoded::Int32(low32 as u32 as i32)),
        TAG_SPECIAL => match v & PAYLOAD_48 {
            SPECIAL_UNDEFINED => Some(Decoded::Undefined),
            SPECIAL_NULL => Some(Decoded::Null),
            SPECIAL_FALSE => Some(Decoded::Bool(false)),
            SPECIAL_TRUE => Some(Decoded::Bool(true)),
            SPECIAL_HOLE => Some(Decoded::Hole),
            _ => None,
        },
        TAG_REF => Some(Decoded::Ref(Ref {
            index: low32 as u32,
            generation: mid16 as u16,
        })),
        TAG_RAW => Some(Decoded::Raw(v & PAYLOAD_48)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_constants_are_the_layout_phase_7_fixes() {
        assert_eq!(Value::UNDEFINED.bits(), 0xFFFA_0000_0000_0000);
        assert_eq!(Value::NULL.bits(), 0xFFFA_0000_0000_0001);
        assert_eq!(Value::FALSE.bits(), 0xFFFA_0000_0000_0002);
        assert_eq!(Value::TRUE.bits(), 0xFFFA_0000_0000_0003);
        assert_eq!(Value::HOLE.bits(), 0xFFFA_0000_0000_0004);
        assert_eq!(Value::int32(-1).bits(), 0xFFF9_0000_FFFF_FFFF);
        assert_eq!(Value::int32(7).bits(), 0xFFF9_0000_0000_0007);
        let r = Ref {
            index: 0xDEAD_BEEF,
            generation: 0x1234,
        };
        assert_eq!(Value::heap_ref(r).bits(), 0xFFFB_1234_DEAD_BEEF);
    }

    #[test]
    fn a_double_is_itself_and_every_nan_is_canonical() {
        for x in [
            0.0,
            -0.0,
            1.5,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::MIN_POSITIVE,
        ] {
            assert_eq!(Value::double(x).bits(), x.to_bits());
        }
        // Positive, negative and payload NaNs all become the canonical NaN.
        for bits in [
            CANON_NAN,
            0xFFF8_0000_0000_0000,
            0x7FF0_0000_0000_0001,
            0xFFFF_FFFF_FFFF_FFFF,
            0xFFFB_0000_0000_0000,
        ] {
            assert_eq!(Value::double(f64::from_bits(bits)).bits(), CANON_NAN);
        }
    }

    #[test]
    fn decode_inverts_every_constructor() {
        let r = Ref {
            index: 9,
            generation: 65535,
        };
        let cases = [
            (Value::UNDEFINED, Decoded::Undefined),
            (Value::NULL, Decoded::Null),
            (Value::boolean(false), Decoded::Bool(false)),
            (Value::boolean(true), Decoded::Bool(true)),
            (Value::HOLE, Decoded::Hole),
            (Value::int32(i32::MIN), Decoded::Int32(i32::MIN)),
            (Value::int32(i32::MAX), Decoded::Int32(i32::MAX)),
            (Value::heap_ref(r), Decoded::Ref(r)),
            (Value::double(2.5), Decoded::Double(2.5)),
        ];
        for (v, d) in cases {
            assert_eq!(v.decode(), d);
            assert_eq!(Value::from_bits(v.bits()), Some(v));
        }
        assert_eq!(
            Value::raw(PAYLOAD_48).map(Value::decode),
            Some(Decoded::Raw(PAYLOAD_48))
        );
        assert_eq!(Value::raw(PAYLOAD_48 + 1), None);
        assert_eq!(Value::heap_ref(r).as_ref(), Some(r));
        assert_eq!(Value::NULL.as_ref(), None);
    }

    #[test]
    fn patterns_that_are_not_values_are_rejected() {
        for bits in [
            0xFFF8_0000_0000_0000, // the negative quiet NaN
            0x7FF0_0000_0000_0001, // a signalling NaN
            0xFFF9_0001_0000_0000, // int32 with a non-zero middle
            0xFFFA_0000_0000_0005, // an unknown special
            0xFFFA_0001_0000_0000, // a special with high payload bits
            0xFFFD_0000_0000_0000, // reserved tags
            0xFFFE_0000_0000_0000,
            0xFFFF_FFFF_FFFF_FFFF,
        ] {
            assert_eq!(Value::from_bits(bits), None, "{bits:#x}");
        }
    }
}

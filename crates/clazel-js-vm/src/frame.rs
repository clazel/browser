//! The frame region: the value stack of phase-7.md's "Shapes fixed here for
//! the JIT" (item 7.8, first slice).
//!
//! Each frame is a window of [`Value`] slots in one [`Region`]: four header
//! slots (callee, `this`, the argument count with the frame kind, the return
//! address), then `nparams` argument registers, then `nregs` local registers.
//! The layout is `spec::hdr_*`, `spec::reg_slot`, `spec::enc_argc` and
//! `spec::pack_ret` of [`crate::spec`], written as executable code; the
//! interpreter and (later) the JIT read and write the same slots. Every access
//! is checked: an index past the region is an `Err`, never a panic.

use clazel_js_heap::value::{Decoded, Value};

/// `spec::hdr_slots`: the header slots of a frame.
pub const HDR_SLOTS: usize = 4;
/// `spec::hdr_callee`.
pub const HDR_CALLEE: usize = 0;
/// `spec::hdr_this`.
pub const HDR_THIS: usize = 1;
/// `spec::hdr_argc`.
pub const HDR_ARGC: usize = 2;
/// `spec::hdr_ret`.
pub const HDR_RET: usize = 3;

/// `spec::kind_plain`: a plain call's frame.
pub const KIND_PLAIN: u32 = 0;
/// `spec::kind_construct`: a construct call's frame.
pub const KIND_CONSTRUCT: u32 = 1;
/// `spec::kind_suspendable`: a generator or async frame.
pub const KIND_SUSPENDABLE: u32 = 2;

/// `spec::ret_limit`: a return address packs a frame base and a `pc`, each
/// below this.
pub const RET_LIMIT: usize = 0xFF_FFFF;
/// `spec::RET_NONE`: the return-address payload of a frame with no caller in
/// the region (the entry of a [`crate::Vm::call`]).
pub const RET_NONE: u64 = 0xFFFF_FFFF_FFFF;

/// One argument count packs with the kind as `argc + kind * 2^28`
/// (`spec::enc_argc`).
const KIND_UNIT: i64 = 268_435_456;

/// The frame region could not be indexed or grown.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FrameError {
    /// A slot index is outside the region.
    OutOfRegion,
    /// The region would pass its limit: the stack overflowed.
    Overflow,
}

/// The slot of register `r` of the frame at `fp` (`spec::reg_slot`), or
/// `None` if the sum does not fit.
#[must_use]
pub fn reg_slot(fp: usize, r: u32) -> Option<usize> {
    fp.checked_add(HDR_SLOTS)?
        .checked_add(usize::try_from(r).ok()?)
}

/// The number of slots of a frame of a function with `nparams` parameters and
/// `nregs` registers (`spec::frame_size`).
#[must_use]
pub fn frame_size(nparams: u32, nregs: u32) -> Option<usize> {
    let n = usize::try_from(nparams)
        .ok()?
        .checked_add(usize::try_from(nregs).ok()?)?;
    n.checked_add(HDR_SLOTS)
}

/// `spec::enc_argc`: the int32 value of the argument-count slot.
#[must_use]
pub fn enc_argc(argc: u32, kind: u32) -> Option<Value> {
    let n = i64::from(argc).checked_add(i64::from(kind).checked_mul(KIND_UNIT)?)?;
    i32::try_from(n).ok().map(Value::int32)
}

/// `spec::argc_of` and `spec::kind_of`: the argument count and the frame kind
/// of an argument-count slot.
#[must_use]
pub fn dec_argc(v: Value) -> Option<(u32, u32)> {
    match v.decode() {
        Decoded::Int32(i) if i >= 0 => {
            let n = i64::from(i);
            let argc = u32::try_from(n.checked_rem(KIND_UNIT)?).ok()?;
            let kind = u32::try_from(n.checked_div(KIND_UNIT)?).ok()?;
            Some((argc, kind))
        }
        _ => None,
    }
}

/// `spec::pack_ret`: the return-address value for a caller with frame base
/// `base` at `pc`; `None` if either is not below [`RET_LIMIT`].
#[must_use]
pub fn pack_ret(base: usize, pc: usize) -> Option<Value> {
    if base >= RET_LIMIT || pc >= RET_LIMIT {
        return None;
    }
    let payload = u64::try_from(base).ok()?.checked_shl(24)? | u64::try_from(pc).ok()?;
    Value::raw(payload)
}

/// What a return-address slot holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ret {
    /// The frame has no caller in the region.
    None,
    /// The caller's frame base and the `pc` of its call op.
    Caller {
        /// The caller's frame base.
        base: usize,
        /// The caller's `pc`.
        pc: usize,
    },
}

/// Reads a return-address slot (the inverse of [`pack_ret`]).
#[must_use]
pub fn unpack_ret(v: Value) -> Option<Ret> {
    match v.decode() {
        Decoded::Raw(RET_NONE) => Some(Ret::None),
        Decoded::Raw(p) => Some(Ret::Caller {
            base: usize::try_from(p >> 24).ok()?,
            pc: usize::try_from(p & 0xFF_FFFF).ok()?,
        }),
        _ => None,
    }
}

/// The value-stack region.
#[derive(Debug)]
pub struct Region {
    slots: Vec<Value>,
    limit: usize,
}

impl Region {
    /// An empty region that may grow to `limit` slots (at most
    /// [`RET_LIMIT`] - 1, so every frame base fits a return address).
    #[must_use]
    pub fn new(limit: usize) -> Self {
        Self {
            slots: Vec::new(),
            limit: limit.min(RET_LIMIT.saturating_sub(1)),
        }
    }

    /// The number of slots the region holds.
    #[must_use]
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    /// Whether the region holds no slots.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    /// The slot limit.
    #[must_use]
    pub const fn limit(&self) -> usize {
        self.limit
    }

    /// Makes the region hold at least `n` slots, new ones `undefined`.
    ///
    /// # Errors
    /// [`FrameError::Overflow`] if `n` passes the limit.
    pub fn ensure(&mut self, n: usize) -> Result<(), FrameError> {
        if n > self.limit {
            return Err(FrameError::Overflow);
        }
        if n > self.slots.len() {
            self.slots.resize(n, Value::UNDEFINED);
        }
        Ok(())
    }

    /// The slot at `i`.
    ///
    /// # Errors
    /// [`FrameError::OutOfRegion`] if `i` is past the region.
    pub fn get(&self, i: usize) -> Result<Value, FrameError> {
        self.slots.get(i).copied().ok_or(FrameError::OutOfRegion)
    }

    /// Sets the slot at `i`.
    ///
    /// # Errors
    /// [`FrameError::OutOfRegion`] if `i` is past the region.
    pub fn set(&mut self, i: usize, v: Value) -> Result<(), FrameError> {
        match self.slots.get_mut(i) {
            Some(s) => {
                *s = v;
                Ok(())
            }
            None => Err(FrameError::OutOfRegion),
        }
    }

    /// Register `r` of the frame at `fp`.
    ///
    /// # Errors
    /// [`FrameError::OutOfRegion`] if the slot is past the region.
    pub fn reg(&self, fp: usize, r: u32) -> Result<Value, FrameError> {
        self.get(reg_slot(fp, r).ok_or(FrameError::OutOfRegion)?)
    }

    /// Sets register `r` of the frame at `fp`.
    ///
    /// # Errors
    /// [`FrameError::OutOfRegion`] if the slot is past the region.
    pub fn set_reg(&mut self, fp: usize, r: u32, v: Value) -> Result<(), FrameError> {
        self.set(reg_slot(fp, r).ok_or(FrameError::OutOfRegion)?, v)
    }

    /// A header slot of the frame at `fp`.
    ///
    /// # Errors
    /// [`FrameError::OutOfRegion`] if the slot is past the region.
    pub fn header(&self, fp: usize, which: usize) -> Result<Value, FrameError> {
        self.get(fp.checked_add(which).ok_or(FrameError::OutOfRegion)?)
    }

    /// Writes a frame's header and fills the rest of it (`size` slots in all)
    /// with `undefined`: `spec::pushed_region`.
    ///
    /// # Errors
    /// [`FrameError::Overflow`] if the frame passes the limit.
    pub fn push_frame(
        &mut self,
        base: usize,
        size: usize,
        header: [Value; HDR_SLOTS],
    ) -> Result<(), FrameError> {
        let end = base.checked_add(size).ok_or(FrameError::Overflow)?;
        self.ensure(end)?;
        let window = self
            .slots
            .get_mut(base..end)
            .ok_or(FrameError::OutOfRegion)?;
        for s in window.iter_mut() {
            *s = Value::UNDEFINED;
        }
        for (i, h) in header.into_iter().enumerate() {
            if let Some(s) = window.get_mut(i) {
                *s = h;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn argc_and_kind_round_trip() {
        for argc in [0u32, 1, 7, 268_435_455] {
            for kind in [KIND_PLAIN, KIND_CONSTRUCT, KIND_SUSPENDABLE] {
                let v = enc_argc(argc, kind);
                assert_eq!(v.and_then(dec_argc), Some((argc, kind)));
            }
        }
        assert_eq!(enc_argc(0, 8), None);
    }

    #[test]
    fn return_addresses_round_trip() {
        let v = pack_ret(12, 345);
        assert_eq!(
            v.and_then(unpack_ret),
            Some(Ret::Caller { base: 12, pc: 345 })
        );
        assert_eq!(pack_ret(RET_LIMIT, 0), None);
        assert_eq!(pack_ret(0, RET_LIMIT), None);
        assert_eq!(Value::raw(RET_NONE).and_then(unpack_ret), Some(Ret::None));
    }

    #[test]
    fn a_frame_is_pushed_and_bounded() {
        let mut r = Region::new(10);
        let hdr = [Value::NULL, Value::TRUE, Value::int32(0), Value::UNDEFINED];
        assert_eq!(r.push_frame(2, 6, hdr), Ok(()));
        assert_eq!(r.header(2, HDR_THIS), Ok(Value::TRUE));
        assert_eq!(r.reg(2, 0), Ok(Value::UNDEFINED));
        assert_eq!(r.set_reg(2, 1, Value::int32(5)), Ok(()));
        assert_eq!(r.reg(2, 1), Ok(Value::int32(5)));
        assert_eq!(r.get(8), Err(FrameError::OutOfRegion));
        assert_eq!(r.push_frame(8, 6, hdr), Err(FrameError::Overflow));
        assert_eq!(r.push_frame(usize::MAX, 6, hdr), Err(FrameError::Overflow));
        assert_eq!(reg_slot(usize::MAX, 0), None);
    }
}

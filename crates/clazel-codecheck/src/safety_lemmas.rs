//! Facts proven about the safety theorem's definitions ([`super::safety`],
//! [`super::safety_inv`]), and the concrete data of the kill certificates of
//! `mutations.json` that mutate them. Each lemma restates a rule of the
//! theorem's side (what the host must hand over, what an access may touch,
//! what an index fact says) in a form that does not mention how it is
//! computed; a certificate evaluates the definition on one concrete input and
//! the lemma contradicts it.
//!
//! The examples in [`super::safety_examples`] are kept apart, so that a mutant
//! that breaks one of them does not stop Verus before it checks a certificate
//! here.

#[allow(unused_imports)]
use super::safety::*;
#[allow(unused_imports)]
use super::safety_inv::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// **A handed region avoids the region table**: otherwise a store through the
/// region could rewrite a bound, and the checks would mean nothing.
pub proof fn lemma_region_avoids_table(h: Handed, r: Region)
    requires
        region_ok(h, r),
    ensures
        disjoint(r.base, r.bound, h.ctx, 256),
{
}

/// **A handed region avoids the code**: code is immutable (J.8).
pub proof fn lemma_region_avoids_code(h: Handed, r: Region)
    requires
        region_ok(h, r),
    ensures
        disjoint(r.base, r.bound, h.code, h.len),
{
}

/// **A handed region does not wrap**: so an address `base + i` computed by
/// the machine modulo 2^64 is the one the region means.
pub proof fn lemma_region_no_wrap(h: Handed, r: Region)
    requires
        region_ok(h, r),
    ensures
        r.base + r.bound <= 0x8000_0000_0000_0000,
{
}

/// **A store to the context lies in the exit area**: the region table is
/// never written.
pub proof fn lemma_ctx_store_avoids_table(h: Handed, addr: int, a: Access)
    requires
        ctx_access_ok(h, addr, a),
        a.store,
    ensures
        disjoint(addr, a.size, h.ctx, 256),
{
}

/// **An index fact leaves room for the access**: `v + n <= bound`.
pub proof fn lemma_idx_fits_room(v: int, n: int, bound: int)
    requires
        idx_fits(v, n, bound),
    ensures
        v + n <= bound,
{
}

// ---- Data for the certificates ----

/// A layout: code at 0x10000 (0x100 bytes), context at 0x1000, no regions.
pub open spec fn cx_h() -> Handed {
    Handed { code: 0x10000, len: 0x100, ctx: 0x1000, sp: 0x8000, rg: Seq::empty() }
}

/// A region on the context's region table.
pub open spec fn cx_region_on_table() -> Region {
    Region { base: 0x1000, bound: 16 }
}

/// A region on the code.
pub open spec fn cx_region_on_code() -> Region {
    Region { base: 0x10010, bound: 16 }
}

/// A region that wraps past 2^63.
pub open spec fn cx_region_wraps() -> Region {
    Region { base: 0x7FFF_FFFF_FFFF_FFF8, bound: 16 }
}

/// An 8-byte store.
pub open spec fn cx_store8() -> Access {
    Access { mem: Mem { base: 15, index: None, disp: 0 }, size: 8, store: true }
}

} // verus!

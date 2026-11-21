//! Examples for the safety theorem's definitions ([`super`]),
//! proven by evaluating them: which layouts the host may hand over, which
//! accesses the theorem allows, and what an index fact says. Each refused
//! example is one that a weakened definition would accept, so the theorem
//! would stop being true (`mutations.json` cites the lemmas of
//! [`super::lemmas`] for the same data).
//!
//! The last example, [`example_handed_satisfiable`], shows that the theorem's
//! hypothesis [`handed_ok`] can be met: a layout of sixteen regions.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A region in free memory is a legitimate handout.
pub proof fn example_region_ok() {
    assert(region_ok(cx_h(), Region { base: 0x2000, bound: 0x100 })) by (compute_only);
}

/// A region on the region table is not: the code could rewrite a bound.
pub proof fn example_region_on_table_refused() {
    assert(!region_ok(cx_h(), cx_region_on_table())) by (compute_only);
}

/// A region on the code is not: the code would not be immutable.
pub proof fn example_region_on_code_refused() {
    assert(!region_ok(cx_h(), cx_region_on_code())) by (compute_only);
}

/// A region that wraps past 2^63 is not.
pub proof fn example_region_wrap_refused() {
    assert(!region_ok(cx_h(), cx_region_wraps())) by (compute_only);
}

/// A store to the exit area of the context is allowed.
pub proof fn example_store_exit_area_ok() {
    assert(ctx_access_ok(cx_h(), 0x1100int, cx_store8())) by (compute_only);
}

/// A store to the region table is not.
pub proof fn example_store_table_refused() {
    assert(!ctx_access_ok(cx_h(), 0x1000int, cx_store8())) by (compute_only);
}

/// A load from the region table is allowed.
pub proof fn example_load_table_ok() {
    assert(ctx_access_ok(
        cx_h(),
        0x1000int,
        Access { mem: Mem { base: 15, index: None, disp: 0 }, size: 8, store: false },
    )) by (compute_only);
}

/// An index of 2 with 8 bytes after it fits a bound of 10; an index of 5 does
/// not.
pub proof fn example_idx_fits() {
    assert(idx_fits(2, 8, 10)) by (compute_only);
    assert(!idx_fits(5, 8, 10)) by (compute_only);
}

/// The hypothesis of the theorem can be met: sixteen 256-byte regions at
/// 0x2000 and after, the context at 0x1000, the code at 0x10000.
pub proof fn example_handed_satisfiable() {
    let h = Handed {
        code: 0x10000,
        len: 0x100,
        ctx: 0x1000,
        sp: 0x8000,
        rg: Seq::new(16, |k: int| Region { base: 0x2000 + 0x100 * k, bound: 0x100 }),
    };
    assert(handed_ok(h)) by {
        assert forall|k: int| 0 <= k < 16 implies region_ok(h, #[trigger] h.rg[k]) by {
            assert(h.rg[k] == Region { base: 0x2000 + 0x100 * k, bound: 0x100 });
        }
    }
}

} // verus!

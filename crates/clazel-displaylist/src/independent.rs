//! A second definition of the display list, from a different text: the paragraph
//! "**The format, as designed.**" of item 5.17a in `docs/phases/phase-5.md`. The format
//! is this project's own, so there is no second standard to read, and that paragraph
//! was written by the same session that wrote `spec.rs`: it is a different text, not a
//! different author's. A misreading in that session could be in both.
//!
//! The definitions (everything before the equivalence section at the end) were written
//! from that paragraph alone, in a session that had not read `spec.rs`, `contract.rs`,
//! `lemmas.rs`, `exec.rs`, `examples.rs`, `mutations.json`, this crate's `README.md` or
//! its `tests/`. The session read this crate's `Cargo.toml` and `lib.rs`, the rest of
//! item 5.17a around the paragraph (the item list and the "Proven" paragraph, which
//! names three theorems), `docs/SPEC-STYLE.md`, and the headers of `clazel-der`,
//! `clazel-ipc`'s `cbor` and `clazel-store`'s `independent.rs` for their shape.
//!
//! ## Modelling choices
//!
//! - Numbers are `int` and `nat`, not machine integers: a field's value is a formula
//!   over its bytes ([`i_u16`], [`i_u32`], [`i_s32`]), and two's complement is
//!   subtracting 2^32 from the values of 2^31 and above.
//! - Reading is by position, not by consuming a prefix. [`i_end`] says where the item
//!   at a position ends; [`i_start`] says where the k-th item starts; the bytes are a
//!   list of k items when the k-th start is the end of the bytes ("nothing around
//!   them"), and the list is then [`i_cmd`] at each start ([`i_read`]). No bytes at all
//!   are a run of no items.
//! - The columns and rows of an upload are not a reading rule: an upload of 0 columns
//!   reads, and the check refuses it.
//! - The check is a left fold of one step over the items ([`i_check`]), with a stack
//!   depth and a table of live masks as its state. It refuses by the fold's state
//!   becoming `None`. What it gives back on success is the table later lists start from.
//! - A live mask in the table is its id and its cost, columns × rows, which is all the
//!   paragraph's rules use. Live coverage is not a counter: it is the sum of the table
//!   over every id below 2^16 ([`i_live_coverage`]), since no other id can be live.
//! - "Stays at most 2^26" is checked when an upload would add to it, the only step
//!   that can raise it, on the table with the new mask in it.
//! - "Within ±2^23" includes both ends, and "at most" and "1 to 2048" include theirs.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One item of a list, as the paragraph's tags describe it.
pub enum Cmd {
    /// Tag 1: "fills a rectangle: x, y (signed, 32 bits), width, height, colour
    /// (unsigned, 32 bits)".
    Rect { x: int, y: int, w: nat, h: nat, colour: nat },
    /// Tag 2: "pushes a clip: x, y, width, height, as tag 1".
    ClipIn { x: int, y: int, w: nat, h: nat },
    /// Tag 3: "pops a clip and has no fields".
    ClipOut,
    /// Tag 4: "uploads a mask: id (unsigned, 32 bits), columns, rows (unsigned, 16
    /// bits), then columns × rows bytes of coverage".
    MaskIn { id: nat, columns: nat, rows: nat, coverage: Seq<u8> },
    /// Tag 5: "draws a mask: id, then x, y, then colour, each 32 bits as above".
    Stamp { id: nat, x: int, y: int, colour: nat },
    /// Tag 6: "frees a mask: id".
    MaskOut { id: nat },
}

// ------------------------------------------------------------------------------------
// The fields: "least significant byte first", "signed fields are two's complement".
// ------------------------------------------------------------------------------------

/// The unsigned 16-bit field at byte `p`.
pub open spec fn i_u16(b: Seq<u8>, p: int) -> nat {
    (b[p] as int + b[p + 1] as int * 0x100) as nat
}

/// The unsigned 32-bit field at byte `p`.
pub open spec fn i_u32(b: Seq<u8>, p: int) -> nat {
    (b[p] as int
        + b[p + 1] as int * 0x100
        + b[p + 2] as int * 0x10000
        + b[p + 3] as int * 0x1000000) as nat
}

/// The signed 32-bit field at byte `p`.
pub open spec fn i_s32(b: Seq<u8>, p: int) -> int {
    let u = i_u32(b, p) as int;
    if u >= 0x80000000 {
        u - 0x100000000
    } else {
        u
    }
}

// ------------------------------------------------------------------------------------
// Reading, by position
// ------------------------------------------------------------------------------------

/// Where the item starting at byte `p` ends: `None` when there is no item there, the
/// tag being past the bytes, not one of the six, or the item "cut short".
pub open spec fn i_end(b: Seq<u8>, p: int) -> Option<int> {
    if p < 0 || p >= b.len() {
        None
    } else {
        // The tag byte and then the fields: 5 × 4, 4 × 4, nothing, 4 + 2 + 2 and the
        // coverage, 4 × 4, 4.
        let end = if b[p] == 1 {
            Some(p + 21)
        } else if b[p] == 2 {
            Some(p + 17)
        } else if b[p] == 3 {
            Some(p + 1)
        } else if b[p] == 4 {
            if p + 9 <= b.len() {
                Some(p + 9 + i_u16(b, p + 5) * i_u16(b, p + 7))
            } else {
                None
            }
        } else if b[p] == 5 {
            Some(p + 17)
        } else if b[p] == 6 {
            Some(p + 5)
        } else {
            None
        };
        match end {
            Some(e) => if e <= b.len() { Some(e) } else { None },
            None => None,
        }
    }
}

/// Where the `k`-th item starts, counting from 0: the first at byte 0, each later one
/// where the one before it ends. `None` when an earlier item does not read.
pub open spec fn i_start(b: Seq<u8>, k: nat) -> Option<int>
    decreases k,
{
    if k == 0 {
        Some(0)
    } else {
        match i_start(b, (k - 1) as nat) {
            Some(p) => i_end(b, p),
            None => None,
        }
    }
}

/// The item whose tag is at byte `p`, when [`i_end`] says one is there.
pub open spec fn i_cmd(b: Seq<u8>, p: int) -> Cmd {
    if b[p] == 1 {
        Cmd::Rect {
            x: i_s32(b, p + 1),
            y: i_s32(b, p + 5),
            w: i_u32(b, p + 9),
            h: i_u32(b, p + 13),
            colour: i_u32(b, p + 17),
        }
    } else if b[p] == 2 {
        Cmd::ClipIn {
            x: i_s32(b, p + 1),
            y: i_s32(b, p + 5),
            w: i_u32(b, p + 9),
            h: i_u32(b, p + 13),
        }
    } else if b[p] == 3 {
        Cmd::ClipOut
    } else if b[p] == 4 {
        let columns = i_u16(b, p + 5);
        let rows = i_u16(b, p + 7);
        Cmd::MaskIn {
            id: i_u32(b, p + 1),
            columns,
            rows,
            coverage: b.subrange(p + 9, p + 9 + columns * rows),
        }
    } else if b[p] == 5 {
        Cmd::Stamp {
            id: i_u32(b, p + 1),
            x: i_s32(b, p + 5),
            y: i_s32(b, p + 9),
            colour: i_u32(b, p + 13),
        }
    } else {
        Cmd::MaskOut { id: i_u32(b, p + 1) }
    }
}

/// "A list is a run of items with nothing around them": `k` items end exactly at the
/// end of the bytes.
pub open spec fn i_is_run(b: Seq<u8>, k: nat) -> bool {
    i_start(b, k) == Some(b.len() as int)
}

/// Reading a list. `None`: "any other tag, an item cut short, or more than 2^27 bytes
/// in all is not a list".
pub open spec fn i_read(b: Seq<u8>) -> Option<Seq<Cmd>> {
    if b.len() > 0x8000000 {
        None
    } else if exists|k: nat| i_is_run(b, k) {
        let k = choose|k: nat| i_is_run(b, k);
        Some(Seq::new(k, |i: int| i_cmd(b, i_start(b, i as nat).unwrap())))
    } else {
        None
    }
}

// ------------------------------------------------------------------------------------
// Checking, as a fold
// ------------------------------------------------------------------------------------

/// "A position lies within ±2^23".
pub open spec fn i_position_ok(v: int) -> bool {
    -0x800000 <= v <= 0x800000
}

/// "A width or height is at most 2^23".
pub open spec fn i_extent_ok(v: nat) -> bool {
    v <= 0x800000
}

/// "An id is below 2^16".
pub open spec fn i_id_ok(id: nat) -> bool {
    id < 0x10000
}

/// The sum of the costs of the live masks with an id below `n`.
pub open spec fn i_coverage_below(live: Map<nat, nat>, n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        let id = (n - 1) as nat;
        i_coverage_below(live, id) + if live.contains_key(id) { live[id] } else { 0 }
    }
}

/// "Live coverage, each mask costing columns × rows".
pub open spec fn i_live_coverage(live: Map<nat, nat>) -> nat {
    i_coverage_below(live, 0x10000)
}

/// The state of the fold: how deep the clip stack is, and the live masks by id with
/// their costs.
pub struct Walk {
    /// How many clips are pushed.
    pub depth: nat,
    /// The cost of each live mask, by id.
    pub live: Map<nat, nat>,
}

/// One item against the state: the next state, or `None` when the item breaks a rule.
pub open spec fn i_step(w: Walk, c: Cmd) -> Option<Walk> {
    match c {
        Cmd::Rect { x, y, w: width, h: height, colour: _ } => {
            // "A position lies within ±2^23 and a width or height is at most 2^23, for
            // fills, clips and draws". "Colours have no rule."
            if i_position_ok(x) && i_position_ok(y) && i_extent_ok(width) && i_extent_ok(height) {
                Some(w)
            } else {
                None
            }
        },
        Cmd::ClipIn { x, y, w: width, h: height } => {
            // As for fills, and the stack "never passes 256".
            if i_position_ok(x) && i_position_ok(y) && i_extent_ok(width) && i_extent_ok(height)
                && w.depth + 1 <= 256 {
                Some(Walk { depth: w.depth + 1, live: w.live })
            } else {
                None
            }
        },
        Cmd::ClipOut => {
            // "A clip stack never pops when empty".
            if w.depth > 0 {
                Some(Walk { depth: (w.depth - 1) as nat, live: w.live })
            } else {
                None
            }
        },
        Cmd::MaskIn { id, columns, rows, coverage: _ } => {
            // "An upload's id is not live, its columns and rows are 1 to 2048, and live
            // coverage, each mask costing columns × rows, stays at most 2^26 bytes".
            let after = w.live.insert(id, columns * rows);
            if i_id_ok(id) && !w.live.contains_key(id) && 1 <= columns <= 2048 && 1 <= rows <= 2048
                && i_live_coverage(after) <= 0x4000000 {
                Some(Walk { depth: w.depth, live: after })
            } else {
                None
            }
        },
        Cmd::Stamp { id, x, y, colour: _ } => {
            // "A draw or a free names a live mask", and a position as above.
            if i_id_ok(id) && w.live.contains_key(id) && i_position_ok(x) && i_position_ok(y) {
                Some(w)
            } else {
                None
            }
        },
        Cmd::MaskOut { id } => {
            // "A draw or a free names a live mask, and a free ends it."
            if i_id_ok(id) && w.live.contains_key(id) {
                Some(Walk { depth: w.depth, live: w.live.remove(id) })
            } else {
                None
            }
        },
    }
}

/// The items checked "in order": the fold of [`i_step`], refusal being absorbing.
pub open spec fn i_walk(items: Seq<Cmd>, start: Walk) -> Option<Walk> {
    items.fold_left(
        Some(start),
        |s: Option<Walk>, c: Cmd|
            match s {
                Some(w) => i_step(w, c),
                None => None,
            },
    )
}

/// A list checked "against the masks earlier lists left": the masks it leaves, or `None`
/// when it is refused. "At most 2^20 items"; the clip stack starts empty and "ends empty".
pub open spec fn i_check(items: Seq<Cmd>, earlier: Map<nat, nat>) -> Option<Map<nat, nat>> {
    if items.len() > 0x100000 {
        None
    } else {
        match i_walk(items, Walk { depth: 0, live: earlier }) {
            Some(w) => if w.depth == 0 { Some(w.live) } else { None },
            None => None,
        }
    }
}

} // verus!

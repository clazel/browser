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
//! `clazel-ipc`'s `cbor` and `clazel-store`'s `independent.rs` for their shape. It also
//! had the brief for this file, which named `decode` and `validate` as what to prove
//! equal and said what the file should define, and it saw this crate's commit subjects.
//! While the definitions were being checked, Verus's warnings about generated code gave
//! the locations `spec.rs:76:1` and `exec.rs:12:1`; that output was filtered so that no
//! line of those files printed, and none did. Those definitions were committed on their
//! own (`b8e3844`), and only then was `spec.rs` read, to write the equivalence section,
//! which necessarily names the spec's items; only it does, and the import of the spec
//! above exists for it. No other file of the list above was opened. Since that commit
//! the definitions have changed only in doc comments and in `Cmd` and `Walk` being
//! marked `ghost`, as the spec's types are: nothing that means anything.
//!
//! ## What the equivalence says
//!
//! - [`theorem_read_equals_decode`]: on every byte string, [`i_read`] is `decode` with
//!   [`cmd_of`] applied to each item, and [`lemma_cmd_of_injective`] shows that mapping
//!   loses nothing.
//! - [`theorem_check_equals_validate`]: on every list and every table of masks of the
//!   spec's fixed length 2^16, [`i_check`] refuses when `validate` does, and otherwise
//!   leaves the masks `validate` leaves, under [`costs_of`]. The length is a hypothesis
//!   because the spec indexes the table by id. `masks_ok`'s bound on the bytes is not
//!   needed.
//! - The masks compare by id and cost. The paragraph's rules use nothing else, so this
//!   file keeps nothing else, and the width and height the spec stores for each mask
//!   are not compared: they are the one thing these theorems say nothing about.
//!
//! The paragraph and the spec did not differ anywhere: no definition had to change for
//! a proof to go through. Being written by the same session, they could still share a
//! misreading of what the format should be; this shows only that they say the same.
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
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One item of a list, as the paragraph's tags describe it.
pub ghost enum Cmd {
    /// Tag 1: "fills a rectangle: x, y (signed, 32 bits), width, height, colour
    /// (unsigned, 32 bits)".
    Rect {
        /// Signed, 32 bits.
        x: int,
        /// Signed, 32 bits.
        y: int,
        /// Unsigned, 32 bits.
        w: nat,
        /// Unsigned, 32 bits.
        h: nat,
        /// Unsigned, 32 bits.
        colour: nat,
    },
    /// Tag 2: "pushes a clip: x, y, width, height, as tag 1".
    ClipIn {
        /// As in [`Cmd::Rect`].
        x: int,
        /// As in [`Cmd::Rect`].
        y: int,
        /// As in [`Cmd::Rect`].
        w: nat,
        /// As in [`Cmd::Rect`].
        h: nat,
    },
    /// Tag 3: "pops a clip and has no fields".
    ClipOut,
    /// Tag 4: "uploads a mask: id (unsigned, 32 bits), columns, rows (unsigned, 16
    /// bits), then columns × rows bytes of coverage".
    MaskIn {
        /// Unsigned, 32 bits.
        id: nat,
        /// Unsigned, 16 bits.
        columns: nat,
        /// Unsigned, 16 bits.
        rows: nat,
        /// Columns × rows bytes.
        coverage: Seq<u8>,
    },
    /// Tag 5: "draws a mask: id, then x, y, then colour, each 32 bits as above".
    Stamp {
        /// Unsigned, 32 bits.
        id: nat,
        /// Signed, 32 bits.
        x: int,
        /// Signed, 32 bits.
        y: int,
        /// Unsigned, 32 bits.
        colour: nat,
    },
    /// Tag 6: "frees a mask: id".
    MaskOut {
        /// Unsigned, 32 bits.
        id: nat,
    },
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
pub ghost struct Walk {
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

// ------------------------------------------------------------------------------------
// The equivalence with the spec: the only part of this file that names it
// ------------------------------------------------------------------------------------

/// An item of the spec as an item of this file: the same fields, as plain numbers.
pub open spec fn cmd_of(item: Item) -> Cmd {
    match item {
        Item::FillRect { x, y, width, height, colour } => Cmd::Rect {
            x: x as int,
            y: y as int,
            w: width as nat,
            h: height as nat,
            colour: colour as nat,
        },
        Item::PushClip { x, y, width, height } => Cmd::ClipIn {
            x: x as int,
            y: y as int,
            w: width as nat,
            h: height as nat,
        },
        Item::PopClip => Cmd::ClipOut,
        Item::UploadMask { id, columns, rows, coverage } => Cmd::MaskIn {
            id: id as nat,
            columns: columns as nat,
            rows: rows as nat,
            coverage,
        },
        Item::DrawMask { id, x, y, colour } => Cmd::Stamp {
            id: id as nat,
            x: x as int,
            y: y as int,
            colour: colour as nat,
        },
        Item::FreeMask { id } => Cmd::MaskOut { id: id as nat },
    }
}

/// A list of the spec's items as a list of this file's.
pub open spec fn cmds_of(items: Seq<Item>) -> Seq<Cmd> {
    items.map_values(|item: Item| cmd_of(item))
}

/// The spec's table of masks as this file's: each live mask's id and its cost.
pub open spec fn costs_of(masks: Masks) -> Map<nat, nat> {
    costs_below(masks.table, masks.table.len())
}

/// The entries of a table with an id below `n`, as a map.
pub open spec fn costs_below(table: Seq<Option<MaskSize>>, n: nat) -> Map<nat, nat>
    decreases n,
{
    if n == 0 {
        Map::empty()
    } else {
        let id = (n - 1) as nat;
        match table[id as int] {
            Some(size) => costs_below(table, id).insert(id, size.width * size.height),
            None => costs_below(table, id),
        }
    }
}

proof fn lemma_costs_below(table: Seq<Option<MaskSize>>, n: nat)
    requires
        n <= table.len(),
    ensures
        forall|id: nat| #[trigger]
            costs_below(table, n).dom().contains(id) == (id < n && table[id as int] is Some),
        forall|id: nat| #[trigger]
            costs_below(table, n).dom().contains(id) ==> costs_below(table, n)[id]
                == table[id as int].unwrap().width * table[id as int].unwrap().height,
    decreases n,
{
    if n > 0 {
        let below = (n - 1) as nat;
        lemma_costs_below(table, below);
        let all = costs_below(table, n);
        let prior = costs_below(table, below);
        assert forall|id: nat| #[trigger] all.dom().contains(id) == (id < n && table[id as int] is Some) by {
            assert(prior.dom().contains(id) == (id < below && table[id as int] is Some));
        }
        assert forall|id: nat| #[trigger] all.dom().contains(id) implies all[id]
            == table[id as int].unwrap().width * table[id as int].unwrap().height by {
            assert(prior.dom().contains(id) == (id < below && table[id as int] is Some));
        }
    }
}

/// What the map holds: the live entries of the table and their costs.
proof fn lemma_costs(m: Masks)
    ensures
        forall|id: nat| #[trigger]
            costs_of(m).dom().contains(id) == (id < m.table.len() && m.table[id as int] is Some),
        forall|id: nat| #[trigger]
            costs_of(m).dom().contains(id) ==> costs_of(m)[id]
                == m.table[id as int].unwrap().width * m.table[id as int].unwrap().height,
{
    lemma_costs_below(m.table, m.table.len());
}

/// The mapping loses nothing: different items of the spec are different items here.
pub proof fn lemma_cmd_of_injective(a: Item, b: Item)
    requires
        cmd_of(a) == cmd_of(b),
    ensures
        a == b,
{
}

// ---- The fields

proof fn lemma_le_value_2(t: Seq<u8>)
    requires
        t.len() == 2,
    ensures
        le_value(t) == t[0] as int + t[1] as int * 0x100,
{
    reveal_with_fuel(le_value, 3);
    let t1 = t.subrange(1, 2);
    assert(t1[0] == t[1]);
    assert(t1.subrange(1, 1).len() == 0);
}

proof fn lemma_le_value_4(t: Seq<u8>)
    requires
        t.len() == 4,
    ensures
        le_value(t) == t[0] as int + t[1] as int * 0x100 + t[2] as int * 0x10000 + t[3] as int * 0x1000000,
{
    let t2 = t.subrange(2, 4);
    assert(t.subrange(1, 4).subrange(1, 3) =~= t2);
    assert(t.subrange(1, 4)[0] == t[1]);
    lemma_le_value_2(t2);
    assert(t2[0] == t[2] && t2[1] == t[3]);
    assert(le_value(t.subrange(1, 4)) == t[1] as int + 256 * le_value(t2));
    assert(le_value(t) == t[0] as int + 256 * le_value(t.subrange(1, 4)));
}

/// A 2-byte field of the bytes from `p` on is the same field of the whole.
proof fn lemma_field2(b: Seq<u8>, p: int, k: int)
    requires
        0 <= p,
        0 <= k,
        p + k + 2 <= b.len(),
    ensures
        field2(b.subrange(p, b.len() as int), k) == i_u16(b, p + k),
        i_u16(b, p + k) < 0x10000,
{
    let t = b.subrange(p, b.len() as int).subrange(k, k + 2);
    assert(t[0] == b[p + k] && t[1] == b[p + k + 1]);
    lemma_le_value_2(t);
}

/// A 4-byte field of the bytes from `p` on is the same field of the whole.
proof fn lemma_field4(b: Seq<u8>, p: int, k: int)
    requires
        0 <= p,
        0 <= k,
        p + k + 4 <= b.len(),
    ensures
        field4(b.subrange(p, b.len() as int), k) == i_u32(b, p + k),
        i_u32(b, p + k) < 0x100000000,
        i32_of(i_u32(b, p + k)) as int == i_s32(b, p + k),
{
    let t = b.subrange(p, b.len() as int).subrange(k, k + 4);
    assert(t[0] == b[p + k] && t[1] == b[p + k + 1] && t[2] == b[p + k + 2] && t[3] == b[p + k + 3]);
    lemma_le_value_4(t);
}

// ---- Reading

/// One item: the spec on the bytes from `p` on says what this file says at `p`.
proof fn lemma_item_at(b: Seq<u8>, p: int)
    requires
        0 <= p < b.len(),
    ensures
        ({
            let t = b.subrange(p, b.len() as int);
            match decode_item(t) {
                None => i_end(b, p) is None,
                Some((item, taken)) => {
                    0 < taken <= t.len() && i_end(b, p) == Some(p + taken) && cmd_of(item) == i_cmd(b, p)
                },
            }
        }),
{
    let t = b.subrange(p, b.len() as int);
    assert(t[0] == b[p]);
    if b[p] == 1 {
        if t.len() >= 21 {
            lemma_field4(b, p, 1);
            lemma_field4(b, p, 5);
            lemma_field4(b, p, 9);
            lemma_field4(b, p, 13);
            lemma_field4(b, p, 17);
        }
    } else if b[p] == 2 {
        if t.len() >= 17 {
            lemma_field4(b, p, 1);
            lemma_field4(b, p, 5);
            lemma_field4(b, p, 9);
            lemma_field4(b, p, 13);
        }
    } else if b[p] == 4 {
        if t.len() >= 9 {
            lemma_field4(b, p, 1);
            lemma_field2(b, p, 5);
            lemma_field2(b, p, 7);
            let size = (i_u16(b, p + 5) * i_u16(b, p + 7)) as int;
            assert(size >= 0) by (nonlinear_arith)
                requires
                    i_u16(b, p + 5) >= 0,
                    i_u16(b, p + 7) >= 0,
                    size == i_u16(b, p + 5) * i_u16(b, p + 7),
            ;
            if t.len() >= 9 + size {
                assert(t.subrange(9, 9 + size) =~= b.subrange(p + 9, p + 9 + size));
            }
        }
    } else if b[p] == 5 {
        if t.len() >= 17 {
            lemma_field4(b, p, 1);
            lemma_field4(b, p, 5);
            lemma_field4(b, p, 9);
            lemma_field4(b, p, 13);
        }
    } else if b[p] == 6 {
        if t.len() >= 5 {
            lemma_field4(b, p, 1);
        }
    }
}

proof fn lemma_none_stays(b: Seq<u8>, k: nat, j: nat)
    requires
        k <= j,
        i_start(b, k) is None,
    ensures
        i_start(b, j) is None,
    decreases j - k,
{
    if k < j {
        lemma_none_stays(b, k, (j - 1) as nat);
    }
}

/// Only one count of items ends at the end of the bytes, so [`i_read`]'s `choose` has
/// one answer: past the end there is no item.
pub proof fn lemma_run_unique(b: Seq<u8>, k: nat, j: nat)
    requires
        i_is_run(b, k),
        i_is_run(b, j),
    ensures
        k == j,
{
    if k < j {
        assert(i_start(b, k + 1) is None);
        lemma_none_stays(b, k + 1, j);
    } else if j < k {
        assert(i_start(b, j + 1) is None);
        lemma_none_stays(b, j + 1, k);
    }
}

/// The items `rest` start at the `n`-th position and run to the end of the bytes.
spec fn run_agrees(b: Seq<u8>, n: nat, rest: Seq<Item>) -> bool {
    &&& i_is_run(b, n + rest.len())
    &&& forall|i: int|
        0 <= i < rest.len() ==> i_cmd(b, i_start(b, (n + i) as nat).unwrap()) == cmd_of(#[trigger] rest[i])
}

/// The spec's recursion on what is left of the bytes against this file's positions.
proof fn lemma_run(b: Seq<u8>, n: nat, p: int)
    requires
        i_start(b, n) == Some(p),
        0 <= p <= b.len(),
    ensures
        match decode_items(b.subrange(p, b.len() as int)) {
            Some(rest) => run_agrees(b, n, rest),
            None => forall|k: nat| k >= n ==> !#[trigger] i_is_run(b, k),
        },
    decreases b.len() - p,
{
    let t = b.subrange(p, b.len() as int);
    assert(i_start(b, n + 1) == i_end(b, p));
    if p < b.len() {
        lemma_item_at(b, p);
        match decode_item(t) {
            None => {
                assert forall|k: nat| k >= n implies !#[trigger] i_is_run(b, k) by {
                    if k > n {
                        lemma_none_stays(b, n + 1, k);
                    }
                }
            },
            Some((item, taken)) => {
                let next = p + taken;
                assert(t.subrange(taken as int, t.len() as int) =~= b.subrange(next, b.len() as int));
                lemma_run(b, n + 1, next);
                match decode_items(b.subrange(next, b.len() as int)) {
                    None => {
                        assert forall|k: nat| k >= n implies !#[trigger] i_is_run(b, k) by {
                            if k > n {
                                assert(k >= n + 1);
                            }
                        }
                    },
                    Some(tail) => {
                        let rest = seq![item] + tail;
                        assert((n + 1) + tail.len() == n + rest.len());
                        assert forall|i: int| 0 <= i < rest.len() implies i_cmd(
                            b,
                            i_start(b, (n + i) as nat).unwrap(),
                        ) == cmd_of(#[trigger] rest[i]) by {
                            if i > 0 {
                                assert(rest[i] == tail[i - 1]);
                                assert((n + i) as nat == ((n + 1) + (i - 1)) as nat);
                            } else {
                                assert((n + i) as nat == n);
                            }
                        }
                    },
                }
            },
        }
    } else {
        assert(t.len() == 0);
    }
}

/// The reader by position is the spec's `decode`, on every input.
pub proof fn theorem_read_equals_decode(b: Seq<u8>)
    ensures
        i_read(b) == match decode(b) {
            None => None,
            Some(items) => Some(cmds_of(items)),
        },
{
    if b.len() <= 0x8000000 {
        assert(i_start(b, 0) == Some(0int));
        lemma_run(b, 0, 0);
        assert(b.subrange(0, b.len() as int) =~= b);
        match decode_items(b) {
            None => {
                assert(forall|k: nat| k >= 0 ==> !#[trigger] i_is_run(b, k));
            },
            Some(items) => {
                assert(i_is_run(b, 0 + items.len()));
                assert(i_is_run(b, items.len()));
                let k = choose|k: nat| i_is_run(b, k);
                lemma_run_unique(b, k, items.len());
                let read = Seq::new(k, |i: int| i_cmd(b, i_start(b, i as nat).unwrap()));
                assert forall|i: int| 0 <= i < items.len() implies read[i] == cmds_of(items)[i] by {
                    assert((0 + i) as nat == i as nat);
                    assert(i_cmd(b, i_start(b, (0 + i) as nat).unwrap()) == cmd_of(items[i]));
                }
                assert(read =~= cmds_of(items));
            },
        }
    }
}

// ---- Live coverage: the spec sums a table from the front, this file a map by id

proof fn lemma_live_bytes_last(t: Seq<Option<MaskSize>>)
    requires
        t.len() > 0,
    ensures
        live_bytes(t) == live_bytes(t.drop_last()) + match t.last() {
            None => 0nat,
            Some(size) => size.width * size.height,
        },
    decreases t.len(),
{
    let tail = t.subrange(1, t.len() as int);
    let front = t.drop_last();
    if t.len() == 1 {
        assert(live_bytes(tail) == 0);
        assert(live_bytes(front) == 0);
        assert(t.last() == t[0]);
    } else {
        lemma_live_bytes_last(tail);
        assert(tail.drop_last() =~= front.subrange(1, front.len() as int));
        assert(front[0] == t[0]);
        assert(tail.last() == t.last());
        assert(live_bytes(front) == live_bytes(tail.drop_last()) + match front[0] {
            None => 0nat,
            Some(size) => size.width * size.height,
        });
        assert(live_bytes(t) == live_bytes(tail) + match t[0] {
            None => 0nat,
            Some(size) => size.width * size.height,
        });
    }
}

proof fn lemma_coverage_below(m: Masks, n: nat)
    requires
        n <= m.table.len(),
    ensures
        i_coverage_below(costs_of(m), n) == live_bytes(m.table.subrange(0, n as int)),
    decreases n,
{
    let t = m.table.subrange(0, n as int);
    if n == 0 {
        assert(t.len() == 0);
    } else {
        let id = (n - 1) as nat;
        lemma_coverage_below(m, id);
        lemma_live_bytes_last(t);
        lemma_costs(m);
        assert(t.drop_last() =~= m.table.subrange(0, id as int));
        assert(t.last() == m.table[id as int]);
        assert(costs_of(m).contains_key(id) == (m.table[id as int] is Some));
    }
}

/// The two sums of a table agree.
proof fn lemma_live_coverage(m: Masks)
    requires
        m.table.len() == 0x10000,
    ensures
        i_live_coverage(costs_of(m)) == live_bytes(m.table),
{
    lemma_coverage_below(m, 0x10000);
    assert(m.table.subrange(0, 0x10000) =~= m.table);
}

// ---- Checking

/// One item: this file's step does what the spec's two steps do.
proof fn lemma_step(m: Masks, d: nat, item: Item)
    requires
        m.table.len() == 0x10000,
    ensures
        match (masks_after(m, item), clip_after(d, item)) {
            (Some(next_masks), Some(next_depth)) => {
                &&& next_masks.table.len() == 0x10000
                &&& i_step(Walk { depth: d, live: costs_of(m) }, cmd_of(item)) == Some(
                    Walk { depth: next_depth, live: costs_of(next_masks) },
                )
            },
            _ => i_step(Walk { depth: d, live: costs_of(m) }, cmd_of(item)) is None,
        },
{
    lemma_costs(m);
    match item {
        Item::UploadMask { id, columns, rows, .. } => {
            if (id as nat) < 0x10000 {
                let size = MaskSize { width: columns as nat, height: rows as nat };
                let updated = Masks { table: m.table.update(id as int, Some(size)) };
                lemma_costs(updated);
                assert(costs_of(m).contains_key(id as nat) == (m.table[id as int] is Some));
                let inserted = costs_of(m).insert(id as nat, columns as nat * rows as nat);
                assert forall|k: nat| #[trigger] costs_of(updated).dom().contains(k) == inserted.dom().contains(k) by {
                    if k < m.table.len() && k != id as nat {
                        assert(updated.table[k as int] == m.table[k as int]);
                    }
                }
                assert(costs_of(updated).dom() =~= inserted.dom());
                assert forall|k: nat| #[trigger] costs_of(updated).dom().contains(k) implies costs_of(updated)[k]
                    == inserted[k] by {
                    if k == id as nat {
                        assert(updated.table[k as int] == Some(size));
                    } else {
                        assert(updated.table[k as int] == m.table[k as int]);
                    }
                }
                assert(costs_of(updated) =~= inserted);
                lemma_live_coverage(updated);
            }
        },
        Item::DrawMask { id, .. } => {
            if (id as nat) < 0x10000 {
                assert(costs_of(m).contains_key(id as nat) == (m.table[id as int] is Some));
            }
        },
        Item::FreeMask { id } => {
            if (id as nat) < 0x10000 {
                assert(costs_of(m).contains_key(id as nat) == (m.table[id as int] is Some));
                let updated = Masks { table: m.table.update(id as int, None) };
                lemma_costs(updated);
                let removed = costs_of(m).remove(id as nat);
                assert forall|k: nat| #[trigger] costs_of(updated).dom().contains(k) == removed.dom().contains(k) by {
                    if k < m.table.len() && k != id as nat {
                        assert(updated.table[k as int] == m.table[k as int]);
                    }
                }
                assert(costs_of(updated).dom() =~= removed.dom());
                assert forall|k: nat| #[trigger] costs_of(updated).dom().contains(k) implies costs_of(updated)[k]
                    == removed[k] by {
                    assert(updated.table[k as int] == m.table[k as int]);
                }
                assert(costs_of(updated) =~= removed);
            }
        },
        _ => {},
    }
}

/// The function [`i_walk`] folds.
spec fn fold_step() -> spec_fn(Option<Walk>, Cmd) -> Option<Walk> {
    |s: Option<Walk>, c: Cmd|
        match s {
            Some(w) => i_step(w, c),
            None => None,
        }
}

proof fn lemma_refused_stays(cs: Seq<Cmd>)
    ensures
        cs.fold_left_alt(None, fold_step()) is None,
    decreases cs.len(),
{
    if cs.len() > 0 {
        lemma_refused_stays(cs.subrange(1, cs.len() as int));
        assert(cs[1..] =~= cs.subrange(1, cs.len() as int));
    }
}

/// The spec's walk from the front against the fold.
proof fn lemma_walk(m: Masks, d: nat, items: Seq<Item>)
    requires
        m.table.len() == 0x10000,
    ensures
        ({
            let out = cmds_of(items).fold_left_alt(Some(Walk { depth: d, live: costs_of(m) }), fold_step());
            match walk(m, d, items) {
                Some(r) => out == Some(Walk { depth: 0, live: costs_of(r) }),
                None => out is None || out.unwrap().depth != 0,
            }
        }),
    decreases items.len(),
{
    let cs = cmds_of(items);
    if items.len() > 0 {
        let tail = items.subrange(1, items.len() as int);
        assert(cs[0] == cmd_of(items[0]));
        assert(cs[1..] =~= cmds_of(tail));
        lemma_step(m, d, items[0]);
        match (masks_after(m, items[0]), clip_after(d, items[0])) {
            (Some(next_masks), Some(next_depth)) => {
                lemma_walk(next_masks, next_depth, tail);
            },
            _ => {
                lemma_refused_stays(cmds_of(tail));
            },
        }
    }
}

/// The checker as a fold is the spec's `validate`, for every list and every table of the
/// spec's fixed length. The spec indexes that table by id, so it says nothing of use for
/// another length; `masks_ok` asks for that length too.
pub proof fn theorem_check_equals_validate(masks: Masks, items: Seq<Item>)
    requires
        masks.table.len() == MAX_MASKS as nat,
    ensures
        i_check(cmds_of(items), costs_of(masks)) == match validate(masks, items) {
            None => None,
            Some(after) => Some(costs_of(after)),
        },
{
    let start = Walk { depth: 0, live: costs_of(masks) };
    let cs = cmds_of(items);
    cs.lemma_fold_left_alt(Some(start), fold_step());
    assert(fold_step() =~= (|s: Option<Walk>, c: Cmd|
        match s {
            Some(w) => i_step(w, c),
            None => None,
        }));
    assert(i_walk(cs, start) == cs.fold_left(Some(start), fold_step()));
    lemma_walk(masks, 0, items);
}

} // verus!

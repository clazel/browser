//! The control state table and the entry list, as executable values, and
//! the values of controls ([`control_value`]).

use super::read::*;
use super::strings::*;
use super::walk::*;
#[cfg(verus_only)]
use crate::contract::*;
use crate::spec::*;
use clazel_dom::exec::{Arena, ExecKind};
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A row of the control state table ([`ControlState`]); the coordinates of
/// a click are `u32`.
pub struct ExecControl {
    /// "value"
    pub value: Vec<u32>,
    /// "dirty value flag"
    pub dirty_value: bool,
    /// "checkedness"
    pub checked: bool,
    /// "dirty checkedness flag"
    pub dirty_checked: bool,
    /// An `option`'s "selectedness"
    pub selected: bool,
    /// The "selected coordinate", x
    pub x: u32,
    /// The "selected coordinate", y
    pub y: u32,
}

impl View for ExecControl {
    type V = ControlState;

    open spec fn view(&self) -> ControlState {
        ControlState {
            value: self.value@,
            dirty_value: self.dirty_value,
            checked: self.checked,
            dirty_checked: self.dirty_checked,
            selected: self.selected,
            x: self.x as nat,
            y: self.y as nat,
        }
    }
}

/// The view of a table.
pub open spec fn state_view(rows: Seq<ExecControl>) -> FormState {
    FormState { rows: rows.map_values(|c: ExecControl| c@) }
}

/// An entry ([`Entry`]).
pub struct ExecEntry {
    /// "name"
    pub name: Vec<u32>,
    /// "value"
    pub value: Vec<u32>,
}

impl View for ExecEntry {
    type V = Entry;

    open spec fn view(&self) -> Entry {
        Entry { name: self.name@, value: self.value@ }
    }
}

/// The view of an entry list.
pub open spec fn entries_view(v: Seq<ExecEntry>) -> Seq<Entry> {
    v.map_values(|e: ExecEntry| e@)
}

/// Appending one entry appends its view.
pub proof fn lemma_entries_push(v: Seq<ExecEntry>, e: ExecEntry)
    ensures
        entries_view(v.push(e)) == entries_view(v).push(e@),
{
    assert(entries_view(v.push(e)) =~= entries_view(v).push(e@));
}

/// A new entry.
pub fn mk_entry(name: &[u32], value: Vec<u32>) -> (r: ExecEntry)
    ensures
        r@ == create_entry(name@, value@),
{
    ExecEntry { name: copy_all(name), value }
}

/// A copy of `s`.
pub fn copy_all(s: &[u32]) -> (r: Vec<u32>)
    ensures
        r@ == s@,
{
    let r = copy_range(s, 0, s.len());
    proof {
        assert(s@.subrange(0, s.len() as int) =~= s@);
    }
    r
}

/// `s` followed by `c`.
pub fn concat1(s: &[u32], c: u32) -> (r: Vec<u32>)
    ensures
        r@ == s@.push(c),
{
    let mut r = copy_all(s);
    r.push(c);
    r
}

/// The control state of node `id`: [`control`], one field at a time.
pub fn row_dirty_value(rows: &[ExecControl], id: usize) -> (r: bool)
    ensures
        r == control(state_view(rows@), id).dirty_value,
{
    match rows.get(id) {
        Some(c) => c.dirty_value,
        None => false,
    }
}

/// [`control`]'s `dirty_checked`.
pub fn row_dirty_checked(rows: &[ExecControl], id: usize) -> (r: bool)
    ensures
        r == control(state_view(rows@), id).dirty_checked,
{
    match rows.get(id) {
        Some(c) => c.dirty_checked,
        None => false,
    }
}

/// [`control`]'s `checked`.
pub fn row_checked(rows: &[ExecControl], id: usize) -> (r: bool)
    ensures
        r == control(state_view(rows@), id).checked,
{
    match rows.get(id) {
        Some(c) => c.checked,
        None => false,
    }
}

/// [`control`]'s `selected`.
pub fn row_selected(rows: &[ExecControl], id: usize) -> (r: bool)
    ensures
        r == control(state_view(rows@), id).selected,
{
    match rows.get(id) {
        Some(c) => c.selected,
        None => false,
    }
}

/// [`control`]'s `x`.
pub fn row_x(rows: &[ExecControl], id: usize) -> (r: u32)
    ensures
        r as nat == control(state_view(rows@), id).x,
{
    match rows.get(id) {
        Some(c) => c.x,
        None => 0,
    }
}

/// [`control`]'s `y`.
pub fn row_y(rows: &[ExecControl], id: usize) -> (r: u32)
    ensures
        r as nat == control(state_view(rows@), id).y,
{
    match rows.get(id) {
        Some(c) => c.y,
        None => 0,
    }
}

/// [`control`]'s `value`.
pub fn row_value(rows: &[ExecControl], id: usize) -> (r: &[u32])
    ensures
        r@ == control(state_view(rows@), id).value,
{
    match rows.get(id) {
        Some(c) => c.value.as_slice(),
        None => &[],
    }
}

/// [`checkedness`].
pub fn checkedness_exec(arena: &Arena, rows: &[ExecControl], n: usize) -> (r: bool)
    requires
        is_element(arena@, n),
    ensures
        r == checkedness(arena@, state_view(rows@), n),
{
    if row_dirty_checked(rows, n) {
        row_checked(rows, n)
    } else {
        has_attr_exec(arena, n, b"checked")
    }
}

/// [`is_disabled`]: the control is a submittable element with the `disabled`
/// attribute, or is under a disabled `fieldset`.
pub fn is_disabled_exec(arena: &Arena, f: usize) -> (r: bool)
    requires
        dom::wf(arena@),
        dom::valid(arena@, f),
        is_submittable(arena@, f),
    ensures
        r == is_disabled(arena@, f),
{
    proof {
        assert(is_element(arena@, f));
    }
    has_attr_exec(arena, f, b"disabled") || fieldset_disables_exec(arena, f)
}

/// Concatenation is associative.
pub proof fn lemma_add_assoc(a: Seq<u32>, b: Seq<u32>, c: Seq<u32>)
    ensures
        (a + b) + c == a + (b + c),
{
    assert((a + b) + c =~= a + (b + c));
}

/// A copy of an ASCII keyword as code points.
pub fn ascii_vec(b: &[u8]) -> (r: Vec<u32>)
    ensures
        r@ == ascii(b@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i ==> (#[trigger] out@[k]) == b@[k] as u32,
        decreases b.len() - i,
    {
        if let Some(c) = b.get(i) {
            out.push(*c as u32);
        }
        // Never saturates: i < b.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(out@ =~= ascii(b@));
    }
    out
}

/// Append `s` to `out`.
pub fn append(out: &mut Vec<u32>, s: &[u32])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost start = out@;
    let mut j: usize = 0;
    while j < s.len()
        invariant
            j <= s.len(),
            out@ == start + s@.subrange(0, j as int),
        decreases s.len() - j,
    {
        if let Some(x) = s.get(j) {
            out.push(*x);
        }
        proof {
            assert(s@.subrange(0, j as int + 1) =~= s@.subrange(0, j as int).push(s@[j as int]));
        }
        // Never saturates: j < s.len().
        j = j.saturating_add(1);
    }
    proof {
        assert(s@.subrange(0, s.len() as int) =~= s@);
    }
}

/// The data of the `Text` children of a node, in order: [`child_text`].
pub fn child_text_exec(arena: &Arena, n: usize) -> (r: Vec<u32>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, n),
    ensures
        r@ == child_text(arena@, arena@.nodes[n as int].children),
{
    let kids = arena.children(n);
    let ghost doc = arena@;
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(kids@.skip(0) =~= kids@);
    }
    while i < kids.len()
        invariant
            i <= kids.len(),
            doc == arena@,
            kids@ == doc.nodes[n as int].children,
            dom::wf(doc),
            dom::valid(doc, n),
            out@ + child_text(doc, kids@.skip(i as int)) == child_text(doc, kids@),
        decreases kids.len() - i,
    {
        if let Some(c) = kids.get(i) {
            let c = *c;
            proof {
                lemma_child_valid(doc, n, i as int);
                assert(kids@.skip(i as int).drop_first() =~= kids@.skip(i as int + 1));
                assert(kids@.skip(i as int)[0] == kids@[i as int]);
            }
            let ghost before = out@;
            if let ExecKind::Text { data } = arena.kind(c) {
                append(&mut out, data.as_slice());
            }
            proof {
                let k = arena@.nodes[c as int].kind;
                let d = if k is Text {
                    k->Text_data
                } else {
                    Seq::<u32>::empty()
                };
                assert(out@ == before + d);
                let rest = child_text(doc, kids@.skip(i as int + 1));
                lemma_add_assoc(before, d, rest);
                assert(child_text(doc, kids@.skip(i as int)) == d + rest);
            }
        }
        // Never saturates: i < kids.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(kids@.skip(kids.len() as int) =~= Seq::<usize>::empty());
    }
    out
}

/// [`wrap_is_hard`].
pub fn wrap_is_hard_exec(arena: &Arena, n: usize) -> (r: bool)
    requires
        is_element(arena@, n),
    ensures
        r == wrap_is_hard(arena@, n),
{
    match attr_exec(arena, n, b"wrap") {
        Some(v) => ci_eq_exec(v.as_slice(), b"hard"),
        None => false,
    }
}

/// Wrapping a string no longer than the width changes nothing.
proof fn lemma_wrap_noop(s: Seq<u32>, cols: nat, col: nat)
    requires
        cols >= col + s.len(),
    ensures
        wrap_from(s, cols, col) == s,
    decreases s.len(),
{
    if s.len() > 0 {
        if s[0] == 0x0A {
            lemma_wrap_noop(s.drop_first(), cols, 0);
        } else {
            lemma_wrap_noop(s.drop_first(), cols, col + 1);
        }
        assert(s =~= seq![s[0]] + s.drop_first());
    }
}

/// The cut-off width gives the same wrapping as the width itself.
proof fn lemma_wrap_cols(nn: Seq<u32>, w: nat, cols: usize)
    requires
        cols as nat == if w > usize::MAX as nat {
            usize::MAX as nat
        } else {
            w
        },
        nn.len() <= usize::MAX as nat,
    ensures
        wrap_from(nn, cols as nat, 0) == wrap_from(nn, w, 0),
{
    if w > usize::MAX as nat {
        lemma_wrap_noop(nn, w, 0);
        lemma_wrap_noop(nn, usize::MAX as nat, 0);
    }
}

/// [`textarea_raw_value`]: the internal value, or the child text content.
pub fn textarea_raw_exec(arena: &Arena, rows: &[ExecControl], n: usize) -> (r: Vec<u32>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, n),
    ensures
        r@ == textarea_raw_value(arena@, state_view(rows@), n),
{
    if row_dirty_value(rows, n) {
        copy_all(row_value(rows, n))
    } else {
        child_text_exec(arena, n)
    }
}

/// [`textarea_wrapping`]: the wrapping transformation applied to `nn`.
pub fn textarea_wrapping_exec(arena: &Arena, n: usize, nn: Vec<u32>) -> (r: Vec<u32>)
    requires
        is_element(arena@, n),
    ensures
        r@ == textarea_wrapping(arena@, n, nn@),
{
    if wrap_is_hard_exec(arena, n) {
        let cols = match attr_exec(arena, n, b"cols") {
            Some(v) => character_width_exec(Some(v.as_slice())),
            None => character_width_exec(None),
        };
        let _l = nn.len();
        proof {
            assert(nn@.len() == _l as nat);
            lemma_wrap_cols(nn@, character_width(arena@, n), cols);
        }
        wrap_hard(nn.as_slice(), cols)
    } else {
        nn
    }
}

/// [`textarea_value`]: the raw value, newlines normalized, and wrapped for
/// the Hard state.
pub fn textarea_value_exec(arena: &Arena, rows: &[ExecControl], n: usize) -> (r: Vec<u32>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, n),
        is_element(arena@, n),
    ensures
        r@ == textarea_value(arena@, state_view(rows@), n),
{
    let raw = textarea_raw_exec(arena, rows, n);
    let nn = normalize_newlines_exec(raw.as_slice());
    textarea_wrapping_exec(arena, n, nn)
}

/// [`sanitize`] of the default value `v` for input state `t`.
pub fn sanitize_exec(t: &InputType, v: &[u32]) -> (r: Vec<u32>)
    ensures
        r@ == sanitize(*t, v@),
{
    match t {
        InputType::Text | InputType::Search | InputType::Tel | InputType::Password => strip_newlines_exec(v),
        InputType::Url | InputType::Email => {
            let a = strip_newlines_exec(v);
            strip_whitespace_exec(a.as_slice())
        },
        _ => copy_all(v),
    }
}

/// [`input_value`].
pub fn input_value_exec(arena: &Arena, rows: &[ExecControl], n: usize) -> (r: Vec<u32>)
    requires
        is_element(arena@, n),
    ensures
        r@ == input_value(arena@, state_view(rows@), n),
{
    let default_value: &[u32] = match attr_exec(arena, n, b"value") {
        Some(v) => v.as_slice(),
        None => &[],
    };
    let t = input_type_exec(arena, n);
    match t {
        InputType::Hidden | InputType::Submit | InputType::Image | InputType::Reset | InputType::Button
        | InputType::Checkbox | InputType::Radio | InputType::File => copy_all(default_value),
        _ => if row_dirty_value(rows, n) {
            copy_all(row_value(rows, n))
        } else {
            sanitize_exec(&t, default_value)
        },
    }
}

/// [`control_value`].
pub fn control_value_exec(arena: &Arena, rows: &[ExecControl], f: usize) -> (r: Vec<u32>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, f),
        is_element(arena@, f),
    ensures
        r@ == control_value(arena@, state_view(rows@), f),
{
    if is_html_exec(arena, f, b"textarea") {
        textarea_value_exec(arena, rows, f)
    } else if is_html_exec(arena, f, b"button") {
        match attr_exec(arena, f, b"value") {
            Some(v) => copy_all(v.as_slice()),
            None => Vec::new(),
        }
    } else {
        input_value_exec(arena, rows, f)
    }
}

} // verus!

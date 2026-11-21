//! "Constructing the entry list" (HTML §4.10.22.4): the entries of each
//! field, and the whole list.

use super::controls::*;
use super::entry::*;
use super::options::*;
use super::read::*;
use super::strings::*;
use super::walk::*;
#[cfg(verus_only)]
use crate::contract::*;
#[cfg(verus_only)]
use crate::lemmas::*;
use crate::spec::*;
use clazel_dom::exec::Arena;
#[cfg(verus_only)]
use clazel_dom::spec as dom;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The pieces of step 5, named (the same expressions as in `field_entries`)

/// Steps 5.2.2 to 5.2.7: the two entries of an image button.
pub open spec fn image_spec(doc: Document, st: FormState, field: NodeId) -> Seq<Entry> {
    let name = match attr(doc, field, b"name"@) {
        Some(v) => if v.len() > 0 {
            v + seq![0x2Eu32]
        } else {
            Seq::empty()
        },
        None => Seq::empty(),
    };
    seq![
        create_entry(name + seq![0x78u32], decimal(control(st, field).x)),
        create_entry(name + seq![0x79u32], decimal(control(st, field).y)),
    ]
}

/// Steps 5.6 to 5.10: the entries of a field named `name`.
pub open spec fn main_spec(doc: Document, st: FormState, encoding: Seq<u32>, field: NodeId, name: Seq<u32>) -> Seq<Entry> {
    let is_input = is_html(doc, field, b"input"@);
    let t = input_type(doc, field);
    if is_html(doc, field, b"select"@) {
        option_entries(doc, st, name, list_of_options(doc, field))
    } else if is_input && (t is Checkbox || t is Radio) {
        seq![create_entry(name, match attr(doc, field, b"value"@) {
            Some(v) => v,
            None => ascii(b"on"@),
        })]
    } else if is_input && t is File {
        Seq::empty()
    } else if is_input && t is Hidden && ci_eq(name, b"_charset_"@) {
        seq![create_entry(name, encoding)]
    } else {
        seq![create_entry(name, control_value(doc, st, field))]
    }
}

/// Step 5.11: the entry of the `dirname` attribute.
pub open spec fn dirname_spec(doc: Document, field: NodeId) -> Seq<Entry> {
    match attr(doc, field, b"dirname"@) {
        Some(d) => if d.len() > 0 && is_auto_directionality(doc, field) {
            seq![create_entry(d, ascii(b"ltr"@))]
        } else {
            Seq::empty()
        },
        None => Seq::empty(),
    }
}

/// Step 5.1's list of conditions.
pub open spec fn blocked_spec(doc: Document, st: FormState, submitter: Option<NodeId>, field: NodeId) -> bool {
    let is_input = is_html(doc, field, b"input"@);
    let t = input_type(doc, field);
    has_datalist_ancestor(doc, field) || is_disabled(doc, field) || (is_button(doc, field) && submitter != Some(field))
        || (is_input && t is Checkbox && !checkedness(doc, st, field)) || (is_input && t is Radio && !checkedness(
        doc,
        st,
        field,
    ))
}

/// [`field_entries`] by cases, as the implementation computes it.
pub proof fn lemma_field_cases(
    doc: Document,
    st: FormState,
    submitter: Option<NodeId>,
    encoding: Seq<u32>,
    field: NodeId,
)
    ensures
        field_entries(doc, st, submitter, encoding, field) == if blocked_spec(doc, st, submitter, field) {
            Seq::<Entry>::empty()
        } else if is_html(doc, field, b"input"@) && input_type(doc, field) is Image {
            if submitter != Some(field) {
                Seq::<Entry>::empty()
            } else {
                image_spec(doc, st, field)
            }
        } else {
            match attr(doc, field, b"name"@) {
                None => Seq::<Entry>::empty(),
                Some(name) => if name.len() == 0 {
                    Seq::<Entry>::empty()
                } else {
                    main_spec(doc, st, encoding, field, name) + dirname_spec(doc, field)
                },
            }
        },
{
}

// ---------------------------------------------------------------------
// Executable pieces

/// Whether `t` is the Checkbox state.
fn ty_checkbox(t: &InputType) -> (r: bool)
    ensures
        r == (*t is Checkbox),
{
    matches!(t, InputType::Checkbox)
}

/// Whether `t` is the Radio Button state.
fn ty_radio(t: &InputType) -> (r: bool)
    ensures
        r == (*t is Radio),
{
    matches!(t, InputType::Radio)
}

/// Whether `t` is the Image Button state.
fn ty_image(t: &InputType) -> (r: bool)
    ensures
        r == (*t is Image),
{
    matches!(t, InputType::Image)
}

/// Whether `t` is the File Upload state.
fn ty_file(t: &InputType) -> (r: bool)
    ensures
        r == (*t is File),
{
    matches!(t, InputType::File)
}

/// Whether `t` is the Hidden state.
fn ty_hidden(t: &InputType) -> (r: bool)
    ensures
        r == (*t is Hidden),
{
    matches!(t, InputType::Hidden)
}

/// Appending an entry appends its view.
fn push_entry(out: &mut Vec<ExecEntry>, e: ExecEntry)
    ensures
        entries_view(final(out)@) == entries_view(old(out)@).push(e@),
{
    let ghost before = out@;
    out.push(e);
    proof {
        lemma_entries_push(before, e);
    }
}

/// The entries of an image button (steps 5.2.2 to 5.2.7).
pub fn image_entries_exec(arena: &Arena, rows: &[ExecControl], field: usize) -> (r: Vec<ExecEntry>)
    requires
        is_element(arena@, field),
    ensures
        entries_view(r@) == image_spec(arena@, state_view(rows@), field),
{
    let named = attr_exec(arena, field, b"name");
    let nm: Vec<u32> = match named {
        Some(v) => if !v.is_empty() {
            concat1(v.as_slice(), 0x2E)
        } else {
            Vec::new()
        },
        None => Vec::new(),
    };
    proof {
        assert(nm@ == match attr(arena@, field, b"name"@) {
            Some(v) => if v.len() > 0 {
                v + seq![0x2Eu32]
            } else {
                Seq::empty()
            },
            None => Seq::empty(),
        });
        let name = nm@;
        assert(name.push(0x78u32) =~= name + seq![0x78u32]);
        assert(name.push(0x79u32) =~= name + seq![0x79u32]);
    }
    let namex = concat1(nm.as_slice(), 0x78);
    let namey = concat1(nm.as_slice(), 0x79);
    let vx = decimal_exec(row_x(rows, field));
    let vy = decimal_exec(row_y(rows, field));
    let mut out: Vec<ExecEntry> = Vec::new();
    proof {
        assert(entries_view(out@) =~= Seq::<Entry>::empty());
    }
    push_entry(&mut out, mk_entry(namex.as_slice(), vx));
    push_entry(&mut out, mk_entry(namey.as_slice(), vy));
    proof {
        assert(entries_view(out@) =~= image_spec(arena@, state_view(rows@), field));
    }
    out
}

/// [`option_disabled`].
pub fn option_disabled_exec(arena: &Arena, o: usize) -> (r: bool)
    requires
        dom::wf(arena@),
        dom::valid(arena@, o),
        is_element(arena@, o),
    ensures
        r == option_disabled(arena@, o),
{
    has_attr_exec(arena, o, b"disabled") || option_ancestors_exec(arena, o)
}

/// [`option_value`].
pub fn option_value_exec(arena: &Arena, rows: &[ExecControl], o: usize) -> (r: Vec<u32>)
    requires
        is_element(arena@, o),
    ensures
        r@ == option_value(arena@, state_view(rows@), o),
{
    match attr_exec(arena, o, b"value") {
        Some(v) => copy_all(v.as_slice()),
        None => copy_all(row_value(rows, o)),
    }
}

/// [`option_entries`]: one entry per selected, enabled option.
pub fn option_entries_exec(arena: &Arena, rows: &[ExecControl], name: &[u32], opts: &[usize]) -> (r: Vec<ExecEntry>)
    requires
        dom::wf(arena@),
        forall|k: int| 0 <= k < opts@.len() ==> is_html(arena@, #[trigger] opts@[k], b"option"@),
    ensures
        entries_view(r@) == option_entries(arena@, state_view(rows@), name@, opts@),
{
    let ghost doc = arena@;
    let ghost st = state_view(rows@);
    let mut out: Vec<ExecEntry> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(entries_view(out@) =~= Seq::<Entry>::empty());
        assert(opts@.subrange(0, 0) =~= Seq::<usize>::empty());
    }
    while i < opts.len()
        invariant
            i <= opts.len(),
            doc == arena@,
            dom::wf(doc),
            st == state_view(rows@),
            forall|k: int| 0 <= k < opts@.len() ==> is_html(doc, #[trigger] opts@[k], b"option"@),
            entries_view(out@) == option_entries(doc, st, name@, opts@.subrange(0, i as int)),
        decreases opts.len() - i,
    {
        if let Some(o) = opts.get(i) {
            let o = *o;
            proof {
                assert(opts@.subrange(0, i as int + 1).drop_last() =~= opts@.subrange(0, i as int));
                assert(opts@.subrange(0, i as int + 1).last() == opts@[i as int]);
                assert(is_html(doc, o, b"option"@));
            }
            if row_selected(rows, o) && !option_disabled_exec(arena, o) {
                let v = option_value_exec(arena, rows, o);
                push_entry(&mut out, mk_entry(name, v));
            }
        }
        // Never saturates: i < opts.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(opts@.subrange(0, opts.len() as int) =~= opts@);
    }
    out
}

/// Steps 5.6 to 5.10: [`main_spec`].
pub fn main_entries_exec(
    arena: &Arena,
    rows: &[ExecControl],
    encoding: &[u32],
    field: usize,
    name: &[u32],
) -> (r: Vec<ExecEntry>)
    requires
        dom::wf(arena@),
        dom::valid(arena@, field),
        is_element(arena@, field),
    ensures
        entries_view(r@) == main_spec(arena@, state_view(rows@), encoding@, field, name@),
{
    let is_input = is_html_exec(arena, field, b"input");
    let t = input_type_exec(arena, field);
    let mut out: Vec<ExecEntry> = Vec::new();
    proof {
        assert(entries_view(out@) =~= Seq::<Entry>::empty());
    }
    if is_html_exec(arena, field, b"select") {
        let opts = list_of_options_exec(arena, field);
        proof {
            lemma_options_in_is_filter(
                arena@,
                arena@.nodes[field as int].children,
                false,
                arena@.nodes.len(),
            );
            assert forall|k: int| 0 <= k < opts@.len() implies is_html(arena@, #[trigger] opts@[k], b"option"@) by {
                lemma_only_options_members(
                    arena@,
                    walk_in(arena@, arena@.nodes[field as int].children, false, arena@.nodes.len()),
                    opts@[k],
                );
            }
        }
        return option_entries_exec(arena, rows, name, opts.as_slice());
    } else if is_input && (ty_checkbox(&t) || ty_radio(&t)) {
        let v: Vec<u32> = match attr_exec(arena, field, b"value") {
            Some(v) => copy_all(v.as_slice()),
            None => {
                ascii_vec(b"on")
            },
        };
        push_entry(&mut out, mk_entry(name, v));
    } else if is_input && ty_file(&t) {
    } else if is_input && ty_hidden(&t) && ci_eq_exec(name, b"_charset_") {
        push_entry(&mut out, mk_entry(name, copy_all(encoding)));
    } else {
        let v = control_value_exec(arena, rows, field);
        push_entry(&mut out, mk_entry(name, v));
    }
    proof {
        assert(entries_view(out@) =~= main_spec(arena@, state_view(rows@), encoding@, field, name@));
    }
    out
}

/// Step 5.11: [`dirname_spec`].
pub fn dirname_entries_exec(arena: &Arena, field: usize) -> (r: Vec<ExecEntry>)
    requires
        dom::valid(arena@, field),
        is_element(arena@, field),
    ensures
        entries_view(r@) == dirname_spec(arena@, field),
{
    let mut out: Vec<ExecEntry> = Vec::new();
    proof {
        assert(entries_view(out@) =~= Seq::<Entry>::empty());
    }
    match attr_exec(arena, field, b"dirname") {
        Some(d) if !d.is_empty() && is_auto_directionality_exec(arena, field) => {
            let ltr: Vec<u32> = ascii_vec(b"ltr");
            push_entry(&mut out, mk_entry(d.as_slice(), ltr));
        },
        _ => {},
    }
    proof {
        assert(entries_view(out@) =~= dirname_spec(arena@, field));
    }
    out
}

/// The entries one field adds (step 5's body): [`field_entries`].
pub fn field_entries_exec(
    arena: &Arena,
    rows: &[ExecControl],
    submitter: Option<usize>,
    encoding: &[u32],
    field: usize,
) -> (r: Vec<ExecEntry>)
    requires
        field_entries_requires(arena@, submitter, field),
    ensures
        field_entries_ensures(
            arena@,
            state_view(rows@),
            submitter,
            encoding@,
            field,
            entries_view(r@),
        ),
{
    proof {
        assert(is_element(arena@, field));
        lemma_field_cases(arena@, state_view(rows@), submitter, encoding@, field);
        assert(entries_view(Seq::<ExecEntry>::empty()) =~= Seq::<Entry>::empty());
    }
    let is_input = is_html_exec(arena, field, b"input");
    let t = input_type_exec(arena, field);
    let is_sub = match submitter {
        Some(s) => s == field,
        None => false,
    };
    let blocked = datalist_exec(arena, field) || is_disabled_exec(arena, field) || (is_button_exec(arena, field)
        && !is_sub) || (is_input && ty_checkbox(&t) && !checkedness_exec(arena, rows, field)) || (is_input
        && ty_radio(&t) && !checkedness_exec(arena, rows, field));
    if blocked {
        return Vec::new();
    }
    if is_input && ty_image(&t) {
        if !is_sub {
            return Vec::new();
        }
        return image_entries_exec(arena, rows, field);
    }
    match attr_exec(arena, field, b"name") {
        None => Vec::new(),
        Some(name) => {
            if name.is_empty() {
                Vec::new()
            } else {
                let mut out = main_entries_exec(arena, rows, encoding, field, name.as_slice());
                let mut extra = dirname_entries_exec(arena, field);
                let ghost a = out@;
                let ghost b = extra@;
                out.append(&mut extra);
                proof {
                    assert(entries_view(out@) =~= entries_view(a) + entries_view(b));
                }
                out
            }
        },
    }
}

/// The view of an optional entry list.
pub open spec fn opt_entries_view(r: Option<Vec<ExecEntry>>) -> Option<Seq<Entry>> {
    match r {
        Some(v) => Some(entries_view(v@)),
        None => None,
    }
}

/// HTML "construct the entry list" for `form`, with the control state in
/// `rows`, an optional `submitter`, the name of the encoding and the
/// form's "constructing entry list" flag.
pub fn construct_entry_list_exec(
    arena: &Arena,
    rows: &[ExecControl],
    form: usize,
    submitter: Option<usize>,
    encoding: &[u32],
    constructing: bool,
) -> (r: Option<Vec<ExecEntry>>)
    requires
        construct_entry_list_requires(arena@, form, submitter),
    ensures
        construct_entry_list_ensures(
            arena@,
            state_view(rows@),
            form,
            submitter,
            encoding@,
            constructing,
            opt_entries_view(r),
        ),
{
    // 1. "If form's constructing entry list is true, then return null."
    if constructing {
        return None;
    }
    // 3. "Let controls be a list of all the submittable elements whose form
    // owner is form, in tree order."
    let ctrls = controls_exec(arena, form);
    let ghost doc = arena@;
    let ghost st = state_view(rows@);
    let ghost ord = tree_order(doc, root(doc, form), doc.nodes.len());
    let ghost cs = ctrls@;
    // 5. "For each element field in controls, in tree order: …"
    let mut out: Vec<ExecEntry> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(entries_view(out@) =~= Seq::<Entry>::empty());
        assert(cs.subrange(0, 0) =~= Seq::<usize>::empty());
        assert(cs == controls_in(doc, form, ord));
        assert forall|k: int| 0 <= k < cs.len() implies is_submittable(doc, #[trigger] cs[k]) by {
            assert(cs.contains(cs[k]));
            lemma_controls_members(doc, form, ord, cs[k]);
        }
    }
    while i < ctrls.len()
        invariant
            i <= ctrls.len(),
            doc == arena@,
            st == state_view(rows@),
            ctrls@ == cs,
            cs == controls(doc, form),
            dom::wf(doc),
            construct_entry_list_requires(doc, form, submitter),
            forall|k: int| 0 <= k < cs.len() ==> is_submittable(doc, #[trigger] cs[k]),
            entries_view(out@) == entries_of(doc, st, submitter, encoding@, cs.subrange(0, i as int)),
        decreases ctrls.len() - i,
    {
        if let Some(f) = ctrls.get(i) {
            let f = *f;
            proof {
                assert(cs.subrange(0, i as int + 1).drop_last() =~= cs.subrange(0, i as int));
                assert(cs.subrange(0, i as int + 1).last() == cs[i as int]);
                assert(is_submittable(doc, f));
            }
            let mut extra = field_entries_exec(arena, rows, submitter, encoding, f);
            let ghost a = out@;
            let ghost b = extra@;
            out.append(&mut extra);
            proof {
                assert(entries_view(out@) =~= entries_view(a) + entries_view(b));
            }
        }
        // Never saturates: i < ctrls.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(cs.subrange(0, cs.len() as int) =~= cs);
    }
    Some(out)
}

} // verus!

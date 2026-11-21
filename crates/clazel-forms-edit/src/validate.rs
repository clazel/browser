//! Constraint validation, `required` only (phase-6.md item 6.15).
//!
//! Sources: HTML §4.10.21 "Constraints" (§4.10.21.1 "Definitions": "candidate
//! for constraint validation", "suffering from being missing"; §4.10.21.3
//! "Interactively validating the constraints" for what the user agent does
//! with an invalid control, with "statically validate the constraints" and
//! "interactively validate the constraints" of §4.10.22.3 form submission
//! algorithm steps 5 and 6), the `required` attribute of each control
//! (§4.10.5.3.4 for `input`, §4.10.7 `select`, §4.10.11 `textarea`; the
//! numbers are the multipage build's and carry † in item 6.15's table).
//!
//! What is checked, per control, for a control that is a candidate for
//! constraint validation (not disabled, not `readonly`, not a button, not
//! Hidden, not in a `datalist`):
//! - a text-like `input` and a `textarea` with `required`: the value is
//!   empty;
//! - a checkbox with `required`: it is not checked;
//! - a radio button with `required`: no radio button of its group is checked;
//! - a `select` with `required`: no option is selected, or the only selected
//!   option is the placeholder label option (the first option, with an empty
//!   value, in a `select` without `multiple` whose display size is 1).
//!
//! Modelling choices (listed):
//! - **Only `required`.** `pattern` waits for a regular expression engine
//!   (Phase 7) and is ignored; `min`, `max`, `step`, `type=email` and `url`
//!   syntax, `minlength`, `maxlength` (the editing layer enforces the latter
//!   as the user types) and custom validity are not validated.
//! - **No message** is shown: the first invalid control, in tree order, gets
//!   the focus (the standard's "interactively validate" focuses the first one
//!   and reports its problem; the report is the browser chrome's, which this
//!   phase does not have).
//! - `type=file` and the other states HTML lists with no `required` are not
//!   checked.

use clazel_dom::exec::Arena;
use clazel_forms::exec::entry::{ExecControl, checkedness_exec};
use clazel_forms::exec::read::input_type_exec;
use clazel_forms::exec::walk::datalist_exec;
use clazel_forms::spec::InputType;
use clazel_layout::boxes::replaced::select_options;

use crate::dom::{attr, current_text, has, is, parse_integer};
use crate::focus::disabled;

/// Whether control `n` is suffering from being missing (the module's rules),
/// with `group` the radio buttons of `n`'s group.
pub fn value_missing(arena: &Arena, rows: &[ExecControl], n: usize, group: &[usize]) -> bool {
    // Candidates for constraint validation are not disabled and have no
    // `datalist` ancestor.
    if !has(arena, n, "required") || disabled(arena, n) || datalist_exec(arena, n) {
        return false;
    }
    if is(arena, n, "textarea") {
        return !has(arena, n, "readonly") && current_text(arena, rows, n).is_empty();
    }
    if is(arena, n, "select") {
        return select_missing(arena, rows, n);
    }
    if !is(arena, n, "input") {
        return false;
    }
    match input_type_exec(arena, n) {
        InputType::Checkbox => !checkedness_exec(arena, rows, n),
        InputType::Radio => !group.iter().any(|&r| checkedness_exec(arena, rows, r)),
        InputType::Hidden
        | InputType::File
        | InputType::Submit
        | InputType::Image
        | InputType::Reset
        | InputType::Button => false,
        _ => !has(arena, n, "readonly") && current_text(arena, rows, n).is_empty(),
    }
}

/// Whether `select` `sel`'s "display size" is 1 (HTML §4.10.7: the `size`
/// attribute's value when it parses as a positive integer, else 4 with
/// `multiple` and 1 without; here, the attribute at most 1 or absent). The
/// selectedness setting algorithm and the placeholder label option read it,
/// though the select is drawn as a list of its own number of rows.
pub fn display_size_is_1(arena: &Arena, sel: usize) -> bool {
    match attr(arena, sel, "size").and_then(|v| parse_integer(&v)) {
        Some(n) if n > 0 => n == 1,
        _ => !has(arena, sel, "multiple"),
    }
}

fn select_missing(arena: &Arena, rows: &[ExecControl], sel: usize) -> bool {
    let options = select_options(arena, sel);
    let selected: Vec<usize> = options
        .iter()
        .copied()
        .filter(|&o| rows.get(o).is_some_and(|r| r.selected))
        .collect();
    let multiple = has(arena, sel, "multiple");
    let placeholder = (!multiple && display_size_is_1(arena, sel))
        .then(|| options.first().copied())
        .flatten()
        .filter(|&o| option_value(arena, o).is_empty());
    match selected.as_slice() {
        [] => true,
        [only] => Some(*only) == placeholder,
        _ => false,
    }
}

/// An option's value: its `value` attribute, else its label text (HTML
/// §4.10.10 "value").
fn option_value(arena: &Arena, o: usize) -> String {
    attr(arena, o, "value")
        .unwrap_or_else(|| clazel_layout::boxes::replaced::option_label(arena, o))
}

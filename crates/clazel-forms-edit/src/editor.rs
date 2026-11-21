//! The editor: the state of every control of a document and what each user
//! event does to it (phase-6.md item 6.15).
//!
//! Sources: HTML §4.10.22.2 "Implicit submission" (a form's default button
//! is its first submit button in tree order; pressing Enter in a field that
//! blocks implicit submission fires a click at the default button unless it
//! is disabled, and with no default button submits only if the form has at
//! most one such field); §4.10.5.1.15 (checkbox) and §4.10.5.1.16 (radio
//! button) for toggling and the radio button group (§4.10.5.1.16 "radio
//! button group": same form owner, same tree, same non-empty `name`; "when
//! any of the radio buttons in a group becomes checked, all the other are
//! unchecked"); §4.10.7 for a `select`'s selectedness setting algorithm;
//! §4.10.22.3 steps 5 and 6 for validating before submitting; §4.10.18.1 the
//! dirty value flag, set by user input; the `readonly` attribute
//! (§4.10.5.3.? "the `readonly` attribute": the user cannot edit the value)
//! and `disabled` (§4.10.18.5).
//!
//! # Modelling choices (listed)
//!
//! - **State is `clazel-forms`' control state table** ([`Editor::rows`]):
//!   a user's edit writes the row's value and sets its dirty value flag, a
//!   toggle writes `checked` and its dirty flag, a `select` click writes the
//!   options' `selected`. Submission (`clazel-forms`' `submit_exec`) reads the
//!   same table, so what is drawn is what is sent. The caret, the selection
//!   and the focus are the editor's own.
//! - **The document does not change** under an [`Editor`] (no scripts until
//!   Phase 7): the form owners and the tree order are read once, in
//!   [`Editor::new`]. A new document gets a new editor.
//! - **Events are in CSS pixels of the document**, the scroll added by the
//!   caller; a click is a [`Event::Press`] followed by [`Event::Release`].
//!   Activation (a button's, a checkbox's) happens on the press.
//! - **The keyboard**: the editing keys of 6.0(f) are [`Key`]; typed text is
//!   [`Event::Text`], which 6.0(f)'s `TextInput` message carries (the kernel
//!   does not route it yet). A space typed with a checkbox, radio button,
//!   push button or `button` focused activates it; Enter on a push button or
//!   `button` activates it, and Enter in a one-line field is implicit
//!   submission. Arrow keys do not move between the radio buttons of a group
//!   and typing does not search a `select`'s options (listed).
//! - **A `select`** is drawn as a list; a click selects the row (toggling it
//!   when `multiple`: no Ctrl or Shift range clicks), and Up, Down, Home and
//!   End move the selection to the previous, next, first and last enabled
//!   option (selecting only that one, also when `multiple`).
//! - **A control reset** (`type=reset`, `button type=reset`) restores the
//!   table to the attributes for the form's controls (HTML §4.10.22.? "reset
//!   algorithm": values, checkedness and selectedness from the content
//!   attributes). No `reset` event.

use std::collections::HashMap;

use clazel_dom::exec::Arena;
use clazel_forms::exec::controls::controls_exec;
use clazel_forms::exec::entry::{ExecControl, checkedness_exec};
use clazel_forms::exec::read::input_type_exec;
use clazel_forms::spec::InputType;
use clazel_forms::submit::exec::submit::is_submit_button_exec;
use clazel_layout::boxes::replaced::select_options;
use clazel_layout::controls::{ControlView, Kind, kind_of};

use crate::dom::{attr, code_points, current_text, has, is, parse_non_negative, tree_order, valid};
use crate::field::{Field, normalize};
use crate::focus::{disabled, focusable, key, sequence};
use crate::validate::{display_size_is_1, value_missing};

/// What the layout tells the editor about a point of the page.
pub trait Geometry {
    /// The deepest element at (`x`, `y`) in CSS pixels of the document.
    fn node_at(&self, x: i32, y: i32) -> Option<usize>;
    /// The character index nearest to the point in text control `view`.
    fn caret_at(&self, view: &ControlView, x: i32, y: i32) -> Option<usize>;
    /// The index, among the `select`'s options, of the one at the point.
    fn option_at(&self, view: &ControlView, x: i32, y: i32) -> Option<usize>;
}

/// A page with no geometry: pointer events hit nothing. For the keyboard
/// alone.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoGeometry;

impl Geometry for NoGeometry {
    fn node_at(&self, _: i32, _: i32) -> Option<usize> {
        None
    }

    fn caret_at(&self, _: &ControlView, _: i32, _: i32) -> Option<usize> {
        None
    }

    fn option_at(&self, _: &ControlView, _: i32, _: i32) -> Option<usize> {
        None
    }
}

/// An editing key (6.0(f): `Input`'s key kind stays for these).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Key {
    /// Backspace.
    Backspace,
    /// Delete.
    Delete,
    /// Left arrow.
    Left,
    /// Right arrow.
    Right,
    /// Up arrow.
    Up,
    /// Down arrow.
    Down,
    /// Home.
    Home,
    /// End.
    End,
    /// Enter.
    Enter,
    /// Tab.
    Tab,
}

/// A user event.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// Typed text (6.0(f)'s `TextInput`).
    Text(String),
    /// An editing key; Shift extends the selection, and with Tab goes back.
    Key {
        /// The key.
        key: Key,
        /// Whether Shift is held.
        shift: bool,
    },
    /// The primary button went down at a point.
    Press {
        /// x in CSS pixels of the document.
        x: i32,
        /// y in CSS pixels of the document.
        y: i32,
        /// Whether Shift is held (it extends a selection).
        shift: bool,
    },
    /// The pointer moved with the button down.
    Drag {
        /// x in CSS pixels of the document.
        x: i32,
        /// y in CSS pixels of the document.
        y: i32,
    },
    /// The button went up.
    Release,
}

/// What the page should do after an event.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum Action {
    /// Nothing.
    #[default]
    None,
    /// Submit `form` with `submitter` (the form itself for an implicit
    /// submission with no button): `submit_exec(arena, rows, (form,
    /// submitter), …)`.
    Submit {
        /// The form element.
        form: usize,
        /// The submit button, or the form.
        submitter: usize,
    },
    /// The form was not submitted: `focus` is its first control with a
    /// missing required value, which now has the focus.
    Refused {
        /// The form element.
        form: usize,
        /// The control.
        focus: usize,
    },
}

/// The result of an event.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Outcome {
    /// Whether anything drawn may have changed (the page paints again).
    pub changed: bool,
    /// What the page does next.
    pub action: Action,
}

impl Outcome {
    fn changed() -> Outcome {
        Outcome {
            changed: true,
            action: Action::None,
        }
    }

    fn act(action: Action) -> Outcome {
        Outcome {
            changed: true,
            action,
        }
    }

    fn of(changed: bool) -> Outcome {
        Outcome {
            changed,
            action: Action::None,
        }
    }
}

/// The state of the controls of one document.
pub struct Editor {
    rows: Vec<ExecControl>,
    order: Vec<usize>,
    owners: HashMap<usize, usize>,
    focus: Option<usize>,
    fields: HashMap<usize, Field>,
    drag: Option<usize>,
}

fn clean() -> ExecControl {
    ExecControl {
        value: Vec::new(),
        dirty_value: false,
        checked: false,
        dirty_checked: false,
        selected: false,
        x: 0,
        y: 0,
    }
}

fn root_of(arena: &Arena, n: usize) -> usize {
    let mut at = n;
    // The arena is a tree: the walk ends within its size.
    for _ in 0..arena.len() {
        match arena.parent(at) {
            Some(p) => at = p,
            None => break,
        }
    }
    at
}

impl Editor {
    /// The editor of `arena`: every control in the state its content
    /// attributes give (the `select`s through the selectedness setting
    /// algorithm), nothing focused.
    pub fn new(arena: &Arena) -> Editor {
        let order = tree_order(arena);
        let mut owners = HashMap::new();
        for &f in &order {
            if is(arena, f, "form") {
                for c in controls_exec(arena, f) {
                    owners.entry(c).or_insert(f);
                }
            }
        }
        let mut e = Editor {
            rows: (0..arena.len()).map(|_| clean()).collect(),
            order,
            owners,
            focus: None,
            fields: HashMap::new(),
            drag: None,
        };
        let selects: Vec<usize> = e
            .order
            .iter()
            .copied()
            .filter(|&n| is(arena, n, "select"))
            .collect();
        for s in selects {
            e.init_select(arena, s);
        }
        e
    }

    /// The control state table, for the submission and the entry list.
    pub fn rows(&self) -> &[ExecControl] {
        &self.rows
    }

    /// The element with the focus.
    pub fn focus(&self) -> Option<usize> {
        self.focus
    }

    /// The editing state of text control `n`, once it has had the focus.
    pub fn field(&self, n: usize) -> Option<&Field> {
        self.fields.get(&n)
    }

    /// The form owner of control `n`.
    pub fn owner(&self, n: usize) -> Option<usize> {
        self.owners.get(&n).copied()
    }

    /// HTML §4.10.7's "selectedness setting algorithm", with the `selected`
    /// attributes as the options' default selectedness.
    fn init_select(&mut self, arena: &Arena, sel: usize) {
        let options = select_options(arena, sel);
        for &o in &options {
            if let Some(r) = self.rows.get_mut(o) {
                r.selected = has(arena, o, "selected");
            }
        }
        let on: Vec<usize> = options
            .iter()
            .copied()
            .filter(|&o| self.rows.get(o).is_some_and(|r| r.selected))
            .collect();
        if !has(arena, sel, "multiple") && on.len() > 1 {
            // "set the selectedness of all the option elements in the list of
            // options except the last … to false".
            for &o in on.iter().take(on.len().saturating_sub(1)) {
                if let Some(r) = self.rows.get_mut(o) {
                    r.selected = false;
                }
            }
        }
        if !has(arena, sel, "multiple") && display_size_is_1(arena, sel) && on.is_empty() {
            // "set the selectedness of the first option element in the list
            // of options in tree order that is not disabled, if any, to
            // true".
            if let Some(&o) = options.iter().find(|&&o| !has(arena, o, "disabled"))
                && let Some(r) = self.rows.get_mut(o)
            {
                r.selected = true;
            }
        }
    }

    /// The views of the controls, for `paint_with_controls`: every control,
    /// every `button`, and the focused element.
    pub fn views(&self, arena: &Arena) -> Vec<ControlView> {
        self.order
            .iter()
            .filter(|&&n| valid(arena, n))
            .filter(|&&n| {
                kind_of(arena, n) != Kind::Other || is(arena, n, "button") || self.focus == Some(n)
            })
            .map(|&n| self.view(arena, n))
            .collect()
    }

    /// The view of element `n`.
    pub fn view(&self, arena: &Arena, n: usize) -> ControlView {
        let kind = kind_of(arena, n);
        let field = self.fields.get(&n);
        let value = match (kind, field) {
            (Kind::Text { .. } | Kind::TextArea, Some(f)) => f.text(),
            (Kind::Text { .. } | Kind::TextArea | Kind::Push, _) => {
                current_text(arena, &self.rows, n)
            }
            _ => String::new(),
        };
        let selected = if kind == Kind::Select {
            select_options(arena, n)
                .into_iter()
                .filter(|&o| self.rows.get(o).is_some_and(|r| r.selected))
                .collect()
        } else {
            Vec::new()
        };
        ControlView {
            node: n,
            value,
            checked: matches!(kind, Kind::Check { .. }) && checkedness_exec(arena, &self.rows, n),
            selected,
            focused: self.focus == Some(n),
            disabled: disabled(arena, n),
            caret: field.map_or(0, |f| f.caret),
            selection: field.and_then(Field::selection),
        }
    }

    /// Handles `event`; `geo` answers where a pointer event landed.
    pub fn handle(&mut self, arena: &Arena, geo: &dyn Geometry, event: Event) -> Outcome {
        match event {
            Event::Text(s) => self.text(arena, &s),
            Event::Key { key, shift } => self.key(arena, key, shift),
            Event::Press { x, y, shift } => self.press(arena, geo, x, y, shift),
            Event::Drag { x, y } => self.drag_to(arena, geo, x, y),
            Event::Release => {
                self.drag = None;
                Outcome::of(false)
            }
        }
    }

    fn set_focus(&mut self, arena: &Arena, n: Option<usize>) -> bool {
        self.drag = None;
        if self.focus == n {
            return false;
        }
        self.focus = n;
        if let Some(n) = n
            && matches!(kind_of(arena, n), Kind::Text { .. } | Kind::TextArea)
            && !self.fields.contains_key(&n)
        {
            let text = current_text(arena, &self.rows, n);
            let multi = is(arena, n, "textarea");
            self.fields.insert(n, Field::new(normalize(&text, multi)));
        }
        true
    }

    /// Writes field `n`'s text to the control state (the dirty value flag).
    fn store(&mut self, n: usize) {
        let Some(f) = self.fields.get(&n) else { return };
        let text = code_points(&f.text());
        if let Some(r) = self.rows.get_mut(n) {
            r.value = text;
            r.dirty_value = true;
        }
    }

    fn text(&mut self, arena: &Arena, s: &str) -> Outcome {
        let Some(n) = self.focus else {
            return Outcome::of(false);
        };
        match kind_of(arena, n) {
            Kind::Text { .. } | Kind::TextArea => {
                if has(arena, n, "readonly") {
                    return Outcome::of(false);
                }
                let multi = is(arena, n, "textarea");
                let max = attr(arena, n, "maxlength").and_then(|v| parse_non_negative(&v));
                let typed: String = s
                    .chars()
                    .filter(|&c| !c.is_control() || c == '\n' || c == '\r')
                    .collect();
                let changed = self
                    .fields
                    .get_mut(&n)
                    .is_some_and(|f| f.insert(&typed, multi, max));
                if changed {
                    self.store(n);
                }
                Outcome::of(changed)
            }
            Kind::Check { .. } | Kind::Push | Kind::Other if s == " " => self.activate(arena, n),
            _ => Outcome::of(false),
        }
    }

    fn key(&mut self, arena: &Arena, key: Key, shift: bool) -> Outcome {
        if key == Key::Tab {
            return self.tab(arena, shift);
        }
        let Some(n) = self.focus else {
            return Outcome::of(false);
        };
        match kind_of(arena, n) {
            Kind::Text { .. } | Kind::TextArea => self.edit_key(arena, n, key, shift),
            Kind::Push | Kind::Other if key == Key::Enter && !is(arena, n, "a") => {
                self.activate(arena, n)
            }
            Kind::Select => self.select_key(arena, n, key),
            _ => Outcome::of(false),
        }
    }

    fn edit_key(&mut self, arena: &Arena, n: usize, key: Key, shift: bool) -> Outcome {
        let multi = is(arena, n, "textarea");
        let readonly = has(arena, n, "readonly");
        let max = attr(arena, n, "maxlength").and_then(|v| parse_non_negative(&v));
        let Some(f) = self.fields.get_mut(&n) else {
            return Outcome::of(false);
        };
        let before = f.clone();
        let edited = match key {
            Key::Backspace if !readonly => f.backspace(),
            Key::Delete if !readonly => f.delete(),
            Key::Enter if multi && !readonly => f.insert("\n", true, max),
            Key::Enter => return self.implicit_submission(arena, n),
            Key::Left => {
                f.left(shift);
                false
            }
            Key::Right => {
                f.right(shift);
                false
            }
            Key::Up => {
                f.up(shift, multi);
                false
            }
            Key::Down => {
                f.down(shift, multi);
                false
            }
            Key::Home => {
                f.home(shift);
                false
            }
            Key::End => {
                f.end(shift);
                false
            }
            _ => false,
        };
        let moved = *f != before;
        if edited {
            self.store(n);
        }
        Outcome::of(moved)
    }

    fn select_key(&mut self, arena: &Arena, sel: usize, key: Key) -> Outcome {
        let options = select_options(arena, sel);
        let enabled: Vec<usize> = options
            .iter()
            .copied()
            .filter(|&o| !has(arena, o, "disabled"))
            .collect();
        let current = options
            .iter()
            .position(|&o| self.rows.get(o).is_some_and(|r| r.selected));
        let pos_of = |o: usize| enabled.iter().position(|&e| e == o);
        let cur = current
            .and_then(|c| options.get(c).copied())
            .and_then(pos_of);
        let target = match (key, cur) {
            (Key::Up | Key::Left, Some(c)) => enabled.get(c.saturating_sub(1)).copied(),
            (Key::Down | Key::Right, Some(c)) => {
                enabled.get(c.saturating_add(1)).or(enabled.last()).copied()
            }
            (Key::Up | Key::Left | Key::Home, None) | (Key::Home, Some(_)) => {
                enabled.first().copied()
            }
            (Key::Down | Key::Right | Key::End, None) | (Key::End, Some(_)) => {
                enabled.last().copied()
            }
            _ => None,
        };
        let Some(t) = target else {
            return Outcome::of(false);
        };
        self.select_only(&options, t)
    }

    fn select_only(&mut self, options: &[usize], t: usize) -> Outcome {
        let mut changed = false;
        for &o in options {
            if let Some(r) = self.rows.get_mut(o) {
                let want = o == t;
                changed |= r.selected != want;
                r.selected = want;
            }
        }
        Outcome::of(changed)
    }

    fn press(&mut self, arena: &Arena, geo: &dyn Geometry, x: i32, y: i32, shift: bool) -> Outcome {
        let mut at = geo.node_at(x, y);
        let mut target = None;
        while let Some(n) = at {
            if focusable(arena, n).is_some() {
                target = Some(n);
                break;
            }
            at = arena.parent(n);
        }
        let moved = self.set_focus(arena, target);
        let Some(n) = target else {
            return Outcome::of(moved);
        };
        let view = self.view(arena, n);
        match kind_of(arena, n) {
            Kind::Text { .. } | Kind::TextArea => {
                if let Some(at) = geo.caret_at(&view, x, y)
                    && let Some(f) = self.fields.get_mut(&n)
                {
                    f.set_caret(at, shift);
                }
                self.drag = Some(n);
                Outcome::changed()
            }
            Kind::Select => {
                let options = select_options(arena, n);
                let Some(&o) = geo.option_at(&view, x, y).and_then(|i| options.get(i)) else {
                    return Outcome::of(moved);
                };
                if has(arena, o, "disabled") {
                    return Outcome::of(moved);
                }
                if has(arena, n, "multiple") {
                    if let Some(r) = self.rows.get_mut(o) {
                        r.selected = !r.selected;
                    }
                    Outcome::changed()
                } else {
                    self.select_only(&options, o);
                    Outcome::changed()
                }
            }
            Kind::Check { .. } | Kind::Push => self.activate(arena, n),
            Kind::Other if is(arena, n, "button") => self.activate(arena, n),
            Kind::Other => Outcome::of(moved),
        }
    }

    fn drag_to(&mut self, arena: &Arena, geo: &dyn Geometry, x: i32, y: i32) -> Outcome {
        let Some(n) = self.drag else {
            return Outcome::of(false);
        };
        let view = self.view(arena, n);
        let Some(at) = geo.caret_at(&view, x, y) else {
            return Outcome::of(false);
        };
        let Some(f) = self.fields.get_mut(&n) else {
            return Outcome::of(false);
        };
        let before = f.clone();
        f.set_caret(at, true);
        Outcome::of(*f != before)
    }

    /// Tab, or Shift-Tab, in tree order with `tabindex` (`focus.rs`).
    fn tab(&mut self, arena: &Arena, back: bool) -> Outcome {
        let seq: Vec<(usize, (bool, i64, usize))> = sequence(arena, &self.order)
            .into_iter()
            .filter(|&(n, _)| self.radio_stop(arena, n))
            .collect();
        let here = self.focus.and_then(|f| {
            let fo = focusable(arena, f)?;
            let idx = self.order.iter().position(|&n| n == f)?;
            Some(key(fo, idx))
        });
        let next = match (here, back) {
            (None, false) => seq.first(),
            (None, true) => seq.last(),
            (Some(k), false) => seq.iter().find(|&&(_, s)| s > k).or(seq.first()),
            (Some(k), true) => seq.iter().rev().find(|&&(_, s)| s < k).or(seq.last()),
        }
        .map(|&(n, _)| n);
        let moved = self.set_focus(arena, next);
        if moved && let Some(n) = next {
            // The caret goes to the end of a field reached by Tab.
            if let Some(f) = self.fields.get_mut(&n) {
                f.set_caret(f.chars.len(), false);
            }
        }
        Outcome::of(moved)
    }

    /// Whether radio button `n` (or any other element) is a tab stop: one
    /// per radio group (`focus.rs`).
    fn radio_stop(&self, arena: &Arena, n: usize) -> bool {
        if !(is(arena, n, "input") && matches!(input_type_exec(arena, n), InputType::Radio)) {
            return true;
        }
        let group = self.radio_group(arena, n);
        match group
            .iter()
            .find(|&&g| checkedness_exec(arena, &self.rows, g))
        {
            Some(&c) => c == n,
            None => group.first() == Some(&n),
        }
    }

    /// The radio buttons of `n`'s group in tree order: the same form owner,
    /// the same tree and the same non-empty `name`.
    fn radio_group(&self, arena: &Arena, n: usize) -> Vec<usize> {
        let name = attr(arena, n, "name").unwrap_or_default();
        if name.is_empty() {
            return vec![n];
        }
        let (owner, root) = (self.owner(n), root_of(arena, n));
        self.order
            .iter()
            .copied()
            .filter(|&m| {
                is(arena, m, "input")
                    && matches!(input_type_exec(arena, m), InputType::Radio)
                    && attr(arena, m, "name").as_deref() == Some(name.as_str())
                    && self.owner(m) == owner
                    && root_of(arena, m) == root
            })
            .collect()
    }

    /// A button's, checkbox's or radio button's activation behaviour.
    fn activate(&mut self, arena: &Arena, n: usize) -> Outcome {
        if disabled(arena, n) {
            return Outcome::of(false);
        }
        if is(arena, n, "input") {
            match input_type_exec(arena, n) {
                InputType::Checkbox => {
                    let on = checkedness_exec(arena, &self.rows, n);
                    if let Some(r) = self.rows.get_mut(n) {
                        r.checked = !on;
                        r.dirty_checked = true;
                    }
                    return Outcome::changed();
                }
                InputType::Radio => {
                    if checkedness_exec(arena, &self.rows, n) {
                        return Outcome::of(false);
                    }
                    for g in self.radio_group(arena, n) {
                        if let Some(r) = self.rows.get_mut(g) {
                            r.checked = g == n;
                            r.dirty_checked = true;
                        }
                    }
                    return Outcome::changed();
                }
                InputType::Reset => return self.reset(arena, n),
                _ => {}
            }
        }
        if is(arena, n, "button")
            && attr(arena, n, "type").is_some_and(|t| t.eq_ignore_ascii_case("reset"))
        {
            return self.reset(arena, n);
        }
        if (is(arena, n, "input") || is(arena, n, "button")) && is_submit_button_exec(arena, n) {
            return match self.owner(n) {
                Some(form) => self.submit(arena, form, n),
                None => Outcome::of(false),
            };
        }
        Outcome::of(false)
    }

    /// The reset button `n`'s form back to its attributes.
    fn reset(&mut self, arena: &Arena, n: usize) -> Outcome {
        let Some(form) = self.owner(n) else {
            return Outcome::of(false);
        };
        for c in controls_exec(arena, form) {
            if let Some(r) = self.rows.get_mut(c) {
                *r = clean();
            }
            self.fields.remove(&c);
            if is(arena, c, "select") {
                self.init_select(arena, c);
            }
            if self.focus == Some(c)
                && matches!(kind_of(arena, c), Kind::Text { .. } | Kind::TextArea)
            {
                let text = current_text(arena, &self.rows, c);
                let multi = is(arena, c, "textarea");
                self.fields.insert(c, Field::new(normalize(&text, multi)));
            }
        }
        Outcome::changed()
    }

    /// HTML §4.10.22.3 steps 5 and 6 before the navigation: unless the form
    /// or the submitter says not to validate, the first control with a
    /// missing required value gets the focus and the form is not submitted.
    fn submit(&mut self, arena: &Arena, form: usize, submitter: usize) -> Outcome {
        let skip = has(arena, form, "novalidate")
            || (submitter != form && has(arena, submitter, "formnovalidate"));
        if !skip {
            for c in controls_exec(arena, form) {
                let group = if is(arena, c, "input")
                    && matches!(input_type_exec(arena, c), InputType::Radio)
                {
                    self.radio_group(arena, c)
                } else {
                    Vec::new()
                };
                if value_missing(arena, &self.rows, c, &group) {
                    self.set_focus(arena, Some(c));
                    return Outcome::act(Action::Refused { form, focus: c });
                }
            }
        }
        Outcome::act(Action::Submit { form, submitter })
    }

    /// HTML §4.10.22.2 "Implicit submission" for Enter in text field `n`.
    fn implicit_submission(&mut self, arena: &Arena, n: usize) -> Outcome {
        let Some(form) = self.owner(n) else {
            return Outcome::of(false);
        };
        let controls = controls_exec(arena, form);
        // "A form element's default button is the first submit button in tree
        // order whose form owner is that form element."
        let default = controls
            .iter()
            .copied()
            .find(|&c| is_submit_button_exec(arena, c));
        if let Some(b) = default {
            // "…if the form has a default button that is not disabled, fire a
            // click event at it": its activation behaviour.
            return if disabled(arena, b) {
                Outcome::of(false)
            } else {
                self.activate(arena, b)
            };
        }
        // "If the form has no submit button, then the implicit submission
        // mechanism must perform the following steps: 1. If the form has more
        // than one field that blocks implicit submission, then return. 2.
        // Submit the form element from the form element itself."
        let blocking = controls
            .iter()
            .filter(|&&c| {
                is(arena, c, "input")
                    && matches!(
                        input_type_exec(arena, c),
                        InputType::Text
                            | InputType::Search
                            | InputType::Url
                            | InputType::Tel
                            | InputType::Email
                            | InputType::Password
                            | InputType::Other
                    )
            })
            .count();
        if blocking > 1 {
            return Outcome::of(false);
        }
        self.submit(arena, form, form)
    }
}

//! Per-control tests of item 6.15, driven by synthetic events (and, in
//! `input_messages`, by `Input` fields), against stored box tree dumps and
//! pixels (`tests/golden/`, regenerated with `CLAZEL_BLESS=1`; each stored
//! file was read against the geometry worked out in the comments here before
//! it was committed).
//!
//! The documents use `IdFont`: 10px glyphs, 10px advance, a 10px line, so a
//! `size=8` field is 80px wide and 10px high, and the text starts 2px in.

mod support;

use clazel_forms_edit::editor::{Action, Event, Key};
use clazel_forms_edit::input::{Surface, code, from_input};
use clazel_layout::paint::Item;
use support::*;

/// The glyph ids of every text item of the list.
fn glyph_ids(p: &Page) -> Vec<Vec<u16>> {
    p.paint()
        .items
        .iter()
        .filter_map(|i| match i {
            Item::Text { run, .. } => Some(run.glyphs.iter().map(|g| g.id).collect()),
            Item::Fill { .. } | Item::PushClip { .. } | Item::PopClip | Item::Image { .. } => None,
        })
        .collect()
}

/// The value of the first entry of form `f`.
fn first_value(p: &Page) -> String {
    p.entries("f")
        .first()
        .map(|e| e.1.clone())
        .unwrap_or_default()
}

fn ids(s: &str) -> Vec<u16> {
    s.chars()
        .map(|c| u16::try_from(u32::from(c)).unwrap_or(0))
        .collect()
}

const FIELD: &str = "<form id=f><div><input id=a size=8 value=hi></div></form>";

// ---- text field --------------------------------------------------------

#[test]
fn text_field_box_tree_and_unfocused_look() {
    let p = Page::new(FIELD);
    // §15.5.6: size=8 is 8 characters of 10px, one 10px line high.
    assert_eq!(p.rect("a"), (0, 0, 80, 10));
    golden("text-field.boxes.txt", &p.boxes());
    // A white box, the text "hi" from x=2, a 1px grey border, no caret.
    golden("text-field.unfocused.pixels.txt", &p.pixels(0, 0, 84, 12));
    // The display list: the canvas, then the control at its place.
    golden("text-field.unfocused.list.txt", &p.list());
    assert_eq!(glyph_ids(&p), vec![ids("hi")]);
}

#[test]
fn click_focuses_places_the_caret_and_typing_inserts() {
    let mut p = Page::new(FIELD);
    // Characters are 10px: "h" spans 2..12 and "i" 12..22. A click at x=14
    // is in the left half of "i": the caret goes between them.
    let o = p.click(14, 5);
    assert!(o.changed);
    assert_eq!(p.focus_id().as_deref(), Some("a"));
    assert_eq!(p.editor.field(p.id("a")).map(|f| f.caret), Some(1));
    p.text("XY");
    assert_eq!(p.value("a"), "hXYi");
    golden("text-field.typed.pixels.txt", &p.pixels(0, 0, 84, 12));
    // The control state is the table's: dirty value, so the entry list reads
    // the edit, not the attribute.
    assert_eq!(p.entries("f"), vec![]);
    let n = p.id("a");
    assert!(p.editor.rows().get(n).is_some_and(|r| r.dirty_value));
    // A click to the right of the text puts the caret at the end.
    p.click(70, 5);
    assert_eq!(p.editor.field(n).map(|f| f.caret), Some(4));
}

#[test]
fn editing_keys() {
    let mut p = Page::new("<form id=f><div><input id=a name=a size=8 value=abcd></div></form>");
    p.click(79, 5);
    p.key(Key::Backspace);
    assert_eq!(p.value("a"), "abc");
    p.key(Key::Home);
    p.key(Key::Delete);
    assert_eq!(p.value("a"), "bc");
    p.key(Key::Right);
    p.text("-");
    assert_eq!(p.value("a"), "b-c");
    p.key(Key::End);
    p.key(Key::Left);
    p.key(Key::Left);
    p.text("+");
    assert_eq!(p.value("a"), "b+-c");
    // Backspace at the start and Delete at the end change nothing.
    p.key(Key::Home);
    assert!(!p.key(Key::Backspace).changed);
    p.key(Key::End);
    assert!(!p.key(Key::Delete).changed);
    assert_eq!(p.entries("f"), vec![("a".to_owned(), "b+-c".to_owned())]);
    // Newlines in typed text are stripped from a one-line field; control
    // characters are dropped.
    p.text("x\ny\u{7}z");
    assert_eq!(p.value("a"), "b+-cxyz");
}

#[test]
fn selection_by_shift_and_replacing_it() {
    let mut p = Page::new("<form><div><input id=a size=8 value=abcdef></div></form>");
    p.click(79, 5);
    p.shift(Key::Left);
    p.shift(Key::Left);
    // "ef" is selected: caret 6 -> 4, anchor 6.
    assert_eq!(
        p.editor.field(p.id("a")).and_then(|f| f.selection()),
        Some((4, 6))
    );
    // The selection is drawn behind the text, from x=2+40 to 2+60, and no
    // caret.
    golden("text-field.selection.pixels.txt", &p.pixels(0, 0, 84, 12));
    p.text("Z");
    assert_eq!(p.value("a"), "abcdZ");
    // Shift+Home selects back to the start; Backspace removes it all.
    p.shift(Key::Home);
    p.key(Key::Backspace);
    assert_eq!(p.value("a"), "");
}

#[test]
fn selection_by_mouse_drag() {
    let mut p = Page::new("<form><div><input id=a size=8 value=abcdef></div></form>");
    // Boundary 1 (between "a" and "b") is at x=12 and boundary 4 at x=42.
    p.send(Event::Press {
        x: 12,
        y: 5,
        shift: false,
    });
    p.send(Event::Drag { x: 42, y: 5 });
    assert_eq!(
        p.editor.field(p.id("a")).and_then(|f| f.selection()),
        Some((1, 4))
    );
    // A drag moves only while the button is down.
    p.send(Event::Release);
    p.send(Event::Drag { x: 72, y: 5 });
    assert_eq!(
        p.editor.field(p.id("a")).and_then(|f| f.selection()),
        Some((1, 4))
    );
    golden("text-field.drag.pixels.txt", &p.pixels(0, 0, 84, 12));
    p.text("Z");
    assert_eq!(p.value("a"), "aZef");
    // Shift+click extends the selection from the caret.
    p.send(Event::Press {
        x: 62,
        y: 5,
        shift: true,
    });
    assert_eq!(
        p.editor.field(p.id("a")).and_then(|f| f.selection()),
        Some((2, 4))
    );
}

#[test]
fn maxlength_readonly_and_disabled() {
    let mut p = Page::new(
        "<form id=f><div><input id=a name=a size=8 maxlength=3 value=ab>\
         <input id=r name=r size=8 readonly value=ro>\
         <input id=d name=d size=8 disabled value=off></div></form>",
    );
    let (ax, ay, _, _) = p.rect("a");
    p.click(ax + 70, ay + 5);
    p.text("cdef");
    assert_eq!(p.value("a"), "abc");
    assert!(!p.text("g").changed);
    // A value longer than the limit is left alone until edited; editing only
    // removes (HTML §4.10.18.7: the limit constrains what the user adds).
    p.key(Key::Backspace);
    p.text("xyz");
    assert_eq!(p.value("a"), "abx");

    // Read-only: the caret moves and selects, nothing is typed or removed.
    p.click_in("r", Some(70));
    assert_eq!(p.focus_id().as_deref(), Some("r"));
    assert!(!p.text("no").changed);
    assert!(!p.key(Key::Backspace).changed);
    assert!(p.key(Key::Left).changed);
    assert_eq!(p.value("r"), "ro");

    // Disabled: a click does not focus it, and the look is greyed.
    p.click_in("d", None);
    assert_ne!(p.focus_id().as_deref(), Some("d"));
    golden("text-field.states.pixels.txt", &p.pixels(0, 0, 250, 12));
    // Disabled controls are not in the entry list; the others are.
    assert_eq!(
        p.entries("f"),
        vec![
            ("a".to_owned(), "abx".to_owned()),
            ("r".to_owned(), "ro".to_owned())
        ]
    );
}

#[test]
fn placeholder_and_password() {
    let mut p = Page::new(
        "<form id=f><div><input id=a size=8 placeholder=name>\
         <input id=b name=b type=password size=8 value=hunter2></div></form>",
    );
    // Empty: the placeholder, in grey; typing replaces it.
    assert_eq!(glyph_ids(&p).first(), Some(&ids("name")));
    golden(
        "text-field.placeholder.pixels.txt",
        &p.pixels(0, 0, 164, 12),
    );
    p.click_in("a", Some(50));
    p.text("z");
    assert_eq!(glyph_ids(&p).first(), Some(&ids("z")));
    // A password is drawn as one bullet per character, and sent as typed.
    let bullets = vec![0x2022u16; 7];
    assert_eq!(glyph_ids(&p).last(), Some(&bullets));
    assert_eq!(
        p.entries("f"),
        vec![
            ("b".to_owned(), "hunter2".to_owned()),
            // `a` has no name: not in the list.
        ]
        .into_iter()
        .collect::<Vec<_>>()
    );
}

#[test]
fn a_long_value_scrolls_to_keep_the_caret_in_view() {
    let mut p = Page::new("<form><div><input id=a size=4 value=0123456789></div></form>");
    p.click(39, 5);
    // 40px box, 2px of padding on the left: with the caret at the end (100px
    // of text) the text is shifted left so the caret is at the right edge.
    golden("text-field.scrolled.pixels.txt", &p.pixels(0, 0, 44, 12));
    // Home brings the start back.
    p.key(Key::Home);
    golden(
        "text-field.scrolled-home.pixels.txt",
        &p.pixels(0, 0, 44, 12),
    );
}

// ---- textarea ----------------------------------------------------------

const AREA: &str =
    "<form id=f><div><textarea id=t name=t cols=10 rows=3>one\ntwo</textarea></div></form>";

#[test]
fn textarea_lines_wrapping_and_editing() {
    let mut p = Page::new(AREA);
    // §15.5.17: 10 columns of 10px, 3 lines of 10px.
    assert_eq!(p.rect("t"), (0, 0, 100, 30));
    golden("textarea.boxes.txt", &p.boxes());
    // The parser drops the newline right after <textarea> only; "one\ntwo".
    assert_eq!(p.value("t"), "one\ntwo");
    assert_eq!(glyph_ids(&p), vec![ids("one"), ids("two")]);
    p.click(95, 25);
    // The click is on the second line (y 11..21 is line 2; 25 is below it:
    // the last line), to the right of "two": the caret is at the end.
    assert_eq!(p.editor.field(p.id("t")).map(|f| f.caret), Some(7));
    p.key(Key::Enter);
    p.text("3");
    assert_eq!(p.value("t"), "one\ntwo\n3");
    // Up and Down move between lines, keeping the column.
    p.key(Key::Up);
    p.key(Key::Up);
    assert_eq!(p.editor.field(p.id("t")).map(|f| f.caret), Some(1));
    p.key(Key::Down);
    assert_eq!(p.editor.field(p.id("t")).map(|f| f.caret), Some(5));
    // Enter submitted nothing: it is a newline in a textarea. The entry list
    // has the value with LF newlines (the encoders write CRLF, item 6.14).
    assert_eq!(
        p.entries("f"),
        vec![("t".to_owned(), "one\ntwo\n3".to_owned())]
    );
    golden("textarea.focused.pixels.txt", &p.pixels(0, 0, 104, 34));
}

#[test]
fn textarea_wraps_at_the_width_and_scrolls_to_the_caret() {
    let mut p = Page::new(
        "<form><div><textarea id=t cols=10 rows=2>aaaa bbbb cccc dddd eeee</textarea></div></form>",
    );
    p.click(2, 5);
    p.key(Key::Home);
    // The text area is 100px wide and the text starts 2px in, with 2px
    // kept at the right: 9 characters per row (`controls.rs`'s choice). A
    // row breaks after the last space that fits: "aaaa " | "bbbb " |
    // "cccc " | "dddd eeee". Two rows are shown (the box is 30px high, 28px
    // inside the border): the first two, the caret being on the first.
    golden("textarea.wrapped.pixels.txt", &p.pixels(0, 0, 104, 22));
    // Moving the caret to the end scrolls the last row into view: rows 3
    // and 4 ("cccc " and "dddd eeee") with the caret at the end of the
    // last, 2 + 90px in.
    p.key(Key::End);
    assert_eq!(p.editor.field(p.id("t")).map(|f| f.caret), Some(24));
    golden("textarea.wrapped-end.pixels.txt", &p.pixels(0, 0, 104, 22));
    // A click on the first shown row (y 1..11) at x=22, 2 + 2 characters in,
    // is in "cccc ": index 10 + 2.
    p.click(22, 5);
    assert_eq!(p.editor.field(p.id("t")).map(|f| f.caret), Some(12));
}

// ---- checkbox and radio ------------------------------------------------

const CHECKS: &str = "<form id=f><div>\
    <input id=c name=c type=checkbox value=on>\
    <input id=d name=d type=checkbox checked>\
    <input id=r1 name=r type=radio value=1>\
    <input id=r2 name=r type=radio value=2 checked>\
    <input id=r3 name=r type=radio value=3>\
    </div></form>";

#[test]
fn checkboxes_toggle_by_click_and_space() {
    let mut p = Page::new(CHECKS);
    golden("checks.boxes.txt", &p.boxes());
    assert_eq!(p.rect("c"), (0, 0, 13, 13));
    golden("checks.initial.pixels.txt", &p.pixels(0, 0, 80, 14));
    assert_eq!(
        p.entries("f"),
        vec![
            ("d".to_owned(), "on".to_owned()),
            ("r".to_owned(), "2".to_owned())
        ]
    );
    p.click_in("c", None);
    assert_eq!(p.focus_id().as_deref(), Some("c"));
    p.click_in("d", None);
    assert_eq!(
        p.entries("f"),
        vec![
            ("c".to_owned(), "on".to_owned()),
            ("r".to_owned(), "2".to_owned())
        ]
    );
    // Space toggles the focused box (the typed text " "): `d` has the focus.
    p.text(" ");
    let all = vec![
        ("c".to_owned(), "on".to_owned()),
        ("d".to_owned(), "on".to_owned()),
        ("r".to_owned(), "2".to_owned()),
    ];
    assert_eq!(p.entries("f"), all);
    // A click on `c` unchecks it and gives it the focus; Space checks it
    // again, and once more unchecks it.
    p.click_in("c", None);
    assert_eq!(p.entries("f").len(), 2);
    p.text(" ");
    assert_eq!(p.entries("f"), all);
    p.text(" ");
    assert_eq!(
        p.entries("f"),
        vec![
            ("d".to_owned(), "on".to_owned()),
            ("r".to_owned(), "2".to_owned())
        ]
    );
    golden("checks.toggled.pixels.txt", &p.pixels(0, 0, 80, 14));
}

#[test]
fn radio_buttons_of_a_group_exclude_each_other() {
    let mut p = Page::new(CHECKS);
    p.click_in("r1", None);
    assert_eq!(
        p.entries("f").last(),
        Some(&("r".to_owned(), "1".to_owned()))
    );
    p.click_in("r3", None);
    assert_eq!(
        p.entries("f").last(),
        Some(&("r".to_owned(), "3".to_owned()))
    );
    // Clicking the checked one again changes nothing.
    assert!(!p.click_in("r3", None).changed);
    // A radio button outside the form with the same name is another group.
    let mut q = Page::new(
        "<form id=f><div><input id=a name=r type=radio value=a></div></form>\
         <div><input id=b name=r type=radio value=b></div>",
    );
    q.click_in("a", None);
    q.click_in("b", None);
    assert_eq!(q.entries("f"), vec![("r".to_owned(), "a".to_owned())]);
}

#[test]
fn a_disabled_checkbox_does_not_toggle() {
    let mut p =
        Page::new("<form id=f><div><input id=c name=c type=checkbox disabled></div></form>");
    assert!(!p.click_in("c", None).changed);
    assert_eq!(p.entries("f"), vec![]);
    golden("checks.disabled.pixels.txt", &p.pixels(0, 0, 16, 14));
}

// ---- select ------------------------------------------------------------

const SELECT: &str = "<form id=f><div>\
    <select id=s name=s><option value=a>Alpha<option value=b>Beta<option value=c selected>Gamma</select>\
    <select id=m name=m multiple size=3><option value=1>One<option value=2 selected>Two\
    <option value=3 disabled>Three<option value=4>Four</select>\
    </div></form>";

#[test]
fn select_is_a_list_in_the_content_area() {
    let mut p = Page::new(SELECT);
    // A drop-down is drawn as the list it opens: 3 rows of 10px, as wide as
    // "Gamma" (5 characters), 4px more each way for the border and padding.
    assert_eq!(p.rect("s"), (0, 0, 54, 34));
    // The multiple select shows `size` rows: 3 rows, "Three" wide.
    assert_eq!(p.rect("m"), (54, 0, 54, 34));
    golden("select.boxes.txt", &p.boxes());
    golden("select.initial.pixels.txt", &p.pixels(0, 0, 110, 36));
    assert_eq!(
        p.entries("f"),
        vec![
            ("s".to_owned(), "c".to_owned()),
            ("m".to_owned(), "2".to_owned())
        ]
    );
    // A click on the first row of the single select selects only that
    // option (rows start 2px down, 10px each).
    p.click(10, 5);
    assert_eq!(first_value(&p), "a");
    // On the multiple select a click toggles the option; a disabled option
    // does not respond.
    p.click(60, 5);
    p.click(60, 25);
    assert_eq!(
        p.entries("f"),
        vec![
            ("s".to_owned(), "a".to_owned()),
            ("m".to_owned(), "1".to_owned()),
            ("m".to_owned(), "2".to_owned()),
        ]
    );
    golden("select.clicked.pixels.txt", &p.pixels(0, 0, 110, 36));
}

#[test]
fn select_keys_move_the_selection() {
    let mut p = Page::new(SELECT);
    p.click(10, 5);
    p.key(Key::Down);
    assert_eq!(first_value(&p), "b");
    p.key(Key::Down);
    p.key(Key::Down);
    assert_eq!(first_value(&p), "c");
    p.key(Key::Home);
    assert_eq!(first_value(&p), "a");
    p.key(Key::End);
    assert_eq!(first_value(&p), "c");
    p.key(Key::Up);
    assert_eq!(first_value(&p), "b");
    // Down in the multiple select skips the disabled option.
    p.click(60, 5);
    p.key(Key::Up);
    p.key(Key::Down);
    p.key(Key::Down);
    assert_eq!(
        p.entries("f").last(),
        Some(&("m".to_owned(), "4".to_owned()))
    );
}

#[test]
fn the_selectedness_setting_algorithm_picks_an_option() {
    // A drop-down with nothing selected selects its first enabled option; a
    // single select with two selected keeps the last.
    let p = Page::new(
        "<form id=f><div><select name=a><option disabled>x<option value=1>One<option value=2>Two</select>\
         <select name=b><option value=1 selected>One<option value=2 selected>Two</select></div></form>",
    );
    assert_eq!(
        p.entries("f"),
        vec![
            ("a".to_owned(), "1".to_owned()),
            ("b".to_owned(), "2".to_owned())
        ]
    );
}

// ---- buttons and focus -------------------------------------------------

#[test]
fn push_buttons_and_button_elements_are_drawn() {
    let mut p = Page::new(
        "<form id=f><div><input id=s type=submit><input id=r type=reset value=Clear>\
         <button id=b type=button>Go</button></div></form>",
    );
    golden("buttons.boxes.txt", &p.boxes());
    golden("buttons.initial.pixels.txt", &p.pixels(0, 0, 140, 12));
    // Tab to the first one: a ring.
    p.key(Key::Tab);
    assert_eq!(p.focus_id().as_deref(), Some("s"));
    golden("buttons.focused.pixels.txt", &p.pixels(0, 0, 140, 12));
}

const TABS: &str = "<form id=f><div>\
    <input id=n1 name=n1 size=2>\
    <input id=p2 name=p2 size=2 tabindex=2>\
    <input id=hid type=hidden name=h>\
    <input id=dis size=2 disabled>\
    <a id=link href=#x>go</a>\
    <input id=p1 size=2 tabindex=1>\
    <input id=neg size=2 tabindex=-1>\
    <div id=z tabindex=0>z</div>\
    <input id=n2 size=2>\
    </div></form>";

#[test]
fn tab_visits_positive_tabindex_first_then_tree_order() {
    let mut p = Page::new(TABS);
    let mut seen = Vec::new();
    for _ in 0..8 {
        p.key(Key::Tab);
        seen.push(p.focus_id().unwrap_or_default());
    }
    // tabindex 1, then 2, then (tabindex 0 and none) in tree order: n1, the
    // link, z, n2; the disabled, hidden and tabindex=-1 inputs are skipped;
    // after the last it wraps to the first.
    assert_eq!(seen, ["p1", "p2", "n1", "link", "z", "n2", "p1", "p2"]);
}

#[test]
fn shift_tab_goes_back_and_a_negative_tabindex_is_focusable_by_click() {
    let mut p = Page::new(TABS);
    p.shift(Key::Tab);
    assert_eq!(p.focus_id().as_deref(), Some("n2"));
    p.shift(Key::Tab);
    assert_eq!(p.focus_id().as_deref(), Some("z"));
    // A click focuses the tabindex=-1 input; Tab from it goes on in order
    // (as if it were at its tree position): after `neg` comes `z`.
    p.click_in("neg", None);
    assert_eq!(p.focus_id().as_deref(), Some("neg"));
    p.key(Key::Tab);
    assert_eq!(p.focus_id().as_deref(), Some("z"));
    p.click_in("neg", None);
    p.shift(Key::Tab);
    assert_eq!(p.focus_id().as_deref(), Some("link"));
    // A click on nothing focusable blurs.
    p.click(299, 119);
    assert_eq!(p.focus_id(), None);
}

#[test]
fn the_focus_ring_is_drawn_on_a_focused_link_and_element() {
    let mut p = Page::new(TABS);
    p.click_in("link", None);
    assert_eq!(p.focus_id().as_deref(), Some("link"));
    let (x, y, w, h) = p.rect("link");
    golden(
        "focus.link.pixels.txt",
        &p.pixels(x - 2, y - 2, w + 4, h + 4),
    );
    p.click_in("z", None);
    assert_eq!(p.focus_id().as_deref(), Some("z"));
    golden("focus.block.boxes.txt", &p.boxes());
    // The `div` with `tabindex=0` is a block: its ring is drawn over its
    // border box.
    let (x, y, w, h) = p.rect("z");
    golden("focus.block.pixels.txt", &p.pixels(x, y, 40.min(w), h));
}

#[test]
fn radio_groups_are_one_tab_stop() {
    let mut p = Page::new(CHECKS);
    let mut seen = Vec::new();
    for _ in 0..4 {
        p.key(Key::Tab);
        seen.push(p.focus_id().unwrap_or_default());
    }
    // c, d, then the checked radio r2 only, then back to c.
    assert_eq!(seen, ["c", "d", "r2", "c"]);
}

// ---- submission --------------------------------------------------------

#[test]
fn enter_submits_through_the_default_button() {
    let mut p = Page::new(
        "<form id=f action=/go><div><input id=a name=a size=8>\
         <input id=b type=submit name=b value=Send><input id=c type=submit name=c value=Other></div></form>",
    );
    p.click(30, 5);
    p.text("hello");
    let o = p.key(Key::Enter);
    // The default button is the first submit button in tree order.
    assert_eq!(action(&p, &o.action), "submit f by b");
}

#[test]
fn a_disabled_default_button_blocks_implicit_submission() {
    let mut p = Page::new(
        "<form id=f><div><input id=a name=a size=8>\
         <input id=b type=submit disabled><input id=c type=submit></div></form>",
    );
    p.click(30, 5);
    let o = p.key(Key::Enter);
    assert_eq!(action(&p, &o.action), "none");
}

#[test]
fn without_a_button_one_field_submits_and_two_do_not() {
    let mut p = Page::new("<form id=f><div><input id=a name=a size=8></div></form>");
    p.click(30, 5);
    let o = p.key(Key::Enter);
    assert_eq!(action(&p, &o.action), "submit f by f");
    let mut q = Page::new("<form id=f><div><input id=a size=8><input id=b size=8></div></form>");
    q.click(30, 5);
    let o = q.key(Key::Enter);
    assert_eq!(action(&q, &o.action), "none");
    // A hidden or checkbox control is not a field that blocks.
    let mut r = Page::new(
        "<form id=f><div><input id=a size=8><input type=hidden name=h><input type=checkbox></div></form>",
    );
    r.click(30, 5);
    let o = r.key(Key::Enter);
    assert_eq!(action(&r, &o.action), "submit f by f");
}

#[test]
fn a_button_click_submits_and_enter_on_a_button_clicks_it() {
    let mut p = Page::new(
        "<form id=f><div><input id=a name=a size=4 value=v><button id=b name=b value=1>Go</button>\
         <button id=k type=button>No</button></div></form>",
    );
    let o = p.click_in("b", None);
    assert_eq!(action(&p, &o.action), "submit f by b");
    let o = p.click_in("k", None);
    assert_eq!(action(&p, &o.action), "none");
    p.key(Key::Tab);
    p.key(Key::Tab);
    assert_eq!(p.focus_id().as_deref(), Some("b"));
    let o = p.key(Key::Enter);
    assert_eq!(action(&p, &o.action), "submit f by b");
    let o = p.text(" ");
    assert_eq!(action(&p, &o.action), "submit f by b");
}

#[test]
fn required_fields_refuse_the_submission_and_take_the_focus() {
    let mut p = Page::new(
        "<form id=f><div>\
         <input id=ok name=ok size=4 required value=x>\
         <input id=a name=a size=4 required>\
         <textarea id=t name=t required></textarea>\
         <input id=c type=checkbox name=c required>\
         <input id=s type=submit>\
         </div></form>",
    );
    let o = p.click_in("s", None);
    // The first control in tree order with a missing value.
    assert_eq!(action(&p, &o.action), "refused f focus a");
    assert_eq!(p.focus_id().as_deref(), Some("a"));
    p.text("v");
    let o = p.click_in("s", None);
    assert_eq!(action(&p, &o.action), "refused f focus t");
    p.text("w");
    let o = p.click_in("s", None);
    assert_eq!(action(&p, &o.action), "refused f focus c");
    p.text(" ");
    let o = p.click_in("s", None);
    assert_eq!(action(&p, &o.action), "submit f by s");
    // Enter in a field goes through the same check.
    p.click_in("a", None);
    p.key(Key::Home);
    p.shift(Key::End);
    p.key(Key::Delete);
    let o = p.key(Key::Enter);
    assert_eq!(action(&p, &o.action), "refused f focus a");
}

#[test]
fn novalidate_formnovalidate_readonly_disabled_and_radio_groups() {
    // `novalidate` on the form, and `formnovalidate` on the button.
    let mut p = Page::new(
        "<form id=f novalidate><div><input name=a required><input id=s type=submit></div></form>",
    );
    let o = p.click_in("s", None);
    assert_eq!(action(&p, &o.action), "submit f by s");
    let mut q = Page::new(
        "<form id=f><div><input name=a required><input id=s type=submit formnovalidate></div></form>",
    );
    let o = q.click_in("s", None);
    assert_eq!(action(&q, &o.action), "submit f by s");
    // A read-only or disabled required field is barred from validation.
    let mut r = Page::new(
        "<form id=f><div><input name=a required readonly><input name=b required disabled>\
         <input id=s type=submit></div></form>",
    );
    let o = r.click_in("s", None);
    assert_eq!(action(&r, &o.action), "submit f by s");
    // A required radio group is satisfied by any checked member.
    let mut g = Page::new(
        "<form id=f><div><input id=x type=radio name=g required><input id=y type=radio name=g required>\
         <input id=s type=submit></div></form>",
    );
    let o = g.click_in("s", None);
    assert_eq!(action(&g, &o.action), "refused f focus x");
    g.click_in("y", None);
    let o = g.click_in("s", None);
    assert_eq!(action(&g, &o.action), "submit f by s");
    // A required select whose only selected option is the placeholder label
    // option is missing.
    let mut h = Page::new(
        "<form id=f><div><select id=q name=q required><option value=''>Pick<option value=1>One</select>\
         <input id=s type=submit></div></form>",
    );
    let o = h.click_in("s", None);
    assert_eq!(action(&h, &o.action), "refused f focus q");
    h.click(10, 15);
    let o = h.click_in("s", None);
    assert_eq!(action(&h, &o.action), "submit f by s");
}

#[test]
fn pattern_is_ignored() {
    let mut p = Page::new(
        "<form id=f><div><input id=a name=a pattern='[0-9]+' value=abc><input id=s type=submit></div></form>",
    );
    let o = p.click_in("s", None);
    assert_eq!(action(&p, &o.action), "submit f by s");
}

#[test]
fn reset_restores_the_attributes() {
    let mut p = Page::new(
        "<form id=f><div><input id=a name=a size=4 value=orig><input id=c type=checkbox name=c>\
         <input id=r type=reset></div></form>",
    );
    p.click_in("a", Some(39));
    p.text("++");
    p.click_in("c", None);
    assert_eq!(
        p.entries("f"),
        vec![
            ("a".to_owned(), "orig++".to_owned()),
            ("c".to_owned(), "on".to_owned())
        ]
    );
    p.click_in("r", None);
    assert_eq!(p.entries("f"), vec![("a".to_owned(), "orig".to_owned())]);
    assert_eq!(p.value("a"), "orig");
}

#[test]
fn what_was_typed_is_what_the_submission_sends() {
    use clazel_encoding::labels::spec::Encoding;
    use clazel_forms::submit::exec::submit::{ExecOutcome, submit_exec};
    use clazel_url::url::parse::basic_url_parser;

    let mut p = Page::new(
        "<form id=f action=/search method=get><div><input id=q name=q size=8>\
         <input id=s type=submit></div></form>",
    );
    p.click_in("q", None);
    p.text("a b&c");
    let o = p.key(Key::Enter);
    let Action::Submit { form, submitter } = o.action else {
        unreachable!("no submission: {:?}", o.action)
    };
    let doc = u32s("http://example.com/dir/page");
    let Some(base) = basic_url_parser(&u32s("http://example.com/dir/"), None) else {
        unreachable!("base")
    };
    let out = submit_exec(
        &p.arena,
        p.editor.rows(),
        (form, submitter),
        Encoding::Utf8,
        &doc,
        &base,
        b"BND",
    );
    let ExecOutcome::Navigate(n) = out else {
        unreachable!("not a navigation")
    };
    let url: String = n
        .url
        .serialize(false)
        .iter()
        .filter_map(|&c| char::from_u32(c))
        .collect();
    assert_eq!(url, "http://example.com/search?q=a+b%26c");
}

// ---- Input messages ----------------------------------------------------

#[test]
fn input_messages_map_to_events() {
    let at = Surface {
        scale: 2,
        scroll_y: 100,
    };
    // A click at device (40, 10) at scale 2 with 100px of scroll: (20, 105).
    assert_eq!(
        from_input(0, 40, 10, 0, at),
        vec![
            Event::Press {
                x: 20,
                y: 105,
                shift: false
            },
            Event::Release
        ]
    );
    // Keys, with Shift in bit 16.
    assert_eq!(
        from_input(2, 0, 0, code::LEFT | (1 << 16), at),
        vec![Event::Key {
            key: Key::Left,
            shift: true
        }]
    );
    assert_eq!(
        from_input(2, 0, 0, code::TAB, at),
        vec![Event::Key {
            key: Key::Tab,
            shift: false
        }]
    );
    // A scroll, and a key the editor does not know, are not editor events.
    assert_eq!(from_input(1, 0, 0, 0, at), vec![]);
    assert_eq!(from_input(2, 0, 0, 999, at), vec![]);
    assert_eq!(
        from_input(4, 6, 8, 0, at),
        vec![Event::Drag { x: 3, y: 104 }]
    );
}

#[test]
fn a_page_driven_only_by_input_messages() {
    let mut p = Page::new("<form id=f><div><input id=a name=a size=8 value=abc></div></form>");
    let at = Surface {
        scale: 1,
        scroll_y: 0,
    };
    let run = |p: &mut Page, kind, x, y, key| {
        for e in from_input(kind, x, y, key, at) {
            p.send(e);
        }
    };
    run(&mut p, 0, 79, 5, 0);
    run(&mut p, 2, 0, 0, code::BACKSPACE);
    run(&mut p, 2, 0, 0, code::HOME);
    run(&mut p, 2, 0, 0, code::RIGHT | (1 << 16));
    assert_eq!(
        p.editor.field(p.id("a")).and_then(|f| f.selection()),
        Some((0, 1))
    );
    run(&mut p, 2, 0, 0, code::DELETE);
    assert_eq!(p.value("a"), "b");
    // Press, drag, release (the proposed kinds 3, 4, 5).
    run(&mut p, 3, 2, 5, 0);
    run(&mut p, 4, 79, 5, 0);
    run(&mut p, 5, 79, 5, 0);
    assert_eq!(
        p.editor.field(p.id("a")).and_then(|f| f.selection()),
        Some((0, 1))
    );
}

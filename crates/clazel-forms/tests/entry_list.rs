//! Hand-made cases of "constructing the entry list" (HTML §4.10.22.4), one
//! or two per step of the algorithm, through the tree builder and the proven
//! executable functions. The expected lists are written out from the
//! standard's steps, not from the implementation.

mod support;

use support::*;

#[test]
fn text_password_hidden_and_textarea_use_their_default_values() {
    let html = "<form id=f><input name=a value=1><input type=password name=b value=2>\
        <input type=hidden name=c value=3><textarea name=d>four</textarea>\
        <input name=e></form>";
    assert_eq!(
        entries_of(html, "f", None),
        pairs(&[("a", "1"), ("b", "2"), ("c", "3"), ("d", "four"), ("e", "")])
    );
}

#[test]
fn dirty_value_replaces_the_default() {
    let arena =
        parse("<form id=f><input id=i name=a value=1><textarea id=t name=b>x</textarea></form>");
    let mut rows = clean_rows(&arena);
    let (f, i, t) = (node(&arena, "f"), node(&arena, "i"), node(&arena, "t"));
    for (n, v) in [(i, "typed"), (t, "a\r\nb\rc\nd")] {
        if let Some(r) = rows.get_mut(n) {
            r.dirty_value = true;
            r.value = u32s(v);
        }
    }
    assert_eq!(
        entry_list(&arena, &rows, f, None, "UTF-8", false),
        Some(pairs(&[("a", "typed"), ("b", "a\nb\nc\nd")]))
    );
}

#[test]
fn missing_and_empty_names_contribute_nothing() {
    let html = "<form id=f><input value=1><input name='' value=2><input name=x value=3></form>";
    assert_eq!(entries_of(html, "f", None), pairs(&[("x", "3")]));
}

#[test]
fn disabled_controls_and_disabled_fieldsets() {
    let html = "<form id=f><input name=a disabled value=1>\
        <fieldset disabled><input name=b value=2>\
        <legend><input name=c value=3></legend>\
        <legend><input name=d value=4></legend>\
        <div><input name=e value=5></div></fieldset>\
        <fieldset><input name=g value=7></fieldset><input name=h value=8></form>";
    // c is under the first legend; d is under a second legend, which does
    // not count; b and e are plainly under the fieldset.
    assert_eq!(
        entries_of(html, "f", None),
        pairs(&[("c", "3"), ("g", "7"), ("h", "8")])
    );
}

#[test]
fn datalist_ancestors_are_skipped() {
    let html =
        "<form id=f><datalist><input name=a value=1></datalist><input name=b value=2></form>";
    assert_eq!(entries_of(html, "f", None), pairs(&[("b", "2")]));
}

#[test]
fn checkboxes_and_radios_need_checkedness_and_default_to_on() {
    let html = "<form id=f><input type=checkbox name=a checked><input type=checkbox name=b>\
        <input type=radio name=c value=v checked><input type=radio name=c value=w>\
        <input type=checkbox name=d value=''  checked></form>";
    assert_eq!(
        entries_of(html, "f", None),
        pairs(&[("a", "on"), ("c", "v"), ("d", "")])
    );
    // The dirty checkedness flag overrides the attribute.
    let arena = parse(
        "<form id=f><input id=i type=checkbox name=a checked><input id=j type=checkbox name=b></form>",
    );
    let mut rows = clean_rows(&arena);
    let (f, i, j) = (node(&arena, "f"), node(&arena, "i"), node(&arena, "j"));
    if let Some(r) = rows.get_mut(i) {
        r.dirty_checked = true;
        r.checked = false;
    }
    if let Some(r) = rows.get_mut(j) {
        r.dirty_checked = true;
        r.checked = true;
    }
    assert_eq!(
        entry_list(&arena, &rows, f, None, "UTF-8", false),
        Some(pairs(&[("b", "on")]))
    );
}

#[test]
fn buttons_are_included_only_as_the_submitter() {
    let html = "<form id=f><input name=foo>\
        <button name=close value=true>close</button>\
        <button type=button name=button value=true>b</button>\
        <button type=reset name=reset value=true>r</button>\
        <button id=s type=submit name=submit value=true>s</button>\
        <input type=submit id=t name=t2 value=go><input type=button name=u value=u></form>";
    assert_eq!(entries_of(html, "f", None), pairs(&[("foo", "")]));
    assert_eq!(
        entries_of(html, "f", Some("s")),
        pairs(&[("foo", ""), ("submit", "true")])
    );
    assert_eq!(
        entries_of(html, "f", Some("t")),
        pairs(&[("foo", ""), ("t2", "go")])
    );
}

#[test]
fn image_button_adds_coordinates_and_only_as_the_submitter() {
    let html = "<form id=f><input type=image id=a name=pic><input type=image id=b></form>";
    let arena = parse(html);
    let mut rows = clean_rows(&arena);
    let (f, a, b) = (node(&arena, "f"), node(&arena, "a"), node(&arena, "b"));
    for (n, x, y) in [(a, 12, 345), (b, 7, 0)] {
        if let Some(r) = rows.get_mut(n) {
            r.x = x;
            r.y = y;
        }
    }
    assert_eq!(
        entry_list(&arena, &rows, f, None, "UTF-8", false),
        Some(vec![])
    );
    assert_eq!(
        entry_list(&arena, &rows, f, Some(a), "UTF-8", false),
        Some(pairs(&[("pic.x", "12"), ("pic.y", "345")]))
    );
    // No name: the names are "x" and "y" with no prefix.
    assert_eq!(
        entry_list(&arena, &rows, f, Some(b), "UTF-8", false),
        Some(pairs(&[("x", "7"), ("y", "0")]))
    );
}

#[test]
fn charset_hidden_input_carries_the_encoding_name() {
    let arena = parse(
        "<form id=f><input type=hidden name=_CharSet_ value=ignored><input type=text name=_charset_ value=t></form>",
    );
    let rows = clean_rows(&arena);
    let f = node(&arena, "f");
    assert_eq!(
        entry_list(&arena, &rows, f, None, "windows-1252", false),
        Some(pairs(&[("_CharSet_", "windows-1252"), ("_charset_", "t")]))
    );
}

#[test]
fn dirname_adds_ltr_for_auto_directionality_controls() {
    let html = "<form id=f><input name=a dirname=a.dir value=x><textarea name=b dirname=b.dir>y</textarea>\
        <input name=c dirname='' value=z><input type=checkbox name=d dirname=d.dir checked>\
        <input name=e dirname=e.dir disabled></form>";
    assert_eq!(
        entries_of(html, "f", None),
        pairs(&[
            ("a", "x"),
            ("a.dir", "ltr"),
            ("b", "y"),
            ("b.dir", "ltr"),
            ("c", "z"),
            ("d", "on"),
        ])
    );
}

#[test]
fn value_sanitization_follows_the_input_type() {
    let html = "<form id=f><input name=a value='  a\nb  '>\
        <input type=email name=b value='  a@b\nc  '><input type=url name=c value=' http://x\n '>\
        <input type=number name=d value=' 5'><input type=search name=e value='s\r\nt'></form>";
    assert_eq!(
        entries_of(html, "f", None),
        pairs(&[
            ("a", "  ab  "),
            ("b", "a@bc"),
            ("c", "http://x"),
            ("d", " 5"),
            ("e", "st"),
        ])
    );
}

#[test]
fn textarea_wrapping_and_newlines() {
    let arena = parse(
        "<form id=f><textarea id=h name=h wrap=HARD cols=4></textarea>\
         <textarea id=s name=s wrap=soft cols=4></textarea>\
         <textarea id=d name=d wrap=hard></textarea></form>",
    );
    let mut rows = clean_rows(&arena);
    let (f, h, s, d) = (
        node(&arena, "f"),
        node(&arena, "h"),
        node(&arena, "s"),
        node(&arena, "d"),
    );
    for (n, v) in [(h, "abcdefghij\r\nkl"), (s, "abcdefghij"), (d, "x")] {
        if let Some(r) = rows.get_mut(n) {
            r.dirty_value = true;
            r.value = u32s(v);
        }
    }
    assert_eq!(
        entry_list(&arena, &rows, f, None, "UTF-8", false),
        Some(pairs(&[
            ("h", "abcd\nefgh\nij\nkl"),
            ("s", "abcdefghij"),
            ("d", "x")
        ]))
    );
}

#[test]
fn select_lists_selected_enabled_options_in_order() {
    let arena = parse(
        "<form id=f><select name=s multiple>\
         <option id=o1 value=one>One\
         <optgroup id=g label=G><option id=o2>Two <b>bold</b>\
         <option id=o3 value=three disabled></optgroup>\
         <optgroup disabled><option id=o4 value=four></optgroup>\
         <option id=o5 value=five></select>\
         <select name=t><option id=p1 value=a><option id=p2 value=b></select></form>",
    );
    let mut rows = clean_rows(&arena);
    let (f, o1, o2, o3, o4, o5, p2) = (
        node(&arena, "f"),
        node(&arena, "o1"),
        node(&arena, "o2"),
        node(&arena, "o3"),
        node(&arena, "o4"),
        node(&arena, "o5"),
        node(&arena, "p2"),
    );
    for n in [o1, o2, o3, o4, o5, p2] {
        if let Some(r) = rows.get_mut(n) {
            r.selected = true;
        }
    }
    // o2 has no value attribute: its text comes from the table.
    if let Some(r) = rows.get_mut(o2) {
        r.value = u32s("Two bold");
    }
    // o3 is disabled, o4 is in a disabled optgroup.
    assert_eq!(
        entry_list(&arena, &rows, f, None, "UTF-8", false),
        Some(pairs(&[
            ("s", "one"),
            ("s", "Two bold"),
            ("s", "five"),
            ("t", "b")
        ]))
    );
}

#[test]
fn options_under_a_datalist_inside_a_select_are_not_listed() {
    // "list of options" does not enter a datalist (nor an hr, an option or
    // a select); an optgroup inside an optgroup cannot be made by the parser.
    let arena = parse(
        "<form id=f><select name=s multiple><datalist><option id=x value=hidden></datalist>         <option id=y value=shown></select></form>",
    );
    let mut rows = clean_rows(&arena);
    let f = node(&arena, "f");
    for id in ["x", "y"] {
        if let Some(r) = rows.get_mut(node(&arena, id)) {
            r.selected = true;
        }
    }
    assert_eq!(
        entry_list(&arena, &rows, f, None, "UTF-8", false),
        Some(pairs(&[("s", "shown")]))
    );
}

#[test]
fn form_owner_is_the_nearest_ancestor_or_the_form_attribute() {
    let html = "<form id=a><input name=in_a value=1><input name=moved form=b value=2></form>\
        <form id=b><input name=in_b value=3></form>\
        <input name=outside form=a value=4><input name=nowhere value=5>\
        <input name=missing form=nosuch value=6><div id=notform></div><input name=div form=notform value=7>";
    assert_eq!(
        entries_of(html, "a", None),
        pairs(&[("in_a", "1"), ("outside", "4")])
    );
    assert_eq!(
        entries_of(html, "b", None),
        pairs(&[("moved", "2"), ("in_b", "3")])
    );
}

#[test]
fn the_first_element_with_the_id_must_be_the_form() {
    // Two elements with id=a: the div comes first, so form=a names no form.
    let html = "<div id=a></div><form id=a><input name=x form=a value=1></form><input name=y form=a value=2>";
    let arena = parse(html);
    let rows = clean_rows(&arena);
    // The form is the second element with id "a": find it by its tag.
    let mut stack = vec![0usize];
    let mut forms = Vec::new();
    while let Some(n) = stack.pop() {
        if let clazel_dom::exec::ExecKind::Element { local_name, .. } = arena.kind(n)
            && *local_name == u32s("form")
        {
            forms.push(n);
        }
        stack.extend(arena.children(n).iter().rev());
    }
    assert_eq!(forms.len(), 1);
    let f = forms.first().copied().unwrap_or(0);
    // x is inside the form but its form attribute names the div: no owner.
    // y: the same. So the form's entry list is empty.
    assert_eq!(
        entry_list(&arena, &rows, f, None, "UTF-8", false),
        Some(vec![])
    );
}

#[test]
fn parser_association_survives_a_closed_form_in_a_table() {
    // `</form>` inside a table sets the form element pointer to null while
    // the form is still open; the input after it is created with no owner and
    // takes the nearest ancestor form instead (the insertion steps' reset).
    let html =
        "<form id=f><table><tr><td><input name=a value=1></form><input name=b value=2></table>";
    assert_eq!(
        entries_of(html, "f", None),
        pairs(&[("a", "1"), ("b", "2")])
    );
}

#[test]
fn constructing_flag_returns_null() {
    let arena = parse("<form id=f><input name=a></form>");
    let rows = clean_rows(&arena);
    let f = node(&arena, "f");
    assert_eq!(entry_list(&arena, &rows, f, None, "UTF-8", true), None);
}

#[test]
fn controls_in_template_contents_are_not_in_the_forms_tree() {
    let html =
        "<form id=f><template><input name=t value=1></template><input name=a value=2></form>";
    assert_eq!(entries_of(html, "f", None), pairs(&[("a", "2")]));
}

#[test]
fn file_inputs_and_unknown_types() {
    let html = "<form id=f><input type=file name=a><input type=date name=b value=2026-01-02>\
        <input type=bogus name=c value=x></form>";
    assert_eq!(
        entries_of(html, "f", None),
        pairs(&[("b", "2026-01-02"), ("c", "x")])
    );
}

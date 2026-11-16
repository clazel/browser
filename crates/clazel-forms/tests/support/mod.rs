//! Helpers of the tests: parse HTML with the tree builder, find elements,
//! and compute an entry list as (name, value) strings.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_forms::exec::entry::ExecControl;
use clazel_forms::exec::fields::construct_entry_list_exec;
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

/// The encoding functions the tree builder calls for `<meta charset>`: the
/// documents are parsed with a certain encoding, so they never change the
/// tree.
struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

/// A string as code points.
pub fn u32s(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

/// Code points as a string.
pub fn text(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// Parse a document.
pub fn parse(html: &str) -> Arena {
    let input = u32s(html);
    let (p, _) = parse_real(&NoEnc, &input, Vec::new(), false, false);
    p.arena
}

/// A clean row of the control state table.
pub fn row() -> ExecControl {
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

/// A table with a clean row for every node.
pub fn clean_rows(arena: &Arena) -> Vec<ExecControl> {
    (0..arena.len()).map(|_| row()).collect()
}

/// The first element, in tree order, whose `id` attribute is `id`.
pub fn by_id(arena: &Arena, id: &str) -> Option<usize> {
    let want = u32s(id);
    let mut stack = vec![0usize];
    while let Some(n) = stack.pop() {
        if let ExecKind::Element { attributes, .. } = arena.kind(n)
            && attributes
                .iter()
                .any(|a| a.namespace.is_none() && a.local_name == u32s("id") && a.value == want)
        {
            return Some(n);
        }
        stack.extend(arena.children(n).iter().rev());
    }
    None
}

/// The element with id `id` (the test fails if there is none).
pub fn node(arena: &Arena, id: &str) -> usize {
    let r = by_id(arena, id);
    assert!(r.is_some(), "no element with id {id}");
    r.unwrap_or(0)
}

/// The entry list of `form` as (name, value) strings; `None` if the form's
/// "constructing entry list" flag is set.
pub fn entry_list(
    arena: &Arena,
    rows: &[ExecControl],
    form: usize,
    submitter: Option<usize>,
    encoding: &str,
    constructing: bool,
) -> Option<Vec<(String, String)>> {
    construct_entry_list_exec(arena, rows, form, submitter, &u32s(encoding), constructing).map(
        |v| {
            v.iter()
                .map(|e| (text(&e.name), text(&e.value)))
                .collect::<Vec<_>>()
        },
    )
}

/// `entry_list` of the form with id `form` and the submitter with id
/// `submitter`, with clean control state and encoding UTF-8.
pub fn entries_of(html: &str, form: &str, submitter: Option<&str>) -> Vec<(String, String)> {
    let arena = parse(html);
    let rows = clean_rows(&arena);
    let Some(f) = by_id(&arena, form) else {
        return vec![("no such form".to_owned(), form.to_owned())];
    };
    let s = submitter.and_then(|id| by_id(&arena, id));
    entry_list(&arena, &rows, f, s, "UTF-8", false).unwrap_or_default()
}

/// Entries as `(name, value)` pairs of `&str`, for comparison.
pub fn pairs(v: &[(&str, &str)]) -> Vec<(String, String)> {
    v.iter()
        .map(|(a, b)| ((*a).to_owned(), (*b).to_owned()))
        .collect()
}

//! Small reads of the DOM that editing needs, over `clazel-forms`'
//! executable readers.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_forms::exec::entry::ExecControl;
use clazel_forms::exec::read::{attr_exec, has_attr_exec, is_html_exec};

/// Code points to a `String`.
pub fn string(s: &[u32]) -> String {
    s.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

/// A string as code points.
pub fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// Whether `n` is an element of `arena`.
pub fn valid(arena: &Arena, n: usize) -> bool {
    n < arena.len() && matches!(arena.kind(n), ExecKind::Element { .. })
}

/// Whether `n` is an HTML element named `name`.
pub fn is(arena: &Arena, n: usize, name: &str) -> bool {
    valid(arena, n) && is_html_exec(arena, n, name.as_bytes())
}

/// Whether `n` has attribute `name`.
pub fn has(arena: &Arena, n: usize, name: &str) -> bool {
    valid(arena, n) && has_attr_exec(arena, n, name.as_bytes())
}

/// The value of attribute `name` of `n`.
pub fn attr(arena: &Arena, n: usize, name: &str) -> Option<String> {
    if !valid(arena, n) {
        return None;
    }
    attr_exec(arena, n, name.as_bytes()).map(|v| string(v))
}

/// HTML §2.3.4.2 "rules for parsing integers" (`tabindex`): leading ASCII
/// whitespace, an optional sign, at least one digit; whatever follows the
/// digits is ignored. `None` for an error.
pub fn parse_integer(s: &str) -> Option<i64> {
    let s = s.trim_start_matches(['\t', '\n', '\x0C', '\r', ' ']);
    let (neg, rest) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    if digits.is_empty() {
        return None;
    }
    let n: i64 = digits.parse().unwrap_or(i64::MAX);
    Some(if neg { n.saturating_neg() } else { n })
}

/// HTML §2.3.4.2 "rules for parsing non-negative integers".
pub fn parse_non_negative(s: &str) -> Option<usize> {
    let s = s.trim_start_matches(['\t', '\n', '\x0C', '\r', ' ']);
    let rest = s.strip_prefix('+').unwrap_or(s);
    let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
    if digits.is_empty() {
        return None;
    }
    Some(digits.parse().unwrap_or(usize::MAX))
}

/// A row of the control state table, if `n` has one.
pub fn row(rows: &[ExecControl], n: usize) -> Option<&ExecControl> {
    rows.get(n)
}

/// The value a text control shows and edits: a `textarea`'s API value
/// without the wrapping transformation (HTML §4.10.11, "raw value" with
/// "normalize newlines"), an `input`'s value (§4.10.5.1: the dirty value
/// when there is one, else the sanitized `value` attribute), as a string.
pub fn current_text(arena: &Arena, rows: &[ExecControl], n: usize) -> String {
    if !valid(arena, n) {
        return String::new();
    }
    if is(arena, n, "textarea") {
        let raw = clazel_forms::exec::entry::textarea_raw_exec(arena, rows, n);
        string(&clazel_forms::exec::strings::normalize_newlines_exec(&raw))
    } else if is(arena, n, "input") {
        string(&clazel_forms::exec::entry::input_value_exec(arena, rows, n))
    } else {
        String::new()
    }
}

/// The nodes of `arena` in tree order, from the document.
pub fn tree_order(arena: &Arena) -> Vec<usize> {
    if arena.is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut stack = vec![0usize];
    while let Some(n) = stack.pop() {
        out.push(n);
        stack.extend(arena.children(n).iter().rev().copied());
    }
    out
}

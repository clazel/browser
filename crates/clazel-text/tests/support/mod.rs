//! Shared by the golden and bound tests: parsing through the real parser,
//! and the crate's bound (`clazel_text` crate docs, "The bound").

use clazel_dom::exec::{Arena, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_text::{PER_NODE_CHARS, PER_NODE_LINES, Page};
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

/// No encoding changes: the documents are already code points.
struct NoEnc;

impl EncFnsExec for NoEnc {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

/// `html` parsed as a document by `exec::driver::parse_real`, scripting off
/// (the browser's setting), certain confidence.
pub fn parse(html: &str) -> Arena {
    let input: Vec<u32> = html.chars().map(u32::from).collect();
    parse_real(&NoEnc, &input, Vec::new(), false, false).0.arena
}

/// `(T, A, N)` of the bound: code points of every `Text` node's data, code
/// points of every HTML `img`'s `alt` values, and the number of nodes.
pub fn measure(doc: &Arena) -> (usize, usize, usize) {
    let mut t = 0usize;
    let mut a = 0usize;
    for id in 0..doc.len() {
        match doc.kind(id) {
            ExecKind::Text { data } => t = t.saturating_add(data.len()),
            ExecKind::Element {
                namespace: Some(Namespace::Html),
                local_name,
                attributes,
                ..
            } if local_name.iter().copied().eq("img".chars().map(u32::from)) => {
                for at in attributes {
                    if at.namespace.is_none()
                        && at
                            .local_name
                            .iter()
                            .copied()
                            .eq("alt".chars().map(u32::from))
                    {
                        a = a.saturating_add(at.value.len());
                    }
                }
            }
            _ => {}
        }
    }
    (t, a, doc.len())
}

/// Checks both inequalities of the bound and that no line is longer than
/// a non-zero width; `Err` says which failed.
pub fn check_bound(doc: &Arena, page: &Page, width: usize) -> Result<(), String> {
    let (t, a, n) = measure(doc);
    let chars = page
        .lines
        .iter()
        .fold(page.title.chars().count(), |acc, l| {
            acc.saturating_add(l.chars().count())
        });
    let base = t.saturating_add(a);
    let char_bound = base.saturating_add(PER_NODE_CHARS.saturating_mul(n));
    let line_bound = base.saturating_add(PER_NODE_LINES.saturating_mul(n));
    if chars > char_bound {
        return Err(format!(
            "characters {chars} > {char_bound} (T={t} A={a} N={n})"
        ));
    }
    if page.lines.len() > line_bound {
        return Err(format!(
            "lines {} > {line_bound} (T={t} A={a} N={n})",
            page.lines.len()
        ));
    }
    if width > 0
        && let Some(l) = page.lines.iter().find(|l| l.chars().count() > width)
    {
        return Err(format!("line longer than {width}: {l:?}"));
    }
    Ok(())
}

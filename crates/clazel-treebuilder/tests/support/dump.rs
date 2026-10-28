//! The html5lib-tests tree format ("| " lines), printed from an arena.
//!
//! Each node is a line `| ` followed by two spaces per level of depth and:
//! `<!DOCTYPE name>` (with `"public" "system"` when either is not empty),
//! `<name>` for an HTML element and `<svg name>` / `<math name>` for SVG and
//! MathML ones, attributes one level deeper as `name="value"` sorted by
//! their printed name (`xlink href`, `xml lang`, `xmlns xlink` for
//! namespaced ones), `"text"`, `<!-- data -->`, `<?target data?>`, and a
//! template's contents as a `content` line one level deeper with the
//! fragment's children below it. The walk is iterative (a stack), so deep
//! trees do not overflow the test's stack.

use clazel_dom::exec::{Arena, ExecKind};
use clazel_dom::spec::Namespace;

fn s(v: &[u32]) -> String {
    v.iter().map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}')).collect()
}

fn line(out: &mut String, depth: usize, text: &str) {
    out.push_str("| ");
    for _ in 0..depth {
        out.push_str("  ");
    }
    out.push_str(text);
    out.push('\n');
}

/// The children of `root` (not `root` itself), as the suite prints them.
pub fn dump_children(arena: &Arena, root: usize) -> String {
    let mut out = String::new();
    // (node, depth) or a template's "content" marker.
    enum Item {
        Node(usize, usize),
        Content(usize, usize),
    }
    let mut stack: Vec<Item> = arena.children(root).iter().rev().map(|&c| Item::Node(c, 0)).collect();
    while let Some(item) = stack.pop() {
        match item {
            Item::Content(frag, depth) => {
                line(&mut out, depth, "content");
                for &c in arena.children(frag).iter().rev() {
                    stack.push(Item::Node(c, depth + 1));
                }
            }
            Item::Node(n, depth) => {
                match arena.kind(n) {
                    ExecKind::DocumentType { name, public_id, system_id } => {
                        if public_id.is_empty() && system_id.is_empty() {
                            line(&mut out, depth, &format!("<!DOCTYPE {}>", s(name)));
                        } else {
                            line(&mut out, depth, &format!("<!DOCTYPE {} \"{}\" \"{}\">", s(name), s(public_id), s(system_id)));
                        }
                    }
                    ExecKind::Element { namespace, local_name, attributes, template_contents, .. } => {
                        let prefix = match namespace {
                            Some(Namespace::Svg) => "svg ",
                            Some(Namespace::MathMl) => "math ",
                            _ => "",
                        };
                        line(&mut out, depth, &format!("<{}{}>", prefix, s(local_name)));
                        let mut attrs: Vec<(String, String)> = attributes
                            .iter()
                            .map(|a| {
                                let name = match (&a.namespace, &a.prefix) {
                                    (Some(Namespace::XLink), _) => format!("xlink {}", s(&a.local_name)),
                                    (Some(Namespace::Xml), _) => format!("xml {}", s(&a.local_name)),
                                    (Some(Namespace::Xmlns), _) => format!("xmlns {}", s(&a.local_name)),
                                    _ => s(&a.local_name),
                                };
                                (name, s(&a.value))
                            })
                            .collect();
                        attrs.sort();
                        for (k, v) in attrs {
                            line(&mut out, depth + 1, &format!("{k}=\"{v}\""));
                        }
                        // Children are pushed first so the template contents
                        // come out before them (a template has none).
                        for &c in arena.children(n).iter().rev() {
                            stack.push(Item::Node(c, depth + 1));
                        }
                        if let (Some(f), Some(Namespace::Html)) = (template_contents, namespace) {
                            stack.push(Item::Content(*f, depth + 1));
                        }
                    }
                    ExecKind::Text { data } => line(&mut out, depth, &format!("\"{}\"", s(data))),
                    ExecKind::Comment { data } => line(&mut out, depth, &format!("<!-- {} -->", s(data))),
                    ExecKind::ProcessingInstruction { target, data } => {
                        line(&mut out, depth, &format!("<?{} {}?>", s(target), s(data)))
                    }
                    ExecKind::Document { .. } | ExecKind::DocumentFragment { .. } => {
                        line(&mut out, depth, "#unexpected")
                    }
                }
            }
        }
    }
    out
}

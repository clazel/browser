//! A reftest's references and fuzziness, found with our own HTML parser.
//!
//! Source: WPT `tools/manifest/sourcefile.py`: `references` ("`link[@rel='match']`",
//! "`link[@rel='mismatch']`", the `href` "stripped" of space characters and
//! joined to the test's URL) and `fuzzy` with `parse_ref_keyed_meta`
//! (`content.rsplit(":", 1)` for a reference key; two `;`-separated parts,
//! each optionally `maxDifference=` or `totalPixels=`, each `N` or `N-M`).

use clazel_dom::exec::{Arena, ExecAttr, ExecKind};
use clazel_dom::spec::Namespace;
use clazel_treebuilder::exec::driver::parse_real;
use clazel_treebuilder::exec::types::EncFnsExec;

/// A reference's relation (`==` or `!=` in WPT's manifest).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Relation {
    /// `rel=match`: the test must render as the reference.
    Match,
    /// `rel=mismatch`: it must not.
    Mismatch,
}

/// One reference: its path in the WPT tree and its relation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Reference {
    /// The resolved path.
    pub path: String,
    /// Match or mismatch.
    pub relation: Relation,
}

/// The allowed differences: inclusive ranges of the maximum per-channel
/// difference and of the count of differing pixels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fuzzy {
    /// `maxDifference`.
    pub max_difference: (u64, u64),
    /// `totalPixels`.
    pub total_pixels: (u64, u64),
}

/// What a test page says.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Meta {
    /// Its references, in document order.
    pub references: Vec<Reference>,
    /// Its fuzziness: for one reference (by resolved path), or for any.
    pub fuzzy: Vec<(Option<String>, Fuzzy)>,
}

/// Why a page's metadata is not usable (WPT's manifest raises `ValueError`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetaError {
    /// A `fuzzy` content that is not two ranges.
    Malformed(String),
    /// A `fuzzy` key that names no reference of the page.
    UnknownReference(String),
    /// Two `fuzzy` metas for the same key.
    Duplicate,
}

struct NoEncodings;

impl EncFnsExec for NoEncodings {
    fn get_an_encoding(&self, _label: &[u32]) -> Option<u64> {
        None
    }

    fn extract_from_meta(&self, _content: &[u32]) -> Option<Vec<u32>> {
        None
    }
}

/// `bytes` (UTF-8, as WPT's files are) parsed by our HTML parser.
pub fn parse(bytes: &[u8]) -> Arena {
    let input: Vec<u32> = String::from_utf8_lossy(bytes)
        .chars()
        .map(u32::from)
        .collect();
    parse_real(&NoEncodings, &input, Vec::new(), false, false)
        .0
        .arena
}

fn text(s: &[u32]) -> String {
    s.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

fn attribute<'a>(attributes: &'a [ExecAttr], name: &str) -> Option<&'a [u32]> {
    attributes
        .iter()
        .find(|a| {
            a.namespace.is_none() && a.local_name.iter().copied().eq(name.chars().map(u32::from))
        })
        .map(|a| a.value.as_slice())
}

/// The HTML elements of `arena` in tree order, as (local name, attributes).
pub fn elements(arena: &Arena) -> Vec<(String, &[ExecAttr])> {
    let n = arena.len();
    let mut out = Vec::new();
    let mut stack = vec![0usize];
    for _ in 0..n.saturating_add(1) {
        let Some(id) = stack.pop() else { break };
        if id >= n {
            continue;
        }
        if let ExecKind::Element {
            namespace: Some(Namespace::Html),
            local_name,
            attributes,
            ..
        } = arena.kind(id)
        {
            out.push((text(local_name), attributes.as_slice()));
        }
        stack.extend(arena.children(id).iter().rev());
    }
    out
}

/// Python's `str.strip(space_chars)` with WPT's `space_chars` (" \t\n\f\r").
fn strip(s: &str) -> &str {
    s.trim_matches([' ', '\t', '\n', '\u{0C}', '\r'])
}

/// `href` resolved against the directory of `base` (paths in the WPT tree;
/// a leading `/` is the root), with `.` and `..` steps removed.
pub fn resolve(base: &str, href: &str) -> String {
    let mut parts: Vec<&str> = if href.starts_with('/') {
        Vec::new()
    } else {
        let mut b: Vec<&str> = base.split('/').collect();
        b.pop();
        b
    };
    for p in href.split('/') {
        match p {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            other => parts.push(other),
        }
    }
    // Drop a query or fragment: the server maps the path.
    let joined = parts.join("/");
    joined
        .split(['?', '#'])
        .next()
        .unwrap_or_default()
        .to_owned()
}

/// One range: `N` (exactly N) or `N-M` (inclusive).
fn range(s: &str) -> Option<(u64, u64)> {
    match s.split_once('-') {
        Some((a, b)) => Some((strip(a).parse().ok()?, strip(b).parse().ok()?)),
        None => {
            let v = strip(s).parse().ok()?;
            Some((v, v))
        }
    }
}

/// A `fuzzy` meta's `content`, with its reference key (as written) if any.
pub fn parse_fuzzy(content: &str) -> Result<(Option<String>, Fuzzy), MetaError> {
    // `parts = item.rsplit(":", 1)`.
    let (key, value) = match content.rsplit_once(':') {
        Some((k, v)) => (Some(k.to_owned()), v),
        None => (None, content),
    };
    let ranges: Vec<&str> = value.split(';').collect();
    if ranges.len() != 2 {
        return Err(MetaError::Malformed(value.to_owned()));
    }
    let mut named: [Option<(u64, u64)>; 2] = [None, None];
    let mut positional: Vec<(u64, u64)> = Vec::new();
    for r in ranges {
        let (name, v) = match r.split_once('=') {
            Some((n, v)) => (Some(strip(n)), strip(v)),
            None => (None, r),
        };
        let value = range(v).ok_or_else(|| MetaError::Malformed(r.to_owned()))?;
        match name {
            None => positional.push(value),
            Some(n) => {
                let slot = match n {
                    "maxDifference" => named.get_mut(0),
                    "totalPixels" => named.get_mut(1),
                    _ => None,
                }
                .ok_or_else(|| MetaError::Malformed(n.to_owned()))?;
                if slot.is_some() {
                    return Err(MetaError::Malformed(n.to_owned()));
                }
                *slot = Some(value);
            }
        }
    }
    // "for arg_name in args: … else: arg_value = positional_args.popleft()".
    let mut positional = positional.into_iter();
    let mut take = |slot: Option<(u64, u64)>| slot.or_else(|| positional.next());
    let max_difference = take(named[0]).ok_or_else(|| MetaError::Malformed(value.to_owned()))?;
    let total_pixels = take(named[1]).ok_or_else(|| MetaError::Malformed(value.to_owned()))?;
    Ok((
        key,
        Fuzzy {
            max_difference,
            total_pixels,
        },
    ))
}

/// The references and fuzziness of the test at `path` whose bytes are
/// `bytes`.
pub fn read(path: &str, bytes: &[u8]) -> Result<Meta, MetaError> {
    let arena = parse(bytes);
    let mut meta = Meta::default();
    let els = elements(&arena);
    for (name, attributes) in &els {
        if name != "link" {
            continue;
        }
        let relation = match attribute(attributes, "rel").map(text).as_deref() {
            Some("match") => Relation::Match,
            Some("mismatch") => Relation::Mismatch,
            _ => continue,
        };
        if let Some(href) = attribute(attributes, "href") {
            meta.references.push(Reference {
                path: resolve(path, strip(&text(href))),
                relation,
            });
        }
    }
    for (name, attributes) in &els {
        if name != "meta" || attribute(attributes, "name").map(text).as_deref() != Some("fuzzy") {
            continue;
        }
        let content = attribute(attributes, "content")
            .map(text)
            .unwrap_or_default();
        let (key, fuzzy) = parse_fuzzy(&content)?;
        let key = match key {
            Some(k) => {
                let p = resolve(path, &k);
                if !meta.references.iter().any(|r| r.path == p) {
                    return Err(MetaError::UnknownReference(k));
                }
                Some(p)
            }
            None => None,
        };
        if meta.fuzzy.iter().any(|(k, _)| *k == key) {
            return Err(MetaError::Duplicate);
        }
        meta.fuzzy.push((key, fuzzy));
    }
    Ok(meta)
}

impl Meta {
    /// The fuzziness for reference `path`: its own, else the unprefixed one
    /// ("any unprefixed value will automatically be applied to any ref that
    /// doesn't have a more specific value").
    pub fn fuzzy_for(&self, path: &str) -> Option<Fuzzy> {
        self.fuzzy
            .iter()
            .find(|(k, _)| k.as_deref() == Some(path))
            .or_else(|| self.fuzzy.iter().find(|(k, _)| k.is_none()))
            .map(|(_, f)| *f)
    }
}

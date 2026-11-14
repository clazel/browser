//! The user agent style sheet of `clazel-style`'s cascade (Phase 5 item 5.7), from HTML §15.
//!
//! HTML §15 "Rendering" gives the user agent style sheet as CSS blocks
//! (`<pre><code class="css">`) between its prose. `rendering.html`, an excerpt of the
//! standard's source at a pinned commit, is vendored under
//! `crates/clazel-style/data/html-<commit>/` with a `SOURCE.md` giving its SHA-256. This
//! module reads every CSS block of it, in order, and writes each one the table [`BLOCKS`]
//! takes into one of three files:
//!
//! - `data/ua.css`: user agent level rules, in every document;
//! - `data/ua-quirks.css`: user agent level rules that apply in quirks mode only ("In quirks
//!   mode, the following rules are also expected to apply");
//! - `data/hints.css`: rules that "are also expected to apply, as presentational hints".
//!
//! What it derives is kept to stated steps: a block's text is what lies between
//! `<pre><code class="css">` and `</code></pre>`, with HTML comments and tags removed and the
//! entities `&lt;`, `&gt;`, `&amp;` and `&quot;` replaced (any other entity is rejected);
//! each block is preceded in the output by a comment naming its section. Nothing else is
//! changed: the adaptations the cascade needs (logical properties, `:heading`) are made by
//! `crates/clazel-style/src/cascade/ua.rs` when it reads the files, where they are listed.
//!
//! `cargo xtask tables` writes the files; `check` and `verify` fail if the vendored file's
//! hash differs from `SOURCE.md`, if the blocks are not exactly those of [`BLOCKS`] (by
//! section, and by a phrase of the sentence that introduces each), or if a file is stale.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::reviews;
use crate::workspace;

/// The vendored data directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-style/data/html-4c54fae1";
/// The vendored excerpt.
const EXCERPT: &str = "rendering.html";
/// Where the generated files go, relative to the repository root.
const OUT_DIR: &str = "crates/clazel-style/data";

/// Where a block of §15 goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// User agent level, every document.
    Ua,
    /// User agent level, quirks mode only.
    UaQuirks,
    /// Presentational hints.
    Hint,
    /// Not used, for the reason given.
    Skip,
}

/// One CSS block of the excerpt, in order: its section's number and heading, a phrase the
/// sentence before it must contain (empty when the block follows its heading directly),
/// where it goes, and why.
struct Block {
    section: &'static str,
    heading: &'static str,
    intro: &'static str,
    kind: Kind,
    why: &'static str,
}

/// Every CSS block of §15.1 to §15.4, in order (phase-5.md item 5.7 names §15.3.1, §15.3.3,
/// §15.3.4, §15.3.6, §15.3.7, §15.3.8 with its quirks-mode rules, §15.3.10, §15.3.11 and
/// the parts of §15.4 that size replaced elements; §15.3.2 is taken too, since the root and
/// `body` need `display: block`).
const BLOCKS: &[Block] = &[
    Block {
        section: "15.3.1",
        heading: "Hidden elements",
        intro: "",
        kind: Kind::Ua,
        why: "item 5.7",
    },
    Block {
        section: "15.3.2",
        heading: "The page",
        intro: "",
        kind: Kind::Ua,
        why: "`html` and `body` are blocks",
    },
    Block {
        section: "15.3.3",
        heading: "Flow content",
        intro: "",
        kind: Kind::Ua,
        why: "item 5.7",
    },
    Block {
        section: "15.3.3",
        heading: "Flow content",
        intro: "also expected to apply, as presentational",
        kind: Kind::Hint,
        why: "item 5.7",
    },
    Block {
        section: "15.3.3",
        heading: "Flow content",
        intro: "In quirks mode, the following rules are also expected to apply",
        kind: Kind::UaQuirks,
        why: "item 5.7",
    },
    Block {
        section: "15.3.4",
        heading: "Phrasing content",
        intro: "",
        kind: Kind::Ua,
        why: "item 5.7",
    },
    Block {
        section: "15.3.4",
        heading: "Phrasing content",
        intro: "also expected to apply, as",
        kind: Kind::Hint,
        why: "item 5.7 (`clear` is not in the subset, so these are dropped)",
    },
    Block {
        section: "15.3.5",
        heading: "Bidirectional text",
        intro: "",
        kind: Kind::Skip,
        why: "bidirectional text is Phase 8's (phase-5.md 5.0(b)); `unicode-bidi` and \
              `direction` are not in the subset",
    },
    Block {
        section: "15.3.5",
        heading: "Bidirectional text",
        intro: "ISO-8859-8",
        kind: Kind::Skip,
        why: "bidirectional text is Phase 8's",
    },
    Block {
        section: "15.3.6",
        heading: "Sections and headings",
        intro: "",
        kind: Kind::Ua,
        why: "item 5.7",
    },
    Block {
        section: "15.3.7",
        heading: "Lists",
        intro: "",
        kind: Kind::Ua,
        why: "item 5.7",
    },
    Block {
        section: "15.3.7",
        heading: "Lists",
        intro: "also expected to apply, as",
        kind: Kind::Hint,
        why: "item 5.7",
    },
    Block {
        section: "15.3.7",
        heading: "Lists",
        intro: "In quirks mode, the following rules are also expected to apply",
        kind: Kind::UaQuirks,
        why: "item 5.7 (`list-style-position` is not in the subset, so these are dropped)",
    },
    Block {
        section: "15.3.8",
        heading: "Tables",
        intro: "",
        kind: Kind::Ua,
        why: "item 5.7",
    },
    Block {
        section: "15.3.8",
        heading: "Tables",
        intro: "also expected to apply, as presentational",
        kind: Kind::Hint,
        why: "item 5.7",
    },
    Block {
        section: "15.3.8",
        heading: "Tables",
        intro: "In quirks mode, the following rules are also expected to apply",
        kind: Kind::UaQuirks,
        why: "item 5.7",
    },
    Block {
        section: "15.3.8",
        heading: "Tables",
        intro: "In HTML documents, the following rules are also expected to apply",
        kind: Kind::Ua,
        why: "item 5.7: every document the renderer styles is an HTML document",
    },
    Block {
        section: "15.3.10",
        heading: "Form controls",
        intro: "",
        kind: Kind::Ua,
        why: "item 5.7",
    },
    Block {
        section: "15.3.10",
        heading: "Form controls",
        intro: "In quirks mode, the following rules are also expected to apply",
        kind: Kind::UaQuirks,
        why: "item 5.7 (`box-sizing` is not in the subset, so this is dropped)",
    },
    Block {
        section: "15.3.11",
        heading: "The hr element",
        intro: "",
        kind: Kind::Ua,
        why: "item 5.7",
    },
    Block {
        section: "15.3.11",
        heading: "The hr element",
        intro: "also expected to apply, as presentational",
        kind: Kind::Hint,
        why: "item 5.7",
    },
    Block {
        section: "15.3.12",
        heading: "The fieldset and legend elements",
        intro: "",
        kind: Kind::Skip,
        why: "not in item 5.7's list; `fieldset` rendering needs its anonymous content box, \
              which 5.13 does not build",
    },
    Block {
        section: "15.4.1",
        heading: "Embedded content",
        intro: "The following CSS rules are expected to apply",
        kind: Kind::Ua,
        why: "item 5.7 (the `iframe` border)",
    },
    Block {
        section: "15.4.2",
        heading: "Images",
        intro: "The following CSS rules are expected to apply",
        kind: Kind::Ua,
        why: "item 5.7 (`contain` is not in the subset, so this is dropped)",
    },
    Block {
        section: "15.4.2",
        heading: "Images",
        intro: "when the Document is in quirks mode",
        kind: Kind::UaQuirks,
        why: "item 5.7",
    },
    Block {
        section: "15.4.3",
        heading: "Attributes for embedded content and images",
        intro: "apply as presentational hints",
        kind: Kind::Hint,
        why: "item 5.7",
    },
];

/// One CSS block as found in the excerpt.
#[derive(Debug, PartialEq, Eq)]
struct Found {
    section: String,
    heading: String,
    intro: String,
    css: String,
}

/// Compare (or, with `write`, rewrite) the generated style sheets. Returns (problems,
/// notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let dir = PathBuf::from(DATA_DIR);
    let mut problems = check_sources(&dir);
    let mut notes = Vec::new();
    if !problems.is_empty() {
        return (problems, notes);
    }
    let files = match std::fs::read_to_string(dir.join(EXCERPT))
        .map_err(|e| e.to_string())
        .and_then(|t| generate(&t))
    {
        Ok(f) => f,
        Err(e) => return (vec![format!("{DATA_DIR}/{EXCERPT}: {e}")], notes),
    };
    for (name, fresh) in files {
        let path = format!("{OUT_DIR}/{name}");
        let current = std::fs::read_to_string(&path).ok();
        if current.as_deref() == Some(fresh.as_str()) {
            notes.push(format!("{path}: up to date"));
        } else if write {
            match std::fs::write(&path, &fresh) {
                Ok(()) => notes.push(format!("{path}: written")),
                Err(e) => problems.push(format!("{path}: {e}")),
            }
        } else if current.is_none() {
            problems.push(format!("{path}: missing; run `cargo xtask tables`"));
        } else {
            problems.push(format!(
                "{path}: stale (differs from what xtask/src/ua_sheet.rs produces); \
                 run `cargo xtask tables` and commit the result"
            ));
        }
    }
    (problems, notes)
}

/// The excerpt is listed in `SOURCE.md` with its SHA-256 and matches it; nothing but it,
/// `SOURCE.md` and `LICENSE` is in the directory.
fn check_sources(dir: &Path) -> Vec<String> {
    let rel = workspace::relative(dir);
    let source = match std::fs::read_to_string(dir.join("SOURCE.md")) {
        Ok(s) => s,
        Err(e) => return vec![format!("{rel}/SOURCE.md: {e}")],
    };
    let mut problems = Vec::new();
    let listed = source.lines().find_map(|l| {
        let rest = l.trim().strip_prefix("SHA-256:")?.trim();
        let (hash, name) = rest.split_once(char::is_whitespace)?;
        (name.trim().trim_matches('`') == EXCERPT).then(|| hash.to_ascii_lowercase())
    });
    match listed {
        None => problems.push(format!(
            "{rel}/SOURCE.md: no \"SHA-256: <hash> {EXCERPT}\" line"
        )),
        Some(listed) => match reviews::sha256(&dir.join(EXCERPT)) {
            Ok(actual) if actual == listed => {}
            Ok(actual) => problems.push(format!(
                "{rel}/{EXCERPT}: SHA-256 {actual} differs from SOURCE.md ({listed})"
            )),
            Err(e) => problems.push(e),
        },
    }
    for key in ["License:", "Commit:"] {
        if !source.lines().any(|l| l.trim().starts_with(key)) {
            problems.push(format!("{rel}/SOURCE.md: no \"{key}\" line"));
        }
    }
    match std::fs::read_dir(dir) {
        Ok(entries) => {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if name != EXCERPT && name != "SOURCE.md" && name != "LICENSE" {
                    problems.push(format!(
                        "{rel}/{name}: not an input of xtask/src/ua_sheet.rs"
                    ));
                }
            }
        }
        Err(e) => problems.push(format!("{rel}: {e}")),
    }
    problems
}

/// `s` with HTML comments and tags removed.
fn strip_markup(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    loop {
        let comment = rest.find("<!--");
        let tag = rest.find('<');
        match (comment, tag) {
            (Some(c), Some(t)) if c == t => {
                out.push_str(rest.get(..c).unwrap_or_default());
                let after = rest.get(c..).unwrap_or_default();
                match after.find("-->") {
                    Some(e) => rest = after.get(e.saturating_add(3)..).unwrap_or_default(),
                    None => return out,
                }
            }
            (_, Some(t)) => {
                out.push_str(rest.get(..t).unwrap_or_default());
                let after = rest.get(t..).unwrap_or_default();
                match after.find('>') {
                    Some(e) => rest = after.get(e.saturating_add(1)..).unwrap_or_default(),
                    None => return out,
                }
            }
            (_, None) => {
                out.push_str(rest);
                return out;
            }
        }
    }
}

/// `s` with the four entities a CSS block uses replaced; an error for any other.
fn unescape(s: &str) -> Result<String, String> {
    let out = s
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"");
    if let Some(i) = out.replace("&amp;", "").find('&') {
        let near: String = out.chars().skip(i).take(12).collect();
        return Err(format!(
            "an entity other than &lt; &gt; &amp; &quot;: {near:?}"
        ));
    }
    Ok(out.replace("&amp;", "&"))
}

/// Whitespace runs collapsed to one space, trimmed.
fn collapse(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// Every CSS block of the excerpt, with the section it is in (numbered from the excerpt's
/// `<h3>` and `<h4>` headings, the first `<h3>` being §15.1) and the text between the
/// previous heading or block and it.
fn blocks(excerpt: &str) -> Result<Vec<Found>, String> {
    const OPEN: &str = "<pre><code class=\"css\">";
    const CLOSE: &str = "</code></pre>";
    let mut out = Vec::new();
    let (mut h3, mut h4) = (0u32, 0u32);
    let mut section = String::new();
    let mut heading = String::new();
    let mut since = String::new();
    let mut lines = excerpt.lines();
    while let Some(line) = lines.next() {
        let t = line.trim_start();
        let is_h3 = t.starts_with("<h3");
        let is_h4 = t.starts_with("<h4");
        if is_h3 || is_h4 {
            if is_h3 {
                h3 = h3.saturating_add(1);
                h4 = 0;
                section = format!("15.{h3}");
            } else {
                h4 = h4.saturating_add(1);
                section = format!("15.{h3}.{h4}");
            }
            heading = collapse(&unescape(&strip_markup(t))?);
            since.clear();
            continue;
        }
        if let Some(start) = line.find(OPEN) {
            since.push_str(line.get(..start).unwrap_or_default());
            let mut text = line
                .get(start.saturating_add(OPEN.len())..)
                .unwrap_or_default()
                .to_owned();
            while !text.contains(CLOSE) {
                let Some(next) = lines.next() else {
                    return Err(format!("§{section}: a CSS block is not closed"));
                };
                text.push('\n');
                text.push_str(next);
            }
            let end = text.find(CLOSE).unwrap_or(text.len());
            let css = unescape(&strip_markup(text.get(..end).unwrap_or_default()))?;
            out.push(Found {
                section: section.clone(),
                heading: heading.clone(),
                intro: collapse(&unescape(&strip_markup(&since))?),
                css,
            });
            since.clear();
            continue;
        }
        since.push_str(line);
        since.push('\n');
    }
    Ok(out)
}

/// The three files, by name.
fn generate(excerpt: &str) -> Result<Vec<(&'static str, String)>, String> {
    let found = blocks(excerpt)?;
    if found.len() != BLOCKS.len() {
        return Err(format!(
            "{} CSS blocks, but BLOCKS lists {}; update BLOCKS for the new text",
            found.len(),
            BLOCKS.len()
        ));
    }
    let mut ua = header(Kind::Ua);
    let mut quirks = header(Kind::UaQuirks);
    let mut hints = header(Kind::Hint);
    for (i, (f, b)) in found.iter().zip(BLOCKS).enumerate() {
        if f.section != b.section || f.heading != b.heading {
            return Err(format!(
                "block {i}: in §{} {:?}, but BLOCKS expects §{} {:?}",
                f.section, f.heading, b.section, b.heading
            ));
        }
        if !f.intro.contains(b.intro) {
            return Err(format!(
                "block {i} (§{}): the text before it, {:?}, no longer says {:?}",
                f.section, f.intro, b.intro
            ));
        }
        let out = match b.kind {
            Kind::Ua => &mut ua,
            Kind::UaQuirks => &mut quirks,
            Kind::Hint => &mut hints,
            Kind::Skip => continue,
        };
        let _ = write!(
            out,
            "\n/* HTML §{} {} ({}) */\n{}\n",
            b.section,
            b.heading,
            b.why,
            f.css.trim_end()
        );
    }
    Ok(vec![
        ("ua.css", ua),
        ("ua-quirks.css", quirks),
        ("hints.css", hints),
    ])
}

/// The comment at the top of each file.
fn header(kind: Kind) -> String {
    let what = match kind {
        Kind::Ua => "the user agent level rules, in every document",
        Kind::UaQuirks => "the user agent level rules that apply in quirks mode only",
        Kind::Hint => "the rules that apply as presentational hints",
        Kind::Skip => "",
    };
    format!(
        "/* Generated by `cargo xtask tables` (xtask/src/ua_sheet.rs) from\n   \
         {DATA_DIR}/{EXCERPT}, HTML §15 at the commit its SOURCE.md names:\n   \
         {what}. Do not edit: each block is the standard's, as written. */\n"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strips_comments_tags_and_entities() {
        let s = "a <span id=x>b</span> <!-- c > d --> e &gt; f";
        assert_eq!(
            unescape(&strip_markup(s)).ok(),
            Some("a b  e > f".to_owned())
        );
        assert!(unescape("&nbsp;").is_err());
    }

    #[test]
    fn finds_blocks_with_sections() {
        let excerpt = "<h3>Intro</h3>\n<p>x</p>\n<h3>Non-replaced</h3>\n<h4>Hidden</h4>\n\
                       <p>The rules:</p>\n  <pre><code class=\"css\">a { b: c; }\n\
                       d &gt; e { }</code></pre>\n";
        let found = blocks(excerpt).ok().unwrap_or_default();
        assert_eq!(
            found,
            vec![Found {
                section: "15.2.1".into(),
                heading: "Hidden".into(),
                intro: "The rules:".into(),
                css: "a { b: c; }\nd > e { }".into(),
            }]
        );
    }
}

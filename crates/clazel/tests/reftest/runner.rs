//! One reftest, with the renderer as a parameter (phase-5.md item 5.25:
//! "rendered by `browse --headless` at 800×600, scale 1, with the bundled
//! font"), so that the real one plugs in when `browse --headless` exists.
//!
//! Source: WPT's "Multiple References": "If there are any match
//! references, at least one must match, and if there are any mismatch
//! references, all must mismatch."

use super::classify::{NotRun, classify};
use super::meta::{MetaError, Relation, read};
use super::pixels::{Image, differences, passes};

/// Renders a page: its path in the WPT tree and its bytes, to an 800×600
/// screenshot at scale 1.
pub trait Render {
    /// The screenshot, or why there is none.
    fn render(&mut self, path: &str, bytes: &[u8]) -> Result<Image, String>;
}

/// A reftest's result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// It passed.
    Pass,
    /// It failed: the first reference that decided it, with the difference
    /// measured against it (`None` when the sizes differ).
    Fail {
        /// The reference.
        reference: String,
        /// `(max_per_channel, pixels_different)`.
        difference: Option<(u8, u64)>,
    },
    /// Not run, by reason (the test's or a reference's).
    NotRun(NotRun),
    /// Not a reftest: it has no reference.
    NotAReftest,
    /// Its metadata is malformed, a file is missing, or rendering failed.
    Error(String),
}

/// Runs the reftest at `path`, reading files through `read_file` (paths in
/// the WPT tree) and rendering with `renderer`.
pub fn run(
    path: &str,
    read_file: &dyn Fn(&str) -> Option<Vec<u8>>,
    renderer: &mut dyn Render,
) -> Outcome {
    let Some(bytes) = read_file(path) else {
        return Outcome::Error(format!("{path}: missing"));
    };
    if let Some(why) = classify(path, &bytes) {
        return Outcome::NotRun(why);
    }
    let meta = match read(path, &bytes) {
        Ok(m) => m,
        Err(MetaError::Malformed(s)) => return Outcome::Error(format!("fuzzy: {s}")),
        Err(MetaError::UnknownReference(s)) => return Outcome::Error(format!("fuzzy key: {s}")),
        Err(MetaError::Duplicate) => return Outcome::Error("fuzzy: duplicate".to_owned()),
    };
    if meta.references.is_empty() {
        return Outcome::NotAReftest;
    }
    // Every reference must be runnable before anything is rendered.
    let mut refs = Vec::new();
    for r in &meta.references {
        let Some(b) = read_file(&r.path) else {
            return Outcome::Error(format!("{}: missing", r.path));
        };
        if let Some(why) = classify(&r.path, &b) {
            return Outcome::NotRun(why);
        }
        refs.push((r, b));
    }
    let test = match renderer.render(path, &bytes) {
        Ok(i) => i,
        Err(e) => return Outcome::Error(e),
    };
    let mut any_match = false;
    let mut first_failed_match: Option<Outcome> = None;
    for (r, b) in refs {
        let image = match renderer.render(&r.path, &b) {
            Ok(i) => i,
            Err(e) => return Outcome::Error(e),
        };
        let fuzzy = meta.fuzzy_for(&r.path);
        let ok = passes(&test, &image, r.relation, fuzzy);
        let fail = || Outcome::Fail {
            reference: r.path.clone(),
            difference: differences(&test, &image),
        };
        match r.relation {
            // "all must mismatch".
            Relation::Mismatch if !ok => return fail(),
            Relation::Mismatch => {}
            // "at least one must match".
            Relation::Match if ok => any_match = true,
            Relation::Match => {
                if first_failed_match.is_none() {
                    first_failed_match = Some(fail());
                }
            }
        }
    }
    let has_match = meta
        .references
        .iter()
        .any(|r| r.relation == Relation::Match);
    if has_match && !any_match {
        return first_failed_match.unwrap_or(Outcome::Pass);
    }
    Outcome::Pass
}

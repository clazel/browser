//! The reftest runner's pure parts (phase-5.md item 5.25): what a WPT
//! reftest asks for, how two screenshots compare, which tests are not run
//! and why, and a runner that takes the renderer as a parameter, so that
//! `browse --headless` plugs in when it exists.
//!
//! Sources: web-platform-tests at commit
//! `4ad507b28db0a636f528def9161d109fe11b93a3` (the commit this repository's
//! WPT data is vendored from): `docs/writing-tests/reftests.md` ("Fuzzy
//! Matching", "Multiple References"), `tools/manifest/sourcefile.py`
//! (`references`, `fuzzy`, `parse_ref_keyed_meta`) and
//! `tools/wptrunner/wptrunner/executors/base.py` (`check_pass`,
//! `get_differences`).
//!
//! - [`meta`]: a test's `<link rel=match|mismatch>` and `<meta name=fuzzy>`,
//!   found with our own HTML parser.
//! - [`pixels`]: the difference of two screenshots and the fuzzy rule.
//! - [`classify`]: "not run, by reason".
//! - [`runner`]: one reftest with a renderer given as a parameter.
//!
//! Modelling choices (ours, each listed):
//!
//! - **wptrunner's comparison, not only the docs' formula.** The docs define
//!   the maximum difference over every pixel and channel; wptrunner counts
//!   and measures only the pixels whose difference image is non-zero after
//!   PIL's conversion to luminance (`convert("L")`, `(19595·R + 38470·G +
//!   7471·B + 0x8000) >> 16`), so a pixel differing by 1 in red alone is not
//!   counted. Reftests are judged by wptrunner, so [`pixels::differences`]
//!   does what it does, and keeps its shortcuts in [`pixels::equal`].
//! - **Alpha is dropped** before comparing, as wptrunner's `convert("RGB")`.
//! - **Screenshots of different sizes are not equal** (wptrunner logs the
//!   sizes; ours are both 800×600, so this never decides a test).
//! - **One level of references**: a reference's own `<link rel=match>` is not
//!   followed (WPT's reference chains are rare in the directories 5.25 names);
//!   listed as not run if met.
//! - **Paths, not URLs**: tests are named by their path in the WPT tree, and
//!   an `href` is resolved against the test's directory (a leading `/` is the
//!   tree's root), as WPT's server maps them.

pub mod classify;
pub mod meta;
pub mod pixels;
pub mod runner;

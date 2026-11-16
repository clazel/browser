//! JIT item J.2: the instruction-set sources `clazel-x64` and `clazel-a64`
//! will be written against (docs/phases/jit.md).
//!
//! Nothing reads these yet, so each suite is an inventory (paths, sizes and
//! SHA-256, as in `inventory.rs`). Two sources are not redistributable, or
//! are too large to vendor, so they are **pinned** instead: `SOURCE.md`
//! names the file by URL, size and SHA-256, and the generated table lists
//! those pins. A reader (item J.3 or J.4) fetches the file and checks the
//! hash.
//!
//! - `acl2-x86isa` (`clazel-x64`): the ACL2 x86isa model, the files the
//!   subset of item J.3 reads.
//! - `acl2-rtl` (`clazel-x64`): Russinoff's RTL library at the same ACL2
//!   commit, which the x86isa floating-point books are defined with.
//! - `sail-x86-from-acl2` (`clazel-x64`): the Sail model that is a
//!   mechanical translation of the one above (see the crate's README: it is
//!   not independent of it).
//! - `intel-sdm` (`clazel-x64`) and `arm-arm` (`clazel-a64`): the vendors'
//!   manuals, pinned only (their terms do not allow redistribution).
//! - `sail-arm` (`clazel-a64`): the Sail Arm model, the A64 base
//!   instructions and the shared pseudocode they call.
//! - `arm-mrs` (`clazel-a64`): Arm's machine-readable specification, the
//!   licence and README vendored, `Instructions.json` (117 MB) pinned.

use std::fmt::Write as _;
use std::path::Path;

use super::inventory::{inventory, listed_hashes, render};

/// The ACL2 checkout's `books/projects/x86isa` paths vendored.
pub const ACL2_X86ISA_ROOTS: &[&str] = &["README", "portcullis", "utils", "machine"];
/// The ACL2 checkout's `books/rtl/rel11` paths vendored.
pub const ACL2_RTL_ROOTS: &[&str] = &["package.lsp", "portcullis.lisp", "lib"];
/// The translated Sail model's roots.
pub const SAIL_X86_FROM_ACL2_ROOTS: &[&str] = &["README.md", "LICENCE", "model"];
/// The Sail Arm model's roots.
pub const SAIL_ARM_ROOTS: &[&str] = &["README.md", "src"];
/// The files of Arm's package that are vendored.
pub const ARM_MRS_ROOTS: &[&str] = &["README.md", "notice.html"];

/// One file the suite names but does not hold.
struct Pin {
    file: String,
    size: u64,
    sha256: String,
}

fn tree(dir: &Path, suite: &str, roots: &[&str], what: &str) -> Result<String, String> {
    let files = inventory(dir, roots)?;
    render(suite, "isa", what, &files)
}

/// `acl2-x86isa`.
pub fn convert_acl2_x86isa(dir: &Path) -> Result<String, String> {
    tree(
        dir,
        "acl2-x86isa",
        ACL2_X86ISA_ROOTS,
        "ACL2 x86isa model files for the subset of jit.md item J.3.",
    )
}

/// `acl2-rtl`.
pub fn convert_acl2_rtl(dir: &Path) -> Result<String, String> {
    tree(
        dir,
        "acl2-rtl",
        ACL2_RTL_ROOTS,
        "Russinoff's RTL library, the floating-point definitions acl2-x86isa's SSE books call.",
    )
}

/// `sail-x86-from-acl2`.
pub fn convert_sail_x86_from_acl2(dir: &Path) -> Result<String, String> {
    tree(
        dir,
        "sail-x86-from-acl2",
        SAIL_X86_FROM_ACL2_ROOTS,
        "Sail x86 model translated from the ACL2 one (jit.md item J.2); not independent of it.",
    )
}

/// `sail-arm`.
pub fn convert_sail_arm(dir: &Path) -> Result<String, String> {
    tree(
        dir,
        "sail-arm",
        SAIL_ARM_ROOTS,
        "Sail Armv9.4-A model, A64 base instructions (jit.md item J.2).",
    )
}

/// The `Size: <bytes> <file>` lines of a `SOURCE.md`, as (file, bytes).
fn listed_sizes(source: &str) -> Vec<(String, u64)> {
    source
        .lines()
        .filter_map(|l| {
            let rest = l.trim().strip_prefix("Size:")?.trim();
            let (size, name) = rest.split_once(char::is_whitespace)?;
            Some((
                name.trim().trim_matches('`').to_owned(),
                size.parse::<u64>().ok()?,
            ))
        })
        .collect()
}

/// The pins `SOURCE.md` makes: every `SHA-256: <hash> <file>` line needs a
/// `Size: <bytes> <file>` line, and a hash of 64 hex digits.
fn pins(dir: &Path) -> Result<Vec<Pin>, String> {
    let source =
        std::fs::read_to_string(dir.join("SOURCE.md")).map_err(|e| format!("SOURCE.md: {e}"))?;
    let sizes = listed_sizes(&source);
    let mut out = Vec::new();
    for (file, hash) in listed_hashes(&source) {
        if hash.len() != 64 || !hash.chars().all(|c| c.is_ascii_hexdigit()) {
            return Err(format!(
                "SOURCE.md: the SHA-256 of {file} is not 64 hex digits"
            ));
        }
        let Some((_, size)) = sizes.iter().find(|(n, _)| *n == file) else {
            return Err(format!("SOURCE.md: no \"Size: <bytes> {file}\" line"));
        };
        out.push(Pin {
            file,
            size: *size,
            sha256: hash,
        });
    }
    if out.is_empty() {
        return Err("SOURCE.md: no \"SHA-256: <hash> <file>\" line".to_owned());
    }
    Ok(out)
}

fn render_pins(suite: &str, what: &str, pins: &[Pin], with_header: bool) -> Result<String, String> {
    let w = |r: std::fmt::Result| r.map_err(|e| e.to_string());
    let mut out = String::new();
    if with_header {
        w(write!(
            out,
            "// @generated by `cargo xtask testdata` from tests/data/{suite}/.\n\
             // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
             // converter (xtask/src/testdata/isa.rs) produces.\n\
             // Source, pins and license: tests/data/{suite}/SOURCE.md.\n\
             //\n\
             // {what}\n\
             \n"
        ))?;
    } else {
        out.push('\n');
    }
    w(write!(
        out,
        "/// A file the suite pins but does not vendor.\n\
         #[derive(Debug, Clone, Copy, PartialEq, Eq)]\n\
         pub struct Pin {{\n\
         \x20   /// The file's name in `SOURCE.md`.\n\
         \x20   pub file: &'static str,\n\
         \x20   /// Its size in bytes.\n\
         \x20   pub size: u64,\n\
         \x20   /// Its SHA-256, in lower-case hex.\n\
         \x20   pub sha256: &'static str,\n\
         }}\n\
         \n\
         /// Every pinned file.\n\
         pub const PINS: &[Pin] = &[\n"
    ))?;
    for p in pins {
        w(writeln!(
            out,
            "    Pin {{ file: {:?}, size: {}, sha256: \"{}\" }},",
            p.file, p.size, p.sha256
        ))?;
    }
    out.push_str("];\n");
    Ok(out)
}

/// `intel-sdm`: nothing vendored, one pin. The directory holds `SOURCE.md`
/// and `LICENSE.md` only (checked by `testdata.rs`).
pub fn convert_intel_sdm(dir: &Path) -> Result<String, String> {
    let pins = pins(dir)?;
    render_pins(
        "intel-sdm",
        "Intel SDM volume 2, pinned by URL and SHA-256 (Intel's terms do not allow redistribution).",
        &pins,
        true,
    )
}

/// `arm-arm`: Arm Architecture Reference Manual for A-profile, nothing
/// vendored, one pin (or, until a person fills it in, a placeholder: see the
/// suite's `SOURCE.md`).
pub fn convert_arm_arm(dir: &Path) -> Result<String, String> {
    let pins = pins(dir)?;
    render_pins(
        "arm-arm",
        "Arm Architecture Reference Manual for A-profile (DDI 0487), pinned by URL and SHA-256 (Arm's terms do not allow redistribution).",
        &pins,
        true,
    )
}

/// `arm-mrs`: the licence notice and README as an inventory, and the
/// `Instructions.json` the notice covers as a pin.
pub fn convert_arm_mrs(dir: &Path) -> Result<String, String> {
    let mut out = tree(
        dir,
        "arm-mrs",
        ARM_MRS_ROOTS,
        "Arm machine-readable specification: licence and README vendored, Instructions.json pinned.",
    )?;
    let pins = pins(dir)?;
    out.push_str(&render_pins("arm-mrs", "", &pins, false)?);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::listed_sizes;

    #[test]
    fn sizes_are_read_from_source_md() {
        let s = "Size: 11294447 sdm.pdf\nSize: x bad.pdf\nnoise\n";
        assert_eq!(
            listed_sizes(s),
            vec![("sdm.pdf".to_owned(), 11_294_447_u64)]
        );
    }
}

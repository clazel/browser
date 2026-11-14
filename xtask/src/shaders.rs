//! The SPIR-V of `clazel-gpu`'s fixed shaders (phase-5.md item 5.17b): compiled
//! from the committed GLSL by `naga`, which is tooling and never ships, and
//! committed beside it. `cargo xtask check` compiles the GLSL again and fails if
//! the committed SPIR-V differs; `cargo xtask tables` rewrites it.
//!
//! The options are fixed here, not taken from `naga`'s defaults, so the output
//! does not depend on how `xtask` was built:
//!
//! - **No coordinate flip** (`ADJUST_COORDINATE_SPACE` off): the GLSL is written
//!   for Vulkan's clip space, y down, already.
//! - **No debug names**, SPIR-V 1.0.
//! - **Every buffer read bounds-checked by `naga`** (`ReadZeroSkipWrite`): an
//!   index past a runtime array's length reads zero. The shaders bound their own
//!   reads too; this is a second bound the GLSL cannot forget.

use std::path::Path;

use naga::back::spv;
use naga::proc::{BoundsCheckPolicies, BoundsCheckPolicy};
use naga::valid::{Capabilities, ValidationFlags, Validator};

/// Where the shaders are.
pub const DIR: &str = "crates/clazel-gpu/shaders";

/// Each GLSL source and its stage; the SPIR-V is the same name with `.spv`.
const SOURCES: &[(&str, naga::ShaderStage)] = &[
    ("quad.vert", naga::ShaderStage::Vertex),
    ("quad.frag", naga::ShaderStage::Fragment),
];

/// The SPIR-V words of one GLSL source, as little-endian bytes.
pub fn compile(source: &str, stage: naga::ShaderStage) -> Result<Vec<u8>, String> {
    let mut frontend = naga::front::glsl::Frontend::default();
    let module = frontend
        .parse(&naga::front::glsl::Options::from(stage), source)
        .map_err(|e| e.emit_to_string(source))?;
    // Push constants ("immediates" to naga) are core Vulkan 1.0; nothing else is
    // enabled.
    let info = Validator::new(ValidationFlags::all(), Capabilities::IMMEDIATES)
        .validate(&module)
        .map_err(|e| format!("{e:?}"))?;
    let checked = BoundsCheckPolicies {
        index: BoundsCheckPolicy::ReadZeroSkipWrite,
        buffer: BoundsCheckPolicy::ReadZeroSkipWrite,
        image_load: BoundsCheckPolicy::ReadZeroSkipWrite,
        binding_array: BoundsCheckPolicy::ReadZeroSkipWrite,
    };
    let options = spv::Options {
        lang_version: (1, 0),
        flags: spv::WriterFlags::empty(),
        bounds_check_policies: checked,
        ..spv::Options::default()
    };
    let words = spv::write_vec(&module, &info, &options, None).map_err(|e| format!("{e:?}"))?;
    Ok(words.iter().flat_map(|w| w.to_le_bytes()).collect())
}

/// Compare (or, with `write`, rewrite) the committed SPIR-V. Returns (problems,
/// notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let (mut problems, mut notes) = (Vec::new(), Vec::new());
    for (name, stage) in SOURCES {
        let src_path = format!("{DIR}/{name}");
        let out_path = format!("{DIR}/{name}.spv");
        let fresh = match std::fs::read_to_string(&src_path)
            .map_err(|e| e.to_string())
            .and_then(|s| compile(&s, *stage))
        {
            Ok(b) => b,
            Err(e) => {
                problems.push(format!("{src_path}: {e}"));
                continue;
            }
        };
        let current = std::fs::read(Path::new(&out_path)).ok();
        if current.as_deref() == Some(fresh.as_slice()) {
            notes.push(format!("{out_path}: up to date ({} bytes)", fresh.len()));
        } else if write {
            match std::fs::write(&out_path, &fresh) {
                Ok(()) => notes.push(format!("{out_path}: written ({} bytes)", fresh.len())),
                Err(e) => problems.push(format!("{out_path}: {e}")),
            }
        } else if current.is_none() {
            problems.push(format!("{out_path}: missing; run `cargo xtask tables`"));
        } else {
            problems.push(format!(
                "{out_path}: stale (differs from {src_path} compiled by xtask/src/shaders.rs); \
                 run `cargo xtask tables` and commit the result"
            ));
        }
    }
    (problems, notes)
}

#[cfg(test)]
mod tests {
    use super::compile;

    #[test]
    fn compiles_and_is_deterministic() -> Result<(), String> {
        let src =
            "#version 450\nlayout(location = 0) out vec4 c;\nvoid main() { c = vec4(1.0); }\n";
        let a = compile(src, naga::ShaderStage::Fragment)?;
        let b = compile(src, naga::ShaderStage::Fragment)?;
        assert_eq!(a, b);
        // The SPIR-V magic number, little-endian.
        assert_eq!(a.get(..4), Some(&[0x03, 0x02, 0x23, 0x07][..]));
        Ok(())
    }

    #[test]
    fn a_broken_shader_is_an_error() {
        assert!(
            compile(
                "#version 450\nvoid main() { x = 1; }\n",
                naga::ShaderStage::Fragment
            )
            .is_err()
        );
    }
}

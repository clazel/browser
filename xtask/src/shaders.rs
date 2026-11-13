//! The compiled forms of `clazel-gpu`'s fixed shaders (phase-5.md item 5.17b).
//!
//! **Direct3D 12**: shader model 5.0 bytecode compiled from the committed HLSL by
//! `vkd3d-compiler` ([`VKD3D`]), an external tool at one stated version, and
//! committed beside it. `cargo xtask check` checks each container's header
//! everywhere, and compiles the HLSL again and compares only where that version
//! is installed; elsewhere its output says the comparison was not made.
//!
//! **Vulkan**: SPIR-V compiled
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

/// The HLSL source of the Direct3D 12 shaders, in [`DIR`].
const HLSL: &str = "quad.hlsl";

/// Each Direct3D shader: the file it is stored in, its entry point and its
/// profile. Shader model 5.0 bytecode ("DXBC"), which Direct3D 12 loads without
/// the signature DXIL needs (phase-5.md item 5.17b).
const D3D: &[(&str, &str, &str)] = &[
    ("quad.hlsl.vs.dxbc", "quad_vertex", "vs_5_0"),
    ("quad.hlsl.ps.dxbc", "quad_fragment", "ps_5_0"),
];

/// The compiler of the Direct3D shaders and the one version whose output is
/// committed: the vkd3d project's `vkd3d-compiler`, tooling that never ships.
/// No HLSL compiler is a Rust crate, so unlike the SPIR-V this cannot be compiled
/// by `xtask` itself: the comparison is made only where this version is on
/// `PATH`, and a note says so where it is not. (The bytes were compiled by
/// Fedora's `vkd3d-compiler-1.19-2.fc45` on aarch64.)
const VKD3D: &str = "vkd3d-compiler";
/// See [`VKD3D`]: what its `--version` must contain.
const VKD3D_VERSION: &str = "vkd3d-shader 1.19";

/// Whether [`VKD3D`] at [`VKD3D_VERSION`] can be run, or why not.
fn vkd3d() -> Result<(), String> {
    let out = std::process::Command::new(VKD3D)
        .arg("--version")
        .output()
        .map_err(|e| format!("{VKD3D} cannot be run ({e})"))?;
    let text = String::from_utf8_lossy(&out.stdout);
    if out.status.success() && text.trim_end().ends_with(VKD3D_VERSION) {
        Ok(())
    } else {
        Err(format!(
            "{VKD3D} is not at `{VKD3D_VERSION}` (it says {:?})",
            text.trim()
        ))
    }
}

/// `source` compiled by [`VKD3D`]: the source on its standard input, the
/// bytecode from its standard output.
fn compile_hlsl(source: &str, entry: &str, profile: &str) -> Result<Vec<u8>, String> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let mut child = Command::new(VKD3D)
        .args(["-x", "hlsl", "-b", "dxbc-tpf", "-p", profile, "-e", entry])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("{VKD3D}: {e}"))?;
    // The source is far smaller than a pipe's buffer, so writing it all before
    // reading cannot block.
    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(source.as_bytes())
            .map_err(|e| format!("{VKD3D}: {e}"))?;
    }
    let out = child
        .wait_with_output()
        .map_err(|e| format!("{VKD3D}: {e}"))?;
    if out.status.success() {
        Ok(out.stdout)
    } else {
        Err(format!(
            "{VKD3D} failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        ))
    }
}

/// What every DXBC container says of itself (Microsoft documents the container
/// only through `D3DGetBlobPart`; the layout is the one vkd3d and Wine read): the
/// magic `DXBC`, a 16-byte checksum, the version 1, the total size, and a count
/// of chunks, each at a listed offset with a four-character tag. A shader has a
/// code chunk, `SHEX` or `SHDR`. This is checked on every machine; it does not
/// show that the bytes are the source's.
pub fn dxbc_problem(bytes: &[u8]) -> Option<String> {
    let word = |at: usize| {
        let b = bytes.get(at..at.checked_add(4)?)?;
        Some(u32::from_le_bytes(b.try_into().ok()?))
    };
    if bytes.get(..4) != Some(b"DXBC") {
        return Some("does not begin with `DXBC`".to_owned());
    }
    if word(20) != Some(1) {
        return Some("container version is not 1".to_owned());
    }
    if word(24).and_then(|n| usize::try_from(n).ok()) != Some(bytes.len()) {
        return Some("the size in the header is not the file's".to_owned());
    }
    let Some(count) = word(28).and_then(|n| usize::try_from(n).ok()) else {
        return Some("no chunk count".to_owned());
    };
    let mut code = false;
    for i in 0..count {
        let tag = i
            .checked_mul(4)
            .and_then(|o| o.checked_add(32))
            .and_then(word)
            .and_then(|at| usize::try_from(at).ok())
            .and_then(|at| bytes.get(at..at.checked_add(4)?));
        match tag {
            Some(b"SHEX" | b"SHDR") => code = true,
            Some(_) => {}
            None => return Some(format!("chunk {i} lies outside the file")),
        }
    }
    (!code).then(|| "no code chunk (`SHEX` or `SHDR`)".to_owned())
}

/// The Direct3D shaders: check each stored container, and compare it with (or,
/// with `write`, rewrite it from) the HLSL where [`VKD3D`] is installed.
fn run_d3d(write: bool, problems: &mut Vec<String>, notes: &mut Vec<String>) {
    let src_path = format!("{DIR}/{HLSL}");
    let source = match std::fs::read_to_string(&src_path) {
        Ok(s) => s,
        Err(e) => {
            problems.push(format!("{src_path}: {e}"));
            return;
        }
    };
    let compiler = vkd3d();
    if let Err(why) = &compiler {
        notes.push(format!(
            "Direct3D shaders NOT compared with {src_path}: {why}; only their containers are checked"
        ));
    }
    for (name, entry, profile) in D3D {
        let out_path = format!("{DIR}/{name}");
        let current = std::fs::read(Path::new(&out_path)).ok();
        if compiler.is_ok() {
            match compile_hlsl(&source, entry, profile) {
                Err(e) => problems.push(format!("{src_path} ({entry}): {e}")),
                Ok(fresh) if current.as_deref() == Some(fresh.as_slice()) => {
                    notes.push(format!("{out_path}: up to date ({} bytes)", fresh.len()));
                }
                Ok(fresh) if write => match std::fs::write(&out_path, &fresh) {
                    Ok(()) => notes.push(format!("{out_path}: written ({} bytes)", fresh.len())),
                    Err(e) => problems.push(format!("{out_path}: {e}")),
                },
                Ok(_) => problems.push(format!(
                    "{out_path}: missing or stale (differs from {src_path} compiled by \
                     {VKD3D}, `{VKD3D_VERSION}`); run `cargo xtask tables` and commit the result"
                )),
            }
        }
        match std::fs::read(Path::new(&out_path)) {
            Ok(bytes) => {
                if let Some(why) = dxbc_problem(&bytes) {
                    problems.push(format!("{out_path}: not a DXBC shader: {why}"));
                }
            }
            Err(e) => problems.push(format!("{out_path}: {e}")),
        }
    }
}

/// Compare (or, with `write`, rewrite) the committed SPIR-V and Direct3D
/// bytecode. Returns (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let (mut problems, mut notes) = (Vec::new(), Vec::new());
    run_d3d(write, &mut problems, &mut notes);
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

    /// The smallest container the check accepts, then each way it can be wrong.
    #[test]
    fn a_dxbc_container_is_recognized() {
        use super::dxbc_problem;
        let mut good = Vec::new();
        good.extend_from_slice(b"DXBC");
        good.extend_from_slice(&[0; 16]);
        good.extend_from_slice(&1u32.to_le_bytes());
        good.extend_from_slice(&44u32.to_le_bytes());
        good.extend_from_slice(&1u32.to_le_bytes());
        good.extend_from_slice(&36u32.to_le_bytes());
        good.extend_from_slice(b"SHEX");
        good.extend_from_slice(&0u32.to_le_bytes());
        assert_eq!(dxbc_problem(&good), None);
        let with = |at: usize, byte: u8| {
            let mut b = good.clone();
            if let Some(x) = b.get_mut(at) {
                *x = byte;
            }
            b
        };
        assert!(dxbc_problem(&with(0, b'X')).is_some_and(|w| w.contains("DXBC")));
        assert!(dxbc_problem(&with(20, 2)).is_some_and(|w| w.contains("version")));
        assert!(dxbc_problem(&with(24, 45)).is_some_and(|w| w.contains("size")));
        assert!(dxbc_problem(&with(32, 41)).is_some_and(|w| w.contains("outside")));
        assert!(dxbc_problem(&with(36, b'X')).is_some_and(|w| w.contains("code chunk")));
        assert!(dxbc_problem(good.get(..30).unwrap_or(&[])).is_some());
        assert!(dxbc_problem(&[]).is_some());
    }

    /// The committed Direct3D shaders are containers, whatever compiled them.
    #[test]
    fn the_committed_direct3d_shaders_are_containers() -> Result<(), String> {
        for (name, _, _) in super::D3D {
            let path = format!("../{}/{name}", super::DIR);
            let bytes = std::fs::read(&path).map_err(|e| format!("{path}: {e}"))?;
            assert_eq!(super::dxbc_problem(&bytes), None, "{path}");
        }
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

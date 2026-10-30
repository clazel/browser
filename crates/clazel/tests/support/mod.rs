//! Shared by the process tests of item 2.16: the binaries of
//! `clazel-renderer`, rebuilt before use so a stale one is never run.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

/// The directory holding `clazel-renderer` and `clazel-adversary`, after
/// `cargo build -p clazel-renderer` (cheap when nothing changed).
fn binaries() -> &'static Path {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(|| {
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        let built = Command::new(cargo)
            .args(["build", "--quiet", "-p", "clazel-renderer"])
            .status();
        assert!(
            built.is_ok_and(|s| s.success()),
            "cannot build clazel-renderer"
        );
        std::env::current_exe()
            .ok()
            .and_then(|exe| exe.parent()?.parent().map(Path::to_path_buf))
            .unwrap_or_default()
    })
}

/// The binary `name` (`clazel-renderer` or `clazel-adversary`).
pub fn binary(name: &str) -> PathBuf {
    binaries().join(format!("{name}{}", std::env::consts::EXE_SUFFIX))
}

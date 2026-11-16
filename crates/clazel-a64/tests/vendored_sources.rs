//! The vendored instruction-set sources are the ones the generated inventories
//! list (docs/phases/jit.md item J.2): every listed file exists with the
//! listed size, and the pinned file has a well-formed pin. `cargo xtask
//! testdata` checks the hashes; nothing here reads the content yet.

use std::path::Path;

mod sail_arm {
    include!("generated/sail_arm.rs");
}
mod arm_mrs {
    include!("generated/arm_mrs.rs");
}
mod arm_arm {
    include!("generated/arm_arm.rs");
}

#[test]
fn the_arm_arm_is_pinned_and_not_vendored() {
    assert_eq!(arm_arm::PINS.len(), 1);
    for p in arm_arm::PINS {
        assert_eq!(p.sha256.len(), 64, "{}", p.file);
        assert!(p.size > 0, "{}", p.file);
        assert!(
            !Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests")
                .join("data")
                .join("arm-arm")
                .join(p.file)
                .exists(),
            "{}: Arm's PDF must not be vendored",
            p.file
        );
    }
}

fn dir(suite: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("data")
        .join(suite)
}

fn check(suite: &str, files: &[(&str, u64)]) {
    assert!(!files.is_empty(), "{suite}: empty inventory");
    for (path, size) in files {
        let len = std::fs::metadata(dir(suite).join(path))
            .map(|m| m.len())
            .ok();
        assert_eq!(len, Some(*size), "{suite}/{path}");
    }
}

#[test]
fn sail_arm_files_have_their_listed_sizes() {
    let files: Vec<_> = sail_arm::FILES.iter().map(|f| (f.path, f.size)).collect();
    check("sail-arm", &files);
}

#[test]
fn arm_mrs_files_have_their_listed_sizes() {
    let files: Vec<_> = arm_mrs::FILES.iter().map(|f| (f.path, f.size)).collect();
    check("arm-mrs", &files);
}

#[test]
fn instructions_json_is_pinned_and_not_vendored() {
    assert_eq!(arm_mrs::PINS.len(), 1);
    for p in arm_mrs::PINS {
        assert_eq!(p.sha256.len(), 64, "{}", p.file);
        assert!(p.size > 0, "{}", p.file);
        assert!(
            !dir("arm-mrs").join(p.file).exists(),
            "{}: 116 MB, pinned only",
            p.file
        );
    }
}

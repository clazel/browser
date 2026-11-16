//! The vendored instruction-set sources are the ones the generated inventories
//! list (docs/phases/jit.md item J.2): every listed file exists with the
//! listed size, and the pinned file has a well-formed pin. `cargo xtask
//! testdata` checks the hashes; nothing here reads the content yet.

use std::path::Path;

mod acl2_x86isa {
    include!("generated/acl2_x86isa.rs");
}
mod acl2_rtl {
    include!("generated/acl2_rtl.rs");
}
mod sail_x86_from_acl2 {
    include!("generated/sail_x86_from_acl2.rs");
}
mod intel_sdm {
    include!("generated/intel_sdm.rs");
}

fn check(suite: &str, files: &[(&str, u64)]) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("data")
        .join(suite);
    assert!(!files.is_empty(), "{suite}: empty inventory");
    for (path, size) in files {
        let len = std::fs::metadata(dir.join(path)).map(|m| m.len()).ok();
        assert_eq!(len, Some(*size), "{suite}/{path}");
    }
}

#[test]
fn acl2_x86isa_files_have_their_listed_sizes() {
    let files: Vec<_> = acl2_x86isa::FILES
        .iter()
        .map(|f| (f.path, f.size))
        .collect();
    check("acl2-x86isa", &files);
}

#[test]
fn acl2_rtl_files_have_their_listed_sizes() {
    let files: Vec<_> = acl2_rtl::FILES.iter().map(|f| (f.path, f.size)).collect();
    check("acl2-rtl", &files);
}

#[test]
fn sail_x86_from_acl2_files_have_their_listed_sizes() {
    let files: Vec<_> = sail_x86_from_acl2::FILES
        .iter()
        .map(|f| (f.path, f.size))
        .collect();
    check("sail-x86-from-acl2", &files);
}

#[test]
fn the_sdm_is_pinned_and_not_vendored() {
    assert_eq!(intel_sdm::PINS.len(), 1);
    for p in intel_sdm::PINS {
        assert_eq!(p.sha256.len(), 64, "{}", p.file);
        assert!(p.size > 0, "{}", p.file);
        let here = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("data")
            .join("intel-sdm")
            .join(p.file);
        assert!(
            !here.exists(),
            "{}: Intel's PDF must not be vendored",
            p.file
        );
    }
}

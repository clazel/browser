//! The one crate with `unsafe` (CLAUDE.md rule 1): safe wrappers around the
//! few calls that put a process into an OS sandbox.
//!
//! It makes **no policy decisions**. It takes data that safe, verified code
//! already built (a BPF program as a slice of instructions, a Seatbelt
//! profile as a string) and hands it to the operating system. What a sandbox
//! allows is decided in `clazel-sandbox`, and the glue that connects the two
//! is in the renderer (Phase 2, item 2.15).
//!
//! Every `unsafe` here is one block holding one call to a foreign function
//! from the list in `xtask/src/sys.rs`, with a `// SAFETY:` comment citing
//! the man page. `cargo xtask check` enforces that, and every change to this
//! crate is audited (`docs/SYS-AUDITS.md`). No public function is `unsafe`,
//! and none panics.
//!
//! Which calls exist depends on the target: `linux` on Linux, `macos` on
//! macOS, `windows` on Windows (which starts the renderer confined, since a
//! running process cannot be moved into an AppContainer). On other targets
//! the crate is empty, so a renderer cannot be sandboxed there, and the
//! renderer must refuse to run.

use std::fmt;

#[cfg(target_os = "linux")]
pub mod linux;
#[cfg(target_os = "macos")]
pub mod macos;
#[cfg(windows)]
pub mod windows;

/// An operating system error number (`errno`), as a foreign call left it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Errno(pub i32);

impl Errno {
    /// The value reported when the OS gave no error number.
    pub const UNKNOWN: Errno = Errno(-1);

    /// The calling thread's `errno`. Call it immediately after the foreign
    /// call that failed, with nothing in between.
    #[cfg(any(target_os = "linux", target_os = "macos", windows))]
    pub(crate) fn last() -> Errno {
        Errno(std::io::Error::last_os_error().raw_os_error().unwrap_or(-1))
    }
}

impl fmt::Display for Errno {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} (os error {})",
            std::io::Error::from_raw_os_error(self.0),
            self.0
        )
    }
}

impl std::error::Error for Errno {}

#[cfg(test)]
mod tests {
    use super::Errno;

    #[test]
    fn errno_displays_its_number() {
        assert!(Errno(1).to_string().contains("os error 1"));
        assert_eq!(Errno::UNKNOWN, Errno(-1));
    }
}

//! The one crate with `unsafe` (CLAUDE.md rule 1): safe wrappers around the
//! few calls that put a process into an OS sandbox, and the one call that
//! reads cryptographically secure random bytes from the OS ([`fill_random`]).
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
//! renderer must refuse to run. [`fill_random`] exists on every target and
//! returns [`RandomError::Unsupported`] where there is no OS source.
//!
//! Randomness is for the TLS client (the X25519 scalar, the ClientHello
//! random and the legacy session id). `fill_random` only fills the buffer it
//! is given; nothing in the workspace calls it yet.

use std::fmt;

#[cfg(target_os = "linux")]
pub mod linux;
#[cfg(target_os = "macos")]
pub mod macos;
#[cfg(windows)]
pub mod windows;

#[cfg(target_os = "linux")]
use linux::fill_random as os_fill_random;
#[cfg(target_os = "macos")]
use macos::fill_random as os_fill_random;
#[cfg(windows)]
use windows::fill_random as os_fill_random;

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

/// Why [`fill_random`] did not fill the buffer. After an error the buffer's
/// contents are unspecified and must not be used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RandomError {
    /// The OS call failed with this error number (`getrandom` on Linux,
    /// `getentropy` on macOS). `EINTR` is retried, never reported.
    Os(Errno),
    /// `BCryptGenRandom` returned this `NTSTATUS` (Windows).
    Status(i32),
    /// The OS reported a byte count of 0 or more than was asked for, so the
    /// fill cannot make progress.
    BadCount,
    /// This target has no OS random source that the crate calls.
    Unsupported,
}

impl fmt::Display for RandomError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RandomError::Os(e) => write!(f, "the OS random source failed: {e}"),
            RandomError::Status(s) => write!(f, "BCryptGenRandom failed: NTSTATUS {s:#010x}"),
            RandomError::BadCount => f.write_str("the OS random source returned a bad count"),
            RandomError::Unsupported => f.write_str("no OS random source on this target"),
        }
    }
}

impl std::error::Error for RandomError {}

/// Fill `buf` with cryptographically secure random bytes from the OS:
/// `getrandom(2)` with flags 0 on Linux (it blocks until the kernel's pool is
/// initialised; `/dev/urandom` is never read), `getentropy(2)` on macOS, and
/// `BCryptGenRandom` with the system-preferred RNG on Windows. A buffer
/// larger than one call allows is filled in chunks, short reads are
/// continued and `EINTR` is retried. An empty buffer succeeds without a
/// call. It never panics, and it decides nothing about what the bytes are
/// for.
pub fn fill_random(buf: &mut [u8]) -> Result<(), RandomError> {
    os_fill_random(buf)
}

/// No OS random source on this target: fail closed.
#[cfg(not(any(target_os = "linux", target_os = "macos", windows)))]
fn os_fill_random(_buf: &mut [u8]) -> Result<(), RandomError> {
    Err(RandomError::Unsupported)
}

#[cfg(test)]
mod tests {
    use super::Errno;

    #[test]
    fn errno_displays_its_number() {
        assert!(Errno(1).to_string().contains("os error 1"));
        assert_eq!(Errno::UNKNOWN, Errno(-1));
    }
}

/// [`fill_random`] against the real OS source. Miri cannot run foreign
/// calls, so each test is skipped there.
#[cfg(all(test, any(target_os = "linux", target_os = "macos", windows)))]
mod random_tests {
    use super::{RandomError, fill_random};
    #[cfg(target_os = "linux")]
    use crate::linux::RANDOM_MAX_PER_CALL;
    #[cfg(target_os = "macos")]
    use crate::macos::RANDOM_MAX_PER_CALL;
    #[cfg(windows)]
    use crate::windows::RANDOM_MAX_PER_CALL;

    /// The largest buffer a test allocates (64 MiB).
    const TEST_LIMIT: usize = 67_108_864;

    #[test]
    #[cfg_attr(miri, ignore)]
    fn two_fills_differ() -> Result<(), RandomError> {
        let mut a = [0u8; 32];
        let mut b = [0u8; 32];
        fill_random(&mut a)?;
        fill_random(&mut b)?;
        assert_ne!(a, b);
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn an_empty_buffer_succeeds() {
        assert_eq!(fill_random(&mut []), Ok(()));
    }

    /// 1 MiB, and one byte more than one call allows where that fits in
    /// [`TEST_LIMIT`] (Linux: 32 MiB; macOS: 257 bytes; not Windows: 4 GiB).
    /// The last 64 bytes are checked too, so an unfilled last chunk shows.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn a_fill_larger_than_one_call_succeeds() -> Result<(), RandomError> {
        let sizes = [1_048_576, RANDOM_MAX_PER_CALL.saturating_add(1)];
        for n in sizes.into_iter().filter(|n| *n <= TEST_LIMIT) {
            let mut buf = vec![0u8; n];
            fill_random(&mut buf)?;
            assert!(buf.iter().any(|b| *b != 0), "{n} bytes all zero");
            let tail = buf.rchunks(64).next().unwrap_or(&[]);
            assert!(tail.iter().any(|b| *b != 0), "{n}: last 64 bytes all zero");
        }
        Ok(())
    }

    /// A crude sanity check, not a statistical test: 4 KiB are not all one
    /// byte value.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn four_kib_are_not_all_the_same_byte() -> Result<(), RandomError> {
        let mut buf = [0u8; 4096];
        fill_random(&mut buf)?;
        let first = buf.first().copied();
        assert!(buf.iter().any(|b| Some(*b) != first));
        Ok(())
    }
}

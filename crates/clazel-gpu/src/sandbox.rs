//! Item 5.21a: the GPU process enters its sandbox, on macOS on Apple silicon.
//!
//! The policy is data from `clazel-sandbox` (`seatbelt::gpu_profile`); the only
//! code that hands it to the OS is `clazel-sys` (`sandbox_init_profile`), whose
//! functions are safe. This module decides the order, which is what the measured
//! profile depends on:
//!
//! 1. make the Metal backend: the device, its command queue and the one fixed
//!    pipeline, compiled from our own shader source (`shaders/quad.metal`);
//! 2. enter the Seatbelt profile, for good;
//! 3. only then may the caller check the blocklist (`Gpu::start`) and read a
//!    message.
//!
//! No byte from a page or a renderer is read before step 2, so a page cannot
//! reach what the warm-up opens except through the connections it leaves open,
//! which is the sandbox's stated weakness (`clazel-sandbox`'s `seatbelt` module).
//! Fail closed: an error in either step ends the GPU process before `GpuReady`,
//! which the crash policy (item 5.17c) counts as a refusal of the machine's GPU.
//!
//! Linux and Windows have no GPU backend yet (item 5.17b's rest), so nothing here
//! enters their policies; `clazel-sandbox` holds them as data.

use std::fmt;

use clazel_sys::macos::{SandboxError, sandbox_init_profile};

use crate::backend::BackendError;
use crate::metal::MetalBackend;

/// Why the GPU process could not start sandboxed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Failure {
    /// Step 1: no usable Metal device, queue or pipeline.
    Device(BackendError),
    /// Step 2: Seatbelt refused the profile.
    Seatbelt(SandboxError),
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Failure::Device(e) => write!(f, "no Metal device: {} ({})", e.what, e.code),
            Failure::Seatbelt(e) => write!(f, "sandbox layer `seatbelt` failed: {e}"),
        }
    }
}

impl std::error::Error for Failure {}

/// Steps 1 and 2: the Metal backend, made before this process entered the GPU
/// process's Seatbelt profile, which it now has. On `Err` the process may or may
/// not be sandboxed and must exit.
pub fn start_metal() -> Result<MetalBackend, Failure> {
    let backend = MetalBackend::new().map_err(Failure::Device)?;
    let profile = clazel_sandbox::seatbelt::gpu_profile();
    sandbox_init_profile(&profile).map_err(Failure::Seatbelt)?;
    Ok(backend)
}

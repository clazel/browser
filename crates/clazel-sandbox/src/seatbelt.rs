//! The macOS Seatbelt (SBPL) profile: `(deny default)` plus the minimum to
//! run.
//!
//! SBPL is Apple's undocumented Scheme-based profile language; there is no
//! standard to cite and nothing here is checked against a reference. The
//! profile is data, rendered by [`render`] from [`RENDERER`], and the
//! integration tests of item 2.16 (a real sandboxed process trying to open
//! files and sockets) are the only check that it denies what it should and
//! allows what a renderer needs. `tests/policies.rs` checks only the shape:
//! it begins `(version 1)` then `(deny default)`, and no rule mentions a
//! file, network, process-creation or process-execution operation.
//!
//! Modelling choices:
//! - The profile is applied (item 2.15) after the process has started and
//!   holds its socket, so it needs no `process-exec`, no `file-read*` for the
//!   binary or libraries (already mapped) and no `network*` (the inherited
//!   socket is used through its descriptor, which `(deny default)` does not
//!   revoke).
//! - Each rule is "allow `operation` with these filters". The three allowed
//!   operations are the least the Rust runtime and allocator are known to
//!   query; if a renderer needs another, 2.16 will show a denial and the rule
//!   is added here with its reason.
//!
//! # The GPU process's profile (phase-5.md item 5.21a)
//!
//! [`GPU`] is the GPU process's profile on macOS (Metal on Apple silicon). It was
//! **measured** on one machine (an Apple M1 Pro, macOS 26.7.2, 2026-11-13) by a process
//! that drew every scene of `clazel-gpu` through the Metal backend, read the pixels
//! back and compared them with the software reference, with Seatbelt's denials read
//! from the system log (`log show --predicate 'sender == "Sandbox"'`).
//!
//! Modelling choices:
//! - **Warm up, then enter.** The GPU process makes its Metal device, its command
//!   queue and its one fixed pipeline (compiling our own shader source, never a
//!   page's) *before* it enters the sandbox and before it reads any message, as the
//!   Linux GPU process opens its device paths before seccomp. Metal then holds the
//!   IOKit connections it needs (`AGXDeviceUserClient`, `IOSurfaceRootUserClient`)
//!   and Seatbelt, which checks `iokit-open-user-client` and `mach-lookup` when a
//!   connection is made, never sees them again. Measured: after that warm-up, a
//!   profile of `(deny default)` alone drew every scene correctly, creating new
//!   IOSurfaces of each scene's size inside it, and the system log showed no denial.
//! - **One rule: `mach-lookup` of `com.apple.MTLCompilerService`** (item 5.23).
//!   5.21a's measurement drew the fixed scenes and needed none. Drawing real pages
//!   (5.23, the renderer's lists of 5.20) then made the sandboxed process abort in
//!   Apple's driver, `AGXMetalG13X`, while compiling a blit program variant
//!   (`findOrCreateDriverProgramVariant<BlitComputeProgramVariant>`) on Metal's
//!   compiler queue, with the system log's `launchd ... denied lookup: name =
//!   com.apple.MTLCompilerService ... Sandbox restriction`. The driver compiles
//!   such variants when first needed, so no warm-up of ours can promise to reach
//!   them all (drawing every scene and every upload offset before entering, tried
//!   the same day, did not prevent it). The service is the one the plan's 5.21a text
//!   names ("the IOKit and Mach services Metal needs"), and Chromium's GPU sandbox
//!   allows it. The cost: a compromised GPU process can send requests to Apple's
//!   Metal compiler, itself a sandboxed XPC service. Measured on the same machine,
//!   2026-11-13: with it, the page-flow test that aborted passes
//!   (`crates/clazel/tests/browse_gpu.rs`), 5.21a's escape attempts are all still
//!   denied (`clazel-gpu`'s `tests/sandbox_macos.rs`), and the only denial logged is
//!   `mach-lookup` of `com.apple.analyticsd` (the driver's telemetry), denied
//!   without effect and left denied.
//! - The renderer's two rules (a signal to itself, three `sysctl` names) are not
//!   copied: the GPU process was not measured to need them.
//! - **What entering first would cost**, measured the same day and not used: a
//!   process that enters before making the device needs `iokit-open-user-client`
//!   for `AGXDeviceUserClient` and `IOSurfaceRootUserClient`, `mach-lookup` of
//!   `com.apple.MTLCompilerService`, `file-read*` under
//!   `/System/Library/Extensions` (the driver bundle), `sysctl-read` of four names,
//!   and `file-read-metadata` of its own executable's directory; without any one of
//!   these it fails or crashes. That profile would also need the executable's path
//!   as a parameter. Warming up first needs none of it.
//! - **No WindowServer.** Making a Metal device looks up
//!   `com.apple.windowserver.active`; denied (in the measurement of entering first)
//!   it changed nothing, and after the warm-up the profile denies it like
//!   everything else.
//! - **Weaker than the renderer's, though its text is shorter.** The process holds
//!   open connections to the GPU's kernel driver and to IOSurface, through which it
//!   can make every call those user clients accept: that kernel surface is what the
//!   renderer's sandbox has and this one does not, and Seatbelt cannot filter it.
//!   The Metal driver's own code also runs in the process.
//! - **An unmeasured driver.** Another GPU or another macOS version may open
//!   something after the warm-up. Then a Metal call fails inside the sandbox, the
//!   GPU process exits, and the crash policy (item 5.17c) acts; the profile is never
//!   widened at run time.

/// One `(allow ...)` rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rule {
    /// The SBPL operation, such as `sysctl-read`.
    pub operation: &'static str,
    /// Filters, each already a complete SBPL form such as `(target self)`.
    pub filters: &'static [&'static str],
    /// Why the renderer needs it.
    pub reason: &'static str,
}

/// The rules after `(deny default)`.
pub const RENDERER: &[Rule] = &[
    Rule {
        operation: "signal",
        filters: &["(target self)"],
        reason: "the Rust runtime may raise a signal on itself (abort on panic)",
    },
    Rule {
        operation: "sysctl-read",
        filters: &["(sysctl-name \"hw.pagesize\" \"hw.ncpu\" \"hw.logicalcpu\")"],
        reason: "the allocator and std::thread::available_parallelism read these",
    },
];

/// The GPU process's rules after `(deny default)`, entered after the warm-up
/// (module documentation).
pub const GPU: &[Rule] = &[Rule {
    operation: "mach-lookup",
    filters: &["(global-name \"com.apple.MTLCompilerService\")"],
    reason: "Apple's driver compiles blit program variants when first needed, through \
             Metal's compiler service (measured, item 5.23)",
}];

/// Render `rules` as an SBPL profile.
pub fn render(rules: &[Rule]) -> String {
    let mut out = String::from("(version 1)\n(deny default)\n");
    for r in rules {
        out.push_str("(allow ");
        out.push_str(r.operation);
        for f in r.filters {
            out.push(' ');
            out.push_str(f);
        }
        out.push_str(")\n");
    }
    out
}

/// The renderer's profile.
pub fn renderer_profile() -> String {
    render(RENDERER)
}

/// The GPU process's profile, to enter after making the Metal device, queue and
/// pipeline (module documentation).
pub fn gpu_profile() -> String {
    render(GPU)
}

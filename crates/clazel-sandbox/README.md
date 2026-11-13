# clazel-sandbox

The sandbox policies for Clazel renderer processes and the GPU process, as
plain data. Part of
[Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

This crate **decides what a renderer may do and produces the policy; it does
not apply it.** It has no dependencies, no `unsafe` and makes no system calls.
Applying a policy to a process is a separate step (Phase 2 item 2.15), which
needs the OS calls that only `clazel-sys` is allowed to make.

## What it is

There is no single standard here; each policy follows the OS it targets.

- **Linux seccomp-BPF** (`syscalls`, `seccomp`): a syscall allowlist with the
  reason for each entry (read and write on the inherited socket, `exit_group`,
  memory management, futex; nothing that opens, connects, forks, executes or
  passes descriptors), with numbers for x86-64 and aarch64, and a generator
  for the classic BPF program: check the architecture field first, then one
  comparison per allowed number, otherwise kill the process.
- **Linux Landlock** (`landlock`): a ruleset that handles every filesystem,
  TCP and scope right and allows none, with `for_abi` to drop rights newer
  than the running kernel's Landlock ABI.
- **Linux namespaces** (`namespaces`): user, mount, PID, network and IPC, with
  their `CLONE_NEW*` flags.
- **macOS Seatbelt** (`seatbelt`): an SBPL profile, `(deny default)` plus the
  minimum the Rust runtime needs. SBPL is Apple's undocumented language, so
  there is no standard to cite.
- **A classic-BPF validator and interpreter** (`interp`), written from the
  kernel's `filter.rst` and `seccomp_filter.rst`, used to run generated
  programs.

Out of scope: applying any of it, argument filters (selection is by syscall
number only), other architectures, and sandboxing on other platforms.

## Verification

Tier 1: Kani bounded model checking shows the code never panics, overflows or
indexes out of bounds on any input within the harnesses' stated bounds. It is
not a Verus-proven functional-correctness tier. Current numbers are in the
[status table](../../README.md#verification-status).

- **Harnesses** (`src/proofs.rs`, run by `cargo kani`): the generator never
  panics and produces a valid program, and the program allows exactly the
  list, for symbolic allowlists of 0 to 3 numbers. For the real allowlist, on
  each architecture, the program allows exactly the list for **every** 32-bit
  syscall number, and kills every other architecture value. The validator and
  interpreter never panic on any program of up to two instructions.
- **Tests:** `tests/policies.rs` repeats the sweep over syscall numbers below
  1024 (and wrong architectures and x32 numbers) as plain tests.
  `tests/vendored.rs` re-derives every syscall number and constant from the
  vendored Linux v6.12 headers and documents in `vendor/linux/`, so none is
  from memory.
- **Known gaps:** Kani proves the pointwise generator (`insn_at`), not the
  `Vec` collection in `generate` (CBMC ran out of memory modelling it); a test
  checks the collected program equals the one the harnesses use. The
  interpreter's rejection rules are the conservative reading of `filter.rst`,
  because the kernel's `seccomp.c` is not vendored. The SBPL profile is
  unchecked: only the integration tests of Phase 2 item 2.16, running a real
  sandboxed process, can show it denies what it should.

## Trust

**The cBPF interpreter is trusted**: it models the kernel, so the exhaustive
checks are only as good as it is. That is why this crate targets Tier 1 and
not a Verus spec of BPF. Beyond that, the proofs assume the Rust compiler and
Kani, and that the OS enforces the policy it is given (macOS Seatbelt; Linux
seccomp, Landlock and namespaces), which is in the trusted computing base. The
full list is in [docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false` for now). It has no
dependencies.

```rust
use clazel_sandbox::interp::{SeccompData, run, validate};
use clazel_sandbox::seccomp::{SECCOMP_RET_ALLOW, SECCOMP_RET_KILL_PROCESS, renderer_program};
use clazel_sandbox::syscalls::Arch;
use clazel_sandbox::{landlock, namespaces, seatbelt};

// Linux: the seccomp program is data; nothing is applied here.
let program = renderer_program(Arch::X86_64).expect("fits in a cBPF program");
validate(&program).expect("a valid program");
let arch = Arch::X86_64.audit_arch();
assert_eq!(run(&program, &SeccompData::new(0, arch)), Ok(SECCOMP_RET_ALLOW)); // read
assert_eq!(run(&program, &SeccompData::new(2, arch)), Ok(SECCOMP_RET_KILL_PROCESS)); // open

// The other policies are data too.
assert!(landlock::RENDERER.allows_nothing());
let flags = namespaces::renderer_unshare_flags();
assert_ne!(flags & namespaces::CLONE_NEWNET, 0);

// macOS: the SBPL text, to hand to the OS elsewhere.
assert!(seatbelt::renderer_profile().starts_with("(version 1)\n(deny default)\n"));
```

## The GPU process (item 5.21a)

A GPU driver cannot run in the renderer's sandbox, so the GPU process has its
own policies. **This sandbox is weaker than the renderer's on every OS**, and
how is stated per OS below. An unlisted driver that the sandbox breaks makes the
GPU process fail and exit; the crash policy (`clazel-gpu`, item 5.17c) then
moves the tab to software, or on macOS, which has no software fallback, shows
the notice. The sandbox is never widened at run time.

On every OS the GPU process **warms up, then enters**. Before installing the
sandbox and before reading any message, it loads its driver, makes its device
and compiles its fixed pipelines from our own shader source, never a page's.

| OS | Policy | State |
|----|--------|-------|
| macOS | `seatbelt::GPU`: `(deny default)` and one rule, `mach-lookup` of `com.apple.MTLCompilerService` (item 5.23) | **measured** on one machine (below); entered by `clazel_gpu::sandbox::start_metal` |
| Linux | `namespaces::GPU`, Landlock with no rule, and `syscalls::GPU_EXTRA` added to the renderer's list (`seccomp::gpu_program`); with a hardware device also `GPU_HARDWARE_EXTRA` (`seccomp::gpu_hardware_program`) | **measured** on lavapipe on aarch64 only (below); the hardware addition is **not measured**; entered by `clazel_gpu::sandbox::start_vulkan` |
| Windows | `appcontainer::GPU_*`: the renderer's policy less `WIN32K`, plus `registryRead`, container `clazel.gpu` | decided by the plan's measurement (2026-11-04); data only, nothing starts a process with it yet |

### macOS, measured

Measured on an Apple M1 Pro, macOS 26.7.2, on 2026-11-13. The method:
- A process drew every scene of `clazel-gpu` (the clear and the fixed pipeline, 7
  lists) through the Metal backend, read the pixels back and compared them with
  the software reference.
- Seatbelt's denials were read from the system log.

After the warm-up, `(deny default)` alone drew every list correctly and logged
no denial. This includes making a new IOSurface of each scene's size inside the
sandbox. Metal opens its IOKit connections during the warm-up, and Seatbelt
checks a connection only when it is opened.

Entering *before* the warm-up was measured too, and is not used. It needs six
rules, and without any one of them Metal fails or the process crashes:
- `iokit-open-user-client` for `AGXDeviceUserClient` and for `IOSurfaceRootUserClient`;
- `mach-lookup` of `com.apple.MTLCompilerService`;
- `file-read*` under `/System/Library/Extensions`;
- `sysctl-read` of four names;
- `file-read-metadata` of the executable's directory.

Making a device also looks up `com.apple.windowserver.active`. Denying it
changed nothing, and the profile denies it.

**Item 5.23 added one rule.** Drawing real pages (5.20's lists, a second page's
glyph uploads) made the sandboxed process abort inside Apple's driver while it
compiled a blit program variant on Metal's compiler queue; the system log showed
the lookup of `com.apple.MTLCompilerService` denied. The driver compiles such
variants when first needed, so a warm-up cannot promise to reach them (drawing
every scene and every upload offset before entering did not prevent it). With
`(allow mach-lookup (global-name "com.apple.MTLCompilerService"))` the page flow
passes, the escape attempts below are still denied, and the only denial logged is
`com.apple.analyticsd` (the driver's telemetry), without effect. The cost: a
compromised GPU process can send requests to Metal's compiler service, an XPC
service sandboxed by Apple; Chromium's GPU sandbox allows the same. The plan's
5.21a text names "the IOKit and Mach services Metal needs".

`clazel-gpu`'s `tests/sandbox_macos.rs` repeats the measurement in child
processes. It attempts each of the following from inside the sandbox, after an
unsandboxed control of the same attempt succeeds:

| Attempt | Result |
|---------|--------|
| Draw every scene, read back, compare with the reference | **allowed**, equal to the unsandboxed control |
| Make the Metal device *after* entering | denied: `MTLCreateSystemDefaultDevice` fails |
| Read a file the test wrote | denied, `EPERM` |
| Create a file in the test's directory | denied, `EPERM` |
| List the home directory | denied, `EPERM` |
| Connect to a loopback TCP port | denied, `EPERM` (`network-outbound`) |
| Bind a UDP socket | denied, `EPERM` (`network-bind`) |
| Connect to a Unix socket | denied, `EPERM` |
| Reach the WindowServer (`CGSessionCopyCurrentDictionary`) | denied: no session (`mach-lookup com.apple.windowserver.active`) |
| `fork` | denied, `EPERM` (`process-fork`) |
| Start `/usr/bin/true` | denied, `EPERM` |

**How it is weaker than the renderer's.**
- The process keeps open connections to the GPU's kernel driver
  (`AGXDeviceUserClient`) and to IOSurface. It can make any call those user
  clients accept, and Seatbelt cannot filter them.
- The Metal driver's own code runs in the process.

The profile text is shorter than the renderer's only because the warm-up does the
opening.

**Not measured:**
- other Macs, GPUs and macOS versions;
- an Intel Mac (not supported);
- a GPU process running for a long time, or under memory pressure;
- the Mach port that brings the host's surfaces (item 5.18).

### Linux, measured on lavapipe

The GPU process unshares `namespaces::GPU` (user, mount, network, IPC) while it
has one thread, makes its Vulkan device and draws a frame of its own, then
enters Landlock with no rule and the seccomp list, installed on **every thread
at once** (`SECCOMP_FILTER_FLAG_TSYNC`), because the driver's worker threads
already exist. There is no PID namespace: after `unshare(CLONE_NEWPID)` the
kernel refuses new threads, and the driver starts its workers later.

`GPU_EXTRA` adds five calls to the renderer's list, each one seen under
`strace -f` after the filter was installed, over the 14 GPU processes of
`clazel`'s `tests/browse_gpu.rs` (lavapipe, Mesa 25.2.8, glibc 2.39, aarch64
Ubuntu 24.04 in a container):
- `ftruncate`: lavapipe grows the memory file behind its device memory;
- `clone3`, `set_robust_list`, `rseq` and `sched_getaffinity`: the GPU
  process's own two reader threads, started after the filter.

The plan's other candidates were not called and are not allowed: `getpid`,
`clone`, and `sendmsg` and `recvmsg` (pixels leave as bytes on a pipe, so no
descriptor is passed). No executable mapping was made after the filter: lavapipe
compiles our shaders during the warm-up. There is still no `open`, `openat`,
`socket` or `connect`.

With a hardware device, `GPU_HARDWARE_EXTRA` adds `ioctl`. **That list is not
measured**: no hardware Vulkan driver has run in this sandbox, and one that
needs another call is killed.

**How it is weaker than the renderer's:**
- Those calls, with no argument filtering: `clone3` can make a process as well
  as a thread (under the same filter), and with a hardware device `ioctl`
  reaches every ioctl of every descriptor the process holds.
- No PID namespace.
- Landlock binds the calling thread and the threads it starts; the driver's
  existing workers are held by the seccomp list alone.
- The process keeps whatever the driver opened during the warm-up.

**Not measured:** x86-64 (CI's architecture), another Mesa or C library, any
hardware driver (Intel, AMD, NVIDIA), a long-running or memory-starved process.

### Windows, data only

The plan measured the Windows policy and decided it. It is restated here as
data, without a new measurement. The cost the plan states: the GPU process can
read `HKCU\Software`, `HKCU\Environment` and `HKLM\SOFTWARE`, and it has
`win32k`.

Starting a process with the `registryRead` capability needs
`clazel_sys::windows::spawn` to take capabilities (`DeriveCapabilitySidsFromName`).
That change to `clazel-sys` cannot be compiled or run from a Mac, so it waits
for a Windows machine.

### Kani

Each harness ran alone, in its own process group, with a 20-minute and 8 GB cap
polled every 5 s.

| Harness | Covers | Result | Verification time | Peak |
|---------|--------|--------|-------------------|------|
| `gpu_other_arch_x86_64` | the GPU program for a software driver (33 instructions since the list was measured), any syscall number, every other architecture value | passed (run again 2026-11-13; its own check count and time were not kept) | not recorded | not recorded |
| `gpu_other_arch_aarch64` | the same on aarch64 | passed, 451 checks (run again 2026-11-13) | 206 s | not recorded |
| `gpu_allowlist_x86_64` | the GPU program allows exactly its list, every 32-bit number, right architecture | **capped at 8 GB** in symbolic execution, three tries; **removed** | — | > 8 GB |

**Not proven by Kani:**
- That the GPU program allows exactly its list for every 32-bit number.
  `tests/policies.rs` sweeps every number below 1024 on both architectures
  instead. Kani's generator theorem covers symbolic lists of up to three numbers
  (`list_0` to `list_3`), not 27.
- That the list is right. It is not measured.

The two passing harnesses peak just under 8 GB, so a smaller machine may not run
them.

## Licence

The code is MIT, as in the repository's [LICENSE](../../LICENSE). The files
under `vendor/linux/` are verbatim copies from the Linux kernel (v6.12), read
by the tests only and never compiled in: the headers are GPL-2.0 with the
Linux syscall note, the documents GPL-2.0 (`vendor/linux/SOURCE.md`). See the
[main README](../../README.md) for the project.

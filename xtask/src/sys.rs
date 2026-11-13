//! The `unsafe` policy (Phase 2 item 2.0, CLAUDE.md rule 1).
//!
//! `unsafe` is allowed in exactly one crate, `crates/clazel-sys`, which
//! enters the OS sandbox. This module enforces what "audited" means for it:
//!
//! 1. only that crate overrides the `unsafe_code` lint, and only that lint
//!    (its `[lints]` tables equal the workspace's except `unsafe_code`);
//! 2. its only dependency is `libc`, pinned exactly;
//! 3. every `unsafe` is a block or an `unsafe extern` block, never an
//!    `unsafe fn`, `impl` or `trait`;
//! 4. each `unsafe { }` block holds exactly one call, to a foreign function
//!    on its file's fixed list ([`FOREIGN_FUNCTIONS`]; `syscall` only with a
//!    number from [`SYSCALLS`]) or through one of its file's dispatcher casts
//!    ([`DISPATCH_CASTS`]), and no pointer dereference; the one other block is
//!    a dispatcher cast itself (below);
//! 5. each `unsafe` has a `// SAFETY:` comment directly above it that cites
//!    a man page (`man 2 prctl`);
//! 6. no raw pointer arithmetic, and no public foreign function: the crate's
//!    public API is safe;
//! 7. a **dispatcher** ([`DISPATCHERS`]: `objc_msgSend`, which must be called
//!    through a function pointer of each method's exact type) is declared once,
//!    in an `unsafe extern "C-unwind"` block, with no parameters, and never called
//!    or named elsewhere; the only use is a `const` on its file's
//!    [`DISPATCH_CASTS`] list, written exactly
//!    `const NAME: unsafe extern "C-unwind" fn(..) -> .. = unsafe {
//!    std::mem::transmute(objc_msgSend as unsafe extern "C-unwind" fn()) };` with
//!    a `// SAFETY:` comment directly above it, and such a const is named nowhere
//!    but in calls inside `unsafe` blocks. Every other `transmute` is rejected.
//!    The ABI is `"C-unwind"` throughout, and only that: an Objective-C exception
//!    unwinding out of a call through a `"C"` pointer is undefined behaviour
//!    (Rust reference, `panic.unwind.ffi.undefined`), and through a `"C-unwind"`
//!    one it is a defined unwind or abort (`items.fn.extern.unwind.behavior`).
//!    The three places must agree: `D as T` coerces the function item only to a
//!    pointer of its declared ABI, and the cast's type is the one called;
//! 8. a **vtable call** is the one call through a pointer read from foreign
//!    memory, which is how a COM method is called (Microsoft Learn, "The COM
//!    Library" and each interface's page: an interface pointer points to a
//!    pointer to a table of function pointers). A vtable is a `#[repr(C)] struct`
//!    on its file's [`VTABLES`] list, whose fields are exactly the listed slots
//!    in the listed order, each either `usize` (never called) or an `unsafe
//!    extern "system" fn(..)`; the list holds every slot of the interface, so a
//!    slot's place in it is its number. The call is written exactly
//!    `unsafe { ((**this).method)(this, ..) }`: the receiver is one identifier,
//!    dereferenced twice and passed again as the first argument, and `method`
//!    is a listed slot's field, the header's name in snake case
//!    ([`slot_field`]: `CreateFence` is `create_fence`). It counts as the block's one call. Those two
//!    dereferences are the only ones allowed in an `unsafe` block; every other
//!    call through an expression, and a function pointer type anywhere else
//!    but a dispatcher cast, is rejected. What the checker cannot see, and the
//!    audit must: that each slot's type is the header's, and that the receiver
//!    is a live interface pointer of that vtable's interface;
//! 9. the latest row of `docs/SYS-AUDITS.md` carries the SHA-256 of the
//!    crate's source ([`source_hash`]), so every change is audited.
//!
//! And the README's memory-safety sentence states the measured `unsafe` count
//! ([`readme_problems`]).
//!
//! What no machine can check, and CLAUDE.md states as a rule: the session
//! that wrote a change to `clazel-sys` never writes its audit.

use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use proc_macro2::{Delimiter, Group, TokenStream, TokenTree};

/// The one crate that may contain `unsafe`, relative to the repository root.
pub const CRATE_DIR: &str = "crates/clazel-sys";
/// The crate's name.
pub const CRATE_NAME: &str = "clazel-sys";
/// The audit log.
pub const AUDITS: &str = "docs/SYS-AUDITS.md";

/// What `crates/clazel-sys/src/linux.rs` may call. `syscall` is the route to
/// `seccomp(2)`, the three `landlock_*` system calls and `ptrace(2)` (glibc does
/// not wrap the first four, and its `ptrace` is variadic with a request type that
/// differs between libcs); it may only be called with a number from [`SYSCALLS`].
const LINUX: &[&str] = &[
    "prctl",
    "syscall",
    "unshare",
    // The escape attempts of the sandbox tests (phase-2.md item 2.16): each
    // returns only whether the OS allowed it. `fork`'s child calls `_exit`
    // at once.
    "fork",
    "_exit",
    // Cryptographically secure random bytes for the TLS client
    // (`clazel_sys::fill_random`): the `libc` wrapper with flags 0, not
    // `syscall`. It only writes into a caller's buffer.
    "getrandom",
    // `clazel_sys::linux::clear_close_on_exec` (items 5.18 and 5.23), as on
    // macOS: only `F_SETFD` with 0, on a descriptor the caller borrows.
    "fcntl",
];

/// What `crates/clazel-sys/src/linux/vulkan.rs` may declare and call: Vulkan
/// core functions for the GPU process's drawing on Linux (phase-5.md item 5.17b),
/// as `libvulkan` exports them (every one in Vulkan 1.0), cited by their
/// reference pages (`man 3 vk…`), and `memcpy` for the one copy into and the one
/// copy out of mapped device memory (the plan: "the checker forbids pointer
/// arithmetic, so that is one audited call that copies"). No extension function,
/// so nothing is looked up.
const VULKAN: &[&str] = &[
    "vkCreateInstance",
    "vkEnumeratePhysicalDevices",
    "vkGetPhysicalDeviceProperties",
    "vkGetPhysicalDeviceQueueFamilyProperties",
    "vkGetPhysicalDeviceMemoryProperties",
    "vkCreateDevice",
    "vkGetDeviceQueue",
    "vkCreateCommandPool",
    "vkAllocateCommandBuffers",
    "vkCreateShaderModule",
    "vkCreateRenderPass",
    "vkCreateDescriptorSetLayout",
    "vkCreatePipelineLayout",
    "vkCreateGraphicsPipelines",
    "vkCreateDescriptorPool",
    "vkAllocateDescriptorSets",
    "vkUpdateDescriptorSets",
    "vkCreateImage",
    "vkDestroyImage",
    "vkGetImageMemoryRequirements",
    "vkAllocateMemory",
    "vkFreeMemory",
    "vkBindImageMemory",
    "vkCreateImageView",
    "vkDestroyImageView",
    "vkCreateFramebuffer",
    "vkDestroyFramebuffer",
    "vkCreateBuffer",
    "vkDestroyBuffer",
    "vkGetBufferMemoryRequirements",
    "vkBindBufferMemory",
    "vkMapMemory",
    "vkUnmapMemory",
    "vkBeginCommandBuffer",
    "vkEndCommandBuffer",
    "vkCmdBeginRenderPass",
    "vkCmdEndRenderPass",
    "vkCmdBindPipeline",
    "vkCmdBindDescriptorSets",
    "vkCmdPushConstants",
    "vkCmdSetViewport",
    "vkCmdSetScissor",
    "vkCmdDraw",
    "vkCmdCopyImageToBuffer",
    "vkQueueSubmit",
    "vkQueueWaitIdle",
    "memcpy",
];

/// What `crates/clazel-sys/src/macos.rs` may declare and call.
const MACOS: &[&str] = &[
    "sandbox_init",
    "sandbox_free_error",
    // The escape attempts of the sandbox tests, as on Linux. `ptrace` is a
    // foreign function here.
    "fork",
    "_exit",
    "ptrace",
    // `clazel_sys::fill_random`. It only writes into a caller's buffer.
    "getentropy",
    // `clazel_sys::macos::clear_close_on_exec` (items 5.18 and 5.23): only
    // `F_SETFD` with 0, on a descriptor the caller borrows.
    "fcntl",
];

/// What `crates/clazel-sys/src/windows.rs` may declare and call. Each is
/// documented on Microsoft Learn, cited as `docs <function>`.
const WINDOWS: &[&str] = &[
    // Start a process inside an AppContainer and a Job Object, check the token,
    // and one escape attempt (`OpenProcess`, the analogue of `ptrace` attach).
    "CreateAppContainerProfile",
    "DeriveAppContainerSidFromAppContainerName",
    "GetLengthSid",
    "CopySid",
    "FreeSid",
    "InitializeProcThreadAttributeList",
    "UpdateProcThreadAttribute",
    "DeleteProcThreadAttributeList",
    "CreateProcessW",
    "CloseHandle",
    "CreateJobObjectW",
    "SetInformationJobObject",
    "SetHandleInformation",
    "WaitForSingleObject",
    "GetExitCodeProcess",
    "TerminateProcess",
    "OpenProcess",
    "OpenProcessToken",
    "GetTokenInformation",
    // `clazel_sys::fill_random`, with the system-preferred RNG. It only writes
    // into a caller's buffer.
    "BCryptGenRandom",
    // The DNS servers on Windows, which has no `/etc/resolv.conf`
    // (`clazel_sys::windows::adapter_addresses`): `GetAdaptersAddresses`
    // only writes into a caller's buffer, whose octets the proven reader in
    // `clazel-dns` (`adapters`) reads without following a pointer.
    "GetAdaptersAddresses",
];

/// What `crates/clazel-sys/src/windows/window.rs` may declare and call: the host's
/// window on Windows (phase-5.md item 5.22a). `DefWindowProcW` is never called from
/// Rust: it is declared so that its address can be the window procedure.
const WINDOW: &[&str] = &[
    "RegisterClassExW",
    "DefWindowProcW",
    "LoadCursorW",
    "CreateWindowExW",
    "DestroyWindow",
    "IsWindow",
    "SetWindowTextW",
    "GetDpiForWindow",
    "PeekMessageW",
    "TranslateMessage",
    "DispatchMessageW",
    "MsgWaitForMultipleObjects",
    "GetClientRect",
    "ScreenToClient",
    "GetDC",
    "ReleaseDC",
    "SetProcessDpiAwarenessContext",
    "SetDIBitsToDevice",
    "GetModuleHandleW",
];

/// What `crates/clazel-sys/src/macos/metal.rs` may declare and call: Metal
/// drawing for the GPU process (phase-5.md item 5.17b). `objc_msgSend` is a
/// dispatcher ([`DISPATCHERS`]): it is only cast, in the consts of [`METAL_CASTS`].
const METAL: &[&str] = &[
    "objc_msgSend",
    "objc_getClass",
    "sel_registerName",
    "MTLCreateSystemDefaultDevice",
    "IOSurfaceCreate",
    "CFRelease",
];

/// What `crates/clazel-sys/src/macos/window.rs` may declare and call: the host's
/// window on macOS (phase-5.md item 5.21), AppKit and Core Animation through the
/// Objective-C runtime, a CPU image through Core Graphics, and two questions about
/// the process (is this the main thread, is there a window server). `objc_msgSend`
/// is a dispatcher ([`DISPATCHERS`]): it is only cast, in the consts of
/// [`APPKIT_CASTS`]. The file declares its own `objc_msgSend`, `objc_getClass`,
/// `sel_registerName` and `CFRelease` with the same types as `metal.rs`, so that
/// each file's casts and calls stay in that file.
const APPKIT: &[&str] = &[
    "objc_msgSend",
    "objc_getClass",
    "sel_registerName",
    "pthread_main_np",
    "CGSessionCopyCurrentDictionary",
    "CFRelease",
    "CFDataCreate",
    "CGDataProviderCreateWithCFData",
    "CGColorSpaceCreateDeviceRGB",
    "CGImageCreate",
];

/// Foreign functions that must be called through a function pointer of the
/// callee's exact type (Apple: "Messaging", in the Objective-C Runtime
/// documentation, says `objc_msgSend` "must be cast to an appropriate function
/// pointer type before being called"). Each is declared once, with no
/// parameters, and used only in the consts of [`DISPATCH_CASTS`].
pub const DISPATCHERS: &[&str] = &["objc_msgSend"];

/// The typed casts of `crates/clazel-sys/src/macos/metal.rs`'s dispatcher, one
/// per message signature, named for it.
const METAL_CASTS: &[&str] = &[
    "MSG_ID",
    "MSG_VOID",
    "MSG_USIZE",
    "MSG_ID_ID",
    "MSG_ID_USIZE",
    "MSG_VOID_ID",
    "MSG_VOID_USIZE",
    "MSG_VOID_BOOL",
    "MSG_ID_ID_ID_OUT",
    "MSG_ID_ID_OUT",
    "MSG_ID_PTR_USIZE_USIZE",
    "MSG_ID_USIZE_USIZE",
    "MSG_ID_ID_ID_USIZE",
    "MSG_ID_IDS_IDS_USIZE",
    "MSG_VOID_ID_USIZE_ID_USIZE_USIZE",
    "MSG_VOID_ID_USIZE_USIZE",
    "MSG_VOID_PTR_USIZE_USIZE",
    "MSG_VOID_SCISSOR",
    "MSG_VOID_CLEAR",
    "MSG_VOID_USIZE_USIZE_USIZE_USIZE_USIZE",
    "MSG_VOID_OUT_USIZE_REGION_USIZE",
];

/// The typed casts of `crates/clazel-sys/src/macos/window.rs`'s dispatcher, one
/// per message signature, named for it. A name may repeat one of [`METAL_CASTS`]:
/// each list belongs to its own file, which defines its own consts.
const APPKIT_CASTS: &[&str] = &[
    "MSG_ID",
    "MSG_VOID",
    "MSG_USIZE",
    "MSG_BOOL",
    "MSG_F64",
    "MSG_U16",
    "MSG_POINT",
    "MSG_RECT",
    "MSG_VOID_ID",
    "MSG_VOID_BOOL",
    "MSG_VOID_F64",
    "MSG_VOID_U32",
    "MSG_VOID_RECT",
    "MSG_BOOL_ISIZE",
    "MSG_U16_USIZE",
    "MSG_ID_F64",
    "MSG_ID_PTR_USIZE_USIZE",
    "MSG_ID_USIZE_ID_ID_BOOL",
    "MSG_ID_RECT_USIZE_USIZE_BOOL",
];

/// Consts that may each hold one cast of a dispatcher, by file (repo-relative).
pub const DISPATCH_CASTS: &[(&str, &[&str])] = &[
    ("crates/clazel-sys/src/macos/metal.rs", METAL_CASTS),
    ("crates/clazel-sys/src/macos/window.rs", APPKIT_CASTS),
];

/// One COM vtable: its `struct`'s name, and its slots in the header's order.
pub type Vtable = (&'static str, &'static [&'static str]);

/// The COM vtables of Direct3D 12 and DXGI that `clazel-sys` declares (phase-5.md
/// item 5.17b), each with **every** slot in the order of its interface and the
/// interfaces it inherits, since a slot's number is its place. From Microsoft's
/// `d3d12.h` and `d3dcommon.h` (the DirectX-Headers release 1.619.5) and, for
/// DXGI, mingw-w64's `dxgi.h` and `dxgi1_4.h`; where both have an interface they
/// agree. `IUnknownVtbl` is what every interface begins with, so `Release` is
/// called through it for all of them.
const D3D12_VTABLES: &[Vtable] = &[
    ("IUnknownVtbl", &["QueryInterface", "AddRef", "Release"]),
    (
        "ID3D12DeviceVtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "GetPrivateData",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "SetName",
            "GetNodeCount",
            "CreateCommandQueue",
            "CreateCommandAllocator",
            "CreateGraphicsPipelineState",
            "CreateComputePipelineState",
            "CreateCommandList",
            "CheckFeatureSupport",
            "CreateDescriptorHeap",
            "GetDescriptorHandleIncrementSize",
            "CreateRootSignature",
            "CreateConstantBufferView",
            "CreateShaderResourceView",
            "CreateUnorderedAccessView",
            "CreateRenderTargetView",
            "CreateDepthStencilView",
            "CreateSampler",
            "CopyDescriptors",
            "CopyDescriptorsSimple",
            "GetResourceAllocationInfo",
            "GetCustomHeapProperties",
            "CreateCommittedResource",
            "CreateHeap",
            "CreatePlacedResource",
            "CreateReservedResource",
            "CreateSharedHandle",
            "OpenSharedHandle",
            "OpenSharedHandleByName",
            "MakeResident",
            "Evict",
            "CreateFence",
            "GetDeviceRemovedReason",
            "GetCopyableFootprints",
            "CreateQueryHeap",
            "SetStablePowerState",
            "CreateCommandSignature",
            "GetResourceTiling",
            "GetAdapterLuid",
        ],
    ),
    (
        "ID3D12CommandQueueVtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "GetPrivateData",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "SetName",
            "GetDevice",
            "UpdateTileMappings",
            "CopyTileMappings",
            "ExecuteCommandLists",
            "SetMarker",
            "BeginEvent",
            "EndEvent",
            "Signal",
            "Wait",
            "GetTimestampFrequency",
            "GetClockCalibration",
            "GetDesc",
        ],
    ),
    (
        "ID3D12CommandAllocatorVtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "GetPrivateData",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "SetName",
            "GetDevice",
            "Reset",
        ],
    ),
    (
        "ID3D12GraphicsCommandListVtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "GetPrivateData",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "SetName",
            "GetDevice",
            "GetType",
            "Close",
            "Reset",
            "ClearState",
            "DrawInstanced",
            "DrawIndexedInstanced",
            "Dispatch",
            "CopyBufferRegion",
            "CopyTextureRegion",
            "CopyResource",
            "CopyTiles",
            "ResolveSubresource",
            "IASetPrimitiveTopology",
            "RSSetViewports",
            "RSSetScissorRects",
            "OMSetBlendFactor",
            "OMSetStencilRef",
            "SetPipelineState",
            "ResourceBarrier",
            "ExecuteBundle",
            "SetDescriptorHeaps",
            "SetComputeRootSignature",
            "SetGraphicsRootSignature",
            "SetComputeRootDescriptorTable",
            "SetGraphicsRootDescriptorTable",
            "SetComputeRoot32BitConstant",
            "SetGraphicsRoot32BitConstant",
            "SetComputeRoot32BitConstants",
            "SetGraphicsRoot32BitConstants",
            "SetComputeRootConstantBufferView",
            "SetGraphicsRootConstantBufferView",
            "SetComputeRootShaderResourceView",
            "SetGraphicsRootShaderResourceView",
            "SetComputeRootUnorderedAccessView",
            "SetGraphicsRootUnorderedAccessView",
            "IASetIndexBuffer",
            "IASetVertexBuffers",
            "SOSetTargets",
            "OMSetRenderTargets",
            "ClearDepthStencilView",
            "ClearRenderTargetView",
            "ClearUnorderedAccessViewUint",
            "ClearUnorderedAccessViewFloat",
            "DiscardResource",
            "BeginQuery",
            "EndQuery",
            "ResolveQueryData",
            "SetPredication",
            "SetMarker",
            "BeginEvent",
            "EndEvent",
            "ExecuteIndirect",
        ],
    ),
    (
        "ID3D12ResourceVtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "GetPrivateData",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "SetName",
            "GetDevice",
            "Map",
            "Unmap",
            "GetDesc",
            "GetGPUVirtualAddress",
            "WriteToSubresource",
            "ReadFromSubresource",
            "GetHeapProperties",
        ],
    ),
    (
        "ID3D12FenceVtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "GetPrivateData",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "SetName",
            "GetDevice",
            "GetCompletedValue",
            "SetEventOnCompletion",
            "Signal",
        ],
    ),
    (
        "ID3D12DescriptorHeapVtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "GetPrivateData",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "SetName",
            "GetDevice",
            "GetDesc",
            "GetCPUDescriptorHandleForHeapStart",
            "GetGPUDescriptorHandleForHeapStart",
        ],
    ),
    (
        "ID3D10BlobVtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "GetBufferPointer",
            "GetBufferSize",
        ],
    ),
    (
        "IDXGIFactory4Vtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "GetPrivateData",
            "GetParent",
            "EnumAdapters",
            "MakeWindowAssociation",
            "GetWindowAssociation",
            "CreateSwapChain",
            "CreateSoftwareAdapter",
            "EnumAdapters1",
            "IsCurrent",
            "IsWindowedStereoEnabled",
            "CreateSwapChainForHwnd",
            "CreateSwapChainForCoreWindow",
            "GetSharedResourceAdapterLuid",
            "RegisterStereoStatusWindow",
            "RegisterStereoStatusEvent",
            "UnregisterStereoStatus",
            "RegisterOcclusionStatusWindow",
            "RegisterOcclusionStatusEvent",
            "UnregisterOcclusionStatus",
            "CreateSwapChainForComposition",
            "GetCreationFlags",
            "EnumAdapterByLuid",
            "EnumWarpAdapter",
        ],
    ),
    (
        "IDXGIAdapter1Vtbl",
        &[
            "QueryInterface",
            "AddRef",
            "Release",
            "SetPrivateData",
            "SetPrivateDataInterface",
            "GetPrivateData",
            "GetParent",
            "EnumOutputs",
            "GetDesc",
            "CheckInterfaceSupport",
            "GetDesc1",
        ],
    ),
];

/// The vtables a file may declare and call through, by file (repo-relative).
/// `d3d12_abi.rs` declares them (and makes no call: it has no foreign function),
/// `windows/d3d12.rs` calls through them.
pub const VTABLES: &[(&str, &[Vtable])] = &[
    ("crates/clazel-sys/src/d3d12_abi.rs", D3D12_VTABLES),
    ("crates/clazel-sys/src/windows/d3d12.rs", D3D12_VTABLES),
];

/// Foreign functions `clazel-sys` may declare or call, by the file that may do so
/// (repo-relative). A file not named here may use none, so that an API's calls stay
/// in its own module and a mistyped path fails the check. Errno is read with
/// `std::io::Error::last_os_error`, which is safe, so it needs no entry.
pub const FOREIGN_FUNCTIONS: &[(&str, &[&str])] = &[
    ("crates/clazel-sys/src/linux.rs", LINUX),
    ("crates/clazel-sys/src/linux/vulkan.rs", VULKAN),
    ("crates/clazel-sys/src/macos.rs", MACOS),
    ("crates/clazel-sys/src/windows.rs", WINDOWS),
    ("crates/clazel-sys/src/windows/window.rs", WINDOW),
    ("crates/clazel-sys/src/macos/metal.rs", METAL),
    ("crates/clazel-sys/src/macos/window.rs", APPKIT),
];

/// The foreign functions `path` may use.
fn permitted_in(path: &str) -> &'static [&'static str] {
    FOREIGN_FUNCTIONS
        .iter()
        .find(|(file, _)| *file == path)
        .map_or(&[], |(_, names)| *names)
}

/// The vtables `path` may declare and call through.
fn vtables_in(path: &str) -> &'static [Vtable] {
    VTABLES
        .iter()
        .find(|(file, _)| *file == path)
        .map_or(&[], |(_, tables)| *tables)
}

/// The dispatcher casts `path` may define and call through.
fn casts_in(path: &str) -> &'static [&'static str] {
    DISPATCH_CASTS
        .iter()
        .find(|(file, _)| *file == path)
        .map_or(&[], |(_, names)| *names)
}

/// The system call numbers `syscall` may be given (names as in `libc`).
pub const SYSCALLS: &[&str] = &[
    "SYS_seccomp",
    "SYS_landlock_create_ruleset",
    "SYS_landlock_add_rule",
    "SYS_landlock_restrict_self",
    "SYS_ptrace",
];

/// Method and function names that do pointer arithmetic. Banned in the
/// crate, whether or not the receiver is a raw pointer.
const POINTER_ARITHMETIC: &[&str] = &[
    "add",
    "sub",
    "offset",
    "offset_from",
    "offset_from_unsigned",
    "sub_ptr",
    "byte_add",
    "byte_sub",
    "byte_offset",
    "byte_offset_from",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_offset",
    "wrapping_byte_add",
    "wrapping_byte_sub",
    "wrapping_byte_offset",
];

/// Words that may be followed by a parenthesis without being a call.
const NOT_CALLS: &[&str] = &[
    "as", "if", "while", "match", "in", "return", "for", "let", "mut", "const", "move", "else",
    "loop", "break", "ref",
];

/// What the checker learned about one source file of `clazel-sys`.
#[derive(Debug, Default)]
pub struct File {
    /// Violations as (1-based line, what).
    pub violations: Vec<(usize, String)>,
    /// Dispatcher casts defined (each also an `unsafe` block).
    pub dispatcher_casts: usize,
    /// Calls through a listed vtable (each in its own `unsafe` block).
    pub vtable_calls: usize,
    /// The foreign functions this file may use.
    permitted: &'static [&'static str],
    /// The dispatcher casts this file may define and call through.
    casts: &'static [&'static str],
    /// The vtables this file may declare and call through.
    vtables: &'static [Vtable],
}

/// Check one source file of `clazel-sys`, at the repo-relative `path`, against
/// rules 3 to 6.
pub fn check_source(path: &str, source: &str) -> Result<File, String> {
    check_with(
        path,
        source,
        permitted_in(path),
        casts_in(path),
        vtables_in(path),
    )
}

/// [`check_source`] with the file's lists given.
fn check_with(
    _path: &str,
    source: &str,
    permitted: &'static [&'static str],
    casts: &'static [&'static str],
    vtables: &'static [Vtable],
) -> Result<File, String> {
    let stream: TokenStream = source
        .parse()
        .map_err(|e: proc_macro2::LexError| format!("cannot tokenize: {e}"))?;
    let tokens: Vec<TokenTree> = stream.into_iter().collect();
    let lines: Vec<&str> = source.lines().collect();
    let mut file = File {
        permitted,
        casts,
        vtables,
        ..File::default()
    };
    walk(&tokens, None, &lines, &mut file);
    file.violations.sort();
    Ok(file)
}

/// The calls found so far in the `unsafe { }` block being checked.
struct Block {
    calls: Vec<String>,
}

fn flag(file: &mut File, line: usize, what: impl Into<String>) {
    file.violations.push((line, what.into()));
}

fn line_of(tt: &TokenTree) -> usize {
    tt.span().start().line
}

fn is_punct(tt: Option<&TokenTree>, c: char) -> bool {
    matches!(tt, Some(TokenTree::Punct(p)) if p.as_char() == c)
}

fn ident_is(tt: Option<&TokenTree>, name: &str) -> bool {
    matches!(tt, Some(TokenTree::Ident(i)) if *i == name)
}

fn walk(tokens: &[TokenTree], mut block: Option<&mut Block>, lines: &[&str], file: &mut File) {
    let mut k = 0usize;
    while let Some(tt) = tokens.get(k) {
        let next = tokens.get(k.saturating_add(1));
        let prev = k.checked_sub(1).and_then(|j| tokens.get(j));
        let line = line_of(tt);
        match tt {
            TokenTree::Ident(id) => {
                let name = id.to_string();
                if name == "const"
                    && block.is_none()
                    && let Some(TokenTree::Ident(c)) = next
                    && file.casts.contains(&c.to_string().as_str())
                {
                    k = dispatcher_cast(tokens, k, lines, file);
                    continue;
                }
                if name == "struct"
                    && let Some(TokenTree::Ident(n)) = next
                    && let Some((_, slots)) = file.vtables.iter().find(|(v, _)| *n == *v).copied()
                {
                    k = vtable_decl(tokens, k, slots, file);
                    continue;
                }
                if name == "transmute" || name == "transmute_copy" {
                    flag(
                        file,
                        line,
                        format!(
                            "`{name}` is only allowed as the cast of a dispatcher in a listed \
                             `const` (see xtask/src/sys.rs)"
                        ),
                    );
                }
                if DISPATCHERS.contains(&name.as_str()) {
                    flag(
                        file,
                        line,
                        format!(
                            "dispatcher `{name}` may only be declared and cast in a listed `const`"
                        ),
                    );
                }
                if file.casts.contains(&name.as_str())
                    && !(block.is_some()
                        && matches!(next, Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis))
                {
                    flag(
                        file,
                        line,
                        format!(
                            "dispatcher cast `{name}` may only be called, inside an `unsafe` block"
                        ),
                    );
                }
                if name == "unsafe" {
                    if block.is_some() {
                        flag(file, line, "nested `unsafe` inside an `unsafe` block");
                    } else if let Some(TokenTree::Group(g)) = next
                        && g.delimiter() == Delimiter::Brace
                    {
                        require_safety_comment(lines, line, file);
                        let mut inner = Block { calls: Vec::new() };
                        let body: Vec<TokenTree> = g.stream().into_iter().collect();
                        walk(&body, Some(&mut inner), lines, file);
                        if inner.calls.len() != 1 {
                            flag(
                                file,
                                line,
                                format!(
                                    "an `unsafe` block must hold exactly one foreign call, found {}",
                                    inner.calls.len()
                                ),
                            );
                        }
                        k = k.saturating_add(2);
                        continue;
                    } else if ident_is(next, "extern")
                        && matches!(tokens.get(k.saturating_add(2)), Some(TokenTree::Literal(_)))
                        && ident_is(tokens.get(k.saturating_add(3)), "fn")
                        && !matches!(tokens.get(k.saturating_add(4)), Some(TokenTree::Ident(_)))
                    {
                        // `unsafe extern ".." fn(..)`: a function pointer type. The
                        // two places one may be written, a listed dispatcher cast
                        // (rule 7) and a listed vtable's slot (rule 8), are checked
                        // whole and never reach this line.
                        flag(
                            file,
                            line,
                            "a function pointer type is only allowed in a listed dispatcher \
                             cast or a listed vtable's slot (see xtask/src/sys.rs)",
                        );
                        k = k.saturating_add(4);
                        continue;
                    } else if ident_is(next, "extern")
                        && ident_is(tokens.get(k.saturating_add(3)), "fn")
                    {
                        flag(
                            file,
                            line,
                            "`unsafe` may only start a block or an `unsafe extern` block, \
                             not `unsafe fn`, `impl` or `trait`",
                        );
                    } else if ident_is(next, "extern") {
                        require_safety_comment(lines, line, file);
                        // `unsafe extern "C" { ... }`: skip the ABI string.
                        let abi = match tokens.get(k.saturating_add(2)) {
                            Some(TokenTree::Literal(l)) => l.to_string(),
                            _ => String::new(),
                        };
                        let rest = tokens.get(k.saturating_add(2)..).unwrap_or(&[]);
                        let at = rest.iter().position(|t| {
                            matches!(t, TokenTree::Group(g) if g.delimiter() == Delimiter::Brace)
                        });
                        match at.and_then(|i| rest.get(i)) {
                            Some(TokenTree::Group(g)) => check_extern(g, &abi, file),
                            _ => flag(file, line, "`unsafe extern` without a block"),
                        }
                        k = k.saturating_add(3).saturating_add(at.unwrap_or(0));
                        continue;
                    } else {
                        flag(
                            file,
                            line,
                            "`unsafe` may only start a block or an `unsafe extern` block, \
                             not `unsafe fn`, `impl` or `trait`",
                        );
                    }
                }
                if name == "extern" && !ident_is(prev, "unsafe") {
                    flag(file, line, "`extern` outside an `unsafe extern` block");
                }
                if name == "macro_rules" || name == "include" {
                    flag(
                        file,
                        line,
                        format!("`{name}` could hide `unsafe` from this check"),
                    );
                }
                if POINTER_ARITHMETIC.contains(&name.as_str()) && call_or_turbofish(next, tokens, k)
                {
                    flag(file, line, format!("raw pointer arithmetic: `{name}`"));
                }
                if name == "pub" {
                    check_pub_use(tokens, k, file);
                }
                if let Some(b) = block.as_deref_mut()
                    && let Some(TokenTree::Group(args)) = next
                    && args.delimiter() == Delimiter::Parenthesis
                    && !NOT_CALLS.contains(&name.as_str())
                {
                    check_call(&name, args, line, b, file);
                }
            }
            TokenTree::Punct(p) if p.as_char() == '#' => {
                // `#[path = ".."]` would pull in source this check never reads.
                let at = if is_punct(next, '!') {
                    k.saturating_add(2)
                } else {
                    k.saturating_add(1)
                };
                if let Some(TokenTree::Group(g)) = tokens.get(at)
                    && g.delimiter() == Delimiter::Bracket
                    && matches!(g.stream().into_iter().next(), Some(TokenTree::Ident(i)) if i == "path")
                {
                    flag(file, line, "`#[path]` attribute");
                }
            }
            TokenTree::Punct(p) if p.as_char() == '*' && block.is_some() => {
                let type_position =
                    ident_is(prev, "as") || ident_is(next, "const") || ident_is(next, "mut");
                if !type_position {
                    flag(
                        file,
                        line,
                        "dereference or multiplication inside an `unsafe` block",
                    );
                }
            }
            TokenTree::Punct(_) | TokenTree::Literal(_) => {}
            TokenTree::Group(callee)
                if callee.delimiter() == Delimiter::Parenthesis
                    && block.is_some()
                    && matches!(next, Some(TokenTree::Group(a)) if a.delimiter() == Delimiter::Parenthesis) =>
            {
                // `(expr)(args)` in an `unsafe` block: a call through a pointer.
                // The one accepted form is a vtable call (rule 8).
                if let Some(TokenTree::Group(args)) = next
                    && let Some(b) = block.as_deref_mut()
                    && vtable_call(callee, args, line, b, file)
                {
                    let body: Vec<TokenTree> = args.stream().into_iter().collect();
                    walk(&body, block.as_deref_mut(), lines, file);
                    k = k.saturating_add(2);
                    continue;
                }
            }
            TokenTree::Group(_) => {}
        }
        // Everything inside a group, a call's arguments included, is walked
        // too, so nested calls are seen.
        if let TokenTree::Group(g) = tt {
            let body: Vec<TokenTree> = g.stream().into_iter().collect();
            walk(&body, block.as_deref_mut(), lines, file);
        }
        k = k.saturating_add(1);
    }
}

/// A header's method name as the Rust field that holds its slot: an underscore
/// before each capital that follows a lower-case letter or a digit, or that ends
/// a run of capitals (`GetCPUDescriptorHandleForHeapStart` is
/// `get_cpu_descriptor_handle_for_heap_start`), then lower case. Rust's
/// `non_snake_case` lint, which no crate may switch off, rejects the header's
/// spelling for a field, so the lists keep the header's names, which is what an
/// auditor compares, and the source uses this one spelling of each.
pub fn slot_field(method: &str) -> String {
    let chars: Vec<char> = method.chars().collect();
    let mut out = String::new();
    for (i, c) in chars.iter().enumerate() {
        let before = i.checked_sub(1).and_then(|j| chars.get(j));
        let after = chars.get(i.saturating_add(1));
        let starts_word = c.is_ascii_uppercase()
            && before.is_some_and(|b| {
                b.is_ascii_lowercase()
                    || b.is_ascii_digit()
                    || (b.is_ascii_uppercase() && after.is_some_and(char::is_ascii_lowercase))
            });
        if starts_word {
            out.push('_');
        }
        out.push(c.to_ascii_lowercase());
    }
    out
}

/// The ABI of every vtable slot: COM methods are `STDMETHODCALLTYPE`, which on
/// 64-bit Windows is the one calling convention, Rust's `"system"`.
const VTABLE_ABI: &str = "\"system\"";

/// `((**this).method)(this, ..)` inside an `unsafe` block: `callee` is the first
/// group and `args` the second. True, and counted as the block's call, if it is
/// exactly that form: the receiver one identifier, dereferenced twice (the
/// interface pointer, then its vtable pointer), `method` the field
/// ([`slot_field`]) of a slot of a vtable this file may use, and the receiver
/// again as the first argument. Anything else is
/// flagged and false.
fn vtable_call(
    callee: &Group,
    args: &Group,
    line: usize,
    block: &mut Block,
    file: &mut File,
) -> bool {
    let inner: Vec<TokenTree> = callee.stream().into_iter().collect();
    let (receiver, method) = match inner.as_slice() {
        [
            TokenTree::Group(r),
            TokenTree::Punct(dot),
            TokenTree::Ident(m),
        ] if r.delimiter() == Delimiter::Parenthesis && dot.as_char() == '.' => {
            let r: Vec<TokenTree> = r.stream().into_iter().collect();
            match r.as_slice() {
                [
                    TokenTree::Punct(a),
                    TokenTree::Punct(b),
                    TokenTree::Ident(this),
                ] if a.as_char() == '*' && b.as_char() == '*' => (this.to_string(), m.to_string()),
                _ => (String::new(), String::new()),
            }
        }
        _ => (String::new(), String::new()),
    };
    if receiver.is_empty() {
        flag(
            file,
            line,
            "a call through an expression must be exactly `((**this).method)(this, ..)`, a \
             listed vtable's slot (see xtask/src/sys.rs)",
        );
        return false;
    }
    if !file
        .vtables
        .iter()
        .any(|(_, slots)| slots.iter().any(|s| slot_field(s) == method))
    {
        flag(
            file,
            line,
            format!(
                "`{method}` is not a slot of a vtable this file may call through (see xtask/src/sys.rs)"
            ),
        );
        return false;
    }
    let args: Vec<TokenTree> = args.stream().into_iter().collect();
    let first_is_receiver =
        ident_is(args.first(), &receiver) && (args.len() == 1 || is_punct(args.get(1), ','));
    if !first_is_receiver {
        flag(
            file,
            line,
            format!(
                "a vtable call's first argument must be its receiver: `((**{receiver}).{method})({receiver}, ..)`"
            ),
        );
        return false;
    }
    block.calls.push(method);
    file.vtable_calls = file.vtable_calls.saturating_add(1);
    true
}

/// `#[repr(C)] struct NAME { .. }` at `k` (the `struct`), NAME a listed vtable
/// with `slots`: its fields must be exactly the slots ([`slot_field`] of each
/// listed name), in order, each either
/// `usize` (a slot that is never called: a pointer's size and nothing callable)
/// or an `unsafe extern "system" fn(..)` pointer. Returns the index after the
/// body.
fn vtable_decl(tokens: &[TokenTree], k: usize, slots: &[&str], file: &mut File) -> usize {
    let line = tokens.get(k).map_or(0, line_of);
    let name = match tokens.get(k.saturating_add(1)) {
        Some(TokenTree::Ident(n)) => n.to_string(),
        _ => String::new(),
    };
    let repr_c = k
        .checked_sub(2)
        .is_some_and(|j| is_punct(tokens.get(j), '#'))
        && matches!(k.checked_sub(1).and_then(|j| tokens.get(j)),
            Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Bracket
                && g.stream().to_string().replace(' ', "") == "repr(C)");
    if !repr_c {
        flag(
            file,
            line,
            format!("vtable `{name}` must be declared directly under `#[repr(C)]`"),
        );
    }
    let Some(TokenTree::Group(body)) = tokens.get(k.saturating_add(2)) else {
        flag(
            file,
            line,
            format!("vtable `{name}` must be a `struct` with named fields"),
        );
        return k.saturating_add(2);
    };
    if body.delimiter() != Delimiter::Brace {
        flag(
            file,
            line,
            format!("vtable `{name}` must be a `struct` with named fields"),
        );
        return k.saturating_add(3);
    }
    let body: Vec<TokenTree> = body.stream().into_iter().collect();
    let mut found = Vec::new();
    for field in body.split(|t| is_punct(Some(t), ',')) {
        // Doc comments are `#[doc = ".."]` here.
        let mut field = field;
        while let [TokenTree::Punct(p), TokenTree::Group(g), rest @ ..] = field
            && p.as_char() == '#'
            && matches!(g.stream().into_iter().next(), Some(TokenTree::Ident(i)) if i == "doc")
        {
            field = rest;
        }
        let [TokenTree::Ident(slot), TokenTree::Punct(colon), ty @ ..] = field else {
            if !field.is_empty() {
                let at = field.first().map_or(line, line_of);
                flag(
                    file,
                    at,
                    format!("vtable `{name}`: a field must be `Slot: type`"),
                );
            }
            continue;
        };
        let unused = matches!(ty, [TokenTree::Ident(u)] if *u == "usize");
        if colon.as_char() != ':' || !(unused || is_fn_pointer(ty, VTABLE_ABI)) {
            flag(
                file,
                field.first().map_or(line, line_of),
                format!(
                    "vtable `{name}`: slot `{slot}` must be `usize` or an `unsafe extern \"system\" fn(..)`"
                ),
            );
        }
        found.push(slot.to_string());
    }
    let want: Vec<String> = slots.iter().map(|s| slot_field(s)).collect();
    if found != want {
        let at = found
            .iter()
            .zip(&want)
            .position(|(a, b)| a != b)
            .unwrap_or(found.len().min(want.len()));
        flag(
            file,
            line,
            format!(
                "vtable `{name}` must have exactly the listed slots in order (see xtask/src/sys.rs): \
                 slot {at} is {:?}, the list has {:?}",
                found.get(at),
                want.get(at)
            ),
        );
    }
    k.saturating_add(3)
}

/// `const NAME: unsafe extern "C-unwind" fn(..) -> .. = unsafe {
/// std::mem::transmute(D as unsafe extern "C-unwind" fn()) };` at `k` (the `const`),
/// with D a dispatcher this file may declare and a `// SAFETY:` comment directly
/// above. Returns the index after the item's `;`.
fn dispatcher_cast(tokens: &[TokenTree], k: usize, lines: &[&str], file: &mut File) -> usize {
    let at = |i: usize| tokens.get(k.saturating_add(i));
    let line = tokens.get(k).map_or(0, line_of);
    require_safety_comment(lines, line, file);
    let end = tokens
        .get(k..)
        .unwrap_or(&[])
        .iter()
        .position(|t| is_punct(Some(t), ';'))
        .map_or(tokens.len(), |p| k.saturating_add(p).saturating_add(1));
    let item: Vec<TokenTree> = tokens.get(k..end).unwrap_or(&[]).to_vec();
    let eq = item.iter().position(|t| is_punct(Some(t), '='));
    let ty = eq.and_then(|e| item.get(3..e)).unwrap_or(&[]);
    let typed = is_punct(at(2), ':') && is_c_unwind_fn_pointer(ty);
    let value = eq
        .and_then(|e| item.get(e.saturating_add(1)..))
        .unwrap_or(&[]);
    let cast = match value {
        [
            TokenTree::Ident(u),
            TokenTree::Group(g),
            TokenTree::Punct(semi),
        ] if *u == "unsafe" && g.delimiter() == Delimiter::Brace && semi.as_char() == ';' => {
            transmute_of_dispatcher(&g.stream().into_iter().collect::<Vec<_>>(), file)
        }
        _ => false,
    };
    if !(typed && cast) {
        flag(
            file,
            line,
            "a dispatcher cast must be exactly `const NAME: unsafe extern \"C-unwind\" fn(..) = \
             unsafe { std::mem::transmute(D as unsafe extern \"C-unwind\" fn()) };`",
        );
    } else {
        file.dispatcher_casts = file.dispatcher_casts.saturating_add(1);
    }
    end
}

/// The one ABI a dispatcher is declared, cast and called with (rule 7).
const DISPATCH_ABI: &str = "\"C-unwind\"";

/// `unsafe extern "C-unwind" fn (..)`, optionally `-> T`, and nothing else.
fn is_c_unwind_fn_pointer(ty: &[TokenTree]) -> bool {
    is_fn_pointer(ty, DISPATCH_ABI)
}

/// `unsafe extern ABI fn (..)`, optionally `-> T`, and nothing else; `want` is
/// the ABI string, quoted.
fn is_fn_pointer(ty: &[TokenTree], want: &str) -> bool {
    matches!(ty,
        [TokenTree::Ident(u), TokenTree::Ident(e), TokenTree::Literal(abi), TokenTree::Ident(f), TokenTree::Group(params), rest @ ..]
            if *u == "unsafe" && *e == "extern" && abi.to_string() == want && *f == "fn"
                && params.delimiter() == Delimiter::Parenthesis
                && (rest.is_empty() || (is_punct(rest.first(), '-') && is_punct(rest.get(1), '>') && rest.len() > 2)))
}

/// `std::mem::transmute(D as unsafe extern "C-unwind" fn())` with D a dispatcher of this
/// file, and nothing else.
fn transmute_of_dispatcher(body: &[TokenTree], file: &File) -> bool {
    let path = ["std", ":", ":", "mem", ":", ":", "transmute"];
    let head_ok = body.len() == path.len().saturating_add(1)
        && body.iter().zip(path).all(|(t, want)| match t {
            TokenTree::Ident(i) => *i == want,
            TokenTree::Punct(p) => p.as_char().to_string() == want,
            _ => false,
        });
    let Some(TokenTree::Group(args)) = body.last() else {
        return false;
    };
    let args: Vec<TokenTree> = args.stream().into_iter().collect();
    head_ok
        && matches!(args.as_slice(),
            [TokenTree::Ident(d), TokenTree::Ident(r#as), ty @ ..]
                if DISPATCHERS.contains(&d.to_string().as_str())
                    && file.permitted.contains(&d.to_string().as_str())
                    && *r#as == "as"
                    && is_c_unwind_fn_pointer(ty)
                    && ty.len() == 5
                    && matches!(ty.get(4), Some(TokenTree::Group(g)) if g.stream().is_empty()))
}

/// `name(` or `name::<..>(`: the identifier at `k` is being called.
fn call_or_turbofish(next: Option<&TokenTree>, tokens: &[TokenTree], k: usize) -> bool {
    match next {
        Some(TokenTree::Group(g)) => g.delimiter() == Delimiter::Parenthesis,
        Some(TokenTree::Punct(p)) if p.as_char() == ':' => {
            is_punct(tokens.get(k.saturating_add(2)), ':')
                && is_punct(tokens.get(k.saturating_add(3)), '<')
        }
        _ => false,
    }
}

/// A call `name(args)` inside an `unsafe` block: it must be a permitted
/// foreign function, and `syscall` only with a permitted number.
fn check_call(name: &str, args: &Group, line: usize, block: &mut Block, file: &mut File) {
    if file.casts.contains(&name) {
        block.calls.push(name.to_owned());
        return;
    }
    if !file.permitted.contains(&name) || DISPATCHERS.contains(&name) {
        flag(
            file,
            line,
            format!(
                "`{name}` is not a permitted foreign function in this file (see xtask/src/sys.rs)"
            ),
        );
        return;
    }
    if name == "syscall" {
        let toks: Vec<TokenTree> = args.stream().into_iter().collect();
        let first: Vec<&TokenTree> = toks
            .iter()
            .take_while(|t| !is_punct(Some(t), ','))
            .collect();
        let number = first.iter().rev().find_map(|t| match t {
            TokenTree::Ident(i) => Some(i.to_string()),
            _ => None,
        });
        if !number.as_deref().is_some_and(|n| SYSCALLS.contains(&n)) {
            flag(
                file,
                line,
                format!("`syscall` with {number:?}: only {SYSCALLS:?} are permitted"),
            );
            return;
        }
    }
    block.calls.push(name.to_owned());
}

/// `unsafe extern ABI { ... }`: only private function declarations from the
/// list, and a dispatcher only where `abi` (the ABI string, quoted, or empty) is
/// `"C-unwind"`.
fn check_extern(g: &Group, abi: &str, file: &mut File) {
    let body: Vec<TokenTree> = g.stream().into_iter().collect();
    for (k, tt) in body.iter().enumerate() {
        let TokenTree::Ident(id) = tt else { continue };
        let line = line_of(tt);
        match id.to_string().as_str() {
            "pub" => flag(
                file,
                line,
                "foreign declaration is `pub`: the public API must be safe",
            ),
            "safe" => flag(
                file,
                line,
                "`safe fn` in `unsafe extern` skips the `unsafe` block",
            ),
            "static" | "type" => flag(
                file,
                line,
                "only functions may be declared in `unsafe extern`",
            ),
            "fn" => {
                let name = match body.get(k.saturating_add(1)) {
                    Some(TokenTree::Ident(n)) => n.to_string(),
                    _ => String::new(),
                };
                if !file.permitted.contains(&name.as_str()) {
                    flag(
                        file,
                        line,
                        format!(
                            "`{name}` is not a permitted foreign function in this file (see xtask/src/sys.rs)"
                        ),
                    );
                }
                if DISPATCHERS.contains(&name.as_str()) {
                    let params = body.get(k.saturating_add(2));
                    let end = body.get(k.saturating_add(3));
                    let bare = matches!(params, Some(TokenTree::Group(g))
                        if g.delimiter() == Delimiter::Parenthesis && g.stream().is_empty())
                        && is_punct(end, ';');
                    if !bare {
                        flag(
                            file,
                            line,
                            format!("dispatcher `{name}` must be declared `fn {name}();`"),
                        );
                    }
                    if abi != DISPATCH_ABI {
                        flag(
                            file,
                            line,
                            format!(
                                "dispatcher `{name}` must be declared in an `unsafe extern \"C-unwind\"` block"
                            ),
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

/// `pub use ...libc...;` would hand callers an unsafe foreign function.
fn check_pub_use(tokens: &[TokenTree], k: usize, file: &mut File) {
    let mut at = k.saturating_add(1);
    if matches!(tokens.get(at), Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Parenthesis)
    {
        at = at.saturating_add(1);
    }
    if !ident_is(tokens.get(at), "use") {
        return;
    }
    let rest = tokens.get(at..).unwrap_or(&[]);
    let end = rest
        .iter()
        .position(|t| is_punct(Some(t), ';'))
        .unwrap_or(rest.len());
    let has_libc = rest
        .get(..end)
        .unwrap_or(&[])
        .iter()
        .any(|t| contains_ident(t, "libc"));
    if has_libc {
        flag(
            file,
            tokens.get(k).map_or(0, line_of),
            "`pub use` of `libc` would export an unsafe function",
        );
    }
}

fn contains_ident(tt: &TokenTree, name: &str) -> bool {
    match tt {
        TokenTree::Ident(i) => *i == name,
        TokenTree::Group(g) => g.stream().into_iter().any(|t| contains_ident(&t, name)),
        TokenTree::Punct(_) | TokenTree::Literal(_) => false,
    }
}

/// Rule 5: the comment lines directly above `line` (1-based) include a
/// `// SAFETY:` line, and the comment cites a man page ("man 2 prctl").
fn require_safety_comment(lines: &[&str], line: usize, file: &mut File) {
    let mut comment = Vec::new();
    let mut idx = line.saturating_sub(1);
    while let Some(above) = idx.checked_sub(1) {
        match lines.get(above) {
            Some(l) if l.trim_start().starts_with("//") => {
                comment.push(l.trim_start());
                idx = above;
            }
            _ => break,
        }
    }
    comment.reverse();
    if !comment.iter().any(|l| l.starts_with("// SAFETY:")) {
        flag(
            file,
            line,
            "`unsafe` without a `// SAFETY:` comment directly above it",
        );
    } else if !cites_man_page(&comment.join(" ")) {
        flag(
            file,
            line,
            "the `// SAFETY:` comment does not cite a man page (e.g. `man 2 prctl`)",
        );
    }
}

/// The text contains `man <section digit> <name>`, or (Windows has no man
/// pages) `docs <FunctionName>`, a Win32 function on Microsoft Learn.
fn cites_man_page(text: &str) -> bool {
    cites_win32_docs(text) || cites_unix_man(text)
}

/// `docs CreateProcessW`: `docs`, a space, then an identifier starting with
/// an uppercase letter.
fn cites_win32_docs(text: &str) -> bool {
    text.match_indices("docs ").any(|(i, _)| {
        text.get(i.saturating_add(5)..)
            .and_then(|rest| rest.chars().next())
            .is_some_and(|c| c.is_ascii_uppercase())
    })
}

fn cites_unix_man(text: &str) -> bool {
    text.match_indices("man ").any(|(i, _)| {
        let mut rest = text.get(i.saturating_add(4)..).unwrap_or("").chars();
        rest.next().is_some_and(|c| c.is_ascii_digit())
            && rest.next() == Some(' ')
            && rest
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
    })
}

// ---------------------------------------------------------------- manifest

/// `[lints.*]` entries of a manifest as (table, key) -> value, whitespace
/// removed. `[workspace.lints.rust]` and `[lints.rust]` are the same table.
fn lint_entries(manifest: &str) -> (BTreeMap<(String, String), String>, bool) {
    let mut entries = BTreeMap::new();
    let mut table = String::new();
    let mut workspace_inherit = false;
    for raw in manifest.lines() {
        let line = strip_comment(raw).trim().to_owned();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            table = line
                .trim_matches(|c| c == '[' || c == ']')
                .trim_start_matches("workspace.")
                .replace(' ', "");
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            continue;
        };
        let key = key.trim().to_owned();
        let value: String = value.chars().filter(|c| !c.is_whitespace()).collect();
        if table == "lints" && key == "workspace" && value == "true" {
            workspace_inherit = true;
        }
        if table.starts_with("lints.") {
            entries.insert((table.clone(), key), value);
        }
    }
    (entries, workspace_inherit)
}

/// Drop a trailing `# comment` that is not inside a string.
fn strip_comment(line: &str) -> &str {
    let mut quoted = false;
    for (i, c) in line.char_indices() {
        match c {
            '"' => quoted = !quoted,
            '#' if !quoted => return line.get(..i).unwrap_or(line),
            _ => {}
        }
    }
    line
}

/// Rule 1: lint overrides in `manifest`, the manifest of the crate at
/// `dir` (repo-relative), given the workspace manifest.
pub fn lint_problems(dir: &str, manifest: &str, workspace: &str) -> Vec<String> {
    let (own, inherits) = lint_entries(manifest);
    let (ws, _) = lint_entries(workspace);
    let mut problems = Vec::new();
    let at = format!("{dir}/Cargo.toml");
    if dir != CRATE_DIR {
        if own.keys().any(|(_, k)| k == "unsafe_code") {
            problems.push(format!(
                "{at}: overrides `unsafe_code`; only {CRATE_DIR} may (CLAUDE.md rule 1)"
            ));
        }
        return problems;
    }
    if inherits {
        problems.push(format!(
            "{at}: must list the workspace lints itself (a crate cannot both inherit them \
             and override `unsafe_code`), not `workspace = true`"
        ));
    }
    let unsafe_key = ("lints.rust".to_owned(), "unsafe_code".to_owned());
    if own.get(&unsafe_key).map(String::as_str) != Some("\"allow\"") {
        problems.push(format!(
            "{at}: [lints.rust] must set unsafe_code = \"allow\""
        ));
    }
    for (key, value) in &ws {
        if *key != unsafe_key && own.get(key) != Some(value) {
            problems.push(format!(
                "{at}: lint {}.{} must equal the workspace's ({value}); only `unsafe_code` may differ",
                key.0, key.1
            ));
        }
    }
    for key in own
        .keys()
        .filter(|k| **k != unsafe_key && !ws.contains_key(*k))
    {
        problems.push(format!(
            "{at}: lint {}.{} is not a workspace lint; only `unsafe_code` may differ",
            key.0, key.1
        ));
    }
    problems
}

/// Rule 2: the crate's dependencies are `libc`, pinned exactly.
pub fn dependency_problems(
    deps: &[(String, String)],
    dev_deps: &[(String, String)],
) -> Vec<String> {
    let mut problems = Vec::new();
    for (name, req) in deps {
        if name != "libc" {
            problems.push(format!(
                "{CRATE_NAME}: dependency {name}; only `libc` is allowed"
            ));
        } else if !req.starts_with('=') {
            problems.push(format!(
                "{CRATE_NAME}: libc must be pinned to an exact version (\"=x.y.z\"), found {req:?}"
            ));
        }
    }
    for (name, _) in dev_deps {
        problems.push(format!(
            "{CRATE_NAME}: dev-dependency {name}; there may be none"
        ));
    }
    problems
}

// ------------------------------------------------------------------- audit

/// SHA-256 of the crate's source, as audited. The files hashed are every
/// regular file under `crates/clazel-sys` except hidden files and
/// directories and `target/`, in byte order of their repo-relative path.
/// For each file one line `<sha256 of the file>  <path>\n` is formed (the
/// output format of `shasum -a 256`), and the audit hash is the SHA-256 of
/// those lines together. To check by hand from the repository root:
///
/// ```sh
/// find crates/clazel-sys -type f -not -path '*/.*' -not -path '*/target/*' \
///   | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256
/// ```
pub fn source_hash(dir: &Path) -> Result<(String, Vec<String>), String> {
    let mut files = Vec::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(d) = pending.pop() {
        let entries = std::fs::read_dir(&d).map_err(|e| format!("{}: {e}", d.display()))?;
        for entry in entries {
            let path = entry.map_err(|e| format!("{}: {e}", d.display()))?.path();
            let name = path
                .file_name()
                .and_then(|n| n.to_str())
                .ok_or_else(|| format!("{}: name is not UTF-8", path.display()))?;
            if name.starts_with('.') || name == "target" {
                continue;
            }
            let kind = std::fs::symlink_metadata(&path)
                .map_err(|e| format!("{}: {e}", path.display()))?
                .file_type();
            if kind.is_symlink() {
                return Err(format!(
                    "{}: symbolic links are not allowed here",
                    path.display()
                ));
            }
            if kind.is_dir() {
                pending.push(path);
            } else {
                files.push(path);
            }
        }
    }
    let mut named: Vec<String> = files
        .iter()
        .map(|p| crate::workspace::relative(p))
        .collect();
    named.sort();
    let mut manifest = String::new();
    for name in &named {
        let hash = crate::reviews::sha256(Path::new(name))?;
        manifest.push_str(&format!("{hash}  {name}\n"));
    }
    Ok((sha256_bytes(manifest.as_bytes())?, named))
}

/// SHA-256 of `data`, via the system's `sha256sum` or `shasum`.
fn sha256_bytes(data: &[u8]) -> Result<String, String> {
    if cfg!(windows) {
        // `certutil` hashes files only.
        let path = std::env::temp_dir().join(format!("clazel-xtask-{}.sha", std::process::id()));
        std::fs::write(&path, data).map_err(|e| format!("{}: {e}", path.display()))?;
        let hash = crate::reviews::sha256(&path);
        let _ = std::fs::remove_file(&path);
        return hash;
    }
    let attempts: [(&str, &[&str]); 2] = [("sha256sum", &[]), ("shasum", &["-a", "256"])];
    for (tool, args) in attempts {
        let Ok(mut child) = Command::new(tool)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
        else {
            continue;
        };
        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(data).map_err(|e| format!("{tool}: {e}"))?;
        }
        let out = child
            .wait_with_output()
            .map_err(|e| format!("{tool}: {e}"))?;
        if out.status.success()
            && let Some(hash) = String::from_utf8_lossy(&out.stdout)
                .split_whitespace()
                .next()
        {
            return Ok(hash.to_ascii_lowercase());
        }
    }
    Err("cannot hash (need sha256sum or shasum)".to_owned())
}

/// One audit row.
#[derive(Debug)]
pub struct Audit {
    pub sha256: String,
    pub verdict: String,
}

const BEGIN: &str = "<!-- BEGIN AUDITS";
const END: &str = "<!-- END AUDITS -->";

/// Parse the audit table between the markers; rows are in file order, so
/// the last one is the latest.
pub fn parse_audits(text: &str) -> Result<Vec<Audit>, String> {
    let start = text
        .find(BEGIN)
        .ok_or_else(|| format!("{AUDITS}: no {BEGIN} marker"))?;
    let body = text.get(start..).unwrap_or_default();
    let end = body
        .find(END)
        .ok_or_else(|| format!("{AUDITS}: no {END} marker"))?;
    let mut rows = Vec::new();
    for line in body.get(..end).unwrap_or_default().lines().skip(1) {
        let line = line.trim();
        if !line.starts_with('|') {
            continue;
        }
        let cells: Vec<&str> = line.trim_matches('|').split('|').map(str::trim).collect();
        let [date, sha, auditor, against, verdict] = cells.as_slice() else {
            return Err(format!("{AUDITS}: expected 5 columns in: {line}"));
        };
        if *date == "Date" || date.chars().all(|c| c == '-') {
            continue;
        }
        if !(sha.len() == 64 && sha.chars().all(|c| c.is_ascii_hexdigit())) {
            return Err(format!("{AUDITS}: {date}: SHA-256 must be 64 hex digits"));
        }
        if [date, auditor, against, verdict]
            .iter()
            .any(|c| c.is_empty())
        {
            return Err(format!("{AUDITS}: {date}: every column is required"));
        }
        rows.push(Audit {
            sha256: sha.to_ascii_lowercase(),
            verdict: (*verdict).to_owned(),
        });
    }
    Ok(rows)
}

/// Rule 7: the latest audit approves exactly the current source.
pub fn audit_problems(log: &str, current: &str) -> Vec<String> {
    let rows = match parse_audits(log) {
        Ok(r) => r,
        Err(e) => return vec![e],
    };
    match rows.last() {
        None => vec![format!(
            "{AUDITS}: no audit of {CRATE_DIR}; its source has SHA-256 {current}. \
             A session other than the author's must audit it (CLAUDE.md rule 1)"
        )],
        Some(a) if a.sha256 != current => vec![format!(
            "{AUDITS}: stale audit of {CRATE_DIR}: the latest row covers {}, the source is now \
             {current}. Every change needs a new audit by a session other than the author's",
            a.sha256
        )],
        Some(a) if a.verdict != "approved" => vec![format!(
            "{AUDITS}: the latest audit of {CRATE_DIR} has verdict {:?}, not \"approved\"",
            a.verdict
        )],
        Some(_) => Vec::new(),
    }
}

// ------------------------------------------------------------------ README

const OLD_CLAIM: &str = "100% safe Rust. `unsafe` is forbidden workspace-wide.";
const NEW_CLAIM: &str = "100% safe Rust except `clazel-sys`: ";

/// The README claim says exactly what was measured: with no `unsafe`
/// anywhere, the old sentence; otherwise the new one, with the measured
/// numbers. The sentence is
/// ``100% safe Rust except `clazel-sys`: N `unsafe` blocks (M lines) that enter the OS sandbox, machine-checked and audited.``
pub fn readme_problems(readme: &str, blocks: usize, lines: usize) -> Vec<String> {
    let mut problems = Vec::new();
    let has_old = readme.contains(OLD_CLAIM);
    let new = readme
        .split_once(NEW_CLAIM)
        .map(|(_, rest)| parse_claim(rest));
    if blocks == 0 {
        if !has_old {
            problems.push(format!(
                "README.md: the workspace has no `unsafe`, so it must say \"{OLD_CLAIM}\""
            ));
        }
        if new.is_some() {
            problems.push(
                "README.md: claims `clazel-sys` `unsafe` blocks, but none exist yet; the claim \
                 changes in the commit that adds the first one"
                    .to_owned(),
            );
        }
        return problems;
    }
    if has_old {
        problems.push(format!(
            "README.md: still says \"{OLD_CLAIM}\", but {blocks} `unsafe` blocks exist"
        ));
    }
    match new {
        None => problems.push(format!(
            "README.md: must say \"{NEW_CLAIM}{blocks} `unsafe` blocks ({lines} lines) that \
             enter the OS sandbox, machine-checked and audited.\""
        )),
        Some(Some((n, m))) if n == blocks && m == lines => {}
        Some(Some((n, m))) => problems.push(format!(
            "README.md claims {n} `unsafe` blocks ({m} lines); measured {blocks} ({lines} lines)"
        )),
        Some(None) => problems.push(format!(
            "README.md: the `clazel-sys` sentence must read \"{NEW_CLAIM}N `unsafe` blocks \
             (M lines) that enter the OS sandbox, machine-checked and audited.\""
        )),
    }
    problems
}

/// Parse "N `unsafe` blocks (M lines) that enter the OS sandbox, machine-checked and audited."
fn parse_claim(rest: &str) -> Option<(usize, usize)> {
    let (n, rest) = rest.split_once(" `unsafe` blocks (")?;
    let (m, rest) = rest.split_once(" lines) ")?;
    rest.starts_with("that enter the OS sandbox, machine-checked and audited.")
        .then_some(())?;
    Some((n.parse().ok()?, m.parse().ok()?))
}

#[cfg(test)]
mod tests {
    use super::{
        audit_problems, check_source, cites_man_page, dependency_problems, lint_problems,
        readme_problems,
    };

    const WORKSPACE: &str = "[workspace.lints.rust]\nunsafe_code = \"forbid\"\nmissing_docs = \"warn\"\n\
        [workspace.lints.clippy]\npanic = \"deny\"\n";
    const SYS_MANIFEST: &str = "[lints.rust]\nunsafe_code = \"allow\"\nmissing_docs = \"warn\"\n\
        [lints.clippy]\npanic = \"deny\"\n";
    const SHA_A: &str = "83cafc50284caea07fa8762df04b00cc0af441f25cdf1631d6c30987c65af446";
    const SHA_B: &str = "7f1d2ff4c6e25d8ef7c1b0f7ae5a7b9d5dd1d4f3f2f4ad8a4d0d9e1f2a3b4c5d";

    const LINUX_FILE: &str = "crates/clazel-sys/src/linux.rs";
    const MACOS_FILE: &str = "crates/clazel-sys/src/macos.rs";

    fn violations(src: &str) -> Result<Vec<String>, String> {
        violations_in(LINUX_FILE, src)
    }

    fn violations_in(path: &str, src: &str) -> Result<Vec<String>, String> {
        Ok(check_source(path, src)?
            .violations
            .into_iter()
            .map(|(line, what)| format!("{line}: {what}"))
            .collect())
    }

    fn good(call: &str) -> String {
        format!(
            "fn f() -> i32 {{\n    // SAFETY: man 2 prctl; the libc declaration matches.\n    unsafe {{ {call} }}\n}}\n"
        )
    }

    #[test]
    fn accepts_a_listed_call_with_a_safety_comment() -> Result<(), String> {
        assert_eq!(
            violations(&good("libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)"))?,
            Vec::<String>::new()
        );
        assert_eq!(
            violations(&good("libc::syscall(libc::SYS_seccomp, 1, 0, p)"))?,
            Vec::<String>::new()
        );
        let multi = "// SAFETY: man 3 sandbox_init. Pointers are valid\n\
                     // for the call.\nlet r = unsafe { sandbox_init(p, 0, e) };\n\
                     // SAFETY: man 3 sandbox_init; declared as in <sandbox.h>.\n\
                     unsafe extern \"C\" { fn sandbox_init(a: i32) -> i32; }";
        assert_eq!(violations_in(MACOS_FILE, multi)?, Vec::<String>::new());
        Ok(())
    }

    #[test]
    fn planted_foreign_function_of_another_file() -> Result<(), String> {
        let decl = "// SAFETY: man 3 sandbox_init.\n\
                    unsafe extern \"C\" { fn sandbox_init(a: i32) -> i32; }";
        assert_eq!(violations_in(MACOS_FILE, decl)?, Vec::<String>::new());
        for path in [LINUX_FILE, "crates/clazel-sys/src/lib.rs", "src/macos.rs"] {
            assert!(
                violations_in(path, decl)?
                    .iter()
                    .any(|m| m.contains("`sandbox_init` is not a permitted")),
                "{path}"
            );
        }
        let call = good("libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0)");
        assert!(
            violations_in(MACOS_FILE, &call)?
                .iter()
                .any(|m| m.contains("`prctl` is not a permitted"))
        );
        Ok(())
    }

    #[test]
    fn planted_unlisted_foreign_function() -> Result<(), String> {
        let v = violations(&good("libc::open(p, 0)"))?;
        assert!(
            v.iter()
                .any(|m| m.contains("`open` is not a permitted foreign function"))
        );
        let v = violations(&good("libc::syscall(libc::SYS_execve, p)"))?;
        assert!(v.iter().any(|m| m.contains("`syscall` with")));
        let decl = "// SAFETY: man 2 open.\nunsafe extern \"C\" { fn open(p: i32) -> i32; }";
        assert!(
            violations(decl)?
                .iter()
                .any(|m| m.contains("`open` is not a permitted"))
        );
        Ok(())
    }

    #[test]
    fn planted_unsafe_without_safety_comment() -> Result<(), String> {
        let none = "fn f() {\n    unsafe { libc::prctl(1) };\n}";
        assert!(
            violations(none)?
                .iter()
                .any(|m| m.contains("without a `// SAFETY:`"))
        );
        // A blank line between the comment and the block breaks "directly above".
        let gap = "// SAFETY: man 2 prctl.\n\nunsafe { libc::prctl(1) };";
        assert!(
            violations(gap)?
                .iter()
                .any(|m| m.contains("without a `// SAFETY:`"))
        );
        // Any other comment does not do.
        let other = "// call prctl\nunsafe { libc::prctl(1) };";
        assert!(
            violations(other)?
                .iter()
                .any(|m| m.contains("without a `// SAFETY:`"))
        );
        let no_man = "// SAFETY: trust me.\nunsafe { libc::prctl(1) };";
        assert!(
            violations(no_man)?
                .iter()
                .any(|m| m.contains("does not cite a man page"))
        );
        Ok(())
    }

    #[test]
    fn one_call_per_block_and_no_other_unsafe_forms() -> Result<(), String> {
        let two = good("libc::prctl(1); libc::prctl(2)");
        assert!(violations(&two)?.iter().any(|m| m.contains("found 2")));
        let none = good("0");
        assert!(violations(&none)?.iter().any(|m| m.contains("found 0")));
        let helper = good("libc::prctl(helper(1))");
        assert!(
            violations(&helper)?
                .iter()
                .any(|m| m.contains("`helper` is not"))
        );
        let deref = good("*p");
        assert!(
            violations(&deref)?
                .iter()
                .any(|m| m.contains("dereference"))
        );
        let nested = good("unsafe { libc::prctl(1) }");
        assert!(violations(&nested)?.iter().any(|m| m.contains("nested")));
        for src in [
            "pub unsafe fn f() {}",
            "pub unsafe extern \"C\" fn f() {}",
            "unsafe extern \"C\" fn f() {}",
            "unsafe impl Send for X {}",
            "unsafe trait T {}",
        ] {
            assert!(
                violations(src)?
                    .iter()
                    .any(|m| m.contains("may only start a block"))
            );
        }
        assert!(
            violations("pub extern \"C\" fn f() {}")?
                .iter()
                .any(|m| m.contains("outside"))
        );
        Ok(())
    }

    #[test]
    fn no_pointer_arithmetic_and_every_public_function_safe() -> Result<(), String> {
        for src in [
            "fn f(p: *const u8) -> *const u8 { p.add(1) }",
            "fn f(p: *const u8) -> *const u8 { p.wrapping_offset(1) }",
            "fn f(p: *const u8) -> *const u8 { p.byte_add::<>(1) }",
        ] {
            assert!(
                violations(src)?
                    .iter()
                    .any(|m| m.contains("pointer arithmetic")),
                "{src}"
            );
        }
        let public = "// SAFETY: man 3 sandbox_init.\nunsafe extern \"C\" { pub fn sandbox_init(a: i32) -> i32; }";
        assert!(violations(public)?.iter().any(|m| m.contains("`pub`")));
        let safe_fn = "// SAFETY: man 3 sandbox_init.\nunsafe extern \"C\" { safe fn sandbox_init(a: i32) -> i32; }";
        assert!(violations(safe_fn)?.iter().any(|m| m.contains("`safe fn`")));
        assert!(
            violations("pub use libc::prctl;")?
                .iter()
                .any(|m| m.contains("export"))
        );
        assert!(violations("pub use crate::x::Y;")?.is_empty());
        assert!(
            violations("macro_rules! m { () => {} }")?
                .iter()
                .any(|m| m.contains("hide"))
        );
        assert!(
            violations("#[path = \"x.rs\"] mod x;")?
                .iter()
                .any(|m| m.contains("#[path]"))
        );
        Ok(())
    }

    #[test]
    fn man_page_citation_forms() {
        assert!(cites_man_page("SAFETY: man 2 prctl"));
        assert!(cites_man_page("see man 3 sandbox_init for it"));
        assert!(!cites_man_page("a human wrote this"));
        assert!(!cites_man_page("man page"));
    }

    #[test]
    fn planted_second_crate_overriding_unsafe_code() {
        let other = "[package]\nname = \"clazel-evil\"\n[lints.rust]\nunsafe_code = \"allow\"\n";
        let p = lint_problems("crates/clazel-evil", other, WORKSPACE);
        assert_eq!(p.len(), 1, "{p:?}");
        assert!(p.iter().all(|m| m.contains("only crates/clazel-sys may")));
        assert!(
            lint_problems(
                "crates/clazel-url",
                "[lints]\nworkspace = true\n",
                WORKSPACE
            )
            .is_empty()
        );
        // The sys crate itself: fine as listed, wrong if it loosens any other lint.
        assert!(lint_problems("crates/clazel-sys", SYS_MANIFEST, WORKSPACE).is_empty());
        let loose = SYS_MANIFEST.replace("panic = \"deny\"", "panic = \"allow\"");
        assert!(!lint_problems("crates/clazel-sys", &loose, WORKSPACE).is_empty());
        let extra = format!("{SYS_MANIFEST}dead_code = \"allow\"\n");
        assert!(!lint_problems("crates/clazel-sys", &extra, WORKSPACE).is_empty());
        let inherit = "[lints]\nworkspace = true\n";
        assert!(!lint_problems("crates/clazel-sys", inherit, WORKSPACE).is_empty());
        let forbid = SYS_MANIFEST.replace("\"allow\"", "\"warn\"");
        assert!(!lint_problems("crates/clazel-sys", &forbid, WORKSPACE).is_empty());
    }

    #[test]
    fn dependencies_are_libc_pinned() {
        let libc = |r: &str| vec![("libc".to_owned(), r.to_owned())];
        assert!(dependency_problems(&libc("=0.2.190"), &[]).is_empty());
        assert_eq!(dependency_problems(&libc("0.2"), &[]).len(), 1);
        let other = vec![("cc".to_owned(), "=1.0.0".to_owned())];
        assert_eq!(dependency_problems(&other, &[]).len(), 1);
        assert_eq!(dependency_problems(&[], &other).len(), 1);
    }

    fn log(rows: &[(&str, &str)]) -> String {
        let mut s = "<!-- BEGIN AUDITS -->\n| Date | SHA-256 | Auditor | Audited against | Verdict |\n|---|---|---|---|---|\n".to_owned();
        for (sha, verdict) in rows {
            s.push_str(&format!(
                "| 2026-10-22 | {sha} | session | man pages | {verdict} |\n"
            ));
        }
        s.push_str("<!-- END AUDITS -->\n");
        s
    }

    #[test]
    fn planted_stale_audit_hash() {
        assert!(audit_problems(&log(&[(SHA_A, "approved")]), SHA_A).is_empty());
        let stale = audit_problems(&log(&[(SHA_A, "approved")]), SHA_B);
        assert!(stale.iter().any(|m| m.contains("stale audit")), "{stale:?}");
        // Only the latest row counts: an old match does not save a new change.
        let old = audit_problems(&log(&[(SHA_A, "approved"), (SHA_B, "approved")]), SHA_A);
        assert!(old.iter().any(|m| m.contains("stale audit")));
        assert!(
            audit_problems(&log(&[]), SHA_A)
                .iter()
                .any(|m| m.contains("no audit"))
        );
        let rejected = audit_problems(&log(&[(SHA_A, "rejected")]), SHA_A);
        assert!(rejected.iter().any(|m| m.contains("not \"approved\"")));
        assert!(!audit_problems("no markers", SHA_A).is_empty());
        assert!(!audit_problems(&log(&[("abc", "approved")]), SHA_A).is_empty());
    }

    #[test]
    fn planted_wrong_readme_count() {
        let claim = |n: usize, m: usize| {
            format!(
                "- **Memory safe:** 100% safe Rust except `clazel-sys`: {n} `unsafe` blocks \
                 ({m} lines) that enter the OS sandbox, machine-checked and audited.\n"
            )
        };
        assert!(readme_problems(&claim(7, 31), 7, 31).is_empty());
        let wrong_n = readme_problems(&claim(6, 31), 7, 31);
        assert!(
            wrong_n.iter().any(|m| m.contains("claims 6")),
            "{wrong_n:?}"
        );
        assert!(!readme_problems(&claim(7, 30), 7, 31).is_empty());
        // The old sentence is wrong once unsafe exists, and the new one before.
        let old = "- 100% safe Rust. `unsafe` is forbidden workspace-wide.\n";
        assert!(!readme_problems(old, 7, 31).is_empty());
        assert!(readme_problems(old, 0, 0).is_empty());
        assert!(!readme_problems(&claim(0, 0), 0, 0).is_empty());
        assert!(!readme_problems("nothing", 7, 31).is_empty());
        let garbled = "100% safe Rust except `clazel-sys`: many `unsafe` blocks.";
        assert!(!readme_problems(garbled, 7, 31).is_empty());
    }

    // ----------------------------------------------------------- vtable calls

    const VTABLES: &[super::Vtable] = &[
        ("IUnknownVtbl", &["QueryInterface", "AddRef", "Release"]),
        (
            "IThingVtbl",
            &["QueryInterface", "AddRef", "Release", "Make"],
        ),
    ];

    fn vtable_violations(src: &str) -> Result<(Vec<String>, usize), String> {
        let f = super::check_with("d3d12.rs", src, &["CloseHandle"], &[], VTABLES)?;
        Ok((
            f.violations
                .into_iter()
                .map(|(line, what)| format!("{line}: {what}"))
                .collect(),
            f.vtable_calls,
        ))
    }

    fn vtable_rejected(src: &str, why: &str) -> Result<(), String> {
        let (v, _) = vtable_violations(src)?;
        assert!(v.iter().any(|m| m.contains(why)), "{why}: {v:?}\n{src}");
        Ok(())
    }

    const UNKNOWN: &str = "#[repr(C)]\nstruct IUnknownVtbl {\n    query_interface: usize,\n    \
        add_ref: usize,\n    /// Drop one reference.\n    \
        release: unsafe extern \"system\" fn(*mut IUnknown) -> u32,\n}\n\
        type IUnknown = *const IUnknownVtbl;\n";

    fn com_call(body: &str) -> String {
        format!(
            "{UNKNOWN}fn f(this: *mut IUnknown) -> u32 {{\n    // SAFETY: docs IUnknown::Release.\n    \
             unsafe {{ {body} }}\n}}\n"
        )
    }

    #[test]
    fn accepts_a_listed_vtable_and_a_call_through_it() -> Result<(), String> {
        let (v, calls) = vtable_violations(&com_call("((**this).release)(this)"))?;
        assert_eq!(v, Vec::<String>::new());
        assert_eq!(calls, 1);
        // With arguments after the receiver, nested groups included.
        let make = "#[repr(C)]\nstruct IThingVtbl {\n    query_interface: usize,\n    add_ref: usize,\n    \
            release: usize,\n    make: unsafe extern \"system\" fn(*mut IThing, u32, *mut *mut u8) -> i32,\n}\n\
            type IThing = *const IThingVtbl;\n\
            fn f(thing: *mut IThing, out: *mut *mut u8) -> i32 {\n    // SAFETY: docs IThing::Make.\n    \
            unsafe { ((**thing).make)(thing, (1u32), out) }\n}\n";
        let (v, calls) = vtable_violations(make)?;
        assert_eq!(v, Vec::<String>::new());
        assert_eq!(calls, 1);
        Ok(())
    }

    /// The same source where no vtable is listed (every file but Direct3D's).
    #[test]
    fn a_vtable_call_needs_the_files_list() -> Result<(), String> {
        let v = violations_in(LINUX_FILE, &com_call("((**this).release)(this)"))?;
        assert!(
            v.iter().any(|m| m.contains("function pointer type")),
            "{v:?}"
        );
        assert!(
            v.iter().any(|m| m.contains("not a slot of a vtable")),
            "{v:?}"
        );
        Ok(())
    }

    #[test]
    fn rejects_every_other_call_through_an_expression() -> Result<(), String> {
        let form = "must be exactly `((**this).method)(this, ..)`";
        for body in [
            // One dereference, three, a field between them, a method call as the
            // receiver, a slot read first, an index.
            "((*this).release)(this)",
            "((***this).release)(this)",
            "((*(*this).vtbl).release)(this)",
            "((**this.get()).release)(this)",
            "(this.release)(this)",
            "((**this)[2])(this)",
            "(f)(this)",
        ] {
            vtable_rejected(&com_call(body), form)?;
        }
        // A slot that is on no list, and one of another crate's naming.
        vtable_rejected(
            &com_call("((**this).destroy)(this)"),
            "`destroy` is not a slot",
        )?;
        // The receiver must be the first argument, alone.
        for body in [
            "((**this).release)()",
            "((**this).release)(other)",
            "((**this).release)(this.cast())",
            "((**this).release)(other, this)",
        ] {
            vtable_rejected(&com_call(body), "first argument must be its receiver")?;
        }
        Ok(())
    }

    #[test]
    fn a_vtable_call_is_the_blocks_one_call_and_needs_its_comment() -> Result<(), String> {
        vtable_rejected(
            &com_call("((**this).release)(this); ((**this).release)(this)"),
            "exactly one foreign call, found 2",
        )?;
        vtable_rejected(
            &com_call("((**this).release)(this); CloseHandle(0)"),
            "exactly one foreign call, found 2",
        )?;
        // A dereference in an argument is still a dereference.
        let deref = format!(
            "{UNKNOWN}fn f(this: *mut IUnknown, p: *mut u32) -> u32 {{\n    // SAFETY: docs IUnknown::Release.\n    \
             unsafe {{ ((**this).release)(this, *p) }}\n}}\n"
        );
        vtable_rejected(&deref, "dereference or multiplication")?;
        let bare = format!(
            "{UNKNOWN}fn f(this: *mut IUnknown) -> u32 {{\n    unsafe {{ ((**this).release)(this) }}\n}}\n"
        );
        vtable_rejected(&bare, "without a `// SAFETY:` comment")?;
        // Outside an `unsafe` block it does not compile, and is not this check's.
        Ok(())
    }

    #[test]
    fn rejects_a_vtable_that_differs_from_its_list() -> Result<(), String> {
        let decl = |attr: &str, fields: &str| format!("{attr}struct IUnknownVtbl {{ {fields} }}\n");
        let release = "release: unsafe extern \"system\" fn(*mut u8) -> u32";
        let good = decl(
            "#[repr(C)]\n",
            &format!("query_interface: usize, add_ref: usize, {release},"),
        );
        assert_eq!(vtable_violations(&good)?.0, Vec::<String>::new());
        let cases = [
            // No `repr(C)`, or another representation.
            (
                decl(
                    "",
                    &format!("query_interface: usize, add_ref: usize, {release}"),
                ),
                "directly under `#[repr(C)]`",
            ),
            (
                decl(
                    "#[repr(packed)]\n",
                    &format!("query_interface: usize, add_ref: usize, {release}"),
                ),
                "directly under `#[repr(C)]`",
            ),
            // A slot missing, two swapped, one added, one renamed.
            (
                decl(
                    "#[repr(C)]\n",
                    &format!("query_interface: usize, {release}"),
                ),
                "exactly the listed slots in order",
            ),
            (
                decl(
                    "#[repr(C)]\n",
                    &format!("add_ref: usize, query_interface: usize, {release}"),
                ),
                "exactly the listed slots in order",
            ),
            (
                decl(
                    "#[repr(C)]\n",
                    &format!("query_interface: usize, add_ref: usize, {release}, more: usize"),
                ),
                "exactly the listed slots in order",
            ),
            (
                decl(
                    "#[repr(C)]\n",
                    "query_interface: usize, add_ref: usize, free: usize",
                ),
                "exactly the listed slots in order",
            ),
            // A slot of another type: a narrower integer, a data pointer, a
            // safe function, another ABI.
            (
                decl(
                    "#[repr(C)]\n",
                    "query_interface: u32, add_ref: usize, release: usize",
                ),
                "slot `query_interface` must be `usize`",
            ),
            (
                decl(
                    "#[repr(C)]\n",
                    "query_interface: *const u8, add_ref: usize, release: usize",
                ),
                "slot `query_interface` must be `usize`",
            ),
            (
                decl(
                    "#[repr(C)]\n",
                    "query_interface: usize, add_ref: usize, release: extern \"system\" fn(*mut u8) -> u32",
                ),
                "slot `release` must be `usize`",
            ),
            (
                decl(
                    "#[repr(C)]\n",
                    "query_interface: usize, add_ref: usize, release: unsafe extern \"C\" fn(*mut u8) -> u32",
                ),
                "slot `release` must be `usize`",
            ),
            // A tuple struct.
            (
                "#[repr(C)]\nstruct IUnknownVtbl(usize, usize, usize);\n".to_owned(),
                "must be a `struct` with named fields",
            ),
        ];
        for (src, why) in cases {
            vtable_rejected(&src, why)?;
        }
        Ok(())
    }

    #[test]
    fn rejects_a_function_pointer_type_anywhere_else() -> Result<(), String> {
        for src in [
            "struct NotListed { f: unsafe extern \"system\" fn() }\n",
            "fn f(g: unsafe extern \"system\" fn()) {}\n",
            "type G = unsafe extern \"C\" fn(u32) -> u32;\n",
        ] {
            vtable_rejected(src, "function pointer type is only allowed")?;
        }
        Ok(())
    }

    #[test]
    fn a_slots_field_is_its_name_in_snake_case() {
        for (method, field) in [
            ("Release", "release"),
            ("QueryInterface", "query_interface"),
            ("EnumAdapters1", "enum_adapters1"),
            ("IASetPrimitiveTopology", "ia_set_primitive_topology"),
            (
                "SetGraphicsRoot32BitConstants",
                "set_graphics_root32_bit_constants",
            ),
            (
                "GetCPUDescriptorHandleForHeapStart",
                "get_cpu_descriptor_handle_for_heap_start",
            ),
            ("GetGPUVirtualAddress", "get_gpu_virtual_address"),
        ] {
            assert_eq!(super::slot_field(method), field);
        }
    }

    /// Every listed vtable begins with `IUnknown`'s three slots, and no slot is
    /// listed twice in one: a slot's place in the list is its number.
    #[test]
    fn the_listed_vtables_are_well_formed() {
        for (file, tables) in super::VTABLES {
            for (name, slots) in *tables {
                assert_eq!(
                    slots.get(..3),
                    Some(&["QueryInterface", "AddRef", "Release"][..]),
                    "{file}: {name}"
                );
                let mut seen = std::collections::BTreeSet::new();
                for s in *slots {
                    let field = super::slot_field(s);
                    assert!(
                        field
                            .chars()
                            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_'),
                        "{file}: {name}: {field}"
                    );
                    assert!(seen.insert(field), "{file}: {name} lists {s} twice");
                }
                assert!(name.ends_with("Vtbl"), "{file}: {name}");
            }
        }
    }

    // ------------------------------------------------------- dispatcher casts

    const DISPATCH_FOREIGN: &[&str] = &["objc_msgSend", "objc_getClass"];
    const DISPATCH_CASTS: &[&str] = &["MSG_ID"];

    fn cast_violations(src: &str) -> Result<(Vec<String>, usize), String> {
        let f = super::check_with("metal.rs", src, DISPATCH_FOREIGN, DISPATCH_CASTS, &[])?;
        Ok((
            f.violations
                .into_iter()
                .map(|(line, what)| format!("{line}: {what}"))
                .collect(),
            f.dispatcher_casts,
        ))
    }

    const DECL: &str = "// SAFETY: docs ObjectiveC/objc_msgSend.\nunsafe extern \"C-unwind\" { fn objc_msgSend(); }\n";
    const CAST: &str = "// SAFETY: docs ObjectiveC/objc_msgSend; the cast Apple prescribes.\n\
        const MSG_ID: unsafe extern \"C-unwind\" fn(*mut u8, *mut u8) -> *mut u8 =\n\
        unsafe { std::mem::transmute(objc_msgSend as unsafe extern \"C-unwind\" fn()) };\n";
    const CALL: &str = "fn f(r: *mut u8, s: *mut u8) -> *mut u8 {\n\
        // SAFETY: docs ObjectiveC/NSObject/new.\n    unsafe { MSG_ID(r, s) }\n}\n";

    #[test]
    fn accepts_a_dispatcher_cast_and_calls_through_it() -> Result<(), String> {
        let (v, casts) = cast_violations(&format!("{DECL}{CAST}{CALL}"))?;
        assert_eq!(v, Vec::<String>::new());
        assert_eq!(casts, 1);
        Ok(())
    }

    fn rejected(src: &str, why: &str) -> Result<(), String> {
        let (v, _) = cast_violations(src)?;
        assert!(v.iter().any(|m| m.contains(why)), "{why}: {v:?}\n{src}");
        Ok(())
    }

    /// The macOS window's file has its own lists: its casts and calls pass there,
    /// and the same source in `metal.rs` (whose lists lack `MSG_POINT` and
    /// `CGImageCreate`) or in `macos.rs` (which may use no dispatcher) is rejected.
    #[test]
    fn the_window_file_has_its_own_lists() -> Result<(), String> {
        const WINDOW_FILE: &str = "crates/clazel-sys/src/macos/window.rs";
        const METAL_FILE: &str = "crates/clazel-sys/src/macos/metal.rs";
        let point = "// SAFETY: docs ObjectiveC/objc_msgSend; the cast Apple prescribes.\n\
            const MSG_POINT: unsafe extern \"C-unwind\" fn(*mut u8, *mut u8) -> [f64; 2] =\n\
            unsafe { std::mem::transmute(objc_msgSend as unsafe extern \"C-unwind\" fn()) };\n\
            fn f(r: *mut u8, s: *mut u8) -> [f64; 2] {\n\
            // SAFETY: docs AppKit/NSEvent/locationInWindow.\n    unsafe { MSG_POINT(r, s) }\n}\n";
        let image = "// SAFETY: docs CoreGraphics/CGImageCreate.\n\
            unsafe extern \"C\" { fn CGImageCreate(w: usize) -> *mut u8; }\n";
        let source = format!("{DECL}{point}{image}");
        assert_eq!(violations_in(WINDOW_FILE, &source)?, Vec::<String>::new());
        let in_window = check_source(WINDOW_FILE, &source)?;
        assert_eq!(in_window.dispatcher_casts, 1);
        let in_metal = violations_in(METAL_FILE, &source)?;
        assert!(
            in_metal
                .iter()
                .any(|m| m.contains("`transmute` is only allowed"))
        );
        assert!(
            in_metal
                .iter()
                .any(|m| m.contains("`CGImageCreate` is not a permitted"))
        );
        let in_macos = violations_in(MACOS_FILE, &source)?;
        assert!(
            in_macos
                .iter()
                .any(|m| m.contains("`objc_msgSend` is not a permitted"))
        );
        Ok(())
    }

    #[test]
    fn planted_transmute_of_data_or_elsewhere() -> Result<(), String> {
        // Of data, in a listed const.
        rejected(
            &format!(
                "{DECL}// SAFETY: docs X.\nconst MSG_ID: unsafe extern \"C-unwind\" fn() = unsafe {{ std::mem::transmute(7usize) }};"
            ),
            "must be exactly",
        )?;
        // Of a dispatcher, in a const not on the list.
        rejected(
            &format!(
                "{DECL}// SAFETY: docs X.\nconst OTHER: unsafe extern \"C-unwind\" fn() = unsafe {{ std::mem::transmute(objc_msgSend as unsafe extern \"C-unwind\" fn()) }};"
            ),
            "`transmute` is only allowed",
        )?;
        // In a function.
        rejected(
            &format!(
                "{DECL}fn f() {{\n// SAFETY: docs X.\nunsafe {{ std::mem::transmute::<u32, f32>(1) }};\n}}"
            ),
            "`transmute` is only allowed",
        )?;
        rejected(
            "fn f() { let x = std::mem::transmute_copy(&1u8); }",
            "`transmute_copy` is only allowed",
        )?;
        // A turbofish, another path, or more than the one call.
        for value in [
            "std::mem::transmute::<unsafe extern \"C-unwind\" fn(), unsafe extern \"C-unwind\" fn()>(objc_msgSend as unsafe extern \"C-unwind\" fn())",
            "core::mem::transmute(objc_msgSend as unsafe extern \"C-unwind\" fn())",
            "std::mem::transmute(objc_getClass as unsafe extern \"C-unwind\" fn())",
            "std::mem::transmute(objc_msgSend as unsafe extern \"C-unwind\" fn(u8))",
            "std::mem::transmute(objc_msgSend as unsafe extern \"C-unwind\" fn()); objc_getClass(p)",
        ] {
            rejected(
                &format!(
                    "{DECL}// SAFETY: docs X.\nconst MSG_ID: unsafe extern \"C-unwind\" fn() = unsafe {{ {value} }};"
                ),
                "must be exactly",
            )?;
        }
        Ok(())
    }

    #[test]
    fn planted_wrong_target_type_or_no_safety_comment() -> Result<(), String> {
        for ty in [
            "usize",
            "unsafe extern \"C\" fn()",
            "unsafe extern \"system\" fn()",
            "extern \"C-unwind\" fn()",
            "Option<unsafe extern \"C-unwind\" fn()>",
        ] {
            rejected(
                &format!(
                    "{DECL}// SAFETY: docs X.\nconst MSG_ID: {ty} = unsafe {{ std::mem::transmute(objc_msgSend as unsafe extern \"C-unwind\" fn()) }};"
                ),
                "must be exactly",
            )?;
        }
        rejected(
            &format!(
                "{DECL}const MSG_ID: unsafe extern \"C-unwind\" fn() = unsafe {{ std::mem::transmute(objc_msgSend as unsafe extern \"C-unwind\" fn()) }};"
            ),
            "without a `// SAFETY:`",
        )
    }

    /// `"C"` anywhere a dispatcher is declared or cast is rejected, so no cast
    /// can mix the two ABIs.
    #[test]
    fn planted_c_abi_instead_of_c_unwind() -> Result<(), String> {
        let c_decl = "// SAFETY: docs X.\nunsafe extern \"C\" { fn objc_msgSend(); }\n";
        rejected(
            &format!("{c_decl}{CAST}{CALL}"),
            "must be declared in an `unsafe extern \"C-unwind\"` block",
        )?;
        rejected(
            "// SAFETY: docs X.\nunsafe extern { fn objc_msgSend(); }\n",
            "must be declared in an `unsafe extern \"C-unwind\"` block",
        )?;
        // The cast's type, its source, or both, in `"C"`.
        for (ty, source) in [
            (
                "unsafe extern \"C\" fn(*mut u8, *mut u8) -> *mut u8",
                "C-unwind",
            ),
            (
                "unsafe extern \"C-unwind\" fn(*mut u8, *mut u8) -> *mut u8",
                "C",
            ),
            ("unsafe extern \"C\" fn(*mut u8, *mut u8) -> *mut u8", "C"),
        ] {
            rejected(
                &format!(
                    "{DECL}// SAFETY: docs X.\nconst MSG_ID: {ty} = unsafe {{ std::mem::transmute(objc_msgSend as unsafe extern \"{source}\" fn()) }};"
                ),
                "must be exactly",
            )?;
        }
        Ok(())
    }

    #[test]
    fn planted_dispatcher_used_any_other_way() -> Result<(), String> {
        // Called directly.
        rejected(
            &format!("{DECL}fn f() {{\n// SAFETY: docs X.\nunsafe {{ objc_msgSend() }};\n}}"),
            "dispatcher `objc_msgSend` may only",
        )?;
        // Made into a function pointer another way.
        rejected(
            &format!("{DECL}fn f() {{ let p = objc_msgSend as unsafe extern \"C-unwind\" fn(); }}"),
            "dispatcher `objc_msgSend` may only",
        )?;
        // Declared with parameters.
        rejected(
            "// SAFETY: docs X.\nunsafe extern \"C-unwind\" { fn objc_msgSend(a: u8); }",
            "must be declared `fn objc_msgSend();`",
        )?;
        rejected(
            "// SAFETY: docs X.\nunsafe extern \"C-unwind\" { fn objc_msgSend() -> u8; }",
            "must be declared `fn objc_msgSend();`",
        )
    }

    #[test]
    fn planted_call_through_another_pointer_or_a_shadowed_cast() -> Result<(), String> {
        // A local function pointer is not on the list.
        rejected(
            &format!("{DECL}{CAST}fn f(p: u8) {{\n// SAFETY: docs X.\nunsafe {{ p(1) }};\n}}"),
            "`p` is not a permitted",
        )?;
        // A cast's name rebound, or passed around, or called outside `unsafe`.
        rejected(
            &format!("{DECL}{CAST}fn f() {{ let MSG_ID = 3; }}"),
            "dispatcher cast `MSG_ID` may only be called",
        )?;
        rejected(
            &format!("{DECL}{CAST}fn f() {{ let g = MSG_ID; }}"),
            "dispatcher cast `MSG_ID` may only be called",
        )?;
        // Two calls in one block.
        rejected(
            &format!(
                "{DECL}{CAST}fn f(r: *mut u8) {{\n// SAFETY: docs X.\nunsafe {{ MSG_ID(r, r); MSG_ID(r, r) }};\n}}"
            ),
            "found 2",
        )
    }
}

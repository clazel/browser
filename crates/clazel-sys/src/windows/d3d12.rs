//! Windows: Direct3D 12 for the GPU process (phase-5.md item 5.17b). A device
//! on an adapter DXGI lists or on WARP, one offscreen RGBA8 render target, one
//! fixed pipeline, buffers the shaders read, and a copy of the target into a
//! buffer the CPU can read.
//!
//! **Nothing in this file has run.** It was written on a Mac and compiled for
//! `x86_64-pc-windows-msvc` without its tests. The structures and vtables it
//! passes are in `crate::d3d12_abi`, whose sizes, offsets and slot numbers are
//! tested against the headers on every target; the order of the calls, their
//! arguments and what Direct3D makes of them are not tested at all.
//!
//! # How COM is called
//!
//! An interface pointer points to an object whose first word points to a table
//! of functions, the interface's methods in the header's order (Microsoft Learn,
//! "COM Objects and Interfaces"). A method is called through its slot with the
//! interface pointer as the first argument:
//! `((**this).create_fence)(this, ..)`. `xtask/src/sys.rs` accepts exactly that
//! form, for the slots of the vtables it lists, as an `unsafe` block's one call.
//! The citations are the Microsoft Learn pages of each method,
//! `https://learn.microsoft.com/windows/win32/api/<header>/nf-<header>-<interface>-<method>`,
//! written `docs <Interface>::<Method>`.
//!
//! Every interface begins with `IUnknown`'s three methods, so [`Com`] releases
//! any of them through `IUnknownVtbl`. A [`Com`] owns one reference, taken from
//! the call that created the object, and releases it when dropped; no other
//! reference is counted here (`AddRef` is never called), and no interface
//! pointer leaves this file.
//!
//! # Modelling choices
//!
//! - **No policy.** Which adapter, what to draw and in what order are the
//!   caller's (`clazel-gpu`). This file checks only what a call's safety needs:
//!   lengths, counts, and that a buffer is used the way it was made.
//! - **One command list, one submission at a time, each waited for.**
//!   [`Device::render`] and [`Device::copy_target`] reset the allocator and the
//!   list, record, close, execute, signal the fence and wait for it
//!   (`ID3D12Fence::SetEventOnCompletion` with no event, which blocks until the
//!   value is reached). So nothing is in flight when a method returns, a buffer
//!   may be written or dropped between calls, and no resource state is tracked:
//!   the target is in the render-target state whenever no call is running.
//! - **Buffers are whole upload-heap or readback-heap resources**, mapped for the
//!   length of one copy. A copy starts at the buffer's first byte: Direct3D's
//!   `Map` gives the start, and this crate does no pointer arithmetic, so a
//!   caller that changes part of a buffer writes the whole of it again.
//! - **Shader buffers are bound as root shader resource views** by GPU address,
//!   which carry no length: the shaders bound their own reads
//!   (`crates/clazel-gpu/src/backend.rs`).
//! - **A failure is an error value**, the method's name and its `HRESULT`.
//!   `GetDeviceRemovedReason` is not called.
//!
//! The process is confined by the host before it starts (item 5.21a), so there
//! is nothing here that enters a sandbox.

use std::ffi::c_void;
use std::fmt;
use std::marker::PhantomData;

use crate::d3d12_abi as abi;

#[link(name = "dxgi")]
#[link(name = "d3d12")]
// SAFETY: docs CreateDXGIFactory2 (dxgi, dxgi1_3.h: `HRESULT
// CreateDXGIFactory2(UINT Flags, REFIID riid, void **ppFactory)`); docs
// D3D12CreateDevice (d3d12, d3d12.h: `HRESULT D3D12CreateDevice(IUnknown
// *pAdapter, D3D_FEATURE_LEVEL MinimumFeatureLevel, REFIID riid, void
// **ppDevice)`); docs D3D12SerializeRootSignature (d3d12, d3d12.h: `HRESULT
// D3D12SerializeRootSignature(const D3D12_ROOT_SIGNATURE_DESC *pRootSignature,
// D3D_ROOT_SIGNATURE_VERSION Version, ID3DBlob **ppBlob, ID3DBlob
// **ppErrorBlob)`). The declarations below match those prototypes on 64-bit
// Windows: `UINT` is 32-bit, `HRESULT` and the two enumerations are `i32`,
// `REFIID` is a pointer to a `GUID`, and `ID3DBlob` is `ID3D10Blob`. `system` is
// the Windows calling convention. None is `pub` or declared `safe`, so every
// call needs its own `unsafe` block.
unsafe extern "system" {
    fn CreateDXGIFactory2(flags: u32, iid: *const abi::Guid, factory: *mut *mut c_void) -> i32;
    fn D3D12CreateDevice(
        adapter: *mut abi::IUnknown,
        minimum_feature_level: i32,
        iid: *const abi::Guid,
        device: *mut *mut c_void,
    ) -> i32;
    fn D3D12SerializeRootSignature(
        desc: *const abi::RootSignatureDesc,
        version: i32,
        blob: *mut *mut abi::ID3D10Blob,
        error_blob: *mut *mut abi::ID3D10Blob,
    ) -> i32;
}

// SAFETY: docs C runtime `memcpy` (Microsoft Learn, C runtime library
// reference, "memcpy, wmemcpy": `void *memcpy(void *dest, const void *src,
// size_t count)`), in the C runtime every Rust program on this target links.
// `size_t` is `usize`; `C` is its calling convention. Not `pub`, not `safe`.
unsafe extern "C" {
    fn memcpy(dest: *mut c_void, src: *const c_void, count: usize) -> *mut c_void;
}

/// A call failed: which, and its `HRESULT` (0 for a check made here).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct D3dError {
    /// The function or method, or the check.
    pub what: &'static str,
    /// The `HRESULT`, as a signed number.
    pub code: i64,
}

impl fmt::Display for D3dError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} failed: {:#010x}", self.what, self.code as u32)
    }
}

impl std::error::Error for D3dError {}

fn fail(what: &'static str) -> D3dError {
    D3dError { what, code: 0 }
}

/// `Ok` for a success code (`SUCCEEDED`: not negative).
fn check(hr: i32, what: &'static str) -> Result<(), D3dError> {
    if hr < 0 {
        Err(D3dError {
            what,
            code: i64::from(hr),
        })
    } else {
        Ok(())
    }
}

/// One reference to a COM object, whose interface pointer is a `*mut T`
/// (`T` being one of `crate::d3d12_abi`'s interface types). Released when
/// dropped. Invariant: `ptr` is not null and points to a live object that
/// implements `T`, because the only way to make one is [`Com::adopt`], from the
/// pointer a creation call stored for that interface's identifier.
struct Com<T> {
    ptr: *mut c_void,
    interface: PhantomData<*mut T>,
}

impl<T> Com<T> {
    /// Own the reference a creation call stored in `raw`, which that call
    /// documents as an interface pointer of type `T`. `what` names the call, for
    /// the error if it stored none.
    fn adopt(raw: *mut c_void, what: &'static str) -> Result<Com<T>, D3dError> {
        if raw.is_null() {
            return Err(fail(what));
        }
        Ok(Com {
            ptr: raw,
            interface: PhantomData,
        })
    }

    /// The interface pointer.
    fn get(&self) -> *mut T {
        self.ptr.cast()
    }

    /// The same pointer as an `IUnknown`, which every interface begins with.
    fn unknown(&self) -> *mut abi::IUnknown {
        self.ptr.cast()
    }
}

impl<T> fmt::Debug for Com<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Com({:p})", self.ptr)
    }
}

impl<T> Drop for Com<T> {
    fn drop(&mut self) {
        let this = self.unknown();
        // SAFETY: docs IUnknown::Release: decrements the reference count of the
        // object behind an interface pointer; `IUnknownVtbl::release` is its
        // slot, the third of every COM interface (`unsigned long Release()`,
        // 32-bit on Windows). `this` is live (the invariant of `Com`), this
        // value owns the one reference it gives up, and the pointer is not used
        // again.
        let _ = unsafe { ((**this).release)(this) };
    }
}

/// The DXGI factory: the list of adapters.
#[derive(Debug)]
pub struct Factory {
    factory: Com<abi::IDXGIFactory4>,
}

/// What DXGI says of an adapter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdapterInfo {
    /// The PCI vendor id.
    pub vendor: u32,
    /// The PCI device id.
    pub device: u32,
    /// `DXGI_ADAPTER_FLAG_SOFTWARE`: a software adapter (WARP).
    pub software: bool,
    /// The user-mode driver's version, four 16-bit parts from the most
    /// significant, if `IDXGIAdapter::CheckInterfaceSupport` gave one.
    pub driver: Option<[u16; 4]>,
    /// The adapter's description.
    pub name: String,
}

/// An adapter and what DXGI says of it.
#[derive(Debug)]
pub struct Adapter {
    adapter: Com<abi::IDXGIAdapter1>,
    /// Its description.
    pub info: AdapterInfo,
}

/// The most adapters [`Factory::adapters`] lists.
const MAX_ADAPTERS: u32 = 16;

impl Factory {
    /// The factory.
    pub fn new() -> Result<Factory, D3dError> {
        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_DXGI_FACTORY4;
        // SAFETY: docs CreateDXGIFactory2: `Flags` 0; `riid` points to the
        // identifier of the interface wanted, here the static
        // `IID_DXGI_FACTORY4`; `ppFactory` receives a pointer to that interface
        // on success, and `slot` points to the live local `raw`.
        let hr = unsafe { CreateDXGIFactory2(0, iid, slot) };
        check(hr, "CreateDXGIFactory2")?;
        Ok(Factory {
            factory: Com::adopt(raw, "CreateDXGIFactory2")?,
        })
    }

    /// The adapters, in DXGI's order (at most 16).
    pub fn adapters(&self) -> Result<Vec<Adapter>, D3dError> {
        let this = self.factory.get();
        let mut out = Vec::new();
        for index in 0..MAX_ADAPTERS {
            let mut raw: *mut abi::IDXGIAdapter1 = std::ptr::null_mut();
            let slot: *mut *mut abi::IDXGIAdapter1 = &raw mut raw;
            // SAFETY: docs IDXGIFactory1::EnumAdapters1: stores the adapter at
            // `Adapter` in `ppAdapter` (here `slot`, the live local `raw`) with a
            // reference for the caller, or returns DXGI_ERROR_NOT_FOUND past the
            // last. `this` is the live factory; `enum_adapters1` is that
            // method's slot in `IDXGIFactory4Vtbl`, which inherits it.
            let hr = unsafe { ((**this).enum_adapters1)(this, index, slot) };
            if hr == abi::ERROR_NOT_FOUND {
                break;
            }
            check(hr, "IDXGIFactory1::EnumAdapters1")?;
            let adapter = Com::adopt(raw.cast(), "IDXGIFactory1::EnumAdapters1")?;
            out.push(Adapter::describe(adapter)?);
        }
        Ok(out)
    }

    /// The software adapter, WARP ("Microsoft Basic Render Driver"), which is
    /// part of Windows.
    pub fn warp(&self) -> Result<Adapter, D3dError> {
        let this = self.factory.get();
        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_DXGI_ADAPTER1;
        // SAFETY: docs IDXGIFactory4::EnumWarpAdapter: stores the WARP adapter
        // as the interface `riid` names (the static `IID_DXGI_ADAPTER1`) in
        // `ppvAdapter` (`slot`, the live local `raw`), with a reference for the
        // caller. `this` is the live factory, an `IDXGIFactory4`.
        let hr = unsafe { ((**this).enum_warp_adapter)(this, iid, slot) };
        check(hr, "IDXGIFactory4::EnumWarpAdapter")?;
        Adapter::describe(Com::adopt(raw, "IDXGIFactory4::EnumWarpAdapter")?)
    }
}

impl Adapter {
    /// Read the adapter's description and driver version.
    fn describe(adapter: Com<abi::IDXGIAdapter1>) -> Result<Adapter, D3dError> {
        let this = adapter.get();
        let mut desc = abi::AdapterDesc1 {
            description: [0; 128],
            vendor_id: 0,
            device_id: 0,
            sub_sys_id: 0,
            revision: 0,
            dedicated_video_memory: 0,
            dedicated_system_memory: 0,
            shared_system_memory: 0,
            adapter_luid: abi::Luid {
                low_part: 0,
                high_part: 0,
            },
            flags: 0,
        };
        let desc_slot: *mut abi::AdapterDesc1 = &raw mut desc;
        // SAFETY: docs IDXGIAdapter1::GetDesc1: fills the DXGI_ADAPTER_DESC1 at
        // `pDesc`; `desc_slot` points to the live local `desc`, which is that
        // structure (312 bytes, tested in `d3d12_abi`). `this` is the live
        // adapter.
        let hr = unsafe { ((**this).get_desc1)(this, desc_slot) };
        check(hr, "IDXGIAdapter1::GetDesc1")?;
        let mut version: i64 = 0;
        let version_slot: *mut i64 = &raw mut version;
        let device_iid: *const abi::Guid = &raw const abi::IID_DXGI_DEVICE;
        // SAFETY: docs IDXGIAdapter::CheckInterfaceSupport: says whether the
        // adapter supports the interface `InterfaceName` names (the static
        // `IID_DXGI_DEVICE`) and, if so, stores the user-mode driver's version
        // in the LARGE_INTEGER at `pUMDVersion`, 64 bits; `version_slot` points
        // to the live local `version`. `this` is the live adapter, whose vtable
        // inherits this slot from `IDXGIAdapter`.
        let hr = unsafe { ((**this).check_interface_support)(this, device_iid, version_slot) };
        let driver = (hr >= 0).then(|| {
            let part = |shift: u32| (version >> shift) as u16;
            [part(48), part(32), part(16), part(0)]
        });
        let end = desc
            .description
            .iter()
            .position(|u| *u == 0)
            .unwrap_or(desc.description.len());
        let name = String::from_utf16_lossy(desc.description.get(..end).unwrap_or(&[]));
        Ok(Adapter {
            adapter,
            info: AdapterInfo {
                vendor: desc.vendor_id,
                device: desc.device_id,
                software: desc.flags & abi::ADAPTER_FLAG_SOFTWARE != 0,
                driver,
                name,
            },
        })
    }

    /// A device on this adapter at feature level 11.0, with its command queue,
    /// one allocator, one command list (closed) and a fence.
    pub fn open(&self) -> Result<Device, D3dError> {
        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let adapter = self.adapter.unknown();
        let iid: *const abi::Guid = &raw const abi::IID_DEVICE;
        // SAFETY: docs D3D12CreateDevice: `pAdapter` is a live adapter (an
        // `IDXGIAdapter1` is an `IUnknown`), the feature level is
        // D3D_FEATURE_LEVEL_11_0, `riid` points to the static `IID_DEVICE`
        // (`ID3D12Device`), and `ppDevice` receives that interface with a
        // reference for the caller; `slot` points to the live local `raw`.
        let hr = unsafe { D3D12CreateDevice(adapter, abi::FEATURE_LEVEL_11_0, iid, slot) };
        check(hr, "D3D12CreateDevice")?;
        let device: Com<abi::ID3D12Device> = Com::adopt(raw, "D3D12CreateDevice")?;
        let this = device.get();

        let queue_desc = abi::CommandQueueDesc {
            kind: abi::COMMAND_LIST_TYPE_DIRECT,
            priority: 0,
            flags: 0,
            node_mask: 0,
        };
        let queue_desc_ptr: *const abi::CommandQueueDesc = &raw const queue_desc;
        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_COMMAND_QUEUE;
        // SAFETY: docs ID3D12Device::CreateCommandQueue: reads the
        // D3D12_COMMAND_QUEUE_DESC at `pDesc` (the live local `queue_desc`: a
        // direct queue, normal priority, no flags, node 0) and stores the queue
        // as `riid` names it (the static `IID_COMMAND_QUEUE`) in `slot`, the
        // live local `raw`. `this` is the live device.
        let hr = unsafe { ((**this).create_command_queue)(this, queue_desc_ptr, iid, slot) };
        check(hr, "ID3D12Device::CreateCommandQueue")?;
        let queue: Com<abi::ID3D12CommandQueue> =
            Com::adopt(raw, "ID3D12Device::CreateCommandQueue")?;

        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_COMMAND_ALLOCATOR;
        // SAFETY: docs ID3D12Device::CreateCommandAllocator: makes an allocator
        // for command lists of `type` (direct) and stores it as `riid` names it
        // (the static `IID_COMMAND_ALLOCATOR`) in `slot`, the live local `raw`.
        // `this` is the live device.
        let hr = unsafe {
            ((**this).create_command_allocator)(this, abi::COMMAND_LIST_TYPE_DIRECT, iid, slot)
        };
        check(hr, "ID3D12Device::CreateCommandAllocator")?;
        let allocator: Com<abi::ID3D12CommandAllocator> =
            Com::adopt(raw, "ID3D12Device::CreateCommandAllocator")?;

        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_GRAPHICS_COMMAND_LIST;
        let allocator_ptr = allocator.get();
        let no_state: *mut abi::IUnknown = std::ptr::null_mut();
        // SAFETY: docs ID3D12Device::CreateCommandList: makes a command list of
        // `type` (direct) for node 0 on `pCommandAllocator` (the live allocator
        // made above, of the same type), with no initial pipeline state
        // (`pInitialState` is optional and NULL), and stores it as `riid` names
        // it (the static `IID_GRAPHICS_COMMAND_LIST`) in `slot`, the live local
        // `raw`. `this` is the live device.
        let hr = unsafe {
            ((**this).create_command_list)(
                this,
                0,
                abi::COMMAND_LIST_TYPE_DIRECT,
                allocator_ptr,
                no_state,
                iid,
                slot,
            )
        };
        check(hr, "ID3D12Device::CreateCommandList")?;
        let list: Com<abi::ID3D12GraphicsCommandList> =
            Com::adopt(raw, "ID3D12Device::CreateCommandList")?;
        let list_ptr = list.get();
        // SAFETY: docs ID3D12GraphicsCommandList::Close: ends recording. A new
        // list is created recording, and every use below begins with `Reset`,
        // which needs a closed list. `list_ptr` is the live list.
        let hr = unsafe { ((**list_ptr).close)(list_ptr) };
        check(hr, "ID3D12GraphicsCommandList::Close")?;

        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_FENCE;
        // SAFETY: docs ID3D12Device::CreateFence: makes a fence with the initial
        // value 0 and no flags and stores it as `riid` names it (the static
        // `IID_FENCE`) in `slot`, the live local `raw`. `this` is the live
        // device.
        let hr = unsafe { ((**this).create_fence)(this, 0, abi::FENCE_FLAG_NONE, iid, slot) };
        check(hr, "ID3D12Device::CreateFence")?;
        let fence: Com<abi::ID3D12Fence> = Com::adopt(raw, "ID3D12Device::CreateFence")?;

        Ok(Device {
            fence,
            fence_value: 0,
            list,
            allocator,
            queue,
            device,
        })
    }
}

/// A device, its queue and the one command list everything is recorded on.
/// The fields are dropped in order, the device last.
#[derive(Debug)]
pub struct Device {
    fence: Com<abi::ID3D12Fence>,
    /// The last value the queue was told to signal.
    fence_value: u64,
    list: Com<abi::ID3D12GraphicsCommandList>,
    allocator: Com<abi::ID3D12CommandAllocator>,
    queue: Com<abi::ID3D12CommandQueue>,
    device: Com<abi::ID3D12Device>,
}

/// What a buffer is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BufferUse {
    /// Written by the CPU and read by the shaders (an upload heap).
    Shader,
    /// Written by a copy from the target and read by the CPU (a readback heap).
    Readback,
}

/// A buffer of `len` bytes in memory the CPU can map.
#[derive(Debug)]
pub struct Buffer {
    resource: Com<abi::ID3D12Resource>,
    len: usize,
    usage: BufferUse,
}

/// The largest buffer: 1 GiB, far over what a frame needs.
const MAX_BUFFER: usize = 1 << 30;

impl Device {
    /// A buffer of `len` bytes (at least 1), contents undefined.
    pub fn new_buffer(&self, len: usize, usage: BufferUse) -> Result<Buffer, D3dError> {
        if len == 0 || len > MAX_BUFFER {
            return Err(fail("buffer length"));
        }
        let (heap_kind, state) = match usage {
            BufferUse::Shader => (abi::HEAP_TYPE_UPLOAD, abi::RESOURCE_STATE_GENERIC_READ),
            BufferUse::Readback => (abi::HEAP_TYPE_READBACK, abi::RESOURCE_STATE_COPY_DEST),
        };
        let desc = abi::ResourceDesc {
            dimension: abi::RESOURCE_DIMENSION_BUFFER,
            alignment: 0,
            width: len as u64,
            height: 1,
            depth_or_array_size: 1,
            mip_levels: 1,
            format: abi::FORMAT_UNKNOWN,
            sample_desc: abi::SampleDesc {
                count: 1,
                quality: 0,
            },
            layout: abi::TEXTURE_LAYOUT_ROW_MAJOR,
            flags: 0,
        };
        let resource = self.committed(heap_kind, &desc, state)?;
        Ok(Buffer {
            resource,
            len,
            usage,
        })
    }

    /// `ID3D12Device::CreateCommittedResource`: a resource and its own heap of
    /// `heap_kind`, in `state`.
    fn committed(
        &self,
        heap_kind: i32,
        desc: &abi::ResourceDesc,
        state: i32,
    ) -> Result<Com<abi::ID3D12Resource>, D3dError> {
        let this = self.device.get();
        let heap = abi::HeapProperties {
            kind: heap_kind,
            cpu_page_property: 0,
            memory_pool_preference: 0,
            creation_node_mask: 0,
            visible_node_mask: 0,
        };
        let heap_ptr: *const abi::HeapProperties = &raw const heap;
        let desc_ptr: *const abi::ResourceDesc = desc;
        let no_clear: *const c_void = std::ptr::null();
        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_RESOURCE;
        // SAFETY: docs ID3D12Device::CreateCommittedResource: reads the
        // D3D12_HEAP_PROPERTIES at `pHeapProperties` (the live local `heap`: a
        // heap type, the other fields 0, which mean unknown page property and
        // pool and node 0) and the D3D12_RESOURCE_DESC at `pDesc` (the caller's
        // live `desc`), with no heap flags, the initial state `state`, no
        // optimized clear value (optional, NULL), and stores the resource as
        // `riidResource` names it (the static `IID_RESOURCE`) in `slot`, the
        // live local `raw`. `this` is the live device.
        let hr = unsafe {
            ((**this).create_committed_resource)(
                this,
                heap_ptr,
                abi::HEAP_FLAG_NONE,
                desc_ptr,
                state,
                no_clear,
                iid,
                slot,
            )
        };
        check(hr, "ID3D12Device::CreateCommittedResource")?;
        Com::adopt(raw, "ID3D12Device::CreateCommittedResource")
    }
}

impl Buffer {
    /// Its length in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Never: a buffer has at least one byte.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Map the whole buffer; the pointer to its first byte. `read` says whether
    /// the CPU will read it.
    fn map(&self, read: bool) -> Result<*mut c_void, D3dError> {
        let this = self.resource.get();
        let range = abi::Range {
            begin: 0,
            end: if read { self.len } else { 0 },
        };
        let range_ptr: *const abi::Range = &raw const range;
        let mut data: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut data;
        // SAFETY: docs ID3D12Resource::Map: maps subresource 0 (a buffer has
        // one) and stores a pointer to its first byte in `ppData` (`slot`, the
        // live local `data`); `pReadRange` (the live local `range`) is the range
        // the CPU may read, empty (`End <= Begin`) when it will only write.
        // `this` is the live resource, made in an upload or readback heap, the
        // two kinds that can be mapped.
        let hr = unsafe { ((**this).map)(this, 0, range_ptr, slot) };
        check(hr, "ID3D12Resource::Map")?;
        if data.is_null() {
            return Err(fail("ID3D12Resource::Map"));
        }
        Ok(data)
    }

    /// End the mapping [`Buffer::map`] began; `written` says whether the CPU
    /// wrote it.
    fn unmap(&self, written: bool) {
        let this = self.resource.get();
        let range = abi::Range {
            begin: 0,
            end: if written { self.len } else { 0 },
        };
        let range_ptr: *const abi::Range = &raw const range;
        // SAFETY: docs ID3D12Resource::Unmap: ends the mapping of subresource 0
        // made by `Map`; `pWrittenRange` (the live local `range`) is the range
        // the CPU wrote, empty when it wrote nothing. `this` is the live
        // resource, mapped once by the caller, and the pointer `Map` gave is not
        // used after this.
        unsafe { ((**this).unmap)(this, 0, range_ptr) };
    }

    /// Copy `bytes` to the start of a [`BufferUse::Shader`] buffer. They must
    /// fit.
    pub fn write(&self, bytes: &[u8]) -> Result<(), D3dError> {
        if self.usage != BufferUse::Shader || bytes.len() > self.len {
            return Err(fail("buffer write"));
        }
        if bytes.is_empty() {
            return Ok(());
        }
        let dst = self.map(false)?;
        let src: *const c_void = bytes.as_ptr().cast();
        let len = bytes.len();
        // SAFETY: docs C runtime `memcpy`: copies `count` bytes from `src` to
        // `dest`, which must not overlap. `dst` is the start of the mapped
        // buffer, `self.len` bytes long, and `len` is at most that (checked
        // above); `src` is the caller's slice of `len` bytes, in Rust's memory,
        // which cannot overlap a mapped resource.
        let _ = unsafe { memcpy(dst, src, len) };
        self.unmap(true);
        Ok(())
    }

    /// Copy the first `out.len()` bytes of a [`BufferUse::Readback`] buffer into
    /// `out`. It must not be longer than the buffer.
    pub fn read(&self, out: &mut [u8]) -> Result<(), D3dError> {
        if self.usage != BufferUse::Readback || out.len() > self.len {
            return Err(fail("buffer read"));
        }
        if out.is_empty() {
            return Ok(());
        }
        let src: *const c_void = self.map(true)?;
        let dst: *mut c_void = out.as_mut_ptr().cast();
        let len = out.len();
        // SAFETY: docs C runtime `memcpy`: as in `write`, the other way: `src`
        // is the start of the mapped buffer, `self.len` bytes long, `len` is at
        // most that (checked above), and `dst` is the caller's slice of `len`
        // bytes, which cannot overlap a mapped resource.
        let _ = unsafe { memcpy(dst, src, len) };
        self.unmap(false);
        Ok(())
    }

    /// The buffer's address on the GPU.
    fn address(&self) -> u64 {
        let this = self.resource.get();
        // SAFETY: docs ID3D12Resource::GetGPUVirtualAddress: returns the GPU
        // virtual address of a buffer resource; it takes only the interface
        // pointer. `this` is the live resource, a buffer.
        unsafe { ((**this).get_gpu_virtual_address)(this) }
    }
}

/// A blend factor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlendFactor {
    /// `D3D12_BLEND_ONE`.
    One,
    /// `D3D12_BLEND_INV_SRC_ALPHA`.
    OneMinusSourceAlpha,
}

impl BlendFactor {
    fn raw(self) -> i32 {
        match self {
            BlendFactor::One => abi::BLEND_ONE,
            BlendFactor::OneMinusSourceAlpha => abi::BLEND_INV_SRC_ALPHA,
        }
    }
}

/// What a pipeline is made from.
#[derive(Debug, Clone, Copy)]
pub struct PipelineDesc<'a> {
    /// The vertex shader's bytecode (a DXBC container).
    pub vertex: &'a [u8],
    /// The pixel shader's bytecode.
    pub fragment: &'a [u8],
    /// The colour and alpha blend, source then destination factor, added; or no
    /// blending.
    pub blend: Option<(BlendFactor, BlendFactor)>,
    /// How many 32-bit constants the shaders read at register `b0` (1 to 64).
    pub constants: u32,
    /// How many buffers the shaders read, at registers `t0`, `t1` and so on (at
    /// most 8).
    pub buffers: u32,
}

/// A pipeline state and its root signature: parameter 0 is the constants,
/// parameter `1 + i` is buffer `i`. It draws triangle lists with no vertex
/// buffer into one RGBA8 target, with no depth, stencil or culling.
#[derive(Debug)]
pub struct Pipeline {
    state: Com<abi::IUnknown>,
    signature: Com<abi::IUnknown>,
    constants: u32,
    buffers: u32,
}

impl Device {
    /// The root signature `desc` describes, serialized by Direct3D and made.
    fn root_signature(&self, desc: &PipelineDesc<'_>) -> Result<Com<abi::IUnknown>, D3dError> {
        let parameter = |kind: i32, register: u32, values: u32| abi::RootParameter {
            kind,
            padding: 0,
            shader_register: register,
            register_space: 0,
            num_32bit_values: values,
            rest_of_union: 0,
            shader_visibility: abi::SHADER_VISIBILITY_ALL,
            padding_after: 0,
        };
        let mut parameters = vec![parameter(
            abi::ROOT_PARAMETER_TYPE_32BIT_CONSTANTS,
            0,
            desc.constants,
        )];
        for register in 0..desc.buffers {
            parameters.push(parameter(abi::ROOT_PARAMETER_TYPE_SRV, register, 0));
        }
        let signature_desc = abi::RootSignatureDesc {
            num_parameters: desc.buffers.saturating_add(1),
            parameters: parameters.as_ptr(),
            num_static_samplers: 0,
            static_samplers: std::ptr::null(),
            flags: 0,
        };
        let desc_ptr: *const abi::RootSignatureDesc = &raw const signature_desc;
        let mut blob_raw: *mut abi::ID3D10Blob = std::ptr::null_mut();
        let blob_slot: *mut *mut abi::ID3D10Blob = &raw mut blob_raw;
        let mut error_raw: *mut abi::ID3D10Blob = std::ptr::null_mut();
        let error_slot: *mut *mut abi::ID3D10Blob = &raw mut error_raw;
        // SAFETY: docs D3D12SerializeRootSignature: reads the
        // D3D12_ROOT_SIGNATURE_DESC at `pRootSignature` (the live local
        // `signature_desc`), whose `pParameters` points to `NumParameters`
        // D3D12_ROOT_PARAMETERs (`parameters`, a live `Vec` of exactly that
        // many, one constants parameter and `buffers` descriptor parameters)
        // and which has no static samplers, at version 1; it stores a blob in
        // `ppBlob` on success and may store an error blob in `ppErrorBlob` on
        // failure, each with a reference for the caller. The two slots point to
        // the live locals `blob_raw` and `error_raw`.
        let hr = unsafe {
            D3D12SerializeRootSignature(
                desc_ptr,
                abi::ROOT_SIGNATURE_VERSION_1,
                blob_slot,
                error_slot,
            )
        };
        // Whichever blobs were stored are owned from here, so that both are
        // released on every path.
        let error: Option<Com<abi::ID3D10Blob>> =
            Com::adopt(error_raw.cast(), "D3D12SerializeRootSignature").ok();
        let blob: Result<Com<abi::ID3D10Blob>, D3dError> =
            Com::adopt(blob_raw.cast(), "D3D12SerializeRootSignature");
        drop(error);
        check(hr, "D3D12SerializeRootSignature")?;
        let blob = blob?;
        let blob_ptr = blob.get();
        // SAFETY: docs ID3D10Blob::GetBufferPointer: returns a pointer to the
        // blob's data; it takes only the interface pointer. `blob_ptr` is the
        // live blob, which outlives the use of the pointer below.
        let data: *const c_void = unsafe { ((**blob_ptr).get_buffer_pointer)(blob_ptr) };
        // SAFETY: docs ID3D10Blob::GetBufferSize: returns the size of the
        // blob's data in bytes; it takes only the interface pointer. `blob_ptr`
        // is the live blob.
        let size = unsafe { ((**blob_ptr).get_buffer_size)(blob_ptr) };
        let this = self.device.get();
        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_ROOT_SIGNATURE;
        // SAFETY: docs ID3D12Device::CreateRootSignature: reads
        // `blobLengthInBytes` bytes of a serialized root signature at
        // `pBlobWithRootSignature`, here the data and size the live `blob` just
        // gave, for node 0, and stores the root signature as `riid` names it
        // (the static `IID_ROOT_SIGNATURE`) in `slot`, the live local `raw`.
        // `this` is the live device.
        let hr = unsafe { ((**this).create_root_signature)(this, 0, data, size, iid, slot) };
        check(hr, "ID3D12Device::CreateRootSignature")?;
        Com::adopt(raw, "ID3D12Device::CreateRootSignature")
    }

    /// The pipeline `desc` describes.
    pub fn new_pipeline(&self, desc: &PipelineDesc<'_>) -> Result<Pipeline, D3dError> {
        if desc.vertex.is_empty()
            || desc.fragment.is_empty()
            || desc.constants == 0
            || desc.constants > 64
            || desc.buffers > 8
        {
            return Err(fail("pipeline description"));
        }
        let signature = self.root_signature(desc)?;
        let bytecode = |b: &[u8]| abi::ShaderBytecode {
            shader_bytecode: b.as_ptr().cast(),
            bytecode_length: b.len(),
        };
        let none = abi::ShaderBytecode {
            shader_bytecode: std::ptr::null(),
            bytecode_length: 0,
        };
        let (source, destination) = desc
            .blend
            .map_or((abi::BLEND_ONE, abi::BLEND_ZERO), |(s, d)| {
                (s.raw(), d.raw())
            });
        let target_blend = abi::RenderTargetBlendDesc {
            blend_enable: i32::from(desc.blend.is_some()),
            logic_op_enable: 0,
            src_blend: source,
            dest_blend: destination,
            blend_op: abi::BLEND_OP_ADD,
            src_blend_alpha: source,
            dest_blend_alpha: destination,
            blend_op_alpha: abi::BLEND_OP_ADD,
            logic_op: abi::LOGIC_OP_NOOP,
            render_target_write_mask: abi::COLOR_WRITE_ENABLE_ALL,
        };
        let stencil = abi::DepthStencilOpDesc {
            stencil_fail_op: abi::STENCIL_OP_KEEP,
            stencil_depth_fail_op: abi::STENCIL_OP_KEEP,
            stencil_pass_op: abi::STENCIL_OP_KEEP,
            stencil_func: abi::COMPARISON_FUNC_ALWAYS,
        };
        let state_desc = abi::GraphicsPipelineStateDesc {
            root_signature: signature.get(),
            vs: bytecode(desc.vertex),
            ps: bytecode(desc.fragment),
            ds: none,
            hs: none,
            gs: none,
            stream_output: abi::StreamOutputDesc {
                declaration: std::ptr::null(),
                num_entries: 0,
                buffer_strides: std::ptr::null(),
                num_strides: 0,
                rasterized_stream: 0,
            },
            blend_state: abi::BlendDesc {
                alpha_to_coverage_enable: 0,
                independent_blend_enable: 0,
                render_target: [target_blend; 8],
            },
            sample_mask: abi::DEFAULT_SAMPLE_MASK,
            rasterizer_state: abi::RasterizerDesc {
                fill_mode: abi::FILL_MODE_SOLID,
                cull_mode: abi::CULL_MODE_NONE,
                front_counter_clockwise: 0,
                depth_bias: 0,
                depth_bias_clamp: 0.0,
                slope_scaled_depth_bias: 0.0,
                depth_clip_enable: 1,
                multisample_enable: 0,
                antialiased_line_enable: 0,
                forced_sample_count: 0,
                conservative_raster: 0,
            },
            depth_stencil_state: abi::DepthStencilDesc {
                depth_enable: 0,
                depth_write_mask: abi::DEPTH_WRITE_MASK_ZERO,
                depth_func: abi::COMPARISON_FUNC_ALWAYS,
                stencil_enable: 0,
                stencil_read_mask: 0,
                stencil_write_mask: 0,
                front_face: stencil,
                back_face: stencil,
            },
            input_layout: abi::InputLayoutDesc {
                input_element_descs: std::ptr::null(),
                num_elements: 0,
            },
            ib_strip_cut_value: 0,
            primitive_topology_type: abi::PRIMITIVE_TOPOLOGY_TYPE_TRIANGLE,
            num_render_targets: 1,
            rtv_formats: [abi::FORMAT_R8G8B8A8_UNORM, 0, 0, 0, 0, 0, 0, 0],
            dsv_format: abi::FORMAT_UNKNOWN,
            sample_desc: abi::SampleDesc {
                count: 1,
                quality: 0,
            },
            node_mask: 0,
            cached_pso: abi::CachedPipelineState {
                cached_blob: std::ptr::null(),
                cached_blob_size_in_bytes: 0,
            },
            flags: 0,
        };
        let this = self.device.get();
        let desc_ptr: *const abi::GraphicsPipelineStateDesc = &raw const state_desc;
        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_PIPELINE_STATE;
        // SAFETY: docs ID3D12Device::CreateGraphicsPipelineState: reads the
        // D3D12_GRAPHICS_PIPELINE_STATE_DESC at `pDesc` (the live local
        // `state_desc`, 656 bytes, tested in `d3d12_abi`). Its pointers are:
        // the live root signature made above; the vertex and pixel bytecode,
        // each the caller's live slice with its own length; and NULL with a
        // length or count of 0 for the three unused shaders, the stream output,
        // the input layout and the cached blob. It stores the pipeline state as
        // `riid` names it (the static `IID_PIPELINE_STATE`) in `slot`, the live
        // local `raw`, and keeps none of those pointers but the root
        // signature's, which it references itself. `this` is the live device.
        let hr = unsafe { ((**this).create_graphics_pipeline_state)(this, desc_ptr, iid, slot) };
        check(hr, "ID3D12Device::CreateGraphicsPipelineState")?;
        Ok(Pipeline {
            state: Com::adopt(raw, "ID3D12Device::CreateGraphicsPipelineState")?,
            signature,
            constants: desc.constants,
            buffers: desc.buffers,
        })
    }
}

/// An RGBA8 texture to draw into, and its render target view.
#[derive(Debug)]
pub struct Target {
    view: abi::CpuDescriptorHandle,
    /// Held so that `view`, a place in it, stays valid.
    _heap: Com<abi::ID3D12DescriptorHeap>,
    texture: Com<abi::ID3D12Resource>,
    width: u32,
    height: u32,
}

impl Target {
    /// Its width in pixels.
    pub fn width(&self) -> u32 {
        self.width
    }

    /// Its height in pixels.
    pub fn height(&self) -> u32 {
        self.height
    }

    /// The bytes from one row to the next in the buffer [`Device::copy_target`]
    /// fills: the row's `4 * width`, rounded up to a multiple of
    /// `D3D12_TEXTURE_DATA_PITCH_ALIGNMENT` (256).
    pub fn row_pitch(&self) -> u32 {
        // At most 4 * 16384, so nothing here can overflow.
        self.width
            .saturating_mul(4)
            .div_ceil(abi::TEXTURE_DATA_PITCH_ALIGNMENT)
            .saturating_mul(abi::TEXTURE_DATA_PITCH_ALIGNMENT)
    }

    /// The length of the buffer [`Device::copy_target`] needs: `height` rows of
    /// [`Target::row_pitch`] bytes.
    pub fn copy_len(&self) -> usize {
        (self.row_pitch() as usize).saturating_mul(self.height as usize)
    }
}

impl Device {
    /// A target of `width` by `height` pixels, each 1 to 16384, contents
    /// undefined, in the render-target state.
    pub fn new_target(&self, width: u32, height: u32) -> Result<Target, D3dError> {
        let max = abi::REQ_TEXTURE2D_U_OR_V_DIMENSION;
        if width == 0 || height == 0 || width > max || height > max {
            return Err(fail("target size"));
        }
        let desc = abi::ResourceDesc {
            dimension: abi::RESOURCE_DIMENSION_TEXTURE2D,
            alignment: 0,
            width: u64::from(width),
            height,
            depth_or_array_size: 1,
            mip_levels: 1,
            format: abi::FORMAT_R8G8B8A8_UNORM,
            sample_desc: abi::SampleDesc {
                count: 1,
                quality: 0,
            },
            layout: abi::TEXTURE_LAYOUT_UNKNOWN,
            flags: abi::RESOURCE_FLAG_ALLOW_RENDER_TARGET,
        };
        let texture = self.committed(
            abi::HEAP_TYPE_DEFAULT,
            &desc,
            abi::RESOURCE_STATE_RENDER_TARGET,
        )?;
        let this = self.device.get();
        let heap_desc = abi::DescriptorHeapDesc {
            kind: abi::DESCRIPTOR_HEAP_TYPE_RTV,
            num_descriptors: 1,
            flags: 0,
            node_mask: 0,
        };
        let heap_desc_ptr: *const abi::DescriptorHeapDesc = &raw const heap_desc;
        let mut raw: *mut c_void = std::ptr::null_mut();
        let slot: *mut *mut c_void = &raw mut raw;
        let iid: *const abi::Guid = &raw const abi::IID_DESCRIPTOR_HEAP;
        // SAFETY: docs ID3D12Device::CreateDescriptorHeap: reads the
        // D3D12_DESCRIPTOR_HEAP_DESC at `pDescriptorHeapDesc` (the live local
        // `heap_desc`: one render target view descriptor, no flags, node 0) and
        // stores the heap as `riid` names it (the static `IID_DESCRIPTOR_HEAP`)
        // in `slot`, the live local `raw`. `this` is the live device.
        let hr = unsafe { ((**this).create_descriptor_heap)(this, heap_desc_ptr, iid, slot) };
        check(hr, "ID3D12Device::CreateDescriptorHeap")?;
        let heap: Com<abi::ID3D12DescriptorHeap> =
            Com::adopt(raw, "ID3D12Device::CreateDescriptorHeap")?;
        let start = heap.get();
        let mut view = abi::CpuDescriptorHandle { ptr: 0 };
        let slot: *mut abi::CpuDescriptorHandle = &raw mut view;
        // SAFETY: docs ID3D12DescriptorHeap::GetCPUDescriptorHandleForHeapStart:
        // gives the CPU handle of the heap's first descriptor. The method
        // returns a structure, which on Windows it writes through a pointer
        // passed after `this` and returns that pointer (`d3d12.h`, the `#else`
        // of `#if !defined(_WIN32)`); `slot` points to the live local `view`.
        // `start` is the live heap.
        let _ = unsafe { ((**start).get_cpu_descriptor_handle_for_heap_start)(start, slot) };
        if view.ptr == 0 {
            return Err(fail(
                "ID3D12DescriptorHeap::GetCPUDescriptorHandleForHeapStart",
            ));
        }
        let texture_ptr = texture.get();
        let default_view: *const c_void = std::ptr::null();
        // SAFETY: docs ID3D12Device::CreateRenderTargetView: writes a render
        // target view of `pResource` (the live texture, made with
        // ALLOW_RENDER_TARGET) to the descriptor `DestDescriptor`, the first of
        // the live heap made above, which holds one; `pDesc` is optional and
        // NULL, the view of the whole texture in its own format. `this` is the
        // live device.
        unsafe { ((**this).create_render_target_view)(this, texture_ptr, default_view, view) };
        Ok(Target {
            view,
            _heap: heap,
            texture,
            width,
            height,
        })
    }
}

/// One draw: a scissor rectangle, a constant to change first, and instances.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Draw {
    /// The scissor rectangle: left, top, width, height, in pixels.
    pub scissor: (u32, u32, u32, u32),
    /// Vertices per instance.
    pub vertices: u32,
    /// How many instances; the shaders see instance numbers from 0.
    pub instances: u32,
    /// Before drawing, set the 32-bit constant at this index to this value.
    pub constant: Option<(u32, u32)>,
}

/// A scissor rectangle as `D3D12_RECT`, if its edges fit in `i32`.
fn scissor_rect((x, y, w, h): (u32, u32, u32, u32)) -> Option<abi::Rect> {
    Some(abi::Rect {
        left: i32::try_from(x).ok()?,
        top: i32::try_from(y).ok()?,
        right: i32::try_from(x.checked_add(w)?).ok()?,
        bottom: i32::try_from(y.checked_add(h)?).ok()?,
    })
}

impl Device {
    /// Begin recording on the one list, with `state` as its pipeline state (or
    /// none). Nothing is in flight: every submission was waited for.
    fn begin(&self, state: *mut abi::IUnknown) -> Result<(), D3dError> {
        let allocator = self.allocator.get();
        // SAFETY: docs ID3D12CommandAllocator::Reset: frees the memory of the
        // lists recorded on it, which must have finished executing; every
        // submission is waited for in `submit`, so none is running. `allocator`
        // is the live allocator.
        let hr = unsafe { ((**allocator).reset)(allocator) };
        check(hr, "ID3D12CommandAllocator::Reset")?;
        let list = self.list.get();
        // SAFETY: docs ID3D12GraphicsCommandList::Reset: begins recording again
        // on `pAllocator` (the live allocator, just reset, of the list's type)
        // with `pInitialState` as the pipeline state, which is optional: `state`
        // is NULL or a live pipeline state the caller holds for this call. The
        // list is closed: `open` closed it and `submit` closes it after every
        // recording. `list` is the live list.
        let hr = unsafe { ((**list).reset)(list, allocator, state) };
        check(hr, "ID3D12GraphicsCommandList::Reset")
    }

    /// Close the list, execute it and wait until the GPU has finished it.
    fn submit(&mut self) -> Result<(), D3dError> {
        let list = self.list.get();
        // SAFETY: docs ID3D12GraphicsCommandList::Close: ends recording;
        // `begin` started it. `list` is the live list.
        let hr = unsafe { ((**list).close)(list) };
        check(hr, "ID3D12GraphicsCommandList::Close")?;
        let queue = self.queue.get();
        let lists: [*mut abi::ID3D12GraphicsCommandList; 1] = [list];
        let lists_ptr = lists.as_ptr();
        // SAFETY: docs ID3D12CommandQueue::ExecuteCommandLists: submits the
        // `NumCommandLists` closed lists at `ppCommandLists`; `lists_ptr`
        // points to the live local array of one, the list closed above, of the
        // queue's type (an `ID3D12GraphicsCommandList` is an
        // `ID3D12CommandList`). `queue` is the live queue.
        unsafe { ((**queue).execute_command_lists)(queue, 1, lists_ptr) };
        let value = self.fence_value.checked_add(1).ok_or(fail("fence value"))?;
        self.fence_value = value;
        let fence = self.fence.get();
        // SAFETY: docs ID3D12CommandQueue::Signal: sets `pFence` (the live
        // fence) to `Value` once the queue has run everything submitted before
        // this call. `queue` is the live queue.
        let hr = unsafe { ((**queue).signal)(queue, fence, value) };
        check(hr, "ID3D12CommandQueue::Signal")?;
        // SAFETY: docs ID3D12Fence::SetEventOnCompletion: with a null event
        // handle it does not return until the fence has reached `Value`, here
        // the value just asked of the queue. `fence` is the live fence.
        let hr = unsafe { ((**fence).set_event_on_completion)(fence, value, 0) };
        check(hr, "ID3D12Fence::SetEventOnCompletion")
    }

    /// Draw into `target` with `pipeline` and wait for it: clear to transparent
    /// black first if `clear`, set the constants to `constants` (as many as the
    /// pipeline has), bind `buffers` (as many as it has, each a
    /// [`BufferUse::Shader`] buffer), then each draw in order.
    pub fn render(
        &mut self,
        pipeline: &Pipeline,
        target: &Target,
        clear: bool,
        constants: &[u32],
        buffers: &[&Buffer],
        draws: &[Draw],
    ) -> Result<(), D3dError> {
        // Everything is checked before recording begins, so that no path
        // leaves the list open.
        if u32::try_from(constants.len()).ok() != Some(pipeline.constants)
            || u32::try_from(buffers.len()).ok() != Some(pipeline.buffers)
            || buffers.iter().any(|b| b.usage != BufferUse::Shader)
        {
            return Err(fail("render arguments"));
        }
        let mut rects = Vec::with_capacity(draws.len());
        for draw in draws {
            rects.push(scissor_rect(draw.scissor).ok_or(fail("scissor"))?);
            if draw
                .constant
                .is_some_and(|(index, _)| index >= pipeline.constants)
            {
                return Err(fail("constant index"));
            }
        }
        self.begin(pipeline.state.get())?;
        let list = self.list.get();
        let signature = pipeline.signature.get();
        // SAFETY: docs ID3D12GraphicsCommandList::SetGraphicsRootSignature:
        // sets the layout of the graphics root arguments; `signature` is the
        // live root signature the pipeline state was made with, held by
        // `pipeline` for this call. `list` is the live list, recording.
        unsafe { ((**list).set_graphics_root_signature)(list, signature) };
        let viewport = abi::Viewport {
            top_left_x: 0.0,
            top_left_y: 0.0,
            width: target.width as f32,
            height: target.height as f32,
            min_depth: 0.0,
            max_depth: 1.0,
        };
        let viewport_ptr: *const abi::Viewport = &raw const viewport;
        // SAFETY: docs ID3D12GraphicsCommandList::RSSetViewports: reads
        // `NumViewports` D3D12_VIEWPORTs at `pViewports`; `viewport_ptr` points
        // to the live local `viewport`, one. `list` is the live list,
        // recording.
        unsafe { ((**list).rs_set_viewports)(list, 1, viewport_ptr) };
        let view_ptr: *const abi::CpuDescriptorHandle = &raw const target.view;
        let no_depth: *const abi::CpuDescriptorHandle = std::ptr::null();
        // SAFETY: docs ID3D12GraphicsCommandList::OMSetRenderTargets: reads
        // `NumRenderTargetDescriptors` handles at `pRenderTargetDescriptors`
        // (`view_ptr`, the one handle of the live `target`, whose heap and
        // texture it holds); `RTsSingleHandleToDescriptorRange` is FALSE and the
        // depth stencil descriptor is optional and NULL. `list` is the live
        // list, recording.
        unsafe { ((**list).om_set_render_targets)(list, 1, view_ptr, 0, no_depth) };
        if clear {
            let colour = [0.0f32; 4];
            let colour_ptr: *const [f32; 4] = &raw const colour;
            let no_rects: *const abi::Rect = std::ptr::null();
            // SAFETY: docs ID3D12GraphicsCommandList::ClearRenderTargetView:
            // sets every pixel of the view `RenderTargetView` (the live
            // target's, in the render-target state) to the four floats at
            // `ColorRGBA` (the live local `colour`); `NumRects` is 0 and
            // `pRects` NULL, the whole view. `list` is the live list, recording.
            unsafe {
                ((**list).clear_render_target_view)(list, target.view, colour_ptr, 0, no_rects)
            };
        }
        // SAFETY: docs ID3D12GraphicsCommandList::IASetPrimitiveTopology: sets
        // how vertices become primitives, here
        // D3D_PRIMITIVE_TOPOLOGY_TRIANGLELIST, which matches the pipeline's
        // topology type. `list` is the live list, recording.
        unsafe { ((**list).ia_set_primitive_topology)(list, abi::TOPOLOGY_TRIANGLE_LIST) };
        let constants_ptr: *const c_void = constants.as_ptr().cast();
        // SAFETY: docs ID3D12GraphicsCommandList::SetGraphicsRoot32BitConstants:
        // copies `Num32BitValuesToSet` 32-bit values from `pSrcData` into root
        // parameter `RootParameterIndex` from offset `DestOffsetIn32BitValues`.
        // Parameter 0 is the pipeline's constants, `pipeline.constants` of
        // them, and `constants` is a live slice of exactly that many `u32`s
        // (checked above), copied whole from offset 0. `list` is the live list,
        // recording, with that root signature set.
        unsafe {
            ((**list).set_graphics_root32_bit_constants)(
                list,
                0,
                pipeline.constants,
                constants_ptr,
                0,
            )
        };
        for (parameter, buffer) in (1u32..).zip(buffers) {
            let address = buffer.address();
            // SAFETY: docs ID3D12GraphicsCommandList::SetGraphicsRootShaderResourceView:
            // sets root parameter `RootParameterIndex`, a shader resource view
            // descriptor, to the buffer at GPU address `BufferLocation`.
            // Parameters 1 to `pipeline.buffers` are those descriptors, and
            // there are exactly that many `buffers` (checked above), each a
            // live upload-heap buffer that the caller holds until this method
            // returns, after the GPU has finished. `list` is the live list,
            // recording.
            unsafe { ((**list).set_graphics_root_shader_resource_view)(list, parameter, address) };
        }
        for (draw, rect) in draws.iter().zip(&rects) {
            let rect_ptr: *const abi::Rect = rect;
            // SAFETY: docs ID3D12GraphicsCommandList::RSSetScissorRects: reads
            // `NumRects` D3D12_RECTs at `pRects`; `rect_ptr` points to one live
            // element of `rects`. `list` is the live list, recording.
            unsafe { ((**list).rs_set_scissor_rects)(list, 1, rect_ptr) };
            if let Some((index, value)) = draw.constant {
                let value_ptr: *const c_void = (&raw const value).cast();
                // SAFETY: docs ID3D12GraphicsCommandList::SetGraphicsRoot32BitConstants: as
                // above, one value from the live local `value` to offset
                // `index` of parameter 0, which is below the pipeline's count
                // of constants (checked before recording). `list` is the live
                // list, recording.
                unsafe {
                    ((**list).set_graphics_root32_bit_constants)(list, 0, 1, value_ptr, index)
                };
            }
            // SAFETY: docs ID3D12GraphicsCommandList::DrawInstanced: draws
            // `InstanceCount` instances of `VertexCountPerInstance` vertices
            // from vertex 0 and instance 0, with no vertex buffer (the pipeline
            // has no input layout); it takes only numbers. `list` is the live
            // list, recording, with the pipeline, root arguments, target,
            // viewport and scissor set above.
            unsafe { ((**list).draw_instanced)(list, draw.vertices, draw.instances, 0, 0) };
        }
        self.submit()
    }

    /// One transition of the whole of `resource` from `before` to `after`.
    fn transition(&self, resource: *mut abi::ID3D12Resource, before: i32, after: i32) {
        let list = self.list.get();
        let barrier = abi::ResourceBarrier {
            kind: abi::RESOURCE_BARRIER_TYPE_TRANSITION,
            flags: 0,
            resource,
            subresource: abi::RESOURCE_BARRIER_ALL_SUBRESOURCES,
            state_before: before,
            state_after: after,
        };
        let barrier_ptr: *const abi::ResourceBarrier = &raw const barrier;
        // SAFETY: docs ID3D12GraphicsCommandList::ResourceBarrier: reads
        // `NumBarriers` D3D12_RESOURCE_BARRIERs at `pBarriers`; `barrier_ptr`
        // points to the live local `barrier`, one transition barrier (the
        // union's `Transition` member, which `ResourceBarrier` is) of a live
        // resource the caller holds. `list` is the live list, recording.
        unsafe { ((**list).resource_barrier)(list, 1, barrier_ptr) };
    }

    /// Copy `target`'s pixels into `staging` and wait for it: a
    /// [`BufferUse::Readback`] buffer of at least [`Target::copy_len`] bytes,
    /// which then holds `height` rows of RGBA8, each [`Target::row_pitch`] bytes
    /// from the last.
    pub fn copy_target(&mut self, target: &Target, staging: &Buffer) -> Result<(), D3dError> {
        if staging.usage != BufferUse::Readback || staging.len < target.copy_len() {
            return Err(fail("staging buffer"));
        }
        let no_state: *mut abi::IUnknown = std::ptr::null_mut();
        self.begin(no_state)?;
        let list = self.list.get();
        let texture = target.texture.get();
        self.transition(
            texture,
            abi::RESOURCE_STATE_RENDER_TARGET,
            abi::RESOURCE_STATE_COPY_SOURCE,
        );
        let destination = abi::TextureCopyFootprint {
            resource: staging.resource.get(),
            kind: abi::TEXTURE_COPY_TYPE_PLACED_FOOTPRINT,
            offset: 0,
            format: abi::FORMAT_R8G8B8A8_UNORM,
            width: target.width,
            height: target.height,
            depth: 1,
            row_pitch: target.row_pitch(),
        };
        let source = abi::TextureCopySubresource {
            resource: texture,
            kind: abi::TEXTURE_COPY_TYPE_SUBRESOURCE_INDEX,
            padding: 0,
            subresource_index: 0,
            rest_of_union: [0; 7],
        };
        let destination_ptr: *const abi::TextureCopyFootprint = &raw const destination;
        let source_ptr: *const abi::TextureCopySubresource = &raw const source;
        let whole: *const c_void = std::ptr::null();
        // SAFETY: docs ID3D12GraphicsCommandList::CopyTextureRegion: copies
        // from the D3D12_TEXTURE_COPY_LOCATION at `pSrc` to the one at `pDst`,
        // at (0, 0, 0), the whole source (`pSrcBox` is optional and NULL). The
        // source (the live local `source`) is subresource 0 of the live
        // texture, in the copy-source state from the barrier above. The
        // destination (the live local `destination`) is a placed footprint at
        // offset 0 of the live readback buffer: the texture's format, width and
        // height, depth 1, and a row pitch that is a multiple of 256 and at
        // least `4 * width`; the buffer holds `row_pitch * height` bytes
        // (checked above), which is what the footprint covers. Both structures
        // are 48 bytes with the union at byte 16 (tested in `d3d12_abi`).
        // `list` is the live list, recording.
        unsafe {
            ((**list).copy_texture_region)(list, destination_ptr, 0, 0, 0, source_ptr, whole)
        };
        self.transition(
            texture,
            abi::RESOURCE_STATE_COPY_SOURCE,
            abi::RESOURCE_STATE_RENDER_TARGET,
        );
        self.submit()
    }
}

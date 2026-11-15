//! Direct3D 12 and DXGI as C declares them (phase-5.md item 5.17b): the
//! structures, the COM vtables, the interface identifiers and the constants that
//! `windows/d3d12.rs` passes. Declarations only: nothing here is called and the
//! file has no `unsafe`.
//!
//! It is compiled on Windows, where it is used, and in this crate's tests on
//! every target, so that **the tests at the bottom run on the machines the code
//! is written on**. They compare every structure's size, every field's offset,
//! the slot number of every method called and every constant with the numbers a
//! C program printed from the headers: mingw-w64's `d3d12.h`, `dxgi.h` and
//! `dxgi1_4.h` compiled for x86-64 Windows (`x86_64-w64-mingw32-gcc` 16.2.1),
//! and, for everything in Direct3D 12, Microsoft's own `d3d12.h` (DirectX-Headers
//! 1.619.5), which agreed on all 199 values both have. The tests are meaningful
//! on a 64-bit target, where pointers are 8 bytes as on 64-bit Windows; no
//! field's type differs between such targets.
//!
//! What the tests cannot show is that a method's parameter types are the
//! header's: each typed slot below was written from the header's declaration,
//! and that comparison is the audit's.
//!
//! # How the C is written in Rust
//!
//! - **Names**: types drop the `D3D12_` or `DXGI_` prefix and are in camel case
//!   (`D3D12_RESOURCE_DESC` is [`ResourceDesc`]), fields are the header's in snake
//!   case without the Hungarian `p`, and `Type` is `kind`. Interfaces and their
//!   vtables keep the header's names. Rust's naming lints, which no crate may
//!   switch off, reject the header's spellings.
//! - **An interface pointer** is `*mut ID3D12Device`, where `ID3D12Device` is
//!   `*const ID3D12DeviceVtbl`: what C calls `ID3D12Device *`, a pointer to an
//!   object whose first word points to its vtable.
//! - **A vtable** holds every slot of its interface and of those it inherits, in
//!   the header's order. A slot this crate calls has the method's type; every
//!   other is a `usize`, which has a pointer's size and cannot be called.
//! - **Unions** are written as the one member used. [`ResourceBarrier`] is the
//!   `Transition` member, the largest. [`TextureCopyFootprint`] and
//!   [`TextureCopySubresource`] are `D3D12_TEXTURE_COPY_LOCATION` with each of its
//!   two members, and [`RootParameter`] covers both `Constants` and `Descriptor`,
//!   which begin with the same two fields; their padding is written out as
//!   fields, so that the layout does not depend on Rust placing it.
//! - **A method that returns a structure** takes, on Windows, a pointer to the
//!   result after `this` and returns that pointer (the `#else` branch of
//!   `#if !defined(_WIN32)` in `d3d12.h`): `GetCPUDescriptorHandleForHeapStart`
//!   is declared that way.
//! - `BOOL`, `UINT`, `INT` and every `enum` are 32 bits; `SIZE_T` and
//!   `D3D12_CPU_DESCRIPTOR_HANDLE::ptr` are `usize`; `UINT64` and
//!   `D3D12_GPU_VIRTUAL_ADDRESS` are `u64`; `HRESULT` is `i32`; `HANDLE` is
//!   `isize`, as in `windows.rs`.

use std::ffi::c_void;

/// `GUID`.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Guid {
    pub(crate) data1: u32,
    pub(crate) data2: u16,
    pub(crate) data3: u16,
    pub(crate) data4: [u8; 8],
}

/// `LUID`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct Luid {
    pub(crate) low_part: u32,
    pub(crate) high_part: i32,
}

/// `DXGI_ADAPTER_DESC1`.
#[repr(C)]
pub(crate) struct AdapterDesc1 {
    pub(crate) description: [u16; 128],
    pub(crate) vendor_id: u32,
    pub(crate) device_id: u32,
    pub(crate) sub_sys_id: u32,
    pub(crate) revision: u32,
    pub(crate) dedicated_video_memory: usize,
    pub(crate) dedicated_system_memory: usize,
    pub(crate) shared_system_memory: usize,
    pub(crate) adapter_luid: Luid,
    pub(crate) flags: u32,
}

/// `D3D12_COMMAND_QUEUE_DESC`.
#[repr(C)]
pub(crate) struct CommandQueueDesc {
    pub(crate) kind: i32,
    pub(crate) priority: i32,
    pub(crate) flags: u32,
    pub(crate) node_mask: u32,
}

/// `D3D12_DESCRIPTOR_HEAP_DESC`.
#[repr(C)]
pub(crate) struct DescriptorHeapDesc {
    pub(crate) kind: i32,
    pub(crate) num_descriptors: u32,
    pub(crate) flags: u32,
    pub(crate) node_mask: u32,
}

/// `D3D12_CPU_DESCRIPTOR_HANDLE`.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub(crate) struct CpuDescriptorHandle {
    pub(crate) ptr: usize,
}

/// `D3D12_HEAP_PROPERTIES`.
#[repr(C)]
pub(crate) struct HeapProperties {
    pub(crate) kind: i32,
    pub(crate) cpu_page_property: i32,
    pub(crate) memory_pool_preference: i32,
    pub(crate) creation_node_mask: u32,
    pub(crate) visible_node_mask: u32,
}

/// `DXGI_SAMPLE_DESC`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct SampleDesc {
    pub(crate) count: u32,
    pub(crate) quality: u32,
}

/// `D3D12_RESOURCE_DESC`.
#[repr(C)]
pub(crate) struct ResourceDesc {
    pub(crate) dimension: i32,
    pub(crate) alignment: u64,
    pub(crate) width: u64,
    pub(crate) height: u32,
    pub(crate) depth_or_array_size: u16,
    pub(crate) mip_levels: u16,
    pub(crate) format: u32,
    pub(crate) sample_desc: SampleDesc,
    pub(crate) layout: i32,
    pub(crate) flags: u32,
}

/// `D3D12_RESOURCE_BARRIER` with its `Transition` member
/// (`D3D12_RESOURCE_TRANSITION_BARRIER`), the union's largest.
#[repr(C)]
pub(crate) struct ResourceBarrier {
    pub(crate) kind: i32,
    pub(crate) flags: i32,
    pub(crate) resource: *mut ID3D12Resource,
    pub(crate) subresource: u32,
    pub(crate) state_before: i32,
    pub(crate) state_after: i32,
}

/// `D3D12_VIEWPORT`.
#[repr(C)]
pub(crate) struct Viewport {
    pub(crate) top_left_x: f32,
    pub(crate) top_left_y: f32,
    pub(crate) width: f32,
    pub(crate) height: f32,
    pub(crate) min_depth: f32,
    pub(crate) max_depth: f32,
}

/// `D3D12_RECT`, which is `RECT`.
#[repr(C)]
pub(crate) struct Rect {
    pub(crate) left: i32,
    pub(crate) top: i32,
    pub(crate) right: i32,
    pub(crate) bottom: i32,
}

/// `D3D12_RANGE`.
#[repr(C)]
pub(crate) struct Range {
    pub(crate) begin: usize,
    pub(crate) end: usize,
}

/// `D3D12_TEXTURE_COPY_LOCATION` with its `PlacedFootprint` member
/// (`D3D12_PLACED_SUBRESOURCE_FOOTPRINT`: an offset, then a
/// `D3D12_SUBRESOURCE_FOOTPRINT`): a place in a buffer.
#[repr(C)]
pub(crate) struct TextureCopyFootprint {
    pub(crate) resource: *mut ID3D12Resource,
    pub(crate) kind: i32,
    pub(crate) offset: u64,
    pub(crate) format: u32,
    pub(crate) width: u32,
    pub(crate) height: u32,
    pub(crate) depth: u32,
    pub(crate) row_pitch: u32,
}

/// `D3D12_TEXTURE_COPY_LOCATION` with its `SubresourceIndex` member: a
/// subresource of a texture. The union starts at byte 16 and is 32 bytes long.
#[repr(C)]
pub(crate) struct TextureCopySubresource {
    pub(crate) resource: *mut ID3D12Resource,
    pub(crate) kind: i32,
    pub(crate) padding: u32,
    pub(crate) subresource_index: u32,
    pub(crate) rest_of_union: [u32; 7],
}

/// `D3D12_SHADER_BYTECODE`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct ShaderBytecode {
    pub(crate) shader_bytecode: *const c_void,
    pub(crate) bytecode_length: usize,
}

/// `D3D12_STREAM_OUTPUT_DESC`.
#[repr(C)]
pub(crate) struct StreamOutputDesc {
    pub(crate) declaration: *const c_void,
    pub(crate) num_entries: u32,
    pub(crate) buffer_strides: *const u32,
    pub(crate) num_strides: u32,
    pub(crate) rasterized_stream: u32,
}

/// `D3D12_RENDER_TARGET_BLEND_DESC`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct RenderTargetBlendDesc {
    pub(crate) blend_enable: i32,
    pub(crate) logic_op_enable: i32,
    pub(crate) src_blend: i32,
    pub(crate) dest_blend: i32,
    pub(crate) blend_op: i32,
    pub(crate) src_blend_alpha: i32,
    pub(crate) dest_blend_alpha: i32,
    pub(crate) blend_op_alpha: i32,
    pub(crate) logic_op: i32,
    pub(crate) render_target_write_mask: u8,
}

/// `D3D12_BLEND_DESC`.
#[repr(C)]
pub(crate) struct BlendDesc {
    pub(crate) alpha_to_coverage_enable: i32,
    pub(crate) independent_blend_enable: i32,
    pub(crate) render_target: [RenderTargetBlendDesc; 8],
}

/// `D3D12_RASTERIZER_DESC`.
#[repr(C)]
pub(crate) struct RasterizerDesc {
    pub(crate) fill_mode: i32,
    pub(crate) cull_mode: i32,
    pub(crate) front_counter_clockwise: i32,
    pub(crate) depth_bias: i32,
    pub(crate) depth_bias_clamp: f32,
    pub(crate) slope_scaled_depth_bias: f32,
    pub(crate) depth_clip_enable: i32,
    pub(crate) multisample_enable: i32,
    pub(crate) antialiased_line_enable: i32,
    pub(crate) forced_sample_count: u32,
    pub(crate) conservative_raster: i32,
}

/// `D3D12_DEPTH_STENCILOP_DESC`.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct DepthStencilOpDesc {
    pub(crate) stencil_fail_op: i32,
    pub(crate) stencil_depth_fail_op: i32,
    pub(crate) stencil_pass_op: i32,
    pub(crate) stencil_func: i32,
}

/// `D3D12_DEPTH_STENCIL_DESC`.
#[repr(C)]
pub(crate) struct DepthStencilDesc {
    pub(crate) depth_enable: i32,
    pub(crate) depth_write_mask: i32,
    pub(crate) depth_func: i32,
    pub(crate) stencil_enable: i32,
    pub(crate) stencil_read_mask: u8,
    pub(crate) stencil_write_mask: u8,
    pub(crate) front_face: DepthStencilOpDesc,
    pub(crate) back_face: DepthStencilOpDesc,
}

/// `D3D12_INPUT_LAYOUT_DESC`.
#[repr(C)]
pub(crate) struct InputLayoutDesc {
    pub(crate) input_element_descs: *const c_void,
    pub(crate) num_elements: u32,
}

/// `D3D12_CACHED_PIPELINE_STATE`.
#[repr(C)]
pub(crate) struct CachedPipelineState {
    pub(crate) cached_blob: *const c_void,
    pub(crate) cached_blob_size_in_bytes: usize,
}

/// `D3D12_GRAPHICS_PIPELINE_STATE_DESC`.
#[repr(C)]
pub(crate) struct GraphicsPipelineStateDesc {
    pub(crate) root_signature: *mut IUnknown,
    pub(crate) vs: ShaderBytecode,
    pub(crate) ps: ShaderBytecode,
    pub(crate) ds: ShaderBytecode,
    pub(crate) hs: ShaderBytecode,
    pub(crate) gs: ShaderBytecode,
    pub(crate) stream_output: StreamOutputDesc,
    pub(crate) blend_state: BlendDesc,
    pub(crate) sample_mask: u32,
    pub(crate) rasterizer_state: RasterizerDesc,
    pub(crate) depth_stencil_state: DepthStencilDesc,
    pub(crate) input_layout: InputLayoutDesc,
    pub(crate) ib_strip_cut_value: i32,
    pub(crate) primitive_topology_type: i32,
    pub(crate) num_render_targets: u32,
    pub(crate) rtv_formats: [u32; 8],
    pub(crate) dsv_format: u32,
    pub(crate) sample_desc: SampleDesc,
    pub(crate) node_mask: u32,
    pub(crate) cached_pso: CachedPipelineState,
    pub(crate) flags: i32,
}

/// `D3D12_ROOT_PARAMETER` with its `Constants` member (`D3D12_ROOT_CONSTANTS`)
/// or its `Descriptor` member (`D3D12_ROOT_DESCRIPTOR`, which is the first two
/// fields of the other; `num_32bit_values` is then 0 and not read). The union
/// starts at byte 8 and is 16 bytes long.
#[repr(C)]
pub(crate) struct RootParameter {
    pub(crate) kind: i32,
    pub(crate) padding: u32,
    pub(crate) shader_register: u32,
    pub(crate) register_space: u32,
    pub(crate) num_32bit_values: u32,
    pub(crate) rest_of_union: u32,
    pub(crate) shader_visibility: i32,
    pub(crate) padding_after: u32,
}

/// `D3D12_ROOT_SIGNATURE_DESC`.
#[repr(C)]
pub(crate) struct RootSignatureDesc {
    pub(crate) num_parameters: u32,
    pub(crate) parameters: *const RootParameter,
    pub(crate) num_static_samplers: u32,
    pub(crate) static_samplers: *const c_void,
    pub(crate) flags: u32,
}

/// `IUnknown`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct IUnknownVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    /// `IUnknown::Release`.
    pub(crate) release: unsafe extern "system" fn(this: *mut IUnknown) -> u32,
}

/// An `IUnknown` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut IUnknown`.
pub(crate) type IUnknown = *const IUnknownVtbl;

/// `ID3D12Device`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct ID3D12DeviceVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) get_private_data: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) set_name: usize,
    pub(crate) get_node_count: usize,
    /// `ID3D12Device::CreateCommandQueue`.
    pub(crate) create_command_queue: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        desc: *const CommandQueueDesc,
        iid: *const Guid,
        queue: *mut *mut c_void,
    ) -> i32,
    /// `ID3D12Device::CreateCommandAllocator`.
    pub(crate) create_command_allocator: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        kind: i32,
        iid: *const Guid,
        allocator: *mut *mut c_void,
    ) -> i32,
    /// `ID3D12Device::CreateGraphicsPipelineState`.
    pub(crate) create_graphics_pipeline_state: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        desc: *const GraphicsPipelineStateDesc,
        iid: *const Guid,
        state: *mut *mut c_void,
    ) -> i32,
    pub(crate) create_compute_pipeline_state: usize,
    /// `ID3D12Device::CreateCommandList`.
    pub(crate) create_command_list: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        node_mask: u32,
        kind: i32,
        allocator: *mut ID3D12CommandAllocator,
        initial_state: *mut IUnknown,
        iid: *const Guid,
        list: *mut *mut c_void,
    ) -> i32,
    pub(crate) check_feature_support: usize,
    /// `ID3D12Device::CreateDescriptorHeap`.
    pub(crate) create_descriptor_heap: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        desc: *const DescriptorHeapDesc,
        iid: *const Guid,
        heap: *mut *mut c_void,
    ) -> i32,
    pub(crate) get_descriptor_handle_increment_size: usize,
    /// `ID3D12Device::CreateRootSignature`.
    pub(crate) create_root_signature: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        node_mask: u32,
        blob: *const c_void,
        length: usize,
        iid: *const Guid,
        signature: *mut *mut c_void,
    ) -> i32,
    pub(crate) create_constant_buffer_view: usize,
    pub(crate) create_shader_resource_view: usize,
    pub(crate) create_unordered_access_view: usize,
    /// `ID3D12Device::CreateRenderTargetView`.
    pub(crate) create_render_target_view: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        resource: *mut ID3D12Resource,
        desc: *const c_void,
        descriptor: CpuDescriptorHandle,
    ),
    pub(crate) create_depth_stencil_view: usize,
    pub(crate) create_sampler: usize,
    pub(crate) copy_descriptors: usize,
    pub(crate) copy_descriptors_simple: usize,
    pub(crate) get_resource_allocation_info: usize,
    pub(crate) get_custom_heap_properties: usize,
    /// `ID3D12Device::CreateCommittedResource`.
    pub(crate) create_committed_resource: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        heap: *const HeapProperties,
        heap_flags: i32,
        desc: *const ResourceDesc,
        initial_state: i32,
        clear_value: *const c_void,
        iid: *const Guid,
        resource: *mut *mut c_void,
    ) -> i32,
    pub(crate) create_heap: usize,
    pub(crate) create_placed_resource: usize,
    pub(crate) create_reserved_resource: usize,
    pub(crate) create_shared_handle: usize,
    pub(crate) open_shared_handle: usize,
    pub(crate) open_shared_handle_by_name: usize,
    pub(crate) make_resident: usize,
    pub(crate) evict: usize,
    /// `ID3D12Device::CreateFence`.
    pub(crate) create_fence: unsafe extern "system" fn(
        this: *mut ID3D12Device,
        initial_value: u64,
        flags: i32,
        iid: *const Guid,
        fence: *mut *mut c_void,
    ) -> i32,
    pub(crate) get_device_removed_reason: usize,
    pub(crate) get_copyable_footprints: usize,
    pub(crate) create_query_heap: usize,
    pub(crate) set_stable_power_state: usize,
    pub(crate) create_command_signature: usize,
    pub(crate) get_resource_tiling: usize,
    pub(crate) get_adapter_luid: usize,
}

/// An `ID3D12Device` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut ID3D12Device`.
pub(crate) type ID3D12Device = *const ID3D12DeviceVtbl;

/// `ID3D12CommandQueue`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct ID3D12CommandQueueVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) get_private_data: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) set_name: usize,
    pub(crate) get_device: usize,
    pub(crate) update_tile_mappings: usize,
    pub(crate) copy_tile_mappings: usize,
    /// `ID3D12CommandQueue::ExecuteCommandLists`.
    pub(crate) execute_command_lists: unsafe extern "system" fn(
        this: *mut ID3D12CommandQueue,
        count: u32,
        lists: *const *mut ID3D12GraphicsCommandList,
    ),
    pub(crate) set_marker: usize,
    pub(crate) begin_event: usize,
    pub(crate) end_event: usize,
    /// `ID3D12CommandQueue::Signal`.
    pub(crate) signal: unsafe extern "system" fn(
        this: *mut ID3D12CommandQueue,
        fence: *mut ID3D12Fence,
        value: u64,
    ) -> i32,
    pub(crate) wait: usize,
    pub(crate) get_timestamp_frequency: usize,
    pub(crate) get_clock_calibration: usize,
    pub(crate) get_desc: usize,
}

/// An `ID3D12CommandQueue` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut ID3D12CommandQueue`.
pub(crate) type ID3D12CommandQueue = *const ID3D12CommandQueueVtbl;

/// `ID3D12CommandAllocator`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct ID3D12CommandAllocatorVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) get_private_data: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) set_name: usize,
    pub(crate) get_device: usize,
    /// `ID3D12CommandAllocator::Reset`.
    pub(crate) reset: unsafe extern "system" fn(this: *mut ID3D12CommandAllocator) -> i32,
}

/// An `ID3D12CommandAllocator` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut ID3D12CommandAllocator`.
pub(crate) type ID3D12CommandAllocator = *const ID3D12CommandAllocatorVtbl;

/// `ID3D12GraphicsCommandList`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct ID3D12GraphicsCommandListVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) get_private_data: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) set_name: usize,
    pub(crate) get_device: usize,
    pub(crate) get_type: usize,
    /// `ID3D12GraphicsCommandList::Close`.
    pub(crate) close: unsafe extern "system" fn(this: *mut ID3D12GraphicsCommandList) -> i32,
    /// `ID3D12GraphicsCommandList::Reset`.
    pub(crate) reset: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        allocator: *mut ID3D12CommandAllocator,
        initial_state: *mut IUnknown,
    ) -> i32,
    pub(crate) clear_state: usize,
    /// `ID3D12GraphicsCommandList::DrawInstanced`.
    pub(crate) draw_instanced: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        vertices_per_instance: u32,
        instances: u32,
        start_vertex: u32,
        start_instance: u32,
    ),
    pub(crate) draw_indexed_instanced: usize,
    pub(crate) dispatch: usize,
    pub(crate) copy_buffer_region: usize,
    /// `ID3D12GraphicsCommandList::CopyTextureRegion`.
    pub(crate) copy_texture_region: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        destination: *const TextureCopyFootprint,
        x: u32,
        y: u32,
        z: u32,
        source: *const TextureCopySubresource,
        source_box: *const c_void,
    ),
    pub(crate) copy_resource: usize,
    pub(crate) copy_tiles: usize,
    pub(crate) resolve_subresource: usize,
    /// `ID3D12GraphicsCommandList::IASetPrimitiveTopology`.
    pub(crate) ia_set_primitive_topology:
        unsafe extern "system" fn(this: *mut ID3D12GraphicsCommandList, topology: i32),
    /// `ID3D12GraphicsCommandList::RSSetViewports`.
    pub(crate) rs_set_viewports: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        count: u32,
        viewports: *const Viewport,
    ),
    /// `ID3D12GraphicsCommandList::RSSetScissorRects`.
    pub(crate) rs_set_scissor_rects: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        count: u32,
        rects: *const Rect,
    ),
    pub(crate) om_set_blend_factor: usize,
    pub(crate) om_set_stencil_ref: usize,
    pub(crate) set_pipeline_state: usize,
    /// `ID3D12GraphicsCommandList::ResourceBarrier`.
    pub(crate) resource_barrier: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        count: u32,
        barriers: *const ResourceBarrier,
    ),
    pub(crate) execute_bundle: usize,
    pub(crate) set_descriptor_heaps: usize,
    pub(crate) set_compute_root_signature: usize,
    /// `ID3D12GraphicsCommandList::SetGraphicsRootSignature`.
    pub(crate) set_graphics_root_signature:
        unsafe extern "system" fn(this: *mut ID3D12GraphicsCommandList, signature: *mut IUnknown),
    pub(crate) set_compute_root_descriptor_table: usize,
    pub(crate) set_graphics_root_descriptor_table: usize,
    pub(crate) set_compute_root32_bit_constant: usize,
    pub(crate) set_graphics_root32_bit_constant: usize,
    pub(crate) set_compute_root32_bit_constants: usize,
    /// `ID3D12GraphicsCommandList::SetGraphicsRoot32BitConstants`.
    pub(crate) set_graphics_root32_bit_constants: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        parameter: u32,
        count: u32,
        values: *const c_void,
        offset: u32,
    ),
    pub(crate) set_compute_root_constant_buffer_view: usize,
    pub(crate) set_graphics_root_constant_buffer_view: usize,
    pub(crate) set_compute_root_shader_resource_view: usize,
    /// `ID3D12GraphicsCommandList::SetGraphicsRootShaderResourceView`.
    pub(crate) set_graphics_root_shader_resource_view: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        parameter: u32,
        location: u64,
    ),
    pub(crate) set_compute_root_unordered_access_view: usize,
    pub(crate) set_graphics_root_unordered_access_view: usize,
    pub(crate) ia_set_index_buffer: usize,
    pub(crate) ia_set_vertex_buffers: usize,
    pub(crate) so_set_targets: usize,
    /// `ID3D12GraphicsCommandList::OMSetRenderTargets`.
    pub(crate) om_set_render_targets: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        count: u32,
        targets: *const CpuDescriptorHandle,
        single_range: i32,
        depth_stencil: *const CpuDescriptorHandle,
    ),
    pub(crate) clear_depth_stencil_view: usize,
    /// `ID3D12GraphicsCommandList::ClearRenderTargetView`.
    pub(crate) clear_render_target_view: unsafe extern "system" fn(
        this: *mut ID3D12GraphicsCommandList,
        target: CpuDescriptorHandle,
        colour: *const [f32; 4],
        rect_count: u32,
        rects: *const Rect,
    ),
    pub(crate) clear_unordered_access_view_uint: usize,
    pub(crate) clear_unordered_access_view_float: usize,
    pub(crate) discard_resource: usize,
    pub(crate) begin_query: usize,
    pub(crate) end_query: usize,
    pub(crate) resolve_query_data: usize,
    pub(crate) set_predication: usize,
    pub(crate) set_marker: usize,
    pub(crate) begin_event: usize,
    pub(crate) end_event: usize,
    pub(crate) execute_indirect: usize,
}

/// An `ID3D12GraphicsCommandList` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut ID3D12GraphicsCommandList`.
pub(crate) type ID3D12GraphicsCommandList = *const ID3D12GraphicsCommandListVtbl;

/// `ID3D12Resource`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct ID3D12ResourceVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) get_private_data: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) set_name: usize,
    pub(crate) get_device: usize,
    /// `ID3D12Resource::Map`.
    pub(crate) map: unsafe extern "system" fn(
        this: *mut ID3D12Resource,
        subresource: u32,
        read_range: *const Range,
        data: *mut *mut c_void,
    ) -> i32,
    /// `ID3D12Resource::Unmap`.
    pub(crate) unmap: unsafe extern "system" fn(
        this: *mut ID3D12Resource,
        subresource: u32,
        written_range: *const Range,
    ),
    pub(crate) get_desc: usize,
    /// `ID3D12Resource::GetGPUVirtualAddress`.
    pub(crate) get_gpu_virtual_address: unsafe extern "system" fn(this: *mut ID3D12Resource) -> u64,
    pub(crate) write_to_subresource: usize,
    pub(crate) read_from_subresource: usize,
    pub(crate) get_heap_properties: usize,
}

/// An `ID3D12Resource` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut ID3D12Resource`.
pub(crate) type ID3D12Resource = *const ID3D12ResourceVtbl;

/// `ID3D12Fence`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct ID3D12FenceVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) get_private_data: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) set_name: usize,
    pub(crate) get_device: usize,
    pub(crate) get_completed_value: usize,
    /// `ID3D12Fence::SetEventOnCompletion`.
    pub(crate) set_event_on_completion:
        unsafe extern "system" fn(this: *mut ID3D12Fence, value: u64, event: isize) -> i32,
    pub(crate) signal: usize,
}

/// An `ID3D12Fence` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut ID3D12Fence`.
pub(crate) type ID3D12Fence = *const ID3D12FenceVtbl;

/// `ID3D12DescriptorHeap`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct ID3D12DescriptorHeapVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) get_private_data: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) set_name: usize,
    pub(crate) get_device: usize,
    pub(crate) get_desc: usize,
    /// `ID3D12DescriptorHeap::GetCPUDescriptorHandleForHeapStart`.
    pub(crate) get_cpu_descriptor_handle_for_heap_start:
        unsafe extern "system" fn(
            this: *mut ID3D12DescriptorHeap,
            result: *mut CpuDescriptorHandle,
        ) -> *mut CpuDescriptorHandle,
    pub(crate) get_gpu_descriptor_handle_for_heap_start: usize,
}

/// An `ID3D12DescriptorHeap` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut ID3D12DescriptorHeap`.
pub(crate) type ID3D12DescriptorHeap = *const ID3D12DescriptorHeapVtbl;

/// `ID3D10Blob`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct ID3D10BlobVtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    /// `ID3D10Blob::GetBufferPointer`.
    pub(crate) get_buffer_pointer: unsafe extern "system" fn(this: *mut ID3D10Blob) -> *mut c_void,
    /// `ID3D10Blob::GetBufferSize`.
    pub(crate) get_buffer_size: unsafe extern "system" fn(this: *mut ID3D10Blob) -> usize,
}

/// An `ID3D10Blob` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut ID3D10Blob`.
pub(crate) type ID3D10Blob = *const ID3D10BlobVtbl;

/// `IDXGIFactory4`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct IDXGIFactory4Vtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) get_private_data: usize,
    pub(crate) get_parent: usize,
    pub(crate) enum_adapters: usize,
    pub(crate) make_window_association: usize,
    pub(crate) get_window_association: usize,
    pub(crate) create_swap_chain: usize,
    pub(crate) create_software_adapter: usize,
    /// `IDXGIFactory4::EnumAdapters1`.
    pub(crate) enum_adapters1: unsafe extern "system" fn(
        this: *mut IDXGIFactory4,
        index: u32,
        adapter: *mut *mut IDXGIAdapter1,
    ) -> i32,
    pub(crate) is_current: usize,
    pub(crate) is_windowed_stereo_enabled: usize,
    pub(crate) create_swap_chain_for_hwnd: usize,
    pub(crate) create_swap_chain_for_core_window: usize,
    pub(crate) get_shared_resource_adapter_luid: usize,
    pub(crate) register_stereo_status_window: usize,
    pub(crate) register_stereo_status_event: usize,
    pub(crate) unregister_stereo_status: usize,
    pub(crate) register_occlusion_status_window: usize,
    pub(crate) register_occlusion_status_event: usize,
    pub(crate) unregister_occlusion_status: usize,
    pub(crate) create_swap_chain_for_composition: usize,
    pub(crate) get_creation_flags: usize,
    pub(crate) enum_adapter_by_luid: usize,
    /// `IDXGIFactory4::EnumWarpAdapter`.
    pub(crate) enum_warp_adapter: unsafe extern "system" fn(
        this: *mut IDXGIFactory4,
        iid: *const Guid,
        adapter: *mut *mut c_void,
    ) -> i32,
}

/// An `IDXGIFactory4` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut IDXGIFactory4`.
pub(crate) type IDXGIFactory4 = *const IDXGIFactory4Vtbl;

/// `IDXGIAdapter1`'s vtable: every slot, in the header's order (`xtask/src/sys.rs` lists
/// them and checks this declaration against the list). A `usize` is a slot this
/// crate never calls.
#[repr(C)]
pub(crate) struct IDXGIAdapter1Vtbl {
    pub(crate) query_interface: usize,
    pub(crate) add_ref: usize,
    pub(crate) release: usize,
    pub(crate) set_private_data: usize,
    pub(crate) set_private_data_interface: usize,
    pub(crate) get_private_data: usize,
    pub(crate) get_parent: usize,
    pub(crate) enum_outputs: usize,
    pub(crate) get_desc: usize,
    /// `IDXGIAdapter1::CheckInterfaceSupport`.
    pub(crate) check_interface_support: unsafe extern "system" fn(
        this: *mut IDXGIAdapter1,
        interface: *const Guid,
        version: *mut i64,
    ) -> i32,
    /// `IDXGIAdapter1::GetDesc1`.
    pub(crate) get_desc1:
        unsafe extern "system" fn(this: *mut IDXGIAdapter1, desc: *mut AdapterDesc1) -> i32,
}

/// An `IDXGIAdapter1` object as C sees it: its first word points to its vtable. An
/// interface pointer is a `*mut IDXGIAdapter1`.
pub(crate) type IDXGIAdapter1 = *const IDXGIAdapter1Vtbl;

/// A `GUID` from the four parts `DEFINE_GUID` is given.
const fn guid(data1: u32, data2: u16, data3: u16, data4: [u8; 8]) -> Guid {
    Guid {
        data1,
        data2,
        data3,
        data4,
    }
}

// The interface identifiers, from the `DEFINE_GUID` lines of `dxgi.h`,
// `dxgi1_4.h` and `d3d12.h`.
/// `IID_IDXGIFactory4`.
pub(crate) static IID_DXGI_FACTORY4: Guid = guid(
    0x1bc6_ea02,
    0xef36,
    0x464f,
    [0xbf, 0x0c, 0x21, 0xca, 0x39, 0xe5, 0x16, 0x8a],
);
/// `IID_IDXGIAdapter1`.
pub(crate) static IID_DXGI_ADAPTER1: Guid = guid(
    0x2903_8f61,
    0x3839,
    0x4626,
    [0x91, 0xfd, 0x08, 0x68, 0x79, 0x01, 0x1a, 0x05],
);
/// `IID_IDXGIDevice`, which `IDXGIAdapter::CheckInterfaceSupport` is asked about
/// to read the driver's version.
pub(crate) static IID_DXGI_DEVICE: Guid = guid(
    0x54ec_77fa,
    0x1377,
    0x44e6,
    [0x8c, 0x32, 0x88, 0xfd, 0x5f, 0x44, 0xc8, 0x4c],
);
/// `IID_ID3D12Device`.
pub(crate) static IID_DEVICE: Guid = guid(
    0x1898_19f1,
    0x1db6,
    0x4b57,
    [0xbe, 0x54, 0x18, 0x21, 0x33, 0x9b, 0x85, 0xf7],
);
/// `IID_ID3D12CommandQueue`.
pub(crate) static IID_COMMAND_QUEUE: Guid = guid(
    0x0ec8_70a6,
    0x5d7e,
    0x4c22,
    [0x8c, 0xfc, 0x5b, 0xaa, 0xe0, 0x76, 0x16, 0xed],
);
/// `IID_ID3D12CommandAllocator`.
pub(crate) static IID_COMMAND_ALLOCATOR: Guid = guid(
    0x6102_dee4,
    0xaf59,
    0x4b09,
    [0xb9, 0x99, 0xb4, 0x4d, 0x73, 0xf0, 0x9b, 0x24],
);
/// `IID_ID3D12GraphicsCommandList`.
pub(crate) static IID_GRAPHICS_COMMAND_LIST: Guid = guid(
    0x5b16_0d0f,
    0xac1b,
    0x4185,
    [0x8b, 0xa8, 0xb3, 0xae, 0x42, 0xa5, 0xa4, 0x55],
);
/// `IID_ID3D12Fence`.
pub(crate) static IID_FENCE: Guid = guid(
    0x0a75_3dcf,
    0xc4d8,
    0x4b91,
    [0xad, 0xf6, 0xbe, 0x5a, 0x60, 0xd9, 0x5a, 0x76],
);
/// `IID_ID3D12Resource`.
pub(crate) static IID_RESOURCE: Guid = guid(
    0x6964_42be,
    0xa72e,
    0x4059,
    [0xbc, 0x79, 0x5b, 0x5c, 0x98, 0x04, 0x0f, 0xad],
);
/// `IID_ID3D12DescriptorHeap`.
pub(crate) static IID_DESCRIPTOR_HEAP: Guid = guid(
    0x8efb_471d,
    0x616c,
    0x4f49,
    [0x90, 0xf7, 0x12, 0x7b, 0xb7, 0x63, 0xfa, 0x51],
);
/// `IID_ID3D12RootSignature`.
pub(crate) static IID_ROOT_SIGNATURE: Guid = guid(
    0xc54a_6b66,
    0x72df,
    0x4ee8,
    [0x8b, 0xe5, 0xa9, 0x46, 0xa1, 0x42, 0x92, 0x14],
);
/// `IID_ID3D12PipelineState`.
pub(crate) static IID_PIPELINE_STATE: Guid = guid(
    0x765a_30f3,
    0xf624,
    0x4c6f,
    [0xa8, 0x28, 0xac, 0xe9, 0x48, 0x62, 0x24, 0x45],
);

// Constants, named as the header names them less the `D3D12_`, `D3D_` or
// `DXGI_` prefix. The tests below compare each with the header's value.
pub(crate) const FEATURE_LEVEL_11_0: i32 = 0xb000;
pub(crate) const COMMAND_LIST_TYPE_DIRECT: i32 = 0;
pub(crate) const DESCRIPTOR_HEAP_TYPE_RTV: i32 = 2;
pub(crate) const HEAP_TYPE_DEFAULT: i32 = 1;
pub(crate) const HEAP_TYPE_UPLOAD: i32 = 2;
pub(crate) const HEAP_TYPE_READBACK: i32 = 3;
pub(crate) const HEAP_FLAG_NONE: i32 = 0;
pub(crate) const RESOURCE_DIMENSION_BUFFER: i32 = 1;
pub(crate) const RESOURCE_DIMENSION_TEXTURE2D: i32 = 3;
pub(crate) const TEXTURE_LAYOUT_UNKNOWN: i32 = 0;
pub(crate) const TEXTURE_LAYOUT_ROW_MAJOR: i32 = 1;
pub(crate) const RESOURCE_FLAG_ALLOW_RENDER_TARGET: u32 = 1;
pub(crate) const RESOURCE_STATE_RENDER_TARGET: i32 = 0x4;
pub(crate) const RESOURCE_STATE_COPY_DEST: i32 = 0x400;
pub(crate) const RESOURCE_STATE_COPY_SOURCE: i32 = 0x800;
pub(crate) const RESOURCE_STATE_GENERIC_READ: i32 = 0xac3;
pub(crate) const RESOURCE_BARRIER_TYPE_TRANSITION: i32 = 0;
pub(crate) const RESOURCE_BARRIER_ALL_SUBRESOURCES: u32 = 0xffff_ffff;
pub(crate) const TEXTURE_COPY_TYPE_SUBRESOURCE_INDEX: i32 = 0;
pub(crate) const TEXTURE_COPY_TYPE_PLACED_FOOTPRINT: i32 = 1;
pub(crate) const FORMAT_UNKNOWN: u32 = 0;
pub(crate) const FORMAT_R8G8B8A8_UNORM: u32 = 28;
pub(crate) const BLEND_ZERO: i32 = 1;
pub(crate) const BLEND_ONE: i32 = 2;
pub(crate) const BLEND_INV_SRC_ALPHA: i32 = 6;
pub(crate) const BLEND_OP_ADD: i32 = 1;
pub(crate) const LOGIC_OP_NOOP: i32 = 4;
pub(crate) const COLOR_WRITE_ENABLE_ALL: u8 = 15;
pub(crate) const DEFAULT_SAMPLE_MASK: u32 = 0xffff_ffff;
pub(crate) const FILL_MODE_SOLID: i32 = 3;
pub(crate) const CULL_MODE_NONE: i32 = 1;
pub(crate) const COMPARISON_FUNC_ALWAYS: i32 = 8;
pub(crate) const STENCIL_OP_KEEP: i32 = 1;
pub(crate) const DEPTH_WRITE_MASK_ZERO: i32 = 0;
pub(crate) const PRIMITIVE_TOPOLOGY_TYPE_TRIANGLE: i32 = 3;
pub(crate) const TOPOLOGY_TRIANGLE_LIST: i32 = 4;
pub(crate) const ROOT_PARAMETER_TYPE_32BIT_CONSTANTS: i32 = 1;
pub(crate) const ROOT_PARAMETER_TYPE_SRV: i32 = 3;
pub(crate) const SHADER_VISIBILITY_ALL: i32 = 0;
pub(crate) const ROOT_SIGNATURE_VERSION_1: i32 = 1;
pub(crate) const FENCE_FLAG_NONE: i32 = 0;
/// A buffer row's pitch, when a texture is copied to it, is a multiple of this.
pub(crate) const TEXTURE_DATA_PITCH_ALIGNMENT: u32 = 256;
/// The largest side of a 2D texture.
pub(crate) const REQ_TEXTURE2D_U_OR_V_DIMENSION: u32 = 16384;
pub(crate) const ADAPTER_FLAG_SOFTWARE: u32 = 2;
/// `DXGI_ERROR_NOT_FOUND`, `0x887A0002`: `EnumAdapters1` past the last adapter.
pub(crate) const ERROR_NOT_FOUND: i32 = -2_005_270_526;

#[cfg(test)]
mod tests {
    use std::mem::{offset_of, size_of};

    use super::*;

    /// The header's sizes, for x86-64 Windows (see the module documentation for
    /// where each number is from).
    #[test]
    #[cfg(target_pointer_width = "64")]
    fn structures_have_the_headers_sizes() {
        assert_eq!(size_of::<Guid>(), 16, "GUID");
        assert_eq!(size_of::<AdapterDesc1>(), 312, "DXGI_ADAPTER_DESC1");
        assert_eq!(
            size_of::<CommandQueueDesc>(),
            16,
            "D3D12_COMMAND_QUEUE_DESC"
        );
        assert_eq!(
            size_of::<DescriptorHeapDesc>(),
            16,
            "D3D12_DESCRIPTOR_HEAP_DESC"
        );
        assert_eq!(
            size_of::<CpuDescriptorHandle>(),
            8,
            "D3D12_CPU_DESCRIPTOR_HANDLE"
        );
        assert_eq!(size_of::<HeapProperties>(), 20, "D3D12_HEAP_PROPERTIES");
        assert_eq!(size_of::<ResourceDesc>(), 56, "D3D12_RESOURCE_DESC");
        assert_eq!(size_of::<ResourceBarrier>(), 32, "D3D12_RESOURCE_BARRIER");
        assert_eq!(size_of::<Viewport>(), 24, "D3D12_VIEWPORT");
        assert_eq!(size_of::<Rect>(), 16, "D3D12_RECT");
        assert_eq!(size_of::<Range>(), 16, "D3D12_RANGE");
        assert_eq!(
            size_of::<TextureCopyFootprint>(),
            48,
            "D3D12_TEXTURE_COPY_LOCATION"
        );
        assert_eq!(size_of::<ShaderBytecode>(), 16, "D3D12_SHADER_BYTECODE");
        assert_eq!(
            size_of::<StreamOutputDesc>(),
            32,
            "D3D12_STREAM_OUTPUT_DESC"
        );
        assert_eq!(
            size_of::<RenderTargetBlendDesc>(),
            40,
            "D3D12_RENDER_TARGET_BLEND_DESC"
        );
        assert_eq!(size_of::<BlendDesc>(), 328, "D3D12_BLEND_DESC");
        assert_eq!(size_of::<RasterizerDesc>(), 44, "D3D12_RASTERIZER_DESC");
        assert_eq!(
            size_of::<DepthStencilOpDesc>(),
            16,
            "D3D12_DEPTH_STENCILOP_DESC"
        );
        assert_eq!(
            size_of::<DepthStencilDesc>(),
            52,
            "D3D12_DEPTH_STENCIL_DESC"
        );
        assert_eq!(size_of::<InputLayoutDesc>(), 16, "D3D12_INPUT_LAYOUT_DESC");
        assert_eq!(
            size_of::<CachedPipelineState>(),
            16,
            "D3D12_CACHED_PIPELINE_STATE"
        );
        assert_eq!(
            size_of::<GraphicsPipelineStateDesc>(),
            656,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC"
        );
        assert_eq!(size_of::<RootParameter>(), 32, "D3D12_ROOT_PARAMETER");
        assert_eq!(
            size_of::<RootSignatureDesc>(),
            40,
            "D3D12_ROOT_SIGNATURE_DESC"
        );
        // The second form of D3D12_TEXTURE_COPY_LOCATION is as large as the first.
        assert_eq!(size_of::<TextureCopySubresource>(), 48);
        assert_eq!(size_of::<Luid>(), 8);
        assert_eq!(size_of::<SampleDesc>(), 8);
    }

    #[test]
    #[cfg(target_pointer_width = "64")]
    fn fields_are_at_the_headers_offsets() {
        assert_eq!(
            offset_of!(AdapterDesc1, description),
            0,
            "DXGI_ADAPTER_DESC1.Description"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, vendor_id),
            256,
            "DXGI_ADAPTER_DESC1.VendorId"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, device_id),
            260,
            "DXGI_ADAPTER_DESC1.DeviceId"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, sub_sys_id),
            264,
            "DXGI_ADAPTER_DESC1.SubSysId"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, revision),
            268,
            "DXGI_ADAPTER_DESC1.Revision"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, dedicated_video_memory),
            272,
            "DXGI_ADAPTER_DESC1.DedicatedVideoMemory"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, dedicated_system_memory),
            280,
            "DXGI_ADAPTER_DESC1.DedicatedSystemMemory"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, shared_system_memory),
            288,
            "DXGI_ADAPTER_DESC1.SharedSystemMemory"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, adapter_luid),
            296,
            "DXGI_ADAPTER_DESC1.AdapterLuid"
        );
        assert_eq!(
            offset_of!(AdapterDesc1, flags),
            304,
            "DXGI_ADAPTER_DESC1.Flags"
        );
        assert_eq!(
            offset_of!(CommandQueueDesc, kind),
            0,
            "D3D12_COMMAND_QUEUE_DESC.Type"
        );
        assert_eq!(
            offset_of!(CommandQueueDesc, priority),
            4,
            "D3D12_COMMAND_QUEUE_DESC.Priority"
        );
        assert_eq!(
            offset_of!(CommandQueueDesc, flags),
            8,
            "D3D12_COMMAND_QUEUE_DESC.Flags"
        );
        assert_eq!(
            offset_of!(CommandQueueDesc, node_mask),
            12,
            "D3D12_COMMAND_QUEUE_DESC.NodeMask"
        );
        assert_eq!(
            offset_of!(DescriptorHeapDesc, kind),
            0,
            "D3D12_DESCRIPTOR_HEAP_DESC.Type"
        );
        assert_eq!(
            offset_of!(DescriptorHeapDesc, num_descriptors),
            4,
            "D3D12_DESCRIPTOR_HEAP_DESC.NumDescriptors"
        );
        assert_eq!(
            offset_of!(DescriptorHeapDesc, flags),
            8,
            "D3D12_DESCRIPTOR_HEAP_DESC.Flags"
        );
        assert_eq!(
            offset_of!(DescriptorHeapDesc, node_mask),
            12,
            "D3D12_DESCRIPTOR_HEAP_DESC.NodeMask"
        );
        assert_eq!(
            offset_of!(CpuDescriptorHandle, ptr),
            0,
            "D3D12_CPU_DESCRIPTOR_HANDLE.ptr"
        );
        assert_eq!(
            offset_of!(HeapProperties, kind),
            0,
            "D3D12_HEAP_PROPERTIES.Type"
        );
        assert_eq!(
            offset_of!(HeapProperties, cpu_page_property),
            4,
            "D3D12_HEAP_PROPERTIES.CPUPageProperty"
        );
        assert_eq!(
            offset_of!(HeapProperties, memory_pool_preference),
            8,
            "D3D12_HEAP_PROPERTIES.MemoryPoolPreference"
        );
        assert_eq!(
            offset_of!(HeapProperties, creation_node_mask),
            12,
            "D3D12_HEAP_PROPERTIES.CreationNodeMask"
        );
        assert_eq!(
            offset_of!(HeapProperties, visible_node_mask),
            16,
            "D3D12_HEAP_PROPERTIES.VisibleNodeMask"
        );
        assert_eq!(
            offset_of!(ResourceDesc, dimension),
            0,
            "D3D12_RESOURCE_DESC.Dimension"
        );
        assert_eq!(
            offset_of!(ResourceDesc, alignment),
            8,
            "D3D12_RESOURCE_DESC.Alignment"
        );
        assert_eq!(
            offset_of!(ResourceDesc, width),
            16,
            "D3D12_RESOURCE_DESC.Width"
        );
        assert_eq!(
            offset_of!(ResourceDesc, height),
            24,
            "D3D12_RESOURCE_DESC.Height"
        );
        assert_eq!(
            offset_of!(ResourceDesc, depth_or_array_size),
            28,
            "D3D12_RESOURCE_DESC.DepthOrArraySize"
        );
        assert_eq!(
            offset_of!(ResourceDesc, mip_levels),
            30,
            "D3D12_RESOURCE_DESC.MipLevels"
        );
        assert_eq!(
            offset_of!(ResourceDesc, format),
            32,
            "D3D12_RESOURCE_DESC.Format"
        );
        assert_eq!(
            offset_of!(ResourceDesc, sample_desc),
            36,
            "D3D12_RESOURCE_DESC.SampleDesc"
        );
        assert_eq!(
            offset_of!(ResourceDesc, layout),
            44,
            "D3D12_RESOURCE_DESC.Layout"
        );
        assert_eq!(
            offset_of!(ResourceDesc, flags),
            48,
            "D3D12_RESOURCE_DESC.Flags"
        );
        assert_eq!(
            offset_of!(ResourceBarrier, kind),
            0,
            "D3D12_RESOURCE_BARRIER.Type"
        );
        assert_eq!(
            offset_of!(ResourceBarrier, flags),
            4,
            "D3D12_RESOURCE_BARRIER.Flags"
        );
        assert_eq!(
            offset_of!(ResourceBarrier, resource),
            8,
            "D3D12_RESOURCE_BARRIER.Transition.pResource"
        );
        assert_eq!(
            offset_of!(ResourceBarrier, subresource),
            16,
            "D3D12_RESOURCE_BARRIER.Transition.Subresource"
        );
        assert_eq!(
            offset_of!(ResourceBarrier, state_before),
            20,
            "D3D12_RESOURCE_BARRIER.Transition.StateBefore"
        );
        assert_eq!(
            offset_of!(ResourceBarrier, state_after),
            24,
            "D3D12_RESOURCE_BARRIER.Transition.StateAfter"
        );
        assert_eq!(
            offset_of!(Viewport, top_left_x),
            0,
            "D3D12_VIEWPORT.TopLeftX"
        );
        assert_eq!(
            offset_of!(Viewport, top_left_y),
            4,
            "D3D12_VIEWPORT.TopLeftY"
        );
        assert_eq!(offset_of!(Viewport, width), 8, "D3D12_VIEWPORT.Width");
        assert_eq!(offset_of!(Viewport, height), 12, "D3D12_VIEWPORT.Height");
        assert_eq!(
            offset_of!(Viewport, min_depth),
            16,
            "D3D12_VIEWPORT.MinDepth"
        );
        assert_eq!(
            offset_of!(Viewport, max_depth),
            20,
            "D3D12_VIEWPORT.MaxDepth"
        );
        assert_eq!(offset_of!(Rect, left), 0, "D3D12_RECT.left");
        assert_eq!(offset_of!(Rect, top), 4, "D3D12_RECT.top");
        assert_eq!(offset_of!(Rect, right), 8, "D3D12_RECT.right");
        assert_eq!(offset_of!(Rect, bottom), 12, "D3D12_RECT.bottom");
        assert_eq!(offset_of!(Range, begin), 0, "D3D12_RANGE.Begin");
        assert_eq!(offset_of!(Range, end), 8, "D3D12_RANGE.End");
        assert_eq!(
            offset_of!(TextureCopyFootprint, resource),
            0,
            "D3D12_TEXTURE_COPY_LOCATION.pResource"
        );
        assert_eq!(
            offset_of!(TextureCopyFootprint, kind),
            8,
            "D3D12_TEXTURE_COPY_LOCATION.Type"
        );
        assert_eq!(
            offset_of!(TextureCopyFootprint, offset),
            16,
            "D3D12_TEXTURE_COPY_LOCATION.PlacedFootprint"
        );
        assert_eq!(
            offset_of!(TextureCopyFootprint, offset),
            16,
            "D3D12_TEXTURE_COPY_LOCATION.PlacedFootprint.Offset"
        );
        assert_eq!(
            offset_of!(TextureCopyFootprint, format),
            24,
            "D3D12_TEXTURE_COPY_LOCATION.PlacedFootprint.Footprint.Format"
        );
        assert_eq!(
            offset_of!(TextureCopyFootprint, width),
            28,
            "D3D12_TEXTURE_COPY_LOCATION.PlacedFootprint.Footprint.Width"
        );
        assert_eq!(
            offset_of!(TextureCopyFootprint, height),
            32,
            "D3D12_TEXTURE_COPY_LOCATION.PlacedFootprint.Footprint.Height"
        );
        assert_eq!(
            offset_of!(TextureCopyFootprint, depth),
            36,
            "D3D12_TEXTURE_COPY_LOCATION.PlacedFootprint.Footprint.Depth"
        );
        assert_eq!(
            offset_of!(TextureCopyFootprint, row_pitch),
            40,
            "D3D12_TEXTURE_COPY_LOCATION.PlacedFootprint.Footprint.RowPitch"
        );
        assert_eq!(
            offset_of!(ShaderBytecode, shader_bytecode),
            0,
            "D3D12_SHADER_BYTECODE.pShaderBytecode"
        );
        assert_eq!(
            offset_of!(ShaderBytecode, bytecode_length),
            8,
            "D3D12_SHADER_BYTECODE.BytecodeLength"
        );
        assert_eq!(
            offset_of!(StreamOutputDesc, declaration),
            0,
            "D3D12_STREAM_OUTPUT_DESC.pSODeclaration"
        );
        assert_eq!(
            offset_of!(StreamOutputDesc, num_entries),
            8,
            "D3D12_STREAM_OUTPUT_DESC.NumEntries"
        );
        assert_eq!(
            offset_of!(StreamOutputDesc, buffer_strides),
            16,
            "D3D12_STREAM_OUTPUT_DESC.pBufferStrides"
        );
        assert_eq!(
            offset_of!(StreamOutputDesc, num_strides),
            24,
            "D3D12_STREAM_OUTPUT_DESC.NumStrides"
        );
        assert_eq!(
            offset_of!(StreamOutputDesc, rasterized_stream),
            28,
            "D3D12_STREAM_OUTPUT_DESC.RasterizedStream"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, blend_enable),
            0,
            "D3D12_RENDER_TARGET_BLEND_DESC.BlendEnable"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, logic_op_enable),
            4,
            "D3D12_RENDER_TARGET_BLEND_DESC.LogicOpEnable"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, src_blend),
            8,
            "D3D12_RENDER_TARGET_BLEND_DESC.SrcBlend"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, dest_blend),
            12,
            "D3D12_RENDER_TARGET_BLEND_DESC.DestBlend"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, blend_op),
            16,
            "D3D12_RENDER_TARGET_BLEND_DESC.BlendOp"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, src_blend_alpha),
            20,
            "D3D12_RENDER_TARGET_BLEND_DESC.SrcBlendAlpha"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, dest_blend_alpha),
            24,
            "D3D12_RENDER_TARGET_BLEND_DESC.DestBlendAlpha"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, blend_op_alpha),
            28,
            "D3D12_RENDER_TARGET_BLEND_DESC.BlendOpAlpha"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, logic_op),
            32,
            "D3D12_RENDER_TARGET_BLEND_DESC.LogicOp"
        );
        assert_eq!(
            offset_of!(RenderTargetBlendDesc, render_target_write_mask),
            36,
            "D3D12_RENDER_TARGET_BLEND_DESC.RenderTargetWriteMask"
        );
        assert_eq!(
            offset_of!(BlendDesc, alpha_to_coverage_enable),
            0,
            "D3D12_BLEND_DESC.AlphaToCoverageEnable"
        );
        assert_eq!(
            offset_of!(BlendDesc, independent_blend_enable),
            4,
            "D3D12_BLEND_DESC.IndependentBlendEnable"
        );
        assert_eq!(
            offset_of!(BlendDesc, render_target),
            8,
            "D3D12_BLEND_DESC.RenderTarget"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, fill_mode),
            0,
            "D3D12_RASTERIZER_DESC.FillMode"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, cull_mode),
            4,
            "D3D12_RASTERIZER_DESC.CullMode"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, front_counter_clockwise),
            8,
            "D3D12_RASTERIZER_DESC.FrontCounterClockwise"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, depth_bias),
            12,
            "D3D12_RASTERIZER_DESC.DepthBias"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, depth_bias_clamp),
            16,
            "D3D12_RASTERIZER_DESC.DepthBiasClamp"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, slope_scaled_depth_bias),
            20,
            "D3D12_RASTERIZER_DESC.SlopeScaledDepthBias"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, depth_clip_enable),
            24,
            "D3D12_RASTERIZER_DESC.DepthClipEnable"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, multisample_enable),
            28,
            "D3D12_RASTERIZER_DESC.MultisampleEnable"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, antialiased_line_enable),
            32,
            "D3D12_RASTERIZER_DESC.AntialiasedLineEnable"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, forced_sample_count),
            36,
            "D3D12_RASTERIZER_DESC.ForcedSampleCount"
        );
        assert_eq!(
            offset_of!(RasterizerDesc, conservative_raster),
            40,
            "D3D12_RASTERIZER_DESC.ConservativeRaster"
        );
        assert_eq!(
            offset_of!(DepthStencilOpDesc, stencil_fail_op),
            0,
            "D3D12_DEPTH_STENCILOP_DESC.StencilFailOp"
        );
        assert_eq!(
            offset_of!(DepthStencilOpDesc, stencil_depth_fail_op),
            4,
            "D3D12_DEPTH_STENCILOP_DESC.StencilDepthFailOp"
        );
        assert_eq!(
            offset_of!(DepthStencilOpDesc, stencil_pass_op),
            8,
            "D3D12_DEPTH_STENCILOP_DESC.StencilPassOp"
        );
        assert_eq!(
            offset_of!(DepthStencilOpDesc, stencil_func),
            12,
            "D3D12_DEPTH_STENCILOP_DESC.StencilFunc"
        );
        assert_eq!(
            offset_of!(DepthStencilDesc, depth_enable),
            0,
            "D3D12_DEPTH_STENCIL_DESC.DepthEnable"
        );
        assert_eq!(
            offset_of!(DepthStencilDesc, depth_write_mask),
            4,
            "D3D12_DEPTH_STENCIL_DESC.DepthWriteMask"
        );
        assert_eq!(
            offset_of!(DepthStencilDesc, depth_func),
            8,
            "D3D12_DEPTH_STENCIL_DESC.DepthFunc"
        );
        assert_eq!(
            offset_of!(DepthStencilDesc, stencil_enable),
            12,
            "D3D12_DEPTH_STENCIL_DESC.StencilEnable"
        );
        assert_eq!(
            offset_of!(DepthStencilDesc, stencil_read_mask),
            16,
            "D3D12_DEPTH_STENCIL_DESC.StencilReadMask"
        );
        assert_eq!(
            offset_of!(DepthStencilDesc, stencil_write_mask),
            17,
            "D3D12_DEPTH_STENCIL_DESC.StencilWriteMask"
        );
        assert_eq!(
            offset_of!(DepthStencilDesc, front_face),
            20,
            "D3D12_DEPTH_STENCIL_DESC.FrontFace"
        );
        assert_eq!(
            offset_of!(DepthStencilDesc, back_face),
            36,
            "D3D12_DEPTH_STENCIL_DESC.BackFace"
        );
        assert_eq!(
            offset_of!(InputLayoutDesc, input_element_descs),
            0,
            "D3D12_INPUT_LAYOUT_DESC.pInputElementDescs"
        );
        assert_eq!(
            offset_of!(InputLayoutDesc, num_elements),
            8,
            "D3D12_INPUT_LAYOUT_DESC.NumElements"
        );
        assert_eq!(
            offset_of!(CachedPipelineState, cached_blob),
            0,
            "D3D12_CACHED_PIPELINE_STATE.pCachedBlob"
        );
        assert_eq!(
            offset_of!(CachedPipelineState, cached_blob_size_in_bytes),
            8,
            "D3D12_CACHED_PIPELINE_STATE.CachedBlobSizeInBytes"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, root_signature),
            0,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.pRootSignature"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, vs),
            8,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.VS"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, ps),
            24,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.PS"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, ds),
            40,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.DS"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, hs),
            56,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.HS"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, gs),
            72,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.GS"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, stream_output),
            88,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.StreamOutput"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, blend_state),
            120,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.BlendState"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, sample_mask),
            448,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.SampleMask"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, rasterizer_state),
            452,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.RasterizerState"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, depth_stencil_state),
            496,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.DepthStencilState"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, input_layout),
            552,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.InputLayout"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, ib_strip_cut_value),
            568,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.IBStripCutValue"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, primitive_topology_type),
            572,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.PrimitiveTopologyType"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, num_render_targets),
            576,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.NumRenderTargets"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, rtv_formats),
            580,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.RTVFormats"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, dsv_format),
            612,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.DSVFormat"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, sample_desc),
            616,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.SampleDesc"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, node_mask),
            624,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.NodeMask"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, cached_pso),
            632,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.CachedPSO"
        );
        assert_eq!(
            offset_of!(GraphicsPipelineStateDesc, flags),
            648,
            "D3D12_GRAPHICS_PIPELINE_STATE_DESC.Flags"
        );
        assert_eq!(
            offset_of!(RootParameter, kind),
            0,
            "D3D12_ROOT_PARAMETER.ParameterType"
        );
        assert_eq!(
            offset_of!(RootParameter, shader_register),
            8,
            "D3D12_ROOT_PARAMETER.Constants.ShaderRegister"
        );
        assert_eq!(
            offset_of!(RootParameter, register_space),
            12,
            "D3D12_ROOT_PARAMETER.Constants.RegisterSpace"
        );
        assert_eq!(
            offset_of!(RootParameter, num_32bit_values),
            16,
            "D3D12_ROOT_PARAMETER.Constants.Num32BitValues"
        );
        assert_eq!(
            offset_of!(RootParameter, shader_register),
            8,
            "D3D12_ROOT_PARAMETER.Descriptor.ShaderRegister"
        );
        assert_eq!(
            offset_of!(RootParameter, register_space),
            12,
            "D3D12_ROOT_PARAMETER.Descriptor.RegisterSpace"
        );
        assert_eq!(
            offset_of!(RootParameter, shader_visibility),
            24,
            "D3D12_ROOT_PARAMETER.ShaderVisibility"
        );
        assert_eq!(
            offset_of!(RootSignatureDesc, num_parameters),
            0,
            "D3D12_ROOT_SIGNATURE_DESC.NumParameters"
        );
        assert_eq!(
            offset_of!(RootSignatureDesc, parameters),
            8,
            "D3D12_ROOT_SIGNATURE_DESC.pParameters"
        );
        assert_eq!(
            offset_of!(RootSignatureDesc, num_static_samplers),
            16,
            "D3D12_ROOT_SIGNATURE_DESC.NumStaticSamplers"
        );
        assert_eq!(
            offset_of!(RootSignatureDesc, static_samplers),
            24,
            "D3D12_ROOT_SIGNATURE_DESC.pStaticSamplers"
        );
        assert_eq!(
            offset_of!(RootSignatureDesc, flags),
            32,
            "D3D12_ROOT_SIGNATURE_DESC.Flags"
        );
        // D3D12_TEXTURE_COPY_LOCATION.SubresourceIndex, the union's other member.
        assert_eq!(offset_of!(TextureCopySubresource, resource), 0);
        assert_eq!(offset_of!(TextureCopySubresource, kind), 8);
        assert_eq!(offset_of!(TextureCopySubresource, subresource_index), 16);
    }

    /// Each method this crate calls is in the header's slot: its field's offset
    /// in the vtable, in pointers.
    #[test]
    #[cfg(target_pointer_width = "64")]
    fn called_methods_are_in_the_headers_slots() {
        assert_eq!(
            offset_of!(IUnknownVtbl, release) / 8,
            2,
            "IUnknown::Release"
        );
        assert_eq!(
            offset_of!(IDXGIFactory4Vtbl, release) / 8,
            2,
            "IDXGIFactory4::Release"
        );
        assert_eq!(
            offset_of!(IDXGIFactory4Vtbl, enum_adapters1) / 8,
            12,
            "IDXGIFactory4::EnumAdapters1"
        );
        assert_eq!(
            offset_of!(IDXGIFactory4Vtbl, enum_warp_adapter) / 8,
            27,
            "IDXGIFactory4::EnumWarpAdapter"
        );
        assert_eq!(
            offset_of!(IDXGIAdapter1Vtbl, check_interface_support) / 8,
            9,
            "IDXGIAdapter1::CheckInterfaceSupport"
        );
        assert_eq!(
            offset_of!(IDXGIAdapter1Vtbl, get_desc1) / 8,
            10,
            "IDXGIAdapter1::GetDesc1"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_command_queue) / 8,
            8,
            "ID3D12Device::CreateCommandQueue"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_command_allocator) / 8,
            9,
            "ID3D12Device::CreateCommandAllocator"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_graphics_pipeline_state) / 8,
            10,
            "ID3D12Device::CreateGraphicsPipelineState"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_command_list) / 8,
            12,
            "ID3D12Device::CreateCommandList"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_descriptor_heap) / 8,
            14,
            "ID3D12Device::CreateDescriptorHeap"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_root_signature) / 8,
            16,
            "ID3D12Device::CreateRootSignature"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_render_target_view) / 8,
            20,
            "ID3D12Device::CreateRenderTargetView"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_committed_resource) / 8,
            27,
            "ID3D12Device::CreateCommittedResource"
        );
        assert_eq!(
            offset_of!(ID3D12DeviceVtbl, create_fence) / 8,
            36,
            "ID3D12Device::CreateFence"
        );
        assert_eq!(
            offset_of!(ID3D12CommandQueueVtbl, execute_command_lists) / 8,
            10,
            "ID3D12CommandQueue::ExecuteCommandLists"
        );
        assert_eq!(
            offset_of!(ID3D12CommandQueueVtbl, signal) / 8,
            14,
            "ID3D12CommandQueue::Signal"
        );
        assert_eq!(
            offset_of!(ID3D12CommandAllocatorVtbl, reset) / 8,
            8,
            "ID3D12CommandAllocator::Reset"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, close) / 8,
            9,
            "ID3D12GraphicsCommandList::Close"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, reset) / 8,
            10,
            "ID3D12GraphicsCommandList::Reset"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, draw_instanced) / 8,
            12,
            "ID3D12GraphicsCommandList::DrawInstanced"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, copy_texture_region) / 8,
            16,
            "ID3D12GraphicsCommandList::CopyTextureRegion"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, ia_set_primitive_topology) / 8,
            20,
            "ID3D12GraphicsCommandList::IASetPrimitiveTopology"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, rs_set_viewports) / 8,
            21,
            "ID3D12GraphicsCommandList::RSSetViewports"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, rs_set_scissor_rects) / 8,
            22,
            "ID3D12GraphicsCommandList::RSSetScissorRects"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, resource_barrier) / 8,
            26,
            "ID3D12GraphicsCommandList::ResourceBarrier"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, set_graphics_root_signature) / 8,
            30,
            "ID3D12GraphicsCommandList::SetGraphicsRootSignature"
        );
        assert_eq!(
            offset_of!(
                ID3D12GraphicsCommandListVtbl,
                set_graphics_root32_bit_constants
            ) / 8,
            36,
            "ID3D12GraphicsCommandList::SetGraphicsRoot32BitConstants"
        );
        assert_eq!(
            offset_of!(
                ID3D12GraphicsCommandListVtbl,
                set_graphics_root_shader_resource_view
            ) / 8,
            40,
            "ID3D12GraphicsCommandList::SetGraphicsRootShaderResourceView"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, om_set_render_targets) / 8,
            46,
            "ID3D12GraphicsCommandList::OMSetRenderTargets"
        );
        assert_eq!(
            offset_of!(ID3D12GraphicsCommandListVtbl, clear_render_target_view) / 8,
            48,
            "ID3D12GraphicsCommandList::ClearRenderTargetView"
        );
        assert_eq!(
            offset_of!(ID3D12ResourceVtbl, map) / 8,
            8,
            "ID3D12Resource::Map"
        );
        assert_eq!(
            offset_of!(ID3D12ResourceVtbl, unmap) / 8,
            9,
            "ID3D12Resource::Unmap"
        );
        assert_eq!(
            offset_of!(ID3D12ResourceVtbl, get_gpu_virtual_address) / 8,
            11,
            "ID3D12Resource::GetGPUVirtualAddress"
        );
        assert_eq!(
            offset_of!(ID3D12FenceVtbl, set_event_on_completion) / 8,
            9,
            "ID3D12Fence::SetEventOnCompletion"
        );
        assert_eq!(
            offset_of!(
                ID3D12DescriptorHeapVtbl,
                get_cpu_descriptor_handle_for_heap_start
            ) / 8,
            9,
            "ID3D12DescriptorHeap::GetCPUDescriptorHandleForHeapStart"
        );
        assert_eq!(
            offset_of!(ID3D10BlobVtbl, get_buffer_pointer) / 8,
            3,
            "ID3D10Blob::GetBufferPointer"
        );
        assert_eq!(
            offset_of!(ID3D10BlobVtbl, get_buffer_size) / 8,
            4,
            "ID3D10Blob::GetBufferSize"
        );
    }

    #[test]
    fn constants_have_the_headers_values() {
        assert_eq!(
            i64::from(FEATURE_LEVEL_11_0),
            45056_i64,
            "D3D_FEATURE_LEVEL_11_0"
        );
        assert_eq!(
            i64::from(COMMAND_LIST_TYPE_DIRECT),
            0_i64,
            "D3D12_COMMAND_LIST_TYPE_DIRECT"
        );
        assert_eq!(
            i64::from(DESCRIPTOR_HEAP_TYPE_RTV),
            2_i64,
            "D3D12_DESCRIPTOR_HEAP_TYPE_RTV"
        );
        assert_eq!(
            i64::from(HEAP_TYPE_DEFAULT),
            1_i64,
            "D3D12_HEAP_TYPE_DEFAULT"
        );
        assert_eq!(i64::from(HEAP_TYPE_UPLOAD), 2_i64, "D3D12_HEAP_TYPE_UPLOAD");
        assert_eq!(
            i64::from(HEAP_TYPE_READBACK),
            3_i64,
            "D3D12_HEAP_TYPE_READBACK"
        );
        assert_eq!(
            i64::from(RESOURCE_DIMENSION_BUFFER),
            1_i64,
            "D3D12_RESOURCE_DIMENSION_BUFFER"
        );
        assert_eq!(
            i64::from(RESOURCE_DIMENSION_TEXTURE2D),
            3_i64,
            "D3D12_RESOURCE_DIMENSION_TEXTURE2D"
        );
        assert_eq!(
            i64::from(TEXTURE_LAYOUT_UNKNOWN),
            0_i64,
            "D3D12_TEXTURE_LAYOUT_UNKNOWN"
        );
        assert_eq!(
            i64::from(TEXTURE_LAYOUT_ROW_MAJOR),
            1_i64,
            "D3D12_TEXTURE_LAYOUT_ROW_MAJOR"
        );
        assert_eq!(
            i64::from(RESOURCE_FLAG_ALLOW_RENDER_TARGET),
            1_i64,
            "D3D12_RESOURCE_FLAG_ALLOW_RENDER_TARGET"
        );
        assert_eq!(
            i64::from(RESOURCE_STATE_RENDER_TARGET),
            4_i64,
            "D3D12_RESOURCE_STATE_RENDER_TARGET"
        );
        assert_eq!(
            i64::from(RESOURCE_STATE_COPY_DEST),
            1024_i64,
            "D3D12_RESOURCE_STATE_COPY_DEST"
        );
        assert_eq!(
            i64::from(RESOURCE_STATE_COPY_SOURCE),
            2048_i64,
            "D3D12_RESOURCE_STATE_COPY_SOURCE"
        );
        assert_eq!(
            i64::from(RESOURCE_STATE_GENERIC_READ),
            2755_i64,
            "D3D12_RESOURCE_STATE_GENERIC_READ"
        );
        assert_eq!(
            i64::from(RESOURCE_BARRIER_TYPE_TRANSITION),
            0_i64,
            "D3D12_RESOURCE_BARRIER_TYPE_TRANSITION"
        );
        assert_eq!(
            i64::from(RESOURCE_BARRIER_ALL_SUBRESOURCES),
            4294967295_i64,
            "D3D12_RESOURCE_BARRIER_ALL_SUBRESOURCES"
        );
        assert_eq!(
            i64::from(TEXTURE_COPY_TYPE_SUBRESOURCE_INDEX),
            0_i64,
            "D3D12_TEXTURE_COPY_TYPE_SUBRESOURCE_INDEX"
        );
        assert_eq!(
            i64::from(TEXTURE_COPY_TYPE_PLACED_FOOTPRINT),
            1_i64,
            "D3D12_TEXTURE_COPY_TYPE_PLACED_FOOTPRINT"
        );
        assert_eq!(
            i64::from(FORMAT_R8G8B8A8_UNORM),
            28_i64,
            "DXGI_FORMAT_R8G8B8A8_UNORM"
        );
        assert_eq!(i64::from(FORMAT_UNKNOWN), 0_i64, "DXGI_FORMAT_UNKNOWN");
        assert_eq!(i64::from(BLEND_ONE), 2_i64, "D3D12_BLEND_ONE");
        assert_eq!(
            i64::from(BLEND_INV_SRC_ALPHA),
            6_i64,
            "D3D12_BLEND_INV_SRC_ALPHA"
        );
        assert_eq!(i64::from(BLEND_ZERO), 1_i64, "D3D12_BLEND_ZERO");
        assert_eq!(i64::from(BLEND_OP_ADD), 1_i64, "D3D12_BLEND_OP_ADD");
        assert_eq!(i64::from(LOGIC_OP_NOOP), 4_i64, "D3D12_LOGIC_OP_NOOP");
        assert_eq!(
            i64::from(COLOR_WRITE_ENABLE_ALL),
            15_i64,
            "D3D12_COLOR_WRITE_ENABLE_ALL"
        );
        assert_eq!(i64::from(FILL_MODE_SOLID), 3_i64, "D3D12_FILL_MODE_SOLID");
        assert_eq!(i64::from(CULL_MODE_NONE), 1_i64, "D3D12_CULL_MODE_NONE");
        assert_eq!(
            i64::from(COMPARISON_FUNC_ALWAYS),
            8_i64,
            "D3D12_COMPARISON_FUNC_ALWAYS"
        );
        assert_eq!(i64::from(STENCIL_OP_KEEP), 1_i64, "D3D12_STENCIL_OP_KEEP");
        assert_eq!(
            i64::from(DEPTH_WRITE_MASK_ZERO),
            0_i64,
            "D3D12_DEPTH_WRITE_MASK_ZERO"
        );
        assert_eq!(
            i64::from(PRIMITIVE_TOPOLOGY_TYPE_TRIANGLE),
            3_i64,
            "D3D12_PRIMITIVE_TOPOLOGY_TYPE_TRIANGLE"
        );
        assert_eq!(
            i64::from(TOPOLOGY_TRIANGLE_LIST),
            4_i64,
            "D3D_PRIMITIVE_TOPOLOGY_TRIANGLELIST"
        );
        assert_eq!(
            i64::from(ROOT_PARAMETER_TYPE_32BIT_CONSTANTS),
            1_i64,
            "D3D12_ROOT_PARAMETER_TYPE_32BIT_CONSTANTS"
        );
        assert_eq!(
            i64::from(ROOT_PARAMETER_TYPE_SRV),
            3_i64,
            "D3D12_ROOT_PARAMETER_TYPE_SRV"
        );
        assert_eq!(
            i64::from(SHADER_VISIBILITY_ALL),
            0_i64,
            "D3D12_SHADER_VISIBILITY_ALL"
        );
        assert_eq!(
            i64::from(ROOT_SIGNATURE_VERSION_1),
            1_i64,
            "D3D_ROOT_SIGNATURE_VERSION_1"
        );
        assert_eq!(i64::from(FENCE_FLAG_NONE), 0_i64, "D3D12_FENCE_FLAG_NONE");
        assert_eq!(
            i64::from(TEXTURE_DATA_PITCH_ALIGNMENT),
            256_i64,
            "D3D12_TEXTURE_DATA_PITCH_ALIGNMENT"
        );
        assert_eq!(
            i64::from(ADAPTER_FLAG_SOFTWARE),
            2_i64,
            "DXGI_ADAPTER_FLAG_SOFTWARE"
        );
        assert_eq!(
            i64::from(ERROR_NOT_FOUND),
            -2005270526_i64,
            "DXGI_ERROR_NOT_FOUND"
        );
        assert_eq!(i64::from(HEAP_FLAG_NONE), 0_i64, "D3D12_HEAP_FLAG_NONE");
        assert_eq!(
            i64::from(REQ_TEXTURE2D_U_OR_V_DIMENSION),
            16384_i64,
            "D3D12_REQ_TEXTURE2D_U_OR_V_DIMENSION"
        );
        assert_eq!(
            i64::from(DEFAULT_SAMPLE_MASK),
            4294967295_i64,
            "D3D12_DEFAULT_SAMPLE_MASK"
        );
    }

    /// A GUID in the form `MIDL_INTERFACE` writes it.
    fn text(g: Guid) -> String {
        let d = g.data4;
        format!(
            "{:08x}-{:04x}-{:04x}-{:02x}{:02x}-{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
            g.data1, g.data2, g.data3, d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7]
        )
    }

    /// The identifiers, against the strings of each interface's `MIDL_INTERFACE`
    /// line (a second place the headers state them).
    #[test]
    fn interface_identifiers_are_the_headers() {
        for (iid, want) in [
            (IID_DXGI_FACTORY4, "1bc6ea02-ef36-464f-bf0c-21ca39e5168a"),
            (IID_DXGI_ADAPTER1, "29038f61-3839-4626-91fd-086879011a05"),
            (IID_DXGI_DEVICE, "54ec77fa-1377-44e6-8c32-88fd5f44c84c"),
            (IID_DEVICE, "189819f1-1db6-4b57-be54-1821339b85f7"),
            (IID_COMMAND_QUEUE, "0ec870a6-5d7e-4c22-8cfc-5baae07616ed"),
            (
                IID_COMMAND_ALLOCATOR,
                "6102dee4-af59-4b09-b999-b44d73f09b24",
            ),
            (
                IID_GRAPHICS_COMMAND_LIST,
                "5b160d0f-ac1b-4185-8ba8-b3ae42a5a455",
            ),
            (IID_FENCE, "0a753dcf-c4d8-4b91-adf6-be5a60d95a76"),
            (IID_RESOURCE, "696442be-a72e-4059-bc79-5b5c98040fad"),
            (IID_DESCRIPTOR_HEAP, "8efb471d-616c-4f49-90f7-127bb763fa51"),
            (IID_ROOT_SIGNATURE, "c54a6b66-72df-4ee8-8be5-a946a1429214"),
            (IID_PIPELINE_STATE, "765a30f3-f624-4c6f-a828-ace948622445"),
        ] {
            assert_eq!(text(iid), want);
        }
    }
}

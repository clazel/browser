//! Vulkan, for the GPU process's drawing (phase-5.md item 5.17b), on Linux.
//!
//! Safe wrappers around the Vulkan core calls that `clazel-gpu`'s Vulkan
//! backend makes: one offscreen colour target, one graphics pipeline with fixed
//! shaders, storage buffers the shaders read, and a copy of the target back to
//! memory. Each wrapper does one Vulkan operation with values `clazel-gpu` chose
//! (format, blend factors, sizes, SPIR-V), checks what the operation's valid usage
//! requires of them, and decides nothing about what is drawn.
//!
//! The functions are those `libvulkan` (the Khronos loader) exports, declared
//! here by hand from `<vulkan/vulkan_core.h>` (Vulkan-Headers 1.3.275, the
//! version Ubuntu 24.04 ships), and the structures passed to them are
//! `#[repr(C)]` declarations written from the same header. The tests at the end
//! of this file state each structure's size and the offsets read, as a C program
//! printed them from that header on aarch64 Linux (x86-64 Linux is LP64 too, with
//! the same sizes and alignments for every type used), so a declaration that
//! drifts fails a test. Citations are to the Vulkan reference
//! pages, which Khronos publishes as section 3 man pages (`man 3 vkCreateDevice`).
//!
//! # Modelling choices
//!
//! - **Vulkan 1.1, with only functions of 1.0; no extension, no layer, no
//!   allocator callback.** Every function called is in Vulkan 1.0. The instance
//!   asks for 1.1 and a device below 1.1 is refused, because the committed
//!   SPIR-V uses the `StorageBuffer` storage class
//!   (`SPV_KHR_storage_buffer_storage_class`), which a device must be 1.1 to
//!   accept without an extension (the validation layer says so of a 1.0
//!   instance). Every `pAllocator` is NULL. Nothing is presented, so there is no
//!   window-system extension; the target's pixels leave through
//!   [`Target::read_pixels`]. No function pointer is looked up, so every call is
//!   a direct foreign call.
//! - **The instance, the device and the pipeline's objects are never destroyed.**
//!   One GPU process has one of each for its whole life, and Vulkan requires
//!   every child object destroyed before its device, which a `Drop` order across
//!   safe values cannot promise. So [`Device`] and [`Pipeline`] have no `Drop`,
//!   and a handle copied into a child ([`Buffer`], [`Target`]) is valid for as
//!   long as the process runs. What a frame replaces (buffers, targets) is
//!   destroyed on `Drop`.
//! - **Every submission is waited for** (`vkQueueWaitIdle`) before the wrapper
//!   returns, so no object is in use by the GPU when safe code can next touch,
//!   rebind or drop it, and one command buffer is reused throughout.
//! - **One thread.** Every type holds a raw pointer, so none is `Send` or `Sync`,
//!   which is Vulkan's external synchronisation for the device's objects.
//! - **Memory is mapped only for the length of one copy**, at the offset the copy
//!   starts at, so no pointer arithmetic is needed: `vkMapMemory` returns the
//!   pointer to that offset, `memcpy` copies, `vkUnmapMemory` ends it. Buffers
//!   use a memory type that is host-visible and host-coherent, which every
//!   implementation has, so nothing is flushed.
//! - **`robustBufferAccess` is enabled** (every implementation supports it): a
//!   shader's read past the end of a bound buffer is then defined (zero, or a
//!   value from inside the buffer) rather than undefined. The fixed shaders bound
//!   their own reads too; this is the device's bound.
//! - **What the shaders are is not checked here** beyond the SPIR-V magic number
//!   and a length that is a multiple of four: the caller passes the SPIR-V
//!   committed in `clazel-gpu/shaders`, compiled from our own GLSL, never a
//!   page's bytes. A pipeline is fixed at: no vertex input, triangle lists, no
//!   culling, no depth, one colour attachment, storage buffers at set 0 from
//!   binding 0, and one push-constant range read by both stages.
//! - **Limits are read, not assumed.** The device's limits bound a target's side,
//!   a bound buffer's size and the push constants; a value over a limit is an
//!   error here, since Vulkan leaves it undefined.

use std::ffi::{c_char, c_void};
use std::fmt;
use std::ptr;

/// A dispatchable handle (`VK_DEFINE_HANDLE`): a pointer.
type Dispatchable = *mut c_void;
/// A non-dispatchable handle (`VK_DEFINE_NON_DISPATCHABLE_HANDLE`): on 64-bit
/// targets a pointer, on others a `uint64_t`; this file is 64-bit Linux only, and
/// a `u64` has a pointer's size, alignment and argument class there.
type Handle = u64;
/// `VkResult`.
type VkResult = i32;

const VK_SUCCESS: VkResult = 0;
const VK_INCOMPLETE: VkResult = 5;
const VK_WHOLE_SIZE: u64 = u64::MAX;

// VkStructureType.
const ST_APPLICATION_INFO: i32 = 0;
const ST_INSTANCE_CREATE_INFO: i32 = 1;
const ST_DEVICE_QUEUE_CREATE_INFO: i32 = 2;
const ST_DEVICE_CREATE_INFO: i32 = 3;
const ST_SUBMIT_INFO: i32 = 4;
const ST_MEMORY_ALLOCATE_INFO: i32 = 5;
const ST_BUFFER_CREATE_INFO: i32 = 12;
const ST_IMAGE_CREATE_INFO: i32 = 14;
const ST_IMAGE_VIEW_CREATE_INFO: i32 = 15;
const ST_SHADER_MODULE_CREATE_INFO: i32 = 16;
const ST_PIPELINE_SHADER_STAGE_CREATE_INFO: i32 = 18;
const ST_PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO: i32 = 19;
const ST_PIPELINE_INPUT_ASSEMBLY_STATE_CREATE_INFO: i32 = 20;
const ST_PIPELINE_VIEWPORT_STATE_CREATE_INFO: i32 = 22;
const ST_PIPELINE_RASTERIZATION_STATE_CREATE_INFO: i32 = 23;
const ST_PIPELINE_MULTISAMPLE_STATE_CREATE_INFO: i32 = 24;
const ST_PIPELINE_COLOR_BLEND_STATE_CREATE_INFO: i32 = 26;
const ST_PIPELINE_DYNAMIC_STATE_CREATE_INFO: i32 = 27;
const ST_GRAPHICS_PIPELINE_CREATE_INFO: i32 = 28;
const ST_PIPELINE_LAYOUT_CREATE_INFO: i32 = 30;
const ST_DESCRIPTOR_SET_LAYOUT_CREATE_INFO: i32 = 32;
const ST_DESCRIPTOR_POOL_CREATE_INFO: i32 = 33;
const ST_DESCRIPTOR_SET_ALLOCATE_INFO: i32 = 34;
const ST_WRITE_DESCRIPTOR_SET: i32 = 35;
const ST_FRAMEBUFFER_CREATE_INFO: i32 = 37;
const ST_RENDER_PASS_CREATE_INFO: i32 = 38;
const ST_COMMAND_POOL_CREATE_INFO: i32 = 39;
const ST_COMMAND_BUFFER_ALLOCATE_INFO: i32 = 40;
const ST_COMMAND_BUFFER_BEGIN_INFO: i32 = 42;
const ST_RENDER_PASS_BEGIN_INFO: i32 = 43;

/// `VK_MAKE_API_VERSION(0, 1, 1, 0)`: Vulkan 1.1 (`VK_API_VERSION_1_1`).
const API_VERSION_1_1: u32 = (1 << 22) | (1 << 12);
/// `VK_PHYSICAL_DEVICE_TYPE_CPU`.
const PHYSICAL_DEVICE_TYPE_CPU: u32 = 4;
/// `VK_QUEUE_GRAPHICS_BIT`.
const QUEUE_GRAPHICS_BIT: u32 = 1;
/// `VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT`.
const COMMAND_POOL_RESET_COMMAND_BUFFER: u32 = 2;
/// `VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT`.
const COMMAND_BUFFER_ONE_TIME_SUBMIT: u32 = 1;
/// `VK_IMAGE_TYPE_2D` and `VK_IMAGE_VIEW_TYPE_2D`.
const TYPE_2D: u32 = 1;
/// `VK_SAMPLE_COUNT_1_BIT`.
const SAMPLE_COUNT_1: u32 = 1;
/// `VK_IMAGE_USAGE_TRANSFER_SRC_BIT | VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT`.
const IMAGE_USAGE_TARGET: u32 = 0x1 | 0x10;
/// `VK_IMAGE_ASPECT_COLOR_BIT`.
const ASPECT_COLOR: u32 = 1;
/// `VK_IMAGE_LAYOUT_UNDEFINED`.
const LAYOUT_UNDEFINED: u32 = 0;
/// `VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL`.
const LAYOUT_COLOR_ATTACHMENT: u32 = 2;
/// `VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL`.
const LAYOUT_TRANSFER_SRC: u32 = 6;
/// `VK_ATTACHMENT_LOAD_OP_LOAD`.
const LOAD_OP_LOAD: u32 = 0;
/// `VK_ATTACHMENT_LOAD_OP_CLEAR`.
const LOAD_OP_CLEAR: u32 = 1;
/// `VK_ATTACHMENT_LOAD_OP_DONT_CARE`.
const LOAD_OP_DONT_CARE: u32 = 2;
/// `VK_ATTACHMENT_STORE_OP_STORE`.
const STORE_OP_STORE: u32 = 0;
/// `VK_ATTACHMENT_STORE_OP_DONT_CARE`.
const STORE_OP_DONT_CARE: u32 = 1;
/// `VK_DESCRIPTOR_TYPE_STORAGE_BUFFER`.
const DESCRIPTOR_STORAGE_BUFFER: u32 = 7;
/// `VK_SHADER_STAGE_VERTEX_BIT`.
const STAGE_VERTEX: u32 = 0x1;
/// `VK_SHADER_STAGE_FRAGMENT_BIT`.
const STAGE_FRAGMENT: u32 = 0x10;
/// `VK_PRIMITIVE_TOPOLOGY_TRIANGLE_LIST`.
const TOPOLOGY_TRIANGLE_LIST: u32 = 3;
/// `VK_COLOR_COMPONENT_{R,G,B,A}_BIT`, all four.
const COLOR_WRITE_ALL: u32 = 0xF;
/// `VK_DYNAMIC_STATE_VIEWPORT`, `VK_DYNAMIC_STATE_SCISSOR`.
const DYNAMIC_VIEWPORT_SCISSOR: [u32; 2] = [0, 1];
/// `VK_BUFFER_USAGE_TRANSFER_DST_BIT`.
const BUFFER_USAGE_TRANSFER_DST: u32 = 0x2;
/// `VK_BUFFER_USAGE_STORAGE_BUFFER_BIT`.
const BUFFER_USAGE_STORAGE: u32 = 0x20;
/// `VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT`.
const MEMORY_HOST: u32 = 0x2 | 0x4;
/// The SPIR-V magic number (SPIR-V specification, "Physical Layout").
const SPIRV_MAGIC: u32 = 0x0723_0203;
/// The shaders' entry point, NUL-terminated.
const ENTRY: &[u8; 5] = b"main\0";
/// The application's and engine's name, NUL-terminated.
const NAME: &[u8; 7] = b"clazel\0";

/// The most physical devices or queue families read.
const MAX_ENUMERATED: u32 = 64;
/// The most storage buffers a pipeline binds.
pub const MAX_STORAGE_BUFFERS: u32 = 8;
/// The largest buffer made, in bytes: 1 GiB.
pub const MAX_BUFFER: usize = 1 << 30;

/// `VkApplicationInfo`.
#[repr(C)]
struct ApplicationInfo {
    s_type: i32,
    p_next: *const c_void,
    p_application_name: *const c_char,
    application_version: u32,
    p_engine_name: *const c_char,
    engine_version: u32,
    api_version: u32,
}

/// `VkInstanceCreateInfo`.
#[repr(C)]
struct InstanceCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    p_application_info: *const ApplicationInfo,
    enabled_layer_count: u32,
    pp_enabled_layer_names: *const *const c_char,
    enabled_extension_count: u32,
    pp_enabled_extension_names: *const *const c_char,
}

/// `VkPhysicalDeviceProperties`. `limits` is `VkPhysicalDeviceLimits` as 126
/// 32-bit words (504 bytes, at offset 296) and `sparse` is
/// `VkPhysicalDeviceSparseProperties` (five `VkBool32`); `align` gives the
/// structure the 8-byte alignment its `VkDeviceSize` members give it in C.
#[repr(C)]
struct PhysicalDeviceProperties {
    api_version: u32,
    driver_version: u32,
    vendor_id: u32,
    device_id: u32,
    device_type: u32,
    device_name: [u8; 256],
    pipeline_cache_uuid: [u8; 16],
    pad: u32,
    limits: [u32; LIMITS_WORDS],
    sparse: [u32; 5],
    align: [u64; 0],
}

/// `sizeof(VkPhysicalDeviceLimits) / 4`.
const LIMITS_WORDS: usize = 126;
// Members of `VkPhysicalDeviceLimits` read here, as the index of their 32-bit
// word (byte offset / 4); the tests state the byte offsets.
const LIMIT_MAX_IMAGE_DIMENSION_2D: usize = 1;
const LIMIT_MAX_STORAGE_BUFFER_RANGE: usize = 7;
const LIMIT_MAX_PUSH_CONSTANTS_SIZE: usize = 8;
const LIMIT_MAX_VIEWPORT_WIDTH: usize = 70;
const LIMIT_MAX_VIEWPORT_HEIGHT: usize = 71;
const LIMIT_MAX_FRAMEBUFFER_WIDTH: usize = 91;
const LIMIT_MAX_FRAMEBUFFER_HEIGHT: usize = 92;

/// `VkQueueFamilyProperties`.
#[repr(C)]
#[derive(Clone, Copy)]
struct QueueFamilyProperties {
    queue_flags: u32,
    queue_count: u32,
    timestamp_valid_bits: u32,
    min_image_transfer_granularity: [u32; 3],
}

/// `VkMemoryType`.
#[repr(C)]
#[derive(Clone, Copy)]
struct MemoryType {
    property_flags: u32,
    heap_index: u32,
}

/// `VkMemoryHeap`.
#[repr(C)]
#[derive(Clone, Copy)]
struct MemoryHeap {
    size: u64,
    flags: u32,
}

/// `VkPhysicalDeviceMemoryProperties`.
#[repr(C)]
#[derive(Clone, Copy)]
struct MemoryProperties {
    memory_type_count: u32,
    memory_types: [MemoryType; 32],
    memory_heap_count: u32,
    memory_heaps: [MemoryHeap; 16],
}

/// `VkDeviceQueueCreateInfo`.
#[repr(C)]
struct DeviceQueueCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    queue_family_index: u32,
    queue_count: u32,
    p_queue_priorities: *const f32,
}

/// `VkPhysicalDeviceFeatures`: 55 `VkBool32`, the first `robustBufferAccess`.
type Features = [u32; 55];

/// `VkDeviceCreateInfo`.
#[repr(C)]
struct DeviceCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    queue_create_info_count: u32,
    p_queue_create_infos: *const DeviceQueueCreateInfo,
    enabled_layer_count: u32,
    pp_enabled_layer_names: *const *const c_char,
    enabled_extension_count: u32,
    pp_enabled_extension_names: *const *const c_char,
    p_enabled_features: *const Features,
}

/// `VkCommandPoolCreateInfo`.
#[repr(C)]
struct CommandPoolCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    queue_family_index: u32,
}

/// `VkCommandBufferAllocateInfo`.
#[repr(C)]
struct CommandBufferAllocateInfo {
    s_type: i32,
    p_next: *const c_void,
    command_pool: Handle,
    level: u32,
    command_buffer_count: u32,
}

/// `VkShaderModuleCreateInfo`.
#[repr(C)]
struct ShaderModuleCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    code_size: usize,
    p_code: *const u32,
}

/// `VkAttachmentDescription`.
#[repr(C)]
struct AttachmentDescription {
    flags: u32,
    format: u32,
    samples: u32,
    load_op: u32,
    store_op: u32,
    stencil_load_op: u32,
    stencil_store_op: u32,
    initial_layout: u32,
    final_layout: u32,
}

/// `VkAttachmentReference`.
#[repr(C)]
struct AttachmentReference {
    attachment: u32,
    layout: u32,
}

/// `VkSubpassDescription`.
#[repr(C)]
struct SubpassDescription {
    flags: u32,
    pipeline_bind_point: u32,
    input_attachment_count: u32,
    p_input_attachments: *const AttachmentReference,
    color_attachment_count: u32,
    p_color_attachments: *const AttachmentReference,
    p_resolve_attachments: *const AttachmentReference,
    p_depth_stencil_attachment: *const AttachmentReference,
    preserve_attachment_count: u32,
    p_preserve_attachments: *const u32,
}

/// `VkRenderPassCreateInfo`.
#[repr(C)]
struct RenderPassCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    attachment_count: u32,
    p_attachments: *const AttachmentDescription,
    subpass_count: u32,
    p_subpasses: *const SubpassDescription,
    dependency_count: u32,
    p_dependencies: *const c_void,
}

/// `VkDescriptorSetLayoutBinding`.
#[repr(C)]
struct DescriptorSetLayoutBinding {
    binding: u32,
    descriptor_type: u32,
    descriptor_count: u32,
    stage_flags: u32,
    p_immutable_samplers: *const Handle,
}

/// `VkDescriptorSetLayoutCreateInfo`.
#[repr(C)]
struct DescriptorSetLayoutCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    binding_count: u32,
    p_bindings: *const DescriptorSetLayoutBinding,
}

/// `VkPushConstantRange`.
#[repr(C)]
struct PushConstantRange {
    stage_flags: u32,
    offset: u32,
    size: u32,
}

/// `VkPipelineLayoutCreateInfo`.
#[repr(C)]
struct PipelineLayoutCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    set_layout_count: u32,
    p_set_layouts: *const Handle,
    push_constant_range_count: u32,
    p_push_constant_ranges: *const PushConstantRange,
}

/// `VkPipelineShaderStageCreateInfo`.
#[repr(C)]
struct PipelineShaderStageCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    stage: u32,
    module: Handle,
    p_name: *const c_char,
    p_specialization_info: *const c_void,
}

/// `VkPipelineVertexInputStateCreateInfo`.
#[repr(C)]
struct PipelineVertexInputStateCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    vertex_binding_description_count: u32,
    p_vertex_binding_descriptions: *const c_void,
    vertex_attribute_description_count: u32,
    p_vertex_attribute_descriptions: *const c_void,
}

/// `VkPipelineInputAssemblyStateCreateInfo`.
#[repr(C)]
struct PipelineInputAssemblyStateCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    topology: u32,
    primitive_restart_enable: u32,
}

/// `VkViewport`.
#[repr(C)]
struct Viewport {
    x: f32,
    y: f32,
    width: f32,
    height: f32,
    min_depth: f32,
    max_depth: f32,
}

/// `VkRect2D`: a `VkOffset2D` and a `VkExtent2D`.
#[repr(C)]
#[derive(Clone, Copy)]
struct Rect2D {
    x: i32,
    y: i32,
    width: u32,
    height: u32,
}

/// `VkPipelineViewportStateCreateInfo`.
#[repr(C)]
struct PipelineViewportStateCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    viewport_count: u32,
    p_viewports: *const Viewport,
    scissor_count: u32,
    p_scissors: *const Rect2D,
}

/// `VkPipelineRasterizationStateCreateInfo`.
#[repr(C)]
struct PipelineRasterizationStateCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    depth_clamp_enable: u32,
    rasterizer_discard_enable: u32,
    polygon_mode: u32,
    cull_mode: u32,
    front_face: u32,
    depth_bias_enable: u32,
    depth_bias_constant_factor: f32,
    depth_bias_clamp: f32,
    depth_bias_slope_factor: f32,
    line_width: f32,
}

/// `VkPipelineMultisampleStateCreateInfo`.
#[repr(C)]
struct PipelineMultisampleStateCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    rasterization_samples: u32,
    sample_shading_enable: u32,
    min_sample_shading: f32,
    p_sample_mask: *const u32,
    alpha_to_coverage_enable: u32,
    alpha_to_one_enable: u32,
}

/// `VkPipelineColorBlendAttachmentState`.
#[repr(C)]
struct PipelineColorBlendAttachmentState {
    blend_enable: u32,
    src_color_blend_factor: u32,
    dst_color_blend_factor: u32,
    color_blend_op: u32,
    src_alpha_blend_factor: u32,
    dst_alpha_blend_factor: u32,
    alpha_blend_op: u32,
    color_write_mask: u32,
}

/// `VkPipelineColorBlendStateCreateInfo`.
#[repr(C)]
struct PipelineColorBlendStateCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    logic_op_enable: u32,
    logic_op: u32,
    attachment_count: u32,
    p_attachments: *const PipelineColorBlendAttachmentState,
    blend_constants: [f32; 4],
}

/// `VkPipelineDynamicStateCreateInfo`.
#[repr(C)]
struct PipelineDynamicStateCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    dynamic_state_count: u32,
    p_dynamic_states: *const u32,
}

/// `VkGraphicsPipelineCreateInfo`.
#[repr(C)]
struct GraphicsPipelineCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    stage_count: u32,
    p_stages: *const PipelineShaderStageCreateInfo,
    p_vertex_input_state: *const PipelineVertexInputStateCreateInfo,
    p_input_assembly_state: *const PipelineInputAssemblyStateCreateInfo,
    p_tessellation_state: *const c_void,
    p_viewport_state: *const PipelineViewportStateCreateInfo,
    p_rasterization_state: *const PipelineRasterizationStateCreateInfo,
    p_multisample_state: *const PipelineMultisampleStateCreateInfo,
    p_depth_stencil_state: *const c_void,
    p_color_blend_state: *const PipelineColorBlendStateCreateInfo,
    p_dynamic_state: *const PipelineDynamicStateCreateInfo,
    layout: Handle,
    render_pass: Handle,
    subpass: u32,
    base_pipeline_handle: Handle,
    base_pipeline_index: i32,
}

/// `VkDescriptorPoolSize`.
#[repr(C)]
struct DescriptorPoolSize {
    descriptor_type: u32,
    descriptor_count: u32,
}

/// `VkDescriptorPoolCreateInfo`.
#[repr(C)]
struct DescriptorPoolCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    max_sets: u32,
    pool_size_count: u32,
    p_pool_sizes: *const DescriptorPoolSize,
}

/// `VkDescriptorSetAllocateInfo`.
#[repr(C)]
struct DescriptorSetAllocateInfo {
    s_type: i32,
    p_next: *const c_void,
    descriptor_pool: Handle,
    descriptor_set_count: u32,
    p_set_layouts: *const Handle,
}

/// `VkDescriptorBufferInfo`.
#[repr(C)]
struct DescriptorBufferInfo {
    buffer: Handle,
    offset: u64,
    range: u64,
}

/// `VkWriteDescriptorSet`.
#[repr(C)]
struct WriteDescriptorSet {
    s_type: i32,
    p_next: *const c_void,
    dst_set: Handle,
    dst_binding: u32,
    dst_array_element: u32,
    descriptor_count: u32,
    descriptor_type: u32,
    p_image_info: *const c_void,
    p_buffer_info: *const DescriptorBufferInfo,
    p_texel_buffer_view: *const Handle,
}

/// `VkImageCreateInfo`.
#[repr(C)]
struct ImageCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    image_type: u32,
    format: u32,
    extent: [u32; 3],
    mip_levels: u32,
    array_layers: u32,
    samples: u32,
    tiling: u32,
    usage: u32,
    sharing_mode: u32,
    queue_family_index_count: u32,
    p_queue_family_indices: *const u32,
    initial_layout: u32,
}

/// `VkMemoryRequirements`.
#[repr(C)]
struct MemoryRequirements {
    size: u64,
    alignment: u64,
    memory_type_bits: u32,
}

/// `VkMemoryAllocateInfo`.
#[repr(C)]
struct MemoryAllocateInfo {
    s_type: i32,
    p_next: *const c_void,
    allocation_size: u64,
    memory_type_index: u32,
}

/// `VkImageViewCreateInfo`; `components` is `VkComponentMapping` (four
/// swizzles) and `subresource_range` is `VkImageSubresourceRange` (aspect mask,
/// base mip level, level count, base array layer, layer count).
#[repr(C)]
struct ImageViewCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    image: Handle,
    view_type: u32,
    format: u32,
    components: [u32; 4],
    subresource_range: [u32; 5],
}

/// `VkFramebufferCreateInfo`.
#[repr(C)]
struct FramebufferCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    render_pass: Handle,
    attachment_count: u32,
    p_attachments: *const Handle,
    width: u32,
    height: u32,
    layers: u32,
}

/// `VkBufferCreateInfo`.
#[repr(C)]
struct BufferCreateInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    size: u64,
    usage: u32,
    sharing_mode: u32,
    queue_family_index_count: u32,
    p_queue_family_indices: *const u32,
}

/// `VkCommandBufferBeginInfo`.
#[repr(C)]
struct CommandBufferBeginInfo {
    s_type: i32,
    p_next: *const c_void,
    flags: u32,
    p_inheritance_info: *const c_void,
}

/// `VkClearValue`, a union of 16 bytes aligned to 4, as its `float32[4]`
/// member.
#[repr(C)]
struct ClearValue {
    float32: [f32; 4],
}

/// `VkRenderPassBeginInfo`.
#[repr(C)]
struct RenderPassBeginInfo {
    s_type: i32,
    p_next: *const c_void,
    render_pass: Handle,
    framebuffer: Handle,
    render_area: Rect2D,
    clear_value_count: u32,
    p_clear_values: *const ClearValue,
}

/// `VkBufferImageCopy`; `image_subresource` is `VkImageSubresourceLayers`
/// (aspect mask, mip level, base array layer, layer count).
#[repr(C)]
struct BufferImageCopy {
    buffer_offset: u64,
    buffer_row_length: u32,
    buffer_image_height: u32,
    image_subresource: [u32; 4],
    image_offset: [i32; 3],
    image_extent: [u32; 3],
}

/// `VkSubmitInfo`.
#[repr(C)]
struct SubmitInfo {
    s_type: i32,
    p_next: *const c_void,
    wait_semaphore_count: u32,
    p_wait_semaphores: *const Handle,
    p_wait_dst_stage_mask: *const u32,
    command_buffer_count: u32,
    p_command_buffers: *const Dispatchable,
    signal_semaphore_count: u32,
    p_signal_semaphores: *const Handle,
}

#[link(name = "vulkan")]
// SAFETY: man 3 vkCreateInstance, man 3 vkEnumeratePhysicalDevices, man 3
// vkGetPhysicalDeviceProperties, man 3 vkGetPhysicalDeviceQueueFamilyProperties,
// man 3 vkGetPhysicalDeviceMemoryProperties, man 3 vkCreateDevice, man 3
// vkGetDeviceQueue, man 3 vkCreateCommandPool and man 3
// vkAllocateCommandBuffers, as <vulkan/vulkan_core.h> declares them. `VKAPI_CALL`
// is empty on Linux, so the ABI is "C". `VkResult` is a C enum (`i32`); a
// dispatchable handle is a pointer; a non-dispatchable handle and `VkDeviceSize`
// are 64 bits; counts are `uint32_t`; each `p…` parameter is a pointer to the
// structure declared above under the same name, and `pAllocator` is a pointer to
// `VkAllocationCallbacks`, only ever NULL here, so declared `*const c_void`. No
// function here takes or calls a callback. libvulkan is linked by name.
unsafe extern "C" {
    fn vkCreateInstance(
        p_create_info: *const InstanceCreateInfo,
        p_allocator: *const c_void,
        p_instance: *mut Dispatchable,
    ) -> VkResult;
    fn vkEnumeratePhysicalDevices(
        instance: Dispatchable,
        p_count: *mut u32,
        p_devices: *mut Dispatchable,
    ) -> VkResult;
    fn vkGetPhysicalDeviceProperties(
        physical: Dispatchable,
        p_properties: *mut PhysicalDeviceProperties,
    );
    fn vkGetPhysicalDeviceQueueFamilyProperties(
        physical: Dispatchable,
        p_count: *mut u32,
        p_properties: *mut QueueFamilyProperties,
    );
    fn vkGetPhysicalDeviceMemoryProperties(
        physical: Dispatchable,
        p_properties: *mut MemoryProperties,
    );
    fn vkCreateDevice(
        physical: Dispatchable,
        p_create_info: *const DeviceCreateInfo,
        p_allocator: *const c_void,
        p_device: *mut Dispatchable,
    ) -> VkResult;
    fn vkGetDeviceQueue(device: Dispatchable, family: u32, index: u32, p_queue: *mut Dispatchable);
    fn vkCreateCommandPool(
        device: Dispatchable,
        p_create_info: *const CommandPoolCreateInfo,
        p_allocator: *const c_void,
        p_pool: *mut Handle,
    ) -> VkResult;
    fn vkAllocateCommandBuffers(
        device: Dispatchable,
        p_allocate_info: *const CommandBufferAllocateInfo,
        p_command_buffers: *mut Dispatchable,
    ) -> VkResult;
}

#[link(name = "vulkan")]
// SAFETY: man 3 vkCreateShaderModule, man 3 vkCreateRenderPass, man 3
// vkCreateDescriptorSetLayout, man 3 vkCreatePipelineLayout, man 3
// vkCreateGraphicsPipelines, man 3 vkCreateDescriptorPool, man 3
// vkAllocateDescriptorSets and man 3 vkUpdateDescriptorSets, as
// <vulkan/vulkan_core.h> declares them, with the types of the block above.
// `vkCreateGraphicsPipelines` takes a `VkPipelineCache` (a non-dispatchable
// handle, only ever `VK_NULL_HANDLE` here) and a count of create infos;
// `vkUpdateDescriptorSets` takes a count and array of writes and a count and
// array of copies (`VkCopyDescriptorSet`, only ever zero and NULL here, so
// declared `*const c_void`). libvulkan is linked by name.
unsafe extern "C" {
    fn vkCreateShaderModule(
        device: Dispatchable,
        p_create_info: *const ShaderModuleCreateInfo,
        p_allocator: *const c_void,
        p_module: *mut Handle,
    ) -> VkResult;
    fn vkCreateRenderPass(
        device: Dispatchable,
        p_create_info: *const RenderPassCreateInfo,
        p_allocator: *const c_void,
        p_render_pass: *mut Handle,
    ) -> VkResult;
    fn vkCreateDescriptorSetLayout(
        device: Dispatchable,
        p_create_info: *const DescriptorSetLayoutCreateInfo,
        p_allocator: *const c_void,
        p_layout: *mut Handle,
    ) -> VkResult;
    fn vkCreatePipelineLayout(
        device: Dispatchable,
        p_create_info: *const PipelineLayoutCreateInfo,
        p_allocator: *const c_void,
        p_layout: *mut Handle,
    ) -> VkResult;
    fn vkCreateGraphicsPipelines(
        device: Dispatchable,
        cache: Handle,
        count: u32,
        p_create_infos: *const GraphicsPipelineCreateInfo,
        p_allocator: *const c_void,
        p_pipelines: *mut Handle,
    ) -> VkResult;
    fn vkCreateDescriptorPool(
        device: Dispatchable,
        p_create_info: *const DescriptorPoolCreateInfo,
        p_allocator: *const c_void,
        p_pool: *mut Handle,
    ) -> VkResult;
    fn vkAllocateDescriptorSets(
        device: Dispatchable,
        p_allocate_info: *const DescriptorSetAllocateInfo,
        p_sets: *mut Handle,
    ) -> VkResult;
    fn vkUpdateDescriptorSets(
        device: Dispatchable,
        write_count: u32,
        p_writes: *const WriteDescriptorSet,
        copy_count: u32,
        p_copies: *const c_void,
    );
}

#[link(name = "vulkan")]
// SAFETY: man 3 vkCreateImage, man 3 vkDestroyImage, man 3
// vkGetImageMemoryRequirements, man 3 vkAllocateMemory, man 3 vkFreeMemory, man 3
// vkBindImageMemory, man 3 vkCreateImageView, man 3 vkDestroyImageView, man 3
// vkCreateFramebuffer, man 3 vkDestroyFramebuffer, man 3 vkCreateBuffer, man 3
// vkDestroyBuffer, man 3 vkGetBufferMemoryRequirements, man 3
// vkBindBufferMemory, man 3 vkMapMemory and man 3 vkUnmapMemory, as
// <vulkan/vulkan_core.h> declares them, with the types of the first block.
// `vkMapMemory` takes an offset and a size (`VkDeviceSize`), flags
// (`VkMemoryMapFlags`, a `uint32_t`) and `void **ppData`. libvulkan is linked by
// name.
unsafe extern "C" {
    fn vkCreateImage(
        device: Dispatchable,
        p_create_info: *const ImageCreateInfo,
        p_allocator: *const c_void,
        p_image: *mut Handle,
    ) -> VkResult;
    fn vkDestroyImage(device: Dispatchable, image: Handle, p_allocator: *const c_void);
    fn vkGetImageMemoryRequirements(
        device: Dispatchable,
        image: Handle,
        p_requirements: *mut MemoryRequirements,
    );
    fn vkAllocateMemory(
        device: Dispatchable,
        p_allocate_info: *const MemoryAllocateInfo,
        p_allocator: *const c_void,
        p_memory: *mut Handle,
    ) -> VkResult;
    fn vkFreeMemory(device: Dispatchable, memory: Handle, p_allocator: *const c_void);
    fn vkBindImageMemory(
        device: Dispatchable,
        image: Handle,
        memory: Handle,
        offset: u64,
    ) -> VkResult;
    fn vkCreateImageView(
        device: Dispatchable,
        p_create_info: *const ImageViewCreateInfo,
        p_allocator: *const c_void,
        p_view: *mut Handle,
    ) -> VkResult;
    fn vkDestroyImageView(device: Dispatchable, view: Handle, p_allocator: *const c_void);
    fn vkCreateFramebuffer(
        device: Dispatchable,
        p_create_info: *const FramebufferCreateInfo,
        p_allocator: *const c_void,
        p_framebuffer: *mut Handle,
    ) -> VkResult;
    fn vkDestroyFramebuffer(device: Dispatchable, framebuffer: Handle, p_allocator: *const c_void);
    fn vkCreateBuffer(
        device: Dispatchable,
        p_create_info: *const BufferCreateInfo,
        p_allocator: *const c_void,
        p_buffer: *mut Handle,
    ) -> VkResult;
    fn vkDestroyBuffer(device: Dispatchable, buffer: Handle, p_allocator: *const c_void);
    fn vkGetBufferMemoryRequirements(
        device: Dispatchable,
        buffer: Handle,
        p_requirements: *mut MemoryRequirements,
    );
    fn vkBindBufferMemory(
        device: Dispatchable,
        buffer: Handle,
        memory: Handle,
        offset: u64,
    ) -> VkResult;
    fn vkMapMemory(
        device: Dispatchable,
        memory: Handle,
        offset: u64,
        size: u64,
        flags: u32,
        pp_data: *mut *mut c_void,
    ) -> VkResult;
    fn vkUnmapMemory(device: Dispatchable, memory: Handle);
}

#[link(name = "vulkan")]
// SAFETY: man 3 vkBeginCommandBuffer, man 3 vkEndCommandBuffer, man 3
// vkCmdBeginRenderPass, man 3 vkCmdEndRenderPass, man 3 vkCmdBindPipeline, man 3
// vkCmdBindDescriptorSets, man 3 vkCmdPushConstants, man 3 vkCmdSetViewport, man 3
// vkCmdSetScissor, man 3 vkCmdDraw, man 3 vkCmdCopyImageToBuffer, man 3
// vkQueueSubmit and man 3 vkQueueWaitIdle, as <vulkan/vulkan_core.h> declares
// them, with the types of the first block. Enumerations (`VkSubpassContents`,
// `VkPipelineBindPoint`, `VkImageLayout`) and flag sets (`VkShaderStageFlags`)
// are 32 bits; `vkQueueSubmit` takes a `VkFence` (a non-dispatchable handle, only
// ever `VK_NULL_HANDLE` here). libvulkan is linked by name.
unsafe extern "C" {
    fn vkBeginCommandBuffer(
        cb: Dispatchable,
        p_begin_info: *const CommandBufferBeginInfo,
    ) -> VkResult;
    fn vkEndCommandBuffer(cb: Dispatchable) -> VkResult;
    fn vkCmdBeginRenderPass(cb: Dispatchable, p_begin: *const RenderPassBeginInfo, contents: u32);
    fn vkCmdEndRenderPass(cb: Dispatchable);
    fn vkCmdBindPipeline(cb: Dispatchable, bind_point: u32, pipeline: Handle);
    fn vkCmdBindDescriptorSets(
        cb: Dispatchable,
        bind_point: u32,
        layout: Handle,
        first_set: u32,
        set_count: u32,
        p_sets: *const Handle,
        dynamic_offset_count: u32,
        p_dynamic_offsets: *const u32,
    );
    fn vkCmdPushConstants(
        cb: Dispatchable,
        layout: Handle,
        stage_flags: u32,
        offset: u32,
        size: u32,
        p_values: *const c_void,
    );
    fn vkCmdSetViewport(cb: Dispatchable, first: u32, count: u32, p_viewports: *const Viewport);
    fn vkCmdSetScissor(cb: Dispatchable, first: u32, count: u32, p_scissors: *const Rect2D);
    fn vkCmdDraw(
        cb: Dispatchable,
        vertex_count: u32,
        instance_count: u32,
        first_vertex: u32,
        first_instance: u32,
    );
    fn vkCmdCopyImageToBuffer(
        cb: Dispatchable,
        image: Handle,
        layout: u32,
        buffer: Handle,
        region_count: u32,
        p_regions: *const BufferImageCopy,
    );
    fn vkQueueSubmit(
        queue: Dispatchable,
        count: u32,
        p_submits: *const SubmitInfo,
        fence: Handle,
    ) -> VkResult;
    fn vkQueueWaitIdle(queue: Dispatchable) -> VkResult;
}

/// A Vulkan call failed, or a value was refused before the call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VulkanError {
    /// The call or the check.
    pub what: &'static str,
    /// The `VkResult`, or 0 for a check of ours.
    pub code: i64,
}

impl fmt::Display for VulkanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({})", self.what, self.code)
    }
}

impl std::error::Error for VulkanError {}

fn refused(what: &'static str) -> VulkanError {
    VulkanError { what, code: 0 }
}

/// `Ok` for `VK_SUCCESS`, else the code under the call's name.
fn check(code: VkResult, what: &'static str) -> Result<(), VulkanError> {
    if code == VK_SUCCESS {
        Ok(())
    } else {
        Err(VulkanError {
            what,
            code: i64::from(code),
        })
    }
}

/// A Vulkan instance: the loader, with no layer and no extension.
#[derive(Debug)]
pub struct Instance {
    instance: Dispatchable,
}

/// One physical device, as `VkPhysicalDeviceProperties` describes it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdapterInfo {
    /// `vendorID`: the PCI vendor id, or a Khronos vendor id (Mesa's is 0x10005).
    pub vendor: u32,
    /// `deviceID`.
    pub device: u32,
    /// `driverVersion`, encoded as the vendor chose.
    pub driver_version: u32,
    /// `apiVersion`.
    pub api_version: u32,
    /// `deviceType` is `VK_PHYSICAL_DEVICE_TYPE_CPU`: a software driver.
    pub cpu: bool,
    /// `deviceName`, up to its NUL, lossily as UTF-8.
    pub name: String,
}

/// A physical device of an [`Instance`], with what was read of it.
#[derive(Debug, Clone)]
pub struct Adapter {
    physical: Dispatchable,
    /// What the device says it is.
    pub info: AdapterInfo,
    limits: Limits,
}

/// The limits this file checks against (`VkPhysicalDeviceLimits`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Limits {
    max_side: u32,
    max_storage_buffer_range: u32,
    max_push_constants_size: u32,
}

impl Instance {
    /// `vkCreateInstance` for Vulkan 1.1 with no layer and no extension. A loader
    /// that only knows 1.0 fails with `VK_ERROR_INCOMPATIBLE_DRIVER`.
    pub fn new() -> Result<Instance, VulkanError> {
        let name: *const c_char = NAME.as_ptr().cast();
        let app = ApplicationInfo {
            s_type: ST_APPLICATION_INFO,
            p_next: ptr::null(),
            p_application_name: name,
            application_version: 0,
            p_engine_name: name,
            engine_version: 0,
            api_version: API_VERSION_1_1,
        };
        let info = InstanceCreateInfo {
            s_type: ST_INSTANCE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            p_application_info: &raw const app,
            enabled_layer_count: 0,
            pp_enabled_layer_names: ptr::null(),
            enabled_extension_count: 0,
            pp_enabled_extension_names: ptr::null(),
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let mut instance: Dispatchable = ptr::null_mut();
        let out = &raw mut instance;
        // SAFETY: man 3 vkCreateInstance: `pCreateInfo` points to a valid
        // `VkInstanceCreateInfo` (`info`, a live local of the declaration above,
        // with `sType` set, `pNext` NULL, flags 0, no layers and no extensions,
        // and `pApplicationInfo` pointing to the live local `app`, whose two
        // names point to the NUL-terminated static `NAME` and whose `apiVersion`
        // is 1.1); `pAllocator` is NULL; `pInstance` points to the live local
        // `instance`, which the call writes a handle to on success. The call only
        // reads the structures and keeps no pointer to them.
        let rc = unsafe { vkCreateInstance(info_ptr, no_allocator, out) };
        check(rc, "vkCreateInstance")?;
        if instance.is_null() {
            return Err(refused("vkCreateInstance returned no instance"));
        }
        Ok(Instance { instance })
    }

    /// `vkEnumeratePhysicalDevices`, then each device's properties, in the
    /// loader's order; at most 64.
    pub fn adapters(&self) -> Result<Vec<Adapter>, VulkanError> {
        let instance = self.instance;
        let mut count: u32 = 0;
        let count_ptr = &raw mut count;
        let no_devices: *mut Dispatchable = ptr::null_mut();
        // SAFETY: man 3 vkEnumeratePhysicalDevices: `instance` is a valid
        // instance (made by `Instance::new`, never destroyed); with
        // `pPhysicalDevices` NULL the call writes the number of devices to
        // `pPhysicalDeviceCount`, which points to the live local `count`.
        let rc = unsafe { vkEnumeratePhysicalDevices(instance, count_ptr, no_devices) };
        check(rc, "vkEnumeratePhysicalDevices")?;
        count = count.min(MAX_ENUMERATED);
        let capacity = usize::try_from(count).map_err(|_| refused("device count"))?;
        let mut devices: Vec<Dispatchable> = vec![ptr::null_mut(); capacity];
        if devices.is_empty() {
            return Ok(Vec::new());
        }
        let devices_ptr = devices.as_mut_ptr();
        let count_ptr = &raw mut count;
        // SAFETY: man 3 vkEnumeratePhysicalDevices: `instance` is valid as
        // above; `pPhysicalDeviceCount` points to the live local `count`, which
        // holds the number of elements `pPhysicalDevices` points to (`devices`
        // has exactly `count` initialised elements and is not moved or dropped
        // before the call returns); the call writes at most that many handles and
        // sets `count` to how many it wrote, returning `VK_INCOMPLETE` if there
        // were more.
        let rc = unsafe { vkEnumeratePhysicalDevices(instance, count_ptr, devices_ptr) };
        if rc != VK_INCOMPLETE {
            check(rc, "vkEnumeratePhysicalDevices")?;
        }
        let written = usize::try_from(count).map_err(|_| refused("device count"))?;
        devices
            .iter()
            .take(written)
            .filter(|d| !d.is_null())
            .map(|physical| Ok(properties_of(*physical)))
            .collect()
    }

    /// `vkCreateDevice` on `adapter` with one queue of its first graphics queue
    /// family and `robustBufferAccess`, then that queue, a command pool and one
    /// command buffer. A device whose `apiVersion` is below 1.1 is refused.
    pub fn open(&self, adapter: &Adapter) -> Result<Device, VulkanError> {
        if adapter.info.api_version < API_VERSION_1_1 {
            return Err(refused("a device of Vulkan 1.1 or later"));
        }
        let physical = adapter.physical;
        let family = graphics_family(physical)?;
        let memory = memory_properties_of(physical);
        let priority: f32 = 1.0;
        let queue_info = DeviceQueueCreateInfo {
            s_type: ST_DEVICE_QUEUE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            queue_family_index: family,
            queue_count: 1,
            p_queue_priorities: &raw const priority,
        };
        let mut features: Features = [0; 55];
        if let Some(robust) = features.first_mut() {
            *robust = 1;
        }
        let info = DeviceCreateInfo {
            s_type: ST_DEVICE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            queue_create_info_count: 1,
            p_queue_create_infos: &raw const queue_info,
            enabled_layer_count: 0,
            pp_enabled_layer_names: ptr::null(),
            enabled_extension_count: 0,
            pp_enabled_extension_names: ptr::null(),
            p_enabled_features: &raw const features,
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let mut device: Dispatchable = ptr::null_mut();
        let out = &raw mut device;
        // SAFETY: man 3 vkCreateDevice: `physicalDevice` is a handle
        // `vkEnumeratePhysicalDevices` returned for this instance, which is never
        // destroyed; `pCreateInfo` points to the live local `info`, a valid
        // `VkDeviceCreateInfo`: one `VkDeviceQueueCreateInfo` (the live local
        // `queue_info`) naming a queue family index below the device's family
        // count with at least one queue (`graphics_family` checked both), one
        // queue, and a priority (the live local `priority`, 1.0, within 0 to 1);
        // no layers or extensions; and `pEnabledFeatures` pointing to the live
        // local `features`, 55 `VkBool32` with only `robustBufferAccess` set,
        // which every implementation supports. `pAllocator` is NULL and `pDevice`
        // points to the live local `device`.
        let rc = unsafe { vkCreateDevice(physical, info_ptr, no_allocator, out) };
        check(rc, "vkCreateDevice")?;
        if device.is_null() {
            return Err(refused("vkCreateDevice returned no device"));
        }
        let mut queue: Dispatchable = ptr::null_mut();
        let queue_out = &raw mut queue;
        let first: u32 = 0;
        // SAFETY: man 3 vkGetDeviceQueue: `device` was just created;
        // `queueFamilyIndex` is the family the device was created with and
        // `queueIndex` 0 is below its one queue; `pQueue` points to the live
        // local `queue`.
        unsafe { vkGetDeviceQueue(device, family, first, queue_out) };
        if queue.is_null() {
            return Err(refused("vkGetDeviceQueue returned no queue"));
        }
        let pool_info = CommandPoolCreateInfo {
            s_type: ST_COMMAND_POOL_CREATE_INFO,
            p_next: ptr::null(),
            flags: COMMAND_POOL_RESET_COMMAND_BUFFER,
            queue_family_index: family,
        };
        let pool_info_ptr = &raw const pool_info;
        let mut pool: Handle = 0;
        let pool_out = &raw mut pool;
        // SAFETY: man 3 vkCreateCommandPool: `device` is valid; `pCreateInfo`
        // points to the live local `pool_info`, a valid
        // `VkCommandPoolCreateInfo` (the reset flag, and the queue family the
        // device was created with); `pAllocator` is NULL; `pCommandPool` points
        // to the live local `pool`.
        let rc = unsafe { vkCreateCommandPool(device, pool_info_ptr, no_allocator, pool_out) };
        check(rc, "vkCreateCommandPool")?;
        let cb_info = CommandBufferAllocateInfo {
            s_type: ST_COMMAND_BUFFER_ALLOCATE_INFO,
            p_next: ptr::null(),
            command_pool: pool,
            level: 0,
            command_buffer_count: 1,
        };
        let cb_info_ptr = &raw const cb_info;
        let mut cb: Dispatchable = ptr::null_mut();
        let cb_out = &raw mut cb;
        // SAFETY: man 3 vkAllocateCommandBuffers: `device` is valid;
        // `pAllocateInfo` points to the live local `cb_info`, a valid
        // `VkCommandBufferAllocateInfo` (the pool just created on this device,
        // `VK_COMMAND_BUFFER_LEVEL_PRIMARY` (0), a count of 1);
        // `pCommandBuffers` points to the live local `cb`, room for the one
        // handle asked for.
        let rc = unsafe { vkAllocateCommandBuffers(device, cb_info_ptr, cb_out) };
        check(rc, "vkAllocateCommandBuffers")?;
        if cb.is_null() {
            return Err(refused("vkAllocateCommandBuffers returned no buffer"));
        }
        Ok(Device {
            device,
            queue,
            cb,
            memory,
            limits: adapter.limits,
        })
    }
}

/// `vkGetPhysicalDeviceProperties` for `physical`.
fn properties_of(physical: Dispatchable) -> Adapter {
    let mut p = PhysicalDeviceProperties {
        api_version: 0,
        driver_version: 0,
        vendor_id: 0,
        device_id: 0,
        device_type: 0,
        device_name: [0; 256],
        pipeline_cache_uuid: [0; 16],
        pad: 0,
        limits: [0; LIMITS_WORDS],
        sparse: [0; 5],
        align: [],
    };
    let out = &raw mut p;
    // SAFETY: man 3 vkGetPhysicalDeviceProperties: `physicalDevice` is a handle
    // `vkEnumeratePhysicalDevices` returned for an instance that is never
    // destroyed; `pProperties` points to the live local `p`, which has the size
    // and alignment of `VkPhysicalDeviceProperties` (824 bytes, 8; the tests
    // state both), every bit pattern of which is valid for the integer and byte
    // fields declared; the call fills it.
    unsafe { vkGetPhysicalDeviceProperties(physical, out) };
    let limit = |word: usize| p.limits.get(word).copied().unwrap_or(0);
    let max_side = limit(LIMIT_MAX_IMAGE_DIMENSION_2D)
        .min(limit(LIMIT_MAX_VIEWPORT_WIDTH))
        .min(limit(LIMIT_MAX_VIEWPORT_HEIGHT))
        .min(limit(LIMIT_MAX_FRAMEBUFFER_WIDTH))
        .min(limit(LIMIT_MAX_FRAMEBUFFER_HEIGHT));
    let name_len = p
        .device_name
        .iter()
        .position(|b| *b == 0)
        .unwrap_or(p.device_name.len());
    let name = String::from_utf8_lossy(p.device_name.get(..name_len).unwrap_or(&[])).into_owned();
    Adapter {
        physical,
        info: AdapterInfo {
            vendor: p.vendor_id,
            device: p.device_id,
            driver_version: p.driver_version,
            api_version: p.api_version,
            cpu: p.device_type == PHYSICAL_DEVICE_TYPE_CPU,
            name,
        },
        limits: Limits {
            max_side,
            max_storage_buffer_range: limit(LIMIT_MAX_STORAGE_BUFFER_RANGE),
            max_push_constants_size: limit(LIMIT_MAX_PUSH_CONSTANTS_SIZE),
        },
    }
}

/// The first queue family of `physical` with `VK_QUEUE_GRAPHICS_BIT` and at
/// least one queue.
fn graphics_family(physical: Dispatchable) -> Result<u32, VulkanError> {
    let mut count: u32 = 0;
    let count_ptr = &raw mut count;
    let none: *mut QueueFamilyProperties = ptr::null_mut();
    // SAFETY: man 3 vkGetPhysicalDeviceQueueFamilyProperties: `physicalDevice`
    // is a handle `vkEnumeratePhysicalDevices` returned for an instance that is
    // never destroyed; with `pQueueFamilyProperties` NULL the call writes the
    // number of families to `pQueueFamilyPropertyCount`, the live local `count`.
    unsafe { vkGetPhysicalDeviceQueueFamilyProperties(physical, count_ptr, none) };
    count = count.min(MAX_ENUMERATED);
    let capacity = usize::try_from(count).map_err(|_| refused("queue family count"))?;
    let empty = QueueFamilyProperties {
        queue_flags: 0,
        queue_count: 0,
        timestamp_valid_bits: 0,
        min_image_transfer_granularity: [0; 3],
    };
    let mut families = vec![empty; capacity];
    if families.is_empty() {
        return Err(refused("no queue family"));
    }
    let families_ptr = families.as_mut_ptr();
    let count_ptr = &raw mut count;
    // SAFETY: man 3 vkGetPhysicalDeviceQueueFamilyProperties: `physicalDevice`
    // is valid as above; `pQueueFamilyPropertyCount` points to the live local
    // `count`, the number of elements `pQueueFamilyProperties` points to
    // (`families` has exactly `count` initialised `VkQueueFamilyProperties` and
    // is not moved or dropped before the call returns); the call writes at most
    // that many and sets `count` to how many it wrote.
    unsafe { vkGetPhysicalDeviceQueueFamilyProperties(physical, count_ptr, families_ptr) };
    let written = usize::try_from(count).map_err(|_| refused("queue family count"))?;
    let at = families
        .iter()
        .take(written)
        .position(|f| f.queue_flags & QUEUE_GRAPHICS_BIT != 0 && f.queue_count > 0)
        .ok_or(refused("no graphics queue family"))?;
    u32::try_from(at).map_err(|_| refused("queue family index"))
}

/// `vkGetPhysicalDeviceMemoryProperties` for `physical`.
fn memory_properties_of(physical: Dispatchable) -> MemoryProperties {
    let no_type = MemoryType {
        property_flags: 0,
        heap_index: 0,
    };
    let no_heap = MemoryHeap { size: 0, flags: 0 };
    let mut m = MemoryProperties {
        memory_type_count: 0,
        memory_types: [no_type; 32],
        memory_heap_count: 0,
        memory_heaps: [no_heap; 16],
    };
    let out = &raw mut m;
    // SAFETY: man 3 vkGetPhysicalDeviceMemoryProperties: `physicalDevice` is a
    // handle `vkEnumeratePhysicalDevices` returned for an instance that is never
    // destroyed; `pMemoryProperties` points to the live local `m`, which has the
    // layout of `VkPhysicalDeviceMemoryProperties` (520 bytes; the tests state
    // it) and only integer fields; the call fills it.
    unsafe { vkGetPhysicalDeviceMemoryProperties(physical, out) };
    m
}

/// A logical device with its one queue and one command buffer. Never destroyed
/// (see the module documentation).
pub struct Device {
    device: Dispatchable,
    queue: Dispatchable,
    cb: Dispatchable,
    memory: MemoryProperties,
    limits: Limits,
}

impl fmt::Debug for Device {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Device")
            .field("limits", &self.limits)
            .finish_non_exhaustive()
    }
}

/// What a [`Buffer`] is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BufferUse {
    /// A storage buffer the shaders read (`VK_BUFFER_USAGE_STORAGE_BUFFER_BIT`).
    Storage,
    /// The destination of [`Target::read_pixels`]'s copy
    /// (`VK_BUFFER_USAGE_TRANSFER_DST_BIT`).
    Readback,
}

/// A buffer with its own host-visible, host-coherent memory. Dropping it
/// destroys both.
#[derive(Debug)]
pub struct Buffer {
    device: Dispatchable,
    buffer: Handle,
    memory: Handle,
    len: usize,
    usage: BufferUse,
}

impl Device {
    /// The largest side a [`Target`] may have on this device: the least of
    /// `maxImageDimension2D`, `maxViewportDimensions` and
    /// `maxFramebufferWidth`/`Height`.
    pub fn max_target_side(&self) -> u32 {
        self.limits.max_side
    }

    /// The index of a memory type allowed by `type_bits` with every flag of
    /// `flags`.
    fn memory_type(&self, type_bits: u32, flags: u32) -> Option<u32> {
        let count = usize::try_from(self.memory.memory_type_count.min(32)).ok()?;
        self.memory
            .memory_types
            .iter()
            .take(count)
            .enumerate()
            .find(|(i, t)| {
                let allowed = u32::try_from(*i)
                    .ok()
                    .and_then(|i| 1u32.checked_shl(i))
                    .is_some_and(|bit| type_bits & bit != 0);
                allowed && t.property_flags & flags == flags
            })
            .and_then(|(i, _)| u32::try_from(i).ok())
    }

    /// `vkAllocateMemory` of `size` bytes of memory type `index`.
    fn allocate(&self, size: u64, index: u32) -> Result<Handle, VulkanError> {
        let device = self.device;
        let info = MemoryAllocateInfo {
            s_type: ST_MEMORY_ALLOCATE_INFO,
            p_next: ptr::null(),
            allocation_size: size,
            memory_type_index: index,
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let mut memory: Handle = 0;
        let out = &raw mut memory;
        // SAFETY: man 3 vkAllocateMemory: `device` is valid (never destroyed);
        // `pAllocateInfo` points to the live local `info`, a valid
        // `VkMemoryAllocateInfo`: `allocationSize` is the non-zero size
        // `vkGet…MemoryRequirements` returned and `memoryTypeIndex` is below the
        // device's `memoryTypeCount` (`memory_type` only returns such an index);
        // `pAllocator` is NULL; `pMemory` points to the live local `memory`. A
        // size over the heap's fails with an error code.
        let rc = unsafe { vkAllocateMemory(device, info_ptr, no_allocator, out) };
        check(rc, "vkAllocateMemory")?;
        Ok(memory)
    }

    /// A buffer of `len` bytes (1 to [`MAX_BUFFER`]), contents undefined.
    pub fn new_buffer(&self, len: usize, usage: BufferUse) -> Result<Buffer, VulkanError> {
        if len == 0 || len > MAX_BUFFER {
            return Err(refused("a buffer of 1 byte to 1 GiB"));
        }
        let size = u64::try_from(len).map_err(|_| refused("buffer length"))?;
        let device = self.device;
        let info = BufferCreateInfo {
            s_type: ST_BUFFER_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            size,
            usage: match usage {
                BufferUse::Storage => BUFFER_USAGE_STORAGE,
                BufferUse::Readback => BUFFER_USAGE_TRANSFER_DST,
            },
            sharing_mode: 0,
            queue_family_index_count: 0,
            p_queue_family_indices: ptr::null(),
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let mut buffer: Handle = 0;
        let out = &raw mut buffer;
        // SAFETY: man 3 vkCreateBuffer: `device` is valid; `pCreateInfo` points
        // to the live local `info`, a valid `VkBufferCreateInfo`: flags 0, a
        // size above 0, one core usage bit, `VK_SHARING_MODE_EXCLUSIVE` (0) with
        // no queue family list; `pAllocator` is NULL; `pBuffer` points to the
        // live local `buffer`.
        let rc = unsafe { vkCreateBuffer(device, info_ptr, no_allocator, out) };
        check(rc, "vkCreateBuffer")?;
        // From here the buffer is owned by `made`, whose `Drop` destroys it and
        // frees `memory` if it is not 0.
        let mut made = Buffer {
            device,
            buffer,
            memory: 0,
            len,
            usage,
        };
        let mut req = MemoryRequirements {
            size: 0,
            alignment: 0,
            memory_type_bits: 0,
        };
        let req_out = &raw mut req;
        // SAFETY: man 3 vkGetBufferMemoryRequirements: `device` is valid and
        // `buffer` was just created on it; `pMemoryRequirements` points to the
        // live local `req`, which the call fills.
        unsafe { vkGetBufferMemoryRequirements(device, buffer, req_out) };
        let index = self
            .memory_type(req.memory_type_bits, MEMORY_HOST)
            .ok_or(refused("no host-visible, host-coherent memory type"))?;
        made.memory = self.allocate(req.size, index)?;
        let memory = made.memory;
        let offset: u64 = 0;
        // SAFETY: man 3 vkBindBufferMemory: `device` is valid; `buffer` was
        // created on it and has no memory bound yet; `memory` was just allocated
        // on it with the size and a memory type from the buffer's own
        // requirements, so it is large enough and of an allowed type; offset 0
        // meets every alignment.
        let rc = unsafe { vkBindBufferMemory(device, buffer, memory, offset) };
        check(rc, "vkBindBufferMemory")?;
        Ok(made)
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

    /// Map `len` bytes at `offset`; the pointer is to the first of them.
    fn map(&self, offset: usize, len: usize) -> Result<*mut c_void, VulkanError> {
        let end = offset.checked_add(len).ok_or(refused("a range"))?;
        if len == 0 || end > self.len {
            return Err(refused("a range inside the buffer"));
        }
        let (device, memory) = (self.device, self.memory);
        let offset = u64::try_from(offset).map_err(|_| refused("offset"))?;
        let size = u64::try_from(len).map_err(|_| refused("length"))?;
        let flags: u32 = 0;
        let mut data: *mut c_void = ptr::null_mut();
        let out = &raw mut data;
        // SAFETY: man 3 vkMapMemory: `device` is valid; `memory` was allocated
        // on it from a host-visible memory type (`new_buffer` chose one) and is
        // not mapped (every mapping this file makes is ended before its function
        // returns, and `Buffer` is not `Sync`); `offset` is below the
        // allocation's size and `offset + size` is at most it (the allocation is
        // at least the buffer's length, and the range was checked against that
        // above); `size` is above 0; flags are 0; `ppData` points to the live
        // local `data`.
        let rc = unsafe { vkMapMemory(device, memory, offset, size, flags, out) };
        check(rc, "vkMapMemory")?;
        if data.is_null() {
            self.unmap();
            return Err(refused("vkMapMemory returned no pointer"));
        }
        Ok(data)
    }

    fn unmap(&self) {
        let (device, memory) = (self.device, self.memory);
        // SAFETY: man 3 vkUnmapMemory: `device` is valid and `memory` is
        // currently mapped (`map` succeeded and nothing has unmapped it since).
        unsafe { vkUnmapMemory(device, memory) };
    }

    /// Copy `bytes` into the buffer at `offset`. The range must lie inside it and
    /// not be empty.
    pub fn write(&self, offset: usize, bytes: &[u8]) -> Result<(), VulkanError> {
        let len = bytes.len();
        let dst = self.map(offset, len)?;
        let src: *const c_void = bytes.as_ptr().cast();
        // SAFETY: man 3 memcpy: copies `n` bytes from `src` to `dest`, which
        // must not overlap; `libc::memcpy(*mut c_void, *const c_void, size_t) ->
        // *mut c_void` matches. `dst` is the pointer `vkMapMemory` returned for a
        // mapping of exactly `len` bytes (man 3 vkMapMemory: host-accessible for
        // `size` bytes from that pointer), still mapped; `src` and `len` are the
        // pointer and length of the live slice `bytes`; device memory and a Rust
        // slice do not overlap.
        let _ = unsafe { libc::memcpy(dst, src, len) };
        self.unmap();
        Ok(())
    }

    /// Copy the buffer's first `out.len()` bytes into `out`, which must not be
    /// empty or longer than the buffer.
    pub fn read(&self, out: &mut [u8]) -> Result<(), VulkanError> {
        let len = out.len();
        let src: *const c_void = self.map(0, len)?;
        let dst: *mut c_void = out.as_mut_ptr().cast();
        // SAFETY: man 3 memcpy: as in `write`, the other way: `src` is the
        // pointer `vkMapMemory` returned for a mapping of exactly `len` bytes,
        // still mapped and readable (man 3 vkMapMemory); `dst` and `len` are the
        // pointer and length of the live slice `out`, borrowed mutably, and any
        // byte is a valid `u8`; the two do not overlap.
        let _ = unsafe { libc::memcpy(dst, src, len) };
        self.unmap();
        Ok(())
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        let (device, buffer, memory) = (self.device, self.buffer, self.memory);
        let no_allocator: *const c_void = ptr::null();
        // SAFETY: man 3 vkDestroyBuffer: `device` is valid (never destroyed);
        // `buffer` was created on it, with no allocator, and is destroyed once
        // (here, in `Drop`); no submitted command still uses it, since every
        // submission in this file is waited for before its function returns.
        unsafe { vkDestroyBuffer(device, buffer, no_allocator) };
        if memory != 0 {
            // SAFETY: man 3 vkFreeMemory: `device` is valid; `memory` was
            // allocated on it, with no allocator, and is freed once (here); the
            // buffer bound to it was destroyed on the line above, and it is not
            // mapped (every mapping is ended before its function returns).
            unsafe { vkFreeMemory(device, memory, no_allocator) };
        }
    }
}

/// A colour format for the target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Format {
    /// `VK_FORMAT_R8G8B8A8_UNORM`: four bytes a pixel, red first, not sRGB.
    Rgba8Unorm,
}

impl Format {
    fn raw(self) -> u32 {
        match self {
            Format::Rgba8Unorm => 37,
        }
    }
}

/// A blend factor (`VkBlendFactor`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlendFactor {
    /// `VK_BLEND_FACTOR_ONE`.
    One,
    /// `VK_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA`.
    OneMinusSourceAlpha,
}

impl BlendFactor {
    fn raw(self) -> u32 {
        match self {
            BlendFactor::One => 1,
            BlendFactor::OneMinusSourceAlpha => 7,
        }
    }
}

/// What [`Device::new_pipeline`] makes.
#[derive(Debug, Clone, Copy)]
pub struct PipelineDesc<'a> {
    /// The vertex shader's SPIR-V, entry point `main`.
    pub vertex: &'a [u8],
    /// The fragment shader's SPIR-V, entry point `main`.
    pub fragment: &'a [u8],
    /// The target's format.
    pub format: Format,
    /// Source and destination factors, for colour and alpha alike, added; `None`
    /// for no blending.
    pub blend: Option<(BlendFactor, BlendFactor)>,
    /// How many storage buffers the shaders read, at set 0, bindings 0 up: 1 to
    /// [`MAX_STORAGE_BUFFERS`].
    pub storage_buffers: u32,
    /// The push constants' size in bytes, a multiple of 4 above 0, read by both
    /// stages.
    pub push_bytes: u32,
}

/// A graphics pipeline with its render passes, layouts and descriptor set. Never
/// destroyed (see the module documentation).
#[derive(Debug)]
pub struct Pipeline {
    device: Dispatchable,
    pass_clear: Handle,
    pass_load: Handle,
    layout: Handle,
    pipeline: Handle,
    set: Handle,
    format: Format,
    storage_buffers: u32,
    push_bytes: u32,
    max_storage_buffer_range: u32,
    /// The buffer bound to each storage binding, in order. The pipeline owns
    /// them, so a bound buffer lives as long as its binding.
    buffers: Vec<Option<Buffer>>,
}

/// The words of a SPIR-V module given as little-endian bytes.
fn spirv_words(bytes: &[u8]) -> Result<Vec<u32>, VulkanError> {
    let (chunks, rest) = bytes.as_chunks::<4>();
    let words: Vec<u32> = chunks.iter().map(|c| u32::from_le_bytes(*c)).collect();
    if !rest.is_empty() || words.first() != Some(&SPIRV_MAGIC) {
        return Err(refused("SPIR-V: whole words after the magic number"));
    }
    Ok(words)
}

impl Device {
    fn shader_module(&self, spirv: &[u8]) -> Result<Handle, VulkanError> {
        let words = spirv_words(spirv)?;
        let device = self.device;
        let info = ShaderModuleCreateInfo {
            s_type: ST_SHADER_MODULE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            code_size: size_of_val(words.as_slice()),
            p_code: words.as_ptr(),
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let mut module: Handle = 0;
        let out = &raw mut module;
        // SAFETY: man 3 vkCreateShaderModule: `device` is valid; `pCreateInfo`
        // points to the live local `info`, a `VkShaderModuleCreateInfo` whose
        // `pCode` points to `codeSize` bytes of 32-bit words (`words`, live until
        // this function returns, its byte length a multiple of 4 above 0)
        // starting with the SPIR-V magic number. That the words are valid SPIR-V
        // for Vulkan is the caller's: they are the modules committed in
        // `clazel-gpu/shaders`, compiled from our GLSL (module documentation).
        // `pAllocator` is NULL; `pShaderModule` points to the live local
        // `module`. The call copies the code.
        let rc = unsafe { vkCreateShaderModule(device, info_ptr, no_allocator, out) };
        check(rc, "vkCreateShaderModule")?;
        Ok(module)
    }

    /// A render pass with one colour attachment of `format`, one subpass, ending
    /// in the transfer-source layout; `clear` chooses clearing from an undefined
    /// layout or loading from the transfer-source layout.
    fn render_pass(&self, format: Format, clear: bool) -> Result<Handle, VulkanError> {
        let device = self.device;
        let attachment = AttachmentDescription {
            flags: 0,
            format: format.raw(),
            samples: SAMPLE_COUNT_1,
            load_op: if clear { LOAD_OP_CLEAR } else { LOAD_OP_LOAD },
            store_op: STORE_OP_STORE,
            stencil_load_op: LOAD_OP_DONT_CARE,
            stencil_store_op: STORE_OP_DONT_CARE,
            initial_layout: if clear {
                LAYOUT_UNDEFINED
            } else {
                LAYOUT_TRANSFER_SRC
            },
            final_layout: LAYOUT_TRANSFER_SRC,
        };
        let reference = AttachmentReference {
            attachment: 0,
            layout: LAYOUT_COLOR_ATTACHMENT,
        };
        let subpass = SubpassDescription {
            flags: 0,
            pipeline_bind_point: 0,
            input_attachment_count: 0,
            p_input_attachments: ptr::null(),
            color_attachment_count: 1,
            p_color_attachments: &raw const reference,
            p_resolve_attachments: ptr::null(),
            p_depth_stencil_attachment: ptr::null(),
            preserve_attachment_count: 0,
            p_preserve_attachments: ptr::null(),
        };
        let info = RenderPassCreateInfo {
            s_type: ST_RENDER_PASS_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            attachment_count: 1,
            p_attachments: &raw const attachment,
            subpass_count: 1,
            p_subpasses: &raw const subpass,
            dependency_count: 0,
            p_dependencies: ptr::null(),
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let mut pass: Handle = 0;
        let out = &raw mut pass;
        // SAFETY: man 3 vkCreateRenderPass: `device` is valid; `pCreateInfo`
        // points to the live local `info`, a valid `VkRenderPassCreateInfo`: one
        // attachment (the live local `attachment`: a core colour format, one
        // sample, a load op, store, a final layout that is neither undefined nor
        // preinitialized, and a load op of `LOAD` only with a defined initial
        // layout), one subpass (the live local `subpass`: the graphics bind point
        // (0), one colour attachment reference, the live local `reference`, to
        // attachment 0 in the colour-attachment layout, and nothing else), and no
        // dependencies; `pAllocator` is NULL; `pRenderPass` points to the live
        // local `pass`.
        let rc = unsafe { vkCreateRenderPass(device, info_ptr, no_allocator, out) };
        check(rc, "vkCreateRenderPass")?;
        Ok(pass)
    }

    /// A descriptor set layout of `count` storage buffers, bindings 0 up, each
    /// visible to the vertex and fragment stages.
    fn set_layout(&self, count: u32) -> Result<Handle, VulkanError> {
        let device = self.device;
        let bindings: Vec<DescriptorSetLayoutBinding> = (0..count)
            .map(|binding| DescriptorSetLayoutBinding {
                binding,
                descriptor_type: DESCRIPTOR_STORAGE_BUFFER,
                descriptor_count: 1,
                stage_flags: STAGE_VERTEX | STAGE_FRAGMENT,
                p_immutable_samplers: ptr::null(),
            })
            .collect();
        let info = DescriptorSetLayoutCreateInfo {
            s_type: ST_DESCRIPTOR_SET_LAYOUT_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            binding_count: count,
            p_bindings: bindings.as_ptr(),
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let mut layout: Handle = 0;
        let out = &raw mut layout;
        // SAFETY: man 3 vkCreateDescriptorSetLayout: `device` is valid;
        // `pCreateInfo` points to the live local `info`, a valid
        // `VkDescriptorSetLayoutCreateInfo` whose `pBindings` points to
        // `bindingCount` elements (`bindings`, live until this function returns,
        // exactly `count` long), each a distinct binding number, one storage
        // buffer, two core stage bits and no samplers; `pAllocator` is NULL;
        // `pSetLayout` points to the live local `layout`.
        let rc = unsafe { vkCreateDescriptorSetLayout(device, info_ptr, no_allocator, out) };
        check(rc, "vkCreateDescriptorSetLayout")?;
        Ok(layout)
    }

    fn pipeline_layout(&self, set_layout: Handle, push_bytes: u32) -> Result<Handle, VulkanError> {
        let device = self.device;
        let range = PushConstantRange {
            stage_flags: STAGE_VERTEX | STAGE_FRAGMENT,
            offset: 0,
            size: push_bytes,
        };
        let info = PipelineLayoutCreateInfo {
            s_type: ST_PIPELINE_LAYOUT_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            set_layout_count: 1,
            p_set_layouts: &raw const set_layout,
            push_constant_range_count: 1,
            p_push_constant_ranges: &raw const range,
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let mut layout: Handle = 0;
        let out = &raw mut layout;
        // SAFETY: man 3 vkCreatePipelineLayout: `device` is valid; `pCreateInfo`
        // points to the live local `info`, a valid `VkPipelineLayoutCreateInfo`:
        // one set layout (the parameter `set_layout`, created on this device and
        // never destroyed, read through a pointer to the live parameter) and one
        // push-constant range (the live local `range`: two core stage bits,
        // offset 0, and a size that is a multiple of 4, above 0 and at most the
        // device's `maxPushConstantsSize`, which `new_pipeline` checked);
        // `pAllocator` is NULL; `pPipelineLayout` points to the live local
        // `layout`.
        let rc = unsafe { vkCreatePipelineLayout(device, info_ptr, no_allocator, out) };
        check(rc, "vkCreatePipelineLayout")?;
        Ok(layout)
    }

    /// One descriptor set of `set_layout` (`count` storage buffers), from a pool
    /// made for exactly it.
    fn descriptor_set(&self, set_layout: Handle, count: u32) -> Result<Handle, VulkanError> {
        let device = self.device;
        let size = DescriptorPoolSize {
            descriptor_type: DESCRIPTOR_STORAGE_BUFFER,
            descriptor_count: count,
        };
        let pool_info = DescriptorPoolCreateInfo {
            s_type: ST_DESCRIPTOR_POOL_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            max_sets: 1,
            pool_size_count: 1,
            p_pool_sizes: &raw const size,
        };
        let pool_info_ptr = &raw const pool_info;
        let no_allocator: *const c_void = ptr::null();
        let mut pool: Handle = 0;
        let pool_out = &raw mut pool;
        // SAFETY: man 3 vkCreateDescriptorPool: `device` is valid; `pCreateInfo`
        // points to the live local `pool_info`, a valid
        // `VkDescriptorPoolCreateInfo`: flags 0, `maxSets` 1, and one pool size
        // (the live local `size`: storage buffers, a count above 0);
        // `pAllocator` is NULL; `pDescriptorPool` points to the live local
        // `pool`.
        let rc = unsafe { vkCreateDescriptorPool(device, pool_info_ptr, no_allocator, pool_out) };
        check(rc, "vkCreateDescriptorPool")?;
        let info = DescriptorSetAllocateInfo {
            s_type: ST_DESCRIPTOR_SET_ALLOCATE_INFO,
            p_next: ptr::null(),
            descriptor_pool: pool,
            descriptor_set_count: 1,
            p_set_layouts: &raw const set_layout,
        };
        let info_ptr = &raw const info;
        let mut set: Handle = 0;
        let out = &raw mut set;
        // SAFETY: man 3 vkAllocateDescriptorSets: `device` is valid;
        // `pAllocateInfo` points to the live local `info`, a valid
        // `VkDescriptorSetAllocateInfo`: the pool just created on this device,
        // which has room for one set of `count` storage buffers and has given
        // none out, a count of 1, and `pSetLayouts` pointing to the one layout
        // (the live parameter `set_layout`, created on this device);
        // `pDescriptorSets` points to the live local `set`, room for the one
        // handle.
        let rc = unsafe { vkAllocateDescriptorSets(device, info_ptr, out) };
        check(rc, "vkAllocateDescriptorSets")?;
        Ok(set)
    }

    /// The pipeline `desc` describes (see the module documentation for what is
    /// fixed), with its two render passes and its descriptor set.
    pub fn new_pipeline(&self, desc: &PipelineDesc<'_>) -> Result<Pipeline, VulkanError> {
        if desc.storage_buffers == 0 || desc.storage_buffers > MAX_STORAGE_BUFFERS {
            return Err(refused("1 to 8 storage buffers"));
        }
        if desc.push_bytes == 0
            || !desc.push_bytes.is_multiple_of(4)
            || desc.push_bytes > self.limits.max_push_constants_size
        {
            return Err(refused("push constants: whole words within the limit"));
        }
        let device = self.device;
        let vertex = self.shader_module(desc.vertex)?;
        let fragment = self.shader_module(desc.fragment)?;
        let pass_clear = self.render_pass(desc.format, true)?;
        let pass_load = self.render_pass(desc.format, false)?;
        let set_layout = self.set_layout(desc.storage_buffers)?;
        let layout = self.pipeline_layout(set_layout, desc.push_bytes)?;
        let set = self.descriptor_set(set_layout, desc.storage_buffers)?;
        let entry: *const c_char = ENTRY.as_ptr().cast();
        let stage = |stage: u32, module: Handle| PipelineShaderStageCreateInfo {
            s_type: ST_PIPELINE_SHADER_STAGE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            stage,
            module,
            p_name: entry,
            p_specialization_info: ptr::null(),
        };
        let stages = [stage(STAGE_VERTEX, vertex), stage(STAGE_FRAGMENT, fragment)];
        let vertex_input = PipelineVertexInputStateCreateInfo {
            s_type: ST_PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            vertex_binding_description_count: 0,
            p_vertex_binding_descriptions: ptr::null(),
            vertex_attribute_description_count: 0,
            p_vertex_attribute_descriptions: ptr::null(),
        };
        let input_assembly = PipelineInputAssemblyStateCreateInfo {
            s_type: ST_PIPELINE_INPUT_ASSEMBLY_STATE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            topology: TOPOLOGY_TRIANGLE_LIST,
            primitive_restart_enable: 0,
        };
        let viewport = PipelineViewportStateCreateInfo {
            s_type: ST_PIPELINE_VIEWPORT_STATE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            viewport_count: 1,
            p_viewports: ptr::null(),
            scissor_count: 1,
            p_scissors: ptr::null(),
        };
        let rasterization = PipelineRasterizationStateCreateInfo {
            s_type: ST_PIPELINE_RASTERIZATION_STATE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            depth_clamp_enable: 0,
            rasterizer_discard_enable: 0,
            polygon_mode: 0,
            cull_mode: 0,
            front_face: 0,
            depth_bias_enable: 0,
            depth_bias_constant_factor: 0.0,
            depth_bias_clamp: 0.0,
            depth_bias_slope_factor: 0.0,
            line_width: 1.0,
        };
        let multisample = PipelineMultisampleStateCreateInfo {
            s_type: ST_PIPELINE_MULTISAMPLE_STATE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            rasterization_samples: SAMPLE_COUNT_1,
            sample_shading_enable: 0,
            min_sample_shading: 0.0,
            p_sample_mask: ptr::null(),
            alpha_to_coverage_enable: 0,
            alpha_to_one_enable: 0,
        };
        let (source, destination) = desc
            .blend
            .unwrap_or((BlendFactor::One, BlendFactor::OneMinusSourceAlpha));
        let blend_attachment = PipelineColorBlendAttachmentState {
            blend_enable: u32::from(desc.blend.is_some()),
            src_color_blend_factor: source.raw(),
            dst_color_blend_factor: destination.raw(),
            color_blend_op: 0,
            src_alpha_blend_factor: source.raw(),
            dst_alpha_blend_factor: destination.raw(),
            alpha_blend_op: 0,
            color_write_mask: COLOR_WRITE_ALL,
        };
        let blend = PipelineColorBlendStateCreateInfo {
            s_type: ST_PIPELINE_COLOR_BLEND_STATE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            logic_op_enable: 0,
            logic_op: 0,
            attachment_count: 1,
            p_attachments: &raw const blend_attachment,
            blend_constants: [0.0; 4],
        };
        let dynamic = PipelineDynamicStateCreateInfo {
            s_type: ST_PIPELINE_DYNAMIC_STATE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            dynamic_state_count: 2,
            p_dynamic_states: DYNAMIC_VIEWPORT_SCISSOR.as_ptr(),
        };
        let info = GraphicsPipelineCreateInfo {
            s_type: ST_GRAPHICS_PIPELINE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            stage_count: 2,
            p_stages: stages.as_ptr(),
            p_vertex_input_state: &raw const vertex_input,
            p_input_assembly_state: &raw const input_assembly,
            p_tessellation_state: ptr::null(),
            p_viewport_state: &raw const viewport,
            p_rasterization_state: &raw const rasterization,
            p_multisample_state: &raw const multisample,
            p_depth_stencil_state: ptr::null(),
            p_color_blend_state: &raw const blend,
            p_dynamic_state: &raw const dynamic,
            layout,
            render_pass: pass_clear,
            subpass: 0,
            base_pipeline_handle: 0,
            base_pipeline_index: -1,
        };
        let info_ptr = &raw const info;
        let no_allocator: *const c_void = ptr::null();
        let no_cache: Handle = 0;
        let one: u32 = 1;
        let mut pipeline: Handle = 0;
        let out = &raw mut pipeline;
        // SAFETY: man 3 vkCreateGraphicsPipelines: `device` is valid; the cache
        // is `VK_NULL_HANDLE`; `pCreateInfos` points to one
        // `VkGraphicsPipelineCreateInfo`, the live local `info`, whose pointers
        // are to live locals of the declared structures: two stages (`stages`: a
        // vertex and a fragment module created on this device from the caller's
        // SPIR-V, entry point the NUL-terminated static `ENTRY`, no
        // specialization; the device is 1.1 or later, `Instance::open` having
        // refused others, so the modules' `StorageBuffer` storage class is
        // allowed), an empty vertex input, triangle lists without
        // restart, one viewport and one scissor with both dynamic (so their
        // pointers are ignored and NULL), fill mode (0), no culling (0), no depth
        // bias, line width 1.0, one sample with no mask, no depth-stencil state
        // (the subpass has no such attachment), one blend attachment for the
        // subpass's one colour attachment with core factors, the add op (0) and
        // no logic op, and two dynamic states from the static
        // `DYNAMIC_VIEWPORT_SCISSOR`; `layout` and `renderPass` were created on
        // this device, subpass 0 exists, and there is no base pipeline (handle 0,
        // index -1). That the stages' interfaces match the layout (storage
        // buffers at set 0 from binding 0, one push-constant block) is the
        // caller's fixed shaders' (module documentation). `pAllocator` is NULL;
        // `pPipelines` points to the live local `pipeline`, room for one handle.
        let rc = unsafe {
            vkCreateGraphicsPipelines(device, no_cache, one, info_ptr, no_allocator, out)
        };
        check(rc, "vkCreateGraphicsPipelines")?;
        Ok(Pipeline {
            device,
            pass_clear,
            pass_load,
            layout,
            pipeline,
            set,
            format: desc.format,
            storage_buffers: desc.storage_buffers,
            push_bytes: desc.push_bytes,
            max_storage_buffer_range: self.limits.max_storage_buffer_range,
            buffers: (0..desc.storage_buffers).map(|_| None).collect(),
        })
    }
}

impl Pipeline {
    /// Bind `buffer` ([`BufferUse::Storage`], whole) to storage binding
    /// `binding`, which must be below the count the pipeline was made with; the
    /// buffer must be of this device and no longer than `maxStorageBufferRange`.
    /// The pipeline takes it, and gives back the buffer bound there before, which
    /// no binding names any more. [`Pipeline::buffer`] lends a bound one, to
    /// write.
    pub fn bind(&mut self, binding: u32, buffer: Buffer) -> Result<Option<Buffer>, VulkanError> {
        let limit = usize::try_from(self.max_storage_buffer_range).unwrap_or(usize::MAX);
        if buffer.device != self.device || buffer.usage != BufferUse::Storage || buffer.len > limit
        {
            return Err(refused("a storage buffer of this device within the limit"));
        }
        let index = usize::try_from(binding).map_err(|_| refused("binding"))?;
        if binding >= self.storage_buffers || index >= self.buffers.len() {
            return Err(refused("a storage binding of the pipeline"));
        }
        let info = DescriptorBufferInfo {
            buffer: buffer.buffer,
            offset: 0,
            range: VK_WHOLE_SIZE,
        };
        let write = WriteDescriptorSet {
            s_type: ST_WRITE_DESCRIPTOR_SET,
            p_next: ptr::null(),
            dst_set: self.set,
            dst_binding: binding,
            dst_array_element: 0,
            descriptor_count: 1,
            descriptor_type: DESCRIPTOR_STORAGE_BUFFER,
            p_image_info: ptr::null(),
            p_buffer_info: &raw const info,
            p_texel_buffer_view: ptr::null(),
        };
        let device = self.device;
        let write_ptr = &raw const write;
        let no_copies: *const c_void = ptr::null();
        let (zero, one): (u32, u32) = (0, 1);
        // SAFETY: man 3 vkUpdateDescriptorSets: `device` is valid;
        // `pDescriptorWrites` points to one valid `VkWriteDescriptorSet`, the
        // live local `write`: it names this pipeline's set (allocated on this
        // device, never freed), a binding below the layout's count (checked
        // above), element 0, one storage-buffer descriptor, and a `pBufferInfo`
        // pointing to the live local `info`, with a buffer created on this device
        // with storage usage, alive (owned by `buffer`), offset 0 and
        // `VK_WHOLE_SIZE`, the buffer's length being at most
        // `maxStorageBufferRange` (checked above). No copies. The set is not in
        // use by a pending command: every submission in this file is waited for
        // before its function returns.
        unsafe { vkUpdateDescriptorSets(device, one, write_ptr, zero, no_copies) };
        // The buffer bound before leaves only now, when the binding names the
        // new one.
        Ok(self
            .buffers
            .get_mut(index)
            .and_then(|slot| slot.replace(buffer)))
    }

    /// The buffer bound to storage binding `binding`, if one is.
    pub fn buffer(&self, binding: u32) -> Option<&Buffer> {
        let index = usize::try_from(binding).ok()?;
        self.buffers.get(index)?.as_ref()
    }

    /// Whether every storage binding has a buffer.
    fn bound(&self) -> bool {
        !self.buffers.is_empty() && self.buffers.iter().all(Option::is_some)
    }

    /// An image of `width` by `height` pixels (each 1 to
    /// [`Device::max_target_side`]) in the pipeline's format, with its memory,
    /// view and framebuffer.
    pub fn new_target(
        &self,
        device: &Device,
        width: u32,
        height: u32,
    ) -> Result<Target, VulkanError> {
        if device.device != self.device {
            return Err(refused("the pipeline's device"));
        }
        let side = |s: u32| (1..=device.limits.max_side).contains(&s);
        if !side(width) || !side(height) {
            return Err(refused("a target side within the device's limits"));
        }
        let dev = self.device;
        let no_allocator: *const c_void = ptr::null();
        let image_info = ImageCreateInfo {
            s_type: ST_IMAGE_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            image_type: TYPE_2D,
            format: self.format.raw(),
            extent: [width, height, 1],
            mip_levels: 1,
            array_layers: 1,
            samples: SAMPLE_COUNT_1,
            tiling: 0,
            usage: IMAGE_USAGE_TARGET,
            sharing_mode: 0,
            queue_family_index_count: 0,
            p_queue_family_indices: ptr::null(),
            initial_layout: LAYOUT_UNDEFINED,
        };
        let image_info_ptr = &raw const image_info;
        let mut image: Handle = 0;
        let image_out = &raw mut image;
        // SAFETY: man 3 vkCreateImage: `device` is valid; `pCreateInfo` points
        // to the live local `image_info`, a valid `VkImageCreateInfo`: a 2D
        // image of a core colour format that every implementation supports as a
        // colour attachment and transfer source with optimal tiling (0)
        // (`VK_FORMAT_R8G8B8A8_UNORM`, the one `Format`), an extent within
        // `maxImageDimension2D` and above 0 with depth 1, one mip level, one
        // layer, one sample, usage colour attachment and transfer source,
        // exclusive sharing (0) and the undefined initial layout; `pAllocator` is
        // NULL; `pImage` points to the live local `image`.
        let rc = unsafe { vkCreateImage(dev, image_info_ptr, no_allocator, image_out) };
        check(rc, "vkCreateImage")?;
        // From here `made` owns what exists; its `Drop` destroys what is not 0.
        let mut made = Target {
            device: dev,
            queue: device.queue,
            cb: device.cb,
            image,
            memory: 0,
            view: 0,
            framebuffer: 0,
            width,
            height,
            drawn: false,
        };
        let mut req = MemoryRequirements {
            size: 0,
            alignment: 0,
            memory_type_bits: 0,
        };
        let req_out = &raw mut req;
        // SAFETY: man 3 vkGetImageMemoryRequirements: `device` is valid and
        // `image` was just created on it; `pMemoryRequirements` points to the
        // live local `req`, which the call fills.
        unsafe { vkGetImageMemoryRequirements(dev, image, req_out) };
        let index = device
            .memory_type(req.memory_type_bits, 0)
            .ok_or(refused("no memory type for the image"))?;
        made.memory = device.allocate(req.size, index)?;
        let memory = made.memory;
        let offset: u64 = 0;
        // SAFETY: man 3 vkBindImageMemory: `device` is valid; `image` was
        // created on it and has no memory bound yet; `memory` was just allocated
        // on it with the size and a memory type from the image's own
        // requirements; offset 0 meets every alignment.
        let rc = unsafe { vkBindImageMemory(dev, image, memory, offset) };
        check(rc, "vkBindImageMemory")?;
        let view_info = ImageViewCreateInfo {
            s_type: ST_IMAGE_VIEW_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            image,
            view_type: TYPE_2D,
            format: self.format.raw(),
            components: [0; 4],
            subresource_range: [ASPECT_COLOR, 0, 1, 0, 1],
        };
        let view_info_ptr = &raw const view_info;
        let mut view: Handle = 0;
        let view_out = &raw mut view;
        // SAFETY: man 3 vkCreateImageView: `device` is valid; `pCreateInfo`
        // points to the live local `view_info`, a valid `VkImageViewCreateInfo`:
        // the image just created, with memory bound, a 2D view of the image's
        // own format, identity swizzles (0), and the colour aspect of its one
        // mip level and one layer; `pAllocator` is NULL; `pView` points to the
        // live local `view`.
        let rc = unsafe { vkCreateImageView(dev, view_info_ptr, no_allocator, view_out) };
        check(rc, "vkCreateImageView")?;
        made.view = view;
        let fb_info = FramebufferCreateInfo {
            s_type: ST_FRAMEBUFFER_CREATE_INFO,
            p_next: ptr::null(),
            flags: 0,
            render_pass: self.pass_clear,
            attachment_count: 1,
            p_attachments: &raw const view,
            width,
            height,
            layers: 1,
        };
        let fb_info_ptr = &raw const fb_info;
        let mut framebuffer: Handle = 0;
        let fb_out = &raw mut framebuffer;
        // SAFETY: man 3 vkCreateFramebuffer: `device` is valid; `pCreateInfo`
        // points to the live local `fb_info`, a valid `VkFramebufferCreateInfo`:
        // a render pass created on this device with one attachment, one
        // attachment (the live local `view`, a view of an image with the render
        // pass's format and sample count, colour-attachment usage, one mip level
        // and the framebuffer's own extent), a width and height above 0 and
        // within `maxFramebufferWidth`/`Height`, and one layer; `pAllocator` is
        // NULL; `pFramebuffer` points to the live local `framebuffer`. A
        // framebuffer may be used with any render pass compatible with the one
        // named, which the clearing and the loading pass are (the same
        // attachment format and sample count, the same subpass).
        let rc = unsafe { vkCreateFramebuffer(dev, fb_info_ptr, no_allocator, fb_out) };
        check(rc, "vkCreateFramebuffer")?;
        made.framebuffer = framebuffer;
        Ok(made)
    }
}

/// Where a pipeline draws: an image with its memory, view and framebuffer.
/// Dropping it destroys them.
#[derive(Debug)]
pub struct Target {
    device: Dispatchable,
    queue: Dispatchable,
    cb: Dispatchable,
    image: Handle,
    memory: Handle,
    view: Handle,
    framebuffer: Handle,
    width: u32,
    height: u32,
    /// Whether a pass has drawn into it, leaving the transfer-source layout.
    drawn: bool,
}

impl Drop for Target {
    fn drop(&mut self) {
        let device = self.device;
        let (framebuffer, view, image, memory) =
            (self.framebuffer, self.view, self.image, self.memory);
        let no_allocator: *const c_void = ptr::null();
        if framebuffer != 0 {
            // SAFETY: man 3 vkDestroyFramebuffer: `device` is valid (never
            // destroyed); `framebuffer` was created on it, with no allocator,
            // and is destroyed once (here); no submitted command still uses it,
            // since every submission is waited for before its function returns.
            unsafe { vkDestroyFramebuffer(device, framebuffer, no_allocator) };
        }
        if view != 0 {
            // SAFETY: man 3 vkDestroyImageView: as above for `view`, whose
            // framebuffer was destroyed on the lines above.
            unsafe { vkDestroyImageView(device, view, no_allocator) };
        }
        // SAFETY: man 3 vkDestroyImage: as above for `image`, whose view was
        // destroyed on the lines above.
        unsafe { vkDestroyImage(device, image, no_allocator) };
        if memory != 0 {
            // SAFETY: man 3 vkFreeMemory: `device` is valid; `memory` was
            // allocated on it, with no allocator, and is freed once (here); the
            // image bound to it was destroyed on the line above, and it was never
            // mapped.
            unsafe { vkFreeMemory(device, memory, no_allocator) };
        }
    }
}

/// One draw of [`Device::render`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Draw {
    /// The scissor rectangle: x, y, width, height, inside the target.
    pub scissor: (u32, u32, u32, u32),
    /// How many vertices each instance has.
    pub vertices: u32,
    /// How many instances.
    pub instances: u32,
    /// The first instance's index.
    pub first_instance: u32,
}

/// `vkBeginCommandBuffer` on `cb`, a device's one command buffer, which resets
/// it.
fn begin(cb: Dispatchable) -> Result<(), VulkanError> {
    let info = CommandBufferBeginInfo {
        s_type: ST_COMMAND_BUFFER_BEGIN_INFO,
        p_next: ptr::null(),
        flags: COMMAND_BUFFER_ONE_TIME_SUBMIT,
        p_inheritance_info: ptr::null(),
    };
    let info_ptr = &raw const info;
    // SAFETY: man 3 vkBeginCommandBuffer: `commandBuffer` is the device's
    // one primary command buffer, allocated from a pool created with the
    // reset flag, and is not recording or pending (every function here ends
    // and submits what it began and waits for it, or leaves the buffer to be
    // reset by the next begin); `pBeginInfo` points to the live local `info`,
    // a valid `VkCommandBufferBeginInfo` for a primary buffer (the one-time
    // flag, no inheritance info).
    let rc = unsafe { vkBeginCommandBuffer(cb, info_ptr) };
    check(rc, "vkBeginCommandBuffer")
}

/// `vkEndCommandBuffer`, `vkQueueSubmit` and `vkQueueWaitIdle`: the commands
/// recorded since [`begin`] have finished when this returns `Ok`.
fn submit_and_wait(cb: Dispatchable, queue: Dispatchable) -> Result<(), VulkanError> {
    // SAFETY: man 3 vkEndCommandBuffer: `commandBuffer` is recording
    // (`begin` succeeded) and no render pass is open in it (every function
    // here ends the pass it begins before calling this).
    let rc = unsafe { vkEndCommandBuffer(cb) };
    check(rc, "vkEndCommandBuffer")?;
    let info = SubmitInfo {
        s_type: ST_SUBMIT_INFO,
        p_next: ptr::null(),
        wait_semaphore_count: 0,
        p_wait_semaphores: ptr::null(),
        p_wait_dst_stage_mask: ptr::null(),
        command_buffer_count: 1,
        p_command_buffers: &raw const cb,
        signal_semaphore_count: 0,
        p_signal_semaphores: ptr::null(),
    };
    let info_ptr = &raw const info;
    let one: u32 = 1;
    let no_fence: Handle = 0;
    // SAFETY: man 3 vkQueueSubmit: `queue` is the device's queue, of the
    // family the command buffer's pool was created for; `pSubmits` points to
    // one valid `VkSubmitInfo`, the live local `info`: no semaphores and one
    // command buffer (the live local `cb`), which is executable (just ended)
    // and not pending; the fence is `VK_NULL_HANDLE`. Every object the
    // commands name is kept alive by the caller's borrows until the wait
    // below returns.
    let rc = unsafe { vkQueueSubmit(queue, one, info_ptr, no_fence) };
    check(rc, "vkQueueSubmit")?;
    // SAFETY: man 3 vkQueueWaitIdle: `queue` is the device's queue; the call
    // blocks until everything submitted to it has finished.
    let rc = unsafe { vkQueueWaitIdle(queue) };
    check(rc, "vkQueueWaitIdle")
}

impl Device {
    /// One render pass into `target` with `pipeline`: cleared to transparent
    /// black first if `clear`, else keeping what is there (which needs an earlier
    /// pass); `push` as the push constants; then each of `draws` under its
    /// scissor. The pipeline's storage buffers must be bound
    /// ([`Pipeline::bind`]). Returns when the GPU has finished.
    pub fn render(
        &self,
        pipeline: &Pipeline,
        target: &mut Target,
        clear: bool,
        push: &[u8],
        draws: &[Draw],
    ) -> Result<(), VulkanError> {
        if pipeline.device != self.device || target.device != self.device {
            return Err(refused("objects of this device"));
        }
        if !pipeline.bound() {
            return Err(refused("storage buffers bound before drawing"));
        }
        if !clear && !target.drawn {
            return Err(refused("a first pass that clears"));
        }
        if u32::try_from(push.len()).ok() != Some(pipeline.push_bytes) {
            return Err(refused("push constants of the pipeline's size"));
        }
        let mut scissors = Vec::with_capacity(draws.len());
        for d in draws {
            let (x, y, w, h) = d.scissor;
            let inside = x.checked_add(w).is_some_and(|r| r <= target.width)
                && y.checked_add(h).is_some_and(|b| b <= target.height);
            if !inside {
                return Err(refused("a scissor inside the target"));
            }
            scissors.push(Rect2D {
                x: i32::try_from(x).map_err(|_| refused("scissor"))?,
                y: i32::try_from(y).map_err(|_| refused("scissor"))?,
                width: w,
                height: h,
            });
        }
        let cb = self.cb;
        begin(cb)?;
        let clear_value = ClearValue { float32: [0.0; 4] };
        let begin = RenderPassBeginInfo {
            s_type: ST_RENDER_PASS_BEGIN_INFO,
            p_next: ptr::null(),
            render_pass: if clear {
                pipeline.pass_clear
            } else {
                pipeline.pass_load
            },
            framebuffer: target.framebuffer,
            render_area: Rect2D {
                x: 0,
                y: 0,
                width: target.width,
                height: target.height,
            },
            clear_value_count: 1,
            p_clear_values: &raw const clear_value,
        };
        let begin_ptr = &raw const begin;
        let inline: u32 = 0;
        // SAFETY: man 3 vkCmdBeginRenderPass: `commandBuffer` is recording with
        // no pass open; `pRenderPassBegin` points to the live local `begin`, a
        // valid `VkRenderPassBeginInfo`: a render pass of this pipeline, the
        // target's framebuffer (created on this device for a compatible pass),
        // a render area that is the framebuffer's whole extent, and one clear
        // value (the live local `clear_value`) for the pass's one attachment.
        // The attachment's image is in the pass's initial layout: undefined for
        // the clearing pass (any layout may be treated as undefined), and for
        // the loading pass the transfer-source layout every earlier pass left it
        // in (`target.drawn` was checked). Contents are
        // `VK_SUBPASS_CONTENTS_INLINE` (0).
        unsafe { vkCmdBeginRenderPass(cb, begin_ptr, inline) };
        let graphics: u32 = 0;
        let pipeline_handle = pipeline.pipeline;
        // SAFETY: man 3 vkCmdBindPipeline: `commandBuffer` is recording;
        // the bind point is graphics (0) and `pipeline` is a graphics pipeline
        // created on this device for a render pass compatible with the one
        // begun.
        unsafe { vkCmdBindPipeline(cb, graphics, pipeline_handle) };
        let layout = pipeline.layout;
        let set = pipeline.set;
        let set_ptr = &raw const set;
        let (zero, one): (u32, u32) = (0, 1);
        let no_offsets: *const u32 = ptr::null();
        // SAFETY: man 3 vkCmdBindDescriptorSets: `commandBuffer` is recording;
        // the bind point is graphics (0); `layout` is the pipeline's layout;
        // first set 0 and one set, `pDescriptorSets` pointing to the live local
        // `set`, allocated with the layout's one set layout and updated for
        // every binding to a buffer the pipeline owns (`pipeline.bound()` was
        // checked); no dynamic offsets, as the layout has no dynamic descriptor.
        unsafe {
            vkCmdBindDescriptorSets(cb, graphics, layout, zero, one, set_ptr, zero, no_offsets)
        };
        let stages = STAGE_VERTEX | STAGE_FRAGMENT;
        let push_size = pipeline.push_bytes;
        let push_ptr: *const c_void = push.as_ptr().cast();
        // SAFETY: man 3 vkCmdPushConstants: `commandBuffer` is recording;
        // `layout` is the pipeline's layout, whose one push-constant range is
        // these two stages from offset 0 for `push_size` bytes, so the stage
        // flags match it exactly and offset 0 and `size` (above 0, a multiple of
        // 4) are within it; `pValues` points to `size` bytes, the live slice
        // `push`, whose length was checked to equal `push_size`.
        unsafe { vkCmdPushConstants(cb, layout, stages, zero, push_size, push_ptr) };
        let viewport = Viewport {
            x: 0.0,
            y: 0.0,
            width: f32_of(target.width),
            height: f32_of(target.height),
            min_depth: 0.0,
            max_depth: 1.0,
        };
        let viewport_ptr = &raw const viewport;
        // SAFETY: man 3 vkCmdSetViewport: `commandBuffer` is recording; first
        // viewport 0 and one viewport, the live local `viewport`: a width and
        // height above 0 and within `maxViewportDimensions` (the target's sides,
        // checked when it was made), an origin of 0 and depths of 0 and 1.
        unsafe { vkCmdSetViewport(cb, zero, one, viewport_ptr) };
        for (d, scissor) in draws.iter().zip(&scissors) {
            let scissor_ptr = ptr::from_ref(scissor);
            // SAFETY: man 3 vkCmdSetScissor: `commandBuffer` is recording; first
            // scissor 0 and one scissor, a live element of `scissors`: an offset
            // that is not negative and an extent whose sum with it does not
            // overflow a signed 32-bit integer (both within the target's sides,
            // checked above).
            unsafe { vkCmdSetScissor(cb, zero, one, scissor_ptr) };
            let (vertices, instances, first) = (d.vertices, d.instances, d.first_instance);
            // SAFETY: man 3 vkCmdDraw: `commandBuffer` is recording inside a
            // render pass, with a graphics pipeline bound that is compatible
            // with it, its one descriptor set bound with every binding updated
            // to a live buffer, its push constants set for both stages, and its
            // two dynamic states (viewport, scissor) set above; the pipeline has
            // no vertex input, so no vertex buffer is needed. The counts are
            // plain integers; what the shaders read for them is bounded by the
            // shaders and by `robustBufferAccess` (module documentation).
            unsafe { vkCmdDraw(cb, vertices, instances, zero, first) };
        }
        // SAFETY: man 3 vkCmdEndRenderPass: `commandBuffer` is recording with
        // the render pass begun above open, in its last (only) subpass.
        unsafe { vkCmdEndRenderPass(cb) };
        submit_and_wait(cb, self.queue)?;
        target.drawn = true;
        Ok(())
    }
}

/// A side as `f32`, exact: sides are at most 2^24.
fn f32_of(side: u32) -> f32 {
    f32::from(u16::try_from(side.min(u32::from(u16::MAX))).unwrap_or(u16::MAX))
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

    /// Copy the target's pixels into `staging` (a [`BufferUse::Readback`]
    /// buffer of this device, at least `width × height × 4` bytes) and from there
    /// into `out`, whose length must be exactly that: rows from the top, packed,
    /// in the format's byte order. Needs an earlier pass.
    pub fn read_pixels(&self, staging: &Buffer, out: &mut [u8]) -> Result<(), VulkanError> {
        let bytes = usize::try_from(self.width)
            .ok()
            .zip(usize::try_from(self.height).ok())
            .and_then(|(w, h)| w.checked_mul(h))
            .and_then(|p| p.checked_mul(4))
            .ok_or(refused("target size"))?;
        if out.len() != bytes {
            return Err(refused("a slice of the target's size"));
        }
        if staging.device != self.device
            || staging.usage != BufferUse::Readback
            || staging.len < bytes
        {
            return Err(refused("a readback buffer of this device, large enough"));
        }
        if !self.drawn {
            return Err(refused("a pass before reading"));
        }
        begin(self.cb)?;
        let region = BufferImageCopy {
            buffer_offset: 0,
            buffer_row_length: 0,
            buffer_image_height: 0,
            image_subresource: [ASPECT_COLOR, 0, 0, 1],
            image_offset: [0; 3],
            image_extent: [self.width, self.height, 1],
        };
        let region_ptr = &raw const region;
        let (cb, image, buffer) = (self.cb, self.image, staging.buffer);
        let one: u32 = 1;
        // SAFETY: man 3 vkCmdCopyImageToBuffer: `commandBuffer` is recording
        // outside a render pass; `srcImage` was created on this device with
        // transfer-source usage and one sample and is in
        // `srcImageLayout`, the transfer-source layout every pass leaves it in
        // (`self.drawn`); `dstBuffer` was created on this device with
        // transfer-destination usage and has memory bound; `pRegions` points to
        // one `VkBufferImageCopy`, the live local `region`: buffer offset 0 (a
        // multiple of the texel size), row length and image height 0 (tightly
        // packed), the colour aspect of mip level 0 and layer 0, offset 0 and the
        // image's whole extent, so the region is inside the image and needs
        // `width × height × 4` bytes of the buffer, which it has (checked
        // above).
        unsafe { vkCmdCopyImageToBuffer(cb, image, LAYOUT_TRANSFER_SRC, buffer, one, region_ptr) };
        submit_and_wait(cb, self.queue)?;
        staging.read(out)
    }
}

#[cfg(test)]
mod tests {
    use std::mem::{align_of, offset_of, size_of};

    use super::*;

    /// Sizes from `<vulkan/vulkan_core.h>` (Vulkan-Headers 1.3.275), as a C
    /// program printed `sizeof` on aarch64 Linux.
    #[test]
    fn structures_have_the_headers_sizes() {
        assert_eq!(size_of::<ApplicationInfo>(), 48);
        assert_eq!(size_of::<InstanceCreateInfo>(), 64);
        assert_eq!(size_of::<PhysicalDeviceProperties>(), 824);
        assert_eq!(align_of::<PhysicalDeviceProperties>(), 8);
        assert_eq!(offset_of!(PhysicalDeviceProperties, limits), 296);
        assert_eq!(offset_of!(PhysicalDeviceProperties, sparse), 800);
        assert_eq!(size_of::<QueueFamilyProperties>(), 24);
        assert_eq!(size_of::<MemoryProperties>(), 520);
        assert_eq!(offset_of!(MemoryProperties, memory_heap_count), 260);
        assert_eq!(offset_of!(MemoryProperties, memory_heaps), 264);
        assert_eq!(size_of::<DeviceQueueCreateInfo>(), 40);
        assert_eq!(size_of::<Features>(), 220);
        assert_eq!(size_of::<DeviceCreateInfo>(), 72);
        assert_eq!(size_of::<CommandPoolCreateInfo>(), 24);
        assert_eq!(size_of::<CommandBufferAllocateInfo>(), 32);
        assert_eq!(size_of::<ShaderModuleCreateInfo>(), 40);
        assert_eq!(size_of::<AttachmentDescription>(), 36);
        assert_eq!(size_of::<AttachmentReference>(), 8);
        assert_eq!(size_of::<SubpassDescription>(), 72);
        assert_eq!(size_of::<RenderPassCreateInfo>(), 64);
        assert_eq!(size_of::<DescriptorSetLayoutBinding>(), 24);
        assert_eq!(size_of::<DescriptorSetLayoutCreateInfo>(), 32);
        assert_eq!(size_of::<PushConstantRange>(), 12);
        assert_eq!(size_of::<PipelineLayoutCreateInfo>(), 48);
        assert_eq!(size_of::<PipelineShaderStageCreateInfo>(), 48);
        assert_eq!(size_of::<PipelineVertexInputStateCreateInfo>(), 48);
        assert_eq!(size_of::<PipelineInputAssemblyStateCreateInfo>(), 32);
        assert_eq!(size_of::<Viewport>(), 24);
        assert_eq!(size_of::<Rect2D>(), 16);
        assert_eq!(size_of::<PipelineViewportStateCreateInfo>(), 48);
        assert_eq!(size_of::<PipelineRasterizationStateCreateInfo>(), 64);
        assert_eq!(size_of::<PipelineMultisampleStateCreateInfo>(), 48);
        assert_eq!(size_of::<PipelineColorBlendAttachmentState>(), 32);
        assert_eq!(size_of::<PipelineColorBlendStateCreateInfo>(), 56);
        assert_eq!(size_of::<PipelineDynamicStateCreateInfo>(), 32);
        assert_eq!(size_of::<GraphicsPipelineCreateInfo>(), 144);
        assert_eq!(size_of::<DescriptorPoolSize>(), 8);
        assert_eq!(size_of::<DescriptorPoolCreateInfo>(), 40);
        assert_eq!(size_of::<DescriptorSetAllocateInfo>(), 40);
        assert_eq!(size_of::<DescriptorBufferInfo>(), 24);
        assert_eq!(size_of::<WriteDescriptorSet>(), 64);
        assert_eq!(size_of::<ImageCreateInfo>(), 88);
        assert_eq!(size_of::<MemoryRequirements>(), 24);
        assert_eq!(size_of::<MemoryAllocateInfo>(), 32);
        assert_eq!(size_of::<ImageViewCreateInfo>(), 80);
        assert_eq!(size_of::<FramebufferCreateInfo>(), 64);
        assert_eq!(size_of::<BufferCreateInfo>(), 56);
        assert_eq!(size_of::<CommandBufferBeginInfo>(), 32);
        assert_eq!(size_of::<ClearValue>(), 16);
        assert_eq!(size_of::<RenderPassBeginInfo>(), 64);
        assert_eq!(size_of::<BufferImageCopy>(), 56);
        assert_eq!(size_of::<SubmitInfo>(), 72);
    }

    /// Byte offsets inside `VkPhysicalDeviceLimits`, as a C program printed
    /// `offsetof` from the same header.
    #[test]
    fn the_limits_read_are_where_the_header_puts_them() {
        assert_eq!(LIMITS_WORDS * 4, 504);
        assert_eq!(LIMIT_MAX_IMAGE_DIMENSION_2D * 4, 4);
        assert_eq!(LIMIT_MAX_STORAGE_BUFFER_RANGE * 4, 28);
        assert_eq!(LIMIT_MAX_PUSH_CONSTANTS_SIZE * 4, 32);
        assert_eq!(LIMIT_MAX_VIEWPORT_WIDTH * 4, 280);
        assert_eq!(LIMIT_MAX_VIEWPORT_HEIGHT * 4, 284);
        assert_eq!(LIMIT_MAX_FRAMEBUFFER_WIDTH * 4, 364);
        assert_eq!(LIMIT_MAX_FRAMEBUFFER_HEIGHT * 4, 368);
    }

    #[test]
    fn spirv_is_whole_words_after_the_magic_number() {
        let magic = SPIRV_MAGIC.to_le_bytes();
        assert_eq!(spirv_words(&magic), Ok(vec![SPIRV_MAGIC]));
        assert!(spirv_words(&[]).is_err());
        assert!(spirv_words(&[3, 2, 35]).is_err());
        assert!(spirv_words(&[3, 2, 35, 7, 0]).is_err());
        assert!(spirv_words(&[0, 0, 0, 0]).is_err());
    }

    #[test]
    fn a_side_is_exact_as_a_float() {
        assert_eq!(f32_of(1), 1.0);
        assert_eq!(f32_of(8192), 8192.0);
        assert_eq!(f32_of(16_384), 16_384.0);
    }
}

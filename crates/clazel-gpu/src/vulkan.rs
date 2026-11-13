//! The Vulkan backend (Linux), through `clazel_sys::linux::vulkan`.
//!
//! # Modelling choices
//!
//! - **Offscreen, read back.** The target is an image the backend makes, and its
//!   pixels leave through [`Backend::read_pixels`], a copy into host-visible
//!   memory. No window-system extension is enabled: the GPU process presents
//!   nothing (item 5.17b). Exporting the target's memory instead (`memfd`,
//!   dma-buf) is the plan's route and is not built; `crate::channel` states the
//!   copy this costs.
//! - **The shaders are the committed SPIR-V** (`shaders/quad.vert.spv`,
//!   `quad.frag.spv`), compiled from our GLSL by `xtask` and embedded at build
//!   time. The pipeline is made when the backend starts, so a driver compiles them
//!   before the sandbox is entered.
//! - **One submission per run of draws, each waited for.** The quads are written
//!   once, before the first pass; an [`Op::Upload`] is a copy into the atlas's
//!   mapped memory and an [`Op::Atlas`] a new buffer, both between passes, with no
//!   pass in flight. So a draw sees exactly the uploads before it, as
//!   `crate::backend` requires, at the cost of one submission for each run. The
//!   first pass clears to transparent black and later ones load; a frame with no
//!   draw still clears.
//! - **The quads and the atlas are storage buffers the pipeline owns**, read by
//!   the shaders as 32-bit words. The quad buffer grows by doubling and is never
//!   shrunk. Before the first upload the atlas is a 4-byte placeholder with
//!   `atlas_bytes` 0, so the fragment shader reads nothing from it.
//! - **Which device.** For hardware, the first device the loader lists that is not
//!   a CPU, else the first; for software, the first CPU device (lavapipe), else
//!   the first, which `crate::start` then refuses as not software. The loader's
//!   order is not ours to change.
//! - **The driver version** is decoded per vendor
//!   (`crate::blocklist::vulkan_driver_version`).

use clazel_sys::linux::vulkan::{
    Adapter as Device0, BlendFactor, Buffer, BufferUse, Device, Draw, Format, Instance, Pipeline,
    PipelineDesc, Target, VulkanError,
};

use crate::backend::{Backend, BackendError, Frame, Op, QUAD_BYTES, quad_bytes};
use crate::blocklist::{Adapter, Api, vulkan_driver_version};
use crate::geom::{Rect, Viewport};

/// The fixed shaders, compiled at build time by `xtask` (`cargo xtask check`
/// confirms they match the GLSL beside them).
const VERTEX: &[u8] = include_bytes!("../shaders/quad.vert.spv");
/// See [`VERTEX`].
const FRAGMENT: &[u8] = include_bytes!("../shaders/quad.frag.spv");

/// The push constants: `width, height, quad_count, atlas_bytes`.
const PUSH_BYTES: u32 = 16;

/// The quad buffer's first size: 256 quads.
const FIRST_QUADS: usize = 256 * QUAD_BYTES;

fn backend_error(e: VulkanError) -> BackendError {
    BackendError {
        what: e.what,
        code: e.code,
    }
}

fn fail(what: &'static str) -> BackendError {
    BackendError { what, code: 0 }
}

/// Drawing with Vulkan.
#[derive(Debug)]
pub struct VulkanBackend {
    device: Device,
    pipeline: Pipeline,
    adapter: Adapter,
    /// The device's name, for the log.
    name: String,
    target: Option<Target>,
    /// Where the target is copied for reading; as large as the target.
    staging: Option<Buffer>,
    atlas_bytes: u32,
}

/// The device [`VulkanBackend::new`] draws with, of those the loader listed.
fn choose(adapters: &[Device0], software: bool) -> Option<&Device0> {
    adapters
        .iter()
        .find(|a| a.info.cpu == software)
        .or(adapters.first())
}

impl VulkanBackend {
    /// A device (see the module documentation for which), its queue and the one
    /// pipeline, with empty buffers bound. An error means there is no usable
    /// Vulkan device.
    pub fn new(software: bool) -> Result<VulkanBackend, BackendError> {
        let instance = Instance::new().map_err(backend_error)?;
        let adapters = instance.adapters().map_err(backend_error)?;
        let chosen = choose(&adapters, software).ok_or(fail("no Vulkan device"))?;
        let device = instance.open(chosen).map_err(backend_error)?;
        let mut pipeline = device
            .new_pipeline(&PipelineDesc {
                vertex: VERTEX,
                fragment: FRAGMENT,
                format: Format::Rgba8Unorm,
                blend: Some((BlendFactor::One, BlendFactor::OneMinusSourceAlpha)),
                storage_buffers: 2,
                push_bytes: PUSH_BYTES,
            })
            .map_err(backend_error)?;
        for (binding, len) in [(0, FIRST_QUADS), (1, 4)] {
            let buffer = device
                .new_buffer(len, BufferUse::Storage)
                .map_err(backend_error)?;
            pipeline.bind(binding, buffer).map_err(backend_error)?;
        }
        Ok(VulkanBackend {
            adapter: Adapter {
                api: Api::Vulkan,
                vendor: chosen.info.vendor,
                device: chosen.info.device,
                driver: Some(vulkan_driver_version(
                    chosen.info.vendor,
                    chosen.info.driver_version,
                )),
                software: chosen.info.cpu,
            },
            name: chosen.info.name.clone(),
            device,
            pipeline,
            target: None,
            staging: None,
            atlas_bytes: 0,
        })
    }

    /// The device's name, as the driver gives it.
    pub fn device_name(&self) -> &str {
        &self.name
    }

    /// Bind a new buffer of `len` bytes at storage binding `binding` (0 the
    /// quads, 1 the atlas); the one bound before is dropped, nothing being in
    /// flight.
    fn rebind(&mut self, binding: u32, len: usize) -> Result<(), BackendError> {
        let new = self
            .device
            .new_buffer(len, BufferUse::Storage)
            .map_err(backend_error)?;
        self.pipeline
            .bind(binding, new)
            .map(drop)
            .map_err(backend_error)
    }

    fn draw_inner(&mut self, frame: &Frame) -> Result<(), BackendError> {
        let viewport = frame.viewport.ok_or(fail("no viewport"))?;
        let fits = self
            .target
            .as_ref()
            .is_some_and(|t| t.width() == viewport.width && t.height() == viewport.height);
        if !fits {
            // The old target is dropped first: nothing is in flight.
            self.target = None;
            self.staging = None;
            self.target = Some(
                self.pipeline
                    .new_target(&self.device, viewport.width, viewport.height)
                    .map_err(backend_error)?,
            );
            self.staging = Some(
                self.device
                    .new_buffer(viewport.bytes(), BufferUse::Readback)
                    .map_err(backend_error)?,
            );
        }
        let quad_count = u32::try_from(frame.quads.len()).map_err(|_| fail("quad count"))?;
        let mut cleared = false;
        let mut quads_written = false;
        let mut k = 0usize;
        while let Some(op) = frame.ops.get(k) {
            match op {
                Op::Atlas { capacity } => {
                    let n = usize::try_from(*capacity).map_err(|_| fail("capacity"))?;
                    self.rebind(1, n.max(4))?;
                    self.atlas_bytes = *capacity;
                    k = k.saturating_add(1);
                }
                Op::Upload { offset, start, len } => {
                    let end = start.checked_add(*len).ok_or(fail("upload range"))?;
                    let bytes = frame.bytes.get(*start..end).ok_or(fail("upload range"))?;
                    let at = usize::try_from(*offset).map_err(|_| fail("offset"))?;
                    if !bytes.is_empty() {
                        self.pipeline
                            .buffer(1)
                            .ok_or(fail("no atlas"))?
                            .write(at, bytes)
                            .map_err(backend_error)?;
                    }
                    k = k.saturating_add(1);
                }
                Op::Draw { .. } => {
                    let run_end = frame
                        .ops
                        .get(k..)
                        .unwrap_or(&[])
                        .iter()
                        .position(|o| !matches!(o, Op::Draw { .. }))
                        .map_or(frame.ops.len(), |p| k.saturating_add(p));
                    let draws = frame.ops.get(k..run_end).unwrap_or(&[]);
                    if !quads_written {
                        self.write_quads(frame)?;
                        quads_written = true;
                    }
                    self.pass(viewport, !cleared, quad_count, draws)?;
                    cleared = true;
                    k = run_end;
                }
            }
        }
        if !cleared {
            self.pass(viewport, true, quad_count, &[])?;
        }
        Ok(())
    }

    /// Copy the frame's quads into the quad buffer, growing it first if they do
    /// not fit.
    fn write_quads(&mut self, frame: &Frame) -> Result<(), BackendError> {
        let bytes = quad_bytes(&frame.quads);
        if bytes.is_empty() {
            return Ok(());
        }
        let have = self.pipeline.buffer(0).ok_or(fail("no quads"))?.len();
        if bytes.len() > have {
            let grown = bytes
                .len()
                .checked_next_power_of_two()
                .ok_or(fail("quad bytes"))?;
            self.rebind(0, grown)?;
        }
        self.pipeline
            .buffer(0)
            .ok_or(fail("no quads"))?
            .write(0, &bytes)
            .map_err(backend_error)
    }

    /// One render pass drawing a run of [`Op::Draw`].
    fn pass(
        &mut self,
        viewport: Viewport,
        clear: bool,
        quad_count: u32,
        draws: &[Op],
    ) -> Result<(), BackendError> {
        let mut push = Vec::with_capacity(16);
        for w in [
            viewport.width,
            viewport.height,
            quad_count,
            self.atlas_bytes,
        ] {
            push.extend_from_slice(&w.to_le_bytes());
        }
        let mut list = Vec::with_capacity(draws.len());
        for op in draws {
            if let Op::Draw {
                scissor,
                first,
                count,
            } = op
            {
                list.push(Draw {
                    scissor: scissor_of(*scissor).ok_or(fail("scissor"))?,
                    vertices: 6,
                    instances: *count,
                    first_instance: *first,
                });
            }
        }
        let target = self.target.as_mut().ok_or(fail("no target"))?;
        self.device
            .render(&self.pipeline, target, clear, &push, &list)
            .map_err(backend_error)
    }
}

/// A scissor rectangle as Vulkan takes it: origin and size, all unsigned.
fn scissor_of(r: Rect) -> Option<(u32, u32, u32, u32)> {
    let x = u32::try_from(r.x0).ok()?;
    let y = u32::try_from(r.y0).ok()?;
    let w = u32::try_from(r.x1.checked_sub(r.x0)?).ok()?;
    let h = u32::try_from(r.y1.checked_sub(r.y0)?).ok()?;
    Some((x, y, w, h))
}

impl Backend for VulkanBackend {
    fn draw_frame(&mut self, frame: &Frame) -> Result<(), BackendError> {
        self.draw_inner(frame)
    }

    fn adapter(&self) -> Adapter {
        self.adapter
    }

    fn read_pixels(&mut self, out: &mut Vec<u8>) -> Result<(), BackendError> {
        let target = self.target.as_ref().ok_or(fail("no target"))?;
        let staging = self.staging.as_ref().ok_or(fail("no staging buffer"))?;
        out.clear();
        out.resize(staging.len(), 0);
        target.read_pixels(staging, out).map_err(backend_error)
    }
}

//! The Direct3D 12 backend (Windows), through `clazel_sys::windows::d3d12`.
//!
//! **Nothing in this file has run**: it was written on a Mac and compiled for
//! `x86_64-pc-windows-msvc` without its tests. Its shape is
//! [`crate::vulkan`]'s, which has run.
//!
//! # Modelling choices
//!
//! - **Offscreen, read back.** The target is a texture the backend makes, and
//!   its pixels leave through [`Backend::read_pixels`]: a copy into a readback
//!   buffer, whose rows Direct3D pads to a multiple of 256 bytes and this file
//!   packs. No swap chain and no composition surface: the plan's route for
//!   Windows (`CreateSwapChainForCompositionSurfaceHandle`, item 5.22a) is not
//!   built, and `crate::channel` states the copy this costs.
//! - **The shaders are the committed bytecode** (`shaders/quad.hlsl.vs.dxbc`,
//!   `quad.hlsl.ps.dxbc`), compiled from our HLSL by `vkd3d-compiler` and
//!   embedded at build time (`xtask/src/shaders.rs` states how they are
//!   checked). The pipeline is made when the backend starts.
//! - **One submission per run of draws, each waited for**, as on Vulkan: the
//!   quads are written once, before the first run; an [`Op::Upload`] or an
//!   [`Op::Atlas`] changes the atlas between runs, with nothing in flight. So a
//!   draw sees exactly the uploads before it, as `crate::backend` requires. The
//!   first run clears to transparent black; a frame with no draw still clears.
//! - **The atlas is kept twice**: in memory here and in a buffer the shaders
//!   read. `clazel-sys` copies to a buffer from its first byte only (it does no
//!   pointer arithmetic), so an upload changes the copy here and the whole
//!   atlas is written again before the next run of draws. That is a copy of the
//!   whole atlas for each run that follows an upload; a cost, listed.
//! - **Each draw's first quad is a constant.** Direct3D numbers a draw's
//!   instances from 0 whatever its first instance is, so the shaders add
//!   `first_instance`, the fifth constant, which is set before each draw
//!   (`shaders/quad.hlsl`). The constants are eight words: `width, height,
//!   quad_count, atlas_bytes, first_instance` and three of padding, the two
//!   16-byte registers the shaders' constant buffer covers.
//! - **Which adapter.** For hardware, the first adapter DXGI lists that is not
//!   software, else WARP; for software, WARP (`IDXGIFactory4::EnumWarpAdapter`),
//!   which is part of Windows (item 5.17c).
//! - **The driver version** is the adapter's user-mode driver version
//!   (`IDXGIAdapter::CheckInterfaceSupport`), four 16-bit parts.

use clazel_sys::windows::d3d12::{
    Adapter as Adapter0, BlendFactor, Buffer, BufferUse, D3dError, Device, Draw, Factory, Pipeline,
    PipelineDesc, Target,
};

use crate::backend::{Backend, BackendError, Frame, Op, QUAD_BYTES, packed_rows, quad_bytes};
use crate::blocklist::{Adapter, Api, Version};
use crate::geom::{Rect, Viewport};

/// The fixed shaders, compiled by `vkd3d-compiler` (`xtask/src/shaders.rs`).
const VERTEX: &[u8] = include_bytes!("../shaders/quad.hlsl.vs.dxbc");
/// See [`VERTEX`].
const FRAGMENT: &[u8] = include_bytes!("../shaders/quad.hlsl.ps.dxbc");

/// The 32-bit constants: `width, height, quad_count, atlas_bytes,
/// first_instance` and three unused.
const CONSTANTS: u32 = 8;

/// Which constant is `first_instance`.
const FIRST_INSTANCE: u32 = 4;

/// The quad buffer's first size: 256 quads.
const FIRST_QUADS: usize = 256 * QUAD_BYTES;

fn backend_error(e: D3dError) -> BackendError {
    BackendError {
        what: e.what,
        code: e.code,
    }
}

fn fail(what: &'static str) -> BackendError {
    BackendError { what, code: 0 }
}

/// Drawing with Direct3D 12. The device is the last field, so that everything
/// made from it is dropped first.
#[derive(Debug)]
pub struct D3d12Backend {
    adapter: Adapter,
    /// The adapter's description, for the log.
    name: String,
    target: Option<Target>,
    /// Where the target is copied for reading.
    staging: Option<Buffer>,
    quads: Buffer,
    atlas: Buffer,
    /// The atlas's bytes, as the shaders should read them.
    atlas_bytes: Vec<u8>,
    /// Whether `atlas_bytes` has changed since it was last written to `atlas`.
    atlas_stale: bool,
    pipeline: Pipeline,
    device: Device,
}

/// The adapter [`D3d12Backend::new`] draws with.
fn choose(factory: &Factory, software: bool) -> Result<Adapter0, BackendError> {
    if !software {
        let listed = factory.adapters().map_err(backend_error)?;
        if let Some(hardware) = listed.into_iter().find(|a| !a.info.software) {
            return Ok(hardware);
        }
    }
    factory.warp().map_err(backend_error)
}

impl D3d12Backend {
    /// A device (see the module documentation for which), its queue and the one
    /// pipeline, with empty buffers. An error means there is no usable Direct3D
    /// 12 device.
    pub fn new(software: bool) -> Result<D3d12Backend, BackendError> {
        let factory = Factory::new().map_err(backend_error)?;
        let chosen = choose(&factory, software)?;
        let device = chosen.open().map_err(backend_error)?;
        let pipeline = device
            .new_pipeline(&PipelineDesc {
                vertex: VERTEX,
                fragment: FRAGMENT,
                blend: Some((BlendFactor::One, BlendFactor::OneMinusSourceAlpha)),
                constants: CONSTANTS,
                buffers: 2,
            })
            .map_err(backend_error)?;
        let quads = device
            .new_buffer(FIRST_QUADS, BufferUse::Shader)
            .map_err(backend_error)?;
        // Before the first upload the atlas is a 4-byte placeholder with
        // `atlas_bytes` 0, so the fragment shader reads nothing from it.
        let atlas = device
            .new_buffer(4, BufferUse::Shader)
            .map_err(backend_error)?;
        Ok(D3d12Backend {
            adapter: Adapter {
                api: Api::D3d12,
                vendor: chosen.info.vendor,
                device: chosen.info.device,
                driver: chosen.info.driver.map(Version),
                software: chosen.info.software,
            },
            name: chosen.info.name.clone(),
            target: None,
            staging: None,
            quads,
            atlas,
            atlas_bytes: Vec::new(),
            atlas_stale: false,
            pipeline,
            device,
        })
    }

    /// The adapter's description, as DXGI gives it.
    pub fn device_name(&self) -> &str {
        &self.name
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
            let target = self
                .device
                .new_target(viewport.width, viewport.height)
                .map_err(backend_error)?;
            self.staging = Some(
                self.device
                    .new_buffer(target.copy_len(), BufferUse::Readback)
                    .map_err(backend_error)?,
            );
            self.target = Some(target);
        }
        let quad_count = u32::try_from(frame.quads.len()).map_err(|_| fail("quad count"))?;
        let mut cleared = false;
        let mut quads_written = false;
        let mut k = 0usize;
        while let Some(op) = frame.ops.get(k) {
            match op {
                Op::Atlas { capacity } => {
                    let n = usize::try_from(*capacity).map_err(|_| fail("capacity"))?;
                    self.atlas = self
                        .device
                        .new_buffer(n.max(4), BufferUse::Shader)
                        .map_err(backend_error)?;
                    self.atlas_bytes = vec![0; n];
                    self.atlas_stale = false;
                    k = k.saturating_add(1);
                }
                Op::Upload { offset, start, len } => {
                    let end = start.checked_add(*len).ok_or(fail("upload range"))?;
                    let bytes = frame.bytes.get(*start..end).ok_or(fail("upload range"))?;
                    let at = usize::try_from(*offset).map_err(|_| fail("offset"))?;
                    let to = at.checked_add(bytes.len()).ok_or(fail("upload range"))?;
                    self.atlas_bytes
                        .get_mut(at..to)
                        .ok_or(fail("upload past the atlas"))?
                        .copy_from_slice(bytes);
                    self.atlas_stale |= !bytes.is_empty();
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
        if bytes.len() > self.quads.len() {
            let grown = bytes
                .len()
                .checked_next_power_of_two()
                .ok_or(fail("quad bytes"))?;
            self.quads = self
                .device
                .new_buffer(grown, BufferUse::Shader)
                .map_err(backend_error)?;
        }
        self.quads.write(&bytes).map_err(backend_error)
    }

    /// One submission drawing a run of [`Op::Draw`].
    fn pass(
        &mut self,
        viewport: Viewport,
        clear: bool,
        quad_count: u32,
        draws: &[Op],
    ) -> Result<(), BackendError> {
        if self.atlas_stale {
            self.atlas.write(&self.atlas_bytes).map_err(backend_error)?;
            self.atlas_stale = false;
        }
        let atlas_len = u32::try_from(self.atlas_bytes.len()).map_err(|_| fail("atlas length"))?;
        let constants = [
            viewport.width,
            viewport.height,
            quad_count,
            atlas_len,
            0,
            0,
            0,
            0,
        ];
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
                    constant: Some((FIRST_INSTANCE, *first)),
                });
            }
        }
        let target = self.target.as_ref().ok_or(fail("no target"))?;
        self.device
            .render(
                &self.pipeline,
                target,
                clear,
                &constants,
                &[&self.quads, &self.atlas],
                &list,
            )
            .map_err(backend_error)
    }
}

/// A scissor rectangle as origin and size, all unsigned.
fn scissor_of(r: Rect) -> Option<(u32, u32, u32, u32)> {
    let x = u32::try_from(r.x0).ok()?;
    let y = u32::try_from(r.y0).ok()?;
    let w = u32::try_from(r.x1.checked_sub(r.x0)?).ok()?;
    let h = u32::try_from(r.y1.checked_sub(r.y0)?).ok()?;
    Some((x, y, w, h))
}

impl Backend for D3d12Backend {
    fn draw_frame(&mut self, frame: &Frame) -> Result<(), BackendError> {
        self.draw_inner(frame)
    }

    fn adapter(&self) -> Adapter {
        self.adapter
    }

    fn read_pixels(&mut self, out: &mut Vec<u8>) -> Result<(), BackendError> {
        let target = self.target.as_ref().ok_or(fail("no target"))?;
        let staging = self.staging.as_ref().ok_or(fail("no staging buffer"))?;
        self.device
            .copy_target(target, staging)
            .map_err(backend_error)?;
        let mut padded = vec![0u8; target.copy_len()];
        staging.read(&mut padded).map_err(backend_error)?;
        let pitch = usize::try_from(target.row_pitch()).map_err(|_| fail("row pitch"))?;
        let row = usize::try_from(target.width())
            .ok()
            .and_then(|w| w.checked_mul(4))
            .ok_or(fail("row length"))?;
        *out = packed_rows(&padded, pitch, row).ok_or(fail("row pitch"))?;
        Ok(())
    }
}

//! The Metal backend (macOS on Apple silicon), through `clazel_sys::macos::metal`.
//!
//! # Modelling choices
//!
//! - **The shaders are compiled when the backend starts**, from `quad.metal` as
//!   embedded at build time: the source is fixed, but the development machine has no
//!   offline Metal toolchain to make a `.metallib`. A compiler failure is a
//!   [`BackendError`].
//! - **One command buffer per frame**, committed and waited for: uploads are blit
//!   copies from one staging buffer holding the frame's bytes, in order with the
//!   render passes, which run between them; the first pass clears to transparent
//!   black and later ones keep what is there. A frame with no draw still clears.
//! - **The target is a [`Target`]**: an IOSurface of the viewport's size with a
//!   texture on it, made by the backend when the size changes. Item 5.18's ring of
//!   shared buffers will supply surfaces instead, through [`MetalBackend::set_target`].
//! - **The atlas is a shared buffer**, replaced on each `Op::Atlas`; draws already
//!   encoded keep the old one alive through the command buffer, which retains what
//!   it uses. Before the first upload a 4-byte placeholder is bound, with
//!   `atlas_bytes` 0, so the fragment shader reads nothing from it.

use clazel_sys::macos::metal::{
    BlendFactor, Buffer, CommandBuffer, CommandQueue, Device, MetalError, Pipeline, PipelineDesc,
    PixelFormat, Stage, Surface, Texture, with_autorelease_pool,
};

use crate::backend::{Backend, BackendError, Frame, Op, quad_bytes};
use crate::blocklist::{APPLE, Adapter, Api};
use crate::geom::{Rect, Viewport};

/// The shaders, fixed at build time.
const SOURCE: &str = include_str!("../shaders/quad.metal");

fn backend_error(e: MetalError) -> BackendError {
    BackendError {
        what: e.what,
        code: e.code,
    }
}

fn fail(what: &'static str) -> BackendError {
    BackendError { what, code: 0 }
}

/// Where a frame is drawn: an IOSurface and a texture on it.
#[derive(Debug)]
pub struct Target {
    surface: Surface,
    texture: Texture,
}

impl Target {
    /// A new surface of the viewport's size, with a texture on it.
    pub fn new(device: &MetalBackend, viewport: Viewport) -> Result<Target, BackendError> {
        let w = usize::try_from(viewport.width).map_err(|_| fail("width"))?;
        let h = usize::try_from(viewport.height).map_err(|_| fail("height"))?;
        let surface = Surface::new(w, h).map_err(backend_error)?;
        let texture = device
            .device
            .new_texture_on(&surface)
            .map_err(backend_error)?;
        Ok(Target { surface, texture })
    }

    /// The surface, which item 5.18 will hand to the compositor.
    pub fn surface(&self) -> &Surface {
        &self.surface
    }
}

/// Drawing with Metal.
#[derive(Debug)]
pub struct MetalBackend {
    device: Device,
    queue: CommandQueue,
    pipeline: Pipeline,
    target: Option<Target>,
    atlas: Buffer,
    atlas_bytes: u32,
}

impl MetalBackend {
    /// The default GPU, a queue and the one pipeline. An error means there is no
    /// usable Metal device.
    pub fn new() -> Result<MetalBackend, BackendError> {
        with_autorelease_pool(|| {
            let device = Device::system_default().map_err(backend_error)?;
            let queue = device.new_command_queue().map_err(backend_error)?;
            let pipeline = device
                .new_pipeline(&PipelineDesc {
                    source: SOURCE,
                    vertex: "quad_vertex",
                    fragment: "quad_fragment",
                    format: PixelFormat::Rgba8Unorm,
                    blend: Some((BlendFactor::One, BlendFactor::OneMinusSourceAlpha)),
                })
                .map_err(backend_error)?;
            let atlas = device.new_buffer(4).map_err(backend_error)?;
            Ok(MetalBackend {
                device,
                queue,
                pipeline,
                target: None,
                atlas,
                atlas_bytes: 0,
            })
        })
        .map_err(backend_error)?
    }

    /// Draw into `target` from now on (item 5.18's ring); its size must be the
    /// viewport's of every frame drawn into it, or the backend replaces it.
    pub fn set_target(&mut self, target: Target) {
        self.target = Some(target);
    }

    /// The current target.
    pub fn target(&self) -> Option<&Target> {
        self.target.as_ref()
    }

    fn draw_inner(&mut self, frame: &Frame) -> Result<(), BackendError> {
        let viewport = frame.viewport.ok_or(fail("no viewport"))?;
        let fits = self.target.as_ref().is_some_and(|t| {
            usize::try_from(viewport.width).ok() == Some(t.texture.width())
                && usize::try_from(viewport.height).ok() == Some(t.texture.height())
        });
        if !fits {
            self.target = Some(Target::new(self, viewport)?);
        }
        let quads = if frame.quads.is_empty() {
            None
        } else {
            Some(
                self.device
                    .new_buffer_with_bytes(&quad_bytes(&frame.quads))
                    .map_err(backend_error)?,
            )
        };
        let quad_count = u32::try_from(frame.quads.len()).map_err(|_| fail("quad count"))?;
        let staging = if frame.bytes.is_empty() {
            None
        } else {
            Some(
                self.device
                    .new_buffer_with_bytes(&frame.bytes)
                    .map_err(backend_error)?,
            )
        };
        let mut cb = self.queue.command_buffer().map_err(backend_error)?;
        let mut cleared = false;
        let mut k = 0usize;
        while let Some(op) = frame.ops.get(k) {
            match op {
                Op::Atlas { capacity } => {
                    let n = usize::try_from(*capacity).map_err(|_| fail("capacity"))?;
                    self.atlas = self.device.new_buffer(n).map_err(backend_error)?;
                    self.atlas_bytes = *capacity;
                    k = k.saturating_add(1);
                }
                Op::Upload { offset, start, len } => {
                    let src = staging.as_ref().ok_or(fail("no staging buffer"))?;
                    let at = usize::try_from(*offset).map_err(|_| fail("offset"))?;
                    cb.copy_buffer(src, *start, &self.atlas, at, *len)
                        .map_err(backend_error)?;
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
                    let quads = quads.as_ref().ok_or(fail("no quads"))?;
                    self.pass(&mut cb, viewport, !cleared, quads, quad_count, draws)?;
                    cleared = true;
                    k = run_end;
                }
            }
        }
        if !cleared {
            let target = self.target.as_ref().ok_or(fail("no target"))?;
            cb.render(&target.texture, Some([0.0; 4]), |_| Ok(()))
                .map_err(backend_error)?;
        }
        cb.commit_and_wait().map_err(backend_error)
    }

    /// One render pass drawing a run of [`Op::Draw`].
    fn pass(
        &self,
        cb: &mut CommandBuffer,
        viewport: Viewport,
        clear: bool,
        quads: &Buffer,
        quad_count: u32,
        draws: &[Op],
    ) -> Result<(), BackendError> {
        let target = self.target.as_ref().ok_or(fail("no target"))?;
        let mut uniforms = Vec::with_capacity(16);
        for w in [
            viewport.width,
            viewport.height,
            quad_count,
            self.atlas_bytes,
        ] {
            uniforms.extend_from_slice(&w.to_le_bytes());
        }
        let clear = clear.then_some([0.0; 4]);
        cb.render(&target.texture, clear, |enc| {
            enc.set_pipeline(&self.pipeline);
            enc.set_buffer(Stage::Vertex, quads, 0)?;
            enc.set_buffer(Stage::Fragment, quads, 0)?;
            enc.set_buffer(Stage::Fragment, &self.atlas, 1)?;
            enc.set_bytes(Stage::Vertex, &uniforms, 2)?;
            enc.set_bytes(Stage::Fragment, &uniforms, 2)?;
            for op in draws {
                if let Op::Draw {
                    scissor,
                    first,
                    count,
                } = op
                {
                    let (x, y, w, h) = scissor_of(*scissor).ok_or(MetalError {
                        what: "scissor",
                        code: 0,
                    })?;
                    enc.set_scissor(x, y, w, h)?;
                    let count = usize::try_from(*count).unwrap_or(0);
                    let first = usize::try_from(*first).unwrap_or(0);
                    enc.draw_triangles(6, count, first);
                }
            }
            Ok(())
        })
        .map_err(backend_error)
    }
}

/// A scissor rectangle as Metal takes it: origin and size, all unsigned.
fn scissor_of(r: Rect) -> Option<(usize, usize, usize, usize)> {
    let x = usize::try_from(r.x0).ok()?;
    let y = usize::try_from(r.y0).ok()?;
    let w = usize::try_from(r.x1.checked_sub(r.x0)?).ok()?;
    let h = usize::try_from(r.y1.checked_sub(r.y0)?).ok()?;
    Some((x, y, w, h))
}

impl Backend for MetalBackend {
    fn draw_frame(&mut self, frame: &Frame) -> Result<(), BackendError> {
        with_autorelease_pool(|| self.draw_inner(frame)).map_err(backend_error)?
    }

    /// Apple's vendor id, no device id (Apple silicon has no PCI device id) and no
    /// driver version: the `clazel-sys` wrappers read neither the device's name nor
    /// the OS version without new foreign calls (item 5.17c, `src/blocklist.rs`).
    fn adapter(&self) -> Adapter {
        Adapter {
            api: Api::Metal,
            vendor: APPLE,
            device: 0,
            driver: None,
            software: false,
        }
    }

    fn read_pixels(&mut self, out: &mut Vec<u8>) -> Result<(), BackendError> {
        let target = self.target.as_ref().ok_or(fail("no target"))?;
        let n = target
            .texture
            .width()
            .checked_mul(target.texture.height())
            .and_then(|p| p.checked_mul(4))
            .ok_or(fail("size"))?;
        out.clear();
        out.resize(n, 0);
        target.texture.read_pixels(out).map_err(backend_error)
    }
}

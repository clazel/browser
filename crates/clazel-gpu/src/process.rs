//! The GPU process's loop (items 5.18 and 5.23), over any backend, so that tests run
//! it with the fake one and no process. `src/main.rs` runs it with Metal, in the
//! sandbox (item 5.21a).
//!
//! # Modelling choices
//!
//! - **Inputs**: frames from the kernel on standard input (only `GpuViewport`; any
//!   other message ends the process, as the kernel sends no other) and lists from
//!   the renderer on the list socket ([`crate::channel`]). Each has its own reader
//!   thread, and the loop takes whichever comes first.
//! - **Every list is drawn, in order**, so the masks the validator and the atlas
//!   hold stay the renderer's. Before the first `GpuViewport` (or after one of 0
//!   by 0) a list is drawn on a 1 by 1 target and no frame is sent.
//! - **A drawn list gives one frame**: its pixels on the surface socket in the
//!   next ring slot (0, 1, 2, 0, …), then `FrameReady { buffer: slot, width,
//!   height }` to the kernel, in that order, so the host has the pixels a
//!   `Paint` names by the time it can see that `Paint`, or soon after.
//! - **A `GpuViewport` alone draws nothing**: the kernel sends the renderer its
//!   `Viewport` too, and the renderer's new list is drawn at the new size.
//!   Drawing the old list again would replay its mask uploads.
//! - **The GPU process ends** on any error (a list that does not decode or
//!   breaks a rule, a backend failure, a message it does not expect) and when
//!   either input ends; [`run`] returns the reason, which the binary prints on
//!   standard error for the host's log.

use std::io::{Read, Write};
use std::sync::mpsc::{Sender, channel};

use clazel_ipc::frame::codec::payload_length;
use clazel_ipc::message::codec::{Msg, decode_framed, encode_framed};

use crate::backend::Backend;
use crate::channel::{SLOTS, SurfaceFrame, read_list, write_surface};
use crate::geom::Viewport;
use crate::start::Ready;
use crate::{Error, Gpu};

/// The GPU process's state between inputs.
#[derive(Debug)]
pub struct Server<B: Backend> {
    gpu: Gpu<B>,
    viewport: Option<Viewport>,
    next: u32,
}

/// What ended the GPU process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Exit {
    /// The kernel's channel closed.
    KernelClosed,
    /// The list socket closed.
    ListClosed,
    /// A channel failed or carried something malformed.
    Channel(String),
    /// The kernel sent something other than `GpuViewport`.
    Unexpected,
    /// A list was refused or the backend failed.
    Draw(Error),
}

impl std::fmt::Display for Exit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Exit::KernelClosed => f.write_str("the kernel's channel closed"),
            Exit::ListClosed => f.write_str("the list socket closed"),
            Exit::Channel(e) => write!(f, "a channel failed: {e}"),
            Exit::Unexpected => {
                f.write_str("the kernel sent a message the GPU process does not take")
            }
            Exit::Draw(e) => write!(f, "{e}"),
        }
    }
}

/// The frame to tell the kernel the start's answer: `GpuReady { software }`.
pub fn ready_frame(ready: Ready) -> Option<Vec<u8>> {
    encode_framed(&Msg::GpuReady {
        software: ready.software,
    })
}

/// The frame `GpuRefused`.
pub fn refused_frame() -> Option<Vec<u8>> {
    encode_framed(&Msg::GpuRefused)
}

/// The frame `FrameReady` for `frame`.
pub fn frame_ready(frame: &SurfaceFrame) -> Option<Vec<u8>> {
    encode_framed(&Msg::FrameReady {
        buffer: u64::from(frame.slot),
        width: u64::from(frame.width),
        height: u64::from(frame.height),
    })
}

impl<B: Backend> Server<B> {
    /// A server drawing with `gpu`, which has started (`Gpu::start`).
    pub fn new(gpu: Gpu<B>) -> Server<B> {
        Server {
            gpu,
            viewport: None,
            next: 0,
        }
    }

    /// The viewport lists are drawn at, if the kernel has sent one.
    pub fn viewport(&self) -> Option<Viewport> {
        self.viewport
    }

    /// A whole frame from the kernel.
    pub fn kernel(&mut self, frame: &[u8]) -> Result<(), Exit> {
        match decode_framed(frame) {
            Some(Msg::GpuViewport { width, height, .. }) => {
                let side = |v: u64| u32::try_from(v).ok();
                self.viewport = match (side(width), side(height)) {
                    (Some(0), _) | (_, Some(0)) => None,
                    (Some(w), Some(h)) => Some(Viewport::new(w, h).ok_or(Exit::Unexpected)?),
                    _ => return Err(Exit::Unexpected),
                };
                Ok(())
            }
            _ => Err(Exit::Unexpected),
        }
    }

    /// Draw a list; its pixels if a viewport is set.
    pub fn list(&mut self, bytes: &[u8]) -> Result<Option<SurfaceFrame>, Exit> {
        let Some(viewport) = self.viewport else {
            let one = Viewport::new(1, 1).ok_or(Exit::Unexpected)?;
            self.gpu.draw(bytes, one).map_err(Exit::Draw)?;
            return Ok(None);
        };
        self.gpu.draw(bytes, viewport).map_err(Exit::Draw)?;
        let mut pixels = Vec::new();
        self.gpu
            .backend()
            .read_pixels(&mut pixels)
            .map_err(|e| Exit::Draw(Error::Backend(e)))?;
        let slot = self.next;
        self.next = slot.saturating_add(1) % SLOTS;
        Ok(Some(SurfaceFrame {
            slot,
            width: viewport.width,
            height: viewport.height,
            pixels,
        }))
    }
}

/// What a reader thread hands the loop.
enum Input {
    Kernel(Vec<u8>),
    List(Vec<u8>),
    Ended(Exit),
}

/// Read whole IPC frames from `r` until it ends.
fn kernel_reader<R: Read>(mut r: R, tx: &Sender<Input>) -> Exit {
    loop {
        let mut head = [0u8; 4];
        match r.read_exact(&mut head) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Exit::KernelClosed,
            Err(e) => return Exit::Channel(e.to_string()),
        }
        let Some(n) = payload_length(&head) else {
            return Exit::Channel("a kernel frame over MAX_FRAME".to_owned());
        };
        let mut frame = vec![0u8; n.saturating_add(4)];
        if let Some(h) = frame.get_mut(..4) {
            h.copy_from_slice(&head);
        }
        if let Err(e) = r.read_exact(frame.get_mut(4..).unwrap_or_default()) {
            return Exit::Channel(e.to_string());
        }
        if tx.send(Input::Kernel(frame)).is_err() {
            return Exit::KernelClosed;
        }
    }
}

fn list_reader<R: Read>(mut r: R, tx: &Sender<Input>) -> Exit {
    loop {
        match read_list(&mut r) {
            Ok(Some(list)) => {
                if tx.send(Input::List(list)).is_err() {
                    return Exit::ListClosed;
                }
            }
            Ok(None) => return Exit::ListClosed,
            Err(e) => return Exit::Channel(e.to_string()),
        }
    }
}

/// Run the GPU process until an input ends or something fails: frames from the
/// kernel on `kernel_in`, lists on `list_in`; pixels to `surface_out` and
/// `FrameReady` to `kernel_out`. Returns why it ended.
pub fn run<B, KR, KW, LR, SW>(
    mut server: Server<B>,
    kernel_in: KR,
    mut kernel_out: KW,
    list_in: LR,
    mut surface_out: SW,
) -> Exit
where
    B: Backend,
    KR: Read + Send + 'static,
    KW: Write,
    LR: Read + Send + 'static,
    SW: Write,
{
    let (tx, rx) = channel();
    let k = tx.clone();
    std::thread::spawn(move || {
        let why = kernel_reader(kernel_in, &k);
        let _ = k.send(Input::Ended(why));
    });
    std::thread::spawn(move || {
        let why = list_reader(list_in, &tx);
        let _ = tx.send(Input::Ended(why));
    });
    loop {
        let step = match rx.recv() {
            Err(_) => return Exit::KernelClosed,
            Ok(Input::Ended(why)) => return why,
            Ok(Input::Kernel(frame)) => server.kernel(&frame),
            Ok(Input::List(list)) => match server.list(&list) {
                Ok(Some(frame)) => send(&frame, &mut kernel_out, &mut surface_out),
                Ok(None) => Ok(()),
                Err(e) => Err(e),
            },
        };
        if let Err(why) = step {
            return why;
        }
    }
}

/// The pixels, then the `FrameReady` naming them.
fn send<KW: Write, SW: Write>(
    frame: &SurfaceFrame,
    kernel_out: &mut KW,
    surface_out: &mut SW,
) -> Result<(), Exit> {
    let channel = |e: std::io::Error| Exit::Channel(e.to_string());
    write_surface(surface_out, frame).map_err(channel)?;
    let ready = frame_ready(frame).ok_or(Exit::Unexpected)?;
    kernel_out.write_all(&ready).map_err(channel)?;
    kernel_out.flush().map_err(channel)
}

#[cfg(test)]
mod tests {
    use clazel_displaylist::exec::encode_list;
    use clazel_ipc::message::codec::{Msg, encode_framed};

    use super::{Exit, Server};
    use crate::geom::Viewport;
    use crate::soft::SoftBackend;
    use crate::{Gpu, start::Launch};

    pub(super) fn server() -> Option<Server<SoftBackend>> {
        let (gpu, _) = Gpu::start(SoftBackend::new(), Launch::SOFTWARE).ok()?;
        Some(Server::new(gpu))
    }

    pub(super) fn viewport(width: u64, height: u64) -> Vec<u8> {
        encode_framed(&Msg::GpuViewport {
            width,
            height,
            scale: 1,
        })
        .unwrap_or_default()
    }

    #[test]
    fn lists_before_a_viewport_send_nothing_and_the_ring_turns() {
        let s = server();
        assert!(s.is_some(), "the fake backend did not start");
        let Some(mut s) = s else { return };
        let list = encode_list(&[]).unwrap_or_default();
        assert_eq!(s.list(&list), Ok(None));
        assert_eq!(s.kernel(&viewport(4, 3)), Ok(()));
        assert_eq!(s.viewport(), Viewport::new(4, 3));
        let slots: Vec<u32> = (0..4)
            .filter_map(|_| s.list(&list).ok().flatten())
            .map(|f| f.slot)
            .collect();
        assert_eq!(slots, [0, 1, 2, 0]);
        assert_eq!(s.kernel(&viewport(0, 3)), Ok(()));
        assert_eq!(s.viewport(), None);
    }

    #[test]
    fn anything_but_a_viewport_or_a_list_ends_it() {
        let s = server();
        assert!(s.is_some(), "the fake backend did not start");
        let Some(mut s) = s else { return };
        let other = encode_framed(&Msg::GpuRefused).unwrap_or_default();
        assert_eq!(s.kernel(&other), Err(Exit::Unexpected));
        assert_eq!(s.kernel(b"\x00\x00\x00\x01\xff"), Err(Exit::Unexpected));
        assert_eq!(s.kernel(&viewport(8193, 1)), Err(Exit::Unexpected));
        assert_eq!(s.kernel(&viewport(4, 3)), Ok(()));
        assert!(matches!(s.list(b"not a list"), Err(Exit::Draw(_))));
    }
}

/// The whole loop on sockets, so Unix only, and not under Miri (threads and
/// sockets are slow there and add nothing the tests above miss).
#[cfg(all(test, unix))]
mod socket_tests {
    use std::io::{Read, Write};
    use std::os::unix::net::UnixStream;

    use clazel_displaylist::exec::encode_list;
    use clazel_ipc::frame::codec::payload_length;
    use clazel_ipc::message::codec::{Msg, decode_framed};

    use super::tests::{server, viewport};
    use super::{Exit, run};
    use crate::channel::{read_surface, write_list};
    use crate::geom::Viewport;
    use crate::reference::{Masks, draw};
    use crate::scenes;

    fn read_frame(kernel: &mut UnixStream) -> Option<Vec<u8>> {
        let mut head = [0u8; 4];
        kernel.read_exact(&mut head).ok()?;
        let mut frame = head.to_vec();
        frame.resize(payload_length(&head)?.checked_add(4)?, 0);
        kernel.read_exact(frame.get_mut(4..)?).ok()?;
        Some(frame)
    }

    /// Every scene's lists in; each list's pixels and `FrameReady` out, the pixels
    /// equal to the software reference.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn the_loop_draws_every_list_it_is_sent() {
        for scene in scenes::all() {
            let ok = (|| -> Option<()> {
                let s = server()?;
                let (mut kernel, kernel_gpu) = UnixStream::pair().ok()?;
                let (mut renderer, list_gpu) = UnixStream::pair().ok()?;
                let (mut host, surface_gpu) = UnixStream::pair().ok()?;
                let kernel_out = kernel_gpu.try_clone().ok()?;
                let gpu = std::thread::spawn(move || {
                    run(s, kernel_gpu, kernel_out, list_gpu, surface_gpu)
                });
                let v = Viewport::new(scene.width, scene.height)?;
                kernel
                    .write_all(&viewport(scene.width.into(), scene.height.into()))
                    .ok()?;
                // The kernel's `GpuViewport` and the renderer's list arrive on two
                // sockets; the kernel sends its viewport before the renderer can
                // have laid out at that size, which a pause stands in for here.
                std::thread::sleep(std::time::Duration::from_millis(50));
                let mut masks = Masks::default();
                for (i, items) in scene.lists.iter().enumerate() {
                    write_list(&mut renderer, &encode_list(items)?).ok()?;
                    let got = read_surface(&mut host).ok().flatten()?;
                    assert_eq!(
                        Some(got.pixels),
                        draw(items, v, &mut masks),
                        "{} {i}",
                        scene.name
                    );
                    let slot = u64::try_from(i % 3).ok()?;
                    let ready = Msg::FrameReady {
                        buffer: slot,
                        width: scene.width.into(),
                        height: scene.height.into(),
                    };
                    assert_eq!(decode_framed(&read_frame(&mut kernel)?), Some(ready));
                }
                drop(renderer);
                assert_eq!(gpu.join().ok(), Some(Exit::ListClosed), "{}", scene.name);
                Some(())
            })();
            assert!(ok.is_some(), "scene {} did not run through", scene.name);
        }
    }
}

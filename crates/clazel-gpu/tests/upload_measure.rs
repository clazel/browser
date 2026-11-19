//! Item 6.12's prototype step: what a 4096 × 4096 image upload (64 MiB of pixels)
//! costs through the list socket, measured, on every OS CI runs (Linux, macOS,
//! Windows). **It decides nothing**: it prints the numbers and checks only that the
//! bytes arrived and the pixels came out. Whether an upload that takes more than a
//! frame should move to a second channel (a shared memory region the renderer writes
//! and the GPU process maps, through `clazel-sys`) is the maintainer's decision, on
//! these numbers; that channel is not built.
//!
//! What is measured, each three times where it can be repeated, in milliseconds of
//! the monotonic clock:
//!
//! - **encode**: the renderer encoding the list (`clazel_displaylist::exec::encode_list`);
//! - **socket**: the whole list written by one thread and read by another through a
//!   socket pair (`clazel_gpu::channel::write_list` and `read_list`, the code the
//!   renderer and the GPU process run). On Linux and macOS the pair is a Unix stream
//!   socket pair, the transport the host makes (`socketpair(2)`); on every OS it is
//!   also a TCP connection on the loopback interface, which is the one socket
//!   `std` offers on Windows. **The Windows host's own channel has not been
//!   measured**: this loopback is a stand-in for it;
//! - **decode** and **validate**: the GPU process decoding the bytes and the validator
//!   walking them (`clazel_displaylist::exec`);
//! - **frame with upload**: `Gpu::draw` of the list that holds the upload, whole
//!   (decode, validate, batching, the upload to the backend's store, the draw and the
//!   wait for it), then **frame without**, the same draw with the image already
//!   there, and **read pixels**, copying the 800 × 600 target out. The backends are
//!   the software fake everywhere, Vulkan on Linux (lavapipe in CI: the "device" is
//!   the CPU, so its upload is a `memcpy` and no bus is crossed), and Metal on Apple
//!   silicon. **Direct3D 12 does not take images yet** (`src/d3d12.rs`), so Windows
//!   has no backend line.
//!
//! **Read the build**: the line says whether this is an optimised build. CI runs
//! tests unoptimised, in which the encoder and decoder are many times slower than
//! shipped; to measure the shipped code run
//! `cargo test --release -p clazel-gpu --test upload_measure -- --nocapture`.
//! A frame is 16.7 ms at 60 Hz.
//!
//! The lines go to standard error in one call each, past libtest's capture, so they
//! are in CI's log whether the test passes or fails; they start `clazel-gpu: upload`.

use std::io::Write;
use std::time::{Duration, Instant};

use clazel_displaylist::exec::{ExecItem, Validator, decode, encode_list};
use clazel_gpu::channel::{Laid, read_list, write_list};
use clazel_gpu::soft::SoftBackend;
use clazel_gpu::start::Launch;
use clazel_gpu::{Backend, Gpu, Viewport};

/// The image's side: 4096 × 4096 × 4 = 64 MiB.
const SIDE: u16 = 4096;

fn log(line: &str) {
    let mut err = std::io::stderr().lock();
    let _ignored = err.write_all(format!("{line}\n").as_bytes());
}

fn ms(d: Duration) -> String {
    format!("{:.1}", d.as_secs_f64() * 1000.0)
}

/// Milliseconds of each run, for a line.
fn runs(ds: &[Duration]) -> String {
    ds.iter().map(|d| ms(*d)).collect::<Vec<_>>().join(", ")
}

/// A byte ramp of period 251 (prime), as the scenes use, for `n` bytes.
fn pixels(n: usize) -> Vec<u8> {
    let period: Vec<u8> = (0..251usize)
        .map(|i| u8::try_from(i.saturating_mul(37) % 256).unwrap_or(0))
        .collect();
    let mut out = period.repeat(n.div_ceil(251));
    out.truncate(n);
    out
}

fn upload_item() -> ExecItem {
    ExecItem::UploadImage {
        id: 0,
        image_width: SIDE,
        image_height: SIDE,
        pixels: pixels(
            usize::from(SIDE)
                .saturating_mul(usize::from(SIDE))
                .saturating_mul(4),
        ),
    }
}

fn draw_item() -> ExecItem {
    ExecItem::DrawImage {
        id: 0,
        x: 0,
        y: 0,
        width: 800,
        height: 600,
        src_x: 0,
        src_y: 0,
        src_width: SIDE,
        src_height: SIDE,
        linear: true,
    }
}

/// Write `list` through `writer`'s end and read it back from `reader`'s, with the
/// writing done on another thread, as the two processes do. The time is from the
/// first byte written to the last read.
fn through<W, R>(mut writer: W, mut reader: R, list: &[u8]) -> Result<(Duration, Vec<u8>), String>
where
    W: Write + Send,
    R: std::io::Read,
{
    let laid = Laid {
        width: 800,
        height: 600,
    };
    let start = Instant::now();
    let got = std::thread::scope(|s| {
        let w = s.spawn(move || write_list(&mut writer, laid, list));
        let r = read_list(&mut reader);
        let w = w.join().map_err(|_| "the writer panicked".to_owned())?;
        w.map_err(|e| format!("write: {e}"))?;
        r.map_err(|e| format!("read: {e}"))?
            .ok_or_else(|| "the stream ended".to_owned())
    })?;
    let elapsed = start.elapsed();
    Ok((elapsed, got.1))
}

#[cfg(unix)]
fn unix_pair() -> Result<
    (
        std::os::unix::net::UnixStream,
        std::os::unix::net::UnixStream,
    ),
    String,
> {
    std::os::unix::net::UnixStream::pair().map_err(|e| e.to_string())
}

fn tcp_pair() -> Result<(std::net::TcpStream, std::net::TcpStream), String> {
    let listener = std::net::TcpListener::bind("127.0.0.1:0").map_err(|e| e.to_string())?;
    let addr = listener.local_addr().map_err(|e| e.to_string())?;
    let a = std::net::TcpStream::connect(addr).map_err(|e| e.to_string())?;
    let (b, _) = listener.accept().map_err(|e| e.to_string())?;
    Ok((a, b))
}

/// Three frames' worth of one backend: the list with the upload, the draw alone,
/// and the read of the target. Returns the pixels of the first.
fn frames<B: Backend>(
    name: &str,
    backend: B,
    launch: Launch,
    with_upload: &[u8],
) -> Result<(), String> {
    let (mut gpu, ready) = Gpu::start(backend, launch).map_err(|e| format!("{e:?}"))?;
    let viewport = Viewport::new(800, 600).ok_or("viewport")?;
    let draw_only = encode_list(&[draw_item()]).ok_or("encode")?;

    let t = Instant::now();
    gpu.draw(with_upload, viewport)
        .map_err(|e| format!("{name}: {e}"))?;
    let first = t.elapsed();

    let t = Instant::now();
    let mut px = Vec::new();
    gpu.backend()
        .read_pixels(&mut px)
        .map_err(|e| format!("{e:?}"))?;
    let read = t.elapsed();
    assert!(
        px.iter().any(|&b| b != 0),
        "{name}: the 4096 by 4096 image drew nothing"
    );

    let mut later = Vec::new();
    for _ in 0..3 {
        let t = Instant::now();
        gpu.draw(&draw_only, viewport)
            .map_err(|e| format!("{name}: {e}"))?;
        later.push(t.elapsed());
    }
    log(&format!(
        "clazel-gpu: upload {name} (software: {}): frame with the upload {} ms; frame without \
         (3 runs) {} ms; read pixels {} ms",
        ready.software,
        ms(first),
        runs(&later),
        ms(read)
    ));
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_4096_by_4096_upload_through_the_list_socket() -> Result<(), String> {
    log(&format!(
        "clazel-gpu: upload measure, {} {}, {} build, image {SIDE} by {SIDE} (64 MiB), \
         a frame at 60 Hz is 16.7 ms",
        std::env::consts::OS,
        std::env::consts::ARCH,
        if cfg!(debug_assertions) {
            "an UNOPTIMISED"
        } else {
            "an optimised"
        }
    ));
    let items = [upload_item(), draw_item()];

    let t = Instant::now();
    let list = encode_list(&items).ok_or("encode")?;
    log(&format!(
        "clazel-gpu: upload encode: {} ms for {} bytes",
        ms(t.elapsed()),
        list.len()
    ));

    // The list socket, three times each.
    #[cfg(unix)]
    {
        let mut times = Vec::new();
        for n in 0..3 {
            let (a, b) = unix_pair()?;
            let (d, got) = through(a, b, &list)?;
            if n == 0 {
                assert!(got == list, "the list that arrived is not the list sent");
            }
            times.push(d);
        }
        log(&format!(
            "clazel-gpu: upload socket (Unix stream socket pair, 3 runs): {} ms",
            runs(&times)
        ));
    }
    let mut times = Vec::new();
    for n in 0..3 {
        let (a, b) = tcp_pair()?;
        let (d, got) = through(a, b, &list)?;
        if n == 0 {
            assert!(got == list, "the list that arrived is not the list sent");
        }
        times.push(d);
    }
    log(&format!(
        "clazel-gpu: upload socket (TCP on the loopback, 3 runs; on Windows the stand-in for \
         the host's channel): {} ms",
        runs(&times)
    ));

    // The GPU process's decoding and validation.
    let (mut decodes, mut validates) = (Vec::new(), Vec::new());
    for _ in 0..3 {
        let t = Instant::now();
        let decoded = decode(&list).ok_or("decode")?;
        decodes.push(t.elapsed());
        let t = Instant::now();
        let ok = Validator::empty().validate(&decoded);
        validates.push(t.elapsed());
        assert!(ok, "the validator refused the list");
    }
    log(&format!(
        "clazel-gpu: upload decode (3 runs): {} ms; validate (3 runs): {} ms",
        runs(&decodes),
        runs(&validates)
    ));

    // Whole frames, on each backend this machine has.
    frames("software fake", SoftBackend::new(), Launch::SOFTWARE, &list)?;
    #[cfg(target_os = "linux")]
    match clazel_gpu::vulkan::VulkanBackend::new(false) {
        Ok(b) => {
            let name = format!("Vulkan \"{}\"", b.device_name());
            frames(&name, b, Launch::HARDWARE, &list)?;
        }
        Err(e) if std::env::var_os("CI").is_some() => {
            return Err(format!("no usable Vulkan device under CI ({e:?})"));
        }
        Err(e) => log(&format!("clazel-gpu: upload skipped Vulkan: {e:?}")),
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    match clazel_gpu::metal::MetalBackend::new() {
        Ok(b) => frames("Metal", b, Launch::HARDWARE, &list)?,
        Err(e) if std::env::var_os("CI").is_some() => {
            return Err(format!("no usable Metal device under CI ({e:?})"));
        }
        Err(e) => log(&format!("clazel-gpu: upload skipped Metal: {e:?}")),
    }
    #[cfg(windows)]
    log("clazel-gpu: upload Direct3D 12: not measured, the backend does not take images yet");
    Ok(())
}

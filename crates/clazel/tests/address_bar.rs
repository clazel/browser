//! Item 5.26's address bar cases: a page or a GPU process trying to draw over, or
//! lie to, the host's address bar strip.
//!
//! - **Negative margins**: a page with `margin-top: -1e9px` is painted at most at
//!   its viewport, which is the content area, and the window places the page's
//!   layer below the strip (`clazel_window::nsevent::layer_frame`), so the strip's
//!   points are outside the page layer. The strip is drawn by the host from the
//!   kernel's URL, in its own layer above.
//! - **An adversarial GPU process** (a Perl stand-in, [`FAKE_GPU`], paired with the
//!   real renderer: it waits for the kernel's `GpuViewport` and the renderer's
//!   first list, then misbehaves one way):
//!   - claiming a surface larger than the viewport: the kernel **drops** the
//!     `FrameReady` (5.18's decision 3: dropped, not a kill), so there is no
//!     `Paint`, and both processes keep running;
//!   - really sending more than it claimed (pixels for twice the claimed height):
//!     the `Paint` names the claimed size, the slot holds pixels of another size,
//!     and `browse` shows nothing (`cli/window.rs`'s `pixels_for`);
//!   - sending something that is not a buffer (a header naming slot 9), a buffer
//!     too small (1 by 1 for the viewport), or a truncated one: the host's reader
//!     refuses it or finds the size wrong, shows nothing, and `browse --headless`
//!     ends with its error, not a crash.
//! - **A title shaped like a URL** reaches the host only as `Paint.title`, never as
//!   `Paint.url`, which is the kernel's; `browse` puts the title after the URL in
//!   the title bar (`title_bar`, unit-tested in `cli/window.rs`) and draws only the
//!   URL in the strip.
//!
//! macOS on Apple silicon only; without a Metal device the real-GPU cases skip,
//! except under CI.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

mod support;

#[path = "support/server.rs"]
mod server;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_kernel::exec::records::{EventRecord, OutputRecord};
use server::{Reply, Request, serve};

/// The fake GPU process. Modes, from `FAKE_GPU_MODE`: `oversize`, `more`,
/// `notbuffer`, `small`, `truncated`.
const FAKE_GPU: &str = r#"#!/usr/bin/perl
use strict;
use IO::Handle;
my %arg = @ARGV;
open(my $list, '<&=', $arg{'--list-fd'}) or die "list: $!";
open(my $surf, '>&=', $arg{'--surface-fd'}) or die "surface: $!";
binmode $list; binmode $surf; binmode STDIN; binmode STDOUT;
STDOUT->autoflush(1); $surf->autoflush(1);
sub exactly { my ($fh, $n) = @_; my $got = '';
  while (length($got) < $n) { my $r = sysread($fh, $got, $n - length($got), length($got)); return undef if !$r; }
  return $got; }
sub uint { my ($b, $i) = @_; my $t = ord(substr($b, $i, 1));
  return ($t, $i + 1) if $t < 24;
  return (ord(substr($b, $i + 1, 1)), $i + 2) if $t == 0x18;
  return (unpack('n', substr($b, $i + 1, 2)), $i + 3) if $t == 0x19;
  return (unpack('N', substr($b, $i + 1, 4)), $i + 5); }
sub cbor { my $v = shift; return chr($v) if $v < 24; return "\x18" . chr($v) if $v < 256;
  return "\x19" . pack('n', $v) if $v < 65536; return "\x1a" . pack('N', $v); }
sub frame_ready { my ($s, $w, $h) = @_; my $m = "\x84" . cbor(15) . cbor($s) . cbor($w) . cbor($h);
  print STDOUT pack('N', length $m) . $m; }
sub surface { my ($s, $w, $h, $bytes) = @_; print {$surf} pack('VVV', $s, $w, $h) . $bytes; }
my ($w, $h);
while (!defined $w) {
  my $head = exactly(\*STDIN, 4) // exit 0; my $m = exactly(\*STDIN, unpack('N', $head)) // exit 0;
  next unless substr($m, 0, 3) eq "\x84\x18\x72";
  my $i = 3; ($w, $i) = uint($m, $i); ($h, $i) = uint($m, $i);
}
my $n = exactly($list, 4) // exit 0; exactly($list, unpack('V', $n)) // exit 0;
my $mode = $ENV{FAKE_GPU_MODE};
my $px = "\xff\x00\x00\xff";
if ($mode eq 'oversize') { surface(0, $w + 64, $h, $px x (($w + 64) * $h)); frame_ready(0, $w + 64, $h); }
elsif ($mode eq 'more') { surface(0, $w, $h * 2, $px x ($w * $h * 2)); frame_ready(0, $w, $h); }
elsif ($mode eq 'notbuffer') { print {$surf} pack('VVV', 9, 1, 1) . "junk"; frame_ready(0, $w, $h); }
elsif ($mode eq 'small') { surface(0, 1, 1, $px); frame_ready(0, $w, $h); }
elsif ($mode eq 'truncated') { surface(0, $w, $h, $px x int($w * $h / 2)); close $surf; frame_ready(0, $w, $h); }
while (defined exactly(\*STDIN, 1)) {}
"#;

/// DejaVu Serif, vendored for `clazel-font`'s tests.
const DEJAVU: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf"
);

/// The viewport, a small one.
const VIEWPORT: (u32, u32) = (160, 120);

/// The real renderer and GPU process, built; the fake GPU's script written to a
/// directory of its own.
struct Fixture {
    dir: PathBuf,
    renderer: PathBuf,
    gpu: PathBuf,
    fake: PathBuf,
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

fn fixture(tag: &str) -> Fixture {
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let built = Command::new(cargo)
        .args([
            "build",
            "--quiet",
            "-p",
            "clazel-gpu",
            "-p",
            "clazel-renderer",
            "-p",
            "clazel",
        ])
        .status();
    assert!(
        built.is_ok_and(|s| s.success()),
        "cannot build the binaries"
    );
    let renderer = support::binary("clazel-renderer");
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("address-bar-{tag}-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let fake = dir.join("fake-gpu.pl");
    assert!(std::fs::write(&fake, FAKE_GPU).is_ok());
    use std::os::unix::fs::PermissionsExt;
    assert!(std::fs::set_permissions(&fake, std::fs::Permissions::from_mode(0o755)).is_ok());
    Fixture {
        dir,
        gpu: renderer.with_file_name("clazel-gpu"),
        renderer,
        fake,
    }
}

fn metal() -> bool {
    match clazel_gpu::metal::MetalBackend::new() {
        Ok(_) => true,
        Err(e) => {
            eprintln!("address_bar: skipped: no Metal device ({})", e.what);
            assert!(std::env::var_os("CI").is_none(), "no Metal device under CI");
            false
        }
    }
}

fn page(body: &'static str) -> server::Server {
    serve(move |r: &Request| {
        assert_eq!(r.path, "/");
        Reply {
            head: "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n".to_owned(),
            piece: body.as_bytes().to_vec(),
            times: 1,
        }
    })
}

/// A host with the real renderer and, as its GPU process, `gpu` in `mode`.
fn host(f: &Fixture, gpu: &Path, mode: &str) -> Host {
    let (renderer, gpu, mode) = (f.renderer.clone(), gpu.to_path_buf(), mode.to_owned());
    Host::new(move |_| {
        let mut c = Command::new(&renderer);
        c.args(["--font", DEJAVU]);
        c
    })
    .with_gpu(move |_| {
        let mut c = Command::new(&gpu);
        c.env("FAKE_GPU_MODE", &mode);
        c
    })
}

/// What a tab came to within `wait`: its `Paint`s (url, title, buffer, width,
/// height), the frame its last `Paint` names (size), and the host's log.
struct Seen {
    paints: Vec<(String, String, u64, u64, u64)>,
    frame: Option<(u32, u32)>,
    log: Vec<String>,
}

fn run(host: &mut Host, wait: Duration) -> Seen {
    let tab = host.open("http://hostile.test/");
    host.event(EventRecord::Resize {
        tab,
        width: VIEWPORT.0.into(),
        height: VIEWPORT.1.into(),
        scale: 1,
    });
    let started = Instant::now();
    let mut seen = Seen {
        paints: Vec::new(),
        frame: None,
        log: Vec::new(),
    };
    while started.elapsed() < wait && seen.frame.is_none() {
        host.pump(Duration::from_millis(20));
        let mine: Vec<OutputRecord> = std::mem::take(&mut host.shown);
        for o in mine {
            if let OutputRecord::Paint {
                tab: t,
                url,
                title,
                buffer,
                width,
                height,
            } = o
                && t == tab
            {
                let url = url.iter().filter_map(|c| char::from_u32(*c)).collect();
                let title = String::from_utf8_lossy(&title).into_owned();
                seen.paints.push((url, title, buffer, width, height));
            }
        }
        let id = host
            .state
            .renderers
            .iter()
            .find(|r| r.tab == tab)
            .map(|r| r.id);
        if let (Some(id), Some((_, _, b, _, _))) = (id, seen.paints.last()) {
            seen.frame = host
                .take_frame(id, u32::try_from(*b).unwrap_or(u32::MAX))
                .map(|f| (f.width, f.height));
        }
    }
    seen.log = host.log.clone();
    seen
}

fn alive(seen: &Seen) -> bool {
    !seen.log.iter().any(|l| l.contains(" exited: "))
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_gpu_process_claiming_more_than_the_viewport_is_dropped() {
    let f = fixture("oversize");
    let server = page("<!doctype html><title>t</title><p>x</p>");
    let mut host = host(&f, &f.fake, "oversize");
    host.route = Some(server.addr);
    let seen = run(&mut host, Duration::from_secs(5));
    assert!(
        seen.paints.is_empty(),
        "the kernel painted an oversized frame: {:?}",
        seen.paints
    );
    assert!(alive(&seen), "a process ended: {:#?}", seen.log);
    assert!(server.seen.lock().is_ok_and(|s| s.len() == 1));
    eprintln!(
        "address_bar: oversized FrameReady: no Paint; renderer and GPU process still running (dropped, not killed)"
    );
}

/// The cases where the kernel paints (it cannot see the bytes) and the host must
/// not show what it got: the slot's pixels, if any, and their size.
fn lying(mode: &str) -> Option<(u32, u32)> {
    let f = fixture(mode);
    let server = page("<!doctype html><title>t</title><p>x</p>");
    let mut host = host(&f, &f.fake, mode);
    host.route = Some(server.addr);
    let seen = run(&mut host, Duration::from_secs(5));
    let claimed = (u64::from(VIEWPORT.0), u64::from(VIEWPORT.1));
    assert_eq!(
        seen.paints.iter().map(|p| (p.3, p.4)).collect::<Vec<_>>(),
        [claimed],
        "{mode}: the Paint names what was claimed"
    );
    assert_eq!(
        seen.paints.first().map(|p| p.0.as_str()),
        Some("http://hostile.test/")
    );
    drop(host);
    // `browse --headless` shows nothing and ends with its error, not a signal.
    let out = f.dir.join("out.png");
    let ran = Command::new(f.renderer.with_file_name("clazel"))
        .args(["browse", "--headless"])
        .arg(&out)
        .args([
            "--size",
            "160x120",
            "--wait",
            "5",
            &format!("http://{}/", server.addr),
        ])
        .env("CLAZEL_RENDERER", &f.renderer)
        .env("CLAZEL_GPU", &f.fake)
        .env("FAKE_GPU_MODE", mode)
        .output();
    let ran = ran.ok();
    let code = ran.as_ref().and_then(|o| o.status.code());
    let stderr = ran
        .map(|o| String::from_utf8_lossy(&o.stderr).into_owned())
        .unwrap_or_default();
    assert_eq!(code, Some(1), "{mode}: {stderr}");
    assert!(stderr.contains("no frame for"), "{mode}: {stderr}");
    assert!(!out.exists(), "{mode}: a file was written");
    eprintln!(
        "address_bar: {mode}: Paint of the claimed size, slot holds {:?}; browse --headless shows nothing",
        seen.frame
    );
    seen.frame
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_gpu_process_sending_more_than_it_claimed_is_not_shown() {
    assert_eq!(lying("more"), Some((VIEWPORT.0, VIEWPORT.1 * 2)));
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_gpu_process_sending_something_that_is_not_a_buffer() {
    assert_eq!(lying("notbuffer"), None);
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_gpu_process_sending_a_buffer_too_small() {
    assert_eq!(lying("small"), Some((1, 1)));
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_gpu_process_sending_a_truncated_buffer() {
    assert_eq!(lying("truncated"), None);
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_title_shaped_like_a_url_is_only_the_title() {
    if !metal() {
        return;
    }
    let f = fixture("title");
    let server = page("<!doctype html><title>https://bank.example/login</title><p>x</p>");
    let mut host = host(&f, &f.gpu, "");
    host.route = Some(server.addr);
    let seen = run(&mut host, Duration::from_secs(20));
    let p = seen.paints.last().cloned();
    assert!(p.is_some(), "no Paint: {:#?}", seen.log);
    let Some((url, title, ..)) = p else { return };
    assert_eq!(url, "http://hostile.test/");
    assert_eq!(title, "https://bank.example/login");
}

#[test]
#[cfg_attr(miri, ignore)]
fn negative_margins_stay_below_the_strip() {
    if !metal() {
        return;
    }
    let f = fixture("margins");
    let server = page(
        "<!doctype html><title>t</title><body style='margin:0'>\
         <div style='margin-top:-1e9px;height:2e9px;background:#f00'>x</div></body>",
    );
    let mut host = host(&f, &f.gpu, "");
    host.route = Some(server.addr);
    let seen = run(&mut host, Duration::from_secs(20));
    let p = seen.paints.last().cloned();
    assert!(p.is_some(), "no Paint: {:#?}", seen.log);
    let Some((_, _, _, w, h)) = p else { return };
    // The frame is at most the content area...
    assert!(w <= u64::from(VIEWPORT.0) && h <= u64::from(VIEWPORT.1));
    assert_eq!(seen.frame, Some((VIEWPORT.0, VIEWPORT.1)));
    // ...and the window puts the page's layer below the strip: in a window whose
    // content area is the strip (36 points) plus the viewport, at scale 1, the
    // layer's top edge (Core Animation's y is from the bottom) is the strip's
    // bottom edge.
    let strip = 36.0;
    let geometry = clazel_window::nsevent::Geometry {
        width: f64::from(VIEWPORT.0),
        height: f64::from(VIEWPORT.1) + strip,
        scale: 1.0,
    };
    let frame = clazel_window::nsevent::layer_frame(0, 36, VIEWPORT.0, VIEWPORT.1, &geometry);
    assert!(
        frame.y + frame.height <= geometry.height - strip,
        "{frame:?}"
    );
}

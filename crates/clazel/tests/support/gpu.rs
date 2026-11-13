//! Shared by `tests/browse_gpu.rs` and `tests/browse_window.rs` (phase-5.md item
//! 5.23): a stand-in renderer that writes a hand-built display list to the list
//! socket it inherits, the real GPU process, and the reference pixels of the list.
//!
//! The stand-in renderer is a shell script: it waits a second (so the kernel has
//! committed the tab and sized it before the list arrives), writes the list to
//! `--list-fd N`, then reads its kernel channel until the host closes it.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_displaylist::exec::{ExecItem, encode_list};
use clazel_gpu::channel::{SurfaceFrame, write_list};
use clazel_gpu::geom::Viewport;
use clazel_gpu::reference::{Masks, draw};
use clazel_kernel::exec::records::{EventRecord, OutputRecord};

/// The stand-in renderer.
const RENDERER: &str = r#"#!/bin/sh
fd=""
while [ $# -gt 0 ]; do
  if [ "$1" = "--list-fd" ]; then fd="$2"; fi
  shift
done
sleep 1
if [ -n "$fd" ]; then eval "cat \"\$CLAZEL_TEST_LIST\" >&$fd"; fi
exec cat > /dev/null
"#;

/// The hand-built list: a white canvas, an opaque and a translucent fill under a
/// clip, and a mask uploaded and drawn.
pub fn items() -> Vec<ExecItem> {
    let coverage: Vec<u8> = (0..96u32)
        .map(|i| u8::try_from(i.saturating_mul(37) % 256).unwrap_or(0))
        .collect();
    vec![
        ExecItem::FillRect {
            x: 0,
            y: 0,
            width: 4096,
            height: 4096,
            colour: 0xffff_ffff,
        },
        ExecItem::FillRect {
            x: 4,
            y: 6,
            width: 30,
            height: 20,
            colour: 0xff20_4080,
        },
        ExecItem::PushClip {
            x: 10,
            y: 10,
            width: 40,
            height: 30,
        },
        ExecItem::FillRect {
            x: 0,
            y: 0,
            width: 100,
            height: 100,
            colour: 0x8000_8000,
        },
        ExecItem::PopClip,
        ExecItem::UploadMask {
            id: 1,
            columns: 12,
            rows: 8,
            coverage,
        },
        ExecItem::DrawMask {
            id: 1,
            x: 40,
            y: 30,
            colour: 0xff00_0000,
        },
    ]
}

/// The reference pixels of [`items`] at `width` by `height`, RGBA8 premultiplied.
pub fn reference(width: u32, height: u32) -> Option<Vec<u8>> {
    draw(
        &items(),
        Viewport::new(width, height)?,
        &mut Masks::default(),
    )
}

/// Whether every channel of `got` is within one level of `want` (a GPU blends in
/// floating point, 5.17b).
pub fn close(got: &[u8], want: &[u8]) -> bool {
    got.len() == want.len() && got.iter().zip(want).all(|(a, b)| a.abs_diff(*b) <= 1)
}

/// The binaries and the stand-in's files, in a directory removed on drop.
pub struct Fixture {
    /// The directory.
    pub dir: PathBuf,
    /// `clazel-gpu`.
    pub gpu: PathBuf,
    /// `clazel`.
    pub clazel: PathBuf,
    /// The real `clazel-renderer`.
    pub renderer: PathBuf,
    /// The stand-in renderer.
    pub script: PathBuf,
    /// The framed list it writes.
    pub list: PathBuf,
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// Build the binaries and write the stand-in's files under a name with `tag`.
pub fn fixture(tag: &str) -> Result<Fixture, String> {
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let built = Command::new(cargo)
        .args([
            "build",
            "--quiet",
            "-p",
            "clazel-gpu",
            "-p",
            "clazel",
            "-p",
            "clazel-renderer",
        ])
        .status();
    if !built.is_ok_and(|s| s.success()) {
        return Err("cannot build clazel-gpu, clazel and clazel-renderer".to_owned());
    }
    let bin = std::env::current_exe()
        .ok()
        .and_then(|e| e.parent()?.parent().map(Path::to_path_buf))
        .ok_or("no target directory")?;
    let name = format!("clazel-{tag}-{}", std::process::id());
    let dir = std::env::temp_dir().join(name);
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let script = dir.join("renderer.sh");
    std::fs::write(&script, RENDERER).map_err(|e| e.to_string())?;
    // `clazel browse` runs `$CLAZEL_RENDERER` itself, so the script must be executable.
    use std::os::unix::fs::PermissionsExt;
    let executable = std::fs::Permissions::from_mode(0o755);
    std::fs::set_permissions(&script, executable).map_err(|e| e.to_string())?;
    let mut framed = Vec::new();
    let list = encode_list(&items()).ok_or("the list does not encode")?;
    write_list(&mut framed, &list).map_err(|e| e.to_string())?;
    let list = dir.join("list");
    std::fs::write(&list, framed).map_err(|e| e.to_string())?;
    Ok(Fixture {
        dir,
        gpu: bin.join("clazel-gpu"),
        clazel: bin.join("clazel"),
        renderer: bin.join("clazel-renderer"),
        script,
        list,
    })
}

/// Whether there is a Metal device; if not, why.
pub fn metal() -> Result<(), String> {
    clazel_gpu::metal::MetalBackend::new()
        .map(drop)
        .map_err(|e| e.what.to_owned())
}

/// A host whose renderer is the stand-in and whose GPU process is real.
pub fn host(f: &Fixture) -> Host {
    let (script, list, gpu) = (f.script.clone(), f.list.clone(), f.gpu.clone());
    Host::new(move |_| {
        let mut c = Command::new("/bin/sh");
        c.arg(&script).env("CLAZEL_TEST_LIST", &list);
        c
    })
    .with_gpu(move |_| Command::new(&gpu))
}

/// A tab at `url` running the stand-in, sized `width` by `height` at scale 1:
/// its id.
pub fn open(host: &mut Host, url: &str, (width, height): (u32, u32)) -> u64 {
    let tab = host.state.next_id;
    host.open_tab(url, "");
    host.event(EventRecord::Resize {
        tab,
        width: width.into(),
        height: height.into(),
        scale: 1,
    });
    tab
}

/// What a `Paint` said, and the pixels it named.
pub struct Painted {
    /// The URL.
    pub url: String,
    /// The ring slot.
    pub buffer: u64,
    /// The size it gave.
    pub size: (u64, u64),
    /// The pixels.
    pub frame: SurfaceFrame,
}

/// Pump until `tab` has a `Paint` and the pixels it names, for up to 20 s.
pub fn painted(host: &mut Host, tab: u64) -> Option<Painted> {
    let end = Instant::now().checked_add(Duration::from_secs(20))?;
    let mut paint = None;
    while Instant::now() < end {
        host.pump(Duration::from_millis(20));
        let mine = |o: &OutputRecord| matches!(o, OutputRecord::Paint { tab: t, .. } if *t == tab);
        if let Some(i) = host.shown.iter().position(mine) {
            paint = Some(host.shown.remove(i));
        }
        let id = host
            .state
            .renderers
            .iter()
            .find(|r| r.tab == tab)
            .map(|r| r.id)?;
        if let Some(OutputRecord::Paint {
            url,
            buffer,
            width,
            height,
            ..
        }) = &paint
            && let Some(frame) = host.take_frame(id, u32::try_from(*buffer).ok()?)
        {
            return Some(Painted {
                url: url.iter().filter_map(|c| char::from_u32(*c)).collect(),
                buffer: *buffer,
                size: (*width, *height),
                frame,
            });
        }
    }
    None
}

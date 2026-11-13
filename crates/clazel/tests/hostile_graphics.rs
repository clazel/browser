//! Hostile pages through the graphical pipeline (phase-5.md item 5.26): each page
//! is served by an in-process server, fetched by the kernel, laid out and painted
//! by a real sandboxed `clazel-renderer` (item 5.20) and drawn by the real
//! sandboxed GPU process (`clazel-gpu`, 5.21a), at an 800 by 600 viewport. Where
//! the item says "a sheet", the CSS is in an inline `<style>` element, since linked
//! sheets wait for item 5.19.
//!
//! Every case checks:
//!
//! - **the outcome**: the page is painted (a `Paint` with its pixels), or the
//!   renderer refuses it and ends, or the kernel kills it; what happened is
//!   printed, and each case states which it expects;
//! - **a stated time limit** ([`Case::limit`]), from the request to that outcome;
//! - **the memory bound**: the renderer's peak resident set is at most item
//!   4.13's terms for the body (`hostile_pages.rs`'s [`text_bound`]) plus item
//!   5.20's graphical terms ([`graphics_bound`], from
//!   `crates/clazel-renderer/README.md`), plus a term for parsed style sheets,
//!   which the README leaves unbounded: this harness's own choice of 64 bytes per
//!   byte of style text, stated here so a case above it is reported. The GPU
//!   process's peak must stay under [`GPU_LIMIT`].
//!
//! Peaks are sampled with `ps` every 25 ms (macOS keeps no peak a test can read
//! without `unsafe`); each process is started through `/bin/sh`, which writes its
//! pid and `exec`s it. A process passing [`CAP`] is killed at once. One case runs at
//! a time ([`HEAVY`]). Cases that take more than about a minute, or allocate more
//! than a few hundred MiB, are `#[ignore]`d with the numbers they gave; run each
//! alone, in its own process group, under a cap of 8 GB and 10 minutes:
//!
//! ```text
//! cargo test -p clazel --test hostile_graphics -- --ignored --exact NAME --nocapture
//! ```
//!
//! Each case prints one `HOSTILE` line: its outcome, time, and peaks against its
//! bound and limit. Two of them are findings (their `ignore` reasons say so): they
//! do not paint within their limit.
//!
//! macOS on Apple silicon only (the GPU process's only backend); without a Metal
//! device every case says so and passes, except under CI.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

mod support;

#[path = "support/server.rs"]
mod server;

#[path = "support/fonts.rs"]
mod fonts;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use clazel::Host;
use clazel_kernel::exec::records::{EventRecord, OutputRecord};
use server::{Reply, Request, serve};

/// One case at a time, so peaks and times are each case's own.
static HEAVY: Mutex<()> = Mutex::new(());

const MIB: u64 = 1024 * 1024;

/// The process itself, before any page (as `hostile_pages.rs`).
const BASE: u64 = 16 * MIB;

/// A process past this resident set is killed at once (the machine's cap).
const CAP: u64 = 8 * 1024 * MIB;

/// The GPU process's stated limit: Metal and the driver (measured near 100
/// MiB idle), a frame and its copy at 800 by 600, a list of at most 256 MiB
/// (`clazel_gpu::channel::LIST_MAX`) and the atlas (at most 128 MiB).
const GPU_LIMIT: u64 = 1024 * MIB;

/// The viewport every case is painted at.
const VIEWPORT: (u64, u64) = (800, 600);

/// DejaVu Serif, vendored for `clazel-font`'s tests: the face every case lays out
/// in, unless it brings its own.
const DEJAVU: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../clazel-font/tests/data/fonts-dejavu/DejaVuSerif.ttf"
);

/// Item 4.13's bound (`hostile_pages.rs`'s `bound`), in bytes, for a body of `b`
/// bytes with `n` nodes and no attribute bytes beyond the body's.
fn text_bound(b: u64, n: u64) -> u64 {
    let parser = b
        .saturating_mul(13)
        .saturating_add(n.saturating_mul(176))
        .saturating_add(b);
    let page_chars = b.saturating_mul(4).saturating_add(n.saturating_mul(162));
    parser
        .saturating_add(page_chars.saturating_mul(4))
        .saturating_add(MIB)
}

/// Item 5.20's terms (`crates/clazel-renderer/README.md`, its second "Memory"
/// table), for `n` nodes, at most `3·n` boxes (a principal box, a marker and a
/// wrapper per node), at most `b` characters, and `style` bytes of style text:
/// the computed table `432·N`; each box's style `432·M`; boxes, fragments and
/// layout state `350·M`; glyphs `24·C`, three copies; the display list, at most
/// nine items of 56 bytes per box; one frame's items (16 MiB) and new masks (64
/// MiB); and this harness's 64 bytes per byte of style text.
fn graphics_bound(b: u64, n: u64, style: u64) -> u64 {
    let m = n.saturating_mul(3);
    n.saturating_mul(432)
        .saturating_add(m.saturating_mul(432 + 350 + 9 * 56))
        .saturating_add(b.saturating_mul(72))
        .saturating_add(80 * MIB)
        .saturating_add(style.saturating_mul(64))
}

/// A hostile page and what is expected of it.
struct Case {
    name: &'static str,
    body: Vec<u8>,
    /// The nodes of its tree, stated by its generator.
    nodes: u64,
    /// Bytes of style text in it.
    style: u64,
    /// The time from the request to the outcome.
    limit: Duration,
    /// A font file to lay out in instead of DejaVu Serif.
    font: Option<PathBuf>,
}

/// What became of a case.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Outcome {
    /// Painted: the `Paint`'s size.
    Painted(u64, u64),
    /// The renderer ended (refused the page, or crashed): the host's line.
    RendererEnded(String),
    /// The GPU process ended: the host's line.
    GpuEnded(String),
    /// Nothing within the limit.
    TimedOut,
    /// A process passed [`CAP`] and was killed.
    Capped(String),
}

/// What a run measured.
struct Measured {
    outcome: Outcome,
    elapsed: Duration,
    renderer_peak: u64,
    gpu_peak: u64,
    bound: u64,
}

fn rss_kib(pid: &str) -> Option<u64> {
    let out = Command::new("ps")
        .args(["-o", "rss=", "-p", pid])
        .output()
        .ok()?;
    String::from_utf8_lossy(&out.stdout).trim().parse().ok()
}

/// A command that records its pid in `dir/<prefix><id>.pid` and becomes
/// `program args`.
fn recorded(dir: &Path, prefix: &str, id: u64, program: &Path, args: &[&str]) -> Command {
    let mut c = Command::new("/bin/sh");
    c.arg("-c")
        .arg("echo $$ > \"$PIDDIR/$PREFIX$ID.pid\"; exec \"$0\" \"$@\"")
        .arg(program)
        .args(args)
        .env("PIDDIR", dir)
        .env("PREFIX", prefix)
        .env("ID", id.to_string());
    c
}

/// One sample of every process whose pid file is in `dir`: the largest value
/// seen for each, in `peaks`; a process past [`CAP`] is killed and named in
/// `capped`.
fn sample_once(dir: &Path, peaks: &Mutex<BTreeMap<String, u64>>, capped: &Mutex<Option<String>>) {
    for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        let Ok(pid) = std::fs::read_to_string(entry.path()) else {
            continue;
        };
        let pid = pid.trim().to_owned();
        let Some(kib) = rss_kib(&pid) else { continue };
        let bytes = kib.saturating_mul(1024);
        if let Ok(mut p) = peaks.lock() {
            let e = p.entry(name.clone()).or_insert(0);
            *e = (*e).max(bytes);
        }
        if bytes > CAP {
            let _ = Command::new("kill").args(["-9", &pid]).status();
            if let Ok(mut c) = capped.lock() {
                *c = Some(format!("{name} at {} MiB", bytes / MIB));
            }
        }
    }
}

/// [`sample_once`] every 25 ms until `stop`.
fn sampler(
    dir: PathBuf,
    stop: Arc<AtomicBool>,
    peaks: Arc<Mutex<BTreeMap<String, u64>>>,
    capped: Arc<Mutex<Option<String>>>,
) -> std::thread::JoinHandle<()> {
    std::thread::spawn(move || {
        while !stop.load(Ordering::SeqCst) {
            sample_once(&dir, &peaks, &capped);
            std::thread::sleep(Duration::from_millis(25));
        }
    })
}

/// Whether to run at all: a Metal device, or fail under CI. Builds `clazel-gpu`
/// beside the renderer first.
fn runs() -> bool {
    static BUILT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let built = BUILT.get_or_init(|| {
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        Command::new(cargo)
            .args([
                "build",
                "--quiet",
                "-p",
                "clazel-gpu",
                "-p",
                "clazel-renderer",
            ])
            .status()
            .is_ok_and(|s| s.success())
    });
    assert!(*built, "cannot build clazel-gpu");
    match clazel_gpu::metal::MetalBackend::new() {
        Ok(_) => true,
        Err(e) => {
            eprintln!("hostile_graphics: skipped: no Metal device ({})", e.what);
            assert!(std::env::var_os("CI").is_none(), "no Metal device under CI");
            false
        }
    }
}

/// Serve `case`, open a tab at it in a host with the real renderer and GPU
/// process, size it, and wait for the outcome.
fn measure(case: &Case) -> Measured {
    let _turn = HEAVY
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
        "hostile-gfx-{}-{}",
        case.name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::create_dir_all(&dir);
    let renderer = support::binary("clazel-renderer");
    let gpu = renderer.with_file_name("clazel-gpu");
    let body = Arc::new(case.body.clone());
    let server = serve(move |_: &Request| Reply {
        head: "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\n".to_owned(),
        piece: body.to_vec(),
        times: 1,
    });
    let font = case.font.clone().unwrap_or_else(|| PathBuf::from(DEJAVU));
    let (rdir, gdir) = (dir.clone(), dir.clone());
    let mut host = Host::new(move |id| {
        let f = font.display().to_string();
        recorded(&rdir, "renderer-", id, &renderer, &["--font", &f])
    })
    .with_gpu(move |id| recorded(&gdir, "gpu-", id, &gpu, &[]));
    host.route = Some(server.addr);
    let (stop, peaks, capped) = (
        Arc::new(AtomicBool::new(false)),
        Arc::default(),
        Arc::default(),
    );
    let sampling = sampler(
        dir.clone(),
        Arc::clone(&stop),
        Arc::clone(&peaks),
        Arc::clone(&capped),
    );
    let started = Instant::now();
    let tab = host.open("http://hostile.test/");
    host.event(EventRecord::Resize {
        tab,
        width: VIEWPORT.0,
        height: VIEWPORT.1,
        scale: 1,
    });
    let mut outcome = Outcome::TimedOut;
    let mut paint: Option<(u64, u32, u64, u64)> = None;
    while started.elapsed() < case.limit {
        host.pump(Duration::from_millis(20));
        if let Some(i) = host
            .shown
            .iter()
            .position(|o| matches!(o, OutputRecord::Paint { tab: t, .. } if *t == tab))
        {
            if let Some(OutputRecord::Paint {
                buffer,
                width,
                height,
                ..
            }) = host.shown.get(i)
            {
                let id = host
                    .state
                    .renderers
                    .iter()
                    .find(|r| r.tab == tab)
                    .map_or(u64::MAX, |r| r.id);
                paint = Some((
                    id,
                    u32::try_from(*buffer).unwrap_or(u32::MAX),
                    *width,
                    *height,
                ));
            }
            host.shown.remove(i);
        }
        if let Some((id, slot, w, h)) = paint
            && host.take_frame(id, slot).is_some()
        {
            outcome = Outcome::Painted(w, h);
            break;
        }
        let ended = |kind: &str| {
            host.log
                .iter()
                .find(|l| l.starts_with(kind) && l.contains(" exited: "))
                .cloned()
        };
        if let Some(line) = ended("renderer ") {
            outcome = Outcome::RendererEnded(line);
            break;
        }
        if let Some(line) = ended("gpu ") {
            outcome = Outcome::GpuEnded(line);
            break;
        }
        if let Ok(Some(c)) = capped.lock().map(|c| c.clone()) {
            outcome = Outcome::Capped(c);
            break;
        }
    }
    let elapsed = started.elapsed();
    stop.store(true, Ordering::SeqCst);
    let _ = sampling.join();
    // A last sample while the processes still run, for a page done in less
    // than a sampling period.
    sample_once(&dir, &peaks, &capped);
    let peak = |prefix: &str| {
        peaks
            .lock()
            .map(|p| {
                p.iter()
                    .filter(|(k, _)| k.starts_with(prefix))
                    .map(|(_, v)| *v)
                    .max()
                    .unwrap_or(0)
            })
            .unwrap_or(0)
    };
    let (renderer_peak, gpu_peak) = (peak("renderer-"), peak("gpu-"));
    drop(host);
    let _ = std::fs::remove_dir_all(&dir);
    let served = server.seen.lock().map(|s| s.len()).unwrap_or(0);
    assert!(served >= 1, "{}: the page was never fetched", case.name);
    let b = u64::try_from(case.body.len()).unwrap_or(u64::MAX);
    let bound = text_bound(b, case.nodes)
        .saturating_add(graphics_bound(b, case.nodes, case.style))
        .saturating_add(BASE);
    let m = Measured {
        outcome,
        elapsed,
        renderer_peak,
        gpu_peak,
        bound,
    };
    eprintln!(
        "HOSTILE {}: {:?} in {:.2} s (limit {} s); renderer peak {} MiB of a {} MiB bound; GPU peak {} MiB of {} MiB",
        case.name,
        m.outcome,
        m.elapsed.as_secs_f64(),
        case.limit.as_secs(),
        m.renderer_peak / MIB,
        m.bound / MIB,
        m.gpu_peak / MIB,
        GPU_LIMIT / MIB
    );
    m
}

/// Run `case`: its outcome must be one of `allowed` (by kind), within its limit
/// and its bounds.
fn check(case: &Case, allowed: &[fn(&Outcome) -> bool]) {
    if !runs() {
        return;
    }
    let m = measure(case);
    assert!(
        allowed.iter().any(|f| f(&m.outcome)),
        "{}: unexpected outcome {:?}",
        case.name,
        m.outcome
    );
    assert!(m.elapsed <= case.limit, "{}: over its limit", case.name);
    assert!(
        m.renderer_peak <= m.bound,
        "{}: renderer peak {} MiB over its {} MiB bound",
        case.name,
        m.renderer_peak / MIB,
        m.bound / MIB
    );
    assert!(
        m.gpu_peak <= GPU_LIMIT,
        "{}: GPU peak {} MiB",
        case.name,
        m.gpu_peak / MIB
    );
}

fn painted(o: &Outcome) -> bool {
    matches!(o, Outcome::Painted(w, h) if *w <= VIEWPORT.0 && *h <= VIEWPORT.1)
}

fn refused(o: &Outcome) -> bool {
    matches!(o, Outcome::RendererEnded(_))
}

/// A page whose only content is `style` in a `style` element and `body`.
fn styled(style: &str, body: &str) -> Vec<u8> {
    format!("<!doctype html><title>hostile</title><style>{style}</style><body>{body}</body>")
        .into_bytes()
}

fn case(name: &'static str, body: Vec<u8>, nodes: u64, style: u64, limit_s: u64) -> Case {
    Case {
        name,
        body,
        nodes,
        style,
        limit: Duration::from_secs(limit_s),
        font: None,
    }
}

// ---------------------------------------------------------------------------
// CSS bombs.
// ---------------------------------------------------------------------------

#[test]
#[ignore = "83 s and a 6,751 MiB renderer peak (bound 10,720 MiB), 2026-11-13; run alone"]
fn css_style_of_64_mib() {
    // `.a{color:red}` until the body is just under the 64 MiB limit.
    let rule = ".a{color:#123456}";
    let n = (64 * 1024 * 1024 - 1024) / rule.len();
    let style = rule.repeat(n);
    let s = u64::try_from(style.len()).unwrap_or(0);
    check(
        &case("css-64mib", styled(&style, "<p class=a>x</p>"), 8, s, 600),
        &[painted, refused],
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn css_braces_a_million_deep() {
    let style = "{".repeat(1_000_000);
    check(
        &case("css-braces", styled(&style, "<p>x</p>"), 8, 1_000_000, 120),
        &[painted, refused],
    );
}

#[test]
#[ignore = "25 s but a 2,149 MiB renderer peak (bound 3,720 MiB), 2026-11-13; run alone"]
fn css_a_million_rules() {
    let style: String = (0..1_000_000)
        .map(|i| format!(".c{i}{{color:#{:06x}}}", i % 0xffffff))
        .collect();
    let s = u64::try_from(style.len()).unwrap_or(0);
    check(
        &case(
            "css-million-rules",
            styled(&style, "<p class=c999999>x</p>"),
            8,
            s,
            600,
        ),
        &[painted, refused],
    );
}

#[test]
#[ignore = "105 s of a 120 s limit (peak 54 MiB), 2026-11-13; run alone"]
fn css_a_selector_of_100000_compounds() {
    let style = format!("{}{{color:red}}", "div ".repeat(100_000));
    let s = u64::try_from(style.len()).unwrap_or(0);
    let divs = format!("{}x{}", "<div>".repeat(100), "</div>".repeat(100));
    check(
        &case("css-100k-compounds", styled(&style, &divs), 110, s, 120),
        &[painted, refused],
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn css_is_nested_10000_deep() {
    let style = format!(
        "{}div{}{{color:red}}",
        ":is(".repeat(10_000),
        ")".repeat(10_000)
    );
    let s = u64::try_from(style.len()).unwrap_or(0);
    check(
        &case("css-is-nested", styled(&style, "<div>x</div>"), 9, s, 120),
        &[painted, refused],
    );
}

#[test]
#[ignore = "FINDING: no paint within the 600 s limit (renderer at 291 MiB of 1,960), 2026-11-13; run alone"]
fn css_10000_rules_over_100000_elements() {
    let style: String = (0..10_000)
        .map(|i| format!(".c{i} span{{color:#{:06x}}}", i * 7))
        .collect();
    let s = u64::try_from(style.len()).unwrap_or(0);
    let body: String = (0..100_000)
        .map(|i| format!("<div class=c{}><span>x</span></div>", i % 10_000))
        .collect();
    check(
        &case(
            "css-10k-rules-100k-elements",
            styled(&style, &body),
            300_010,
            s,
            600,
        ),
        &[painted, refused],
    );
}

// ---------------------------------------------------------------------------
// Malicious fonts, loaded as the renderer's font.
// ---------------------------------------------------------------------------

fn font_case(name: &'static str, break_it: fn(&mut [u8]) -> Option<()>) {
    if !runs() {
        return;
    }
    let mut bytes = std::fs::read(DEJAVU).unwrap_or_default();
    assert!(
        break_it(&mut bytes).is_some(),
        "{name}: the font could not be edited"
    );
    let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("{name}-{}.ttf", std::process::id()));
    assert!(std::fs::write(&path, &bytes).is_ok());
    let mut c = case(
        name,
        styled("p{font-size:40px}", "<p>xyz xyz Hello</p>"),
        9,
        17,
        60,
    );
    c.font = Some(path.clone());
    check(&c, &[painted, refused]);
    let _ = std::fs::remove_file(path);
}

#[test]
#[cfg_attr(miri, ignore)]
fn font_with_offsets_past_the_end() {
    font_case("font-offsets-past-end", fonts::offsets_past_the_end);
}

#[test]
#[cfg_attr(miri, ignore)]
fn font_with_overlapping_tables() {
    font_case("font-overlapping-tables", fonts::overlapping_tables);
}

#[test]
#[cfg_attr(miri, ignore)]
fn font_with_loca_not_monotone() {
    font_case("font-loca-not-monotone", fonts::loca_not_monotone);
}

#[test]
#[cfg_attr(miri, ignore)]
fn font_with_a_composite_containing_itself() {
    font_case("font-composite-self", fonts::composite_containing_itself);
}

#[test]
#[cfg_attr(miri, ignore)]
fn font_with_32767_contours() {
    font_case("font-32767-contours", fonts::contours_32767);
}

#[test]
#[cfg_attr(miri, ignore)]
fn font_with_overlapping_cmap_segments() {
    font_case("font-cmap-overlap", fonts::overlapping_cmap_segments);
}

#[test]
#[cfg_attr(miri, ignore)]
fn font_with_num_glyphs_disagreeing_with_loca() {
    font_case("font-numglyphs", fonts::num_glyphs_disagreeing);
}

// ---------------------------------------------------------------------------
// Large trees and tables.
// ---------------------------------------------------------------------------

#[test]
#[ignore = "137 s and a 3,591 MiB renderer peak (bound 10,629 MiB), 2026-11-13; run alone"]
fn a_million_elements_flat() {
    let body = "<b>x</b>".repeat(1_000_000);
    check(
        &case("million-flat", styled("", &body), 2_000_010, 0, 600),
        &[painted, refused],
    );
}

#[test]
#[ignore = "FINDING: no paint within the 600 s limit, killed at the cap (228 MiB), 2026-11-13; run alone"]
fn a_million_elements_nested() {
    let body = format!("{}x", "<div>".repeat(1_000_000));
    check(
        &case("million-nested", styled("", &body), 1_000_010, 0, 600),
        &[painted, refused],
    );
}

#[test]
#[ignore = "454 s of a 600 s limit and a 4,496 MiB renderer peak (bound 10,337 MiB), 2026-11-13; run alone"]
fn a_million_column_table() {
    let body = format!("<table><tr>{}</tr></table>", "<td>x".repeat(1_000_000));
    check(
        &case("million-columns", styled("", &body), 2_000_010, 0, 600),
        &[painted, refused],
    );
}

#[test]
#[ignore = "49 s and a 480 MiB renderer peak (bound 1,253 MiB), 2026-11-13; run alone"]
fn colspan_1000_everywhere() {
    let row = format!("<tr>{}</tr>", "<td colspan=1000>x".repeat(100));
    let body = format!("<table>{}</table>", row.repeat(1000));
    check(
        &case("colspan-1000", styled("", &body), 201_010, 0, 600),
        &[painted, refused],
    );
}

// ---------------------------------------------------------------------------
// Huge values.
// ---------------------------------------------------------------------------

#[test]
#[cfg_attr(miri, ignore)]
fn a_font_size_of_1e9px() {
    check(
        &case(
            "font-size-1e9",
            styled("p{font-size:1e9px}", "<p>Hello</p>"),
            9,
            18,
            60,
        ),
        &[painted, refused],
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn a_width_of_1e9px() {
    let body = "<div style='width:1e9px;height:100px;background:#f00'>x</div>";
    check(
        &case("width-1e9", styled("", body), 9, 0, 60),
        &[painted, refused],
    );
}

#[test]
#[cfg_attr(miri, ignore)]
fn margins_of_minus_1e9px() {
    let body = "<div style='margin:-1e9px;height:1e9px;width:1e9px;background:#f00'>x</div>";
    check(
        &case("margins-minus-1e9", styled("", body), 9, 0, 60),
        &[painted, refused],
    );
}

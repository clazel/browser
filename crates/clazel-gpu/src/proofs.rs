//! Kani harnesses for the batching and atlas arithmetic. Compiled only under
//! `cargo kani`. The crate is tier 0 (the plan's tier for `clazel-gpu`); these are
//! evidence, not a tier claim.
//!
//! Each harness checks that no panic, overflow or out-of-bounds index is reachable
//! and the assertions written in it. Where possible a harness takes **one step from
//! any state** that satisfies a stated invariant, so it holds for lists of every
//! length:
//!
//! - For every input: [`place_any`], [`grown_capacity_any`] (from any capacity
//!   the atlas can hold), [`rect_at_any`], [`intersect_any`], [`blend_any`].
//!
//! Not covered: `atlas::texel_index` (every pixel of a mask that fits the atlas
//! has an index inside the mask). Its harness, for any `u16` sides and later with
//! sides up to 2048, reached the 20-minute cap twice at 0.17 GB (the 32-bit
//! multiplications) and was removed. Every step of it is checked, so a missed case
//! returns `None` and an error rather than panicking or wrapping; the unit tests
//! and every scene through the fake backend exercise it.
//! - The draw step's cut, for every input: [`visible_any`] (a recorded quad is
//!   inside the viewport and not empty, under a scissor that is not empty).
//! - Bounded to one draw: [`clip_then_draw_any`] (any viewport, any clip, any
//!   quad, from a fresh frame: one quad and one batch over it, or nothing). Batching
//!   across many draws (`Builder::close`'s indices) is covered by the unit tests and
//!   the scenes, not by a harness.
//!
//! Item 5.17c, the blocklist and the crash policy:
//!
//! - For every input: [`matches_any`] (the matcher against its statement).
//! - One step from any state meeting the invariants, so for any number of tabs and
//!   any history: [`note_exit_any`] (`theorem_site_cannot_demote_others`'s step),
//!   [`tab_step_any`] (invariants kept, `theorem_gpu_restart_bounded`'s step,
//!   demotion by refusal only before `GpuReady`, only hardware exits counted by
//!   site).
//! - Bounded: [`version_parse_any`] (inputs up to 8 bytes), [`hex_any`] (10),
//!   [`drivers_parse_any`] (7), and [`policy_contained_any`]
//!   (`theorem_gpu_exit_contained` over two tabs; the step finds the event's tab and
//!   steps it, which [`tab_step_any`] covers from every state). A whole table's
//!   parse is covered by the unit tests, not a harness.
//!
//! Also not covered: an atlas upload from any state (`Atlas::upload`, compaction
//! included). Its harness, over two live masks of at most 2 × 2 with any offsets
//! meeting the invariant, passed the 8 GB cap in 83 s and was removed. The unit
//! tests in `atlas.rs` and the scene "atlas", which compacts in the middle of a
//! list, cover it; every step is checked.

use crate::atlas::{MAX_CAPACITY, MIN_CAPACITY, grown_capacity, place};
use crate::backend::{Op, Quad};
use crate::batch::{Builder, visible};
use crate::geom::{MAX_VIEWPORT_SIDE, Rect, Viewport};
use crate::soft::blend;

#[kani::proof]
fn place_any() {
    let (capacity, top, size): (u32, u32, u32) = kani::any();
    if let Some(offset) = place(capacity, top, size) {
        assert!(offset == top);
        assert!(u64::from(offset) + u64::from(size) <= u64::from(capacity));
    } else {
        assert!(u64::from(top) + u64::from(size) > u64::from(capacity));
    }
}

#[kani::proof]
#[kani::unwind(9)]
fn grown_capacity_any() {
    let (current, total): (u32, u32) = kani::any();
    // The atlas's invariant: no store yet, or one this function made.
    kani::assume(
        current == 0
            || (current.is_power_of_two() && (MIN_CAPACITY..=MAX_CAPACITY).contains(&current)),
    );
    match grown_capacity(current, total) {
        Some(c) => {
            assert!(c >= total);
            assert!((MIN_CAPACITY..=MAX_CAPACITY).contains(&c));
            assert!(c.is_power_of_two());
        }
        None => assert!(total > MAX_CAPACITY),
    }
}

#[kani::proof]
fn rect_at_any() {
    let (x, y, w, h): (i32, i32, u32, u32) = kani::any();
    if let Some(r) = Rect::at(x, y, w, h) {
        assert!(i64::from(r.x1) - i64::from(r.x0) == i64::from(w));
        assert!(i64::from(r.y1) - i64::from(r.y0) == i64::from(h));
    }
    // Every rectangle of a list that passed the validator is representable.
    let bound = 1i32 << 23;
    if (-bound..=bound).contains(&x)
        && (-bound..=bound).contains(&y)
        && w <= 1 << 23
        && h <= 1 << 23
    {
        assert!(Rect::at(x, y, w, h).is_some());
    }
}

fn any_rect() -> Rect {
    Rect {
        x0: kani::any(),
        y0: kani::any(),
        x1: kani::any(),
        y1: kani::any(),
    }
}

#[kani::proof]
fn intersect_any() {
    let (a, b) = (any_rect(), any_rect());
    let i = a.intersect(b);
    assert!(i.within(a) && i.within(b));
    let (px, py): (i32, i32) = kani::any();
    assert!(i.contains(px, py) == (a.contains(px, py) && b.contains(px, py)));
}

#[kani::proof]
fn blend_any() {
    let (c, a, k, d): (u8, u8, u8, u8) = kani::any();
    let out = blend(c, a, k, d);
    if k == 0 {
        assert!(out == d);
    }
    if k == 255 && a == 255 {
        assert!(out == c);
    }
    if c <= a {
        // A well-formed premultiplied colour never brightens past its own alpha's
        // share plus what was kept: out <= c + d, with no clamp needed.
        assert!(u32::from(out) <= u32::from(c) + u32::from(d));
    }
}

fn any_viewport() -> Viewport {
    let (w, h): (u32, u32) = kani::any();
    kani::assume((1..=MAX_VIEWPORT_SIDE).contains(&w) && (1..=MAX_VIEWPORT_SIDE).contains(&h));
    Viewport {
        width: w,
        height: h,
    }
}

fn any_fill() -> Quad {
    Quad {
        rect: any_rect(),
        origin_x: kani::any(),
        origin_y: kani::any(),
        offset: kani::any(),
        columns: kani::any(),
        colour: kani::any(),
    }
}

/// What a draw keeps: the quad it records is inside the viewport and not empty,
/// and its scissor is not empty, for any rectangles at all.
#[kani::proof]
fn visible_any() {
    let (rect, screen, scissor) = (any_rect(), any_rect(), any_rect());
    if let Some(cut) = visible(rect, screen, scissor) {
        assert!(!cut.is_empty() && cut.within(screen) && cut.within(rect));
        assert!(!scissor.is_empty() && !cut.intersect(scissor).is_empty());
    }
}

/// One draw under one clip from a fresh frame of any viewport: the frame's
/// batch covers exactly the recorded quad and its scissor is inside the viewport.
/// (A first form, with a draw before the clip, passed the 8 GB cap in 21 s.)
#[kani::proof]
#[kani::unwind(3)]
fn clip_then_draw_any() {
    let viewport = any_viewport();
    let screen = viewport.rect();
    let mut b = Builder::new(viewport);
    let _ = b.push_clip(any_rect());
    let _ = b.draw(any_fill());
    let _ = b.pop_clip();
    let Ok(frame) = b.finish() else {
        panic!("a balanced frame always finishes");
    };
    match (frame.quads.as_slice(), frame.ops.as_slice()) {
        ([], []) => {}
        (
            [q],
            [
                Op::Draw {
                    scissor,
                    first: 0,
                    count: 1,
                },
            ],
        ) => {
            assert!(!q.rect.is_empty() && q.rect.within(screen));
            assert!(!scissor.is_empty() && scissor.within(screen));
        }
        _ => panic!("one draw makes one quad and one batch, or nothing"),
    }
}

// Item 5.17c: the blocklist matcher and parser pieces, and the crash policy's step.

use crate::blocklist::{Adapter, Api, Drivers, Entry, Version, parse_hex};
use crate::policy::{
    Action, Config, Demotion, Event, Phase, Policy, Reason, Shared, SiteId, Tab, TabId, within,
};
use crate::start::Mode;

fn any_api() -> Api {
    match kani::any::<u8>() % 3 {
        0 => Api::Vulkan,
        1 => Api::D3d12,
        _ => Api::Metal,
    }
}

fn any_version() -> Version {
    Version(kani::any())
}

fn any_drivers() -> Drivers {
    if kani::any() {
        Drivers::Any
    } else {
        Drivers::Range {
            first: any_version(),
            last: any_version(),
        }
    }
}

/// The matcher, for every entry and every adapter: it refuses exactly a hardware
/// adapter of the entry's API and vendor, of its device if it names one, with a
/// driver version in its range (an unknown version only under `*`).
#[kani::proof]
fn matches_any() {
    let entry = Entry {
        line: kani::any(),
        api: any_api(),
        vendor: kani::any(),
        device: kani::any(),
        drivers: any_drivers(),
        evidence: String::new(),
        reason: String::new(),
    };
    let driver: Option<Version> = if kani::any() {
        Some(any_version())
    } else {
        None
    };
    let adapter = Adapter {
        api: any_api(),
        vendor: kani::any(),
        device: kani::any(),
        driver,
        software: kani::any(),
    };
    let in_range = match entry.drivers {
        Drivers::Any => true,
        Drivers::Range { first, last } => match driver {
            Some(v) => first <= v && v <= last,
            None => false,
        },
    };
    let spec = !adapter.software
        && entry.api == adapter.api
        && entry.vendor == adapter.vendor
        && (entry.device.is_none() || entry.device == Some(adapter.device))
        && in_range;
    assert!(entry.matches(&adapter) == spec);
}

/// A version of any text up to 8 bytes: no panic, and an answer only for digits
/// and dots.
#[kani::proof]
#[kani::unwind(10)]
fn version_parse_any() {
    let bytes: [u8; 8] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 8);
    let text = &bytes[..len];
    let fill: u16 = kani::any();
    if Version::parse(text, fill).is_some() {
        assert!(!text.is_empty());
        assert!(text.iter().all(|&b| b.is_ascii_digit() || b == b'.'));
    }
}

/// A hex field of any text up to 10 bytes: no panic, and an answer only after `0x`
/// with 1 to 8 digits.
#[kani::proof]
#[kani::unwind(11)]
fn hex_any() {
    let bytes: [u8; 10] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 10);
    let text = &bytes[..len];
    if parse_hex(text).is_some() {
        assert!(len >= 3 && text[0] == b'0' && text[1] == b'x');
        assert!(text[2..].iter().all(u8::is_ascii_hexdigit));
    }
}

/// The drivers field of any text up to 7 bytes: no panic, and a range is never
/// empty.
#[kani::proof]
#[kani::unwind(9)]
fn drivers_parse_any() {
    let bytes: [u8; 7] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 7);
    if let Ok(Drivers::Range { first, last }) = Drivers::parse(&bytes[..len]) {
        assert!(first <= last);
    }
}

fn any_config() -> Config {
    Config {
        fallback: kani::any(),
        software_only: kani::any(),
    }
}

fn any_site_time() -> Option<(SiteId, u64)> {
    if kani::any() {
        Some((SiteId(kani::any()), kani::any()))
    } else {
        None
    }
}

fn any_shared(config: &Config) -> Shared {
    let demoted = match kani::any::<u8>() % 3 {
        0 => None,
        1 => Some(Demotion::Refused),
        _ => Some(Demotion::Sites),
    };
    let shared = Shared {
        demoted,
        sites: [any_site_time(), any_site_time()],
    };
    kani::assume(shared.invariant(config));
    shared
}

fn any_mode() -> Mode {
    if kani::any() {
        Mode::Hardware
    } else {
        Mode::Software
    }
}

fn any_reason() -> Reason {
    match kani::any::<u8>() % 3 {
        0 => Reason::Crashed,
        1 => Reason::Refused,
        _ => Reason::NoSoftware,
    }
}

fn any_phase() -> Phase {
    match kani::any::<u8>() % 3 {
        0 => Phase::Starting,
        1 => Phase::Running,
        _ => Phase::Stopped(any_reason()),
    }
}

fn any_time() -> Option<u64> {
    if kani::any() { Some(kani::any()) } else { None }
}

fn any_tab(id: TabId, config: &Config) -> Tab {
    let tab = Tab {
        id,
        site: SiteId(kani::any()),
        mode: any_mode(),
        phase: any_phase(),
        exits: [any_time(), any_time()],
    };
    kani::assume(tab.invariant(config));
    tab
}

/// Any event naming `tab` that the tab's own step handles.
fn any_event(tab: TabId) -> Event {
    match kani::any::<u8>() % 7 {
        0 => Event::Opened {
            tab,
            site: SiteId(kani::any()),
        },
        1 => Event::Ready {
            tab,
            software: kani::any(),
        },
        2 => Event::Refused { tab },
        3 => Event::Exited { tab },
        4 => Event::Navigated {
            tab,
            site: SiteId(kani::any()),
        },
        5 => Event::Reload { tab },
        _ => Event::Closed { tab },
    }
}

/// `theorem_site_cannot_demote_others`, one step from any state meeting the
/// invariant (so for any number of tabs and exits before it): a hardware exit sets
/// every-tab demotion by sites only if two sites other than its own have exits
/// within the window, and only with a fallback; the invariant is kept.
#[kani::proof]
fn note_exit_any() {
    let config = any_config();
    let mut shared = any_shared(&config);
    let before = shared;
    let (site, now): (u64, u64) = kani::any();
    let site = SiteId(site);
    shared.note_exit(site, now, &config);
    assert!(shared.invariant(&config));
    if before.demoted.is_none() && shared.demoted.is_some() {
        assert!(shared.demoted == Some(Demotion::Sites));
        assert!(config.fallback);
        match before.sites {
            [Some((a, ta)), Some((b, tb))] => {
                assert!(a != site && b != site && a != b);
                assert!(within(ta, now) && within(tb, now));
            }
            _ => panic!("demoted with fewer than two other sites"),
        }
    }
    // Demotion is for the rest of the run.
    if before.demoted.is_some() {
        assert!(shared.demoted == before.demoted);
    }
}

/// One tab's step, from any record and shared state meeting their invariants, for
/// any event naming it, at any time: the invariants are kept;
/// `theorem_gpu_restart_bounded`'s step (a drawing process's exit restarts in the
/// same mode only if fewer than two recorded exits of that mode are within the
/// window); every-tab demotion by refusal only from a process in hardware that had
/// not said `GpuReady`; and the action is for this tab.
#[kani::proof]
fn tab_step_any() {
    let config = any_config();
    let mut shared = any_shared(&config);
    let id = TabId(kani::any());
    let mut tab = any_tab(id, &config);
    let event = any_event(id);
    let now: u64 = kani::any();
    let (shared_before, tab_before) = (shared, tab);
    let action = tab.step(&mut shared, &config, event, now);
    assert!(tab.invariant(&config) && shared.invariant(&config));
    assert!(tab.id == id);
    if let Some(a) = action {
        assert!(a.tab() == id);
    }
    if let (Event::Exited { .. }, Phase::Running, Some(Action::Start { software, .. })) =
        (event, tab_before.phase, action)
    {
        if software == (tab_before.mode == Mode::Software) {
            let [a, b] = tab_before.exits;
            assert!(!(a.is_some_and(|t| within(t, now)) && b.is_some_and(|t| within(t, now))));
        }
    }
    if shared_before.demoted.is_none() && shared.demoted == Some(Demotion::Refused) {
        assert!(tab_before.phase == Phase::Starting && tab_before.mode == Mode::Hardware);
        assert!(matches!(
            event,
            Event::Refused { .. } | Event::Exited { .. }
        ));
    }
    // Only a hardware exit of a drawing process is counted by site.
    if shared.sites != shared_before.sites {
        assert!(matches!(event, Event::Exited { .. }));
        assert!(tab_before.phase == Phase::Running && tab_before.mode == Mode::Hardware);
    }
}

/// `theorem_gpu_exit_contained`, one step of the whole policy from any two-tab state
/// meeting the invariant: an event for the first tab, or for a tab not open,
/// leaves the second tab's record unchanged, and any action is for the event's tab.
/// The policy's step only finds the event's tab and steps it (`tab_step_any`), so
/// the same holds for every number of tabs.
#[kani::proof]
#[kani::unwind(4)]
fn policy_contained_any() {
    let config = any_config();
    let shared = any_shared(&config);
    let a = any_tab(TabId(kani::any()), &config);
    let b = any_tab(TabId(kani::any()), &config);
    kani::assume(a.id != b.id);
    let mut policy = Policy {
        config,
        shared,
        tabs: vec![a, b],
    };
    let target = TabId(kani::any());
    kani::assume(target != b.id);
    let event = any_event(target);
    let now: u64 = kani::any();
    let action = policy.step(event, now);
    assert!(policy.invariant());
    assert!(policy.tab(b.id) == Some(&b));
    if let Some(act) = action {
        assert!(act.tab() == target);
    }
}

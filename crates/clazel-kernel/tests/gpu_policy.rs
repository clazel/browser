//! The GPU crash policy (phase-5.md item 5.17c), row by row, through the exec
//! kernel as the host drives it: the four rules, the refusal, the numbers
//! (300 seconds, three exits, three sites) at both edges, and that a GPU exit
//! touches no other tab. The proofs (`gpu_theorems.rs`, `gpu_rel.rs`) are what
//! say the kernel does these things for every state; these check the rows
//! the plan names.

mod support;

use clazel_ipc::message::codec::{Msg, encode_framed};
use clazel_kernel::exec::records::EventRecord;
use support::{Kernel, Out, code_points};

/// A time well inside the cookie clock's range.
const T0: u64 = 13_000_000_000;

fn tick(kernel: &mut Kernel, time: u64) {
    kernel.event(&EventRecord::Tick { time });
}

fn tab(kernel: &mut Kernel, url: &str) -> u64 {
    let (id, _) = kernel.open_tab(url, "");
    id.unwrap_or(u64::MAX)
}

fn ready(kernel: &mut Kernel, id: u64, software: bool) -> Vec<Out> {
    let bytes = encode_framed(&Msg::GpuReady { software }).unwrap_or_default();
    kernel.event(&EventRecord::FromGpu { id, bytes })
}

fn exited(kernel: &mut Kernel, id: u64) -> Vec<Out> {
    kernel.event(&EventRecord::GpuExited { id })
}

/// A tab whose GPU process said `GpuReady` in hardware.
fn drawing(kernel: &mut Kernel, url: &str) -> u64 {
    let id = tab(kernel, url);
    assert!(ready(kernel, id, false).is_empty());
    id
}

/// An exit while drawing, then the new process's `GpuReady`; the exit's
/// outputs.
fn crash(kernel: &mut Kernel, id: u64, software: bool) -> Vec<Out> {
    let out = exited(kernel, id);
    ready(kernel, id, software);
    out
}

#[test]
fn rule_1_an_exit_restarts_the_gpu_process_in_the_same_mode() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let id = drawing(&mut k, "https://a.test/");
    assert_eq!(crash(&mut k, id, false), vec![Out::SpawnGpu(id)]);
    // With a viewport, the renderer and the new process are told it again,
    // so the renderer sends its whole list again.
    k.event(&EventRecord::Resize {
        tab: id,
        width: 8,
        height: 6,
        scale: 1,
    });
    tick(&mut k, T0 + 1000);
    assert_eq!(
        crash(&mut k, id, false),
        vec![
            Out::SpawnGpu(id),
            Out::To(
                id,
                Msg::Viewport {
                    width: 8,
                    height: 6,
                    scale: 1
                }
            ),
            Out::ToGpu(
                id,
                Msg::GpuViewport {
                    width: 8,
                    height: 6,
                    scale: 1
                }
            ),
        ]
    );
}

#[test]
fn rule_2_the_third_exit_within_300_seconds_moves_the_tab_to_software() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let id = drawing(&mut k, "https://a.test/");
    assert_eq!(crash(&mut k, id, false), vec![Out::SpawnGpu(id)]);
    tick(&mut k, T0 + 100);
    assert_eq!(crash(&mut k, id, false), vec![Out::SpawnGpu(id)]);
    // 299 seconds after the first: the third within the window.
    tick(&mut k, T0 + 299);
    assert_eq!(crash(&mut k, id, true), vec![Out::SpawnGpuSoftware(id)]);
    // Another tab is untouched: it still restarts in hardware.
    let other = drawing(&mut k, "https://b.test/");
    assert_eq!(crash(&mut k, other, false), vec![Out::SpawnGpu(other)]);
}

#[test]
fn rule_2_an_exit_300_seconds_after_the_oldest_does_not_count() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let id = drawing(&mut k, "https://a.test/");
    crash(&mut k, id, false);
    tick(&mut k, T0 + 100);
    crash(&mut k, id, false);
    tick(&mut k, T0 + 300);
    assert_eq!(crash(&mut k, id, false), vec![Out::SpawnGpu(id)]);
}

#[test]
fn rule_4_software_failing_three_times_stops_the_tab_with_the_notice() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let id = drawing(&mut k, "https://a.test/");
    crash(&mut k, id, false);
    crash(&mut k, id, false);
    // The third hardware exit: to software.
    assert_eq!(crash(&mut k, id, true), vec![Out::SpawnGpuSoftware(id)]);
    // The mode changed, so software counts afresh: two restarts, then the
    // third software exit within 300 seconds stops the tab.
    assert_eq!(crash(&mut k, id, true), vec![Out::SpawnGpuSoftware(id)]);
    assert_eq!(crash(&mut k, id, true), vec![Out::SpawnGpuSoftware(id)]);
    assert_eq!(
        exited(&mut k, id),
        vec![Out::GpuStopped(id, code_points("https://a.test/"))]
    );
    // Stopped: no process, so a further exit changes nothing.
    assert!(exited(&mut k, id).is_empty());
}

#[test]
fn an_exit_before_gpu_ready_in_hardware_puts_every_tab_in_software() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let id = tab(&mut k, "https://a.test/");
    assert_eq!(
        exited(&mut k, id),
        vec![Out::GpuAllSoftware, Out::SpawnGpuSoftware(id)]
    );
    // Told once. A tab opened after it starts in software, so its process
    // dying before `GpuReady` is rule 4: the notice.
    let other = tab(&mut k, "https://b.test/");
    assert_eq!(
        exited(&mut k, other),
        vec![Out::GpuStopped(other, code_points("https://b.test/"))]
    );
}

#[test]
fn an_exit_before_gpu_ready_in_software_stops_the_tab() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let id = tab(&mut k, "https://a.test/");
    exited(&mut k, id);
    // The restarted process is software and dies before `GpuReady`.
    assert_eq!(
        exited(&mut k, id),
        vec![Out::GpuStopped(id, code_points("https://a.test/"))]
    );
}

#[test]
fn rule_3_hardware_exits_from_three_sites_put_every_tab_in_software() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let a = drawing(&mut k, "https://a.test/");
    let b = drawing(&mut k, "https://b.test/");
    let c = drawing(&mut k, "https://c.test/");
    assert_eq!(crash(&mut k, a, false), vec![Out::SpawnGpu(a)]);
    assert_eq!(crash(&mut k, b, false), vec![Out::SpawnGpu(b)]);
    tick(&mut k, T0 + 299);
    assert_eq!(
        crash(&mut k, c, true),
        vec![Out::GpuAllSoftware, Out::SpawnGpuSoftware(c)]
    );
}

#[test]
fn rule_3_one_site_crashing_many_tabs_demotes_nobody_else() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let a1 = drawing(&mut k, "https://a.test/");
    let a2 = drawing(&mut k, "https://a.test/x");
    let a3 = drawing(&mut k, "https://www.a.test/");
    let b = drawing(&mut k, "https://b.test/");
    for id in [a1, a2, a3] {
        assert_eq!(crash(&mut k, id, false), vec![Out::SpawnGpu(id)]);
    }
    // Two sites, not three: nothing for every tab.
    assert_eq!(crash(&mut k, b, false), vec![Out::SpawnGpu(b)]);
}

#[test]
fn rule_3_exits_300_seconds_apart_do_not_make_three_sites() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let a = drawing(&mut k, "https://a.test/");
    let b = drawing(&mut k, "https://b.test/");
    let c = drawing(&mut k, "https://c.test/");
    crash(&mut k, a, false);
    crash(&mut k, b, false);
    tick(&mut k, T0 + 300);
    assert_eq!(crash(&mut k, c, false), vec![Out::SpawnGpu(c)]);
}

#[test]
fn the_hosts_gpu_software_tells_the_host_once() {
    let mut k = Kernel::new();
    assert_eq!(
        k.event(&EventRecord::GpuSoftware),
        vec![Out::GpuAllSoftware]
    );
    assert!(k.event(&EventRecord::GpuSoftware).is_empty());
    // A process started after it is a software one: its exit before
    // `GpuReady` stops the tab.
    let id = tab(&mut k, "https://a.test/");
    assert_eq!(
        exited(&mut k, id),
        vec![Out::GpuStopped(id, code_points("https://a.test/"))]
    );
}

#[test]
fn a_hardware_process_that_found_only_software_counts_as_software() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let id = tab(&mut k, "https://a.test/");
    assert!(ready(&mut k, id, true).is_empty());
    assert_eq!(crash(&mut k, id, true), vec![Out::SpawnGpuSoftware(id)]);
}

#[test]
fn a_frame_after_an_exit_is_not_painted_until_gpu_ready() {
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let id = drawing(&mut k, "https://a.test/");
    k.event(&EventRecord::Resize {
        tab: id,
        width: 8,
        height: 6,
        scale: 1,
    });
    exited(&mut k, id);
    // The renderer's own messages are unaffected by its GPU process's exit.
    assert!(
        k.send(
            id,
            &Msg::Title {
                title: b"T".to_vec()
            }
        )
        .is_empty()
    );
    let frame = |buffer| EventRecord::FromGpu {
        id,
        bytes: encode_framed(&Msg::FrameReady {
            buffer,
            width: 8,
            height: 6,
        })
        .unwrap_or_default(),
    };
    assert!(k.event(&frame(0)).is_empty());
    ready(&mut k, id, false);
    assert_eq!(k.event(&frame(1)).len(), 1);
}

#[test]
fn an_exit_of_a_process_the_kernel_does_not_know_is_ignored() {
    let mut k = Kernel::new();
    let id = drawing(&mut k, "https://a.test/");
    assert!(exited(&mut k, id + 9).is_empty());
    // The tab still restarts as before.
    assert_eq!(crash(&mut k, id, false), vec![Out::SpawnGpu(id)]);
}

#[test]
fn the_declassified_site_count_alone_changes_only_the_shared_count() {
    // `GpuSiteExit` is never sent by the host; it is what another domain's
    // hardware exit leaves for an observer. Three distinct sites make it say
    // `GpuAllSoftware`, and nothing else is output.
    let mut k = Kernel::new();
    tick(&mut k, T0);
    let site = |host: &str| EventRecord::GpuSiteExit {
        lock: clazel_origin::exec::ParsedOrigin::Opaque(match host {
            "a" => 1_000,
            "b" => 1_001,
            _ => 1_002,
        }),
    };
    assert!(k.event(&site("a")).is_empty());
    assert!(k.event(&site("b")).is_empty());
    assert_eq!(k.event(&site("c")), vec![Out::GpuAllSoftware]);
}

//! The crash policy (phase-5.md item 5.17c): what happens when a tab's GPU
//! process exits, as a pure state machine over the kernel's events.
//!
//! The plan puts this machine in the kernel, proven there, over the host event
//! `GpuExited { tab }` and the messages `GpuReady` and `GpuRefused` of item 5.18.
//! None of those exist yet, so it is built here, with no dependency and no foreign
//! call, for the kernel to take over: 5.18 states it in the kernel's spec and proves
//! the three theorems there (with certified mutations). Here its rules are tested
//! row by row and the step is checked by Kani from any state meeting the invariants
//! (`src/proofs.rs`).
//!
//! # The rules, with the numbers stated once
//!
//! [`WINDOW_MS`] is five minutes, [`EXITS`] and [`SITES`] are three.
//!
//! 1. A tab's GPU process exits while drawing: the tab keeps its last frame (the
//!    host's), and the kernel starts a new process in the same mode ([`Action::Start`]).
//! 2. The [`EXITS`]th exit of a tab in one mode within [`WINDOW_MS`]: a hardware tab
//!    goes to software until it navigates to another site.
//! 3. Exits in hardware from [`SITES`] different sites within [`WINDOW_MS`]: every
//!    tab goes to software for the rest of the run, each at its next start. Counting
//!    by site is deliberate: otherwise any one page could crash its own GPU process
//!    on purpose and put the whole browser on the slow path.
//! 4. Software also exits [`EXITS`] times within [`WINDOW_MS`], or there is no
//!    fallback: the tab stops restarting and the host draws a notice in the content
//!    area with the URL and the reason ([`Action::Notice`]). A reload tries once more.
//!
//! # Contracts
//!
//! `Policy::step(event, now)` from any policy meeting [`Policy::invariant`]:
//!
//! - **Invariants kept**: the policy after meets [`Policy::invariant`].
//! - **Contained** (the plan's `theorem_gpu_exit_contained`): every other tab's
//!   record is unchanged, and the action, if any, is for the event's tab. Another
//!   tab's next start can change only through [`Shared::demoted`], which the next
//!   contract bounds.
//! - **Sites** (`theorem_site_cannot_demote_others`): an exit sets
//!   [`Demotion::Sites`] only if two sites other than its own have hardware exits
//!   recorded within [`WINDOW_MS`] of it, so exits from fewer than [`SITES`] sites
//!   never change another site's mode; and [`Demotion::Refused`] is set only by a
//!   process in hardware that had not said `GpuReady`, which no page has reached.
//! - **Restarts bounded** (`theorem_gpu_restart_bounded`): a [`Action::Start`] in
//!   the mode the tab was drawing in follows an exit only if fewer than two of the
//!   tab's recorded exits in that mode are within [`WINDOW_MS`]; so in any window a
//!   tab restarts in one mode at most `EXITS - 1` times after exits of that mode,
//!   each mode at most once, and once more per reload.
//!
//! # Modelling choices
//!
//! - **Time is the host's monotonic clock in milliseconds**, given with each event:
//!   the kernel is pure. A time earlier than one recorded counts as no time passed
//!   (`saturating_sub`), which can only move a tab on sooner.
//! - **A refusal is a property of the machine.** `GpuRefused`, or an exit before
//!   `GpuReady` in hardware (a missing device, a driver 5.21a's sandbox kills at
//!   start), puts every tab in software ([`Demotion::Refused`]). No page has reached a
//!   process before `GpuReady` (it reads no list until then), so a page cannot cause
//!   this, and these exits are not counted by site. A `GpuRefused` at any other time
//!   is out of order and ignored here; the kernel ends that process, and its exit
//!   counts under rules 1 to 3.
//! - **Every-tab demotion takes effect at each tab's next start.** No running process
//!   is ended for it: a tab drawing well keeps drawing, and an exit changes no other
//!   tab's state or output (`theorem_gpu_exit_contained`).
//! - **The window counts the last two exits in the current mode** ([`Tab::exits`],
//!   newest first): the third within [`WINDOW_MS`] moves the tab on. Changing mode
//!   clears them.
//! - **Only hardware exits are counted by site**, and the two most recent distinct
//!   sites are kept ([`Shared::sites`]). Before every-tab demotion no three sites have
//!   exits in one window, so with a monotonic clock the sites with exits in the
//!   window are among those two.
//! - **A reload of a stopped tab** starts it in its mode with two exits recorded at
//!   the reload's time, so one more exit within [`WINDOW_MS`] moves it on (to the
//!   notice again, or from hardware to software), and after that window it counts
//!   afresh.
//! - **Without a fallback (macOS)**, nothing goes to software: the third hardware
//!   exit, a refusal or a start that fails goes to the notice, and every-tab demotion
//!   never happens. `--gpu=software` there puts every tab on the notice.
//! - **A cross-site navigation** starts a new process (5.0: the GPU process is
//!   replaced with the renderer) in hardware unless every tab is in software, with
//!   no exits recorded; a same-site navigation changes nothing here, even on a
//!   stopped tab, which only a reload or another site restarts.
//! - **`GpuReady { software: true }` from a process started for hardware** (the
//!   Vulkan loader offered only lavapipe) moves the tab to software, so the indicator
//!   shows; `software: false` from one started for software is out of order and
//!   ignored.
//! - **Sites and tabs are the kernel's ids** ([`SiteId`], [`TabId`]); the kernel
//!   interns a site (scheme and registrable domain) to a number.
//! - **Counts do not outlive a run** until item 3.10's store exists, so a driver that
//!   crashes every time costs a few restarts on each launch.

use crate::start::Mode;

/// The window in which exits are counted: five minutes.
pub const WINDOW_MS: u64 = 5 * 60 * 1000;

/// The exits of one tab in one mode within [`WINDOW_MS`] that move it on.
pub const EXITS: usize = 3;

/// The sites with hardware exits within [`WINDOW_MS`] that put every tab in software.
pub const SITES: usize = 3;

/// A tab, as the kernel numbers it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TabId(pub u64);

/// A site (scheme and registrable domain), as the kernel interns it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SiteId(pub u64);

/// What the platform offers and what the user asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
    /// A software driver exists: lavapipe on Linux, WARP on Windows; not on macOS.
    pub fallback: bool,
    /// `browse --gpu=software`: every tab starts in software.
    pub software_only: bool,
}

/// Why every tab is in software.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Demotion {
    /// A GPU process was refused, or exited before `GpuReady`, in hardware.
    Refused,
    /// Hardware exits from [`SITES`] sites within [`WINDOW_MS`].
    Sites,
}

/// What every tab shares. Invariant ([`Shared::invariant`]): the two sites are
/// different, the second is recorded only with the first, and every-tab demotion
/// happens only where there is a fallback.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Shared {
    /// Every tab is in software from its next start, for the rest of the run.
    pub demoted: Option<Demotion>,
    /// The two most recent distinct sites with a hardware exit, and the time of
    /// each one's latest, newest first.
    pub sites: [Option<(SiteId, u64)>; 2],
}

/// Where a tab's GPU process is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    /// Started; no `GpuReady` yet, so no list has reached it.
    Starting,
    /// Said `GpuReady`: drawing.
    Running,
    /// Not restarted: the host shows the notice until a reload or another site.
    Stopped(Reason),
}

/// Why a tab shows the notice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    /// [`EXITS`] exits within [`WINDOW_MS`] in the last mode there is.
    Crashed,
    /// The hardware device was refused, or its process died before `GpuReady`, and
    /// there is no fallback.
    Refused,
    /// Software was needed and could not start: there is none on this platform, or
    /// its process died before `GpuReady`.
    NoSoftware,
}

/// One tab's record. Invariant ([`Tab::invariant`]): a second exit is recorded only
/// with a first, and a tab is in software only where software can be asked for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tab {
    /// The tab.
    pub id: TabId,
    /// The site its document is from.
    pub site: SiteId,
    /// The mode it runs, or last ran, in.
    pub mode: Mode,
    /// Where its process is.
    pub phase: Phase,
    /// The last two exits in this mode, newest first.
    pub exits: [Option<u64>; 2],
}

/// What the kernel tells the policy. Each names one tab.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// A tab opened on a site: its first GPU process.
    Opened {
        /// The tab.
        tab: TabId,
        /// Its site.
        site: SiteId,
    },
    /// `GpuReady { software }` from the tab's current process.
    Ready {
        /// The tab.
        tab: TabId,
        /// Its adapter is a software driver.
        software: bool,
    },
    /// `GpuRefused` from the tab's current process.
    Refused {
        /// The tab.
        tab: TabId,
    },
    /// The host's `GpuExited { tab }`: the tab's current process ended.
    Exited {
        /// The tab.
        tab: TabId,
    },
    /// The tab committed a document from `site`.
    Navigated {
        /// The tab.
        tab: TabId,
        /// The new document's site.
        site: SiteId,
    },
    /// The user reloaded the tab.
    Reload {
        /// The tab.
        tab: TabId,
    },
    /// The tab closed.
    Closed {
        /// The tab.
        tab: TabId,
    },
}

impl Event {
    /// The tab the event names.
    pub fn tab(&self) -> TabId {
        match *self {
            Event::Opened { tab, .. }
            | Event::Ready { tab, .. }
            | Event::Refused { tab }
            | Event::Exited { tab }
            | Event::Navigated { tab, .. }
            | Event::Reload { tab }
            | Event::Closed { tab } => tab,
        }
    }
}

/// What the kernel does. At most one per event, always for the event's tab.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    /// Start a GPU process for the tab, in software or not, with a new channel to
    /// its renderer, which sends its whole list again.
    Start {
        /// The tab.
        tab: TabId,
        /// In software.
        software: bool,
    },
    /// The tab's process is drawing; the host shows the software indicator in the
    /// address bar strip if `software`.
    Drawing {
        /// The tab.
        tab: TabId,
        /// In software.
        software: bool,
    },
    /// The host draws the notice in the tab's content area, with its URL and the
    /// reason.
    Notice {
        /// The tab.
        tab: TabId,
        /// Why.
        reason: Reason,
    },
}

impl Action {
    /// The tab the action is for.
    pub fn tab(&self) -> TabId {
        match *self {
            Action::Start { tab, .. }
            | Action::Drawing { tab, .. }
            | Action::Notice { tab, .. } => tab,
        }
    }
}

/// The whole policy: the configuration, what tabs share, and each open tab's record.
/// Invariant ([`Policy::invariant`]): tab ids are distinct and every record meets
/// its own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Policy {
    /// What the platform offers and what the user asked for.
    pub config: Config,
    /// What every tab shares.
    pub shared: Shared,
    /// The open tabs.
    pub tabs: Vec<Tab>,
}

/// Whether `then` is within [`WINDOW_MS`] before `now` (a later `then` counts as no
/// time passed).
pub fn within(then: u64, now: u64) -> bool {
    now.saturating_sub(then) < WINDOW_MS
}

impl Shared {
    /// The invariant: different sites, the second only with the first, demotion only
    /// with a fallback.
    pub fn invariant(&self, config: &Config) -> bool {
        let sites = match self.sites {
            [Some((a, _)), Some((b, _))] => a != b,
            [None, Some(_)] => false,
            _ => true,
        };
        sites && (self.demoted.is_none() || config.fallback)
    }
}

impl Tab {
    /// The invariant: a second exit only with a first; software only where it can be
    /// asked for (a fallback, or `--gpu=software`).
    pub fn invariant(&self, config: &Config) -> bool {
        let exits = !matches!(self.exits, [None, Some(_)]);
        let mode = self.mode == Mode::Hardware || config.fallback || config.software_only;
        exits && mode
    }
}

impl Policy {
    /// The invariant: distinct tab ids, and every part meeting its own.
    pub fn invariant(&self) -> bool {
        let distinct = self.tabs.iter().enumerate().all(|(i, a)| {
            self.tabs
                .iter()
                .skip(i.saturating_add(1))
                .all(|b| b.id != a.id)
        });
        distinct
            && self.shared.invariant(&self.config)
            && self.tabs.iter().all(|t| t.invariant(&self.config))
    }
}

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

// `Shared::sites` keeps `SITES - 1` sites; written out, since it is an array length.
const _: () = assert!(SITES == 3);

impl Shared {
    /// Rule 3: a hardware exit from `site` at `now`. Every tab goes to software if
    /// the two other most recent sites both have exits within [`WINDOW_MS`] and there
    /// is a fallback; either way `site` becomes the most recent.
    pub fn note_exit(&mut self, site: SiteId, now: u64, config: &Config) {
        let others = self
            .sites
            .iter()
            .flatten()
            .filter(|&&(s, t)| s != site && within(t, now))
            .count();
        if self.demoted.is_none() && config.fallback && others.saturating_add(1) >= SITES {
            self.demoted = Some(Demotion::Sites);
        }
        let [first, second] = self.sites;
        self.sites = match first {
            Some((s, _)) if s == site => [Some((site, now)), second],
            _ => [Some((site, now)), first],
        };
    }
}

impl Tab {
    /// A new tab on `site`, before its first start.
    pub fn new(id: TabId, site: SiteId) -> Tab {
        Tab {
            id,
            site,
            mode: Mode::Hardware,
            phase: Phase::Starting,
            exits: [None, None],
        }
    }

    /// The mode the next start uses: software if asked for, if every tab is in
    /// software, or if this tab is.
    pub fn wanted(&self, shared: &Shared, config: &Config) -> Mode {
        if config.software_only || shared.demoted.is_some() || self.mode == Mode::Software {
            Mode::Software
        } else {
            Mode::Hardware
        }
    }

    /// Start a process in the wanted mode (a new mode records no exits), or, for
    /// software with no fallback, stop with the notice.
    fn start(&mut self, shared: &Shared, config: &Config) -> Action {
        let mode = self.wanted(shared, config);
        if mode != self.mode {
            self.mode = mode;
            self.exits = [None, None];
        }
        if mode == Mode::Software && !config.fallback {
            self.stop(Reason::NoSoftware)
        } else {
            self.phase = Phase::Starting;
            Action::Start {
                tab: self.id,
                software: mode == Mode::Software,
            }
        }
    }

    fn stop(&mut self, reason: Reason) -> Action {
        self.phase = Phase::Stopped(reason);
        Action::Notice {
            tab: self.id,
            reason,
        }
    }

    /// A process in hardware refused, or ended before `GpuReady`: every tab to
    /// software if there is one, else this tab to the notice.
    fn refused(&mut self, shared: &mut Shared, config: &Config) -> Action {
        if config.fallback {
            if shared.demoted.is_none() {
                shared.demoted = Some(Demotion::Refused);
            }
            self.start(shared, config)
        } else {
            self.stop(Reason::Refused)
        }
    }

    /// Item 5.17c's crash policy for one event naming this tab, at `now`. Reads and
    /// writes this tab's record and `shared` and nothing else. `Opened` and `Closed`
    /// are [`Policy::step`]'s and do nothing here.
    pub fn step(
        &mut self,
        shared: &mut Shared,
        config: &Config,
        event: Event,
        now: u64,
    ) -> Option<Action> {
        match event {
            Event::Opened { .. } | Event::Closed { .. } => None,
            Event::Ready { software, .. } => {
                if self.phase != Phase::Starting {
                    return None;
                }
                if software && self.mode == Mode::Hardware {
                    // Only a software driver was found. Without a fallback this cannot
                    // be an honest answer (no software driver exists): out of order.
                    if !config.fallback {
                        return None;
                    }
                    self.mode = Mode::Software;
                    self.exits = [None, None];
                } else if !software && self.mode == Mode::Software {
                    return None;
                }
                self.phase = Phase::Running;
                Some(Action::Drawing {
                    tab: self.id,
                    software: self.mode == Mode::Software,
                })
            }
            Event::Refused { .. } => {
                if self.phase == Phase::Starting && self.mode == Mode::Hardware {
                    Some(self.refused(shared, config))
                } else {
                    None
                }
            }
            Event::Exited { .. } => match self.phase {
                Phase::Stopped(_) => None,
                // Before `GpuReady`: a refusal (the plan: "a driver 5.21a's sandbox
                // kills at startup counts as refused").
                Phase::Starting => Some(match self.mode {
                    Mode::Hardware => self.refused(shared, config),
                    Mode::Software => self.stop(Reason::NoSoftware),
                }),
                Phase::Running => {
                    if self.mode == Mode::Hardware {
                        shared.note_exit(self.site, now, config);
                    }
                    let [a, b] = self.exits;
                    let third = [a, b].iter().all(|e| e.is_some_and(|t| within(t, now)));
                    if !third {
                        // Rule 1.
                        self.exits = [Some(now), a];
                        Some(self.start(shared, config))
                    } else if self.mode == Mode::Hardware && config.fallback {
                        // Rule 2.
                        self.mode = Mode::Software;
                        self.exits = [None, None];
                        Some(self.start(shared, config))
                    } else {
                        // Rule 4.
                        Some(self.stop(Reason::Crashed))
                    }
                }
            },
            Event::Navigated { site, .. } => {
                if site == self.site {
                    return None;
                }
                self.site = site;
                self.mode = Mode::Hardware;
                self.exits = [None, None];
                Some(self.start(shared, config))
            }
            Event::Reload { .. } => {
                if !matches!(self.phase, Phase::Stopped(_)) {
                    return None;
                }
                self.exits = [Some(now), Some(now)];
                Some(self.start(shared, config))
            }
        }
    }
}

impl Policy {
    /// No tabs, nothing recorded.
    pub fn new(config: Config) -> Policy {
        Policy {
            config,
            shared: Shared::default(),
            tabs: Vec::new(),
        }
    }

    /// The record of `tab`, if it is open.
    pub fn tab(&self, tab: TabId) -> Option<&Tab> {
        self.tabs.iter().find(|t| t.id == tab)
    }

    /// Item 5.17c's crash policy: one event at `now`, and what the kernel does. Only
    /// the event's tab's record and [`Policy::shared`] change, and the action is for
    /// the event's tab. An event for a tab that is not open (or `Opened` for one that
    /// is) changes nothing.
    pub fn step(&mut self, event: Event, now: u64) -> Option<Action> {
        match event {
            Event::Opened { tab, site } => {
                if self.tab(tab).is_some() {
                    return None;
                }
                let mut record = Tab::new(tab, site);
                let action = record.start(&self.shared, &self.config);
                self.tabs.push(record);
                Some(action)
            }
            Event::Closed { tab } => {
                self.tabs.retain(|t| t.id != tab);
                None
            }
            _ => {
                let id = event.tab();
                let record = self.tabs.iter_mut().find(|t| t.id == id)?;
                record.step(&mut self.shared, &self.config, event, now)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Action, Config, Demotion, Event, Phase, Policy, Reason, SiteId, TabId, WINDOW_MS};
    use crate::start::Mode;

    const LINUX: Config = Config {
        fallback: true,
        software_only: false,
    };
    const MACOS: Config = Config {
        fallback: false,
        software_only: false,
    };
    const T: TabId = TabId(1);
    const U: TabId = TabId(2);
    const MIN: u64 = 60_000;

    fn start(tab: TabId, software: bool) -> Option<Action> {
        Some(Action::Start { tab, software })
    }

    fn notice(tab: TabId, reason: Reason) -> Option<Action> {
        Some(Action::Notice { tab, reason })
    }

    /// A policy with tab `tab` open on `site` and drawing in hardware.
    fn drawing(config: Config, tabs: &[(TabId, u64)]) -> Policy {
        let mut p = Policy::new(config);
        for &(tab, site) in tabs {
            assert_eq!(
                p.step(
                    Event::Opened {
                        tab,
                        site: SiteId(site)
                    },
                    0
                ),
                start(tab, false)
            );
            assert_eq!(
                p.step(
                    Event::Ready {
                        tab,
                        software: false
                    },
                    0
                ),
                Some(Action::Drawing {
                    tab,
                    software: false
                })
            );
        }
        p
    }

    /// Exit and come back up, at `now`; the action of the exit.
    fn crash(p: &mut Policy, tab: TabId, now: u64) -> Option<Action> {
        let a = p.step(Event::Exited { tab }, now);
        if let Some(Action::Start { software, .. }) = a {
            p.step(Event::Ready { tab, software }, now);
        }
        a
    }

    fn phase(p: &Policy, tab: TabId) -> Option<Phase> {
        p.tab(tab).map(|t| t.phase)
    }

    // Opened.

    #[test]
    fn a_tab_opens_in_hardware() {
        let mut p = Policy::new(LINUX);
        assert_eq!(
            p.step(
                Event::Opened {
                    tab: T,
                    site: SiteId(1)
                },
                0
            ),
            start(T, false)
        );
        assert_eq!(phase(&p, T), Some(Phase::Starting));
        // Opening it again changes nothing.
        let before = p.clone();
        assert_eq!(
            p.step(
                Event::Opened {
                    tab: T,
                    site: SiteId(2)
                },
                0
            ),
            None
        );
        assert_eq!(p, before);
    }

    #[test]
    fn gpu_software_opens_in_software_or_the_notice() {
        let mut p = Policy::new(Config {
            fallback: true,
            software_only: true,
        });
        let open = Event::Opened {
            tab: T,
            site: SiteId(1),
        };
        assert_eq!(p.step(open, 0), start(T, true));
        let mut p = Policy::new(Config {
            fallback: false,
            software_only: true,
        });
        assert_eq!(p.step(open, 0), notice(T, Reason::NoSoftware));
        assert!(p.invariant());
    }

    // Ready.

    #[test]
    fn ready_rows() {
        // Hardware says hardware: drawing.
        let p = drawing(LINUX, &[(T, 1)]);
        assert_eq!(phase(&p, T), Some(Phase::Running));
        // Hardware says software (only lavapipe was found): drawing in software.
        let mut p = Policy::new(LINUX);
        p.step(
            Event::Opened {
                tab: T,
                site: SiteId(1),
            },
            0,
        );
        assert_eq!(
            p.step(
                Event::Ready {
                    tab: T,
                    software: true
                },
                0
            ),
            Some(Action::Drawing {
                tab: T,
                software: true
            })
        );
        assert_eq!(p.tab(T).map(|t| t.mode), Some(Mode::Software));
        // A second Ready, once running: ignored.
        let before = p.clone();
        assert_eq!(
            p.step(
                Event::Ready {
                    tab: T,
                    software: true
                },
                0
            ),
            None
        );
        assert_eq!(p, before);
        // Without a fallback, hardware saying software is out of order.
        let mut p = Policy::new(MACOS);
        p.step(
            Event::Opened {
                tab: T,
                site: SiteId(1),
            },
            0,
        );
        assert_eq!(
            p.step(
                Event::Ready {
                    tab: T,
                    software: true
                },
                0
            ),
            None
        );
        assert_eq!(phase(&p, T), Some(Phase::Starting));
        // Software saying hardware is out of order.
        let mut p = Policy::new(Config {
            fallback: true,
            software_only: true,
        });
        p.step(
            Event::Opened {
                tab: T,
                site: SiteId(1),
            },
            0,
        );
        assert_eq!(
            p.step(
                Event::Ready {
                    tab: T,
                    software: false
                },
                0
            ),
            None
        );
        assert_eq!(
            p.step(
                Event::Ready {
                    tab: T,
                    software: true
                },
                0
            ),
            Some(Action::Drawing {
                tab: T,
                software: true
            })
        );
    }

    // Refused, and exits before Ready.

    #[test]
    fn a_refusal_puts_every_tab_in_software() {
        let mut p = drawing(LINUX, &[(U, 2)]);
        p.step(
            Event::Opened {
                tab: T,
                site: SiteId(1),
            },
            0,
        );
        assert_eq!(p.step(Event::Refused { tab: T }, 1), start(T, true));
        assert_eq!(p.shared.demoted, Some(Demotion::Refused));
        // The other tab keeps drawing in hardware until its next start.
        assert_eq!(
            p.tab(U).map(|t| (t.mode, t.phase)),
            Some((Mode::Hardware, Phase::Running))
        );
        assert_eq!(crash(&mut p, U, 2), start(U, true));
        // A refusal from a software process, or once drawing, is ignored.
        let before = p.clone();
        assert_eq!(p.step(Event::Refused { tab: T }, 3), None);
        p.step(
            Event::Ready {
                tab: T,
                software: true,
            },
            3,
        );
        let mut q = drawing(LINUX, &[(T, 1)]);
        let q_before = q.clone();
        assert_eq!(q.step(Event::Refused { tab: T }, 3), None);
        assert_eq!(q, q_before);
        assert_ne!(p, before);
    }

    #[test]
    fn an_exit_before_ready_is_a_refusal() {
        let mut p = Policy::new(LINUX);
        p.step(
            Event::Opened {
                tab: T,
                site: SiteId(1),
            },
            0,
        );
        assert_eq!(p.step(Event::Exited { tab: T }, 1), start(T, true));
        assert_eq!(p.shared.demoted, Some(Demotion::Refused));
        // Software also dies before Ready: the notice.
        assert_eq!(
            p.step(Event::Exited { tab: T }, 2),
            notice(T, Reason::NoSoftware)
        );
        // Stopped: an exit changes nothing.
        let before = p.clone();
        assert_eq!(p.step(Event::Exited { tab: T }, 3), None);
        assert_eq!(p, before);
    }

    #[test]
    fn without_a_fallback_a_refusal_is_the_notice() {
        for event in [Event::Refused { tab: T }, Event::Exited { tab: T }] {
            let mut p = Policy::new(MACOS);
            p.step(
                Event::Opened {
                    tab: T,
                    site: SiteId(1),
                },
                0,
            );
            assert_eq!(p.step(event, 1), notice(T, Reason::Refused));
            assert_eq!(p.shared.demoted, None);
            // A reload tries once more, in hardware.
            assert_eq!(p.step(Event::Reload { tab: T }, 2), start(T, false));
            assert_eq!(p.step(event, 3), notice(T, Reason::Refused));
        }
    }

    // Exits while drawing: rules 1, 2 and 4.

    #[test]
    fn three_exits_in_five_minutes_go_to_software_then_the_notice() {
        let mut p = drawing(LINUX, &[(T, 1)]);
        assert_eq!(crash(&mut p, T, MIN), start(T, false));
        assert_eq!(crash(&mut p, T, 2 * MIN), start(T, false));
        assert_eq!(crash(&mut p, T, 3 * MIN), start(T, true));
        assert_eq!(p.shared.demoted, None);
        assert_eq!(crash(&mut p, T, 4 * MIN), start(T, true));
        assert_eq!(crash(&mut p, T, 5 * MIN), start(T, true));
        assert_eq!(crash(&mut p, T, 6 * MIN), notice(T, Reason::Crashed));
        assert!(p.invariant());
    }

    #[test]
    fn exits_further_apart_than_the_window_keep_restarting() {
        let mut p = drawing(LINUX, &[(T, 1)]);
        // The first and third of any three are five minutes apart or more.
        for n in 1..=20 {
            assert_eq!(crash(&mut p, T, n * WINDOW_MS / 2), start(T, false));
        }
        // Just inside: the third goes to software.
        let mut p = drawing(LINUX, &[(T, 1)]);
        assert_eq!(crash(&mut p, T, 10), start(T, false));
        assert_eq!(crash(&mut p, T, 20), start(T, false));
        assert_eq!(crash(&mut p, T, 10 + WINDOW_MS - 1), start(T, true));
    }

    #[test]
    fn without_a_fallback_three_exits_are_the_notice() {
        let mut p = drawing(MACOS, &[(T, 1)]);
        assert_eq!(crash(&mut p, T, 1), start(T, false));
        assert_eq!(crash(&mut p, T, 2), start(T, false));
        assert_eq!(crash(&mut p, T, 3), notice(T, Reason::Crashed));
    }

    #[test]
    fn a_clock_going_back_counts_as_no_time() {
        let mut p = drawing(LINUX, &[(T, 1)]);
        assert_eq!(crash(&mut p, T, 10 * MIN), start(T, false));
        assert_eq!(crash(&mut p, T, 20 * MIN), start(T, false));
        assert_eq!(crash(&mut p, T, MIN), start(T, true));
    }

    // Sites: rule 3.

    #[test]
    fn three_sites_put_every_tab_in_software() {
        let mut p = drawing(
            LINUX,
            &[(TabId(1), 1), (TabId(2), 2), (TabId(3), 3), (TabId(4), 4)],
        );
        assert_eq!(crash(&mut p, TabId(1), MIN), start(TabId(1), false));
        assert_eq!(crash(&mut p, TabId(2), 2 * MIN), start(TabId(2), false));
        assert_eq!(p.shared.demoted, None);
        // The third site: it restarts in software, and so will every other tab.
        assert_eq!(crash(&mut p, TabId(3), 3 * MIN), start(TabId(3), true));
        assert_eq!(p.shared.demoted, Some(Demotion::Sites));
        assert_eq!(
            p.tab(TabId(4)).map(|t| (t.mode, t.phase)),
            Some((Mode::Hardware, Phase::Running))
        );
        assert_eq!(crash(&mut p, TabId(4), 3 * MIN), start(TabId(4), true));
        // For the rest of the run: another site does not bring hardware back.
        assert_eq!(
            p.step(
                Event::Navigated {
                    tab: TabId(4),
                    site: SiteId(9)
                },
                100 * MIN
            ),
            start(TabId(4), true)
        );
    }

    #[test]
    fn one_or_two_sites_never_demote_another() {
        // One page crashing its own process on purpose, in many tabs.
        let mut p = drawing(
            LINUX,
            &[(TabId(1), 1), (TabId(2), 1), (TabId(3), 2), (TabId(4), 3)],
        );
        for n in 0..50 {
            crash(&mut p, TabId(1 + n % 3), n);
        }
        assert_eq!(p.shared.demoted, None);
        assert_eq!(
            p.tab(TabId(4)).map(|t| (t.mode, t.phase)),
            Some((Mode::Hardware, Phase::Running))
        );
        // Three sites, but not within one window.
        let mut p = drawing(LINUX, &[(TabId(1), 1), (TabId(2), 2), (TabId(3), 3)]);
        crash(&mut p, TabId(1), 0);
        crash(&mut p, TabId(2), 3 * MIN);
        crash(&mut p, TabId(3), 3 * MIN + WINDOW_MS);
        assert_eq!(p.shared.demoted, None);
        // Software exits are not counted by site.
        let mut p = drawing(LINUX, &[(TabId(1), 1), (TabId(2), 2), (TabId(3), 3)]);
        for t in 1..=3 {
            crash(&mut p, TabId(1), t);
        }
        assert_eq!(p.tab(TabId(1)).map(|t| t.mode), Some(Mode::Software));
        // Its hardware exits are now out of the window; its software exit is not
        // counted, so two hardware sites remain.
        crash(&mut p, TabId(1), WINDOW_MS + 4);
        crash(&mut p, TabId(2), WINDOW_MS + 5);
        assert_eq!(p.shared.demoted, None);
        crash(&mut p, TabId(3), WINDOW_MS + 6);
        assert_eq!(p.shared.demoted, None);
    }

    #[test]
    fn without_a_fallback_sites_demote_nothing() {
        let mut p = drawing(MACOS, &[(TabId(1), 1), (TabId(2), 2), (TabId(3), 3)]);
        for t in 1..=3 {
            assert_eq!(crash(&mut p, TabId(t), t), start(TabId(t), false));
        }
        assert_eq!(p.shared.demoted, None);
    }

    // Navigation and reload.

    #[test]
    fn another_site_brings_a_tab_back_to_hardware() {
        let mut p = drawing(LINUX, &[(T, 1)]);
        for t in 1..=3 {
            crash(&mut p, T, t);
        }
        assert_eq!(p.tab(T).map(|t| t.mode), Some(Mode::Software));
        // The same site: nothing.
        let before = p.clone();
        assert_eq!(
            p.step(
                Event::Navigated {
                    tab: T,
                    site: SiteId(1)
                },
                4
            ),
            None
        );
        assert_eq!(p, before);
        assert_eq!(
            p.step(
                Event::Navigated {
                    tab: T,
                    site: SiteId(2)
                },
                4
            ),
            start(T, false)
        );
        assert_eq!(p.tab(T).map(|t| t.exits), Some([None, None]));
    }

    #[test]
    fn a_stopped_tab_restarts_on_another_site_not_the_same() {
        let mut p = drawing(MACOS, &[(T, 1)]);
        for t in 1..=3 {
            crash(&mut p, T, t);
        }
        assert_eq!(phase(&p, T), Some(Phase::Stopped(Reason::Crashed)));
        assert_eq!(
            p.step(
                Event::Navigated {
                    tab: T,
                    site: SiteId(1)
                },
                4
            ),
            None
        );
        assert_eq!(
            p.step(
                Event::Navigated {
                    tab: T,
                    site: SiteId(2)
                },
                4
            ),
            start(T, false)
        );
    }

    #[test]
    fn a_reload_tries_once_more() {
        let mut p = drawing(LINUX, &[(T, 1)]);
        for t in 1..=6 {
            crash(&mut p, T, t);
        }
        assert_eq!(phase(&p, T), Some(Phase::Stopped(Reason::Crashed)));
        // A reload of a tab that is not stopped does nothing.
        let mut q = drawing(LINUX, &[(T, 1)]);
        let before = q.clone();
        assert_eq!(q.step(Event::Reload { tab: T }, 7), None);
        assert_eq!(q, before);
        // Once more, then the notice at the next exit within the window.
        assert_eq!(p.step(Event::Reload { tab: T }, 10), start(T, true));
        p.step(
            Event::Ready {
                tab: T,
                software: true,
            },
            10,
        );
        assert_eq!(crash(&mut p, T, 10 + MIN), notice(T, Reason::Crashed));
        // After a window, the reloaded tab counts afresh.
        assert_eq!(p.step(Event::Reload { tab: T }, 20 * MIN), start(T, true));
        p.step(
            Event::Ready {
                tab: T,
                software: true,
            },
            20 * MIN,
        );
        assert_eq!(crash(&mut p, T, 26 * MIN), start(T, true));
    }

    // Closed, and unknown tabs.

    #[test]
    fn closed_tabs_and_unknown_tabs() {
        let mut p = drawing(LINUX, &[(T, 1), (U, 2)]);
        assert_eq!(p.step(Event::Closed { tab: T }, 1), None);
        assert!(p.tab(T).is_none());
        let before = p.clone();
        for event in [
            Event::Ready {
                tab: T,
                software: false,
            },
            Event::Refused { tab: T },
            Event::Exited { tab: T },
            Event::Navigated {
                tab: T,
                site: SiteId(5),
            },
            Event::Reload { tab: T },
            Event::Closed { tab: T },
        ] {
            assert_eq!(p.step(event, 2), None);
        }
        assert_eq!(p, before);
    }

    /// The restart bound over a trace: a tab whose process crashes every second
    /// starts twice in hardware, once into software, twice more there, and then
    /// shows the notice. No reload, so nothing more.
    #[test]
    fn a_tab_crashing_forever_restarts_five_times() {
        let mut p = drawing(LINUX, &[(T, 1)]);
        let mut starts = 0;
        for s in 1..=3600 {
            if let Some(Action::Start { .. }) = crash(&mut p, T, s * 1000) {
                starts += 1;
            }
        }
        assert_eq!(starts, 5);
        assert_eq!(phase(&p, T), Some(Phase::Stopped(Reason::Crashed)));
    }

    /// Containment and the invariants over a long pseudo-random trace: every step
    /// leaves every other tab's record unchanged, acts only for the event's tab, and
    /// keeps the invariants; every-tab demotion by sites needs three sites.
    #[test]
    fn every_step_is_contained() {
        let steps = if cfg!(miri) { 300 } else { 20_000 };
        for config in [LINUX, MACOS] {
            let mut p = Policy::new(config);
            let mut seed: u64 = 0xc1a2e1;
            let mut now = 0u64;
            for _ in 0..steps {
                seed = seed
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let r = seed >> 33;
                let tab = TabId(r % 5);
                let site = SiteId((r >> 3) % 4);
                now = now.saturating_add((r >> 5) % (2 * MIN));
                let event = match (r >> 12) % 8 {
                    0 => Event::Opened { tab, site },
                    1 | 2 => Event::Ready {
                        tab,
                        software: (r >> 16).is_multiple_of(2),
                    },
                    3 => Event::Refused { tab },
                    4 | 5 => Event::Exited { tab },
                    6 => Event::Navigated { tab, site },
                    _ => {
                        if (r >> 16).is_multiple_of(4) {
                            Event::Closed { tab }
                        } else {
                            Event::Reload { tab }
                        }
                    }
                };
                let before = p.clone();
                let action = p.step(event, now);
                assert!(p.invariant());
                assert!(action.is_none_or(|a| a.tab() == event.tab()));
                for t in &before.tabs {
                    if t.id != event.tab() {
                        assert_eq!(p.tab(t.id), Some(t));
                    }
                }
                if before.shared.demoted.is_none() && p.shared.demoted == Some(Demotion::Sites) {
                    let others = before
                        .shared
                        .sites
                        .iter()
                        .flatten()
                        .filter(|&&(s, t)| {
                            Some(s) != before.tab(event.tab()).map(|r| r.site)
                                && super::within(t, now)
                        })
                        .count();
                    assert_eq!(others, 2);
                }
            }
        }
    }
}

//! The GPU process's start (phase-5.md item 5.17c): the mode the kernel asked
//! for, the adapter the backend found, the blocklist, and the answer, before any
//! list is read.
//!
//! The only way to make a [`crate::Gpu`], and so to draw, is `Gpu::start`, which
//! checks the adapter first. Its answer is the message item 5.18 adds: `GpuReady {
//! software }` (tag 18) for [`Ready`], `GpuRefused` (tag 19) for
//! [`Refusal::Blocked`]. The other refusals are a wrong start: the process exits,
//! which the crash policy (`crate::policy`) counts as a refusal too, since it
//! happens before any list.
//!
//! # Modelling choices
//!
//! - **The kernel chooses the mode** ([`Mode`]); the GPU process does not fall back
//!   by itself. A process started for hardware that finds only a software adapter
//!   (a Linux machine whose Vulkan loader offers only lavapipe) draws with it and
//!   says so (`GpuReady { software: true }`), so the window shows the indicator. A
//!   process started for software that finds a hardware adapter exits: the host
//!   selected the software driver (the Vulkan loader's driver-file setting, WARP
//!   through `EnumWarpAdapter`), so the start is wrong.
//! - **`--gpu=hardware` skips the blocklist** ([`Check::Ignore`], with a warning
//!   the host prints) and nothing else: the crash policy still applies, since a
//!   crashing driver must still show pages. `--gpu=software` is the kernel's (every
//!   tab starts in software).
//! - **No second drawing backend.** The software mode is the same GPU code on a
//!   software driver (5.0(d)): lavapipe on Linux, WARP on Windows. The fake
//!   [`crate::soft::SoftBackend`] stays a test double and is never a fallback. On
//!   macOS there is no software Metal driver, so a refused or failing Metal device
//!   goes to the notice.

use crate::blocklist::{Adapter, Entry};

/// The mode the kernel started the GPU process in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// The machine's GPU.
    Hardware,
    /// The software driver: lavapipe on Linux, WARP on Windows; none on macOS.
    Software,
}

/// Whether the blocklist is read (`browse --gpu=hardware` ignores it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Check {
    /// Check the shipped table.
    Obey,
    /// Do not check it (`--gpu=hardware`; the host warns).
    Ignore,
}

/// How the kernel started the GPU process.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Launch {
    /// The mode.
    pub mode: Mode,
    /// Whether the blocklist is read.
    pub check: Check,
}

impl Launch {
    /// Hardware, obeying the blocklist: the default.
    pub const HARDWARE: Launch = Launch {
        mode: Mode::Hardware,
        check: Check::Obey,
    };

    /// Software.
    pub const SOFTWARE: Launch = Launch {
        mode: Mode::Software,
        check: Check::Obey,
    };
}

/// The start went through: `GpuReady { software }`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ready {
    /// The adapter is a software driver.
    pub software: bool,
}

/// Why the GPU process will not draw.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Refusal {
    /// The adapter matches this entry: `GpuRefused`, and the kernel starts the
    /// software mode.
    Blocked(Entry),
    /// The shipped table does not parse (never in a shipped build, which a test
    /// guards): the device is refused, as `GpuRefused`.
    Unreadable(crate::blocklist::ParseError),
    /// Started for software on a hardware adapter: a wrong start; the process exits.
    NotSoftware,
}

impl Refusal {
    /// Whether this refusal is sent as `GpuRefused` (otherwise the process exits
    /// without a message).
    pub fn is_gpu_refused(&self) -> bool {
        matches!(self, Refusal::Blocked(_) | Refusal::Unreadable(_))
    }
}

/// Item 5.17c, the blocklist paragraph: the answer the GPU process gives for
/// `adapter`, started by `launch`, with the blocklist `table` (the shipped one in the
/// GPU process; tests pass others). It reads no list.
pub fn admit(adapter: &Adapter, launch: Launch, table: &[u8]) -> Result<Ready, Refusal> {
    match launch.mode {
        Mode::Software if adapter.software => Ok(Ready { software: true }),
        Mode::Software => Err(Refusal::NotSoftware),
        Mode::Hardware if adapter.software => Ok(Ready { software: true }),
        Mode::Hardware if launch.check == Check::Ignore => Ok(Ready { software: false }),
        Mode::Hardware => {
            let list = crate::blocklist::Blocklist::parse(table).map_err(Refusal::Unreadable)?;
            match list.check(adapter) {
                Some(entry) => Err(Refusal::Blocked(entry.clone())),
                None => Ok(Ready { software: false }),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Check, Launch, Mode, Ready, Refusal, admit};
    use crate::blocklist::{APPLE, Adapter, Api, Version};

    const TABLE: &[u8] = b"vulkan 0x10de * 470-470.57 https://e/1 hangs";

    fn nvidia(software: bool) -> Adapter {
        Adapter {
            api: Api::Vulkan,
            vendor: 0x10de,
            device: 0x2204,
            driver: Some(Version([470, 3, 0, 0])),
            software,
        }
    }

    #[test]
    fn a_listed_device_is_refused_as_gpu_refused() {
        let got = admit(&nvidia(false), Launch::HARDWARE, TABLE);
        assert!(matches!(&got, Err(Refusal::Blocked(e)) if e.line == 1));
        assert!(got.is_err_and(|r| r.is_gpu_refused()));
    }

    #[test]
    fn an_unlisted_device_is_ready_in_hardware() {
        let mut other = nvidia(false);
        other.driver = Some(Version([471, 0, 0, 0]));
        assert_eq!(
            admit(&other, Launch::HARDWARE, TABLE),
            Ok(Ready { software: false })
        );
    }

    #[test]
    fn gpu_hardware_ignores_the_table() {
        let launch = Launch {
            mode: Mode::Hardware,
            check: Check::Ignore,
        };
        assert_eq!(
            admit(&nvidia(false), launch, TABLE),
            Ok(Ready { software: false })
        );
        // Even an unreadable one.
        assert_eq!(
            admit(&nvidia(false), launch, b"\0"),
            Ok(Ready { software: false })
        );
    }

    #[test]
    fn an_unreadable_table_refuses() {
        let got = admit(&nvidia(false), Launch::HARDWARE, b"opengl");
        assert!(matches!(&got, Err(Refusal::Unreadable(_))));
        assert!(got.is_err_and(|r| r.is_gpu_refused()));
    }

    #[test]
    fn a_software_adapter_is_never_checked() {
        assert_eq!(
            admit(&nvidia(true), Launch::HARDWARE, b"\0"),
            Ok(Ready { software: true })
        );
        assert_eq!(
            admit(&nvidia(true), Launch::SOFTWARE, TABLE),
            Ok(Ready { software: true })
        );
    }

    #[test]
    fn software_on_a_hardware_adapter_is_a_wrong_start() {
        let got = admit(&nvidia(false), Launch::SOFTWARE, b"");
        assert_eq!(got, Err(Refusal::NotSoftware));
        assert!(got.is_err_and(|r| !r.is_gpu_refused()));
    }

    #[test]
    fn metal_matches_only_wildcards() {
        let metal = Adapter {
            api: Api::Metal,
            vendor: APPLE,
            device: 0,
            driver: None,
            software: false,
        };
        assert_eq!(
            admit(
                &metal,
                Launch::HARDWARE,
                b"metal 0x106b * 1-99 https://e/1 r"
            ),
            Ok(Ready { software: false })
        );
        assert!(matches!(
            admit(&metal, Launch::HARDWARE, b"metal 0x106b * * https://e/1 r"),
            Err(Refusal::Blocked(_))
        ));
    }
}

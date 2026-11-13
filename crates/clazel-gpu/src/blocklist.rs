//! The driver blocklist (phase-5.md item 5.17c): which GPU drivers the GPU process
//! refuses, and the parser of the table that lists them.
//!
//! The table is `data/blocklist`, embedded at build time ([`SHIPPED`]). The GPU
//! process describes its adapter ([`Adapter`], from the backend) and checks it
//! against the table **before it reads any list** (`crate::start`), so no page has
//! touched the process yet and its answer can be believed.
//!
//! # The format
//!
//! ASCII text, lines ended by LF. Every byte is printable ASCII (0x20 to 0x7E) or
//! LF; a tab, a CR or any other byte is an error. A line is blank (empty or only
//! spaces), a comment (its first byte that is not a space is `#`), or an entry of
//! six fields separated by runs of spaces, leading and trailing spaces ignored:
//!
//! ```text
//! <api> <vendor> <device> <drivers> <evidence> <reason>
//! ```
//!
//! - `api`: `vulkan`, `d3d12` or `metal` ([`Api`]).
//! - `vendor`: `0x` and 1 to 8 hex digits, either case: the PCI vendor id (Vulkan's
//!   `VkPhysicalDeviceProperties::vendorID`, DXGI's `VendorId`).
//! - `device`: the same, or `*` for every device of the vendor.
//! - `drivers`: `*`, or `first-last`, or one version meaning `v-v`. A version is 1 to
//!   4 parts of 1 to 5 decimal digits, each at most 65,535, separated by `.`. Parts a
//!   version leaves out are 0 in `first` and 65,535 in `last`, so a shorter `last`
//!   covers every version it is a prefix of. `first` must not be after `last`.
//! - `evidence`: `https://` and at least one more byte.
//! - `reason`: the rest of the line, at least one byte that is not a space.
//!
//! # Modelling choices
//!
//! - **Our own format and parser** (CLAUDE.md rule 8). The table is ours and shipped,
//!   not page input, but it is still parsed by code that never panics, refuses
//!   anything outside the format with the line number, and bounds its work: at most
//!   [`MAX_BYTES`] bytes, [`MAX_LINE`] bytes a line, [`MAX_ENTRIES`] entries.
//! - **An unreadable table refuses the device** (fails closed): it cannot say the
//!   device is fine. A unit test parses [`SHIPPED`], so this is never reached by a
//!   shipped build.
//! - **Versions are four 16-bit parts**, compared in order ([`Version`]). That is
//!   Direct3D's driver version (`CheckInterfaceSupport`'s four 16-bit words) exactly;
//!   Vulkan's 32-bit `driverVersion` is encoded per vendor, and its backend will
//!   decode it into parts (NVIDIA's 10.8.8.6 bits, Intel's 18.14 on Windows, the
//!   `VK_MAKE_API_VERSION` layout otherwise) when it is built.
//! - **An unknown driver version** ([`Adapter::driver`] `None`) matches only `*`. An
//!   entry with a range is for versions someone measured; refusing a device whose
//!   version cannot be read would block it on a guess.
//! - **Software adapters are never checked** (lavapipe, WARP, the fake backend). The
//!   software driver is the fallback itself and the one CI tests; refusing it would
//!   leave nothing to draw with.
//! - **Metal has no device id or driver version today.** On Apple silicon there is no
//!   PCI device id, and the `clazel-sys` wrappers read neither the device's name nor
//!   the OS version without new foreign calls, which this item does not add. A Metal
//!   adapter is vendor `0x106b` (Apple), device 0, driver unknown, so a Metal entry
//!   can only use `*` for both. With no fallback on macOS, a refused Metal device
//!   shows the notice instead of pages.
//! - **Duplicate or overlapping entries are allowed**: the first match is reported.

use std::fmt;

/// The table as shipped, embedded at build time.
pub const SHIPPED: &str = include_str!("../data/blocklist");

/// The longest table read, in bytes.
pub const MAX_BYTES: usize = 65_536;

/// The longest line read, in bytes, LF excluded.
pub const MAX_LINE: usize = 1024;

/// The most entries a table holds.
pub const MAX_ENTRIES: usize = 1024;

/// Apple's PCI vendor id, which a Metal adapter reports.
pub const APPLE: u32 = 0x106b;

/// The drawing API an adapter is reached through.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Api {
    /// Vulkan (Linux).
    Vulkan,
    /// Direct3D 12 (Windows).
    D3d12,
    /// Metal (macOS).
    Metal,
}

/// A driver version: four parts, compared in order (the derived order is the
/// lexicographic one).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Version(pub [u16; 4]);

/// The driver versions an entry covers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Drivers {
    /// Every version, and an unknown one.
    Any,
    /// `first` to `last`, both included, with `first <= last`. An unknown version is
    /// not in it.
    Range {
        /// The first version covered.
        first: Version,
        /// The last version covered.
        last: Version,
    },
}

/// One entry of the table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// The line it is on, from 1, for the refusal's log line.
    pub line: u32,
    /// The API.
    pub api: Api,
    /// The PCI vendor id.
    pub vendor: u32,
    /// The PCI device id, or `None` for every device of the vendor.
    pub device: Option<u32>,
    /// The driver versions.
    pub drivers: Drivers,
    /// The link to the evidence, starting `https://`.
    pub evidence: String,
    /// What goes wrong.
    pub reason: String,
}

/// What the GPU process knows of its adapter, read from the backend before any
/// list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Adapter {
    /// The API.
    pub api: Api,
    /// The PCI vendor id ([`APPLE`] on Metal).
    pub vendor: u32,
    /// The PCI device id (0 on Metal, which has none).
    pub device: u32,
    /// The driver version, if the backend can read one.
    pub driver: Option<Version>,
    /// A software driver (lavapipe, WARP, the fake backend): never checked.
    pub software: bool,
}

/// A parsed table. Invariant: at most [`MAX_ENTRIES`] entries, each meeting
/// [`Entry::well_formed`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Blocklist {
    entries: Vec<Entry>,
}

/// What is wrong with a table, and on which line (from 1; 0 for the whole table).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParseError {
    /// The line.
    pub line: u32,
    /// What is wrong.
    pub what: Problem,
}

/// The ways a table can be wrong.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Problem {
    /// More than [`MAX_BYTES`] bytes.
    TooLong,
    /// A line of more than [`MAX_LINE`] bytes.
    LineTooLong,
    /// More than [`MAX_ENTRIES`] entries.
    TooManyEntries,
    /// A byte that is not printable ASCII or LF.
    Byte,
    /// Fewer than six fields.
    MissingField,
    /// The API is not `vulkan`, `d3d12` or `metal`.
    Api,
    /// The vendor is not `0x` and 1 to 8 hex digits.
    Vendor,
    /// The device is not `0x` and 1 to 8 hex digits, or `*`.
    Device,
    /// The drivers are not `*`, a version, or two versions joined by `-`.
    Drivers,
    /// The first version is after the last.
    EmptyRange,
    /// The evidence is not `https://` and at least one more byte.
    Evidence,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "blocklist line {}: {:?}", self.line, self.what)
    }
}

impl std::error::Error for ParseError {}

impl Entry {
    /// The invariant every parsed entry meets: a range is not empty, the evidence
    /// starts `https://` with more after it, and the reason has a byte that is not a
    /// space.
    pub fn well_formed(&self) -> bool {
        let range_ok = match self.drivers {
            Drivers::Any => true,
            Drivers::Range { first, last } => first <= last,
        };
        range_ok
            && self
                .evidence
                .strip_prefix("https://")
                .is_some_and(|rest| !rest.is_empty())
            && self.reason.bytes().any(|b| b != b' ')
    }
}

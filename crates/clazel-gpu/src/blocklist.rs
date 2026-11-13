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

impl Version {
    /// Item 5.17c, the blocklist's `drivers` field: a version of 1 to 4 parts of 1 to
    /// 5 decimal digits, each at most 65,535, separated by `.`; the parts left out
    /// are `fill`.
    pub fn parse(text: &[u8], fill: u16) -> Option<Version> {
        let mut parts = [fill; 4];
        let mut n = 0usize;
        for part in text.split(|&b| b == b'.') {
            if part.is_empty() || part.len() > 5 {
                return None;
            }
            let mut value: u32 = 0;
            for &b in part {
                if !b.is_ascii_digit() {
                    return None;
                }
                value = value
                    .checked_mul(10)?
                    .checked_add(u32::from(b.checked_sub(b'0')?))?;
            }
            *parts.get_mut(n)? = u16::try_from(value).ok()?;
            n = n.checked_add(1)?;
        }
        Some(Version(parts))
    }
}

/// `0x` and 1 to 8 hex digits, either case.
pub fn parse_hex(text: &[u8]) -> Option<u32> {
    let digits = text.strip_prefix(b"0x")?;
    if digits.is_empty() || digits.len() > 8 {
        return None;
    }
    let mut value: u32 = 0;
    for &b in digits {
        let d = match b {
            b'0'..=b'9' => b.checked_sub(b'0')?,
            b'a'..=b'f' => b.checked_sub(b'a')?.checked_add(10)?,
            b'A'..=b'F' => b.checked_sub(b'A')?.checked_add(10)?,
            _ => return None,
        };
        value = value.checked_mul(16)?.checked_add(u32::from(d))?;
    }
    Some(value)
}

impl Drivers {
    /// The `drivers` field: `*`, one version, or two joined by `-`.
    pub fn parse(text: &[u8]) -> Result<Drivers, Problem> {
        if text == b"*" {
            return Ok(Drivers::Any);
        }
        let (a, b) = match text.iter().position(|&c| c == b'-') {
            Some(i) => {
                let (a, rest) = text.split_at_checked(i).ok_or(Problem::Drivers)?;
                (a, rest.get(1..).ok_or(Problem::Drivers)?)
            }
            None => (text, text),
        };
        let first = Version::parse(a, 0).ok_or(Problem::Drivers)?;
        let last = Version::parse(b, u16::MAX).ok_or(Problem::Drivers)?;
        if first > last {
            return Err(Problem::EmptyRange);
        }
        Ok(Drivers::Range { first, last })
    }

    /// Whether `version` is covered: every version and an unknown one by `Any`; by a
    /// range, a known version from `first` to `last`.
    pub fn contains(&self, version: Option<Version>) -> bool {
        match *self {
            Drivers::Any => true,
            Drivers::Range { first, last } => version.is_some_and(|v| first <= v && v <= last),
        }
    }
}

impl Entry {
    /// Whether this entry refuses `adapter`: same API and vendor, the device if one
    /// is named, and the driver version in range. A software adapter is never
    /// refused.
    pub fn matches(&self, adapter: &Adapter) -> bool {
        !adapter.software
            && self.api == adapter.api
            && self.vendor == adapter.vendor
            && self.device.is_none_or(|d| d == adapter.device)
            && self.drivers.contains(adapter.driver)
    }
}

/// The first field of `text` after any spaces, and what follows it.
fn field(text: &[u8]) -> (&[u8], &[u8]) {
    let start = text.iter().position(|&b| b != b' ').unwrap_or(text.len());
    let rest = text.get(start..).unwrap_or_default();
    let end = rest.iter().position(|&b| b == b' ').unwrap_or(rest.len());
    rest.split_at_checked(end).unwrap_or((rest, &[]))
}

fn text_of(bytes: &[u8]) -> Result<String, Problem> {
    String::from_utf8(bytes.to_vec()).map_err(|_| Problem::Byte)
}

/// One line, its bytes already checked to be printable ASCII: `None` for a blank
/// line or a comment.
fn parse_line(line: &[u8], number: u32) -> Result<Option<Entry>, Problem> {
    let (api, rest) = field(line);
    if api.is_empty() || api.first() == Some(&b'#') {
        return Ok(None);
    }
    let api = match api {
        b"vulkan" => Api::Vulkan,
        b"d3d12" => Api::D3d12,
        b"metal" => Api::Metal,
        _ => return Err(Problem::Api),
    };
    let (vendor, rest) = field(rest);
    let (device, rest) = field(rest);
    let (drivers, rest) = field(rest);
    let (evidence, rest) = field(rest);
    let reason = rest.trim_ascii();
    if [vendor, device, drivers, evidence, reason]
        .iter()
        .any(|f| f.is_empty())
    {
        return Err(Problem::MissingField);
    }
    let vendor = parse_hex(vendor).ok_or(Problem::Vendor)?;
    let device = if device == b"*" {
        None
    } else {
        Some(parse_hex(device).ok_or(Problem::Device)?)
    };
    let drivers = Drivers::parse(drivers)?;
    if evidence
        .strip_prefix(b"https://")
        .is_none_or(<[u8]>::is_empty)
    {
        return Err(Problem::Evidence);
    }
    Ok(Some(Entry {
        line: number,
        api,
        vendor,
        device,
        drivers,
        evidence: text_of(evidence)?,
        reason: text_of(reason)?,
    }))
}

impl Blocklist {
    /// Item 5.17c: parse a table in the format above, or say on which line it is
    /// wrong. Never panics; the work is bounded by [`MAX_BYTES`].
    pub fn parse(text: &[u8]) -> Result<Blocklist, ParseError> {
        if text.len() > MAX_BYTES {
            return Err(ParseError {
                line: 0,
                what: Problem::TooLong,
            });
        }
        let mut entries = Vec::new();
        let mut number: u32 = 0;
        for line in text.split(|&b| b == b'\n') {
            // At most 65,537 lines, so this cannot overflow.
            number = number.saturating_add(1);
            let fail = |what| ParseError { line: number, what };
            if line.len() > MAX_LINE {
                return Err(fail(Problem::LineTooLong));
            }
            if !line.iter().all(|&b| (0x20..=0x7e).contains(&b)) {
                return Err(fail(Problem::Byte));
            }
            if let Some(entry) = parse_line(line, number).map_err(fail)? {
                if entries.len() >= MAX_ENTRIES {
                    return Err(fail(Problem::TooManyEntries));
                }
                entries.push(entry);
            }
        }
        Ok(Blocklist { entries })
    }

    /// The shipped table, [`SHIPPED`].
    pub fn shipped() -> Result<Blocklist, ParseError> {
        Blocklist::parse(SHIPPED.as_bytes())
    }

    /// The entries, in the table's order.
    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }

    /// The first entry that refuses `adapter`, if any.
    pub fn check(&self, adapter: &Adapter) -> Option<&Entry> {
        self.entries.iter().find(|e| e.matches(adapter))
    }
}

#[cfg(test)]
mod tests {
    use super::{
        APPLE, Adapter, Api, Blocklist, Drivers, MAX_BYTES, MAX_ENTRIES, MAX_LINE, ParseError,
        Problem, Version, parse_hex,
    };

    const GOOD: &str =
        "vulkan 0x10de 0x2204 470-470.57 https://example.org/1 hangs on the first frame";

    fn nvidia(driver: Option<[u16; 4]>) -> Adapter {
        Adapter {
            api: Api::Vulkan,
            vendor: 0x10de,
            device: 0x2204,
            driver: driver.map(Version),
            software: false,
        }
    }

    fn problem(text: &str) -> Option<ParseError> {
        Blocklist::parse(text.as_bytes()).err()
    }

    #[test]
    fn the_shipped_table_parses_and_is_empty() -> Result<(), ParseError> {
        // The plan: the table starts empty, and an entry is added only when a real
        // failure is recorded.
        assert_eq!(Blocklist::shipped()?.entries(), &[]);
        Ok(())
    }

    #[test]
    fn an_entry_has_six_fields() -> Result<(), ParseError> {
        let list = Blocklist::parse(format!("# a comment\n\n   \n  {GOOD}  \n").as_bytes())?;
        let [e] = list.entries() else {
            return Err(ParseError {
                line: 0,
                what: Problem::MissingField,
            });
        };
        assert_eq!(e.line, 4);
        assert_eq!(e.api, Api::Vulkan);
        assert_eq!(e.vendor, 0x10de);
        assert_eq!(e.device, Some(0x2204));
        assert_eq!(
            e.drivers,
            Drivers::Range {
                first: Version([470, 0, 0, 0]),
                last: Version([470, 57, u16::MAX, u16::MAX]),
            }
        );
        assert_eq!(e.evidence, "https://example.org/1");
        assert_eq!(e.reason, "hangs on the first frame");
        assert!(e.well_formed());
        Ok(())
    }

    #[test]
    fn apis_wildcards_and_single_versions() -> Result<(), ParseError> {
        let list = Blocklist::parse(
            b"d3d12 0x8086 * 31.0.101.4502 https://e/x a\nmetal 0x106B * * https://e/y b",
        )?;
        let [d3d, metal] = list.entries() else {
            return Err(ParseError {
                line: 0,
                what: Problem::MissingField,
            });
        };
        assert_eq!((d3d.api, d3d.device), (Api::D3d12, None));
        assert_eq!(
            d3d.drivers,
            Drivers::Range {
                first: Version([31, 0, 101, 4502]),
                last: Version([31, 0, 101, 4502]),
            }
        );
        assert_eq!(
            (metal.api, metal.vendor, metal.drivers),
            (Api::Metal, APPLE, Drivers::Any)
        );
        Ok(())
    }

    #[test]
    fn hostile_text_is_refused_with_its_line() {
        let cases: &[(&str, u32, Problem)] = &[
            ("vulkan\t0x1 * * https://e r", 1, Problem::Byte),
            ("# fine\r\nvulkan 0x1 * * https://e r", 1, Problem::Byte),
            ("# caf\u{e9}", 1, Problem::Byte),
            ("\n\0", 2, Problem::Byte),
            ("\u{7f}", 1, Problem::Byte),
            ("vulkan 0x1 * * https://e", 1, Problem::MissingField),
            ("vulkan 0x1 * * https://e    ", 1, Problem::MissingField),
            ("vulkan", 1, Problem::MissingField),
            ("opengl 0x1 * * https://e r", 1, Problem::Api),
            ("Vulkan 0x1 * * https://e r", 1, Problem::Api),
            ("vulkan 10de * * https://e r", 1, Problem::Vendor),
            ("vulkan 0x * * https://e r", 1, Problem::Vendor),
            ("vulkan 0x123456789 * * https://e r", 1, Problem::Vendor),
            ("vulkan 0xg * * https://e r", 1, Problem::Vendor),
            ("vulkan 0X1 * * https://e r", 1, Problem::Vendor),
            ("vulkan * * * https://e r", 1, Problem::Vendor),
            ("vulkan 0x1 ** * https://e r", 1, Problem::Device),
            ("vulkan 0x1 -1 * https://e r", 1, Problem::Device),
            ("vulkan 0x1 * 1.2.3.4.5 https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * 65536 https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * 1..2 https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * 1. https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * - https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * 1- https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * 1-2-3 https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * 000001 https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * +1 https://e r", 1, Problem::Drivers),
            ("vulkan 0x1 * 2-1 https://e r", 1, Problem::EmptyRange),
            ("vulkan 0x1 * 1.1-1.0 https://e r", 1, Problem::EmptyRange),
            // A shorter last version covers what it is a prefix of: not empty.
            (
                "# ok\nvulkan 0x1 * 1.0.1-1 https://e r\nvulkan",
                3,
                Problem::MissingField,
            ),
            ("vulkan 0x1 * * http://e r", 1, Problem::Evidence),
            ("vulkan 0x1 * * https:// r", 1, Problem::Evidence),
            ("vulkan 0x1 * * HTTPS://e r", 1, Problem::Evidence),
        ];
        for &(text, line, what) in cases {
            assert_eq!(problem(text), Some(ParseError { line, what }), "{text:?}");
        }
    }

    #[test]
    fn limits_are_kept() {
        let long_line = format!("# {}", "x".repeat(MAX_LINE));
        assert_eq!(
            problem(&long_line),
            Some(ParseError {
                line: 1,
                what: Problem::LineTooLong
            })
        );
        let at_limit = format!("#{}", "x".repeat(MAX_LINE - 1));
        assert_eq!(problem(&at_limit), None);
        let huge = "\n".repeat(MAX_BYTES + 1);
        assert_eq!(
            problem(&huge),
            Some(ParseError {
                line: 0,
                what: Problem::TooLong
            })
        );
        let short = "vulkan 0x1 * * https://e r\n";
        let full = short.repeat(MAX_ENTRIES);
        assert_eq!(problem(&full), None);
        let over = short.repeat(MAX_ENTRIES + 1);
        assert_eq!(
            problem(&over),
            Some(ParseError {
                line: 1025,
                what: Problem::TooManyEntries
            })
        );
    }

    #[test]
    fn hex_and_versions() {
        assert_eq!(parse_hex(b"0xffffffff"), Some(u32::MAX));
        assert_eq!(parse_hex(b"0x00000000"), Some(0));
        assert_eq!(parse_hex(b"0xAbC"), Some(0xabc));
        assert_eq!(parse_hex(b"0x"), None);
        assert_eq!(Version::parse(b"1", 7), Some(Version([1, 7, 7, 7])));
        assert_eq!(
            Version::parse(b"65535.0.1.2", 7),
            Some(Version([65535, 0, 1, 2]))
        );
        assert_eq!(Version::parse(b"00001", 0), Some(Version([1, 0, 0, 0])));
        assert_eq!(Version::parse(b"", 0), None);
        assert_eq!(Version::parse(b"1.", 0), None);
        assert_eq!(Version::parse(b".1", 0), None);
        assert!(Version([1, 2, 0, 0]) < Version([1, 10, 0, 0]));
    }

    #[test]
    fn matching() -> Result<(), ParseError> {
        let list = Blocklist::parse(GOOD.as_bytes())?;
        // In range, at both ends, and either side of them.
        assert!(list.check(&nvidia(Some([470, 0, 0, 0]))).is_some());
        assert!(list.check(&nvidia(Some([470, 57, 2, 0]))).is_some());
        assert!(list.check(&nvidia(Some([470, 57, 65535, 65535]))).is_some());
        assert!(
            list.check(&nvidia(Some([469, 65535, 65535, 65535])))
                .is_none()
        );
        assert!(list.check(&nvidia(Some([470, 58, 0, 0]))).is_none());
        // An unknown version matches only `*`.
        assert!(list.check(&nvidia(None)).is_none());
        // Another device, vendor or API.
        let mut other = nvidia(Some([470, 1, 0, 0]));
        other.device = 0x2205;
        assert!(list.check(&other).is_none());
        let mut other = nvidia(Some([470, 1, 0, 0]));
        other.vendor = 0x10df;
        assert!(list.check(&other).is_none());
        let mut other = nvidia(Some([470, 1, 0, 0]));
        other.api = Api::D3d12;
        assert!(list.check(&other).is_none());
        // A software adapter is never refused.
        let mut soft = nvidia(Some([470, 1, 0, 0]));
        soft.software = true;
        assert!(list.check(&soft).is_none());
        // Wildcards, and the first match is reported.
        let list = Blocklist::parse(
            b"vulkan 0x10de * * https://e/a first\nvulkan 0x10de 0x2204 * https://e/b second",
        )?;
        assert_eq!(list.check(&nvidia(None)).map(|e| e.line), Some(1));
        Ok(())
    }

    /// Any bytes: an answer, never a panic. A fixed pseudo-random sequence, and
    /// every one-byte change of a good line.
    #[test]
    fn arbitrary_bytes_never_panic() {
        let mut seed: u64 = 0x5eed;
        let rounds = if cfg!(miri) { 40 } else { 4000 };
        for _ in 0..rounds {
            let mut bytes = Vec::new();
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let len = usize::try_from(seed >> 58).unwrap_or(0);
            for _ in 0..len {
                seed = seed
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                // Mostly the format's own bytes, so lines get past the first field.
                let alphabet = b"vulkan 0x1fd*.-https://e r\n#";
                let pick = usize::try_from(seed >> 59).unwrap_or(0);
                bytes.push(alphabet.get(pick).copied().unwrap_or(seed.to_le_bytes()[7]));
            }
            if let Ok(list) = Blocklist::parse(&bytes) {
                assert!(list.entries().iter().all(super::Entry::well_formed));
            }
        }
        let good = GOOD.as_bytes();
        let step = if cfg!(miri) { 9 } else { 1 };
        for i in (0..good.len()).step_by(step) {
            for b in [0u8, b' ', b'-', b'.', b'*', b'9', 0xff] {
                let mut bytes = good.to_vec();
                if let Some(slot) = bytes.get_mut(i) {
                    *slot = b;
                }
                if let Ok(list) = Blocklist::parse(&bytes) {
                    assert!(list.entries().iter().all(super::Entry::well_formed));
                }
            }
        }
    }
}

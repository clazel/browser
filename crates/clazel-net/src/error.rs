//! The errors of the shell.

use std::fmt;
use std::io;

/// Where a timeout fired.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    /// Connecting a TCP socket.
    Connect,
    /// Waiting for bytes from a peer.
    Read,
    /// Sending bytes to a peer.
    Write,
    /// Waiting for a nameserver.
    Resolve,
}

/// Why a host name was not resolved.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolveError {
    /// The host is not a name the proven query encoder accepts.
    InvalidName,
    /// `resolv.conf` could not be read.
    ResolvConf(io::ErrorKind),
    /// No `nameserver` line, or none usable.
    NoNameservers,
    /// `/dev/urandom` could not be read for the query ID.
    Random(io::ErrorKind),
    /// No nameserver gave an acceptable reply.
    NoAnswer,
    /// The name exists but has neither an A nor an AAAA record.
    NoAddresses,
    /// A CNAME target that cannot be asked about again.
    BadAlias,
    /// More CNAME hops than the shell follows.
    TooManyAliases,
}

/// An error from the network shell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetError {
    /// The host name was not resolved.
    Resolve(ResolveError),
    /// No address could be connected to; the last error seen. An empty
    /// address list is `ErrorKind::InvalidInput`.
    Connect(io::ErrorKind),
    /// A socket failed after connecting.
    Io(io::ErrorKind),
    /// A timeout fired.
    Timeout(Stage),
}

impl fmt::Display for NetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NetError::Resolve(e) => write!(f, "resolve: {e:?}"),
            NetError::Connect(k) => write!(f, "connect: {k}"),
            NetError::Io(k) => write!(f, "i/o: {k}"),
            NetError::Timeout(s) => write!(f, "timeout: {s:?}"),
        }
    }
}

impl std::error::Error for NetError {}

/// The error for an I/O failure at `stage`: timeouts are their own variant.
pub(crate) fn from_io(e: &io::Error, stage: Stage) -> NetError {
    match e.kind() {
        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut => NetError::Timeout(stage),
        k => NetError::Io(k),
    }
}

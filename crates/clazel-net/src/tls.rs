//! TLS 1.3 over a TCP [`Connection`]: the socket loop around
//! `clazel_crypto::client::Client` (phase-3.md items 3.5f and 3.8).
//!
//! The shell makes no protocol decision. It writes every octet the driver
//! asks it to send, hands the driver every octet read and the end of the
//! stream, keeps the plaintext the driver delivers until the caller reads
//! it, and turns the driver's final state into a [`NetError`]. The
//! handshake, the alerts and when the connection is over are the driver's.

use crate::conn::{Connection, READ_BUF, Timeouts};
use crate::error::{NetError, Stage};
use clazel_crypto::client::{Client, Failure, Origin, Output, State};
use clazel_crypto::join::exec::ChainVerifier;
use clazel_tls::host::exec::Host;
use std::io;
use std::net::IpAddr;

/// RFC 8446 §6.1 `close_notify`, reported as the server's when it ends the
/// handshake.
const CLOSE_NOTIFY: u8 = 0;

/// One TLS connection, for a caller that decides itself when to send and
/// read, like [`Connection`]. Dropping it closes the socket without a
/// close_notify; [`TlsConnection::close`] sends one first.
pub struct TlsConnection<'r> {
    conn: Connection,
    client: Client<'r>,
    /// Plaintext the driver delivered that the caller has not read.
    plain: Vec<u8>,
    buf: Vec<u8>,
}

impl<'r> TlsConnection<'r> {
    /// Connect to `addrs` in order (as [`crate::connect`]) and run the TLS
    /// handshake for `host`, validating the server's certificates at `now`
    /// (seconds since the Unix epoch) against `verifier`'s trust anchors.
    /// The driver's secret random octets come from the OS
    /// (`clazel_sys::fill_random`); if it fails, the error is
    /// [`NetError::Random`] and nothing is connected or sent. Each read and
    /// write of the handshake waits at most `timeouts.idle`; a timeout is
    /// [`NetError::Timeout`] at [`Stage::Handshake`]. A handshake that the
    /// driver ends is [`NetError::Tls`], including a close_notify from the
    /// server (alert 0, from the server).
    pub fn open(
        addrs: &[IpAddr],
        port: u16,
        timeouts: Timeouts,
        host: Host,
        now: u64,
        verifier: ChainVerifier<'r>,
    ) -> Result<Self, NetError> {
        let mut os = |buf: &mut [u8]| clazel_sys::fill_random(buf).map_err(NetError::Random);
        Self::start(addrs, port, timeouts, host, now, verifier, &mut os)
    }

    /// [`Self::open`] with the caller's source of random octets instead of
    /// the OS's, for tests that need a reproducible handshake. `random`
    /// must fill its argument with fresh, secret, uniformly random octets
    /// (see `clazel_crypto::client::Client::connect`): a fixed seed makes
    /// every key of the connection predictable.
    pub fn open_with_random(
        addrs: &[IpAddr],
        port: u16,
        timeouts: Timeouts,
        host: Host,
        now: u64,
        verifier: ChainVerifier<'r>,
        random: &mut dyn FnMut(&mut [u8]),
    ) -> Result<Self, NetError> {
        let mut caller = |buf: &mut [u8]| {
            random(buf);
            Ok(())
        };
        Self::start(addrs, port, timeouts, host, now, verifier, &mut caller)
    }

    /// Build the driver, then connect and run the handshake. `random` may
    /// fail. The driver draws every random octet inside `Client::connect`,
    /// which sends nothing itself, so after a failed draw the remaining
    /// draws are skipped, the ClientHello built from them is dropped unsent,
    /// and no socket is opened.
    fn start(
        addrs: &[IpAddr],
        port: u16,
        timeouts: Timeouts,
        host: Host,
        now: u64,
        verifier: ChainVerifier<'r>,
        random: &mut dyn FnMut(&mut [u8]) -> Result<(), NetError>,
    ) -> Result<Self, NetError> {
        let mut drawn = Ok(());
        let (client, first) = Client::connect(host, now, verifier, &mut |buf: &mut [u8]| {
            if drawn.is_ok() {
                drawn = random(buf);
            }
        });
        drawn?;
        let conn = Connection::open(addrs, port, timeouts)?;
        let mut tls = TlsConnection {
            conn,
            client,
            plain: Vec::new(),
            buf: vec![0u8; READ_BUF],
        };
        tls.carry(first).map_err(handshake_stage)?;
        while tls.client.state() == State::Handshaking {
            tls.pull().map_err(handshake_stage)?;
        }
        match tls.client.state() {
            State::Failed(failure) => Err(NetError::Tls(failure)),
            State::Closed => Err(NetError::Tls(Failure {
                alert: CLOSE_NOTIFY,
                origin: Origin::Peer,
            })),
            State::Handshaking | State::Open | State::Closing => Ok(tls),
        }
    }

    /// Send `bytes` as application data, in full. After [`Self::close`]
    /// or the end of the connection it is `Io(NotConnected)`, or the
    /// connection's [`NetError::Tls`].
    pub fn send(&mut self, bytes: &[u8]) -> Result<(), NetError> {
        match self.client.send(bytes) {
            Ok(out) => self.carry(out),
            Err(_) => match self.client.state() {
                State::Failed(failure) => Err(NetError::Tls(failure)),
                _ => Err(NetError::Io(io::ErrorKind::NotConnected)),
            },
        }
    }

    /// Read the next plaintext into `buf`: `Some(n)` octets (never 0 for a
    /// nonempty `buf`), or `None` once both close_notify alerts have been
    /// seen. Plaintext delivered before a failure is read first; the end of
    /// the stream without the server's close_notify is [`NetError::Tls`]
    /// with [`Origin::Truncated`].
    pub fn read(&mut self, buf: &mut [u8]) -> Result<Option<usize>, NetError> {
        loop {
            if !self.plain.is_empty() || buf.is_empty() {
                let n = buf.len().min(self.plain.len());
                let rest = self.plain.split_off(n);
                if let Some(dst) = buf.get_mut(..n) {
                    dst.copy_from_slice(&self.plain);
                }
                self.plain = rest;
                return Ok(Some(n));
            }
            match self.client.state() {
                State::Closed => return Ok(None),
                State::Failed(failure) => return Err(NetError::Tls(failure)),
                State::Handshaking | State::Open | State::Closing => self.pull()?,
            }
        }
    }

    /// Send our close_notify (if the connection is still open) and close
    /// the socket, without waiting for the server's (RFC 8446 §6.1 lets the
    /// closing side stop reading).
    pub fn close(mut self) -> Result<(), NetError> {
        let out = self.client.close();
        if !out.send.is_empty() {
            self.conn.send(&out.send)?;
        }
        Ok(())
    }

    /// Read once from the socket and give the driver what arrived.
    fn pull(&mut self) -> Result<(), NetError> {
        let out = match self.conn.read(&mut self.buf)? {
            Some(n) => self.client.receive(self.buf.get(..n).unwrap_or_default()),
            None => self.client.receive_eof(),
        };
        self.carry(out)
    }

    /// Carry out one driver output: write what it sends, keep what it
    /// delivers. A write that fails while the driver is failing anyway
    /// (its alert) is not reported over the failure.
    fn carry(&mut self, out: Output) -> Result<(), NetError> {
        self.plain.extend_from_slice(&out.deliver);
        if !out.send.is_empty() {
            let sent = self.conn.send(&out.send);
            if !matches!(out.state, State::Failed(_)) {
                sent?;
            }
        }
        Ok(())
    }
}

/// A socket timeout while the handshake runs is a handshake timeout.
fn handshake_stage(e: NetError) -> NetError {
    match e {
        NetError::Timeout(Stage::Read | Stage::Write) => NetError::Timeout(Stage::Handshake),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clazel_crypto::join::exec::Root;
    use clazel_sys::RandomError;
    use std::net::{Ipv4Addr, TcpListener};
    use std::time::Duration;

    /// A random source that fails never reaches the network: no socket is
    /// opened, so no ClientHello built from unfilled octets is sent.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn a_failed_draw_opens_no_socket() -> Result<(), Box<dyn std::error::Error>> {
        let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0))?;
        listener.set_nonblocking(true)?;
        let port = listener.local_addr()?.port();
        let mut calls = 0u32;
        let mut failing = |_: &mut [u8]| {
            calls = calls.saturating_add(1);
            Err(NetError::Random(RandomError::Unsupported))
        };
        let result = TlsConnection::start(
            &[IpAddr::V4(Ipv4Addr::LOCALHOST)],
            port,
            Timeouts {
                connect: Duration::from_secs(2),
                idle: Duration::from_secs(2),
            },
            Host::Dns(b"test.example".to_vec()),
            0,
            ChainVerifier::new(&[] as &[Root<'_>]),
            &mut failing,
        );
        assert!(matches!(
            result,
            Err(NetError::Random(RandomError::Unsupported))
        ));
        // The first failure skips the remaining draws.
        assert_eq!(calls, 1);
        let accepted = listener.accept();
        assert!(
            matches!(&accepted, Err(e) if e.kind() == io::ErrorKind::WouldBlock),
            "{accepted:?}"
        );
        Ok(())
    }
}

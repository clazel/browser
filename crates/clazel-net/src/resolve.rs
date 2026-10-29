//! The stub resolver: carries a query to a nameserver and the reply back.
//!
//! Every decision about the bytes is a proven function of `clazel-dns`:
//! `resolv::parse::nameservers` reads `resolv.conf`, `encode::encode_query`
//! builds the query, `decode::decode_udp` and `decode_message` read the reply,
//! `answer::answer_addresses` accepts it (ID, question, QR, RCODE) and
//! `encode::tcp_frame` / `tcp_message_len` do the TCP framing. This module
//! only owns sockets, clocks, the random ID and the retry order.

use crate::error::{NetError, ResolveError, Stage, from_io};
use clazel_dns::answer::answer_addresses;
use clazel_dns::decode::{decode_message, decode_udp};
use clazel_dns::encode::{
    dotted_to_wire, encode_query, tcp_frame, tcp_message_len, wire_to_dotted,
};
use clazel_dns::resolv::parse::nameservers;
use clazel_dns::spec::Addr;
use clazel_dns::types::{Msg, Resolved};
use std::io::{self, Read, Write};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, TcpStream, UdpSocket};
use std::path::Path;
use std::time::{Duration, Instant};

const RESOLV_CONF: &str = "/etc/resolv.conf";
const QTYPE_A: u16 = 1;
const QTYPE_AAAA: u16 = 28;
/// CNAME hops followed for one lookup (the name is asked about again each time).
const MAX_ALIAS_HOPS: usize = 8;
/// Largest UDP datagram accepted.
const UDP_BUF: usize = 4096;
/// Largest TCP reply: a 2-octet length and at most 65535 octets (RFC 1035 §4.2.2).
const MAX_TCP_READ: usize = 65_537;

/// What the resolver needs to run: tests point it at a fake server.
pub(crate) struct Config {
    /// Nameservers, tried in order.
    pub nameservers: Vec<SocketAddr>,
    /// How long to wait for one reply (UDP) or one TCP exchange.
    pub timeout: Duration,
    /// Extra UDP attempts per nameserver.
    pub retries: usize,
}

/// Resolve `host` (a dotted name or an IP literal, `[::1]` allowed) to
/// addresses, in the order to try them. IP literals and `localhost` need no
/// query; anything else goes to the nameservers of `/etc/resolv.conf`, port
/// 53, A first and AAAA only if A gave no address. Two attempts per
/// nameserver, 2 s each.
pub fn resolve(host: &[u8]) -> Result<Vec<IpAddr>, NetError> {
    if let Some(addrs) = without_query(host) {
        return Ok(addrs);
    }
    let cfg = Config {
        nameservers: nameservers_from_file(Path::new(RESOLV_CONF), 53)?,
        timeout: Duration::from_secs(2),
        retries: 1,
    };
    resolve_with(host, &cfg)
}

/// The addresses of an IP literal or `localhost`, which need no query.
fn without_query(host: &[u8]) -> Option<Vec<IpAddr>> {
    let text = std::str::from_utf8(host).ok()?;
    if text.eq_ignore_ascii_case("localhost") {
        return Some(vec![
            IpAddr::V4(Ipv4Addr::LOCALHOST),
            IpAddr::V6(Ipv6Addr::LOCALHOST),
        ]);
    }
    let bare = text
        .strip_prefix('[')
        .and_then(|t| t.strip_suffix(']'))
        .unwrap_or(text);
    bare.parse::<IpAddr>().ok().map(|ip| vec![ip])
}

/// The nameserver lines of the resolv.conf at `path`, at `port`.
pub(crate) fn nameservers_from_file(path: &Path, port: u16) -> Result<Vec<SocketAddr>, NetError> {
    let bytes =
        std::fs::read(path).map_err(|e| NetError::Resolve(ResolveError::ResolvConf(e.kind())))?;
    let list: Vec<SocketAddr> = nameservers(&bytes)
        .into_iter()
        .map(|a| SocketAddr::new(to_ip(a), port))
        .collect();
    if list.is_empty() {
        Err(NetError::Resolve(ResolveError::NoNameservers))
    } else {
        Ok(list)
    }
}

fn to_ip(a: Addr) -> IpAddr {
    match a {
        Addr::V4(n) => IpAddr::V4(Ipv4Addr::from(n)),
        Addr::V6(n) => IpAddr::V6(Ipv6Addr::from(n)),
    }
}

/// Resolve with the given nameservers; see [`resolve`].
pub(crate) fn resolve_with(host: &[u8], cfg: &Config) -> Result<Vec<IpAddr>, NetError> {
    if let Some(addrs) = without_query(host) {
        return Ok(addrs);
    }
    // Reject names the proven encoder does not accept before any I/O.
    if dotted_to_wire(host).is_none() {
        return Err(NetError::Resolve(ResolveError::InvalidName));
    }
    let a = lookup(host, QTYPE_A, cfg)?;
    if !a.is_empty() {
        return Ok(a);
    }
    let aaaa = lookup(host, QTYPE_AAAA, cfg)?;
    if aaaa.is_empty() {
        Err(NetError::Resolve(ResolveError::NoAddresses))
    } else {
        Ok(aaaa)
    }
}

/// One type's lookup, following CNAMEs the proven `answer_addresses` reports
/// as `redirect` (RFC 1034 §5.3.3 step 3a) for a bounded number of hops.
fn lookup(host: &[u8], qtype: u16, cfg: &Config) -> Result<Vec<IpAddr>, NetError> {
    let mut name = host.to_vec();
    for _ in 0..=MAX_ALIAS_HOPS {
        let resolved = ask(&name, qtype, cfg)?;
        match resolved.redirect {
            None => return Ok(resolved.addresses.into_iter().map(to_ip).collect()),
            Some(wire) => {
                name = wire_to_dotted(&wire).ok_or(NetError::Resolve(ResolveError::BadAlias))?;
            }
        }
    }
    Err(NetError::Resolve(ResolveError::TooManyAliases))
}

/// Ask the nameservers in order about `name`; the first acceptable reply wins.
fn ask(name: &[u8], qtype: u16, cfg: &Config) -> Result<Resolved, NetError> {
    let mut last = NetError::Resolve(ResolveError::NoAnswer);
    for ns in &cfg.nameservers {
        for _ in 0..=cfg.retries {
            let id = random_id()?;
            let query = encode_query(id, name, qtype)
                .ok_or(NetError::Resolve(ResolveError::InvalidName))?;
            match ask_udp(*ns, id, &query, name, qtype, cfg.timeout) {
                Ok(Reply::Answer(r)) => return Ok(r),
                Ok(Reply::Truncated) => {
                    // RFC 7766 §8: repeat the query over TCP, once, to this server.
                    match ask_tcp(*ns, id, &query, name, qtype, cfg.timeout) {
                        Ok(r) => return Ok(r),
                        Err(e) => last = e,
                    }
                    break;
                }
                Err(e) => last = e,
            }
        }
    }
    Err(match last {
        NetError::Timeout(_) => NetError::Timeout(Stage::Resolve),
        other => other,
    })
}

enum Reply {
    Answer(Resolved),
    Truncated,
}

/// One UDP exchange. Datagrams from another address, that do not decode, or
/// that `answer_addresses` rejects (wrong ID or question) are ignored until
/// the timeout.
fn ask_udp(
    ns: SocketAddr,
    id: u16,
    query: &[u8],
    name: &[u8],
    qtype: u16,
    timeout: Duration,
) -> Result<Reply, NetError> {
    let bind: SocketAddr = match ns {
        SocketAddr::V4(_) => SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0),
        SocketAddr::V6(_) => SocketAddr::new(IpAddr::V6(Ipv6Addr::UNSPECIFIED), 0),
    };
    let io_err = |e: io::Error| from_io(&e, Stage::Resolve);
    let sock = UdpSocket::bind(bind).map_err(io_err)?;
    sock.connect(ns).map_err(io_err)?;
    sock.send(query).map_err(io_err)?;
    let deadline = deadline_after(timeout);
    let mut buf = vec![0u8; UDP_BUF];
    loop {
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(NetError::Timeout(Stage::Resolve));
        }
        sock.set_read_timeout(Some(left)).map_err(io_err)?;
        let n = match sock.recv(&mut buf) {
            Ok(n) => n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            // An ICMP port-unreachable for an earlier send: this server is down.
            Err(e) if e.kind() == io::ErrorKind::ConnectionRefused => {
                return Err(NetError::Io(e.kind()));
            }
            Err(e) => return Err(from_io(&e, Stage::Resolve)),
        };
        let Some(msg) = buf.get(..n).and_then(decode_udp) else {
            continue;
        };
        if msg.header.id == id && msg.header.qr && msg.tc() {
            return Ok(Reply::Truncated);
        }
        if let Some(r) = answer_addresses(id, name, qtype, &msg) {
            return Ok(Reply::Answer(r));
        }
    }
}

/// The TCP retry (RFC 1035 §4.2.2): the framed query, then the framed reply.
fn ask_tcp(
    ns: SocketAddr,
    id: u16,
    query: &[u8],
    name: &[u8],
    qtype: u16,
    timeout: Duration,
) -> Result<Resolved, NetError> {
    let deadline = deadline_after(timeout);
    let io_err = |e: io::Error| from_io(&e, Stage::Resolve);
    let mut stream = TcpStream::connect_timeout(&ns, timeout).map_err(io_err)?;
    stream.set_write_timeout(Some(timeout)).map_err(io_err)?;
    let framed = tcp_frame(query).ok_or(NetError::Resolve(ResolveError::InvalidName))?;
    stream.write_all(&framed).map_err(io_err)?;
    let mut data: Vec<u8> = Vec::new();
    let mut buf = vec![0u8; 4096];
    let len = loop {
        if let Some(n) = tcp_message_len(&data) {
            break n;
        }
        if data.len() >= MAX_TCP_READ {
            return Err(NetError::Resolve(ResolveError::NoAnswer));
        }
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(NetError::Timeout(Stage::Resolve));
        }
        stream.set_read_timeout(Some(left)).map_err(io_err)?;
        match stream.read(&mut buf) {
            Ok(0) => return Err(NetError::Io(io::ErrorKind::UnexpectedEof)),
            Ok(n) => data.extend_from_slice(buf.get(..n).unwrap_or(&[])),
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(io_err(e)),
        }
    };
    let msg: Msg = data
        .get(2..len.saturating_add(2))
        .and_then(decode_message)
        .ok_or(NetError::Resolve(ResolveError::NoAnswer))?;
    answer_addresses(id, name, qtype, &msg).ok_or(NetError::Resolve(ResolveError::NoAnswer))
}

fn deadline_after(d: Duration) -> Instant {
    let now = Instant::now();
    now.checked_add(d).unwrap_or(now)
}

/// A random 16-bit query ID from `/dev/urandom` (RFC 5452 §9.2 wants it
/// unpredictable).
#[cfg(unix)]
fn random_id() -> Result<u16, NetError> {
    let mut b = [0u8; 2];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut b))
        .map_err(|e| NetError::Resolve(ResolveError::Random(e.kind())))?;
    Ok(u16::from_be_bytes(b))
}

/// Windows: `std` has no safe OS random source, and `BCryptGenRandom` needs
/// `unsafe`, which only `clazel-sys` may hold (CLAUDE.md rule 1). Until it has
/// that call (it needs an audit), take the ID from `std`'s per-process random
/// hasher key, which the standard library seeds from the OS. It is
/// unpredictable to an off-path attacker, but it is not a CSPRNG.
#[cfg(not(unix))]
fn random_id() -> Result<u16, NetError> {
    use std::hash::{BuildHasher, Hasher, RandomState};
    let mut h = RandomState::new().build_hasher();
    h.write_u64(0);
    let [a, b, ..] = h.finish().to_be_bytes();
    Ok(u16::from_be_bytes([a, b]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::TcpListener;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::thread::{self, JoinHandle};

    type T = Result<(), Box<dyn std::error::Error>>;

    fn cfg(ns: SocketAddr) -> Config {
        Config {
            nameservers: vec![ns],
            timeout: Duration::from_millis(150),
            retries: 1,
        }
    }

    /// A reply to `query`: its header and question, with `flags`, the ID
    /// changed by `id_xor`, and `answers` appended (`ancount` of them).
    fn reply(query: &[u8], flags: [u8; 2], id_xor: u16, ancount: u8, answers: &[u8]) -> Vec<u8> {
        let mut out = query.to_vec();
        let id = u16::from_be_bytes([
            query.first().copied().unwrap_or(0),
            query.get(1).copied().unwrap_or(0),
        ]) ^ id_xor;
        let [i0, i1] = id.to_be_bytes();
        for (k, v) in [
            (0usize, i0),
            (1, i1),
            (2, flags[0]),
            (3, flags[1]),
            (7, ancount),
        ] {
            if let Some(slot) = out.get_mut(k) {
                *slot = v;
            }
        }
        out.extend_from_slice(answers);
        out
    }

    const OK: [u8; 2] = [0x81, 0x80];
    /// An A record owned by the question's name (a pointer to offset 12).
    const A_RECORD: [u8; 16] = [0xC0, 12, 0, 1, 0, 1, 0, 0, 0, 60, 0, 4, 192, 0, 2, 7];

    /// A UDP server on 127.0.0.1 that answers `queries` datagrams with what
    /// `handler(query, index)` returns (nothing, for `None`).
    fn udp_server(
        queries: usize,
        mut handler: impl FnMut(&[u8], usize) -> Option<Vec<u8>> + Send + 'static,
    ) -> Result<(SocketAddr, JoinHandle<()>), Box<dyn std::error::Error>> {
        let sock = UdpSocket::bind("127.0.0.1:0")?;
        sock.set_read_timeout(Some(Duration::from_secs(3)))?;
        let addr = sock.local_addr()?;
        let h = thread::spawn(move || {
            let mut buf = [0u8; 600];
            for i in 0..queries {
                let Ok((n, from)) = sock.recv_from(&mut buf) else {
                    return;
                };
                if let Some(r) = buf.get(..n).and_then(|q| handler(q, i)) {
                    let _ = sock.send_to(&r, from);
                }
            }
        });
        Ok((addr, h))
    }

    #[test]
    fn literals_and_localhost_need_no_query() {
        assert_eq!(
            without_query(b"127.0.0.1"),
            Some(vec![IpAddr::V4(Ipv4Addr::LOCALHOST)])
        );
        assert_eq!(
            without_query(b"[::1]"),
            Some(vec![IpAddr::V6(Ipv6Addr::LOCALHOST)])
        );
        assert_eq!(
            without_query(b"::1"),
            Some(vec![IpAddr::V6(Ipv6Addr::LOCALHOST)])
        );
        assert_eq!(without_query(b"LocalHost").map(|v| v.len()), Some(2));
        assert_eq!(without_query(b"example.com"), None);
        assert_eq!(without_query(&[0xff, 0xfe]), None);
        // No nameserver is asked.
        let none = Config {
            nameservers: vec![],
            timeout: Duration::from_millis(10),
            retries: 0,
        };
        assert!(resolve_with(b"10.1.2.3", &none).is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore = "writes a file")]
    fn resolv_conf_nameservers_are_read_in_order() -> T {
        let path = std::env::temp_dir().join(format!("clazel-net-resolv-{}", std::process::id()));
        std::fs::write(
            &path,
            "# c\nsearch x\nnameserver 192.0.2.1\nnameserver ::1\n",
        )?;
        let got = nameservers_from_file(&path, 5353);
        std::fs::remove_file(&path)?;
        let want: Vec<SocketAddr> = vec!["192.0.2.1:5353".parse()?, "[::1]:5353".parse()?];
        assert_eq!(got, Ok(want));
        assert_eq!(
            nameservers_from_file(&path, 53),
            Err(NetError::Resolve(ResolveError::ResolvConf(
                io::ErrorKind::NotFound
            )))
        );
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn a_query_is_answered_over_udp() -> T {
        let (ns, h) = udp_server(1, |q, _| Some(reply(q, OK, 0, 1, &A_RECORD)))?;
        let got = resolve_with(b"example.test", &cfg(ns));
        assert_eq!(got, Ok(vec![IpAddr::V4(Ipv4Addr::new(192, 0, 2, 7))]));
        h.join().map_err(|_| "server panicked")?;
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn aaaa_is_asked_when_a_is_empty() -> T {
        let aaaa: Vec<u8> = {
            let mut r = vec![0xC0, 12, 0, 28, 0, 1, 0, 0, 0, 60, 0, 16];
            r.extend_from_slice(&Ipv6Addr::LOCALHOST.octets());
            r
        };
        let (ns, h) = udp_server(2, move |q, i| {
            // The first query (A) gets NODATA, the second (AAAA) an address.
            if i == 0 {
                Some(reply(q, OK, 0, 0, &[]))
            } else {
                Some(reply(q, OK, 0, 1, &aaaa))
            }
        })?;
        assert_eq!(
            resolve_with(b"example.test", &cfg(ns)),
            Ok(vec![IpAddr::V6(Ipv6Addr::LOCALHOST)])
        );
        h.join().map_err(|_| "server panicked")?;
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn a_cname_is_followed() -> T {
        // example.test CNAME real.test; then real.test A.
        let mut cname = vec![0xC0, 12, 0, 5, 0, 1, 0, 0, 0, 60, 0, 11];
        cname.extend_from_slice(b"\x04real\x04test\x00");
        let (ns, h) = udp_server(2, move |q, i| {
            if i == 0 {
                Some(reply(q, OK, 0, 1, &cname))
            } else {
                Some(reply(q, OK, 0, 1, &A_RECORD))
            }
        })?;
        assert_eq!(
            resolve_with(b"example.test", &cfg(ns)),
            Ok(vec![IpAddr::V4(Ipv4Addr::new(192, 0, 2, 7))])
        );
        h.join().map_err(|_| "server panicked")?;
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn a_cname_chain_is_bounded() -> T {
        let count = Arc::new(AtomicUsize::new(0));
        let seen = Arc::clone(&count);
        // Every reply is a CNAME to a new name (h0.test, h1.test, ...): the
        // chain never ends, so the shell must give up.
        let (ns, h) = udp_server(MAX_ALIAS_HOPS + 1, move |q, i| {
            seen.fetch_add(1, Ordering::SeqCst);
            let digit = b'0'.saturating_add(u8::try_from(i).unwrap_or(0));
            let mut cname = vec![0xC0, 12, 0, 5, 0, 1, 0, 0, 0, 60, 0, 9];
            cname.extend_from_slice(&[2, b'h', digit, 4, b't', b'e', b's', b't', 0]);
            Some(reply(q, OK, 0, 1, &cname))
        })?;
        assert_eq!(
            resolve_with(b"real.test", &cfg(ns)),
            Err(NetError::Resolve(ResolveError::TooManyAliases))
        );
        h.join().map_err(|_| "server panicked")?;
        assert_eq!(count.load(Ordering::SeqCst), MAX_ALIAS_HOPS + 1);
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn a_truncated_reply_is_retried_over_tcp() -> T {
        // The same port over UDP and TCP.
        let mut pair = None;
        for _ in 0..50 {
            let tcp = TcpListener::bind("127.0.0.1:0")?;
            let port = tcp.local_addr()?.port();
            if let Ok(udp) = UdpSocket::bind(("127.0.0.1", port)) {
                pair = Some((tcp, udp, port));
                break;
            }
        }
        let (tcp, udp, port) = pair.ok_or("no free port pair")?;
        udp.set_read_timeout(Some(Duration::from_secs(3)))?;
        let uh = thread::spawn(move || {
            let mut buf = [0u8; 600];
            if let Ok((n, from)) = udp.recv_from(&mut buf)
                && let Some(q) = buf.get(..n)
            {
                let _ = udp.send_to(&reply(q, [0x83, 0x80], 0, 0, &[]), from);
            }
        });
        let th = thread::spawn(move || -> io::Result<()> {
            let (mut s, _) = tcp.accept()?;
            s.set_read_timeout(Some(Duration::from_secs(3)))?;
            let mut hdr = [0u8; 2];
            s.read_exact(&mut hdr)?;
            let mut q = vec![0u8; usize::from(u16::from_be_bytes(hdr))];
            s.read_exact(&mut q)?;
            let r = reply(&q, OK, 0, 1, &A_RECORD);
            let [l0, l1] = u16::try_from(r.len()).unwrap_or(0).to_be_bytes();
            // Split writes: the client must wait for the whole message.
            s.write_all(&[l0])?;
            s.flush()?;
            thread::sleep(Duration::from_millis(20));
            s.write_all(&[l1])?;
            s.write_all(&r)
        });
        let ns: SocketAddr = format!("127.0.0.1:{port}").parse()?;
        let mut c = cfg(ns);
        c.timeout = Duration::from_secs(2);
        assert_eq!(
            resolve_with(b"example.test", &c),
            Ok(vec![IpAddr::V4(Ipv4Addr::new(192, 0, 2, 7))])
        );
        uh.join().map_err(|_| "udp server panicked")?;
        th.join().map_err(|_| "tcp server panicked")??;
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn a_reply_with_the_wrong_id_is_ignored() -> T {
        let (ns, h) = udp_server(2, |q, _| Some(reply(q, OK, 1, 1, &A_RECORD)))?;
        let got = resolve_with(b"example.test", &cfg(ns));
        assert_eq!(got, Err(NetError::Timeout(Stage::Resolve)));
        h.join().map_err(|_| "server panicked")?;
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn a_reply_to_another_question_is_ignored() -> T {
        let (ns, h) = udp_server(2, |q, _| {
            let mut r = reply(q, OK, 0, 1, &A_RECORD);
            // Change the first label's first letter: "example" becomes "xxample".
            if let Some(b) = r.get_mut(13) {
                *b = b'x';
            }
            Some(r)
        })?;
        assert_eq!(
            resolve_with(b"example.test", &cfg(ns)),
            Err(NetError::Timeout(Stage::Resolve))
        );
        h.join().map_err(|_| "server panicked")?;
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn the_next_nameserver_is_tried() -> T {
        let (dead, h1) = udp_server(2, |_, _| None)?;
        let (live, h2) = udp_server(1, |q, _| Some(reply(q, OK, 0, 1, &A_RECORD)))?;
        let c = Config {
            nameservers: vec![dead, live],
            timeout: Duration::from_millis(100),
            retries: 1,
        };
        assert_eq!(
            resolve_with(b"example.test", &c),
            Ok(vec![IpAddr::V4(Ipv4Addr::new(192, 0, 2, 7))])
        );
        h1.join().map_err(|_| "server panicked")?;
        h2.join().map_err(|_| "server panicked")?;
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn nxdomain_is_no_addresses_and_bad_names_fail_early() -> T {
        let (ns, h) = udp_server(2, |q, _| Some(reply(q, [0x81, 0x83], 0, 0, &[])))?;
        assert_eq!(
            resolve_with(b"nothing.test", &cfg(ns)),
            Err(NetError::Resolve(ResolveError::NoAddresses))
        );
        h.join().map_err(|_| "server panicked")?;
        assert_eq!(
            resolve_with(b"a..b", &cfg(ns)),
            Err(NetError::Resolve(ResolveError::InvalidName))
        );
        Ok(())
    }

    #[test]
    #[cfg_attr(miri, ignore = "opens sockets")]
    fn a_cname_target_with_no_dotted_form_is_a_bad_alias() -> T {
        // example.test CNAME "a.b" "test": the first label holds a dot, so
        // the target cannot be written as a name to ask about.
        let mut cname = vec![0xC0, 12, 0, 5, 0, 1, 0, 0, 0, 60, 0, 10];
        cname.extend_from_slice(b"\x03a.b\x04test\x00");
        let (ns, h) = udp_server(1, move |q, _| Some(reply(q, OK, 0, 1, &cname)))?;
        assert_eq!(
            resolve_with(b"example.test", &cfg(ns)),
            Err(NetError::Resolve(ResolveError::BadAlias))
        );
        h.join().map_err(|_| "server panicked")?;
        Ok(())
    }
}

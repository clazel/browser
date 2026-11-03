//! Executable-style specification of the DNS servers in the buffer that
//! Windows' `GetAdaptersAddresses` fills, which the network shell
//! (phase-3.md item 3.8) reads on Windows in place of `/etc/resolv.conf`.
//!
//! Sources (Microsoft Learn, and the Windows SDK 10.0.26100.0 headers they
//! document):
//!
//! - `GetAdaptersAddresses` (iphlpapi.h): on success the buffer "contains a
//!   linked list of IP_ADAPTER_ADDRESSES structures";
//!   <https://learn.microsoft.com/windows/win32/api/iphlpapi/nf-iphlpapi-getadaptersaddresses>.
//! - `IP_ADAPTER_ADDRESSES_LH` (IPTypes.h), the list's element:
//!   <https://learn.microsoft.com/windows/win32/api/iptypes/ns-iptypes-ip_adapter_addresses_lh>.
//! - `IP_ADAPTER_DNS_SERVER_ADDRESS_XP` (IPTypes.h), one DNS server:
//!   <https://learn.microsoft.com/windows/win32/api/iptypes/ns-iptypes-ip_adapter_dns_server_address_xp>.
//! - `SOCKET_ADDRESS` (ws2def.h), `SOCKADDR_IN` (ws2def.h) and
//!   `SOCKADDR_IN6` (ws2ipdef.h): the server's address, `AF_INET` = 2 and
//!   `AF_INET6` = 23.
//! - `IF_OPER_STATUS` (ifdef.h): `IfOperStatusUp` = 1.
//!
//! No standard defines this buffer: it is C structures laid out by the
//! compiler, so the offsets below are the 64-bit layout of those headers
//! (pointers and `ULONGLONG` 8 octets, `ULONG`, `DWORD`, `INT` and enums 4,
//! natural alignment). A probe of a real buffer on Windows 11 (26200) agreed
//! with every offset.
//!
//! ## The layout read
//!
//! ```text
//! IP_ADAPTER_ADDRESSES_LH            IP_ADAPTER_DNS_SERVER_ADDRESS_XP
//!   +0   Length, IfIndex               +0   Length, Reserved
//!   +8   Next                          +8   Next
//!   +48  FirstDnsServerAddress         +16  Address.lpSockaddr
//!   +104 OperStatus                    +24  Address.iSockaddrLength
//!   (108 octets read)                  (28 octets read)
//!
//! SOCKADDR_IN                        SOCKADDR_IN6
//!   +0   sin_family (2)                +0   sin6_family (23)
//!   +4   sin_addr (4 octets)           +8   sin6_addr (16 octets)
//!   (16 octets)                        (28 octets)
//! ```
//!
//! Integers in the structures are little-endian (every 64-bit Windows
//! target is); the addresses themselves are in network order.
//!
//! ## Modelling choices
//!
//! - **The buffer is octets and a base address.** The shell never follows a
//!   pointer: `clazel-sys` hands over a copy of the octets and the address
//!   the OS wrote them at. A pointer `p` names the octets at offset
//!   `p - base`, and is used only if every octet the record needs lies
//!   inside the buffer; otherwise the list it is part of ends there. The
//!   documentation does not promise that the records the list links lie in
//!   the caller's buffer; if one did not, this reads none of it.
//! - **Every list only moves forward.** A `Next` pointer is followed only to
//!   a record at a higher offset than the one it is in, and an adapter's
//!   first DNS server only if it lies after the adapter. Otherwise the list
//!   ends there. This makes the walk terminate on any octets (a cycle
//!   cannot repeat), and the real buffer is laid out in this order.
//! - **The first adapter is at offset 0**, the start of the buffer the OS
//!   filled. An empty buffer (`ERROR_NO_DATA`: no adapters) has no servers.
//! - **Only adapters that are up count**: `OperStatus` is `IfOperStatusUp`.
//!   An adapter that is down keeps its configured servers in the list, and
//!   asking them would only time out.
//! - **Scoped IPv6 servers are dropped**: link-local `fe80::/10` and the
//!   deprecated site-local `fec0::/10` (RFC 3879), that is, every address
//!   whose first octet is `0xFE` and whose second is at least `0x80`.
//!   `Addr` carries no zone, so a link-local server could not be reached,
//!   and Windows lists `fec0:0:0:ffff::1` to `::3` on every adapter with no
//!   IPv6 DNS server configured, where no server answers.
//! - **A server is used only when its socket address is whole**: the family
//!   is `AF_INET` with `iSockaddrLength` at least 16, or `AF_INET6` with it
//!   at least 28, and all `iSockaddrLength` octets lie in the buffer. The
//!   port, flow information and scope identifier are ignored. A negative
//!   `iSockaddrLength` reads as a number of at least 2^31 and so never fits.
//! - **`Length` fields are not read**: every field read is at its fixed
//!   offset. A record shorter than that is still inside the buffer, so
//!   nothing outside it is read.
//! - **Order**: adapters in list order, each adapter's servers in list
//!   order, with no duplicates removed (as resolv.conf's lines are).
//! - **Addresses are numbers**, as in `crate::spec`: an IPv4 address is the
//!   `u32` its four octets spell in network order, an IPv6 address the
//!   `u128` of its sixteen.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The layout (IPTypes.h, ws2def.h, ws2ipdef.h, ifdef.h; 64-bit).
// ---------------------------------------------------------------------------

/// `IP_ADAPTER_ADDRESSES_LH.Next`.
pub open spec fn adapter_next_at() -> nat {
    8
}

/// `IP_ADAPTER_ADDRESSES_LH.FirstDnsServerAddress`.
pub open spec fn adapter_first_dns_server_at() -> nat {
    48
}

/// `IP_ADAPTER_ADDRESSES_LH.OperStatus`.
pub open spec fn adapter_oper_status_at() -> nat {
    104
}

/// The octets of an adapter that are read: up to the end of `OperStatus`.
pub open spec fn adapter_len() -> nat {
    108
}

/// `IfOperStatusUp` of `IF_OPER_STATUS` (ifdef.h).
pub open spec fn if_oper_status_up() -> nat {
    1
}

/// `IP_ADAPTER_DNS_SERVER_ADDRESS_XP.Next`.
pub open spec fn server_next_at() -> nat {
    8
}

/// `IP_ADAPTER_DNS_SERVER_ADDRESS_XP.Address.lpSockaddr`.
pub open spec fn server_sockaddr_at() -> nat {
    16
}

/// `IP_ADAPTER_DNS_SERVER_ADDRESS_XP.Address.iSockaddrLength`.
pub open spec fn server_sockaddr_len_at() -> nat {
    24
}

/// The octets of a DNS server record that are read: up to the end of
/// `iSockaddrLength`.
pub open spec fn server_len() -> nat {
    28
}

/// `AF_INET` (ws2def.h).
pub open spec fn af_inet() -> nat {
    2
}

/// `AF_INET6` (ws2def.h).
pub open spec fn af_inet6() -> nat {
    23
}

/// `sizeof(SOCKADDR_IN)`.
pub open spec fn sockaddr_in_len() -> nat {
    16
}

/// `sizeof(SOCKADDR_IN6)`.
pub open spec fn sockaddr_in6_len() -> nat {
    28
}

/// `SOCKADDR_IN.sin_addr`.
pub open spec fn sin_addr_at() -> nat {
    4
}

/// `SOCKADDR_IN6.sin6_addr`.
pub open spec fn sin6_addr_at() -> nat {
    8
}

// ---------------------------------------------------------------------------
// Octets.
// ---------------------------------------------------------------------------

/// The unsigned integer `s` spells little-endian, least significant octet
/// first.
pub open spec fn le_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        le_value(s.drop_first()) * 256 + s[0] as nat
    }
}

/// The `n`-octet little-endian field at offset `at`.
pub open spec fn le_at(b: Seq<u8>, at: nat, n: nat) -> nat {
    le_value(b.subrange(at as int, (at + n) as int))
}

/// The offset of the `need` octets that pointer `p` points at, in a buffer
/// `b` that starts at address `base`: `None` for a null pointer, or if any
/// of those octets is outside `b`.
pub open spec fn offset_of(b: Seq<u8>, base: nat, p: nat, need: nat) -> Option<nat> {
    if p != 0 && base <= p && (p - base) + need <= b.len() {
        Some((p - base) as nat)
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// One server's address.
// ---------------------------------------------------------------------------

/// An IPv6 address that needs a zone, or is a deprecated site-local one:
/// `fe80::/10` or `fec0::/10`, which together are the addresses whose first
/// octet is `0xFE` and second at least `0x80`.
pub open spec fn is_scoped_v6(a: Seq<u8>) -> bool {
    a[0] == 0xFE && a[1] >= 0x80
}

/// The address of the `SOCKET_ADDRESS` `{ lpSockaddr: p, iSockaddrLength:
/// len }`, if it is a whole `SOCKADDR_IN`, or a whole `SOCKADDR_IN6` whose
/// address is not scoped.
pub open spec fn socket_address(b: Seq<u8>, base: nat, p: nat, len: nat) -> Option<crate::spec::Addr> {
    match offset_of(b, base, p, len) {
        None => None,
        Some(o) => {
            if len >= sockaddr_in_len() && le_at(b, o, 2) == af_inet() {
                let a = b.subrange((o + sin_addr_at()) as int, (o + sin_addr_at() + 4) as int);
                Some(crate::spec::Addr::V4(crate::spec::be_value(a) as u32))
            } else if len >= sockaddr_in6_len() && le_at(b, o, 2) == af_inet6() {
                let a = b.subrange((o + sin6_addr_at()) as int, (o + sin6_addr_at() + 16) as int);
                if is_scoped_v6(a) {
                    None
                } else {
                    Some(crate::spec::Addr::V6(crate::spec::be_value(a) as u128))
                }
            } else {
                None
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The lists.
// ---------------------------------------------------------------------------

/// The addresses of the DNS server list from the record `p` points at,
/// appended to `acc`. `after` is the offset the record must lie beyond: the
/// previous record's, or the adapter's for the first.
pub open spec fn servers_from(b: Seq<u8>, base: nat, p: nat, after: nat, acc: Seq<crate::spec::Addr>) -> Seq<crate::spec::Addr>
    decreases b.len() - after
{
    match offset_of(b, base, p, server_len()) {
        None => acc,
        Some(o) => {
            if o <= after {
                // Not forward: the list ends.
                acc
            } else {
                let sockaddr = le_at(b, o + server_sockaddr_at(), 8);
                let sockaddr_len = le_at(b, o + server_sockaddr_len_at(), 4);
                let acc2 = match socket_address(b, base, sockaddr, sockaddr_len) {
                    Some(a) => acc.push(a),
                    None => acc,
                };
                servers_from(b, base, le_at(b, o + server_next_at(), 8), o, acc2)
            }
        },
    }
}

/// The servers of the adapter at offset `at` and of the adapters it links
/// to, appended to `acc`.
pub open spec fn adapters_from(b: Seq<u8>, base: nat, at: nat, acc: Seq<crate::spec::Addr>) -> Seq<crate::spec::Addr>
    decreases b.len() - at
{
    if at + adapter_len() > b.len() {
        // No whole adapter here.
        acc
    } else {
        let acc2 = if le_at(b, at + adapter_oper_status_at(), 4) == if_oper_status_up() {
            servers_from(b, base, le_at(b, at + adapter_first_dns_server_at(), 8), at, acc)
        } else {
            acc
        };
        match offset_of(b, base, le_at(b, at + adapter_next_at(), 8), adapter_len()) {
            None => acc2,
            Some(o) => {
                if o <= at {
                    // Not forward: the list ends.
                    acc2
                } else {
                    adapters_from(b, base, o, acc2)
                }
            },
        }
    }
}

/// The DNS servers of the adapters that are up, in the buffer `b` that
/// `GetAdaptersAddresses` filled at address `base`, in list order.
pub open spec fn dns_servers(b: Seq<u8>, base: nat) -> Seq<crate::spec::Addr> {
    adapters_from(b, base, 0, seq![])
}

} // verus!

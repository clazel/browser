//! The executable typed host, refined to [`super::spec`].

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The target host: a DNS name or an IP address ([`super::spec::Host`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Host {
    /// A DNS name, ASCII, without a trailing dot (RFC 6066 §3).
    Dns(Vec<u8>),
    /// An IPv4 (4 octets) or IPv6 (16 octets) address, network byte order.
    Ip(Vec<u8>),
}

impl View for Host {
    type V = super::spec::Host;
    open spec fn view(&self) -> super::spec::Host {
        match self {
            Host::Dns(name) => super::spec::Host::Dns(name@),
            Host::Ip(address) => super::spec::Host::Ip(address@),
        }
    }
}

impl Host {
    /// [`super::spec::host_ok`].
    pub fn is_ok(&self) -> (out: bool)
        ensures out == super::spec::host_ok(self@),
    {
        match self {
            Host::Dns(name) => match name.last() {
                Some(last) => name.len() <= 253 && *last != 0x2eu8,
                None => false,
            },
            Host::Ip(address) => address.len() == 4 || address.len() == 16,
        }
    }

    /// RFC 6066 §3 ([`super::spec::sni_host_name`]): the HostName to send,
    /// if any; an address has none.
    pub fn sni_host_name(&self) -> (out: Option<&[u8]>)
        ensures match out {
            Some(name) => super::spec::sni_host_name(self@) == Some(name@),
            None => super::spec::sni_host_name(self@) is None,
        },
    {
        match self {
            Host::Dns(name) => Some(name.as_slice()),
            Host::Ip(_) => None,
        }
    }
}

} // verus!

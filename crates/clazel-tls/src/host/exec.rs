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
            Host::Dns(name) => {
                if name.len() == 0 || name.len() > 253 {
                    return false;
                }
                let mut run: usize = 0;
                let mut digits = true;
                let mut i: usize = 0;
                proof {
                    assert(name@.subrange(0, name@.len() as int) =~= name@);
                }
                while i < name.len()
                    invariant
                        i <= name@.len(),
                        1 <= name@.len() <= 253,
                        run <= 63,
                        super::spec::host_ok(self@) == super::spec::dns_labels_ok(
                            name@.subrange(i as int, name@.len() as int), run as nat, digits),
                    decreases name@.len() - i,
                {
                    let ghost rest = name@.subrange(i as int, name@.len() as int);
                    proof {
                        assert(rest[0] == name@[i as int]);
                        assert(rest.subrange(1, rest.len() as int) =~= name@.subrange(i + 1, name@.len() as int));
                    }
                    let b = match name.get(i) {
                        Some(b) => *b,
                        None => return false,
                    };
                    if b == 0x2eu8 {
                        if run == 0 {
                            return false;
                        }
                        run = 0;
                        digits = true;
                    } else {
                        if b >= 0x80u8 || b == 0x3au8 || run >= 63 {
                            return false;
                        }
                        run = run + 1;
                        digits = digits && 0x30u8 <= b && b <= 0x39u8;
                    }
                    i = i + 1;
                }
                proof {
                    assert(name@.subrange(i as int, name@.len() as int) =~= Seq::<u8>::empty());
                }
                run >= 1 && !digits
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

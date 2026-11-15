//! The kernel's sub-fetch connections on the network shell's driver
//! (phase-5.md item 5.19). The kernel names them `(renderer, serial, hop)`;
//! the driver keys connections by one number, so each name gets a number of
//! its own, from [`SUB_BASE`] up, far above the kernel's navigation
//! connections (its `next_conn` counts one per navigation from 0). The map
//! decides nothing: which connection, which octets and which credentials
//! stay the kernel's.

use std::collections::HashMap;

use clazel_kernel::exec::records::{EventRecord, OutputRecord};

use crate::driver::{InputBuf, Op};

/// A sub-fetch connection's name: renderer, serial, hop.
pub type Name = (u64, u64, u64);

/// The first number a sub-fetch connection runs under.
pub const SUB_BASE: u64 = 1 << 63;

/// The numbers of the kernel's sub-fetch connections.
#[derive(Debug, Default)]
pub struct SubConns {
    ids: HashMap<Name, u64>,
    names: HashMap<u64, Name>,
}

impl SubConns {
    fn id(&mut self, name: Name) -> u64 {
        let next = SUB_BASE.saturating_add(u64::try_from(self.ids.len()).unwrap_or(u64::MAX));
        let id = *self.ids.entry(name).or_insert(next);
        self.names.insert(id, name);
        id
    }

    /// The driver's operation for a `SubConnect`, `SubSend` or `SubClose`,
    /// on its connection's number; `None` for any other output.
    pub fn op(&mut self, o: &OutputRecord) -> Option<(u64, Op)> {
        let (name, op) = match o {
            OutputRecord::SubConnect {
                renderer,
                serial,
                hop,
                host,
                port,
                tls,
            } => {
                let op = Op::Connect {
                    host: host.clone(),
                    port: *port,
                    tls: *tls,
                };
                ((*renderer, *serial, *hop), op)
            }
            OutputRecord::SubSend {
                renderer,
                serial,
                hop,
                bytes,
            } => ((*renderer, *serial, *hop), Op::Send(bytes.clone())),
            OutputRecord::SubClose {
                renderer,
                serial,
                hop,
            } => ((*renderer, *serial, *hop), Op::Close),
            _ => return None,
        };
        Some((self.id(name), op))
    }

    /// The kernel's event for what connection `conn` reported: `SubNet`
    /// for a sub-fetch connection, `Net` for any other.
    pub fn event(&self, conn: u64, input: InputBuf) -> EventRecord {
        match self.names.get(&conn) {
            Some(&(renderer, serial, hop)) => EventRecord::SubNet {
                renderer,
                serial,
                hop,
                input,
            },
            None => EventRecord::Net { conn, input },
        }
    }
}

//! RFC 5280 name-constraint matching (§4.2.1.10, §6.1.3 (b) and (c),
//! §6.1.4 (g)) for dNSName, iPAddress, rfc822Name and directoryName:
//! the specification (`spec`), its contract (`contract`) and, once proven,
//! the executable code (`exec`).

pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod mutation_certificates;
pub mod spec;

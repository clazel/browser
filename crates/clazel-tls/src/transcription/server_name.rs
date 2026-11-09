//! RFC 6066 §3, Server Name Indication, as a TLS 1.3 client uses it: which host
//! gets the extension, its HostName, its encoding, and what the server's
//! `server_name` in EncryptedExtensions must be.
//!
//! RFC 8446 makes the extension mandatory to implement: §9.2, "all
//! implementations MUST support the use of the 'server_name' extension with
//! applications capable of using it", and §4.4.2.2, "As servers MAY require the
//! presence of the 'server_name' extension, clients SHOULD send this extension,
//! when applicable". §4.2's table places it in CH and EE.
//!
//! Sources, read for the sections cited:
//! - RFC 6066, January 2011, <https://www.rfc-editor.org/rfc/rfc6066>, the
//!   plain-text form fetched on 8 November 2026, SHA-256
//!   `6a33cceaa5e1b6518923d9d04ffaa738bad0417806b3c94a995484e140f5cbc0`.
//! - RFC 5890 §2.3.1 (LDH label), RFC 1123 §2.1 (host names and numbers) and
//!   RFC 1035 §2.3.4 (size limits), for what a "DNS hostname" is.
//!
//! Modelling choices:
//! - **The host is the client's string, as bytes** ([`host_name_for`]): what the
//!   application asked to connect to, after any conversion of U-labels to
//!   A-labels (RFC 5891 §4), which is the URL layer's job and is not transcribed
//!   here. RFC 6066: "'HostName' contains the fully qualified DNS hostname of the
//!   server, as understood by the client".
//! - **Which hosts get the extension.** RFC 6066 says the client "MAY include"
//!   it, and "It is RECOMMENDED that clients include an extension of type
//!   'server_name' in the client hello whenever they locate a server by a
//!   supported name type"; RFC 8446 §4.4.2.2 says SHOULD. The model follows the
//!   recommendation: the extension is sent exactly when the host is a DNS
//!   hostname, the one supported name type ("Currently, the only server names
//!   supported are DNS hostnames"). A host that is not (an IP literal, a string
//!   that breaks the hostname syntax) gets no extension, since no name of a
//!   supported type exists for it.
//! - **What a DNS hostname is.** RFC 6066 names no grammar. The one used is the
//!   one its own reference, RFC 5890 §2.3.1, gives: labels of "ASCII letters,
//!   digits, and the hyphen", with no hyphen "at the beginning or end", of at
//!   most 63 octets; RFC 1123 §2.1's relaxation (a label may start with a
//!   digit); and RFC 1035 §2.3.4's "names 255 octets or less", which, for the
//!   wire form of a name of n text octets without a trailing dot (a length octet
//!   per label and the root's zero octet), is n + 2 ≤ 255. Whether an "xn--"
//!   label is valid Punycode (RFC 5890's "Fake A-labels") is not checked: that
//!   needs IDNA, and RFC 6066 only asks for "A-labels" by reference.
//! - **IP literals.** "Literal IPv4 and IPv6 addresses are not permitted in
//!   'HostName'." An IPv6 literal, bracketed or not, holds `:`, which no LDH
//!   label does. An IPv4 literal is all digits and dots; RFC 1123 §2.1 says "a
//!   valid host name can never have the dotted-decimal form #.#.#.#, since at
//!   least the highest-level component label will be alphabetic". The rule
//!   applied is the weaker "the last label is not all digits", which excludes
//!   every dotted-decimal form (and the shorter ones some parsers accept, such
//!   as `127.1`) while keeping top-level labels such as `xn--p1ai`, which are
//!   not letters only.
//! - **The trailing dot.** "The hostname is represented as a byte string using
//!   ASCII encoding without a trailing dot": one trailing dot of the host is
//!   removed. A second one leaves an empty last label, which is not a hostname.
//! - **Case** is kept as given. "DNS hostnames are case-insensitive", and RFC
//!   6066 does not ask for a case to be chosen.
//! - **One name.** "The ServerNameList MUST NOT contain more than one name of the
//!   same name_type", and there is one type: the list holds one HostName.
//! - **The server's response.** "the server SHALL include an extension of type
//!   'server_name' in the (extended) server hello. The 'extension_data' field of
//!   this extension SHALL be empty." In TLS 1.3 §4.2's table moves it to EE. A
//!   non-empty body is a body that does not have the one form defined for it, so
//!   it is `decode_error` (by RFC 8446 §6's note), checked in
//!   `extension_bodies`. Its absence is not an error: the server "MAY use the
//!   information", and the SHALL binds only a server that did.
//! - The server's `unrecognized_name(112)` alert is an error alert like any
//!   other (RFC 8446 §6.2 "all unknown alerts" and the listed ones "are
//!   universally considered fatal"), handled by `connection`.
//! - "server endpoint identification", the comparison of the name with the
//!   certificate, is the application's (RFC 6066: "the client application will
//!   have to decide"), and part of `Primitives::validate_certificate_chain`.
//! - Resumption ("The client SHOULD include the same server_name extension in the
//!   session resumption request") does not arise: the client never resumes.

#[allow(unused_imports)]
use vstd::prelude::*;

#[cfg(verus_only)]
use super::extensions::*;
#[cfg(verus_only)]
use super::key_exchange::*;
#[cfg(verus_only)]
use super::presentation::*;

verus! {

// --------------------------------------------------------------------------
// RFC 6066 §3: the structures.
// --------------------------------------------------------------------------

/// RFC 6066 §3: `enum { host_name(0), (255) } NameType;`
pub open spec fn name_type_host_name() -> nat { 0 }

/// RFC 6066 §3: `struct { NameType name_type; select (name_type) { case
/// host_name: HostName; } name; } ServerName;`
pub struct ServerName {
    /// RFC 6066 §3 name_type.
    pub name_type: nat,
    /// RFC 6066 §3 name: for host_name, `opaque HostName<1..2^16-1>`.
    pub name: Seq<u8>,
}

/// RFC 6066 §3: the encoded `ServerNameList` of one HostName:
/// `struct { ServerName server_name_list<1..2^16-1> } ServerNameList;`
pub open spec fn write_server_name_list(host_name: Seq<u8>) -> Seq<u8> {
    write_vector(uint8(name_type_host_name()) + write_vector(host_name, 0xffff), 0xffff)
}

/// RFC 6066 §3: the body of `server_name_list` as its entries. "all future data
/// structures associated with new NameTypes MUST begin with a 16-bit length
/// field", so an entry of another type is read as a 16-bit-length vector.
pub open spec fn read_server_names(body: Seq<u8>) -> Option<Seq<ServerName>>
    decreases body.len(),
{
    if body.len() == 0 {
        Some(seq![])
    } else {
        let name_type = body[0] as nat;
        let floor: nat = if name_type == name_type_host_name() { 1 } else { 0 };
        match read_vector(body.subrange(1, body.len() as int), floor, 0xffff) {
            None => None,
            Some((name, rest)) =>
                if rest.len() >= body.len() {
                    None
                } else {
                    match read_server_names(rest) {
                        None => None,
                        Some(tail) => Some(seq![ServerName { name_type, name }] + tail),
                    }
                },
        }
    }
}

/// RFC 6066 §3: a whole `ServerNameList`.
pub open spec fn read_server_name_list(data: Seq<u8>) -> Option<Seq<ServerName>> {
    match read_vector(data, 1, 0xffff) {
        Some((body, rest)) => if rest.len() == 0 { read_server_names(body) } else { None },
        None => None,
    }
}

// --------------------------------------------------------------------------
// What a DNS hostname is (RFC 5890 §2.3.1, RFC 1123 §2.1, RFC 1035 §2.3.4).
// --------------------------------------------------------------------------

/// RFC 1035 §2.3.1 `<letter>`: "any one of the 52 alphabetic characters A
/// through Z in upper case and a through z in lower case".
pub open spec fn is_letter(byte: u8) -> bool {
    (0x41 <= byte && byte <= 0x5A) || (0x61 <= byte && byte <= 0x7A)
}

/// RFC 1035 §2.3.1 `<digit>`: "any one of the ten digits 0 through 9".
pub open spec fn is_digit(byte: u8) -> bool {
    0x30 <= byte && byte <= 0x39
}

/// RFC 1035 §2.3.1 `<let-dig-hyp>`.
pub open spec fn is_let_dig_hyp(byte: u8) -> bool {
    is_letter(byte) || is_digit(byte) || byte == 0x2D
}

/// Whether every byte is a letter, digit or hyphen.
pub open spec fn all_let_dig_hyp(label: Seq<u8>) -> bool
    decreases label.len(),
{
    if label.len() == 0 {
        true
    } else {
        is_let_dig_hyp(label[0]) && all_let_dig_hyp(label.subrange(1, label.len() as int))
    }
}

/// Whether every byte is a digit.
pub open spec fn all_digits(label: Seq<u8>) -> bool
    decreases label.len(),
{
    if label.len() == 0 {
        true
    } else {
        is_digit(label[0]) && all_digits(label.subrange(1, label.len() as int))
    }
}

/// RFC 5890 §2.3.1: an LDH label, "a string consisting of ASCII letters, digits,
/// and the hyphen with the further restriction that the hyphen cannot appear at
/// the beginning or end of the string. Like all DNS labels, its total length
/// must not exceed 63 octets." (RFC 1123 §2.1 lets it start with a digit.)
pub open spec fn is_ldh_label(label: Seq<u8>) -> bool {
    &&& 1 <= label.len() && label.len() <= 63
    &&& all_let_dig_hyp(label)
    &&& label[0] != 0x2D
    &&& label[label.len() - 1] != 0x2D
}

/// The labels of a name: the strings between its dots (0x2E), in order. Two
/// dots in a row, or a dot at either end, give an empty label.
pub open spec fn split_labels(name: Seq<u8>, current: Seq<u8>) -> Seq<Seq<u8>>
    decreases name.len(),
{
    if name.len() == 0 {
        seq![current]
    } else if name[0] == 0x2E {
        seq![current] + split_labels(name.subrange(1, name.len() as int), seq![])
    } else {
        split_labels(name.subrange(1, name.len() as int), current.push(name[0]))
    }
}

/// Whether every label is an LDH label.
pub open spec fn all_ldh_labels(labels: Seq<Seq<u8>>) -> bool
    decreases labels.len(),
{
    if labels.len() == 0 {
        true
    } else {
        is_ldh_label(labels[0]) && all_ldh_labels(labels.subrange(1, labels.len() as int))
    }
}

/// A DNS hostname, without a trailing dot, by the rules of the modelling choices.
pub open spec fn is_dns_host_name(name: Seq<u8>) -> bool {
    let labels = split_labels(name, seq![]);
    // RFC 1035 §2.3.4: "names 255 octets or less", in the wire form.
    &&& name.len() + 2 <= 255
    // RFC 5890 §2.3.1, RFC 1123 §2.1.
    &&& all_ldh_labels(labels)
    // RFC 6066: "Literal IPv4 and IPv6 addresses are not permitted"; RFC 1123
    // §2.1: "at least the highest-level component label will be alphabetic".
    &&& !all_digits(labels.last())
}

/// RFC 6066 §3: the HostName the client sends for `host`, if it locates the
/// server by a DNS hostname: "a byte string using ASCII encoding without a
/// trailing dot".
pub open spec fn host_name_for(host: Seq<u8>) -> Option<Seq<u8>> {
    let name = if host.len() > 0 && host.last() == 0x2E { host.drop_last() } else { host };
    if is_dns_host_name(name) { Some(name) } else { None }
}

// --------------------------------------------------------------------------
// RFC 6066 §3 in the ClientHello.
// --------------------------------------------------------------------------

/// RFC 6066 §3: "It is RECOMMENDED that clients include an extension of type
/// 'server_name' in the client hello whenever they locate a server by a
/// supported name type". The extension for `host`, or none.
pub open spec fn server_name_extensions(host: Seq<u8>) -> Seq<Extension> {
    match host_name_for(host) {
        Some(host_name) => seq![Extension {
            extension_type: ext_server_name(),
            extension_data: write_server_name_list(host_name),
        }],
        None => seq![],
    }
}

/// RFC 6066 §3 and RFC 8446 §4.4.2.2, §9.2: what a ClientHello for `host` holds
/// as server_name: the one HostName of the host if it has one, and otherwise no
/// extension.
pub open spec fn client_hello_names_host(hello: ClientHello, host: Seq<u8>) -> bool {
    find_extension(hello.extensions, ext_server_name()) == match host_name_for(host) {
        Some(host_name) => Some(write_server_name_list(host_name)),
        None => None,
    }
}

// --------------------------------------------------------------------------
// RFC 6066 §3 in EncryptedExtensions.
// --------------------------------------------------------------------------

/// RFC 6066 §3: "The 'extension_data' field of this extension SHALL be empty."
pub open spec fn server_name_response_well_formed(data: Seq<u8>) -> bool {
    data.len() == 0
}

} // verus!

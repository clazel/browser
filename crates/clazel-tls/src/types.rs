//! The executable message types. Each is the exec twin of the spec struct
//! of the same name in [`super::spec`], whose view it is. Opaque fields
//! are slices of the message buffer, so reading a message copies nothing
//! but the lists.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The spec view of a sequence of values with views.
pub open spec fn views<T: View>(s: Seq<T>) -> Seq<T::V> {
    s.map_values(|t: T| t@)
}

/// Pushing a value pushes its view.
pub proof fn lemma_views_push<T: View>(s: Seq<T>, t: T)
    ensures
        views(s.push(t)) =~= views(s).push(t@),
{
    assert(views(s.push(t)).len() == s.len() + 1);
    assert forall|i: int| 0 <= i < s.len() + 1 implies views(s.push(t))[i] == views(s).push(t@)[i] by {
        if i < s.len() {
            assert(s.push(t)[i] == s[i]);
        }
    }
}

/// §4.2 `Extension`: the type and the opaque `extension_data`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Extension<'a> {
    /// `extension_type`.
    pub etype: u16,
    /// `extension_data`.
    pub data: &'a [u8],
}

impl<'a> View for Extension<'a> {
    type V = super::spec::Ext;

    open spec fn view(&self) -> super::spec::Ext {
        super::spec::Ext { etype: self.etype, data: self.data@ }
    }
}

/// §4.2.8 `KeyShareEntry`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct KeyShare<'a> {
    /// `group`.
    pub group: u16,
    /// `key_exchange`.
    pub key_exchange: &'a [u8],
}

impl<'a> View for KeyShare<'a> {
    type V = super::spec::KeyShare;

    open spec fn view(&self) -> super::spec::KeyShare {
        super::spec::KeyShare { group: self.group, key_exchange: self.key_exchange@ }
    }
}

/// RFC 6066 §3 `ServerName` of type `host_name`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ServerName<'a> {
    /// The `HostName` bytes.
    pub host_name: &'a [u8],
}

impl<'a> View for ServerName<'a> {
    type V = super::spec::ServerName;

    open spec fn view(&self) -> super::spec::ServerName {
        super::spec::ServerName { host_name: self.host_name@ }
    }
}

/// §4.1.2 `ClientHello`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ClientHello<'a> {
    /// `legacy_version`.
    pub legacy_version: u16,
    /// `random`.
    pub random: &'a [u8],
    /// `legacy_session_id`.
    pub session_id: &'a [u8],
    /// `cipher_suites`.
    pub cipher_suites: Vec<u16>,
    /// `legacy_compression_methods`.
    pub compression: &'a [u8],
    /// `extensions`.
    pub extensions: Vec<Extension<'a>>,
}

impl<'a> View for ClientHello<'a> {
    type V = super::spec::ClientHello;

    open spec fn view(&self) -> super::spec::ClientHello {
        super::spec::ClientHello {
            legacy_version: self.legacy_version,
            random: self.random@,
            session_id: self.session_id@,
            cipher_suites: self.cipher_suites@,
            compression: self.compression@,
            extensions: views(self.extensions@),
        }
    }
}

/// §4.1.3 `ServerHello`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ServerHello<'a> {
    /// `legacy_version`.
    pub legacy_version: u16,
    /// `random`.
    pub random: &'a [u8],
    /// `legacy_session_id_echo`.
    pub session_id_echo: &'a [u8],
    /// `cipher_suite`.
    pub cipher_suite: u16,
    /// `legacy_compression_method`.
    pub compression: u8,
    /// `extensions`.
    pub extensions: Vec<Extension<'a>>,
}

impl<'a> View for ServerHello<'a> {
    type V = super::spec::ServerHello;

    open spec fn view(&self) -> super::spec::ServerHello {
        super::spec::ServerHello {
            legacy_version: self.legacy_version,
            random: self.random@,
            session_id_echo: self.session_id_echo@,
            cipher_suite: self.cipher_suite,
            compression: self.compression,
            extensions: views(self.extensions@),
        }
    }
}

/// §4.3.2 `CertificateRequest`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CertificateRequest<'a> {
    /// `certificate_request_context`.
    pub context: &'a [u8],
    /// `extensions`.
    pub extensions: Vec<Extension<'a>>,
}

impl<'a> View for CertificateRequest<'a> {
    type V = super::spec::CertificateRequest;

    open spec fn view(&self) -> super::spec::CertificateRequest {
        super::spec::CertificateRequest { context: self.context@, extensions: views(self.extensions@) }
    }
}

/// §4.4.2 `CertificateEntry`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CertificateEntry<'a> {
    /// `cert_data`.
    pub cert_data: &'a [u8],
    /// `extensions`.
    pub extensions: Vec<Extension<'a>>,
}

impl<'a> View for CertificateEntry<'a> {
    type V = super::spec::CertificateEntry;

    open spec fn view(&self) -> super::spec::CertificateEntry {
        super::spec::CertificateEntry { cert_data: self.cert_data@, extensions: views(self.extensions@) }
    }
}

/// §4.4.2 `Certificate`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Certificate<'a> {
    /// `certificate_request_context`.
    pub context: &'a [u8],
    /// `certificate_list`.
    pub entries: Vec<CertificateEntry<'a>>,
}

impl<'a> View for Certificate<'a> {
    type V = super::spec::Certificate;

    open spec fn view(&self) -> super::spec::Certificate {
        super::spec::Certificate { context: self.context@, entries: views(self.entries@) }
    }
}

/// §4.4.3 `CertificateVerify`.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct CertificateVerify<'a> {
    /// `algorithm`.
    pub algorithm: u16,
    /// `signature`.
    pub signature: &'a [u8],
}

impl<'a> View for CertificateVerify<'a> {
    type V = super::spec::CertificateVerify;

    open spec fn view(&self) -> super::spec::CertificateVerify {
        super::spec::CertificateVerify { algorithm: self.algorithm, signature: self.signature@ }
    }
}

/// §4.6.1 `NewSessionTicket`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NewSessionTicket<'a> {
    /// `ticket_lifetime`.
    pub ticket_lifetime: u32,
    /// `ticket_age_add`.
    pub ticket_age_add: u32,
    /// `ticket_nonce`.
    pub ticket_nonce: &'a [u8],
    /// `ticket`.
    pub ticket: &'a [u8],
    /// `extensions`.
    pub extensions: Vec<Extension<'a>>,
}

impl<'a> View for NewSessionTicket<'a> {
    type V = super::spec::NewSessionTicket;

    open spec fn view(&self) -> super::spec::NewSessionTicket {
        super::spec::NewSessionTicket {
            ticket_lifetime: self.ticket_lifetime,
            ticket_age_add: self.ticket_age_add,
            ticket_nonce: self.ticket_nonce@,
            ticket: self.ticket@,
            extensions: views(self.extensions@),
        }
    }
}

/// A handshake message this crate reads: [`super::spec::HsMsg`].
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum HsMsg<'a> {
    /// §4.1.2.
    ClientHello(ClientHello<'a>),
    /// §4.1.3 and §4.1.4.
    ServerHello(ServerHello<'a>),
    /// §4.6.1.
    NewSessionTicket(NewSessionTicket<'a>),
    /// §4.5.
    EndOfEarlyData,
    /// §4.3.1.
    EncryptedExtensions(Vec<Extension<'a>>),
    /// §4.4.2.
    Certificate(Certificate<'a>),
    /// §4.3.2.
    CertificateRequest(CertificateRequest<'a>),
    /// §4.4.3.
    CertificateVerify(CertificateVerify<'a>),
    /// §4.4.4: `verify_data`.
    Finished(&'a [u8]),
    /// §4.6.3: `request_update`.
    KeyUpdate(u8),
}

impl<'a> View for HsMsg<'a> {
    type V = super::spec::HsMsg;

    open spec fn view(&self) -> super::spec::HsMsg {
        match self {
            HsMsg::ClientHello(m) => super::spec::HsMsg::ClientHello(m@),
            HsMsg::ServerHello(m) => super::spec::HsMsg::ServerHello(m@),
            HsMsg::NewSessionTicket(m) => super::spec::HsMsg::NewSessionTicket(m@),
            HsMsg::EndOfEarlyData => super::spec::HsMsg::EndOfEarlyData,
            HsMsg::EncryptedExtensions(es) => super::spec::HsMsg::EncryptedExtensions(views(es@)),
            HsMsg::Certificate(m) => super::spec::HsMsg::Certificate(m@),
            HsMsg::CertificateRequest(m) => super::spec::HsMsg::CertificateRequest(m@),
            HsMsg::CertificateVerify(m) => super::spec::HsMsg::CertificateVerify(m@),
            HsMsg::Finished(v) => super::spec::HsMsg::Finished(v@),
            HsMsg::KeyUpdate(r) => super::spec::HsMsg::KeyUpdate(*r),
        }
    }
}

/// The exec result of a parse, as the spec's [`super::spec::Res`].
pub open spec fn res_view<T: View>(r: Result<T, super::spec::ErrKind>) -> super::spec::Res<T::V> {
    match r {
        Ok(v) => super::spec::Res::Ok(v@),
        Err(k) => super::spec::Res::Err(k),
    }
}

} // verus!

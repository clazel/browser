//! The executable states, inputs and actions, and their views as the
//! spec's.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_http::message::types::ResponseBuf;
use clazel_url::url::record::ParsedUrl;

verus! {

/// [`Phase`], executable.
pub enum PhaseBuf {
    /// waiting for `Connected`
    Connecting,
    /// reading the response
    Reading {
        /// the octets received and not yet consumed
        received: Vec<u8>,
    },
    /// over
    Finished,
}

impl View for PhaseBuf {
    type V = Phase;

    open spec fn view(&self) -> Phase {
        match self {
            PhaseBuf::Connecting => Phase::Connecting,
            PhaseBuf::Reading { received } => Phase::Reading { received: received@ },
            PhaseBuf::Finished => Phase::Finished,
        }
    }
}

/// [`State`], executable.
pub struct StateBuf {
    /// the URL of the current request
    pub url: ParsedUrl,
    /// where it is
    pub phase: PhaseBuf,
}

impl View for StateBuf {
    type V = State;

    open spec fn view(&self) -> State {
        State { url: self.url@, phase: self.phase@ }
    }
}

/// [`Input`], executable.
#[derive(Debug, PartialEq, Eq)]
pub enum InputBuf {
    /// the connection is open
    Connected,
    /// octets read from it
    Bytes(Vec<u8>),
    /// the server closed it
    Closed,
    /// it could not be opened, or failed
    Error,
}

impl View for InputBuf {
    type V = Input;

    open spec fn view(&self) -> Input {
        match self {
            InputBuf::Connected => Input::Connected,
            InputBuf::Bytes(b) => Input::Bytes(b@),
            InputBuf::Closed => Input::Closed,
            InputBuf::Error => Input::Error,
        }
    }
}

/// [`Action`], executable.
pub enum ActionBuf {
    /// open a connection
    Connect {
        /// the host, for the resolver
        host: Vec<u8>,
        /// the port
        port: u16,
        /// whether to speak TLS (never, yet)
        tls: bool,
    },
    /// write these octets
    Send(Vec<u8>),
    /// close the connection
    Close,
    /// the final response (boxed: it is far larger than the others)
    Done {
        /// the URL of the request it answers
        url: Box<ParsedUrl>,
        /// the response
        response: Box<ResponseBuf>,
    },
    /// the fetch failed
    Fail(Reason),
}

impl View for ActionBuf {
    type V = Action;

    open spec fn view(&self) -> Action {
        match self {
            ActionBuf::Connect { host, port, tls } => Action::Connect { host: host@, port: *port as nat, tls: *tls },
            ActionBuf::Send(b) => Action::Send(b@),
            ActionBuf::Close => Action::Close,
            ActionBuf::Done { url, response } => Action::Done { url: url@, response: response@ },
            ActionBuf::Fail(r) => Action::Fail(*r),
        }
    }
}

/// The view of a list of actions.
pub open spec fn actions_view(a: Seq<ActionBuf>) -> Seq<Action> {
    a.map_values(|x: ActionBuf| x@)
}

/// [`Settled`], executable.
pub enum SettledBuf {
    /// wait, with these octets unconsumed
    Wait(Vec<u8>),
    /// the final response
    Final(ResponseBuf),
    /// the fetch fails
    Bad(Reason),
}

impl View for SettledBuf {
    type V = Settled;

    open spec fn view(&self) -> Settled {
        match self {
            SettledBuf::Wait(b) => Settled::Wait(b@),
            SettledBuf::Final(r) => Settled::Final(r@),
            SettledBuf::Bad(r) => Settled::Bad(*r),
        }
    }
}

} // verus!

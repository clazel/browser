//! The executable states, inputs and actions, and their views as the
//! spec's.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use clazel_cookie::storage::exec::{RequestContextRecord, RequestUrlRecord};
use clazel_http::message::body::ResponseParser;
use clazel_http::message::types::ResponseBuf;
use clazel_url::url::record::ParsedUrl;

verus! {

/// [`Phase`], executable.
pub enum PhaseBuf {
    /// waiting for `Connected`
    Connecting,
    /// reading the response
    Reading {
        /// the parser holding the octets received and not yet consumed
        /// (its `received()`)
        parser: ResponseParser,
    },
    /// over
    Finished,
}

impl View for PhaseBuf {
    type V = Phase;

    open spec fn view(&self) -> Phase {
        match self {
            PhaseBuf::Connecting => Phase::Connecting,
            PhaseBuf::Reading { parser } => Phase::Reading { received: parser.received() },
            PhaseBuf::Finished => Phase::Finished,
        }
    }
}

/// [`State`], executable.
pub struct StateBuf {
    /// the URL of the current request
    pub url: ParsedUrl,
    /// the redirect count, at most 20
    pub redirects: u8,
    /// where it is
    pub phase: PhaseBuf,
    /// the redirect-taint is cross-site
    pub tainted: bool,
}

impl View for StateBuf {
    type V = State;

    open spec fn view(&self) -> State {
        State {
            url: self.url@,
            redirects: self.redirects as nat,
            phase: self.phase@,
            tainted: self.tainted,
        }
    }
}

/// [`LocationUrl`], executable.
pub enum LocationBuf {
    /// null
    Null,
    /// failure
    Failure,
    /// a URL
    Url(ParsedUrl),
}

impl View for LocationBuf {
    type V = LocationUrl;

    open spec fn view(&self) -> LocationUrl {
        match self {
            LocationBuf::Null => LocationUrl::Null,
            LocationBuf::Failure => LocationUrl::Failure,
            LocationBuf::Url(u) => LocationUrl::Url(u@),
        }
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

/// [`JarOp`], executable.
pub enum JarOpBuf {
    /// §5.8.3 retrieval
    Retrieved {
        /// the request URL
        url: RequestUrlRecord,
        /// the request context
        ctx: RequestContextRecord,
        /// the time
        now: u64,
    },
    /// §5.7 storage of one `Set-Cookie` value
    Stored {
        /// the field value
        line: Vec<u8>,
        /// the request URL
        url: RequestUrlRecord,
        /// the request context
        ctx: RequestContextRecord,
        /// the time
        now: u64,
    },
}

impl View for JarOpBuf {
    type V = JarOp;

    open spec fn view(&self) -> JarOp {
        match self {
            JarOpBuf::Retrieved { url, ctx, now } => JarOp::Retrieved { url: url@, ctx: ctx@, now: *now as int },
            JarOpBuf::Stored { line, url, ctx, now } => JarOp::Stored { line: line@, url: url@, ctx: ctx@, now: *now as int },
        }
    }
}

/// The view of a list of jar operations.
pub open spec fn ops_view(a: Seq<JarOpBuf>) -> Seq<JarOp> {
    a.map_values(|x: JarOpBuf| x@)
}

/// [`Settled`], executable.
pub enum SettledBuf {
    /// wait, with the octets this parser received unconsumed
    Wait(ResponseParser),
    /// the final response
    Final(ResponseBuf),
    /// the fetch fails
    Bad(Reason),
}

impl View for SettledBuf {
    type V = Settled;

    open spec fn view(&self) -> Settled {
        match self {
            SettledBuf::Wait(p) => Settled::Wait(p.received()),
            SettledBuf::Final(r) => Settled::Final(r@),
            SettledBuf::Bad(r) => Settled::Bad(*r),
        }
    }
}

} // verus!

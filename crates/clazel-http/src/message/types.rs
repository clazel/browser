//! The executable records and results, and their views as the spec's.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use crate::field::types::FieldLineBuf;

verus! {

/// A status line (§4), viewed as [`StatusLine`].
#[derive(Debug, PartialEq, Eq)]
pub struct StatusLineBuf {
    /// The major version digit's value.
    pub major: u8,
    /// The minor version digit's value.
    pub minor: u8,
    /// The status code, 0 to 999.
    pub status: u16,
    /// The reason phrase, possibly empty; never interpret it (§4).
    pub reason: Vec<u8>,
}

impl View for StatusLineBuf {
    type V = StatusLine;

    open spec fn view(&self) -> StatusLine {
        StatusLine { major: self.major as nat, minor: self.minor as nat, status: self.status as nat, reason: self.reason@ }
    }
}

/// A response head, viewed as [`Head`].
#[derive(Debug, PartialEq, Eq)]
pub struct HeadBuf {
    /// The status line.
    pub status_line: StatusLineBuf,
    /// The field lines, in order.
    pub fields: Vec<FieldLineBuf>,
}

impl View for HeadBuf {
    type V = Head;

    open spec fn view(&self) -> Head {
        Head { status_line: self.status_line@, fields: crate::field::types::lines_view(self.fields@) }
    }
}

/// A response, viewed as [`Response`].
#[derive(Debug, PartialEq, Eq)]
pub struct ResponseBuf {
    /// The status line.
    pub status_line: StatusLineBuf,
    /// The header field lines, in order.
    pub fields: Vec<FieldLineBuf>,
    /// The content, with the chunked coding removed.
    pub body: Vec<u8>,
}

impl View for ResponseBuf {
    type V = Response;

    open spec fn view(&self) -> Response {
        Response { status_line: self.status_line@, fields: crate::field::types::lines_view(self.fields@), body: self.body@ }
    }
}

/// The result of parsing a response, viewed as [`Parse`].
#[derive(Debug, PartialEq, Eq)]
pub enum ParseBuf {
    /// The response, and the octets received after it (never a second
    /// response: RFC 9112 §6.3).
    Done {
        /// the response
        response: ResponseBuf,
        /// the octets after it
        rest: Vec<u8>,
    },
    /// More bytes are needed.
    Incomplete,
    /// Not a valid response, or past a limit.
    Invalid,
    /// A transfer coding this client cannot decode.
    Unsupported,
}

impl View for ParseBuf {
    type V = Parse;

    open spec fn view(&self) -> Parse {
        match self {
            ParseBuf::Done { response, rest } => Parse::Done { response: response@, rest: rest@ },
            ParseBuf::Incomplete => Parse::Incomplete,
            ParseBuf::Invalid => Parse::Invalid,
            ParseBuf::Unsupported => Parse::Unsupported,
        }
    }
}

/// A request to serialize, viewed as [`Request`].
#[derive(Debug, PartialEq, Eq)]
pub struct RequestBuf {
    /// The method, a token.
    pub method: Vec<u8>,
    /// The request target, in the form the caller chose.
    pub target: Vec<u8>,
    /// The header field lines, in order.
    pub fields: Vec<FieldLineBuf>,
}

impl View for RequestBuf {
    type V = Request;

    open spec fn view(&self) -> Request {
        Request { method: self.method@, target: self.target@, fields: crate::field::types::lines_view(self.fields@) }
    }
}

/// The view of an optional field line.
pub open spec fn opt_line_view(p: Option<FieldLineBuf>) -> Option<FieldLine> {
    match p {
        Some(l) => Some(l@),
        None => None,
    }
}

} // verus!

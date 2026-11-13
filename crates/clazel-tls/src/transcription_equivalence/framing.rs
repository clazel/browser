//! RFC 8446 §5.1 and §5.2: the crate's record framer,
//! `connection/framing_spec.rs` (with `spec.rs` `read_record`), against the
//! clean-room transcription's reading of a byte stream
//! (`connection::receive_stream`, `record_length_failure`, `receive_record`,
//! `record::read_record_header`).
//!
//! The earlier theorems ([`super::bootstrap`], [`super::dispatcher`],
//! [`super::post_handshake`]) compare one *whole* record at a time. This
//! file closes the gap between that and a byte stream delivered in
//! arbitrary chunks:
//!
//! 1. **Chunking does not matter** ([`lemma_drive`],
//!    [`theorem_framing_equivalence`]). [`drive`] is the framer's caller:
//!    it feeds the chunks in order, takes every record the framer
//!    completes and feeds the rest of the chunk again, and stops at a
//!    failure. Its result is [`frames`] of the concatenated bytes, a
//!    function of the bytes alone.
//! 2. **The framer completes exactly the transcription's whole records**
//!    ([`framing_agrees`]). [`split`] is how `receive_stream` divides a
//!    stream (its header, its length check, five bytes and `length` more),
//!    with the protection fixed. The crate's records are the first of the
//!    transcription's, byte for byte, and consume exactly their bytes; when
//!    the crate waits, the transcription waits on the same bytes; when the
//!    crate fails, it fails on the next record of the transcription's split
//!    with the alert it gives that whole record, or the record is not yet
//!    whole and the failure is an [`early_reject`].
//! 3. **Timing** ([`early_reject`], [`lemma_early_reject`]). The crate
//!    decides on the five header bytes as soon as they are there
//!    (`read_record` steps 1, 3 and 4). The transcription decides on the
//!    header's length as soon as it is there too (`receive_stream`'s
//!    `record_length_failure`), but on the record's type only once the whole
//!    record has arrived (`receive_record`), or never, if the stream ends
//!    first. So on a record whose header has arrived and whose body has not,
//!    the crate may reject (a type the mode does not allow) where the
//!    transcription waits. [`lemma_early_reject`] proves that every
//!    completion of such a header is rejected by both: by the crate with the
//!    same alert, and by the transcription with that alert, or both reject
//!    and [`header_two_faults`] holds (the existing "record header order"
//!    difference). No header that the crate rejects early is accepted by the
//!    transcription once its record is complete.
//! 4. **Each layer, for streams.** For each of the three machines, its
//!    caller over any chunking is a function of the concatenated bytes (the
//!    machine's whole-record step on each record the framer completes, in
//!    order), and along that stream the machine and the transcription agree
//!    record by record through the existing whole-record theorem, from the
//!    states it says agree again, with the end of the stream as in item 2:
//!    - **bootstrap** ([`theorem_boot_stream`]): [`boot_drive`] is
//!      [`boot_steps`] (`bootstrap_lemmas::record_step` on each record), and
//!      [`boot_stream_agrees`] carries `bootstrap::record_agrees` against
//!      `middlebox::client_receive_stream` of the whole stream;
//!    - **dispatcher** ([`theorem_disp_stream`]): [`disp_drive`] is
//!      [`disp_steps`] (`dispatcher_spec::receive_record` on each record),
//!      and [`disp_stream_agrees`] carries `dispatcher::record_agrees`
//!      against `client_receive_stream`, at every record (the crate's
//!      transcript cap is the dispatcher theorem's stated difference
//!      `dispatcher::transcript_cap`, not a domain);
//!    - **post-handshake** ([`theorem_post_stream`]): [`post_drive`] is
//!      [`post_steps`] (`step` on what is held, the caller resubmitting the
//!      rest), and [`post_stream_agrees`] carries
//!      `post_handshake::record_agrees` against `connection::receive_stream`,
//!      up to the first record after which the transcription owes a
//!      KeyUpdate (the existing `settle` difference: the crate has sent its
//!      answer and the transcription has not, so the two connections differ
//!      by that KeyUpdate from then on).
//!
//!    When a machine stops on a record (an action for its caller: a flight to
//!    send and acknowledge, the handover to the next machine, a failure, a
//!    closure), the transcription's result on the whole stream is its result
//!    on that record joined with its result on the rest
//!    (`post_handshake::joined`), and the unconsumed bytes stay with the
//!    caller: what comes next is the caller's (the driver theorem's).
//!
//! Where the two sides decide differently on a partial record (each stated
//! as a definition, none excluded from a domain):
//! - [`early_reject`]: the crate rejects a header with a type its mode does
//!   not allow before the body arrives; the transcription waits for the
//!   body, then rejects it with the same alert ([`lemma_early_reject`]), or
//!   never decides if the stream ends first. When the length is refused too,
//!   both reject at the header, the crate naming the type
//!   ([`header_two_faults`], the earlier theorems' `two_faults` for a
//!   header).
//! - `post_handshake::exhausted`: after sequence number 2^64 - 1, the
//!   transducer refuses the next step with `internal_error` before any byte
//!   of a next record has arrived; the transcription waits (and refuses the
//!   record once its header passes, or its length).
//!
//! No disagreement was found: no header the crate rejects early is accepted
//! by the transcription once its record is complete, and the crate never
//! completes a record the transcription does not split off whole.
//!
//! Modelling choices of this file:
//! - [`drive`] is the caller that the framer's modelling choices describe
//!   ("The caller retains/resubmits only the unconsumed suffix. A completed
//!   record is cleared by take."). It stops at a failure, which is final
//!   in every layer. [`boot_drive`], [`disp_drive`] and [`post_drive`] are
//!   that caller for each machine: they feed again while the machine still
//!   reads and asked nothing of the caller, and otherwise stop with the
//!   machine's action.
//! - [`split`] fixes the transcription's protection (`Connection::receive`),
//!   since a stream's protection changes only at the record boundaries where
//!   the crate hands over from one layer to the next (§5.1: "all messages
//!   immediately preceding a key change align with a record boundary").
//!   The read side is open (§6.1: once it has closed, both sides ignore
//!   what follows).

#[cfg(verus_only)]
use crate::connection::framing_spec::{Feed, Status};
#[cfg(verus_only)]
use crate::spec::Read;
use crate::transcription::alerts::ClientError;
#[cfg(verus_only)]
use crate::transcription::connection::{Connection, Progress, Protection, Receive};
#[cfg(verus_only)]
use crate::transcription::primitives::Primitives;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// The crate's framer on a stream.
// ---------------------------------------------------------------------------

/// §5.1: where the crate's framer decides on the record at the front of `w`,
/// and what it decides, from `read_record` on the bytes it holds: on the
/// five header bytes (steps 1, 3, 4), then on the whole record (step 5); or
/// it waits, holding all of `w`.
pub open spec fn first(w: Seq<u8>, protected: bool) -> (Status, nat) {
    if w.len() < 5 {
        (Status::Pending, w.len())
    } else {
        match crate::spec::read_record(w.take(5), protected) {
            Read::Fail(e) => (Status::Fail(crate::spec::alert_of(e)), 5),
            _ => {
                let n = 5 + super::bootstrap::length(w);
                if w.len() < n {
                    (Status::Pending, w.len())
                } else {
                    match crate::spec::read_record(w.take(n as int), protected) {
                        Read::Fail(e) => (Status::Fail(crate::spec::alert_of(e)), n),
                        Read::Done(_, _) => (Status::Complete, n),
                        // Not reached (`lemma_first`).
                        Read::NeedMore => (Status::Pending, w.len()),
                    }
                }
            },
        }
    }
}

/// `read_record` decides on `b` exactly as on any longer stream that starts
/// with `b`: a decision does not depend on the bytes after it.
pub proof fn lemma_read_extend(b: Seq<u8>, more: Seq<u8>, protected: bool)
    requires !(crate::spec::read_record(b, protected) is NeedMore),
    ensures
        crate::spec::read_record(b + more, protected) == match crate::spec::read_record(b, protected) {
            Read::Done(f, r) => Read::Done(f, r + more),
            other => other,
        },
{
    reveal(crate::spec::read_record);
    let w = b + more;
    assert(b.len() >= 5);
    assert(w[0] == b[0]);
    assert(w.subrange(3, 5) =~= b.subrange(3, 5));
    assert(w.take(5) =~= b.take(5));
    let len = crate::spec::be_value(b.subrange(3, 5));
    if b.len() >= 5 + len {
        assert(w.subrange(5, (5 + len) as int) =~= b.subrange(5, (5 + len) as int));
        assert(w.skip((5 + len) as int) =~= b.skip((5 + len) as int) + more);
    }
}

/// A prefix the parser waits on is within the framer's bound.
pub proof fn lemma_need_more_wf(b: Seq<u8>, protected: bool)
    requires crate::spec::read_record(b, protected) is NeedMore,
    ensures crate::connection::framing_spec::wf_mode(b, protected),
{
    reveal(crate::spec::read_record);
}

/// The empty prefix is one the parser waits on.
pub proof fn lemma_empty(protected: bool)
    ensures
        crate::spec::read_record(Seq::<u8>::empty(), protected) is NeedMore,
        crate::connection::framing_spec::wf_mode(Seq::<u8>::empty(), protected),
{
    reveal(crate::spec::read_record);
}

/// What `read_record` says of every prefix `w.take(j)` of `w`, given
/// [`first`]: it waits before the decision, decides there as [`first`]
/// says, and does not wait after it.
pub proof fn lemma_first(w: Seq<u8>, j: nat, protected: bool)
    requires j <= w.len(),
    ensures ({
        let (st, k) = first(w, protected);
        &&& (st is Pending || j < k) ==> crate::spec::read_record(w.take(j as int), protected) is NeedMore
        &&& (st is Pending ==> k == w.len())
        &&& !(st is Pending) ==> {
            &&& 5 <= k <= w.len()
            &&& !(crate::spec::read_record(w.take(k as int), protected) is NeedMore)
            &&& crate::connection::framing_spec::status_mode(w.take(k as int), protected) == st
            &&& (k <= j ==> !(crate::spec::read_record(w.take(j as int), protected) is NeedMore))
        }
    }),
{
    reveal(crate::spec::read_record);
    let (st, k) = first(w, protected);
    let x = w.take(j as int);
    if w.len() >= 5 {
        let h = w.take(5);
        let len = super::bootstrap::length(w);
        assert(h.subrange(3, 5) =~= w.subrange(3, 5));
        if j >= 5 {
            assert(x.subrange(3, 5) =~= w.subrange(3, 5));
            assert(x[0] == w[0]);
            assert(x.take(5) =~= h);
        }
        if w.len() >= 5 + len {
            let b = w.take((5 + len) as int);
            assert(b.subrange(3, 5) =~= w.subrange(3, 5));
            assert(b.take(5) =~= h);
            assert(b.skip((5 + len) as int) =~= Seq::<u8>::empty());
            if j >= 5 + len {
                assert(x.subrange(5, (5 + len) as int) =~= b.subrange(5, (5 + len) as int));
            }
        }
        if !(st is Pending) && k <= j {
            let y = w.take(k as int);
            assert(x =~= y + w.subrange(k as int, j as int));
            lemma_read_extend(y, w.subrange(k as int, j as int), protected);
        }
    }
}

/// A decision on `x` is the decision on every stream that starts with `x`.
pub proof fn lemma_first_extend(x: Seq<u8>, y: Seq<u8>, protected: bool)
    requires !(first(x, protected).0 is Pending),
    ensures first(x + y, protected) == first(x, protected),
{
    let w = x + y;
    assert(w.take(5) =~= x.take(5));
    assert(w.subrange(3, 5) =~= x.subrange(3, 5));
    let n = 5 + super::bootstrap::length(x);
    if x.len() >= n {
        assert(w.take(n as int) =~= x.take(n as int));
    }
}

/// §5.1: the framer fed `input` after a prefix `buf` it waits on holds the
/// stream up to [`first`]'s decision, and decides as [`first`] says.
pub proof fn lemma_feed_from(buf: Seq<u8>, input: Seq<u8>, protected: bool)
    requires
        crate::connection::framing_spec::wf_mode(buf, protected),
        crate::spec::read_record(buf, protected) is NeedMore,
    ensures ({
        let w = buf + input;
        let (st, k) = first(w, protected);
        &&& buf.len() <= k <= w.len()
        &&& (!(st is Pending) ==> buf.len() < k)
        &&& crate::connection::framing_spec::feed_mode(buf, input, protected)
            == (Feed { buffer: w.take(k as int), consumed: (k - buf.len()) as nat, status: st })
    }),
    decreases input.len(),
{
    let w = buf + input;
    let (st, k) = first(w, protected);
    assert(w.take(buf.len() as int) =~= buf);
    lemma_first(w, buf.len(), protected);
    if input.len() == 0 {
        crate::connection::framing_lemmas::lemma_feed_stops_mode(buf, input, protected);
        assert(w =~= buf);
        assert(w.take(k as int) =~= w);
    } else {
        crate::connection::framing_lemmas::lemma_feed_step_mode(buf, input, protected);
        let appended = buf.push(input[0]);
        assert(appended =~= w.take(buf.len() as int + 1));
        lemma_first(w, (buf.len() + 1) as nat, protected);
        match crate::spec::read_record(appended, protected) {
            Read::NeedMore => {
                lemma_need_more_wf(appended, protected);
                assert(appended + input.skip(1) =~= w);
                lemma_feed_from(appended, input.skip(1), protected);
            },
            Read::Fail(_) => {},
            Read::Done(_, _) => {
                crate::connection::framing_lemmas::lemma_one_byte_rest_empty_mode(buf, input[0], protected);
            },
        }
    }
}

/// How a run of the framer ends.
pub enum FrameEnd {
    /// It waits, holding these bytes (a prefix of one record).
    Pending(Seq<u8>),
    /// It failed with this alert.
    Failed(u8),
}

/// The records a run of the framer completes, in order, how it ends, and
/// how many input bytes it consumed.
pub struct Framed {
    /// The records taken, each whole, in order.
    pub records: Seq<Seq<u8>>,
    /// How the run ends.
    pub end: FrameEnd,
    /// Input bytes consumed.
    pub consumed: nat,
}

/// §5.1: the framer on the stream `w` from an empty buffer: every record it
/// completes, taken, then the framer again on the rest, until it waits or
/// fails. A function of the bytes alone.
pub open spec fn frames(w: Seq<u8>, protected: bool) -> Framed
    decreases w.len(),
{
    let (st, k) = first(w, protected);
    match st {
        Status::Pending => Framed { records: seq![], end: FrameEnd::Pending(w), consumed: w.len() },
        Status::Fail(a) => Framed { records: seq![], end: FrameEnd::Failed(a), consumed: k },
        Status::Complete => if 0 < k <= w.len() {
            let r = frames(w.skip(k as int), protected);
            Framed { records: seq![w.take(k as int)] + r.records, end: r.end, consumed: k + r.consumed }
        } else {
            // Not reached (`lemma_first`).
            Framed { records: seq![], end: FrameEnd::Pending(w), consumed: w.len() }
        },
    }
}

/// The framer's caller, on the chunks `chunk` then `chunks`: feed the chunk;
/// on a completed record, take it and feed the rest of the chunk; when the
/// chunk is used up, the next; stop at a failure (final in every layer).
/// `buf` is what the framer holds at the start.
pub open spec fn drive(buf: Seq<u8>, chunk: Seq<u8>, chunks: Seq<Seq<u8>>, protected: bool) -> Framed
    decreases chunks.len(), chunk.len(),
{
    let f = crate::connection::framing_spec::feed_mode(buf, chunk, protected);
    match f.status {
        Status::Pending => if chunks.len() == 0 {
            Framed { records: seq![], end: FrameEnd::Pending(f.buffer), consumed: f.consumed }
        } else {
            let r = drive(f.buffer, chunks[0], chunks.skip(1), protected);
            Framed { consumed: f.consumed + r.consumed, ..r }
        },
        Status::Fail(a) => Framed { records: seq![], end: FrameEnd::Failed(a), consumed: f.consumed },
        Status::Complete => if 0 < f.consumed <= chunk.len() {
            let r = drive(seq![], chunk.skip(f.consumed as int), chunks, protected);
            Framed { records: seq![f.buffer] + r.records, end: r.end, consumed: f.consumed + r.consumed }
        } else {
            // Not reached (`lemma_feed_from`).
            Framed { records: seq![f.buffer], end: FrameEnd::Pending(seq![]), consumed: f.consumed }
        },
    }
}

/// [`frames`] with `before` bytes already held by the framer.
pub open spec fn held(r: Framed, before: nat) -> Framed {
    Framed { consumed: (r.consumed - before) as nat, ..r }
}

/// **Chunking does not matter.** Driving the framer over `chunk` then
/// `chunks`, from a prefix `buf` it waits on, is [`frames`] of all the
/// bytes, `buf` included.
pub proof fn lemma_drive(buf: Seq<u8>, chunk: Seq<u8>, chunks: Seq<Seq<u8>>, protected: bool)
    requires
        crate::connection::framing_spec::wf_mode(buf, protected),
        crate::spec::read_record(buf, protected) is NeedMore,
    ensures
        frames(buf + chunk + super::ccs::flatten(chunks), protected).consumed >= buf.len(),
        drive(buf, chunk, chunks, protected)
            == held(frames(buf + chunk + super::ccs::flatten(chunks), protected), buf.len()),
    decreases chunks.len(), chunk.len(),
{
    hide(crate::connection::framing_spec::feed_mode);
    hide(first);
    let x = buf + chunk;
    let rest = super::ccs::flatten(chunks);
    let w = x + rest;
    lemma_feed_from(buf, chunk, protected);
    let (st, k) = first(x, protected);
    let f = crate::connection::framing_spec::feed_mode(buf, chunk, protected);
    match st {
        Status::Pending => {
            lemma_first(x, x.len(), protected);
            assert(x.take(k as int) =~= x);
            if chunks.len() == 0 {
                assert(rest =~= Seq::<u8>::empty());
                assert(w =~= x);
            } else {
                assert(x.take(x.len() as int) =~= x);
                lemma_need_more_wf(x, protected);
                lemma_drive(x, chunks[0], chunks.skip(1), protected);
                assert(x + chunks[0] + super::ccs::flatten(chunks.skip(1)) =~= w);
            }
        },
        Status::Fail(_) => {
            lemma_first_extend(x, rest, protected);
        },
        Status::Complete => {
            lemma_first_extend(x, rest, protected);
            lemma_empty(protected);
            let c = f.consumed;
            lemma_drive(seq![], chunk.skip(c as int), chunks, protected);
            assert(Seq::<u8>::empty() + chunk.skip(c as int) + rest =~= w.skip(k as int));
            assert(w.take(k as int) =~= x.take(k as int));
        },
    }
}

// ---------------------------------------------------------------------------
// The transcription's division of a stream into records.
// ---------------------------------------------------------------------------

/// How the transcription's division of a stream ends.
pub enum SplitEnd {
    /// No whole record is left: `receive_stream` returns these bytes as the
    /// incomplete last record.
    Partial(Seq<u8>),
    /// The next header's length is refused (`record_length_failure`).
    TooLong(ClientError),
}

/// The transcription's division of a stream.
pub struct Split {
    /// The whole records, in order.
    pub records: Seq<Seq<u8>>,
    /// How it ends.
    pub end: SplitEnd,
}

/// §5, §5.1, §5.2: how `connection::receive_stream` divides `w` into
/// records, with the protection of `c` and the read side open: the header
/// (`read_record_header`), its length (`record_length_failure`), then five
/// bytes and `length` more.
pub open spec fn split(c: Connection, w: Seq<u8>) -> Split
    decreases w.len(),
{
    match crate::transcription::record::read_record_header(w) {
        None => Split { records: seq![], end: SplitEnd::Partial(w) },
        Some(header) =>
            if crate::transcription::connection::record_length_failure(c, header) is Some {
                Split { records: seq![],
                    end: SplitEnd::TooLong(crate::transcription::connection::record_length_failure(c, header)->0) }
            } else if w.len() < 5 + header.length {
                Split { records: seq![], end: SplitEnd::Partial(w) }
            } else {
                let r = split(c, w.subrange((5 + header.length) as int, w.len() as int));
                Split { records: seq![w.subrange(0, (5 + header.length) as int)] + r.records, end: r.end }
            },
    }
}

/// The header's fields, on the transcription's side, for a stream of at
/// least five bytes.
pub proof fn lemma_t_header(w: Seq<u8>)
    requires w.len() >= 5,
    ensures
        crate::transcription::record::read_record_header(w) is Some,
        crate::transcription::record::read_record_header(w)->Some_0.content_type == w[0] as nat,
        crate::transcription::record::read_record_header(w)->Some_0.length == super::bootstrap::length(w),
{
    super::record::lemma_read_uint(w.subrange(3, 5), 2);
    assert(w.subrange(3, 5).take(2) =~= w.subrange(3, 5));
}

/// The protection a framer mode stands for: protected after the
/// ServerHello (§5.1: "Once record protection has started").
pub open spec fn mode_agrees(c: Connection, protected: bool) -> bool {
    (c.receive is Protected) == protected
}

/// Two faults in one record header, where each side names a different one:
/// a type the mode does not allow (the crate's step 1, checked first,
/// `unexpected_message`) and a length above 2^14 (the transcription's
/// `record_length_failure`, checked first, `record_overflow`). The bootstrap
/// and post-handshake theorems' `two_faults` for the header.
pub open spec fn header_two_faults(b: Seq<u8>, protected: bool) -> bool {
    let t = b[0];
    &&& !(if protected {
        t == crate::spec::CT_APPLICATION_DATA || t == crate::spec::CT_CHANGE_CIPHER_SPEC
    } else {
        t == crate::spec::CT_CHANGE_CIPHER_SPEC || t == crate::spec::CT_ALERT || t == crate::spec::CT_HANDSHAKE
    })
    &&& super::bootstrap::length(b) > crate::spec::MAX_PLAINTEXT
}

/// **The timing difference.** The crate rejects the record at the front of
/// `w` with `alert` from its five header bytes alone, before its body has
/// arrived (`read_record` steps 1 and 3: a type the mode does not allow, or
/// a length above the limit).
pub open spec fn early_reject(w: Seq<u8>, protected: bool, alert: u8) -> bool {
    &&& 5 <= w.len() < 5 + super::bootstrap::length(w)
    &&& crate::spec::read_record(w.take(5), protected) matches Read::Fail(e)
    &&& crate::spec::alert_of(e) == alert
}

/// When the transcription refuses a header's length and the crate rejects
/// the same header with `alert`: the alerts are the same, or
/// [`header_two_faults`] holds.
pub open spec fn too_long_agrees(end: SplitEnd, b: Seq<u8>, protected: bool, alert: u8) -> bool {
    end matches SplitEnd::TooLong(e) ==>
        crate::transcription::alerts::required_alert(e) == alert as nat || header_two_faults(b, protected)
}

/// How the crate's failure on the front of `w` and the transcription's
/// division of `w` agree: the record at the front is whole, the crate's
/// alert is the one it gives that whole record, and it is the
/// transcription's next record; or the record is not yet whole, the crate
/// decided on its header ([`early_reject`]), and the transcription waits
/// for the body. In both cases, if the transcription refuses the header's
/// length instead, [`too_long_agrees`].
pub open spec fn fail_agrees(c: Connection, w: Seq<u8>, protected: bool, alert: u8) -> bool {
    let t = split(c, w);
    let n = 5 + super::bootstrap::length(w);
    &&& w.len() >= 5
    &&& if w.len() >= n {
        &&& crate::spec::read_record(w.take(n as int), protected) matches Read::Fail(e)
        &&& crate::spec::alert_of(e) == alert
        &&& t.records.len() > 0 ==> t.records[0] == w.take(n as int)
        &&& t.records.len() == 0 ==> t.end is TooLong && too_long_agrees(t.end, w, protected, alert)
    } else {
        &&& early_reject(w, protected, alert)
        &&& t.records.len() == 0
        &&& (t.end == SplitEnd::Partial(w) || t.end is TooLong && too_long_agrees(t.end, w, protected, alert))
    }
}

/// The crate's framer and the transcription's division agree on `w` (see
/// the module documentation, item 2), record by record.
pub open spec fn framing_agrees(c: Connection, w: Seq<u8>, protected: bool) -> bool
    decreases w.len(),
{
    let (st, k) = first(w, protected);
    let t = split(c, w);
    match st {
        Status::Pending => t == Split { records: seq![], end: SplitEnd::Partial(w) },
        Status::Fail(a) => fail_agrees(c, w, protected, a),
        Status::Complete => {
            &&& 5 <= k <= w.len()
            &&& super::bootstrap::whole_record(w.take(k as int))
            &&& crate::spec::read_record(w.take(k as int), protected) is Done
            &&& t == Split { records: seq![w.take(k as int)] + split(c, w.skip(k as int)).records,
                end: split(c, w.skip(k as int)).end }
            &&& framing_agrees(c, w.skip(k as int), protected)
        },
    }
}

/// The crate's header checks pass exactly when its length is within the
/// limit and the type allowed; the transcription's length check is the
/// crate's limit for a type the crate allows.
pub proof fn lemma_header_checks(c: Connection, w: Seq<u8>, protected: bool)
    requires w.len() >= 5, mode_agrees(c, protected),
    ensures ({
        let header = crate::transcription::record::read_record_header(w)->Some_0;
        let failure = crate::transcription::connection::record_length_failure(c, header);
        &&& !(crate::spec::read_record(w.take(5), protected) is Fail) ==> failure is None
        &&& failure matches Some(e) ==> {
            &&& crate::spec::read_record(w.take(5), protected) matches Read::Fail(k)
            &&& (crate::transcription::alerts::required_alert(e) == crate::spec::alert_of(k) as nat
                || header_two_faults(w, protected))
        }
    }),
{
    reveal(crate::spec::read_record);
    lemma_t_header(w);
    let h = w.take(5);
    assert(h.subrange(3, 5) =~= w.subrange(3, 5));
}

/// **Item 2, one record at a time.**
pub proof fn lemma_framing_agrees(c: Connection, w: Seq<u8>, protected: bool)
    requires mode_agrees(c, protected),
    ensures framing_agrees(c, w, protected),
    decreases w.len(),
{
    let (st, k) = first(w, protected);
    lemma_first(w, w.len(), protected);
    if w.len() >= 5 {
        lemma_t_header(w);
        lemma_header_checks(c, w, protected);
        let n = 5 + super::bootstrap::length(w);
        if w.len() >= n {
            assert(w.take(n as int).subrange(3, 5) =~= w.subrange(3, 5));
            assert(w.take(n as int).take(5) =~= w.take(5));
            assert(w.subrange(0, n as int) =~= w.take(n as int));
            assert(w.subrange(n as int, w.len() as int) =~= w.skip(n as int));
        }
        if w.len() >= n && crate::spec::read_record(w.take(5), protected) is Fail {
            assert(w.take(n as int) =~= w.take(5) + w.subrange(5, n as int));
            lemma_read_extend(w.take(5), w.subrange(5, n as int), protected);
        }
        reveal(crate::spec::read_record);
        match st {
            Status::Complete => {
                lemma_framing_agrees(c, w.skip(k as int), protected);
            },
            _ => {},
        }
    }
}

/// **Item 3: every completion of an early-rejected header is rejected by
/// both sides**: by the crate with the same alert; by the transcription
/// (with the read side open, in the mode's protection) with that alert, or
/// [`header_two_faults`] holds. The transcription meanwhile waits on the
/// partial record, unless it refuses the header's length.
pub proof fn lemma_early_reject(p: Primitives, c: Connection, w: Seq<u8>, protected: bool, alert: u8, b: Seq<u8>)
    requires
        early_reject(w, protected, alert),
        mode_agrees(c, protected),
        !c.read_closed,
        super::bootstrap::whole_record(b),
        b.take(5) == w.take(5),
    ensures
        crate::spec::read_record(b, protected) matches Read::Fail(e) && crate::spec::alert_of(e) == alert,
        super::bootstrap::one_record(p, c, b) matches Receive::Abort(e)
            && (crate::transcription::alerts::required_alert(e) == alert as nat || header_two_faults(b, protected)),
        split(c, w).records.len() == 0,
        split(c, w).end == SplitEnd::Partial(w)
            || split(c, w).end is TooLong && too_long_agrees(split(c, w).end, w, protected, alert),
{
    reveal(crate::spec::read_record);
    let h = w.take(5);
    assert(b.take(5).subrange(3, 5) =~= b.subrange(3, 5));
    assert(h.subrange(3, 5) =~= w.subrange(3, 5));
    assert(b.subrange(3, 5) == w.subrange(3, 5));
    assert(b[0] == b.take(5)[0]);
    assert(w[0] == h[0]);
    lemma_header_checks(c, w, protected);
    lemma_header_checks(c, b, protected);
    lemma_t_header(w);
    lemma_t_header(b);
    super::bootstrap::lemma_header(b);
}

// ---------------------------------------------------------------------------
// Item 1 and 2: the framer-level theorem.
// ---------------------------------------------------------------------------

/// **The framer theorem.** For every stream cut into any chunks (`chunk`
/// then `chunks`), the framer's caller ([`drive`]) gives [`frames`] of the
/// concatenated bytes; and for every connection in the framer's
/// protection, [`frames`] agrees with the transcription's division of
/// those bytes ([`framing_agrees`]). For every header the crate rejects
/// before its body has arrived ([`early_reject`]), every completion of it is
/// rejected by both ([`lemma_early_reject`]).
pub proof fn theorem_framing_equivalence(p: Primitives)
    ensures
        forall|chunk: Seq<u8>, chunks: Seq<Seq<u8>>, protected: bool|
            #[trigger] drive(seq![], chunk, chunks, protected) == frames(chunk + super::ccs::flatten(chunks), protected),
        forall|c: Connection, w: Seq<u8>, protected: bool|
            mode_agrees(c, protected) ==> #[trigger] framing_agrees(c, w, protected),
        forall|c: Connection, w: Seq<u8>, protected: bool, alert: u8, b: Seq<u8>| #![trigger early_reject(w, protected, alert), super::bootstrap::one_record(p, c, b)]
            early_reject(w, protected, alert) && mode_agrees(c, protected) && !c.read_closed
                && super::bootstrap::whole_record(b) && b.take(5) == w.take(5) ==> {
                &&& crate::spec::read_record(b, protected) matches Read::Fail(e) && crate::spec::alert_of(e) == alert
                &&& super::bootstrap::one_record(p, c, b) matches Receive::Abort(e)
                    && (crate::transcription::alerts::required_alert(e) == alert as nat
                        || header_two_faults(b, protected))
            },
{
    assert forall|chunk: Seq<u8>, chunks: Seq<Seq<u8>>, protected: bool|
        #[trigger] drive(seq![], chunk, chunks, protected) == frames(chunk + super::ccs::flatten(chunks), protected) by {
        lemma_empty(protected);
        lemma_drive(seq![], chunk, chunks, protected);
        assert(Seq::<u8>::empty() + chunk + super::ccs::flatten(chunks) =~= chunk + super::ccs::flatten(chunks));
    }
    assert forall|c: Connection, w: Seq<u8>, protected: bool|
        mode_agrees(c, protected) implies #[trigger] framing_agrees(c, w, protected) by {
        lemma_framing_agrees(c, w, protected);
    }
    assert forall|c: Connection, w: Seq<u8>, protected: bool, alert: u8, b: Seq<u8>| #![trigger early_reject(w, protected, alert), super::bootstrap::one_record(p, c, b)]
        early_reject(w, protected, alert) && mode_agrees(c, protected) && !c.read_closed
            && super::bootstrap::whole_record(b) && b.take(5) == w.take(5) implies {
            &&& crate::spec::read_record(b, protected) matches Read::Fail(e) && crate::spec::alert_of(e) == alert
            &&& super::bootstrap::one_record(p, c, b) matches Receive::Abort(e)
                && (crate::transcription::alerts::required_alert(e) == alert as nat
                    || header_two_faults(b, protected))
        } by {
        lemma_early_reject(p, c, w, protected, alert, b);
    }
}

// ---------------------------------------------------------------------------
// The transcription's stream, record by record.
// ---------------------------------------------------------------------------

/// §5: on a stream with no whole record, `receive_stream` waits (the bytes
/// are its incomplete last record) or refuses the header's length, as
/// [`split`] says.
pub proof fn lemma_stream_partial(p: Primitives, c: Connection, w: Seq<u8>)
    requires !c.read_closed, split(c, w).records.len() == 0,
    ensures
        crate::transcription::connection::receive_stream(p, c, w).0 == match split(c, w).end {
            SplitEnd::Partial(_) => Receive::Continue(Progress { connection: c, application_data: seq![],
                records_to_send: seq![] }),
            SplitEnd::TooLong(e) => Receive::Abort(e),
        },
{
}

/// §5: the transcription's client reads a stream that starts with a whole
/// record `b` as `b`, then the rest from where `b` left it
/// (`post_handshake::joined`), with D.4's dummy record
/// (`dispatcher::lifted`).
pub proof fn lemma_client_prefix(p: Primitives, cl: crate::transcription::middlebox::ClientConnection,
    b: Seq<u8>, rest: Seq<u8>)
    requires super::bootstrap::whole_record(b), !cl.connection.read_closed,
    ensures
        crate::transcription::middlebox::client_receive_stream(p, cl, b + rest).0
            == super::dispatcher::lifted(cl, super::post_handshake::joined(
                super::bootstrap::one_record(p, cl.connection, b),
                |c2: Connection| crate::transcription::connection::receive_stream(p, c2, rest).0)),
{
    super::post_handshake::lemma_stream_prefix(p, cl.connection, b, rest);
    super::bootstrap::lemma_stream_one(p, cl.connection, b);
}

/// A record that changes nothing but the connection, and writes and
/// delivers nothing, leaves the rest of the stream to the connection after
/// it.
pub proof fn lemma_client_continue(p: Primitives, cl: crate::transcription::middlebox::ClientConnection,
    c2: Connection, rest: Seq<u8>)
    ensures
        super::dispatcher::lifted(cl, super::post_handshake::joined(
            Receive::Continue(Progress { connection: c2, application_data: seq![], records_to_send: seq![] }),
            |c3: Connection| crate::transcription::connection::receive_stream(p, c3, rest).0))
        == crate::transcription::middlebox::client_receive_stream(p,
            crate::transcription::middlebox::ClientConnection { connection: c2, ..cl }, rest).0,
{
    match crate::transcription::connection::receive_stream(p, c2, rest).0 {
        Receive::Continue(two) => {
            assert(Seq::<u8>::empty() + two.application_data =~= two.application_data);
            assert(Seq::<Seq<u8>>::empty() + two.records_to_send =~= two.records_to_send);
        },
        _ => {},
    }
}

/// `lifted` of a result that writes nothing keeps the client as it is but
/// for the connection.
pub proof fn lemma_lifted_quiet(cl: crate::transcription::middlebox::ClientConnection, c2: Connection)
    ensures
        super::dispatcher::lifted(cl, Receive::Continue(Progress { connection: c2, application_data: seq![],
            records_to_send: seq![] }))
        == (crate::transcription::middlebox::ClientReceive::Continue {
            client: crate::transcription::middlebox::ClientConnection { connection: c2, ..cl },
            application_data: seq![], records_to_send: seq![] }),
{
}

// ---------------------------------------------------------------------------
// The bootstrap (`hello/bootstrap_spec.rs`) on a stream.
// ---------------------------------------------------------------------------

/// What a run of the bootstrap's `feed` leaves: its last action, the state,
/// the framer's bytes and the input consumed.
pub struct BootRun {
    /// The last action (`None`: it waits for more bytes).
    pub action: crate::hello::bootstrap_spec::Action,
    /// The bootstrap after the run.
    pub state: crate::hello::bootstrap_spec::State,
    /// The bytes the framer holds.
    pub framing: Seq<u8>,
    /// Input bytes consumed.
    pub consumed: nat,
}

/// Whether the bootstrap's caller feeds it more: the last call had no
/// effect, and it still waits for the server's Hello.
pub open spec fn boot_goes_on(s: crate::hello::bootstrap_spec::State,
    a: crate::hello::bootstrap_spec::Action) -> bool
{
    a is None && s.mode == crate::hello::bootstrap_spec::Mode::AwaitServerHello
}

/// The bootstrap's caller, on the chunks `chunk` then `chunks`: `feed` the
/// chunk, and again on what it did not consume, while [`boot_goes_on`];
/// when the chunk is used up, the next. Any other action is the caller's to
/// handle (send and acknowledge, hand over, or end), with the unconsumed
/// bytes kept (`bootstrap_spec::feed`: "Caller-owned suffix bytes remain
/// unconsumed").
pub open spec fn boot_drive(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: crate::hello::bootstrap_spec::State,
    framing: Seq<u8>, chunk: Seq<u8>, chunks: Seq<Seq<u8>>) -> BootRun
    decreases chunks.len(), chunk.len(),
{
    let f = crate::hello::bootstrap_spec::feed(hash, s, framing, chunk);
    let stop = BootRun { action: f.action, state: f.state, framing: f.framing, consumed: f.consumed };
    if boot_goes_on(f.state, f.action) {
        if 0 < f.consumed < chunk.len() {
            let r = boot_drive(hash, f.state, f.framing, chunk.skip(f.consumed as int), chunks);
            BootRun { consumed: f.consumed + r.consumed, ..r }
        } else if f.consumed == chunk.len() && chunks.len() > 0 {
            let r = boot_drive(hash, f.state, f.framing, chunks[0], chunks.skip(1));
            BootRun { consumed: f.consumed + r.consumed, ..r }
        } else {
            stop
        }
    } else {
        stop
    }
}

/// The bootstrap on the stream `w` from an empty framer: the whole-record
/// step (`bootstrap_lemmas::record_step`) on each record [`frames`]
/// completes, in order, while [`boot_goes_on`]; the framer's failure; or
/// it waits, holding the partial record.
pub open spec fn boot_steps(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: crate::hello::bootstrap_spec::State,
    w: Seq<u8>) -> BootRun
    decreases w.len(),
{
    let (st, k) = first(w, false);
    match st {
        Status::Pending => BootRun { action: crate::hello::bootstrap_spec::Action::None, state: s,
            framing: w, consumed: w.len() },
        Status::Fail(a) => BootRun { action: crate::hello::bootstrap_spec::Action::Fail(a),
            state: crate::hello::bootstrap_lemmas::terminal(s, crate::hello::bootstrap_spec::Mode::Failed,
                s.reassembly),
            framing: w.take(k as int), consumed: k },
        Status::Complete => {
            let (s2, a) = crate::hello::bootstrap_lemmas::record_step(hash, s, w.take(k as int));
            if boot_goes_on(s2, a) && 0 < k <= w.len() {
                let r = boot_steps(hash, s2, w.skip(k as int));
                BootRun { consumed: k + r.consumed, ..r }
            } else {
                BootRun { action: a, state: s2, framing: seq![], consumed: k }
            }
        },
    }
}

/// [`boot_steps`] with `before` bytes already held by the framer.
pub open spec fn boot_held(r: BootRun, before: nat) -> BootRun {
    BootRun { consumed: (r.consumed - before) as nat, ..r }
}

/// The bootstrap's `feed` from a framer holding `buf`, as [`first`]
/// decides on the bytes it holds and the chunk.
pub proof fn lemma_boot_feed(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: crate::hello::bootstrap_spec::State,
    buf: Seq<u8>, chunk: Seq<u8>)
    requires
        s.mode == crate::hello::bootstrap_spec::Mode::AwaitServerHello,
        crate::connection::framing_spec::wf_mode(buf, false),
        crate::spec::read_record(buf, false) is NeedMore,
    ensures ({
        let x = buf + chunk;
        let (st, k) = first(x, false);
        &&& buf.len() <= k <= x.len()
        &&& (st is Pending ==> k == x.len())
        &&& (!(st is Pending) ==> buf.len() < k)
        &&& crate::hello::bootstrap_spec::feed(hash, s, buf, chunk) == match st {
            Status::Pending => crate::hello::bootstrap_spec::Feed { consumed: chunk.len(), state: s, framing: x,
                action: crate::hello::bootstrap_spec::Action::None },
            Status::Fail(a) => crate::hello::bootstrap_spec::Feed { consumed: (k - buf.len()) as nat,
                state: crate::hello::bootstrap_lemmas::terminal(s, crate::hello::bootstrap_spec::Mode::Failed,
                    s.reassembly),
                framing: x.take(k as int), action: crate::hello::bootstrap_spec::Action::Fail(a) },
            Status::Complete => crate::hello::bootstrap_spec::Feed { consumed: (k - buf.len()) as nat,
                state: crate::hello::bootstrap_lemmas::record_step(hash, s, x.take(k as int)).0, framing: seq![],
                action: crate::hello::bootstrap_lemmas::record_step(hash, s, x.take(k as int)).1 },
        }
    }),
{
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(crate::hello::bootstrap_spec::receive);
    let x = buf + chunk;
    lemma_feed_from(buf, chunk, false);
    lemma_first(x, x.len(), false);
    let (st, k) = first(x, false);
    match st {
        Status::Pending => {
            assert(x.take(k as int) =~= x);
        },
        Status::Complete => {
            crate::hello::bootstrap_lemmas::lemma_feed_complete(hash, s, buf, chunk);
        },
        _ => {},
    }
}

/// **Chunking does not matter for the bootstrap.** Its caller over `chunk`
/// then `chunks`, from a framer holding `buf`, is [`boot_steps`] of all the
/// bytes.
pub proof fn lemma_boot_drive(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: crate::hello::bootstrap_spec::State,
    buf: Seq<u8>, chunk: Seq<u8>, chunks: Seq<Seq<u8>>)
    requires
        s.mode == crate::hello::bootstrap_spec::Mode::AwaitServerHello,
        crate::connection::framing_spec::wf_mode(buf, false),
        crate::spec::read_record(buf, false) is NeedMore,
    ensures
        boot_steps(hash, s, buf + chunk + super::ccs::flatten(chunks)).consumed >= buf.len(),
        boot_drive(hash, s, buf, chunk, chunks)
            == boot_held(boot_steps(hash, s, buf + chunk + super::ccs::flatten(chunks)), buf.len()),
    decreases chunks.len(), chunk.len(),
{
    hide(crate::hello::bootstrap_spec::feed);
    hide(first);
    hide(crate::hello::bootstrap_lemmas::record_step);
    let x = buf + chunk;
    let rest = super::ccs::flatten(chunks);
    let w = x + rest;
    lemma_boot_feed(hash, s, buf, chunk);
    lemma_first(x, x.len(), false);
    let (st, k) = first(x, false);
    match st {
        Status::Pending => {
            assert(x.take(k as int) =~= x);
            if chunks.len() == 0 {
                assert(rest =~= Seq::<u8>::empty());
                assert(w =~= x);
            } else {
                assert(x.take(x.len() as int) =~= x);
                lemma_need_more_wf(x, false);
                lemma_boot_drive(hash, s, x, chunks[0], chunks.skip(1));
                assert(x + chunks[0] + super::ccs::flatten(chunks.skip(1)) =~= w);
            }
        },
        Status::Fail(_) => {
            lemma_first_extend(x, rest, false);
            assert(w.take(k as int) =~= x.take(k as int));
        },
        Status::Complete => {
            lemma_first_extend(x, rest, false);
            assert(w.take(k as int) =~= x.take(k as int));
            let (s2, a) = crate::hello::bootstrap_lemmas::record_step(hash, s, x.take(k as int));
            let c = (k - buf.len()) as nat;
            if boot_goes_on(s2, a) {
                lemma_empty(false);
                if c < chunk.len() {
                    lemma_boot_drive(hash, s2, seq![], chunk.skip(c as int), chunks);
                    assert(Seq::<u8>::empty() + chunk.skip(c as int) + rest =~= w.skip(k as int));
                } else if chunks.len() > 0 {
                    lemma_boot_drive(hash, s2, seq![], chunks[0], chunks.skip(1));
                    assert(Seq::<u8>::empty() + chunks[0] + super::ccs::flatten(chunks.skip(1)) =~= w.skip(k as int));
                } else {
                    assert(w.skip(k as int) =~= Seq::<u8>::empty());
                    reveal(first);
                    assert(first(w.skip(k as int), false).0 is Pending);
                }
            }
        },
    }
}

/// The transcription's client after records that changed only the bytes of
/// an unfinished handshake message: `cl` with those bytes.
pub open spec fn with_fragments(cl: crate::transcription::middlebox::ClientConnection, buf: Seq<u8>)
    -> crate::transcription::middlebox::ClientConnection
{
    crate::transcription::middlebox::ClientConnection {
        connection: Connection { handshake_fragments: buf, ..cl.connection },
        ..cl
    }
}

/// The bootstrap and the transcription's client (`client_receive_stream`)
/// agree on the stream `w`, record by record, along [`boot_steps`]:
/// - the crate waits on a partial record: the transcription writes,
///   delivers and changes nothing;
/// - the crate's framer fails on a whole record: the whole-record theorem
///   (`bootstrap::record_agrees`) holds of it, the crate's step on it is
///   that failure, and the transcription reads the stream as that record,
///   then the rest;
/// - the crate's framer fails on a partial record ([`early_reject`]): the
///   transcription waits (and every completion is rejected by both,
///   [`lemma_early_reject`]), or refuses the header's length
///   ([`too_long_agrees`]);
/// - the crate completes a record: `bootstrap::record_agrees` holds of it,
///   and the transcription reads the stream as that record then the rest;
///   if the crate goes on, the two states agree again
///   (`bootstrap::bootstrap_agrees`) and the transcription's result is its
///   result on the rest, from there.
pub open spec fn boot_stream_agrees(p: Primitives, s: crate::hello::bootstrap_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, w: Seq<u8>) -> bool
    decreases w.len(),
{
    let (st, k) = first(w, false);
    let c = cl.connection;
    let u = crate::transcription::middlebox::client_receive_stream(p, cl, w).0;
    let n = 5 + super::bootstrap::length(w);
    let quiet = crate::transcription::middlebox::ClientReceive::Continue { client: cl,
        application_data: seq![], records_to_send: seq![] };
    match st {
        Status::Pending => u == quiet,
        Status::Fail(a) => if w.len() >= n {
            let b = w.take(n as int);
            &&& super::bootstrap::whole_record(b)
            &&& super::bootstrap::record_agrees(p, s, cl, b)
            &&& crate::hello::bootstrap_lemmas::record_step(p.hash, s, b)
                == (crate::hello::bootstrap_lemmas::terminal(s, crate::hello::bootstrap_spec::Mode::Failed,
                    s.reassembly), crate::hello::bootstrap_spec::Action::Fail(a))
            &&& u == super::dispatcher::lifted(cl, super::post_handshake::joined(
                super::bootstrap::one_record(p, c, b),
                |c2: Connection| crate::transcription::connection::receive_stream(p, c2, w.skip(n as int)).0))
        } else {
            &&& early_reject(w, false, a)
            &&& (u == quiet || (u matches crate::transcription::middlebox::ClientReceive::Abort(e)
                && too_long_agrees(SplitEnd::TooLong(e), w, false, a)))
        },
        Status::Complete => {
            let b = w.take(k as int);
            let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b);
            let cl2 = with_fragments(cl, s2.reassembly.buf);
            &&& super::bootstrap::whole_record(b)
            &&& super::bootstrap::record_agrees(p, s, cl, b)
            &&& u == super::dispatcher::lifted(cl, super::post_handshake::joined(
                super::bootstrap::one_record(p, c, b),
                |c2: Connection| crate::transcription::connection::receive_stream(p, c2, w.skip(k as int)).0))
            &&& boot_goes_on(s2, a) ==> {
                &&& super::bootstrap::bootstrap_agrees(p, s2, cl2)
                &&& u == crate::transcription::middlebox::client_receive_stream(p, cl2, w.skip(k as int)).0
                &&& boot_stream_agrees(p, s2, cl2, w.skip(k as int))
            }
        },
    }
}

/// [`bootstrap::record_agrees`] for every whole record, from agreeing
/// states (the bootstrap theorem's second part).
pub proof fn lemma_boot_record(p: Primitives, s: crate::hello::bootstrap_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, b: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        super::bootstrap::bootstrap_agrees(p, s, cl),
        super::bootstrap::whole_record(b),
    ensures super::bootstrap::record_agrees(p, s, cl, b),
{
    if super::bootstrap::handshake_record(b) {
        super::bootstrap::lemma_handshake_record(p, s, cl, b);
    } else {
        super::bootstrap::lemma_other_record(p, s, cl, b);
    }
}

/// When the crate goes on after a whole record, the transcription's result
/// on it is "go on, with these fragments" (from `record_agrees`).
pub proof fn lemma_boot_quiet(p: Primitives, s: crate::hello::bootstrap_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, b: Seq<u8>)
    requires
        super::bootstrap::record_agrees(p, s, cl, b),
        boot_goes_on(crate::hello::bootstrap_lemmas::record_step(p.hash, s, b).0,
            crate::hello::bootstrap_lemmas::record_step(p.hash, s, b).1),
    ensures ({
        let s2 = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b).0;
        let c2 = Connection { handshake_fragments: s2.reassembly.buf, ..cl.connection };
        &&& super::bootstrap::one_record(p, cl.connection, b)
            == Receive::Continue(Progress { connection: c2, application_data: seq![], records_to_send: seq![] })
        &&& super::bootstrap::bootstrap_agrees(p, s2, with_fragments(cl, s2.reassembly.buf))
    }),
{
    let c = cl.connection;
    let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b);
    let c2 = Connection { handshake_fragments: s2.reassembly.buf, ..c };
    let t = super::bootstrap::one_record(p, c, b);
    if super::bootstrap::handshake_record(b) && crate::spec::extract_messages(super::bootstrap::buffer(s, b)) is Ok {
        let bf = super::bootstrap::buffer(s, b);
        assert(super::bootstrap::buffer_agrees(p, s, cl, bf));
    } else {
        match t {
            Receive::Continue(progress) => {
                let (records, sent) = crate::transcription::middlebox::before_second_flight(cl.compatibility_mode,
                    cl.change_cipher_spec_sent, progress.records_to_send);
                if progress.records_to_send.len() > 0 {
                    assert(records.len() > 0);
                }
                assert(progress.records_to_send =~= Seq::<Seq<u8>>::empty());
            },
            _ => {},
        }
    }
}

/// `client_receive_stream` is `lifted` of `receive_stream`.
pub proof fn lemma_client_lifted(p: Primitives, cl: crate::transcription::middlebox::ClientConnection, w: Seq<u8>)
    ensures
        crate::transcription::middlebox::client_receive_stream(p, cl, w).0
            == super::dispatcher::lifted(cl, crate::transcription::connection::receive_stream(p, cl.connection, w).0),
{
}

/// What [`lemma_boot_stream`] uses of `bootstrap::bootstrap_agrees`.
pub proof fn lemma_boot_agrees_facts(p: Primitives, s: crate::hello::bootstrap_spec::State,
    cl: crate::transcription::middlebox::ClientConnection)
    requires super::bootstrap::bootstrap_agrees(p, s, cl),
    ensures mode_agrees(cl.connection, false), !cl.connection.read_closed,
        s.mode == crate::hello::bootstrap_spec::Mode::AwaitServerHello,
{
}

/// The bootstrap's step on a whole record its framer refuses.
pub proof fn lemma_record_step_fail(hash: spec_fn(Seq<u8>) -> Seq<u8>, s: crate::hello::bootstrap_spec::State,
    b: Seq<u8>, e: crate::spec::ErrKind)
    requires crate::spec::read_record(b, false) == Read::<crate::spec::Frame>::Fail(e),
    ensures crate::hello::bootstrap_lemmas::record_step(hash, s, b)
        == (crate::hello::bootstrap_lemmas::terminal(s, crate::hello::bootstrap_spec::Mode::Failed, s.reassembly),
            crate::hello::bootstrap_spec::Action::Fail(crate::spec::alert_of(e))),
{
}

/// The bootstrap's stream on a record its framer completes.
pub proof fn lemma_boot_stream_complete(p: Primitives, s: crate::hello::bootstrap_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, w: Seq<u8>, k: nat)
    requires
        super::transcript::hash_is_32(p.hash),
        super::bootstrap::bootstrap_agrees(p, s, cl),
        5 <= k <= w.len(),
        super::bootstrap::whole_record(w.take(k as int)),
    ensures ({
        let b = w.take(k as int);
        let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b);
        let cl2 = with_fragments(cl, s2.reassembly.buf);
        let u = crate::transcription::middlebox::client_receive_stream(p, cl, w).0;
        &&& super::bootstrap::record_agrees(p, s, cl, b)
        &&& u == super::dispatcher::lifted(cl, super::post_handshake::joined(
            super::bootstrap::one_record(p, cl.connection, b),
            |c2: Connection| crate::transcription::connection::receive_stream(p, c2, w.skip(k as int)).0))
        &&& boot_goes_on(s2, a) ==> {
            &&& super::bootstrap::bootstrap_agrees(p, s2, cl2)
            &&& u == crate::transcription::middlebox::client_receive_stream(p, cl2, w.skip(k as int)).0
        }
    }),
{
    hide(super::bootstrap::record_agrees);
    hide(super::bootstrap::bootstrap_agrees);
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(super::bootstrap::one_record);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(crate::transcription::connection::receive_stream);
    hide(super::dispatcher::lifted);
    let c = cl.connection;
    let b = w.take(k as int);
    lemma_boot_agrees_facts(p, s, cl);
    lemma_boot_record(p, s, cl, b);
    assert(b + w.skip(k as int) =~= w);
    lemma_client_prefix(p, cl, b, w.skip(k as int));
    let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, b);
    if boot_goes_on(s2, a) {
        lemma_boot_quiet(p, s, cl, b);
        let c2 = Connection { handshake_fragments: s2.reassembly.buf, ..c };
        lemma_client_continue(p, cl, c2, w.skip(k as int));
    }
}

/// **The bootstrap on a stream** ([`boot_stream_agrees`]), from agreeing
/// states, for every stream.
pub proof fn lemma_boot_stream(p: Primitives, s: crate::hello::bootstrap_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, w: Seq<u8>)
    requires
        super::transcript::hash_is_32(p.hash),
        super::bootstrap::bootstrap_agrees(p, s, cl),
    ensures boot_stream_agrees(p, s, cl, w),
    decreases w.len(),
{
    hide(super::bootstrap::record_agrees);
    hide(super::bootstrap::bootstrap_agrees);
    hide(crate::hello::bootstrap_lemmas::record_step);
    hide(super::bootstrap::one_record);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(crate::transcription::connection::receive_stream);
    hide(split);
    let c = cl.connection;
    let (st, k) = first(w, false);
    let n = 5 + super::bootstrap::length(w);
    lemma_boot_agrees_facts(p, s, cl);
    lemma_first(w, w.len(), false);
    lemma_framing_agrees(c, w, false);
    lemma_client_lifted(p, cl, w);
    match st {
        Status::Pending => {
            lemma_stream_partial(p, c, w);
            lemma_lifted_quiet(cl, c);
            assert(crate::transcription::middlebox::ClientConnection { connection: c, ..cl } == cl);
        },
        Status::Fail(a) => {
            if w.len() >= n {
                let b = w.take(n as int);
                assert(b.subrange(3, 5) =~= w.subrange(3, 5));
                let e = crate::spec::read_record(b, false)->Fail_0;
                lemma_record_step_fail(p.hash, s, b, e);
                lemma_boot_stream_complete(p, s, cl, w, n);
            } else {
                lemma_stream_partial(p, c, w);
                lemma_lifted_quiet(cl, c);
                assert(crate::transcription::middlebox::ClientConnection { connection: c, ..cl } == cl);
            }
        },
        Status::Complete => {
            lemma_boot_stream_complete(p, s, cl, w, k);
            let (s2, a) = crate::hello::bootstrap_lemmas::record_step(p.hash, s, w.take(k as int));
            if boot_goes_on(s2, a) {
                lemma_boot_stream(p, s2, with_fragments(cl, s2.reassembly.buf), w.skip(k as int));
            }
        },
    }
}

/// **The bootstrap theorem, for streams.** From agreeing states
/// (`bootstrap::bootstrap_agrees`) and an empty framer, for every stream
/// cut into any chunks, the bootstrap's caller ([`boot_drive`]) is
/// [`boot_steps`] of the concatenated bytes: the whole-record step on each
/// record its framer completes, in order; and along those records, the
/// crate and the transcription's `client_receive_stream` of the same bytes
/// agree ([`boot_stream_agrees`]).
pub proof fn theorem_boot_stream(p: Primitives)
    requires super::transcript::hash_is_32(p.hash),
    ensures
        forall|s: crate::hello::bootstrap_spec::State, cl: crate::transcription::middlebox::ClientConnection,
            chunk: Seq<u8>, chunks: Seq<Seq<u8>>|
            #[trigger] super::bootstrap::bootstrap_agrees(p, s, cl) ==> {
                &&& #[trigger] boot_drive(p.hash, s, seq![], chunk, chunks)
                    == boot_steps(p.hash, s, chunk + super::ccs::flatten(chunks))
                &&& boot_stream_agrees(p, s, cl, chunk + super::ccs::flatten(chunks))
            },
{
    assert forall|s: crate::hello::bootstrap_spec::State, cl: crate::transcription::middlebox::ClientConnection,
        chunk: Seq<u8>, chunks: Seq<Seq<u8>>|
        #[trigger] super::bootstrap::bootstrap_agrees(p, s, cl) implies {
            &&& #[trigger] boot_drive(p.hash, s, seq![], chunk, chunks)
                == boot_steps(p.hash, s, chunk + super::ccs::flatten(chunks))
            &&& boot_stream_agrees(p, s, cl, chunk + super::ccs::flatten(chunks))
        } by {
        lemma_empty(false);
        lemma_boot_drive(p.hash, s, seq![], chunk, chunks);
        assert(Seq::<u8>::empty() + chunk + super::ccs::flatten(chunks) =~= chunk + super::ccs::flatten(chunks));
        lemma_boot_stream(p, s, cl, chunk + super::ccs::flatten(chunks));
    }
}

// ---------------------------------------------------------------------------
// The dispatcher (`connection/dispatcher_spec.rs`) on a stream.
// ---------------------------------------------------------------------------

/// A record's messages leave the framer as they found it, empty.
pub proof fn lemma_run_messages_framing(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State,
    messages: Seq<Seq<u8>>)
    requires s.framing.len() == 0,
    ensures crate::connection::dispatcher_spec::run_messages(c, v, f, s, messages).1.framing.len() == 0,
    decreases messages.len(),
{
    hide(crate::auth::spec::step);
    if messages.len() > 0 {
        let (action, after) = crate::connection::dispatcher_spec::process_one(c, v, f, s, messages[0]);
        if action is None {
            lemma_run_messages_framing(c, v, f, after, messages.skip(1));
        }
    }
}

/// A record's content leaves the framer as it found it, empty.
pub proof fn lemma_receive_plaintext_framing(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State, typ: u8,
    bytes: Seq<u8>)
    requires s.framing.len() == 0,
    ensures crate::connection::dispatcher_spec::receive_plaintext(c, v, f, s, typ, bytes).1.framing.len() == 0,
{
    hide(crate::connection::dispatcher_spec::run_messages);
    if bytes.len() <= crate::spec::MAX_PLAINTEXT {
        match crate::spec::feed_record(s.reassembly, crate::spec::Record { ctype: typ, fragment: bytes }) {
            crate::spec::Res::Ok((crate::spec::Event::Messages(messages), reassembly)) => {
                lemma_run_messages_framing(c, v, f, crate::connection::dispatcher_spec::State { reassembly, ..s },
                    messages);
            },
            _ => {},
        }
    }
}

/// `receive_record` from an empty framer leaves it empty.
pub proof fn lemma_receive_record_framing(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State, b: Seq<u8>)
    requires s.framing.len() == 0,
    ensures crate::connection::dispatcher_spec::receive_record(c, v, f, s, b).1.framing.len() == 0,
{
    hide(crate::connection::dispatcher_spec::receive_plaintext);
    match crate::spec::read_record(b, true) {
        crate::spec::Read::Done(crate::spec::Frame::Protected(_, _), _) => {
            if s.handshake_receiver is Some {
                let rx = s.handshake_receiver->Some_0;
                let (epoch, read) = crate::traffic::spec::receive(
                    crate::connection::dispatcher_spec::open_with(f, rx), rx, b);
                let opened = crate::connection::dispatcher_spec::State { handshake_receiver: Some(epoch), ..s };
                if read is Record {
                    lemma_receive_plaintext_framing(c, v, f, opened, read->Record_0, read->Record_1);
                }
            }
        },
        _ => {},
    }
}

/// A fatal alert does not depend on the framer's bytes.
pub proof fn lemma_fatal_framing(f: crate::connection::dispatcher_spec::Ciphers,
    s: crate::connection::dispatcher_spec::State, x: Seq<u8>, alert: u8)
    ensures crate::connection::dispatcher_spec::fatal(f, crate::connection::dispatcher_spec::State { framing: x, ..s }, alert)
        == crate::connection::dispatcher_spec::fatal(f, s, alert),
{
}

/// The dispatcher's `feed` from a framer holding `s.framing`, as [`first`]
/// decides on the bytes it holds and the chunk; `s0` is `s` with the
/// framer emptied.
pub proof fn lemma_disp_feed(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State, chunk: Seq<u8>)
    requires
        s.mode == crate::connection::dispatcher_spec::Mode::Handshake,
        crate::connection::framing_spec::wf_mode(s.framing, true),
        crate::spec::read_record(s.framing, true) is NeedMore,
    ensures ({
        let x = s.framing + chunk;
        let (st, k) = first(x, true);
        let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
        &&& s.framing.len() <= k <= x.len()
        &&& (st is Pending ==> k == x.len())
        &&& (!(st is Pending) ==> s.framing.len() < k)
        &&& crate::connection::dispatcher_spec::feed(c, v, f, s, chunk) == match st {
            Status::Pending => (chunk.len(), crate::connection::dispatcher_spec::Action::None,
                crate::connection::dispatcher_spec::State { framing: x, ..s }),
            Status::Fail(a) => ((k - s.framing.len()) as nat, crate::connection::dispatcher_spec::fatal(f, s0, a).0,
                crate::connection::dispatcher_spec::fatal(f, s0, a).1),
            Status::Complete => ((k - s.framing.len()) as nat,
                crate::connection::dispatcher_spec::receive_record(c, v, f, s0, x.take(k as int)).0,
                crate::connection::dispatcher_spec::receive_record(c, v, f, s0, x.take(k as int)).1),
        }
    }),
{
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(crate::connection::dispatcher_spec::fatal);
    let x = s.framing + chunk;
    lemma_feed_from(s.framing, chunk, true);
    lemma_first(x, x.len(), true);
    let (st, k) = first(x, true);
    if st is Pending {
        assert(x.take(k as int) =~= x);
    }
    if st is Fail {
        lemma_fatal_framing(f, crate::connection::dispatcher_spec::State { framing: seq![], ..s }, s.framing,
            st->Fail_0);
        assert(crate::connection::dispatcher_spec::State { framing: s.framing,
            ..crate::connection::dispatcher_spec::State { framing: seq![], ..s } } == s);
    }
}

/// What a run of the dispatcher's `feed` gives: its actions other than
/// `None`, in order, the state, and the input consumed.
pub struct DispRun {
    /// Actions other than `None`, in order.
    pub actions: Seq<crate::connection::dispatcher_spec::Action>,
    /// The dispatcher after the run (its framer holds a partial record).
    pub state: crate::connection::dispatcher_spec::State,
    /// Input bytes consumed.
    pub consumed: nat,
}

/// Whether the dispatcher's caller feeds it more: it is still reading the
/// server's flight and the last call asked nothing of the caller (no
/// effect, a dropped change_cipher_spec, a user_canceled).
pub open spec fn disp_goes_on(s: crate::connection::dispatcher_spec::State,
    a: crate::connection::dispatcher_spec::Action) -> bool
{
    &&& s.mode == crate::connection::dispatcher_spec::Mode::Handshake
    &&& (a is None || a is Ignored || a is Cancelled)
}

/// `a` as a list of actions the caller sees: none for `None`.
pub open spec fn shown(a: crate::connection::dispatcher_spec::Action) -> Seq<crate::connection::dispatcher_spec::Action> {
    if a is None { seq![] } else { seq![a] }
}

/// The dispatcher's caller, on the chunks `chunk` then `chunks`: `feed` the
/// chunk, and again on what it did not consume, while [`disp_goes_on`];
/// when the chunk is used up, the next. Any other action is the caller's to
/// handle (`dispatcher_spec`: "unconsumed suffix bytes remain caller
/// owned").
pub open spec fn disp_drive(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State, chunk: Seq<u8>,
    chunks: Seq<Seq<u8>>) -> DispRun
    decreases chunks.len(), chunk.len(),
{
    let (n, a, s2) = crate::connection::dispatcher_spec::feed(c, v, f, s, chunk);
    let stop = DispRun { actions: shown(a), state: s2, consumed: n };
    if disp_goes_on(s2, a) {
        if 0 < n < chunk.len() {
            let r = disp_drive(c, v, f, s2, chunk.skip(n as int), chunks);
            DispRun { actions: shown(a) + r.actions, state: r.state, consumed: n + r.consumed }
        } else if n == chunk.len() && chunks.len() > 0 {
            let r = disp_drive(c, v, f, s2, chunks[0], chunks.skip(1));
            DispRun { actions: shown(a) + r.actions, state: r.state, consumed: n + r.consumed }
        } else {
            stop
        }
    } else {
        stop
    }
}

/// The dispatcher on the stream `w` from an empty framer: its whole-record
/// step (`dispatcher_spec::receive_record`) on each record [`frames`]
/// completes, in order, while [`disp_goes_on`]; the framer's failure
/// (`fatal`); or it waits, its framer holding the partial record.
pub open spec fn disp_steps(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State, w: Seq<u8>) -> DispRun
    decreases w.len(),
{
    let (st, k) = first(w, true);
    match st {
        Status::Pending => DispRun { actions: seq![],
            state: crate::connection::dispatcher_spec::State { framing: w, ..s }, consumed: w.len() },
        Status::Fail(a) => DispRun { actions: seq![crate::connection::dispatcher_spec::fatal(f, s, a).0],
            state: crate::connection::dispatcher_spec::fatal(f, s, a).1, consumed: k },
        Status::Complete => {
            let (a, s2) = crate::connection::dispatcher_spec::receive_record(c, v, f, s, w.take(k as int));
            if disp_goes_on(s2, a) && 0 < k <= w.len() {
                let r = disp_steps(c, v, f, s2, w.skip(k as int));
                DispRun { actions: shown(a) + r.actions, state: r.state, consumed: k + r.consumed }
            } else {
                DispRun { actions: shown(a), state: s2, consumed: k }
            }
        },
    }
}

/// [`disp_steps`] with `before` bytes already held by the framer.
pub open spec fn disp_held(r: DispRun, before: nat) -> DispRun {
    DispRun { consumed: (r.consumed - before) as nat, ..r }
}

/// **Chunking does not matter for the dispatcher.** Its caller over `chunk`
/// then `chunks`, from a framer holding `s.framing`, is [`disp_steps`] of
/// all the bytes from an empty framer.
pub proof fn lemma_disp_drive(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, s: crate::connection::dispatcher_spec::State, chunk: Seq<u8>,
    chunks: Seq<Seq<u8>>)
    requires
        s.mode == crate::connection::dispatcher_spec::Mode::Handshake,
        crate::connection::framing_spec::wf_mode(s.framing, true),
        crate::spec::read_record(s.framing, true) is NeedMore,
    ensures ({
        let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
        let w = s.framing + chunk + super::ccs::flatten(chunks);
        &&& disp_steps(c, v, f, s0, w).consumed >= s.framing.len()
        &&& disp_drive(c, v, f, s, chunk, chunks) == disp_held(disp_steps(c, v, f, s0, w), s.framing.len())
    }),
    decreases chunks.len(), chunk.len(),
{
    hide(crate::connection::dispatcher_spec::feed);
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(crate::connection::dispatcher_spec::fatal);
    hide(first);
    let buf = s.framing;
    let s0 = crate::connection::dispatcher_spec::State { framing: seq![], ..s };
    let x = buf + chunk;
    let rest = super::ccs::flatten(chunks);
    let w = x + rest;
    lemma_disp_feed(c, v, f, s, chunk);
    lemma_first(x, x.len(), true);
    let (st, k) = first(x, true);
    match st {
        Status::Pending => {
            assert(x.take(k as int) =~= x);
            let s1 = crate::connection::dispatcher_spec::State { framing: x, ..s };
            assert(crate::connection::dispatcher_spec::State { framing: seq![], ..s1 } == s0);
            assert(crate::connection::dispatcher_spec::State { framing: w, ..s0 }
                == crate::connection::dispatcher_spec::State { framing: w, ..s });
            if chunks.len() == 0 {
                assert(rest =~= Seq::<u8>::empty());
                assert(w =~= x);
            } else {
                assert(x.take(x.len() as int) =~= x);
                lemma_need_more_wf(x, true);
                lemma_disp_drive(c, v, f, s1, chunks[0], chunks.skip(1));
                assert(x + chunks[0] + super::ccs::flatten(chunks.skip(1)) =~= w);
            }
        },
        Status::Fail(_) => {
            lemma_first_extend(x, rest, true);
            reveal(crate::connection::dispatcher_spec::fatal);
        },
        Status::Complete => {
            lemma_first_extend(x, rest, true);
            assert(w.take(k as int) =~= x.take(k as int));
            let (a, s2) = crate::connection::dispatcher_spec::receive_record(c, v, f, s0, x.take(k as int));
            let n = (k - buf.len()) as nat;
            if disp_goes_on(s2, a) {
                lemma_receive_record_framing(c, v, f, s0, x.take(k as int));
                assert(s2.framing =~= Seq::<u8>::empty());
                assert(crate::connection::dispatcher_spec::State { framing: seq![], ..s2 } == s2);
                lemma_empty(true);
                if n < chunk.len() {
                    lemma_disp_drive(c, v, f, s2, chunk.skip(n as int), chunks);
                    assert(Seq::<u8>::empty() + chunk.skip(n as int) + rest =~= w.skip(k as int));
                    assert(s2.framing + chunk.skip(n as int) + rest =~= w.skip(k as int));
                } else if chunks.len() > 0 {
                    lemma_disp_drive(c, v, f, s2, chunks[0], chunks.skip(1));
                    assert(s2.framing + chunks[0] + super::ccs::flatten(chunks.skip(1)) =~= w.skip(k as int));
                } else {
                    assert(w.skip(k as int) =~= Seq::<u8>::empty());
                    reveal(first);
                    assert(first(w.skip(k as int), false).0 is Pending);
                    assert(first(w.skip(k as int), true).0 is Pending);
                    assert(crate::connection::dispatcher_spec::State { framing: w.skip(k as int), ..s2 } == s2);
                    assert(shown(a) + Seq::<crate::connection::dispatcher_spec::Action>::empty() =~= shown(a));
                }
            }
        },
    }
}

/// The dispatcher and the transcription's client (`client_receive_stream`)
/// agree on the stream `w`, record by record, along [`disp_steps`] (as
/// [`boot_stream_agrees`] for the bootstrap): the crate waits on a partial
/// record and the transcription does nothing; the crate's framer fails on a
/// whole record, which is `receive_record`'s `fatal` and
/// `dispatcher::record_agrees`;
/// it fails on a partial record ([`early_reject`]) with the transcription's
/// `alert_record` of its alert, while the transcription waits or refuses
/// the header's length; it completes a record, and
/// `dispatcher::record_agrees` holds of it and, if the crate goes on, the
/// states agree again (`dispatcher::dispatcher_agrees`) and the
/// transcription's result is its result on the rest from there. In every
/// whole-record case the transcription reads the stream as that record,
/// then the rest.
pub open spec fn disp_stream_agrees(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, p: Primitives, s: crate::connection::dispatcher_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, w: Seq<u8>) -> bool
    decreases w.len(),
{
    let (st, k) = first(w, true);
    let y = cl.connection;
    let u = crate::transcription::middlebox::client_receive_stream(p, cl, w).0;
    let n = 5 + super::bootstrap::length(w);
    let quiet = crate::transcription::middlebox::ClientReceive::Continue { client: cl,
        application_data: seq![], records_to_send: seq![] };
    match st {
        Status::Pending => u == quiet,
        Status::Fail(a) => if w.len() >= n {
            let b = w.take(n as int);
            &&& super::bootstrap::whole_record(b)
            &&& crate::connection::dispatcher_spec::receive_record(c, v, f, s, b)
                == crate::connection::dispatcher_spec::fatal(f, s, a)
            &&& u == super::dispatcher::lifted(cl, super::post_handshake::joined(
                super::bootstrap::one_record(p, y, b),
                |c2: Connection| crate::transcription::connection::receive_stream(p, c2, w.skip(n as int)).0))
            &&& super::dispatcher::record_agrees(c, v, f, p, s, cl, b)
        } else {
            &&& early_reject(w, true, a)
            &&& crate::connection::dispatcher_spec::fatal(f, s, a)
                == (crate::connection::dispatcher_spec::Action::Fail(a,
                    Some(crate::transcription::connection::alert_record(p, y, a as nat))),
                    crate::connection::dispatcher_spec::failed())
            &&& (u == quiet || (u matches crate::transcription::middlebox::ClientReceive::Abort(e)
                && too_long_agrees(SplitEnd::TooLong(e), w, true, a)))
        },
        Status::Complete => {
            let b = w.take(k as int);
            let (a, s2) = crate::connection::dispatcher_spec::receive_record(c, v, f, s, b);
            let t = super::bootstrap::one_record(p, y, b);
            let cl2 = crate::transcription::middlebox::ClientConnection { connection: t->Continue_0.connection, ..cl };
            &&& super::bootstrap::whole_record(b)
            &&& u == super::dispatcher::lifted(cl, super::post_handshake::joined(t,
                |c2: Connection| crate::transcription::connection::receive_stream(p, c2, w.skip(k as int)).0))
            &&& super::dispatcher::record_agrees(c, v, f, p, s, cl, b)
            &&& disp_goes_on(s2, a) ==> {
                &&& super::dispatcher::dispatcher_agrees(p, v, s2, cl2)
                &&& u == crate::transcription::middlebox::client_receive_stream(p, cl2, w.skip(k as int)).0
                &&& disp_stream_agrees(c, v, f, p, s2, cl2, w.skip(k as int))
            }
        },
    }
}

/// A record whose result writes and delivers nothing leaves the rest of the
/// stream to the connection after it.
pub proof fn lemma_client_continue_progress(p: Primitives, cl: crate::transcription::middlebox::ClientConnection,
    pr: Progress, rest: Seq<u8>)
    requires pr.application_data.len() == 0, pr.records_to_send.len() == 0,
    ensures
        super::dispatcher::lifted(cl, super::post_handshake::joined(Receive::Continue(pr),
            |c3: Connection| crate::transcription::connection::receive_stream(p, c3, rest).0))
        == crate::transcription::middlebox::client_receive_stream(p,
            crate::transcription::middlebox::ClientConnection { connection: pr.connection, ..cl }, rest).0,
{
    assert(pr.application_data =~= Seq::<u8>::empty());
    assert(pr.records_to_send =~= Seq::<Seq<u8>>::empty());
    assert(pr == Progress { connection: pr.connection, application_data: seq![], records_to_send: seq![] });
    lemma_client_continue(p, cl, pr.connection, rest);
}

/// An early rejection's alert is `unexpected_message` or `record_overflow`.
pub proof fn lemma_early_alert(w: Seq<u8>, alert: u8)
    requires early_reject(w, true, alert) || early_reject(w, false, alert),
    ensures alert != 0, alert != 90,
{
    reveal(crate::spec::read_record);
}

/// The transcription's client on a stream with no whole record: it waits,
/// changing nothing, or refuses the header's length.
pub proof fn lemma_client_partial(p: Primitives, cl: crate::transcription::middlebox::ClientConnection, w: Seq<u8>)
    requires !cl.connection.read_closed, split(cl.connection, w).records.len() == 0,
    ensures
        crate::transcription::middlebox::client_receive_stream(p, cl, w).0 == match split(cl.connection, w).end {
            SplitEnd::Partial(_) => crate::transcription::middlebox::ClientReceive::Continue { client: cl,
                application_data: seq![], records_to_send: seq![] },
            SplitEnd::TooLong(e) => crate::transcription::middlebox::ClientReceive::Abort(e),
        },
{
    lemma_stream_partial(p, cl.connection, w);
    lemma_client_lifted(p, cl, w);
    assert(crate::transcription::middlebox::ClientConnection { connection: cl.connection, ..cl } == cl);
}

/// What [`lemma_disp_stream`] uses of `dispatcher::dispatcher_agrees`.
pub proof fn lemma_disp_agrees_facts(p: Primitives, v: crate::auth::spec::Verification,
    s: crate::connection::dispatcher_spec::State, cl: crate::transcription::middlebox::ClientConnection)
    requires super::dispatcher::dispatcher_agrees(p, v, s, cl),
    ensures
        mode_agrees(cl.connection, true),
        !cl.connection.read_closed,
        s.mode == crate::connection::dispatcher_spec::Mode::Handshake,
        s.framing.len() == 0,
        super::dispatcher::sender_fresh(p, s, cl.connection),
        super::auth::phase_is(s.auth->Some_0.phase, cl.connection.handshake.state),
{
}

/// When the dispatcher goes on after a record, the transcription's result
/// writes and delivers nothing, and the states agree again (from
/// `dispatcher::outcome_agrees`).
pub proof fn lemma_disp_quiet(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, p: Primitives, s: crate::connection::dispatcher_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, a: crate::connection::dispatcher_spec::Action,
    s2: crate::connection::dispatcher_spec::State, t: Receive)
    requires
        super::dispatcher::outcome_agrees(c, v, f, p, s, cl, a, s2, t, true),
        disp_goes_on(s2, a),
    ensures
        t is Continue,
        t->Continue_0.application_data.len() == 0,
        t->Continue_0.records_to_send.len() == 0,
        super::dispatcher::dispatcher_agrees(p, v, s2,
            crate::transcription::middlebox::ClientConnection { connection: t->Continue_0.connection, ..cl }),
{
    hide(super::dispatcher::dispatcher_agrees);
}

/// The dispatcher's stream on a whole record at the front of `w`.
pub proof fn lemma_disp_stream_whole(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, p: Primitives, s: crate::connection::dispatcher_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, w: Seq<u8>, k: nat)
    requires
        super::dispatcher::hypotheses(c, v, f, p),
        super::dispatcher::dispatcher_agrees(p, v, s, cl),
        5 <= k <= w.len(),
        super::bootstrap::whole_record(w.take(k as int)),
    ensures ({
        let b = w.take(k as int);
        let (a, s2) = crate::connection::dispatcher_spec::receive_record(c, v, f, s, b);
        let t = super::bootstrap::one_record(p, cl.connection, b);
        let cl2 = crate::transcription::middlebox::ClientConnection { connection: t->Continue_0.connection, ..cl };
        let u = crate::transcription::middlebox::client_receive_stream(p, cl, w).0;
        &&& u == super::dispatcher::lifted(cl, super::post_handshake::joined(t,
            |c2: Connection| crate::transcription::connection::receive_stream(p, c2, w.skip(k as int)).0))
        &&& super::dispatcher::record_agrees(c, v, f, p, s, cl, b)
        &&& disp_goes_on(s2, a) ==> {
            &&& super::dispatcher::dispatcher_agrees(p, v, s2, cl2)
            &&& u == crate::transcription::middlebox::client_receive_stream(p, cl2, w.skip(k as int)).0
        }
    }),
{
    hide(super::dispatcher::record_agrees);
    hide(super::dispatcher::dispatcher_agrees);
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(super::bootstrap::one_record);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(crate::transcription::connection::receive_stream);
    hide(super::dispatcher::lifted);
    hide(super::dispatcher::hypotheses);
    hide(super::dispatcher::outcome_agrees);
    hide(super::post_handshake::joined);
    let b = w.take(k as int);
    lemma_disp_agrees_facts(p, v, s, cl);
    assert(b + w.skip(k as int) =~= w);
    lemma_client_prefix(p, cl, b, w.skip(k as int));
    super::dispatcher::lemma_receive(c, v, f, p, s, cl, b);
    let (a, s2) = crate::connection::dispatcher_spec::receive_record(c, v, f, s, b);
    if disp_goes_on(s2, a) {
        let t = super::bootstrap::one_record(p, cl.connection, b);
        assert(super::dispatcher::outcome_agrees(c, v, f, p, s, cl, a, s2, t, true)) by {
            reveal(super::dispatcher::record_agrees);
        }
        lemma_disp_quiet(c, v, f, p, s, cl, a, s2, t);
        lemma_client_continue_progress(p, cl, t->Continue_0, w.skip(k as int));
    }
}

/// **The dispatcher on a stream** ([`disp_stream_agrees`]), from agreeing
/// states, for every stream.
pub proof fn lemma_disp_stream(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, p: Primitives, s: crate::connection::dispatcher_spec::State,
    cl: crate::transcription::middlebox::ClientConnection, w: Seq<u8>)
    requires
        super::dispatcher::hypotheses(c, v, f, p),
        super::dispatcher::dispatcher_agrees(p, v, s, cl),
    ensures disp_stream_agrees(c, v, f, p, s, cl, w),
    decreases w.len(),
{
    hide(super::dispatcher::record_agrees);
    hide(super::dispatcher::dispatcher_agrees);
    hide(crate::connection::dispatcher_spec::receive_record);
    hide(super::bootstrap::one_record);
    hide(crate::transcription::middlebox::client_receive_stream);
    hide(crate::transcription::connection::receive_stream);
    hide(split);
    hide(super::dispatcher::lifted);
    hide(super::dispatcher::hypotheses);
    hide(super::post_handshake::joined);
    hide(crate::connection::dispatcher_spec::fatal);
    hide(too_long_agrees);
    let y = cl.connection;
    let (st, k) = first(w, true);
    let n = 5 + super::bootstrap::length(w);
    lemma_disp_agrees_facts(p, v, s, cl);
    lemma_first(w, w.len(), true);
    lemma_framing_agrees(y, w, true);
    match st {
        Status::Pending => {
            lemma_client_partial(p, cl, w);
        },
        Status::Fail(a) => {
            if w.len() >= n {
                let b = w.take(n as int);
                assert(b.subrange(3, 5) =~= w.subrange(3, 5));
                reveal(crate::connection::dispatcher_spec::receive_record);
                lemma_disp_stream_whole(c, v, f, p, s, cl, w, n);
            } else {
                lemma_client_partial(p, cl, w);
                lemma_early_alert(w, a);
                assert(super::dispatcher::ciphers_agree(f, p)) by { reveal(super::dispatcher::hypotheses); }
                super::dispatcher::lemma_fatal(f, p, s, y, a);
            }
        },
        Status::Complete => {
            lemma_disp_stream_whole(c, v, f, p, s, cl, w, k);
            let (a, s2) = crate::connection::dispatcher_spec::receive_record(c, v, f, s, w.take(k as int));
            let t = super::bootstrap::one_record(p, y, w.take(k as int));
            if disp_goes_on(s2, a) {
                lemma_disp_stream(c, v, f, p, s2,
                    crate::transcription::middlebox::ClientConnection { connection: t->Continue_0.connection, ..cl },
                    w.skip(k as int));
            }
        },
    }
}

/// **The dispatcher theorem, for streams.** From agreeing states
/// (`dispatcher::dispatcher_agrees`, whose framer is empty), for every
/// stream cut into any chunks, the dispatcher's caller ([`disp_drive`]) is
/// [`disp_steps`] of the concatenated bytes: `receive_record` on each record
/// its framer completes, in order; and along those records the crate and
/// the transcription's `client_receive_stream` of the same bytes agree
/// ([`disp_stream_agrees`], at every record).
pub proof fn theorem_disp_stream(c: crate::schedule::spec::Crypto, v: crate::auth::spec::Verification,
    f: crate::connection::dispatcher_spec::Ciphers, p: Primitives)
    requires super::dispatcher::hypotheses(c, v, f, p),
    ensures
        forall|s: crate::connection::dispatcher_spec::State, cl: crate::transcription::middlebox::ClientConnection,
            chunk: Seq<u8>, chunks: Seq<Seq<u8>>|
            #[trigger] super::dispatcher::dispatcher_agrees(p, v, s, cl) ==> {
                &&& #[trigger] disp_drive(c, v, f, s, chunk, chunks)
                    == disp_steps(c, v, f, s, chunk + super::ccs::flatten(chunks))
                &&& disp_stream_agrees(c, v, f, p, s, cl, chunk + super::ccs::flatten(chunks))
            },
{
    assert forall|s: crate::connection::dispatcher_spec::State, cl: crate::transcription::middlebox::ClientConnection,
        chunk: Seq<u8>, chunks: Seq<Seq<u8>>|
        #[trigger] super::dispatcher::dispatcher_agrees(p, v, s, cl) implies {
            &&& #[trigger] disp_drive(c, v, f, s, chunk, chunks)
                == disp_steps(c, v, f, s, chunk + super::ccs::flatten(chunks))
            &&& disp_stream_agrees(c, v, f, p, s, cl, chunk + super::ccs::flatten(chunks))
        } by {
        lemma_disp_agrees_facts(p, v, s, cl);
        assert(s.framing =~= Seq::<u8>::empty());
        assert(crate::connection::dispatcher_spec::State { framing: seq![], ..s } == s);
        lemma_empty(true);
        lemma_disp_drive(c, v, f, s, chunk, chunks);
        assert(s.framing + chunk + super::ccs::flatten(chunks) =~= chunk + super::ccs::flatten(chunks));
        lemma_disp_stream(c, v, f, p, s, cl, chunk + super::ccs::flatten(chunks));
    }
}

// ---------------------------------------------------------------------------
// The post-handshake transducer (`connection/post_handshake_spec.rs`) on a
// stream.
// ---------------------------------------------------------------------------

/// The transducer's step waits: it consumed nothing and ended nothing
/// (modelling choice 1: "An incomplete record consumes nothing and changes
/// nothing").
pub open spec fn post_waits(r: (crate::connection::post_handshake_spec::Out,
    crate::connection::post_handshake_spec::State, nat)) -> bool
{
    r.2 == 0 && r.0.end is Continue
}

/// Whether the transducer's caller steps it again: the step ended nothing
/// and the read side is open.
pub open spec fn post_goes_on(r: (crate::connection::post_handshake_spec::Out,
    crate::connection::post_handshake_spec::State, nat)) -> bool
{
    r.0.end is Continue && crate::connection::post_handshake_spec::can_read(r.1)
}

/// What a run of the transducer gives: the outputs of its steps that did
/// not wait, in order, the state, and, if it stopped to wait for more
/// bytes, the bytes it holds.
pub struct PostRun {
    /// The outputs of the steps that read a record (or failed), in order.
    pub outs: Seq<crate::connection::post_handshake_spec::Out>,
    /// The transducer after the run.
    pub state: crate::connection::post_handshake_spec::State,
    /// `Some(bytes)`: it waits, and the caller holds `bytes`; `None`: it
    /// stopped on an output that ends the connection or its read side.
    pub waiting: Option<Seq<u8>>,
}

/// The transducer's caller, holding `buf` and then given `chunks`: `step`
/// on what it holds; when the step waits, append the next chunk; when it
/// reads a record, drop the bytes it consumed and step again while
/// [`post_goes_on`] (modelling choice 1: "The caller resubmits the rest").
pub open spec fn post_drive(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, buf: Seq<u8>, chunks: Seq<Seq<u8>>) -> PostRun
    decreases chunks.len(), buf.len(),
{
    let r = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(buf));
    if post_waits(r) {
        if chunks.len() == 0 {
            PostRun { outs: seq![], state: s, waiting: Some(buf) }
        } else {
            post_drive(c, f, s, buf + chunks[0], chunks.skip(1))
        }
    } else if post_goes_on(r) && 0 < r.2 <= buf.len() {
        let x = post_drive(c, f, r.1, buf.skip(r.2 as int), chunks);
        PostRun { outs: seq![r.0] + x.outs, ..x }
    } else {
        PostRun { outs: seq![r.0], state: r.1, waiting: None }
    }
}

/// The transducer on the stream `w`: `step` on the stream, then on what it
/// did not consume, while [`post_goes_on`].
pub open spec fn post_steps(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, w: Seq<u8>) -> PostRun
    decreases w.len(),
{
    let r = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(w));
    if post_waits(r) {
        PostRun { outs: seq![], state: s, waiting: Some(w) }
    } else if post_goes_on(r) && 0 < r.2 <= w.len() {
        let x = post_steps(c, f, r.1, w.skip(r.2 as int));
        PostRun { outs: seq![r.0] + x.outs, ..x }
    } else {
        PostRun { outs: seq![r.0], state: r.1, waiting: None }
    }
}

/// A step that does not wait decides as it would on any longer stream: the
/// same output and state, and, if it goes on, the same record consumed.
pub proof fn lemma_post_step_extend(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, b: Seq<u8>, more: Seq<u8>)
    requires
        crate::connection::post_handshake_spec::can_read(s),
        !post_waits(crate::connection::post_handshake_spec::step(c, f, s,
            crate::connection::post_handshake_spec::Input::Bytes(b))),
    ensures ({
        let r0 = crate::connection::post_handshake_spec::step(c, f, s,
            crate::connection::post_handshake_spec::Input::Bytes(b));
        let r1 = crate::connection::post_handshake_spec::step(c, f, s,
            crate::connection::post_handshake_spec::Input::Bytes(b + more));
        &&& r1.0 == r0.0
        &&& r1.1 == r0.1
        &&& r0.0.end is Continue ==> r1.2 == r0.2 && 0 < r0.2 <= b.len()
    }),
{
    hide(crate::connection::post_handshake_spec::record);
    let r0 = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(b));
    let r1 = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(b + more));
    if s.receiver is Some {
        let rx = s.receiver->Some_0;
        let open = crate::connection::post_handshake_spec::open_of(f, rx);
        if !rx.failed && rx.next is Some {
            match crate::spec::read_record(b, true) {
                Read::NeedMore => {
                    assert(r0.2 == 0);
                    assert(r0.0.end is Continue);
                },
                Read::Fail(_) => {
                    lemma_read_extend(b, more, true);
                    assert(crate::traffic::spec::receive(open, rx, b) == crate::traffic::spec::receive(open, rx, b + more));
                },
                Read::Done(_, rest) => {
                    lemma_read_extend(b, more, true);
                    lemma_done_rest(b, true);
                    assert((b + more).len() - (rest + more).len() == b.len() - rest.len());
                    assert(crate::traffic::spec::receive(open, rx, b).0 == crate::traffic::spec::receive(open, rx, b + more).0);
                    assert(crate::traffic::spec::receive(open, rx, b).1 == crate::traffic::spec::receive(open, rx, b + more).1);
                },
            }
        }
    }
}

/// A record read off `b` leaves fewer bytes than `b` (its header at least).
pub proof fn lemma_done_rest(b: Seq<u8>, protected: bool)
    requires crate::spec::read_record(b, protected) is Done,
    ensures crate::spec::read_record(b, protected)->Done_1.len() + 5 <= b.len(),
{
    reveal(crate::spec::read_record);
}

/// **Chunking does not matter for the transducer.** Its caller, holding
/// `buf` and given `chunks`, is [`post_steps`] of all the bytes.
pub proof fn lemma_post_drive(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher,
    s: crate::connection::post_handshake_spec::State, buf: Seq<u8>, chunks: Seq<Seq<u8>>)
    requires crate::connection::post_handshake_spec::can_read(s),
    ensures post_drive(c, f, s, buf, chunks) == post_steps(c, f, s, buf + super::ccs::flatten(chunks)),
    decreases chunks.len(), buf.len(),
{
    hide(crate::connection::post_handshake_spec::step);
    let w = buf + super::ccs::flatten(chunks);
    let r = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(buf));
    if post_waits(r) {
        if chunks.len() == 0 {
            assert(w =~= buf);
        } else {
            lemma_post_drive(c, f, s, buf + chunks[0], chunks.skip(1));
            assert(buf + chunks[0] + super::ccs::flatten(chunks.skip(1)) =~= w);
        }
    } else {
        lemma_post_step_extend(c, f, s, buf, super::ccs::flatten(chunks));
        if post_goes_on(r) {
            lemma_post_drive(c, f, r.1, buf.skip(r.2 as int), chunks);
            assert(buf.skip(r.2 as int) + super::ccs::flatten(chunks) =~= w.skip(r.2 as int));
        }
    }
}

/// The transducer and the transcription on a stream `w` with a whole record
/// `b` at its front: the step on `w` is the step on `b` (output and state),
/// the whole-record theorem (`post_handshake::record_agrees`) holds of `b`,
/// and the transcription reads `w` as `b`, then the rest
/// (`post_handshake::joined`); if the crate goes on, it consumed exactly
/// `b` and the transcription went on too, and, unless the transcription now
/// owes a KeyUpdate (the `settle` difference: the crate sent its answer in
/// that step), the crate sent nothing and the states agree again
/// (`post_agrees`).
pub open spec fn post_whole_agrees(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: crate::connection::post_handshake_spec::State, conn: Connection, w: Seq<u8>) -> bool
{
    let n = 5 + super::bootstrap::length(w);
    let r = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(w));
    let b = w.take(n as int);
    let rb = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(b));
    let tb = crate::transcription::connection::receive_stream(p, conn, b).0;
    &&& super::bootstrap::whole_record(b)
    &&& r.0 == rb.0
    &&& r.1 == rb.1
    &&& super::post_handshake::record_agrees(p, f, s, conn, b, rb, tb)
    &&& crate::transcription::connection::receive_stream(p, conn, w).0 == super::post_handshake::joined(tb,
        |c2: Connection| crate::transcription::connection::receive_stream(p, c2, w.skip(n as int)).0)
    &&& post_goes_on(r) ==> {
        &&& r.2 == n
        &&& tb is Continue
        &&& !tb->Continue_0.connection.key_update_owed ==> {
            &&& r.0.wires.len() == 0
            &&& super::post_handshake::post_agrees(r.1, tb->Continue_0.connection)
        }
    }
}

/// The transducer and the transcription on a stream `w` with no whole
/// record at its front: the crate waits and the transcription does
/// nothing; or the crate fails, with the transcription's `alert_record` of
/// its alert while it can write, because its epoch is exhausted
/// (`post_handshake::exhausted`: it refuses before reading any byte,
/// `internal_error`; the transcription waits or refuses the header) or
/// because it rejected the header early ([`early_reject`]; the
/// transcription waits or refuses the header's length,
/// [`too_long_agrees`]).
pub open spec fn post_partial_agrees(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: crate::connection::post_handshake_spec::State, conn: Connection, w: Seq<u8>) -> bool
{
    let r = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(w));
    let tr = crate::transcription::connection::receive_stream(p, conn, w).0;
    let quiet_t = Receive::Continue(Progress { connection: conn, application_data: seq![], records_to_send: seq![] });
    if post_waits(r) {
        &&& r.0 == crate::connection::post_handshake_spec::quiet()
        &&& r.1 == s
        &&& tr == quiet_t
    } else {
        let a = r.0.end->Fail_0;
        &&& r.0.end is Fail
        &&& r.0 == (crate::connection::post_handshake_spec::Out { wires: super::post_handshake::alert_wires(p, s, conn, a),
            delivered: seq![], end: crate::connection::post_handshake_spec::End::Fail(a) })
        &&& r.1 == crate::connection::post_handshake_spec::failed()
        &&& ((super::post_handshake::exhausted(s) && a == crate::spec::INTERNAL_ERROR && (tr == quiet_t || tr is Abort))
            || (early_reject(w, true, a) && (tr == quiet_t
                || (tr matches Receive::Abort(e) && too_long_agrees(SplitEnd::TooLong(e), w, true, a)))))
    }
}

/// The transducer and the transcription's `receive_stream` agree on the
/// stream `w`, along [`post_steps`]: [`post_whole_agrees`] when a whole
/// record is at its front, and then, when the crate goes on and the
/// transcription owes no KeyUpdate, again on the rest from the agreeing
/// states; [`post_partial_agrees`] when none is.
pub open spec fn post_stream_agrees(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: crate::connection::post_handshake_spec::State, conn: Connection, w: Seq<u8>) -> bool
    decreases w.len(),
{
    let n = 5 + super::bootstrap::length(w);
    if w.len() >= 5 && w.len() >= n {
        let r = crate::connection::post_handshake_spec::step(c, f, s,
            crate::connection::post_handshake_spec::Input::Bytes(w));
        let tb = crate::transcription::connection::receive_stream(p, conn, w.take(n as int)).0;
        &&& post_whole_agrees(c, f, p, s, conn, w)
        &&& (post_goes_on(r) && !tb->Continue_0.connection.key_update_owed) ==>
            post_stream_agrees(c, f, p, r.1, tb->Continue_0.connection, w.skip(n as int))
    } else {
        post_partial_agrees(c, f, p, s, conn, w)
    }
}

/// [`post_partial_agrees`].
#[verifier::rlimit(40)]
pub proof fn lemma_post_partial(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: crate::connection::post_handshake_spec::State, conn: Connection, w: Seq<u8>)
    requires
        super::post_handshake::hypotheses(c, f, p),
        super::post_handshake::post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_read(s),
        w.len() < 5 || w.len() < 5 + super::bootstrap::length(w),
    ensures post_partial_agrees(c, f, p, s, conn, w),
{
    hide(crate::connection::post_handshake_spec::record);
    hide(crate::connection::post_handshake_spec::fatal);
    hide(super::post_handshake::post_agrees);
    hide(super::post_handshake::alert_wires);
    hide(crate::transcription::connection::receive_stream);
    hide(split);
    hide(too_long_agrees);
    super::post_handshake::lemma_receive_open_facts(s, conn);
    lemma_first(w, w.len(), true);
    assert(w.take(w.len() as int) =~= w);
    lemma_framing_agrees(conn, w, true);
    lemma_stream_partial(p, conn, w);
    let rx = s.receiver->Some_0;
    assert(super::post_handshake::cipher_agrees(f, p)) by { reveal(super::post_handshake::hypotheses); }
    if rx.next is Some {
        let rr = crate::spec::read_record(w, true);
        if !(rr is NeedMore) {
            lemma_post_partial_fail(w);
            let e = rr->Fail_0;
            super::post_handshake::lemma_alert_of(e);
            super::post_handshake::lemma_fatal(f, p, s, conn, crate::spec::alert_of(e));
        }
    } else {
        super::post_handshake::lemma_fatal(f, p, s, conn, crate::spec::INTERNAL_ERROR);
    }
}

/// On a stream with no whole record at its front, the protected parser
/// waits or fails on the header, and then the crate rejected it early.
pub proof fn lemma_post_partial_fail(w: Seq<u8>)
    requires
        w.len() < 5 || w.len() < 5 + super::bootstrap::length(w),
        !(crate::spec::read_record(w, true) is NeedMore),
    ensures
        crate::spec::read_record(w, true) is Fail,
        early_reject(w, true, crate::spec::alert_of(crate::spec::read_record(w, true)->Fail_0)),
{
    reveal(crate::spec::read_record);
    assert(w.take(5).subrange(3, 5) =~= w.subrange(3, 5));
    assert(w.take(5)[0] == w[0]);
}

/// [`post_whole_agrees`].
pub proof fn lemma_post_whole(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: crate::connection::post_handshake_spec::State, conn: Connection, w: Seq<u8>)
    requires
        super::post_handshake::hypotheses(c, f, p),
        super::post_handshake::post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_read(s),
        w.len() >= 5,
        w.len() >= 5 + super::bootstrap::length(w),
    ensures post_whole_agrees(c, f, p, s, conn, w),
{
    hide(crate::connection::post_handshake_spec::step);
    hide(crate::transcription::connection::receive_stream);
    hide(super::post_handshake::post_agrees);
    hide(super::post_handshake::record_agrees);
    hide(super::post_handshake::hypotheses);
    let n = 5 + super::bootstrap::length(w);
    let b = w.take(n as int);
    assert(b.subrange(3, 5) =~= w.subrange(3, 5));
    assert(b + w.skip(n as int) =~= w);
    super::post_handshake::lemma_step_prefix(c, f, s, b, w.skip(n as int));
    super::post_handshake::lemma_stream_prefix(p, conn, b, w.skip(n as int));
    super::post_handshake::lemma_receive(c, f, p, s, conn, b);
    let r = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(w));
    let rb = crate::connection::post_handshake_spec::step(c, f, s,
        crate::connection::post_handshake_spec::Input::Bytes(b));
    let tb = crate::transcription::connection::receive_stream(p, conn, b).0;
    if post_goes_on(r) {
        assert(super::post_handshake::outcome_agrees(p, s, conn, rb.0, rb.1, tb, true) && rb.2 == b.len()) by {
            reveal(super::post_handshake::record_agrees);
        }
        lemma_post_quiet(p, s, conn, rb.0, rb.1, tb);
    }
}

/// When the transducer goes on after a record, the transcription went on
/// too; unless it owes a KeyUpdate, the crate sent nothing and the states
/// agree.
pub proof fn lemma_post_quiet(p: Primitives, s: crate::connection::post_handshake_spec::State, conn: Connection,
    o: crate::connection::post_handshake_spec::Out, s2: crate::connection::post_handshake_spec::State, t: Receive)
    requires
        super::post_handshake::outcome_agrees(p, s, conn, o, s2, t, true),
        o.end is Continue,
    ensures
        t is Continue,
        !t->Continue_0.connection.key_update_owed ==> {
            &&& o.wires.len() == 0
            &&& super::post_handshake::post_agrees(s2, t->Continue_0.connection)
        },
{
    hide(super::post_handshake::post_agrees);
}

/// **The transducer on a stream** ([`post_stream_agrees`]), from agreeing
/// states with the read side open, for every stream.
#[verifier::rlimit(40)]
pub proof fn lemma_post_stream(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives,
    s: crate::connection::post_handshake_spec::State, conn: Connection, w: Seq<u8>)
    requires
        super::post_handshake::hypotheses(c, f, p),
        super::post_handshake::post_agrees(s, conn),
        crate::connection::post_handshake_spec::can_read(s),
    ensures post_stream_agrees(c, f, p, s, conn, w),
    decreases w.len(),
{
    hide(crate::connection::post_handshake_spec::step);
    hide(crate::transcription::connection::receive_stream);
    hide(super::post_handshake::post_agrees);
    hide(super::post_handshake::hypotheses);
    hide(post_whole_agrees);
    hide(post_partial_agrees);
    let n = 5 + super::bootstrap::length(w);
    if w.len() >= 5 && w.len() >= n {
        lemma_post_whole(c, f, p, s, conn, w);
        let r = crate::connection::post_handshake_spec::step(c, f, s,
            crate::connection::post_handshake_spec::Input::Bytes(w));
        let tb = crate::transcription::connection::receive_stream(p, conn, w.take(n as int)).0;
        if post_goes_on(r) && !tb->Continue_0.connection.key_update_owed {
            assert(super::post_handshake::post_agrees(r.1, tb->Continue_0.connection)) by {
                reveal(post_whole_agrees);
            }
            lemma_post_stream(c, f, p, r.1, tb->Continue_0.connection, w.skip(n as int));
        }
    } else {
        lemma_post_partial(c, f, p, s, conn, w);
    }
}

/// **The post-handshake theorem, for streams.** From agreeing states with
/// the read side open, for every stream cut into any chunks, the
/// transducer's caller ([`post_drive`]) is [`post_steps`] of the
/// concatenated bytes, and the transducer and the transcription's
/// `receive_stream` of the same bytes agree along it
/// ([`post_stream_agrees`]).
pub proof fn theorem_post_stream(c: crate::schedule::spec::Crypto, f: crate::traffic::spec::Cipher, p: Primitives)
    requires super::post_handshake::hypotheses(c, f, p),
    ensures
        forall|s: crate::connection::post_handshake_spec::State, conn: Connection, chunk: Seq<u8>,
            chunks: Seq<Seq<u8>>|
            #[trigger] super::post_handshake::post_agrees(s, conn) && crate::connection::post_handshake_spec::can_read(s)
                ==> {
                &&& #[trigger] post_drive(c, f, s, chunk, chunks)
                    == post_steps(c, f, s, chunk + super::ccs::flatten(chunks))
                &&& post_stream_agrees(c, f, p, s, conn, chunk + super::ccs::flatten(chunks))
            },
{
    assert forall|s: crate::connection::post_handshake_spec::State, conn: Connection, chunk: Seq<u8>,
        chunks: Seq<Seq<u8>>|
        #[trigger] super::post_handshake::post_agrees(s, conn) && crate::connection::post_handshake_spec::can_read(s)
            implies {
            &&& #[trigger] post_drive(c, f, s, chunk, chunks)
                == post_steps(c, f, s, chunk + super::ccs::flatten(chunks))
            &&& post_stream_agrees(c, f, p, s, conn, chunk + super::ccs::flatten(chunks))
        } by {
        lemma_post_drive(c, f, s, chunk, chunks);
        lemma_post_stream(c, f, p, s, conn, chunk + super::ccs::flatten(chunks));
    }
}

} // verus!

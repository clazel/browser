//! Supporting proofs for bounded one-record framing.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// A NeedMore result cannot fill the maximum protected record buffer.
pub proof fn lemma_need_more_bound(buffer: Seq<u8>)
    requires super::framing_spec::wf(buffer),
        crate::spec::read_record(buffer, true) is NeedMore,
    ensures buffer.len() < super::framing_spec::MAX_BUFFER,
{
    reveal(crate::spec::read_record);
}

/// Appending one byte to a NeedMore prefix cannot leave an unconsumed suffix.
pub proof fn lemma_one_byte_rest_empty(buffer: Seq<u8>, byte: u8)
    requires super::framing_spec::wf(buffer),
        crate::spec::read_record(buffer, true) is NeedMore,
    ensures match crate::spec::read_record(buffer.push(byte), true) {
        crate::spec::Read::Done(_, rest) => rest.len() == 0,
        _ => true,
    },
{
    reveal(crate::spec::read_record);
    let appended = buffer.push(byte);
    match crate::spec::read_record(buffer, true) {
        crate::spec::Read::NeedMore => {
            if buffer.len() < crate::spec::RECORD_HEADER {
                assert(appended.len() <= crate::spec::RECORD_HEADER);
            } else {
                let payload_len = crate::spec::be_value(buffer.subrange(3, 5));
                assert(buffer.len() < crate::spec::RECORD_HEADER + payload_len);
                assert(appended.len() == buffer.len() + 1);
                assert(appended.len() <= crate::spec::RECORD_HEADER + payload_len);
            }
            match crate::spec::read_record(appended, true) {
                crate::spec::Read::Done(_, rest) => {
                    reveal(crate::spec::read_record);
                    if buffer.len() < crate::spec::RECORD_HEADER {
                        let total = crate::spec::RECORD_HEADER
                            + crate::spec::be_value(appended.subrange(3, 5));
                        assert(appended.len() == crate::spec::RECORD_HEADER);
                        assert(total <= appended.len());
                        assert(appended.len() <= total);
                        assert(rest == appended.skip(total as int));
                        assert(rest.len() == 0);
                    } else {
                        let total = crate::spec::RECORD_HEADER
                            + crate::spec::be_value(appended.subrange(3, 5));
                        assert(appended.subrange(3, 5) =~= buffer.subrange(3, 5));
                        assert(total == crate::spec::RECORD_HEADER
                            + crate::spec::be_value(buffer.subrange(3, 5)));
                        assert(appended.len() >= total);
                        assert(appended.len() <= total);
                        assert(rest == appended.skip(total as int));
                        assert(rest.len() == 0);
                    }
                },
                _ => {},
            }
        },
        _ => assert(false),
    }
}

/// The pure feed step consumes its first byte when the parser remains pending.
pub proof fn lemma_feed_pending_step(buffer: Seq<u8>, input: Seq<u8>)
    requires super::framing_spec::wf(buffer), input.len() > 0,
        crate::spec::read_record(buffer, true) is NeedMore,
        crate::spec::read_record(buffer.push(input[0]), true) is NeedMore,
    ensures super::framing_spec::feed(buffer, input).buffer
            == super::framing_spec::feed(buffer.push(input[0]), input.skip(1)).buffer,
        super::framing_spec::feed(buffer, input).consumed
            == super::framing_spec::feed(buffer.push(input[0]), input.skip(1)).consumed + 1,
        super::framing_spec::feed(buffer, input).status
            == super::framing_spec::feed(buffer.push(input[0]), input.skip(1)).status,
{
    reveal(super::framing_spec::feed);
}

/// One model step for any nonempty input suffix at a Pending prefix.
pub proof fn lemma_feed_step(buffer: Seq<u8>, input: Seq<u8>)
    requires super::framing_spec::wf(buffer),
        super::framing_spec::status(buffer) is Pending, input.len() > 0,
    ensures {
        let appended = buffer.push(input[0]);
        match crate::spec::read_record(appended, true) {
            crate::spec::Read::NeedMore => {
                let tail = super::framing_spec::feed(appended, input.skip(1));
                super::framing_spec::feed(buffer, input)
                    == super::framing_spec::Feed { buffer: tail.buffer,
                        consumed: tail.consumed + 1, status: tail.status }
            },
            crate::spec::Read::Fail(error) => super::framing_spec::feed(buffer, input)
                == super::framing_spec::Feed { buffer: appended, consumed: 1,
                    status: super::framing_spec::Status::Fail(crate::spec::alert_of(error)) },
            crate::spec::Read::Done(_, _) => super::framing_spec::feed(buffer, input)
                == super::framing_spec::Feed { buffer: appended, consumed: 1,
                    status: super::framing_spec::Status::Complete },
        }
    },
{
    reveal(super::framing_spec::feed);
}

/// No bytes are consumed after a terminal status or from an empty suffix.
pub proof fn lemma_feed_stops(buffer: Seq<u8>, input: Seq<u8>)
    requires super::framing_spec::wf(buffer),
        super::framing_spec::status(buffer) is Complete || super::framing_spec::status(buffer) is Fail
            || input.len() == 0,
    ensures super::framing_spec::feed(buffer, input)
        == (super::framing_spec::Feed { buffer,
            consumed: 0, status: super::framing_spec::status(buffer) }),
{
    reveal(super::framing_spec::feed);
}
} // verus!

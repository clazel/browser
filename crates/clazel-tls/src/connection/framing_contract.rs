//! Refinement contracts for incremental protected-record framing.
#[allow(unused_imports)]
use vstd::prelude::*;
verus! {
/// Construction starts empty and satisfies the framing invariant.
pub open spec fn new_ensures(out: Seq<u8>) -> bool {
    out == super::framing_spec::new() && super::framing_spec::wf(out)
}

/// Feed copies no more than the supplied prefix and exactly follows the spec.
pub open spec fn feed_ensures(before: Seq<u8>, input: Seq<u8>, out: super::framing_spec::Feed) -> bool {
    super::framing_spec::wf(before)
        && out == super::framing_spec::feed(before, input)
        && out.consumed <= input.len()
        && out.buffer == before + input.take(out.consumed as int)
        && super::framing_spec::wf(out.buffer)
        && super::framing_spec::status_matches(out.buffer, out.status)
}

/// Feed in the immutable parser mode selected by the buffer constructor.
pub open spec fn feed_mode_ensures(protected: bool, before: Seq<u8>, input: Seq<u8>,
    out: super::framing_spec::Feed) -> bool {
    super::framing_spec::wf_mode(before, protected)
        && out == super::framing_spec::feed_mode(before, input, protected)
        && out.consumed <= input.len()
        && out.buffer == before + input.take(out.consumed as int)
        && super::framing_spec::wf_mode(out.buffer, protected)
        && super::framing_spec::status_matches_mode(out.buffer, out.status, protected)
}

/// take returns the exact held prefix, clears it, and restores the invariant.
pub open spec fn take_ensures(before: Seq<u8>, returned: Seq<u8>, after: Seq<u8>) -> bool {
    super::framing_spec::wf(before)
        && (returned, after) == super::framing_spec::take(before)
        && super::framing_spec::wf(after)
        && after == seq![]
}

/// take returns the exact held prefix and clears a buffer in either mode.
pub open spec fn take_mode_ensures(protected: bool, before: Seq<u8>, returned: Seq<u8>, after: Seq<u8>) -> bool {
    super::framing_spec::wf_mode(before, protected)
        && (returned, after) == super::framing_spec::take(before)
        && super::framing_spec::wf_mode(after, protected)
        && after == seq![]
}

/// length reports the number of bytes currently buffered.
pub open spec fn len_ensures(buffer: Seq<u8>, reported: nat) -> bool {
    super::framing_spec::wf(buffer) && reported == super::framing_spec::len(buffer)
}

/// length reports a mode-independent byte count for a valid buffer.
pub open spec fn len_mode_ensures(protected: bool, buffer: Seq<u8>, reported: nat) -> bool {
    super::framing_spec::wf_mode(buffer, protected) && reported == super::framing_spec::len(buffer)
}

/// is_empty reports whether there are zero buffered bytes.
pub open spec fn is_empty_ensures(buffer: Seq<u8>, reported: bool) -> bool {
    super::framing_spec::wf(buffer) && reported == super::framing_spec::is_empty(buffer)
}

/// is_empty reports a mode-independent byte predicate for a valid buffer.
pub open spec fn is_empty_mode_ensures(protected: bool, buffer: Seq<u8>, reported: bool) -> bool {
    super::framing_spec::wf_mode(buffer, protected) && reported == super::framing_spec::is_empty(buffer)
}
} // verus!

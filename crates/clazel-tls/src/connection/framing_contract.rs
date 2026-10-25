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
        && super::framing_spec::wf(out.buffer)
        && super::framing_spec::status_matches(out.buffer, out.status)
}

/// take returns the exact held prefix, clears it, and restores the invariant.
pub open spec fn take_ensures(before: Seq<u8>, returned: Seq<u8>, after: Seq<u8>) -> bool {
    super::framing_spec::wf(before)
        && (returned, after) == super::framing_spec::take(before)
        && super::framing_spec::wf(after)
        && after == seq![]
}

/// length reports the number of bytes currently buffered.
pub open spec fn len_ensures(buffer: Seq<u8>, reported: nat) -> bool {
    super::framing_spec::wf(buffer) && reported == super::framing_spec::len(buffer)
}
} // verus!

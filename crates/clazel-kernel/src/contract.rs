//! Contracts the executable kernel (item 2.12, in [`crate::exec`]) is proven
//! to meet. Each exec function's `ensures` clause is exactly one of
//! these predicates, so reviewing these (and [`super::spec`]) is enough to
//! know what the implementation guarantees.
//!
//! The exec `step` ([`crate::exec::step::step_exec`]) is pure: no I/O, no
//! clock, no processes. Bytes, renderer ids and the time come in as arguments,
//! as the host shell (item 2.15) gets them, and the outputs go out as a value
//! for the host to act on. An exec `StateRecord` is viewed as a [`State`]
//! (renderers, jar, storage maps, connections, counters, time), an `EventRecord` as an
//! [`Event`] and an `OutputRecord` as an [`Output`]; the exec jar is the view
//! of `clazel-cookie`'s (item 2.9), with its times `u64`s, hence
//! `jar_in_range`. Ids are `u64`s, hence `next_id` below `u64::MAX`. Web
//! Storage is a vector of buckets, one per origin, whose view is the map; the
//! exec state's own invariant `StateRecord::exec_wf` (the buckets' origins
//! are distinct and each bucket is non-empty) holds of `init_record` and of
//! every state `step_exec` returns, and is the only thing the exec `step`
//! asks of its state besides [`step_requires`].
//!
//! Every contract is about the Public Suffix List the generated tables hold
//! (`clazel_psl::table::psl_rules()`), as `clazel-cookie`'s are, and for a
//! given [`UrlFns`] `urls`: the spec view of the exec URL functions, and a
//! given [`FetchFns`] `fetch`, the spec view of the exec fetch (item 3.7).
//! Item 2.12 proves the exec `step` for any implementation of them whose view
//! is `urls` and `fetch` (so the kernel proofs never unfold the URL parser or
//! the HTTP client), and item 2.13 supplies the real URL functions. The
//! isolation theorems hold for every `urls` and `fetch`, so the contract
//! assumes nothing about them.
//!
//! The exec `step` also needs the facts of [`super::spec`] that are not
//! about a single call and that its caller keeps: `kernel_wf` of the state it
//! passes, which `lemma_step_preserves_wf` shows `step` preserves, so the
//! host loop establishes it once, from [`super::spec::init_state`]
//! (`lemma_init_wf`). `jar_in_range` and `now_in_range` of the state hold of
//! every state the exec `step` returns because its jar and time are `u64`s
//! that the exec cookie functions keep in range (their contracts); the exec
//! `step` ensures both. (`next_id` and `next_conn` may reach `u64::MAX`, after which the
//! host must not call it again; the exec `step` ensures each grows by at most
//! one.)
//!
//! The spec casts a storage map's length to `u64` (`StorageLength`). That is
//! exact in the exec `step` because a bucket is a `Vec`, whose length is a
//! `usize`; and for the spec alone, `lemma_storage_length_exact` proves that
//! a map with unique keys within its quota (`within_quota`, both in
//! `kernel_wf`) has at most `max_storage_size() + 1` entries.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The Public Suffix List the kernel runs with.
pub open spec fn psl() -> Seq<clazel_psl::spec::Rule> {
    clazel_psl::table::psl_rules()
}

/// Every URL `resolve` returns is a string of Unicode scalar values (the
/// serialization of a parsed URL always is). The `Commit` of a URL sends it
/// UTF-8 encoded, and the Encoding Standard's encoder is only defined on
/// scalar values, so the exec `step` needs this of the URL functions it is
/// given. (Added by item 2.12; the spec's `commit_frame` is unchanged. It
/// is a condition on the instantiation, which item 2.13 proves of the real
/// parser, so the isolation theorems still hold for every `UrlFns`.)
pub open spec fn urls_resolve_scalar(urls: UrlFns) -> bool {
    forall|base: Seq<u32>, input: Seq<u32>|
        match #[trigger] (urls.resolve)(base, input) {
            Some(u) => clazel_encoding::utf8::spec::all_scalar_values(u),
            None => true,
        }
}

/// Precondition of `step(StateRecord, &EventRecord) -> (StateRecord,
/// Vec<OutputRecord>)`: the state is well formed (`kernel_wf`); its jar and
/// time are in the range of the exec cookie functions; the next id fits a
/// `u64` with room for one more; a `Tick` carries a time in that range; and
/// the URL of an `OpenTab` (and those `resolve` returns,
/// [`urls_resolve_scalar`]) are strings of Unicode scalar values, which a
/// `Commit` must UTF-8 encode. (The id in `FromRenderer` and the tab in
/// `NavigateTab` and the connection in `Net` are `u64`s, so they fit. A
/// `NavigateTab` URL is never encoded, and neither is the final URL of a
/// fetch: the kernel checks it itself (`commit_navigation`), so the fetch
/// functions need no condition on it.) Item 3.7: the connection counter fits
/// a `u64` with room for one more (a step opens at most one connection: the
/// transducer's actions hold at most one `Connect`), and the transducer's
/// Public Suffix List is the kernel's (`UrlFnsExec::rules_are_psl` of
/// `clazel-fetch`), so the `Cookie` field is read from the jar with the same
/// cookie roots the kernel applies the jar operations with.
pub open spec fn step_requires(urls: UrlFns, fetch: FetchFns, s: State, e: Event) -> bool {
    &&& super::invariant::kernel_wf(psl(), urls, s)
    &&& clazel_cookie::storage::contract::jar_in_range(s.jar)
    &&& clazel_cookie::set_cookie::contract::now_in_range(s.now)
    &&& s.next_id < 0xFFFF_FFFF_FFFF_FFFFnat
    &&& s.next_conn < 0xFFFF_FFFF_FFFF_FFFFnat
    &&& fetch.urls.rules == psl()
    &&& (e is Tick ==> clazel_cookie::set_cookie::contract::now_in_range(e->Tick_time))
    &&& urls_resolve_scalar(urls)
    &&& (e is OpenTab ==> clazel_encoding::utf8::spec::all_scalar_values(e->OpenTab_url))
}

/// Contract for `step(StateRecord, &EventRecord) -> (StateRecord,
/// Vec<OutputRecord>)`: the state and outputs of the spec's `step`.
pub open spec fn step_ensures(urls: UrlFns, fetch: FetchFns, s: State, e: Event, output: (State, Seq<Output>)) -> bool {
    output == step(psl(), urls, fetch, s, e)
}

/// Contract for `decode_renderer_frame(&[u8]) -> Option<Message>`: the
/// message in a frame a renderer sent, or `None` if the frame does not decode
/// or holds a message only the kernel may send. Whole frames, header
/// included.
pub open spec fn decode_renderer_frame_ensures(bytes: Seq<u8>, output: Option<clazel_ipc::message::spec::Message>) -> bool {
    output == decode_renderer_frame(bytes)
}

/// Contract for `reply_frame(&Message) -> Vec<u8>`: the frame of the
/// message, or the frame of `Error { error_encode }` if the message cannot
/// be sent (a text that is not UTF-8, or a payload over `MAX_FRAME`). Always
/// a whole frame within `MAX_FRAME`.
pub open spec fn reply_frame_ensures(m: clazel_ipc::message::spec::Message, output: Seq<u8>) -> bool {
    output == reply_frame(m)
}

/// Contract for `commit_frame(&[u32], &[u8]) -> Vec<u8>`: the frame of a
/// `Commit` of the URL (encoded as UTF-8) running the script.
pub open spec fn commit_frame_ensures(url: Seq<u32>, script: Seq<u8>, output: Seq<u8>) -> bool {
    output == commit_frame(url, script)
}

} // verus!

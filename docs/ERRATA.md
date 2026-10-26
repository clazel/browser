# Spec errata found while formalizing

Places where a web standard, read literally, says something other than what
it evidently means. Each entry records what we specified instead.

## Encoding §3 "peek" reads from index 1, not 0

- **Spec:** Encoding Standard, Living Standard last updated 19 October 2026
  (commit `dd7943441a861a60a073bffa55869d91cb6a8288`),
  <https://encoding.spec.whatwg.org/#i-o-queue-peek>
- **Text:** "For each n in the range 1 to number, inclusive: If ioQueue[n] is
  end-of-queue, break. Otherwise, append ioQueue[n] to prefix."
- **Problem:** Infra lists are zero-based ("a zero-based index into a list").
  Read literally, peeking 3 items returns `ioQueue[1..=3]` and skips the
  first item. "UTF-8 decode" step 2 would then test bytes 1–3 for the BOM
  instead of bytes 0–2.
- **We specify:** the first `number` items (`ioQueue[0..number]`). See
  `starts_with_bom` in `crates/clazel-encoding/src/utf8/spec.rs`.
- **Reported upstream:** [whatwg/encoding#367](https://github.com/whatwg/encoding/issues/367),
  19 October 2026.

## Fetch "collect an HTTP quoted string" step 7 takes one code point too many

- **Spec:** Fetch Standard, Living Standard last updated 19 October 2026
  (commit `59afe349913d56898c947576216f1c2579308be7`),
  <https://fetch.spec.whatwg.org/#collect-an-http-quoted-string>
- **Text:** "Return the code points from positionStart to position,
  inclusive, within input."
- **Problem:** after the loop, position points just past the closing
  U+0022 ("), or past the end of input. Read literally, "inclusive" adds the
  code point after the closing quote (or one that does not exist). The
  standard's own example table contradicts that: input `"Hello" World`
  gives `"Hello"` with final position 7, and input `"\` gives `"\` with
  final position 2, past the end of the two-code-point input.
- **We specify:** the code points from positionStart up to, but not
  including, position. See `collect_an_http_quoted_string` in
  `crates/clazel-mime/src/mime_type/spec.rs`. (Parse a MIME type only calls
  it with extract-value true, which does not reach this step.)
- **Reported upstream:** not yet.

## MIME Sniffing §6 pattern matching reads past the end of input

- **Spec:** MIME Sniffing Standard, Living Standard last updated 19 October
  2026 (commit `ba4b3c385b9765ddfe4a994e2bb89e0ab96068e2`),
  <https://mimesniff.spec.whatwg.org/#pattern-matching-algorithm>
- **Text:** step 2 "If input's length is less than pattern's length,
  return false", then step 4 skips ignored leading bytes, then step 6.1
  "Let maskedData be the result of applying the bitwise AND operator to
  input[s] and mask[p]."
- **Problem:** the length check comes before the skip. With leading
  whitespace bytes skipped, fewer than pattern's length bytes may remain,
  and step 6.1 reads input[s] past the end.
- **We specify:** return false when s reaches the end of input before the
  pattern does. See `compare_pattern` in
  `crates/clazel-mime/src/sniff/spec.rs`.
- **Reported upstream:** not yet.

## MIME Sniffing §6.2.2 signature for WebM and "parse a vint"

- **Spec:** as above, <https://mimesniff.spec.whatwg.org/#signature-for-webm>
- **Text and problems:**
  - Step 6.1 compares "the two bytes from sequence[iter] to
    sequence[iter + 1]" while only iter < length is known: when iter is
    length − 1, sequence[iter + 1] does not exist.
  - "parse a vint ... starting at index iter" then says "Let index be 0",
    so it always reads sequence[0], the 0x1A its caller has already
    checked.
  - Its step 5.1 "abort these steps" would end the algorithm without the
    return value of step 10.
  - "Matching a padded sequence" is defined "starting at byte offset and
    ending at by end", but the caller gives only the offset.
- **We specify:** the two bytes are not 0x42 0x82 when only one remains;
  index starts at iter; 5.1 (and 9.4) leave their loop; and end is the last
  byte of the pattern after any run of 0x00 bytes from offset. See
  `webm_loop`, `parse_a_vint` and `matches_padded_sequence` in
  `crates/clazel-mime/src/sniff/spec.rs`.
- **Reported upstream:** not by us. Already open: whatwg/mimesniff#93,
  #126, #146, #167.

## MIME Sniffing §6.2.3 signature for MP3 without ID3

- **Spec:** as above, <https://mimesniff.spec.whatwg.org/#signature-for-mp3-without-id3>
- **Text and problems** (the algorithm is Mozilla's `mp3sniff.c`, per
  whatwg/mimesniff#70; we follow it where the text departs from it):
  - "match an mp3 header" step 1 "If length is less than 4" ignores the
    offset s at which it then reads four bytes (the second call has s > 0).
    We require four bytes from s.
  - Step 2 "If sequence[s] is not equal to 0xff and sequence[s + 1] & 0xe0
    is not equal to 0xe0, return false" must be "or": a frame sync needs
    both.
  - "sequence[s + 1] & 0x06 >> 1" and the like: read with ">>" binding
    first, they test other bits. We apply the AND first, as `mp3sniff.c`
    does.
  - Step 7 "skipped-bytes is greater than s - length": s − length is never
    positive, so every input fails. We compare with length − s.
  - "parse an mp3 frame" steps 3–4 pick the mp2.5-rates table when
    version & 1 is non-zero, and "compute an mp3 frame size" picks scale 72
    when version is 1. MPEG audio's version 3 (0b11) is MPEG-1, whose
    Layer III bitrates are the mp3-rates table and whose frames use 144;
    versions 2 and 0 (MPEG-2, 2.5) use mp2.5-rates and 72. Read literally,
    an ordinary 128 kbit/s MPEG-1 file computes a 261-byte frame instead of
    417 and is not recognised. We pick the table and scale by version & 1
    as `mp3sniff.c` does.
- **We specify:** each correction at its step in
  `match_an_mp3_header`, `parse_an_mp3_frame`,
  `compute_an_mp3_frame_size` and `matches_mp3_without_id3` in
  `crates/clazel-mime/src/sniff/spec.rs`.
- **Reported upstream:** not by us. Already open: whatwg/mimesniff#70,
  #168. (The table and scale swap is not in either; not yet reported.)

## RFC 6265bis §5.6.1 steps 3 and 4 and §5.6.2 step 5: the cookie-age-limit has two meanings

- **Spec:** draft-ietf-httpbis-rfc6265bis-22 (1 December 2025),
  <https://www.ietf.org/archive/id/draft-ietf-httpbis-rfc6265bis-22.txt>
- **Text and problem:** §5.6.1 step 3 says "Let cookie-age-limit be the
  maximum age of the cookie (which SHOULD be 400 days in the future or
  sooner, see Section 5.5)", and step 4 "If the expiry-time is more than
  cookie-age-limit, the user agent MUST set the expiry time to
  cookie-age-limit in seconds." The expiry-time is an instant, and an age
  is a duration, so the comparison and the assignment mix units ("400 days
  in the future" is an instant; "in seconds" is a duration). §5.6.2 steps
  5 and 6 use the same name for the duration (the smaller of delta-seconds
  and cookie-age-limit), which is the reading §5.5 gives ("34560000
  seconds").
- **We specify:** for Expires, the limit is the instant now plus 34 560 000
  seconds; for Max-Age it is the duration 34 560 000 seconds. See
  `process_expires` and `process_max_age` in
  `crates/clazel-cookie/src/set_cookie/spec.rs`.
- **Reported upstream:** not yet.

## RFC 6265bis §5.7 step 10: "request-host-canonical" is not bound unless step 9 runs

- **Spec:** draft-ietf-httpbis-rfc6265bis-22 (1 December 2025),
  <https://www.ietf.org/archive/id/draft-ietf-httpbis-rfc6265bis-22.txt>
- **Text and problem:** step 9 reads "If the user agent is configured to
  reject 'public suffixes' and the domain-attribute is a public suffix:
  1. Let request-host-canonical be the canonicalized request-host. 2. If
  request-host fails to be canonicalized then abort this algorithm and ignore
  the cookie entirely." Step 10 then says "If request-host-canonical does not
  domain-match [...] the domain-attribute" and, for an empty
  domain-attribute, "Set the cookie's domain to request-host-canonical". So
  the variable is defined only inside step 9's condition (a user agent that
  is not configured to reject public suffixes, or a domain-attribute that is
  not one, never binds it), and the failure to canonicalize is only detected
  there. Read literally, the usual cookie (no Domain attribute) has its
  domain set from an undefined name.
- **We specify:** the evident intent. The request host is canonicalized
  before step 9 for every cookie, and the cookie is ignored entirely if that
  fails; steps 9 and 10 then use the result. See `create_a_cookie` and
  `step_9_domain_attribute` in `crates/clazel-cookie/src/storage/spec.rs`.
- **Reported upstream:** not yet.

## RFC 1035 §4.1.4: "a prior occurance" does not rule out a loop

- **Spec:** RFC 1035 (November 1987), §4.1.4 "Message compression",
  <https://www.rfc-editor.org/rfc/rfc1035#section-4.1.4>
- **Text:** "an entire domain name or a list of labels at the end of a domain
  name is replaced with a pointer to a prior occurance of the same name."
  Phase 3's plan (item 3.4) reads this as "the pointer must point to a lower
  offset than its own".
- **Problem:** a lower offset is not enough. A label at offset 0 followed by
  a pointer at offset 2 to offset 0 points to a lower offset, yet reading
  the name from offset 0 reaches the pointer again, and a decoder that
  checks only the offset never stops. The text also does not say whether
  the "prior occurance" may overlap the pointer.
- **We specify:** the evident intent: the target is a name that has already
  occurred, so the octets read from a pointer's target must end at or before
  the pointer itself (and a pointer found there is held to the same rule
  against its own offset). A target at or above the pointer is an error as
  well. Every message an encoder produces satisfies this, because it
  compresses a name only against names that ended earlier. This gives the
  decoder a lexicographic `decreases` (the limit, then the distance to it).
  See `read_name` in `crates/clazel-dns/src/spec.rs`.
- **Reported upstream:** not yet.

## RFC 7230 §3.2: `field-content` cannot match a value with two inner whitespace runs

- **Spec:** RFC 7230 (June 2014), §3.2 "Header Fields",
  <https://www.rfc-editor.org/rfc/rfc7230#section-3.2>
- **Text:** "field-value = *( field-content / obs-fold )", "field-content =
  field-vchar [ 1*( SP / HTAB ) field-vchar ]", "field-vchar = VCHAR /
  obs-text".
- **Problem:** `field-vchar` is one octet, so a `field-content` is one octet
  or two octets with whitespace between, and `*( field-content / obs-fold )`
  is a row of those. A value such as `a b c` would need `a b` followed by
  ` c`, and ` c` begins with whitespace, so no row matches. Read literally,
  `text/html; charset=utf-8` is not a field value. The rule evidently means
  a value that begins and ends with a `field-vchar` with `SP`, `HTAB` and
  `field-vchar` between, which is what RFC 9110 §5.5 (`field-content =
  field-vchar [ 1*( SP / HTAB / field-vchar ) field-vchar ]`) writes.
- **We specify:** the RFC 9110 §5.5 reading, in `r_is_field_value` in
  `crates/clazel-http/src/message/independent.rs` (the independent
  transcription of RFC 7230 §3); the spec itself is RFC 9112's and has no
  such issue.
- **Reported upstream:** not yet (RFC 9110, which obsoletes RFC 7230, already
  states the corrected rule).

## RFC 8446 §5 and §5.1: a compatibility CCS inside a fragmented handshake message

- **Spec:** RFC 8446 (August 2018), §5 "Record Protocol" and §5.1 "Record
  Layer", <https://www.rfc-editor.org/rfc/rfc8446#section-5>
- **Text:** §5: "An implementation may receive an unencrypted record of type
  change_cipher_spec consisting of the single byte value 0x01 at any time
  after the first ClientHello message has been sent or received and before
  the peer's Finished message has been received and MUST simply drop it
  without further processing." §5.1: "Handshake messages MUST NOT be
  interleaved with other record types. That is, if a handshake message is
  split over two or more records, there MUST NOT be any other records
  between them."
- **Problem:** a CCS record between two fragments of one handshake message
  is covered by both. §5 says drop it; §5.1 says the peer may not send it.
  The CCS exists only for middlebox compatibility (Appendix D.4), which has
  the server send it immediately after its first handshake message, so it
  evidently never needs to fall inside one. Implementations differ:
  BoringSSL and NSS refuse a CCS inside a fragmented ServerHello, and after
  ServerHello both drop one without checking for a message boundary.
- **We specify:** the §5 drop applies only at a handshake message boundary;
  inside a fragmented message a CCS is fatal with `unexpected_message`. See
  `receive` in `crates/clazel-tls/src/hello/bootstrap_spec.rs` (plaintext
  ServerHello/HRR) and `compatibility_ccs_dropped` in
  `crates/clazel-tls/src/connection/dispatcher_spec.rs` (protected
  handshake).
- **Reported upstream:** not yet.

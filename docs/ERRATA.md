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
  `starts_with_bom` in `crates/clazel-encoding/src/utf8/spec.rs`, and
  "BOM sniff" (which peeks 3 bytes too) in
  `crates/clazel-encoding/src/hooks/spec.rs`.
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

## FIPS 186-5 §6.4.2 step 3 numbers its two sub-steps "a." and "a."

- **Spec:** FIPS 186-5, *Digital Signature Standard (DSS)*, published
  3 February 2023 (PDF SHA-256
  `fbb9c7c2ba442f03c57b63b43c888311903c9d0f29f89b06efdebd9b619140c5`),
  §6.4.2 "ECDSA Signature Verification Algorithm", printed page 25,
  <https://doi.org/10.6028/NIST.FIPS.186-5>
- **Text:** step 3 "Derive the integer e from H as follows:", then "a. If
  ⌈log2(n)⌉ ≥ hashlen, set E = H. Otherwise, set E equal to the leftmost
  ⌈log2(n)⌉ bits of H." and then again "a. Convert the bit string E to the
  integer e as specified in Appendix B.2.1."
- **Problem:** two sub-steps carry the label "a." (the signing algorithm,
  §6.4.1 step 2, labels them "a." and "b."). A citation "step 3a" is
  ambiguous.
- **We specify:** the second sub-step is 3b, and the first is 3a. See
  `derive_e` in `crates/clazel-p384/src/spec.rs`.
- **Reported upstream:** not yet.

## FIPS 186-5 §6.4 says "the leftmost n bits" of a long hash, where n is the order

- **Spec:** as above, §6.4 "ECDSA Digital Signature Generation and
  Verification", printed page 23.
- **Text:** "When the length of the output of the hash function (or XOF) is
  greater than the bit length of n, then the leftmost n bits of the hash
  function (or XOF) output block shall be used in any calculation using the
  hash function (or XOF) output".
- **Problem:** the symbol n is the order of the base point, a number of 384
  bits for P-384 (SP 800-186 §3.2.1.4), so "the leftmost n bits" read
  literally asks for about 2^384 bits. The same paragraph's first clause
  says "the bit length of n", §6.1.1 says "the leftmost len(n) bits", and
  §6.4.2 step 3a says "the leftmost ⌈log2(n)⌉ bits".
- **We specify:** the leftmost `⌈log2 n⌉` bits, which for a prime n > 2 is
  `len(n)`, as in §6.4.2 step 3a and SEC 1 §4.1.4 step 3.2. See `derive_e`
  in `crates/clazel-p384/src/spec.rs`.

## HTML §13.2.6.4.10 "in table text" with an empty pending list

- **Spec:** HTML Standard, Living Standard (`source` at commit
  `939677714df7379fee3667040113b41c91c851e7`, 26 October 2026),
  <https://html.spec.whatwg.org/multipage/parsing.html#parsing-main-intabletext>
- **Text:** "Otherwise, insert the characters given by the pending table
  character tokens list." and, in "insert a character", "Let data be the
  characters passed to the algorithm, or, if no characters were explicitly
  specified, the character of the character token being processed."
- **Problem:** the list is empty when every character token since the "in
  table" mode was U+0000 NULL, which "in table text" ignores (`<table>`
  then a NULL then `</table>`). Read literally, inserting the empty list
  either creates an empty `Text` node ("insert a character" step 5) or falls
  back to "the character of the character token being processed", which is
  the end tag, not a character token.
- **We specify:** nothing is inserted. See `mode_in_table_text` in
  `crates/clazel-treebuilder/src/spec/modes/in_table_text.rs`.
- **Reported upstream:** not yet.

## W3C HTML 5.2 §8.2.4.77 multiplies decimal digits by 16

- **Spec:** HTML 5.2, W3C Recommendation, 14 December 2017,
  <https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#decimal-character-reference-state>
  (the second source of `clazel-html`'s independent tokenizer
  transcription; the living standard is what the crate implements).
- **Text:** "ASCII digit: Multiply the character reference code by 16. Add
  a numeric version of the current input character (subtract 0x0030 from
  the character's code point) to the character reference code."
- **Problem:** this is the decimal state; read literally, `&#65;` is
  U+0065 instead of U+0041. The hexadecimal state above it multiplies by
  16, and the WHATWG text this was forked from, and every browser,
  multiply by 10 here.
- **We specify:** nothing new: the crate implements the living standard
  (§13.2.5.83, "Multiply the character reference code by 10"). The W3C
  transcription (`crates/clazel-html/src/tokenizer/independent.rs`)
  keeps the text as written, and the comparison of the two
  (`tokenizer/agreement.rs`) lists the inputs where this makes them differ.
  W3C HTML 5.2 is superseded by the living standard.
- **Reported upstream:** not yet.

## W3C HTML 5.2 §8.2.4.72 matches named references after the current character

- **Spec:** HTML 5.2, W3C Recommendation, 14 December 2017,
  <https://www.w3.org/TR/2017/REC-html52-20171214/syntax.html#character-reference-state>
- **Text:** "Consume the next input character: ... Anything else: Consume
  the maximum number of characters possible, with the consumed characters
  matching one of the identifiers in the first column of the §8.5 Named
  character references table".
- **Problem:** the state has already consumed the next input character;
  read literally, the match starts after it, so `&amp;` would try to match
  `mp;`, and on no match the character would be lost.
- **We specify:** the W3C transcription reads "the consumed characters" as
  including the current input character (its modelling choice 15). The
  crate implements the living standard, whose named character reference
  state reconsumes that character first (§13.2.5.77, §13.2.5.78).
- **Reported upstream:** not yet.

## RFC 5937 §3.2: the anchor's pathLenConstraint is set before RFC 5280 §6.1.2 (k) resets it

- **Spec:** RFC 5937, August 2010, <https://www.rfc-editor.org/rfc/rfc5937.txt>
  (SHA-256 `6424a9b13e2ea7accfed71e0adef806309851909775aea74471187910f861f01`),
  §3.2; with RFC 5280 §6.1.2 (k).
- **Text:** RFC 5937 §3.2: "These steps (or equivalent) MUST be performed
  prior to initialization steps described in RFC 5280." Its last step: "If a
  basic constraints extension is associated with the trust anchor and
  contains a pathLenConstraint value, set the max_path_length state variable
  equal to the pathLenConstraint value from the basic constraints
  extension." RFC 5280 §6.1.2 (k): "max_path_length: this integer is
  initialized to n".
- **Problem:** the other §3.2 steps set *inputs* (§6.1.1) that §6.1.2 then
  reads, so performing them first is right. max_path_length is not an input
  but a §6.1.2 state variable. Read literally, the order makes §6.1.2 (k)
  overwrite the anchor's value with n, and the step has no effect.
- **We specify:** max_path_length starts at the anchor's pathLenConstraint
  when it has one, and at n otherwise. See `initialization` in
  `crates/clazel-x509/src/path/spec.rs`. (No RFC 5937 erratum was found on
  2026-10-29.)
- **Reported upstream:** not yet.

## HTML "get an XML encoding" reads bytes that may not exist

- **Spec:** HTML Standard, Living Standard (whatwg/html commit
  `939677714df7379fee3667040113b41c91c851e7`, 26 October 2026),
  <https://html.spec.whatwg.org/multipage/parsing.html#concept-get-xml-encoding-when-sniffing>
- **Text:** steps 6 to 10: "While the byte at encodingPosition is less than
  or equal to 0x20 ..., advance encodingPosition to the next byte." "If the
  byte at encodingPosition is not 0x3D (=), then return failure." "Let
  quoteMark be the byte at encodingPosition."
- **Problem:** after `encoding` (step 4 only bounds where that word starts),
  the bytes can end, and these steps then read a byte that is not there.
  The prescan's rule for running out of bytes ("abort the prescan ...")
  covers the prescan and "get an attribute", not this algorithm, which runs
  after the prescan was aborted. Read literally, what happens is undefined.
- **We specify:** a byte that is not there is not 0x3D and not a quote, so
  steps 7 and 11 return failure (and step 6's loop stops at the end). This
  is the evident intent: an XML declaration cut off before its encoding's
  value names no encoding. See `get_xml_encoding` in
  `crates/clazel-html/src/sniff/spec.rs`.
- **Reported upstream:** not yet.

## X.509 §12.5 ignores self-signed certificates, including the end entity

- **Spec:** Recommendation ITU-T X.509 (10/2019) | ISO/IEC 9594-8:2020,
  <https://www.itu.int/rec/T-REC-X.509-201910-I/en> (SHA-256
  `1f4ea2939ecc31a3433c499084d485e770f9b8dcee55a0ba9fe4c27128822e8c`),
  §12.5.1 and §12.5.2, with §9.1.5.
- **Text:** §12.5.1: "Self-signed certificates, if encountered in the path,
  are ignored." (repeated at the start of §12.5.2). §9.1.5: "self-issued
  certificates of category a) are self-signed certificates ..., and if they
  are encountered in the path, they shall be ignored" and, for category b),
  "may only appear as end-entity public-key certificates in a path, and shall
  be processed as end-entity public-key certificates", then "If self-issued
  certificates of category b) are encountered within a path, they shall be
  ignored."
- **Problem:** §12.5: "The last public-key certificate is considered to be the
  end-entity public-key certificate" and the checks apply to it. Read
  literally, a self-signed end-entity certificate is ignored, so a path made
  of one self-signed certificate passes every check with nothing verified
  under the trust anchor's key, and any self-signed certificate would be
  accepted. §9.1.5 also says category b) certificates are both processed as
  end-entity certificates and ignored, and a path cannot tell categories b)
  and c) apart (both are self-issued and not self-signed).
- **We specify:** a self-signed certificate (self-issued, and its signature
  verifies under its own key, §3.5.69) is removed from the path unless it is
  the last certificate, and the rest is processed with the previous kept
  certificate as issuer. The last certificate is always processed. A
  self-issued certificate that is not self-signed is processed as §12.5's
  "intermediate self-issued" rules say, or as the end entity if last. See
  `drop_ignored` in `crates/clazel-x509/src/path/independent.rs`.
- **Reported upstream:** not yet.

## BR §7.1.2.2.5 omits two rows of §7.1.2.10.6

- **Spec:** CA/Browser Forum, Baseline Requirements for the Issuance and
  Management of Publicly-Trusted TLS Server Certificates, version 2.3.1
  (4 October 2026; `docs/BR.md` at commit
  `3574ae809e5f909b58ee4c26b7bac4a3b9e78421` of cabforum/servercert),
  <https://cabforum.org/working-groups/server/baseline-requirements/documents/>
- **Text:** §7.1.2.2.5, "Table: TLS Cross-Certified Subordinate CA EKU" lists
  `id-kp-serverAuth` (MUST be present), `id-kp-clientAuth` (MAY),
  `id-kp-emailProtection`, `id-kp-codeSigning`, `id-kp-timeStamping` and
  `anyExtendedKeyUsage` (MUST NOT), and "Any other value" (NOT
  RECOMMENDED). The table of §7.1.2.10.6, which the other TLS subordinate CA
  profiles use, has the same rows and two more, `id-kp-OCSPSigning` and the
  "Precertificate Signing Certificate" purpose (1.3.6.1.4.1.11129.2.4.4),
  both MUST NOT.
- **Problem:** read literally, a restricted cross-certified TLS subordinate CA
  may carry OCSPSigning or the precertificate-signing purpose next to
  serverAuth ("any other value" is only NOT RECOMMENDED), while a TLS
  subordinate CA that is not a cross-certificate may not. Nothing in the
  document gives a reason for the difference, and a relying party cannot tell
  the two kinds apart from the certificate.
- **We specify:** §7.1.2.10.6's table for every subordinate CA, cross-certified
  or not. See `ca_eku_table_ok` in
  `crates/clazel-x509/src/path/independent_profile.rs`.
- **Reported upstream:** not yet.

## BR §7.1.2.7.6 makes keyUsage "SHOULD" but §7.1.2.7.11 says "MUST" be set

- **Spec:** as above, §7.1.2.7.6 and §7.1.2.7.11.
- **Text:** §7.1.2.7.6 lists the subscriber `keyUsage` extension with
  presence "SHOULD". The Note under §7.1.2.7.11's RSA table says "At least
  one Key Usage MUST be set for RSA Public Keys", and the ECC table has
  `digitalSignature` as required "MUST".
- **Problem:** a subscriber certificate with no keyUsage extension has no key
  usage bits set, so read literally it breaks the Note's "MUST" and the ECC
  table's "MUST", which makes the extension's own "SHOULD" meaningless.
- **We specify:** the extension is optional, as §7.1.2.7.6 says. A
  certificate without it is accepted. When it is present, the tables'
  "MUST"s apply to its bits. See `subscriber_key_usage_ok` in
  `crates/clazel-x509/src/path/independent_profile.rs`.
- **Reported upstream:** not yet.

## CSS Syntax §5.5.5 "consume a block's contents" never appends its last declarations

- **Spec:** CSS Syntax Module Level 3, Editor's Draft (commit
  `c410ee5e4d2afe6d8b2e8ce53723b8d1eb3b5b67` of `w3c/csswg-drafts`),
  <https://drafts.csswg.org/css-syntax-3/#consume-block-contents>
- **Text:** for `<EOF-token>` and `<}-token>`: "Return rules."
- **Problem:** declarations collect in decls, which only reaches rules when an
  at-rule, a rule or an invalid rule error follows it. Read literally, the
  declarations after the last of those are thrown away, so `a { color: red }`
  has no declarations at all, and neither does any block with no nested rule.
  The same section says its result holds "lists of declarations", and "consume a
  qualified rule" reads the first of them as the rule's declarations.
- **We specify:** append decls to rules if it is not empty, as the other
  branches do, then return rules. See `blocks_contents_loop` in
  `crates/clazel-css/src/parser/spec.rs`, and
  `lemma_example_declaration_in_a_rule` in its `examples.rs`.
- **Reported upstream:** not yet.

## RFC 8446 §4.2 and §6.2 name two alerts for an extension not allowed in a message

- **Spec:** RFC 8446, August 2018, <https://www.rfc-editor.org/rfc/rfc8446>
- **Text:** §4.2: "If an implementation receives an extension which it recognizes
  and which is not specified for the message in which it appears, it MUST abort the
  handshake with an 'illegal_parameter' alert." §6.2, unsupported_extension: "Sent
  by endpoints receiving any handshake message containing an extension known to be
  prohibited for inclusion in the given handshake message".
- **Problem:** the same condition, two alerts. §4.3.1 agrees with §4.2 for
  EncryptedExtensions.
- **We specify:** `illegal_parameter`, §4.2's MUST, in the clean-room transcription
  (`recognized_but_not_specified` and `response_block_failures` in
  `crates/clazel-tls/src/transcription/extensions.rs`). `unsupported_extension`
  stays for an extension the client did not offer.
- **Reported upstream:** not yet.

## RFC 8446 §4.1.3's ServerHello cannot hold the older hello it must check

- **Spec:** RFC 8446, August 2018, <https://www.rfc-editor.org/rfc/rfc8446>
- **Text:** §4.1.3: `Extension extensions<6..2^16-1>;` and "TLS 1.3 clients
  receiving a ServerHello indicating TLS 1.2 or below MUST check that the last 8
  bytes are not equal to either of these values."
- **Problem:** a TLS 1.2 ServerHello may have fewer than 6 bytes of extensions, or
  no extensions field (§4.1.2: "All versions of TLS allow an extensions field to
  optionally follow the compression_methods field"). Read literally, it fails
  §4.1.3's structure with `decode_error` before the check that must give
  `illegal_parameter`, or Appendix D.1's `protocol_version`.
- **We specify:** the version is detected with the extensions optional and no floor;
  §4.1.3's structure applies once the message is known to be TLS 1.3 or a
  HelloRetryRequest (`read_server_hello_any_version` and `receive_server_hello` in
  `crates/clazel-tls/src/transcription/`).
- **Reported upstream:** not yet.

## RFC 8446 §4.1.4, §4.2.1 and Appendix D.5 disagree on ServerHello.legacy_version

- **Spec:** RFC 8446, August 2018, <https://www.rfc-editor.org/rfc/rfc8446>
- **Text:** §4.2.1: "If this extension is present, clients MUST ignore the
  ServerHello.legacy_version value". §4.1.4: "the client MUST check the
  legacy_version ... as specified in Section 4.1.3". Appendix D.5: "Any endpoint
  receiving a Hello message with ClientHello.legacy_version or
  ServerHello.legacy_version set to 0x0300 MUST abort the handshake with a
  'protocol_version' alert."
- **Problem:** a HelloRetryRequest "has the same format as a ServerHello message" and
  must carry supported_versions, so §4.2.1 says to ignore what §4.1.4 says to check.
  §4.1.3 gives the check no alert. And D.5 aborts on a value §4.2.1 ignores.
- **We specify:** by specificity, in `key_exchange.rs` of the clean-room transcription:
  0x0300 always aborts with `protocol_version`; a HelloRetryRequest's other values
  must be 0x0303, or `illegal_parameter` by §6's note; with supported_versions, a
  ServerHello's is otherwise ignored.
- **Reported upstream:** not yet.

## RFC 8446 §5 and §5.1: dropping change_cipher_spec "at any time" against no interleaving

- **Spec:** RFC 8446, August 2018, <https://www.rfc-editor.org/rfc/rfc8446>
- **Text:** §5: "An implementation may receive an unencrypted record of type
  change_cipher_spec consisting of the single byte value 0x01 at any time after the
  first ClientHello ... and MUST simply drop it without further processing." §5.1:
  "if a handshake message is split over two or more records, there MUST NOT be any
  other records between them."
- **Problem:** a change_cipher_spec between two fragments of one handshake message
  meets the first sentence and breaks the second.
- **We specify:** in the clean-room transcription, the record is dropped and the
  fragments kept (`receive_record` in
  `crates/clazel-tls/src/transcription/connection.rs`), because §5's sentence is a
  receiver's rule explicit about time, and §5.1's binds the sender and gives the
  receiver no action. This entry was written without reading the earlier entry above
  on the same subject, only its heading, so that the two readings stay independent;
  the later equivalence proof decides if they differ.
- **Reported upstream:** not yet.

## RFC 8446 §5.3: "each record" has no sequence number before a key

- **Spec:** RFC 8446, August 2018, <https://www.rfc-editor.org/rfc/rfc8446>
- **Text:** §5.3: "The appropriate sequence number is incremented by one after reading
  or writing each record."
- **Problem:** read literally, the dummy change_cipher_spec of Appendix D.4, unprotected
  and received while protection is engaged, advances the read number, and every later
  nonce would then be wrong. §5's "without further processing" contradicts that.
- **We specify:** the number counts records protected under the key, in the clean-room
  transcription (`receive_ciphertext` and `send_one` in
  `crates/clazel-tls/src/transcription/connection.rs`).
- **Reported upstream:** not yet.

## RFC 8446 §4.4.3's "unless" gives a client nothing to verify with

- **Spec:** RFC 8446, August 2018, <https://www.rfc-editor.org/rfc/rfc8446>
- **Text:** §4.4.3: "the signature algorithm MUST be one offered in the client's
  'signature_algorithms' extension unless no valid certificate chain can be produced
  without unsupported algorithms".
- **Problem:** the exception makes sense for a certificate's signature, which a client
  may be able to check through other means (§4.4.2.2), not for this message's, which
  is one the client must itself verify. §4.2.3: each value is one "that the client is
  willing to verify".
- **We specify:** a client refuses a CertificateVerify whose algorithm it did not offer,
  always, with `illegal_parameter` by §6's note (`certificate_verify_failures` in
  `crates/clazel-tls/src/transcription/authentication.rs`).
- **Reported upstream:** not yet.

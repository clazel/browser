# RSA-PSS CertificateVerify fixtures

Generated for `tests/signature.rs` on 2026-10-26 with LibreSSL 3.3.6 (macOS).
There is no deterministic RFC test vector for RSASSA-PSS (the salt is random),
so these are our own. Only public keys and signatures are kept; the private
keys were discarded.

- `msg.bin`: the 27-octet message `clazel rsa-pss test message`.
- `k2048.spki.der`: a 2048-bit rsaEncryption key, e = 65537.
  `k2048.{sha256,sha384,sha512}.sig`: RSASSA-PSS signatures of `msg.bin` with
  MGF1 over the same hash and a salt as long as the digest (RFC 8446 §4.2.3),
  each checked with `openssl pkeyutl -verify` before being kept.
- `ke3.spki.der` / `ke3.sha256.sig`: a 2048-bit key with e = 3, signed the
  same way. It must be refused: libcrux-rsa verifies only with e = 65537.
- `k2047.spki.der` / `k2047.sha256.sig`: a 2047-bit key (its modulus fills
  256 octets without the top bit set). It must be refused, too.

To regenerate (new keys give new files, so update the tests' expectations):

```sh
printf 'clazel rsa-pss test message' > msg.bin
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out k2048.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -pkeyopt rsa_keygen_pubexp:3 -out ke3.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2047 -out k2047.pem
openssl pkey -in k2048.pem -pubout -outform DER -out k2048.spki.der   # likewise ke3, k2047
openssl dgst -sha256 -binary msg.bin > d256
openssl pkeyutl -sign -in d256 -inkey k2048.pem -pkeyopt digest:sha256 \
  -pkeyopt rsa_padding_mode:pss -pkeyopt rsa_pss_saltlen:32 -pkeyopt rsa_mgf1_md:sha256 \
  -out k2048.sha256.sig                                              # likewise 384/48, 512/64
```

# Certificate-link fixtures

Generated for `tests/chain.rs` on 2026-10-29 with LibreSSL 3.3.6 (macOS).
Every certificate is self-signed except the two `child-of-*`, and every
signature was checked with `openssl verify` before being kept, so a refusal
in the tests is the link profile's, never a bad signature. Only public data
is kept; the private keys were discarded.

| File | Key | Signature algorithm | Expected |
|---|---|---|---|
| `rsa2048-sha256.der`, `-sha384`, `-sha512` | RSA 2048, e = 65537 | sha{256,384,512}WithRSAEncryption | verifies |
| `rsae3-sha256.der` | RSA 2048, e = 3 | sha256WithRSAEncryption | verifies |
| `rsae2p33m1-sha256.der` | RSA 2048, e = 2^33 - 1 | sha256WithRSAEncryption | verifies |
| `rsa2052-sha256.der` | RSA 2052 | sha256WithRSAEncryption | verifies (not a multiple of 8) |
| `p256-sha256.der`, `p256-sha384.der` | P-256 | ecdsa-with-SHA256/384 | verifies |
| `child-of-rsa2048-sha384.der` | P-256 | sha384WithRSAEncryption by `rsa2048-sha256.der`'s key | verifies under that key |
| `child-of-p256-sha384.der` | RSA 2048 | ecdsa-with-SHA384 by `p256-sha256.der`'s key | verifies under that key |
| `rsa1024-sha256.der` | RSA 1024 | sha256WithRSAEncryption | refused: below 2048 bits |
| `rsae2p33p1-sha256.der` | RSA 2048, e = 2^33 + 1 | sha256WithRSAEncryption | refused: e above 33 bits |
| `rsa2048-sha1.der` | RSA 2048 | sha1WithRSAEncryption | refused |
| `rsa2048-pss.der` | RSA 2048 | RSASSA-PSS (SHA-256, salt 32) | refused |
| `p256-sha512.der` | P-256 | ecdsa-with-SHA512 | refused |
| `p384-sha384.der` | P-384 | ecdsa-with-SHA384 | refused until P17 |
| `p256-compressed.spki.der` | `p256-sha256.der`'s key, compressed point | (an SPKI, not a certificate) | refused |

To regenerate (new keys give new files; the tests read only these, so they
need no change):

```sh
mk() { name=$1; key=$2; dg=$3; shift 3
  openssl req -new -x509 -key $key -$dg -days 3650 -subj "/CN=clazel link test $name" \
    -set_serial 1 "$@" -outform DER -out $name.der; }
openssl ecparam -name prime256v1 -genkey -noout -out p256.pem
openssl ecparam -name secp384r1 -genkey -noout -out p384.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out r2048.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:1024 -out r1024.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2052 -out r2052.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -pkeyopt rsa_keygen_pubexp:3 -out re3.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -pkeyopt rsa_keygen_pubexp:8589934591 -out rmax.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -pkeyopt rsa_keygen_pubexp:8589934593 -out rbig.pem
mk p256-sha256 p256.pem sha256; mk p256-sha384 p256.pem sha384; mk p256-sha512 p256.pem sha512
mk p384-sha384 p384.pem sha384
mk rsa2048-sha256 r2048.pem sha256; mk rsa2048-sha384 r2048.pem sha384
mk rsa2048-sha512 r2048.pem sha512; mk rsa2048-sha1 r2048.pem sha1
mk rsa2048-pss r2048.pem sha256 -sigopt rsa_padding_mode:pss -sigopt rsa_pss_saltlen:32
mk rsa1024-sha256 r1024.pem sha256; mk rsa2052-sha256 r2052.pem sha256
mk rsae3-sha256 re3.pem sha256
mk rsae2p33m1-sha256 rmax.pem sha256; mk rsae2p33p1-sha256 rbig.pem sha256
openssl x509 -inform DER -in rsa2048-sha256.der -out rsaroot.pem
openssl x509 -inform DER -in p256-sha256.der -out p256root.pem
openssl req -new -key p256.pem -subj "/CN=clazel link test child of rsa" -out c1.csr
openssl x509 -req -in c1.csr -CA rsaroot.pem -CAkey r2048.pem -set_serial 2 -sha384 \
  -days 3650 -outform DER -out child-of-rsa2048-sha384.der
openssl req -new -key r2048.pem -subj "/CN=clazel link test child of p256" -out c2.csr
openssl x509 -req -in c2.csr -CA p256root.pem -CAkey p256.pem -set_serial 3 -sha384 \
  -days 3650 -outform DER -out child-of-p256-sha384.der
openssl ec -in p256.pem -pubout -conv_form compressed -outform DER -out p256-compressed.spki.der
```

Ed25519 certificates could not be made (LibreSSL 3.3.6 has no Ed25519
`req`); the test refuses the Ed25519 and Ed448 OIDs with a hand-built
AlgorithmIdentifier instead.

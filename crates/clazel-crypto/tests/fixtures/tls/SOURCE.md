# TLS end-to-end fixtures

Generated on 2026-10-31 with OpenSSL 3.5.4 (Git for Windows' MSYS2 build) for
`tests/conformance_tls.rs`. Everything is test data. The private keys of the
leaves are vendored (`*.key.der`, PKCS#8) because the rustls test server needs
them to sign CertificateVerify; they protect nothing. The root's and the two
intermediates' keys were discarded after signing. Nothing here is trusted by
any other test or by the browser: the end-to-end test builds its trust store
from `root.der` alone (`join::exec::ChainVerifier::new`), where production
uses Mozilla's roots (`join::exec::mozilla`, `clazel_x509::roots::ROOTS`).

| File | What | Key | Signed by (algorithm) | Validity |
|---|---|---|---|---|
| `root.der` | test root, CA, self-signed | RSA 2048 | itself (sha256WithRSAEncryption) | 2019-01-01 to 2046-01-01 |
| `intermediate.der` | CA, pathlen 0 | RSA 2048 | root (sha256WithRSAEncryption) | 2019-01-01 to 2046-01-01 |
| `leaf-ecdsa.der`, `.key.der` | `test.example`, SAN dNSName, serverAuth | ECDSA P-256 | intermediate (sha256WithRSAEncryption, PKCS#1 v1.5) | 2019-01-01 to 2046-01-01 |
| `leaf-rsa.der`, `.key.der` | `test.example` | RSA 2048 (the server signs CertificateVerify with rsa_pss_rsae_sha256) | intermediate (sha256WithRSAEncryption, PKCS#1 v1.5) | 2019-01-01 to 2046-01-01 |
| `leaf-other-name.der`, `.key.der` | `other.example` (a certificate for another name) | ECDSA P-256 | intermediate | 2019-01-01 to 2046-01-01 |
| `leaf-expired.der`, `.key.der` | `test.example`, expired | ECDSA P-256 | intermediate | 2020-01-01 to 2021-01-01 |
| `intermediate-expired.der` | CA, pathlen 0, expired | RSA 2048 | root | 2019-01-01 to 2021-01-01 |
| `leaf-under-expired-intermediate.der` | `test.example`; its key is `leaf-ecdsa.key.der` | ECDSA P-256 | `intermediate-expired.der` | 2019-01-01 to 2046-01-01 |
| `self-signed.der`, `.key.der` | `test.example` leaf, not a CA | ECDSA P-256 | itself (ecdsa-with-SHA256) | 2019-01-01 to 2046-01-01 |

The test validates at 2026-10-31T12:00:00Z (Unix time 1793448000). The three
chains that should validate were checked with `openssl verify -attime
1793448000` before the files were kept, so a refusal in the test is the
client's, never a bad signature.

To regenerate (new keys give new files; the test reads only these files, so
it needs no change; on MSYS2 export `MSYS2_ARG_CONV_EXCL='*'` first so that
`-subj "/CN=..."` is not rewritten as a path):

```sh
NB=20190101000000Z; NA=20460101000000Z
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out root.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out int.pem
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out leaf-rsa.pem
openssl genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out leaf-ecdsa.pem
openssl genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out leaf-other-name.pem
openssl genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out leaf-expired.pem
openssl genpkey -algorithm EC -pkeyopt ec_paramgen_curve:P-256 -out self-signed.pem
printf 'basicConstraints=critical,CA:TRUE\nkeyUsage=critical,keyCertSign,cRLSign\n' > ca.ext
printf 'basicConstraints=critical,CA:TRUE,pathlen:0\nkeyUsage=critical,keyCertSign,cRLSign\n' > int.ext
leafext() { printf 'basicConstraints=critical,CA:FALSE\nkeyUsage=critical,digitalSignature\nextendedKeyUsage=serverAuth\nsubjectAltName=DNS:%s\n' "$1" > "$2"; }
leafext test.example leaf.ext
leafext other.example other.ext
openssl req -new -key root.pem -subj "/CN=clazel TLS test root" -out root.csr
openssl x509 -req -in root.csr -signkey root.pem -sha256 -set_serial 1 -not_before $NB -not_after $NA -extfile ca.ext -outform DER -out root.der
openssl x509 -inform DER -in root.der -out root.crt
openssl req -new -key int.pem -subj "/CN=clazel TLS test intermediate" -out int.csr
openssl x509 -req -in int.csr -CA root.crt -CAkey root.pem -sha256 -set_serial 2 -not_before $NB -not_after $NA -extfile int.ext -outform DER -out intermediate.der
openssl x509 -inform DER -in intermediate.der -out int.crt
leaf() { name=$1; key=$2; ext=$3; nb=$4; na=$5; serial=$6; cn=$7
  openssl req -new -key $key -subj "/CN=$cn" -out $name.csr
  openssl x509 -req -in $name.csr -CA int.crt -CAkey int.pem -sha256 -set_serial $serial -not_before $nb -not_after $na -extfile $ext -outform DER -out $name.der; }
leaf leaf-ecdsa leaf-ecdsa.pem leaf.ext $NB $NA 10 test.example
leaf leaf-rsa leaf-rsa.pem leaf.ext $NB $NA 11 test.example
leaf leaf-other-name leaf-other-name.pem other.ext $NB $NA 12 other.example
leaf leaf-expired leaf-expired.pem leaf.ext 20200101000000Z 20210101000000Z 13 test.example
openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:2048 -out int-expired.pem
openssl req -new -key int-expired.pem -subj "/CN=clazel TLS test expired intermediate" -out intx.csr
openssl x509 -req -in intx.csr -CA root.crt -CAkey root.pem -sha256 -set_serial 3 -not_before $NB -not_after 20210101000000Z -extfile int.ext -outform DER -out intermediate-expired.der
openssl x509 -inform DER -in intermediate-expired.der -out intx.crt
openssl req -new -key leaf-ecdsa.pem -subj "/CN=test.example" -out lx.csr
openssl x509 -req -in lx.csr -CA intx.crt -CAkey int-expired.pem -sha256 -set_serial 15 -not_before $NB -not_after $NA -extfile leaf.ext -outform DER -out leaf-under-expired-intermediate.der
openssl req -new -key self-signed.pem -subj "/CN=test.example" -out ss.csr
openssl x509 -req -in ss.csr -signkey self-signed.pem -sha256 -set_serial 14 -not_before $NB -not_after $NA -extfile leaf.ext -outform DER -out self-signed.der
for k in leaf-ecdsa leaf-rsa leaf-other-name leaf-expired self-signed; do
  openssl pkcs8 -topk8 -nocrypt -in $k.pem -outform DER -out $k.key.der; done
for c in leaf-ecdsa leaf-rsa leaf-other-name; do
  openssl x509 -inform DER -in $c.der -out $c.crt
  openssl verify -attime 1793448000 -CAfile root.crt -untrusted int.crt $c.crt; done
```

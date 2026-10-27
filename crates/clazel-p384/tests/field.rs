//! Field arithmetic (`clazel_p384::field`) against known answers.
//!
//! Every expected value below was computed with Python 3 integers
//! (`(a + b) % m`, `a * b % m`, `pow(a, -1, m)`, `pow(a, e, m)`), not with
//! this crate or fiat-crypto. The inputs are P-384's base point
//! coordinates (SP 800-186 §3.2.1.4) and small or boundary values, for both
//! moduli. All values are 48 octets, big-endian, as 96 hexadecimal digits.
//!
//! The proofs show the field functions meet `field/contract.rs` over six
//! axioms that state fiat-crypto's printed postconditions; these tests are
//! the independent check on those axioms and on the constants in `spec.rs`
//! (that fiat's `m` is p and n, and that its Montgomery domain is the one
//! the code assumes).

use clazel_p384::field::{Fe, Which};

type TestResult = Result<(), String>;

fn octets(hex: &str) -> Result<[u8; 48], String> {
    let digits = hex.as_bytes();
    if digits.len() != 96 {
        return Err(format!("{} hex digits, want 96", digits.len()));
    }
    let mut out = [0u8; 48];
    for (slot, pair) in out.iter_mut().zip(digits.chunks(2)) {
        let pair = std::str::from_utf8(pair).map_err(|e| e.to_string())?;
        *slot = u8::from_str_radix(pair, 16).map_err(|e| format!("{pair}: {e}"))?;
    }
    Ok(out)
}

fn hex(o: &[u8; 48]) -> String {
    o.iter().map(|b| format!("{b:02x}")).collect()
}

fn elem(w: Which, hex: &str) -> Result<Fe, String> {
    Fe::from_octets(w, &octets(hex)?).ok_or_else(|| format!("{hex} was refused"))
}

fn same(f: &Fe, expect: &str) -> TestResult {
    let got = hex(&f.to_octets());
    if got == expect {
        Ok(())
    } else {
        Err(format!("got {got}, want {expect}"))
    }
}

fn named(w: Which) -> &'static str {
    match w {
        Which::P => "p",
        Which::N => "n",
    }
}

/// Binary operations: `(a, b, a + b, a - b, a * b)` modulo p.
const BINARY_P: &[(&str, &str, &str, &str, &str)] = &[
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        "e09fa86d54b131a6ec505fde85b3899e6711591fb441b01543d172f43844e2f85f63a42bdcd3ab09b4977bb503601916",
        "746febd82864d8c831132e5f608dd14a75291da5630d871b701d10cccc6371784aa2408fa1d6a7cec01140bbe18bfc58",
        "332e559389c970313cb29c4b55af5783821971a99c250daf84dc5d3cc441cb0a482e90de9d3ccd96b3c8c48b2ad3f025",
    ),
    (
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "e09fa86d54b131a6ec505fde85b3899e6711591fb441b01543d172f43844e2f85f63a42bdcd3ab09b4977bb503601916",
        "8b901427d79b2737ceecd1a09f722eb58ad6e25a9cf278e48fe2ef33339c8e86b55dbf6f5e2958313feebf451e7403a7",
        "332e559389c970313cb29c4b55af5783821971a99c250daf84dc5d3cc441cb0a482e90de9d3ccd96b3c8c48b2ad3f025",
    ),
    (
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd",
    ),
    (
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "abab0f8a4836d3268fd50c867ccc7b636f4080ca155369875b1a87480bfff827562637c54900f75b3b77a39ffc21d8a6",
        "569b7b44cb20c8b772717e48968b207a93060a04fe043256a72c03870757a3b5ac205308ca56a482c6cee7301735c337",
        "5f493ac6c23d5d581f526ddd722c90d72931e9fc1f3518e8695a688e14dc6b6424c2fa7740139e4eb626418d6d335eed",
    ),
    (
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffb",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
];

/// Inverses: `(a, a^-1 or none)` modulo p.
const INVERSE_P: &[(&str, Option<&str>)] = &[
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        None,
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        Some(
            "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        ),
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002",
        Some(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffff800000000000000080000000",
        ),
    ),
    (
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        Some(
            "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        ),
    ),
    (
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd",
        Some(
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffff80000000000000007fffffff",
        ),
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        Some(
            "1ce18121749aa29a393faddf4e55522af8c67dabdfa413aac45da5c5f0781147133e1c96ca2a8234440fbf89e7e96410",
        ),
    ),
    (
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        Some(
            "9eee8231a5913c8aac5a8f03b92fee93f6d05a5777cb0bf87063909e7e5682f7a26736b36031e4006ecf009e5f9c8231",
        ),
    ),
    (
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        Some(
            "083ba7221f8540bce4baa0d81a28cd3a9cd5fda67bd6eacf37bcee804c2e7a83953328d6fdb7499c7a3679d32aec85a7",
        ),
    ),
];

/// Powers: `(a, e, a^e)` modulo p, `e` also 48 octets.
const POWER_P: &[(&str, &str, &str)] = &[
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002",
        "046af925fa51ac496728217df5bc7c1fc3353aca34a380e1ffd8419fe7b13f6a92e8614fee38a288e2222412aca8b019",
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010001",
        "8be4f5f04eb6f8dd47bacdb4bdbaa5d645906f972413e32f27854253e3b3dd7104f0a7748db0d2fca2dd2297545ac094",
    ),
    (
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd",
        "9eee8231a5913c8aac5a8f03b92fee93f6d05a5777cb0bf87063909e7e5682f7a26736b36031e4006ecf009e5f9c8231",
    ),
    (
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "6d2588c497808712d6ddb0bccfa7c5bbdea4947e8b014335a6fc80d42c46cf26d22a7fd8366812b09d0027a62c8848e5",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002",
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "0f7ab66865508d65dd41b1dbcc104f7cfb6b19188236ea7315ba8a86ef07bcc8a216fd6963428a0365bd81b0a0fc4022",
    ),
    (
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "1951c767fbd507d75dfcdd0ab00c04ce5e9f8c840b62a913637f975804279291b82f84bf0735488baa9f6d05cc6cef4b",
    ),
];

/// Octet strings of p that are residues, and ones that are not.
const IN_RANGE_P: &[&str] = &[
    "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd",
    "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
];
const OUT_OF_RANGE_P: &[&str] = &[
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff000000000000000100000000",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000100000000ffffffff",
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
];

/// Binary operations: `(a, b, a + b, a - b, a * b)` modulo n.
const BINARY_N: &[(&str, &str, &str, &str, &str)] = &[
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        "e09fa86d54b131a6ec505fde85b3899e6711591fb441b01543d172f43844e2f85f63a42bdcd3ab09b4977bb503601916",
        "746febd82864d8c831132e5f608dd14a75291da5630d871b701d10cccc6371784aa2408fa1d6a7cec01140bbe18bfc58",
        "2a8e172f52ea8a3f1864714efafb6588d0ed2fc509e9b4502bdd369bdbeeb9019f58804fbe958008223ba8752ead1f2c",
    ),
    (
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "e09fa86d54b131a6ec505fde85b3899e6711591fb441b01543d172f43844e2f85f63a42bdcd3ab09b4977bb503601916",
        "8b901427d79b2737ceecd1a09f722eb58ad6e25a9cf278e457463cb527d3bc670d77cd22a6d9ffac2cdad8aeeb392d1b",
        "2a8e172f52ea8a3f1864714efafb6588d0ed2fc509e9b4502bdd369bdbeeb9019f58804fbe958008223ba8752ead1f2c",
    ),
    (
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971",
    ),
    (
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "abab0f8a4836d3268fd50c867ccc7b636f4080ca155369875b1a87480bfff827562637c54900f75b3b77a39ffc21d8a6",
        "569b7b44cb20c8b772717e48968b207a93060a04fe0432566e8f5108fb8ed196043a60bc13074bfdb3bb0099e3faecab",
        "f08ef28044c2bdaf8ddc2192b5cc753040ed1aa5298de782dde9d083376e1963df48de687b5dd8e9f9535ded3d5f646a",
    ),
    (
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc5296f",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
];

/// Inverses: `(a, a^-1 or none)` modulo n.
const INVERSE_N: &[(&str, Option<&str>)] = &[
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        None,
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        Some(
            "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        ),
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002",
        Some(
            "7fffffffffffffffffffffffffffffffffffffffffffffffe3b1a6c0fa1b96efac0d06d9245853bd76760cb5666294ba",
        ),
    ),
    (
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        Some(
            "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        ),
    ),
    (
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971",
        Some(
            "7fffffffffffffffffffffffffffffffffffffffffffffffe3b1a6c0fa1b96efac0d06d9245853bd76760cb5666294b9",
        ),
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        Some(
            "c0345088d98aa2f119e693230bbfb7a15f02792e7267cb55b3b0da1cb38a1c5d5f05c8d102d5128f524604074c4c8846",
        ),
    ),
    (
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        Some(
            "195089baf8f5f0aff5c30a6cbde5b89a548ed7f739d253a675186a655eb60fe5e7973625ab399512e7a68c6b1bc8c167",
        ),
    ),
    (
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        Some(
            "46ae825365df7a1d62825d81fa487fc38308db2cd6f56ceb22e631917f150eb006e8baeef59facc741d22ac15aad230b",
        ),
    ),
];

/// Powers: `(a, e, a^e)` modulo n, `e` also 48 octets.
const POWER_N: &[(&str, &str, &str)] = &[
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002",
        "a067a4d6fd10d2108a2d4649446529d5501f3734e9d5075a68178b74a7fb933b79d068c4f3d6e8585115c859fd9c0bc3",
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010001",
        "86970749f08da887bd258aa6157760202526bd6275c5c393748c139aedc22ff58ee3fd0e4711f8ede5fd57ed73fc8829",
    ),
    (
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971",
        "195089baf8f5f0aff5c30a6cbde5b89a548ed7f739d253a675186a655eb60fe5e7973625ab399512e7a68c6b1bc8c167",
    ),
    (
        "3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "89cb315840a564fc1a7bdefc1d2c84f6afada827883d396e812a65c2c2a8b87239d53ba024b3f5a98bcf81839f72e558",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    ),
    (
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    ),
    (
        "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002",
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "51851b3973f5614cee410b803872239260684ee82effe90e9cea8f1b9d52761671bc824bec54e198a0b9dc974b59cb84",
    ),
    (
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "5cc922b0883daf1711b0da1e33bb3154cb48799d3c77ccd77a957c5a7ddc436db68e3ce6fab6ac4d37e74c8a8b43b4e7",
    ),
];

/// Octet strings of n that are residues, and ones that are not.
const IN_RANGE_N: &[&str] = &[
    "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
    "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001",
    "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52972",
    "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52971",
    "aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7",
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
];
const OUT_OF_RANGE_N: &[&str] = &[
    "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973",
    "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52974",
    "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77becec196accc52973",
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe",
];

/// One modulus and its known answers.
struct Table {
    which: Which,
    binary: &'static [(
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
    )],
    inverse: &'static [(&'static str, Option<&'static str>)],
    power: &'static [(&'static str, &'static str, &'static str)],
    in_range: &'static [&'static str],
    out_of_range: &'static [&'static str],
}

const TABLES: [Table; 2] = [
    Table {
        which: Which::P,
        binary: BINARY_P,
        inverse: INVERSE_P,
        power: POWER_P,
        in_range: IN_RANGE_P,
        out_of_range: OUT_OF_RANGE_P,
    },
    Table {
        which: Which::N,
        binary: BINARY_N,
        inverse: INVERSE_N,
        power: POWER_N,
        in_range: IN_RANGE_N,
        out_of_range: OUT_OF_RANGE_N,
    },
];

#[test]
fn add_sub_mul_known_answers() -> TestResult {
    for t in &TABLES {
        let w = t.which;
        for &(a, b, sum, diff, prod) in t.binary {
            let (x, y) = (elem(w, a)?, elem(w, b)?);
            same(&x.add(&y), sum).map_err(|e| format!("mod {}: {a} + {b}: {e}", named(w)))?;
            same(&x.sub(&y), diff).map_err(|e| format!("mod {}: {a} - {b}: {e}", named(w)))?;
            same(&x.mul(&y), prod).map_err(|e| format!("mod {}: {a} * {b}: {e}", named(w)))?;
        }
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "each inverse is 768 field multiplications")]
fn inverse_known_answers() -> TestResult {
    for t in &TABLES {
        let w = t.which;
        for &(a, expect) in t.inverse {
            let x = elem(w, a)?;
            match (x.inv(), expect) {
                (Some(got), Some(want)) => {
                    same(&got, want).map_err(|e| format!("mod {}: inv {a}: {e}", named(w)))?;
                    if !x.mul(&got).equals(&Fe::one(w)) {
                        return Err(format!("mod {}: {a} * inv {a} is not 1", named(w)));
                    }
                }
                (None, None) => {}
                (Some(_), None) => return Err(format!("mod {}: inv {a} should be none", named(w))),
                (None, Some(_)) => return Err(format!("mod {}: inv {a} should exist", named(w))),
            }
        }
    }
    Ok(())
}

/// The three inverses the task names: of 1, of 2 and of m - 1, spelled out.
#[test]
#[cfg_attr(miri, ignore = "each inverse is 768 field multiplications")]
fn inverse_of_one_two_and_minus_one() -> TestResult {
    let tail = |last: &str| format!("{}{last}", "0".repeat(94));
    for t in &TABLES {
        let w = t.which;
        let one = elem(w, &tail("01"))?;
        let two = elem(w, &tail("02"))?;
        same(&one.inv().ok_or("inv 1")?, &tail("01"))?;
        // inv 2 = (m + 1) / 2, so 2 * inv 2 = 1.
        let half = two.inv().ok_or("inv 2")?;
        if !two.mul(&half).equals(&one) {
            return Err(format!("mod {}: 2 * inv 2 is not 1", named(w)));
        }
        // m - 1 = 1 - 2 is its own inverse: (-1)(-1) = 1.
        let minus_one = one.sub(&two);
        same(
            &minus_one.inv().ok_or("inv -1")?,
            &hex(&minus_one.to_octets()),
        )?;
    }
    Ok(())
}

#[test]
#[cfg_attr(miri, ignore = "each power is up to 768 field multiplications")]
fn pow_known_answers() -> TestResult {
    for t in &TABLES {
        let w = t.which;
        for &(a, e, expect) in t.power {
            let got = elem(w, a)?.pow(&octets(e)?);
            same(&got, expect).map_err(|err| format!("mod {}: {a} ^ {e}: {err}", named(w)))?;
        }
    }
    Ok(())
}

#[test]
fn octets_round_trip_and_the_range_check() -> TestResult {
    for t in &TABLES {
        let w = t.which;
        for &h in t.in_range {
            same(&elem(w, h)?, h).map_err(|e| format!("mod {}: round trip {h}: {e}", named(w)))?;
        }
        for &h in t.out_of_range {
            if Fe::from_octets(w, &octets(h)?).is_some() {
                return Err(format!("mod {}: {h} is not below the modulus", named(w)));
            }
        }
    }
    Ok(())
}

#[test]
fn p_minus_one_is_a_residue_mod_p_but_not_mod_n() -> TestResult {
    let p_minus_1 = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffe";
    if Fe::from_octets(Which::P, &octets(p_minus_1)?).is_none() {
        return Err("p - 1 should be a residue mod p".into());
    }
    if Fe::from_octets(Which::N, &octets(p_minus_1)?).is_some() {
        return Err("p - 1 is above n".into());
    }
    Ok(())
}

#[test]
fn one_and_equality() -> TestResult {
    for t in &TABLES {
        let w = t.which;
        same(&Fe::one(w), &format!("{}01", "0".repeat(94)))?;
        for &(a, b, ..) in t.binary {
            let (x, y) = (elem(w, a)?, elem(w, b)?);
            if x.equals(&y) != (a == b) {
                return Err(format!("mod {}: {a} equals {b} is wrong", named(w)));
            }
            if !x.equals(&x) {
                return Err(format!("mod {}: {a} does not equal itself", named(w)));
            }
        }
    }
    Ok(())
}

//! Where `mutations.json`'s evaluated certificates are added when they run.
//! Empty on purpose: Verus evaluates every `compute_only` assertion of a
//! module it verifies, even when it verifies one function, so a certificate
//! beside `examples` would stop at the examples' own assertions, which are
//! false in the mutant. In this module only the certificate is evaluated.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

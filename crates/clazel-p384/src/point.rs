//! Points of P-384 and the group law, executable and proven against
//! [`crate::spec`]. Affine coordinates, SEC 1 §2.2.1's rules in the spec's
//! order; every branch performs the spec's field operations on [`Fe`]s modulo
//! p, so each proof is a composition of the field contracts. The key decoding
//! (SEC 1 §2.3.4, §2.3.6 and SP 800-186 D.1.1.1) is here too.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

use crate::convert::fe_of_byte;
use crate::field::Fe;

/// A point of the curve: the point at infinity, or an affine pair of
/// residues modulo p. Its view is the spec's [`crate::spec::Point`] with
/// those residues as coordinates.
pub enum Point {
    /// The identity element, `O`.
    Infinity,
    /// `(x, y)`, both residues modulo p (see [`Point::wf`]).
    Affine {
        /// The x-coordinate.
        x: Fe,
        /// The y-coordinate.
        y: Fe,
    },
}

impl View for Point {
    type V = crate::spec::Point;

    open spec fn view(&self) -> crate::spec::Point {
        match self {
            Point::Infinity => crate::spec::Point::Infinity,
            Point::Affine { x, y } => crate::spec::Point::Affine { x: x.val(), y: y.val() },
        }
    }
}

impl Point {
    /// Both coordinates are residues modulo p, not modulo n. (They are below
    /// p by the type invariant of [`Fe`], as modelling choice 4 of
    /// [`crate::spec`] has it.)
    pub open spec fn wf(&self) -> bool {
        match self {
            Point::Infinity => true,
            Point::Affine { x, y } => x.which() == crate::field::spec::Which::P && y.which() == crate::field::spec::Which::P,
        }
    }

    /// A copy.
    pub fn dup(&self) -> (r: Point)
        requires
            self.wf(),
        ensures
            r.wf(),
            r@ == self@,
    {
        match self {
            Point::Infinity => Point::Infinity,
            Point::Affine { x, y } => Point::Affine { x: x.dup(), y: y.dup() },
        }
    }
}

/// The views of an optional point.
pub open spec fn opt_view(o: &Option<Point>) -> Option<crate::spec::Point> {
    match o {
        Some(p) => Some(p@),
        None => None,
    }
}

/// An optional point is well formed.
pub open spec fn opt_wf(o: &Option<Point>) -> bool {
    match o {
        Some(p) => p.wf(),
        None => true,
    }
}

/// The residue 0 modulo p.
fn zero_p() -> (r: Fe)
    ensures
        r.which() == crate::field::spec::Which::P,
        r.val() == 0,
{
    fe_of_byte(crate::field::spec::Which::P, 0)
}

/// The curve constant b as a residue modulo p.
fn const_b() -> (r: Fe)
    ensures
        r.which() == crate::field::spec::Which::P,
        r.val() == p384().b,
{
    let o: [u8; 48] = [0xb3, 0x31, 0x2f, 0xa7, 0xe2, 0x3e, 0xe7, 0xe4, 0x98, 0x8e, 0x05, 0x6b, 0xe3, 0xf8, 0x2d, 0x19, 0x18, 0x1d, 0x9c, 0x6e, 0xfe, 0x81, 0x41, 0x12, 0x03, 0x14, 0x08, 0x8f, 0x50, 0x13, 0x87, 0x5a, 0xc6, 0x56, 0x39, 0x8d, 0x8a, 0x2e, 0xd1, 0x9d, 0x2a, 0x85, 0xc8, 0xed, 0xd3, 0xec, 0x2a, 0xef];
    proof {
        crate::lemmas::lemma_b_octets();
        crate::lemmas::lemma_curve_a();
        assert(o@ =~= crate::lemmas::b_octets());
    }
    match Fe::from_octets(crate::field::spec::Which::P, &o) {
        Some(f) => f,
        // Unreachable: os2ip(o) = b < p.
        None => {
            proof {
                assert(false);
            }
            Fe::one(crate::field::spec::Which::P)
        },
    }
}

/// The curve constant Gx as a residue modulo p.
fn const_gx() -> (r: Fe)
    ensures
        r.which() == crate::field::spec::Which::P,
        r.val() == p384().gx,
{
    let o: [u8; 48] = [0xaa, 0x87, 0xca, 0x22, 0xbe, 0x8b, 0x05, 0x37, 0x8e, 0xb1, 0xc7, 0x1e, 0xf3, 0x20, 0xad, 0x74, 0x6e, 0x1d, 0x3b, 0x62, 0x8b, 0xa7, 0x9b, 0x98, 0x59, 0xf7, 0x41, 0xe0, 0x82, 0x54, 0x2a, 0x38, 0x55, 0x02, 0xf2, 0x5d, 0xbf, 0x55, 0x29, 0x6c, 0x3a, 0x54, 0x5e, 0x38, 0x72, 0x76, 0x0a, 0xb7];
    proof {
        crate::lemmas::lemma_gx_octets();
        crate::lemmas::lemma_curve_a();
        assert(o@ =~= crate::lemmas::gx_octets());
    }
    match Fe::from_octets(crate::field::spec::Which::P, &o) {
        Some(f) => f,
        // Unreachable: os2ip(o) = gx < p.
        None => {
            proof {
                assert(false);
            }
            Fe::one(crate::field::spec::Which::P)
        },
    }
}

/// The curve constant Gy as a residue modulo p.
fn const_gy() -> (r: Fe)
    ensures
        r.which() == crate::field::spec::Which::P,
        r.val() == p384().gy,
{
    let o: [u8; 48] = [0x36, 0x17, 0xde, 0x4a, 0x96, 0x26, 0x2c, 0x6f, 0x5d, 0x9e, 0x98, 0xbf, 0x92, 0x92, 0xdc, 0x29, 0xf8, 0xf4, 0x1d, 0xbd, 0x28, 0x9a, 0x14, 0x7c, 0xe9, 0xda, 0x31, 0x13, 0xb5, 0xf0, 0xb8, 0xc0, 0x0a, 0x60, 0xb1, 0xce, 0x1d, 0x7e, 0x81, 0x9d, 0x7a, 0x43, 0x1d, 0x7c, 0x90, 0xea, 0x0e, 0x5f];
    proof {
        crate::lemmas::lemma_gy_octets();
        crate::lemmas::lemma_curve_a();
        assert(o@ =~= crate::lemmas::gy_octets());
    }
    match Fe::from_octets(crate::field::spec::Which::P, &o) {
        Some(f) => f,
        // Unreachable: os2ip(o) = gy < p.
        None => {
            proof {
                assert(false);
            }
            Fe::one(crate::field::spec::Which::P)
        },
    }
}

/// The curve coefficient `a = p - 3` as a residue modulo p.
fn const_a() -> (r: Fe)
    ensures
        r.which() == crate::field::spec::Which::P,
        r.val() == p384().a,
{
    let zero = zero_p();
    let three = fe_of_byte(crate::field::spec::Which::P, 3);
    proof {
        crate::lemmas::lemma_curve_a();
        crate::lemmas::lemma_modulus_gt_256(crate::field::spec::Which::P);
        vstd::arithmetic::div_mod::lemma_small_mod(
            (p384().p - 3) as nat,
            p384().p,
        );
    }
    zero.sub(&three)
}

/// The base point `G` (SP 800-186 §3.2.1.4).
pub fn base() -> (r: Point)
    ensures
        r.wf(),
        r@ == base_point(p384()),
{
    Point::Affine { x: const_gx(), y: const_gy() }
}

/// Rule 4 of SEC 1 §2.2.1: two points with different x-coordinates.
fn add_distinct(x1: &Fe, y1: &Fe, x2: &Fe, y2: &Fe) -> (r: Option<Point>)
    requires
        x1.which() == crate::field::spec::Which::P,
        y1.which() == crate::field::spec::Which::P,
        x2.which() == crate::field::spec::Which::P,
        y2.which() == crate::field::spec::Which::P,
        x1.val() != x2.val(),
    ensures
        opt_wf(&r),
        crate::point_contract::ec_add_ensures(
            crate::spec::Point::Affine { x: x1.val(), y: y1.val() },
            crate::spec::Point::Affine { x: x2.val(), y: y2.val() },
            opt_view(&r),
        ),
{
    let d = x2.sub(x1);
    match d.inv() {
        None => None,
        Some(w) => {
            let num = y2.sub(y1);
            let lambda = num.mul(&w);
            let l2 = lambda.mul(&lambda);
            let t = l2.sub(x1);
            let x3 = t.sub(x2);
            let u = x1.sub(&x3);
            let lu = lambda.mul(&u);
            let y3 = lu.sub(y1);
            Some(Point::Affine { x: x3, y: y3 })
        },
    }
}

/// Rule 5 of SEC 1 §2.2.1: a point added to itself (the case of equal
/// x-coordinates that is not rule 3).
fn add_double(x1: &Fe, y1: &Fe, _x2: &Fe, _y2: &Fe) -> (r: Option<Point>)
    requires
        x1.which() == crate::field::spec::Which::P,
        y1.which() == crate::field::spec::Which::P,
        _x2.which() == crate::field::spec::Which::P,
        _y2.which() == crate::field::spec::Which::P,
        x1.val() == _x2.val(),
        (y1.val() + _y2.val()) % crate::field::spec::modulus(crate::field::spec::Which::P) != 0,
    ensures
        opt_wf(&r),
        crate::point_contract::ec_add_ensures(
            crate::spec::Point::Affine { x: x1.val(), y: y1.val() },
            crate::spec::Point::Affine { x: _x2.val(), y: _y2.val() },
            opt_view(&r),
        ),
{
    let two_y = y1.add(y1);
    match two_y.inv() {
        None => None,
        Some(w) => {
            let xx = x1.mul(x1);
            let xx2 = xx.add(&xx);
            let xx3 = xx2.add(&xx);
            let ca = const_a();
            let num = xx3.add(&ca);
            let lambda = num.mul(&w);
            let l2 = lambda.mul(&lambda);
            let two_x = x1.add(x1);
            let x3 = l2.sub(&two_x);
            let u = x1.sub(&x3);
            let lu = lambda.mul(&u);
            let y3 = lu.sub(y1);
            x1.val_lt_modulus();
            proof {
                crate::lemmas::lemma_curve_a();
                crate::lemmas::lemma_dbl_num(crate::field::spec::modulus(crate::field::spec::Which::P), x1.val(), p384().a);
            }
            Some(Point::Affine { x: x3, y: y3 })
        },
    }
}

/// `a + b`: SEC 1 §2.2.1, [`crate::spec::ec_add`].
pub fn ec_add(a: &Point, b: &Point) -> (r: Option<Point>)
    requires
        a.wf(),
        b.wf(),
    ensures
        opt_wf(&r),
        crate::point_contract::ec_add_ensures(a@, b@, opt_view(&r)),
{
    match (a, b) {
        // SEC 1 §2.2.1 rule 1: O + O = O.
        (Point::Infinity, Point::Infinity) => Some(Point::Infinity),
        // Rule 2: (x, y) + O = O + (x, y) = (x, y).
        (Point::Infinity, Point::Affine { .. }) => Some(b.dup()),
        (Point::Affine { .. }, Point::Infinity) => Some(a.dup()),
        (Point::Affine { x: x1, y: y1 }, Point::Affine { x: x2, y: y2 }) => {
            let zero = zero_p();
            let same_x = x1.equals(x2);
            let ysum = y1.add(y2);
            let ysum_zero = ysum.equals(&zero);
            if same_x && ysum_zero {
                // Rule 3: (x, y) + (x, -y) = O.
                Some(Point::Infinity)
            } else if !same_x {
                add_distinct(x1, y1, x2, y2)
            } else {
                add_double(x1, y1, x2, y2)
            }
        },
    }
}

/// The octet `q[i]` (a zero if there is none, which `requires` rules out).
fn at(q: &[u8], i: usize) -> (b: u8)
    requires
        i < q.len(),
    ensures
        b == q@[i as int],
{
    match q.get(i) {
        Some(b) => *b,
        None => 0,
    }
}

/// The 48 octets `q[off..off + 48]`.
fn copy48(q: &[u8], off: usize) -> (o: [u8; 48])
    requires
        off + 48 <= q.len(),
    ensures
        o@ == q@.subrange(off as int, off as int + 48),
{
    let o = [
        at(q, off.saturating_add(0)),
        at(q, off.saturating_add(1)),
        at(q, off.saturating_add(2)),
        at(q, off.saturating_add(3)),
        at(q, off.saturating_add(4)),
        at(q, off.saturating_add(5)),
        at(q, off.saturating_add(6)),
        at(q, off.saturating_add(7)),
        at(q, off.saturating_add(8)),
        at(q, off.saturating_add(9)),
        at(q, off.saturating_add(10)),
        at(q, off.saturating_add(11)),
        at(q, off.saturating_add(12)),
        at(q, off.saturating_add(13)),
        at(q, off.saturating_add(14)),
        at(q, off.saturating_add(15)),
        at(q, off.saturating_add(16)),
        at(q, off.saturating_add(17)),
        at(q, off.saturating_add(18)),
        at(q, off.saturating_add(19)),
        at(q, off.saturating_add(20)),
        at(q, off.saturating_add(21)),
        at(q, off.saturating_add(22)),
        at(q, off.saturating_add(23)),
        at(q, off.saturating_add(24)),
        at(q, off.saturating_add(25)),
        at(q, off.saturating_add(26)),
        at(q, off.saturating_add(27)),
        at(q, off.saturating_add(28)),
        at(q, off.saturating_add(29)),
        at(q, off.saturating_add(30)),
        at(q, off.saturating_add(31)),
        at(q, off.saturating_add(32)),
        at(q, off.saturating_add(33)),
        at(q, off.saturating_add(34)),
        at(q, off.saturating_add(35)),
        at(q, off.saturating_add(36)),
        at(q, off.saturating_add(37)),
        at(q, off.saturating_add(38)),
        at(q, off.saturating_add(39)),
        at(q, off.saturating_add(40)),
        at(q, off.saturating_add(41)),
        at(q, off.saturating_add(42)),
        at(q, off.saturating_add(43)),
        at(q, off.saturating_add(44)),
        at(q, off.saturating_add(45)),
        at(q, off.saturating_add(46)),
        at(q, off.saturating_add(47)),
    ];
    proof {
        assert(o@ =~= q@.subrange(off as int, off as int + 48));
    }
    o
}

/// `x^3 + a x + b` modulo p: [`crate::spec::curve_rhs`].
fn rhs_fe(x: &Fe) -> (r: Fe)
    requires
        x.which() == crate::field::spec::Which::P,
    ensures
        r.which() == crate::field::spec::Which::P,
        r.val() == curve_rhs(p384(), x.val()),
{
    let x2 = x.mul(x);
    let x3 = x2.mul(x);
    let ca = const_a();
    let ax = ca.mul(x);
    let s = x3.add(&ax);
    let cb = const_b();
    let r = s.add(&cb);
    proof {
        crate::lemmas::lemma_curve_a();
        crate::lemmas::lemma_rhs(crate::field::spec::modulus(crate::field::spec::Which::P), x.val(), p384().a, p384().b);
    }
    r
}

/// `y^2 = x^3 + a x + b` modulo p: [`crate::spec::satisfies_equation`].
fn on_curve(x: &Fe, y: &Fe) -> (r: bool)
    requires
        x.which() == crate::field::spec::Which::P,
        y.which() == crate::field::spec::Which::P,
    ensures
        r == satisfies_equation(p384(), x.val(), y.val()),
{
    let lhs = y.mul(y);
    let rhs = rhs_fe(x);
    lhs.equals(&rhs)
}

/// The key `q` decoded and validated: SEC 1 §2.3.4 (octet string to point,
/// uncompressed form only: choice 7 of [`crate::spec`]) and SP 800-186
/// D.1.1.1, [`crate::spec::decode_public_key`].
pub fn decode_public_key(q: &[u8]) -> (r: Option<Point>)
    ensures
        opt_wf(&r),
        crate::point_contract::decode_public_key_ensures(q@, opt_view(&r)),
{
    // SEC 1 §2.3.4: the input has one of three lengths; the point at
    // infinity (`00`, length 1), the compressed form (length 49) and any
    // other length give no valid key.
    if q.len() != 97 {
        return None;
    }
    // Step 3.2: W must be 04.
    let w: u8 = at(q, 0);
    if w != 4 {
        return None;
    }
    // Step 3.1: parse W || X || Y.
    let xs = copy48(q, 1);
    let ys = copy48(q, 49);
    // Steps 3.3 and 3.4: X and Y are field elements (§2.3.6).
    let x = Fe::from_octets(crate::field::spec::Which::P, &xs);
    let y = Fe::from_octets(crate::field::spec::Which::P, &ys);
    match (x, y) {
        (Some(x), Some(y)) => {
            // Step 3.5: the defining equation.
            if on_curve(&x, &y) {
                // Step 3.6, and the validation of D.1.1.1 (infinity is
                // refused by construction, the coordinates are below p).
                Some(Point::Affine { x, y })
            } else {
                None
            }
        },
        _ => None,
    }
}

} // verus!

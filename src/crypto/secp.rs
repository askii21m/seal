//! secp256k1: the minimum needed to assemble taproot outputs, zero
//! dependencies.
//!
//! Operations: field arithmetic mod p, `lift_x` (BIP340 even-y), point
//! add, and scalar multiplication, enough for `Q = P + t*G`, the NUMS
//! key path, and MuSig2 KeyAgg. There is NO signing here and never
//! will be: the compiler holds no secrets.
//!
//! # Security model (deliberate, load-bearing)
//!
//! Every value through this code is PUBLIC: extern public keys, leaf
//! hashes, tweaks. Constant-time execution is therefore a non-goal;
//! variable-time double-and-add and Fermat inversion are chosen for
//! auditability. Do not reuse this module in signing contexts.
//!
//! # Correctness gates (tests/secp.rs)
//!
//! - k*G against the official BIP340 vectors (Core's own ground truth);
//! - field/point differentials against an independent from-scratch python
//!   reference (big-int arithmetic);
//! - algebraic identities: n*G = infinity, (n-1)*G = -G, 5G + 7G = 12G;
//! - the BIP341 wallet vectors downstream exercise the full tweak path.

/// 256-bit unsigned integer, four little-endian u64 limbs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct U256(pub [u64; 4]);

impl U256 {
    pub const ZERO: U256 = U256([0; 4]);
    pub const ONE: U256 = U256([1, 0, 0, 0]);

    pub fn from_be_bytes(b: &[u8; 32]) -> U256 {
        let mut limbs = [0u64; 4];
        for i in 0..4 {
            let mut w = [0u8; 8];
            w.copy_from_slice(&b[i * 8..i * 8 + 8]);
            limbs[3 - i] = u64::from_be_bytes(w);
        }
        U256(limbs)
    }

    pub fn to_be_bytes(self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for i in 0..4 {
            out[i * 8..i * 8 + 8].copy_from_slice(&self.0[3 - i].to_be_bytes());
        }
        out
    }

    pub fn is_zero(self) -> bool {
        self.0 == [0; 4]
    }

    fn is_odd(self) -> bool {
        self.0[0] & 1 == 1
    }

    /// Bit i (0 = least significant).
    fn bit(self, i: usize) -> bool {
        (self.0[i / 64] >> (i % 64)) & 1 == 1
    }

    fn lt(self, other: U256) -> bool {
        for i in (0..4).rev() {
            if self.0[i] != other.0[i] {
                return self.0[i] < other.0[i];
            }
        }
        false
    }

    pub fn ge(self, other: U256) -> bool {
        !self.lt(other)
    }

    /// (self + other, carry out).
    fn adc(self, other: U256) -> (U256, bool) {
        let mut r = [0u64; 4];
        let mut carry = 0u64;
        for (i, limb) in r.iter_mut().enumerate() {
            let s = self.0[i] as u128 + other.0[i] as u128 + carry as u128;
            *limb = s as u64;
            carry = (s >> 64) as u64;
        }
        (U256(r), carry != 0)
    }

    /// (self - other, borrow out).
    fn sbb(self, other: U256) -> (U256, bool) {
        let mut r = [0u64; 4];
        let mut borrow = 0i128;
        for (i, limb) in r.iter_mut().enumerate() {
            let d = self.0[i] as i128 - other.0[i] as i128 - borrow;
            *limb = d as u64; // two's-complement wrap is the limb result
            borrow = i128::from(d < 0);
        }
        (U256(r), borrow != 0)
    }

    /// Schoolbook 256-by-256 to 512-bit.
    fn mul_wide(self, other: U256) -> [u64; 8] {
        let mut w = [0u64; 8];
        for i in 0..4 {
            let mut carry = 0u128;
            for j in 0..4 {
                let acc = w[i + j] as u128 + self.0[i] as u128 * other.0[j] as u128 + carry;
                w[i + j] = acc as u64;
                carry = acc >> 64;
            }
            w[i + 4] = carry as u64; // i+j < i+4 for j<4; slot was zero
        }
        w
    }

    /// self >> 2 (for deriving (p+1)/4).
    fn shr2(self) -> U256 {
        let l = self.0;
        U256([
            (l[0] >> 2) | (l[1] << 62),
            (l[1] >> 2) | (l[2] << 62),
            (l[2] >> 2) | (l[3] << 62),
            l[3] >> 2,
        ])
    }
}

/// The field prime p = 2^256 - 2^32 - 977.
pub const P: U256 = U256([
    0xFFFF_FFFE_FFFF_FC2F,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
]);

/// The group order n.
///
/// Stored LITTLE-ENDIAN by u64 limb (limb[0] is least significant), like P,
/// GX, and GY above/below. The canonical big-endian value is
///   FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141
/// which splits into 64-bit words MSB-first as
///   FFFF..FFFF | FFFF..FFFE | BAAEDCE6AF48A03B | BFD25E8CD0364141
/// so limb[0]=...4141, limb[3]=FFFF..FFFF below. (An audit lens twice misread
/// this as a wrong first limb by assuming big-endian storage; it is correct.
/// `tests/secp.rs::n_g_is_infinity` asserts N*G == infinity, which pins it.)
pub const N: U256 = U256([
    0xBFD2_5E8C_D036_4141,
    0xBAAE_DCE6_AF48_A03B,
    0xFFFF_FFFF_FFFF_FFFE,
    0xFFFF_FFFF_FFFF_FFFF,
]);

/// 2^256 mod p = 2^32 + 977.
const C: u64 = 0x1_0000_03D1;

const GX: U256 = U256([
    0x59F2_815B_16F8_1798,
    0x029B_FCDB_2DCE_28D9,
    0x55A0_6295_CE87_0B07,
    0x79BE_667E_F9DC_BBAC,
]);
const GY: U256 = U256([
    0x9C47_D08F_FB10_D4B8,
    0xFD17_B448_A685_5419,
    0x5DA4_FBFC_0E11_08A8,
    0x483A_DA77_26A3_C465,
]);

/// A field element, always reduced mod p.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fe(U256);

impl Fe {
    pub const ZERO: Fe = Fe(U256::ZERO);
    pub const ONE: Fe = Fe(U256::ONE);

    /// Reduce an arbitrary 256-bit value (one conditional subtract: the
    /// input is < 2*p whenever it comes from our own arithmetic; general
    /// inputs >= p are still correctly folded since 2^256 < 2p).
    pub fn new(v: U256) -> Fe {
        if v.ge(P) {
            let (r, _) = v.sbb(P);
            Fe(r)
        } else {
            Fe(v)
        }
    }

    /// None when the bytes encode a value >= p (invalid field element).
    pub fn from_be_bytes(b: &[u8; 32]) -> Option<Fe> {
        let v = U256::from_be_bytes(b);
        if v.ge(P) { None } else { Some(Fe(v)) }
    }

    pub fn to_be_bytes(self) -> [u8; 32] {
        self.0.to_be_bytes()
    }

    pub fn is_zero(self) -> bool {
        self.0.is_zero()
    }

    pub fn is_odd(self) -> bool {
        self.0.is_odd()
    }

    fn add(self, other: Fe) -> Fe {
        let (s, carry) = self.0.adc(other.0);
        if carry {
            // value = s + 2^256 == s + C (mod p); s < p here so no second carry.
            let (r, _) = s.adc(U256([C, 0, 0, 0]));
            Fe(r)
        } else {
            Fe::new(s)
        }
    }

    fn sub(self, other: Fe) -> Fe {
        let (d, borrow) = self.0.sbb(other.0);
        if borrow {
            let (r, _) = d.adc(P);
            Fe(r)
        } else {
            Fe(d)
        }
    }

    fn neg(self) -> Fe {
        Fe::ZERO.sub(self)
    }

    fn mul(self, other: Fe) -> Fe {
        Fe(reduce_512(self.0.mul_wide(other.0)))
    }

    fn square(self) -> Fe {
        self.mul(self)
    }

    /// Fermat inversion a^(p-2). Variable-time (public data).
    fn invert(self) -> Fe {
        let (e, _) = P.sbb(U256([2, 0, 0, 0]));
        self.pow(e)
    }

    /// Square root via a^((p+1)/4) (p == 3 mod 4). None if no root exists.
    fn sqrt(self) -> Option<Fe> {
        let (p1, _) = P.adc(U256::ONE); // p+1 < 2^256: no carry
        let r = self.pow(p1.shr2());
        if r.square() == self { Some(r) } else { None }
    }

    /// Square-and-multiply, MSB-first. Variable-time (public data).
    fn pow(self, e: U256) -> Fe {
        let mut acc = Fe::ONE;
        for i in (0..256).rev() {
            acc = acc.square();
            if e.bit(i) {
                acc = acc.mul(self);
            }
        }
        acc
    }
}

/// Reduce a 512-bit product mod p by folding: 2^256 == C (mod p).
fn reduce_512(w: [u64; 8]) -> U256 {
    let lo = U256([w[0], w[1], w[2], w[3]]);
    let hi = [w[4], w[5], w[6], w[7]];

    // lo + hi*C: hi*C is <= 289 bits, four limbs plus a small overflow.
    let mut r = [0u64; 4];
    let mut carry = 0u128;
    for i in 0..4 {
        let acc = lo.0[i] as u128 + hi[i] as u128 * C as u128 + carry;
        r[i] = acc as u64;
        carry = acc >> 64;
    }
    // value == r + carry*2^256 == r + carry*C (mod p); carry <= about 2^34
    // so carry*C fits u128 and the second fold spans at most two limbs.
    let fold = carry * C as u128;
    let (mut t, overflow) = U256(r).adc(U256([fold as u64, (fold >> 64) as u64, 0, 0]));
    if overflow {
        // + 2^256 == + C once more; t wrapped to a tiny value, no recursion.
        let (t2, _) = t.adc(U256([C, 0, 0, 0]));
        t = t2;
    }
    if t.ge(P) {
        let (t2, _) = t.sbb(P);
        t = t2;
    }
    t
}

/// A curve point. Affine plus infinity: chosen for auditability over speed
/// (the compiler performs a handful of point operations per compile).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Point {
    Infinity,
    Affine { x: Fe, y: Fe },
}

/// The generator.
pub const fn generator() -> Point {
    Point::Affine {
        x: Fe(GX),
        y: Fe(GY),
    }
}

impl std::ops::Add for Point {
    type Output = Point;

    fn add(self, other: Point) -> Point {
        let (x1, y1, x2, y2) = match (self, other) {
            (Point::Infinity, q) => return q,
            (p, Point::Infinity) => return p,
            (Point::Affine { x: x1, y: y1 }, Point::Affine { x: x2, y: y2 }) => (x1, y1, x2, y2),
        };
        if x1 == x2 {
            if y1.add(y2).is_zero() {
                return Point::Infinity; // P + (-P)
            }
            // P + P. (y = 0 cannot occur: the group order is odd, so
            // there is no 2-torsion, but degrade safely regardless.)
            if y1.is_zero() {
                return Point::Infinity;
            }
            let three = Fe(U256([3, 0, 0, 0]));
            let lam = three.mul(x1.square()).mul(y1.add(y1).invert());
            let x3 = lam.square().sub(x1).sub(x1);
            let y3 = lam.mul(x1.sub(x3)).sub(y1);
            return Point::Affine { x: x3, y: y3 };
        }
        let lam = y2.sub(y1).mul(x2.sub(x1).invert());
        let x3 = lam.square().sub(x1).sub(x2);
        let y3 = lam.mul(x1.sub(x3)).sub(y1);
        Point::Affine { x: x3, y: y3 }
    }
}

impl std::ops::Neg for Point {
    type Output = Point;

    /// `-P = (x, -y)`: the curve `y^2 = x^3 + 7` is symmetric in y. Used to
    /// form `s*G - e*P` in BIP340 verification.
    fn neg(self) -> Point {
        match self {
            Point::Infinity => Point::Infinity,
            Point::Affine { x, y } => Point::Affine { x, y: y.neg() },
        }
    }
}

impl std::ops::Mul<U256> for Point {
    type Output = Point;

    /// k*self, MSB-first double-and-add. Variable-time (public data).
    fn mul(self, k: U256) -> Point {
        let mut acc = Point::Infinity;
        for i in (0..256).rev() {
            acc = acc + acc;
            if k.bit(i) {
                acc = acc + self;
            }
        }
        acc
    }
}

/// Reduce an arbitrary 256-bit value mod the group order n (one
/// conditional subtract suffices: 2^256 < 2n).
pub fn scalar_mod_n(v: U256) -> U256 {
    if v.ge(N) {
        let (r, _) = v.sbb(N);
        r
    } else {
        v
    }
}

/// `(a + b) mod n` for `a, b < n`. The sum is `< 2n < 2^257`, so a single
/// correction suffices, accounting for a carry out of 256 bits.
pub fn add_mod_n(a: U256, b: U256) -> U256 {
    let (s, carry) = a.adc(b);
    if carry {
        // True sum is 2^256 + s; mod n that is s + (2^256 - n), which is < n.
        let neg_n = U256::ZERO.sbb(N).0;
        s.adc(neg_n).0
    } else if s.ge(N) {
        s.sbb(N).0
    } else {
        s
    }
}

/// `(a * b) mod n` by double-and-add over the bits of `b` (no 512-bit
/// reduction needed; every step stays in `[0, n)`). Variable-time -- public
/// data only, like the rest of this module.
pub fn mul_mod_n(a: U256, b: U256) -> U256 {
    let mut result = U256::ZERO;
    let mut addend = scalar_mod_n(a);
    let b = scalar_mod_n(b);
    for i in 0..256 {
        if b.bit(i) {
            result = add_mod_n(result, addend);
        }
        addend = add_mod_n(addend, addend);
    }
    result
}

/// `(n - x) mod n`, the additive inverse, for `x < n`.
pub fn neg_scalar(x: U256) -> U256 {
    if x.is_zero() { U256::ZERO } else { N.sbb(x).0 }
}

impl Point {
    /// BIP340 x-only lift: the curve point with this x and EVEN y.
    /// None when x >= p or x is not on the curve.
    pub fn lift_x(xb: &[u8; 32]) -> Option<Point> {
        let x = Fe::from_be_bytes(xb)?;
        // y^2 = x^3 + 7
        let y2 = x.square().mul(x).add(Fe(U256([7, 0, 0, 0])));
        let mut y = y2.sqrt()?;
        if y.is_odd() {
            y = y.neg();
        }
        Some(Point::Affine { x, y })
    }

    /// Decode a 33-byte compressed key (02 = even y, 03 = odd y).
    /// None on any other prefix, x >= p, or x off-curve (BIP327 "invalid
    /// public key contribution").
    pub fn from_compressed(b: &[u8; 33]) -> Option<Point> {
        let mut xb = [0u8; 32];
        xb.copy_from_slice(&b[1..]);
        let even = Point::lift_x(&xb)?;
        match (b[0], even) {
            (0x02, p) => Some(p),
            (0x03, Point::Affine { x, y }) => Some(Point::Affine { x, y: y.neg() }),
            _ => None,
        }
    }

    /// The 33-byte compressed encoding; None for infinity.
    pub fn to_compressed(self) -> Option<[u8; 33]> {
        let Point::Affine { x, y } = self else {
            return None;
        };
        let mut out = [0u8; 33];
        out[0] = if y.is_odd() { 0x03 } else { 0x02 };
        out[1..].copy_from_slice(&x.to_be_bytes());
        Some(out)
    }

    pub fn x_bytes(self) -> Option<[u8; 32]> {
        match self {
            Point::Infinity => None,
            Point::Affine { x, .. } => Some(x.to_be_bytes()),
        }
    }

    pub fn has_even_y(self) -> bool {
        match self {
            Point::Infinity => true,
            Point::Affine { y, .. } => !y.is_odd(),
        }
    }
}

#[cfg(test)]
mod tests {
    //! Field-level differentials against the independent python reference
    //! (the point-level vectors live in tests/secp.rs; these reach the
    //! private Fe operations directly).

    use super::*;

    fn fe(hex: &str) -> Fe {
        let mut b = [0u8; 32];
        for i in 0..32 {
            b[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).expect("hex");
        }
        Fe::from_be_bytes(&b).expect("reduced")
    }

    fn hex(f: Fe) -> String {
        f.to_be_bytes().iter().map(|x| format!("{x:02x}")).collect()
    }

    #[test]
    fn field_ops_python_differential() {
        // (a, b, a+b, a-b, a*b, a^-1) triples from the python reference.
        let cases = [
            (
                "f55ff16f66f43360266b95db6f8fec01d76031054306ae4a4b380598f6cfd114",
                "7dc96f776c8423e57a2785489a3f9c43fb6e756876d6ad9a9cac4aa4e72ec193",
                "732960e6d3785745a0931b2409cf8845d2cea66db9dd5be4e7e4503eddfe9678",
                "779681f7fa700f7aac441092d5504fbddbf1bb9ccc3000afae8bbaf40fa10f81",
                "1cadd7a597f54634d51b1fc55608f073c34a9d226e8166c43cd451d6c1a764ee",
                "fbff0613085c1a3fbd068d5dcc84ecbdd1315a5bbb611c552f013b8bf50de553",
            ),
            (
                "2c3a4249d77070058649dbd822dcaf7957586fce428cfb2ca88b94741eda8b07",
                "4814d92093ac8a0f4a2163ab87dee509ba306a58f5888be0edcb2fcd0712028b",
                "744f1b6a6b1cfa14d06b3f83aabb94831188da273815870d9656c44125ec8d92",
                "e425692943c3e5f63c28782c9afdca6f9d2805754d046f4bbac064a617c884ab",
                "0df87b078b244f43c939257cf4d79efc1bf88f7edaeab3aac53266c0ddef9723",
                "32fb437a86c76d30f57b1c0e0076e37e36280e6a1b78adf6aea42a73160405b2",
            ),
            (
                "f46dd28a5499d8efef0b8fb8ee1ec1c5a5e407c9381741d576ba8deb4f59ec3f",
                "76a8277347f52530e1cf979175a178980b3a180d176165c985d85f7e142f1eed",
                "6b15f9fd9c8efe20d0db274a63c03a5db11e1fd64f78a79efc92ed6a63890efd",
                "7dc5ab170ca4b3bf0d3bf827787d492d9aa9efbc20b5dc0bf0e22e6d3b2acd52",
                "267e7fb837d7a96e74739e8ab169db39c796ef8e260590a2b8e88290b64cf325",
                "98aa4d53a7542dfe9ebfd1a87694fbd6f2a4060568e447f69f7e6185921b4530",
            ),
        ];
        for (a, b, add, sub, mul, inv_a) in cases {
            let (fa, fb) = (fe(a), fe(b));
            assert_eq!(hex(fa.add(fb)), add, "a = {a}");
            assert_eq!(hex(fa.sub(fb)), sub, "a = {a}");
            assert_eq!(hex(fa.mul(fb)), mul, "a = {a}");
            assert_eq!(hex(fa.invert()), inv_a, "a = {a}");
            // Identities: a*a^-1 = 1, a - a = 0, a + (-a) = 0.
            assert_eq!(fa.mul(fa.invert()), Fe::ONE);
            assert_eq!(fa.sub(fa), Fe::ZERO);
            assert_eq!(fa.add(fa.neg()), Fe::ZERO);
        }
    }

    #[test]
    fn sqrt_python_differential() {
        let cases = [
            (
                "2734df22b520eef94b98e6c4ac0f23910ddd9e7f4b884f099f4bd86e33a97f2c",
                "e8bc163c82eee18733288c7d4ac636db3a6deb013ef2d37b68322be20edc45cc",
            ),
            (
                "5e6bad672afe0a9caa8c7d7d5aeb89b9916aa15b937108c4e3f62ace74322398",
                "52cd77b955e74cd5cca7e9c8baee353ef9c38fb473a86661ae25606e7d6f548b",
            ),
        ];
        for (v, root) in cases {
            assert_eq!(hex(fe(v).sqrt().expect("residue")), root);
        }
        // A known non-residue has no root (5^3+7 = 132 is one; tested at
        // the lift_x level too).
        let non_residue = fe("0000000000000000000000000000000000000000000000000000000000000084");
        assert!(non_residue.sqrt().is_none());
    }

    #[test]
    fn reduction_edges() {
        // (p-1) + 1 = 0; (p-1)*(p-1) = 1 (since (-1)^2 = 1).
        let p_minus_1 = fe("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e");
        assert_eq!(p_minus_1.add(Fe::ONE), Fe::ZERO);
        assert_eq!(p_minus_1.mul(p_minus_1), Fe::ONE);
        // Encodings >= p are rejected.
        let mut pb = P.to_be_bytes();
        assert!(Fe::from_be_bytes(&pb).is_none());
        pb[31] = 0xff;
        assert!(Fe::from_be_bytes(&pb).is_none());
    }
}

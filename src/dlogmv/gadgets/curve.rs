// Do not edit manually!
// This file was automatically generated by Sage (and cargo fmt).

use std::ops::{Add, Mul, Neg, Sub};

use curve25519_dalek::scalar::Scalar;
use gridiron::*;
use num_traits::Zero;

use sha2::Digest;
use sha2::Sha512;

use serde::{Deserialize, Serialize};

use rand_core::RngCore;

// size of inner field in bits
pub const FP_INNER_BITS: usize = 250;

// scalar field of the inner curve
pub use fp_inner::Fp250 as Fp;

// point on inner curve
#[derive(Copy, Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct CurvePoint {
    pub x: Scalar,
    pub y: Scalar,
}

// p = 1809251394333065553493296640760748560179195344757230816271751023405726101733
fp31!(
    fp_inner, // name of mode
    Fp250,    // name of class
    250,      // length of prime in bits
    9,        // length of prime in 2^31 limbs
    // prime number in limbs, least significant first
    [
        0x732af0e5, 0xdcaefbe, 0x7eb74868, 0x5696e248, 0x7ffffffe, 0x7fffffff, 0x7fffffff,
        0x7fffffff, 0x3
    ],
    // barrett
    [
        0x6a512331, 0x4f890505, 0x6c226f33, 0x3208dff7, 0x316ecd1c, 0x8fb978f, 0x1f5bfaf1,
        0x504f7198, 0
    ],
    // montgomery R mod p
    [0x60000000, 0x233543c6, 0x7c8d4410, 0x60522de5, 0x2a5a476d, 0, 0, 0, 0],
    // montgomery R^2 mod p
    [
        0x70e038c2, 0x5043c12b, 0x4e66f240, 0x425619ce, 0x4c9b95ea, 0x316ecd1c, 0x8fb978f,
        0x1f5bfaf1, 0
    ],
    1105244947
);

pub fn param_d() -> Scalar {
    Scalar::from_bits([
        0x33, 0xd1, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10,
    ])
}

fn sqrt(s: Scalar) -> Option<Scalar> {
    let acc = s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    let acc = acc * s;
    let acc = acc * acc;
    if acc * acc == s {
        Some(acc)
    } else {
        None
    }
}

impl Fp {
    pub fn random<R: RngCore>(rng: &mut R) -> Self {
        let mut limbs: [u8; 32] = [0; 32];
        rng.fill_bytes(&mut limbs);
        limbs[0] = 0;
        limbs.into()
    }
}

impl Zero for CurvePoint {
    fn zero() -> Self {
        CurvePoint {
            x: Scalar::zero(),
            y: Scalar::one(),
        }
    }

    fn is_zero(&self) -> bool {
        *self == CurvePoint::zero()
    }
}

impl CurvePoint {
    pub fn on_curve(&self) -> bool {
        let x2 = self.x * self.x;
        let y2 = self.y * self.y;
        x2 + y2 == Scalar::one() + param_d() * x2 * y2
    }

    pub fn hash(val: &[u8]) -> Self {
        fn hash_cnt(val: &[u8], cnt: u32) -> Option<CurvePoint> {
            // hash (val || cnt)
            let mut hasher = Sha512::default();
            hasher.update(val);
            hasher.update(&cnt.to_le_bytes());

            // y coordinate is hash
            let y = Scalar::from_hash(hasher);

            // isolate x in x^2 + y^2 = 1 + d x^2 y^2
            let y2 = y * y;

            // sqrt(y^2 - 1)
            let y2_1 = y2 - Scalar::one();
            let y2_1_sq = sqrt(y2_1)?;

            // sqrt(d * y^2 - 1)
            let dy2_1 = param_d() * y2 - Scalar::one();
            let dy2_1_sq = sqrt(dy2_1)?;

            // x = sqrt(y^2 - 1) / sqrt(d * y^2 - 1)
            let x = y2_1_sq * dy2_1_sq.invert();
            Some(CurvePoint { x, y })
        }

        let mut cnt: u32 = 0;
        loop {
            match hash_cnt(val, cnt) {
                None => {
                    cnt += 1;
                }
                Some(p) => {
                    debug_assert!(p.on_curve());
                    break p;
                }
            }
        }
    }
}

impl Mul<CurvePoint> for Fp {
    type Output = CurvePoint;

    fn mul(self, point: CurvePoint) -> CurvePoint {
        let mut res = Zero::zero();
        let mut pow = point.clone();
        for bit in self.iter_bit().map(|b| b.0) {
            if bit == 1 {
                res = res + pow;
            }
            pow = pow + pow;
        }
        res
    }
}

impl Add for CurvePoint {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        debug_assert!(self.on_curve());
        debug_assert!(other.on_curve());
        let p = param_d() * self.x * self.y * other.x * other.y;
        let x = (self.x * other.y + other.x * self.y) * (Scalar::one() + p).invert();
        let y = (self.y * other.y - self.x * other.x) * (Scalar::one() - p).invert();
        let p = CurvePoint { x, y };
        debug_assert!(p.on_curve());
        p
    }
}

impl Sub for CurvePoint {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        self + (-other)
    }
}

impl Neg for CurvePoint {
    type Output = Self;

    fn neg(self) -> Self::Output {
        CurvePoint {
            x: -self.x,
            y: self.y,
        }
    }
}

// random generator 1 (hashed to curve)
pub fn g0() -> CurvePoint {
    CurvePoint {
        x: Scalar::from_bits([
            0x44, 0x72, 0x7f, 0x5c, 0xf2, 0x2b, 0xb1, 0x70, 0x45, 0xce, 0xfa, 0x96, 0xc3, 0xfc,
            0xfa, 0x38, 0x9a, 0x28, 0xfb, 0x0f, 0x88, 0xaf, 0xbe, 0x46, 0xd1, 0xf0, 0x73, 0xb5,
            0xe4, 0x4e, 0xc8, 0x0c,
        ]),
        y: Scalar::from_bits([
            0x1f, 0x04, 0xad, 0x91, 0xe4, 0xaf, 0x5a, 0xf0, 0xc0, 0xc5, 0x7f, 0xe6, 0xec, 0xaf,
            0x21, 0x71, 0x98, 0x30, 0x50, 0xbc, 0x7c, 0x39, 0x16, 0x1a, 0xac, 0x52, 0xff, 0xe1,
            0x3a, 0x52, 0xc1, 0x0a,
        ]),
    }
}

// random generator 2 (hashed to curve)
pub fn g1() -> CurvePoint {
    CurvePoint {
        x: Scalar::from_bits([
            0xdb, 0x1e, 0x0a, 0x52, 0x13, 0x69, 0x32, 0x98, 0x03, 0x1a, 0x82, 0x2a, 0xbf, 0x67,
            0x1a, 0x52, 0xf1, 0x13, 0x27, 0x1b, 0x1f, 0xc3, 0xad, 0x18, 0x6d, 0x67, 0xd5, 0x34,
            0xa2, 0xec, 0x9e, 0x0f,
        ]),
        y: Scalar::from_bits([
            0x46, 0x69, 0xe7, 0xe0, 0xa7, 0x47, 0x35, 0x27, 0xc9, 0x33, 0xdc, 0x8c, 0x75, 0xd0,
            0xd0, 0xaa, 0x7f, 0xc7, 0x54, 0xe4, 0x18, 0x64, 0x96, 0xdd, 0xf4, 0x65, 0xaa, 0x66,
            0x85, 0xc2, 0x0f, 0x07,
        ]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand_core::OsRng;

    // scalar mult.: check small multiples
    #[test]
    fn test_scalar_small() {
        for i in 0..50 {
            let gi = Fp::from(i as u32) * g0();
            let mut gi_t: CurvePoint = Zero::zero();
            for _ in 0..i {
                gi_t = gi_t + g0();
            }
            assert_eq!(gi, gi_t);
        }
    }

    // scalar mult.: check associative
    #[test]
    fn test_scalar_associative() {
        for _ in 0..10 {
            let r0 = Fp::random(&mut OsRng);
            let r1 = Fp::random(&mut OsRng);
            assert_eq!((r0 + r1) * g0(), r0 * g0() + r1 * g0());
        }
    }

    // check curve inverse
    #[test]
    fn test_inv() {
        let r = Fp::random(&mut OsRng);
        let p = r * g0();
        assert_eq!(p - p, Zero::zero());
    }

    #[test]
    fn test_hash() {
        for _ in 0..10 {
            let mut msg: [u8; 64] = [0u8; 64];
            OsRng.fill_bytes(&mut msg);
            CurvePoint::hash(&msg);
        }
    }
}

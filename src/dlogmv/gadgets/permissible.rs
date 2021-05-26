use bulletproofs::r1cs::*;
use curve25519_dalek::scalar::Scalar;

use rug::{integer, Integer};

use std::iter::FromIterator;

use super::*;

impl CurvePoint {
    pub fn is_permissible(&self) -> bool {
        assert!(self.on_curve());

        let y_bytes = self.y.as_bytes();
        let x_bytes = self.x.as_bytes();

        // (x, y) is a point on the curve
        // y[31] \in {0, 1} -> y \in [0, 2^250]
        // x mod 2 == 0
        // y is prime
        (y_bytes[31] < 4) && (x_bytes[0] & 1 == 0) & is_prime(&self.y)
    }
}

// x must be in a "small" range
pub const SIZE_X_BITS: usize = 250;

// the entire field
pub const SIZE_Y_BITS: usize = 253;

pub struct Gadget {
    x_bits: bits::Gadget,
    y_bits: bits::Gadget,
}

fn is_prime(x: &Scalar) -> bool {
    let p = Integer::from_digits(x.as_bytes(), integer::Order::Lsf);
    p.is_probably_prime(64) != integer::IsPrime::No
}

impl Gadget {
    pub fn new() -> Self {
        let y_bits = bits::Gadget::new_size(250);
        let x_bits = bits::Gadget::new_even_size(253);
        Self { x_bits, y_bits }
    }

    pub fn gadget<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        witness: Option<CurvePoint>,
    ) -> Result<CurveVariable, R1CSError> {
        #[cfg(test)]
        {
            if let Some(point) = witness {
                assert!(point.is_permissible())
            }
        }

        // compute x as a linear combination
        let x_decomp = self.x_bits.gadget_scalar(cs, witness.map(|p| p.x))?;
        let (x1, x2, xx) = cs.allocate_multiplier(witness.map(|p| (p.x, p.x)))?;
        let x_lin: LinearCombination = x_decomp.into();
        cs.constrain(x1 - x_lin);
        cs.constrain(LinearCombination::from(x1) - x2);

        // compute y as a linear combination
        let y_decomp = self.y_bits.gadget_scalar(cs, witness.map(|p| p.y))?;
        let (y1, y2, yy) = cs.allocate_multiplier(witness.map(|p| (p.y, p.y)))?;
        let y_lin: LinearCombination = y_decomp.into();
        cs.constrain(y1 - y_lin);
        cs.constrain(LinearCombination::from(y1) - y2);

        /*
        // check that x^2 + y^2 = 1 + d x^2 y^2
        let (_, _, xxyy) = cs.multiply(xx.into(), yy.into());
        cs.constrain((xx + yy) - one() - curve::param_d() * xxyy);
        */

        Ok(CurveVariable { x: x1, y: y1 })
    }
}

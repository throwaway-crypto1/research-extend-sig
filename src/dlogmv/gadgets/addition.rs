use super::*;

use bulletproofs::r1cs::*;
use curve25519_dalek::scalar::Scalar;

pub struct Gadget();

pub struct Witness {
    in1: CurvePoint,
    in2: CurvePoint,
    out: CurvePoint,
}

impl Witness {
    pub fn output(&self) -> CurvePoint {
        self.out
    }
}

impl Gadget {
    pub fn witness(in1: CurvePoint, in2: CurvePoint) -> Witness {
        Witness {
            in1,
            in2,
            out: in1 + in2,
        }
    }

    pub fn gadget<CS: ConstraintSystem>(
        cs: &mut CS,
        witness: Option<&Witness>,
    ) -> Result<(CurveVariable, CurveVariable, CurveVariable), R1CSError> {
        let (m1, m2, m3, m4) = match witness {
            Some(w) => {
                let a = w.in1.x * w.in2.y;
                let b = w.in1.y * w.in2.x;
                let c = curve::param_d() * a * b;
                let m1 = cs.allocate_multiplier(Some((w.in1.x, w.in2.y)))?;
                let m2 = cs.allocate_multiplier(Some((w.in1.y, w.in2.x)))?;
                let m3 = cs.allocate_multiplier(Some((Scalar::one() + c, w.out.x)))?;
                let m4 = cs.allocate_multiplier(Some((Scalar::one() - c, w.out.y)))?;
                (m1, m2, m3, m4)
            }
            None => {
                let m1 = cs.allocate_multiplier(None)?;
                let m2 = cs.allocate_multiplier(None)?;
                let m3 = cs.allocate_multiplier(None)?;
                let m4 = cs.allocate_multiplier(None)?;
                (m1, m2, m3, m4)
            }
        };

        let (in1_x, in2_y, a) = m1;
        let (in1_y, in2_x, b) = m2;

        let (one_p_c, out_x, left1) = m3;
        let (one_m_c, out_y, left2) = m4;

        let (_, _, t) = cs.multiply(in1_x + in1_y, in2_y - in2_x);
        let (_, _, c) = cs.multiply(curve::param_d() * a, b.into());

        cs.constrain(one() + c - one_p_c);
        cs.constrain(one() - c - one_m_c);
        cs.constrain(left1 - (a + b));
        cs.constrain(left2 - (t - a + b));

        // the result should fit on the curve
        // (only checked for each individual window in tests)
        #[cfg(debug_assertions)]
        if cfg!(test) {
            let (_, _, x2) = cs.multiply(out_x.into(), out_x.into());
            let (_, _, y2) = cs.multiply(out_y.into(), out_y.into());
            let (_, _, x2y2) = cs.multiply(x2.into(), y2.into());
            cs.constrain((x2 + y2) - (one() + curve::param_d() * x2y2));
        };

        Ok((
            CurveVariable { x: in1_x, y: in1_y },
            CurveVariable { x: in2_x, y: in2_y },
            CurveVariable { x: out_x, y: out_y },
        ))
    }
}

use bulletproofs::r1cs::*;

use num_traits::Zero;

use curve25519_dalek::scalar::Scalar;

use super::*;

pub const WINDOW_SIZE: usize = 3;
pub const WINDOW_ELEMS: usize = 1 << WINDOW_SIZE;

pub struct Witness {
    lookup: CurvePoint,
    b0: bool,
    b1: bool,
    b2: bool,
}

impl Witness {
    pub fn lookup(&self) -> CurvePoint {
        self.lookup
    }

    pub fn bits(&self) -> (bool, bool, bool) {
        (self.b0, self.b1, self.b2)
    }
}

pub struct EdwardsWindow {
    u: [Scalar; WINDOW_ELEMS],
    v: [Scalar; WINDOW_ELEMS],
}

// constrain u = u[s0 + s1*2 + s2*4] with sa = s1 * s2
#[inline(always)]
fn lookup_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    sa: bits::BitVariable,
    s0: bits::BitVariable,
    s1: bits::BitVariable,
    s2: bits::BitVariable,
    e: LinearCombination,
    u: &[Scalar; 8],
) {
    // left side
    let (_, _, left): (Variable, Variable, Variable) = cs.multiply(s0.into(), {
        let f = -(u[0] * sa) + (u[0] * s2) + (u[0] * s1) - u[0] + (u[2] * sa);
        let f = f - (u[2] * s1) + (u[4] * sa) - (u[4] * s2) - (u[6] * sa);
        let f = f + (u[1] * sa) - (u[1] * s2) - (u[1] * s1) + u[1] - (u[3] * sa);
        let f = f + (u[3] * s1) - (u[5] * sa) + (u[5] * s2) + (u[7] * sa);
        f
    });

    // right size
    let right: LinearCombination = e - (u[0] * sa) + (u[0] * s2) + (u[0] * s1) - u[0] + (u[2] * sa);
    let right = right - (u[2] * s1) + (u[4] * sa) - (u[4] * s2) - (u[6] * sa);

    // left == right
    cs.constrain(left - right)
}

impl EdwardsWindow {
    /// Creates a new 3-bit lookup table
    pub fn new(d: Scalar, p1: CurvePoint) -> Self {
        let p0: CurvePoint = Zero::zero();
        let p2 = p1 + p1;
        let p3 = p2 + p1;
        let p4 = p3 + p1;
        let p5 = p4 + p1;
        let p6 = p5 + p1;
        let p7 = p6 + p1;
        EdwardsWindow {
            u: [p0.x, p1.x, p2.x, p3.x, p4.x, p5.x, p6.x, p7.x],
            v: [p0.y, p1.y, p2.y, p3.y, p4.y, p5.y, p6.y, p7.y],
        }
    }

    pub fn lookup(
        &self,
        b0: bool, // scalar (0th bit)
        b1: bool, // scalar (1st bit)
        b2: bool, // scalar (2nd bit)
    ) -> CurvePoint {
        let i0: usize = b0 as usize;
        let i1: usize = b1 as usize;
        let i2: usize = b2 as usize;
        let i = i0 + i1 * 2 + i2 * 4;
        CurvePoint {
            x: self.u[i],
            y: self.v[i],
        }
    }

    /// Compute assignments to intermediate wires.
    /// Computes:
    ///
    /// - uv   (lookup result)
    /// - xy_r (resulting point)
    ///
    /// From:
    ///
    /// - xy (input point)
    /// - s0, s1, s2 (bit decomposition of 3-bit scalar)
    pub fn witness(
        &self,
        b0: bool, // scalar (0th bit)
        b1: bool, // scalar (1st bit)
        b2: bool, // scalar (2nd bit)
    ) -> Witness {
        Witness {
            lookup: self.lookup(b0, b1, b2),
            b0,
            b1,
            b2,
        }
    }

    /// Checks that:
    ///
    /// - uv = window[s0 + 2*s1 + 4*s2]
    /// - xy_r = xy <Edwards Addition> uv
    pub fn gadget<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        witness: Option<&Witness>,
        lookup: CurveVariable,
        s0: bits::BitVariable,
        s1: bits::BitVariable,
        s2: bits::BitVariable, // s = s0 + 2 * s1 + 4 * s2
    ) -> Result<(), R1CSError> {
        let sa = bits::BitVariable::mul(cs, s1, s2);
        lookup_gadget(cs, sa, s0, s1, s2, lookup.x.into(), &self.u);
        lookup_gadget(cs, sa, s0, s1, s2, lookup.y.into(), &self.v);
        Ok(())
    }
}

mod tests {
    use super::*;

    use bulletproofs::{BulletproofGens, PedersenGens};
    use curve25519_dalek::ristretto::CompressedRistretto;
    use merlin::Transcript;
    use rand::{thread_rng, Rng};
    use test::Bencher;

    #[test]
    fn test_lookup_proof() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let mut rng = thread_rng();

        let u: [Scalar; 8] = [
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
        ];

        let b0: bool = rng.gen();
        let b1: bool = rng.gen();
        let b2: bool = rng.gen();

        let i = (b0 as usize) + 2 * (b1 as usize) + 4 * (b2 as usize);

        // happy path
        {
            let mut prover = Prover::new(&pc_gens, Transcript::new(b"Test"));
            let mut verifier = Verifier::new(Transcript::new(b"Test"));

            let s0 = bits::BitVariable::new(&mut prover, b0).unwrap();
            let s1 = bits::BitVariable::new(&mut prover, b1).unwrap();
            let s2 = bits::BitVariable::new(&mut prover, b2).unwrap();
            let sa = bits::BitVariable::mul(&mut prover, s1, s2);

            let blind_e = Scalar::random(&mut rng);
            let value_e = u[i];

            // prove

            let (comm_e, input_e) = prover.commit(value_e, blind_e);

            lookup_gadget(&mut prover, sa, s0, s1, s2, input_e.into(), &u);

            let proof = prover.prove(&bp_gens).unwrap();

            // verify

            let s0 = bits::BitVariable::free(&mut verifier).unwrap();
            let s1 = bits::BitVariable::free(&mut verifier).unwrap();
            let s2 = bits::BitVariable::free(&mut verifier).unwrap();
            let sa = bits::BitVariable::mul(&mut verifier, s1, s2);

            let input_e = verifier.commit(comm_e);

            lookup_gadget(&mut verifier, sa, s0, s1, s2, input_e.into(), &u);

            assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok())
        }

        // error path
        {
            let mut prover = Prover::new(&pc_gens, Transcript::new(b"Test"));
            let mut verifier = Verifier::new(Transcript::new(b"Test"));

            let s0 = bits::BitVariable::new(&mut prover, b0).unwrap();
            let s1 = bits::BitVariable::new(&mut prover, b1).unwrap();
            let s2 = bits::BitVariable::new(&mut prover, b2).unwrap();
            let sa = bits::BitVariable::mul(&mut prover, s1, s2);

            let blind_e = Scalar::random(&mut rng);
            let value_e = Scalar::random(&mut rng);

            // prove

            let (comm_e, input_e) = prover.commit(value_e, blind_e);

            lookup_gadget(&mut prover, sa, s0, s1, s2, input_e.into(), &u);

            let proof = prover.prove(&bp_gens).unwrap();

            // verify

            let s0 = bits::BitVariable::free(&mut verifier).unwrap();
            let s1 = bits::BitVariable::free(&mut verifier).unwrap();
            let s2 = bits::BitVariable::free(&mut verifier).unwrap();
            let sa = bits::BitVariable::mul(&mut verifier, s1, s2);

            let input_e = verifier.commit(comm_e);

            lookup_gadget(&mut verifier, sa, s0, s1, s2, input_e.into(), &u);

            assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err())
        }
    }

    #[test]
    fn test_window_proof() {
        let ed_window = EdwardsWindow::new(
            Scalar::from_bytes_mod_order([
                0x33, 0xd1, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
                0xde, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x10,
            ]),
            curve::g0(),
        );

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        // compute lookup

        let witness = ed_window.witness(true, true, true);

        // prove

        let transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(&pc_gens, transcript);

        let s0 = bits::BitVariable::new(&mut prover, true).unwrap();
        let s1 = bits::BitVariable::new(&mut prover, true).unwrap();
        let s2 = bits::BitVariable::new(&mut prover, true).unwrap();

        let blind_x = Scalar::from(53753735735u64);
        let blind_y = Scalar::from(46713612753u64);

        let (comm_x, lookup_x) = prover.commit(witness.lookup().x, blind_x);
        let (comm_y, lookup_y) = prover.commit(witness.lookup().y, blind_y);

        let lookup = CurveVariable {
            x: lookup_x,
            y: lookup_y,
        };

        ed_window
            .gadget(&mut prover, Some(&witness), lookup, s0, s1, s2)
            .unwrap();

        let proof = prover.prove(&bp_gens).unwrap();

        // verify

        let transcript = Transcript::new(b"Test");
        let mut verifier = Verifier::new(transcript);

        let s0 = bits::BitVariable::free(&mut verifier).unwrap();
        let s1 = bits::BitVariable::free(&mut verifier).unwrap();
        let s2 = bits::BitVariable::free(&mut verifier).unwrap();

        let lookup_x = verifier.commit(comm_x);
        let lookup_y = verifier.commit(comm_y);

        let lookup = CurveVariable {
            x: lookup_x,
            y: lookup_y,
        };

        ed_window
            .gadget(&mut verifier, None, lookup, s0, s1, s2)
            .unwrap();

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap()
    }
}

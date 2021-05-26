// constraints for addition on the curve
mod addition;

// specification of the curve
pub mod curve;

// lookup windows
mod window;

//
mod misc;

// fixed based exponentiation
pub mod fixexp;

// bit decomposition
pub mod bits;

// check permissible point
pub mod permissible;

use misc::*;

use curve::CurvePoint;

impl Into<Scalar> for curve::Fp {
    fn into(self: curve::Fp) -> Scalar {
        let mut pow = Scalar::one();
        let mut res = Scalar::zero();
        for b in self.iter_bit().map(|b| b.0 != 0) {
            pow = pow + pow;
            if b {
                res = res + pow;
            }
        }
        res
    }
}

#[derive(Copy, Clone, Debug)]
pub struct CurveVariable {
    pub x: Variable,
    pub y: Variable,
}

impl CurveVariable {
    // create a free variable representing a curve point (no curve check!)
    fn free<CS: ConstraintSystem>(cs: &mut CS) -> Result<Self, R1CSError> {
        let x = cs.allocate(None)?;
        let y = cs.allocate(None)?;
        Ok(Self { x, y })
    }

    // create a free variable and assign it the witness of "value"
    fn assign<CS: ConstraintSystem>(cs: &mut CS, value: CurvePoint) -> Result<Self, R1CSError> {
        let x = cs.allocate(Some(value.x))?;
        let y = cs.allocate(Some(value.y))?;
        Ok(Self { x, y })
    }

    pub fn equal<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        other: &CurveVariable,
    ) -> Result<(), R1CSError> {
        cs.constrain(self.x - other.x);
        cs.constrain(self.y - other.y);
        Ok(())
    }

    pub fn constant<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        other: &CurvePoint,
    ) -> Result<(), R1CSError> {
        cs.constrain(self.x - other.x);
        cs.constrain(self.y - other.y);
        Ok(())
    }
}

use std::convert::TryFrom;

use rand::{Rng, RngCore};

use bulletproofs::r1cs::*;
use curve25519_dalek::scalar::Scalar;

use num_traits::One;

/*
use misc::*;

pub use permissible::{Permissible, PermissibleWitness};


pub use window::{FixScalarMult, FixScalarMultWitness};

use rug::Integer;

use crate::bytes_to_integer;

pub struct Statement {
    pub g_dlog: FixScalarMult,
    pub h_dlog: FixScalarMult,
    pub permissible: Permissible,
}

pub struct StatementWitness {
    g_dlog: FixScalarMultWitness,
    h_dlog: FixScalarMultWitness,
    permissible: PermissibleWitness,
}

impl Statement {
    pub fn new(d: Scalar) -> Self {
        Statement {
            g_dlog: FixScalarMult::new(d, curve::generator_0()),
            h_dlog: FixScalarMult::new(d, curve::generator_1()),
            permissible: Permissible::new(d),
        }
    }

    pub fn find_permissible_randomness<R: RngCore>(
        &self,
        rng: &mut R,
        xy: PointValue,
    ) -> (curve::Fp, PointValue) {
        // pick initial randomness
        let mut r = curve::Fp::random(rng); // commitment randomness
        let mut comm = self.rerandomize.compute(r, xy); // randomized commitment

        // count up randomness until the commitment is permissible
        loop {
            if self.permissible.is_permissible(comm) {
                break (r, comm);
            }
            r = r + curve::Fp::one();
            comm = curve_add(self.permissible.d, comm, curve::generator());
        }
    }

    pub fn witness(
        &self,
        pk: PointValue, // public key
        x: curve::Fp,   // private key
    ) -> StatementWitness {
        debug_assert!(self.permissible.is_permissible(pk), "not a valid witness");
        let permissible = self.permissible.witness(pk);
        let rerandomize = self.rerandomize.witness(pk, x);
        StatementWitness {
            permissible,
            rerandomize,
        }
    }

    pub fn gadget<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        witness: Option<&StatementWitness>,
        x: Variable,      // input point (hidden, described by x coordinate only)
        xy_r: PointValue, // rerandomized point (public)
    ) -> Result<(), R1CSError> {
        // check permissible
        let point = self
            .permissible
            .gadget(cs, witness.map(|x| &x.permissible))?;
        cs.constrain(point.x - x);

        // apply re-randomization
        let point_r = self
            .rerandomize
            .gadget(cs, witness.map(|x| &x.rerandomize), point)?;
        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Point {
    pub x: Variable,
    pub y: Variable,
}

impl Point {
    fn free<CS: ConstraintSystem>(cs: &mut CS) -> Result<Self, R1CSError> {
        let x = cs.allocate(None)?;
        let y = cs.allocate(None)?;
        Ok(Point { x, y })
    }
}

impl From<PointValue> for Integer {
    // convert the coefficient x to Integer
    fn from(point: PointValue) -> Integer {
        debug_assert!(
            Permissible::new(curve::param_d()).is_permissible(point),
            "converting a non-permissible point to an integer is undefined"
        );
        bytes_to_integer(point.x.as_bytes())
    }
}

impl PointValue {
    pub fn check(&self, d: Scalar) -> bool {
        let x2 = self.x * self.x;
        let y2 = self.y * self.y;
        x2 + y2 == Scalar::one() + d * x2 * y2
    }

    pub fn assign<CS: ConstraintSystem>(&self, cs: &mut CS) -> Result<Point, R1CSError> {
        let x = cs.allocate(Some(self.x))?;
        let y = cs.allocate(Some(self.y))?;
        Ok(Point { x, y })
    }
}



mod tests {
    use super::*;

    use bulletproofs::r1cs::ConstraintSystem;
    use bulletproofs::{BulletproofGens, PedersenGens};
    use curve25519_dalek::ristretto::CompressedRistretto;
    use curve25519_dalek::scalar::Scalar;
    use merlin::Transcript;

    use rand::thread_rng;
    use rand::Rng;

    use test::Bencher;

    #[bench]
    fn verify_statement(b: &mut Bencher) {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2100, 1);
        let transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(&pc_gens, transcript);

        let mut rng = thread_rng();
        let xy = curve::identity();
        let statement = Statement::new(curve::param_d());

        let (r, comm) = statement.find_permissible_randomness(&mut rng, xy);

        let witness = statement.witness(comm, -r);

        let blind_x = Scalar::random(&mut rng);

        let (comm_x, input_x) = prover.commit(comm.x, blind_x);

        statement
            .gadget(&mut prover, Some(&witness), input_x, xy)
            .unwrap();

        let proof = prover.prove(&bp_gens).unwrap();

        b.iter(|| {
            let transcript = Transcript::new(b"Test");
            let mut verifier = Verifier::new(transcript);
            let input_x = verifier.commit(comm_x);
            statement.gadget(&mut verifier, None, input_x, xy).unwrap();
            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
        })
    }

    #[test]
    fn test_statement() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2100, 1);
        let transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(&pc_gens, transcript);

        let transcript = Transcript::new(b"Test");
        let mut verifier = Verifier::new(transcript);

        let mut rng = thread_rng();
        let xy = curve::identity();
        let statement = Statement::new(curve::param_d());

        let (r, comm) = statement.find_permissible_randomness(&mut rng, xy);

        println!("{:?} {:?}", r, comm);

        let witness = statement.witness(comm, -r);

        let blind_x = Scalar::random(&mut rng);

        let (comm_x, input_x) = prover.commit(comm.x, blind_x);

        statement
            .gadget(&mut prover, Some(&witness), input_x, xy)
            .unwrap();

        let proof = prover.prove(&bp_gens).unwrap();

        // verify

        let input_x = verifier.commit(comm_x);

        statement.gadget(&mut verifier, None, input_x, xy).unwrap();

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();

        println!("{:?}", proof.serialized_size());
    }
}
*/

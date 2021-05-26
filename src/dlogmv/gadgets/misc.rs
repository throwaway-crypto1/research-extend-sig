use bulletproofs::r1cs::*;
use curve25519_dalek::scalar::Scalar;

pub fn one() -> LinearCombination {
    Scalar::one().into()
}

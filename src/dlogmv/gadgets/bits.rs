use super::*;

use std::iter::{Chain, Copied, Repeat};
use std::ops::Mul;

use bulletproofs::r1cs::*;

use curve25519_dalek::scalar::Scalar;

/// A variable which is constraint to be a bit-value
/// (can be converted into a Variable, but not vise versa)
#[derive(Clone, Copy, Debug)]
pub enum BitVariable {
    Var(Variable),
    Zero,
    One,
}

pub struct Gadget {
    // enabled bits
    enabled: Vec<bool>,
}

#[derive(Debug, Clone)]
pub struct Decompose {
    bits: Vec<BitVariable>,
    value: LinearCombination,
}

impl Decompose {
    pub fn iter_bits<'a>(
        &'a self,
    ) -> Chain<Copied<std::slice::Iter<'a, BitVariable>>, Repeat<BitVariable>> {
        self.bits
            .iter()
            .copied()
            .chain(std::iter::repeat(BitVariable::Zero))
    }
}

impl Into<LinearCombination> for Decompose {
    fn into(self) -> LinearCombination {
        self.value
    }
}

impl Into<LinearCombination> for BitVariable {
    fn into(self) -> LinearCombination {
        match self {
            BitVariable::Var(var) => var.into(),
            BitVariable::Zero => Scalar::zero().into(),
            BitVariable::One => Scalar::one().into(),
        }
    }
}

impl Mul<Scalar> for BitVariable {
    type Output = LinearCombination;

    fn mul(self, scalar: Scalar) -> LinearCombination {
        match self {
            BitVariable::Var(var) => {
                let lin: LinearCombination = var.into();
                scalar * lin
            }
            BitVariable::Zero => Scalar::zero().into(),
            BitVariable::One => scalar.into(),
        }
    }
}

impl Mul<BitVariable> for Scalar {
    type Output = LinearCombination;

    #[inline(always)]
    fn mul(self, bit: BitVariable) -> LinearCombination {
        bit * self
    }
}

impl BitVariable {
    pub fn free<CS: ConstraintSystem>(cs: &mut CS) -> Result<Self, R1CSError> {
        Ok(Self::Var(bit_gadget(cs, None)?.into()))
    }

    #[inline(always)]
    pub fn zero() -> Self {
        BitVariable::Zero
    }

    #[inline(always)]
    pub fn one() -> Self {
        BitVariable::One
    }

    pub fn new<CS: ConstraintSystem>(cs: &mut CS, v: bool) -> Result<Self, R1CSError> {
        Ok(BitVariable::Var(
            bit_gadget(cs, Some(if v { Scalar::one() } else { Scalar::zero() }))?.into(),
        ))
    }

    pub fn alloc<CS: ConstraintSystem>(cs: &mut CS, v: Option<bool>) -> Result<Self, R1CSError> {
        match v {
            Some(b) => Self::new(cs, b),
            None => Self::free(cs),
        }
    }

    pub fn mul<CS: ConstraintSystem>(cs: &mut CS, b1: Self, b2: Self) -> Self {
        match (b1, b2) {
            (BitVariable::Var(v1), BitVariable::Var(v2)) => {
                let (_, _, sa) = cs.multiply(v1.into(), v2.into());
                BitVariable::Var(sa)
            }
            (BitVariable::Zero, _) => BitVariable::Zero,
            (_, BitVariable::Zero) => BitVariable::Zero,
            (v1, BitVariable::One) => v1,
            (BitVariable::One, v2) => v2,
        }
    }
}

fn bit_gadget<CS: ConstraintSystem>(cs: &mut CS, v: Option<Scalar>) -> Result<Variable, R1CSError> {
    let (a, b, c) = match v {
        Some(bit) => {
            debug_assert!(bit == Scalar::one() || bit == Scalar::zero());
            cs.allocate_multiplier(Some((bit, Scalar::one() - bit)))
        }
        None => cs.allocate_multiplier(None),
    }?;
    let lc: LinearCombination = a.into();
    cs.constrain(lc - (Scalar::one() - b));
    cs.constrain(c.into());
    Ok(a)
}

// convert a scalar into little-endian bits
pub fn scalar_to_bits(s: Scalar) -> Vec<bool> {
    let mut v: Vec<bool> = Vec::with_capacity(256);
    for byte in s.as_bytes().iter() {
        let mut bits: u8 = *byte;
        // low nibble
        v.push((bits & 1) != 0);
        bits >>= 1;
        v.push((bits & 1) != 0);
        bits >>= 1;
        v.push((bits & 1) != 0);
        bits >>= 1;
        v.push((bits & 1) != 0);
        bits >>= 1;

        // high nibble
        v.push((bits & 1) != 0);
        bits >>= 1;
        v.push((bits & 1) != 0);
        bits >>= 1;
        v.push((bits & 1) != 0);
        bits >>= 1;
        v.push((bits & 1) != 0);
        debug_assert_eq!(bits >> 1, 0);
    }
    v
}

impl Gadget {
    pub fn new(enabled: Vec<bool>) -> Self {
        Gadget { enabled }
    }

    pub fn new_size(bit_size: usize) -> Self {
        Gadget {
            enabled: vec![true; bit_size],
        }
    }
    pub fn new_even_size(bit_size: usize) -> Self {
        let mut enabled = vec![true; bit_size];
        enabled[0] = false;
        Gadget { enabled }
    }

    pub fn gadget_scalar<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        witness: Option<Scalar>,
    ) -> Result<Decompose, R1CSError> {
        match witness {
            Some(scalar) => {
                let bits = scalar_to_bits(scalar);
                self.gadget(cs, Some(&bits[..]))
            }
            None => self.gadget(cs, None),
        }
    }

    pub fn gadget_inner<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        witness: Option<curve::Fp>,
    ) -> Result<Decompose, R1CSError> {
        match witness {
            Some(scalar) => {
                let bits: Vec<bool> = scalar.iter_bit().map(|b| b.0 != 0).collect();
                self.gadget(cs, Some(&bits[..]))
            }
            None => self.gadget(cs, None),
        }
    }

    pub fn gadget<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        witness: Option<&[bool]>,
    ) -> Result<Decompose, R1CSError> {
        #[cfg(test)]
        {
            if let Some(scalar) = witness {
                for (b0, b1) in scalar.iter().copied().zip(self.enabled.iter().copied()) {
                    assert!(b1 || !b0);
                }
            }
        }

        // the range checked value
        let mut mul: Scalar = Scalar::one();
        let mut value: LinearCombination = Scalar::zero().into();

        // bit decomposition
        let mut bits: Vec<BitVariable> = Vec::with_capacity(self.enabled.len());
        for (i, enable) in self.enabled.iter().copied().enumerate() {
            if enable {
                let bit = BitVariable::alloc(cs, witness.map(|w| w[i]))?;
                value = value + bit * mul;
                bits.push(bit);
            } else {
                bits.push(BitVariable::Zero)
            }
            mul = mul * Scalar::from(2u32);
        }
        Ok(Decompose { value, bits })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use merlin::Transcript;

    use bulletproofs::{BulletproofGens, PedersenGens};

    use rand_core::OsRng;

    #[test]
    fn test_scalar() {
        let scalar = Scalar::random(&mut OsRng);
        let random = Scalar::random(&mut OsRng);

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(5000, 1);

        let transcript = Transcript::new(b"TEST");
        let mut prover = Prover::new(&pc_gens, transcript);

        let (comm, value) = prover.commit(scalar, random);

        let gadget = Gadget::new_size(253);

        let out: LinearCombination = gadget
            .gadget_scalar(&mut prover, Some(scalar))
            .unwrap()
            .into();
        prover.constrain(out - value);

        let proof = prover.prove(&bp_gens).unwrap();

        // verify

        let transcript = Transcript::new(b"TEST");
        let mut verifier = Verifier::new(transcript);

        let value = verifier.commit(comm);

        let out: LinearCombination = gadget.gadget_scalar(&mut verifier, None).unwrap().into();
        verifier.constrain(out - value);

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap();
    }
}

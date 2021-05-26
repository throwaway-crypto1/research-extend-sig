use cpsnarks_set::protocols::modeq::channel::{ModEqProverChannel, ModEqVerifierChannel};
use cpsnarks_set::protocols::modeq::{CRSModEq, Proof, Protocol, Statement, Witness};

use cpsnarks_set::protocols::modeq::transcript::{
    TranscriptProverChannel, TranscriptVerifierChannel,
};

use rand::{CryptoRng, RngCore};
use rand_core::OsRng;

use rug::rand::{MutRandState, RandState};
use rug::Integer;

use merlin::Transcript;

use cpsnarks_set::commitments::integer::IntegerCommitment;
use cpsnarks_set::commitments::pedersen::PedersenCommitment;
use cpsnarks_set::parameters::Parameters;
use cpsnarks_set::utils::ConvertibleUnknownOrderGroup;

use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;

use std::marker::PhantomData;

use std::cell::RefCell;

use serde::Serialize;

use crate::scalar_to_integer;

const TRANSCRIPT_SEP: &'static [u8] = b"ZK_POK_MODEQ";

pub struct RangeModEq<G: ConvertibleUnknownOrderGroup> {
    protocol: Protocol<G, RistrettoPoint>, // contains crs
    rng1: RandState<'static>,
    rng2: OsRng,
}

#[derive(Serialize)]
pub struct ModEqProof<G: ConvertibleUnknownOrderGroup> {
    proof: Proof<G, RistrettoPoint>,
}

impl<G: ConvertibleUnknownOrderGroup> RangeModEq<G> {
    pub fn new(
        gen_g1: &G::Elem,
        gen_h1: &G::Elem,
        gen_g2: &RistrettoPoint,
        gen_h2: &RistrettoPoint,
    ) -> Self {
        RangeModEq {
            rng1: RandState::new(),
            rng2: OsRng,
            protocol: Protocol {
                crs: CRSModEq::<G, RistrettoPoint> {
                    parameters: Parameters::from_curve::<Scalar>().unwrap().0,
                    integer_commitment_parameters: IntegerCommitment::new(gen_g1, gen_h1),
                    pedersen_commitment_parameters: PedersenCommitment::new(gen_g2, gen_h2),
                },
            },
        }
    }

    pub fn prove(
        &mut self,
        comm1: &G::Elem,        // commitment in group 1
        comm2: &RistrettoPoint, // commitment in group 2
        rand1: Integer,
        rand2: Scalar,
        value: Scalar,
    ) -> ModEqProof<G> {
        let proof_transcript = RefCell::new(Transcript::new(TRANSCRIPT_SEP));
        let mut verifier_channel =
            TranscriptVerifierChannel::new(&self.protocol.crs, &proof_transcript);

        let e = scalar_to_integer(&value);
        let r_q = scalar_to_integer(&rand2);

        self.protocol
            .prove(
                &mut verifier_channel,
                &mut self.rng1,
                &mut self.rng2,
                &Statement {
                    c_e: comm1.clone(),
                    c_e_q: comm2.clone(),
                },
                &Witness { e, r: rand1, r_q },
            )
            .unwrap();

        ModEqProof {
            proof: verifier_channel.proof().unwrap(),
        }
    }

    pub fn verify(
        &self,
        comm1: &G::Elem,        // commitment in group 1
        comm2: &RistrettoPoint, // commitment in group 2
        proof: &ModEqProof<G>,
    ) -> bool {
        let verification_transcript = RefCell::new(Transcript::new(TRANSCRIPT_SEP));
        let mut prover_channel = TranscriptProverChannel::new(
            &self.protocol.crs,
            &verification_transcript,
            &proof.proof,
        );
        self.protocol
            .verify(
                &mut prover_channel,
                &Statement {
                    c_e: comm1.clone(),
                    c_e_q: comm2.clone(),
                },
            )
            .is_ok()
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use crate::unknown::{new_fujisaki_okamoto_gens, random_order};

    use bulletproofs::PedersenGens;

    use accumulator::group::{ClassGroup, Rsa2048};

    fn test_prove_verify<G: ConvertibleUnknownOrderGroup>() {
        let (gen_g1, gen_h1) = new_fujisaki_okamoto_gens::<G>();
        let pedersen = PedersenGens::default();

        let mut protocol =
            RangeModEq::<G>::new(&gen_g1, &gen_h1, &pedersen.B, &pedersen.B_blinding);

        let rand1 = random_order::<G>();
        let rand2 = Scalar::random(&mut OsRng);

        let value = Scalar::from(1337u32);
        let value_int = scalar_to_integer(&value);

        let comm1 = G::op(&G::exp(&gen_g1, &value_int), &G::exp(&gen_h1, &rand1));

        let comm2 = pedersen.commit(value, rand2);

        let proof = protocol.prove(&comm1, &comm2, rand1, rand2, value);

        assert!(protocol.verify(&comm1, &comm2, &proof));
    }

    #[test]
    fn test_prove_verify_rsa() {
        test_prove_verify::<Rsa2048>();
    }

    #[test]
    fn test_prove_verify_classgroup() {
        test_prove_verify::<ClassGroup>();
    }
}

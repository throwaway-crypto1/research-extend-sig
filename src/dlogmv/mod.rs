pub mod gadgets;

use merlin::Transcript;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};

use gadgets::{bits, curve, fixexp, permissible, CurveVariable};

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;

use serde::{Deserialize, Serialize};

use proofsize_derive::*;

const TRANSCRIPT_SEP: &'static [u8] = b"ZK_EXP";

#[derive(Serialize, Deserialize, Debug, ProofSize)]
pub struct Proof(R1CSProof);

struct Witness {
    pk: curve::CurvePoint, // public key
    sk: curve::Fp,         // private key
    g_exp: fixexp::Witness,
    h_exp: fixexp::Witness,
}

pub struct Statement {
    bp_gens: BulletproofGens,
    pc_gens: PedersenGens,

    // permissible of the public key
    permissible: permissible::Gadget,

    // bit decomposition of private key
    decomp: bits::Gadget,

    // proof of exp
    g_exp: fixexp::Gadget,
    h_exp: fixexp::Gadget,
}

impl Statement {
    pub fn gens(&self) -> &PedersenGens {
        &self.pc_gens
    }

    pub fn new(g: curve::CurvePoint, h: curve::CurvePoint) -> Self {
        Self {
            pc_gens: PedersenGens::default(),
            bp_gens: BulletproofGens::new(4100, 1),
            permissible: permissible::Gadget::new(),
            decomp: bits::Gadget::new_size(250),
            g_exp: fixexp::Gadget::new(g),
            h_exp: fixexp::Gadget::new(h),
        }
    }

    fn gadget<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        pk_y: Variable,                  // x coordinate of the public key
        claimed_tag: &curve::CurvePoint, // tag provided with the signature
        witness: Option<&Witness>,
    ) -> Result<(), R1CSError> {
        // decompose secret key
        let decomp = self.decomp.gadget_inner(cs, witness.map(|w| w.sk))?;

        // recompute public key
        let exp_pk = self.g_exp.gadget(cs, &decomp, witness.map(|w| &w.g_exp))?;
        let exp_pk_y: LinearCombination = exp_pk.y.into();
        cs.constrain(exp_pk_y - pk_y);

        // check that the recomputed public key is permissible (i.e. x is canonical, y is "small")
        let per_pk = self.permissible.gadget(cs, witness.map(|w| w.pk))?;
        per_pk.equal(cs, &exp_pk)?;

        // recompute tag
        let exp_tag = self.h_exp.gadget(cs, &decomp, witness.map(|w| &w.h_exp))?;
        exp_tag.constant(cs, claimed_tag)?;

        Ok(())
    }

    pub fn prove(
        &self,
        pk: curve::CurvePoint, // public key
        sk: curve::Fp,         // private key
        r: Scalar,             // randomness of commitment
    ) -> (Proof, CompressedRistretto, curve::CurvePoint) {
        let transcript = Transcript::new(TRANSCRIPT_SEP);
        let mut prover = Prover::new(&self.pc_gens, transcript);

        // commit to y-coordinate of public key
        let (comm_pk, pk_y) = prover.commit(pk.y, r);

        // prove public key
        let (g_exp, pk_exp) = self.g_exp.witness(sk);
        assert_eq!(pk_exp, pk);

        // compute tag
        let (h_exp, tag) = self.h_exp.witness(sk);

        // constrain entire relation
        self.gadget(
            &mut prover,
            pk_y,
            &tag,
            Some(&Witness {
                pk,
                sk,
                g_exp,
                h_exp,
            }),
        )
        .unwrap();

        // prove, return commitment to public and tag
        let proof = prover.prove(&self.bp_gens).unwrap();
        (Proof(proof), comm_pk, tag)
    }

    pub fn verify(
        &self,
        proof: &Proof,
        comm_pk: CompressedRistretto,
        tag: &curve::CurvePoint,
    ) -> bool {
        let transcript = Transcript::new(TRANSCRIPT_SEP);
        let mut verifier = Verifier::new(transcript);

        // input y-coordinate of public key
        let pk_y = verifier.commit(comm_pk);

        self.gadget(&mut verifier, pk_y, tag, None).unwrap();

        verifier
            .verify(&proof.0, &self.pc_gens, &self.bp_gens)
            .is_ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::SigningKey;

    use rand_core::OsRng;

    use test::Bencher;

    #[test]
    fn test_prove_verify() {
        let sk = SigningKey::new();

        let statement = Statement::new(curve::g0(), curve::g1());

        let r = Scalar::random(&mut OsRng);

        let (proof, comm_pk, tag) = statement.prove(sk.pk, sk.sk, r);

        assert!(statement.verify(&proof, comm_pk, &tag))
    }

    #[bench]
    fn bench_verify(b: &mut Bencher) {
        let sk = SigningKey::new();

        let statement = Statement::new(curve::g0(), curve::g1());

        let r = Scalar::random(&mut OsRng);

        let (proof, comm_pk, tag) = statement.prove(sk.pk, sk.sk, r);

        b.iter(|| assert!(statement.verify(&proof, comm_pk, &tag)))
    }
}

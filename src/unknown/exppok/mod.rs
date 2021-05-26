use cpsnarks_set::transcript::{TranscriptProtocolChallenge, TranscriptProtocolInteger};
use cpsnarks_set::utils::ConvertibleUnknownOrderGroup;

use rug::Integer;

use merlin::Transcript;

use serde::Serialize;

const TRANSCRIPT_SEP: &'static [u8] = b"ZK_POK_EXP";

const STAT_SECURITY: usize = 128;

pub trait ProofOfExp<G: ConvertibleUnknownOrderGroup>: Serialize {
    fn new<I: Iterator<Item = Integer>>(base: &G::Elem, keys: I) -> Self;

    fn verify<I: Iterator<Item = Integer>>(&self, base: &G::Elem, keys: I) -> Option<G::Elem>;
}

#[derive(Debug, Serialize)]
pub struct TrivialProof();

impl<G: ConvertibleUnknownOrderGroup> ProofOfExp<G> for TrivialProof {
    fn new<I: Iterator<Item = Integer>>(base: &G::Elem, keys: I) -> Self {
        TrivialProof()
    }

    fn verify<I: Iterator<Item = Integer>>(&self, base: &G::Elem, keys: I) -> Option<G::Elem> {
        let mut res = base.clone();
        for key in keys {
            res = G::exp(&res, &key);
        }
        Some(res)
    }
}

/// This proof is just a proof-of-knowledge (not zero-knowledge)
#[derive(Debug, Serialize)]
pub struct Proof<G: ConvertibleUnknownOrderGroup> {
    Q: G::Elem,
    r: Integer,
    p: Integer,
}

impl<G: ConvertibleUnknownOrderGroup> ProofOfExp<G> for Proof<G> {
    fn new<I: Iterator<Item = Integer>>(base: &G::Elem, keys: I) -> Self {
        // compute exponent
        let mut exp = Integer::from(1);
        // commit to statement
        let mut transcript = Transcript::new(TRANSCRIPT_SEP);
        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"base", base);
        for key in keys {
            exp = exp * &key;
            TranscriptProtocolInteger::<G>::append_integer_scalar(&mut transcript, b"keys", &key);
        }
        let p = TranscriptProtocolChallenge::challenge_scalar(
            &mut transcript,
            b"prime",
            STAT_SECURITY as u16,
        )
        .next_prime();
        let (q, r) = exp.div_rem(p.clone());
        Self {
            Q: G::exp(base, &q),
            r,
            p,
        }
    }

    fn verify<I: Iterator<Item = Integer>>(&self, base: &G::Elem, keys: I) -> Option<G::Elem> {
        // commit to statement
        let mut rem = Integer::from(1);
        let mut transcript = Transcript::new(TRANSCRIPT_SEP);
        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"base", base);
        for key in keys {
            rem = rem * &key;
            let (_q, r) = rem.div_rem(self.p.clone());
            rem = r;
            TranscriptProtocolInteger::<G>::append_integer_scalar(&mut transcript, b"keys", &key);
        }

        // check consistency with prime
        let p = TranscriptProtocolChallenge::challenge_scalar(
            &mut transcript,
            b"prime",
            STAT_SECURITY as u16,
        )
        .next_prime();
        if self.p != p {
            return None;
        }

        let Qp = G::exp(&self.Q, &p);
        let Br = G::exp(base, &rem);
        Some(G::op(&Qp, &Br))
    }
}

use rug::Integer;

use serde::{Deserialize, Serialize};

use cpsnarks_set::transcript::{TranscriptProtocolChallenge, TranscriptProtocolInteger};
use cpsnarks_set::utils::ConvertibleUnknownOrderGroup;
use merlin::Transcript;

use rug_binserial::Integer as BinInteger;

use super::random_order;

const TRANSCRIPT_SEP: &'static [u8] = b"ZK_POK_REP";

const STAT_SECURITY: usize = 128;

#[derive(Serialize, Deserialize, Debug)]
pub struct ZKPokRep<G: ConvertibleUnknownOrderGroup> {
    a: G::Elem,
    Q: G::Elem,
    r1: BinInteger,
    r2: BinInteger,
}

impl<G: ConvertibleUnknownOrderGroup> ZKPokRep<G> {
    pub fn new(
        g1: &G::Elem, // generator 1
        g2: &G::Elem, // generator 2
        y: &G::Elem,  // y = g1^x1 g2^x2
        x1: &Integer, // dlog 1
        x2: &Integer, // dlog 2
    ) -> Self {
        // first round message
        let a_g1 = random_order::<G>();
        let a_g2 = random_order::<G>();
        let a = G::op(&G::exp(g1, &a_g1), &G::exp(g2, &a_g2));

        // compute challenge

        let mut transcript = Transcript::new(TRANSCRIPT_SEP);

        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"a", &a);
        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"y", &y);
        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"g1", &g1);
        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"g2", &g2);

        let c = TranscriptProtocolChallenge::challenge_scalar(
            &mut transcript,
            b"challenge",
            STAT_SECURITY as u16,
        );

        let p = TranscriptProtocolChallenge::challenge_scalar(
            &mut transcript,
            b"prime",
            STAT_SECURITY as u16,
        )
        .next_prime();

        // compute response

        let z1 = &c * x1 + a_g1;
        let z2 = &c * x2 + a_g2;

        let (q1, r1) = z1.div_rem(p.clone());
        let (q2, r2) = z2.div_rem(p);

        let Q1 = G::exp(g1, &q1);
        let Q2 = G::exp(g2, &q2);
        let Q = G::op(&Q1, &Q2);

        Self {
            a,
            Q,
            r1: r1.into(),
            r2: r2.into(),
        }
    }

    pub fn verify(
        &self,
        g1: &G::Elem, // generator 1
        g2: &G::Elem, // generator 2
        y: &G::Elem,  // y = g1^x1 g2^x2
    ) -> bool {
        // compute challenge
        let mut transcript = Transcript::new(TRANSCRIPT_SEP);

        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"a", &self.a);
        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"y", &y);
        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"g1", &g1);
        TranscriptProtocolInteger::<G>::append_integer_point(&mut transcript, b"g2", &g2);

        let c = TranscriptProtocolChallenge::challenge_scalar(
            &mut transcript,
            b"challenge",
            STAT_SECURITY as u16,
        );

        let p = TranscriptProtocolChallenge::challenge_scalar(
            &mut transcript,
            b"prime",
            STAT_SECURITY as u16,
        )
        .next_prime();

        // verify response

        let yc = G::exp(y, &c);
        let Qp = G::exp(&self.Q, &p);
        let g1r1 = G::exp(g1, self.r1.as_ref());
        let g2r2 = G::exp(g2, self.r2.as_ref());

        let right = G::op(&Qp, &G::op(&g1r1, &g2r2));
        let left = G::op(&yc, &self.a);

        left == right
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rug::rand::RandState;

    use accumulator::group::{ClassGroup, Rsa2048};

    use test::Bencher;

    use bincode;

    fn test_ser<G: ConvertibleUnknownOrderGroup>() {
        let mut rand = RandState::new();
        let g1 = G::unknown_possibly_random_order_elem(&mut rand);
        let g2 = G::unknown_possibly_random_order_elem(&mut rand);

        let x1 = random_order::<G>();
        let x2 = random_order::<G>();

        let y1 = G::exp(&g1, &x1);
        let y2 = G::exp(&g2, &x2);
        let y = G::op(&y1, &y2);

        let pi = ZKPokRep::<G>::new(&g1, &g2, &y, &x1, &x2);

        let bs = bincode::serialize(&pi).unwrap();

        println!("{:?} {}", &bs[..], bs.len());

        assert!(pi.verify(&g1, &g2, &y));
    }

    #[test]
    fn test_ser_rsa() {
        test_ser::<Rsa2048>();
    }

    #[test]
    fn test_ser_class() {
        test_ser::<ClassGroup>();
    }

    fn test_mult_proof<G: ConvertibleUnknownOrderGroup>() {
        let mut rand = RandState::new();
        let g1 = G::unknown_possibly_random_order_elem(&mut rand);
        let g2 = G::unknown_possibly_random_order_elem(&mut rand);

        let x1 = random_order::<G>();
        let x2 = random_order::<G>();

        let y1 = G::exp(&g1, &x1);
        let y2 = G::exp(&g2, &x2);
        let y = G::op(&y1, &y2);

        let pi = ZKPokRep::<G>::new(&g1, &g2, &y, &x1, &x2);

        assert!(pi.verify(&g1, &g2, &y));
    }

    fn bench_proof_gen<G: ConvertibleUnknownOrderGroup>(b: &mut Bencher) {
        b.iter(|| {
            let mut rand = RandState::new();
            let g1 = G::unknown_possibly_random_order_elem(&mut rand);
            let g2 = G::unknown_possibly_random_order_elem(&mut rand);

            let x1 = random_order::<G>();
            let x2 = random_order::<G>();

            let y1 = G::exp(&g1, &x1);
            let y2 = G::exp(&g2, &x2);
            let y = G::op(&y1, &y2);

            let _ = ZKPokRep::<G>::new(&g1, &g2, &y, &x1, &x2);
        });
    }

    fn bench_proof_vrfy<G: ConvertibleUnknownOrderGroup>(b: &mut Bencher) {
        let mut rand = RandState::new();
        let g1 = G::unknown_possibly_random_order_elem(&mut rand);
        let g2 = G::unknown_possibly_random_order_elem(&mut rand);

        let x1 = random_order::<G>();
        let x2 = random_order::<G>();

        let y1 = G::exp(&g1, &x1);
        let y2 = G::exp(&g2, &x2);
        let y = G::op(&y1, &y2);

        let pi = ZKPokRep::<G>::new(&g1, &g2, &y, &x1, &x2);
        b.iter(|| {
            assert!(pi.verify(&g1, &g2, &y));
        });
    }

    // test and benchmarks for RSA

    #[test]
    fn test_mult_proof_rsa() {
        test_mult_proof::<Rsa2048>();
    }

    #[bench]
    fn bench_proof_gen_rsa(b: &mut Bencher) {
        bench_proof_gen::<Rsa2048>(b);
    }

    #[bench]
    fn bench_proof_vrfy_rsa(b: &mut Bencher) {
        bench_proof_vrfy::<Rsa2048>(b);
    }

    // test and benchmarks for ClassGroups

    #[test]
    fn test_mult_proof_classgroup() {
        test_mult_proof::<ClassGroup>();
    }

    #[bench]
    fn bench_proof_gen_classgroup(b: &mut Bencher) {
        bench_proof_gen::<ClassGroup>(b);
    }

    #[bench]
    fn bench_proof_vrfy_classgroup(b: &mut Bencher) {
        bench_proof_vrfy::<ClassGroup>(b);
    }
}

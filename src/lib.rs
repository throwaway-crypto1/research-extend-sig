#![feature(unsigned_abs)]
#![feature(test)]

extern crate test;

mod dlogmv;
// mod membership;
pub mod unknown;

use dlogmv::gadgets::curve;
use num_traits::One;
use rand_core::OsRng;
use rug::{integer, Integer};

use cpsnarks_set::utils::ConvertibleUnknownOrderGroup;

use bulletproofs::PedersenGens;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;

use serde::Serialize;

use unknown::exppok::ProofOfExp;

pub(crate) fn bytes_to_integer(bytes: &[u8]) -> Integer {
    Integer::from_digits(bytes, integer::Order::Lsf)
}

pub(crate) fn scalar_to_integer(s: &Scalar) -> Integer {
    bytes_to_integer(s.as_bytes())
}

pub(crate) fn point_to_scalar(p: &curve::CurvePoint) -> Scalar {
    p.y
}

pub struct SigningKey {
    pk: curve::CurvePoint,
    sk: curve::Fp,
}

#[derive(Debug, Copy, Clone)]
pub struct PublicKey {
    pk: curve::CurvePoint,
}

#[derive(Serialize)]
pub struct Signature<G: ConvertibleUnknownOrderGroup, E: ProofOfExp<G>> {
    tag: curve::CurvePoint,     // linkability tag
    comm1: G::Elem,             // commit to PK
    comm2: CompressedRistretto, // commit to PK
    rand: Integer,              // randomness of last commitment
    dlogmv: dlogmv::Proof,
    modeq: unknown::base::ModEqProof<G>,
    exp_pi: E,
    extend: Vec<(G::Elem, unknown::extend::ExtendProof<G>)>,
}

pub struct Context<G: ConvertibleUnknownOrderGroup> {
    g1: G::Elem,
    h1: G::Elem,
    modeq: unknown::base::RangeModEq<G>,
    dlogmv: dlogmv::Statement,
}

impl<G: ConvertibleUnknownOrderGroup> Context<G> {
    pub fn setup(msg: &[u8]) -> Context<G> {
        let (g1, h1) = unknown::new_fujisaki_okamoto_gens::<G>();

        let dlogmv = dlogmv::Statement::new(curve::g0(), curve::CurvePoint::hash(msg));

        let modeq =
            unknown::base::RangeModEq::new(&g1, &h1, &dlogmv.gens().B, &dlogmv.gens().B_blinding);

        Context {
            modeq,
            dlogmv,
            g1,
            h1,
        }
    }
}

impl SigningKey {
    pub fn new() -> Self {
        let mut sk = curve::Fp::random(&mut OsRng);
        let mut pk = sk * curve::g0();
        while !pk.is_permissible() {
            sk = sk + One::one();
            pk = pk + curve::g0();
        }
        SigningKey { pk, sk }
    }

    pub fn pk(&self) -> PublicKey {
        PublicKey { pk: self.pk }
    }

    pub fn sign<G: ConvertibleUnknownOrderGroup, E: ProofOfExp<G>>(
        &self,
        ctx: &mut Context<G>,
    ) -> Signature<G, E> {
        let pks = point_to_scalar(&self.pk);
        let pki = scalar_to_integer(&pks);

        let rand1 = unknown::random_order::<G>();
        let rand2 = Scalar::random(&mut OsRng);

        let comm1 = G::op(
            &G::exp(&ctx.g1, &pki),   // G^pk
            &G::exp(&ctx.h1, &rand1), // H^rand
        );

        let (dlogmv, comm2, tag) = ctx.dlogmv.prove(self.pk, self.sk, rand2);

        let modeq = ctx.modeq.prove(
            &comm1,
            &comm2.decompress().unwrap(),
            rand1.clone(),
            rand2,
            pks,
        );

        let extend: Vec<(G::Elem, unknown::extend::ExtendProof<G>)> = vec![];

        Signature {
            tag,
            comm1,
            comm2,
            exp_pi: E::new(
                &ctx.g1,
                [self.pk]
                    .iter()
                    .map(|key| scalar_to_integer(&point_to_scalar(key))),
            ),
            rand: rand1,
            dlogmv,
            modeq,
            extend,
        }
    }
}

impl<G: ConvertibleUnknownOrderGroup, E: ProofOfExp<G>> Signature<G, E> {
    pub fn extend(
        mut self,
        ctx: &Context<G>,
        delta: &[PublicKey], // new public keys
        total: &[PublicKey], // total list
    ) -> Signature<G, E> {
        let last_comm = self
            .extend
            .last()
            .map(|last| &last.0)
            .unwrap_or(&self.comm1);

        let keys: Vec<Integer> = delta
            .iter()
            .map(|key| scalar_to_integer(&point_to_scalar(&key.pk)))
            .collect();

        let (new_comm, new_rand, new_proof) = unknown::extend::ExtendProof::<G>::new(
            &last_comm, // Fujisaki-Okamoto commitment
            &ctx.h1,    // randomness generator
            self.rand,  // randomness scalar
            &keys[..],  // keys to add
        );

        self.rand = new_rand;
        self.exp_pi = E::new(
            &ctx.g1,
            total
                .iter()
                .map(|key| scalar_to_integer(&point_to_scalar(&key.pk))),
        );
        self.extend.push((new_comm, new_proof));
        self
    }

    pub fn verify(&self, ctx: &Context<G>, total: &[PublicKey]) -> Option<curve::CurvePoint> {
        // verify base proof: tag valid
        if !ctx.dlogmv.verify(&self.dlogmv, self.comm2, &self.tag) {
            println!("bad dlogmv");
            return None;
        }

        // range proof and modeq
        let comm2 = self.comm2.decompress()?;
        if !ctx.modeq.verify(&self.comm1, &comm2, &self.modeq) {
            println!("bad modeq");
            return None;
        }

        // verify extensions
        let mut last_comm = &self.comm1;
        for (new_comm, proof) in self.extend.iter() {
            if !proof.verify(last_comm, &ctx.h1, new_comm) {
                println!("bad extension");
                return None;
            }
            last_comm = new_comm;
        }

        // recompute opened commitment (last)
        let res = self.exp_pi.verify(
            &ctx.g1,
            total
                .iter()
                .map(|key| scalar_to_integer(&point_to_scalar(&key.pk))),
        )?;
        let res = G::op(&res, &G::exp(&ctx.h1, &self.rand));

        // check equality with commitment chain
        if res != last_comm.clone() {
            println!("bad opening");
            return None;
        }

        Some(self.tag)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use accumulator::group::{ClassGroup, Rsa3072};

    use test::Bencher;

    use std::env;

    use bincode;

    fn sign_verify<G: ConvertibleUnknownOrderGroup>() {
        let msg: &[u8] = &[];

        let mut ctx = Context::<G>::setup(msg);
        let sk = SigningKey::new();
        let pk = sk.pk();

        let sig: Signature<G, unknown::exppok::Proof<G>> = sk.sign(&mut ctx);

        assert!(sig.verify(&ctx, &[pk]).is_some());

        let sks: Vec<SigningKey> = (0..10).map(|_| SigningKey::new()).collect();
        let mut delta: Vec<PublicKey> = sks.iter().map(|sk| sk.pk()).collect();
        let mut total = delta.clone();
        total.push(pk);
        let sig = sig.extend(&ctx, &delta[..], &total[..]);

        assert!(sig.verify(&ctx, &total[..]).is_some());
    }

    fn bench_sign<G: ConvertibleUnknownOrderGroup, E: ProofOfExp<G>>(
        b: &mut Bencher,
        num_extend: usize, // how many extensions
        num_keys: usize,   // how many keys in each
    ) {
        let msg: &[u8] = &[];

        println!("num_extend: {}", num_extend);
        println!("num_keys: {}", num_keys);

        let mut ctx = Context::<G>::setup(msg);
        let sk = SigningKey::new();
        let pk = sk.pk();

        let mut pkss: Vec<Vec<PublicKey>> = vec![];
        let mut skss: Vec<Vec<SigningKey>> = vec![];

        let mut total: Vec<PublicKey> = vec![];

        for _ in 0..num_extend {
            let sks: Vec<SigningKey> = (0..num_keys).map(|_| SigningKey::new()).collect();
            let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.pk()).collect();
            total.extend(&pks[..]);
            skss.push(sks);
            pkss.push(pks);
        }

        b.iter(|| {
            let mut sig: Signature<G, E> = sk.sign(&mut ctx);
            for pks in pkss.iter() {
                sig = sig.extend(&ctx, &pks[..], &total);
            }
        })
    }

    fn bench_verify<G: ConvertibleUnknownOrderGroup, E: ProofOfExp<G>>(
        b: &mut Bencher,
        num_extend: usize, // how many extensions
        num_keys: usize,   // how many keys in each
    ) {
        let msg: &[u8] = &[];

        println!("num_extend: {}", num_extend);
        println!("num_keys: {}", num_keys);

        let mut ctx = Context::<G>::setup(msg);

        #[cfg(debug_assertions)]
        println!("signing");

        let sk = SigningKey::new();
        let pk = sk.pk();

        let mut pkss: Vec<Vec<PublicKey>> = vec![];
        let mut skss: Vec<Vec<SigningKey>> = vec![];
        let mut total: Vec<PublicKey> = vec![pk];

        #[cfg(debug_assertions)]
        println!("generating keys");

        for j in 0..num_extend {
            let mut sks: Vec<SigningKey> = vec![];
            for i in 0..num_keys {
                if i % 10 == 0 {
                    #[cfg(debug_assertions)]
                    println!("keys: {}", i + j * num_keys);
                }
                sks.push(SigningKey::new());
            }
            let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.pk()).collect();
            total.extend(pks.iter());
            skss.push(sks);
            pkss.push(pks);
        }

        #[cfg(debug_assertions)]
        println!("extending");

        assert_eq!(total.len(), num_extend * num_keys + 1);

        let mut sig: Signature<G, E> = sk.sign(&mut ctx);
        for pks in pkss.iter() {
            sig = sig.extend(&ctx, &pks[..], &total);
        }

        #[cfg(debug_assertions)]
        println!("signed");

        println!("size: {}", bincode::serialize(&sig).unwrap().len());

        b.iter(|| {
            assert!(sig.verify(&ctx, &total[..]).is_some());
        })
    }

    fn bench_verify_args<G: ConvertibleUnknownOrderGroup>(b: &mut Bencher) {
        let keys: usize = env::var("BENCH_KEYS")
            .unwrap_or("1".to_string())
            .parse()
            .unwrap();
        let exts: usize = env::var("BENCH_EXTS")
            .unwrap_or("1".to_string())
            .parse()
            .unwrap();
        bench_verify::<G, unknown::exppok::Proof<_>>(b, exts, keys);
    }

    fn bench_sign_args<G: ConvertibleUnknownOrderGroup>(b: &mut Bencher) {
        let keys: usize = env::var("BENCH_KEYS")
            .unwrap_or("1".to_string())
            .parse()
            .unwrap();
        let exts: usize = env::var("BENCH_EXTS")
            .unwrap_or("1".to_string())
            .parse()
            .unwrap();
        bench_sign::<G, unknown::exppok::Proof<_>>(b, exts, keys);
    }

    #[test]
    fn sign_verify_rsa() {
        sign_verify::<Rsa3072>();
    }

    #[test]
    fn sign_verify_classgroup() {
        sign_verify::<ClassGroup>();
    }

    #[bench]
    fn bench_verify_rsa(b: &mut Bencher) {
        bench_verify_args::<Rsa3072>(b);
    }

    #[bench]
    fn bench_verify_class(b: &mut Bencher) {
        bench_verify_args::<ClassGroup>(b);
    }

    #[bench]
    fn bench_sign_rsa(b: &mut Bencher) {
        bench_sign_args::<Rsa3072>(b);
    }

    #[bench]
    fn bench_sign_class(b: &mut Bencher) {
        bench_sign_args::<ClassGroup>(b);
    }
}

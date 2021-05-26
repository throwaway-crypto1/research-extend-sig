use cpsnarks_set::commitments::pedersen::PedersenCommitment;
use cpsnarks_set::utils::ConvertibleUnknownOrderGroup;

use rand_core::{OsRng, RngCore};
use rug::Integer;

use crate::bytes_to_integer;
use crate::unknown::random_order;

use serde::{Deserialize, Serialize};

#[allow(non_snake_case)]
mod zkpokrep;

#[allow(non_snake_case)]
mod reduce;

#[derive(Serialize, Debug)]
pub struct ExtendProof<G: ConvertibleUnknownOrderGroup> {
    proof: zkpokrep::ZKPokRep<G>,
}

impl<G: ConvertibleUnknownOrderGroup> ExtendProof<G> {
    pub fn new(
        com: &G::Elem,    // Fujisaki-Okamoto commitment
        h: &G::Elem,      // randomness generator
        r: Integer,       // randomness scalar
        keys: &[Integer], // keys to add
    ) -> (G::Elem, Integer, ExtendProof<G>) {
        // compute exponent
        let mut mul = Integer::from(1);
        for v in keys.iter() {
            mul = mul * v;
        }

        // pick new randomness
        let r_new = random_order::<G>();
        let r_delta = (&r_new - &mul * &r).into();

        // compute new commitment
        let h_rnd = G::exp(h, &r_delta);
        let com_mul = G::exp(com, &mul);
        let com_new = G::op(&h_rnd, &com_mul);

        //
        let proof = zkpokrep::ZKPokRep::new(com, h, &com_new, &mul, &r_delta);
        (com_new, r_new, ExtendProof { proof })
    }

    pub fn verify(
        &self,
        com: &G::Elem,     // Fujisaki-Okamoto commitment
        h: &G::Elem,       // randomness generator
        com_new: &G::Elem, // new commitment
    ) -> bool {
        self.proof.verify(com, h, com_new)
    }
}

mod tests {
    use super::*;

    use rug::rand::RandState;

    use accumulator::group::{ClassGroup, Rsa2048, UnknownOrderGroup};

    fn random_integer(magnitude: usize) -> Integer {
        let mut bytes = vec![0; magnitude];
        OsRng.fill_bytes(&mut bytes);
        bytes_to_integer(&bytes[..])
    }

    fn random_integers(len: usize, magnitude: usize) -> Vec<Integer> {
        let mut elems: Vec<Integer> = Vec::with_capacity(len);
        for _ in 0..len {
            elems.push(random_integer(magnitude));
        }
        elems
    }

    fn commit<G: ConvertibleUnknownOrderGroup>(
        g: &G::Elem,
        h: &G::Elem,
        v: &Integer,
        r: &Integer,
    ) -> G::Elem {
        let gv = G::exp(g, v);
        let hr = G::exp(h, r);
        G::op(&gv, &hr)
    }

    fn test_extend<G: ConvertibleUnknownOrderGroup>() {
        let mut rand = RandState::new();
        let g = G::unknown_possibly_random_order_elem(&mut rand);
        let mut h = G::unknown_possibly_random_order_elem(&mut rand);
        if g == h {
            let r = random_order::<G>();
            h = G::exp(&h, &r);
        }

        let key_0 = random_integer(32);
        let keys_1 = random_integers(20, 32);
        let keys_2 = random_integers(20, 32);

        let rnd0 = random_order::<G>();
        let com0 = commit::<G>(&g, &h, &key_0, &rnd0);

        let (com1, rnd1, proof0) = ExtendProof::<G>::new(&com0, &h, rnd0, &keys_1[..]);
        let (com2, rnd2, proof1) = ExtendProof::<G>::new(&com1, &h, rnd1, &keys_2[..]);

        assert!(proof0.verify(&com0, &h, &com1));
        assert!(proof1.verify(&com1, &h, &com2));

        let mut product = key_0.clone();
        for k in keys_1.iter() {
            product = product * k;
        }
        for k in keys_2.iter() {
            product = product * k;
        }

        assert_eq!(commit::<G>(&g, &h, &product, &rnd2), com2);
    }

    #[test]
    fn test_extend_rsa() {
        test_extend::<Rsa2048>();
    }

    #[test]
    fn test_extend_classgroup() {
        test_extend::<ClassGroup>();
    }
}

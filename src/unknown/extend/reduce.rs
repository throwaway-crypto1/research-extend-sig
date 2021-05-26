use accumulator::group::Group;
use rand_core::{OsRng, RngCore};

use rug::Integer;

use std::ops::Mul;

trait Reducible<G: Group> {
    // reduce equation modulo p
    fn reduce(&self, base: &G::Elem, p: &Integer) -> (G::Elem, Integer);
}

struct ReducibleProduct<G: Group> {
    reduc: Box<dyn Reducible<G>>,
    small: Integer,
}

struct ReducibleSum<G: Group> {
    left: Box<dyn Reducible<G>>,
    right: Box<dyn Reducible<G>>,
}

impl<G: Group> Reducible<G> for ReducibleProduct<G> {
    fn reduce(&self, base: &G::Elem, p: &Integer) -> (G::Elem, Integer) {
        // G^q0, r0 : n0 = q0 * p + r0
        let (Q0, r0) = self.reduc.reduce(base, p);

        //   q1, r1 : n1 = q1 * p + r1
        let (q1, r1) = self.small.clone().div_rem(p.clone());

        // compute Q0^(n1) = G^{p n1} = G^{q0 q1 p + q0 r1}
        let Q0_q1p = G::exp(&Q0, &self.small);

        // multiply remainders
        let r0r1: Integer = (&r0 * &r1).into();
        let (div, rem) = r0r1.div_rem(p.clone());

        // compute G^{q1 * r0 + div}
        let q1r0_div = q1 * r0 + div;
        let G_r1 = G::exp(base, &q1r0_div);

        (G::op(&Q0_q1p, &G_r1), rem)
    }
}

impl<G: Group> Mul<Integer> for Box<dyn Reducible<G>> {
    type Output = Box<ReducibleProduct<G>>;

    fn mul(self, rhs: Integer) -> Self::Output {
        Box::new(ReducibleProduct {
            reduc: self,
            small: rhs,
        })
    }
}

fn mul_reducible<G: Group>(
    reduc: Box<dyn Reducible<G>>,
    small: Integer,
) -> Box<ReducibleProduct<G>> {
    Box::new(ReducibleProduct { reduc, small })
}

impl<G: Group> Reducible<G> for ReducibleSum<G> {
    fn reduce(&self, base: &G::Elem, p: &Integer) -> (G::Elem, Integer) {
        // G^q0, r0 : n0 = q0 * p + r0
        let (Q0, r0) = self.left.reduce(base, p);

        // G^q0, r0 : n0 = q0 * p + r0
        let (Q1, r1) = self.right.reduce(base, p);

        // add remainders
        let (div, rem) = (r0 + r1).div_rem(p.clone());

        // quotient computation
        let G_div = G::exp(base, &div);
        let Q0_Q1 = G::op(&Q0, &Q1);
        (G::op(&G_div, &Q0_Q1), rem)
    }
}

impl<G: Group> Reducible<G> for Integer {
    fn reduce(&self, base: &G::Elem, p: &Integer) -> (G::Elem, Integer) {
        let (qou, rem) = self.clone().div_rem(p.clone());
        (G::exp(base, &qou), rem)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::bytes_to_integer;

    use test::Bencher;

    use accumulator::group::Rsa2048;
    use accumulator::group::UnknownOrderGroup;

    fn random_integer(magnitude: usize) -> Integer {
        let mut bytes = vec![0; magnitude];
        OsRng.fill_bytes(&mut bytes);
        bytes_to_integer(&bytes[..])
    }

    fn elems(len: usize, magnitude: usize) -> Vec<Integer> {
        let mut elems: Vec<Integer> = Vec::with_capacity(len);
        for _ in 0..len {
            elems.push(random_integer(magnitude));
        }
        elems
    }

    #[bench]
    fn bench_reduce_mul_reduce(b: &mut Bencher) {
        let elems = elems(2000, 32);
        let prime = random_integer(16);
        let base = Rsa2048::unknown_order_elem();
        b.iter(|| {
            let mut m: Box<dyn Reducible<Rsa2048>> = Box::new(elems[0].clone());
            for v in elems[1..].iter() {
                m = mul_reducible::<Rsa2048>(m, v.clone());
            }
            m.reduce(&base, &prime);
        })
    }

    #[bench]
    fn bench_reduce_mul_naive(b: &mut Bencher) {
        let elems = elems(2000, 32);
        let prime = random_integer(16);
        let base = Rsa2048::unknown_order_elem();
        b.iter(|| {
            let mut res = Integer::from(1);
            for v in elems.iter() {
                res = res * v;
            }
            let (div, _) = res.div_rem(prime.clone());
            Rsa2048::exp(&base, &div);
        })
    }

    #[test]
    fn test_reduce_mul() {
        let p = Integer::from(0x4621).next_prime();

        let elems = vec![
            Integer::from(0x54333234),
            Integer::from(0x4a888b6c),
            Integer::from(0x6276e54b),
            Integer::from(0x6275454a),
            Integer::from(0x6275454a) * Integer::from(0x7355_3254) * Integer::from(0x7355_3254),
            Integer::from(0x4a888b6c),
            Integer::from(0x6276e54b),
            Integer::from(0x6275454a),
        ];

        // create reducible product
        let mut m: Box<dyn Reducible<Rsa2048>> = Box::new(elems[0].clone());
        for v in elems[1..].iter() {
            m = mul_reducible::<Rsa2048>(m, v.clone());
        }
        let base = Rsa2048::unknown_order_elem();
        let (Q1, rem1) = m.reduce(&base, &p);

        // compute base truth
        let mut res = Integer::from(1);
        for v in elems.iter() {
            res = res * v;
        }
        let (div2, rem2) = res.div_rem(p.clone());

        // compare
        assert_eq!(Q1, Rsa2048::exp(&base, &div2));
        assert_eq!(rem1, rem2);
    }
}

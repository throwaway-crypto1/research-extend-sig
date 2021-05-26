use super::*;

use num_traits::Zero;

const WINDOWS: usize = (curve::FP_INNER_BITS + window::WINDOW_SIZE - 1) / window::WINDOW_SIZE;

pub struct Witness {
    windows: Vec<window::Witness>,
    additions: Vec<addition::Witness>,
}

pub struct Gadget {
    windows: Vec<window::EdwardsWindow>,
}

/// Optimized circuit for fixed-based exponentiation
impl Gadget {
    pub fn new(base: CurvePoint) -> Self {
        debug_assert!(base.on_curve());

        let mut current = base;
        let mut windows = Vec::with_capacity(WINDOWS);
        for _ in 0..WINDOWS {
            let win = window::EdwardsWindow::new(curve::param_d(), current);
            current = current + win.lookup(true, true, true);
            windows.push(win);
        }
        Self { windows }
    }

    pub fn compute(&self, scalar: curve::Fp) -> CurvePoint {
        let mut bits = scalar.iter_bit().map(|b| b.0);
        let mut point = Zero::zero();
        for win in self.windows.iter() {
            let b0 = bits.next().unwrap_or(0) != 0;
            let b1 = bits.next().unwrap_or(0) != 0;
            let b2 = bits.next().unwrap_or(0) != 0;
            point = win.lookup(b0, b1, b2) + point;
        }
        debug_assert!(bits.next().is_none());
        point
    }

    pub fn witness(&self, scalar: curve::Fp) -> (Witness, CurvePoint) {
        let mut bits = scalar.iter_bit().map(|b| b.0 != 0);
        let mut point = None;
        let mut windows = Vec::with_capacity(self.windows.len() - 1);
        let mut additions = Vec::with_capacity(self.windows.len());
        for (i, window) in self.windows.iter().enumerate() {
            // do lookup
            let b0 = bits.next().unwrap_or(false);
            let b1 = bits.next().unwrap_or(false);
            let b2 = bits.next().unwrap_or(false);
            let win = window.witness(b0, b1, b2);

            // do addition
            point = Some(match point {
                None => win.lookup(),
                Some(p) => {
                    let add = addition::Gadget::witness(p, win.lookup());
                    let new = add.output();
                    additions.push(add);
                    new
                }
            });
            windows.push(win);
        }
        debug_assert_eq!(windows.len(), additions.len() + 1);
        (Witness { windows, additions }, point.unwrap())
    }

    /// The bit decomposition is padded with zeroes (at "circuit compile time") in case it is to short.
    pub fn gadget<CS: ConstraintSystem>(
        &self,
        cs: &mut CS,
        scalar: &bits::Decompose, // bit decomposition of scalar
        witness: Option<&Witness>,
    ) -> Result<CurveVariable, R1CSError> {
        // traverse bits, least significant to most
        let mut bits = scalar.iter_bits();

        // do all additions
        let mut additions = Vec::with_capacity(self.windows.len() - 1);
        for i in 0..self.windows.len() - 1 {
            additions.push(addition::Gadget::gadget(
                cs,
                witness.map(|w| &w.additions[i]),
            )?);
        }

        // constrain first left term to lookup table 1
        self.windows[0].gadget(
            cs,
            witness.map(|w| &w.windows[0]),
            additions[0].0,
            bits.next().unwrap(),
            bits.next().unwrap(),
            bits.next().unwrap(),
        )?;

        // constrain first right term to lookup table 2
        self.windows[1].gadget(
            cs,
            witness.map(|w| &w.windows[1]),
            additions[0].1,
            bits.next().unwrap(),
            bits.next().unwrap(),
            bits.next().unwrap(),
        )?;

        // handle remaining windows one-by-one
        let mut next_j = 1; // next addition index
        let mut output = additions[0].2;
        for i in 2..self.windows.len() {
            // constrain left term to current result
            additions[next_j].0.equal(cs, &output)?;

            // constrain right term to window
            self.windows[i].gadget(
                cs,
                witness.map(|w| &w.windows[i]),
                additions[next_j].1,
                bits.next().unwrap(),
                bits.next().unwrap(),
                bits.next().unwrap(),
            )?;

            // update current result
            output = additions[next_j].2;
            next_j += 1;
        }

        Ok(output)
    }
}

mod tests {
    use super::*;

    use bulletproofs::{BulletproofGens, PedersenGens};
    use curve25519_dalek::ristretto::CompressedRistretto;
    use merlin::Transcript;

    use rand::thread_rng;
    use rand::Rng;

    use test::Bencher;

    use num_traits::One;

    #[test]
    fn test_fixexp_compute() {
        let mut rng = thread_rng();
        let fixexp = Gadget::new(curve::g0());
        let scalar = curve::Fp::random(&mut rng);
        let real = scalar * curve::g0();
        let point = fixexp.compute(scalar);
        assert_eq!(point, real);
    }

    /*
    #[test]
    fn test_lookup_proof() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        let mut rng = thread_rng();

        let u: [Scalar; 8] = [
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
            Scalar::random(&mut rng),
        ];

        let b0: bool = rng.gen();
        let b1: bool = rng.gen();
        let b2: bool = rng.gen();

        let i = (b0 as usize) + 2 * (b1 as usize) + 4 * (b2 as usize);

        // happy path
        {
            let mut prover = Prover::new(&pc_gens, Transcript::new(b"Test"));
            let mut verifier = Verifier::new(Transcript::new(b"Test"));

            let s0 = Bit::new(&mut prover, b0).unwrap();
            let s1 = Bit::new(&mut prover, b1).unwrap();
            let s2 = Bit::new(&mut prover, b2).unwrap();
            let sa = Bit::mul(&mut prover, s1, s2);

            let blind_e = Scalar::random(&mut rng);
            let value_e = u[i];

            // prove

            let (comm_e, input_e) = prover.commit(value_e, blind_e);

            lookup(&mut prover, sa, s0, s1, s2, input_e.into(), &u);

            let proof = prover.prove(&bp_gens).unwrap();

            // verify

            let s0 = Bit::free(&mut verifier).unwrap();
            let s1 = Bit::free(&mut verifier).unwrap();
            let s2 = Bit::free(&mut verifier).unwrap();
            let sa = Bit::mul(&mut verifier, s1, s2);

            let input_e = verifier.commit(comm_e);

            lookup(&mut verifier, sa, s0, s1, s2, input_e.into(), &u);

            assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok())
        }

        // error path
        {
            let mut prover = Prover::new(&pc_gens, Transcript::new(b"Test"));
            let mut verifier = Verifier::new(Transcript::new(b"Test"));

            let s0 = Bit::new(&mut prover, b0).unwrap();
            let s1 = Bit::new(&mut prover, b1).unwrap();
            let s2 = Bit::new(&mut prover, b2).unwrap();
            let sa = Bit::mul(&mut prover, s1, s2);

            let blind_e = Scalar::random(&mut rng);
            let value_e = Scalar::random(&mut rng);

            // prove

            let (comm_e, input_e) = prover.commit(value_e, blind_e);

            lookup(&mut prover, sa, s0, s1, s2, input_e.into(), &u);

            let proof = prover.prove(&bp_gens).unwrap();

            // verify

            let s0 = Bit::free(&mut verifier).unwrap();
            let s1 = Bit::free(&mut verifier).unwrap();
            let s2 = Bit::free(&mut verifier).unwrap();
            let sa = Bit::mul(&mut verifier, s1, s2);

            let input_e = verifier.commit(comm_e);

            lookup(&mut verifier, sa, s0, s1, s2, input_e.into(), &u);

            assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_err())
        }
    }

    #[test]
    fn test_window_proof() {
        let ed_window = EdwardsWindow::new(
            Scalar::from_bytes_mod_order([
                0x33, 0xd1, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
                0xde, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x10,
            ]),
            curve::generator_0(),
        );

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        let transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(&pc_gens, transcript);

        let transcript = Transcript::new(b"Test");
        let mut verifier = Verifier::new(transcript);

        // compute witness

        let input = PointValue {
            x: Scalar::one(),
            y: Scalar::zero(),
        };

        let s0 = Bit::new(&mut prover, true).unwrap();
        let s1 = Bit::new(&mut prover, true).unwrap();
        let s2 = Bit::new(&mut prover, true).unwrap();

        let witness = ed_window.compute(input, true, true, true);

        let blind_x = Scalar::from(53753735735u64); // clearly a dummy
        let blind_y = Scalar::from(46713612753u64);

        // prove

        let (comm_x, input_x) = prover.commit(input.x, blind_x);
        let (comm_y, input_y) = prover.commit(input.y, blind_y);

        let input = Point {
            x: input_x,
            y: input_y,
        };

        ed_window
            .gadget(&mut prover, Some(&witness), input, s0, s1, s2)
            .unwrap();

        let proof = prover.prove(&bp_gens).unwrap();

        // verify

        let s0 = Bit::free(&mut verifier).unwrap();
        let s1 = Bit::free(&mut verifier).unwrap();
        let s2 = Bit::free(&mut verifier).unwrap();

        let input_x = verifier.commit(comm_x);
        let input_y = verifier.commit(comm_y);

        let input = Point {
            x: input_x,
            y: input_y,
        };

        ed_window
            .gadget(&mut verifier, None, input, s0, s1, s2)
            .unwrap();

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap()
    }

    #[bench]
    fn randomize_prove(b: &mut Bencher) {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2100, 1);

        let fixexp = Gadget::new(curve::g0());

        // pick random scalar

        let mut rng = thread_rng();
        let scalar = curve::Fp::random(&mut rng);
        let witness = fixexp.witness(scalar);

        b.iter(|| {
            let transcript = Transcript::new(b"Test");
            let scalar = bits::Gadget::new_size(250);
            scalar.wit

            let mut prover = Prover::new(&pc_gens, transcript);
            let blind_x = Scalar::random(&mut rng);
            let blind_y = Scalar::random(&mut rng);
            fixexp.gadget(&mut prover, Some(&witness), input).unwrap();
            let proof = prover.prove(&bp_gens).unwrap();
        })
    }

    #[bench]
    fn randomize_verify(b: &mut Bencher) {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2100, 1);

        let randomize = FixScalarMult::new(curve::param_d(), curve::generator_0());

        // compute witness

        let input = PointValue {
            x: Scalar::one(),
            y: Scalar::zero(),
        };

        // pick random scalar

        let mut rng = thread_rng();
        let scalar = curve::Fp::random(&mut rng);
        let witness = randomize.witness(input, scalar);

        let transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(&pc_gens, transcript);
        let blind_x = Scalar::from(53753735735u64); // clearly a dummy
        let blind_y = Scalar::from(46713612753u64);
        let (comm_x, input_x) = prover.commit(input.x, blind_x);
        let (comm_y, input_y) = prover.commit(input.y, blind_y);
        let input = Point {
            x: input_x,
            y: input_y,
        };
        randomize
            .gadget(&mut prover, Some(&witness), input)
            .unwrap();

        let proof = prover.prove(&bp_gens).unwrap();

        b.iter(|| {
            let transcript = Transcript::new(b"Test");
            let mut verifier = Verifier::new(transcript);
            let input_x = verifier.commit(comm_x);
            let input_y = verifier.commit(comm_y);
            let input = Point {
                x: input_x,
                y: input_y,
            };
            randomize.gadget(&mut verifier, None, input).unwrap();
            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap()
        })
    }

    #[test]
    fn test_randomize_proof() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2100, 1);
        let transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(&pc_gens, transcript);

        let transcript = Transcript::new(b"Test");
        let mut verifier = Verifier::new(transcript);

        let randomize = FixScalarMult::new(curve::param_d(), curve::generator_0());

        // pick random point

        let mut rng = thread_rng();
        let input = randomize.compute(curve::Fp::random(&mut rng), curve::identity());

        // pick random scalar

        let scalar = curve::Fp::random(&mut rng);
        let witness = randomize.witness(input, scalar);

        // prove

        let blind_x = Scalar::random(&mut rng); // clearly a dummy
        let blind_y = Scalar::random(&mut rng);

        let (comm_x, input_x) = prover.commit(input.x, blind_x);
        let (comm_y, input_y) = prover.commit(input.y, blind_y);

        let input = Point {
            x: input_x,
            y: input_y,
        };

        randomize
            .gadget(&mut prover, Some(&witness), input)
            .unwrap();

        // println!("{:?}", prover.multipliers_len());

        let proof = prover.prove(&bp_gens).unwrap();

        // verify

        let input_x = verifier.commit(comm_x);
        let input_y = verifier.commit(comm_y);

        let input = Point {
            x: input_x,
            y: input_y,
        };

        randomize.gadget(&mut verifier, None, input).unwrap();

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap()
    }

    #[bench]
    fn randomize_prove(b: &mut Bencher) {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2100, 1);

        let randomize = FixScalarMult::new(curve::param_d(), curve::generator_0());

        // compute witness

        let input = PointValue {
            x: Scalar::one(),
            y: Scalar::zero(),
        };

        // pick random scalar

        let mut rng = thread_rng();
        let scalar = curve::Fp::random(&mut rng);
        let witness = randomize.witness(input, scalar);

        b.iter(|| {
            let transcript = Transcript::new(b"Test");
            let mut prover = Prover::new(&pc_gens, transcript);
            let blind_x = Scalar::random(&mut rng);
            let blind_y = Scalar::random(&mut rng);
            let (comm_x, input_x) = prover.commit(input.x, blind_x);
            let (comm_y, input_y) = prover.commit(input.y, blind_y);
            let input = Point {
                x: input_x,
                y: input_y,
            };
            randomize
                .gadget(&mut prover, Some(&witness), input)
                .unwrap();
            let proof = prover.prove(&bp_gens).unwrap();
        })
    }

    #[bench]
    fn randomize_verify(b: &mut Bencher) {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2100, 1);

        let randomize = FixScalarMult::new(curve::param_d(), curve::generator_0());

        // compute witness

        let input = PointValue {
            x: Scalar::one(),
            y: Scalar::zero(),
        };

        // pick random scalar

        let mut rng = thread_rng();
        let scalar = curve::Fp::random(&mut rng);
        let witness = randomize.witness(input, scalar);

        let transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(&pc_gens, transcript);
        let blind_x = Scalar::from(53753735735u64); // clearly a dummy
        let blind_y = Scalar::from(46713612753u64);
        let (comm_x, input_x) = prover.commit(input.x, blind_x);
        let (comm_y, input_y) = prover.commit(input.y, blind_y);
        let input = Point {
            x: input_x,
            y: input_y,
        };
        randomize
            .gadget(&mut prover, Some(&witness), input)
            .unwrap();

        let proof = prover.prove(&bp_gens).unwrap();

        b.iter(|| {
            let transcript = Transcript::new(b"Test");
            let mut verifier = Verifier::new(transcript);
            let input_x = verifier.commit(comm_x);
            let input_y = verifier.commit(comm_y);
            let input = Point {
                x: input_x,
                y: input_y,
            };
            randomize.gadget(&mut verifier, None, input).unwrap();
            verifier.verify(&proof, &pc_gens, &bp_gens).unwrap()
        })
    }

    #[test]
    fn test_randomize_proof() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(2100, 1);
        let transcript = Transcript::new(b"Test");
        let mut prover = Prover::new(&pc_gens, transcript);

        let transcript = Transcript::new(b"Test");
        let mut verifier = Verifier::new(transcript);

        let randomize = FixScalarMult::new(curve::param_d(), curve::generator_0());

        // pick random point

        let mut rng = thread_rng();
        let input = randomize.compute(curve::Fp::random(&mut rng), curve::identity());

        // pick random scalar

        let scalar = curve::Fp::random(&mut rng);
        let witness = randomize.witness(input, scalar);

        // prove

        let blind_x = Scalar::random(&mut rng); // clearly a dummy
        let blind_y = Scalar::random(&mut rng);

        let (comm_x, input_x) = prover.commit(input.x, blind_x);
        let (comm_y, input_y) = prover.commit(input.y, blind_y);

        let input = Point {
            x: input_x,
            y: input_y,
        };

        randomize
            .gadget(&mut prover, Some(&witness), input)
            .unwrap();

        // println!("{:?}", prover.multipliers_len());

        let proof = prover.prove(&bp_gens).unwrap();

        // verify

        let input_x = verifier.commit(comm_x);
        let input_y = verifier.commit(comm_y);

        let input = Point {
            x: input_x,
            y: input_y,
        };

        randomize.gadget(&mut verifier, None, input).unwrap();

        verifier.verify(&proof, &pc_gens, &bp_gens).unwrap()
    }
     */
}

use extend_sig::unknown::exppok::ProofOfExp;
use extend_sig::*;
use std::time::{Duration, SystemTime};

use num_traits::One;
use rand_core::OsRng;
use rug::{integer, Integer};

use cpsnarks_set::utils::ConvertibleUnknownOrderGroup;

use bulletproofs::PedersenGens;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;

use serde::Serialize;

use accumulator::group::{ClassGroup, Rsa3072};

use std::env;

use bincode;

fn bench_sign<G: ConvertibleUnknownOrderGroup, E: ProofOfExp<G>>(
    iters: usize,
    num_extend: usize, // how many extensions
    num_keys: usize,   // how many keys in each
) {
    let msg: &[u8] = &[];

    println!("iters: {}", iters);
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

    let start = SystemTime::now();

    println!("time_start: {}", num_keys);

    for _ in 0..iters {
        let mut sig: Signature<G, E> = sk.sign(&mut ctx);
        for pks in pkss.iter() {
            sig = sig.extend(&ctx, &pks[..], &total);
        }
    }

    let elapsed = start.elapsed().unwrap();

    println!("duration: {}", elapsed.as_nanos());
}

fn bench_verify<G: ConvertibleUnknownOrderGroup, E: ProofOfExp<G>>(
    iters: usize,
    num_extend: usize, // how many extensions
    num_keys: usize,   // how many keys in each
) {
    let msg: &[u8] = &[];

    println!("iters: {}", iters);
    println!("num_extend: {}", num_extend);
    println!("num_keys: {}", num_keys);

    let mut ctx = Context::<G>::setup(msg);

    let sk = SigningKey::new();
    let pk = sk.pk();

    let mut pkss: Vec<Vec<PublicKey>> = vec![];
    let mut skss: Vec<Vec<SigningKey>> = vec![];
    let mut total: Vec<PublicKey> = vec![pk];

    for j in 0..num_extend {
        let mut sks: Vec<SigningKey> = vec![];
        for i in 0..num_keys {
            sks.push(SigningKey::new());
        }
        let pks: Vec<PublicKey> = sks.iter().map(|sk| sk.pk()).collect();
        total.extend(pks.iter());
        skss.push(sks);
        pkss.push(pks);
    }

    assert_eq!(total.len(), num_extend * num_keys + 1);

    let mut sig: Signature<G, E> = sk.sign(&mut ctx);
    for pks in pkss.iter() {
        sig = sig.extend(&ctx, &pks[..], &total);
    }

    println!("size: {}", bincode::serialize(&sig).unwrap().len());

    let start = SystemTime::now();

    println!("time_start: {}", num_keys);

    for _ in 0..iters {
        assert!(sig.verify(&ctx, &total[..]).is_some());
    }

    let elapsed = start.elapsed().unwrap();

    println!("duration: {}", elapsed.as_nanos());
}

fn bench_verify_args<G: ConvertibleUnknownOrderGroup>() {
    let keys: usize = env::var("BENCH_KEYS")
        .unwrap_or("1".to_string())
        .parse()
        .unwrap();
    let exts: usize = env::var("BENCH_EXTS")
        .unwrap_or("1".to_string())
        .parse()
        .unwrap();
    let iters: usize = env::var("BENCH_ITERS")
        .unwrap_or("1".to_string())
        .parse()
        .unwrap();
    bench_verify::<G, unknown::exppok::Proof<_>>(iters, exts, keys);
}

fn bench_sign_args<G: ConvertibleUnknownOrderGroup>() {
    let keys: usize = env::var("BENCH_KEYS")
        .unwrap_or("1".to_string())
        .parse()
        .unwrap();
    let exts: usize = env::var("BENCH_EXTS")
        .unwrap_or("1".to_string())
        .parse()
        .unwrap();
    let iters: usize = env::var("BENCH_ITERS")
        .unwrap_or("1".to_string())
        .parse()
        .unwrap();
    bench_sign::<G, unknown::exppok::Proof<_>>(iters, exts, keys);
}

fn main() {
    let algo = env::var("BENCH_ALGO").unwrap();
    let op = env::var("BENCH_OP").unwrap();

    match (algo.as_ref(), op.as_ref()) {
        ("rsa", "sign") => bench_sign_args::<Rsa3072>(),
        ("rsa", "verify") => bench_verify_args::<Rsa3072>(),
        ("class", "sign") => bench_sign_args::<ClassGroup>(),
        ("class", "verify") => bench_verify_args::<ClassGroup>(),
        _ => unimplemented!(),
    }
}

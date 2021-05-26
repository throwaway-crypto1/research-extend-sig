pub mod base;
pub mod exppok;
pub mod extend;

use cpsnarks_set::utils::ConvertibleUnknownOrderGroup;
use rand_core::{OsRng, RngCore};

use rug::rand::RandState;
use rug::Integer;

use crate::bytes_to_integer;

pub fn random_bound(upper: &Integer) -> Integer {
    let size = (upper.significant_bits() + 7) / 8;
    let mut bytes = vec![0; size as usize];
    OsRng.fill_bytes(&mut bytes);
    bytes_to_integer(&bytes[..])
}

pub fn random_order<G: ConvertibleUnknownOrderGroup>() -> Integer {
    random_bound(&G::order_upper_bound())
}

pub fn new_fujisaki_okamoto_gens<G: ConvertibleUnknownOrderGroup>() -> (G::Elem, G::Elem) {
    let mut rand = RandState::new();
    let g = G::unknown_possibly_random_order_elem(&mut rand);
    let mut h = G::unknown_possibly_random_order_elem(&mut rand);
    if g == h {
        let r = random_order::<G>();
        h = G::exp(&h, &r);
    }
    (g, h)
}

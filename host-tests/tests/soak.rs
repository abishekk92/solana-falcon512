use pqcrypto_falcon::falcon512;
use pqcrypto_traits::sign::{DetachedSignature, PublicKey};
use rayon::prelude::*;
use solana_falcon512::{
    FALCON_512_PUBKEY_LEN, FALCON_512_SIGNATURE_LEN, Falcon512Pubkey, Falcon512Signature,
};
use std::time::Instant;

fn iters(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed.max(1))
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn fill(&mut self, buf: &mut [u8]) {
        let mut i = 0;
        while i < buf.len() {
            let v = self.next().to_le_bytes();
            let n = (buf.len() - i).min(8);
            buf[i..i + n].copy_from_slice(&v[..n]);
            i += n;
        }
    }
}

fn pad_pk_bytes(pk: &falcon512::PublicKey) -> [u8; FALCON_512_PUBKEY_LEN] {
    let mut a = [0u8; FALCON_512_PUBKEY_LEN];
    a.copy_from_slice(pk.as_bytes());
    a
}

fn pad_sig_bytes(sig: &falcon512::DetachedSignature) -> [u8; FALCON_512_SIGNATURE_LEN] {
    let mut a = [0u8; FALCON_512_SIGNATURE_LEN];
    a[..sig.as_bytes().len()].copy_from_slice(sig.as_bytes());
    a
}

#[test]
#[ignore = "soak test; run with `cargo test --release -- --ignored`"]
fn soak_completeness() {
    // Every signed message must verify true. Default 100k; override via SOAK_COMPLETENESS=N.
    let n = iters("SOAK_COMPLETENESS", 100_000);
    println!("soak_completeness: {n} iterations");
    let start = Instant::now();
    let failures: usize = (0..n)
        .into_par_iter()
        .map(|i| {
            let (pk, sk) = falcon512::keypair();
            let msg = format!("soak completeness msg #{i}");
            let sig = falcon512::detached_sign(msg.as_bytes(), &sk);
            let pubkey = Falcon512Pubkey::from(pad_pk_bytes(&pk));
            let signature = Falcon512Signature::from(pad_sig_bytes(&sig));
            if signature.verify(msg.as_bytes(), &pubkey) {
                0
            } else {
                1
            }
        })
        .sum();
    let elapsed = start.elapsed();
    println!(
        "soak_completeness: {n} iters in {:.1}s ({:.0} iter/s)",
        elapsed.as_secs_f64(),
        n as f64 / elapsed.as_secs_f64()
    );
    assert_eq!(
        failures, 0,
        "{failures} valid signatures failed verification"
    );
}

#[test]
#[ignore = "soak test; run with `cargo test --release -- --ignored`"]
fn soak_random_inputs_reject() {
    // Random pubkey/sig/msg — verify must always reject (cryptographically negligible
    // chance of accidental acceptance).
    let n = iters("SOAK_RANDOM", 10_000_000);
    println!("soak_random_inputs_reject: {n} iterations");
    let start = Instant::now();
    let accepted: usize = (0..n)
        .into_par_iter()
        .with_min_len(4096)
        .map(|i| {
            let mut rng = Rng::new(i as u64 + 1);
            let mut pk = [0u8; FALCON_512_PUBKEY_LEN];
            let mut sg = [0u8; FALCON_512_SIGNATURE_LEN];
            let mut msg = [0u8; 32];
            rng.fill(&mut pk);
            rng.fill(&mut sg);
            rng.fill(&mut msg);
            let pubkey = Falcon512Pubkey::from(pk);
            let signature = Falcon512Signature::from(sg);
            if signature.verify(&msg, &pubkey) {
                1
            } else {
                0
            }
        })
        .sum();
    let elapsed = start.elapsed();
    println!(
        "soak_random_inputs_reject: {n} iters in {:.1}s ({:.0} iter/s)",
        elapsed.as_secs_f64(),
        n as f64 / elapsed.as_secs_f64()
    );
    assert_eq!(accepted, 0, "{accepted} random inputs were accepted");
}

#[test]
#[ignore = "soak test; run with `cargo test --release -- --ignored`"]
fn soak_mutated_sig_rejects() {
    // Single-bit flips of a valid signature must always reject.
    let n = iters("SOAK_MUTATIONS", 10_000_000);
    println!("soak_mutated_sig_rejects: {n} iterations");

    let pairs: Vec<_> = (0..16)
        .map(|i| {
            let (pk, sk) = falcon512::keypair();
            let msg = format!("mutation soak msg #{i}").into_bytes();
            let sig = falcon512::detached_sign(&msg, &sk);
            (pad_pk_bytes(&pk), pad_sig_bytes(&sig), msg)
        })
        .collect();

    let start = Instant::now();
    let accepted: usize = (0..n)
        .into_par_iter()
        .with_min_len(4096)
        .map(|i| {
            let mut rng = Rng::new(i as u64 + 1);
            let (pk, sig, msg) = &pairs[i % pairs.len()];
            let mut sig_arr = *sig;
            let pos = (rng.next() as usize) % FALCON_512_SIGNATURE_LEN;
            let bit = (rng.next() % 8) as u8;
            sig_arr[pos] ^= 1 << bit;
            let pubkey = Falcon512Pubkey::from(*pk);
            let signature = Falcon512Signature::from(sig_arr);
            if signature.verify(msg, &pubkey) { 1 } else { 0 }
        })
        .sum();
    let elapsed = start.elapsed();
    println!(
        "soak_mutated_sig_rejects: {n} iters in {:.1}s ({:.0} iter/s)",
        elapsed.as_secs_f64(),
        n as f64 / elapsed.as_secs_f64()
    );
    assert_eq!(accepted, 0, "{accepted} mutated sigs were accepted");
}

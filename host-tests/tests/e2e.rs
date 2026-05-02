use pqcrypto_falcon::falcon512;
use pqcrypto_traits::sign::{DetachedSignature, PublicKey};
use solana_falcon512::{
    FALCON_512_PREPARED_PUBKEY_LEN, FALCON_512_PUBKEY_LEN, FALCON_512_SIGNATURE_LEN,
    Falcon512PreparedPubkey, Falcon512Pubkey, Falcon512Signature,
};

fn sign_with_pqclean(msg: &[u8]) -> ([u8; FALCON_512_PUBKEY_LEN], [u8; FALCON_512_SIGNATURE_LEN]) {
    let (pk, sk) = falcon512::keypair();
    let sig = falcon512::detached_sign(msg, &sk);

    let pk_bytes = pk.as_bytes();
    let sig_bytes = sig.as_bytes();
    assert_eq!(pk_bytes.len(), FALCON_512_PUBKEY_LEN);
    assert!(sig_bytes.len() <= FALCON_512_SIGNATURE_LEN);

    let mut pk_arr = [0u8; FALCON_512_PUBKEY_LEN];
    pk_arr.copy_from_slice(pk_bytes);

    let mut sig_arr = [0u8; FALCON_512_SIGNATURE_LEN];
    sig_arr[..sig_bytes.len()].copy_from_slice(sig_bytes);

    (pk_arr, sig_arr)
}

#[test]
fn verify_pqclean_signature() {
    let msg = b"falcon-512 test message";
    let (pk_bytes, sig_bytes) = sign_with_pqclean(msg);

    let pubkey = Falcon512Pubkey::from(pk_bytes);
    let signature = Falcon512Signature::from(sig_bytes);

    assert!(signature.verify(msg, &pubkey));
}

#[test]
fn rejects_modified_message() {
    let msg = b"original message";
    let (pk_bytes, sig_bytes) = sign_with_pqclean(msg);

    let pubkey = Falcon512Pubkey::from(pk_bytes);
    let signature = Falcon512Signature::from(sig_bytes);

    assert!(!signature.verify(b"tampered message", &pubkey));
}

#[test]
fn rejects_modified_signature() {
    let msg = b"falcon-512 test message";
    let (pk_bytes, sig_bytes) = sign_with_pqclean(msg);
    let pubkey = Falcon512Pubkey::from(pk_bytes);

    // Each mutation should be rejected. Hits one byte in each of the three
    // wire-format regions: the header (rejected at header check), the salt
    // (rejected at hash-to-point divergence), the compressed s2 payload
    // (rejected at norm or decompression). The deeper-fuzz battery in
    // `fuzz.rs::fuzz_mutated_signature_rejects` exercises 500 random mutations.
    for &mutation_byte in &[0usize, 20, 100] {
        let mut tampered = sig_bytes;
        tampered[mutation_byte] ^= 0x01;
        let signature = Falcon512Signature::from(tampered);
        assert!(
            !signature.verify(msg, &pubkey),
            "mutation at byte {mutation_byte} was not rejected"
        );
    }
}

#[test]
fn rejects_wrong_pubkey() {
    let msg = b"falcon-512 test message";
    let (_pk_bytes, sig_bytes) = sign_with_pqclean(msg);
    let (other_pk_bytes, _) = sign_with_pqclean(b"unrelated");

    let pubkey = Falcon512Pubkey::from(other_pk_bytes);
    let signature = Falcon512Signature::from(sig_bytes);

    assert!(!signature.verify(msg, &pubkey));
}

#[test]
fn many_signatures_verify() {
    // Run several independent keypairs to exercise different signature lengths
    // and nonce/coefficient distributions.
    for i in 0..8 {
        let msg = format!("message #{i}");
        let (pk_bytes, sig_bytes) = sign_with_pqclean(msg.as_bytes());
        let pubkey = Falcon512Pubkey::from(pk_bytes);
        let signature = Falcon512Signature::from(sig_bytes);
        assert!(signature.verify(msg.as_bytes(), &pubkey), "iter {i}");
    }
}

#[test]
fn prepared_pubkey_roundtrip_matches_direct_verify() {
    // Models the on-chain "prepare once, store in PDA, verify later" flow:
    // call `prepare_pubkey()` at runtime, serialize to bytes, deserialize
    // back, and confirm `verify_with_prepared` accepts the same signatures
    // that direct `verify` accepts (and rejects the same forgeries).
    for i in 0..8 {
        let msg = format!("prepared roundtrip msg #{i}");
        let (pk_bytes, sig_bytes) = sign_with_pqclean(msg.as_bytes());
        let pubkey = Falcon512Pubkey::from(pk_bytes);
        let signature = Falcon512Signature::from(sig_bytes);

        let prepared = pubkey.prepare_pubkey();
        let serialized: [u8; FALCON_512_PREPARED_PUBKEY_LEN] = *prepared.as_bytes();
        let prepared_roundtripped = Falcon512PreparedPubkey::from_bytes(serialized);

        assert!(
            signature.verify(msg.as_bytes(), &pubkey),
            "iter {i}: direct verify rejected a valid signature"
        );
        assert!(
            signature.verify_with_prepared(msg.as_bytes(), &prepared),
            "iter {i}: prepared verify rejected a valid signature"
        );
        assert!(
            signature.verify_with_prepared(msg.as_bytes(), &prepared_roundtripped),
            "iter {i}: roundtripped prepared verify rejected a valid signature"
        );

        // And the negative direction — tampered message must fail on the
        // prepared path too.
        let tampered = format!("tampered msg #{i}");
        assert!(
            !signature.verify_with_prepared(tampered.as_bytes(), &prepared_roundtripped),
            "iter {i}: prepared verify accepted a tampered message"
        );
    }
}

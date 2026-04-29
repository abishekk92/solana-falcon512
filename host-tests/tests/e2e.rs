use pqcrypto_falcon::falcon512;
use pqcrypto_traits::sign::{DetachedSignature, PublicKey};
use solana_falcon512::{
    FALCON_512_PUBKEY_LEN, FALCON_512_SIGNATURE_LEN, Falcon512Pubkey, Falcon512Signature,
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
    let (pk_bytes, mut sig_bytes) = sign_with_pqclean(msg);

    // Flip a bit inside the compressed sig payload (past the 1-byte header and
    // 40-byte nonce).
    sig_bytes[100] ^= 0x01;

    let pubkey = Falcon512Pubkey::from(pk_bytes);
    let signature = Falcon512Signature::from(sig_bytes);

    assert!(!signature.verify(msg, &pubkey));
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

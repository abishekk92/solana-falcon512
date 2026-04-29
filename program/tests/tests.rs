use mollusk_svm::Mollusk;
use pqcrypto_falcon::falcon512;
use pqcrypto_traits::sign::{DetachedSignature, SecretKey};
use solana_address::Address;
use solana_instruction::Instruction;

const SK_BYTES: &[u8] = include_bytes!("fixtures/falcon.sk");
const SIG_LEN: usize = 666;

fn sign_ix_data(msg: &[u8]) -> Vec<u8> {
    let sk = falcon512::SecretKey::from_bytes(SK_BYTES).unwrap();
    let sig = falcon512::detached_sign(msg, &sk);
    let mut sig_padded = [0u8; SIG_LEN];
    sig_padded[..sig.as_bytes().len()].copy_from_slice(sig.as_bytes());
    let mut data = Vec::with_capacity(SIG_LEN + msg.len());
    data.extend_from_slice(&sig_padded);
    data.extend_from_slice(msg);
    data
}

// `cargo test-sbf` builds the SBF program and sets `SBF_OUT_DIR` to its
// `target/deploy` directory; Mollusk picks the `.so` up from there.
fn make_mollusk() -> (Mollusk, Address) {
    let program_id = Address::new_unique();
    let mollusk = Mollusk::new(&program_id, "program");
    (mollusk, program_id)
}

#[test]
fn verify_random_message() {
    let (mollusk, program_id) = make_mollusk();
    let mut msg = [0u8; 64];
    let mut state: u64 = 0x00C0_FFEE_DEAD_BEEF;
    for b in msg.iter_mut() {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *b = (state >> 56) as u8;
    }
    let data = sign_ix_data(&msg);
    let ix = Instruction {
        program_id,
        accounts: vec![],
        data,
    };
    let result = mollusk.process_instruction(&ix, &[]);
    assert!(
        !result.program_result.is_err(),
        "verify failed: {:?}",
        result.program_result
    );
    println!(
        "verify_random_message OK — compute units consumed: {}",
        result.compute_units_consumed
    );
}

#[test]
fn rejects_tampered_message() {
    let (mollusk, program_id) = make_mollusk();
    let mut data = sign_ix_data(b"original message");
    data[SIG_LEN] ^= 0x01;
    let ix = Instruction {
        program_id,
        accounts: vec![],
        data,
    };
    let result = mollusk.process_instruction(&ix, &[]);
    assert!(
        result.program_result.is_err(),
        "expected failure on tampered msg, got: {:?}",
        result.program_result
    );
}

#[test]
fn rejects_tampered_signature() {
    let (mollusk, program_id) = make_mollusk();
    let mut data = sign_ix_data(b"some message");
    data[100] ^= 0x01;
    let ix = Instruction {
        program_id,
        accounts: vec![],
        data,
    };
    let result = mollusk.process_instruction(&ix, &[]);
    assert!(
        result.program_result.is_err(),
        "expected failure on tampered sig, got: {:?}",
        result.program_result
    );
}

//! Pure-Rust Falcon-512 signature **verification**, optimised for Solana SBF.
//!
//! Implements [FN-DSA / Falcon] signature verification (compressed-format
//! signatures only, header byte `0x39`). The crate is `no_std`, allocation
//! free, and all heavy work — pubkey decoding, NTT, SHAKE-256, signature
//! decompression — is hand-written. On Solana SBF a single verify costs
//! roughly 255–290k compute units depending on the message length and whether
//! the pubkey is precomputed via [`Falcon512Pubkey::prepare_pubkey`].
//!
//! [FN-DSA / Falcon]: https://falcon-sign.info
//!
//! # Quick start
//!
//! ```ignore
//! use solana_falcon512::{Falcon512Pubkey, Falcon512Signature};
//!
//! let pubkey = Falcon512Pubkey::try_from(&pk_bytes[..])?;
//! let signature = Falcon512Signature::try_from(&sig_bytes[..])?;
//! let ok = signature.verify(message, &pubkey);
//! ```
//!
//! For Solana programs with a hard-coded pubkey, prefer the prepared-pubkey
//! path — `prepare_pubkey()` is a `const fn`, so the NTT-form pubkey can be
//! embedded as a `const` and the per-call work is reduced by ~99k CUs:
//!
//! ```ignore
//! use solana_falcon512::{Falcon512Pubkey, Falcon512PreparedPubkey};
//!
//! const PREPARED: Falcon512PreparedPubkey =
//!     Falcon512Pubkey::from_bytes(*include_bytes!("../keys/falcon.pk"))
//!         .prepare_pubkey();
//!
//! let ok = signature.verify_with_prepared(message, &PREPARED);
//! ```
//!
//! # Compatibility
//!
//! - **Falcon-512 only.** Falcon-1024 is not supported.
//! - **Compressed-format signatures only** (header `0x39`). Padded (`0x49`)
//!   and CT-format signatures are rejected.
//! - **Verify only.** Key generation and signing are out of scope; produce
//!   keys and signatures with PQClean / `pqcrypto-falcon` or a hardware key.
//!
//! # Security notes
//!
//! - This crate is **not audited**. Use at your own risk for protecting
//!   anything of value.
//! - Verification operates on **public data only** (signature, pubkey,
//!   message). It is deliberately **not** constant-time — it short-circuits
//!   on header / length / decompression failures and on the running L2 norm
//!   exceeding the bound. That's safe for verify, since none of those leak
//!   secret information.
//! - The implementation has been cross-checked against:
//!   - the NIST FIPS 202 SHAKE-256 KATs (empty input, `"abc"`, multi-block);
//!   - 1,000,000 PQClean-generated signatures (zero failures);
//!   - 10,000 random-input fuzz iterations and 500-iter mutation tests for
//!     each of `(signature, pubkey, message)` (zero false accepts).

#![cfg_attr(not(test), no_std)]

use solana_program_error::ProgramError;

mod codec;
mod keccak;
mod ntt;

/// Wire-encoded Falcon-512 pubkey length, including the 1-byte header.
pub const FALCON_512_PUBKEY_LEN: usize = 897;

/// Falcon-512 compressed-signature buffer length: 1 header byte + 40-byte
/// nonce + up to 625 bytes of Golomb-Rice-encoded `s2`. Signatures whose
/// encoded portion is shorter must zero-pad the trailing bytes.
pub const FALCON_512_SIGNATURE_LEN: usize = 666;

/// Serialised length of a [`Falcon512PreparedPubkey`]: 512 little-endian `u32`
/// coefficients = 2048 bytes. Use this as the account-data size when storing
/// a prepared pubkey on-chain to amortise the ~99k CU NTT step.
pub const FALCON_512_PREPARED_PUBKEY_LEN: usize = N * 4;

pub(crate) const N: usize = 512;
pub(crate) const Q: u32 = 12289;

const NONCE_LEN: usize = 40;
const L2_BOUND: u64 = 34_034_726;
const PUBKEY_HEADER: u8 = 0x09;
const SIG_HEADER: u8 = 0x39;

/// Wire-encoded Falcon-512 public key (header byte `0x09` + 14-bit-packed
/// polynomial `h ∈ Z_q[x] / (x^512 + 1)`).
#[derive(Clone, Eq, PartialEq)]
pub struct Falcon512Pubkey([u8; FALCON_512_PUBKEY_LEN]);

impl TryFrom<&[u8]> for Falcon512Pubkey {
    type Error = ProgramError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let bytes: [u8; FALCON_512_PUBKEY_LEN] = value
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        Ok(bytes.into())
    }
}

impl From<[u8; FALCON_512_PUBKEY_LEN]> for Falcon512Pubkey {
    fn from(value: [u8; FALCON_512_PUBKEY_LEN]) -> Self {
        Self(value)
    }
}

impl Falcon512Pubkey {
    /// Wrap a 897-byte buffer as a pubkey without validation. The contents
    /// are validated lazily at verify time (`verify`) or eagerly when
    /// preparing the NTT form (`prepare_pubkey`).
    pub const fn from_bytes(value: [u8; FALCON_512_PUBKEY_LEN]) -> Self {
        Self(value)
    }

    /// Borrow the raw 897-byte wire encoding.
    pub const fn as_bytes(&self) -> &[u8; FALCON_512_PUBKEY_LEN] {
        &self.0
    }

    /// Decode the pubkey polynomial and run a forward NTT, returning a form
    /// that lets [`Falcon512Signature::verify_with_prepared`] skip the per-call
    /// decode and forward NTT (saves ~99k CUs on Solana SBF).
    ///
    /// `const fn`, so consumer programs can embed the prepared pubkey as a
    /// `const` and pay zero runtime setup cost.
    ///
    /// # Panics
    ///
    /// Panics if the pubkey is malformed (wrong header, an out-of-range
    /// coefficient, or non-zero trailing bits). When invoked in const
    /// context this becomes a compile-time error — exactly what you want
    /// if the pubkey is baked into the binary. For untrusted runtime
    /// pubkeys, prefer [`Falcon512Signature::verify`] which never panics.
    pub const fn prepare_pubkey(&self) -> Falcon512PreparedPubkey {
        let bytes = &self.0;
        assert!(bytes[0] == PUBKEY_HEADER, "invalid pubkey header");

        let mut h = [0u32; N];
        let mut acc: u32 = 0;
        let mut acc_len: u32 = 0;
        let mut idx_in: usize = 1;
        let mut idx_out: usize = 0;
        while idx_out < N {
            acc = (acc << 8) | bytes[idx_in] as u32;
            idx_in += 1;
            acc_len += 8;
            if acc_len >= 14 {
                acc_len -= 14;
                let w = (acc >> acc_len) & 0x3FFF;
                assert!(w < Q, "invalid pubkey coefficient");
                h[idx_out] = w;
                idx_out += 1;
            }
        }
        assert!(
            (acc & ((1u32 << acc_len) - 1)) == 0,
            "non-zero trailing bits in pubkey",
        );

        ntt::ntt(&mut h);
        Falcon512PreparedPubkey(h)
    }
}

/// Pubkey polynomial decoded and pre-transformed into NTT (frequency) form,
/// ready to be multiplied with a signature's NTT polynomial during verify.
///
/// Construct from a [`Falcon512Pubkey`] via [`Falcon512Pubkey::prepare_pubkey`]
/// (which can run in `const` context), or from a 2048-byte serialised buffer
/// via [`Falcon512PreparedPubkey::from_bytes`] / [`as_bytes`](Self::as_bytes).
/// Storing the serialised form on-chain costs 2048 bytes of account data but
/// lets repeated verifies skip the ~99k-CU NTT prep on every call.
#[derive(Clone, Eq, PartialEq)]
pub struct Falcon512PreparedPubkey([u32; N]);

impl Falcon512PreparedPubkey {
    /// Reconstruct from a 2048-byte buffer produced by [`as_bytes`](Self::as_bytes).
    /// Coefficients are read as little-endian `u32`s. No validation is
    /// performed — the bytes are assumed to come from a trusted source
    /// (typically a Solana account previously written by your own program).
    pub const fn from_bytes(bytes: [u8; FALCON_512_PREPARED_PUBKEY_LEN]) -> Self {
        let mut h = [0u32; N];
        let mut i = 0;
        while i < N {
            h[i] = u32::from_le_bytes([
                bytes[4 * i],
                bytes[4 * i + 1],
                bytes[4 * i + 2],
                bytes[4 * i + 3],
            ]);
            i += 1;
        }
        Self(h)
    }

    /// Serialise to a 2048-byte buffer suitable for storing in a Solana
    /// account. Round-trips via [`from_bytes`](Self::from_bytes).
    pub fn as_bytes(&self) -> [u8; FALCON_512_PREPARED_PUBKEY_LEN] {
        let mut out = [0u8; FALCON_512_PREPARED_PUBKEY_LEN];
        for (i, &coeff) in self.0.iter().enumerate() {
            out[4 * i..4 * i + 4].copy_from_slice(&coeff.to_le_bytes());
        }
        out
    }
}

impl TryFrom<&[u8]> for Falcon512PreparedPubkey {
    type Error = ProgramError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let bytes: [u8; FALCON_512_PREPARED_PUBKEY_LEN] = value
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        Ok(Self::from_bytes(bytes))
    }
}

/// Wire-encoded compressed Falcon-512 signature (header `0x39` + 40-byte
/// nonce + Golomb-Rice-encoded `s2`, zero-padded to 666 bytes).
#[derive(Clone, Eq, PartialEq)]
pub struct Falcon512Signature([u8; FALCON_512_SIGNATURE_LEN]);

impl From<[u8; FALCON_512_SIGNATURE_LEN]> for Falcon512Signature {
    fn from(value: [u8; FALCON_512_SIGNATURE_LEN]) -> Self {
        Self(value)
    }
}

impl TryFrom<&[u8]> for Falcon512Signature {
    type Error = ProgramError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let bytes: [u8; FALCON_512_SIGNATURE_LEN] = value
            .try_into()
            .map_err(|_| ProgramError::InvalidArgument)?;
        Ok(bytes.into())
    }
}

impl Falcon512Signature {
    /// Wrap a 666-byte buffer as a signature without validation.
    pub const fn from_bytes(value: [u8; FALCON_512_SIGNATURE_LEN]) -> Self {
        Self(value)
    }

    /// Borrow the raw 666-byte wire encoding.
    pub const fn as_bytes(&self) -> &[u8; FALCON_512_SIGNATURE_LEN] {
        &self.0
    }

    /// Verify against a prepared pubkey. Use this when the pubkey is a
    /// `const` (e.g. baked into a Solana program) to avoid the pubkey decode
    /// + forward NTT on every call.
    ///
    /// Returns `false` on any failure mode — wrong header byte, malformed
    /// signature compression, L2-norm bound exceeded, etc. — and never
    /// panics. Distinguishing the failure reason is intentionally unsupported
    /// since outside of debugging it usually doesn't matter.
    #[inline(never)]
    pub fn verify_with_prepared(&self, message: &[u8], prepared: &Falcon512PreparedPubkey) -> bool {
        let sig = &self.0;
        if sig[0] != SIG_HEADER {
            return false;
        }

        let nonce = &sig[1..1 + NONCE_LEN];
        let comp = &sig[1 + NONCE_LEN..];

        let mut s2 = [0i16; N];
        if !codec::decompress_signature(comp, &mut s2) {
            return false;
        }

        let mut c = [0u16; N];
        codec::hash_to_point(nonce, message, &mut c);

        norm_check_with_prepared(&prepared.0, &s2, &c)
    }

    /// Verify against a raw pubkey. Decodes and runs the forward NTT on every
    /// call — for hot paths with a static pubkey, prefer
    /// [`verify_with_prepared`](Self::verify_with_prepared).
    ///
    /// Returns `false` on any failure mode (wrong header, malformed pubkey
    /// or signature, norm bound exceeded). Never panics.
    #[inline(never)]
    pub fn verify(&self, message: &[u8], pubkey: &Falcon512Pubkey) -> bool {
        let sig = &self.0;
        let pk = &pubkey.0;

        if sig[0] != SIG_HEADER || pk[0] != PUBKEY_HEADER {
            return false;
        }

        let nonce = &sig[1..1 + NONCE_LEN];
        let comp = &sig[1 + NONCE_LEN..];

        let mut s2 = [0i16; N];
        if !codec::decompress_signature(comp, &mut s2) {
            return false;
        }

        let mut c = [0u16; N];
        codec::hash_to_point(nonce, message, &mut c);

        check_norm(&pk[1..], &s2, &c)
    }
}

#[inline(never)]
fn check_norm(pk_data: &[u8], s2: &[i16; N], c: &[u16; N]) -> bool {
    let mut h_ntt = [0u32; N];
    if !codec::decode_pubkey_u32(pk_data, &mut h_ntt) {
        return false;
    }
    ntt::ntt(&mut h_ntt);
    norm_check_with_prepared(&h_ntt, s2, c)
}

#[inline(never)]
fn norm_check_with_prepared(h_pk_ntt: &[u32; N], s2: &[i16; N], c: &[u16; N]) -> bool {
    // Single working buffer that flows through three roles in sequence:
    //   1. NTT-main-levels output of s2  (after `ntt_main_levels_from_signed`)
    //   2. pointwise-mul + first-inv-level result  (after `fused_last_fwd_mul_first_inv`)
    //   3. s2 * h in coefficient form  (after `inv_ntt_main_levels`)
    // Re-using a single buffer eliminates the 2 KB `s2_ntt` scratch.
    let mut buf = [0u32; N];
    ntt::ntt_main_levels_from_signed(&mut buf, s2);
    ntt::fused_last_fwd_mul_first_inv(&mut buf, h_pk_ntt);
    ntt::inv_ntt_main_levels(&mut buf);

    let q_i32 = Q as i32;
    let half_q = q_i32 / 2;
    let mut norm: u64 = 0;
    for i in 0..N {
        let mut s1 = c[i] as i32 - buf[i] as i32;
        if s1 < 0 {
            s1 += q_i32;
        }
        let s1c = if s1 > half_q { s1 - q_i32 } else { s1 };
        norm += (s1c as i64 * s1c as i64) as u64;
        let s2c = s2[i] as i32;
        norm += (s2c as i64 * s2c as i64) as u64;
        if norm > L2_BOUND {
            return false;
        }
    }
    norm <= L2_BOUND
}

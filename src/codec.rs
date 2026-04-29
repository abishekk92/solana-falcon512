use crate::keccak::Shake256;
use crate::{N, Q};

pub fn decode_pubkey_u32(buf: &[u8], h: &mut [u32; N]) -> bool {
    if buf.len() < (N * 14) / 8 {
        return false;
    }
    let mut acc: u32 = 0;
    let mut acc_len: u32 = 0;
    let mut idx_in = 0usize;
    let mut idx_out = 0usize;
    while idx_out < N {
        acc = (acc << 8) | buf[idx_in] as u32;
        idx_in += 1;
        acc_len += 8;
        if acc_len >= 14 {
            acc_len -= 14;
            let w = (acc >> acc_len) & 0x3FFF;
            if w >= Q {
                return false;
            }
            h[idx_out] = w;
            idx_out += 1;
        }
    }
    if (acc & ((1u32 << acc_len) - 1)) != 0 {
        return false;
    }
    true
}

pub fn decompress_signature(buf: &[u8], s2: &mut [i16; N]) -> bool {
    let mut acc: u32 = 0;
    let mut acc_len: i32 = 0;
    let mut idx_in = 0usize;
    for u in s2.iter_mut().take(N) {
        if idx_in >= buf.len() {
            return false;
        }
        acc = (acc << 8) | buf[idx_in] as u32;
        idx_in += 1;
        let b = acc >> acc_len;
        let s = b & 128;
        let mut m: u32 = b & 127;
        loop {
            if acc_len == 0 {
                if idx_in >= buf.len() {
                    return false;
                }
                acc = (acc << 8) | buf[idx_in] as u32;
                idx_in += 1;
                acc_len = 8;
            }
            acc_len -= 1;
            if ((acc >> acc_len) & 1) != 0 {
                break;
            }
            m += 128;
            if m >= 2048 {
                return false;
            }
        }
        if s != 0 && m == 0 {
            return false;
        }
        *u = if s != 0 { -(m as i32) as i16 } else { m as i16 };
    }
    if (acc & ((1u32 << acc_len) - 1)) != 0 {
        return false;
    }
    // The compressed encoding may end before the buffer; remaining bytes are
    // zero-padding and must all be zero.
    let mut i = idx_in;
    while i < buf.len() {
        if buf[i] != 0 {
            return false;
        }
        i += 1;
    }
    true
}

pub fn hash_to_point(nonce: &[u8], message: &[u8], c: &mut [u16; N]) {
    let mut s = Shake256::new();
    s.absorb(nonce);
    s.absorb(message);
    s.finalize();

    // SAFETY (cryptographic equivalence with the per-byte squeeze loop):
    //
    // After `finalize`, `s.pos == 0` and a freshly-permuted rate (17 u64 lanes
    // = 136 bytes) is ready to be squeezed. Falcon's `hash_to_point` reads the
    // SHAKE256 output as a stream of bytes and pairs them up big-endian into
    // 16-bit candidates: `w = (byte[2k] << 8) | byte[2k+1]`. With FIPS-202's
    // little-endian-within-lane convention, every (2k, 2k+1) byte pair lives
    // entirely in ONE lane (lane `k/4`, byte offsets `2*(k%4)` and
    // `2*(k%4)+1`) — no candidate ever straddles a lane boundary, since 17
    // lanes × 4 candidates = 68 candidates per rate block.
    //
    // We therefore extract all four candidates per lane in one go and only
    // call `permute()` after exhausting the rate, instead of byte-by-byte
    // shifting + a per-byte rate-boundary check. The rejection sampling
    // (accept iff `w < 5*Q`, then `w % Q`) is byte-for-byte identical to the
    // spec.
    let mut i = 0usize;
    'outer: loop {
        let mut lane_idx = 0;
        while lane_idx < 17 {
            let lane = s.rate_lanes()[lane_idx];
            // Four big-endian u16 candidates packed into this lane.
            let pairs: [u32; 4] = [
                (((lane & 0xff) << 8) | ((lane >> 8) & 0xff)) as u32,
                ((((lane >> 16) & 0xff) << 8) | ((lane >> 24) & 0xff)) as u32,
                ((((lane >> 32) & 0xff) << 8) | ((lane >> 40) & 0xff)) as u32,
                ((((lane >> 48) & 0xff) << 8) | ((lane >> 56) & 0xff)) as u32,
            ];
            let mut k = 0;
            while k < 4 {
                let w = pairs[k];
                if w < 5 * Q {
                    c[i] = (w % Q) as u16;
                    i += 1;
                    if i == N {
                        break 'outer;
                    }
                }
                k += 1;
            }
            lane_idx += 1;
        }
        s.permute();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pubkey_decode_round_trip() {
        // Pack 512 known coefficients (0,1,2,...,511 mod q) and decode.
        let mut packed = [0u8; (N * 14) / 8];
        let mut acc: u32 = 0;
        let mut acc_len: u32 = 0;
        let mut idx = 0;
        for i in 0..N {
            let w = (i as u32) % Q;
            acc = (acc << 14) | w;
            acc_len += 14;
            while acc_len >= 8 {
                acc_len -= 8;
                packed[idx] = (acc >> acc_len) as u8;
                idx += 1;
            }
        }
        if acc_len > 0 {
            packed[idx] = (acc << (8 - acc_len)) as u8;
        }
        let mut h = [0u32; N];
        assert!(decode_pubkey_u32(&packed, &mut h));
        for (i, &coeff) in h.iter().enumerate() {
            assert_eq!(coeff, (i as u32) % Q);
        }
    }
}

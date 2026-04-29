const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

fn keccak_f1600(s: &mut [u64; 25]) {
    // One full Keccak-f round, parameterised on its round constant. We
    // unroll all 24 rounds at the call site below; this saves the
    // per-round counter/branch (~3 ops × 24 ≈ 72 ops per permutation, with
    // ~10 permutations per verify).
    macro_rules! round {
        ($rc:expr) => {{
            // theta — column parities
            let c0 = s[0] ^ s[5] ^ s[10] ^ s[15] ^ s[20];
            let c1 = s[1] ^ s[6] ^ s[11] ^ s[16] ^ s[21];
            let c2 = s[2] ^ s[7] ^ s[12] ^ s[17] ^ s[22];
            let c3 = s[3] ^ s[8] ^ s[13] ^ s[18] ^ s[23];
            let c4 = s[4] ^ s[9] ^ s[14] ^ s[19] ^ s[24];

            let d0 = c4 ^ c1.rotate_left(1);
            let d1 = c0 ^ c2.rotate_left(1);
            let d2 = c1 ^ c3.rotate_left(1);
            let d3 = c2 ^ c4.rotate_left(1);
            let d4 = c3 ^ c0.rotate_left(1);

            // rho + pi merged with theta's xor.
            let b00 = s[0] ^ d0;
            let b01 = (s[6] ^ d1).rotate_left(44);
            let b02 = (s[12] ^ d2).rotate_left(43);
            let b03 = (s[18] ^ d3).rotate_left(21);
            let b04 = (s[24] ^ d4).rotate_left(14);
            let b05 = (s[3] ^ d3).rotate_left(28);
            let b06 = (s[9] ^ d4).rotate_left(20);
            let b07 = (s[10] ^ d0).rotate_left(3);
            let b08 = (s[16] ^ d1).rotate_left(45);
            let b09 = (s[22] ^ d2).rotate_left(61);
            let b10 = (s[1] ^ d1).rotate_left(1);
            let b11 = (s[7] ^ d2).rotate_left(6);
            let b12 = (s[13] ^ d3).rotate_left(25);
            let b13 = (s[19] ^ d4).rotate_left(8);
            let b14 = (s[20] ^ d0).rotate_left(18);
            let b15 = (s[4] ^ d4).rotate_left(27);
            let b16 = (s[5] ^ d0).rotate_left(36);
            let b17 = (s[11] ^ d1).rotate_left(10);
            let b18 = (s[17] ^ d2).rotate_left(15);
            let b19 = (s[23] ^ d3).rotate_left(56);
            let b20 = (s[2] ^ d2).rotate_left(62);
            let b21 = (s[8] ^ d3).rotate_left(55);
            let b22 = (s[14] ^ d4).rotate_left(39);
            let b23 = (s[15] ^ d0).rotate_left(41);
            let b24 = (s[21] ^ d1).rotate_left(2);

            // chi + iota (only lane 0 absorbs the round constant)
            s[0] = b00 ^ ((!b01) & b02) ^ $rc;
            s[1] = b01 ^ ((!b02) & b03);
            s[2] = b02 ^ ((!b03) & b04);
            s[3] = b03 ^ ((!b04) & b00);
            s[4] = b04 ^ ((!b00) & b01);
            s[5] = b05 ^ ((!b06) & b07);
            s[6] = b06 ^ ((!b07) & b08);
            s[7] = b07 ^ ((!b08) & b09);
            s[8] = b08 ^ ((!b09) & b05);
            s[9] = b09 ^ ((!b05) & b06);
            s[10] = b10 ^ ((!b11) & b12);
            s[11] = b11 ^ ((!b12) & b13);
            s[12] = b12 ^ ((!b13) & b14);
            s[13] = b13 ^ ((!b14) & b10);
            s[14] = b14 ^ ((!b10) & b11);
            s[15] = b15 ^ ((!b16) & b17);
            s[16] = b16 ^ ((!b17) & b18);
            s[17] = b17 ^ ((!b18) & b19);
            s[18] = b18 ^ ((!b19) & b15);
            s[19] = b19 ^ ((!b15) & b16);
            s[20] = b20 ^ ((!b21) & b22);
            s[21] = b21 ^ ((!b22) & b23);
            s[22] = b22 ^ ((!b23) & b24);
            s[23] = b23 ^ ((!b24) & b20);
            s[24] = b24 ^ ((!b20) & b21);
        }};
    }

    round!(RC[0]);
    round!(RC[1]);
    round!(RC[2]);
    round!(RC[3]);
    round!(RC[4]);
    round!(RC[5]);
    round!(RC[6]);
    round!(RC[7]);
    round!(RC[8]);
    round!(RC[9]);
    round!(RC[10]);
    round!(RC[11]);
    round!(RC[12]);
    round!(RC[13]);
    round!(RC[14]);
    round!(RC[15]);
    round!(RC[16]);
    round!(RC[17]);
    round!(RC[18]);
    round!(RC[19]);
    round!(RC[20]);
    round!(RC[21]);
    round!(RC[22]);
    round!(RC[23]);
}

const RATE: usize = 136;

pub struct Shake256 {
    state: [u64; 25],
    pos: usize,
}

impl Shake256 {
    pub fn new() -> Self {
        Self {
            state: [0; 25],
            pos: 0,
        }
    }

    pub fn absorb(&mut self, data: &[u8]) {
        let mut i = 0;
        let len = data.len();

        // Phase 1: byte-by-byte until lane-aligned.
        while i < len && !self.pos.is_multiple_of(8) {
            let lane = self.pos / 8;
            let shift = 8 * (self.pos % 8);
            self.state[lane] ^= (data[i] as u64) << shift;
            self.pos += 1;
            if self.pos == RATE {
                keccak_f1600(&mut self.state);
                self.pos = 0;
            }
            i += 1;
        }

        // Phase 2: bulk 8-byte chunks XORed straight into a lane. Bytes within
        // a lane are little-endian per FIPS 202, so `from_le_bytes` is the
        // correct assembly. Each iteration here replaces 8 byte-by-byte
        // iterations of the original loop.
        while i + 8 <= len {
            let chunk = u64::from_le_bytes([
                data[i],
                data[i + 1],
                data[i + 2],
                data[i + 3],
                data[i + 4],
                data[i + 5],
                data[i + 6],
                data[i + 7],
            ]);
            self.state[self.pos / 8] ^= chunk;
            self.pos += 8;
            i += 8;
            if self.pos == RATE {
                keccak_f1600(&mut self.state);
                self.pos = 0;
            }
        }

        // Phase 3: tail bytes (< 8 left).
        while i < len {
            let lane = self.pos / 8;
            let shift = 8 * (self.pos % 8);
            self.state[lane] ^= (data[i] as u64) << shift;
            self.pos += 1;
            if self.pos == RATE {
                keccak_f1600(&mut self.state);
                self.pos = 0;
            }
            i += 1;
        }
    }

    pub fn finalize(&mut self) {
        let lane = self.pos / 8;
        let shift = 8 * (self.pos % 8);
        self.state[lane] ^= 0x1Fu64 << shift;
        let last = RATE - 1;
        self.state[last / 8] ^= 0x80u64 << (8 * (last % 8));
        keccak_f1600(&mut self.state);
        self.pos = 0;
    }

    /// First 17 u64 lanes (= the 136-byte rate). Bytes within each lane are
    /// little-endian per FIPS 202: byte at offset `b` of lane `l` is
    /// `(state[l] >> (8*b)) & 0xff`. Used by the bulk-rate squeeze in
    /// `hash_to_point`.
    pub(crate) fn rate_lanes(&self) -> &[u64] {
        &self.state[..17]
    }

    /// Apply Keccak-f[1600]. Used by callers that drain the rate manually
    /// (i.e. `hash_to_point`) and need a fresh block of squeezable bytes.
    pub(crate) fn permute(&mut self) {
        keccak_f1600(&mut self.state);
    }

    /// Byte-by-byte squeeze. Production uses `rate_lanes()` + `permute()`
    /// directly (see `codec::hash_to_point`) for the bulk-rate path; this
    /// method is only kept for unit tests that exercise the per-byte API.
    #[cfg(test)]
    pub fn squeeze(&mut self, out: &mut [u8]) {
        for byte in out {
            let lane = self.pos / 8;
            let shift = 8 * (self.pos % 8);
            *byte = (self.state[lane] >> shift) as u8;
            self.pos += 1;
            if self.pos == RATE {
                keccak_f1600(&mut self.state);
                self.pos = 0;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shake256_empty() {
        // NIST KAT: SHAKE256("") first 32 bytes
        let expected: [u8; 32] = [
            0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e,
            0xeb, 0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64,
            0x6e, 0xd5, 0x76, 0x2f,
        ];
        let mut s = Shake256::new();
        s.finalize();
        let mut out = [0u8; 32];
        s.squeeze(&mut out);
        assert_eq!(out, expected);
    }

    #[test]
    fn shake256_abc() {
        // SHAKE256("abc") first 32 bytes
        let expected: [u8; 32] = [
            0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77, 0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4,
            0x11, 0x4d, 0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee, 0x4f, 0x94, 0xea, 0x37,
            0xe7, 0x8b, 0x57, 0x39,
        ];
        let mut s = Shake256::new();
        s.absorb(b"abc");
        s.finalize();
        let mut out = [0u8; 32];
        s.squeeze(&mut out);
        assert_eq!(out, expected);
    }

    #[test]
    fn shake256_long_squeeze() {
        // Squeeze across multiple blocks (RATE=136 bytes per permutation).
        let mut s = Shake256::new();
        s.finalize();
        let mut out = [0u8; 200];
        s.squeeze(&mut out);
        // Bytes 136..168 are the start of the second permutation block.
        // Verify by squeezing two halves and comparing.
        let mut s2 = Shake256::new();
        s2.finalize();
        let mut a = [0u8; 100];
        let mut b = [0u8; 100];
        s2.squeeze(&mut a);
        s2.squeeze(&mut b);
        assert_eq!(&out[..100], &a[..]);
        assert_eq!(&out[100..], &b[..]);
    }
}

// Keccak-f[1600] round constants from NIST FIPS 202, §3.2.5.
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

// NIST FIPS 202, §6.2 defines SHAKE with suffix `1111`; after the first
// `pad10*1` bit is included in the byte stream, the little-endian byte suffix
// is `0001_1111` = 0x1f. The final `pad10*1` bit is set in the last rate byte.
const SHAKE256_DOMAIN_SUFFIX: u64 = 0x1f;
const SHAKE256_FINAL_RATE_BIT: u64 = 0x80;

fn keccak_f1600(s: &mut [u64; 25]) {
    // **Bertoni lane-complementing + chi-row** layout.
    //
    // Pre-complement the canonical 6-lane Keccak Team set
    //     CS = {1, 2, 8, 12, 17, 20}
    // chosen so that across one full round (theta+rho+pi+chi+iota), the
    // complementation pattern is invariant. Per-row IN-complemented b's at
    // post-pi positions (derived from theta+rho+pi propagation):
    //     row 0: b0, b2, b3   row 1: b0, b2     row 2: b0, b2
    //     row 3: b1, b3, b4   row 4: b0, b3
    // Per-row OUT-complemented (must store ~A_logical_new):
    //     row 0: x=1, x=2     row 1: x=3        row 2: x=2
    //     row 3: x=2          row 4: x=0
    // Net ~456 NOTs eliminated per 24-round permute, ~12 added at boundaries.

    // Entry: complement the 6 CS lanes once.
    s[1] = !s[1];
    s[2] = !s[2];
    s[8] = !s[8];
    s[12] = !s[12];
    s[17] = !s[17];
    s[20] = !s[20];

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

            // **In-place chi-row + 10 cell-saves**, per PLAN.md item #4.
            // Row 0 outputs to s[0..5]; rows 1..4 read s[3], s[1], s[4], s[2]
            // from this range — save before overwriting.
            let s3 = s[3];
            let s1 = s[1];
            let s4 = s[4];
            let s2 = s[2];

            // Row 0 — IN: b0,b2,b3 complemented; OUT-complement: x=1,2.
            // Iota fused into lane 0.
            {
                let b0 = s[0] ^ d0;
                let b1 = (s[6] ^ d1).rotate_left(44);
                let b2 = (s[12] ^ d2).rotate_left(43);
                let b3 = (s[18] ^ d3).rotate_left(21);
                let b4 = (s[24] ^ d4).rotate_left(14);
                s[0] = b0 ^ (b1 | b2) ^ $rc;
                s[1] = b1 ^ ((!b2) | b3);
                s[2] = b2 ^ (b3 & b4);
                s[3] = b3 ^ (b4 | b0);
                s[4] = b4 ^ (b0 & b1);
            }

            // Row 1 outputs to s[5..10]; rows 2..4 read s[7], s[5], s[8].
            let s7 = s[7];
            let s5 = s[5];
            let s8 = s[8];

            // Row 1 — IN: b0,b2 complemented; OUT-complement: x=3.
            {
                let b0 = (s3 ^ d3).rotate_left(28);
                let b1 = (s[9] ^ d4).rotate_left(20);
                let b2 = (s[10] ^ d0).rotate_left(3);
                let b3 = (s[16] ^ d1).rotate_left(45);
                let b4 = (s[22] ^ d2).rotate_left(61);
                s[5] = b0 ^ (b1 | b2);
                s[6] = b1 ^ (b2 & b3);
                s[7] = (!b2) ^ b4 ^ (b3 & b4);
                s[8] = b3 ^ (b4 | b0);
                s[9] = b4 ^ (b0 & b1);
            }

            // Row 2 outputs to s[10..15]; rows 3..4 read s[11], s[14].
            let s11 = s[11];
            let s14 = s[14];

            // Row 2 — IN: b0,b2 complemented; OUT-complement: x=2.
            {
                let b0 = (s1 ^ d1).rotate_left(1);
                let b1 = (s7 ^ d2).rotate_left(6);
                let b2 = (s[13] ^ d3).rotate_left(25);
                let b3 = (s[19] ^ d4).rotate_left(8);
                let b4 = (s[20] ^ d0).rotate_left(18);
                s[10] = b0 ^ (b1 | b2);
                s[11] = b1 ^ (b2 & b3);
                s[12] = b2 ^ b4 ^ (b3 & b4);
                s[13] = b3 ^ !(b4 | b0);
                s[14] = b4 ^ (b0 & b1);
            }

            // Row 3 outputs to s[15..20]; row 4 reads s[15].
            let s15 = s[15];

            // Row 3 — IN: b1,b3,b4 complemented; OUT-complement: x=2.
            {
                let b0 = (s4 ^ d4).rotate_left(27);
                let b1 = (s5 ^ d0).rotate_left(36);
                let b2 = (s11 ^ d1).rotate_left(10);
                let b3 = (s[17] ^ d2).rotate_left(15);
                let b4 = (s[23] ^ d3).rotate_left(56);
                s[15] = b0 ^ (b1 & b2);
                s[16] = b1 ^ (b2 | b3);
                s[17] = b2 ^ ((!b3) | b4);
                s[18] = (!b3) ^ (b4 & b0);
                s[19] = b4 ^ (b0 | b1);
            }

            // Row 4 — IN: b0,b3 complemented; OUT-complement: x=0.
            {
                let b0 = (s2 ^ d2).rotate_left(62);
                let b1 = (s8 ^ d3).rotate_left(55);
                let b2 = (s14 ^ d4).rotate_left(39);
                let b3 = (s15 ^ d0).rotate_left(41);
                let b4 = (s[21] ^ d1).rotate_left(2);
                s[20] = b0 ^ b2 ^ (b1 & b2);
                s[21] = b1 ^ !(b2 | b3);
                s[22] = b2 ^ (b3 & b4);
                s[23] = b3 ^ (b4 | b0);
                s[24] = b4 ^ (b0 & b1);
            }
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

    // Exit: un-complement the 6 CS lanes so the caller sees the normal
    // (uncomplemented) state. Cost paid once per permute.
    s[1] = !s[1];
    s[2] = !s[2];
    s[8] = !s[8];
    s[12] = !s[12];
    s[17] = !s[17];
    s[20] = !s[20];
}

// NIST FIPS 202, §6.2: SHAKE256 uses capacity 512 bits, so its rate is
// 1600 - 512 = 1088 bits = 136 bytes.
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

    #[inline(always)]
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
        // correct assembly. The `try_into` over an 8-byte sub-slice gives
        // LLVM-SBF a clean shape it can lower to a single (possibly
        // unaligned) `ldxdw` rather than 8 × `ldxb` + shifts + ORs.
        while i + 8 <= len {
            // SAFETY: phase 1 made `self.pos` lane-aligned (multiple of 8),
            // and `pos < RATE = 136 = 17 * 8`, so `pos / 8 < 17 < 25`. Tells
            // LLVM-SBF the lane index is in-bounds without a runtime check.
            unsafe { core::hint::assert_unchecked(self.pos / 8 < 17) };
            let chunk_bytes: [u8; 8] = data[i..i + 8].try_into().unwrap();
            let chunk = u64::from_le_bytes(chunk_bytes);
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

    #[inline(always)]
    pub fn finalize(&mut self) {
        let lane = self.pos / 8;
        let shift = 8 * (self.pos % 8);
        self.state[lane] ^= SHAKE256_DOMAIN_SUFFIX << shift;
        let last = RATE - 1;
        self.state[last / 8] ^= SHAKE256_FINAL_RATE_BIT << (8 * (last % 8));
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

// =========================================================================
// FIPS-202 §3.2 textbook reference. Used as the differential oracle for the
// Bertoni-optimized `keccak_f1600` above (operational tests + Kani symbolic
// equivalence harness). Visible to `tests` and `kani` builds only.
// =========================================================================

#[cfg(any(test, kani))]
fn keccak_lfsr_next_bit(r: &mut u8) -> u64 {
    let bit = (*r & 1) as u64;
    if (*r & 0x80) != 0 {
        *r = (*r << 1) ^ 0x71;
    } else {
        *r <<= 1;
    }
    bit
}

#[cfg(any(test, kani))]
fn rc_if_bit_set(rc: &mut u64, bit: u64, position: usize) {
    if bit != 0 {
        *rc ^= 1u64 << position;
    }
}

/// Derives the Keccak-f[1600] round constants using the FIPS 202 §3.2.5
/// LFSR sequence instead of duplicating the literal table.
#[cfg(any(test, kani))]
pub(crate) fn spec_round_constants() -> [u64; 24] {
    let mut constants = [0u64; 24];
    let mut lfsr = 0x01u8;
    for rc in &mut constants {
        for j in 0..=6 {
            rc_if_bit_set(rc, keccak_lfsr_next_bit(&mut lfsr), (1usize << j) - 1);
        }
    }
    constants
}

/// Textbook Keccak-f[1600] (FIPS-202 §3.2, array form). Differential oracle
/// for the production `keccak_f1600` above.
#[cfg(any(test, kani))]
pub(crate) fn keccak_f1600_ref(s: &mut [u64; 25]) {
    const RHO: [[u32; 5]; 5] = [
        [0, 36, 3, 41, 18],
        [1, 44, 10, 45, 2],
        [62, 6, 43, 15, 61],
        [28, 55, 25, 21, 56],
        [27, 20, 39, 8, 14],
    ];

    let round_constants = spec_round_constants();
    for &rc in &round_constants {
        let mut c = [0u64; 5];
        for x in 0..5 {
            c[x] = s[x] ^ s[x + 5] ^ s[x + 10] ^ s[x + 15] ^ s[x + 20];
        }

        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        }
        for y in 0..5 {
            for x in 0..5 {
                s[x + 5 * y] ^= d[x];
            }
        }

        let mut b = [0u64; 25];
        for y in 0..5 {
            for x in 0..5 {
                let dst_x = y;
                let dst_y = (2 * x + 3 * y) % 5;
                b[dst_x + 5 * dst_y] = s[x + 5 * y].rotate_left(RHO[x][y]);
            }
        }

        for y in 0..5 {
            for x in 0..5 {
                s[x + 5 * y] =
                    b[x + 5 * y] ^ ((!b[((x + 1) % 5) + 5 * y]) & b[((x + 2) % 5) + 5 * y]);
            }
        }

        s[0] ^= rc;
    }
}

/// **Kani symbolic refinement (full f1600)**: the Bertoni-optimized
/// `keccak_f1600` equals the FIPS-202 textbook reference
/// `keccak_f1600_ref` for every 1600-bit input state. Combined with
/// `KeccakOptimized.optimized_eq_canonical` (Lean proof that the
/// *abstract* Bertoni structure equals canonical FIPS Keccak-f[1600]),
/// this closes the Rust ↔ FIPS gap end-to-end: the Lean argument
/// removes the algebra trust, this Kani argument removes the
/// hand-transcription-into-Rust trust.
///
/// This is the heavy harness: 1600-bit symbolic state × 24 rounds bit-
/// blasts to a sizeable SAT instance. Run with `cargo kani --harness
/// keccak_f1600_matches_clean_reference_symbolic`.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(26)]
fn keccak_f1600_matches_clean_reference_symbolic() {
    let s: [u64; 25] = kani::any();
    let mut s_opt = s;
    let mut s_ref = s;
    keccak_f1600(&mut s_opt);
    keccak_f1600_ref(&mut s_ref);
    assert_eq!(s_opt, s_ref);
}

// SMT solver A/B testing — recorded result, no harness retained.
//
// Tested Kani's z3 backend (`#[kani::solver(z3)]`) on both harnesses:
//   * `chi_per_row_formulas_match_canonical` (5 symbolic u64s):
//     cadical 0.78s vs z3 2.0s — cadical ~2.5× faster.
//   * `keccak_f1600_matches_clean_reference_symbolic` (180k VCCs
//     after slicing, 24-round symbolic unroll): z3 backend crashes
//     with `map::at: key not found` during CBMC's SMT2 conversion,
//     before z3 is invoked. CBMC integration bug at this scale,
//     not a z3 capability issue.
//
// Conclusion: cadical is the correct backend here. Pure SAT after
// bit-blasting beats SMT-BV theory for crypto-level bit-vector
// problems, matching the general empirical pattern.

/// **Kani lightweight per-row chi harness.** Verifies that each of the
/// five Bertoni-modified chi rows in `keccak_f1600` (the actual
/// substantive optimization) equals the canonical FIPS chi composed
/// with the row's IN/OUT mask flips. Each row is 5 symbolic u64s and
/// 5 Boolean identities — trivially fast for CBMC. Complements the
/// 9-identity Lean proof in `Falcon512.KeccakOptimized.chi_id_1..9`
/// by checking the same identities at the *u64* / Rust level instead
/// of via `Nat.testBit` reasoning. Uses cadical (default SAT backend).
#[cfg(kani)]
#[kani::proof]
fn chi_per_row_formulas_match_canonical() {
    // 5 symbolic u64 lane values for a single row (post-θ,ρ,π).
    let b0: u64 = kani::any();
    let b1: u64 = kani::any();
    let b2: u64 = kani::any();
    let b3: u64 = kani::any();
    let b4: u64 = kani::any();

    // -------- Row 0: IN=(T,F,T,T,F) → b0,b2,b3 complemented; OUT={1,2} --------
    {
        // Logical (uncomplemented) values:
        let big0 = !b0;  // IN T → stored b0 = !B0, so B0 = !b0
        let big1 = b1;   // IN F
        let big2 = !b2;  // IN T
        let big3 = !b3;  // IN T
        let big4 = b4;   // IN F
        // Canonical chi outputs (logical):
        let c0 = big0 ^ ((!big1) & big2);
        let c1 = big1 ^ ((!big2) & big3);
        let c2 = big2 ^ ((!big3) & big4);
        let c3 = big3 ^ ((!big4) & big0);
        let c4 = big4 ^ ((!big0) & big1);
        // Bertoni-modified formulas from src/keccak.rs Row 0:
        assert_eq!(b0 ^ (b1 | b2), c0);            // OUT[0] = F
        assert_eq!(b1 ^ ((!b2) | b3), !c1);        // OUT[1] = T
        assert_eq!(b2 ^ (b3 & b4), !c2);           // OUT[2] = T
        assert_eq!(b3 ^ (b4 | b0), c3);            // OUT[3] = F
        assert_eq!(b4 ^ (b0 & b1), c4);            // OUT[4] = F
    }

    // -------- Row 1: IN=(T,F,T,F,F) → b0,b2 complemented; OUT={8} (col 3) --
    {
        let big0 = !b0; let big1 = b1; let big2 = !b2;
        let big3 = b3;  let big4 = b4;
        let c0 = big0 ^ ((!big1) & big2);
        let c1 = big1 ^ ((!big2) & big3);
        let c2 = big2 ^ ((!big3) & big4);
        let c3 = big3 ^ ((!big4) & big0);
        let c4 = big4 ^ ((!big0) & big1);
        assert_eq!(b0 ^ (b1 | b2), c0);
        assert_eq!(b1 ^ (b2 & b3), c1);
        assert_eq!((!b2) ^ b4 ^ (b3 & b4), c2);    // SPECIAL: NOT-eliminated form
        assert_eq!(b3 ^ (b4 | b0), !c3);           // OUT[3] = T (CS lane 8)
        assert_eq!(b4 ^ (b0 & b1), c4);
    }

    // -------- Row 2: IN=(T,F,T,F,F); OUT={12} (col 2) --------
    {
        let big0 = !b0; let big1 = b1; let big2 = !b2;
        let big3 = b3;  let big4 = b4;
        let c0 = big0 ^ ((!big1) & big2);
        let c1 = big1 ^ ((!big2) & big3);
        let c2 = big2 ^ ((!big3) & big4);
        let c3 = big3 ^ ((!big4) & big0);
        let c4 = big4 ^ ((!big0) & big1);
        assert_eq!(b0 ^ (b1 | b2), c0);
        assert_eq!(b1 ^ (b2 & b3), c1);
        assert_eq!(b2 ^ b4 ^ (b3 & b4), !c2);      // OUT[2] = T (CS lane 12)
        assert_eq!(b3 ^ !(b4 | b0), c3);
        assert_eq!(b4 ^ (b0 & b1), c4);
    }

    // -------- Row 3: IN=(F,T,F,T,T) → b1,b3,b4 complemented; OUT={17} (col 2) --
    {
        let big0 = b0;  let big1 = !b1; let big2 = b2;
        let big3 = !b3; let big4 = !b4;
        let c0 = big0 ^ ((!big1) & big2);
        let c1 = big1 ^ ((!big2) & big3);
        let c2 = big2 ^ ((!big3) & big4);
        let c3 = big3 ^ ((!big4) & big0);
        let c4 = big4 ^ ((!big0) & big1);
        assert_eq!(b0 ^ (b1 & b2), c0);
        assert_eq!(b1 ^ (b2 | b3), c1);
        assert_eq!(b2 ^ ((!b3) | b4), !c2);        // OUT[2] = T (CS lane 17)
        assert_eq!((!b3) ^ (b4 & b0), c3);
        assert_eq!(b4 ^ (b0 | b1), c4);
    }

    // -------- Row 4: IN=(T,F,F,T,F) → b0,b3 complemented; OUT={20} (col 0) --
    {
        let big0 = !b0; let big1 = b1; let big2 = b2;
        let big3 = !b3; let big4 = b4;
        let c0 = big0 ^ ((!big1) & big2);
        let c1 = big1 ^ ((!big2) & big3);
        let c2 = big2 ^ ((!big3) & big4);
        let c3 = big3 ^ ((!big4) & big0);
        let c4 = big4 ^ ((!big0) & big1);
        assert_eq!(b0 ^ b2 ^ (b1 & b2), !c0);      // OUT[0] = T (CS lane 20)
        assert_eq!(b1 ^ !(b2 | b3), c1);
        assert_eq!(b2 ^ (b3 & b4), c2);
        assert_eq!(b3 ^ (b4 | b0), c3);
        assert_eq!(b4 ^ (b0 & b1), c4);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keccak_constants_match_spec() {
        assert_eq!(RATE, (1600 - 512) / 8, "SHAKE256 rate");
        assert_eq!(RATE, 17 * 8, "SHAKE256 rate lanes");
        assert_eq!(SHAKE256_DOMAIN_SUFFIX, 0x1f, "SHAKE256 domain suffix");
        assert_eq!(
            SHAKE256_FINAL_RATE_BIT, 0x80,
            "multi-rate padding final bit"
        );

        let derived = spec_round_constants();
        assert_eq!(RC, derived, "Keccak-f[1600] round constants");
    }

    #[test]
    fn optimized_keccak_f1600_matches_clean_reference() {
        struct Rng(u64);
        impl Rng {
            fn next(&mut self) -> u64 {
                let mut x = self.0;
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                self.0 = x;
                x
            }
        }

        let mut cases: Vec<[u64; 25]> = vec![[0; 25], [u64::MAX; 25]];
        for lane in 0..25 {
            let mut s = [0u64; 25];
            s[lane] = 1;
            cases.push(s);
            let mut s = [0u64; 25];
            s[lane] = u64::MAX;
            cases.push(s);
        }

        let mut rng = Rng(0x51A0_5EED_1600_0024);
        for _ in 0..512 {
            let mut s = [0u64; 25];
            for lane in &mut s {
                *lane = rng.next();
            }
            cases.push(s);
        }

        for (case, input) in cases.into_iter().enumerate() {
            let mut optimized = input;
            let mut reference = input;
            keccak_f1600(&mut optimized);
            keccak_f1600_ref(&mut reference);
            assert_eq!(
                optimized, reference,
                "case {case}: optimized Keccak-f[1600] diverges from clean reference"
            );
        }
    }

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

    /// Differential test against the RustCrypto `sha3` crate. NIST KATs cover
    /// only three inputs, so a typo in any of Keccak-f1600's 24 round
    /// constants or 25 rotation offsets that happens to leave those three
    /// outputs unchanged would slip through. This compares full-output
    /// (300+ bytes) against `sha3::Shake256` across 10K random inputs of
    /// varying lengths to flush out any such typo.
    #[test]
    fn shake256_matches_sha3_crate() {
        use sha3::digest::{ExtendableOutput, Update, XofReader};

        struct Rng(u64);
        impl Rng {
            fn next(&mut self) -> u64 {
                let mut x = self.0;
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                self.0 = x;
                x
            }
            fn fill(&mut self, buf: &mut [u8]) {
                for slot in buf.iter_mut() {
                    *slot = self.next() as u8;
                }
            }
        }
        let mut rng = Rng(0xDEAD_BEEF_CAFE_F00D);

        for iter in 0..10_000 {
            // Vary input length 0..=400 bytes (spans head, bulk, tail phases
            // and multiple rate boundaries).
            let in_len = (rng.next() % 401) as usize;
            let mut input = vec![0u8; in_len];
            rng.fill(&mut input);

            // Vary output length 0..=300 bytes (spans rate boundary 136).
            let out_len = (rng.next() % 301) as usize;

            let mut ours = Shake256::new();
            ours.absorb(&input);
            ours.finalize();
            let mut our_out = vec![0u8; out_len];
            ours.squeeze(&mut our_out);

            let mut theirs = sha3::Shake256::default();
            theirs.update(&input);
            let mut their_reader = theirs.finalize_xof();
            let mut their_out = vec![0u8; out_len];
            their_reader.read(&mut their_out);

            assert_eq!(
                our_out, their_out,
                "iter {iter}: SHAKE256 diverges from sha3 crate (in_len={in_len}, out_len={out_len})"
            );
        }
    }

    /// Cross-rate-boundary differential: chunked absorbs and chunked
    /// squeezes against the reference. Catches any state-misalignment
    /// bug across rate transitions that the single-shot test above
    /// might mask.
    #[test]
    fn shake256_chunked_matches_sha3_crate() {
        use sha3::digest::{ExtendableOutput, Update, XofReader};

        let mut state = 0xABCD_1234_FEED_FACEu64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };

        for iter in 0..1_000 {
            // Random total input length 0..=500.
            let total = (next() % 501) as usize;
            let mut input = vec![0u8; total];
            for slot in input.iter_mut() {
                *slot = next() as u8;
            }

            // Split into 1..=8 random absorb chunks.
            let n_chunks = ((next() % 8) + 1) as usize;
            let mut splits: Vec<usize> = (0..n_chunks - 1)
                .map(|_| (next() as usize) % (total + 1))
                .collect();
            splits.push(0);
            splits.push(total);
            splits.sort();
            splits.dedup();

            let mut ours = Shake256::new();
            for w in splits.windows(2) {
                ours.absorb(&input[w[0]..w[1]]);
            }
            ours.finalize();

            // Random output 0..=400 bytes, squeezed in 1..=8 chunks.
            let out_total = (next() % 401) as usize;
            let n_out = ((next() % 8) + 1) as usize;
            let mut out_splits: Vec<usize> = (0..n_out - 1)
                .map(|_| (next() as usize) % (out_total + 1))
                .collect();
            out_splits.push(0);
            out_splits.push(out_total);
            out_splits.sort();
            out_splits.dedup();

            let mut our_out = vec![0u8; out_total];
            for w in out_splits.windows(2) {
                ours.squeeze(&mut our_out[w[0]..w[1]]);
            }

            let mut theirs = sha3::Shake256::default();
            theirs.update(&input);
            let mut their_reader = theirs.finalize_xof();
            let mut their_out = vec![0u8; out_total];
            their_reader.read(&mut their_out);

            assert_eq!(
                our_out, their_out,
                "iter {iter}: chunked SHAKE diverges (total_in={total}, total_out={out_total})"
            );
        }
    }

    /// Pins the `rate_lanes()` contract directly: bytes assembled from the
    /// 17 returned lanes (little-endian per FIPS 202) must equal the bytes
    /// produced by the per-byte `squeeze()` path over the same RATE-byte
    /// window. The codec-side `hash_to_point` tests cover this transitively
    /// via rejection sampling, but a direct test fails earlier with a clearer
    /// signal — and protects any future caller of `rate_lanes()` outside
    /// `hash_to_point`. Load-bearing for internal-state-representation
    /// changes (e.g. Bertoni lane complementation): such optimizations are
    /// only correct if `rate_lanes()` reads out the same byte values that
    /// `squeeze()` would.
    #[test]
    fn rate_lanes_matches_squeeze() {
        let inputs: &[&[u8]] = &[
            b"",
            b"abc",
            &[0u8; 100],
            &[0xff; 200],
            &[0x5a; 271], // crosses RATE = 136 absorb boundary
        ];

        for input in inputs {
            let mut via_lanes = Shake256::new();
            via_lanes.absorb(input);
            via_lanes.finalize();

            let mut via_squeeze = Shake256::new();
            via_squeeze.absorb(input);
            via_squeeze.finalize();

            // Three permutation blocks: covers the post-finalize block plus
            // two further re-permutations after manual rate drains.
            for block in 0..3 {
                let lanes = via_lanes.rate_lanes();
                assert_eq!(
                    lanes.len(),
                    17,
                    "rate_lanes must expose 17 lanes (= RATE / 8)"
                );
                let mut from_lanes = [0u8; RATE];
                for (i, lane) in lanes.iter().enumerate() {
                    from_lanes[i * 8..i * 8 + 8].copy_from_slice(&lane.to_le_bytes());
                }
                via_lanes.permute();

                // Squeeze the same RATE-byte window via the byte path. After
                // exactly RATE bytes, `squeeze()` triggers an internal
                // permute and resets pos — so both states stay in lockstep.
                let mut from_squeeze = [0u8; RATE];
                via_squeeze.squeeze(&mut from_squeeze);

                assert_eq!(
                    from_lanes,
                    from_squeeze,
                    "block {block}: rate_lanes() and squeeze() disagree (input_len={})",
                    input.len()
                );
            }
        }
    }
}

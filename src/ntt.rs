use crate::{N, Q};

const fn pow_mod(base: u32, mut exp: u32, m: u32) -> u32 {
    let mut result: u64 = 1;
    let mut b = base as u64;
    let m64 = m as u64;
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result * b) % m64;
        }
        b = (b * b) % m64;
        exp >>= 1;
    }
    result as u32
}

const fn bitrev9(mut x: u32) -> u32 {
    let mut r: u32 = 0;
    let mut i = 0;
    while i < 9 {
        r = (r << 1) | (x & 1);
        x >>= 1;
        i += 1;
    }
    r
}

// Smallest psi in Z_Q with psi^N = -1 mod Q. This implies psi^(2N) = 1 and
// psi^N != 1, so psi has order 2N = 1024 — a primitive 2N-th root of unity, which
// is exactly what the negacyclic NTT for Z_q[x]/(x^N+1) needs.
const fn find_psi() -> u32 {
    let target = Q - 1;
    let mut psi = 2u32;
    while psi < Q {
        if pow_mod(psi, N as u32, Q) == target {
            return psi;
        }
        psi += 1;
    }
    0
}

const PSI: u32 = find_psi();
const PSI_INV: u32 = pow_mod(PSI, Q - 2, Q);
const N_INV: u32 = pow_mod(N as u32, Q - 2, Q);

const ZETAS: [u32; N] = {
    let mut z = [0u32; N];
    let mut k = 0;
    while k < N {
        z[k] = pow_mod(PSI, bitrev9(k as u32), Q);
        k += 1;
    }
    z
};

const INV_ZETAS: [u32; N] = {
    let mut z = [0u32; N];
    let mut k = 0;
    while k < N {
        z[k] = pow_mod(PSI_INV, bitrev9(k as u32), Q);
        k += 1;
    }
    z
};

// CT (Cooley–Tukey) butterfly used by the forward NTT. Reads `r[j]` and
// `r[j+len]`, multiplies the upper half by `zeta`, and writes the (a+b, a-b)
// pair back. Macro so we can unroll inner/outer loops cheaply without losing
// the const-fn-ability.
macro_rules! ct_butterfly {
    ($r:ident, $j:expr, $len:expr, $zeta:expr) => {{
        let t = (($r[$j + $len] as u64) * $zeta % Q as u64) as u32;
        let u = $r[$j];
        $r[$j] = if u + t >= Q { u + t - Q } else { u + t };
        $r[$j + $len] = if u >= t { u - t } else { u + Q - t };
    }};
}

// GS (Gentleman–Sande) butterfly used by the inverse NTT.
macro_rules! gs_butterfly {
    ($r:ident, $j:expr, $len:expr, $zeta:expr) => {{
        let u = $r[$j];
        let v = $r[$j + $len];
        $r[$j] = if u + v >= Q { u + v - Q } else { u + v };
        let diff = if u >= v { u - v } else { u + Q - v };
        $r[$j + $len] = (diff as u64 * $zeta % Q as u64) as u32;
    }};
}

// Forward NTT levels with len = N/4 down to len = 2 (everything except the
// first len=N/2 level and the final len=1 level). The first level is
// handled separately so it can either operate in-place (`ntt_main_levels`)
// or fuse the s2 sign-fix conversion (`ntt_main_levels_from_signed`).
const fn ntt_levels_after_first(r: &mut [u32; N]) {
    let mut k: usize = 2;

    // Levels with len = N/4, N/8, ..., 16: inner butterfly loop unrolled by 8.
    let mut len = N / 4;
    while len >= 16 {
        let mut start = 0;
        while start < N {
            let zeta = ZETAS[k] as u64;
            k += 1;
            let mut j = start;
            let end = start + len;
            while j < end {
                ct_butterfly!(r, j, len, zeta);
                ct_butterfly!(r, j + 1, len, zeta);
                ct_butterfly!(r, j + 2, len, zeta);
                ct_butterfly!(r, j + 3, len, zeta);
                ct_butterfly!(r, j + 4, len, zeta);
                ct_butterfly!(r, j + 5, len, zeta);
                ct_butterfly!(r, j + 6, len, zeta);
                ct_butterfly!(r, j + 7, len, zeta);
                j += 8;
            }
            start += 2 * len;
        }
        len /= 2;
    }

    // Level len=8: 32 outer iters, 8 inline butterflies each.
    {
        let mut start = 0;
        while start < N {
            let zeta = ZETAS[k] as u64;
            k += 1;
            ct_butterfly!(r, start, 8, zeta);
            ct_butterfly!(r, start + 1, 8, zeta);
            ct_butterfly!(r, start + 2, 8, zeta);
            ct_butterfly!(r, start + 3, 8, zeta);
            ct_butterfly!(r, start + 4, 8, zeta);
            ct_butterfly!(r, start + 5, 8, zeta);
            ct_butterfly!(r, start + 6, 8, zeta);
            ct_butterfly!(r, start + 7, 8, zeta);
            start += 16;
        }
    }

    // Level len=4: 64 outer iters, 4 inline butterflies each.
    {
        let mut start = 0;
        while start < N {
            let zeta = ZETAS[k] as u64;
            k += 1;
            ct_butterfly!(r, start, 4, zeta);
            ct_butterfly!(r, start + 1, 4, zeta);
            ct_butterfly!(r, start + 2, 4, zeta);
            ct_butterfly!(r, start + 3, 4, zeta);
            start += 8;
        }
    }

    // Level len=2: 128 outer iters, 2 butterflies each. Outer-unroll by 2.
    {
        let mut start = 0;
        while start < N {
            let zeta_a = ZETAS[k] as u64;
            let zeta_b = ZETAS[k + 1] as u64;
            ct_butterfly!(r, start, 2, zeta_a);
            ct_butterfly!(r, start + 1, 2, zeta_a);
            ct_butterfly!(r, start + 4, 2, zeta_b);
            ct_butterfly!(r, start + 5, 2, zeta_b);
            k += 2;
            start += 8;
        }
    }
}

// Forward NTT levels with len = N/2 down to len = 2. In-place variant.
pub const fn ntt_main_levels(r: &mut [u32; N]) {
    // Level len=N/2 (k=1, single zeta). 256 butterflies, inner unroll by 8.
    {
        let zeta = ZETAS[1] as u64;
        let mut j = 0;
        while j < N / 2 {
            ct_butterfly!(r, j, N / 2, zeta);
            ct_butterfly!(r, j + 1, N / 2, zeta);
            ct_butterfly!(r, j + 2, N / 2, zeta);
            ct_butterfly!(r, j + 3, N / 2, zeta);
            ct_butterfly!(r, j + 4, N / 2, zeta);
            ct_butterfly!(r, j + 5, N / 2, zeta);
            ct_butterfly!(r, j + 6, N / 2, zeta);
            ct_butterfly!(r, j + 7, N / 2, zeta);
            j += 8;
        }
    }
    ntt_levels_after_first(r);
}

// Forward NTT, but the first level reads from `s2` (signed `i16` in
// [-2047, 2047]) directly, applying the centered → canonical-mod-q
// sign-fix (`v < 0 ? v + q : v`) on the fly. Eliminates the separate
// sign-fix pass over s2_ntt that would otherwise precede the NTT.
//
// Output `r` is fully written by the first level (every j ∈ 0..N/2 writes
// both r[j] and r[j+N/2]) — caller does NOT need to pre-zero `r`.
pub fn ntt_main_levels_from_signed(r: &mut [u32; N], s2: &[i16; N]) {
    let q_i32 = Q as i32;
    let zeta = ZETAS[1] as u64;
    let mut j = 0;
    while j < N / 2 {
        macro_rules! sgn_ct_bf {
            ($jj:expr) => {{
                let v_lo = s2[$jj] as i32;
                let v_hi = s2[$jj + N / 2] as i32;
                let r_lo = if v_lo < 0 {
                    (q_i32 + v_lo) as u32
                } else {
                    v_lo as u32
                };
                let r_hi = if v_hi < 0 {
                    (q_i32 + v_hi) as u32
                } else {
                    v_hi as u32
                };
                let t = ((r_hi as u64) * zeta % Q as u64) as u32;
                r[$jj] = if r_lo + t >= Q {
                    r_lo + t - Q
                } else {
                    r_lo + t
                };
                r[$jj + N / 2] = if r_lo >= t { r_lo - t } else { r_lo + Q - t };
            }};
        }
        sgn_ct_bf!(j);
        sgn_ct_bf!(j + 1);
        sgn_ct_bf!(j + 2);
        sgn_ct_bf!(j + 3);
        sgn_ct_bf!(j + 4);
        sgn_ct_bf!(j + 5);
        sgn_ct_bf!(j + 6);
        sgn_ct_bf!(j + 7);
        j += 8;
    }
    ntt_levels_after_first(r);
}

// Forward NTT level len=1, the final stage. Reads ZETAS starting at index N/2.
const fn ntt_last_level(r: &mut [u32; N]) {
    let mut k: usize = N / 2;
    let mut start = 0;
    while start < N {
        let zeta_a = ZETAS[k] as u64;
        let zeta_b = ZETAS[k + 1] as u64;
        let zeta_c = ZETAS[k + 2] as u64;
        let zeta_d = ZETAS[k + 3] as u64;
        ct_butterfly!(r, start, 1, zeta_a);
        ct_butterfly!(r, start + 2, 1, zeta_b);
        ct_butterfly!(r, start + 4, 1, zeta_c);
        ct_butterfly!(r, start + 6, 1, zeta_d);
        k += 4;
        start += 8;
    }
}

pub const fn ntt(r: &mut [u32; N]) {
    ntt_main_levels(r);
    ntt_last_level(r);
}

// Inverse NTT first level (len=1). Reads INV_ZETAS starting at index N/2.
// Only used by the standalone `inv_ntt` (test-only); production uses
// `fused_last_fwd_mul_first_inv` which folds this level with the pointwise
// multiply.
#[cfg(test)]
const fn inv_ntt_first_level(r: &mut [u32; N]) {
    let mut i = 0;
    while i < N / 2 {
        let zeta_a = INV_ZETAS[N / 2 + i] as u64;
        let zeta_b = INV_ZETAS[N / 2 + i + 1] as u64;
        let zeta_c = INV_ZETAS[N / 2 + i + 2] as u64;
        let zeta_d = INV_ZETAS[N / 2 + i + 3] as u64;
        let s = 2 * i;
        gs_butterfly!(r, s, 1, zeta_a);
        gs_butterfly!(r, s + 2, 1, zeta_b);
        gs_butterfly!(r, s + 4, 1, zeta_c);
        gs_butterfly!(r, s + 6, 1, zeta_d);
        i += 4;
    }
}

// Inverse NTT levels with len = 2 up to len = N/2, plus the final 1/N
// scaling. Used both as the back half of `inv_ntt()` and standalone after
// the fused last-fwd / pointwise / first-inv path has produced the buffer
// already in post-len=1 state.
pub const fn inv_ntt_main_levels(r: &mut [u32; N]) {
    // Level len=2: 128 outer iters, 2 butterflies each. Outer-unroll by 2.
    {
        let mut i = 0;
        while i < N / 4 {
            let zeta_a = INV_ZETAS[N / 4 + i] as u64;
            let zeta_b = INV_ZETAS[N / 4 + i + 1] as u64;
            let s = 4 * i;
            gs_butterfly!(r, s, 2, zeta_a);
            gs_butterfly!(r, s + 1, 2, zeta_a);
            gs_butterfly!(r, s + 4, 2, zeta_b);
            gs_butterfly!(r, s + 5, 2, zeta_b);
            i += 2;
        }
    }

    // Level len=4: 64 outer iters, 4 inline butterflies each (no inner loop).
    {
        let mut i = 0;
        while i < N / 8 {
            let k = N / 8 + i;
            let start = 8 * i;
            let zeta = INV_ZETAS[k] as u64;
            gs_butterfly!(r, start, 4, zeta);
            gs_butterfly!(r, start + 1, 4, zeta);
            gs_butterfly!(r, start + 2, 4, zeta);
            gs_butterfly!(r, start + 3, 4, zeta);
            i += 1;
        }
    }

    // Level len=8: 32 outer iters, 8 inline butterflies each.
    {
        let mut i = 0;
        while i < N / 16 {
            let k = N / 16 + i;
            let start = 16 * i;
            let zeta = INV_ZETAS[k] as u64;
            gs_butterfly!(r, start, 8, zeta);
            gs_butterfly!(r, start + 1, 8, zeta);
            gs_butterfly!(r, start + 2, 8, zeta);
            gs_butterfly!(r, start + 3, 8, zeta);
            gs_butterfly!(r, start + 4, 8, zeta);
            gs_butterfly!(r, start + 5, 8, zeta);
            gs_butterfly!(r, start + 6, 8, zeta);
            gs_butterfly!(r, start + 7, 8, zeta);
            i += 1;
        }
    }

    // Levels with len >= 16: inner unrolled by 8.
    let mut len = 16;
    while len < N {
        let butts = N / (2 * len);
        let k_base = butts;
        let mut i = 0;
        while i < butts {
            let k = k_base + i;
            let start = 2 * i * len;
            let zeta = INV_ZETAS[k] as u64;
            let mut j = start;
            let end = start + len;
            while j < end {
                gs_butterfly!(r, j, len, zeta);
                gs_butterfly!(r, j + 1, len, zeta);
                gs_butterfly!(r, j + 2, len, zeta);
                gs_butterfly!(r, j + 3, len, zeta);
                gs_butterfly!(r, j + 4, len, zeta);
                gs_butterfly!(r, j + 5, len, zeta);
                gs_butterfly!(r, j + 6, len, zeta);
                gs_butterfly!(r, j + 7, len, zeta);
                j += 8;
            }
            i += 1;
        }
        len *= 2;
    }

    // Final scale by N_INV: unrolled by 8.
    let n_inv = N_INV as u64;
    let mut i = 0;
    while i < N {
        r[i] = (r[i] as u64 * n_inv % Q as u64) as u32;
        r[i + 1] = (r[i + 1] as u64 * n_inv % Q as u64) as u32;
        r[i + 2] = (r[i + 2] as u64 * n_inv % Q as u64) as u32;
        r[i + 3] = (r[i + 3] as u64 * n_inv % Q as u64) as u32;
        r[i + 4] = (r[i + 4] as u64 * n_inv % Q as u64) as u32;
        r[i + 5] = (r[i + 5] as u64 * n_inv % Q as u64) as u32;
        r[i + 6] = (r[i + 6] as u64 * n_inv % Q as u64) as u32;
        r[i + 7] = (r[i + 7] as u64 * n_inv % Q as u64) as u32;
        i += 8;
    }
}

// Standalone full inverse NTT, only used by unit tests (round-trip and
// schoolbook-multiplication checks). Production calls
// `fused_last_fwd_mul_first_inv` followed by `inv_ntt_main_levels`.
#[cfg(test)]
pub const fn inv_ntt(r: &mut [u32; N]) {
    inv_ntt_first_level(r);
    inv_ntt_main_levels(r);
}

/// Fused: forward-NTT last level + pointwise multiply by prepared pubkey +
/// inverse-NTT first level, all in one pass over 256 pairs — operating
/// **in place** on a single buffer that holds s2 in NTT-main-levels form
/// on input and the post-first-INV product on output.
///
/// `h_pk_ntt` is the prepared pubkey in full NTT form (output of
/// `Falcon512Pubkey::prepare_pubkey`). `buf` is the working buffer.
///
/// Math per pair `i ∈ 0..256`, for `pair = 2*i`:
///   z      = ZETAS[N/2 + i]
///   z_inv  = INV_ZETAS[N/2 + i]
///   t      = buf[pair+1] * z              mod q   (last fwd CT butterfly)
///   s_low  = buf[pair]  + t               mod q
///   s_high = buf[pair]  - t               mod q
///   p_low  = h_pk_ntt[pair]   * s_low     mod q   (pointwise mul)
///   p_high = h_pk_ntt[pair+1] * s_high    mod q
///   buf[pair]   = p_low + p_high          mod q   (first inv GS butterfly)
///   buf[pair+1] = (p_low - p_high) * z_inv mod q
///
/// SAFETY (in-place aliasing): each iteration reads `buf[pair]` and
/// `buf[pair+1]` into registers (`prev_low`, `prev_high`) *before* any
/// write back, and only writes those same two indices — no other
/// iteration touches them. So reading and writing through one buffer is
/// equivalent to a separate-input/output formulation.
pub fn fused_last_fwd_mul_first_inv(buf: &mut [u32; N], h_pk_ntt: &[u32; N]) {
    macro_rules! step {
        ($i:expr) => {{
            let pair = 2 * $i;
            let z = ZETAS[N / 2 + $i] as u64;
            let z_inv = INV_ZETAS[N / 2 + $i] as u64;

            // Snapshot s2_ntt's values at this pair *before* any write, so
            // the buffer can safely back both the input (s2) and output
            // (prod) roles.
            let prev_low = buf[pair];
            let prev_high = buf[pair + 1];

            // Forward last level CT butterfly (in registers).
            let t = ((prev_high as u64) * z % Q as u64) as u32;
            let s_low = if prev_low + t >= Q {
                prev_low + t - Q
            } else {
                prev_low + t
            };
            let s_high = if prev_low >= t {
                prev_low - t
            } else {
                prev_low + Q - t
            };

            // Pointwise multiplication with prepared pubkey.
            let p_low = (h_pk_ntt[pair] as u64 * s_low as u64 % Q as u64) as u32;
            let p_high = (h_pk_ntt[pair + 1] as u64 * s_high as u64 % Q as u64) as u32;

            // Inverse first level GS butterfly back into the same pair.
            let new_low = if p_low + p_high >= Q {
                p_low + p_high - Q
            } else {
                p_low + p_high
            };
            let diff = if p_low >= p_high {
                p_low - p_high
            } else {
                p_low + Q - p_high
            };
            let new_high = (diff as u64 * z_inv % Q as u64) as u32;

            buf[pair] = new_low;
            buf[pair + 1] = new_high;
        }};
    }

    let mut i = 0;
    while i < N / 2 {
        step!(i);
        step!(i + 1);
        step!(i + 2);
        step!(i + 3);
        i += 4;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ntt_round_trip() {
        let mut a = [0u32; N];
        for (i, slot) in a.iter_mut().enumerate() {
            *slot = ((i * 17 + 3) as u32) % Q;
        }
        let original = a;
        ntt(&mut a);
        inv_ntt(&mut a);
        assert_eq!(a, original);
    }

    #[test]
    fn ntt_multiplication_matches_schoolbook() {
        // Random-ish polynomials a, b in Z_q. Compute a*b via NTT and via schoolbook
        // negacyclic mul; results must match.
        let mut a = [0u32; N];
        let mut b = [0u32; N];
        for i in 0..N {
            a[i] = ((i * 31 + 7) as u32) % Q;
            b[i] = ((i * 19 + 11) as u32) % Q;
        }

        // Schoolbook negacyclic
        let mut c_school = [0i64; N];
        #[allow(clippy::needless_range_loop)] // index used into both `a` and `b` simultaneously
        for i in 0..N {
            for j in 0..N {
                let prod = (a[i] as i64) * (b[j] as i64);
                let k = i + j;
                if k < N {
                    c_school[k] += prod;
                } else {
                    c_school[k - N] -= prod;
                }
            }
        }
        let mut c_school_q = [0u32; N];
        for i in 0..N {
            let v = c_school[i].rem_euclid(Q as i64) as u32;
            c_school_q[i] = v;
        }

        let mut a_ntt = a;
        let mut b_ntt = b;
        ntt(&mut a_ntt);
        ntt(&mut b_ntt);
        let mut prod = [0u32; N];
        for i in 0..N {
            prod[i] = (a_ntt[i] as u64 * b_ntt[i] as u64 % Q as u64) as u32;
        }
        inv_ntt(&mut prod);

        assert_eq!(prod, c_school_q);
    }
}

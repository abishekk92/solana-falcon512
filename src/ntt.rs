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
pub(crate) const N_INV: u32 = pow_mod(N as u32, Q - 2, Q);

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
//
// All arithmetic is in u64 (operands are < Q < 2^14, sums fit easily). SBF
// has no native u32 arithmetic — keeping intermediates as u64 avoids the
// `lsh 0x20 ; rsh 0x20` truncation pair LLVM-SBF emits when comparing u32
// values for the `>= Q` reduction. The reductions use explicit `% q`: SBF's
// `mod64` is 1 CU, beating the 5-instruction `if s >= q { s - q } else { s }`
// branchless pattern LLVM otherwise emits.
//
// **Lazy reduction**: only the high-half multiplication is reduced. The low
// half (`u + t`) and the additive half (`u + q - t`) are stored unreduced.
// After K levels of unreduced sums the value is bounded by (K+1)·Q which fits
// in u32 for the 9 forward levels (max 10·Q ≈ 130k). The next level's
// `value * zeta % q` cleanly absorbs the un-reduction since mod is
// distributive (`(a*b) mod q = ((a mod q) * b) mod q`). Saves 2 mods per
// butterfly across hundreds of butterflies.
macro_rules! ct_butterfly {
    ($r:ident, $j:expr, $len:expr, $zeta:expr) => {{
        let q = Q as u64;
        let t = ($r[$j + $len] as u64) * $zeta % q;
        let u = $r[$j] as u64;
        $r[$j] = (u + t) as u32;
        $r[$j + $len] = (u + q - t) as u32;
    }};
}

// CT butterfly that *also* skips the `t = ... % q` reduction. Only safe at
// the very last forward NTT level (len=2) — the next consumer is the fused
// step which does `α·a + β·b mod q` and absorbs any un-reduction. After 7
// prior lazy levels (sgn_ct_bf → ntt_levels_after_first up to len=4), inputs
// are bounded by 8·Q, so `t = b·zeta` is bounded by 8·Q² ≈ 1.21·10⁹ — fits
// u32. The high-half subtract uses `8·Q²` as the offset (a multiple of Q so
// `% Q` is unchanged) to keep `u + offset - t` non-negative.
macro_rules! ct_butterfly_lazy_t {
    ($r:ident, $j:expr, $len:expr, $zeta:expr) => {{
        // 8 · Q · Q = 8 · 12289² = 1,208,605,448 — multiple of Q, fits 32-bit imm.
        const T_OFFSET: u64 = 8 * (Q as u64) * (Q as u64);
        let t = ($r[$j + $len] as u64) * $zeta;
        let u = $r[$j] as u64;
        $r[$j] = (u + t) as u32;
        $r[$j + $len] = (u + T_OFFSET - t) as u32;
    }};
}

// GS (Gentleman–Sande) butterfly used by the inverse NTT. CANNOT be lazy
// like `ct_butterfly`: the diff half is `u + q - v`, where `v` is *also*
// an input from storage — if previous levels stored an unreduced `v ≥ q`
// then `u + q - v` underflows in u64 and the subsequent `% q` returns
// garbage. (Forward CT is safe because `t = r * zeta % q` is always
// reduced before the subtract.) So this stays fully reducing.
//
// Production uses `gs_butterfly_lazy` exclusively — this strict variant is
// only invoked from the test-only `inv_ntt_first_level`, hence the
// `unused_macros` allow.
#[allow(unused_macros)]
macro_rules! gs_butterfly {
    ($r:ident, $j:expr, $len:expr, $zeta:expr) => {{
        let q = Q as u64;
        let u = $r[$j] as u64;
        let v = $r[$j + $len] as u64;
        $r[$j] = ((u + v) % q) as u32;
        $r[$j + $len] = ((u + q - v) * $zeta % q) as u32;
    }};
}

// Lazy GS butterfly that skips the low-half `% q` reduction. Safe for
// inv-NTT levels where the next level will mod-reduce again via the high
// half's `* zeta % q` (which absorbs un-reduction).
//
// To stop `u + q - v` from underflowing when previous levels stored
// unreduced lows (up to 256·Q in the worst case — fused-step output is
// 2·Q lazy, levels 1..7 then double per pass), the constant added is
// `LAZY_OFFSET = 256·Q` instead of plain `q`. Both are multiples of `q`,
// so `% q` of the result is identical; the bigger offset is simply enough
// to keep the subtract non-negative for any `v` we'll see.
//
// Each butterfly saves 1 `mod64` (the low-half `% q`) over the strict
// variant — ~1.8k CU across 7 levels × 256 butterflies on the inverse path.
macro_rules! gs_butterfly_lazy {
    ($r:ident, $j:expr, $len:expr, $zeta:expr) => {{
        let q = Q as u64;
        let lazy_offset = q * 256;
        let u = $r[$j] as u64;
        let v = $r[$j + $len] as u64;
        $r[$j] = (u + v) as u32;
        $r[$j + $len] = ((u + lazy_offset - v) * $zeta % q) as u32;
    }};
}

// Forward NTT levels with len = N/4 down to len = 2 (everything except the
// first len=N/2 level and the final len=1 level). The first level is
// handled separately so it can either operate in-place (`ntt_main_levels`)
// or fuse the s2 sign-fix conversion (`ntt_main_levels_from_signed`).
//
// `assert_unchecked` calls communicate loop invariants (e.g. `start + 2*len
// <= N`) that LLVM-SBF can't otherwise prove. Without them the backend emits
// a per-butterfly `jge r, 0x200, <fail>` bounds check and 3-instruction
// recompute of the high-half base address — visible in the unrolled hot
// loop and worth hundreds of CUs across the full NTT.
#[inline(always)]
pub(crate) const fn ntt_levels_after_first(r: &mut [u32; N]) {
    let mut k: usize = 2;

    // Levels with len = N/4, N/8, ..., 16: inner butterfly loop unrolled by 8.
    let mut len = N / 4;
    while len >= 16 {
        let mut start = 0;
        while start < N {
            // SAFETY: start + 2*len <= N. start steps by 2*len starting at 0,
            // and 2*len divides N, so start ≤ N - 2*len exactly.
            unsafe { core::hint::assert_unchecked(start + 2 * len <= N) };
            let zeta = ZETAS[k] as u64;
            k += 1;
            let mut j = start;
            let end = start + len;
            while j < end {
                // SAFETY: j ranges over [start, start+len), unrolled by 8, so
                // j + 7 + len <= start + 2*len ≤ N — every access stays in.
                unsafe { core::hint::assert_unchecked(j + 7 + len < N) };
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
            unsafe { core::hint::assert_unchecked(start + 16 <= N) };
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
            unsafe { core::hint::assert_unchecked(start + 8 <= N) };
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
    // This is the *last* main forward level, so we use the lazy-t variant
    // that skips `t = ... % q`. The downstream consumer (fused step
    // `α·a + β·b mod q` for runtime, or `ntt_last_level` for the const
    // path) absorbs any un-reduction since the multiplications fit u64.
    // Saves one `mod64` per butterfly × 256 butterflies ≈ 256 CU.
    {
        let mut start = 0;
        while start < N {
            unsafe { core::hint::assert_unchecked(start + 8 <= N) };
            let zeta_a = ZETAS[k] as u64;
            let zeta_b = ZETAS[k + 1] as u64;
            ct_butterfly_lazy_t!(r, start, 2, zeta_a);
            ct_butterfly_lazy_t!(r, start + 1, 2, zeta_a);
            ct_butterfly_lazy_t!(r, start + 4, 2, zeta_b);
            ct_butterfly_lazy_t!(r, start + 5, 2, zeta_b);
            k += 2;
            start += 8;
        }
    }
}

// Forward NTT levels with len = N/2 down to len = 2. In-place variant.
// Used only by `ntt()` (const-fn / `prepare_pubkey`) — runtime uses
// `ntt_main_levels_from_signed`. Lazy-reduce is fine here because `ntt()`
// applies a final canonicalising reduction pass.
pub const fn ntt_main_levels(r: &mut [u32; N]) {
    // Level len=N/2 (k=1, single zeta). 256 butterflies, inner unroll by 8.
    {
        let zeta = ZETAS[1] as u64;
        let mut j = 0;
        while j < N / 2 {
            unsafe { core::hint::assert_unchecked(j + 7 + N / 2 < N) };
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
    let q = Q as u64;
    let zeta = ZETAS[1] as u64;
    let mut j = 0;
    while j < N / 2 {
        unsafe { core::hint::assert_unchecked(j + 7 + N / 2 < N) };
        macro_rules! sgn_ct_bf {
            ($jj:expr) => {{
                // Sign-fix WITHOUT a `% q` reduction. `s2[i] as i64 as u64`
                // sign-extends i16 → i64 then takes the bit pattern as u64;
                // adding `q` lands the value at `q + s2[i]` for positive s2
                // (∈ [q, q+2047]) and wraps to `q - |s2[i]|` for negative
                // (∈ [q-2047, q]). Either way `r_lo` ≡ `s2[i] mod q` and is
                // bounded by `q + 2047 < 2·q`. The lazy CT outputs `r_lo + t`
                // and `r_lo + q - t` are then ≤ 3·q each, well within u32,
                // and the next level's mul·zeta·% q absorbs un-reduction.
                // Saves the per-butterfly sign-fix mod (~512 mods total).
                let r_lo = (s2[$jj] as i64 as u64).wrapping_add(q);
                let r_hi = (s2[$jj + N / 2] as i64 as u64).wrapping_add(q);
                let t = r_hi * zeta % q;
                r[$jj] = (r_lo + t) as u32;
                r[$jj + N / 2] = (r_lo + q - t) as u32;
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
        unsafe { core::hint::assert_unchecked(start + 8 <= N) };
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
    // Final reduction. The lazy-reduce butterflies leave each element bounded
    // by ~10·Q which fits in u32 fine for runtime use, but `ntt()` is the
    // const-fn entry point used by `prepare_pubkey`, and a serialized
    // prepared pubkey should be canonical (every element in [0, Q)).
    let q = Q as u64;
    let mut k = 0;
    while k < N {
        r[k] = (r[k] as u64 % q) as u32;
        k += 1;
    }
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
    // All non-last levels use the *lazy* GS variant: low-half `(u + v)` is
    // stored without `% q`. The high half's `* zeta % q` keeps it reduced,
    // and the next level's high-half `* zeta % q` (or, after level 7, the
    // last-level fused-norm path) absorbs any un-reduction. Per-level
    // values double; level 7's worst-case is ~128·Q which still fits u32,
    // and the lazy macro adds 128·Q (a multiple of q) before the subtract
    // to prevent underflow with that worst-case `v`.

    // Level len=2: 128 outer iters, 2 butterflies each. Outer-unroll by 2.
    {
        let mut i = 0;
        while i < N / 4 {
            let s = 4 * i;
            unsafe { core::hint::assert_unchecked(s + 8 <= N) };
            let zeta_a = INV_ZETAS[N / 4 + i] as u64;
            let zeta_b = INV_ZETAS[N / 4 + i + 1] as u64;
            gs_butterfly_lazy!(r, s, 2, zeta_a);
            gs_butterfly_lazy!(r, s + 1, 2, zeta_a);
            gs_butterfly_lazy!(r, s + 4, 2, zeta_b);
            gs_butterfly_lazy!(r, s + 5, 2, zeta_b);
            i += 2;
        }
    }

    // Level len=4: 64 outer iters, 4 inline butterflies each (no inner loop).
    {
        let mut i = 0;
        while i < N / 8 {
            let k = N / 8 + i;
            let start = 8 * i;
            unsafe { core::hint::assert_unchecked(start + 8 <= N) };
            let zeta = INV_ZETAS[k] as u64;
            gs_butterfly_lazy!(r, start, 4, zeta);
            gs_butterfly_lazy!(r, start + 1, 4, zeta);
            gs_butterfly_lazy!(r, start + 2, 4, zeta);
            gs_butterfly_lazy!(r, start + 3, 4, zeta);
            i += 1;
        }
    }

    // Level len=8: 32 outer iters, 8 inline butterflies each.
    {
        let mut i = 0;
        while i < N / 16 {
            let k = N / 16 + i;
            let start = 16 * i;
            unsafe { core::hint::assert_unchecked(start + 16 <= N) };
            let zeta = INV_ZETAS[k] as u64;
            gs_butterfly_lazy!(r, start, 8, zeta);
            gs_butterfly_lazy!(r, start + 1, 8, zeta);
            gs_butterfly_lazy!(r, start + 2, 8, zeta);
            gs_butterfly_lazy!(r, start + 3, 8, zeta);
            gs_butterfly_lazy!(r, start + 4, 8, zeta);
            gs_butterfly_lazy!(r, start + 5, 8, zeta);
            gs_butterfly_lazy!(r, start + 6, 8, zeta);
            gs_butterfly_lazy!(r, start + 7, 8, zeta);
            i += 1;
        }
    }

    // Levels with 16 <= len < N/2: inner unrolled by 8. The N_INV scaling that
    // an inverse NTT normally needs at the end is pre-folded into the
    // prepared pubkey at compile time (see `Falcon512Pubkey::prepare_pubkey`),
    // so the back half of `inv_NTT(fwd_NTT(s2) * h_pk_NTT)` produces the
    // correct (un-scaled) coefficients directly.
    //
    // The final level (len = N/2) is intentionally *omitted* here: production
    // does it inside `last_level_fused_norm` below, fused with the L2-norm
    // accumulation, so the 512-element pass writing buf and the 512-element
    // pass reading buf back collapse into one. The standalone test path
    // (`inv_ntt`) calls `last_level` separately.
    let mut len = 16;
    while len < N / 2 {
        let butts = N / (2 * len);
        let k_base = butts;
        let mut i = 0;
        while i < butts {
            let k = k_base + i;
            let start = 2 * i * len;
            unsafe { core::hint::assert_unchecked(start + 2 * len <= N) };
            let zeta = INV_ZETAS[k] as u64;
            let mut j = start;
            let end = start + len;
            while j < end {
                unsafe { core::hint::assert_unchecked(j + 7 + len < N) };
                gs_butterfly_lazy!(r, j, len, zeta);
                gs_butterfly_lazy!(r, j + 1, len, zeta);
                gs_butterfly_lazy!(r, j + 2, len, zeta);
                gs_butterfly_lazy!(r, j + 3, len, zeta);
                gs_butterfly_lazy!(r, j + 4, len, zeta);
                gs_butterfly_lazy!(r, j + 5, len, zeta);
                gs_butterfly_lazy!(r, j + 6, len, zeta);
                gs_butterfly_lazy!(r, j + 7, len, zeta);
                j += 8;
            }
            i += 1;
        }
        len *= 2;
    }
}

/// Inverse NTT's last level (len = N/2): single zeta, 256 butterflies. Split
/// from `inv_ntt_main_levels` so the runtime can fuse this pass with the
/// L2-norm accumulation (see `last_level_fused_norm`). Used standalone only
/// by the test-only `inv_ntt`. Uses the lazy butterfly to handle the
/// unreduced inputs from the lazy `inv_ntt_main_levels`; the trailing
/// `* N_INV % q` scaling in `inv_ntt` then canonicalises.
#[cfg(test)]
pub const fn inv_ntt_last_level(r: &mut [u32; N]) {
    let zeta = INV_ZETAS[1] as u64;
    let mut j = 0;
    while j < N / 2 {
        unsafe { core::hint::assert_unchecked(j + 7 + N / 2 < N) };
        gs_butterfly_lazy!(r, j, N / 2, zeta);
        gs_butterfly_lazy!(r, j + 1, N / 2, zeta);
        gs_butterfly_lazy!(r, j + 2, N / 2, zeta);
        gs_butterfly_lazy!(r, j + 3, N / 2, zeta);
        gs_butterfly_lazy!(r, j + 4, N / 2, zeta);
        gs_butterfly_lazy!(r, j + 5, N / 2, zeta);
        gs_butterfly_lazy!(r, j + 6, N / 2, zeta);
        gs_butterfly_lazy!(r, j + 7, N / 2, zeta);
        j += 8;
    }
}

/// Fused inverse-NTT-last-level + L2-norm accumulation.
///
/// Replaces the `inv_ntt_last_level(buf); for i in 0..N { norm += ... }`
/// sequence: the last GS butterfly's two outputs (positions `j` and
/// `j + N/2`) are computed in registers and consumed directly to update the
/// running norm, so `buf` is read but never re-written, and the norm loop's
/// 512 buf reloads are gone.
///
/// Returns `true` iff the final L2 sum is ≤ `bound`. There is **no**
/// per-iteration early-exit — the running norm is bounded above by
/// `256 · (2·(Q/2)² + 2·2047²) ≈ 2.1·10¹⁰` which fits comfortably in u64,
/// and the per-iter compare-and-branch was pure overhead on the success
/// path (the only path the caller cares about).
///
/// The math is identical to the unfused path:
///   raw = (c[i] + Q − buf[i]) mod Q
///   |s1c| = min(raw, Q − raw)
///   norm += |s1c|² + s2[i]²
pub fn last_level_fused_norm(buf: &[u32; N], c: &[u16; N], s2: &[i16; N], bound: u64) -> bool {
    let q = Q as u64;
    let half_q = q / 2;
    let zeta = INV_ZETAS[1] as u64;
    // `big_q = q << 23` ≈ 1.03·10¹¹ — large enough to absorb unreduced
    // `new_lo` (≤ 512·Q ≈ 6.3·10⁶) and unreduced `new_hi` (≤ 512·Q² ≈
    // 7.7·10¹⁰) in `(c + big_q - new_*) % q`. Both `new_*` values are
    // computed without `% q` (saves 2 mods per iter × 256 iters); the
    // outer `% q` on raw_* absorbs the un-reduction.
    let big_q = q << 23;
    // Same `256·Q` offset as `gs_butterfly_lazy`: the previous (level 7)
    // output may be unreduced up to ~256·Q (fused step now leaves its low
    // halves at up to 2·Q, doubling every level), so a plain `u + q - v`
    // would underflow.
    let lazy_offset = q * 256;
    let mut norm: u64 = 0;
    let mut j = 0;
    while j < N / 2 {
        // Last GS butterfly in registers — outputs are *not* written back
        // to `buf`. Both halves (`new_lo` for index `j`, `new_hi` for index
        // `j + N/2`) feed straight into the norm contribution below.
        unsafe { core::hint::assert_unchecked(j + N / 2 < N) };
        let u = buf[j] as u64;
        let v = buf[j + N / 2] as u64;
        // Unreduced — `% q` happens via the `raw_*` computations below.
        let new_lo = u + v;
        let new_hi = (u + lazy_offset - v) * zeta;

        // |s1c|² for both positions. The intermediate uses a large multiple
        // of q (`big_q = q << 23`) so the value comfortably exceeds the
        // un-reduced `new_*` ranges, AND exceeds u32::MAX so LLVM-SBF can't
        // infer the computation fits u32 and emit `lsh 0x20 ; rsh 0x20`
        // zero-extension pairs around the subtract.
        let raw_lo = ((c[j] as u64).wrapping_add(big_q).wrapping_sub(new_lo)) % q;
        let raw_hi = ((c[j + N / 2] as u64)
            .wrapping_add(big_q)
            .wrapping_sub(new_hi))
            % q;
        let s1c_lo = if raw_lo > half_q { q - raw_lo } else { raw_lo };
        let s1c_hi = if raw_hi > half_q { q - raw_hi } else { raw_hi };

        // s2[i]² as signed mul (i16 → i64 sign-extend → square gives the
        // unsigned magnitude squared).
        let s2_lo = s2[j] as i64;
        let s2_hi = s2[j + N / 2] as i64;

        norm += s1c_lo * s1c_lo + s1c_hi * s1c_hi;
        norm += (s2_lo * s2_lo + s2_hi * s2_hi) as u64;

        j += 1;
    }
    norm <= bound
}

// Standalone full inverse NTT, only used by unit tests (round-trip and
// schoolbook-multiplication checks). Production calls
// `fused_last_fwd_mul_first_inv` followed by `inv_ntt_main_levels`.
//
// Production's `inv_ntt_main_levels` is intentionally unscaled — the `1/N`
// factor is pre-folded into the prepared pubkey at compile time so the
// runtime path needs no scaling pass. The test path here applies it
// manually so the round-trip identity holds.
#[cfg(test)]
pub const fn inv_ntt(r: &mut [u32; N]) {
    inv_ntt_first_level(r);
    inv_ntt_main_levels(r);
    inv_ntt_last_level(r);
    let n_inv = N_INV as u64;
    let q = Q as u64;
    let mut k = 0;
    while k < N {
        r[k] = (r[k] as u64 * n_inv % q) as u32;
        k += 1;
    }
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
pub fn fused_last_fwd_mul_first_inv(buf: &mut [u32; N], h_pk_ntt: &[u16; N]) {
    // `T_OFFSET = 2³¹·Q ≈ 2.64·10¹³` — a multiple of Q (so `% Q` is
    // unchanged) and ≥ the worst-case `t = prev_high · z ≤ 8·Q³ ≈ 1.49·10¹³`
    // (since the forward NTT's last main level uses `ct_butterfly_lazy_t`,
    // capping prev_* at 8·Q²). Lifted to the function level so LLVM-SBF
    // emits the `lddw` once and reuses the register across all 256 inner
    // iterations rather than reloading per unrolled body.
    let t_offset: u64 = (Q as u64) * (1u64 << 31);
    macro_rules! step {
        ($i:expr) => {{
            let pair = 2 * $i;
            let z = ZETAS[N / 2 + $i] as u64;
            let z_inv = INV_ZETAS[N / 2 + $i] as u64;
            let q = Q as u64;

            // Snapshot s2_ntt's values at this pair *before* any write, so
            // the buffer can safely back both the input (s2) and output
            // (prod) roles.
            let prev_low = buf[pair] as u64;
            let prev_high = buf[pair + 1] as u64;

            // Forward last level CT butterfly (in registers, u64 throughout).
            // We deliberately *don't* reduce `t`, `s_low`, or `s_high` mod q
            // — they all flow into the next mul+mod which absorbs un-reduced
            // state.
            let t = prev_high * z;
            let s_low = prev_low + t;
            let s_high = prev_low + t_offset - t;

            // Pointwise multiplication with prepared pubkey.
            let p_low = h_pk_ntt[pair] as u64 * s_low % q;
            let p_high = h_pk_ntt[pair + 1] as u64 * s_high % q;

            // Inverse first level GS butterfly back into the same pair.
            // Low half stored unreduced (up to 2·Q): the next inv-NTT level
            // uses `gs_butterfly_lazy` whose `* zeta % q` absorbs it.
            let new_low = p_low + p_high;
            let new_high = (p_low + q - p_high) * z_inv % q;

            buf[pair] = new_low as u32;
            buf[pair + 1] = new_high as u32;
        }};
    }

    let mut i = 0;
    while i < N / 2 {
        unsafe { core::hint::assert_unchecked(2 * (i + 3) + 1 < N) };
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

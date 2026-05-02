/-
  Falcon512.NTTIso — Negacyclic NTT ring isomorphism (Aristotle target).

  The existing `Falcon512.NTT` proves per-pair butterfly identities and the
  scalar facts `psi_has_order_2N` / `n_inv_correct`. The umbrella comment in
  `Falcon512.lean` explicitly punts on whole-array correctness:

    > Pipeline-level correctness — that the 9-level NTT loop with bit-reversed
    > twiddles realizes the negacyclic ring isomorphism, that
    > `inv_ntt ∘ ntt = N · id`, that fused composition matches three-pass
    > composition across the whole array — is checked operationally
    > (Rust kernel-vs-spec proptests plus the ignored/manual PQClean
    > differential and soak tests), not in Lean.

  This file closes the gap at the abstract math level. The model is the
  bilinear NTT formula (not the Cooley-Tukey level decomposition), so
  the proof obligations reduce to: ψ-algebra (`ψ^(2N) = 1`, `ψ^N = -1`),
  the roots-of-unity sum identity, and Mathlib `Finset.sum` shuffling.

  ┌──────────────────────────────────────────────────────────────────┐
  │ TARGETS                                                          │
  ├──────────────────────────────────────────────────────────────────┤
  │ §1  ψ_zmod_pow_2N         — ψ^(2N) = 1 in ZMod Q                 │
  │ §2  ψ_zmod_pow_N          — ψ^N = -1 in ZMod Q                   │
  │ §3  ω_zmod_pow_N          — (ψ²)^N = 1                            │
  │ §4  Ninv_mul_N            — N⁻¹ · N = 1 in ZMod Q                │
  │ §5  rou_sum               — roots-of-unity sum identity          │
  │ §6  ntt_intt_id           — INTT ∘ NTT = id (the iso direction) │
  │ §7  ntt_neg_mul           — NTT preserves polynomial product    │
  │                             (Z_q[x]/(x^N+1) → Z_q^N is a ring   │
  │                              isomorphism)                        │
  └──────────────────────────────────────────────────────────────────┘

  All proofs are `sorry` — Aristotle is the intended prover. The
  per-pair butterfly facts in `Falcon512.NTT` and the scalar identities
  `psi_has_order_2N` / `n_inv_correct` are the lower rungs of the same
  ladder; this file covers the upper rungs.

  Operational counterpart: `src/ntt.rs::tests::
  ntt_multiplication_matches_schoolbook` exercises §7 on PQClean-derived
  inputs, `ntt_inv_round_trip` exercises §6.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Falcon512.Defs
import Falcon512.NTT

namespace Falcon512.Spec.NTTIso

open Falcon512.Spec
open Finset

/-! ## Constants in ZMod Q -/

/-- Primitive 2N-th root of unity in ZMod Q. The Nat-level value 49 is
    transferred via the `ZMod Q` numeric coercion; `psi_is_root` /
    `psi_order_divides` (Nat-level, in `Falcon512.NTT`) lift here. -/
def ψ : ZMod Q := 49

/-- ω = ψ² is a primitive N-th root of unity. Used as the "standard" DFT
    root for the proof of the roots-of-unity sum identity. -/
def ω : ZMod Q := ψ * ψ

/-- Modular inverse of N in ZMod Q. -/
def Ninv : ZMod Q := 12265

/-! ## §1–§4. Scalar facts (ψ algebra in ZMod Q) -/

/-- §1. `ψ^(2N) = 1` in ZMod Q. Lifts the Nat-level
    `Falcon512.Spec.NTT.psi_order_divides`. -/
theorem ψ_zmod_pow_2N : ψ ^ (2 * N) = 1 := by
  sorry

/-- §2. `ψ^N = -1` in ZMod Q. Lifts the Nat-level
    `Falcon512.Spec.NTT.psi_is_root` (which states `powQ PSI N = Q - 1`,
    and `Q - 1 ≡ -1 (mod Q)`). -/
theorem ψ_zmod_pow_N : ψ ^ N = -1 := by
  sorry

/-- §3. `ω^N = 1` — corollary of §1, since `ω = ψ²` and `ω^N = ψ^(2N) = 1`. -/
theorem ω_zmod_pow_N : ω ^ N = 1 := by
  sorry

/-- §4. `Ninv · N = 1` in ZMod Q. Lifts the Nat-level
    `Falcon512.Spec.NTT.n_inv_correct`. -/
theorem Ninv_mul_N : Ninv * (N : ZMod Q) = 1 := by
  sorry

/-! ## §5. Roots-of-unity sum identity

The load-bearing fact for both §6 and §7. For the primitive N-th root
`ω = ψ²`:

  Σ_{k=0}^{N-1} ω^(j·k) = if N ∣ j then N else 0

Standard geometric-series identity; in Mathlib reach via `geom_sum_eq`
plus a case split on `j ≡ 0 (mod N)`. -/

/-- §5. Roots-of-unity sum: full when `N ∣ j`, zero otherwise. -/
theorem rou_sum (j : Nat) :
    (∑ k : Fin N, ω ^ (j * k.val)) =
      if N ∣ j then (N : ZMod Q) else 0 := by
  sorry

/-! ## §6–§7. The ring isomorphism

Bilinear NTT formula (matches Falcon's negacyclic convention; see also
the Rust `ntt::ntt` function):

  NTT(a)[k] = Σ_{i=0}^{N-1} a[i] · ψ^((2k+1)·i)

The inverse uses `ψ⁻¹` (multiplicative inverse in ZMod Q) and the `Ninv`
factor; combined with §5, the round-trip telescopes to the identity. -/

/-- Forward negacyclic NTT. -/
def ntt (a : Fin N → ZMod Q) : Fin N → ZMod Q :=
  fun k => ∑ i : Fin N, a i * ψ ^ ((2 * k.val + 1) * i.val)

/-- Inverse negacyclic NTT. The factor `Ninv` cancels the `N` from §5;
    `ψ⁻¹` is the per-coefficient untwist. -/
def intt (f : Fin N → ZMod Q) : Fin N → ZMod Q :=
  fun i => Ninv * ∑ k : Fin N, f k * ψ⁻¹ ^ ((2 * k.val + 1) * i.val)

/-- Pointwise (Hadamard) product on `Fin N → ZMod Q`. -/
def pmul (a b : Fin N → ZMod Q) : Fin N → ZMod Q :=
  fun k => a k * b k

/-- Negacyclic polynomial multiplication: coefficients of `a · b` in
    `Z_q[x]/(x^N + 1)`. The `x^N ≡ -1` reduction shows up as the `-1`
    factor on the wrap-around half. -/
def negMul (a b : Fin N → ZMod Q) : Fin N → ZMod Q :=
  fun k => ∑ ij : Fin N × Fin N,
    if ij.1.val + ij.2.val = k.val then a ij.1 * b ij.2
    else if ij.1.val + ij.2.val = k.val + N then -(a ij.1 * b ij.2)
    else 0

/-- §6. **NTT round-trip identity.** `INTT ∘ NTT = id` on `Fin N → ZMod Q`.

    Proof outline:
      `intt (ntt a) i = Ninv · Σₖ (Σᵢ' a[i'] · ψ^((2k+1)i')) · ψ^(-(2k+1)i)`
      = `Ninv · Σᵢ' a[i'] · Σₖ ψ^((2k+1)(i'-i))`
      = `Ninv · Σᵢ' a[i'] · ψ^(i'-i) · Σₖ ω^(k(i'-i))`              (split exponent)
      = `Ninv · Σᵢ' a[i'] · ψ^(i'-i) · (N · [i' = i])`              (§5 with j = i'-i, |i'-i| < N)
      = `Ninv · N · a[i] · ψ^0 = a[i]`                             (§4)

    Aristotle target. -/
theorem ntt_intt_id (a : Fin N → ZMod Q) : intt (ntt a) = a := by
  sorry

/-- §7. **NTT preserves the polynomial product.** This is the substantive
    half of the negacyclic ring isomorphism

      `(Z_q[x]/(x^N + 1), +, ·) ≃ (Fin N → ZMod Q, +, pmul)`

    via NTT/INTT. The pointwise direction (`+`) is trivial; the product
    direction is non-trivial and requires §1 (so the `x^N ≡ -1` wrap
    cancels into the bilinear sum) and Mathlib `Finset.sum` shuffling.

    Proof sketch:
      `ntt (negMul a b) [k]`
      = `Σᵢ Σⱼ (sign · aᵢ bⱼ) · ψ^((2k+1)·(i+j  or  i+j-N))`
      = `Σᵢ Σⱼ aᵢ bⱼ · ψ^((2k+1)·(i+j))`                            (§2 absorbs the wrap sign)
      = `(Σᵢ aᵢ · ψ^((2k+1)i)) · (Σⱼ bⱼ · ψ^((2k+1)j))`              (bilinearity)
      = `ntt a [k] · ntt b [k]`
      = `pmul (ntt a) (ntt b) [k]`. -/
theorem ntt_neg_mul (a b : Fin N → ZMod Q) :
    ntt (negMul a b) = pmul (ntt a) (ntt b) := by
  sorry

end Falcon512.Spec.NTTIso

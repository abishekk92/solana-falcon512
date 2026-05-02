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

import Mathlib
import Falcon512.Defs
import Falcon512.NTT

namespace Falcon512.Spec.NTTIso

open Falcon512.Spec
open Finset

/-! ## Q is prime -/

instance Q_prime : Fact (Nat.Prime Q) := by unfold Q; exact ⟨by norm_num⟩

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
  unfold ψ N Q; native_decide

/-- §2. `ψ^N = -1` in ZMod Q. Lifts the Nat-level
    `Falcon512.Spec.NTT.psi_is_root` (which states `powQ PSI N = Q - 1`,
    and `Q - 1 ≡ -1 (mod Q)`). -/
theorem ψ_zmod_pow_N : ψ ^ N = -1 := by
  unfold ψ N Q; native_decide

/-- §3. `ω^N = 1` — corollary of §1, since `ω = ψ²` and `ω^N = ψ^(2N) = 1`. -/
theorem ω_zmod_pow_N : ω ^ N = 1 := by
  unfold ω ψ N Q; native_decide

/-- §4. `Ninv · N = 1` in ZMod Q. Lifts the Nat-level
    `Falcon512.Spec.NTT.n_inv_correct`. -/
theorem Ninv_mul_N : Ninv * (N : ZMod Q) = 1 := by
  unfold Ninv N Q; native_decide

/-! ## §5. Roots-of-unity sum identity -/

/-- ω is a primitive N-th root: ω^m ≠ 1 for 0 < m < N. -/
theorem omega_primitive : ∀ m : Fin N, m.val ≠ 0 → ω ^ m.val ≠ 1 := by
  unfold ω ψ N Q; native_decide

/-- (ω^j)^N = 1 for all j. -/
theorem omega_pow_j_pow_N (j : ℕ) : (ω ^ j) ^ N = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, ω_zmod_pow_N, one_pow]

/-
ω^j = 1 iff N ∣ j.
-/
theorem omega_pow_eq_one_iff (j : ℕ) : ω ^ j = 1 ↔ N ∣ j := by
  have h_order : orderOf ω = N := by
    rw [ orderOf_eq_iff ];
    · native_decide +revert;
    · decide +revert
  generalize_proofs at *;
  rw [ ← h_order, orderOf_dvd_iff_pow_eq_one ]

/-
§5. Roots-of-unity sum: full when `N ∣ j`, zero otherwise.
-/
theorem rou_sum (j : Nat) :
    (∑ k : Fin N, ω ^ (j * k.val)) =
      if N ∣ j then (N : ZMod Q) else 0 := by
  split_ifs with h;
  · obtain ⟨ k, rfl ⟩ := h;
    simp +decide [ pow_mul, ω_zmod_pow_N ];
  · have h_geom_sum : ∑ k ∈ Finset.range N, (ω ^ j) ^ k = 0 := by
      rw [ geom_sum_eq ];
      · rw [ ← pow_mul, mul_comm, pow_mul, ω_zmod_pow_N, one_pow, sub_self, zero_div ];
      · exact fun h' => h <| omega_pow_eq_one_iff j |>.1 h';
    simpa [ pow_mul, Finset.sum_range ] using h_geom_sum

/-! ## §6–§7. The ring isomorphism -/

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

/-- ψ is a unit in ZMod Q. -/
theorem psi_ne_zero : ψ ≠ 0 := by unfold ψ Q; native_decide

/-- ψ * ψ⁻¹ = 1 in ZMod Q. -/
theorem psi_mul_inv : ψ * ψ⁻¹ = 1 := by
  exact mul_inv_cancel₀ psi_ne_zero

/-- ψ⁻¹ * ψ = 1 in ZMod Q. -/
theorem psi_inv_mul : ψ⁻¹ * ψ = 1 := by
  exact inv_mul_cancel₀ psi_ne_zero

/-- N > 0. -/
theorem N_pos : (0 : ℕ) < N := by unfold N; omega

/-
§6. **NTT round-trip identity.** `INTT ∘ NTT = id` on `Fin N → ZMod Q`.
-/
set_option maxHeartbeats 800000 in
theorem ntt_intt_id (a : Fin N → ZMod Q) : intt (ntt a) = a := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∀ i : Fin N, ∑ k : Fin N, (∑ j : Fin N, a j * ψ ^ ((2 * k.val + 1) * j.val)) * ψ⁻¹ ^ ((2 * k.val + 1) * i.val) = ∑ j : Fin N, a j * (∑ k : Fin N, ψ ^ ((2 * k.val + 1) * (j.val - i.val : ℤ))) := by
    intro i;
    simp +decide only [sum_mul, mul_assoc, Finset.mul_sum _ _ _];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
    group;
    rw [ mul_assoc, ← zpow_add₀ ( show ψ ≠ 0 from by native_decide ) ] ; ring;
  -- By the properties of the roots of unity, we know that $\sum_{k=0}^{N-1} \psi^{(2k+1)(j-i)} = N$ if $j = i$ and $0$ otherwise.
  have h_sum : ∀ i j : Fin N, ∑ k : Fin N, ψ ^ ((2 * k.val + 1) * (j.val - i.val : ℤ)) = if i = j then (N : ZMod Q) else 0 := by
    intro i j
    by_cases hij : i = j;
    · aesop;
    · -- Since $i \neq j$, we have $j - i \neq 0$, and thus $\psi^{2(j-i)} \neq 1$.
      have h_ne_one : ψ ^ (2 * (j.val - i.val : ℤ)) ≠ 1 := by
        have h_ne_one : ω ^ (Int.natAbs (j.val - i.val)) ≠ 1 := by
          native_decide +revert;
        cases abs_cases ( j - i : ℤ ) <;> simp_all +decide [ pow_mul, ω ];
        · convert h_ne_one using 1 ; ring;
          rw [ show ( j : ℤ ) * 2 - i * 2 = ( j - i : ℤ ) * 2 by ring, show ( j - i : ℤ ).natAbs * 2 = ( j - i : ℤ ).natAbs * 2 by ring ] ; norm_cast;
          rw [ Int.subNatNat_of_le ( mod_cast ‹_› ) ] ; norm_cast;
        · contrapose! h_ne_one;
          convert congr_arg ( fun x : ZMod Q => x⁻¹ ) h_ne_one using 1 ; norm_num [ zpow_mul ];
          group;
          exact congr_arg _ ( by omega );
      -- Since $\psi^{2(j-i)} \neq 1$, we can factor out $\psi^{j-i}$ from the sum.
      have h_factor : ∑ k : Fin N, ψ ^ ((2 * k.val + 1) * (j.val - i.val : ℤ)) = ψ ^ (j.val - i.val : ℤ) * ∑ k : Fin N, (ψ ^ (2 * (j.val - i.val : ℤ))) ^ k.val := by
        rw [ Finset.mul_sum _ _ _ ] ; congr ; ext k ; ring;
        group;
        rw [ ← zpow_add₀ ( show ψ ≠ 0 from by native_decide ) ] ; ring;
      have h_geom_sum : ∑ k ∈ Finset.range N, (ψ ^ (2 * (j.val - i.val : ℤ))) ^ k = (1 - (ψ ^ (2 * (j.val - i.val : ℤ))) ^ N) / (1 - ψ ^ (2 * (j.val - i.val : ℤ))) := by
        rw [ geom_sum_eq ];
        · rw [ ← neg_div_neg_eq, neg_sub, neg_sub ];
        · exact h_ne_one;
      simp_all +decide [ Finset.sum_range, Fin.cast_val_eq_self ];
      rw [ ← zpow_natCast, ← zpow_mul ];
      rw [ show ( ψ : ZMod Q ) ^ ( 2 * ( j - i : ℤ ) * N : ℤ ) = ( ψ ^ ( 2 * N : ℤ ) ) ^ ( j - i : ℤ ) by group, show ( ψ : ZMod Q ) ^ ( 2 * N : ℤ ) = 1 by exact mod_cast ψ_zmod_pow_2N ] ; norm_num;
  -- By combining the results from h_fubini and h_sum, we can conclude that the inverse NTT of the NTT of a is equal to a.
  have h_final : ∀ i : Fin N, Ninv * ∑ j : Fin N, a j * (∑ k : Fin N, ψ ^ ((2 * k.val + 1) * (j.val - i.val : ℤ))) = a i := by
    intro i
    simp [h_sum];
    rw [ mul_left_comm, show ( N : ZMod Q ) = Ninv⁻¹ from ?_, mul_inv_cancel₀ ] <;> norm_num [ Ninv_mul_N ];
    · native_decide +revert;
    · native_decide +revert;
  exact funext fun i => by simpa only [ intt, ntt, h_fubini ] using h_final i;

/-
§7. **NTT preserves the polynomial product.**
-/
theorem ntt_neg_mul (a b : Fin N → ZMod Q) :
    ntt (negMul a b) = pmul (ntt a) (ntt b) := by
  -- By definition of ntt and pmul, we can expand both sides.
  ext k
  simp [ntt, pmul];
  unfold negMul;
  have h_sum : ∀ (i j : Fin N), ψ ^ ((2 * k.val + 1) * (i.val + j.val)) = if i.val + j.val < N then ψ ^ ((2 * k.val + 1) * (i.val + j.val)) else -ψ ^ ((2 * k.val + 1) * (i.val + j.val - N)) := by
    intro i j
    by_cases h : i.val + j.val < N;
    · rw [ if_pos h ];
    · rw [ show ( 2 * k.val + 1 ) * ( i.val + j.val ) = ( 2 * k.val + 1 ) * ( i.val + j.val - N ) + ( 2 * k.val + 1 ) * N by nlinarith [ Nat.sub_add_cancel ( show N ≤ i.val + j.val from le_of_not_gt h ) ] ];
      rw [ pow_add, show ψ ^ ( ( 2 * k.val + 1 ) * N ) = ( ψ ^ N ) ^ ( 2 * k.val + 1 ) by ring, ψ_zmod_pow_N ] ; norm_num;
  have h_sum : ∑ i : Fin N, (∑ ij : Fin N × Fin N, if ij.1.val + ij.2.val = i.val then a ij.1 * b ij.2 else if ij.1.val + ij.2.val = i.val + N then -(a ij.1 * b ij.2) else 0) * ψ ^ ((2 * k.val + 1) * i.val) = ∑ ij : Fin N × Fin N, a ij.1 * b ij.2 * ψ ^ ((2 * k.val + 1) * (ij.1.val + ij.2.val)) := by
    simp +decide only [Finset.sum_mul _ _ _];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun ij _ => _;
    by_cases h : ( ij.1 : ℕ ) + ij.2 < N <;> simp +decide [ h ];
    · rw [ Finset.sum_eq_single ⟨ ij.1 + ij.2, h ⟩ ] <;> simp +contextual [ h ];
      grind;
    · rw [ Finset.sum_eq_single ⟨ ij.1 + ij.2 - N, by
        rw [ tsub_lt_iff_left ] <;> linarith [ Fin.is_lt ij.1, Fin.is_lt ij.2, show N = 512 from rfl ] ⟩ ] <;> norm_num
      all_goals generalize_proofs at *;
      · grind;
      · grind;
  rw [ h_sum, Finset.sum_mul_sum ];
  rw [ ← Finset.sum_product' ];
  exact Finset.sum_congr rfl fun _ _ => by ring;

end Falcon512.Spec.NTTIso
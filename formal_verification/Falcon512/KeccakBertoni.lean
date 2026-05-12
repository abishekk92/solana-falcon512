/-
  Falcon512.KeccakBertoni — Bertoni lane-complementation invariance.

  The optimized `keccak_f1600` in `src/keccak.rs` pre-complements six
  specific lanes (the Keccak Team set `CS = {1, 2, 8, 12, 17, 20}`) and
  rewrites χ to use mixed Boolean operations (`b ∨ c`, `b ∧ c`) such
  that across one full round the complementation pattern returns to
  CS. Net: ~456 NOTs eliminated per 24-round permute.

  This file states the mathematical content of that optimization as the
  **round-commutation theorem**:

    `round rc (applyMask CS_mask s) = applyMask CS_mask (round rc s)`

  for any state `s` and round constant `rc`. If this holds, then 24
  rounds preserve the CS-complementation pattern, and the entry/exit
  `applyMask CS_mask` cancels — recovering the canonical
  `keccak_f1600`. The 6 entry XORs + 6 exit XORs are the boundary
  cost; the per-round NOT eliminations are the savings.

  ┌──────────────────────────────────────────────────────────────────┐
  │ TARGETS (Aristotle ladder, original framing)                     │
  ├──────────────────────────────────────────────────────────────────┤
  │ §1  applyMask_xor_self  — applyMask M ∘ applyMask M = id         │
  │ §3  rho_under_mask      — ρ permutes which lanes are masked     │
  │ §5  chi_under_CS_mask   — χ commutes with applyMask CS_mask     │
  │                            **FALSE as stated** (see note below) │
  │ §6  iota_under_CS_mask  — ι (CS excludes lane 0) commutes       │
  │ §7  bertoni_round_inv   — round rc commutes with applyMask CS   │
  │                            **FALSE as stated** (follows from §5)│
  │ §8  bertoni_f1600_eq    — applyMask CS_mask ∘ f1600 ∘           │
  │                            applyMask CS_mask = f1600            │
  │                            **FALSE as stated** (follows from §7)│
  └──────────────────────────────────────────────────────────────────┘

  (§2 and §4 — existential forms of θ/π under mask — removed. The
  equational propagation forms with explicit `m_theta` and `m_pi`
  witnesses are proved in `Falcon512.KeccakOptimized` as `theta_specific`
  and `pi_specific` instead.)

  **STATUS NOTE:**

  Theorems §1, §3, §6 are proved unconditionally and feed directly into
  `Falcon512.KeccakOptimized`'s round-commutation chain.

  Theorems §5, §7, §8 are **false as stated**. Concrete counterexample
  for §5: `s = fun _ => 1`, lane 4 gives `chi(applyMask CS s)[4] =
  2^64 − 1` but `(applyMask CS (chi s))[4] = 1`. The real Bertoni
  optimization works by *modifying* the χ implementation (replacing
  `¬b ∧ c` with `b ∧ c`, `¬b ∨ c`, etc.) so that the modified round
  absorbs the complementation — it does NOT claim the *standard* χ
  commutes with the mask. §7 and §8 fall as dependents.

  The correct round-commutation rung uses a `modified_chi` that
  encodes the per-row IN/OUT complementation table; that rung is
  proved in `Falcon512.KeccakOptimized` as `chi_rung`, and the full
  24-round Bertoni soundness is proved there as
  `optimized_eq_canonical`.
-/

import Mathlib
import Falcon512.Defs
import Falcon512.Keccakf1600

namespace Falcon512.Spec.KeccakBertoni

open Falcon512.Spec.Keccakf1600

/-- The Keccak Team's chosen lane-complementation set. Indices into
    `Fin 25` (FIPS-202 §B.1 lane order: `idx = 5y + x`). The set is
    `{1, 2, 8, 12, 17, 20}` — picked so that one full round
    `θ ∘ ρ ∘ π ∘ χ ∘ ι` propagates this complementation pattern back
    to itself, allowing entry/exit XOR-cancellation across 24 rounds. -/
def CS_mask : Fin 25 → Bool
  | ⟨1,  _⟩ | ⟨2,  _⟩ | ⟨8,  _⟩ | ⟨12, _⟩ | ⟨17, _⟩ | ⟨20, _⟩ => true
  | _ => false

/-- All-1s 64-bit mask. XORing with this is bit-complement on a u64. -/
def all_ones : Nat := 2 ^ 64 - 1

/-- Apply a complementation mask to a state: XOR each masked lane with
    `all_ones` (i.e. flip all 64 bits of that lane). -/
def applyMask (m : Fin 25 → Bool) (s : State) : State :=
  fun i => if m i then s i ^^^ all_ones else s i

/-! ## §1. applyMask is self-inverse -/

/-
§1. `applyMask M (applyMask M s) = s`. XOR is involutive.
-/
theorem applyMask_xor_self (m : Fin 25 → Bool) (s : State) :
    applyMask m (applyMask m s) = s := by
  ext i; unfold applyMask; aesop;

/-! ## §2–§6. Per-step commutation lemmas

Each of θ, ρ, π either commutes with `applyMask M` for any mask `M` (the
linear operations) or commutes for the specific CS-derived mask after
its propagation step. χ is the substantive nonlinear case; ι touches
only lane 0, which CS_mask excludes.

For the linear operations we don't need an abstract mask-propagation
function — we state the specific result that's used in §7. -/

/-
§2. **θ commutes with `applyMask` (existentially).** θ is unconditionally
XOR-linear (`Keccakf1600.theta_linear`, which holds because our `rotL64`
uses XOR for the half-merge — `rotL64_xor` is XOR-distributive on `Nat`
without a 64-bit bound). Splitting `applyMask m s = s ⊕ d` where `d j`
is `all_ones` on masked lanes and `0` elsewhere, θ pushes through the
XOR to give `θ(applyMask m s) = θ s ⊕ θ d`. Since `θ d` is itself a
mask state (per-lane in `{0, all_ones}`, proved below via
`theta_mask_state`), we can witness the existential with
`m' i := (θ d) i = all_ones`.
-/

/-
Helper: rotL64 of all_ones is all_ones. Bit-level reasoning over the
XOR-form `rotL64`. For `i < 64` the low and high halves of the rotation
have disjoint bit ranges (one from the left shift, the other from the
right shift), so the XOR fills all 64 bits; mod 2^64 keeps exactly
those bits, which is `all_ones`. For `i ≥ 64` both sides have testBit
`false`.
-/
lemma rotL64_all_ones (n : Nat) : rotL64 all_ones n = all_ones := by
  unfold rotL64 all_ones
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · simp only [hi, decide_true, Bool.true_and]
    rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
        Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    have hsub : i - n < 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hi
    by_cases hn : n ≤ i
    · have h1 : ¬ (64 - n + i < 64) := by omega
      simp [hn, hsub, h1]
    · have h1 : (64 - n + i < 64) := by omega
      simp [hn, h1]
  · simp [hi]

/-
§3. **ρ commutes with `applyMask`.** ρ is per-lane (rotates each lane
independently, never moves lanes between indices), and 64-bit rotation
commutes with 64-bit complement: `rotL64_xor` (unconditional) gives
`rotL64 (a ^^^ all_ones) n = rotL64 a n ^^^ rotL64 all_ones n`, and
`rotL64_all_ones` collapses the second rotation to `all_ones`. No bound
on `s` is needed.
-/
lemma rotL64_xor_all_ones (a n : Nat) :
    rotL64 (a ^^^ all_ones) n = rotL64 a n ^^^ all_ones := by
  rw [rotL64_xor, rotL64_all_ones]

/-- §3. ρ commutes with `applyMask`. Unconditional. -/
theorem rho_under_mask (m : Fin 25 → Bool) (s : State) :
    rho (applyMask m s) = applyMask m (rho s) := by
  funext i
  by_cases hi : m i <;> simp +decide [*, rho, applyMask]
  exact rotL64_xor_all_ones _ _

/-
§2 and §4 (`theta_under_mask`, `pi_under_mask`) — existential forms
removed. `Falcon512.KeccakOptimized` proves the stronger *equational*
forms (`theta_specific`, `pi_specific`) with explicit witness masks
`m_theta` and `m_pi` propagated from `CS_mask`, which is what the
round-commutation chain actually needs. The existential forms were
historical scaffolds; the equations are load-bearing.
-/

/-
§5. **χ commutes with `applyMask CS_mask`.**

   FALSE: χ is nonlinear (`¬b ∧ c`), and complementing input lanes
   does not produce a simple lane-complement on the output.

   Concrete counterexample: `s = fun _ => 1`.
   - `chi (applyMask CS_mask s) ⟨4, _⟩ = 2^64 − 1` (= all_ones)
   - `(applyMask CS_mask (chi s)) ⟨4, _⟩ = 1`
   These differ, so the theorem is false.

   The real Bertoni optimization modifies the χ implementation for
   complemented lanes (replacing `¬b ∧ c` with `b ∧ c` or `¬b ∨ c`
   as appropriate) rather than claiming standard χ commutes with
   `CS_mask`.

   A correct formulation would define `chi_bertoni` (the modified χ)
   and prove:
     `chi_bertoni (applyMask CS_mask_at_chi s)
      = applyMask CS_mask_out (chi s)`
   where `CS_mask_at_chi` is the mask after θ→ρ→π and `CS_mask_out`
   is determined by the per-row complementation table.

   Original (false) statement — commented out:
theorem chi_under_CS_mask (s : State) :
    chi (applyMask CS_mask s) = applyMask CS_mask (chi s) := by
  sorry

§6. **ι commutes with `applyMask CS_mask`.** ι touches only lane 0;
    `CS_mask 0 = false`, so the lane-0-bound XOR doesn't intersect
    the mask.
-/
theorem iota_under_CS_mask (rc : Nat) (s : State) :
    iota rc (applyMask CS_mask s) = applyMask CS_mask (iota rc s) := by
  exact List.ofFn_inj.mp rfl

/-! ## §7. Headline: round commutation (Aristotle target)

  FALSE as stated: since §5 (`chi_under_CS_mask`) is false, the
  standard round does not commute with `applyMask CS_mask`.

  Verified by counterexample: `s = fun _ => 1`, `rc = 0` — all 25
  lanes differ between `round 0 (applyMask CS_mask s)` and
  `applyMask CS_mask (round 0 s)`.

  Original (false) statement — commented out:
theorem bertoni_round_inv (rc : Nat) (s : State) :
    round rc (applyMask CS_mask s) = applyMask CS_mask (round rc s) := by
  sorry
-/

/-! ## §8. 24-round cancellation

  FALSE as stated: depends on §7, which is false.

  Original (false) statement — commented out:
theorem bertoni_f1600_eq (rcTable : List Nat) (s : State) :
    applyMask CS_mask (f1600 rcTable (applyMask CS_mask s)) = f1600 rcTable s := by
  sorry
-/

end Falcon512.Spec.KeccakBertoni
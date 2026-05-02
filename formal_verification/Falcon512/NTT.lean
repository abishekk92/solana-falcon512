/-
  Falcon512.NTT — Number Theoretic Transform correctness.

  Proves that the CT and GS butterflies are mutual inverses,
  that the NTT round-trip identity holds at the butterfly level,
  and key algebraic constants (N_INV, PSI).

  Uses Mathlib's ZMod for modular arithmetic ring reasoning.
-/

import Falcon512.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

namespace Falcon512.Spec.NTT

open Falcon512.Spec

-- ============================================================================
-- N_INV correctness
-- ============================================================================

def N_INV : Nat := 12265

theorem n_inv_correct : (N_INV * N) % Q = 1 := by native_decide

-- ============================================================================
-- PSI (primitive 2N-th root of unity)
-- ============================================================================

def PSI : Nat := 49

theorem psi_is_root : powQ PSI N = Q - 1 := by native_decide

theorem psi_order_divides : powQ PSI (2 * N) = 1 := by native_decide

-- ============================================================================
-- Modular distributivity helpers (used by Fused.lean and Norm.lean)
-- ============================================================================

/-- (a * b) % q = ((a % q) * b) % q -/
theorem mul_mod_left (a b q : Nat) (_hq : q > 0) :
    (a * b) % q = ((a % q) * b) % q := by
  conv_lhs => rw [Nat.mul_mod]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]

/-- (a * b) % q = (a * (b % q)) % q -/
theorem mul_mod_right (a b q : Nat) (_hq : q > 0) :
    (a * b) % q = (a * (b % q)) % q := by
  conv_lhs => rw [Nat.mul_mod]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]

/-- Adding a multiple of q doesn't change the residue. -/
theorem add_mul_mod (a k q : Nat) (_hq : q > 0) :
    (a + k * q) % q = a % q := by
  rw [Nat.add_mul_mod_self_right]

-- ============================================================================
-- CT/GS butterfly inverse relationship
-- ============================================================================

/-- A CT butterfly followed by a GS butterfly with the inverse twiddle
    factor recovers the original pair scaled by 2.
    This is proven in ZMod Q where we have ring structure. -/
theorem ct_gs_inverse_zmod (a b z : ZMod Q)
    (hz : z * z⁻¹ = 1) :
    let lo := a + b * z
    let hi := a - b * z
    lo + hi = 2 * a ∧ (lo - hi) * z⁻¹ = 2 * b := by
  constructor
  · ring
  · -- (lo - hi) * z⁻¹ = 2 * b * z * z⁻¹ = 2 * b
    have : (a + b * z - (a - b * z)) * z⁻¹ = 2 * b * (z * z⁻¹) := by ring
    rw [this, hz, mul_one]

-- ============================================================================
-- Full NTT round-trip scaling factor
-- ============================================================================
--
-- `ct_gs_inverse_zmod` above already establishes the per-level round-trip
-- (forward CT followed by inverse GS recovers `(2a, 2b)`). The full NTT
-- applies `log₂(N) = 9` levels, accumulating a factor of `2^9 = N`, which
-- is then cancelled by `N_INV` (pre-folded into the prepared pubkey).

/-- After log₂(N) = 9 butterfly levels, the accumulated scaling factor
    is 2^9 = 512 = N. Multiplying by N_INV recovers the original. -/
theorem scaling_factor_correct :
    (2^9 : Nat) = N := by unfold N; omega

/-- N * N_INV ≡ 1 (mod Q), confirming the scaling cancels. -/
theorem n_times_n_inv : (N * N_INV) % Q = 1 := by
  unfold N N_INV Q; native_decide

-- ============================================================================
-- PSI is a primitive 2N-th root of unity in Z_q
-- ============================================================================

/-- PSI has order exactly 2N in Z_q*: `psi^N = -1 (mod Q)` and
    `psi^(2N) = 1 (mod Q)`. These are the two scalar facts that make
    PSI a primitive 2N-th root of unity, the precondition for the
    NTT-as-ring-isomorphism construction (`Z_q[x]/(x^N+1) ↔ Z_q^N` via
    CRT).

    This lemma proves *only* the order facts; the full ring-isomorphism
    claim (that NTT-pointwise-mul corresponds to polynomial mul mod
    x^N+1) is exhaustively checked by the
    `ntt_multiplication_matches_schoolbook` test in `src/ntt.rs`. -/
theorem psi_has_order_2N :
    powQ PSI N = Q - 1 ∧ powQ PSI (2 * N) = 1 :=
  ⟨psi_is_root, psi_order_divides⟩

end Falcon512.Spec.NTT

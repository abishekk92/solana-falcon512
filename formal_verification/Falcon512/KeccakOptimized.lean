/-
  Falcon512.KeccakOptimized — formal soundness of Bertoni
  lane-complementing optimization in `src/keccak.rs::keccak_f1600`.

  ## Theorem (final)

      ∀ rcTable s, (∀ i, s i < 2^64) →
        optimized_f1600 rcTable s = canonical_f1600 rcTable s

  where `optimized_f1600` mirrors the entry-XOR-mask + 24 modified
  rounds + exit-XOR-mask structure of `src/keccak.rs::keccak_f1600`.

  ## Strategy

  1. Bridge: `(2^64 - 1) - n = n ^^^ (2^64 - 1)` for `n < 2^64` lifts
     the canonical-chi `mask - n % 2^64` form to XOR-form complement.
  2. Per-lane chi identities: 9 distinct (formula shape, IN-pattern,
     OUT) combinations cover all 25 lanes; each is proved via
     `Nat.eq_of_testBit_eq` + 8-way Boolean case analysis.
  3. State-level `chi_rung`:
        modified_chi (applyMask m_pi s) = applyMask CS_mask (canonical_chi s).
  4. Round commutation via §2/§3/§4/§6 from `KeccakBertoni` chained
     with the chi rung.
  5. 24-round induction lifts to `f1600` cancellation.
  6. Soundness: entry/exit applyMask cancels (`applyMask_xor_self`
     §1) → `optimized_f1600 s = canonical_f1600 s`.
-/

import Mathlib
import Falcon512.Defs
import Falcon512.Keccakf1600
import Falcon512.KeccakBertoni

namespace Falcon512.Spec.KeccakOptimized

open Falcon512.Spec.Keccakf1600
open Falcon512.Spec.KeccakBertoni

/-! ## Bridge: subtractive complement = XOR complement on u64 -/

/-- For `n < 2^64`, `mask - n` (canonical-chi form) equals
    `n ^^^ (2^64 - 1)` (Bertoni XOR form). Lifts via `BitVec 64`
    where `bv_decide` discharges the closed identity. -/
lemma sub_eq_xor_ones {n : Nat} (h : n < 2 ^ 64) :
    (2 ^ 64 - 1) - n = n ^^^ (2 ^ 64 - 1) := by
  have h_bv : ∀ x : BitVec 64, BitVec.allOnes 64 - x = x ^^^ BitVec.allOnes 64 := by
    intro x; bv_decide
  have h_specific := h_bv (BitVec.ofNat 64 n)
  have hL : (BitVec.allOnes 64 - BitVec.ofNat 64 n).toNat = (2 ^ 64 - 1) - n := by
    rw [BitVec.toNat_sub, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt h]
    omega
  have hR : (BitVec.ofNat 64 n ^^^ BitVec.allOnes 64).toNat = n ^^^ (2 ^ 64 - 1) := by
    simp [BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h]
    exact h
  exact hL ▸ hR ▸ congrArg BitVec.toNat h_specific

/-! ## Per-lane testBit infrastructure -/

private lemma testBit_of_lt_64 {B : Nat} (h : B < 2 ^ 64) {i : Nat} (hi : ¬ i < 64) :
    B.testBit i = false :=
  Nat.testBit_eq_false_of_lt
    (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hi)))

-- (Inlined per-lane proof template — each chi_id_X carries its own
-- Nat.eq_of_testBit_eq + 8-way case split.)

/-! ## The 9 distinct per-lane chi identities

Each lemma has the form: `rust_formula(stored_b0, stored_b1, stored_b2) =
canonical(B0, B1, B2) ⊕ out_mask`, where `stored_bk = Bk ⊕ in_k * ones`.

Identity #1: shape `a ^ (b | c)`, IN=(T,F,T), OUT=F.
  Used by lanes 0, 3, 5, 10, 16, 19, 23 (7 lanes). -/
lemma chi_id_1 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    (B0 ^^^ (2^64 - 1)) ^^^ (B1 ||| (B2 ^^^ (2^64 - 1))) =
      B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-- Identity #2: shape `a ^ (b | c)`, IN=(F,F,T), OUT=T.
    Used by lane 8. -/
lemma chi_id_2 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    B0 ^^^ (B1 ||| (B2 ^^^ (2^64 - 1))) =
      (B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2)) ^^^ (2^64 - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-- Identity #3: shape `a ^ ((!b) | c)`, IN=(F,T,T), OUT=T.
    Used by lanes 1, 17. Note `!(B1 ⊕ ones) = B1` so the formula's NOT
    cancels the IN-flip on B1. -/
lemma chi_id_3 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    B0 ^^^ (((B1 ^^^ (2^64 - 1)) ^^^ (2^64 - 1)) ||| (B2 ^^^ (2^64 - 1))) =
      (B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2)) ^^^ (2^64 - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-- Identity #4: shape `a ^ (b & c)`, IN=(T,T,F), OUT=T.
    Used by lane 2. -/
lemma chi_id_4 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    (B0 ^^^ (2^64 - 1)) ^^^ ((B1 ^^^ (2^64 - 1)) &&& B2) =
      (B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2)) ^^^ (2^64 - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-- Identity #5: shape `a ^ (b & c)`, IN=(F,T,F), OUT=F.
    Used by lanes 4, 6, 9, 11, 14, 15, 22, 24 (8 lanes). -/
lemma chi_id_5 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    B0 ^^^ ((B1 ^^^ (2^64 - 1)) &&& B2) =
      B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-- Identity #6: shape `(!a) ^ c ^ (b & c)`, IN=(T,F,F), OUT=F.
    Used by lane 7. -/
lemma chi_id_6 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    ((B0 ^^^ (2^64 - 1)) ^^^ (2^64 - 1)) ^^^ B2 ^^^ (B1 &&& B2) =
      B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-- Identity #7: shape `a ^ c ^ (b & c)`, IN=(T,F,F), OUT=T.
    Used by lanes 12, 20. -/
lemma chi_id_7 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    (B0 ^^^ (2^64 - 1)) ^^^ B2 ^^^ (B1 &&& B2) =
      (B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2)) ^^^ (2^64 - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-- Identity #8: shape `a ^ !(b | c)`, IN=(F,F,T), OUT=F.
    Used by lanes 13, 21. -/
lemma chi_id_8 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    B0 ^^^ ((B1 ||| (B2 ^^^ (2^64 - 1))) ^^^ (2^64 - 1)) =
      B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-- Identity #9: shape `(!a) ^ (b & c)`, IN=(T,T,F), OUT=F.
    Used by lane 18. -/
lemma chi_id_9 (B0 B1 B2 : Nat)
    (h0 : B0 < 2^64) (h1 : B1 < 2^64) (h2 : B2 < 2^64) :
    ((B0 ^^^ (2^64 - 1)) ^^^ (2^64 - 1)) ^^^ ((B1 ^^^ (2^64 - 1)) &&& B2) =
      B0 ^^^ (((2^64 - 1) ^^^ B1) &&& B2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hi, decide_true]
    cases B0.testBit i <;> cases B1.testBit i <;> cases B2.testBit i <;> rfl
  · have hb0 := testBit_of_lt_64 h0 hi
    have hb1 := testBit_of_lt_64 h1 hi
    have hb2 := testBit_of_lt_64 h2 hi
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
               Nat.testBit_two_pow_sub_one, hb0, hb1, hb2,
               decide_eq_false (Nat.not_lt.mpr (Nat.le_of_not_lt hi))]
    try decide

/-! ## State-level masks and modified χ

`m_pi` is the IN-complement mask at the chi step: `CS_mask` propagated
through θ ∘ ρ ∘ π. Computed by hand:

  CS_mask = {1, 2, 8, 12, 17, 20}
  → after θ (column-parity XOR with d[x] derived from CS):
    m_θ = {0, 1, 2, 3, 5, 10, 12, 13, 15, 17, 18, 23}
  → ρ leaves the mask in place (per-lane rotation)
  → π lane permutation (x,y) → (y, (2x+3y) mod 5):
    m_pi = {0, 2, 3, 5, 7, 10, 12, 16, 18, 19, 20, 23}

The 25-lane Rust formulas in `src/keccak.rs::keccak_f1600` lines
81–162 each pick the appropriate (shape, IN-pattern, OUT) combination
from the 9 catalogued in `chi_id_1` … `chi_id_9` above. -/

/-- IN-complement mask at the chi step (`CS_mask` propagated through
    θ∘ρ∘π). 12 lanes flipped. -/
def m_pi : Fin 25 → Bool
  | ⟨0,  _⟩ | ⟨2,  _⟩ | ⟨3,  _⟩ | ⟨5,  _⟩ | ⟨7,  _⟩ | ⟨10, _⟩
  | ⟨12, _⟩ | ⟨16, _⟩ | ⟨18, _⟩ | ⟨19, _⟩ | ⟨20, _⟩ | ⟨23, _⟩ => true
  | _ => false

/-- Bertoni-modified χ. Per-lane formulas mirror
    `src/keccak.rs::keccak_f1600` lines 81–162 verbatim. The function
    is total over `State` (no boundedness hypothesis on its definition);
    correctness vs. canonical χ is asserted in `chi_rung_xor` below
    under `∀ i, s i < 2^64`. -/
def modified_chi (s : State) : State := fun i =>
  let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
  let x : Fin 5 := ⟨i.val % 5, by omega⟩
  let x1 : Fin 5 := ⟨(x.val + 1) % 5, by omega⟩
  let x2 : Fin 5 := ⟨(x.val + 2) % 5, by omega⟩
  let a := s (laneIdx x y)
  let b := s (laneIdx x1 y)
  let c := s (laneIdx x2 y)
  let ones := (2 ^ 64 - 1 : Nat)
  match i with
  | ⟨0,  _⟩ => a ^^^ (b ||| c)                            -- shape 1
  | ⟨1,  _⟩ => a ^^^ ((b ^^^ ones) ||| c)                 -- shape 2
  | ⟨2,  _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | ⟨3,  _⟩ => a ^^^ (b ||| c)                            -- shape 1
  | ⟨4,  _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | ⟨5,  _⟩ => a ^^^ (b ||| c)                            -- shape 1
  | ⟨6,  _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | ⟨7,  _⟩ => (a ^^^ ones) ^^^ c ^^^ (b &&& c)           -- shape 4
  | ⟨8,  _⟩ => a ^^^ (b ||| c)                            -- shape 1
  | ⟨9,  _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | ⟨10, _⟩ => a ^^^ (b ||| c)                            -- shape 1
  | ⟨11, _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | ⟨12, _⟩ => a ^^^ c ^^^ (b &&& c)                      -- shape 5
  | ⟨13, _⟩ => a ^^^ ((b ||| c) ^^^ ones)                 -- shape 6
  | ⟨14, _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | ⟨15, _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | ⟨16, _⟩ => a ^^^ (b ||| c)                            -- shape 1
  | ⟨17, _⟩ => a ^^^ ((b ^^^ ones) ||| c)                 -- shape 2
  | ⟨18, _⟩ => (a ^^^ ones) ^^^ (b &&& c)                 -- shape 7
  | ⟨19, _⟩ => a ^^^ (b ||| c)                            -- shape 1
  | ⟨20, _⟩ => a ^^^ c ^^^ (b &&& c)                      -- shape 5
  | ⟨21, _⟩ => a ^^^ ((b ||| c) ^^^ ones)                 -- shape 6
  | ⟨22, _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | ⟨23, _⟩ => a ^^^ (b ||| c)                            -- shape 1
  | ⟨24, _⟩ => a ^^^ (b &&& c)                            -- shape 3
  | _ => 0

/-! ## XOR-form canonical χ (matches the existing `Keccakf1600.chi`
    on bounded states via `sub_eq_xor_ones`) -/

/-- Canonical χ with XOR-form complement (`b ^^^ all_ones` in place of
    `mask - b % 2^64`). Equals `Keccakf1600.chi` on bounded states. -/
def canonical_chi_xor (s : State) : State := fun i =>
  let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
  let x : Fin 5 := ⟨i.val % 5, by omega⟩
  let x1 : Fin 5 := ⟨(x.val + 1) % 5, by omega⟩
  let x2 : Fin 5 := ⟨(x.val + 2) % 5, by omega⟩
  s (laneIdx x y) ^^^
    (((2 ^ 64 - 1) ^^^ s (laneIdx x1 y)) &&& s (laneIdx x2 y))

/-- Bridge: XOR-form canonical χ equals `Keccakf1600.chi` for states
    with all lanes `< 2^64`. -/
theorem canonical_chi_xor_eq_chi (s : State) (h : ∀ i, s i < 2 ^ 64) :
    canonical_chi_xor s = chi s := by
  funext i
  show s _ ^^^ (((2 ^ 64 - 1) ^^^ s _) &&& s _) = s _ ^^^ (((2 ^ 64 - 1) - s _ % (2 ^ 64)) &&& s _)
  have hb := h (laneIdx ⟨(i.val % 5 + 1) % 5, by omega⟩
                         ⟨i.val / 5, by have := i.isLt; omega⟩)
  congr 2
  · rw [Nat.xor_comm, ← sub_eq_xor_ones hb, Nat.mod_eq_of_lt hb]

/-! ## The chi commutation rung (State level)

Per-lane: each of the 25 lanes' modified-χ formula, applied to the
mask-pre-flipped inputs, equals the canonical-χ output XOR-flipped at
the OUT-mask positions. -/

/-- State-level chi commutation rung. Reduces to one of the 9
    `chi_id_X` identities per lane, dispatched via `fin_cases`. -/
theorem chi_rung_xor (s : State) (h : ∀ i, s i < 2 ^ 64) :
    modified_chi (applyMask m_pi s) = applyMask CS_mask (canonical_chi_xor s) := by
  funext i
  -- Each of the 25 lanes carries its own per-row Rust formula and (IN, OUT)
  -- pattern; reduce to the matching `chi_id_X` by case-analysis on `i`.
  fin_cases i <;>
  · simp only [modified_chi, applyMask, canonical_chi_xor, m_pi, CS_mask, laneIdx,
               ↓reduceIte]
    first
    | exact chi_id_1 _ _ _ (h _) (h _) (h _)
    | exact chi_id_2 _ _ _ (h _) (h _) (h _)
    | exact chi_id_3 _ _ _ (h _) (h _) (h _)
    | exact chi_id_4 _ _ _ (h _) (h _) (h _)
    | exact chi_id_5 _ _ _ (h _) (h _) (h _)
    | exact chi_id_6 _ _ _ (h _) (h _) (h _)
    | exact chi_id_7 _ _ _ (h _) (h _) (h _)
    | exact chi_id_8 _ _ _ (h _) (h _) (h _)
    | exact chi_id_9 _ _ _ (h _) (h _) (h _)

/-- Chi rung against canonical (subtractive) χ — chains
    `chi_rung_xor` with `canonical_chi_xor_eq_chi`. -/
theorem chi_rung (s : State) (h : ∀ i, s i < 2 ^ 64) :
    modified_chi (applyMask m_pi s) = applyMask CS_mask (chi s) := by
  rw [chi_rung_xor s h, canonical_chi_xor_eq_chi s h]

/-! ## θ-specific and π-specific mask propagation -/

/-- The IN-mask after θ propagation of `CS_mask`. Hand-computed: each
    lane's contribution from the column-parity XOR with `CS_mask`'s
    columns ((d[0]=ones, d[1..3]=0..., d[4]=0)). -/
def m_theta : Fin 25 → Bool
  | ⟨0,  _⟩ | ⟨1,  _⟩ | ⟨2,  _⟩ | ⟨3,  _⟩ | ⟨5,  _⟩
  | ⟨10, _⟩ | ⟨12, _⟩ | ⟨13, _⟩ | ⟨15, _⟩ | ⟨17, _⟩
  | ⟨18, _⟩ | ⟨23, _⟩ => true
  | _ => false

/-- π lane permutation (FIPS form): `pi`'s source for output lane
    `i = 5y + x` is `laneIdx ((x+3y) mod 5) x`. We confirm
    `m_pi i = m_theta (pi-source i)` by `fin_cases` + `decide`. -/
theorem m_pi_eq_pi_perm_m_theta : ∀ i : Fin 25,
    m_pi i = m_theta (laneIdx ⟨(i.val % 5 + 3 * (i.val / 5)) % 5, by omega⟩
                              ⟨i.val % 5, by omega⟩) := by
  decide

/-- π propagates `m_theta` to `m_pi`. -/
theorem pi_specific (s : State) :
    pi (applyMask m_theta s) = applyMask m_pi (pi s) := by
  funext i
  show (applyMask m_theta s) _ = if m_pi i then pi s i ^^^ all_ones else pi s i
  show (if m_theta _ then s _ ^^^ all_ones else s _) = _
  rw [m_pi_eq_pi_perm_m_theta i]
  rfl

/-! ## θ propagation: prove the column-parity propagation matches m_theta -/

/-- Mask state: `all_ones` at masked lanes, `0` elsewhere. -/
def maskState (m : Fin 25 → Bool) : State :=
  fun i => if m i then all_ones else 0

/-- `applyMask m s = fun j => s j ⊕ maskState m j`. -/
private lemma applyMask_xor_form (m : Fin 25 → Bool) (s : State) :
    applyMask m s = fun j => s j ^^^ maskState m j := by
  funext j
  unfold applyMask maskState
  by_cases hj : m j <;> simp [hj]

/-- θ of the CS mask state equals the m_θ mask state. Closed by
    `decide` (concrete computation over 25 lanes). -/
theorem theta_maskState_CS : theta (maskState CS_mask) = maskState m_theta := by
  decide

/-- θ-specific propagation: θ (applyMask CS_mask s) = applyMask m_θ (θ s). -/
theorem theta_specific (s : State) :
    theta (applyMask CS_mask s) = applyMask m_theta (theta s) := by
  rw [applyMask_xor_form, applyMask_xor_form]
  funext i
  rw [show (fun j => s j ^^^ maskState CS_mask j) =
        (fun j => s j ^^^ maskState CS_mask j) from rfl]
  rw [theta_linear s (maskState CS_mask) i, theta_maskState_CS]

/-! ## ρ-specific: ρ commutes with `applyMask` (use existing §3) -/

theorem rho_specific (s : State) :
    rho (applyMask m_theta s) = applyMask m_theta (rho s) :=
  rho_under_mask m_theta s

/-! ## ι-specific: use existing §6 -/

theorem iota_specific (rc : Nat) (s : State) :
    iota rc (applyMask CS_mask s) = applyMask CS_mask (iota rc s) :=
  iota_under_CS_mask rc s

/-! ## Round commutation -/

/-- Bertoni-modified round: `ι ∘ modified_χ ∘ π ∘ ρ ∘ θ`. -/
def optimized_round (rc : Nat) (s : State) : State :=
  iota rc (modified_chi (pi (rho (theta s))))

/-- Aux: ρ preserves the per-lane `< 2^64` bound (each lane is `rotL64`
    of the input, which mods by `2^64`). -/
private lemma rho_bounded (s : State) : ∀ i, rho s i < 2 ^ 64 := by
  intro i
  unfold rho rotL64
  exact Nat.mod_lt _ (by decide)

/-- Aux: π preserves the bound (it just permutes lanes). -/
private lemma pi_bounded (s : State) (h : ∀ i, s i < 2 ^ 64) :
    ∀ i, pi s i < 2 ^ 64 := by
  intro i; unfold pi; exact h _

/-- Round commutation: one optimized round, applied to the
    CS-pre-complemented state, equals the canonical round followed by
    CS-complementation. -/
theorem round_commutation (rc : Nat) (s : State) (h : ∀ i, s i < 2 ^ 64) :
    optimized_round rc (applyMask CS_mask s) = applyMask CS_mask (Keccakf1600.round rc s) := by
  unfold optimized_round Keccakf1600.round
  rw [theta_specific, rho_specific, pi_specific]
  rw [chi_rung _ (pi_bounded _ (rho_bounded _))]
  rw [iota_specific]

/-! ## 24-round induction and final soundness -/

/-- `applyMask` preserves the `< 2^64` bound: flipping with `all_ones`
    keeps a `< 2^64` value `< 2^64`. -/
private lemma applyMask_bounded (m : Fin 25 → Bool) (s : State) (h : ∀ i, s i < 2 ^ 64) :
    ∀ i, applyMask m s i < 2 ^ 64 := by
  intro i
  unfold applyMask all_ones
  by_cases hi : m i
  · simp [hi]
    exact Nat.xor_lt_two_pow (h i) (by omega)
  · simp [hi]; exact h i

/-! ### Boundedness preservation per step (`< 2^64`) -/

private lemma theta_bounded (s : State) (h : ∀ i, s i < 2 ^ 64) :
    ∀ i, theta s i < 2 ^ 64 := by
  intro i
  unfold theta rotL64
  refine Nat.xor_lt_two_pow ?_ ?_
  · refine Nat.xor_lt_two_pow (h _) ?_
    exact Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow
        (Nat.xor_lt_two_pow
          (Nat.xor_lt_two_pow (h _) (h _))
          (h _))
        (h _))
      (h _)
  · exact Nat.mod_lt _ (by decide)

private lemma chi_bounded (s : State) (h : ∀ i, s i < 2 ^ 64) :
    ∀ i, chi s i < 2 ^ 64 := by
  intro i
  unfold chi
  refine Nat.xor_lt_two_pow (h _) ?_
  calc _ ≤ s _ := Nat.and_le_right
    _ < 2 ^ 64 := h _

private lemma iota_bounded (rc : Nat) (hrc : rc < 2 ^ 64) (s : State) (h : ∀ i, s i < 2 ^ 64) :
    ∀ i, iota rc s i < 2 ^ 64 := by
  intro i; unfold iota
  by_cases hi : i.val = 0
  · simp [hi]; exact Nat.xor_lt_two_pow (h _) hrc
  · simp [hi]; exact h _

/-- One canonical round preserves the `< 2^64` lane bound. -/
private lemma round_bounded (rc : Nat) (hrc : rc < 2 ^ 64) (s : State) (h : ∀ i, s i < 2 ^ 64) :
    ∀ i, Keccakf1600.round rc s i < 2 ^ 64 := by
  unfold Keccakf1600.round
  apply iota_bounded _ hrc
  apply chi_bounded
  apply pi_bounded
  apply rho_bounded

/-- 24-round invariance: optimized rounds applied to the CS-flipped
    state produce the CS-flipped canonical f1600 output. -/
theorem optimized_rounds_eq_canonical_rounds
    (rcTable : List Nat) (hrc : ∀ rc ∈ rcTable, rc < 2 ^ 64)
    (s : State) (h : ∀ i, s i < 2 ^ 64) :
    rcTable.foldl (fun s' rc => optimized_round rc s') (applyMask CS_mask s)
      = applyMask CS_mask (rcTable.foldl (fun s' rc => Keccakf1600.round rc s') s) := by
  induction rcTable generalizing s with
  | nil => simp
  | cons rc rest ih =>
    simp only [List.foldl_cons]
    have hrc_head : rc < 2 ^ 64 := hrc rc List.mem_cons_self
    rw [round_commutation rc s h]
    apply ih
    · intro r hr; exact hrc r (List.mem_cons_of_mem _ hr)
    · exact round_bounded rc hrc_head s h

/-- The Bertoni-optimized Keccak-f[1600]: pre-complement CS lanes,
    run 24 modified rounds, post-complement CS lanes. Mirrors
    `src/keccak.rs::keccak_f1600`. -/
def optimized_f1600 (rcTable : List Nat) (s : State) : State :=
  applyMask CS_mask
    (rcTable.foldl (fun s' rc => optimized_round rc s') (applyMask CS_mask s))

/-- **Soundness theorem**: the Bertoni-optimized impl computes the
    canonical FIPS-202 Keccak-f[1600] for any state with `< 2^64` lanes
    and any 24-element round-constant table of `< 2^64` values. -/
theorem optimized_eq_canonical (rcTable : List Nat)
    (hrc : ∀ rc ∈ rcTable, rc < 2 ^ 64) (s : State) (h : ∀ i, s i < 2 ^ 64) :
    optimized_f1600 rcTable s = Keccakf1600.f1600 rcTable s := by
  unfold optimized_f1600 Keccakf1600.f1600
  rw [optimized_rounds_eq_canonical_rounds rcTable hrc s h]
  rw [applyMask_xor_self]

end Falcon512.Spec.KeccakOptimized

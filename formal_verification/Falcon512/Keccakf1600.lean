/-
  Falcon512.Keccakf1600 — Canonical FIPS-202 Keccak-f[1600] in Lean.

  This file models the canonical (non-optimized) Keccak-f[1600] permutation
  per FIPS-202 §3.2 — theta, rho, pi, chi, iota over the 25-lane state.
  It is the Lean counterpart to the reference function `keccak_f1600_ref`
  in `src/keccak.rs::tests`.

  The optimized `keccak_f1600` in `src/keccak.rs` (Bertoni lane-complementing
  + chi-row, ~456 NOTs eliminated per 24-round permute) is a separate
  Lean target (`Falcon512.KeccakBertoni`, depends on this file).

  ┌──────────────────────────────────────────────────────────────────┐
  │ CONTENTS                                                         │
  ├──────────────────────────────────────────────────────────────────┤
  │ Definitions:                                                     │
  │   theta, rho, pi, chi, iota, round, f1600                        │
  │   laneIdx (FIPS-202 §B.1 (x,y) ↔ 5y+x), rotL64, piInv            │
  │                                                                  │
  │ Structural lemmas (all proven, no sorries):                      │
  │ §1  theta_linear        — θ is XOR-linear (via rotL64_xor +      │
  │                           Nat.shiftLeft_xor_distrib + ac_rfl)    │
  │ §2  iota_only_lane_0    — ι touches only lane 0 (case split)     │
  │ §3  rho_in_place        — ρ rotates each lane in place (rfl)     │
  │ §4  pi_left_inverse     — piInv ∘ π = id (Fin 25 case analysis)  │
  │ §5  f1600_unfold        — f1600 = foldl round (rfl)              │
  └──────────────────────────────────────────────────────────────────┘

  The ≡ FIPS-202 §3.2 contract is asserted by definition: the
  array-form `theta`/`rho`/`pi`/`chi`/`iota` here are the §B.1
  little-endian-within-lane realization of the §3.2.1–§3.2.5 bit-cube
  operations. Cross-checking against the §3.2 bit-cube form (a separate
  modeling effort, ~200 more lines) is out of scope for this file.

  Operational counterpart: `src/keccak.rs::tests::
  optimized_keccak_f1600_matches_clean_reference` runs 1024 random states
  through both this canonical reference and the optimized Bertoni-form
  impl in `src/keccak.rs`.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Falcon512.Defs

namespace Falcon512.Spec.Keccakf1600

open Finset

/-! ## State representation

A Keccak-f[1600] state is 25 lanes of 64 bits each. We use `Nat` for the
lane representation (rather than `BitVec 64` or `UInt64`) for two reasons:

  1. The structural lemmas below (`theta_linear`, `pi_permutation`, …)
     are about *which lane goes where*, not about bit-level identities;
     `Nat`-typed lanes keep the proof obligations XOR-and-rotate
     algebra rather than `BitVec` cast manipulation.
  2. The Rust impl uses `u64`; `Nat` with implicit `% 2^64` discipline
     matches the wrap-around semantics on overflow-free operations
     (XOR, rotate) without modeling overflow explicitly.

Each lane is opaquely a 64-bit value; we never appeal to its structure
beyond XOR (`HXor` on Nat) and rotation. -/

/-- A Keccak-f[1600] state: 25 lanes. The (x, y) ↔ index correspondence
    follows FIPS-202 §B.1: index = 5·y + x for `x, y ∈ [0, 5)`. -/
abbrev State : Type := Fin 25 → Nat

/-- FIPS-202 §B.1 lane index for column `x` and row `y`. -/
def laneIdx (x y : Fin 5) : Fin 25 :=
  ⟨5 * y.val + x.val, by have := x.isLt; have := y.isLt; omega⟩

/-- 64-bit left-rotation by `n` bits, where `n ∈ [0, 64)`. Uses XOR
    instead of OR for the halves; on u64-bounded lanes the two halves
    don't overlap so OR ≡ XOR there, but the XOR form is provably
    distributive over input XOR (`shiftLeft_xor_distrib` +
    `xor_mod_two_pow` from core Lean) — needed for `theta_linear`. -/
def rotL64 (lane n : Nat) : Nat :=
  ((lane <<< n) ^^^ (lane >>> (64 - n))) % (2 ^ 64)

/-- FIPS-202 ρ rotation offsets, indexed by `[x][y]`. Matches the
    `RHO` constant in `src/keccak.rs::tests::keccak_f1600_ref`. -/
def rhoOffset (x y : Fin 5) : Nat :=
  match x.val, y.val with
  | 0, 0 => 0  | 0, 1 => 36 | 0, 2 => 3  | 0, 3 => 41 | 0, 4 => 18
  | 1, 0 => 1  | 1, 1 => 44 | 1, 2 => 10 | 1, 3 => 45 | 1, 4 => 2
  | 2, 0 => 62 | 2, 1 => 6  | 2, 2 => 43 | 2, 3 => 15 | 2, 4 => 61
  | 3, 0 => 28 | 3, 1 => 55 | 3, 2 => 25 | 3, 3 => 21 | 3, 4 => 56
  | 4, 0 => 27 | 4, 1 => 20 | 4, 2 => 39 | 4, 3 => 8  | 4, 4 => 14
  | _, _ => 0  -- unreachable given Fin 5 × Fin 5

/-! ## §3.2.x operations

Each follows FIPS-202 §3.2.{1..5} in array form. -/

/-- §3.2.1 θ (theta): column-parity XOR + rotate-left-by-1. -/
def theta (s : State) : State := fun i =>
  let x : Fin 5 := ⟨i.val % 5, by omega⟩
  let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
  let xm1 : Fin 5 := ⟨(x.val + 4) % 5, by omega⟩
  let xp1 : Fin 5 := ⟨(x.val + 1) % 5, by omega⟩
  let cLeft  := s (laneIdx xm1 ⟨0, by decide⟩) ^^^ s (laneIdx xm1 ⟨1, by decide⟩)
              ^^^ s (laneIdx xm1 ⟨2, by decide⟩) ^^^ s (laneIdx xm1 ⟨3, by decide⟩)
              ^^^ s (laneIdx xm1 ⟨4, by decide⟩)
  let cRight := s (laneIdx xp1 ⟨0, by decide⟩) ^^^ s (laneIdx xp1 ⟨1, by decide⟩)
              ^^^ s (laneIdx xp1 ⟨2, by decide⟩) ^^^ s (laneIdx xp1 ⟨3, by decide⟩)
              ^^^ s (laneIdx xp1 ⟨4, by decide⟩)
  s (laneIdx x y) ^^^ cLeft ^^^ rotL64 cRight 1

/-- §3.2.2 ρ (rho): per-lane left-rotation by `rhoOffset[x][y]`. -/
def rho (s : State) : State := fun i =>
  let x : Fin 5 := ⟨i.val % 5, by omega⟩
  let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
  rotL64 (s i) (rhoOffset x y)

/-- §3.2.3 π (pi): lane permutation `(x, y) ↦ (y, (2x + 3y) % 5)`. -/
def pi (s : State) : State := fun i =>
  let x : Fin 5 := ⟨i.val % 5, by omega⟩
  let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
  let xSrc : Fin 5 := y
  let ySrc : Fin 5 := ⟨(2 * x.val + 3 * y.val) % 5, by omega⟩
  -- π(s)[x, y] = s[xSrc, ySrc] where (xSrc, ySrc) is chosen so the
  -- inverse permutation is `(x', y') ↦ (y, 2x + 3y)`. The match here is
  -- the convention used in `keccak_f1600_ref`.
  s (laneIdx xSrc ySrc)

/-- §3.2.4 χ (chi): row-wise nonlinear `b ⊕ ((¬c) ∧ d)`. -/
def chi (s : State) : State := fun i =>
  let x : Fin 5 := ⟨i.val % 5, by omega⟩
  let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
  let x1 : Fin 5 := ⟨(x.val + 1) % 5, by omega⟩
  let x2 : Fin 5 := ⟨(x.val + 2) % 5, by omega⟩
  let mask : Nat := 2 ^ 64 - 1
  let notB := (mask - s (laneIdx x1 y) % (2 ^ 64))   -- bitwise NOT under 64-bit mask
  s (laneIdx x y) ^^^ (notB &&& s (laneIdx x2 y))

/-- §3.2.5 ι (iota): XOR round constant `rc` into lane (0, 0). All other
    lanes are unchanged. -/
def iota (rc : Nat) (s : State) : State := fun i =>
  if i.val = 0 then s i ^^^ rc else s i

/-- One full Keccak-f[1600] round. The order is θ, ρ, π, χ, ι. -/
def round (rc : Nat) (s : State) : State :=
  iota rc (chi (pi (rho (theta s))))

/-- Twenty-four-fold composition: `f1600 s = round rc[23] ∘ … ∘ round rc[0]`,
    where `rc` is the 24-element FIPS-202 round-constant table. -/
def f1600 (rcTable : List Nat) (s : State) : State :=
  rcTable.foldl (fun s' rc => round rc s') s

/-! ## Structural rungs (Aristotle targets) -/

/-- `rotL64` distributes over `^^^` on its lane argument. Follows from
    `Nat.shiftLeft_xor_distrib`, `Nat.shiftRight_xor_distrib`, and
    `Nat.xor_mod_two_pow` (mod by `2^64` distributes over XOR since the
    `mod` is a bit-mask). -/
theorem rotL64_xor (a b n : Nat) :
    rotL64 (a ^^^ b) n = rotL64 a n ^^^ rotL64 b n := by
  unfold rotL64
  rw [Nat.shiftLeft_xor_distrib, Nat.shiftRight_xor_distrib]
  rw [show (a <<< n ^^^ b <<< n) ^^^ (a >>> (64 - n) ^^^ b >>> (64 - n)) =
        (a <<< n ^^^ a >>> (64 - n)) ^^^ (b <<< n ^^^ b >>> (64 - n))
        from by rw [Nat.xor_assoc, ← Nat.xor_assoc (b <<< n),
                    Nat.xor_comm (b <<< n), Nat.xor_assoc, ← Nat.xor_assoc]]
  exact Nat.xor_mod_two_pow

/-- §1. **θ is XOR-linear.** Bitwise XOR distributes through θ:
    `theta (s ⊕ t) i = theta s i ⊕ theta t i` for every lane index `i`.

    Proof: unfold θ on both sides, observe that the column parities `cLeft`
    and `cRight` are 5-fold XORs (so they distribute over per-lane XOR by
    `Nat.xor_assoc` / `xor_comm`), and `rotL64` distributes by
    `rotL64_xor` above. The remaining XOR rearrangement is bookkeeping. -/
theorem theta_linear (s t : State) :
    ∀ i, theta (fun j => s j ^^^ t j) i = theta s i ^^^ theta t i := by
  intro i
  simp only [theta, rotL64_xor]
  ac_rfl

/-- §2. **ι touches only lane (0, 0).** For any `i ≠ 0`, `iota rc s i = s i`. -/
theorem iota_only_lane_0 (rc : Nat) (s : State) (i : Fin 25) (h : i.val ≠ 0) :
    iota rc s i = s i := by
  unfold iota; simp [h]

/-- §3. **ρ rotates each lane in place.** For each index `i`, the resulting
    lane is `rotL64 (s i) (rhoOffset x y)` — no lane moves to a different
    index. -/
theorem rho_in_place (s : State) (i : Fin 25) :
    let x : Fin 5 := ⟨i.val % 5, by omega⟩
    let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
    rho s i = rotL64 (s i) (rhoOffset x y) := by
  rfl

/-- The inverse of FIPS-202 π. The matrix M = [[0,1],[2,3]] over ℤ/5
    has det 3, inverse 2, and adj M = [[3,4],[3,0]], giving
    M⁻¹ = 2·adj M = [[1,3],[1,0]] (mod 5). So
    π⁻¹: (x, y) ↦ ((x + 3y) % 5, x). -/
def piInv (s : State) : State := fun i =>
  let x : Fin 5 := ⟨i.val % 5, by omega⟩
  let y : Fin 5 := ⟨i.val / 5, by have := i.isLt; omega⟩
  let xSrc : Fin 5 := ⟨(x.val + 3 * y.val) % 5, by omega⟩
  let ySrc : Fin 5 := x
  s (laneIdx xSrc ySrc)

/-- §4. **π is a permutation.** `piInv` is a left inverse of `pi`. The
    proof is by case analysis on `Fin 25`: each of the 25 lane indices
    reduces to a concrete arithmetic identity `(2*((x + 3y) % 5) + 3x) % 5 = y`
    for the corresponding `(x, y)`, which closes by `decide`. -/
theorem pi_left_inverse (s : State) : piInv (pi s) = s := by
  funext i
  fin_cases i <;> rfl

/-- §5. **f1600 unfolds to 24 successive rounds.** Trivially true by
    definition; this lemma is the convenient elimination form for
    inducting over the round-constant list. -/
theorem f1600_unfold (rcTable : List Nat) (s : State) :
    f1600 rcTable s = rcTable.foldl (fun s' rc => round rc s') s := by
  rfl

end Falcon512.Spec.Keccakf1600

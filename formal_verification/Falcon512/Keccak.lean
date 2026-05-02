/-
  Falcon512.Keccak — FIPS-202 reference math for Falcon-512's SHAKE-256.

  Falcon-512 uses SHAKE-256 only as an opaque XOF inside `hash_to_point`.
  This module's role is narrow: state the structural facts the Rust
  implementation in `src/keccak.rs` relies on, in our specific setting.

  ┌──────────────────────────────────────────────────────────────────┐
  │ TARGETS                                                          │
  ├──────────────────────────────────────────────────────────────────┤
  │ §1  absorb_nil           — `absorb [] s = s` (trivial smoke test)│
  │ §2  absorb_singleton     — single-byte step matches direct xor   │
  │ §3  absorb_append        — `absorb (a ++ b) s = absorb b (absorb a s)`
  │                            (sponge associativity over ‖)         │
  └──────────────────────────────────────────────────────────────────┘

  The model abstracts the permutation as an opaque `π : State → State`,
  matching the `keccak_f1600` boundary in the Rust impl. Equivalence of
  the optimized `keccak_f1600` (Bertoni lane-complementing + chi-row) with
  the FIPS-202 reference is checked operationally in
  `src/keccak.rs::tests::optimized_keccak_f1600_matches_clean_reference` —
  symbolic 1600-bit equivalence is out of scope, mirroring the
  textbook-math division in `Falcon512.lean`.

  Operational counterpart in Rust: `src/codec.rs::adversarial::
  shake_absorb_chunk_boundaries` exercises `absorb_append` on random
  inputs across 500 iterations and 10 split points.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Defs

namespace Falcon512.Spec.Keccak

/-! ## Abstract sponge state

The Rust `Shake256` struct holds `state : [u64; 25]` plus `pos : usize`.
We model the same shape with `Nat` everywhere — the algebraic facts we
care about don't depend on word size, only on the rate-boundary discipline.

  • `inner` stands for the 1600-bit Keccak state (any type works since the
    permutation is opaque here).
  • `pos` is the byte offset into the rate, in `[0, RATE)`.

The injection of one input byte into the state is also opaque (`xorByte`):
its only structural property the proofs need is that distinct calls don't
collide — and even that isn't needed for the associativity-shaped facts
below, which are pure list-induction. -/

/-- SHAKE-256 rate in bytes, from FIPS-202 §6.2: `(1600 - 512) / 8 = 136`. -/
def RATE : Nat := 136

/-- Abstract sponge state. `inner` is the Keccak-f[1600] state (left
    polymorphic via a fixed opaque type below); `pos` is the byte offset
    into the rate. -/
structure SpongeState where
  inner : Nat   -- abstract — any type; Nat is convenient for `decide`
  pos   : Nat
  deriving Repr, DecidableEq

/-- The opaque Keccak-f[1600] permutation. We never unfold it — every
    proof in this file is structural over byte input, not over the
    permutation's internals. -/
opaque permute : Nat → Nat

/-- Byte injection at a rate offset. Opaque for the same reason as
    `permute`: the structural lemmas below don't probe its bits. -/
opaque xorByte : Nat → Nat → Nat → Nat

/-- One step of `absorb` on a single byte. Mirrors the Rust loop body in
    `src/keccak.rs::Shake256::absorb` (modulo the byte-vs-lane bulk
    optimization, which preserves this shape — that equivalence is the
    operational claim of `shake_absorb_chunk_boundaries`). -/
def absorbByte (b : UInt8) (s : SpongeState) : SpongeState :=
  let inner' := xorByte s.inner s.pos b.toNat
  let pos'   := s.pos + 1
  if pos' = RATE then
    { inner := permute inner', pos := 0 }
  else
    { inner := inner', pos := pos' }

/-- Absorb a byte stream by folding `absorbByte` left-to-right. Mirrors
    the per-byte semantics of the Rust `absorb`; the bulk-lane and tail
    phases of the Rust code are operationally equivalent (`Phase 1/2/3`
    in `src/keccak.rs`) and verified by the `shake_absorb_chunk_boundaries`
    proptest. -/
def absorb : List UInt8 → SpongeState → SpongeState
  | [],      s => s
  | b :: bs, s => absorb bs (absorbByte b s)

/-! ## §1–§3. Theorems -/

/-- §1. Empty input is the identity. Smoke test for the toolchain wiring. -/
theorem absorb_nil (s : SpongeState) : absorb [] s = s := by
  sorry

/-- §2. Single-byte absorb is exactly one `absorbByte`. Step lemma used
    by the associativity proof. -/
theorem absorb_singleton (b : UInt8) (s : SpongeState) :
    absorb [b] s = absorbByte b s := by
  sorry

/-- §3. **Sponge absorb is associative over byte concatenation.**

    `absorb (a ++ b) s = absorb b (absorb a s)`

    This is the mathematical content of the Rust comment

      ```rust
      /// `absorb(a) + absorb(b) == absorb(a||b)` (Phase 1/2/3 of the
      /// 3-phase byte-vs-lane optimization)
      ```

    and the operational counterpart of the `shake_absorb_chunk_boundaries`
    proptest. Proof: induction on `a`. -/
theorem absorb_append (a b : List UInt8) (s : SpongeState) :
    absorb (a ++ b) s = absorb b (absorb a s) := by
  sorry

/-- Convenience: chunked absorb sequence equals one absorb of the join. -/
theorem absorb_concat (chunks : List (List UInt8)) (s : SpongeState) :
    absorb chunks.flatten s = chunks.foldl (fun s' c => absorb c s') s := by
  sorry

end Falcon512.Spec.Keccak

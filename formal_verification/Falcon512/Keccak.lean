/-
  Falcon512.Keccak — FIPS-202 reference math for Falcon-512's SHAKE-256.

  Falcon-512 uses SHAKE-256 only as an opaque XOF inside `hash_to_point`.
  This module's role is narrow: state the structural facts the Rust
  implementation in `src/keccak.rs` relies on, in our specific setting.

  ┌──────────────────────────────────────────────────────────────────┐
  │ TARGETS                                                          │
  ├──────────────────────────────────────────────────────────────────┤
  │ Absorb associativity (sponge, opaque permutation):               │
  │ §1  absorb_nil           — `absorb [] s = s` (trivial smoke test)│
  │ §2  absorb_singleton     — single-byte step matches direct xor   │
  │ §3  absorb_append        — `absorb (a ++ b) s = absorb b (absorb a s)`
  │                            (sponge associativity over ‖)         │
  │                                                                  │
  │ FIPS-202 contract validation (literal bit-level checks):         │
  │ §4  rc_matches_fips202   — RC[24] ≡ §3.2.5 LFSR (native_decide)  │
  │ §5  shake_pad_bits       — domain suffix 0x1f / final 0x80       │
  │                            realize pad10*1 + suffix `1111`       │
  │ §6  lane_byte_eq_squeeze — byte b of lane l = (lane>>8b) & 0xff  │
  │                            (FIPS-202 §B.1 lane LE encoding)      │
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
import Mathlib.Data.Nat.Basic

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
  rfl

/-- §2. Single-byte absorb is exactly one `absorbByte`. Step lemma used
    by the associativity proof. -/
theorem absorb_singleton (b : UInt8) (s : SpongeState) :
    absorb [b] s = absorbByte b s := by
  rfl

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
  induction a generalizing s with
  | nil => rfl
  | cons x xs ih => simp [absorb, ih]

/-- Convenience: chunked absorb sequence equals one absorb of the join. -/
theorem absorb_concat (chunks : List (List UInt8)) (s : SpongeState) :
    absorb chunks.flatten s = chunks.foldl (fun s' c => absorb c s') s := by
  induction chunks generalizing s with
  | nil => rfl
  | cons c cs ih => simp [List.flatten, absorb_append, ih]

/-! ## §4. FIPS-202 §3.2.5 round-constant LFSR

The 24 round constants of Keccak-f[1600] are derived from a single 8-bit
LFSR seeded at `0x01`. For each round `i ∈ [0, 24)`, the next 7 LFSR bits
are deposited at lane positions `2^j - 1` for `j ∈ [0, 7)`.

The construction below mirrors `keccak_lfsr_next_bit` and
`spec_round_constants` in `src/keccak.rs::tests` byte-for-byte. The
hard-coded `RC` table at the top of `src/keccak.rs` is then a literal
`native_decide` against the spec construction. -/

/-- One step of the FIPS-202 LFSR over an 8-bit state. Returns the output
    bit (LSB of `r`) and the next state. Polynomial reflects
    `r := (r << 1) XOR 0x71` when the high bit is set. -/
def lfsrStep (r : Nat) : Bool × Nat :=
  let bit := r % 2 = 1
  let shifted := (2 * r) % 256
  let r' := if r / 128 % 2 = 1 then shifted ^^^ 0x71 else shifted
  (bit, r')

/-- Run `n` LFSR steps from state `r`, returning the final state. -/
def lfsrAdvance (r : Nat) : Nat → Nat
  | 0 => r
  | n + 1 => lfsrAdvance (lfsrStep r).2 n

/-- The FIPS-202 spec round constant for round `i ∈ [0, 24)`. Takes the
    LFSR state at `7*i` steps past the seed `0x01`, draws 7 fresh bits,
    and deposits each at lane position `2^j - 1`. -/
def specRC (i : Nat) : Nat :=
  let r0 := lfsrAdvance 0x01 (7 * i)
  let (b0, r1) := lfsrStep r0
  let (b1, r2) := lfsrStep r1
  let (b2, r3) := lfsrStep r2
  let (b3, r4) := lfsrStep r3
  let (b4, r5) := lfsrStep r4
  let (b5, r6) := lfsrStep r5
  let (b6, _)  := lfsrStep r6
  (if b0 then 1 else 0) ^^^
  (if b1 then 2 else 0) ^^^
  (if b2 then 8 else 0) ^^^
  (if b3 then 128 else 0) ^^^
  (if b4 then 32768 else 0) ^^^
  (if b5 then 1 <<< 31 else 0) ^^^
  (if b6 then 1 <<< 63 else 0)

/-- Hard-coded `RC[24]` table, copied verbatim from `src/keccak.rs::RC`.
    The whole point of §4 is to verify this table against `specRC`. -/
def rustRC : List Nat :=
  [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

/-- §4. **Hard-coded `RC` table matches the FIPS-202 §3.2.5 LFSR derivation.**
    Closed by `native_decide`: the LFSR runs 24·7 = 168 steps, each
    constant deposits 7 bits, table comparison is finite. -/
theorem rc_matches_fips202 :
    rustRC = (List.range 24).map specRC := by
  native_decide

/-! ## §5. SHAKE-256 padding bit-pattern

FIPS-202 §6.2 defines SHAKE-256 with domain suffix `1111` followed by the
multi-rate-padding `pad10*1`. Within the byte-stream representation
(LSB-first within each byte per §B.1), this realizes:

  • At bit-position `pos` of the rate (where the input ends): five
    consecutive 1-bits — the four-bit suffix `1111` plus the leading `1`
    of `pad10*1`. LSB-first this is the byte `0b00011111 = 0x1f`.
  • At bit-position `8·RATE - 1` (the last bit of the rate): one 1-bit —
    the closing `1` of `pad10*1`. LSB-first within byte 16, bit 7, that's
    `0x80`.

`SHAKE256_DOMAIN_SUFFIX` and `SHAKE256_FINAL_RATE_BIT` in `src/keccak.rs`
are literally these two byte values. -/

/-- LSB-first bit `b ∈ [0, 8)` of a byte. -/
def bitAt (byte b : Nat) : Bool := byte / 2 ^ b % 2 = 1

/-- §5a. The byte `0x1f` realizes the LSB-first pattern `1,1,1,1,1,0,0,0`
    — i.e., bits 0..4 set (the SHAKE domain suffix `1111` + the pad10*1
    leading `1`), bits 5..7 clear. -/
theorem shake_suffix_byte :
    ∀ b : Fin 8, bitAt 0x1f b.val = (b.val < 5) := by
  decide

/-- §5b. The byte `0x80` realizes the LSB-first pattern `0,0,0,0,0,0,0,1`
    — i.e., bit 7 set (the pad10*1 closing `1` at the last bit of the
    rate), bits 0..6 clear. -/
theorem shake_final_byte :
    ∀ b : Fin 8, bitAt 0x80 b.val = (b.val = 7) := by
  decide

/-! ## §6. Lane-byte ≡ rate_lanes squeeze

FIPS-202 §B.1 specifies that within each 64-bit lane, the bytes are laid
out little-endian: byte at offset `b ∈ [0, 8)` of lane `l` equals
`(state[l] >>> (8·b)) & 0xff`.

The Rust impl uses two byte-extraction shapes:
  • `Shake256::squeeze` reads byte `(state[pos/8] >>> (8·(pos%8)))` and
    advances `pos` by one — direct per-byte form.
  • `Shake256::rate_lanes` exposes the first 17 lanes; `hash_to_point`
    extracts four big-endian u16 candidates per lane via
    `lane.to_le_bytes()`, which is the same byte order as the per-byte
    squeeze on the same `pos` range.

The spec version of both is the same function — this is the FIPS-202
contract for any code that mixes the two forms. -/

/-- Byte at offset `b` of an integer lane `lane`, FIPS-202 §B.1
    little-endian-within-lane. -/
def laneByte (lane : Nat) (b : Nat) : Nat := (lane / 2 ^ (8 * b)) % 256

/-- §6a. `laneByte` is bounded < 256. -/
theorem lane_byte_lt_256 (lane : Nat) (b : Nat) : laneByte lane b < 256 := by
  unfold laneByte
  exact Nat.mod_lt _ (by decide)

/-- §6b. **Per-byte squeeze ≡ direct lane-byte extract** at the FIPS-202
    abstraction layer. Both the per-byte form `(state[pos/8] >> (8·(pos%8)))`
    used by `Shake256::squeeze` and the per-lane LE-byte form used by
    `hash_to_point` (via `rate_lanes()` + `lane.to_le_bytes()`) reduce to
    the same `laneByte` function. The equality is therefore definitional;
    the Rust-level claim that the optimized lane-extract path in
    `hash_to_point` agrees with the per-byte squeeze is the operational
    counterpart, exercised by
    `src/codec.rs::adversarial::hash_to_point_matches_per_byte_squeeze_random`. -/
theorem squeeze_eq_lane_byte (state : Nat → Nat) (pos : Nat) :
    (state (pos / 8) / 2 ^ (8 * (pos % 8))) % 256 =
      laneByte (state (pos / 8)) (pos % 8) := rfl

end Falcon512.Spec.Keccak

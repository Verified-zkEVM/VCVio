/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.Ring.Kernel

/-!
# Rounding And Decomposition For Negacyclic Rings

Abstract rounding and decomposition interfaces for lattice signature schemes,
parameterized by a `NegacyclicRing`. Defines:

- `RoundingOps`: the ML-DSA-style high/low-bit decomposition and hint
  mechanism, parameterized by a rounding modulus `α` (typically `2 · γ₂`).
- `Power2RoundOps`: the power-of-two rounding used for ML-DSA public-key
  compression, parameterized by the number of dropped bits `d`.
- `RoundingOps.Laws` / `Power2RoundOps.Laws`: algebraic correctness
  properties (decomposition identity, norm bounds, hint injectivity).

Concrete implementations live in `MLDSA.Concrete.Rounding`. The abstract
interfaces are consumed by `MLDSA.Scheme` and `MLDSA.Signature`.
-/

@[expose] public section


namespace LatticeCrypto

universe u v

/-- Abstract rounding operations on a `NegacyclicRing`, parameterized by a
rounding modulus `α` (typically `2 · γ₂` in the ML-DSA specification).

Bundles the `highBits` / `lowBits` decomposition, the `shift` embedding,
and the `makeHint` / `useHint` pair used by ML-DSA signing and verification
to recover `w₁` from a hint vector. -/
structure RoundingOps {Coeff : Type u} [CommRing Coeff]
    (ring : NegacyclicRing Coeff) (α : ℕ) where
  /-- The type of high-order parts, returned by `highBits` and `useHint`. -/
  High : Type v
  /-- The type of hints produced by `makeHint`. -/
  Hint : Type v
  /-- `LowBits` (FIPS 204 Algorithm 38): the low-order part of a polynomial with respect to
  `α`. -/
  lowBits : ring.Poly → ring.Poly
  /-- `HighBits` (FIPS 204 Algorithm 37): the high-order part of a polynomial with respect to
  `α`. -/
  highBits : ring.Poly → High
  /-- Embed a high-order part back into the ring as the matching multiple of `α`, so that
  `shift (highBits r) + lowBits r = r`. -/
  shift : High → ring.Poly
  /-- `MakeHint` (FIPS 204 Algorithm 39): from `z` and `r`, the hint recording where adding `z`
  to `r` changes the high-order part. -/
  makeHint : ring.Poly → ring.Poly → Hint
  /-- `UseHint` (FIPS 204 Algorithm 40): from the hint for `z` and from `r`, recover the
  high-order part of `r + z`. -/
  useHint : Hint → ring.Poly → High

/-- Abstract power-2 rounding operations, parameterized by the number of dropped bits `d`. -/
structure Power2RoundOps {Coeff : Type*} [CommRing Coeff]
    (ring : NegacyclicRing Coeff) (d : ℕ) where
  /-- The type of high-order parts produced by `power2Round`. -/
  Power2High : Type*
  /-- `Power2Round` (FIPS 204 Algorithm 35), keeping the high-order part `t₁` of a polynomial
  after its `d` low-order bits are dropped. -/
  power2Round : ring.Poly → Power2High
  /-- Embed a high-order part `t₁` back into the ring as `t₁ · 2^d`. -/
  shift2 : Power2High → ring.Poly

/-- Algebraic laws for `RoundingOps`. -/
structure RoundingOps.Laws {Coeff : Type*} [CommRing Coeff]
    {ring : NegacyclicRing Coeff} [AddCommGroup ring.Poly]
    {α : ℕ} (ops : RoundingOps ring α) (cInfNorm : ring.Poly → ℕ) : Prop where
  high_low_decomp : ∀ x : ring.Poly, ops.shift (ops.highBits x) + ops.lowBits x = x
  lowBits_bound : ∀ r : ring.Poly, cInfNorm (ops.lowBits r) ≤ α / 2
  hide_low : ∀ (r s : ring.Poly) (b : ℕ),
    cInfNorm s ≤ b → cInfNorm (ops.lowBits r) + b < α / 2 →
    ops.highBits (r + s) = ops.highBits r
  shift_injective : Function.Injective ops.shift
  useHint_correct : ∀ (z r : ring.Poly),
    cInfNorm z ≤ α / 2 →
    ops.useHint (ops.makeHint z r) r = ops.highBits (r + z)
  useHint_bound : ∀ (r : ring.Poly) (h : ops.Hint),
    cInfNorm (r - ops.shift (ops.useHint h r)) ≤ α + 1

/-- Algebraic laws for `Power2RoundOps`. -/
structure Power2RoundOps.Laws {Coeff : Type*} [CommRing Coeff]
    {ring : NegacyclicRing Coeff} [AddCommGroup ring.Poly]
    {d : ℕ} (ops : Power2RoundOps ring d) (cInfNorm : ring.Poly → ℕ) : Prop where
  power2Round_bound : ∀ r : ring.Poly,
    cInfNorm (r - ops.shift2 (ops.power2Round r)) ≤ 2 ^ (d - 1)

end LatticeCrypto

/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.Data.LawfulXor.Basic

/-!
# Universal hash families

A keyed hash family is a map `hash : K → D → T`; write `h_k := hash k`. Throughout, the key is
drawn uniformly, `k ←$ K`, and `Pr_k[E k]` denotes `Pr{let k ← $ᵗ K}[E k]`. For `ε : ℝ≥0∞`:

* `hash` is *`ε`-almost-universal* (`ε`-AU) if
  `∀ x y : D, x ≠ y → Pr_k[h_k x = h_k y] ≤ ε`;
* `hash` is *`ε`-almost-XOR-universal* (`ε`-AXU) if
  `∀ x y : D, x ≠ y → ∀ Δ : T, Pr_k[h_k x ⊕ h_k y = Δ] ≤ ε`.

## Main Definitions

- `IsAlmostUniversal hash ε`: `hash` is `ε`-AU.
- `IsAlmostXorUniversal hash ε`: `hash` is `ε`-AXU.

## Main Results

- `IsAlmostXorUniversal.isAlmostUniversal`: if `a ⊕ b = 0 ↔ a = b` on `T`, every `ε`-AXU family
  is `ε`-AU.
- `IsAlmostXorUniversal.card_inv_le`: if `hash` is `ε`-AXU, `T` is finite and `D` has two distinct
  elements, then `|T|⁻¹ ≤ ε`.
- `isAlmostXorUniversal_div_card_iff`: for finite `K` and `d : ℕ`, `hash` is `(d / |K|)`-AXU iff
  `#{k : K | h_k x ⊕ h_k y = Δ} ≤ d` for all `x ≠ y` and all `Δ`;
  `isAlmostXorUniversal_of_card_le` is the `←` direction.

## References

* J. L. Carter, M. N. Wegman, *Universal classes of hash functions*, J. Comput. Syst. Sci. 18
  (1979).
* H. Krawczyk, *LFSR-based hashing and authentication*, CRYPTO '94.
-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace UniversalHash

variable {K D T : Type}

/-- `hash : K → D → T` is `ε`-almost-universal if distinct inputs collide with probability at
most `ε` over a uniform key:

`∀ x y : D, x ≠ y → Pr_{k ←$ K}[hash k x = hash k y] ≤ ε`.

For `ε = |T|⁻¹` this is a universal class in the sense of Carter and Wegman. -/
@[expose] def IsAlmostUniversal [SampleableType K] (hash : K → D → T) (ε : ℝ≥0∞) : Prop :=
  ∀ x y : D, x ≠ y → Pr{let k ← $ᵗ K}[hash k x = hash k y] ≤ ε

/-- `hash : K → D → T` is `ε`-almost-XOR-universal (AXU) if, for distinct inputs, every XOR
difference of their hashes has probability at most `ε` over a uniform key:

`∀ x y : D, x ≠ y → ∀ Δ : T, Pr_{k ←$ K}[hash k x ⊕ hash k y = Δ] ≤ ε`.

Both hashes use the same key `k`, and `Δ` is quantified before `k` is drawn, so it cannot depend
on `k`. -/
@[expose] def IsAlmostXorUniversal [SampleableType K] [XorOp T]
    (hash : K → D → T) (ε : ℝ≥0∞) : Prop :=
  ∀ x y : D, x ≠ y → ∀ Δ : T, Pr{let k ← $ᵗ K}[hash k x ^^^ hash k y = Δ] ≤ ε

namespace IsAlmostXorUniversal

/-- `ε`-AXU implies `ε`-AU when `a ⊕ b = 0 ↔ a = b` (`LawfulXor`): the collision event
`hash k x = hash k y` is the difference event for `Δ = 0`. -/
theorem isAlmostUniversal [SampleableType K] [XorOp T] [Zero T] [LawfulXor T]
    {hash : K → D → T} {ε : ℝ≥0∞} (h : IsAlmostXorUniversal hash ε) :
    IsAlmostUniversal hash ε := fun x y hxy => by
  simpa only [xor_eq_zero_iff] using h x y hxy 0

/-- If `hash` is `ε`-AXU, `T` is finite and `x ≠ y` in `D`, then `|T|⁻¹ ≤ ε`.

The events `{k | hash k x ⊕ hash k y = Δ}` for `Δ : T` partition `K`, so

`1 = ∑ Δ : T, Pr_{k ←$ K}[hash k x ⊕ hash k y = Δ] ≤ |T| · ε`.

The hypothesis `x ≠ y` is needed: if `D` is a subsingleton, every family is `0`-AXU. -/
theorem card_inv_le [SampleableType K] [XorOp T] [Fintype T]
    {hash : K → D → T} {ε : ℝ≥0∞} (h : IsAlmostXorUniversal hash ε) {x y : D} (hxy : x ≠ y) :
    (Fintype.card T : ℝ≥0∞)⁻¹ ≤ ε := by
  let : MeasurableSpace T := ⊤
  let μ := 𝒟[(fun k => hash k x ^^^ hash k y) <$> ($ᵗ K : ProbComp K)]
  have hΔ (Δ : T) : μ {Δ} ≤ ε := by
    rw [← prEvent_eq_evalDist_singleton, prEvent_map]
    exact h x y hxy Δ
  have hone : (1 : ℝ≥0∞) ≤ Fintype.card T * ε :=
    calc (1 : ℝ≥0∞)
        = μ Set.univ := measure_univ.symm
      _ = ∑ Δ : T, μ {Δ} := by rw [sum_measure_singleton, Finset.coe_univ]
      _ ≤ ∑ _Δ : T, ε := Finset.sum_le_sum fun Δ _ => hΔ Δ
      _ = Fintype.card T * ε := by simp
  refine (ENNReal.inv_le_iff_le_mul (fun hε => ?_) (fun hT => absurd hT (natCast_ne_top _))).2
    hone
  rintro hT
  simp [hT] at hone

end IsAlmostXorUniversal

/-- Counting characterisation of AXU. For finite `K` and `d : ℕ`, `hash` is `(d / |K|)`-AXU iff

`∀ x y : D, x ≠ y → ∀ Δ : T, #{k : K | hash k x ⊕ hash k y = Δ} ≤ d`,

since under a uniform key `Pr_{k ←$ K}[E k] = #{k | E k} / |K|`. -/
theorem isAlmostXorUniversal_div_card_iff [SampleableType K] [Fintype K] [XorOp T]
    [DecidableEq T] {hash : K → D → T} {d : ℕ} :
    IsAlmostXorUniversal hash ((d : ℝ≥0∞) / Fintype.card K) ↔
      ∀ x y : D, x ≠ y → ∀ Δ : T,
        (Finset.univ.filter fun k : K => hash k x ^^^ hash k y = Δ).card ≤ d := by
  simp only [IsAlmostXorUniversal, SampleableType.prEvent_uniformSample_le_div_iff]

/-- Counting criterion for AXU: if `#{k : K | hash k x ⊕ hash k y = Δ} ≤ d` for all `x ≠ y` and
all `Δ : T`, then `hash` is `(d / |K|)`-AXU. This is the `←` direction of
`isAlmostXorUniversal_div_card_iff`. -/
theorem isAlmostXorUniversal_of_card_le [SampleableType K] [Fintype K] [XorOp T] [DecidableEq T]
    {hash : K → D → T} {d : ℕ}
    (h : ∀ x y : D, x ≠ y → ∀ Δ : T,
      (Finset.univ.filter fun k : K => hash k x ^^^ hash k y = Δ).card ≤ d) :
    IsAlmostXorUniversal hash ((d : ℝ≥0∞) / Fintype.card K) :=
  isAlmostXorUniversal_div_card_iff.2 h

end UniversalHash

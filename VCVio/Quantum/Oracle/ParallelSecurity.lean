/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Oracle.ParallelSearch
public import VCVio.Quantum.Oracle.ParallelPreimage
public import VCVio.Quantum.Oracle.ParallelPlantedPreimage
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Security bits with parallel oracle queries

`parallelQROMBound` calibrates security against adaptive oracle rounds and maximum parallel
width to the search bound. `ParallelQROMBits` is a target for a named game and its declared
adversary model: every bounded adversary must satisfy that bound. Its admissibility relation
must describe the actual resource restrictions; the concrete search corollaries use the
program's syntactic round and width bounds.

The advantage is unconditional, so failed executions count as failure. Local computation is
free. This query-model predicate does not supply a gate-cost estimate, limit retained memory,
or assert security against oracle-dependent advice. It is a conclusion to prove for the game,
rather than an oracle assumption for a downstream reduction.

## References

* `docs/quantum/reference/literature.md`, “Search-calibrated security bits”, states the
  normalization and its relation to the search and inversion theorems.
* C. Zalka, *Grover's quantum searching algorithm is optimal*, arXiv:quant-ph/9711070v2, §4.
-/

public section

open scoped ENNReal

namespace Quantum

/-- Search-calibrated success bound for `bits` security bits, `D` adaptive rounds and maximum
width `P`. The unit guessing term applies even when no points are queried. -/
@[expose]
noncomputable def parallelQROMBound (bits : ℝ) (D P : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + 2 * (D : ℝ) * Real.sqrt P) ^ 2) / ENNReal.ofReal ((2 : ℝ) ^ bits)

/-- Every adversary admitted by the named game's resource model has the search-calibrated
success bound. `IsBound adv D P` specifies at most `D` adaptive rounds of width at most `P`;
the predicate is relative to that declared model and must be established from the game's
semantics. The advantage must count failed runs without renormalizing them. -/
@[expose]
def ParallelQROMBits {Adv : Type*} (advantage : Adv → ℝ≥0∞)
    (IsBound : Adv → ℕ → ℕ → Prop) (bits : ℝ) : Prop :=
  ∀ D P adv, IsBound adv D P → advantage adv ≤ parallelQROMBound bits D P

/-- Increasing the claimed security bits decreases the calibrated success bound. -/
theorem parallelQROMBound_antitone (D P : ℕ) :
    Antitone (fun bits ↦ parallelQROMBound bits D P) := by
  intro bits bits' hbits
  exact ENNReal.div_le_div_left (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hbits)) _

/-- A security certificate also certifies any smaller number of bits under the same
admissibility predicate. -/
theorem ParallelQROMBits.mono {Adv : Type*} {advantage : Adv → ℝ≥0∞}
    {IsBound : Adv → ℕ → ℕ → Prop} {bits bits' : ℝ}
    (h : ParallelQROMBits advantage IsBound bits) (hbits : bits' ≤ bits) :
    ParallelQROMBits advantage IsBound bits' := by
  intro D P adv hadv
  exact (h D P adv hadv).trans (parallelQROMBound_antitone D P hbits)

/-- A positive denominator gives its exact base-two logarithm as the number of security bits. -/
theorem parallelQROMBound_logb (N : ℝ) (hN : 0 < N) (D P : ℕ) :
    parallelQROMBound (Real.logb 2 N) D P =
      ENNReal.ofReal ((1 + 2 * (D : ℝ) * Real.sqrt P) ^ 2) / ENNReal.ofReal N := by
  unfold parallelQROMBound
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hN]

/-- A uniform search-shaped bound with positive denominator certifies its logarithmic bits. -/
theorem parallelQROMBits_logb_of_le_div {Adv : Type*} (advantage : Adv → ℝ≥0∞)
    (IsBound : Adv → ℕ → ℕ → Prop) (N : ℝ) (hN : 0 < N)
    (h : ∀ D P adv, IsBound adv D P → advantage adv ≤
      ENNReal.ofReal ((1 + 2 * (D : ℝ) * Real.sqrt P) ^ 2) / ENNReal.ofReal N) :
    ParallelQROMBits advantage IsBound (Real.logb 2 N) := by
  intro D P adv hadv
  rw [parallelQROMBound_logb N hN]
  exact h D P adv hadv

universe u v w

variable {X : Type} [Fintype X] [DecidableEq X]
  {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- A uniformly hidden marked input has the base-two logarithm of the input-space size in
security bits. The complete adversary, including its initial state and observer, is independent
of the mark. The theorem holds for every local interpretation, substate and guessing rule. -/
theorem parallelQROMBits_markedSearch [Nonempty X] (I : L.Interp) (ρ : SubState A)
    (guess : (Σ B, W B) → X) :
    ParallelQROMBits (fun x ↦ markedSearchAdvantage I x ρ guess)
      (fun x D P ↦ x.IsTotalQueryBound D ∧ x.IsWidthBound P)
      (Real.logb 2 (Fintype.card X)) := by
  apply parallelQROMBits_logb_of_le_div _ _ (Fintype.card X) (by positivity)
  intro D P x hx
  simpa only [ENNReal.ofReal_natCast] using
    (markedSearchAdvantage_le I hx.1 hx.2 ρ guess).trans (min_le_right _ _)

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Fixed-target inversion in one uniform random function has the base-two logarithm of the
range size in security bits. The adversary may depend on the target, but is fixed independently
of the function; success is not conditioned on the target having a preimage. -/
theorem parallelQROMBits_preimageSearch (target : Y) (I : L.Interp) (ρ : SubState A)
    (guess : (Σ B, W B) → X) :
    ParallelQROMBits (fun x ↦ preimageSearchAdvantage target I x ρ guess)
      (fun x D P ↦ x.IsTotalQueryBound D ∧ x.IsWidthBound P)
      (Real.logb 2 (Fintype.card Y)) := by
  apply parallelQROMBits_logb_of_le_div _ _ (Fintype.card Y) (by positivity)
  intro D P x hx
  simpa only [ENNReal.ofReal_natCast] using
    (preimageSearchAdvantage_le target I hx.1 hx.2 ρ guess).trans (min_le_right _ _)

/-- Inverting the image of a uniform secret input has the logarithm of inverse preimage
density in security bits. Every public target may select its own complete adversary; round
and width bounds hold for all target-selected programs. -/
theorem parallelQROMBits_plantedPreimage [Nonempty X] :
    ParallelQROMBits
      (plantedPreimageAdvantage (X := X) (Y := Y) (L := L) (W := W) (A := A))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P)
      (Real.logb 2 ((ProbabilityTheory.plantedTargetDensity (X := X) (Y := Y))⁻¹)) := by
  have hρ := ProbabilityTheory.plantedTargetDensity_pos (X := X) (Y := Y)
  apply parallelQROMBits_logb_of_le_div _ _ _ (inv_pos.mpr hρ)
  intro D P adv hadv
  simpa only [ENNReal.ofReal_inv_of_pos hρ, div_eq_mul_inv, inv_inv, mul_comm] using
    (plantedPreimageAdvantage_le adv hadv.1 hadv.2).trans (min_le_right _ _)

/-- An upper bound on the planted preimage density certifies whole or fractional bits for
inverting a uniform secret input's image, under the actual syntactic round and width bounds. -/
theorem parallelQROMBits_plantedPreimage_of_density_le [Nonempty X] (bits : ℝ)
    (hρ : ProbabilityTheory.plantedTargetDensity (X := X) (Y := Y) ≤
      ((2 : ℝ) ^ bits)⁻¹) :
    ParallelQROMBits
      (plantedPreimageAdvantage (X := X) (Y := Y) (L := L) (W := W) (A := A))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P) bits := by
  intro D P adv hadv
  refine ((plantedPreimageAdvantage_le adv hadv.1 hadv.2).trans
    (min_le_right _ _)).trans ?_
  rw [parallelQROMBound, div_eq_mul_inv, mul_comm]
  apply mul_le_mul le_rfl _ bot_le bot_le
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (by norm_num) bits)]
  exact ENNReal.ofReal_le_ofReal hρ

/-- Equal input and response spaces of size `2^128` certify 127 security bits for inversion
of a uniform secret input's image. The adversary may depend on the public image. -/
theorem parallelQROMBits_plantedPreimage_127 [Nonempty X]
    (hX : Fintype.card X = 2 ^ 128) (hY : Fintype.card Y = 2 ^ 128) :
    ParallelQROMBits
      (plantedPreimageAdvantage (X := X) (Y := Y) (L := L) (W := W) (A := A))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P) 127 := by
  apply parallelQROMBits_plantedPreimage_of_density_le
  norm_num [ProbabilityTheory.plantedTargetDensity, hX, hY]

/-- Equal input and response spaces of size `2^129` certify 128 security bits for inversion
of a uniform secret input's image. The adversary may depend on the public image. -/
theorem parallelQROMBits_plantedPreimage_128 [Nonempty X]
    (hX : Fintype.card X = 2 ^ 129) (hY : Fintype.card Y = 2 ^ 129) :
    ParallelQROMBits
      (plantedPreimageAdvantage (X := X) (Y := Y) (L := L) (W := W) (A := A))
      (fun adv D P ↦ (∀ target, (adv.program target).IsTotalQueryBound D) ∧
        ∀ target, (adv.program target).IsWidthBound P) 128 := by
  apply parallelQROMBits_plantedPreimage_of_density_le
  norm_num [ProbabilityTheory.plantedTargetDensity, hX, hY]

end Quantum

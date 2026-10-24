/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Tactics

/-!
# `vcgen` on core `vcgen`

Exhaustive `vcgen` lowers an event over several draws to a triple with the indicator of the
event, hands quantitative triples to core `vcgen` with the `@[spec]` rules of the lower reading,
and closes the verification conditions that `simp` closes. Probability-one goals take the pointwise
rules and descend through every draw; fractional bounds take the exact rules and are left as
arithmetic over the averages. `vcstep` stays a single step, and `vcvio.vcgen.core` switches the
delegation off.
-/

public section

open OracleSpec OracleComp OracleComp.ProgramLogic ENNReal

namespace VCVioTest.ProgramLogic.VCGenCoreDelegation

example : Pr{let b ← $ᵗ Bool}[(b || true) = true] = 1 := by
  vcgen

example : Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b || c || true) = true] = 1 := by
  vcgen

example : (1 : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b || c || true) = true] := by
  vcgen

example (n : ℕ) : Pr{let i ← $[0..n]; let b ← $ᵗ Bool}[i.val ≤ n ∨ b = true] = 1 := by
  vcgen
  simp [Fin.is_le]

example :
    Pr{let b ← $ᵗ Bool
       let c ← (match b with | true => pure false | false => $ᵗ Bool : ProbComp Bool)}[
        (c || true) = true] = 1 := by
  vcgen

example : (4⁻¹ : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b && c) = true] := by
  vcgen
  norm_num [ENNReal.div_eq_inv_mul, Finset.filter_insert, Finset.filter_singleton,
    ← ENNReal.mul_inv]

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec]

example (t : spec.Domain) (p : spec.Range t → spec.Range t → Prop) (hp : ∀ u v, p u v) :
    Pr{let u ← (query t : OracleComp spec _)
       let v ← (query t : OracleComp spec _)}[p u v] = 1 := by
  vcgen
  simp [hp]

example {oa : OracleComp spec ι} {f : ι → OracleComp spec Bool}
    {pre : ℝ≥0∞} {cut : ι → ℝ≥0∞} {post : Bool → ℝ≥0∞}
    (hoa : Triple pre oa cut) (hob : ∀ x, Triple (cut x) (f x) post) :
    Triple pre (oa >>= f) post := by
  vcstep
  exact hob

set_option vcvio.vcgen.core false in
example : Pr{let b ← $ᵗ Bool}[(b || true) = true] = 1 := by
  vcgen
  exact triple_ofLE (by simp)

end VCVioTest.ProgramLogic.VCGenCoreDelegation

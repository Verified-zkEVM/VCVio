/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.NotationCore
public import VCVio.ProgramLogic.Unary.WP.LowerSpecs

/-!
# Probability goals on core `vcgen` alone

Probability goals closed without VCVio's tactics: the module imports none of
`VCVio.ProgramLogic.Tactics`. Each proof opens one scope of the lower reading, rewrites the event
into a triple through a bridge lemma (`triple_propInd_self_iff_prEvent_eq_one`,
`triple_propInd_self_iff_le_prEvent`, or `prEvent_eq_wp_propInd`), and calls core `vcgen` with
the `@[spec]` rules of `VCVio.ProgramLogic.Unary.WP.LowerSpecs`. Core states its verification
conditions in its own order `⊑`, read back to `≤` by `Lean.Order.rel_eq_le`.

A probability-one event takes the pointwise rules of `OracleComp.Lower.Pointwise`, and core
descends through every draw. A fractional bound takes the exact rules, and core stops at the
average of the first draw, `∑'` for `$ᵗ` and `∫⁻` for a query, with the expectation of the rest
of the program under it; the `wp` equations of `VCVio.ProgramLogic.Unary.HoareTriple`
(`OracleComp.Lower.wp_uniformSample_eq_tsum`, `wp_map`, `wp_HasQuery_query`) finish those.
-/

public section

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP ENNReal

namespace VCVioTest.ProgramLogic.CoreVCGenCanary

set_option experimental.vcgen true

section Lower

open scoped OracleComp.Lower

open scoped OracleComp.Lower.Pointwise in
/-- Probability one over two draws: the pointwise rules descend through both. -/
example : Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b || c || true) = true] = 1 := by
  rw [← triple_propInd_self_iff_prEvent_eq_one]
  vcgen
  simp [Lean.Order.rel_eq_le]

/-- A fractional bound on one draw: the exact rule leaves the average of the event. -/
example : (2⁻¹ : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool}[b = true] := by
  rw [prEvent_eq_wp_propInd, ← Lean.Order.rel_eq_le]
  refine Triple.le_wp ?_
  vcgen
  simp [Lean.Order.rel_eq_le, propInd]

/-- A fractional bound over two draws: core stops under the average of the first draw, and the
`wp` equations compute the expectation of the second. -/
example : (4⁻¹ : ℝ≥0∞) ≤ Pr{let b ← $ᵗ Bool; let c ← $ᵗ Bool}[(b && c) = true] := by
  rw [← triple_propInd_self_iff_le_prEvent]
  vcgen
  norm_num [Lean.Order.rel_eq_le, binderNameHint, wp_map,
    OracleComp.Lower.wp_uniformSample_eq_tsum, propInd, ENNReal.div_eq_inv_mul,
    Finset.filter_insert, Finset.filter_singleton, ← ENNReal.mul_inv]

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec]

open scoped OracleComp.Lower.Pointwise in
/-- Probability one over two queries of an arbitrary specification. -/
example (t : spec.Domain) (p : spec.Range t → spec.Range t → Prop) (hp : ∀ u v, p u v) :
    Pr{let u ← (query t : OracleComp spec _)
       let v ← (query t : OracleComp spec _)}[p u v] = 1 := by
  rw [← triple_propInd_self_iff_prEvent_eq_one]
  vcgen
  simp [Lean.Order.rel_eq_le, hp]

/-- A fractional bound over two queries: core stops under the integral against the first answer
measure, and `wp_HasQuery_query` computes the inner expectation. -/
example (t : spec.Domain) (p : spec.Range t → spec.Range t → Prop) (r : ℝ≥0∞)
    (hr : r ≤ ∫⁻ u, ∫⁻ v, propInd (p u v) ∂OracleSpec.AnswerMeasure.toMeasure t
      ∂OracleSpec.AnswerMeasure.toMeasure t) :
    r ≤ Pr{let u ← (query t : OracleComp spec _)
           let v ← (query t : OracleComp spec _)}[p u v] := by
  rw [← triple_propInd_self_iff_le_prEvent]
  vcgen
  simpa only [Lean.Order.rel_eq_le, binderNameHint, wp_map, wp_HasQuery_query,
    Function.comp_apply] using hr

end Lower

end VCVioTest.ProgramLogic.CoreVCGenCanary

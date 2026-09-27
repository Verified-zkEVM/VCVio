/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.Replicate.Basic
public import VCVio.EvalDist.Defs.Measure.Core

/-!
# Measure laws for repeated computations

The distribution of a repeated computation is obtained by binding the first output to the
pushforward distribution of the remaining list. Its successful-output mass is a power of the
single-run mass. The laws apply to any lawful measure semantics for `OracleComp` and do not
select an oracle's response distribution.
-/

public section

open MeasureTheory

namespace OracleComp

/-- A repeated computation denotes a measure-valued bind of its first result and the
remaining list. -/
theorem evalDist_replicate_succ {ι : Type} {spec : OracleSpec ι} {α : Type}
    [EvalDistSemantics (OracleComp spec)] [LawfulEvalDistSemantics (OracleComp spec)]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace (List α)]
    (oa : OracleComp spec α) (n : ℕ)
    (hcons : ∀ x : α, Measurable (List.cons x)) :
    𝒟[oa.replicate (n + 1)] =
      Measure.bind 𝒟[oa] (fun x => (𝒟[oa.replicate n]).map (List.cons x)) := by
  rw [replicate_succ_bind, evalDist_bind_of_discrete]
  congr 1
  funext x
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    (evalDist_map (oa.replicate n) (hcons x))

/-- The success mass of `n` repetitions is the `n`th power of one run's success mass. -/
theorem evalDist_replicate_apply_univ {ι : Type} {spec : OracleSpec ι} {α : Type}
    [EvalDistSemantics (OracleComp spec)] [LawfulEvalDistSemantics (OracleComp spec)]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [MeasurableSpace (List α)]
    (oa : OracleComp spec α) (n : ℕ)
    (hcons : ∀ x : α, Measurable (List.cons x)) :
    𝒟[oa.replicate n] Set.univ = (𝒟[oa] Set.univ) ^ n := by
  induction n with
  | zero => simp [replicate, evalDist_pure]
  | succ n ih =>
      rw [evalDist_replicate_succ oa n hcons]
      rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
      simp only [Measure.map_apply (hcons _) MeasurableSet.univ,
        Set.preimage_univ, ih, lintegral_const]
      rw [pow_succ]

/-- Discrete list outputs make the success-mass power law available to `simp`. -/
@[simp high, grind =]
theorem evalDist_replicate_apply_univ_of_discrete
    {ι : Type} {spec : OracleSpec ι} {α : Type}
    [EvalDistSemantics (OracleComp spec)] [LawfulEvalDistSemantics (OracleComp spec)]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [MeasurableSpace (List α)] [DiscreteMeasurableSpace (List α)]
    (oa : OracleComp spec α) (n : ℕ) :
    𝒟[oa.replicate n] Set.univ = (𝒟[oa] Set.univ) ^ n :=
  evalDist_replicate_apply_univ oa n (fun _ => Measurable.of_discrete)

end OracleComp

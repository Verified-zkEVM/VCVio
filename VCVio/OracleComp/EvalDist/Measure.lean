/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.EvalDist
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.MeasureSpec
import ToMathlib.Probability.UniformOn

/-!
# Measure reasoning from structural support

Continuations that denote the same measure on all syntactically reachable outputs may
be interchanged. The proof inducts on the free program, so no probability/support bridge
or positivity assumption on query answers is necessary.

If every query answer has positive singleton mass, a second induction identifies structural
support with positive output mass. Native uniform oracle specifications satisfy that condition.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory

namespace OracleComp

/-- Equal continuation measures on structural support give equal composed measures. -/
theorem evalDist_bind_congr_of_support {ι α β : Type} {spec : OracleSpec ι}
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [MeasurableSpace β]
    [EvalDistSemantics (OracleComp spec)] [LawfulEvalDistSemantics (OracleComp spec)]
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, bind_assoc, evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro u
    exact ih u fun a ha => h a ((mem_support_bind_iff _ _ _).mpr ⟨u, by simp, ha⟩)

/-- Structural support is positive singleton mass when every oracle response has positive
singleton mass. The full-support hypothesis belongs to the chosen measure interpretation;
finiteness alone does not determine it. -/
theorem mem_support_iff_evalDist_singleton_pos_of_fullSupport
    {ι : Type} {spec : OracleSpec ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec]
    (hfull : ∀ t (u : spec.Range t),
      0 < OracleSpec.IsMeasureSpec.toMeasure t {u})
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : OracleComp spec α) (x : α) :
    x ∈ support mx ↔ 0 < 𝒟[mx] {x} := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
      change x = a ↔ 0 < (Measure.dirac a) {x}
      constructor
      · intro h
        subst x
        simp
      · intro h
        have ha : a ∈ ({x} : Set α) := by
          by_contra hn
          rw [Measure.dirac_apply a {x}, Set.indicator_of_notMem hn] at h
          exact (not_lt_of_ge le_rfl) h
        exact (Set.mem_singleton_iff.mp ha).symm
  | query_bind t k ih =>
      rw [mem_support_bind_iff]
      change (∃ u, u ∈ support (query t : OracleComp spec _) ∧ x ∈ support (k u)) ↔
        0 < 𝒟[(query t : OracleComp spec _) >>= k] {x}
      rw [evalDist_bind_of_discrete,
        Measure.bind_apply (measurableSet_singleton x)
          (Measurable.of_discrete).aemeasurable,
        evalDist_query,
        lintegral_pos_iff_support (Measurable.of_discrete)]
      constructor
      · rintro ⟨u, _, hu⟩
        apply lt_of_lt_of_le (hfull t u)
        apply measure_mono
        intro v hv
        have h : v = u := Set.mem_singleton_iff.mp hv
        subst v
        exact ne_of_gt ((ih u).1 hu)
      · intro hpos
        have hs : (Function.support fun u => 𝒟[k u] {x}).Nonempty := by
          by_contra hn
          have he : (Function.support fun u => 𝒟[k u] {x}) = ∅ :=
            Set.not_nonempty_iff_eq_empty.mp hn
          rw [he, measure_empty] at hpos
          exact (not_lt_of_ge le_rfl) hpos
        obtain ⟨u, hu⟩ := hs
        exact ⟨u, mem_support_query t u, (ih u).2 (pos_iff_ne_zero.mpr hu)⟩

/-- Under native uniform oracle semantics, structural reachability is positive singleton mass. -/
theorem mem_support_iff_evalDist_singleton_pos
    {ι : Type} {spec : OracleSpec ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec]
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : OracleComp spec α) (x : α) :
    x ∈ support mx ↔ 0 < 𝒟[mx] {x} := by
  apply mem_support_iff_evalDist_singleton_pos_of_fullSupport
    (fun t u => ?_) mx x
  have heq : OracleSpec.IsMeasureSpec.toMeasure (spec := spec) t =
      uniformOn (Set.univ : Set (spec.Range t)) :=
    OracleSpec.IsUniformMeasureSpec.toMeasure_eq_uniform t
  rw [heq, ProbabilityTheory.uniformOn_univ_apply_singleton]
  exact ENNReal.inv_pos.mpr (by simp)

end OracleComp

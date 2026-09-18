/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Support
public import VCVio.EvalDist.Monad.Measure
public import VCVio.OracleComp.EvalDist.MeasureSpec
import ToMathlib.Probability.UniformOn
import VCVio.EvalDist.ProbabilityNotation

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
open scoped ENNReal

universe u

namespace OracleComp

/-- Equal continuation measures on structural support give equal composed measures. -/
theorem evalDist_bind_congr_of_support {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
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
    exact ih u fun a ha => h a ((MonadAttach.mem_support_bind).mpr ⟨u, by simp, ha⟩)

/-- Compare event masses after a common oracle computation when the continuation bound only
needs to hold on structurally reachable outputs. This is the operational specialization of
`evalDist_bind_apply_mono`: structural reachability supplies its almost-everywhere premise. -/
theorem evalDist_bind_apply_mono_of_support
    {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace β]
    (mx : OracleComp spec α) (f g : α → OracleComp spec β)
    {event : Set β} (hevent : MeasurableSet event)
    (hfg : ∀ a ∈ support mx, 𝒟[f a] event ≤ 𝒟[g a] event) :
    𝒟[mx >>= f] event ≤ 𝒟[mx >>= g] event := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using hfg a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, bind_assoc, evalDist_bind_of_discrete, evalDist_bind_of_discrete,
      Measure.bind_apply hevent Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hevent Measurable.of_discrete.aemeasurable]
    exact lintegral_mono fun u ↦ ih u fun a ha ↦
      hfg a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

/-- A uniform lower bound on reachable continuation events bounds their composed event.
The common computation need not carry a measurable-space instance on its output type. -/
theorem le_evalDist_bind_apply_of_support
    {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    [MeasurableSpace β]
    (mx : OracleComp spec α) (f : α → OracleComp spec β)
    {event : Set β} (hevent : MeasurableSet event) {r : ℝ≥0∞}
    (h : ∀ a ∈ support mx, r ≤ 𝒟[f a] event) :
    r ≤ 𝒟[mx >>= f] event := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply hevent Measurable.of_discrete.aemeasurable]
    calc
      r = ∫⁻ _u, r ∂𝒟[(query t : OracleComp spec (spec.Range t))] := by
        rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]
      _ ≤ _ := lintegral_mono fun u ↦ ih u fun a ha ↦
        h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

/-- Events agreeing on every possible output have equal successful probability. -/
theorem prEvent_congr_of_support
    {ι : Type u} {α : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]
    (mx : OracleComp spec α) (p q : α → Prop)
    (h : ∀ a ∈ support mx, p a ↔ q a) :
    Pr{let a ← mx}[p a] = Pr{let a ← mx}[q a] := by
  exact congrArg (fun μ : Measure Prop ↦ μ {True})
    (evalDist_bind_congr_of_support mx (pure ∘ p) (pure ∘ q)
      fun a ha ↦ by simp [propext (h a ha)])

/-- Structural support is positive singleton mass when every oracle response has positive
singleton mass. The full-support hypothesis belongs to the chosen measure interpretation;
finiteness alone does not determine it. -/
theorem mem_support_iff_evalDist_singleton_pos_of_fullSupport
    {ι : Type u} {spec : OracleSpec.{u, 0} ι}
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
      rw [MonadAttach.mem_support_bind]
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

/-- An event has probability one exactly when it contains every structurally reachable output,
provided every oracle response has positive singleton mass. -/
theorem evalDist_apply_setOf_eq_one_iff_forall_mem_support_of_fullSupport
    {ι : Type u} {α : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec]
    (hfull : ∀ t (u : spec.Range t),
      0 < OracleSpec.IsMeasureSpec.toMeasure t {u})
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : OracleComp spec α) (p : α → Prop) :
    𝒟[mx] {x | p x} = 1 ↔ ∀ x ∈ support mx, p x := by
  rw [← MeasureTheory.ae_iff_prob_eq_one Measurable.of_discrete]
  constructor
  · intro hp x hx
    by_contra hpx
    have hxzero : 𝒟[mx] {x} = 0 :=
      measure_mono_null (by
        intro y hy
        simpa [Set.mem_singleton_iff.mp hy] using hpx)
        (MeasureTheory.ae_iff.mp hp)
    exact (ne_of_gt
      ((mem_support_iff_evalDist_singleton_pos_of_fullSupport hfull mx x).mp hx)) hxzero
  · exact evalDist.ae_of_forall_mem_support mx p MeasurableSet.of_discrete

/-- Under native uniform oracle semantics, structural reachability is positive singleton mass. -/
theorem mem_support_iff_evalDist_singleton_pos
    {ι : Type u} {spec : OracleSpec.{u, 0} ι}
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

/-- Under native uniform oracle semantics, an event has probability one exactly when it contains
every structurally reachable output. -/
@[grind =]
theorem evalDist_apply_setOf_eq_one_iff_forall_mem_support
    {ι : Type u} {α : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)]
    [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsUniformMeasureSpec spec]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : OracleComp spec α) (p : α → Prop) :
    𝒟[mx] {x | p x} = 1 ↔ ∀ x ∈ support mx, p x := by
  apply evalDist_apply_setOf_eq_one_iff_forall_mem_support_of_fullSupport
  intro t u
  have heq : OracleSpec.IsMeasureSpec.toMeasure (spec := spec) t =
      uniformOn (Set.univ : Set (spec.Range t)) :=
    OracleSpec.IsUniformMeasureSpec.toMeasure_eq_uniform t
  rw [heq, ProbabilityTheory.uniformOn_univ_apply_singleton]
  exact ENNReal.inv_pos.mpr (by simp)

end OracleComp

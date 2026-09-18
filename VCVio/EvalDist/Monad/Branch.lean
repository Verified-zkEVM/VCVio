/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.Lossless
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Data.Fintype.Sets

/-!
# Conditional branches under measure semantics

A proposition-valued observation selects between two computations. The resulting measure is
the sum of the branch measures weighted by the selector's successful outcome masses. Discarded
source values need no measurable space, and failure is kept separate from either branch.
-/

public section

open MeasureTheory

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

/-- An impossible final observation has zero mass, including after a failed computation. -/
@[simp↓ high, grind norm↓]
theorem prEvent_false {α : Type} (mx : m α) : Pr{let _ ← mx}[False] = 0 :=
  prEvent_eq_zero_of_forall_not mx (fun _ ↦ False) (fun _ ↦ id)

open scoped Classical in
omit [LawfulMonad m] in
/-- Binding a propositional selector gives the two branch measures with their actual masses. -/
theorem evalDist_bind_prop {β : Type} [MeasurableSpace β]
    (selector : m Prop) (yes no : m β) :
    𝒟[selector >>= fun p ↦ if p then yes else no] =
      𝒟[selector] {True} • 𝒟[yes] + 𝒟[selector] {False} • 𝒟[no] := by
  classical
  rw [evalDist_bind_of_discrete]
  ext s hs
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_fintype]
  simp [Fintype.univ_Prop, mul_comm]

/-- An observation's negation is the false mass of the same propositional selector. -/
theorem prEvent_not_eq_apply_false {α : Type} (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[¬p x] = 𝒟[p <$> mx] {False} := by
  calc
    _ = Pr{let b ← p <$> mx}[¬b] := by simp only [bind_map_left]
    _ = 𝒟[p <$> mx] {b | ¬b} := prEvent_eq_evalDist_of_discrete _ _
    _ = _ := by congr 1; ext b; simp

/-- An event and its negation partition the selector's successful mass, including lossy draws. -/
theorem prEvent_add_prEvent_not {α : Type} (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] + Pr{let x ← mx}[¬p x] = 𝒟[p <$> mx] Set.univ := by
  rw [prEvent_eq_evalDist_map, prEvent_not_eq_apply_false]
  rw [← measure_union (by simp) (measurableSet_singleton False)]
  congr 1
  ext b
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact (Classical.em b).imp (fun hb ↦ propext (iff_true_intro hb))
    (fun hb ↦ propext (iff_false_intro hb))

/-- A conditional continuation is a mixture weighted by the observed predicate, without a
measurable space on discarded source values. -/
theorem evalDist_bind_ite {α β : Type} [MeasurableSpace β]
    (mx : m α) (p : α → Prop) [DecidablePred p] (yes no : m β) :
    𝒟[mx >>= fun x ↦ if p x then yes else no] =
      Pr{let x ← mx}[p x] • 𝒟[yes] + Pr{let x ← mx}[¬p x] • 𝒟[no] := by
  classical
  calc
    _ = 𝒟[(p <$> mx) >>= fun b ↦ if b then yes else no] := by
      simp only [bind_map_left]
      congr 1
      apply bind_congr
      intro x
      by_cases hx : p x <;> simp [hx]
    _ = _ := by
      rw [evalDist_bind_prop, prEvent_not_eq_apply_false]
      simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- Measurable selector measures and branch measures give a measurable conditional family.
The family can be bundled by `evalDistKernel`; discarded source values need no measurable space.
-/
@[fun_prop]
theorem measurable_evalDist_bind_ite {ρ : Type*} {α β : Type}
    [MeasurableSpace ρ] [MeasurableSpace β]
    (mx : ρ → m α) (p : ρ → α → Prop) [∀ r, DecidablePred (p r)] (yes no : ρ → m β)
    (hobs : Measurable fun r ↦ 𝒟[p r <$> mx r])
    (hyes : Measurable fun r ↦ 𝒟[yes r]) (hno : Measurable fun r ↦ 𝒟[no r]) :
    Measurable fun r ↦ 𝒟[mx r >>= fun x ↦ if p r x then yes r else no r] := by
  simp_rw [evalDist_bind_ite, prEvent_not_eq_apply_false, prEvent_eq_evalDist_map]
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact (((Measure.measurable_coe (measurableSet_singleton True)).comp hobs).mul
    ((Measure.measurable_coe hs).comp hyes)).add
    (((Measure.measurable_coe (measurableSet_singleton False)).comp hobs).mul
      ((Measure.measurable_coe hs).comp hno))

/-- Lossless branches selected by a lossless observation give a lossless computation.
The selected output space may be continuous, and the discarded source needs no measurable space.
-/
theorem evalDist.isProbabilityMeasure_bind_ite {α β : Type} [MeasurableSpace β]
    (mx : m α) (p : α → Prop) [DecidablePred p] [IsProbabilityMeasure 𝒟[p <$> mx]]
    (yes no : m β) [IsProbabilityMeasure 𝒟[yes]] [IsProbabilityMeasure 𝒟[no]] :
    IsProbabilityMeasure 𝒟[mx >>= fun x ↦ if p x then yes else no] := by
  constructor
  rw [evalDist_bind_ite]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact (prEvent_add_prEvent_not mx p).trans (measure_univ)

/-- The event probability of a conditional continuation is the weighted sum of its two branch
event probabilities. Each weight retains successful mass. -/
theorem prEvent_bind_ite {α β : Type} (mx : m α) (p : α → Prop) [DecidablePred p]
    (yes no : m β) (q : β → Prop) :
    Pr{let y ← mx >>= fun x ↦ if p x then yes else no}[q y] =
      Pr{let x ← mx}[p x] * Pr{let y ← yes}[q y] +
        Pr{let x ← mx}[¬p x] * Pr{let y ← no}[q y] := by
  rw [bind_assoc]
  simp_rw [apply_ite (fun x ↦ x >>= fun y ↦ pure (q y))]
  rw [evalDist_bind_ite]
  simp

/-- A continuation event that is constant on an observed condition and zero otherwise factors
through that condition's probability. The reference event may have a different output type. -/
theorem prEvent_bind_eq_mul_of_ite {α β γ : Type}
    (mx : m α) (f : α → m β) (p : α → Prop) [DecidablePred p] (q : β → Prop)
    (my : m γ) (r : γ → Prop)
    (h : ∀ x,
      Pr{
        let y ← f x}[q y] = if p x then Pr{
        let z ← my}[r z] else 0) :
    Pr{let y ← mx >>= f}[q y] = Pr{let x ← mx}[p x] * Pr{let z ← my}[r z] := by
  calc
    _ = Pr{let b ← mx >>= fun x ↦ if p x then r <$> my else pure False}[b] := by
      simpa only [id, bind_pure] using
        prEvent_bind_congr mx f (fun x ↦ if p x then r <$> my else pure False) q id (by
          intro x
          rw [h]
          split_ifs <;> simp)
    _ = _ := by
      rw [evalDist_bind_ite]
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [← prEvent_eq_evalDist_map]
      simp

/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub, Devon Tuma
-/

module
public import ToMathlib.Probability.Kernel.Bounds
public import VCVio.EvalDist.Monad.Measure
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.Monad.Branch
import Mathlib.Data.Fin.VecNotation

/-!
# Additive comparison of observed continuations

Native event probabilities after a common prefix satisfy finite-sum comparison rules.
Measurable continuation observations admit AE premises on the chosen prefix law. Structural
premises use core attachment and the actual continuation-measure observer; arbitrary hidden
payloads need no measurable space. Constant allowances retain the prefix's success mass.

The disagreement rules charge an exceptional event or an observed bad world while sharing this
finite-sum integration argument.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v
variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {α β ι : Type} [Fintype ι]

/-- AE comparison with a finite family of reference events integrates the conditional allowance.
No measurability of the allowance is required. -/
theorem prEvent_bind_le_sum_add_lintegral_ae [MeasurableSpace α]
    (mx : m α) (f : α → m β) (p : β → Prop)
    (g : ι → α → m Prop)
    (hf : Measurable fun a ↦ 𝒟[do let b ← f a; return p b])
    (hg : ∀ i, Measurable fun a ↦ 𝒟[g i a]) (bound : α → ENNReal)
    (h : ∀ᵐ a ∂𝒟[mx], Pr{let b ← f a}[p b] ≤
      (∑ i, Pr{let q ← g i a}[q]) + bound a) :
    Pr{let b ← mx >>= f}[p b] ≤
      (∑ i, Pr{let q ← mx >>= g i}[q]) + ∫⁻ a, bound a ∂𝒟[mx] := by
  have hg' (i : ι) : Measurable fun a ↦ Pr{let q ← g i a}[q] := by
    simpa only [bind_pure, Function.comp_def] using
      (Measure.measurable_coe (measurableSet_singleton True)).comp (hg i)
  rw [prEvent_bind_eq_lintegral mx f p hf]
  have hi (i : ι) : Pr{let q ← mx >>= g i}[q] =
      ∫⁻ a, Pr{let q ← g i a}[q] ∂𝒟[mx] := by
    simpa only [id_eq, bind_pure] using prEvent_bind_eq_lintegral mx (g i) id
      (by simpa only [id_eq, bind_pure] using hg i)
  simp_rw [hi]
  exact lintegral_le_sum_add_lintegral_of_le_ae Finset.univ
    (fun i _ ↦ (hg' i).aemeasurable) h

/-- Reachable conditional event comparisons hold after a common prefix, retaining the
allowance's successful-mass factor. Only actual observation measures are made measurable. -/
theorem prEvent_bind_le_sum_add_mul_mass_of_support [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (mx : m α) (f : α → m β) (p : β → Prop) (g : ι → α → m Prop) (ε : ENNReal)
    (h : ∀ a ∈ support mx, Pr{let b ← f a}[p b] ≤
      (∑ i, Pr{let q ← g i a}[q]) + ε) :
    Pr{let b ← mx >>= f}[p b] ≤ (∑ i, Pr{let q ← mx >>= g i}[q]) +
      ε * Pr{let _a ← mx}[True] := by
  let obs : α → Measure Prop × (ι → Measure Prop) := fun a ↦
    (𝒟[do let b ← f a; return p b], fun i ↦ 𝒟[g i a])
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  have hf : Measurable fun a ↦ 𝒟[do let b ← f a; return p b] := measurable_fst.comp hobs
  have hg (i : ι) : Measurable fun a ↦ 𝒟[g i a] :=
    (measurable_pi_apply i).comp (measurable_snd.comp hobs)
  have hp : Measurable fun a ↦ Pr{let b ← f a}[p b] :=
    (Measure.measurable_coe (measurableSet_singleton True)).comp hf
  have hq (i : ι) : Measurable fun a ↦ Pr{let q ← g i a}[q] := by
    simpa only [bind_pure, Function.comp_def] using
      (Measure.measurable_coe (measurableSet_singleton True)).comp (hg i)
  have hae := evalDist.ae_of_forall_mem_support mx _
    (measurableSet_le hp ((Finset.measurable_sum _ fun i _ ↦ hq i).add_const ε)) h
  have hb := prEvent_bind_le_sum_add_lintegral_ae mx f p g hf hg (fun _ ↦ ε) hae
  simpa only [lintegral_const, prEvent_eq_evalDist mx (fun _ ↦ True) measurable_const,
    Set.ofPred_true] using hb

/-- A uniform reachable allowance gives an additive comparison with finitely many references. -/
theorem prEvent_bind_le_sum_add_of_support [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (mx : m α) (f : α → m β) (p : β → Prop) (g : ι → α → m Prop) (ε : ENNReal)
    (h : ∀ a ∈ support mx, Pr{let b ← f a}[p b] ≤
      (∑ i, Pr{let q ← g i a}[q]) + ε) :
    Pr{let b ← mx >>= f}[p b] ≤ (∑ i, Pr{let q ← mx >>= g i}[q]) + ε :=
  (prEvent_bind_le_sum_add_mul_mass_of_support mx f p g ε h).trans <|
    add_le_add le_rfl ((mul_le_mul' le_rfl
      (measure_le_one 𝒟[do let _a ← mx; return True] {True})).trans_eq (mul_one ε))

variable {γ : Type} [MonadAttach m] [WeaklyLawfulMonadAttach m]

omit [Fintype ι] in
/-- A reachable conditional comparison outside a disagreement event charges its probability
and a uniform allowance. -/
theorem prEvent_bind_le_add_of_disagree {mx : m α} {my oc : α → m β}
    {q : β → Prop} {D : α → Prop} {ε₁ ε₂ : ENNReal}
    (hD : Pr{let x ← mx}[D x] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬D x →
      Pr{let y ← my x}[q y] ≤ Pr{let y ← oc x}[q y] + ε₂) :
    Pr{let y ← mx >>= my}[q y] ≤ Pr{let y ← mx >>= oc}[q y] + ε₁ + ε₂ := by
  classical
  have hb := prEvent_bind_le_sum_add_of_support mx my q
    ![fun x ↦ q <$> oc x, fun x ↦ pure (D x)] ε₂ (by
      intro x hx
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        ← prEvent_eq_evalDist_map, evalDist_pure, Measure.dirac_apply_singleton_true]
      by_cases hDx : D x
      · simpa only [ite_eq_left hDx] using
          (measure_le_one 𝒟[do let y ← my x; return q y] {True}).trans
          (le_add_right (le_add_left le_rfl) : (1 : ENNReal) ≤
            Pr{let y ← oc x}[q y] + 1 + ε₂)
      · simpa only [ite_eq_right hDx, add_zero] using h x hx hDx)
  have hb' : Pr{let y ← mx >>= my}[q y] ≤
      Pr{let y ← mx >>= oc}[q y] + Pr{let x ← mx}[D x] + ε₂ := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind] using hb
  exact hb'.trans (add_le_add (add_le_add le_rfl hD) le_rfl)

omit [Fintype ι] in
/-- A bad world that certainly fires on disagreement absorbs that event's charge. The
good-branch comparison may already contain the conditional bad-world probability. -/
theorem prEvent_bind_le_add_bad_of_disagree' {mx : m α}
    {my oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε : ENNReal}
    (hbad : ∀ x ∈ support mx, D x → Pr{let z ← ob x}[r z] = 1)
    (h : ∀ x ∈ support mx, ¬D x → Pr{let y ← my x}[q y] ≤
      Pr{let y ← oc x}[q y] + Pr{let z ← ob x}[r z] + ε) :
    Pr{let y ← mx >>= my}[q y] ≤
      Pr{let y ← mx >>= oc}[q y] + Pr{let z ← mx >>= ob}[r z] + ε := by
  have hb := prEvent_bind_le_sum_add_of_support mx my q
    ![fun x ↦ q <$> oc x, fun x ↦ r <$> ob x] ε (by
      intro x hx
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        ← prEvent_eq_evalDist_map]
      by_cases hDx : D x
      · simpa only [hbad x hx hDx] using
          (measure_le_one 𝒟[do let y ← my x; return q y] {True}).trans
            (le_add_right (le_add_left le_rfl) : (1 : ENNReal) ≤
              Pr{let y ← oc x}[q y] + 1 + ε)
      · exact h x hx hDx)
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind] using hb

omit [Fintype ι] in
/-- A bad world that certainly fires on disagreement pays for the exceptional branches. -/
theorem prEvent_bind_le_add_bad_of_disagree {mx : m α}
    {my oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε : ENNReal}
    (hbad : ∀ x ∈ support mx, D x → Pr{let z ← ob x}[r z] = 1)
    (h : ∀ x ∈ support mx, ¬D x →
      Pr{let y ← my x}[q y] ≤ Pr{let y ← oc x}[q y] + ε) :
    Pr{let y ← mx >>= my}[q y] ≤
      Pr{let y ← mx >>= oc}[q y] + Pr{let z ← mx >>= ob}[r z] + ε :=
  prEvent_bind_le_add_bad_of_disagree' hbad fun x hx hDx ↦
    (h x hx hDx).trans (add_le_add (le_add_right le_rfl) le_rfl)

omit [Fintype ι] in
/-- Disagreement and a separate conditional bad world are both charged after a shared prefix. -/
theorem prEvent_bind_le_add_bad_disagree {mx : m α}
    {my oc : α → m β} {ob : α → m γ}
    {q : β → Prop} {r : γ → Prop} {D : α → Prop} {ε₁ ε₂ : ENNReal}
    (hD : Pr{let x ← mx}[D x] ≤ ε₁)
    (h : ∀ x ∈ support mx, ¬D x → Pr{let y ← my x}[q y] ≤
      Pr{let y ← oc x}[q y] + Pr{let z ← ob x}[r z] + ε₂) :
    Pr{let y ← mx >>= my}[q y] ≤ Pr{let y ← mx >>= oc}[q y] +
      Pr{let z ← mx >>= ob}[r z] + ε₁ + ε₂ := by
  classical
  have hb := prEvent_bind_le_sum_add_of_support mx my q
    ![fun x ↦ q <$> oc x, fun x ↦ r <$> ob x, fun x ↦ pure (D x)] ε₂ (by
      intro x hx
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ← prEvent_eq_evalDist_map,
        evalDist_pure, Measure.dirac_apply_singleton_true]
      by_cases hDx : D x
      · simpa only [ite_eq_left hDx] using
          (measure_le_one 𝒟[do let y ← my x; return q y] {True}).trans
            (le_add_right (le_add_left le_rfl) : (1 : ENNReal) ≤
              (Pr{let y ← oc x}[q y] + Pr{let z ← ob x}[r z]) + 1 + ε₂)
      · simpa only [ite_eq_right hDx, add_zero] using h x hx hDx)
  have hb' : Pr{let y ← mx >>= my}[q y] ≤ Pr{let y ← mx >>= oc}[q y] +
      Pr{let z ← mx >>= ob}[r z] + Pr{let x ← mx}[D x] + ε₂ := by
    simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind, add_assoc] using hb
  exact hb'.trans (add_le_add (add_le_add le_rfl hD) le_rfl)

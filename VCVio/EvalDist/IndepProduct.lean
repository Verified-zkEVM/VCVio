/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.IndepProductMeasure
public import VCVio.EvalDist.ProbabilityNotation
public import VCVio.EvalDist.Defs.Support

/-!
# Events and reachability of independent products

Finite families of independent computations denote Mathlib product measures. Joint events
factor into their coordinate events. A coordinate marginal retains the successful mass of
all other factors; it recovers its own event probability when those factors are lossless.
Event observations need no measurable space on discarded payloads, and coordinate
reachability uses core lawful attachment independently of the probability interpretation.
-/

public section

open MeasureTheory
open scoped ENNReal

universe u v

/-- Every reachable coordinate is reachable in its own factor. -/
lemma mem_support_mOfFn {α : Type u} {m : Type u → Type v}
    [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    (n : ℕ) (g : Fin n → m α) (v : Fin n → α)
    (hv : v ∈ support (Fin.mOfFn n g)) (i : Fin n) : v i ∈ support (g i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      rw [Fin.mOfFn] at hv
      obtain ⟨a, ha, hv⟩ := LawfulMonadAttach.canReturn_bind_imp' hv
      obtain ⟨rest, hrest, hv⟩ := LawfulMonadAttach.canReturn_bind_imp' hv
      have heq := LawfulMonadAttach.eq_of_canReturn_pure hv
      subst v
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using ha
      · simpa using ih (fun j ↦ g j.succ) rest hrest j

/-- Independent coordinate events factor into their event probabilities. -/
lemma prEvent_forall_coord_mOfFn {α : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (n : ℕ) (g : Fin n → m α) (p : (i : Fin n) → α → Prop) :
    Pr{let v ← Fin.mOfFn n g}[∀ i, p i (v i)] = ∏ i, Pr{let x ← g i}[p i x] := by
  induction n with
  | zero => simp [Fin.mOfFn, evalDist_pure]
  | succ n ih =>
      simpa only [Fin.mOfFn, bind_assoc, pure_bind, Fin.forall_fin_succ,
        Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ, ih] using
        prEvent_bind_bind_and (g 0) (Fin.mOfFn n fun i ↦ g i.succ)
          (p 0) (fun rest ↦ ∀ i, p i.succ (rest i))

private lemma prEvent_coord_eq_mul_of_forall {α ι : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [Fintype ι] [DecidableEq ι] (joint : m (ι → α)) (g : ι → m α)
    (hjoint : ∀ p : ι → α → Prop,
      Pr{let v ← joint}[∀ j, p j (v j)] = ∏ j, Pr{let x ← g j}[p j x])
    (i : ι) (p : α → Prop) :
    Pr{let v ← joint}[p (v i)] =
      Pr{let x ← g i}[p x] * ∏ j ∈ Finset.univ.erase i, Pr{let _ ← g j}[True] := by
  classical
  let q (j : ι) (x : α) : Prop := if j = i then p x else True
  have hq (v : ι → α) : p (v i) ↔ ∀ j, q j (v j) := by
    constructor
    · intro h j
      by_cases hj : j = i <;> simp [q, hj, h]
    · intro h
      simpa [q] using h i
  rw [prEvent_congr joint _ _ hq, hjoint q,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [q, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.ne_of_mem_erase hj, ite_false]

/-- A coordinate event retains the success masses of all other factors. -/
lemma prEvent_coord_mOfFn_eq_mul {α : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (n : ℕ) (g : Fin n → m α) (i : Fin n) (p : α → Prop) :
    Pr{let v ← Fin.mOfFn n g}[p (v i)] =
      Pr{let x ← g i}[p x] * ∏ j ∈ Finset.univ.erase i, Pr{let _ ← g j}[True] :=
  prEvent_coord_eq_mul_of_forall _ g (prEvent_forall_coord_mOfFn n g) i p

/-- A lossy factor can only decrease another coordinate event probability. -/
lemma prEvent_coord_mOfFn_le {α : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (n : ℕ) (g : Fin n → m α) (i : Fin n) (p : α → Prop) :
    Pr{let v ← Fin.mOfFn n g}[p (v i)] ≤ Pr{let x ← g i}[p x] := by
  rw [prEvent_coord_mOfFn_eq_mul]
  exact mul_le_of_le_one_right bot_le (Finset.prod_le_one fun _ _ ↦
    MeasureTheory.measure_le_one _ _)

/-- A coordinate marginal is exact when every other factor has full success mass. -/
lemma prEvent_coord_mOfFn {α : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (n : ℕ) (g : Fin n → m α) (i : Fin n) (p : α → Prop)
    (hg : ∀ j, j ≠ i → Pr{
      let _ ← g j}[True] = 1) :
    Pr{let v ← Fin.mOfFn n g}[p (v i)] = Pr{let x ← g i}[p x] := by
  rw [prEvent_coord_mOfFn_eq_mul]
  simp only [Finset.prod_congr rfl (fun j hj ↦ hg j (Finset.ne_of_mem_erase hj)),
    Finset.prod_const_one, mul_one]

/-- Joint events of a finite independent family factor over its indices. -/
lemma prEvent_forall_coord_mPi {α ι : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [Fintype ι] (g : ι → m α) (p : ι → α → Prop) :
    Pr{let v ← Fintype.mPi g}[∀ i, p i (v i)] = ∏ i, Pr{let x ← g i}[p i x] := by
  let e := Fintype.equivFin ι
  rw [Fintype.mPi, prEvent_map]
  calc
    _ = Pr{let w ← Fin.mOfFn (Fintype.card ι) (fun k ↦ g (e.symm k))}[
        ∀ k, p (e.symm k) (w k)] := by
      apply prEvent_congr
      intro w
      simp only [Equiv.arrowCongr, Equiv.coe_fn_mk, Equiv.coe_refl,
        Equiv.symm_symm]
      exact ⟨fun hw k ↦ by simpa [e] using hw ((Fintype.equivFin ι).symm k),
        fun hw i ↦ by simpa [e] using hw ((Fintype.equivFin ι) i)⟩
    _ = _ := (prEvent_forall_coord_mOfFn _ _ _).trans
      (Equiv.prod_comp (Fintype.equivFin ι).symm fun i ↦ Pr{let x ← g i}[p i x])

/-- Every reachable coordinate of a finite independent family is reachable in its factor. -/
lemma mem_support_mPi {α : Type u} {m : Type u → Type v}
    [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    {ι : Type} [Fintype ι] (g : ι → m α) (v : ι → α)
    (hv : v ∈ support (Fintype.mPi g)) (i : ι) : v i ∈ support (g i) := by
  rw [Fintype.mPi] at hv
  obtain ⟨w, hw, hv⟩ := LawfulMonadAttach.canReturn_map_imp' hv
  subst v
  simpa using mem_support_mOfFn _ _ w hw (Fintype.equivFin ι i)

/-- Equality to an independent tuple factors without measuring its payloads. -/
lemma prEvent_eq_mOfFn {α : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (n : ℕ) (g : Fin n → m α) (v : Fin n → α) :
    Pr{let w ← Fin.mOfFn n g}[w = v] = ∏ i, Pr{let x ← g i}[x = v i] := by
  rw [prEvent_congr _ _ _ (fun _ ↦ funext_iff)]
  exact prEvent_forall_coord_mOfFn n g (fun i x ↦ x = v i)

/-- Equality to a finite independent output factors into its coordinate events. -/
lemma prEvent_eq_mPi {α ι : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [Fintype ι] (g : ι → m α) (v : ι → α) :
    Pr{let w ← Fintype.mPi g}[w = v] = ∏ i, Pr{let x ← g i}[x = v i] := by
  rw [prEvent_congr _ _ _ (fun _ ↦ funext_iff)]
  exact prEvent_forall_coord_mPi g (fun i x ↦ x = v i)

/-- The coordinate event of a finite family retains every other factor's success mass. -/
lemma prEvent_coord_mPi_eq_mul {α ι : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [Fintype ι] [DecidableEq ι] (g : ι → m α) (i : ι) (p : α → Prop) :
    Pr{let v ← Fintype.mPi g}[p (v i)] =
      Pr{let x ← g i}[p x] * ∏ j ∈ Finset.univ.erase i, Pr{let _ ← g j}[True] :=
  prEvent_coord_eq_mul_of_forall _ g (prEvent_forall_coord_mPi g) i p

/-- A finite family's coordinate event is bounded by that factor's event probability. -/
lemma prEvent_coord_mPi_le {α ι : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [Fintype ι] (g : ι → m α) (i : ι) (p : α → Prop) :
    Pr{let v ← Fintype.mPi g}[p (v i)] ≤ Pr{let x ← g i}[p x] := by
  classical
  rw [prEvent_coord_mPi_eq_mul]
  exact mul_le_of_le_one_right bot_le (Finset.prod_le_one fun _ _ ↦
    MeasureTheory.measure_le_one _ _)

/-- Other factors with full success mass give an exact coordinate event marginal. -/
lemma prEvent_coord_mPi {α ι : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [Fintype ι] (g : ι → m α) (i : ι) (p : α → Prop)
    (hg : ∀ j, j ≠ i → Pr{
      let _ ← g j}[True] = 1) :
    Pr{let v ← Fintype.mPi g}[p (v i)] = Pr{let x ← g i}[p x] := by
  classical
  rw [prEvent_coord_mPi_eq_mul]
  simp only [Finset.prod_congr rfl (fun j hj ↦ hg j (Finset.ne_of_mem_erase hj)),
    Finset.prod_const_one, mul_one]

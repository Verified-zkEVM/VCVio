/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.EvalDist.Monad.Option
public import ToMathlib.Data.Vector.Count
public import ToMathlib.Data.Vector.ListVector

/-!
# Uniform selection on output measures

Events of the uniform selection primitives, stated with `Pr{…}`. Selecting from a nonempty vector
gives an event the proportion of entries satisfying it; selecting from a list, finset or multiset
does the same through the optional monad, where an empty collection fails and so contributes no
successful mass. A uniform range and a fair coin give an event its proportion of admissible
values.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbComp

section uniformSelectVector

variable {α : Type} {n : ℕ} (xs : Vector α (n + 1))

/-- Selecting uniformly from a nonempty vector gives an event its proportion of entries. -/
theorem prEvent_uniformSelectVector (p : α → Prop) [DecidablePred p] :
    Pr{let x ← $! xs}[p x] = (xs.countP (fun a => decide (p a)) : ℝ≥0∞) / (n + 1) := by
  rw [uniformSelectVector_def, prEvent_map, prEvent_uniformFin, ← Vector.card_eq_countP]

end uniformSelectVector

section uniformSelectListVector

variable {α : Type} {n : ℕ} (xs : List.Vector α (n + 1))

/-- Selecting uniformly from a nonempty list vector gives an event its proportion of entries. -/
theorem prEvent_uniformSelectListVector (p : α → Prop) [DecidablePred p] :
    Pr{let x ← $! xs}[p x] = (xs.toList.countP (fun a => decide (p a)) : ℝ≥0∞) / (n + 1) := by
  rw [uniformSelectListVector_def, prEvent_map, prEvent_uniformFin, ← List.Vector.card_eq_countP]
  rfl

end uniformSelectListVector

section uniformSelectList

variable {α : Type}

/-- Selecting uniformly from a list gives an event its proportion of entries. An empty list fails,
so its events have no successful mass. -/
theorem prEvent_uniformSelectList (xs : List α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← ($ xs : OptionT ProbComp α)}[p x] =
      (xs.countP (fun a => decide (p a)) : ℝ≥0∞) / xs.length := by
  match xs with
  | [] => simp
  | y :: ys =>
    have hsel : ($ (y :: ys) : OptionT ProbComp α) =
        OptionT.lift ($! (List.Vector.cons y ⟨ys, rfl⟩)) := rfl
    rw [hsel, OptionT.prEvent_lift, prEvent_uniformSelectListVector, List.length_cons,
      Nat.cast_succ]
    rfl

/-- Selecting uniformly from a finset gives an event its proportion of elements. -/
theorem prEvent_uniformSelectFinset (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← ($ s : OptionT ProbComp α)}[p x] = ({x ∈ s | p x}.card : ℝ≥0∞) / s.card := by
  rw [uniformSelectFinset_def, prEvent_uniformSelectList, Finset.length_toList,
    ← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter]
  rfl

/-- Selecting uniformly from a multiset gives an event its proportion of elements, counted with
multiplicity. -/
theorem prEvent_uniformSelectMultiset (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← ($ s : OptionT ProbComp α)}[p x] =
      (Multiset.countP p s : ℝ≥0∞) / Multiset.card s := by
  rw [uniformSelectMultiset_def, prEvent_uniformSelectList, ← Multiset.coe_countP,
    Multiset.coe_toList, Multiset.length_toList]

end uniformSelectList

section uniformRange

/-- A uniform range draw gives an event its proportion of admissible values in the range. -/
theorem prEvent_uniformRange (n m : ℕ) (h : n < m) (p : Fin (m + 1) → Prop) [DecidablePred p] :
    Pr{let x ← uniformRange n m h}[p x] =
      ((Finset.univ.filter fun x : Fin (m + 1) => n ≤ x ∧ p x).card : ℝ≥0∞) / (m - n + 1) := by
  rw [uniformRange, prEvent_map, prEvent_uniformFin]
  congr 2
  · refine Finset.card_nbij (fun i => ⟨i + n, by omega⟩) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
      exact ⟨Nat.le_add_left n i, hi⟩
    · intro i _ j _ hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
      refine ⟨⟨x - n, by omega⟩, by simpa [Nat.sub_add_cancel hx.1] using hx.2, ?_⟩
      exact Fin.ext (by simp [Nat.sub_add_cancel hx.1])
  · exact ENNReal.natCast_sub m n

end uniformRange

end ProbComp

/-- A fair coin gives an event its proportion of the two outcomes. -/
theorem OracleComp.prEvent_coin (p : Bool → Prop) [DecidablePred p] :
    Pr{let b ← OracleComp.coin}[p b] = ((Finset.univ.filter p).card : ℝ≥0∞) / 2 := by
  rw [prEvent_eq_evalDist_of_discrete, OracleComp.coin,
    OracleComp.evalDist_liftM_query_uniform (spec := coinSpec) (), uniformOn_univ_apply_setOf]
  simp

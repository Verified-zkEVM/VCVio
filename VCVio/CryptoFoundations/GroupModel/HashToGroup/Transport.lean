/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Transport of algebraic explanations

Each chronological input has a recorded row over a reduction basis. Substituting those rows
into an explanation is matrix multiplication, expressed by `Interaction.evaluate` in the module
of coefficient vectors. The reduction basis can include fixed inputs using a sum index.
-/

public section

namespace GroupModel.HashToGroup

open Interaction

variable {F G κ : Type}

/-- Substitute the recorded reduction-basis row for each chronological received input. -/
@[expose] def transport [Semiring F] (rows : List (κ → F)) (c : List F) : κ → F :=
  evaluate c rows

/-- Substitution preserves the group element represented by any coefficient list. -/
theorem linearCombination_transport [CommSemiring F] [AddCommMonoid G] [Module F G] [Fintype κ]
    (B : κ → G) (rows : List (κ → F)) (c : List F) :
    Fintype.linearCombination F B (transport rows c) =
      evaluate c (rows.map (Fintype.linearCombination F B)) :=
  (evaluate_map _ c rows).symm

/-- Substitute recorded rows into every output of a multi-sort interaction explanation. -/
@[expose] def transportExplained [Semiring F] {S Data : Type} {Gs : S → Type}
    {K : S → Type} (rows : (s : S) → List (K s → F)) (out : Explained F Data Gs) :
    (s : S) → List (K s → F) :=
  fun s => (out.coefficients s).map (transport (rows s))

/-- Every valid explained output has an explicit representation over the reduction basis.
This statement is independent of the game, the sampling distribution, and the group sorts. -/
theorem transportExplained_evaluate [CommSemiring F] {S Data : Type} {Gs : S → Type}
    {K : S → Type} [∀ s, Fintype (K s)] [∀ s, AddCommMonoid (Gs s)]
    [∀ s, Module F (Gs s)] (B : (s : S) → K s → Gs s)
    (rows : (s : S) → List (K s → F)) (out : Explained F Data Gs)
    (h : out.Valid (fun s => (rows s).map (Fintype.linearCombination F (B s)))) (s : S) :
    (transportExplained rows out s).map (Fintype.linearCombination F (B s)) =
      out.value.groups s := by
  have hs := h s
  simp only [transportExplained, List.map_map, Function.comp_def, linearCombination_transport]
  generalize out.value.groups s = gs, out.coefficients s = cs at hs ⊢
  induction hs with
  | nil => rfl
  | cons h _ ih => simp only [List.map_cons, h.2, ih]

/-- Enlarge a reduction basis by the fixed inputs, keeping their coordinates separate. -/
@[expose] def withFixed (fixed : List G) (B : κ → G) : Fin fixed.length ⊕ κ → G :=
  Sum.elim (fun i => fixed[i]) B

/-- Embed a programmed row into the enlarged basis with zero fixed-input coefficients. -/
@[expose] def hashRow [Zero F] (n : ℕ) (c : κ → F) : Fin n ⊕ κ → F :=
  Sum.elim (fun _ => 0) c

/-- The coordinate row for one fixed input in the enlarged basis. -/
@[expose] def fixedRow [Zero F] [One F] (n : ℕ) (i : Fin n) : Fin n ⊕ κ → F :=
  Sum.elim (fun j => if j = i then 1 else 0) (fun _ => 0)

/-- Hash rows evaluate identically after adjoining fixed inputs. -/
@[simp] theorem linearCombination_hashRow [CommSemiring F] [AddCommMonoid G] [Module F G]
    [Fintype κ] (fixed : List G) (B : κ → G) (c : κ → F) :
    Fintype.linearCombination F (withFixed fixed B) (hashRow fixed.length c) =
      Fintype.linearCombination F B c := by
  simp [Fintype.linearCombination_apply, withFixed, hashRow, Fintype.sum_sum_type]

/-- Each fixed-input row evaluates to that input. -/
@[simp] theorem linearCombination_fixedRow [CommSemiring F] [AddCommMonoid G] [Module F G]
    [Fintype κ] (fixed : List G) (B : κ → G) (i : Fin fixed.length) :
    Fintype.linearCombination F (withFixed fixed B) (fixedRow (F := F) fixed.length i) =
      fixed[i] := by
  simp [Fintype.linearCombination_apply, withFixed, fixedRow, Fintype.sum_sum_type, ite_smul]

end GroupModel.HashToGroup

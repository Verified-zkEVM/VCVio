/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import Mathlib.LinearAlgebra.Pi

/-! # Transport of algebraic explanations

Each chronological input has a recorded row over a reduction basis. Substituting those rows
into an explanation is matrix multiplication, expressed by `Interaction.evaluate` in the module
of coefficient vectors. The reduction basis can include fixed inputs using a sum index.
-/

public section

namespace GroupModel.HashToGroup

open Interaction

variable {F G κ : Type}

/-- Evaluate a finite coefficient vector over a reduction's fixed basis. -/
@[expose] def basisMap [CommSemiring F] [AddCommMonoid G] [Module F G] [Fintype κ]
    (B : κ → G) : (κ → F) →ₗ[F] G where
  toFun c := ∑ k, c k • B k
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

/-- A linear map commutes with evaluation of a chronological coefficient list. -/
theorem evaluate_linearMap [Semiring F]
    {V W : Type} [AddCommMonoid V] [AddCommMonoid W] [Module F V] [Module F W]
    (φ : V →ₗ[F] W) (c : List F) (rows : List V) :
    φ (evaluate c rows) = evaluate c (rows.map φ) := by
  simp only [evaluate, map_list_sum]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Substitute the recorded reduction-basis row for each chronological received input. -/
@[expose] def transport [Semiring F] (rows : List (κ → F)) (c : List F) : κ → F :=
  evaluate c rows

/-- Substitution preserves the group element represented by any coefficient list. -/
theorem basisMap_transport [CommSemiring F] [AddCommMonoid G] [Module F G] [Fintype κ]
    (B : κ → G) (rows : List (κ → F)) (c : List F) :
    basisMap B (transport rows c) = evaluate c (rows.map (basisMap B)) :=
  evaluate_linearMap (basisMap B) c rows

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
    (h : out.Valid (fun s => (rows s).map (basisMap (B s)))) (s : S) :
    (transportExplained rows out s).map (basisMap (B s)) = out.value.groups s := by
  have hs := h s
  simp only [transportExplained, List.map_map, Function.comp_def, basisMap_transport]
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
@[simp] theorem basisMap_hashRow [CommSemiring F] [AddCommMonoid G] [Module F G]
    [Fintype κ] (fixed : List G) (B : κ → G) (c : κ → F) :
    basisMap (withFixed fixed B) (hashRow fixed.length c) = basisMap B c := by
  simp [basisMap, withFixed, hashRow, Fintype.sum_sum_type]

/-- Each fixed-input row evaluates to that input. -/
@[simp] theorem basisMap_fixedRow [CommSemiring F] [AddCommMonoid G] [Module F G]
    [Fintype κ] (fixed : List G) (B : κ → G) (i : Fin fixed.length) :
    basisMap (withFixed fixed B) (fixedRow (F := F) fixed.length i) = fixed[i] := by
  simp [basisMap, withFixed, fixedRow, Fintype.sum_sum_type, ite_smul]

end GroupModel.HashToGroup

/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.EvalDist
public import Batteries.Control.OptionT

/-!
# Finite support of uniform sampling

This module collects `VCVio.OracleComp.ProbComp.Basic` with the finite supports of the uniform
sampling operations of `ProbComp`.
-/

@[expose] public section

open OracleComp ENNReal

universe u v w

namespace ProbComp

section uniformFin

@[simp]
lemma finSupport_uniformFin (n : ℕ) :
    finSupport (do $[0..n]) = Finset.univ := by
  rw [finSupport_eq_iff_support_eq_coe, support_uniformFin]; simp

end uniformFin

section uniformRange

@[simp]
lemma finSupport_uniformRange (n m : ℕ) (h : n < m) :
    finSupport (do uniformRange n m h) =
      Finset.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformRange n m h]

end uniformRange

section uniformSelectList

variable {α : Type} (xs : List α)

@[simp, grind =]
lemma finSupport_uniformSelectList [DecidableEq α] (xs : List α) :
    finSupport ($ xs) = xs.toFinset := match xs with
  | [] => by simp
  | x :: xs => by
      apply finSupport_eq_of_support_eq_coe
      simp [Set.ext_iff]

end uniformSelectList

section uniformSelectVector

variable {α : Type} {n : ℕ} (xs : Vector α (n + 1))

@[simp, grind =]
lemma finSupport_uniformSelectVector [DecidableEq α] :
    finSupport ($ xs) = xs.toList.toFinset := by
  rw [uniformSelect_eq_liftM_uniformSelect!, OptionT.finSupport_liftM]
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformSelectVector]

end uniformSelectVector

section uniformSelectFinset

variable {α : Type} (s : Finset α)

@[simp, grind =]
lemma finSupport_uniformSelectFinset [DecidableEq α] :
    finSupport ($ s) = if s.Nonempty then s else ∅ := by
  aesop (add norm uniformSelectFinset_def)

end uniformSelectFinset

section uniformSelectArray

variable {α : Type} (xs : Array α)

@[simp, grind =]
lemma finSupport_uniformSelectArray [DecidableEq α] :
    finSupport ($ xs) = xs.toList.toFinset := by
  simp [finSupport_eq_iff_support_eq_coe, support_uniformSelectArray]

-- TODO: `prEvent_uniformSelectArray` analogous to `prEvent_uniformSelectList`. It needs a
-- careful `Fin (xs.size - 1 + 1) ≃ Fin xs.size` reindexing that the present helpers don't cleanly
-- factor. Bridging through `xs.toList` once a clean `($ xs : OptionT ProbComp α) = $ xs.toList`
-- lemma lands is probably the right path.

end uniformSelectArray

section uniformSelectMultiset

variable {α : Type} (s : Multiset α)

@[simp, grind =]
lemma finSupport_uniformSelectMultiset [DecidableEq α] :
    finSupport ($ s) = s.toFinset := by
  apply finSupport_eq_of_support_eq_coe
  ext x
  simp [Multiset.mem_toFinset]

end uniformSelectMultiset

end ProbComp

section coinSpec
-- NOTE: This treats `coin` as essentially part of `ProbComp`, but it is more general.
-- In particular we can have a seperate theory of bounded uniform selection using only coins.

@[simp, grind =]
lemma finSupport_coin : finSupport coin = {true, false} := by aesop

end coinSpec

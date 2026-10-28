/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.BigOperators
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

-- Enumeration entry points inspected by the per-module initialization sweep.
import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Pi

/-! # Erasure and linear interpretation of algebraic transcripts

Recording received inputs does not change an interactive adversary's output. Linear maps
commute with evaluation of a chronological coefficient vector, so scalar or affine input
representations can be interpreted as concrete group inputs after execution.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.Interaction

/-- Discarding the received-input trace yields the raw explained program under the same handler.
This erases only bookkeeping, preserving every query and its reply-dependent continuation. -/
theorem Adversary.run_fst {Tag F Input Query Result : Type} {G : Tag → Type}
    {Reply : Query → Type} [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)]
    {N : Type → Type} [Monad N] [LawfulMonad N]
    (A : Adversary F G Input Query Reply Result)
    (impl : QueryImpl (plainSpec G Query Reply) N) (input : Message Input G) :
    Prod.fst <$> A.run impl input = simulateQ (fun q => impl q.value) (A.main input) := by
  have h := run'_simulateQ_eq_of_query_map_eq
    (fun q => StateT.mk fun basis => do
      let reply ← impl q.value
      pure (reply, extend basis reply.groups))
    (QueryImpl.liftTarget (StateT Unit N)
      (fun q => impl q.value : QueryImpl (explainedSpec F G Query Reply) N))
    (fun _ => ()) (fun q basis => by simp [QueryImpl.liftTarget]) (A.main input) input.groups
  simpa [Adversary.run, StateT.run'_eq] using h

/-- Applying a linear map to a represented point is the same as mapping its received inputs.
Coefficient vectors retain their chronological positions. -/
theorem evaluate_map {F V W : Type} [Semiring F]
    [AddCommMonoid V] [Module F V] [AddCommMonoid W] [Module F W]
    (f : V →ₗ[F] W) (coeff : List F) (inputs : List V) :
    evaluate coeff (inputs.map f) = f (evaluate coeff inputs) := by
  simp only [evaluate, map_list_sum]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Evaluation consumes one chronological coefficient for each received input. -/
theorem evaluate_cons {F V : Type} [Zero F] [AddMonoid V] [SMul F V]
    (coeff : List F) (v : V) (inputs : List V) :
    evaluate coeff (v :: inputs) = coeff.headD 0 • v + evaluate coeff.tail inputs := by
  cases coeff <;> simp [evaluate, List.mapIdx_cons]

/-- Evaluation of mapped inputs as a finite sum over their original chronological indices. -/
theorem evaluate_map_eq_sum {F V X : Type} [Semiring F] [AddCommMonoid V] [Module F V]
    (coeff : List F) (inputs : List X) (f : X → V) :
    evaluate coeff (inputs.map f) =
      ∑ i : Fin inputs.length, (coeff[i.val]?).getD 0 • f (inputs.get i) := by
  simp [evaluate, List.mapIdx_eq_ofFn, List.sum_ofFn]

/-- A valid explanation evaluates its first coefficient vector to its first output point.
Empty output lists use zero on both sides. -/
theorem Explained.evaluate_headD {Tag F Result : Type} {G : Tag → Type}
    [Semiring F] [∀ s, AddCommMonoid (G s)] [∀ s, Module F (G s)]
    (out : Explained F Result G) (inputs : Groups G) (h : out.Valid inputs) (s : Tag) :
    evaluate ((out.coefficients s).headD []) (inputs s) =
      (out.value.groups s).headD 0 := by
  have hv := h s
  cases hg : out.value.groups s with
  | nil =>
    have hc : out.coefficients s = [] := by simpa [hg] using hv
    simp [hc, evaluate, List.mapIdx_eq_ofFn]
  | cons σ rest =>
    cases hc : out.coefficients s with
    | nil => simp [hg, hc] at hv
    | cons c cs =>
      rw [hg, hc] at hv
      simpa [hg, hc] using (List.forall₂_cons.mp hv).1.2

end GroupModel.Interaction

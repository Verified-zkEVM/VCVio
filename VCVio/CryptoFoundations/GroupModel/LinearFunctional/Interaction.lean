/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.BigOperators

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
  unfold Adversary.run
  generalize A.main input = program
  generalize input.groups = basis
  induction program using OracleComp.inductionOn generalizing basis with
  | pure out => simp
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk,
        map_bind, bind_assoc, pure_bind]
      apply bind_congr
      intro reply
      exact ih reply (extend basis reply.groups)

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

end GroupModel.Interaction

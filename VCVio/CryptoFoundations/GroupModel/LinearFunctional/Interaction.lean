/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.BigOperators


/-! # Linear interpretation of algebraic transcripts

Linear maps commute with evaluation of a chronological coefficient vector (`evaluate_map`), so
scalar or affine input representations can be interpreted as concrete group inputs after
execution.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.Interaction

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

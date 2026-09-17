/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Support
public import PolyFun.PFunctor.Free.Support

/-!
# Operational support of polynomial free programs

Universe-polymorphic mapping and operation-object equations for PolyFun's native
`MonadAttach.support`. This module uses no probability interpretation.
-/

public section

universe uA uB v w

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v}

/-- Mapping a free tree maps its reachable leaves. -/
@[simp]
theorem support_map {γ : Type v} {δ : Type w} (f : γ → δ) (program : FreeM P γ) :
    support (FreeM.map f program) = f '' support program := by
  induction program with
  | pure value => simp
  | lift_bind position next ih =>
      change (⋃ direction, support (FreeM.map f (next direction))) =
        f '' (⋃ direction, support (next direction))
      simp [ih, Set.image_iUnion]

/-- An operation object can return exactly the outputs of its continuation. -/
theorem support_liftObj (object : P.Obj α) :
    MonadAttach.support (FreeM.liftObj object) = Set.range (PFunctor.Obj.snd object) := by
  cases object using PFunctor.Obj.rec
  simp [FreeM.liftObj, support_map, PFunctor.Obj.snd]

end PFunctor.FreeM

/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Basic

/-!
# Support of `SetM` and `Id` computations

A `SetM` computation's support is its underlying set, and an `Id` computation has its value as
its only possible output, with the corresponding finite support.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u}

namespace SetM

@[simp, grind =]
lemma support_eq_run (s : SetM α) : support s = s.run := rfl

end SetM

namespace Id

instance : HasEvalFinset Id where
  finSupport x := {x}
  coe_finSupport x := by
    change (↑({x.run} : Finset _) : Set _) = support (pure x.run : Id _)
    rw [Finset.coe_singleton]
    exact (MonadAttach.support_pure x.run).symm

@[grind =]
lemma support_eq_singleton (x : Id α) : support x = {x.run} := by
  change support (pure x.run : Id _) = {x.run}
  exact MonadAttach.support_pure _

@[simp, grind =]
lemma finSupport_eq_singleton [DecidableEq α] (x : Id α) : finSupport x = {x.run} := rfl

end Id

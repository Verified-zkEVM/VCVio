/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Basic

/-!
# Support of computations with `map`

The support of a constant map: `(fun _ => y) <$> mx` returns only `y` once `mx` has an output.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

/-! ## Support of a constant map -/

section const_support

variable [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m] (mx : m α) (y : β)

@[aesop safe norm, grind .]
lemma support_map_const
    (hx : (support mx).Nonempty) :
    support ((fun _ => y) <$> mx) = {y} := by
  aesop

@[grind .]
lemma finSupport_map_const
    [DecidableEq α] [DecidableEq β] [HasEvalFinset m]
    (hx : (finSupport mx).Nonempty) : finSupport ((fun _ => y) <$> mx) =
      if (finSupport mx).Nonempty then {y} else ∅ := by
  grind

end const_support

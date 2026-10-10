/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Seq
public import ToMathlib.Data.ENNReal.SumSquares

/-!
# Support of computations with `Prod`

The support and finite support of pairs of independent computations, `Prod.mk <$> mx <*> my`.
-/

@[expose] public section

open ENNReal Prod

universe u v

variable {m : Type u → Type v} {α β γ δ : Type u}

/-! ## Support of pairs -/

section support

variable [Monad m] [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]
variable (mx : m α) (my : m β) (f : α → γ) (g : β → δ)

@[simp high]
lemma support_seq_map_prod_mk :
    support (Prod.mk <$> mx <*> my) = support mx ×ˢ support my := by
  simp [Set.ext_iff]

lemma finSupport_seq_map_prod_mk
    [HasEvalFinset m] [DecidableEq α] [DecidableEq β] :
    finSupport (Prod.mk <$> mx <*> my) = Finset.product (finSupport mx) (finSupport my) := by
  simp

@[simp high]
lemma support_seq_map_prod_mk_eq_sprod :
    support ((f ·, g ·) <$> mx <*> my) = (f '' support mx) ×ˢ (g '' support my) := by
  simp [Set.ext_iff]; grind

lemma finSupport_seq_map_prod_mk_eq_product
    [HasEvalFinset m] [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ] : finSupport ((f ·, g ·) <$> mx <*> my) =
      ((finSupport mx).image f).product ((finSupport my).image g) := by
  simp [Finset.ext_iff]; grind

end support

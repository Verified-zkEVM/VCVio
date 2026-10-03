/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Map
public import VCVio.EvalDist.Monad.Seq.Measure

/-!
# Support of computations with `seq`

The support and finite support of the monadic `seq`, `seqLeft`, and `seqRight` operations, and of
`f <$> mx <*> my`. Their output measures are in `VCVio.EvalDist.Monad.Seq.Measure`.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

open ENNReal

section seq

section support

variable [MonadAttach m] [ExactMonadAttach m]

lemma support_seq (mf : m (α → β)) (mx : m α) :
    support (mf <*> mx) = ⋃ f ∈ support mf, f '' support mx :=
  MonadAttach.support_seq mf mx

lemma mem_support_seq_iff (mf : m (α → β)) (mx : m α) (y : β) :
    y ∈ support (mf <*> mx) ↔ ∃ f ∈ support mf, ∃ x ∈ support mx, f x = y := by
  simp

@[simp]
lemma finSupport_seq [HasEvalFinset m]
    [DecidableEq (α → β)] [DecidableEq α] [DecidableEq β]
    (mf : m (α → β)) (mx : m α) :
    finSupport (mf <*> mx) = (finSupport mf).biUnion fun f => (finSupport mx).image f := by
  simp [seq_eq_bind_map]

end support

end seq

section seqLeft

section support

variable [MonadAttach m] [ExactMonadAttach m]

@[simp]
lemma support_seqLeft (mx : m α) (my : m β) [Decidable (support my).Nonempty] :
    support (mx <* my) = if (support my).Nonempty then support mx else ∅ := by
  rw [seqLeft_eq, Set.ext_iff]; aesop

end support

end seqLeft

section seqRight

section support

variable [MonadAttach m] [ExactMonadAttach m]

@[simp]
lemma support_seqRight (mx : m α) (my : m β) [Decidable (support mx).Nonempty] :
    support (mx *> my) = if (support mx).Nonempty then support my else ∅ := by
  rw [seqRight_eq, Set.ext_iff]; aesop

end support

end seqRight

section seq_map

variable (mx : m α) (my : m β) (f : α → β → γ)

section support

variable [MonadAttach m] [ExactMonadAttach m]

lemma support_seq_map_eq_image2 :
    support (f <$> mx <*> my) = Set.image2 f (support mx) (support my) := by
  ext z; simp [seq_eq_bind_map, Set.mem_image2]

@[simp low + 1]
lemma finSupport_seq_map_eq_image2 [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] :
    finSupport (f <$> mx <*> my) = Finset.image₂ f (finSupport mx) (finSupport my) := by
  ext z; simp [seq_eq_bind_map, Finset.mem_image₂]

end support

section operational

variable [MonadAttach m] [ExactMonadAttach m]

lemma mem_support_seq_map_iff_of_injective2 (hf : f.Injective2) (x : α) (y : β) :
    f x y ∈ support (f <$> mx <*> my) ↔ x ∈ support mx ∧ y ∈ support my := by
  rw [support_seq_map_eq_image2, Set.mem_image2_iff hf]

lemma mem_finSupport_seq_map_iff_of_injective2 [HasEvalFinset m]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (hf : f.Injective2) (x : α) (y : β) :
    f x y ∈ finSupport (f <$> mx <*> my) ↔ x ∈ finSupport mx ∧ y ∈ finSupport my := by
  rw [finSupport_seq_map_eq_image2, Finset.mem_image₂_iff hf]

lemma support_seq_map_swap :
    support (Function.swap f <$> my <*> mx) = support (f <$> mx <*> my) := by
  simp only [support_seq_map_eq_image2, Set.image2_swap f]

lemma finSupport_seq_map_swap [HasEvalFinset m] [DecidableEq γ] :
    finSupport (Function.swap f <$> my <*> mx) = finSupport (f <$> mx <*> my) := by
  classical
  simp only [finSupport_seq_map_eq_image2, Finset.image₂_swap f]

end operational

end seq_map

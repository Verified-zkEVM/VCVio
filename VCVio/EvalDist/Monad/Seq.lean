/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Map
public import VCVio.EvalDist.Monad.Seq.Measure

/-!
# Evaluation Distributions of Computations with `seq`

File for lemmas about `evalSPMF` and `support` involving the monadic `seq`, `seqLeft`,
and `seqRight` operations.

TODO: many lemmas should probably have mirrored versions for `bind_map`.
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

section spmf

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

@[grind norm]
lemma evalSPMF_seq (mf : m (α → β)) (mx : m α) :
    𝒮[mf <*> mx] = 𝒮[mf] <*> 𝒮[mx] := by simp [monad_norm]

variable [MonadAttach m] [EvalDistCompatible m]

@[simp, grind =_]
lemma probFailure_seq (mf : m (α → β)) (mx : m α) :
    Pr[⊥ | mf <*> mx] = Pr[⊥ | mf] + Pr[⊥ | mx] - Pr[⊥ | mf] * Pr[⊥ | mx] := by
  rw [seq_eq_bind_map]
  exact probFailure_bind_of_const' probFailure_ne_top (fun g _ => probFailure_map mx g)

end spmf

end seq

section seqLeft

section support

variable [MonadAttach m] [ExactMonadAttach m]

@[simp]
lemma support_seqLeft (mx : m α) (my : m β) [Decidable (support my).Nonempty] :
    support (mx <* my) = if (support my).Nonempty then support mx else ∅ := by
  rw [seqLeft_eq, Set.ext_iff]; aesop

end support

section spmf

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

@[grind norm]
lemma evalSPMF_seqLeft (mx : m α) (my : m β) :
    𝒮[mx <* my] = 𝒮[mx] <* 𝒮[my] := by
  simp [seqLeft_eq]

@[simp, grind =_]
lemma probOutput_seqLeft (mx : m α) (my : m β) (x : α) :
    Pr[= x | mx <* my] = (1 - Pr[⊥ | my]) * Pr[= x | mx] := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  simpa only [MeasureTheory.Measure.smul_apply, smul_eq_mul, evalDist_apply_univ,
    evalDist_apply_singleton] using
    congrArg (fun μ : MeasureTheory.Measure α => μ {x}) (evalDist_seqLeft mx my)

@[simp, grind =_]
lemma probEvent_seqLeft (mx : m α) (my : m β) (p : α → Prop) :
    Pr[ p | mx <* my] = (1 - Pr[⊥ | my]) * Pr[ p | mx] := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  simpa only [MeasureTheory.Measure.smul_apply, smul_eq_mul, evalDist_apply_univ,
    evalDist_apply_setOf] using
    congrArg (fun μ : MeasureTheory.Measure α => μ {x | p x}) (evalDist_seqLeft mx my)

variable [MonadAttach m] [EvalDistCompatible m]

@[simp, grind =_]
lemma probFailure_seqLeft (mx : m α) (my : m β) :
    Pr[⊥ | mx <* my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by
  rw [seqLeft_eq, probFailure_seq, probFailure_map]

end spmf

end seqLeft

section seqRight

section support

variable [MonadAttach m] [ExactMonadAttach m]

@[simp]
lemma support_seqRight (mx : m α) (my : m β) [Decidable (support mx).Nonempty] :
    support (mx *> my) = if (support mx).Nonempty then support my else ∅ := by
  rw [seqRight_eq, Set.ext_iff]; aesop

end support

section spmf

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

@[grind norm]
lemma evalSPMF_seqRight (mx : m α) (my : m β) :
    𝒮[mx *> my] = 𝒮[mx] *> 𝒮[my] := by
  simp [seqRight_eq]

variable [MonadAttach m] [EvalDistCompatible m]

@[simp, grind =_]
lemma probOutput_seqRight (mx : m α) (my : m β) (y : β) :
    Pr[= y | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by
  simp [seqRight_eq, seq_eq_bind_map, probOutput_bind_const]

@[simp, grind =_]
lemma probFailure_seqRight (mx : m α) (my : m β) :
    Pr[⊥ | mx *> my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by
  rw [seqRight_eq, probFailure_seq, probFailure_map]

@[simp, grind =_]
lemma probEvent_seqRight (mx : m α) (my : m β) (p : β → Prop) :
    Pr[ p | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[ p | my] := by
  simp [seqRight_eq, seq_eq_bind_map, probEvent_bind_const]

end spmf

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

section spmf

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

lemma probOutput_seq_map_eq_tsum (z : γ) :
    Pr[= z | f <$> mx <*> my] = ∑' (x : α) (y : β),
      Pr[= x | mx] * Pr[= y | my] * Pr[= z | (pure (f x y) : m γ)] := by
  simp only [monad_norm, Function.comp,
    probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left, mul_assoc]

section injective2

lemma probOutput_seq_map_eq_mul_of_injective2 (hf : f.Injective2) (x : α) (y : β) :
    Pr[= f x y | f <$> mx <*> my] = Pr[= x | mx] * Pr[= y | my] := by
  rw [probOutput_seq_map_eq_tsum]
  simp only [probOutput_pure_eq_indicator, Set.indicator, mul_ite, mul_zero]
  refine (tsum_eq_single x fun x' hx' => ?_).trans ?_
  · exact ENNReal.tsum_eq_zero.mpr fun b => ite_eq_right fun h' => hx' (hf h').1.symm
  · refine (tsum_eq_single y fun y' hy' => ?_).trans ?_
    · exact ite_eq_right fun h' => hy' (hf h').2.symm
    · simp

end injective2

section swap

lemma probOutput_seq_map_swap (z : γ) :
    Pr[= z | Function.swap f <$> my <*> mx] = Pr[= z | f <$> mx <*> my] := by
  simp only [probOutput_seq_map_eq_tsum, Function.swap]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun x' => tsum_congr fun y' => by ring

end swap

end spmf

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

section mixed

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadAttach m] [EvalDistCompatible m]

end mixed

end seq_map

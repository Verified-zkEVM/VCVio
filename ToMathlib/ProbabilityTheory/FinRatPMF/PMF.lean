/-
Copyright (c) 2025 Quang Dao, 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/

module
public import ToMathlib.ProbabilityTheory.FinRatPMF.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Distributions.Uniform
public import PolyFun.Control.Monad.Hom

/-!
# Discrete interoperability for finite rational distributions

The rational samplers and their distributional quotient have probability mass function
interpretations. These maps preserve pure and bind and identify distributional equality.
-/

public section

universe u

namespace FinRatPMF

variable {α β γ : Type u}

namespace Raw

/-- Convert to a `PMF` by mapping weights through `ℚ≥0 → ℝ≥0 → ℝ≥0∞`. -/
@[expose]
noncomputable def toPMF [DecidableEq α] (p : Raw α) : PMF α :=
  PMF.ofFinset (fun x => ((p.prob x : NNReal) : ENNReal)) p.support
    (by
      have hsum : p.support.sum p.prob = (1 : ℚ≥0) := by
        rw [sum_prob_eq_sum]
        simpa [Raw.toList] using p.sum_eq_one
      rw [← ENNReal.ofNNReal_finsetSum, ← NNRat.cast_sum (K := NNReal)]
      change (((p.support.sum p.prob : ℚ≥0) : NNReal) : ENNReal) = 1
      simpa using congrArg (fun q : ℚ≥0 => ((q : NNReal) : ENNReal)) hsum)
    (fun a ha => by simp [prob_eq_zero_of_not_mem_support p ha])

@[simp] lemma toPMF_apply [DecidableEq α] (p : Raw α) (x : α) :
    p.toPMF x = ((p.prob x : NNReal) : ENNReal) := rfl

@[simp] lemma toPMF_pure [DecidableEq α] (a : α) :
    (pure a : Raw α).toPMF = PMF.pure a := by
  ext x
  rw [toPMF_apply, PMF.pure_apply, prob_pure]
  split_ifs <;> simp [*]

@[simp] lemma toPMF_uniform [FinEnum α] [Inhabited α] :
    (Raw.uniform (α := α)).toPMF = PMF.uniformOfFintype α := by
  ext x
  rw [toPMF_apply, PMF.uniformOfFintype_apply, prob_uniform]
  simp [NNRat.cast_inv]

@[simp] lemma toPMF_coin : Raw.coin.toPMF = PMF.uniformOfFintype Bool := by
  ext b
  rw [toPMF_apply, PMF.uniformOfFintype_apply, prob_coin]
  simp [NNRat.cast_inv]

@[simp] lemma toPMF_bind [DecidableEq α] [DecidableEq β] (m : Raw α) (f : α → Raw β) :
    (m >>= f).toPMF = m.toPMF >>= fun a => (f a).toPMF := by
  ext y
  rw [toPMF_apply]
  change (((m >>= f).prob y : NNReal) : ENNReal) =
      ∑' a, m.toPMF a * (f a).toPMF y
  rw [tsum_eq_sum (s := m.support)]
  · simp_rw [Raw.toPMF_apply, ← ENNReal.coe_mul, ← NNRat.cast_mul]
    rw [← ENNReal.ofNNReal_finsetSum, ← NNRat.cast_sum (K := NNReal), Raw.prob_bind]
  · intro x hx
    simp [Raw.toPMF_apply, prob_eq_zero_of_not_mem_support m hx]

@[expose]
noncomputable def toPMFHom : Raw →ᵐ PMF where
  toFun _ p := @Raw.toPMF _ (Classical.decEq _) p
  toFun_pure' := by
    intro α x
    let := Classical.decEq α
    exact Raw.toPMF_pure (α := α) x
  toFun_bind' := by
    intro α β x y
    let := Classical.decEq α
    let := Classical.decEq β
    exact Raw.toPMF_bind (α := α) (β := β) x y

end Raw

/-! ### Connection to `PMF` -/

/-- Convert a `FinRatPMF` to a `PMF`. Well-defined since `SameDist` implies equal `toPMF`. -/
@[expose]
noncomputable def toPMF (p : FinRatPMF α) : PMF α := by
  classical
  refine Quotient.lift (fun raw => @Raw.toPMF _ (Classical.decEq _) raw) ?_ p
  intro a b hab
  refine PMF.ext fun x => ?_
  rw [Raw.toPMF_apply, Raw.toPMF_apply]
  exact congrArg (fun q : ℚ≥0 => ((q : NNReal) : ENNReal)) (hab x)

@[simp] lemma toPMF_mk (p : Raw α) : toPMF (mk p) = @Raw.toPMF _ (Classical.decEq _) p := by
  classical
  unfold toPMF mk
  rw [Quotient.lift_mk]

@[simp] lemma toPMF_pure (a : α) : toPMF (pure a : FinRatPMF α) = PMF.pure a := by
  classical
  rw [show (pure a : FinRatPMF α) = mk (Raw.pure a) by rfl, toPMF_mk]
  exact Raw.toPMF_pure a

lemma toPMF_out (p : FinRatPMF α) :
    toPMF p = @Raw.toPMF _ (Classical.decEq _) (Quotient.out p) := by
  classical
  refine Quotient.inductionOn p ?_
  intro q
  refine PMF.ext fun x => ?_
  change (toPMF (mk q : FinRatPMF α)) x =
    ((@Raw.toPMF _ (Classical.decEq _) (Quotient.out (mk q : FinRatPMF α)) : PMF α) x)
  rw [toPMF_mk, Raw.toPMF_apply, Raw.toPMF_apply]
  exact congrArg (fun r : ℚ≥0 => ((r : NNReal) : ENNReal))
    ((SameDist.symm <| Quotient.exact (Quotient.out_eq (mk q : FinRatPMF α))) x)

@[simp] lemma toPMF_bind (ma : FinRatPMF α) (f : α → FinRatPMF β) :
    toPMF (ma >>= f) = toPMF ma >>= fun a => toPMF (f a) := by
  classical
  calc
    toPMF (ma >>= f)
        = @Raw.toPMF _ (Classical.decEq _)
            (Raw.bind (Quotient.out ma) (fun a => Quotient.out (f a))) := by
              rw [bind_eq_out, toPMF_mk]
    _ = @Raw.toPMF _ (Classical.decEq _) (Quotient.out ma) >>=
          fun a => @Raw.toPMF _ (Classical.decEq _) (Quotient.out (f a)) :=
            Raw.toPMF_bind _ _
    _ = toPMF ma >>= fun a => toPMF (f a) := by
          rw [← toPMF_out ma]
          congr 1
          funext a
          rw [← toPMF_out (f a)]

@[expose]
noncomputable def toPMFHom : FinRatPMF →ᵐ PMF where
  toFun _ p := toPMF p
  toFun_pure' := by
    intro α x
    exact toPMF_pure x
  toFun_bind' := by
    intro α β x y
    exact toPMF_bind x y

lemma toPMF_injective : Function.Injective (toPMF (α := α)) := by
  classical
  intro p q hpq
  revert hpq
  refine Quotient.inductionOn₂ p q fun a b hab => ?_
  apply Quotient.sound
  intro x
  have hmass :
      ((@Raw.prob _ (Classical.decEq _) a x : NNReal) : ENNReal) =
        ((@Raw.prob _ (Classical.decEq _) b x : NNReal) : ENNReal) :=
    congrArg (fun p : PMF α => p x) hab
  exact_mod_cast hmass

end FinRatPMF

/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.ProbabilityTheory.FinRatPMF
public import VCVio.EvalDist.Defs.Basic

/-!
# Measure Semantics for `FinRatPMF.Raw`

The executable rational distribution has a measure interpretation through `PMF`.
Its namespaced `Raw.support` records positive mass; raw arrays may also retain
zero-weight entries, so generic `MonadAttach.support` is not defined for `Raw`.
-/

@[expose] public section

universe u

namespace FinRatPMF
namespace Raw

variable {α : Type u}

noncomputable instance : MonadLift Raw PMF where
  monadLift := Raw.toPMFHom.toFun _

noncomputable instance : LawfulMonadLift Raw PMF where
  monadLift_pure := Raw.toPMFHom.toFun_pure'
  monadLift_bind := Raw.toPMFHom.toFun_bind'

/-- For finite rational computations, the singleton measure is computed by `Raw.prob`.
The latter needs only decidable equality and can be evaluated by `#eval`. -/
theorem evalDist_apply_singleton_eq_prob [MeasurableSpace α]
    [MeasurableSingletonClass α] [dec : DecidableEq α] (mx : Raw α) (x : α) :
    𝒟[mx] {x} = ((mx.prob x : NNReal) : ENNReal) := by
  rw [evalDist_apply_singleton, probOutput_def, evalSPMF_def]
  change ((liftM (liftM mx : PMF α) : SPMF α) x) = _
  rw [SPMF.liftM_apply]
  change (@Raw.toPMF _ (Classical.decEq _) mx) x = _
  rw [@Raw.toPMF_apply _ (Classical.decEq _) mx x]
  exact congrArg (fun q : ℚ≥0 => ((q : NNReal) : ENNReal))
    (Raw.prob_eq_prob (Classical.decEq _) dec mx x)

end Raw
end FinRatPMF

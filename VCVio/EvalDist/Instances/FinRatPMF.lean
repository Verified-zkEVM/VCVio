/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.ProbabilityTheory.FinRatPMF
public import VCVio.EvalDist.Defs.Basic

/-!
# EvalDist Instances for `FinRatPMF.Raw`

This file exposes the executable `FinRatPMF.Raw` monad to the generic `EvalDist` API.
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

/-- Direct `MonadLiftT Raw SetM` defined via the underlying PMF support. The generic
`MonadLiftT SPMF SetM` is non-transitive (declared as `MonadLiftT`, not `MonadLift`,
so `monadLiftTrans` cannot chain through it), so every monad with probabilistic
semantics declares its `SetM` lift directly. -/
noncomputable instance instMonadLiftTRawSetM : MonadLiftT Raw SetM where
  monadLift mx := ((liftM mx : PMF _).support : Set _)

noncomputable instance instLawfulMonadLiftTRawSetM : LawfulMonadLiftT Raw SetM where
  monadLift_pure x := by
    change ((liftM (pure x : Raw _) : PMF _).support : Set _) = {x}
    have : (liftM (pure x : Raw _) : PMF _) = pure x :=
      LawfulMonadLift.monadLift_pure (m := Raw) (n := PMF) x
    rw [this]
    exact PMF.support_pure x
  monadLift_bind mx my := by
    change ((liftM (mx >>= my) : PMF _).support : Set _) =
      Bind.bind (m := SetM)
        ((liftM mx : PMF _).support : Set _)
        (fun x => ((liftM (my x) : PMF _).support : Set _))
    have hbind : (liftM (mx >>= my) : PMF _) =
        (liftM mx : PMF _) >>= fun x => (liftM (my x) : PMF _) :=
      LawfulMonadLift.monadLift_bind (m := Raw) (n := PMF) mx my
    rw [hbind]
    exact PMF.support_bind _ _

/-- Compatibility: `Raw`'s SetM support equals the SPMF support of its `evalSPMF`. -/
noncomputable instance : EvalDistCompatible Raw where
  support_eq_SPMF_support mx := by
    change ((liftM mx : PMF _).support : Set _) =
      SPMF.support (liftM (liftM mx : PMF _) : SPMF _)
    rw [SPMF.support_liftM]

instance : HasEvalFinset Raw where
  finSupport := Raw.support
  coe_finSupport mx := by
    ext x
    rw [Finset.mem_coe, _root_.mem_support_iff, Raw.mem_support_iff, probOutput_def, evalSPMF_def]
    change mx.prob x ≠ 0 ↔ (liftM (liftM mx : PMF _) : SPMF _) x ≠ 0
    rw [SPMF.liftM_apply]
    change mx.prob x ≠ 0 ↔ ((@Raw.toPMF _ (Classical.decEq _) mx) x) ≠ 0
    simp [Raw.toPMF_apply, Raw.prob_eq_prob inferInstance (Classical.decEq _) mx x]

@[simp] lemma finSupport_eq_support [DecidableEq α] (mx : Raw α) :
    finSupport mx = mx.support := rfl

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

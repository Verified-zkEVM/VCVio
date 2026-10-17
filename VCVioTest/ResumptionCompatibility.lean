/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.ResumptionRejection
public import VCVio.EvalDist.ResumptionMeasure.Domain

/-! # Finite-program compatibility and the distinction between cutoff and divergence -/

public section

open PFunctor MeasureTheory ResumptionRejection
open scoped ENNReal

namespace VCVioTest.ResumptionCompatibility

/-- One visible request, with its answer returned unchanged. -/
@[expose]
def once : FreeM four (Fin 4) := .liftBind () pure

theorem once_bound (n : ℕ) (h : 0 < n) : once.IsTotalRollBound n := by
  simp only [once, FreeM.isTotalRollBound_liftBind_iff, FreeM.isTotalRollBound_pure]
  exact ⟨h, fun _ => trivial⟩

example : Resumption.outputMeasure 1 (FreeM.toResumption once) = FreeM.denote once :=
  Resumption.outputMeasure_toResumption once (once_bound 1 (by decide))

example : Resumption.outputMeasure 3 (FreeM.toResumption once) = FreeM.denote once :=
  Resumption.outputMeasure_toResumption once (once_bound 3 (by decide))

example : Resumption.returnedMeasure (FreeM.toResumption once) = FreeM.denote once :=
  Resumption.returnedMeasure_toResumption_of_bound once (once_bound 1 (by decide))

example : Resumption.outputMeasure 0 (FreeM.toResumption (pure (0 : Fin 4) : FreeM four _)) =
    Measure.dirac 0 := by simp

example : Resumption.truncateMeasure 0 sample {none} = 1 := by
  rw [cutoff_mass, pow_zero]

example : Resumption.truncateMeasure 1 sample {none} = (4 : ℝ≥0∞)⁻¹ := by
  rw [cutoff_mass, pow_one]

example : Resumption.returnedMeasure sample Set.univ = 1 := almost_sure_return

-- The ordinary-import bridge also accepts a nonzero operation/answer universe.
example {P : PFunctor.{1, 1}} [∀ a, MeasurableSpace (P.B a)]
    [∀ a, DiscreteMeasurableSpace (P.B a)] [P.AnswerMeasure]
    (c : FreeM P (ULift.{1} Bool)) {k : ℕ} (h : c.IsTotalRollBound k) :
    Resumption.returnedMeasure (FreeM.toResumption c) = FreeM.denote c :=
  Resumption.returnedMeasure_toResumption_of_bound c h

/-- Countably branching syntax can be well founded without a uniform finite depth. -/
abbrev NatBranch : PFunctor := PUnit y^ Nat

@[expose] def spine : Nat → FreeM NatBranch Unit
  | 0 => pure ()
  | n + 1 => .liftBind PUnit.unit (fun _ => spine n)

@[expose] def unboundedDepth : FreeM NatBranch Unit := .liftBind PUnit.unit spine

theorem spine_bound_iff (n k : Nat) : (spine n).IsTotalRollBound k ↔ n ≤ k := by
  induction n generalizing k with
  | zero => simp [spine]
  | succ n ih =>
      simp only [spine, FreeM.isTotalRollBound_liftBind_iff, ih]
      simp only [forall_const]
      omega

theorem unboundedDepth_no_bound (k : Nat) : ¬ unboundedDepth.IsTotalRollBound k := by
  rw [unboundedDepth, FreeM.isTotalRollBound_liftBind_iff]
  intro h
  have hk := (spine_bound_iff k (k - 1)).mp (h.2 k)
  omega

-- A total depth bound is deliberately unavailable; the general bridge still applies.
example [NatBranch.AnswerMeasure] :
    Resumption.returnedMeasure unboundedDepth.toResumption = FreeM.denote unboundedDepth :=
  Resumption.returnedMeasure_toResumption unboundedDepth

end VCVioTest.ResumptionCompatibility

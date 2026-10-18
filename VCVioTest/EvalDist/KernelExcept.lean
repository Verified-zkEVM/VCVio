/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.UniformThreshold.Budget.Semantics

/-! # Explicit errors retain private state in finite-client kernel laws -/

public section

open MeasureTheory ProbabilityTheory PFunctor
open scoped ENNReal

universe u

namespace VCVioTest.KernelExcept

/-- A Boolean operation leaves continuous private state to the handler. -/
abbrev signature : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

example {K : KernelHandler (signature.withExcept Bool) ℝ}
    {handler : Handler (ExceptT Bool (StateT ℝ ProbComp)) signature}
    (h : K.Realizes handler.exceptAnswers) (client : FreeM signature ℝ) (state : ℝ) :
    𝒟[((client.liftM handler).run).run state] =
      FreeM.runKernel K client.withExcept state := h.runExcept client state

open UniformThreshold UniformThreshold.Budget

example (cap : ℚ → Session → ℕ) (q : ℚ) : IsMarkovKernel (Budget.answerKernel cap q) :=
  inferInstance

example {α : Type} [MeasurableSpace α] (cap : ℚ → Session → ℕ)
    (client : FreeM spec.toPFunctor α) (state : Session) :
    𝒟[Budget.run cap client state] =
      FreeM.runKernel (Budget.answerKernel cap) client.withExcept state :=
  Budget.evalDist_run cap client state

/-- Exhausted budget gives an error with probability one and preserves the whole session. -/
example (p : Prefix) :
    Budget.answerKernel (fun _ _ => 0) (1 / 3) (p, 0) =
      Measure.dirac (Except.error Failure.budgetExhausted, (p, 0)) := by
  apply Budget.answerKernel_of_refused
  norm_num [Budget.charge]

/-- A continuous result does not need a discrete measurable-space instance for the error bound. -/
example (cap : ℚ → Session → ℕ) (client : FreeM spec.toPFunctor ℝ)
    (p : Prefix) (precision : ℕ) :
    𝒟[Budget.run cap client (p, Budget.charge precision)]
      {out | out.1 = .error .timeout} ≤ (2 : ℝ≥0∞)⁻¹ ^ precision :=
  Budget.timeout_le_geometric cap client p precision

/-- The reserve proof is independent of the result universe and permits continuous private state. -/
example {α : Type u} [MeasurableSpace α] (K : KernelHandler (signature.withExcept Bool) ℝ)
    (budget : ℝ → ℝ≥0∞)
    (hstep : ∀ a s, (∫⁻ out, out.1.casesOn (({true} : Set Bool).indicator (fun _ => 1))
      (fun _ => budget out.2) ∂K a s) ≤ budget s)
    (client : FreeM signature α) (s : ℝ) :
    FreeM.runKernel K client.withExcept s {out | out.1 = .error true} ≤ budget s := by
  simpa using FreeM.runKernel_withExcept_error_le K {true} (measurableSet_singleton _)
    budget hstep client s

example (client : FreeM spec.toPFunctor ℝ) (p : Prefix) (precision : ℕ) :
    𝒟[Budget.run halfAllowanceCap client (p, Budget.charge precision)]
      {out | out.1.toOption = none} ≤ (2 : ℝ≥0∞)⁻¹ ^ precision := by
  rw [← coe_charge]
  apply failure_le_allowance_halfAllowanceCap
  exact pow_pos (by norm_num : (0 : ℚ≥0) < 1 / 2) _

end VCVioTest.KernelExcept

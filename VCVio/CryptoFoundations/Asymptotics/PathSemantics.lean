/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public import VCVio.EvalDist.Expectation
public import VCVio.EvalDist.PFunctor
public import PolyFun.PFunctor.Free.Path.Execution

/-!
# Probability semantics of typed interaction paths

Every probabilistic computation in VCVio is first a well-founded free polynomial program. Its
canonical `FreeM.withPath` instrumentation returns the fully typed root-to-leaf path selected by
the oracle answers. Probability enters only afterward, by folding that syntax with the configured
per-query distributions.

This module records the two bridges needed by complexity proofs. Erasing a sampled path recovers
the ordinary output distribution exactly, and a worst-case syntactic query bound bounds the
expected sampled path length. The latter specializes a strict-PPT witness without introducing a
second probabilistic cost model or trusting a numeric meter.
-/

@[expose] public section

open scoped ENNReal

universe u v w x

namespace PFunctor.FreeM

variable {P : PFunctor.{u, u}} {α : Type u}

/-! ## Typed path distributions -/

/-- Distribution of fully typed root-to-leaf paths through a free polynomial program.

The path is produced syntactically by `withPath`; `evalDist` then supplies the configured
per-operation probability semantics. -/
noncomputable def pathDistribution [P.IsProbabilitySpec] (program : FreeM P α) :
    SPMF (Path program) :=
  𝒟[withPath program]

/-- Forgetting a sampled typed path and retaining its selected leaf recovers the program's
ordinary output distribution exactly. -/
theorem map_output_pathDistribution [P.IsProbabilitySpec] (program : FreeM P α) :
    output program <$> pathDistribution program = 𝒟[program] := by
  change output program <$> 𝒟[withPath program] = 𝒟[program]
  rw [← evalDist_map]
  change evalDist (FreeM.map (output program) (withPath program)) = evalDist program
  exact congrArg (fun computation : FreeM P α ↦ evalDist computation)
    (map_output_withPath program)

/-! ## Syntactic and expected path lengths -/

/-- Every complete typed path through a totally query-bounded program fits the same bound. -/
theorem Path.trace_length_le_of_isTotalRollBound (program : FreeM P α) {bound : ℕ}
    (hbound : program.IsTotalRollBound bound) (path : Path program) :
    (Path.trace program path).length ≤ bound := by
  induction program generalizing bound with
  | pure result =>
      change 0 ≤ bound
      exact Nat.zero_le bound
  | lift_bind position next ih =>
      rcases path with ⟨answer, tail⟩
      rw [isTotalRollBound_lift_bind_iff] at hbound
      change (Path.trace (next answer) tail).length + 1 ≤ bound
      have htail := ih answer (hbound.2 answer) tail
      omega

/-- Expected number of visible query-answer steps in the sampled typed path. -/
noncomputable def expectedQueryCount [P.IsProbabilitySpec] (program : FreeM P α) : ℝ≥0∞ :=
  OracleComp.EvalDist.expectedValue (withPath program) fun path ↦
    ((Path.trace program path).length : ℝ≥0∞)

/-- A branchwise syntactic query bound also bounds expected sampled query count.

This is a consequence of the pointwise path theorem and total probability mass; it is not an
independent expected-cost assumption. -/
theorem expectedQueryCount_le_of_isTotalRollBound [P.IsProbabilitySpec]
    (program : FreeM P α) {bound : ℕ} (hbound : program.IsTotalRollBound bound) :
    expectedQueryCount program ≤ (bound : ℝ≥0∞) := by
  unfold expectedQueryCount
  calc
    OracleComp.EvalDist.expectedValue (withPath program) (fun path ↦
        ((Path.trace program path).length : ℝ≥0∞)) ≤
        OracleComp.EvalDist.expectedValue (withPath program) (fun _ ↦ (bound : ℝ≥0∞)) :=
      OracleComp.EvalDist.expectedValue_mono _ fun path ↦ by
        exact_mod_cast Path.trace_length_le_of_isTotalRollBound program hbound path
    _ = (bound : ℝ≥0∞) :=
      OracleComp.EvalDist.expectedValue_const
        (probFailure_eq_zero (mx := withPath program)) (bound : ℝ≥0∞)

end PFunctor.FreeM

namespace OracleComp.Complexity

open PFunctor
open PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {label : Type x}
  {contract : OracleContract Q bd.interface label}
  {program : input → FreeM p output}

namespace StrictPPTWitness

/-- Under a model admitting every typed oracle reply, a strict-PPT witness's query polynomial
bounds the expected length of the probabilistically sampled typed path.

The all-answers premise is explicit because `StrictPPTWitness` can also describe relational
contracts which intentionally exclude some typed replies. A later support-aware theorem may weaken
it to almost-sure conformance without changing the syntactic definition. -/
theorem expectedQueryCount_le [p.IsProbabilitySpec]
    (witness : StrictPPTWitness Q bd contract program) (model : contract.Model)
    (hAllows : ∀ position answer, model.resourceModel.allows position answer)
    (value : input) :
    PFunctor.FreeM.expectedQueryCount (program value) ≤
      ((witness.polynomial.eval model.modulus (Q.size bd.input value)).queries : ℝ≥0∞) :=
  PFunctor.FreeM.expectedQueryCount_le_of_isTotalRollBound (program value)
    (witness.isTotalRollBound model hAllows value)

end StrictPPTWitness

end OracleComp.Complexity

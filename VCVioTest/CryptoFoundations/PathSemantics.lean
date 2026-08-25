/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.PathSemantics

/-!
# Typed-path probability bridge checks

Compile-time checks for the path distribution, its exact output marginal, and the derivation of
expected query bounds from branchwise syntactic bounds.
-/

public section

open scoped ENNReal

universe u v w x

open PFunctor
open PFunctor.DynSystem.DynComputation

#check FreeM.pathDistribution
#check FreeM.map_output_pathDistribution
#check FreeM.Path.trace_length_le_of_isTotalRollBound
#check FreeM.expectedQueryCount
#check FreeM.expectedQueryCount_le_of_isTotalRollBound
#check OracleComp.Complexity.StrictPPTWitness.expectedQueryCount_le

namespace PFunctor.FreeM

variable {P : PFunctor.{u, u}} [P.IsProbabilitySpec]

/-- A single syntactic oracle operation has expected path length at most one because every typed
path contains exactly that one operation. -/
example (position : P.A) :
    expectedQueryCount (FreeM.lift position : FreeM P (P.B position)) ≤ (1 : ℝ≥0∞) := by
  simpa using expectedQueryCount_le_of_isTotalRollBound
    (FreeM.lift position : FreeM P (P.B position)) (bound := 1) (by
      change 0 < 1 ∧ ∀ answer : P.B position,
        IsTotalRollBound (FreeM.pure (P := P) answer) 0
      simp)

end PFunctor.FreeM

namespace OracleComp.Complexity

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  [p.IsProbabilitySpec]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {label : Type x}
  {contract : OracleContract Q bd.interface label}
  {program : input → FreeM p output}

/-- The probabilistic corollary consumes the existing strict witness and an explicit all-answers
model; it cannot be constructed from a query-count assertion alone. -/
example (witness : StrictPPTWitness Q bd contract program) (model : contract.Model)
    (hAllows : ∀ position answer, model.resourceModel.allows position answer)
    (value : input) :
    FreeM.expectedQueryCount (program value) ≤
      ((witness.polynomial.eval model.modulus (Q.size bd.input value)).queries : ℝ≥0∞) :=
  witness.expectedQueryCount_le model hAllows value

end OracleComp.Complexity

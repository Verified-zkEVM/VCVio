/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public import VCVio.EvalDist.PFunctorPath

/-!
# Expected path bounds for strict PPT witnesses

This module connects VCVio's strict oracle-complexity witnesses to the native measure observer in
`VCVio.EvalDist.PFunctorPath`. The underlying path measure, output marginal, exact-length law, and
worst-case-to-expectation theorem are independent of the selected complexity backend.
-/

@[expose] public section

open scoped ENNReal

universe u v w x

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
bounds the expected length of the measure-denoted typed path.

The all-answers premise is explicit because `StrictPPTWitness` can also describe relational
contracts which intentionally exclude some typed replies. A later support-aware theorem may
weaken it to almost-sure conformance without changing the syntactic definition. -/
theorem expectedQueryCount_le [∀ position, MeasurableSpace (p.B position)]
    [p.IsMeasureSpec] [∀ position, DiscreteMeasurableSpace (p.B position)]
    (witness : StrictPPTWitness Q bd contract program) (model : contract.Model)
    (hAllows : ∀ position answer, model.resourceModel.allows position answer)
    (value : input) :
    PFunctor.FreeM.expectedQueryCount (program value) ≤
      ((witness.polynomial.eval model.modulus (Q.size bd.input value)).queries : ℝ≥0∞) :=
  PFunctor.FreeM.expectedQueryCount_le_of_isTotalRollBound (program value)
    (witness.isTotalRollBound model hAllows value)

end StrictPPTWitness

end OracleComp.Complexity

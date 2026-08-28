/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioComplexity
public import VCVioComplexityTest.Backend.OracleCanary

/-!
# Aggregate backend canaries

These compile-time checks exercise the public exact-machine, polynomial-realizer, and strict-PPT
facades through the package umbrella. No test constructs an additional Turing machine.
-/

@[expose] public section

namespace VCVioComplexityTest.Canaries

open PFunctor
open OracleComp.Complexity
open VCVioComplexity.Backend.TuringMachine

local instance : stepClass.HasProd := hasProd
local instance : stepClass.HasSum := hasSum
local instance : stepClass.HasOption := hasOption

/-- The free-monad theorem remains available through the aggregate import. -/
example :
    IsOraclePPTBy quantitativeStepClass coinBoundary
      (fairCoinContract quantitativeStepClass coinBoundary.interface) oneCoinProgram :=
  oneCoin_isOraclePPTBy

/-- The same witness is exposed through the canonical `OracleComp` fair-coin facade. -/
example : IsPPTBy quantitativeStepClass coinBoundary oneCoinOracleProgram :=
  oneCoin_isPPTBy

/-- The facade introduces no translation layer in the underlying fully syntactic program. -/
example (input : Unit) :
    (oneCoinOracleProgram input).toFreeM = oneCoinProgram input :=
  oneCoinOracleProgram_toFreeM input

/-- Exact run time bounds raw output length in the public adapter. -/
example {workTapes : ℕ} {machine : _root_.Complexity.TM workTapes}
    {input output : Word} (run : ExactRun machine input output) :
    output.length ≤ run.steps :=
  run.output_length_le_steps

/-- A polynomial machine can derive a complete PolyFun realizer from the same time proof. -/
noncomputable example :
    polynomialQuantitativeStepClass.PolyRealizer .unit .unit id :=
  Primitive.unitIdentityPolynomial.toPolyRealizerFromTime

end VCVioComplexityTest.Canaries

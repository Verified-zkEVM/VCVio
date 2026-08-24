/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Polynomial
public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public meta import VCVio.CryptoFoundations.Asymptotics.ComplexityTactics

/-!
# Complexity-tactic checks

Compile-time checks for strict `@[ppt_primitive]` validation and the bounded `ppt`, `ppt?`, and
`ppt using` lookup modes. The test backend has zero cost and size solely to provide small concrete
`PolyRealizer` values; the tactic never constructs those values itself.
-/

@[expose] public section

open PFunctor

namespace OracleComp.Complexity.ComplexityTacticsTest

/-- Qualitative carrier used only by the tactic smoke tests. -/
def stepClass : StepClass where
  Str _ := PUnit
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial

/-- The unique test representation of a type. -/
def representation (A : Type) : stepClass.Str A :=
  PUnit.unit

/-- Zero-cost quantitative backend used to construct concrete test certificates. -/
def backend : QuantitativeStepClass stepClass where
  Realizer _ _ _ := PUnit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := trivial

/-- Every function has an explicit zero-cost polynomial realizer in the test backend. -/
def polyRealizer {A B : Type} (a : stepClass.Str A) (b : stepClass.Str B) (f : A → B) :
    backend.PolyRealizer a b f where
  code := PUnit.unit
  work := Complexity.FirstOrderPolynomial.const 0
  outputSize := Complexity.FirstOrderPolynomial.const 0
  work_le _ := le_rfl
  outputSize_le _ := le_rfl

abbrev unitRepresentation : stepClass.Str Unit := representation Unit
abbrev boolRepresentation : stepClass.Str Bool := representation Bool

@[ppt_primitive]
def boolIdentityPrimitive :
    backend.PolyRealizer boolRepresentation boolRepresentation id :=
  polyRealizer boolRepresentation boolRepresentation id

@[ppt_primitive]
def unitIdentityPrimitive :
    backend.PolyRealizer unitRepresentation unitRepresentation id :=
  polyRealizer unitRepresentation unitRepresentation id

example : backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt

example (hypothesis : backend.PolyRealizer unitRepresentation unitRepresentation id) :
    backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt

example : backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt using unitIdentityPrimitive

#guard_msgs (drop info) in
example : backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt?

/- The attribute rejects an unsupported theorem conclusion. -/
#guard_msgs (drop error) in
@[ppt_primitive]
theorem rejectedTruthPrimitive : True :=
  trivial

/- `ppt` does not run on unrelated proposition shapes. -/
#guard_msgs (drop error) in
example : True := by
  ppt

/- Exact-head lookup does not synthesize an unregistered realizer. -/
#guard_msgs (drop error) in
example : backend.PolyRealizer boolRepresentation boolRepresentation Bool.not := by
  ppt

/- `ppt using` rejects a supplied primitive for a different exact target. -/
#guard_msgs (drop error) in
example : backend.PolyRealizer unitRepresentation unitRepresentation id := by
  ppt using boolIdentityPrimitive

section OraclePPT

universe u v w x

open PFunctor.DynSystem.DynComputation

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {label : Type x}
  {contract : OracleContract Q bd.interface label} {program : input → FreeM p output}

/- An `IsOraclePPTBy` definition is not accepted in place of a theorem declaration. -/
#guard_msgs (drop error) in
@[ppt_primitive]
def rejectedOraclePPTDefinition (hypothesis : IsOraclePPTBy Q bd contract program) :
    IsOraclePPTBy Q bd contract program :=
  hypothesis

@[ppt_primitive]
theorem oraclePPTPrimitive (hypothesis : IsOraclePPTBy Q bd contract program) :
    IsOraclePPTBy Q bd contract program :=
  hypothesis

example (hypothesis : IsOraclePPTBy Q bd contract program) :
    IsOraclePPTBy Q bd contract program := by
  ppt

example (hypothesis : IsOraclePPTBy Q bd contract program) :
    IsOraclePPTBy Q bd contract program := by
  ppt using oraclePPTPrimitive hypothesis

end OraclePPT

end OracleComp.Complexity.ComplexityTacticsTest

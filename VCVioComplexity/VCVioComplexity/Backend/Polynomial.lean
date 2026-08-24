/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Polynomial
public import VCVioComplexity.Backend.TuringMachine

/-!
# PolyFun polynomial certificates for complexitylib machines

This file connects the optional complexitylib machine substrate to PolyFun's generic
`PolyRealizer` interface. A `PolynomialCode` already proves that the exact transition count of
one concrete Turing machine is bounded by a Mathlib polynomial. `toPolyRealizer` translates that
bound into PolyFun's inspectable first-order syntax.

Output growth remains a separate argument. Polynomial running time does not, at this stage of the
adapter, imply that the encoding on complexitylib's output tape has been charged by the machine
trace. Requiring the size certificate explicitly prevents the adapter from silently manufacturing
that missing adequacy fact.
-/

@[expose] public section

namespace VCVioComplexity.Backend.TuringMachine

open PFunctor
open Complexity

namespace PolynomialCode

variable {A B : Type} {input : Representation A} {output : Representation B}
  {function : A → B}

/-- A deterministic first-order syntax tree corresponding to the concrete Mathlib polynomial
stored by a `PolynomialCode` certificate. -/
noncomputable def workPolynomial (code : PolynomialCode input output function) :
    FirstOrderPolynomial :=
  FirstOrderPolynomial.ofNatPolynomial code.certificate.polynomial

/-- The exact transition count on a represented value is bounded by `workPolynomial`. -/
theorem valueCost_le_workPolynomial (code : PolynomialCode input output function) (value : A) :
    code.valueCost value ≤ code.workPolynomial.eval (encodedSize input value) := by
  refine (code.valueCost_le_bound value).trans ?_
  rw [workPolynomial, FirstOrderPolynomial.eval_ofNatPolynomial]
  exact code.certificate.bound_le_polynomial (encodedSize input value)

/-- Turn one exact polynomial complexitylib machine into a PolyFun polynomial realizer.

The caller must additionally bound encoded output length. This is intentionally independent of
the machine's time certificate until the future tape-level adequacy theorem proves that writing an
output of length `m` consumes at least `m` charged transitions. -/
noncomputable def toPolyRealizer (code : PolynomialCode input output function)
    (outputSize : FirstOrderPolynomial)
    (outputSize_le : ∀ value, encodedSize output (function value) ≤
      outputSize.eval (encodedSize input value)) :
    polynomialQuantitativeStepClass.PolyRealizer input output function where
  code := code
  work := code.workPolynomial
  outputSize := outputSize
  work_le := code.valueCost_le_workPolynomial
  outputSize_le := outputSize_le

end PolynomialCode

namespace Primitive

/-- The exact zero-step unit identity as a complete PolyFun polynomial realizer. -/
noncomputable def unitIdentityPolyRealizer :
    polynomialQuantitativeStepClass.PolyRealizer .unit .unit id :=
  unitIdentityPolynomial.toPolyRealizer (FirstOrderPolynomial.const 0) fun value ↦ by
    cases value
    rfl

@[simp]
theorem unitIdentityPolyRealizer_cost (value : PUnit) :
    polynomialQuantitativeStepClass.cost unitIdentityPolyRealizer.code value = 0 :=
  rfl

/-- The canary exposes the generic work certificate as well as the exact zero-step equation. -/
theorem unitIdentityPolyRealizer_work_le (value : PUnit) :
    polynomialQuantitativeStepClass.cost unitIdentityPolyRealizer.code value ≤
      unitIdentityPolyRealizer.work.eval
        (polynomialQuantitativeStepClass.size Representation.unit value) :=
  unitIdentityPolyRealizer.work_le value

end Primitive

end VCVioComplexity.Backend.TuringMachine

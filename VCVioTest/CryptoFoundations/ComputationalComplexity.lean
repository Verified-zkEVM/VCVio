/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity

/-!
# Computational-complexity API checks

Compile-time checks that the public predicates retain the backend, representations, oracle-length
discipline, and single packed security-family program in their types.
-/

public section

universe u v w x

open PFunctor
open PFunctor.DynSystem.DynComputation

#check OracleComp.Complexity.ResourcePolynomial
#check OracleComp.Complexity.ResourcePolynomial.comp
#check OracleComp.Complexity.ResourcePolynomial.reindex
#check OracleComp.Complexity.ResourcePolynomial.subst
#check OracleComp.Complexity.ResourcePolynomial.eval_comp
#check OracleComp.Complexity.ResourcePolynomial.eval_reindex
#check OracleComp.Complexity.ResourcePolynomial.eval_subst
#check OracleComp.Complexity.OracleModulus
#check OracleComp.Complexity.OracleResourceModel
#check OracleComp.Complexity.OracleContract
#check OracleComp.Complexity.OracleContract.Model.modulus_monotone
#check OracleComp.Complexity.StrictPPTWitness
#check OracleComp.Complexity.StrictPPTWitness.isTotalRollBound
#check OracleComp.Complexity.StrictPPTWitness.congrProgram
#check OracleComp.Complexity.PureCertificate
#check OracleComp.Complexity.PureCertificate.ofPolyRealizer
#check OracleComp.Complexity.PureCertificate.strictPPTWitness
#check OracleComp.Complexity.PureCertificate.isOraclePPTBy
#check OracleComp.Complexity.IsOraclePPTBy
#check OracleComp.Complexity.IsOraclePPTBy.congrProgram
#check OracleComp.Complexity.IsPPTBy
#check OracleComp.Complexity.OracleProgram.IsOraclePPTBy
#check OracleComp.Complexity.SecurityFamily.IsOraclePPTBy
#check OracleComp.Complexity.SecurityFamily.IsCoinPPTByUnder
#check OracleComp.Complexity.fairCoinResourceModel
#check OracleComp.Complexity.fairCoinContract
#check OracleComp.Complexity.fairCoinModel
#check OracleComp.Complexity.fairCoinModel_eq

namespace OracleComp.Complexity

example {label : Type x} (symbol : OracleModulus label) :
    ∃ interface, symbol = .responseSize interface := by
  cases symbol with
  | responseSize interface => exact ⟨interface, rfl⟩

section OracleAnswerAccounting

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  {Q : QuantitativeStepClass.{u, v, w} C} {input output : Type u}
  {bd : Boundary C p input output} {label : Type x}
  {contract : OracleContract Q bd.interface label} (model : contract.Model)

example (position : p.A) (answer : p.B position)
    (hanswer : model.resourceModel.allows position answer) :
    Q.size bd.idx ⟨position, answer⟩ ≤
      model.resourceModel.responseSize (contract.labelOf position) (Q.size bd.pos position) :=
  model.resourceModel.responseSize_le position answer hanswer

end OracleAnswerAccounting

section CertifiedPure

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C}
  {input output : Type u} {bd : Boundary C p input output}
  {function : input → output} {label : Type x}

example (certificate : PureCertificate Q bd function)
    (contract : OracleContract Q bd.interface label) :
    IsOraclePPTBy Q bd contract fun input ↦ FreeM.pure (function input) :=
  certificate.isOraclePPTBy contract

example (model : Q.PolynomialModel)
    (result : Q.PolyRealizer bd.input bd.out function) :
    letI := model.kernel.cProd
    letI := model.kernel.cSum
    letI := model.kernel.cOption
    PureCertificate Q bd function :=
  PureCertificate.ofPolyRealizer model result

end CertifiedPure

section ProgramCongruence

variable {p : PFunctor.{u, u}} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption] [DecidableEq p.A]
  {Q : QuantitativeStepClass.{u, v, w} C}
  {input output : Type u} {bd : Boundary C p input output} {label : Type x}
  {contract : OracleContract Q bd.interface label}
  {program program' : input → FreeM p output}

example (witness : StrictPPTWitness Q bd contract program)
    (program_eq : program = program') : StrictPPTWitness Q bd contract program' :=
  witness.congrProgram program_eq

example (hPPT : IsOraclePPTBy Q bd contract program)
    (program_eq : program = program') : IsOraclePPTBy Q bd contract program' :=
  hPPT.congrProgram program_eq

end ProgramCongruence

section FairCoinContract

variable {input output : Type} {C : StepClass}
  [C.HasProd] [C.HasSum] [C.HasOption]
  (Q : QuantitativeStepClass C)
  (bd : Boundary C coinSpec.toPFunctor input output)

example (program : input → OracleComp coinSpec output) :
    IsPPTBy Q bd program ↔
      OracleProgram.IsOraclePPTBy Q bd (fairCoinContract Q bd.interface) program :=
  Iff.rfl

example (model : (fairCoinContract Q bd.interface).Model) :
    model.resourceModel = fairCoinResourceModel Q bd.interface := by
  rw [fairCoinModel_eq Q bd.interface model]
  rfl

end FairCoinContract

end OracleComp.Complexity

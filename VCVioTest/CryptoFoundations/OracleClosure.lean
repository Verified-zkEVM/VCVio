/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.OracleClosure

/-!
# Oracle-handler complexity API checks

Compile-time checks for the proof-bearing handler boundary and its whole-tree result-conformance
predicate.
-/

public section

open PFunctor
open PFunctor.DynSystem.DynComputation
open OracleComp.Complexity

#check FreeM.LeavesSatisfyUnder
#check FreeM.leavesSatisfyUnder_bind_iff
#check handlerBoundary
#check packHandler
#check closeHandler
#check leavesSatisfyUnder_closeHandler
#check BindCertificate
#check BindCertificate.handoffBound
#check BindCertificate.polynomial
#check BindCertificate.runsWithin
#check BindCertificate.strictPPTWitness
#check BindCertificate.isOraclePPTBy
#check IsOraclePPTBy.bind
#check HandlerCertificate
#check HandlerCertificate.nonempty_of_isOraclePPTBy
#check HandlerCertificate.packedReturnsAllowed
#check HandlerCertificate.closeLeavesSatisfyUnder
#check HandlerCertificate.isOraclePPTBy

universe u v w x y

namespace OracleComp.Complexity

variable {p q : PFunctor.{u, u}} {α : Type u}

example (handler : ∀ position : p.A, FreeM q (p.B position))
    (position : p.A) :
    packHandler handler position =
      (fun answer ↦ ⟨position, answer⟩) <$> handler position :=
  rfl

example (handler : ∀ position : p.A, FreeM q (p.B position))
    (result : α) :
    closeHandler handler (pure result : FreeM p α) = pure result :=
  rfl

section BindClosure

variable {C : StepClass.{u, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{u, v, w} C}
  {r : PFunctor.{u, u}} [DecidableEq r.A]
  [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd] [Q.IsDistributive]
  {input middle output : Type u} {bd : Boundary C r input middle}
  {outRep : C.Str output} {label : Type x}
  {contract : OracleContract Q bd.interface label}
  {program : input → FreeM r middle} {next : middle → FreeM r output}

/-- The final bound follows from component witnesses and the exact structural-overhead
certificate. -/
example (first : StrictPPTWitness Q bd contract program)
    (second : StrictPPTWitness Q (bd.mid outRep) contract next)
    (certificate : BindCertificate first second) (model : contract.Model) :
    (first.realization.seqComp second.realization).RunsWithinUnder
      model.resourceModel.allows fun value ↦
        certificate.polynomial.eval model.modulus (Q.size bd.input value) :=
  certificate.runsWithin model

/-- Propositional strict-PPT witnesses compose only after a certificate for the exact assembled
machine cost is supplied. -/
example
    (first : IsOraclePPTBy Q bd contract program)
    (second : IsOraclePPTBy Q (bd.mid outRep) contract next)
    (resourceClosure : ∀ (firstWitness : StrictPPTWitness Q bd contract program)
      (secondWitness : StrictPPTWitness Q (bd.mid outRep) contract next),
      Nonempty (BindCertificate firstWitness secondWitness)) :
    IsOraclePPTBy Q (bd.withOut outRep) contract fun value ↦
      FreeM.bind (program value) next :=
  first.bind second resourceClosure

end BindClosure

/-! ## Genuinely dependent response canary -/

/-- Two query positions whose response types are not definitionally equal. -/
inductive DependentQuery where
  | bit
  | trit
  deriving DecidableEq

/-- A small dependent oracle: one position returns a bit and the other returns a ternary digit. -/
abbrev dependentSpec : OracleSpec DependentQuery
  | .bit => Bool
  | .trit => Fin 3

/-- The answer policy also depends on the query position. Every bit is admitted, while ternary
answers are restricted to zero or one. -/
@[expose] def dependentAllows : ∀ position, dependentSpec position → Prop
  | .bit, _ => True
  | .trit, answer => answer.val ≤ 1

/-- A coin-powered implementation whose result type varies with the outer query position. -/
@[expose] def dependentHandler : ∀ position, FreeM coinSpec.toPFunctor (dependentSpec position)
  | .bit => FreeM.liftBind () fun answer ↦ FreeM.pure answer
  | .trit => FreeM.liftBind () fun answer ↦
      FreeM.pure (if answer then (1 : Fin 3) else 0)

/-- An adaptive outer program uses the Boolean reply to decide whether to request a `Fin 3`
reply. -/
@[expose] def dependentProgram : FreeM dependentSpec.toPFunctor ℕ :=
  FreeM.liftBind .bit fun answer ↦
    if answer then
      FreeM.liftBind .trit fun digit ↦ FreeM.pure digit.val
    else
      FreeM.pure 0

/-- Both branches of the dependent handler meet their corresponding answer policy. -/
theorem dependentHandler_returnsAllowed (position : dependentSpec.Domain) :
    (dependentHandler position).LeavesSatisfyUnder (fun _ _ ↦ True)
      (dependentAllows position) := by
  cases position with
  | bit =>
      change ∀ _ : Bool, True → True
      simp
  | trit =>
      change ∀ answer : Bool, True → (if answer then (1 : Fin 3) else 0).val ≤ 1
      intro answer _
      cases answer <;> decide

/-- The adaptive outer program returns only zero or one on every admitted typed-answer path. -/
theorem dependentProgram_returnsSmall :
    dependentProgram.LeavesSatisfyUnder dependentAllows (fun result ↦ result ≤ 1) := by
  unfold dependentProgram
  rw [FreeM.leavesSatisfyUnder_liftBind]
  intro answer _
  cases answer with
  | false => simp
  | true =>
      simp only [if_true, FreeM.leavesSatisfyUnder_liftBind]
      intro digit hdigit
      simpa [dependentAllows] using hdigit

/-- Typed handler substitution composes the variable-response policy without erasing the query
index or appealing to a probabilistic semantics. -/
theorem closeDependentHandler_returnsSmall :
    (closeHandler dependentHandler dependentProgram).LeavesSatisfyUnder
      (fun _ _ ↦ True) (fun result ↦ result ≤ 1) :=
  leavesSatisfyUnder_closeHandler dependentHandler dependentAllows (fun _ _ ↦ True)
    (fun result ↦ result ≤ 1) dependentHandler_returnsAllowed dependentProgram
      dependentProgram_returnsSmall

section ProofBearingCanary

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {outer : InterfaceBoundary C dependentSpec.toPFunctor}
  {inner : InterfaceBoundary C coinSpec.toPFunctor}
  {outerLabel : Type x} {innerLabel : Type y}
  {outerContract : OracleContract Q outer outerLabel}
  {innerContract : OracleContract Q inner innerLabel}

/-- Even for a variable-response handler, a bare semantic conformance theorem does not fabricate
executable evidence: the constructor additionally consumes strict PPT of the one packed
dispatcher. -/
example
    (hppt : IsOraclePPTBy Q (handlerBoundary outer inner) innerContract
      (packHandler dependentHandler))
    (modelMap : innerContract.Model → outerContract.Model)
    (returnsAllowed : ∀ (innerModel : innerContract.Model)
      (position : dependentSpec.Domain),
      (dependentHandler position).LeavesSatisfyUnder innerModel.resourceModel.allows
        ((modelMap innerModel).resourceModel.allows position)) :
    Nonempty (HandlerCertificate outer inner outerContract innerContract dependentHandler) :=
  HandlerCertificate.nonempty_of_isOraclePPTBy hppt modelMap returnsAllowed

end ProofBearingCanary

end OracleComp.Complexity

/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public import PolyFun.Realizability.Quantitative.BoundedClosure

/-!
# Proof-bearing oracle handlers

An open resource contract describes which answers an oracle may return and how large those
answers may be. Closing an interface requires more than substituting a numeric bound: one uniform
handler program must implement all query positions, satisfy its own strict resource bound, and
prove that every result reached along a conforming inner interaction path is admitted by the outer
contract.

This module packages that non-circular proof boundary. `HandlerCertificate` currently proves the
semantic leaf-conformance needed for typed handler substitution. A future trace simulation and
resource-polynomial substitution theorem will consume the same certificate; a bare `QueryImpl` or
claimed cost function cannot justify that quantitative step.
-/

@[expose] public section

universe u v w x y

namespace PFunctor.FreeM

variable {p : PFunctor.{u, u}} {α β : Type u}

/-- Every returned leaf reached using allowed answers satisfies `accept`.

Non-vacuity is intentionally not part of this predicate. It is supplied by
`QuantitativeRealization.RunsWithinUnder`, which requires progress at every conformingly reachable
query. Keeping the two obligations separate makes result conformance reusable independently of a
particular cost witness. -/
def LeavesSatisfyUnder (allows : ∀ position, p.B position → Prop) (accept : α → Prop) :
    FreeM p α → Prop
  | .pure result => accept result
  | .liftBind position next =>
      ∀ direction, allows position direction →
        (next direction).LeavesSatisfyUnder allows accept

@[simp]
theorem leavesSatisfyUnder_pure (allows : ∀ position, p.B position → Prop)
    (accept : α → Prop) (result : α) :
    (pure result : FreeM p α).LeavesSatisfyUnder allows accept ↔ accept result :=
  Iff.rfl

@[simp]
theorem leavesSatisfyUnder_liftBind (allows : ∀ position, p.B position → Prop)
    (accept : α → Prop) (position : p.A) (next : p.B position → FreeM p α) :
    (FreeM.liftBind position next).LeavesSatisfyUnder allows accept ↔
      ∀ direction, allows position direction →
        (next direction).LeavesSatisfyUnder allows accept :=
  Iff.rfl

/-- Weakening the required leaf predicate preserves whole-tree conformance. -/
theorem LeavesSatisfyUnder.mono {allows : ∀ position, p.B position → Prop}
    {accept accept' : α → Prop} (haccept : ∀ result, accept result → accept' result)
    {program : FreeM p α} (h : program.LeavesSatisfyUnder allows accept) :
    program.LeavesSatisfyUnder allows accept' := by
  induction program with
  | pure result => exact haccept result h
  | lift_bind position next ih =>
      exact fun direction hdirection ↦ ih direction (h direction hdirection)

/-- Mapping a function changes only the predicate imposed on returned leaves. -/
theorem leavesSatisfyUnder_map_iff (allows : ∀ position, p.B position → Prop)
    (accept : β → Prop) (function : α → β) (program : FreeM p α) :
    (function <$> program).LeavesSatisfyUnder allows accept ↔
      program.LeavesSatisfyUnder allows (accept ∘ function) := by
  induction program with
  | pure result => rfl
  | lift_bind position next ih =>
      change
        (∀ direction, allows position direction →
          (function <$> next direction).LeavesSatisfyUnder allows accept) ↔
        ∀ direction, allows position direction →
          (next direction).LeavesSatisfyUnder allows (accept ∘ function)
      exact forall_congr' fun direction ↦
        imp_congr_right fun _ ↦ ih direction

/-- Whole-tree result conformance composes through monadic sequencing. -/
theorem leavesSatisfyUnder_bind_iff (allows : ∀ position, p.B position → Prop)
    (accept : β → Prop) (program : FreeM p α) (next : α → FreeM p β) :
    (FreeM.bind program next).LeavesSatisfyUnder allows accept ↔
      program.LeavesSatisfyUnder allows
        (fun result ↦ (next result).LeavesSatisfyUnder allows accept) := by
  induction program with
  | pure result => rfl
  | lift_bind position continuation ih =>
      change
        (∀ direction, allows position direction →
          (FreeM.bind (continuation direction) next).LeavesSatisfyUnder allows accept) ↔
        ∀ direction, allows position direction →
          (continuation direction).LeavesSatisfyUnder allows
            (fun result ↦ (next result).LeavesSatisfyUnder allows accept)
      exact forall_congr' fun direction ↦
        imp_congr_right fun _ ↦ ih direction

end PFunctor.FreeM

namespace OracleComp.Complexity

open PFunctor
open PFunctor.DynSystem.DynComputation

variable {p q : PFunctor.{u, u}} {α : Type u} {C : StepClass.{u, v}}
  [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{u, v, w} C}

/-! ## Sequential strict-PPT closure seam -/

section Bind

variable [DecidableEq p.A] [Q.HasCategory] [Q.HasSum] [Q.HasOption] [Q.HasProd]
  [Q.IsDistributive]
  {input middle output : Type u} {bd : Boundary C p input middle}
  {outRep : C.Str output} {label : Type x}
  {contract : OracleContract Q bd.interface label}
  {program : input → FreeM p middle} {next : middle → FreeM p output}

/-- The backend-specific resource obligation left after composing two strict-PPT realizers.

PolyFun derives phase-local bounds, handoff progress, and resolution generically. This certificate
therefore contains only the exact comparison for the structural code assembled by `seqComp` and a
uniform polynomial bound on that comparison's overhead. It cannot attach an unverified meter to
the bind: `SeqCompCostCertificate.cost_le` refers to the concrete composed realization's actual
`ExecutionCost`. -/
structure BindCertificate
    (first : StrictPPTWitness Q bd contract program)
    (second : StrictPPTWitness Q (bd.mid outRep) contract next) where
  /-- One polynomial allowance for structural wiring and phase-switching overhead. -/
  overheadPolynomial : ResourcePolynomial (OracleModulus label)
  /-- Exact composite-to-phase cost comparison for every compatible answer model. -/
  costCertificate : ∀ model : contract.Model,
    SeqCompCostCertificate first.realization second.realization
      model.resourceModel.allows
  /-- The exact structural overhead is uniformly polynomial in the original input size. -/
  overhead_le : ∀ (model : contract.Model) (value : input),
    (costCertificate model).overhead value ≤
      overheadPolynomial.eval model.modulus (Q.size bd.input value)

namespace BindCertificate

variable {first : StrictPPTWitness Q bd contract program}
  {second : StrictPPTWitness Q (bd.mid outRep) contract next}

/-- Uniform second-phase envelope obtained from the first witness's polynomial output recovery.

Only values actually returned by a conforming first-phase trace are compared. The second
witness's resource polynomial is monotone in encoded input size, so the recovered intermediate
size supplies the required handoff envelope. -/
def handoffBound (first : StrictPPTWitness Q bd contract program)
    (second : StrictPPTWitness Q (bd.mid outRep) contract next)
    (model : contract.Model) :
    SeqCompHandoffBound first.realization model.resourceModel.allows fun value ↦
      second.polynomial.eval model.modulus (Q.size (bd.mid outRep).input value) where
  bound value := second.polynomial.eval model.modulus
    (first.outputSizePolynomial.eval model.modulus (Q.size bd.input value))
  returned_le value _finish trace htrace result view_eq :=
    second.polynomial.eval_mono_input model.modulus_monotone
      (first.returnedSize_le model value trace htrace result view_eq)

/-- Canonical resource polynomial for a certified bind.

The second phase is composed with the first phase's returned-size polynomial; the remaining
backend structural overhead is added conservatively. -/
def polynomial (certificate : BindCertificate first second) :
    ResourcePolynomial (OracleModulus label) :=
  (first.polynomial + second.polynomial.comp first.outputSizePolynomial) +
    certificate.overheadPolynomial

/-- PolyFun's bounded sequential-composition theorem derives the complete exact bound. -/
theorem runsWithin (certificate : BindCertificate first second)
    (model : contract.Model) :
    (first.realization.seqComp second.realization).RunsWithinUnder
      model.resourceModel.allows fun value ↦
        certificate.polynomial.eval model.modulus (Q.size bd.input value) := by
  let secondComposed := second.polynomial.comp first.outputSizePolynomial
  have hphases := ResourcePolynomial.add_eval_le_eval_add first.polynomial
    secondComposed model.modulus
  have htotal := ResourcePolynomial.add_eval_le_eval_add
    (first.polynomial + secondComposed) certificate.overheadPolynomial model.modulus
  apply ((first.runsWithin model).seqComp (second.runsWithin model)
    (handoffBound first second model) (certificate.costCertificate model)).mono
  intro value
  have hoverhead := certificate.overhead_le model value
  have hcomponents := ExecutionCost.add_le_add
    (hphases (Q.size bd.input value)) hoverhead
  simpa only [handoffBound, polynomial, secondComposed,
    ResourcePolynomial.eval_comp] using
      hcomponents.trans (htotal (Q.size bd.input value))

/-- Assemble the complete strict-PPT witness for monadic sequencing. -/
def strictPPTWitness (certificate : BindCertificate first second) :
    StrictPPTWitness Q (bd.withOut outRep) contract fun value ↦
      FreeM.bind (program value) next where
  realization := first.realization.seqComp second.realization
  implements := by
    change (first.realization.machine.seqComp second.realization.machine).Implements _
    exact first.implements.seqComp second.implements
  outputRecovery :=
    { polynomial := second.outputRecovery.polynomial
      output_le := second.outputRecovery.output_le }
  polynomial := certificate.polynomial
  runsWithin := certificate.runsWithin

/-- A certified exact-resource bind establishes backend-relative strict oracle PPT. -/
theorem isOraclePPTBy (certificate : BindCertificate first second) :
    IsOraclePPTBy Q (bd.withOut outRep) contract fun value ↦
      FreeM.bind (program value) next :=
  ⟨certificate.strictPPTWitness⟩

end BindCertificate

/-- Strict PPT composes through bind once exact resource closure has been proved for the two
hidden executable witnesses.

The closure argument returns `Nonempty` because the component predicates are propositions. This
keeps executable evidence from being extracted from proof irrelevance while still supporting
compositional PPT proofs. -/
theorem IsOraclePPTBy.bind
    (first : IsOraclePPTBy Q bd contract program)
    (second : IsOraclePPTBy Q (bd.mid outRep) contract next)
    (resourceClosure : ∀ (firstWitness : StrictPPTWitness Q bd contract program)
      (secondWitness : StrictPPTWitness Q (bd.mid outRep) contract next),
      Nonempty (BindCertificate firstWitness secondWitness)) :
    IsOraclePPTBy Q (bd.withOut outRep) contract fun value ↦
      FreeM.bind (program value) next := by
  obtain ⟨firstWitness⟩ := first
  obtain ⟨secondWitness⟩ := second
  obtain ⟨certificate⟩ := resourceClosure firstWitness secondWitness
  exact certificate.isOraclePPTBy

end Bind

/-- Boundary used to certify one packed handler dispatcher.

The input and result representations are the outer interface's position and tagged-answer
representations. Its visible interactions use the inner interface. -/
def handlerBoundary (outer : InterfaceBoundary C p) (inner : InterfaceBoundary C q) :
    Boundary C q p.A p.Idx where
  input := outer.pos
  out := outer.idx
  pos := inner.pos
  idx := inner.idx

/-- Pack a dependent handler into one ordinary program family.

The returned sigma tag is fixed by construction, so one realization implements every outer query
position without a pointwise choice of code. -/
def packHandler (handler : ∀ position : p.A, FreeM q (p.B position)) :
    p.A → FreeM q p.Idx :=
  fun position ↦ (fun answer ↦ ⟨position, answer⟩) <$> handler position

/-- Interpret every outer query by a dependent handler, leaving the handler's inner queries open. -/
def closeHandler (handler : ∀ position : p.A, FreeM q (p.B position))
    (program : FreeM p α) : FreeM q α :=
  program.liftM handler

@[simp]
theorem closeHandler_pure (handler : ∀ position : p.A, FreeM q (p.B position))
    (result : α) : closeHandler handler (pure result : FreeM p α) = pure result :=
  rfl

@[simp]
theorem closeHandler_liftBind (handler : ∀ position : p.A, FreeM q (p.B position))
    (position : p.A) (next : p.B position → FreeM p α) :
    closeHandler handler (FreeM.liftBind position next) =
      handler position >>= fun direction ↦ closeHandler handler (next direction) :=
  rfl

/-- Closing an outer program through conforming handlers preserves its leaf contract.

The proof ranges over every answer admitted by the two contracts. It therefore composes the
semantic obligations needed by oracle substitution without appealing to probabilities or to a
particular machine backend. -/
theorem leavesSatisfyUnder_closeHandler
    (handler : ∀ position : p.A, FreeM q (p.B position))
    (outerAllows : ∀ position, p.B position → Prop)
    (innerAllows : ∀ position, q.B position → Prop)
    (accept : α → Prop)
    (hhandler : ∀ position,
      (handler position).LeavesSatisfyUnder innerAllows (outerAllows position))
    (program : FreeM p α)
    (hprogram : program.LeavesSatisfyUnder outerAllows accept) :
    (closeHandler handler program).LeavesSatisfyUnder innerAllows accept := by
  induction program with
  | pure result => exact hprogram
  | lift_bind position next ih =>
      change
        (handler position >>= fun direction ↦
          closeHandler handler (next direction)).LeavesSatisfyUnder innerAllows accept
      change
        (FreeM.bind (handler position)
          (fun direction ↦ closeHandler handler (next direction))).LeavesSatisfyUnder
          innerAllows accept
      rw [PFunctor.FreeM.leavesSatisfyUnder_bind_iff]
      exact (hhandler position).mono fun direction hdirection ↦
        ih direction (hprogram direction hdirection)

/-- Result conformance of a dependent handler is equivalent to conformance of its packed form. -/
theorem leavesSatisfyUnder_packHandler_iff
    (handler : ∀ position : p.A, FreeM q (p.B position))
    (allows : ∀ position, q.B position → Prop) (accept : p.Idx → Prop)
    (position : p.A) :
    (packHandler handler position).LeavesSatisfyUnder allows accept ↔
      (handler position).LeavesSatisfyUnder allows
        (fun answer ↦ accept ⟨position, answer⟩) := by
  change
    ((fun answer ↦ ⟨position, answer⟩) <$> handler position).LeavesSatisfyUnder allows accept ↔
      (handler position).LeavesSatisfyUnder allows
        (accept ∘ fun answer ↦ ⟨position, answer⟩)
  exact PFunctor.FreeM.leavesSatisfyUnder_map_iff allows accept
    (fun answer ↦ ⟨position, answer⟩) (handler position)

variable [DecidableEq q.A]

/-- One uniform, strict-PPT implementation of an outer interface using an inner interface.

`witness` supplies executable code and pathwise resource bounds for the single packed dispatcher.
`modelMap` identifies the outer resource environment implemented under each inner environment.
`returnsAllowed` then proves semantic compatibility: every handler result along an
inner-contract-conforming path is admitted by that selected outer model. This avoids requiring
unrelated outer and inner models to be compatible while keeping the relationship explicit. -/
structure HandlerCertificate
    (outer : InterfaceBoundary C p) (inner : InterfaceBoundary C q)
    {outerLabel : Type x} {innerLabel : Type y}
    (outerContract : OracleContract Q outer outerLabel)
    (innerContract : OracleContract Q inner innerLabel)
    (handler : ∀ position : p.A, FreeM q (p.B position)) where
  /-- One code and polynomial bound for the entire dependent dispatcher. -/
  witness : StrictPPTWitness Q (handlerBoundary outer inner) innerContract
    (packHandler handler)
  /-- Outer resource environment implemented under each inner environment. -/
  modelMap : innerContract.Model → outerContract.Model
  /-- Every result of the handler satisfies the selected outer environment. -/
  returnsAllowed : ∀ (innerModel : innerContract.Model) (position : p.A),
    (handler position).LeavesSatisfyUnder innerModel.resourceModel.allows
      ((modelMap innerModel).resourceModel.allows position)

namespace HandlerCertificate

variable {outer : InterfaceBoundary C p} {inner : InterfaceBoundary C q}
  {outerLabel : Type x} {innerLabel : Type y}
  {outerContract : OracleContract Q outer outerLabel}
  {innerContract : OracleContract Q inner innerLabel}
  {handler : ∀ position : p.A, FreeM q (p.B position)}

/-- Build propositional existence of a handler certificate from strict PPT of the packed
dispatcher and semantic compatibility of its returned leaves.

The result is `Nonempty` because `IsOraclePPTBy` deliberately hides its executable witness behind
a proposition. This theorem does not eliminate that proposition into computational data. -/
theorem nonempty_of_isOraclePPTBy
    (hppt : IsOraclePPTBy Q (handlerBoundary outer inner) innerContract
      (packHandler handler))
    (modelMap : innerContract.Model → outerContract.Model)
    (returnsAllowed : ∀ (innerModel : innerContract.Model) (position : p.A),
      (handler position).LeavesSatisfyUnder innerModel.resourceModel.allows
        ((modelMap innerModel).resourceModel.allows position)) :
    Nonempty (HandlerCertificate outer inner outerContract innerContract handler) := by
  obtain ⟨witness⟩ := hppt
  exact ⟨⟨witness, modelMap, returnsAllowed⟩⟩

/-- The packed dispatcher returns only correctly tagged answers admitted by the outer model. -/
theorem packedReturnsAllowed
    (certificate : HandlerCertificate outer inner outerContract innerContract handler)
    (innerModel : innerContract.Model) (position : p.A) :
    (packHandler handler position).LeavesSatisfyUnder innerModel.resourceModel.allows
      (fun answer ↦ answer.1 = position ∧
        (certificate.modelMap innerModel).resourceModel.allows answer.1 answer.2) := by
  rw [leavesSatisfyUnder_packHandler_iff]
  exact (certificate.returnsAllowed innerModel position).mono fun answer hanswer ↦
    ⟨rfl, hanswer⟩

/-- A certified handler transports any outer-model leaf invariant to the closed program under the
chosen inner model. This is the semantic half of oracle substitution; the quantitative machine
and bound substitution remain separate obligations. -/
theorem closeLeavesSatisfyUnder
    (certificate : HandlerCertificate outer inner outerContract innerContract handler)
    (innerModel : innerContract.Model) (accept : α → Prop) (program : FreeM p α)
    (hprogram : program.LeavesSatisfyUnder
      (certificate.modelMap innerModel).resourceModel.allows accept) :
    (closeHandler handler program).LeavesSatisfyUnder
      innerModel.resourceModel.allows accept :=
  leavesSatisfyUnder_closeHandler handler
    (certificate.modelMap innerModel).resourceModel.allows
    innerModel.resourceModel.allows accept
    (certificate.returnsAllowed innerModel) program hprogram

/-- Forget handler conformance while retaining strict PPT of its packed dispatcher. -/
theorem isOraclePPTBy
    (certificate : HandlerCertificate outer inner outerContract innerContract handler) :
    IsOraclePPTBy Q (handlerBoundary outer inner) innerContract (packHandler handler) :=
  ⟨certificate.witness⟩

end HandlerCertificate

end OracleComp.Complexity

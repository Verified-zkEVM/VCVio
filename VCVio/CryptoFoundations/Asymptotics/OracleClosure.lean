/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity

/-!
# Proof-bearing oracle handlers

An open resource contract describes which answers an oracle may return and how large those
answers may be. Closing an interface requires more than substituting a numeric bound: one uniform
handler program must implement all query positions, satisfy its own strict resource bound, and
prove that every result reached along a conforming inner interaction path is admitted by the outer
contract.

This module packages that non-circular proof boundary. The generic trace simulation and polynomial
substitution theorem can consume `HandlerCertificate`; a bare `QueryImpl` or claimed cost function
cannot be used in its place.
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
`returnsAllowed` is semantic compatibility between the two contracts: every handler result along
every inner-contract-conforming path is an answer allowed by the chosen outer model. Both model
quantifiers are explicit, so no numeric contract is mistaken for executable handler evidence. -/
structure HandlerCertificate
    (outer : InterfaceBoundary C p) (inner : InterfaceBoundary C q)
    {outerLabel : Type x} {innerLabel : Type y}
    (outerContract : OracleContract Q outer outerLabel)
    (innerContract : OracleContract Q inner innerLabel)
    (handler : ∀ position : p.A, FreeM q (p.B position)) where
  /-- One code and polynomial bound for the entire dependent dispatcher. -/
  witness : StrictPPTWitness Q (handlerBoundary outer inner) innerContract
    (packHandler handler)
  /-- Every result of the handler satisfies the outer contract. -/
  returnsAllowed : ∀ (outerModel : outerContract.Model)
    (innerModel : innerContract.Model) (position : p.A),
    (handler position).LeavesSatisfyUnder innerModel.resourceModel.allows
      (outerModel.resourceModel.allows position)

namespace HandlerCertificate

variable {outer : InterfaceBoundary C p} {inner : InterfaceBoundary C q}
  {outerLabel : Type x} {innerLabel : Type y}
  {outerContract : OracleContract Q outer outerLabel}
  {innerContract : OracleContract Q inner innerLabel}
  {handler : ∀ position : p.A, FreeM q (p.B position)}

/-- The packed dispatcher returns only correctly tagged answers admitted by the outer model. -/
theorem packedReturnsAllowed
    (certificate : HandlerCertificate outer inner outerContract innerContract handler)
    (outerModel : outerContract.Model) (innerModel : innerContract.Model)
    (position : p.A) :
    (packHandler handler position).LeavesSatisfyUnder innerModel.resourceModel.allows
      (fun answer ↦ answer.1 = position ∧
        outerModel.resourceModel.allows answer.1 answer.2) := by
  rw [leavesSatisfyUnder_packHandler_iff]
  exact (certificate.returnsAllowed outerModel innerModel position).mono fun answer hanswer ↦
    ⟨rfl, hanswer⟩

/-- Forget handler conformance while retaining strict PPT of its packed dispatcher. -/
theorem isOraclePPTBy
    (certificate : HandlerCertificate outer inner outerContract innerContract handler) :
    IsOraclePPTBy Q (handlerBoundary outer inner) innerContract (packHandler handler) :=
  ⟨certificate.witness⟩

end HandlerCertificate

end OracleComp.Complexity

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyExamples

/-!
# Recursion across numeric instantiations

This finite description calls its recursive declaration at a different numeric
argument. Its outer abstraction is available, but every body instance diverges.
The proof uses the whole scheme's least fixed point before instantiation.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Polymorphic.Examples

/-- One numeric quantifier returning a bit. -/
@[expose, reducible] def numericBit : Scheme 0 0 := .allNum (.mono .bit)

/-- A finite recursive body making its call at the next numeric argument. -/
@[expose] def shiftedCycle : Term Scope.empty [] numericBit :=
  .fix (.numAbs (.numApp (.var .zero) (.add (.var 0) (.finite 1))))

/-- The continuous functional described by the shifted recursive body. -/
@[expose] noncomputable def shiftedStep :
    numericBit.Meaning emptyAssignment.val →𝒄 numericBit.Meaning emptyAssignment.val :=
  .ofFun (fun rec => DomainResult.valueContinuous (fun l : Length =>
    DomainResult.elim DomainResult.error
      (ContinuousHom.ofFun (fun f => f (l.add (.finite 1)))) rec))

/-- The finite syntax denotes the simultaneous, pre-instantiation fixed point. -/
theorem denote_shiftedCycle : shiftedCycle.denote emptyAssignment (Env.empty _) =
    shiftedStep.fix := rfl

/-- Recursive instantiation exposes the outer abstraction without manufacturing any bit. -/
theorem shiftedCycle_partial : shiftedCycle.denote emptyAssignment (Env.empty _) =
    DomainResult.value (fun _ : Length => (⊥ : Computation .bit)) := by
  rw [denote_shiftedCycle]
  apply le_antisymm
  · exact shiftedStep.fix_le le_rfl
  · exact shiftedStep.approximants_le_fix 1

/-- Two finite declarations; the first calls the second at a changed instantiation. -/
@[expose] def mutualGroup : Term Scope.empty [] numericBit :=
  Term.letRec (w := Scope.empty) (Γ := []) [numericBit, numericBit]
    (Fin.cases
      (.numAbs (.numApp (.var (.succ .zero)) (.add (.var 0) (.finite 1))))
      (Fin.cases (.numAbs (.bit true)) (fun p => nomatch p)))
    (Term.var .zero)

/-- A returned abstraction with a defined result at every numeric argument. -/
@[expose] noncomputable def trueFamily : numericBit.Meaning emptyAssignment.val :=
  DomainResult.value (fun _ : Length => (DomainResult.value ⟨true⟩ : Computation .bit))

/-- Simultaneous meaning of the two declaration bodies. -/
@[expose] noncomputable def mutualStep :
    Env emptyAssignment [numericBit, numericBit] →𝒄
      Env emptyAssignment [numericBit, numericBit] :=
  .ofFun (fun η => Env.cons emptyAssignment
    (Env.cons emptyAssignment (Env.empty _, trueFamily),
      shiftedStep (η numericBit (.succ .zero))))

/-- A proposed solution of the whole declaration group. -/
@[expose] noncomputable def mutualSolution : Env emptyAssignment [numericBit, numericBit] :=
  Env.cons emptyAssignment (Env.cons emptyAssignment (Env.empty _, trueFamily), trueFamily)

/-- The shared group fixed point reaches its least solution after two approximations. -/
theorem mutualStep_fix : mutualStep.fix = mutualSolution := by
  apply le_antisymm
  · exact mutualStep.fix_le le_rfl
  · exact mutualStep.approximants_le_fix 2

/-- Declaration order and cross-instantiation references are interpreted by the group fold. -/
theorem denote_mutualGroup : mutualGroup.denote emptyAssignment (Env.empty _) = trueFamily := by
  calc
    mutualGroup.denote emptyAssignment (Env.empty _) = mutualStep.fix numericBit .zero := by
      apply congrArg (fun f : Env emptyAssignment [numericBit, numericBit] →𝒄
        Env emptyAssignment [numericBit, numericBit] => f.fix numericBit .zero)
      ext ξ s x
      cases x with
      | zero => rfl
      | succ x =>
          cases x with
          | zero => rfl
          | succ x => exact nomatch x
    _ = trueFamily := by rw [mutualStep_fix]; rfl

end Interop.Cryptol.Polymorphic.Examples

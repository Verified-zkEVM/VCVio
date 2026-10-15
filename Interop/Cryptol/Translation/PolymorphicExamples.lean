/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyExamples
public import Interop.Cryptol.Model.NativeLaws
public import Interop.Cryptol.Translation.CertifiedFamily

/-!
# A certificate for every finite XOR width

The source is a single finite polymorphic description. The certificate proves
its fully instantiated meaning for every natural width and both input words,
including the zero-width case. Arbitrary Lean specifications then transfer.
-/

public section

namespace Interop.Cryptol.Finite.PolymorphicExamples

/-- The all-width interface of the finite polymorphic XOR source. -/
@[expose] def xorInterface :
    FamilyInterface (w := .empty) Polymorphic.Examples.xorScheme Nat where
  assignment _ := Polymorphic.emptyAssignment
  input n := .prod (.word n) (.word n)
  output n := .word n
  inputData n := .prod (.word n) (.word n)
  outputData n := .word n
  specialization := Polymorphic.Examples.xorInstance

/-- A finite native implementation at a selected width. -/
@[expose] def xorImplementation (n : Nat) :
    Term [] (.arrow (.prod (.word n) (.word n)) (.word n)) :=
  .lam (.wordOp .xor (.fst (.var .zero)) (.snd (.var .zero)))

/-- One source and an all-input, all-width representation proof. -/
@[expose] noncomputable def xorCertificate : CertifiedFamily xorInterface where
  source := Polymorphic.Examples.xor
  implementation := xorImplementation
  correct n x := by
    change BitVec n × BitVec n at x
    change DomainResult.applyContinuous (DomainResult.applyContinuous
      (Polymorphic.wordLogic (.var 0) .xor
        (Polymorphic.Scope.entails_here Polymorphic.Scope.empty.bindNum (.fin (.var 0)))
        ((Polymorphic.emptyAssignment.extendNum (.finite n)).assume
          (c := .fin (.var 0)) ⟨n, rfl⟩))
      (DomainResult.value (wordValue x.1))) (DomainResult.value (wordValue x.2)) =
        DomainResult.value (wordValue (x.1 ^^^ x.2))
    rw [Polymorphic.wordLogic_finite _ _ _ _ n rfl]
    exact Semantics.wordLogic_values .xor x.1 x.2

/-- Arbitrary word specifications transfer for every width; no Boolean reification is needed. -/
theorem xor_contract (n : Nat) (pre : (BitVec n × BitVec n) → Prop)
    (post : (BitVec n × BitVec n) → BitVec n → Prop) :
    DataMeaningContract (b := .word n) (.prod (.word n) (.word n))
      (xorCertificate.meaningAt n).meaning pre post ↔
        ∀ x, pre x → post x (x.1 ^^^ x.2) :=
  xorCertificate.contract_iff n (fun x : BitVec n × BitVec n => x.1 ^^^ x.2)
    (fun _ => rfl) pre post

end Interop.Cryptol.Finite.PolymorphicExamples

/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Bridge.ImportedScalar
import Interop.Cryptol.Bridge.ImportedSpecialization
import Interop.Cryptol.Bridge.KeccakCodec
import Interop.Cryptol.Bridge.ListView
import Interop.Cryptol.Bridge.Imperative
import VCVio.Algorithms.CRC

/-! # Foundation certificates through ordinary imports in an independent package -/

open Cryptol Cryptol.Bridge

example : ImperativeSource.bundle.elaborate ImperativeSource.source.provenance.name 32 =
    .ok Imperative.imported := Imperative.import_accepted

example (initial : Computation .integer) :
    Imperative.whileLoop (.value (.const (.value ⟨false⟩))) ⊥ initial = initial :=
  Imperative.whileLoop_false _ _

example : Imperative.whileLoop (a := .bit)
    (.value OmegaCompletePartialOrder.ContinuousHom.id)
    (.value (.const (.value ⟨false⟩))) (.value ⟨true⟩) = .value ⟨false⟩ := by
  rw [Imperative.whileLoop_eq_step_of_true _ _ _ rfl]
  exact Imperative.whileLoop_eq_of_false _ _ _ rfl

example : Translation.SourceElaboration.check ImportedScalarSource.bundle
    ImportedScalarSource.root 1000 = .ok ImportedScalar.certificate.result :=
  ImportedScalar.accepted

example (x : UInt32) :
    DomainResult.applyContinuous
      (Resolved.denote Foundation.wordSource1In Environment.empty)
      (.value (wordValue x.toBitVec)) =
        .value (wordValue (VCVio.Algorithms.Sha2.ssig0 x).toBitVec) :=
  ImportedScalar.core_correct x

example (x : UInt32) :
    DomainResult.applyContinuous
      (Resolved.denote ImportedSpecialization.source Environment.empty)
      (.value (wordValue x.toBitVec)) =
        .value (wordValue (VCVio.Algorithms.Sha2.ssig0 x).toBitVec) :=
  ImportedSpecialization.core_correct x

example (pre : BitVec 32 → Prop) (post : BitVec 32 → BitVec 32 → Prop) :
    DataContract (.word 32) (.word 32)
      (Resolved.denote Foundation.wordSource1In Environment.empty) pre post ↔
        ∀ x, pre x → post x (VCVio.Algorithms.Sha2.ssig0 (UInt32.ofBitVec x)).toBitVec :=
  ImportedScalar.core_contract_iff pre post

example (x : Fin 5) : Int.tmod ((x.val : Int) + 4) 5 = ((x.val : Int) - 1) % 5 :=
  KeccakCodec.theta_predecessor x

example {A : Type} {a : ClosedTy} (relation : A → Computation a → Prop)
    (element : A → Computation a) (faithful : ∀ x, relation x (element x))
    (xs : List A) (tail : Nat → Computation a) :
    ListView.Represents relation xs (ListView.encode element xs tail) :=
  ListView.represents_encode relation element faithful xs tail

example {width : Nat} (p : VCVio.Algorithms.Crc.Parameters width) (state : BitVec width)
    (xs ys : List (BitVec 8)) :
    VCVio.Algorithms.Crc.updateResult p state (xs ++ ys) =
      VCVio.Algorithms.Crc.updateResult p (VCVio.Algorithms.Crc.updateResult p state xs).state ys :=
  VCVio.Algorithms.Crc.updateResult_append p state xs ys

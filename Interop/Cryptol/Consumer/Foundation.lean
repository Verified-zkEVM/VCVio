/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Bridge.ImportedScalar
import Interop.Cryptol.Bridge.KeccakCodec

/-! # Foundation certificates through ordinary imports in an independent package -/

open Interop.Cryptol Interop.Cryptol.Bridge

example : Translation.SourceElaboration.check ImportedScalarSource.bundle
    ImportedScalarSource.root.expression 1000 = .ok ImportedScalar.certificate.result :=
  ImportedScalar.accepted

example (x : UInt32) :
    DomainResult.applyContinuous
      (Resolved.denote ImportedScalar.certificate.result.2 Environment.empty)
      (.value (wordValue x.toBitVec)) =
        .value (wordValue (VCVio.Algorithms.Sha2.ssig0 x).toBitVec) :=
  ImportedScalar.core_correct x

example (pre : BitVec 32 → Prop) (post : BitVec 32 → BitVec 32 → Prop) :
    Finite.DataContract (.word 32) (Resolved.lower ImportedScalar.compiled.source) pre post ↔
      ∀ x, pre x → post x (VCVio.Algorithms.Sha2.ssig0 (UInt32.ofBitVec x)).toBitVec :=
  ImportedScalar.core_contract_iff pre post

example (x : Fin 5) : Int.tmod ((x.val : Int) + 4) 5 = ((x.val : Int) - 1) % 5 :=
  KeccakCodec.theta_predecessor x

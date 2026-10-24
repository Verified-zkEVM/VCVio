/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.Import
public import Interop.Cryptol.Bridge.SourceScalars
public import Interop.Cryptol.Bridge.CompressionTotal
public import Interop.Cryptol.Bridge.Round
public import PolyFunCryptol.Translation.SourceElaboration
public import PolyFunCryptol.Translation.DataCertificate
import PolyFunCryptol.Translation.SourceElaboration
import PolyFunCryptol.Translation.SourceScope
import PolyFunCryptol.Model.Reference.Kinds
import PolyFunCryptol.Model.Reference.Types
import PolyFunCryptol.Model.Reference.Syntax
import PolyFunCryptol.Model.Types

/-!
# A checked Foundation scalar import

`cryptol_import` reads the exported frontend bundle, which passes the scope, kind,
constraint and expression typing gates. Its elaborated result is the retained resolved
scalar, whose partial semantics and all-input agreement with the core SHA-2
implementation are proved. The pinned external frontend remains outside Lean's
trusted kernel; regeneration checks tie the export to the source digests.
-/

public section

namespace Cryptol.Bridge

cryptol_import ImportedScalar from "Interop/Cryptol/artifacts/references/scalar-bundle.json"
  as smallSigma256Zero

namespace ImportedScalar

open Translation SourceElaboration

set_option maxRecDepth 10000

/-- The import is the retained Foundation scalar. -/
theorem import_eq : smallSigma256Zero = Foundation.wordSource1In := rfl

/-- Kernel reduction checks the actual exported dependency graph and scalar expression. -/
theorem accepted : check bundle smallSigma256Zero.root 1000 =
    .ok ⟨.arrow (wordTy 32) (wordTy 32), Foundation.wordSource1In⟩ := by
  rw [← import_eq]
  exact smallSigma256Zero.accepted

/-- The imported scalar's typing certificate retains its exact source and output. -/
@[expose] def certificate : Certificate bundle smallSigma256Zero.root where
  budget := 1000
  result := ⟨.arrow (wordTy 32) (wordTy 32), Foundation.wordSource1In⟩
  accepted := accepted

/-! `accepted` identifies the import's result with `Foundation.wordSource1In`, so the semantic
facts below are stated about that term. -/

/-- The imported scalar preserves all three shift demands, including on partial inputs. -/
theorem partial_correct (x : PartialWord) :
    DomainResult.applyContinuous (Resolved.denote Foundation.wordSource1In Environment.empty) x =
      sigmaMeaning 7 18 3 .right x := wordSource1In_correct _ x

/-- Native evaluation certifies the imported scalar against VCVio's `ssig0`. -/
@[expose] noncomputable def compiled : DataCertificate (.word 32) (.word 32) :=
  Resolved.dataCertificate (.word 32) (.word 32) Foundation.wordSource1In
    (fun x => (VCVio.Algorithms.Sha2.ssig0 (UInt32.ofBitVec x)).toBitVec) fun x => by
      have h := smallSigma256Zero_eq (UInt32.ofBitVec x)
      rw [UInt32.toBitVec_ofBitVec] at h
      rw [← h]
      simp [Foundation.wordSource1In]
      rfl

/-- Every 32-bit input agrees with the actual core SHA-2 small-sigma implementation. -/
theorem core_correct (x : UInt32) :
    DomainResult.applyContinuous (Resolved.denote Foundation.wordSource1In Environment.empty)
      (.value (wordValue x.toBitVec)) =
        .value (wordValue (VCVio.Algorithms.Sha2.ssig0 x).toBitVec) :=
  compiled.correct x.toBitVec

/-- Arbitrary bitvector specifications transfer from the imported scalar to the core algorithm. -/
theorem core_contract_iff (pre : BitVec 32 → Prop) (post : BitVec 32 → BitVec 32 → Prop) :
    DataContract (.word 32) (.word 32)
      (Resolved.denote Foundation.wordSource1In Environment.empty) pre post ↔
        ∀ x, pre x → post x (VCVio.Algorithms.Sha2.ssig0 (UInt32.ofBitVec x)).toBitVec :=
  compiled.contract_iff pre post

end ImportedScalar

end Cryptol.Bridge

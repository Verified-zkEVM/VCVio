/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.ImportedScalarSource
public import Interop.Cryptol.Bridge.SourceScalars
public import Interop.Cryptol.Bridge.CompressionTotal
public import Interop.Cryptol.Bridge.Round
public import Interop.Cryptol.Translation.SourceElaboration
public import Interop.Cryptol.Translation.Certified
import all Interop.Cryptol.Translation.SourceScope
import all Interop.Cryptol.Model.Reference.Kinds
import all Interop.Cryptol.Model.Reference.Types
import all Interop.Cryptol.Model.Reference.Syntax
import all Interop.Cryptol.Model.Types

/-!
# A checked Foundation scalar import

The exact quoted frontend bundle passes the scope, kind, constraint and expression
typing gates. Its elaborated result is the retained resolved scalar, whose partial
semantics and all-input agreement with the core SHA-2 implementation are proved.
The quotation and pinned external frontend remain outside Lean's trusted kernel;
regeneration checks tie the quotation to the exported JSON and source digests.
-/

public section

namespace Interop.Cryptol.Bridge.ImportedScalar

open Translation SourceElaboration ImportedScalarSource

set_option maxRecDepth 10000
/-- Kernel reduction checks the actual exported dependency graph and scalar expression. -/
theorem accepted : check bundle root.expression 1000 =
    .ok ⟨.arrow (wordTy 32) (wordTy 32), Foundation.wordSource1In⟩ := by
  with_unfolding_all rfl

/-- The imported scalar's typing certificate retains its exact source and output. -/
@[expose] def certificate : Certificate bundle root.expression where
  budget := 1000
  result := ⟨.arrow (wordTy 32) (wordTy 32), Foundation.wordSource1In⟩
  accepted := accepted

/-- The imported scalar preserves all three shift demands, including on partial inputs. -/
theorem partial_correct (x : PartialWord) :
    DomainResult.applyContinuous (Resolved.denote certificate.result.2 Environment.empty) x =
      sigmaMeaning 7 18 3 .right x := wordSource1In_correct _ x

/-- Every 32-bit input agrees with the actual core SHA-2 small-sigma implementation. -/
theorem core_correct (x : UInt32) :
    DomainResult.applyContinuous (Resolved.denote certificate.result.2 Environment.empty)
      (.value (wordValue x.toBitVec)) =
        .value (wordValue (VCVio.Algorithms.Sha2.ssig0 x).toBitVec) := by
  rw [partial_correct, sigmaMeaning_value]
  exact congrArg (fun v => DomainResult.value (wordValue v)) (smallSigma256Zero_eq x)

/-- The imported source has the existing finite native scalar as a certified implementation. -/
@[expose] noncomputable def compiled : Finite.CertifiedFunction (.word 32) (.word 32) where
  source := certificate.result.2
  implementation := Foundation.smallSigma256Zero
  correct x := (partial_correct (.value (wordValue x))).trans
    (sigmaMeaning_value 7 18 3 .right x)

/-- Arbitrary bitvector specifications transfer from the imported scalar to the core algorithm. -/
theorem core_contract_iff (pre : BitVec 32 → Prop) (post : BitVec 32 → BitVec 32 → Prop) :
    Finite.DataContract (.word 32) (Resolved.lower compiled.source) pre post ↔
      ∀ x, pre x → post x (VCVio.Algorithms.Sha2.ssig0 (UInt32.ofBitVec x)).toBitVec := by
  apply compiled.contract_iff
  intro x
  simpa only [compiled, UInt32.toBitVec_ofBitVec] using
    smallSigma256Zero_eq (UInt32.ofBitVec x)

end Interop.Cryptol.Bridge.ImportedScalar

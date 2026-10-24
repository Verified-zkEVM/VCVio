/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.ImportedScalar
public import PolyFunCryptol.Model.ResolvedLaws
import PolyFunCryptol.Translation.SourceElaboration
import PolyFunCryptol.Translation.SourceScope
import PolyFunCryptol.Model.Reference.Kinds
import PolyFunCryptol.Model.Reference.Types
import PolyFunCryptol.Model.Reference.Syntax
import PolyFunCryptol.Model.Types

/-!
# Checking an official Cryptol specialization candidate

The candidate is produced by Cryptol's `Specialize.specializeEWhere`, keeping primitive
instantiations explicit. `cryptol_import` checks it with the Lean elaborator, like the
unspecialized source. It keeps four local declarations: the shift, the two rotations, and the
function combining them by exclusive-or, which is the result. The correspondence below checks the
candidate's meaning on partial inputs; the external transformation is not an axiom. The
ordinary native implementation and its contracts use the existing certified-function API.
-/

public section

namespace Cryptol.Bridge

cryptol_import ImportedSpecialization from
  "Interop/Cryptol/artifacts/references/specialized-scalar-bundle.json" as smallSigma256Zero

namespace ImportedSpecialization

open Translation SourceElaboration

/-- The candidate carries the same typed-import evidence as the unspecialized source. -/
@[expose] def certificate : Certificate bundle smallSigma256Zero.root where
  budget := 1000
  result := ⟨_, smallSigma256Zero⟩
  accepted := smallSigma256Zero.accepted

/-- Specialization preserves the full partial function, including errors and bottom. -/
theorem correct : Resolved.denote smallSigma256Zero Environment.empty =
    Resolved.denote Foundation.wordSource1In Environment.empty := by
  rw [Foundation.wordSource1In, smallSigma256Zero]
  simp (config := { dsimp := false }) only [Resolved.denote_letE]
  simp (config := { dsimp := false }) only [Resolved.denote_var, Environment.cons_zero]
  apply Resolved.denote_lam_congr
  intro x
  simp (config := { dsimp := false }) only [Resolved.denote_app, Resolved.denote_primitive,
    Resolved.denote_wordLogic]
  simp (config := { dsimp := false }) only [Resolved.denote_var, Environment.cons_zero,
    Environment.cons_succ]
  simp (config := { dsimp := false }) only [Resolved.denote_lam_apply, Resolved.denote_app,
    Resolved.denote_primitive, Resolved.denote_shift]
  simp (config := { dsimp := false }) only [Resolved.denote_var, Environment.cons_zero,
    Resolved.denote_integer]
  simp only [Primitive.denote, Semantics.apply_function₂]

/-- All 32-bit inputs agree with VCVio's implementation after the checked transformation. -/
theorem core_correct (x : UInt32) :
    DomainResult.applyContinuous (Resolved.denote smallSigma256Zero Environment.empty)
      (.value (wordValue x.toBitVec)) =
        .value (wordValue (VCVio.Algorithms.Sha2.ssig0 x).toBitVec) := by
  rw [correct]
  exact ImportedScalar.core_correct x

end ImportedSpecialization

end Cryptol.Bridge

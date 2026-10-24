/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.ImportedScalar
public import Interop.Cryptol.Bridge.ImportedSpecializationSource
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
instantiations explicit. Both endpoints pass the Lean elaborator. The correspondence below
checks the candidate's meaning on partial inputs; the external transformation is not an axiom.
The ordinary native implementation and its contracts use the existing certified-function API.
-/

public section

namespace Cryptol.Bridge.ImportedSpecialization

open Translation SourceElaboration ImportedSpecializationSource

/-- The candidate retains four local declarations produced by the official specializer. -/
@[expose] def source : Resolved.Term [] (.arrow (wordTy 32) (wordTy 32)) :=
  .letE (.lam (.app (.app (.primitive (.shift 32 .right)) (.var .zero)) (.integer 3)))
    (.letE (.lam (.app (.app (.primitive (.shift 32 .rotateRight)) (.var .zero)) (.integer 7)))
      (.letE (.lam (.app (.app (.primitive (.shift 32 .rotateRight)) (.var .zero))
        (.integer 18)))
        (.letE (.lam (.app (.app (.primitive (.wordLogic 32 .xor))
          (.app (.app (.primitive (.wordLogic 32 .xor))
            (.app (.var (.succ (.succ .zero))) (.var .zero)))
            (.app (.var (.succ .zero)) (.var .zero))))
          (.app (.var (.succ (.succ (.succ .zero)))) (.var .zero)))) (.var .zero))))

set_option maxRecDepth 10000 in
/-- Kernel reduction checks the candidate graph, all local bindings, and its result type. -/
theorem accepted : check bundle root 1000 =
    .ok ⟨.arrow (wordTy 32) (wordTy 32), source⟩ := by
  with_unfolding_all rfl

/-- The candidate carries the same typed-import evidence as the unspecialized source. -/
@[expose] def certificate : Certificate bundle root where
  budget := 1000
  result := ⟨.arrow (wordTy 32) (wordTy 32), source⟩
  accepted := accepted

/-- Specialization preserves the full partial function, including errors and bottom. -/
theorem correct : Resolved.denote source Environment.empty =
    Resolved.denote Foundation.wordSource1In Environment.empty := by
  rw [Foundation.wordSource1In, source]
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
    DomainResult.applyContinuous (Resolved.denote source Environment.empty)
      (.value (wordValue x.toBitVec)) =
        .value (wordValue (VCVio.Algorithms.Sha2.ssig0 x).toBitVec) := by
  rw [correct]
  exact ImportedScalar.core_correct x

end Cryptol.Bridge.ImportedSpecialization

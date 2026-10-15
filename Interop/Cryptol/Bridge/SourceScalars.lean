/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.CompressionSemantics

import Mathlib.Tactic.FinCases

/-!
# Scalar equations for the preserved source

The closed source units have equations on partial words. These lemmas keep
source normalization independent of the concrete representation of the CPOs.
-/

public section

namespace Interop.Cryptol.Bridge

open Interop.Cryptol

set_option maxRecDepth 4096

/-- The preserved scalar unit retains all three partial shift demands. -/
theorem wordSource0In_correct {Γ : List ClosedTy} (ρ : Environment Γ) (x : PartialWord) :
    DomainResult.applyContinuous (Resolved.denote Foundation.wordSource0In ρ) x =
      sigmaMeaning 17 19 10 .right x := by
  rw [Foundation.wordSource0In, Resolved.denote_lam_apply]
  simp (config := { dsimp := false }) only [Resolved.denote_lam_apply, Resolved.denote_wordLogic,
    Resolved.denote_app, Resolved.denote_var, Resolved.denote_shift, Resolved.denote_integer,
    Environment.extend_zero]
  rfl

/-- The preserved scalar unit retains all three partial shift demands. -/
theorem wordSource1In_correct {Γ : List ClosedTy} (ρ : Environment Γ) (x : PartialWord) :
    DomainResult.applyContinuous (Resolved.denote Foundation.wordSource1In ρ) x =
      sigmaMeaning 7 18 3 .right x := by
  rw [Foundation.wordSource1In, Resolved.denote_lam_apply]
  simp (config := { dsimp := false }) only [Resolved.denote_lam_apply, Resolved.denote_wordLogic,
    Resolved.denote_app, Resolved.denote_var, Resolved.denote_shift, Resolved.denote_integer,
    Environment.extend_zero]
  rfl

/-- The preserved scalar unit retains all three partial shift demands. -/
theorem wordSource2In_correct {Γ : List ClosedTy} (ρ : Environment Γ) (x : PartialWord) :
    DomainResult.applyContinuous (Resolved.denote Foundation.wordSource2In ρ) x =
      sigmaMeaning 6 11 25 .rotateRight x := by
  rw [Foundation.wordSource2In, Resolved.denote_lam_apply]
  simp (config := { dsimp := false }) only [Resolved.denote_lam_apply, Resolved.denote_wordLogic,
    Resolved.denote_app, Resolved.denote_var, Resolved.denote_shift, Resolved.denote_integer,
    Environment.extend_zero]
  rfl

/-- The preserved scalar unit retains all three partial shift demands. -/
theorem wordSource4In_correct {Γ : List ClosedTy} (ρ : Environment Γ) (x : PartialWord) :
    DomainResult.applyContinuous (Resolved.denote Foundation.wordSource4In ρ) x =
      sigmaMeaning 2 13 22 .rotateRight x := by
  rw [Foundation.wordSource4In, Resolved.denote_lam_apply]
  simp (config := { dsimp := false }) only [Resolved.denote_lam_apply, Resolved.denote_wordLogic,
    Resolved.denote_app, Resolved.denote_var, Resolved.denote_shift, Resolved.denote_integer,
    Environment.extend_zero]
  rfl

/-- The complete choice closure is independent of the surrounding source environment. -/
theorem wordSource3In_denote {Γ : List ClosedTy} (ρ : Environment Γ) :
    Resolved.denote Foundation.wordSource3In ρ = .value choiceTupleMeaning := by
  rw [Foundation.wordSource3In]
  apply Resolved.denote_lam_eq
  intro p
  simp (config := { dsimp := false }) only [Resolved.denote_letE, Resolved.denote_fst,
    Resolved.denote_snd, Resolved.denote_wordLogic, Resolved.denote_app,
    Resolved.denote_primitive, Resolved.denote_var, Environment.extend_zero,
    Environment.extend_succ]
  rfl

/-- The complete majority closure is independent of the surrounding source environment. -/
theorem wordSource5In_denote {Γ : List ClosedTy} (ρ : Environment Γ) :
    Resolved.denote Foundation.wordSource5In ρ = .value majorityTupleMeaning := by
  rw [Foundation.wordSource5In]
  apply Resolved.denote_lam_eq
  intro p
  simp (config := { dsimp := false }) only [Resolved.denote_letE, Resolved.denote_fst,
    Resolved.denote_snd, Resolved.denote_wordLogic, Resolved.denote_var,
    Environment.extend_zero, Environment.extend_succ]
  rfl

/-- The source choice function on a constructed tuple demands only its components. -/
theorem wordSource3In_correct {Γ : List ClosedTy} (ρ : Environment Γ)
    (x y z : PartialWord) :
    DomainResult.applyContinuous (Resolved.denote Foundation.wordSource3In ρ)
      (.value (x, .value (y, z))) =
      Semantics.wordLogic 32 .xor (Semantics.wordLogic 32 .and x y)
        (Semantics.wordLogic 32 .and (Semantics.wordNot 32 x) z) := by
  rw [wordSource3In_denote, DomainResult.applyContinuous_value]
  rfl

/-- The source majority function on a constructed tuple retains all word operations. -/
theorem wordSource5In_correct {Γ : List ClosedTy} (ρ : Environment Γ)
    (x y z : PartialWord) :
    DomainResult.applyContinuous (Resolved.denote Foundation.wordSource5In ρ)
      (.value (x, .value (y, z))) =
      Semantics.wordLogic 32 .xor
        (Semantics.wordLogic 32 .xor (Semantics.wordLogic 32 .and x y)
          (Semantics.wordLogic 32 .and x z)) (Semantics.wordLogic 32 .and y z) := by
  rw [wordSource5In_denote, DomainResult.applyContinuous_value]
  rfl

/-- The source range contains exactly the 64 integer indices. -/
theorem tableSource0In_correct {Γ : List ClosedTy} (ρ : Environment Γ) :
    Resolved.denote Foundation.tableSource0In ρ = roundIndices := by
  rw [Foundation.tableSource0In, Resolved.denote_sequence]
  change DomainResult.value _ = DomainResult.value _
  apply congrArg DomainResult.value
  funext i
  rw [Resolved.denote_integer, Int.zero_add]

/-- The source literal table has all 64 extracted round constants. -/
theorem tableSource1In_correct {Γ : List ClosedTy} (ρ : Environment Γ) :
    Resolved.denote Foundation.tableSource1In ρ = constantsMeaning := by
  rw [Foundation.tableSource1In, Resolved.denote_sequence]
  change DomainResult.value _ = DomainResult.value _
  apply congrArg DomainResult.value
  funext i
  change Fin 64 at i
  fin_cases i <;> rfl

end Interop.Cryptol.Bridge

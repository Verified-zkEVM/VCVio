/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.SourceScalars
import Mathlib.Tactic.FinCases

/-!
# Normalization of the preserved Foundation source

These equations retain arbitrary partial inputs. They identify the source
fixed point and lazy fold before any recurrence is compiled.
-/

public section

namespace Cryptol.Bridge

open OmegaCompletePartialOrder Cryptol

set_option maxRecDepth 4096 in
/-- Source beta reduction and comprehension lowering preserve the recursive schedule. -/
theorem scheduleSourceIn_correct {Γ : List ClosedTy} (ρ : Environment Γ) (m : PartialBlock) :
    DomainResult.applyContinuous (Resolved.denote Foundation.scheduleSourceIn ρ) m =
      scheduleMeaning m := by
  rw [Foundation.scheduleSourceIn, Resolved.denote_lam_apply, Resolved.denote_fix]
  unfold scheduleMeaning
  apply congrArg ContinuousHom.fix
  apply DFunLike.ext
  intro w
  simp (config := { dsimp := false }) only [Resolved.denote_app,
    Resolved.denote_lam_apply, Resolved.denote_letE, Resolved.denote_var,
    Environment.cons_zero, Environment.cons_succ,
    Resolved.denote_primitive,
    Primitive.denote, Semantics.apply_function₂, Resolved.denote_generate,
    wordSource0In_correct, wordSource1In_correct, tableSource0In_correct, roundIndices,
    Resolved.denote_index, Resolved.denote_integer,
    Resolved.denote_ite, Resolved.denote_intOp,
    Resolved.denote_wordArithmetic]
  change DomainResult.value _ = DomainResult.value _
  apply congrArg DomainResult.value
  funext i
  simp (config := { dsimp := false }) only [Semantics.index_value_indexNat
    (l := .finite 64) (a := .integer)]
  have hc : Semantics.intLe (.value ⟨(i.val : Int)⟩) (.value ⟨15⟩) =
      (.value ⟨decide ((i.val : Int) ≤ 15)⟩ : Computation .bit) := rfl
  have hs (d : Int) : Semantics.binary IntOp.sub.eval
      (.value ⟨(i.val : Int)⟩ : Computation .integer) (.value ⟨d⟩) =
      .value ⟨(i.val : Int) - d⟩ := rfl
  simp (config := { dsimp := false }) only [hc, hs, Semantics.conditional_value]
  change (if decide ((i.val : Int) ≤ 15) then _ else _) =
    (if i.val ≤ 15 then _ else _)
  by_cases hi : i.val ≤ 15
  · have hb : decide ((i.val : Int) ≤ 15) = true := by
      simpa using (show (i.val : Int) ≤ 15 by omega)
    simp only [hb, hi, ↓reduceIte]
    rfl
  · have hb : decide ((i.val : Int) ≤ 15) = false := by
      simpa using (show ¬ (i.val : Int) ≤ 15 by omega)
    simp only [hb, hi, ↓reduceIte, Bool.false_eq_true]
    rfl

set_option maxRecDepth 4096 in
/-- The preserved round acts on arbitrary suspended registers and indices. -/
theorem roundSourceIn_apply_correct {Γ : List ClosedTy} (ρ : Environment Γ) (w : PartialSchedule)
    (s : PartialState) (t : Computation .integer) :
    DomainResult.applyContinuous (DomainResult.applyContinuous
      (DomainResult.applyContinuous (Resolved.denote Foundation.roundSourceIn ρ) w) s) t =
      roundMeaning w s t := by
  rw [Foundation.roundSourceIn, Resolved.denote_lam_apply, Resolved.denote_lam_apply,
    Resolved.denote_lam_apply]
  simp (config := { dsimp := false }) only [Resolved.denote_app,
    Resolved.denote_lam_apply, Resolved.denote_letE, Resolved.denote_var,
    Environment.cons_zero, Environment.cons_succ, wordSource2In_correct, wordSource3In_denote,
    wordSource4In_correct, wordSource5In_denote,
    tableSource1In_correct, Resolved.denote_sequence, Resolved.denote_index,
    Resolved.denote_integer, Resolved.denote_wordArithmetic, Resolved.denote_pair]
  change DomainResult.value _ = DomainResult.value _
  apply congrArg DomainResult.value
  change (_ : Fin 8 → PartialWord) = _
  funext i
  change Fin 8 at i
  fin_cases i <;> rfl

set_option maxRecDepth 4096 in
/-- A partially applied round retains the whole partial source function. -/
theorem roundSourceIn_correct {Γ : List ClosedTy} (ρ : Environment Γ) (w : PartialSchedule) :
    DomainResult.applyContinuous (Resolved.denote Foundation.roundSourceIn ρ) w =
      Semantics.function₂ (roundMeaning w) := by
  rw [Foundation.roundSourceIn, Resolved.denote_lam_apply]
  apply Resolved.denote_lam_eq (f := .ofFun (fun s =>
    (DomainResult.valueContinuous (roundMeaning w s) :
      Computation (.arrow .integer (.seq (.finite 8) (wordTy 32))))))
  intro s
  apply Resolved.denote_lam_eq (f := roundMeaning w s)
  intro t
  have h := roundSourceIn_apply_correct ρ w s t
  rw [Foundation.roundSourceIn, Resolved.denote_lam_apply, Resolved.denote_lam_apply,
    Resolved.denote_lam_apply] at h
  exact h

set_option maxRecDepth 4096 in
/-- Complete normalization preserves the recursive source on arbitrary partial inputs. -/
theorem compressionSource_correct (s : PartialState) (m : PartialBlock) :
    DomainResult.applyContinuous (DomainResult.applyContinuous
      (Resolved.denote Foundation.compressionSource Environment.empty) s) m =
      compressionMeaning s m := by
  rw [Foundation.compressionSource, Resolved.denote_lam_apply, Resolved.denote_lam_apply]
  simp (config := { dsimp := false }) only [Resolved.denote_app,
    Resolved.denote_lam_apply, Resolved.denote_letE]
  simp (config := { dsimp := false }) only [Resolved.denote_var, Environment.cons_zero,
    Environment.cons_succ]
  simp (config := { dsimp := false }) only [Resolved.denote_primitive, Primitive.denote,
    tableSource0In_correct, scheduleSourceIn_correct, roundSourceIn_correct,
    Semantics.apply_function₂, Semantics.apply_function₃]
  rfl

end Cryptol.Bridge

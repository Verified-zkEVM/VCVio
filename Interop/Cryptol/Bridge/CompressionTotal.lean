/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.CompressionSemantics

import Mathlib.Tactic.FinCases

/-!
# Totality and finite recurrence compilation

Fully represented input data yields all bits of all output words. The proof
uses uniqueness of prefix-dependent recursive arrays, followed by induction
over the finite fold. No evaluator fuel or solver result is assumed.
-/

public section

namespace Cryptol.Bridge

open OmegaCompletePartialOrder Cryptol Cryptol.Finite

/-- Canonical complete representation of an array of 32-bit words. -/
@[expose] noncomputable def wordsMeaning {n : Nat} (xs : Fin n → BitVec 32) :
    Computation (.seq (.finite n) (wordTy 32)) :=
  .value (fun i => .value (wordValue (xs i)))

/-- The direct source sigma operations compute their native bitvector functions. -/
theorem sigmaMeaning_value (a b c : Nat) (op : ShiftOp) (x : BitVec 32) :
    sigmaMeaning a b c op (.value (wordValue x)) =
      .value (wordValue (x.rotateRight a ^^^ x.rotateRight b ^^^
        (match op with
          | .left => x <<< c | .right => x >>> c
          | .rotateLeft => x.rotateLeft c | .rotateRight => x.rotateRight c))) := by
  unfold sigmaMeaning
  dsimp only [ContinuousHom.ofFun, ContinuousHom.coe_mk, OrderHom.coe_mk]
  rw [← Semantics.shiftFixed_eq_shift .rotateRight 32 a,
    ← Semantics.shiftFixed_eq_shift .rotateRight 32 b, ← Semantics.shiftFixed_eq_shift op 32 c]
  simp only [Semantics.shiftFixed_value, Semantics.wordLogic_values]
  rfl

/-- Schedule equations use only strictly earlier entries of a constructor-bearing table. -/
theorem scheduleMeaningBody_usesPrefix (m : PartialBlock) :
    Function.UsesPrefix (fun xs => scheduleMeaningBody m (DomainResult.value xs)) := by
  intro i x y hxy
  change (if i.val ≤ 15 then _ else _) = (if i.val ≤ 15 then _ else _)
  by_cases hi : i.val ≤ 15
  · simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte]
    erw [Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) x i.val 2 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) x i.val 7 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) x i.val 15 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) x i.val 16 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) y i.val 2 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) y i.val 7 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) y i.val 15 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) y i.val 16 (by omega) (by omega)]
    rw [hxy ⟨i.val - 2, by omega⟩ (by change i.val - 2 < i.val; omega),
      hxy ⟨i.val - 7, by omega⟩ (by change i.val - 7 < i.val; omega),
      hxy ⟨i.val - 15, by omega⟩ (by change i.val - 15 < i.val; omega),
      hxy ⟨i.val - 16, by omega⟩ (by change i.val - 16 < i.val; omega)]

/-- The native schedule satisfies every partial source equation with complete word values. -/
theorem scheduleMeaningBody_value (m : Fin 16 → BitVec 32) :
    scheduleMeaningBody (wordsMeaning m) (wordsMeaning (schedule256 m)) =
      fun i => DomainResult.value (wordValue (schedule256 m i)) := by
  funext i
  have hn : schedule256 m i = scheduleStep m i.val
      (fun j => schedule256 m ⟨j.val, j.isLt.trans i.isLt⟩) :=
    prefixValues_apply (scheduleStep m) 64 i
  rw [hn]
  change (if i.val ≤ 15 then _ else _) = _
  by_cases hi : i.val ≤ 15
  · rw [ite_eq_left hi, scheduleStep, dite_eq_left (by omega)]
    exact Semantics.indexAt_value_nat (n := 16) (a := wordTy 32) _ i.val (by omega)
  · rw [ite_eq_right hi, scheduleStep, dite_eq_right (by omega)]
    unfold wordsMeaning
    erw [Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) _ i.val 2 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) _ i.val 7 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) _ i.val 15 (by omega) (by omega),
      Semantics.indexAt_value_sub (n := 64) (a := wordTy 32) _ i.val 16 (by omega) (by omega)]
    rw [sigmaMeaning_value, sigmaMeaning_value, Semantics.wordAdd_values,
      Semantics.wordAdd_values, Semantics.wordAdd_values]
    rfl

set_option maxRecDepth 4096 in
/-- The least fixed point equals the compiled 64-entry schedule for every block. -/
theorem scheduleMeaning_value (m : Fin 16 → BitVec 32) :
    scheduleMeaning (wordsMeaning m) = wordsMeaning (schedule256 m) := by
  exact DomainResult.generateStep_fix_eq (n := 64) (ε := EvalError) (D := PartialWord)
    (scheduleMeaningBody (wordsMeaning m)) (scheduleMeaningBody_usesPrefix _)
    (fun i => DomainResult.value (wordValue (schedule256 m i))) (scheduleMeaningBody_value m)

/-- Every represented source round computes the extracted native register update. -/
theorem roundMeaning_value (s : Fin 8 → BitVec 32) (w : Fin 64 → BitVec 32) (i : Fin 64) :
    roundMeaning (wordsMeaning w) (wordsMeaning s) (.value ⟨(i.val : Int)⟩) =
      wordsMeaning (Foundation.round256Native (s, Foundation.constants256 i, w i)) := by
  unfold roundMeaning
  dsimp only [ContinuousHom.ofFun, ContinuousHom.coe_mk, OrderHom.coe_mk]
  change DomainResult.value _ = DomainResult.value _
  apply congrArg DomainResult.value
  funext j
  fin_cases j <;>
    simp [wordsMeaning, constantsMeaning, Semantics.indexAt, Semantics.index_values,
      Length.checkIndex, i.isLt, sigmaMeaning_value, Foundation.round256Native]

/-- Every prefix of the lazy source fold computes its compiled register state. -/
theorem compressionFold_value (w : Fin 64 → BitVec 32) (s : Fin 8 → BitVec 32)
    (k : Nat) (hk : k ≤ 64) :
    Semantics.foldlPrefix 64 k (Semantics.function₂ (roundMeaning (wordsMeaning w)))
      (wordsMeaning s) roundIndices = wordsMeaning (compressionRounds w s k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Semantics.foldlPrefix_succ, ih (by omega), Semantics.apply_function₂]
      have hx : Semantics.indexAt roundIndices (k : Int) =
          (.value ⟨(k : Int)⟩ : Computation .integer) :=
        Semantics.indexAt_value_nat (n := 64) (a := .integer) _ k (by omega)
      rw [hx, roundMeaning_value _ _ ⟨k, by omega⟩]
      simp only [compressionRounds, compressionRound, dite_eq_left (by omega : k < 64)]

/-- Complete source compression produces every output bit on represented inputs. -/
theorem compressionMeaning_value (s : Fin 8 → BitVec 32) (m : Fin 16 → BitVec 32) :
    compressionMeaning (wordsMeaning s) (wordsMeaning m) =
      wordsMeaning (compressionNative (s, m)) := by
  unfold compressionMeaning
  rw [scheduleMeaning_value, compressionFold_value _ _ 64 (by omega)]
  unfold Semantics.wordArrayArithmetic
  simp only [wordsMeaning]
  change DomainResult.value _ = DomainResult.value _
  apply congrArg DomainResult.value
  funext i
  erw [Semantics.indexAt_value_nat (a := wordTy 32) (n := 8) _ i.val i.isLt,
    Semantics.indexAt_value_nat (a := wordTy 32) (n := 8) _ i.val i.isLt]
  rw [Semantics.wordAdd_values]
  rfl

end Cryptol.Bridge

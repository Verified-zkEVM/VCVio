/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Programming
import Mathlib.Tactic.FinCases

/-!
# Ranked pointer-chain programming regressions

The one-chain boundary has no repeated input with zero or one internal step, even when its
state labels coincide. Two internal steps can repeat an oracle input and demand conflicting
answers. Full programmed mask responses also retain bytes outside the honest mask prefix.

A separate two-node example shows why causal ordering is needed to express the inverse
exchange as programming with fixed final labels.
-/

public section

open PointerChainPuzzle PointerChainPuzzle.LeanSeal OracleComp

namespace VCVioTest.PointerChainProgramming

private theorem hb32 : 32 ≤ 32 := by decide
private theorem hB32 : hashInputBound 32 ≤ 86 := by decide
private theorem hb16 : 16 ≤ 32 := by decide
private theorem hB16 : hashInputBound 16 ≤ 86 := by decide

private def emptyLinks : Fin 0 → Bytes 32 := Fin.elim0

/-- With at most one internal step, every path input uses a different typed oracle family. -/
private theorem small_inputs_injective {m : ℕ} (hm : m ≤ 1)
    (W : PathValue 1 m → Bytes 32) :
    Function.Injective (fun v ↦ rawPathInput hb32 hB32 (n := 1) 0 0 emptyLinks v W) := by
  rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
  all_goals
    intro v w h
    have ht := hashInput_injective (b := 32) (n := 1) (by decide)
      (congrArg ByteArray.Bounded.toByteArray h)
    clear h
    fin_cases v <;> fin_cases w <;> simp_all [PathValue.equivSum, pathInput]

/-- The zero-step boundary recovers the complete prescribed puzzle and key under the named
raw programmer, without any distinctness hypothesis on the output labels. -/
example (H : ByteArray.Bounded 86 → Bytes 32) (W : PathValue 1 0 → Bytes 32) :
    simulateQ (impl (extendWindowOracle (programPath hb32 hB32 0 0 emptyLinks H W)) 32 1)
        (genMaskedWith 0 (ctx 32 1 0) id 0 0 emptyLinks) =
      pure (labelPuzzle 0 0 emptyLinks (pathLabels hb32 W), (pathLabels hb32 W) .key) := by
  have hi := small_inputs_injective (m := 0) (by decide) W
  exact simulateQ_genMaskedWith_programPath_of_injective (b := 32) (n := 1) (m := 0)
    (B := 86) hb32 hB32 0 0 emptyLinks H W hi

/-- Equal start and endpoint labels do not create a path-input collision with one step. -/
example :
    pathLabels hb32 (fun _ : PathValue 1 1 ↦ 0) (.state 0 0) =
        pathLabels hb32 (fun _ : PathValue 1 1 ↦ 0) (.state 0 1) ∧
      Function.Injective (fun v ↦ rawPathInput hb32 hB32 (n := 1) 0 0 emptyLinks v
        (fun _ : PathValue 1 1 ↦ 0)) := by
  exact ⟨rfl, small_inputs_injective (by decide) _⟩

/-- A full raw response with one nonzero byte beyond the 16-byte mask prefix. -/
@[expose]
def taggedWord : Bytes 32 :=
  ⟨Vector.ofFn fun i ↦ if i.val = 31 then 7 else 0⟩

private theorem taggedWord_ne_zero : taggedWord ≠ 0 := by
  intro h
  have he := congrArg (fun w : Bytes 32 ↦ w.toVector[31]) h
  norm_num [taggedWord] at he

private def inconsistentWords (v : PathValue 1 2) : Bytes 32 :=
  if v = .state 0 2 then taggedWord else 0

/-- Two internal steps may query the same cell when their predecessor labels coincide. -/
private theorem repeated_step_input :
    rawPathInput hb32 hB32 (n := 1) 0 0 emptyLinks (.state 0 1) inconsistentWords =
      rawPathInput hb32 hB32 (n := 1) 0 0 emptyLinks (.state 0 2) inconsistentWords := by
  simp [rawPathInput, pathWindowInput, pathLabels, splitPath, pathInput, inconsistentWords]
  rfl

/-- The repeated cell cannot provide two different prescribed full responses. -/
example : ¬ ∃ H : ByteArray.Bounded 86 → Bytes 32,
    ∀ v : PathValue 1 2,
      H (rawPathInput hb32 hB32 0 0 emptyLinks v inconsistentWords) = inconsistentWords v := by
  rintro ⟨H, h⟩
  have he : inconsistentWords (.state 0 1) = inconsistentWords (.state 0 2) :=
    (h (.state 0 1)).symm.trans ((congrArg H repeated_step_input).trans (h (.state 0 2)))
  have hn : inconsistentWords (.state 0 1) ≠ inconsistentWords (.state 0 2) := by
    simpa [inconsistentWords] using Ne.symm taggedWord_ne_zero
  exact hn he

/-- The honest mask prefix is zero even though the complementary raw bytes are nonzero. -/
example :
    (splitMask (by decide : 16 ≤ 32) taggedWord).1 = 0 ∧
      (splitMask (by decide : 16 ≤ 32) taggedWord).2.toVector[15] = 7 := by
  constructor
  · change (taggedWord.take : Bytes 16) = 0
    apply Bytes.ext_getElem
    intro i hi
    simp [Bytes.take, Bytes.read, taggedWord, List.getD_eq_getElem?_getD,
      Bytes.getElem_toList, show i < 32 by omega, show i ≠ 31 by omega]
  · change (Bytes.read taggedWord.toList 16 : Bytes 16).toVector[15] = 7
    simp [Bytes.read, taggedWord, List.getD_eq_getElem?_getD, Bytes.getElem_toList]

/-- A programmed mask retains its full raw response beyond the prefix used by honest code. -/
example (H : ByteArray.Bounded 86 → Bytes 32) (W : PathValue 2 0 → Bytes 32)
    (hinj : Function.Injective (fun v ↦ rawPathInput hb16 hB16 (n := 2) 0 0
      (fun _ ↦ (0 : Bytes 16)) v W)) (hw : W (.mask 0) = taggedWord) :
    (programPath hb16 hB16 0 0 (fun _ ↦ (0 : Bytes 16)) H W
      (rawPathInput hb16 hB16 0 0 (fun _ ↦ (0 : Bytes 16)) (.mask 0) W)).toVector[31] = 7 := by
  rw [programPath_apply_of_injective hb16 hB16 0 0 (fun _ ↦ (0 : Bytes 16)) H W hinj, hw]
  decide

/-! ## Inverse exchanges need causal input dependencies -/

private def futureInput (v : Bool) (l : Bool → Bool) : Bool :=
  if v then false else l true

private theorem futureInput_update (v : Bool) (l : Bool → Bool) (a : Bool) :
    futureInput v (Function.update l v a) = futureInput v l := by
  cases v <;> simp [futureInput]

private def fullSplit (_v : Bool) : Bool ≃ Bool × Unit :=
  (Equiv.prodPUnit Bool).symm

private def futureExchange :
    ((Bool → Bool) × (Bool → Bool)) ≃ ((Bool → Bool) × (Bool → Bool)) :=
  Equiv.tableLabelExchangeList futureInput fullSplit futureInput_update [false, true]

/-- Own-label invariance permits the permutation, but a future-label dependency prevents
reconstructing its inverse by reverse programming with fixed final labels. -/
example :
    (futureExchange.symm (id, id)).1 false = false ∧
      Equiv.tableLabelProgram futureInput fullSplit [false, true] id id false = true := by
  decide

end VCVioTest.PointerChainProgramming

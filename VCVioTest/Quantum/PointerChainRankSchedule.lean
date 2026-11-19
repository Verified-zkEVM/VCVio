/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.RankSchedule
public import VCVio.Quantum.Oracle.ParallelSchedule
public import VCVioTest.Quantum.PointerChainProgramming
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Rank-cutoff oracle regressions

Repeated inputs do not obstruct the support theorem. Typed labels alone do not determine a
prefix's raw responses: a mask tail can change while every typed label stays fixed. The public
commitment survives resampling, although its oracle cell remains unprogrammed before its rank.
-/

public section

open Quantum PointerChainPuzzle PointerChainPuzzle.LeanSeal OracleComp

namespace VCVioTest.PointerChainRankSchedule

private theorem hb : 16 ≤ 32 := by decide
private theorem hB : hashInputBound 16 ≤ 86 := by decide

/-- A listed full-word write is recovered when no other listed write uses its input. -/
private theorem read_unique {D V M : Type} [DecidableEq D]
    (input : V → (V → M) → D) (vs : List V) (H : D → M) (W : V → M) (v : V)
    (hv : v ∈ vs) (hu : ∀ w ∈ vs, input w W = input v W → w = v) :
    Equiv.tableLabelProgram input (fun _ ↦ (Equiv.prodPUnit M).symm) vs H W
      (input v W) = W v := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
    rw [Equiv.tableLabelProgram]
    by_cases he : w = v
    · subst w
      simp
    · rw [Function.update_of_ne (fun h ↦ he (hu w List.mem_cons_self h.symm))]
      exact ih (List.mem_cons.mp hv |>.resolve_left (Ne.symm he))
        (fun u hu' ↦ hu u (List.mem_cons_of_mem _ hu'))

private theorem read_mask (W : PathValue 2 0 → Bytes 32) :
    prefixProgram hb hB (n := 2) 0 0 (fun _ ↦ 0) 2 (fun _ ↦ 0) W
      (rawPathInput hb hB 0 0 (fun _ ↦ 0) (.mask 0) W) = W (.mask 0) := by
  apply read_unique
  · simp [PathValue.mem_order, PathValue.rho]
  · intro v _ he
    have ht := hashInputWindow_injective (b := 16) (n := 2) hB (by decide) he
    clear he
    fin_cases v <;> simp_all [PathValue.equivSum, pathInput]

private def zeroWords : PathValue 2 0 → Bytes 32 := fun _ ↦ 0
/-- Raw mask words with a nonzero byte beyond the honest 16-byte prefix. -/
@[expose]
def tailWords : PathValue 2 0 → Bytes 32 :=
  Function.update (fun _ ↦ 0) (.mask 0) PointerChainProgramming.taggedWord

private theorem mask_prefix_zero :
    (PointerChainProgramming.taggedWord.take : Bytes 16) = 0 := by
  apply Bytes.ext_getElem
  intro i hi
  simp [Bytes.take, Bytes.read, PointerChainProgramming.taggedWord,
    List.getD_eq_getElem?_getD, Bytes.getElem_toList, show i < 32 by omega,
    show i ≠ 31 by omega]

/-- A raw tail is invisible to every typed label but changes a rank-two prefix oracle. -/
example : pathLabels hb zeroWords = pathLabels hb tailWords ∧
    prefixProgram hb hB (n := 2) 0 0 (fun _ ↦ 0) 2 (fun _ ↦ 0) zeroWords ≠
      prefixProgram hb hB (n := 2) 0 0 (fun _ ↦ 0) 2 (fun _ ↦ 0) tailWords := by
  constructor
  · funext v
    by_cases hv : v = .mask 0
    · subst v
      simp only [pathLabels, zeroWords, tailWords, Function.update_self, splitPath]
      change (0 : Bytes 32).take = PointerChainProgramming.taggedWord.take
      rw [mask_prefix_zero]
      apply Bytes.ext_getElem
      intro i hi
      simp [Bytes.take, Bytes.read, List.getD_eq_getElem?_getD, Bytes.getElem_toList,
        show i < 32 by omega]
    · simp [pathLabels, zeroWords, tailWords, Function.update_of_ne hv]
  · intro he
    have hm := congrArg (fun H ↦ H (rawPathInput hb hB 0 0 (fun _ ↦ 0)
      (.mask 0) zeroWords)) he
    have ha : rawPathInput hb hB 0 0 (fun _ ↦ 0) (.mask 0) tailWords =
        rawPathInput hb hB 0 0 (fun _ ↦ 0) (.mask 0) zeroWords :=
      rawPathInput_update_self hb hB 0 0 (fun _ ↦ 0) _ _ _
    rw [read_mask, ← ha, read_mask] at hm
    have he := congrArg (fun w : Bytes 32 ↦ w.toVector[31]) hm
    norm_num [zeroWords, tailWords, PointerChainProgramming.taggedWord] at he

private def repeatedWords (v : PathValue 1 2) : Bytes 32 :=
  if v = .state 0 2 then PointerChainProgramming.taggedWord else 0

/-- Future-input support remains valid for an actual collision with conflicting node words. -/
example :
    rawPathInput hb hB (n := 1) 0 0 Fin.elim0 (.state 0 1) repeatedWords =
      rawPathInput hb hB (n := 1) 0 0 Fin.elim0 (.state 0 2) repeatedWords ∧
    ∀ d ∉ futureRawPathInputs hb hB 0 0 Fin.elim0 repeatedWords 2,
      programPath hb hB 0 0 Fin.elim0 (fun _ ↦ 0) repeatedWords d =
        prefixProgram hb hB 0 0 Fin.elim0 2 (fun _ ↦ 0) repeatedWords d := by
  constructor
  · simp [rawPathInput, pathWindowInput, pathLabels, splitPath, pathInput, repeatedWords]
    rfl
  · exact fun d hd ↦ programPath_eq_prefixProgram_of_avoids_future hb hB
      0 0 Fin.elim0 2 (fun _ ↦ 0) repeatedWords d hd

private theorem small_injective (W : PathValue 1 0 → Bytes 32) :
    Function.Injective (fun v ↦ rawPathInput hb hB (n := 1) 0 0 Fin.elim0 v W) := by
  intro v w h
  have ht := hashInput_injective (b := 16) (n := 1) (by decide)
    (congrArg ByteArray.Bounded.toByteArray h)
  fin_cases v <;> fin_cases w <;> simp_all [PathValue.equivSum, pathInput]

private theorem commit_unprogrammed (W : PathValue 1 0 → Bytes 32) :
    prefixProgram hb hB (n := 1) 0 0 Fin.elim0 2 (fun _ ↦ 0) W
      (rawPathInput hb hB 0 0 Fin.elim0 .commit W) = 0 := by
  apply Equiv.tableLabelProgram_apply_of_avoids
  intro v hv he
  have hr : v.rho ≤ 2 := by simpa using (List.mem_filter.mp hv).2
  have hv := small_injective W he
  subst v
  norm_num [PathValue.rho, keyRound] at hr

/-- The boundary has key rank three. Resampling preserves the public commitment, but at
rank two the commitment's raw cell still answers from the base oracle. -/
example (W : PathValue 1 0 → Bytes 32) (ℓ' : Labels 1 0 (Bytes 32) (Bytes 16)) :
    keyRound 1 0 = 3 ∧
    labelPuzzle (0 : Bytes 16) 0 Fin.elim0 (pathLabels hb (mixPathWords hb ∅ W ℓ')) =
      labelPuzzle 0 0 Fin.elim0 (pathLabels hb W) ∧
    prefixProgram hb hB (n := 1) 0 0 Fin.elim0 2 (fun _ ↦ 0)
      (mixPathWords hb ∅ W ℓ')
      (rawPathInput hb hB 0 0 Fin.elim0 .commit (mixPathWords hb ∅ W ℓ')) = 0 := by
  exact ⟨rfl, labelPuzzle_pathLabels_mixPathWords hb 0 0 Fin.elim0 ∅ W ℓ',
    commit_unprogrammed _⟩

/-- The rectangular runtime extraction preserves zero-width calls and private memory. -/
example (H : ℕ → Fin 2 → ZMod 3) (t : ℕ) :
    (parallelScheduledRuntime H).step (t, (), 0) = SubInstrument.pure () := by
  change (parallelOracleQuery (H t) 0).frame (QReg.of Unit) = _
  rw [parallelOracleQuery_zero_width, SubInstrument.frame_pure]

end VCVioTest.PointerChainRankSchedule

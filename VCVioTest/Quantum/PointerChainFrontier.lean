/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.RankFrontier
public import Mathlib.Data.ZMod.Basic

/-!
# Pointer-chain rank-frontier regressions

The one-chain, zero-step boundary still has a start, accumulator, key and commitment.
For several chains, the later accumulator needs both its earlier accumulator and its own
chain end. Public knowledge of the commitment's output does not reveal its oracle input.
-/

public section

open PointerChainPuzzle

namespace VCVioTest.PointerChainFrontier

/-- Even with no internal steps, the key and commitment occupy different rounds. -/
example : (PathValue.key : PathValue 1 0).rho = 3 ∧
    (PathValue.commit : PathValue 1 0).rho = 4 := by decide

/-- Round zero contains no path values; round one contains exactly the initial start. -/
example : PathValue.rankPrefix 1 0 0 = ∅ ∧
    PathValue.rankPrefix 1 0 1 = {PathValue.firstStart} := by
  constructor
  · ext v
    rcases v with ⟨i, k⟩ | i | i | _ | _
    · fin_cases i
      fin_cases k
      norm_num [PathValue.mem_rankPrefix, PathValue.rho]
    · exact Fin.elim0 i
    · fin_cases i
      norm_num [PathValue.mem_rankPrefix, PathValue.rho]
    · norm_num [PathValue.mem_rankPrefix, PathValue.rho, keyRound]
    · norm_num [PathValue.mem_rankPrefix, PathValue.rho, keyRound]
  · ext v
    rcases v with ⟨i, k⟩ | i | i | _ | _
    · fin_cases i
      fin_cases k
      norm_num [PathValue.mem_rankPrefix, PathValue.rho, PathValue.firstStart]
    · exact Fin.elim0 i
    · fin_cases i
      norm_num [PathValue.mem_rankPrefix, PathValue.rho, PathValue.firstStart]
    · norm_num [PathValue.mem_rankPrefix, PathValue.rho, PathValue.firstStart, keyRound]
    · norm_num [PathValue.mem_rankPrefix, PathValue.rho, PathValue.firstStart, keyRound]

/-- The key becomes available at its rank, while the commitment waits one more round. -/
example : (PathValue.key : PathValue 1 0) ∉ PathValue.rankPrefix 1 0 2 ∧
    PathValue.key ∈ PathValue.rankPrefix 1 0 3 ∧
    PathValue.commit ∉ PathValue.rankPrefix 1 0 3 ∧
    PathValue.commit ∈ PathValue.rankPrefix 1 0 4 := by
  norm_num [PathValue.mem_rankPrefix, PathValue.rho, keyRound]

/-- A later accumulator needs the preceding accumulator and the new chain's endpoint. -/
example : (PathValue.acc 1 : PathValue 2 1).preds =
    {PathValue.acc 0, PathValue.state 1 1} := by rfl

/-- Before the second chain ends, only one of those accumulator predecessors is available. -/
example : (PathValue.acc 0 : PathValue 2 1) ∈ PathValue.rankPrefix 2 1 4 ∧
    PathValue.state 1 1 ∉ PathValue.rankPrefix 2 1 4 ∧
    (PathValue.acc 1 : PathValue 2 1).rho = 6 := by
  norm_num [PathValue.mem_rankPrefix, PathValue.rho]

/-- Once both predecessors are available, resampling future labels preserves the input. -/
example (P : Puzzle 2 (ZMod 3) (ZMod 2) Unit) (ℓ₀ ℓ' : Labels 2 1 (ZMod 3) (ZMod 2)) :
    pathInput 1 (fun _ : Unit ↦ ()) (fun _ ↦ (0 : ZMod 3)) P
        (mixLabels (PathValue.rankPrefix 2 1 5) ℓ₀ ℓ') (PathValue.acc 1) =
      pathInput 1 (fun _ : Unit ↦ ()) (fun _ ↦ (0 : ZMod 3)) P ℓ₀ (PathValue.acc 1) :=
  pathInput_mixLabels_rankPrefix P ℓ₀ ℓ' (by decide)

/-- Keeping the public commitment fixed does not also keep its hidden key input fixed. -/
example (ℓ₀ ℓ' : Labels 1 0 (ZMod 3) (ZMod 2)) :
    mixLabels (PathValue.rankPrefix 1 0 2) ℓ₀ ℓ' .commit = ℓ₀ .commit ∧
    mixLabels (PathValue.rankPrefix 1 0 2) ℓ₀ ℓ' .key = ℓ' .key := by
  constructor
  · exact mixLabels_commit _ _ _
  · exact mixLabels_of_not_mem
      (by norm_num [PathValue.mem_rankPrefix, PathValue.rho, keyRound])
      (by intro h; cases h)

/-- A fixed input remains subject to the future-input incidence bound at the empty frontier. -/
example (P : Puzzle 1 (ZMod 3) (ZMod 2) Unit) (ℓ₀ : Labels 1 0 (ZMod 3) (ZMod 2))
    (t : Point 1 (ZMod 3) (ZMod 2) Unit Unit) :
    Pr{let ℓ' ← $ᵗ Labels 1 0 (ZMod 3) (ZMod 2)}[
      t ∈ futurePathInputs 0 (fun _ : Unit ↦ ()) (fun _ ↦ (0 : ZMod 3)) P
        (mixLabels (PathValue.rankPrefix 1 0 0) ℓ₀ ℓ') 1] ≤
      hitBound 1 0 (ZMod 3) (ZMod 2) :=
  prEvent_mem_futurePathInputs_mixLabels_le P ℓ₀ 0 t

end VCVioTest.PointerChainFrontier

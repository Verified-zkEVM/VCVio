/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.Algorithms.IndexedChain.Witnesses

/-!
# Indexed chain regressions

The position-sensitive callback distinguishes zero-based addresses from positive-step tweaks.
State observations check callback order; finite witnesses check both designated-cut branches.
-/

public section

namespace VCVioTest.IndexedChain

open VCVio.Algorithms.IndexedChain

private def orderedStep (j x : Nat) : Nat := 10 * x + j

/-- Zero-based callback positions distinguish every step in the resulting value. -/
theorem zero_based_positions : chain (fun j x : Nat => 10 * x + j) 0 3 4 = 4012 := rfl
example : chain orderedStep 1 3 4 = 4123 := rfl
example : chain orderedStep 7 0 4 = 4 := rfl

private def recordStep (j x : Nat) : StateM (List Nat) Nat := do
  modify (· ++ [j])
  pure (orderedStep j x)

example : (chainM recordStep 2 3 0).run [] = (234, [2, 3, 4]) := rfl
example : (chainM recordStep 7 0 4).run [] = (4, []) := rfl

example : chainM (m := Option) (fun j x => if j = 3 then none else some (x + j))
    2 3 0 = none := rfl

example : chain orderedStep 2 (1 + 2) 0 =
    chain orderedStep 3 2 (chain orderedStep 2 1 0) :=
  chain_add orderedStep 2 1 2 0

private def mergeStep (j x : Nat) : Nat := if j = 2 then 0 else x

example : findMerge mergeStep 0 3 1 2 = some ⟨2, by decide⟩ := by decide
example : findMerge mergeStep 0 0 1 2 = none := rfl
example : findMerge orderedStep 0 3 1 2 = none := by decide

example : (findMerge mergeStep 0 3 1 2).isSome :=
  findMerge_isSome mergeStep 0 3 1 2 (by decide) (by decide)

example : findCut (fun _ x : Nat => x + 1) 0 2 3 2 0 = some (.inl 1) := by decide

example : (fun _ x : Nat => x + 1) (2 - 1) 1 = 2 :=
  findCut_preimage_sound (fun _ x : Nat => x + 1) 0 2 3 2 0 1 (by decide) (by decide)

private def cutMergeStep (j x : Nat) : Nat := if j = 3 then 0 else orderedStep j x

example : findCut cutMergeStep 0 2 4 99 1 = some (.inr ⟨1, by decide⟩) := by decide

example : (findCut cutMergeStep 0 2 4 99 1).isSome :=
  findCut_isSome cutMergeStep 0 2 4 99 1 (by decide) (by decide) (by decide)

end VCVioTest.IndexedChain

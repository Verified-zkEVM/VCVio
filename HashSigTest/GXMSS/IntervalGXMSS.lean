/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
public import HashSig.GXMSS.Security.Interval.Auxiliary.FullRangeInteraction

/-!
# Interval GXMSS import and trust probe

`DirectTrustAudit` checks compiler origins and transitive axioms in both interval
specification and security modules. The finite fixtures exercise mixed frontier geometry.
-/

public section

open GXMSS.IntervalMerkle

private def interval25 : Interval 3 := ⟨2, 5, by decide⟩

private def interval16 : Interval 3 := ⟨1, 6, by decide⟩

private def singleton3 : Interval 3 := ⟨3, 3, by decide⟩

example : Epoch.IsActive interval25 2 := by decide
example : Epoch.IsActive interval25 5 := by decide
example : ¬ Epoch.IsActive interval25 1 := by decide
example : Subtree.DisjointFromInterval interval25 0 8 := by decide
example : ¬ Subtree.IsInactiveFrontier interval25 0 8 := by decide
example : ¬ Subtree.IsInactiveFrontier interval25 3 0 := by decide
example : Subtree.IsInactiveFrontier interval25 1 0 := by decide
example : Subtree.IsInactiveFrontier interval25 1 3 := by decide
example : frontierLevel interval25 (0 : Fin 8) = 1 := by decide
example : frontierLevel interval25 (7 : Fin 8) = 1 := by decide
example : Subtree.IsInactiveFrontier interval16 0 0 := by decide
example : Subtree.IsInactiveFrontier interval16 0 7 := by decide
example : Subtree.IsInactiveFrontier singleton3 1 0 := by decide
example : Subtree.IsInactiveFrontier singleton3 0 2 := by decide
example : Subtree.IsInactiveFrontier singleton3 2 1 := by decide
example : frontierLevel singleton3 (2 : Fin 8) = 0 := by decide
example : frontierLevel singleton3 (0 : Fin 8) = 1 := by decide

/-- A one-step constant hash collision keeps the honest ordered pair first. -/
theorem one_step_collision_oriented :
    PerfectMerkleTree.findCollision (fun _ : ℕ => (0 : ℕ))
      (fun _ _ _ _ => (0 : ℕ)) 0 1 [0] =
        some (1, (0, 0), (1, 0)) := by decide

/-- The height-zero full interval has no filler frontier. -/
theorem full_zero_not_isInactiveFrontier (subtreeHeight subtreeIndex : ℕ) :
    ¬ Subtree.IsInactiveFrontier (Interval.full 0) subtreeHeight subtreeIndex :=
  Subtree.full_not_isInactiveFrontier 0 subtreeHeight subtreeIndex

private def interval24 : Interval 3 := ⟨2, 4, by decide⟩

example : Epoch.IsActive interval24 2 ∧ Epoch.IsActive interval24 4 := by decide
example : ¬ Epoch.IsActive interval24 1 ∧ ¬ Epoch.IsActive interval24 5 := by decide
example : Subtree.IsInactiveFrontier interval24 1 0 := by decide
example : Subtree.IsInactiveFrontier interval24 0 5 := by decide
example : Subtree.IsInactiveFrontier interval24 1 3 := by decide
example : ¬ Subtree.IsInactiveFrontier interval24 0 0 := by decide
example : ¬ Subtree.IsInactiveFrontier interval24 2 0 := by decide
example : frontierLevel interval24 (0 : Fin 8) = 1 := by decide
example : frontierLevel interval24 (5 : Fin 8) = 0 := by decide
example : frontierLevel interval24 (6 : Fin 8) = 1 := by decide

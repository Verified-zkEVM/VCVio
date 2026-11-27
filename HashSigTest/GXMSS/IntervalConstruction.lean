/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
public import HashSigTest.GXMSS.Chain

/-!
# Interval construction and pruned-tree observations

The height-three interval [2,4] has inactive frontier roots (1,0), (0,5), (1,3). Tagged digests
pin retained child order and active leaf-first paths independently of the tree implementation.
-/

public section

namespace GXMSS.IntervalConstructionProbe

open GXMSS.IntervalMerkle

/-- The two active boundary epochs are two and four. -/
@[expose] def active : Interval 3 := ⟨2, 4, by decide⟩

/-- Distinct endpoint tags keep active leaves observable. -/
@[expose] def endpoints : Fin 8 → Fin 1 → List ℕ := fun ep _ => [90 + ep.val]

/-- Each stored frontier digest records its own level and index. -/
@[expose] def fillers : Fillers active (List ℕ) :=
  fun node => [9000 + 100 * node.val.1.val + node.val.2.val]

/-- The expected root retains the left/right order and the three maximal inactive roots. -/
@[expose] def expectedRoot : List ℕ :=
  [9100, 92, 2000, 0, 2, 93, 2000, 0, 3, 3000, 1, 1, 3000, 2, 0,
    94, 2000, 0, 4, 9005, 3000, 1, 2, 9103, 3000, 2, 1, 3000, 3, 0]

/-- The mixed engine root has the independently enumerated retained subtree values. -/
theorem mixed_root :
    root (ChainProbe.traceInstance 3 3) active () endpoints fillers = expectedRoot := by decide

/-- Direct pruning gives exactly the same concrete root. -/
theorem pruned_root :
    prunedRoot (ChainProbe.traceInstance 3 3) active () endpoints fillers 3 0 = expectedRoot := by
  decide

/-- At active epoch two, the lower sibling is active and the next sibling is a filler. -/
theorem path_two :
    authPath (ChainProbe.traceInstance 3 3) active () endpoints fillers 2 =
      ![[93, 2000, 0, 3], [9100],
        [94, 2000, 0, 4, 9005, 3000, 1, 2, 9103, 3000, 2, 1]] := by decide

/-- At active epoch four, both lower sibling subtrees terminate at stored fillers. -/
theorem path_four :
    authPath (ChainProbe.traceInstance 3 3) active () endpoints fillers 4 =
      ![[9005], [9103],
        [9100, 92, 2000, 0, 2, 93, 2000, 0, 3, 3000, 1, 1, 3000, 2, 0]] := by decide

/-- The active path reconstructs the concrete mixed root under ordinary verification hashing. -/
theorem active_recovery :
    (ChainProbe.traceInstance 3 3).recoverRoot () 2 (endpoints 2)
      (authPath (ChainProbe.traceInstance 3 3) active () endpoints fillers 2) = expectedRoot := by
  rw [recoverRoot_authPath_isActive _ active _ endpoints fillers 2 (by decide)]
  exact mixed_root

/-- A full-range sampler has no filler query, even for an arbitrary finite hash alphabet. -/
theorem full_range_filler_program {H : Type} [SampleableType H] (h : ℕ) :
    sampleFillers (Interval.full h) H = pure (fun x => isEmptyElim x) := sampleFillers_full h H

/-- Full-range key generation keeps the entire actual seed/start computation after projection. -/
theorem full_range_keygen {PP T X H : Type} {h w v : ℕ} [SampleableType H]
    (hash : HashInstance PP T X H h w v) :
    (fun ks => (ks.1, GXMSS.Interval.projectSecret ks.2)) <$>
      GXMSS.Interval.keygen hash (Interval.full h) = GXMSS.keygen hash :=
  GXMSS.Interval.keygen_full_project hash

end GXMSS.IntervalConstructionProbe

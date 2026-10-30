/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.TouchRead

/-!
# Touch-then-read in the eager game

In the eager game of a canonical graph a touch is a read whose value is discarded, also where
there is no cell: both sides are then `pure ()`. A touch-then-read of cell `s + 1` therefore
unfolds into the touch-then-read of cell `s` and a read of cell `s + 1`, whatever cell `s` is, and
when cell `s + 1` exists the read draws it. The examples unfold a chain whose first cell is
missing, which the draw form allows since it constrains only cell `s + 1`.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.TouchReadEager

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : CanonicalGraph pub X K R)
  [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

/-- Where there is no cell, a touch and a discarded read are both `pure ()`. -/
example : simulateQ G.eagerImpl (touchCell (none : Option (X ⊕ K))) =
    (fun _ ↦ ()) <$> simulateQ G.eagerImpl (readCell (none : Option (X ⊕ K))) :=
  G.simulateQ_eagerImpl_touchCell none

example : simulateQ G.eagerImpl (touchCell (none : Option (X ⊕ K))) = pure () := by
  simp [touchCell]

/-- Two unfoldings of a touch-then-read of cell `2`. -/
example (cell : ℕ → Option (X ⊕ K)) :
    simulateQ G.eagerImpl (touchRead cell 2) =
      simulateQ G.eagerImpl (touchRead cell 0) >>= fun _ ↦
        simulateQ G.eagerImpl (readCell (cell 1)) >>= fun _ ↦
          simulateQ G.eagerImpl (readCell (cell 2)) := by
  rw [G.simulateQ_eagerImpl_touchRead_succ, G.simulateQ_eagerImpl_touchRead_succ, bind_assoc]

/-- A chain whose cell `0` is missing: the touch-then-read of cell `1` is the touch-then-read of
the missing cell `0`, followed by a draw of cell `1`. -/
example (c : X ⊕ K) (st : RelabelState pub X K R) :
    (simulateQ G.eagerImpl (touchRead (fun s ↦ if s = 0 then none else some c) 1)).run st =
      (simulateQ G.eagerImpl (touchRead (fun s ↦ if s = 0 then none else some c) 0)).run st >>=
        fun z ↦ (RelabelState.drawCell c).run z.2 :=
  G.eagerImpl_touchRead_succ_run _ 0 (by simp) st

end VCVioTest.TouchReadEager

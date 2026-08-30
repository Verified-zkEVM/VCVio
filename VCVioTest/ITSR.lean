/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR

/-! # ITSR source-game canaries -/

public section

open OracleComp KeyedHash

namespace ITSRTest

def parityProblem : ITSRProblem Bool Nat Bool Nat where
  khf := { keygen := $ᵗ Bool, hash := fun k x => k == decide (x % 2 = 0) }
  indices := fun y => if y then [0] else [1]

def constantIndexProblem : ITSRProblem Bool Nat Unit Nat where
  khf := { keygen := $ᵗ Bool, hash := fun _ _ => () }
  indices := fun _ => [0]

/-- The candidate pair must be fresh even when its semantic index is covered. -/
example : ¬ parityProblem.Wins [(true, 2)] (true, 2) := by decide

/-- Pair freshness permits reusing a target key at a fresh input. -/
example : constantIndexProblem.Wins [(true, 1)] (true, 2) := by decide

/-- Pair freshness also permits reusing a target input under a fresh key. -/
example : constantIndexProblem.Wins [(true, 1)] (false, 1) := by decide

/-- A fresh pair loses when its selected index is not covered by the transcript. -/
example : ¬ parityProblem.Wins [(true, 2)] (true, 3) := by decide

/-- The target oracle's state theorem pins append-in-issue-order semantics. -/
example (x : Nat) (targets : ITSRTranscript Bool Nat) :
    (ITSRTargetOracle constantIndexProblem x).run targets =
      constantIndexProblem.khf.keygen >>= fun k => pure (k, targets ++ [(k, x)]) :=
  ITSRTargetOracle_run constantIndexProblem x targets

end ITSRTest

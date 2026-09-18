/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.ReplayCheckpoint

/-! # Ordinary execution and replay observation through a public checkpoint example -/

public section

open OracleComp Examples.ReplayCheckpoint

example :
    run ($ᵗ Bool) pure = run (pure ()) (fun _ => $ᵗ Bool) ∧
    𝒟[agreement ($ᵗ Bool) pure] ≠ 𝒟[agreement (pure ()) (fun _ => $ᵗ Bool)] :=
  ⟨ordinary_execution_equal, replay_laws_differ⟩

example : 𝒟[agreement ($ᵗ Bool) pure] {true} -
    𝒟[agreement (pure ()) (fun _ => $ᵗ Bool)] {true} = (1 : ENNReal) / 2 := by
  rw [shared_agreement, fresh_agreement]
  norm_num

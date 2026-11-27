/-
Copyright (c) 2026 leanEthereum and VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: leanEthereum, VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.CyclicMass

/-!
# Cached selections across the two starts of a Boolean cycle

One position already holds an accepted bit. The other has a fresh answer.
The bound sums the probabilities of selecting the occupied position over both starts.
-/

public section

open OracleComp OracleSpec AcceptedScan
open scoped ENNReal

namespace VCVioTest.RandomOracleAcceptedScanMass

/-- Either start can reach the stored accepted bit, including a start at the fresh position. -/
theorem two_starts :
    let c : QueryCache (Bool →ₒ Bool) := QueryCache.ofFn fun b => if b then some true else none
    let next := Equiv.swap false true
    let p := Pr{let b ← $ᵗ Bool}[b ∈ ({true} : Finset Bool)]
    p * ∑ r, Pr{let z ← (simulateQ randomOracle (scan {true} id (orbit next 2 r))).run c}[
      z.1 = some true] ≤ 1 := by
  intro c next p
  have warm : ({true} : Finset Bool) ⊆ occupied id c := by
    intro r hr
    simpa [occupied, c, QueryCache.ofFn_apply] using hr
  have distinct (r : Bool) : ((orbit next 2 r).map id).Nodup := by cases r <;> decide
  have bound := cyclic_selection_mass_le ({true} : Finset Bool) id c {true} warm next 2 distinct
  have occupied_eq : occupied id c = {true} := by
    ext r
    cases r <;> simp [occupied, c, QueryCache.ofFn_apply]
  simpa only [occupied_eq, Finset.card_singleton, Nat.cast_one, mul_one,
    add_tsub_cancel_of_le (prEvent_le_one _), Finset.mem_singleton, exists_eq_left] using bound

end VCVioTest.RandomOracleAcceptedScanMass

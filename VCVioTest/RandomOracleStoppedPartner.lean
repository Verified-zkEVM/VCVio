/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.StoppedPartner

/-!
# A new partner at the final fresh trial

The earlier address holds true.
The cold address rejects false.
It accepts true and acquires its first partner.
-/

public section

open OracleSpec OracleComp AcceptedScan randomOracle.Partners
open scoped ENNReal

namespace VCVioTest.RandomOracleStoppedPartner

/-- The fresh success pairs immediately with the earlier accepted bit. -/
theorem first_fresh_pair :
    let c : QueryCache (Bool →ₒ Bool) := QueryCache.ofFn fun b => if b then none else some true
    let decode : Bool → Option Unit := fun b => if b then some () else none
    Pr{let z ← (simulateQ randomOracle (scanWithAnswer {true} id [true])).run c}[
      ∃ w, z.1 = some (true, w) ∧ Partner (fun _ => ()) decode z.2 true] = 2⁻¹ := by
  classical
  intro c decode
  have cold : c true = none := rfl
  have old : c false = some true := rfl
  have hit : Partner (fun _ => ()) decode (c.cacheQuery true true) true :=
    ⟨true, QueryCache.cacheQuery_self .., (), rfl, false, by decide, rfl, true,
      (QueryCache.cacheQuery_of_ne c true (by decide : false ≠ true)).trans old, rfl⟩
  have event : Pr{let z ← (simulateQ randomOracle (scanWithAnswer {true} id [true])).run c}[
      ∃ w, z.1 = some (true, w) ∧ Partner (fun _ => ()) decode z.2 true] =
      Pr{let b ← $ᵗ Bool}[b = true] := by
    simp only [scanWithAnswer, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, id_eq,
      QueryImpl.withCaching_run_none _ cold, bind_map_left]
    rw [prEvent_bind_eq_sum_fintype, Fintype.sum_bool]
    have card : ({b ∈ ({true, false} : Finset Bool) | b = true}).card = 1 := by decide
    simp [hit, uniformSampleImpl, SampleableType.prEvent_uniformSample_eq_singleton, card]
  rw [event, SampleableType.prEvent_uniformSample_eq_singleton]
  norm_num

end VCVioTest.RandomOracleStoppedPartner

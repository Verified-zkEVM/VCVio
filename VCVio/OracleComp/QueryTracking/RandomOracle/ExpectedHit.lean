/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedPotential
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Expected charge of marked replies

Marking happens before the query and may depend on the incoming state.
Each marked reply can set the persistent flag.
The bound uses the expected final counter of the original run. The counter increases by one
on each marked call and can start above zero.
-/

public section

namespace OracleComp
open OracleSpec
open scoped ENNReal

namespace MarkedHit

variable {ι σ α : Type} {spec : OracleSpec ι}

/-- A flag can first become true only on a marked call. -/
@[expose] def update (mark : spec.Domain → σ → Bool)
    (hit : (t : spec.Domain) → σ → spec.Range t → Bool)
    (t : spec.Domain) (s : σ) (a : spec.Range t) (_ : σ) (seen : Bool) : Bool :=
  seen || (mark t s && hit t s a)

/-- Starting with the flag clear, the probability it is set by the end of the run is at most
`ε` times the expected final counter. Each marked call has conditional hit probability at
most `ε`. -/
theorem prEvent_le_expected (so : QueryImpl spec (StateT σ ProbComp)) (paid : σ → Nat)
    (mark : spec.Domain → σ → Bool) (hit : (t : spec.Domain) → σ → spec.Range t → Bool)
    (ε : ℝ≥0∞)
    (price : ∀ t s z, z ∈ support ((so t).run s) →
      paid z.2 = paid s + (if mark t s then 1 else 0))
    (rate : ∀ t s, mark t s = true → Pr{let z ← (so t).run s}[hit t s z.1] ≤ ε)
    (body : OracleComp spec α) (s : σ) :
    Pr{let z ← (simulateQ (so.extendState (update mark hit)) body).run (s, false)}[
      z.2.2 = true] ≤ (∑' z, Pr{let u ← (simulateQ so body).run s}[u = z] * paid z.2) * ε := by
  classical
  let record := so.extendState (update mark hit)
  let val (u : σ × Bool) : ℝ≥0∞ := paid u.1 * ε
  have bill (t : spec.Domain) (u : σ × Bool) (z : spec.Range t × σ × Bool)
      (hz : z ∈ support ((record t).run u)) :
      paid z.2.1 = paid u.1 + if mark t u.1 then 1 else 0 :=
    price t u.1 (z.1, z.2.1) ((QueryImpl.mem_support_extendState_run_iff _ _ _ _ _).1 hz).1
  have credit := expected_credit_of_increments record (fun u => u.2 = true) val
    (fun t u z hz => by
      have h := bill t u z hz
      unfold val
      gcongr
      omega) (fun t u clean => by
        have cleared : u.2 = false := Bool.eq_false_iff.mpr clean
        cases active : mark t u.1 with
        | false =>
          refine ⟨0, ?_, ?_⟩
          · simp [record, update, QueryImpl.extendState_apply, prEvent_norm, cleared, active]
          · intro z hz
            simp [val, bill t u z hz, active]
        | true =>
          refine ⟨ε, ?_, ?_⟩
          · simpa [record, update, QueryImpl.extendState_apply, prEvent_norm, cleared, active]
              using rate t u.1 active
          · intro z hz
            simp only [val, bill t u z hz, active, ite_true, Nat.cast_add, Nat.cast_one,
              add_mul, one_mul, add_comm, le_refl]) body (s, false)
  have one : (1 : ℝ≥0∞) ≤ val (s, false) + (if (false : Bool) = true then 0 else 1) := by simp
  have risk := prEvent_le_expected_of_credit ((simulateQ record body).run (s, false))
    (fun z => z.2.2 = true) (fun z => val z.2) (one.trans credit)
  have eq := extendState_run_proj_eq so (update mark hit) body s false
  rw [← eq, tsum_prEvent_map_mul, ← ENNReal.tsum_mul_right]
  simpa [val, record, mul_assoc] using risk

end MarkedHit

end OracleComp

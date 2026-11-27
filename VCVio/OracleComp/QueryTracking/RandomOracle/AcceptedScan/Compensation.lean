/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.PartnerDrift

/-!
# A compensating potential for partnered selections

The number of valid physical inputs and the occupied selection mass pay for new partnerships.
One count is shared across messages and scan schedules at that key.
-/

public section

open OracleSpec OracleComp OracleComp.AcceptedScan
open scoped ENNReal

namespace randomOracle.Partners

variable {A X Y K D : Type} [Fintype X] [DecidableEq A] [DecidableEq Y] [SampleableType Y]

/-- The gain in partnered selection is paid by the gain of valid count times occupancy.
The probed row may belong to a different message's scan at this same key. -/
theorem compensate (key : A → K) (decode : Y → Option D) (accepted : Finset Y)
    (encode : X → A) (inj : Function.Injective encode) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : (A →ₒ Y).QueryCache) (a : A) (cold : c a = none)
    (ref : Y) (ok : ref ∈ accepted) (ε V : ℝ≥0∞) (prior : priorPairRate key decode c a ≤ ε * V)
    (valid : ∀ w d, decode w = some d → w ∈ accepted)
    (rate : ∀ d, Pr{let w ← $ᵗ Y}[decode w = some d] ≤ ε) :
    let p := Pr{let v ← $ᵗ Y}[v ∈ accepted]
    let H := cachedMass accepted encode xs
    let Φ := partneredMass key decode accepted encode xs
    let update := fun v => c.cacheQuery a v
    p * freshMean (fun v => Φ (update v)) + ε * (V * H c) ≤
      p * Φ c + ε * freshMean (fun v => (if v ∈ accepted then V + 1 else V) * H (update v)) := by
  classical
  intro p H Φ update
  obtain ⟨R, meanH, drift⟩ : ∃ R : ℝ≥0∞, freshMean (fun v => H (update v)) = H c + p * R ∧
      freshMean (fun v => Φ (update v)) ≤ Φ c + ε * (H c + V * R) := by
    by_cases covered : ∃ t, encode t = a
    · obtain ⟨t, rfl⟩ := covered
      exact ⟨_, mean_cachedMass accepted encode inj xs distinct c t cold ref ok,
        partnered_mass_drift key decode accepted encode inj xs distinct c t cold ref ok ε V
          prior valid rate⟩
    · have outside := fun t h => covered ⟨t, h⟩
      refine ⟨0, ?_, ?_⟩
      · simpa only [mul_zero, add_zero] using
          mean_cachedMass_outside accepted encode xs c a cold outside
      · simpa only [mul_zero, add_zero] using
          partnered_mass_drift_outside key decode accepted encode xs distinct c a cold outside ε
            valid rate
  have growth := weighted_mass_drift accepted encode xs distinct c a V R meanH
  calc
    _ ≤ p * (Φ c + ε * (H c + V * R)) + ε * (V * H c) := by gcongr
    _ = p * Φ c + ε * (V * H c + p * (H c + V * R)) := by ring
    _ ≤ _ := by gcongr

omit [DecidableEq Y] in
private theorem mean_sum {ι : Type} (family : Finset ι) (f : ι → Y → ℝ≥0∞) :
    freshMean (fun v => ∑ i ∈ family, f i v) = ∑ i ∈ family, freshMean (f i) := by
  simp only [freshMean, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)

/-- All schedules at one key, including different messages and cyclic starts, use one count.
The finite family need only include the schedules whose contributions the caller observes. -/
theorem compensate_sum {ι : Type} (family : Finset ι) (key : A → K) (decode : Y → Option D)
    (accepted : Finset Y) (encode : ι → X → A) (inj : ∀ i ∈ family, Function.Injective (encode i))
    (xs : ι → List X) (distinct : ∀ i ∈ family, ((xs i).map (encode i)).Nodup)
    (c : (A →ₒ Y).QueryCache) (a : A) (cold : c a = none) (ref : Y) (ok : ref ∈ accepted)
    (ε V : ℝ≥0∞) (prior : priorPairRate key decode c a ≤ ε * V)
    (valid : ∀ w d, decode w = some d → w ∈ accepted)
    (rate : ∀ d, Pr{let w ← $ᵗ Y}[decode w = some d] ≤ ε) :
    let p := Pr{let v ← $ᵗ Y}[v ∈ accepted]
    let H (st : (A →ₒ Y).QueryCache) := ∑ i ∈ family, cachedMass accepted (encode i) (xs i) st
    let Φ (st : (A →ₒ Y).QueryCache) :=
      ∑ i ∈ family, partneredMass key decode accepted (encode i) (xs i) st
    let update := fun v => c.cacheQuery a v
    p * freshMean (fun v => Φ (update v)) + ε * (V * H c) ≤
      p * Φ c + ε * freshMean (fun v => (if v ∈ accepted then V + 1 else V) * H (update v)) := by
  dsimp only
  simp_rw [Finset.mul_sum, mean_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i hi =>
    compensate key decode accepted (encode i) (inj i hi) (xs i) (distinct i hi) c a cold
      ref ok ε V prior valid rate

end randomOracle.Partners

/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Occupied

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Probe
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Selection

/-!
# Paying for partner matches created by one fresh query

Cached accepted selections can grow only when the probe fills the selected position.
Weighting their mass by the number of accepted rows also pays for a new partner of an older row.
-/

public section

open OracleSpec OracleComp OracleComp.AcceptedScan
open scoped ENNReal

namespace randomOracle.Partners

variable {A X Y K D : Type} [Fintype X] [DecidableEq A] [DecidableEq Y] [SampleableType Y]

open Classical in
/-- Positions of the scan already occupied by accepted words before the probe. -/
@[expose] noncomputable def validRows (accepted : Finset Y) (encode : X → A)
    (c : (A →ₒ Y).QueryCache) : Finset X :=
  Finset.univ.filter fun r => ∃ w ∈ accepted, c (encode r) = some w

/-- Average over the original full word returned by the fresh query. -/
@[expose] noncomputable def freshMean (f : Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' w, Pr{let y ← $ᵗ Y}[y = w] * f w

/-- Probability that the finder selects an initially accepted, occupied row. -/
@[expose] noncomputable def cachedMass (accepted : Finset Y) (encode : X → A) (xs : List X)
    (c : (A →ₒ Y).QueryCache) : ℝ≥0∞ :=
  Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run c}[
    ∃ r ∈ validRows accepted encode c, z.1 = some r]

/-- Probability of selecting the probed target after fixing it to an accepted answer. -/
@[expose] noncomputable def forcedMass (accepted : Finset Y) (encode : X → A) (xs : List X)
    (c : (A →ₒ Y).QueryCache) (target : X) (ref : Y) : ℝ≥0∞ :=
  Pr{let z ←
    (simulateQ randomOracle (scan accepted encode xs)).run (c.cacheQuery (encode target) ref)}[
    z.1 = some target]

omit [SampleableType Y] in
private theorem valid_before (accepted : Finset Y) (encode : X → A) (c : (A →ₒ Y).QueryCache)
    (a : A) (cold : c a = none) (v : Y) :
    validRows accepted encode c ⊆ validRows accepted encode (c.cacheQuery a v) := by
  classical
  intro r hr
  simp only [validRows, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  obtain ⟨w, ok, has⟩ := hr
  refine ⟨w, ok, ?_⟩
  have other : encode r ≠ a := fun h => by rw [h, cold] at has; cases has
  exact (QueryCache.cacheQuery_of_ne c v other).trans has

open Classical in
omit [SampleableType Y] in
private theorem valid_probe (accepted : Finset Y) (encode : X → A) (inj : Function.Injective encode)
    (c : (A →ₒ Y).QueryCache) (target : X) (v : Y) (cold : c (encode target) = none) :
    validRows accepted encode (c.cacheQuery (encode target) v) =
      if v ∈ accepted then insert target (validRows accepted encode c) else
        validRows accepted encode c := by
  classical
  ext r
  by_cases same : r = target
  · subst r
    by_cases ok : v ∈ accepted <;>
      simp [ok, validRows, QueryCache.cacheQuery_self, cold]
  · have other : encode r ≠ encode target := fun h => same (inj h)
    by_cases ok : v ∈ accepted <;>
      simp [ok, same, validRows, QueryCache.cacheQuery_of_ne c v other]

private theorem cachedMass_eq_answer (accepted : Finset Y) (encode : X → A) (xs : List X)
    (c : (A →ₒ Y).QueryCache) : cachedMass accepted encode xs c =
      Pr{let z ← (simulateQ randomOracle (scanWithAnswer accepted encode xs)).run c}[
        cachedSelection accepted encode c z.1] := by
  classical
  simp only [cachedMass, scan, simulateQ_map, StateT.run_map, prEvent_norm]
  apply prEvent_congr
  rintro ⟨_ | ⟨x, v⟩, _⟩
  · simp [cachedSelection]
  · simp [validRows, cachedSelection]

/-- Filling the probe by an accepted value cannot lower the cached selection mass. -/
theorem cachedMass_le_after_accept (accepted : Finset Y) (encode : X → A) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : (A →ₒ Y).QueryCache) (a : A) (v : Y)
    (ok : v ∈ accepted) :
    cachedMass accepted encode xs c ≤ cachedMass accepted encode xs (c.cacheQuery a v) := by
  simpa only [cachedMass_eq_answer] using
    cachedSelection_le_of_accepted accepted encode xs distinct c a v ok

/-- A fresh reply adds its acceptance probability times the chance of reaching its position. -/
theorem mean_cachedMass (accepted : Finset Y) (encode : X → A) (inj : Function.Injective encode)
    (xs : List X) (distinct : (xs.map encode).Nodup) (c : (A →ₒ Y).QueryCache)
    (target : X) (cold : c (encode target) = none) (ref : Y) (ok : ref ∈ accepted) :
    freshMean (fun v => cachedMass accepted encode xs (c.cacheQuery (encode target) v)) =
      cachedMass accepted encode xs c +
        Pr{let y ← $ᵗ Y}[y ∈ accepted] * forcedMass accepted encode xs c target ref := by
  classical
  let input : A := encode target
  let before (o : Option X) := ∃ r ∈ validRows accepted encode c, o = some r
  let after (v : Y) (o : Option X) := ∃ r ∈ validRows accepted encode (c.cacheQuery input v),
    o = some r
  have gain := average_growing_event (scan accepted encode xs) c input cold before after
    (fun v _ ⟨r, h, eq⟩ => ⟨r, valid_before accepted encode c input cold v h, eq⟩)
  unfold freshMean cachedMass
  rw [gain]
  congr 1
  rw [prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro v
  have originally : target ∉ validRows accepted encode c := by simp [validRows, cold]
  by_cases yes : v ∈ accepted
  · simp only [yes, ite_true]
    unfold forcedMass
    rw [← select_eq_of_probe_accepted accepted encode xs distinct c target input v ref yes ok]
    congr 1
    apply prEvent_congr
    rintro ⟨result, _⟩
    simp only [before, after, input, valid_probe accepted encode inj c target v cold, yes, ite_true,
      Finset.mem_insert]
    constructor
    · rintro ⟨⟨r, same | hr, pick⟩, old⟩
      · exact same ▸ pick
      · exact (old ⟨r, hr, pick⟩).elim
    · rintro rfl
      refine ⟨⟨target, Or.inl rfl, rfl⟩, ?_⟩
      rintro ⟨r, hr, eq⟩
      exact originally ((Option.some.inj eq).symm ▸ hr)
  · simp only [yes, ite_false, zero_mul]
    apply mul_eq_zero_of_right
    apply prEvent_eq_zero_of_forall_mem_support
    rintro z _ ⟨⟨r, h, eq⟩, old⟩
    rw [show validRows accepted encode (c.cacheQuery input v) = validRows accepted encode c by
      rw [valid_probe accepted encode inj c target v cold, ite_eq_right yes]] at h
    exact old ⟨r, h, eq⟩

private theorem mean_indicator (accepted : Finset Y) (b : ℝ≥0∞) :
    freshMean (fun v => if v ∈ accepted then b else 0) =
      Pr{let v ← $ᵗ Y}[v ∈ accepted] * b := by
  rw [freshMean, prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro v
  by_cases ok : v ∈ accepted <;> simp [ok]

omit [DecidableEq Y] in
/-- An average over full replies distributes over addition of nonnegative masses. -/
theorem freshMean_add (f g : Y → ℝ≥0∞) :
    freshMean (fun v => f v + g v) = freshMean f + freshMean g := by
  simp only [freshMean, mul_add, tsum_add]

omit [DecidableEq Y] in
private theorem mean_mul (b : ℝ≥0∞) (f : Y → ℝ≥0∞) :
    freshMean (fun v => b * f v) = b * freshMean f := by
  simp only [freshMean, ← ENNReal.tsum_mul_left, mul_left_comm]

/-- The full count at the probed key grows by one exactly when the fresh answer is accepted.
This count may include rows in other scans or messages at that key. -/
theorem weighted_mass_drift (accepted : Finset Y) (encode : X → A) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : (A →ₒ Y).QueryCache) (a : A)
    (V R : ℝ≥0∞) (meanH : freshMean (fun v => cachedMass accepted encode xs (c.cacheQuery a v)) =
      cachedMass accepted encode xs c + Pr{let v ← $ᵗ Y}[v ∈ accepted] * R) :
    let H := cachedMass accepted encode xs
    let p := Pr{let v ← $ᵗ Y}[v ∈ accepted]
    V * H c + p * (H c + V * R) ≤
      freshMean (fun v => (if v ∈ accepted then V + 1 else V) * H (c.cacheQuery a v)) := by
  classical
  intro H p
  let update := fun v => c.cacheQuery a v
  have one v : V * H (update v) + (if v ∈ accepted then H c else 0) ≤
      (if v ∈ accepted then V + 1 else V) * H (update v) := by
    by_cases yes : v ∈ accepted
    · simp only [yes, ite_true, add_mul, one_mul]
      exact add_le_add_right (cachedMass_le_after_accept accepted encode xs distinct c _ v yes) _
    · simp [yes]
  calc
    _ = V * (H c + p * R) + p * H c := by ring
    _ = freshMean (fun v => V * H (update v) + (if v ∈ accepted then H c else 0)) := by
      rw [freshMean_add, mean_mul, mean_indicator, meanH]
    _ ≤ _ := tsum_le_tsum fun v => mul_le_mul_right (one v) _

/-- Probing outside a scan's address family leaves mean cached selection mass unchanged. -/
theorem mean_cachedMass_outside (accepted : Finset Y) (encode : X → A) (xs : List X)
    (c : (A →ₒ Y).QueryCache) (a : A) (cold : c a = none) (outside : ∀ x, encode x ≠ a) :
    freshMean (fun v => cachedMass accepted encode xs (c.cacheQuery a v)) =
      cachedMass accepted encode xs c := by
  classical
  have rows v : validRows accepted encode (c.cacheQuery a v) = validRows accepted encode c := by
    ext r
    simp only [validRows, Finset.mem_filter, QueryCache.cacheQuery_of_ne c v (outside r)]
  unfold freshMean cachedMass
  simp_rw [rows]
  exact (prEvent_eq_average_cacheQuery (scan accepted encode xs) c a cold
    (fun z => ∃ r ∈ validRows accepted encode c, z = some r)).symm

end randomOracle.Partners

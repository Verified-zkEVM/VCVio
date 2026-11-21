/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.NewPartner
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.OccupiedMass
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.PartnerSet

/-!
# Partnerships created by a fresh physical query

An earlier selected row and the newly queried address can each acquire a partner.
-/

@[expose] public section

open OracleSpec OracleComp OracleComp.AcceptedScan
open scoped ENNReal

namespace randomOracle.Partners

variable {A X Y K D : Type} [Fintype X] [DecidableEq A] [DecidableEq Y] [SampleableType Y]

/-- The selected finder position already has a digest partner in this initial cache. -/
noncomputable def partneredMass (key : A → K) (decode : Y → Option D) (accepted : Finset Y)
    (encode : X → A) (xs : List X) (c : (A →ₒ Y).QueryCache) : ℝ≥0∞ :=
  Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run c}[
    ∃ r, z.1 = some r ∧ Partner key decode c (encode r)]

/-- Probability that the probe word decodes to a digest already present at the same key. -/
noncomputable def priorPairRate (key : A → K) (decode : Y → Option D)
    (c : (A →ₒ Y).QueryCache) (a : A) : ℝ≥0∞ :=
  Pr{let y ← $ᵗ Y}[∃ d, decode y = some d ∧ ∃ b ≠ a, key b = key a ∧
    ∃ w, c b = some w ∧ decode w = some d]

/-- A word decodes to a digest already present at the given key, from any message. -/
def StoredDigest (key : A → K) (decode : Y → Option D) (c : (A →ₒ Y).QueryCache)
    (k : K) (w : Y) : Prop :=
  ∃ d, decode w = some d ∧ ∃ b, key b = k ∧ ∃ u, c b = some u ∧ decode u = some d

omit [DecidableEq A] [DecidableEq Y] in
/-- An occupied row of the probe's key can account for at most one digest. -/
theorem storedDigest_rate_le (key : A → K) (decode : Y → Option D) (c : (A →ₒ Y).QueryCache)
    (k : K) (rows : Finset A) (ε : ℝ≥0∞)
    (covered : ∀ b, key b = k → ∀ w, c b = some w → ∀ d, decode w = some d → b ∈ rows)
    (rate : ∀ d, Pr{let w ← $ᵗ Y}[decode w = some d] ≤ ε) :
    Pr{let w ← $ᵗ Y}[StoredDigest key decode c k w] ≤ ε * rows.card := by
  classical
  let hit (r : A) (v : Y) := ∃ w d, c r = some w ∧ decode w = some d ∧ decode v = some d
  have each (r : A) : Pr{let v ← $ᵗ Y}[hit r v] ≤ ε := by
    by_cases old : ∃ w d, c r = some w ∧ decode w = some d
    · obtain ⟨w, d, hw, hd⟩ := old
      refine (prEvent_mono _ _ _ fun v h => ?_).trans (rate d)
      obtain ⟨u, e, hu, he, hv⟩ := h
      have eq := Option.some.inj (hu.symm.trans hw)
      exact hv.trans ((eq ▸ he).symm.trans hd)
    · have none : Pr{let v ← $ᵗ Y}[hit r v] = 0 := by
        apply prEvent_eq_zero_of_forall_mem_support
        rintro _ _ ⟨w, d, hw, hd, _⟩
        exact old ⟨w, d, hw, hd⟩
      simp [none]
  calc
    _ ≤ Pr{let v ← $ᵗ Y}[∃ r ∈ rows, hit r v] := by
      apply prEvent_mono
      rintro v ⟨d, hv, b, hk, w, hw, hd⟩
      exact ⟨b, covered b hk w hw d hd, w, d, hw, hd, hv⟩
    _ ≤ ∑ r ∈ rows, Pr{let v ← $ᵗ Y}[hit r v] := prEvent_exists_finset_le rows _ hit
    _ ≤ ∑ _r ∈ rows, ε := Finset.sum_le_sum fun r _ => each r
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

omit [DecidableEq A] [DecidableEq Y] in
/-- An occupied row of the probe's key can account for at most one digest. -/
theorem priorPairRate_le (key : A → K) (decode : Y → Option D) (c : (A →ₒ Y).QueryCache)
    (a : A) (rows : Finset A) (ε : ℝ≥0∞)
    (covered : ∀ b, key b = key a → ∀ w, c b = some w → ∀ d, decode w = some d → b ∈ rows)
    (rate : ∀ d, Pr{let w ← $ᵗ Y}[decode w = some d] ≤ ε) :
    priorPairRate key decode c a ≤ ε * rows.card := by
  refine (prEvent_mono _ _ _ ?_).trans (storedDigest_rate_le key decode c
    (key a) rows ε covered rate)
  rintro v ⟨d, hd, b, _, hk, w, hw, wd⟩
  exact ⟨d, hd, b, hk, w, hw, wd⟩

private theorem paired_gain (key : A → K) (decode : Y → Option D) (accepted : Finset Y)
    (encode : X → A) (xs : List X) (distinct : (xs.map encode).Nodup)
    (c : (A →ₒ Y).QueryCache) (a : A) (cold : c a = none) (ε : ℝ≥0∞)
    (valid : ∀ w d, decode w = some d → w ∈ accepted)
    (rate : ∀ d, Pr{let w ← $ᵗ Y}[decode w = some d] ≤ ε) :
    let run (v : Y) := (simulateQ randomOracle (scan accepted encode xs)).run (c.cacheQuery a v)
    let new (v : Y) := Pr{let z ← run v}[
      (∃ r, z.1 = some r ∧ encode r = a) ∧ Partner key decode (c.cacheQuery a v) a]
    freshMean (fun v => partneredMass key decode accepted encode xs (c.cacheQuery a v)) ≤
      partneredMass key decode accepted encode xs c + (ε * cachedMass accepted encode xs c +
        freshMean new) := by
  classical
  intro scanned new
  let update := fun v => c.cacheQuery a v
  let s := (validRows accepted encode c).filter fun r =>
    ¬Partner key decode c (encode r) ∧ ∃ w d, c (encode r) = some w ∧ decode w = some d
  let run (st : (A →ₒ Y).QueryCache) := (simulateQ randomOracle (scan accepted encode xs)).run st
  let hit (st : (A →ₒ Y).QueryCache) (o : Option X) :=
    ∃ r, o = some r ∧ Partner key decode st (encode r)
  let old (v : Y) := Pr{let z ← run (update v)}[
    ∃ r ∈ s, z.1 = some r ∧ Partner key decode (update v) (encode r)]
  have gain := average_growing_event (scan accepted encode xs) c a cold (hit c)
    (fun v => hit (update v)) (fun v _ ⟨r, eq, h⟩ =>
      ⟨r, eq, mono key decode (QueryCache.le_cacheQuery c cold) h⟩)
  have split v : Pr{let z ← run (update v)}[hit (update v) z.1 ∧ ¬hit c z.1] ≤ old v + new v := by
    refine (prEvent_mono _ _ _ ?_).trans (prEvent_or_le _ _ _)
    rintro z ⟨⟨r, pick, pair⟩, was⟩
    by_cases same : encode r = a
    · exact Or.inr ⟨⟨r, pick, same⟩, (congrArg (Partner key decode (update v)) same) ▸ pair⟩
    · have noPair : ¬Partner key decode c (encode r) := fun h => was ⟨r, pick, h⟩
      obtain ⟨w, d, hw, hd, _, _⟩ := newly_matches key decode same v noPair pair
      have mem : r ∈ validRows accepted encode c := by
        simpa [validRows] using (⟨w, valid w d hd, hw⟩ : ∃ w ∈ accepted, c (encode r) = some w)
      exact Or.inl ⟨r, Finset.mem_filter.mpr ⟨mem, noPair, w, d, hw, hd⟩, pick, pair⟩
  have oldBound : freshMean old ≤ ε * cachedMass accepted encode xs c := by
    refine (selection_gain_set_le accepted encode xs distinct c a cold key decode s ε
      (fun _ hr => (Finset.mem_filter.mp hr).2) valid rate).trans ?_
    apply mul_le_mul_right
    apply prEvent_mono
    rintro z ⟨r, hr, eq⟩
    exact ⟨r, (Finset.mem_filter.mp hr).1, eq⟩
  calc
    _ = partneredMass key decode accepted encode xs c +
        freshMean (fun v => Pr{let z ← run (update v)}[hit (update v) z.1 ∧ ¬hit c z.1]) := gain
    _ ≤ partneredMass key decode accepted encode xs c + freshMean (fun v => old v + new v) :=
      add_le_add_right (tsum_le_tsum fun v => mul_le_mul_right (split v) _) _
    _ ≤ _ := by
      rw [freshMean_add]
      exact add_le_add_right (add_le_add oldBound le_rfl) _

/-- A new partnership can occur at an older selected row or at the probed position itself.
Both costs use the same occupancy potential. -/
theorem partnered_mass_drift (key : A → K) (decode : Y → Option D) (accepted : Finset Y)
    (encode : X → A) (inj : Function.Injective encode) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : (A →ₒ Y).QueryCache) (target : X)
    (cold : c (encode target) = none) (ref : Y) (ok : ref ∈ accepted) (ε : ℝ≥0∞)
    (volume : ℝ≥0∞) (prior : priorPairRate key decode c (encode target) ≤ ε * volume)
    (valid : ∀ w d, decode w = some d → w ∈ accepted)
    (rate : ∀ d, Pr{let w ← $ᵗ Y}[decode w = some d] ≤ ε) :
    freshMean (fun v =>
      partneredMass key decode accepted encode xs (c.cacheQuery (encode target) v))
      ≤ partneredMass key decode accepted encode xs c + ε * (cachedMass accepted encode xs c +
        volume * forcedMass accepted encode xs c target ref) := by
  let a := encode target
  let update := fun v => c.cacheQuery a v
  let run (v : Y) := (simulateQ randomOracle (scan accepted encode xs)).run (update v)
  let new (v : Y) := Pr{let z ← run v}[z.1 = some target ∧ Partner key decode (update v) a]
  have selected (o : Option X) : (∃ r, o = some r ∧ encode r = a) ↔ o = some target := by
    exact ⟨fun ⟨r, eq, addr⟩ => inj addr ▸ eq, fun eq => ⟨target, eq, rfl⟩⟩
  have gain := paired_gain key decode accepted encode xs distinct c a cold ε valid rate
  dsimp only at gain
  simp_rw [selected] at gain
  have newBound : freshMean new ≤ (ε * volume) * forcedMass accepted encode xs c target ref :=
    (new_selection_gain key decode accepted encode xs distinct c target ref ok valid).le.trans
      (mul_le_mul_left prior _)
  refine gain.trans ?_
  rw [mul_add, ← mul_assoc]
  exact add_le_add_right (add_le_add_right newBound _) _

/-- A fresh row outside the scan can give an earlier selected row its first partner. -/
theorem partnered_mass_drift_outside (key : A → K) (decode : Y → Option D) (accepted : Finset Y)
    (encode : X → A) (xs : List X) (distinct : (xs.map encode).Nodup) (c : (A →ₒ Y).QueryCache)
    (a : A) (cold : c a = none) (outside : ∀ x, encode x ≠ a) (ε : ℝ≥0∞)
    (valid : ∀ w d, decode w = some d → w ∈ accepted)
    (rate : ∀ d, Pr{let w ← $ᵗ Y}[decode w = some d] ≤ ε) :
    freshMean (fun v => partneredMass key decode accepted encode xs (c.cacheQuery a v)) ≤
      partneredMass key decode accepted encode xs c + ε * cachedMass accepted encode xs c := by
  have gain := paired_gain key decode accepted encode xs distinct c a cold ε valid rate
  have absent (o : Option X) : ¬∃ r, o = some r ∧ encode r = a := fun ⟨r, _, eq⟩ => outside r eq
  simpa [absent, freshMean] using gain

end randomOracle.Partners

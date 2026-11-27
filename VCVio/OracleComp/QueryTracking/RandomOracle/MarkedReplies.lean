/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer

/-!
# Fresh matching replies at selected addresses

The charge counts distinct occupied addresses in a fixed set. The caller may draw private
coins, revisit addresses, and start with a populated cache. The match bound requires that
the initial cache contain no selected matching reply.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace randomOracle

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- Occupied addresses selected by the caller's previously fixed predicate. -/
@[expose] def occupiedAt (eligible : Set ι) (c : spec.QueryCache) : Set ι :=
  {t | t ∈ eligible ∧ (c t).isSome}

/-- The cache contains a matching reply at one of the selected addresses. -/
@[expose] def hasMatch (eligible : Set ι) (mark : ∀ t, spec.Range t → Prop)
    (c : spec.QueryCache) : Prop :=
  ∃ t ∈ eligible, ∃ w, c t = some w ∧ mark t w

omit [DecidableEq ι] [∀ t : spec.Domain, SampleableType (spec.Range t)] in
private theorem occupiedAt_mono (eligible : Set ι) {c d : spec.QueryCache} (le : c ≤ d) :
    occupiedAt eligible c ⊆ occupiedAt eligible d := by
  rintro t ⟨here, present⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp present
  exact ⟨here, Option.isSome_iff_exists.mpr ⟨y, le hy⟩⟩

/-- A matching reply costs its per-address probability once per occupied selected address. -/
theorem isPotentialStep_hasMatch (eligible : Set ι) (mark : ∀ t, spec.Range t → Prop)
    (ε : ℝ≥0∞) (rate : ∀ t ∈ eligible, Pr{let w ← $ᵗ (spec.Range t)}[mark t w] ≤ ε) :
    IsPotentialStep (unifFwdImpl spec + spec.randomOracle) (hasMatch eligible mark)
      (fun c => ((occupiedAt eligible c).encard : ℝ≥0∞) * ε) := by
  classical
  constructor
  · intro t c z hz
    have le : c ≤ z.2 := le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl
      (liftM (OracleSpec.query t) : OracleComp (unifSpec + spec) ((unifSpec + spec).Range t))
      (by simpa using hz)
    gcongr
    exact occupiedAt_mono eligible le
  · rintro (i | t) c good
    · obtain ⟨sampler, run⟩ := exists_run_unifFwdImpl_add_randomOracle_inl (spec := spec) i c
      exact Or.inr ⟨sampler, fun _ => c, 0, run, by simp [good], fun _ => by simp⟩
    · cases seen : c t with
      | some w => exact Or.inl ⟨w, c, QueryImpl.withCaching_run_some _ seen, good⟩
      | none =>
        have fires (w : spec.Range t) (h : hasMatch eligible mark (c.cacheQuery t w)) :
            t ∈ eligible ∧ mark t w := by
          obtain ⟨b, hb, v, stored, matching⟩ := h
          by_cases same : b = t
          · subst b
            simp only [QueryCache.cacheQuery_self, Option.some.injEq] at stored
            exact ⟨hb, stored ▸ matching⟩
          · rw [QueryCache.cacheQuery_of_ne _ _ same] at stored
            exact False.elim (good ⟨b, hb, v, stored, matching⟩)
        have keep (w : spec.Range t) : occupiedAt eligible c ⊆
            occupiedAt eligible (c.cacheQuery t w) := by
          rintro b ⟨hb, cell⟩
          by_cases same : b = t
          · subst b
            simp [seen] at cell
          · exact ⟨hb, by rwa [QueryCache.cacheQuery_of_ne _ _ same]⟩
        by_cases charge : t ∈ eligible
        · refine Or.inr ⟨$ᵗ spec.Range t, fun w => c.cacheQuery t w, ε,
            QueryImpl.withCaching_run_none _ seen, ?_, ?_⟩
          · exact (prEvent_mono _ _ _ (fun w h => (fires w h).2)).trans (rate t charge)
          · intro w
            have new : t ∉ occupiedAt eligible c := fun h => by simpa [seen] using h.2
            have inc : insert t (occupiedAt eligible c) ⊆ occupiedAt eligible (c.cacheQuery t w) :=
              Set.insert_subset ⟨charge, by simp⟩ (keep w)
            have size := Set.encard_le_encard inc
            rw [Set.encard_insert_of_notMem new] at size
            calc
              _ = (((occupiedAt eligible c).encard : ℝ≥0∞) + 1) * ε := by ring
              _ ≤ _ := by gcongr; exact_mod_cast size
        · refine Or.inr ⟨$ᵗ spec.Range t, fun w => c.cacheQuery t w, 0,
            QueryImpl.withCaching_run_none _ seen, ?_, ?_⟩
          · exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ (fun w h => charge (fires w h).1))
          · intro w
            rw [zero_add]
            gcongr
            exact keep w

/-- From a cache with no match, the joint probability of a terminal match and at most `q`
occupied selected addresses is at most `q * ε`. -/
theorem prEvent_hasMatch_and_count {α : Type} (eligible : Set ι)
    (mark : ∀ t, spec.Range t → Prop) (ε : ℝ≥0∞) (finite : ε ≠ ⊤)
    (rate : ∀ t ∈ eligible, Pr{let w ← $ᵗ (spec.Range t)}[mark t w] ≤ ε)
    (oa : OracleComp (unifSpec + spec) α) (cache : spec.QueryCache)
    (good : ¬hasMatch eligible mark cache) (q : Nat) :
    Pr{let z ← (simulateQ (unifFwdImpl spec + spec.randomOracle) oa).run cache}[
      hasMatch eligible mark z.2 ∧ (occupiedAt eligible z.2).encard ≤ q] ≤ (q : ℝ≥0∞) * ε := by
  have s := isPotentialStep_hasMatch eligible mark ε rate
  apply (prEvent_mono _ _ _ ?_).trans
    ((prEvent_and_le_of_potential _ _ _ s.mono s.step oa (q * ε) (by finiteness) cache good).trans
      tsub_le_self)
  rintro z ⟨matched, cost⟩
  refine ⟨matched, ?_⟩
  gcongr
  exact_mod_cast cost

end randomOracle

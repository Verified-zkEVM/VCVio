/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.PartnerDrift

/-!
# Partnerships at the end of a stopped scan

Before the scan stops it adds only rejected words to its cache.
When it stops on a fresh accepted word, that word has the accepted-word distribution.
-/

public section

open OracleSpec OracleComp OracleComp.AcceptedScan
open scoped ENNReal

namespace randomOracle.Partners

variable {A X Y K D : Type} [DecidableEq A] [DecidableEq Y] [SampleableType Y]

/-- Every newly occupied, accepted word is the unique terminating answer of this scan. -/
theorem stopped_cache (accepted : Finset Y) (encode : X → A) (xs : List X)
    (c : (A →ₒ Y).QueryCache) {z}
    (run : z ∈ support ((simulateQ randomOracle (scanWithAnswer accepted encode xs)).run c)) :
    c ≤ z.2 ∧
      (∀ x w, z.1 = some (x, w) → z.2 (encode x) = some w ∧ w ∈ accepted) ∧
      ∀ a w, z.2 a = some w → w ∈ accepted →
        c a = some w ∨ ∃ x, z.1 = some (x, w) ∧ encode x = a := by
  induction xs generalizing c with
  | nil =>
    simp only [scanWithAnswer, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst z
    refine ⟨le_rfl, ?_, fun _ _ read _ => Or.inl read⟩
    intro _ _ eq
    cases eq
  | cons x xs ih =>
    simp only [scanWithAnswer, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at run
    obtain ⟨⟨v, mid⟩, step, tail⟩ := run
    have stored : mid (encode x) = some v :=
      QueryImpl.withCaching_run_caches uniformSampleImpl _ c _ step
    have ext : c ≤ mid := QueryImpl.withCaching_cache_le uniformSampleImpl _ c _ step
    have rest {b : A} (other : b ≠ encode x) : mid b = c b := by
      have eq := QueryImpl.withCaching_run_eq_cacheQuery uniformSampleImpl step
      exact (congrArg (fun cache : (A →ₒ Y).QueryCache => cache b) eq).trans
        (QueryCache.cacheQuery_of_ne c v other)
    by_cases yes : v ∈ accepted
    · simp only [yes, ite_true, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at tail
      subst z
      refine ⟨ext, ?_, ?_⟩
      · intro r w h
        cases h
        exact ⟨stored, yes⟩
      · intro b w hw _
        by_cases same : b = encode x
        · subst b
          exact Or.inr ⟨x, by rw [Option.some.inj (stored.symm.trans hw)], rfl⟩
        · exact Or.inl ((rest same).symm.trans hw)
    · simp only [yes, ite_false] at tail
      obtain ⟨later, chosen, only⟩ := ih mid tail
      refine ⟨ext.trans later, chosen, ?_⟩
      intro b w hw ok
      rcases only b w hw ok with atMid | selected
      · by_cases same : b = encode x
        · subst b
          exact (yes ((Option.some.inj (atMid.symm.trans stored)) ▸ ok)).elim
        · exact Or.inl ((rest same).symm.trans atMid)
      · exact Or.inr selected

/-- A cold terminating answer is charged at its conditional acceptance rate. -/
theorem stopped_fresh_rate (accepted : Finset Y) (encode : X → A) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : (A →ₒ Y).QueryCache) (mark : Y → Prop) :
    let run := (simulateQ randomOracle (scanWithAnswer accepted encode xs)).run c
    Pr{let w ← $ᵗ Y}[w ∈ accepted] *
      Pr{let z ← run}[∃ x w, z.1 = some (x, w) ∧ c (encode x) = none ∧ mark w] =
      Pr{let w ← $ᵗ Y}[w ∈ accepted ∧ mark w] *
        Pr{let z ← run}[∃ x w, z.1 = some (x, w) ∧ c (encode x) = none] := by
  classical
  intro run
  let hit (o : Option (X × Y)) := ∃ x w, o = some (x, w) ∧ c (encode x) = none ∧ mark w
  let fresh (o : Option (X × Y)) := ∃ x w, o = some (x, w) ∧ c (encode x) = none
  rw [prEvent_scanWithAnswer accepted encode xs distinct c hit,
    prEvent_scanWithAnswer accepted encode xs distinct c fresh]
  clear run distinct
  induction xs with
  | nil => simp [answerProbability, hit, fresh]
  | cons x xs ih =>
    simp only [answerProbability, List.foldr_cons] at ih ⊢
    cases hx : c (encode x) with
    | some w =>
      by_cases ok : w ∈ accepted
      · simp [hit, fresh, hx, ok]
      · simpa [ok] using ih
    | none =>
      simp only [mul_add]
      congr 1
      · simp [hit, fresh, hx, mul_comm]
      · rw [mul_left_comm, ih, mul_left_comm]

/-- The partner at the end of a scan is already present at entry.
If the selected address itself was warm then the partnership also existed at entry. -/
theorem stopped_partner_cases (key : A → K) (decode : Y → Option D) (accepted : Finset Y)
    (encode : X → A) (xs : List X) (c : (A →ₒ Y).QueryCache)
    (valid : ∀ w d, decode w = some d → w ∈ accepted) {z}
    (run : z ∈ support ((simulateQ randomOracle (scanWithAnswer accepted encode xs)).run c))
    {x w} (selected : z.1 = some (x, w)) (pair : Partner key decode z.2 (encode x)) :
    Partner key decode c (encode x) ∨
      c (encode x) = none ∧ StoredDigest key decode c (key (encode x)) w := by
  have ⟨ext, read, unchanged⟩ := stopped_cache accepted encode xs c run
  obtain ⟨own, ownValue, d, ownDigest, b, other, same, u, hv, hd⟩ := pair
  have reply : own = w := Option.some.inj (ownValue.symm.trans (read x w selected).1)
  subst own
  have old : c b = some u := by
    rcases unchanged b u hv (valid u d hd) with present | ⟨r, atFinal, position⟩
    · exact present
    · have role := congrArg Prod.fst (Option.some.inj (atFinal.symm.trans selected))
      exact (other (position.symm.trans (congrArg encode role))).elim
  cases h : c (encode x) with
  | none => exact Or.inr ⟨rfl, d, ownDigest, b, same, u, old, hd⟩
  | some v =>
    obtain rfl := Option.some.inj ((ext h).symm.trans ownValue)
    exact Or.inl ⟨_, h, d, ownDigest, b, other, same, u, old, hd⟩

/-- Price the fresh-final case once for a search at this key, even for a fixed starting seed.
A warm selected row contributes precisely through its entry partnership mass. -/
theorem stopped_partner_le (key : A → K) (decode : Y → Option D) (accepted : Finset Y)
    (encode : X → A) (xs : List X) (distinct : (xs.map encode).Nodup) (c : (A →ₒ Y).QueryCache)
    (k : K) (sameKey : ∀ x, key (encode x) = k) (valid : ∀ w d, decode w = some d → w ∈ accepted) :
    let p := Pr{let w ← $ᵗ Y}[w ∈ accepted]
    let pick := (simulateQ randomOracle (scanWithAnswer accepted encode xs)).run c
    p * Pr{let z ← pick}[∃ x w, z.1 = some (x, w) ∧ Partner key decode z.2 (encode x)] ≤
      p * partneredMass key decode accepted encode xs c +
        Pr{let w ← $ᵗ Y}[w ∈ accepted ∧ StoredDigest key decode c k w] := by
  classical
  intro p pick
  let prior (z : Option (X × Y) × (A →ₒ Y).QueryCache) :=
    ∃ x w, z.1 = some (x, w) ∧ Partner key decode c (encode x)
  let fresh (z : Option (X × Y) × (A →ₒ Y).QueryCache) :=
    ∃ x w, z.1 = some (x, w) ∧ c (encode x) = none ∧ StoredDigest key decode c k w
  have split : Pr{let z ← pick}[∃ x w, z.1 = some (x, w) ∧ Partner key decode z.2 (encode x)] ≤
      Pr{let z ← pick}[prior z] + Pr{let z ← pick}[fresh z] := by
    refine (prEvent_mono_of_support pick _ _ ?_).trans (prEvent_or_le pick prior fresh)
    rintro z hz ⟨x, w, eq, pair⟩
    rcases stopped_partner_cases key decode accepted encode xs c valid hz eq pair with old | new
    · exact Or.inl ⟨x, w, eq, old⟩
    · exact Or.inr ⟨x, w, eq, new.1, sameKey x ▸ new.2⟩
  have init : Pr{let z ← pick}[prior z] = partneredMass key decode accepted encode xs c := by
    simp only [partneredMass, scan, simulateQ_map, StateT.run_map, prEvent_norm]
    apply prEvent_congr
    rintro ⟨_ | ⟨x, w⟩, cache⟩ <;> simp [prior]
  have conditional := stopped_fresh_rate accepted encode xs distinct c (StoredDigest key decode c k)
  have final : p * Pr{let z ← pick}[fresh z] ≤
      Pr{let w ← $ᵗ Y}[w ∈ accepted ∧ StoredDigest key decode c k w] := by
    refine conditional.le.trans ?_
    exact mul_le_of_le_one_right zero_le (prEvent_le_one _)
  calc
    _ ≤ p * (Pr{let z ← pick}[prior z] + Pr{let z ← pick}[fresh z]) := by gcongr
    _ ≤ _ := by rw [mul_add, init]; gcongr

end randomOracle.Partners

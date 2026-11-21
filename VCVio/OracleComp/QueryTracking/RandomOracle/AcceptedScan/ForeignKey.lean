/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Compensation

/-!
# A probe at another signing key

A lookup at a foreign key can change neither the finder's replies nor any of its partnerships.
These identities hold separately for each possible word returned by the probe.
-/

public section

open OracleSpec OracleComp OracleComp.AcceptedScan
open scoped ENNReal

namespace randomOracle.Partners

variable {A X Y K D : Type} [Fintype X] [DecidableEq A] [DecidableEq Y] [SampleableType Y]

/-- Occupancy and partnership selection masses are unchanged, word by word, at an unrelated key. -/
theorem unchanged_at_other_key (key : A → K) (decode : Y → Option D) (accepted : Finset Y)
    (encode : X → A) (xs : List X) (distinct : (xs.map encode).Nodup)
    (c : (A →ₒ Y).QueryCache) (a : A) (cold : c a = none)
    (other : ∀ r, key a ≠ key (encode r)) (v : Y) :
    cachedMass accepted encode xs (c.cacheQuery a v) = cachedMass accepted encode xs c ∧
      partneredMass key decode accepted encode xs (c.cacheQuery a v) =
        partneredMass key decode accepted encode xs c := by
  classical
  have ne (r : X) : encode r ≠ a := fun eq => other r ((congrArg key eq).symm)
  have agree (r : X) : (c.cacheQuery a v) (encode r) = c (encode r) :=
    QueryCache.cacheQuery_of_ne c v (ne r)
  have rows : validRows accepted encode (c.cacheQuery a v) = validRows accepted encode c := by
    ext r
    simp only [validRows, Finset.mem_filter, agree]
  have partner (r : X) : Partner key decode (c.cacheQuery a v) (encode r) ↔
      Partner key decode c (encode r) := by
    refine ⟨fun post => ?_, mono key decode (QueryCache.le_cacheQuery c cold)⟩
    by_contra old
    obtain ⟨_, _, _, _, same, _⟩ := newly_matches key decode (ne r) v old post
    exact other r same
  constructor
  · unfold cachedMass
    rw [rows]
    exact selection_congr accepted encode xs distinct _ c
      (fun o => ∃ r ∈ validRows accepted encode c, o = some r) fun r _ => agree r
  · unfold partneredMass
    simp_rw [partner]
    exact selection_congr accepted encode xs distinct _ c
      (fun o => ∃ r, o = some r ∧ Partner key decode c (encode r)) fun r _ => agree r

end randomOracle.Partners

/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.PartnerProbe

/-!
# The selection mass added at a probed address

A newly sampled word has a partner exactly when its digest already occurs elsewhere at its key.
If it does, the scan treats it as an accepted word.
-/

public section

open OracleSpec OracleComp AcceptedScan
open scoped ENNReal

namespace randomOracle.Partners

variable {ι X Y K D : Type} [DecidableEq ι] (key : ι → K) (decode : Y → Option D)

/-- The new word can acquire a partner only from a different, previously occupied address. -/
theorem at_probe_iff (c : (ι →ₒ Y).QueryCache) (a : ι) (v : Y) :
    Partner key decode (c.cacheQuery a v) a ↔
      ∃ d, decode v = some d ∧ ∃ b ≠ a, key b = key a ∧
        ∃ w, c b = some w ∧ decode w = some d := by
  constructor
  · rintro ⟨w, hw, d, wd, b, ne, hk, z, hz, zd⟩
    rw [QueryCache.cacheQuery_self, Option.some_inj] at hw
    exact ⟨d, hw ▸ wd, b, ne, hk, z, (QueryCache.cacheQuery_of_ne c v ne).symm ▸ hz, zd⟩
  · rintro ⟨d, vd, b, ne, hk, w, hw, wd⟩
    exact ⟨v, QueryCache.cacheQuery_self _ _ _, d, vd, b, ne, hk, w,
      (QueryCache.cacheQuery_of_ne c v ne) ▸ hw, wd⟩

variable [DecidableEq Y] [SampleableType Y]

/-- The new address contributes exactly its chance of finding an existing partner times the
selection probability when that address is occupied by any accepted word. -/
theorem new_selection_gain (accepted : Finset Y) (encode : X → ι) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : (ι →ₒ Y).QueryCache) (target : X) (ref : Y)
    (ok : ref ∈ accepted) (valid : ∀ v d, decode v = some d → v ∈ accepted) :
    let a := encode target
    let paired (v : Y) := ∃ d, decode v = some d ∧ ∃ b ≠ a, key b = key a ∧
      ∃ w, c b = some w ∧ decode w = some d
    (∑' v, Pr{let y ← $ᵗ Y}[y = v] *
      Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run (c.cacheQuery a v)}[
        z.1 = some target ∧ Partner key decode (c.cacheQuery a v) a]) =
      Pr{let y ← $ᵗ Y}[paired y] *
        Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run (c.cacheQuery a ref)}[
          z.1 = some target] := by
  classical
  intro a paired
  rw [prEvent_eq_tsum_ite ($ᵗ Y) paired, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro v
  by_cases occurs : paired v
  · have p := (at_probe_iff key decode c a v).2 occurs
    have accepted_v : v ∈ accepted := by
      obtain ⟨d, vd, _⟩ := occurs
      exact valid v d vd
    simp only [p, occurs, and_true, ite_true]
    rw [select_eq_of_probe_accepted accepted encode xs distinct c target a v ref accepted_v ok]
  · have p : ¬Partner key decode (c.cacheQuery a v) a := fun h =>
      occurs ((at_probe_iff key decode c a v).1 h)
    simp [p, occurs]

end randomOracle.Partners

/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Probe

/-!
# Cache entries that share a valid digest at one key

One fresh reply can give an older entry its first partner.
Two different older entries cannot both acquire their first partner from the same insertion.
-/

public section

open OracleSpec OracleComp
open scoped ENNReal

namespace randomOracle.Partners

variable {ι Y K D : Type} [DecidableEq ι]
  (key : ι → K) (decode : Y → Option D)

/-- Two different addresses of one key contain words that decode to the same digest. -/
@[expose] def Partner (cache : (ι →ₒ Y).QueryCache) (a : ι) : Prop :=
  ∃ w, cache a = some w ∧ ∃ d, decode w = some d ∧
    ∃ b ≠ a, key b = key a ∧ ∃ v, cache b = some v ∧ decode v = some d

omit [DecidableEq ι] in
/-- Once an address has a partner, extending the random-oracle cache preserves both words. -/
theorem mono {c c' : (ι →ₒ Y).QueryCache} (le : c ≤ c') {a : ι}
    (h : Partner key decode c a) : Partner key decode c' a := by
  obtain ⟨w, hw, d, hd, b, ne, k, v, hv, vd⟩ := h
  exact ⟨w, le hw, d, hd, b, ne, k, v, le hv, vd⟩

/-- An older address that gains its first partner must match the newly inserted word. -/
theorem newly_matches {c : (ι →ₒ Y).QueryCache} {x a : ι} (ne : a ≠ x) (v : Y)
    (old : ¬Partner key decode c a) (new : Partner key decode (c.cacheQuery x v) a) :
    ∃ w d, c a = some w ∧ decode w = some d ∧ key x = key a ∧ decode v = some d := by
  obtain ⟨w, hw, d, hd, b, diff, hk, u, hu, ud⟩ := new
  rw [QueryCache.cacheQuery_of_ne _ _ ne] at hw
  by_cases bx : b = x
  · subst b
    rw [QueryCache.cacheQuery_self, Option.some_inj] at hu
    exact ⟨w, d, hw, hd, hk, hu ▸ ud⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ bx] at hu
    exact False.elim (old ⟨w, hw, d, hd, b, diff, hk, u, hu, ud⟩)

/-- At most one earlier address gains its first partner when a single reply is inserted. -/
theorem unique_old {c : (ι →ₒ Y).QueryCache} {x a b : ι} (v : Y) (ha : a ≠ x) (hb : b ≠ x)
    (oldA : ¬Partner key decode c a) (oldB : ¬Partner key decode c b)
    (newA : Partner key decode (c.cacheQuery x v) a)
    (newB : Partner key decode (c.cacheQuery x v) b) : a = b := by
  obtain ⟨wa, da, ca, ava, ka, va⟩ := newly_matches key decode ha v oldA newA
  obtain ⟨wb, db, cb, avb, kb, vb⟩ := newly_matches key decode hb v oldB newB
  by_contra diff
  have same := Option.some.inj (vb.symm.trans va)
  exact oldA ⟨wa, ca, da, ava, b, Ne.symm diff, kb.symm.trans ka, wb, cb, same ▸ avb⟩

variable [SampleableType Y]

/-- Averaged over a fresh probe, the gain is exactly the chance of selecting a newly partnered row.

The caller may choose later query addresses as functions of the earlier replies. -/
theorem selection_gain (oa : OracleComp (ι →ₒ Y) (Option ι)) (c : (ι →ₒ Y).QueryCache) (x : ι)
    (cold : c x = none) :
    let hit (cache : (ι →ₒ Y).QueryCache) (r : Option ι) :=
      ∃ a, r = some a ∧ Partner key decode cache a
    (∑' v, Pr{let w ← $ᵗ Y}[w = v] *
      Pr{let z ← (simulateQ randomOracle oa).run (c.cacheQuery x v)}[hit (c.cacheQuery x v) z.1]) =
      Pr{let z ← (simulateQ randomOracle oa).run c}[hit c z.1] +
        ∑' v, Pr{let w ← $ᵗ Y}[w = v] *
          Pr{let z ← (simulateQ randomOracle oa).run (c.cacheQuery x v)}[
            hit (c.cacheQuery x v) z.1 ∧ ¬hit c z.1] := by
  let hit (cache : (ι →ₒ Y).QueryCache) (r : Option ι) :=
    ∃ a, r = some a ∧ Partner key decode cache a
  apply average_growing_event oa c x cold (hit c) (fun v => hit (c.cacheQuery x v))
  rintro v _ ⟨a, rfl, h⟩
  exact ⟨a, rfl, mono key decode (QueryCache.le_cacheQuery c cold) h⟩

end randomOracle.Partners

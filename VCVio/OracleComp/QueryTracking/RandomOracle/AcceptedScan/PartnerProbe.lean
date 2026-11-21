/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Partners
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Selection

/-!
# Selection of an old word that gains its first partner

A new matching digest stops the scan at its own address.
It can only lower the selection probability at a different address.
-/

public section

open OracleComp OracleSpec AcceptedScan
open scoped ENNReal

namespace randomOracle.Partners

variable {ι X Y K D : Type} [DecidableEq ι] [DecidableEq Y] [SampleableType Y]

/-- The mass added to one older address is at most its original selection mass times its
singleton digest probability. -/
theorem old_selection_gain_le (accepted : Finset Y) (encode : X → ι) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : (ι →ₒ Y).QueryCache) (a : ι) (target : X)
    (other : a ≠ encode target) (key : ι → K) (decode : Y → Option D) (d : D) (w : Y)
    (cached : c (encode target) = some w) (digit : decode w = some d)
    (valid : ∀ y, decode y = some d → y ∈ accepted) (old : ¬Partner key decode c (encode target)) :
    (∑' v, Pr{let y ← $ᵗ Y}[y = v] *
      Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run (c.cacheQuery a v)}[
        z.1 = some target ∧ Partner key decode (c.cacheQuery a v) (encode target)]) ≤
      Pr{let y ← $ᵗ Y}[decode y = some d] *
        Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run c}[
          z.1 = some target] := by
  classical
  rw [prEvent_eq_tsum_ite ($ᵗ Y) (fun y => decode y = some d), ← ENNReal.tsum_mul_right]
  apply tsum_le_tsum
  intro v
  dsimp only
  by_cases sameDigest : decode v = some d
  · simp only [sameDigest, ite_true]
    gcongr
    exact (prEvent_mono _ _ _ (fun _ h => h.1)).trans
      (select_le_of_probe_accepted accepted encode xs distinct c target a other v
        (valid v sameDigest))
  · simp only [sameDigest, ite_false, zero_mul]
    have none : Pr{let z ←
        (simulateQ randomOracle (scan accepted encode xs)).run (c.cacheQuery a v)}[
        z.1 = some target ∧ Partner key decode (c.cacheQuery a v) (encode target)] = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      rintro _ _ ⟨_, h⟩
      obtain ⟨u, e, hu, he, _, hv⟩ := newly_matches key decode other.symm v old h
      have same := Option.some.inj (hu.symm.trans cached)
      subst u
      exact sameDigest (hv.trans (he.symm.trans digit))
    simp [none]

end randomOracle.Partners

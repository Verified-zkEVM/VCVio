/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.PartnerProbe

/-!
# A probe's contribution across previously unpartnered targets

A scan selects at most one position.
The mass of selecting any older target that gains a partner is charged to the original chance
of selecting a target from the whole set.
-/

public section

open OracleSpec OracleComp AcceptedScan
open scoped ENNReal

namespace randomOracle.Partners

variable {ι X Y K D σ : Type} [DecidableEq ι] [DecidableEq Y] [SampleableType Y]

/-- Disjoint selection outcomes add to the mass of selecting any member of a finite set. -/
private theorem sum_selected (run : ProbComp (Option X × σ)) (s : Finset X) :
    (∑ t ∈ s, Pr{let z ← run}[z.1 = some t]) =
      Pr{let z ← run}[∃ t ∈ s, z.1 = some t] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert t s ht ih =>
    rw [Finset.sum_insert ht, ih]
    let any (z : Option X × σ) := ∃ u ∈ insert t s, z.1 = some u
    have first : (fun z => any z ∧ z.1 = some t) = (fun z => z.1 = some t) := by
      ext z
      exact ⟨And.right, fun h => ⟨⟨t, Finset.mem_insert_self _ _, h⟩, h⟩⟩
    have rest : (fun z => any z ∧ z.1 ≠ some t) = (fun z => ∃ u ∈ s, z.1 = some u) := by
      ext z
      constructor
      · rintro ⟨⟨u, hu, chosen⟩, ne⟩
        rcases Finset.mem_insert.mp hu with eq | inS
        · exact False.elim (ne (eq ▸ chosen))
        · exact ⟨u, inS, chosen⟩
      · rintro ⟨u, hu, chosen⟩
        exact ⟨⟨u, Finset.mem_insert_of_mem hu, chosen⟩, fun eq =>
          ht ((Option.some.inj (chosen.symm.trans eq)) ▸ hu)⟩
    exact (prEvent_eq_prEvent_and_add_prEvent_and_not run any (fun z => z.1 = some t)
      |>.trans (by rw [first, rest])).symm

/-- A fresh probe contributes at most the singleton rate times the original selection mass
of the whole set of previously unpartnered targets. -/
theorem selection_gain_set_le (accepted : Finset Y) (encode : X → ι) (xs : List X)
    (distinct : (xs.map encode).Nodup) (c : (ι →ₒ Y).QueryCache) (a : ι) (cold : c a = none)
    (key : ι → K) (decode : Y → Option D) (s : Finset X) (ε : ℝ≥0∞)
    (eligible : ∀ t ∈ s, ¬Partner key decode c (encode t) ∧
      ∃ w d, c (encode t) = some w ∧ decode w = some d)
    (valid : ∀ w d, decode w = some d → w ∈ accepted)
    (rate : ∀ d, Pr{let w ← $ᵗ Y}[decode w = some d] ≤ ε) :
    (∑' v, Pr{let w ← $ᵗ Y}[w = v] *
      Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run (c.cacheQuery a v)}[
        ∃ t ∈ s, z.1 = some t ∧ Partner key decode (c.cacheQuery a v) (encode t)]) ≤
      ε * Pr{let z ← (simulateQ randomOracle (scan accepted encode xs)).run c}[
        ∃ t ∈ s, z.1 = some t] := by
  classical
  let run (cache : (ι →ₒ Y).QueryCache) :=
    (simulateQ randomOracle (scan accepted encode xs)).run cache
  let mass (v : Y) (t : X) := Pr{let z ← run (c.cacheQuery a v)}[
    z.1 = some t ∧ Partner key decode (c.cacheQuery a v) (encode t)]
  calc
    _ ≤ ∑' v, Pr{let w ← $ᵗ Y}[w = v] * ∑ t ∈ s, mass v t := by
      apply tsum_le_tsum
      intro v
      dsimp only
      gcongr
      exact prEvent_exists_finset_le s (run (c.cacheQuery a v)) _
    _ = ∑ t ∈ s, ∑' v, Pr{let w ← $ᵗ Y}[w = v] * mass v t := by
      simp_rw [Finset.mul_sum]
      exact Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)
    _ ≤ ∑ t ∈ s, ε * Pr{let z ← run c}[z.1 = some t] := by
      refine Finset.sum_le_sum fun t ht => ?_
      obtain ⟨old, w, d, cached, decoded⟩ := eligible t ht
      have other : a ≠ encode t := by
        rintro rfl
        rw [cold] at cached
        contradiction
      exact (old_selection_gain_le accepted encode xs distinct c a t other key decode d w
        cached decoded (fun y => valid y d) old).trans (by gcongr; exact rate d)
    _ = _ := by rw [← Finset.mul_sum, sum_selected]

end randomOracle.Partners

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Conditions
public import VCVio.Quantum.Oracle.Compressed.Instability

/-!
# Instability of salted Merkle extraction

For one extraction tuple, a fresh answer can change the online label only at its unique root
for the selected oracle or at a half-preimage. Thus databases with at most `s` entries have
instability at most `min (1, (2s + 1) / |Y|)`, including databases with collisions.

## References

Chiesa–Di–Hu–Zheng, ePrint 2025/2166: half-preimages and extraction sensitivity
(Definition 8.5 and Lemma 8.6, p. 55), and the online instability argument
(Lemma 8.8, p. 56). The singleton-tuple bound proved here counts one selected root
and at most two half-preimages per database cell.
-/

public section

open Quantum OracleSpec
open scoped ENNReal

namespace SaltedMerkle

variable {X Y Msg Salt : Type} [Fintype X] [DecidableEq X] [LinearOrder Y] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y) {k : ℕ} (d : Fin k → ℕ)

open scoped Classical in
/-- A singleton online extraction has at most one root at any selected oracle. -/
theorem card_onlineLabel_changes_le (tic : TpIC k Y) (Dfix : Fin k → Database X Y)
    (j : Fin k) (D : Database X Y) (x : X) (hx : D x = none) :
    (Finset.univ.filter fun y : Y ↦
      onlineLabel (multiExtract enc d) ![tic] Dfix j (Function.update D x (some y)) ≠
        onlineLabel (multiExtract enc d) ![tic] Dfix j D).card ≤ 2 * D.size + 1 := by
  classical
  let π := onlineLabel (multiExtract enc d) ![tic] Dfix j
  have stable (y : Y)
      (hy : ∀ i, (tic.2 i).1 = j → y ∉ insert (tic.2 i).2 (halfPreimages enc D)) :
      π (Function.update D x (some y)) = π D := by
    funext a
    fin_cases a
    have h := multiExtract_update_eq enc d tic (Function.update Dfix j D) j
      (by simpa using hx) (by simpa using hy)
    simpa [π, onlineLabel, Function.update_idem] using h
  by_cases hinj : Function.Injective tic.idx
  · by_cases hex : ∃ i, (tic.2 i).1 = j
    · obtain ⟨i, hi⟩ := hex
      let S := (insert (tic.2 i).2 (halfPreimages enc D)).toFinset
      have hsub : (Finset.univ.filter fun y : Y ↦ π (Function.update D x (some y)) ≠ π D) ⊆ S := by
        intro y hy
        apply Set.mem_toFinset.mpr
        by_contra hn
        apply (Finset.mem_filter.mp hy).2
        apply stable y
        intro l hl
        have heq : l = i := hinj (hl.trans hi.symm)
        simpa [heq] using hn
      calc _ ≤ S.card := Finset.card_le_card hsub
        _ = (insert (tic.2 i).2 (halfPreimages enc D)).ncard :=
          (Set.ncard_eq_toFinset_card' (insert (tic.2 i).2 (halfPreimages enc D))).symm
        _ ≤ (halfPreimages enc D).ncard + 1 := Set.ncard_insert_le _ _
        _ ≤ 2 * D.size + 1 := by
          have h := ncard_halfPreimages_le_of_finite enc D
          rw [Database.ncard_support_eq_size] at h
          omega
    · have hπ (y : Y) : π (Function.update D x (some y)) = π D :=
        stable y fun i hi ↦ (hex ⟨i, hi⟩).elim
      change (Finset.univ.filter fun y : Y ↦ π (Function.update D x (some y)) ≠ π D).card ≤ _
      simp [hπ]
  · have hπ (y : Y) : π (Function.update D x (some y)) = π D := by
      funext a
      fin_cases a
      simp [π, onlineLabel, multiExtract, hinj]
    change (Finset.univ.filter fun y : Y ↦ π (Function.update D x (some y)) ≠ π D).card ≤ _
    simp [hπ]

omit [Fintype X] in
/-- Concrete Merkle instability at the `s + 1` truncation used after `s` oracle calls. -/
theorem instability_onlineLabel_le [Finite X] [UniformAnswerMeasure (X →ₒ Y)]
    (tic : TpIC k Y) (Dfix : Fin k → Database X Y) (j : Fin k) (s : ℕ) :
    Database.instability (onlineLabel (multiExtract enc d) ![tic] Dfix j) (s + 1) ≤
      min 1 ((2 * s + 1 : ℝ≥0∞) / Fintype.card Y) := by
  classical
  let _ := Fintype.ofFinite X
  refine le_min (Database.instability_le_one _ _) ?_
  rw [Database.instability_eq_iSup]
  refine iSup_le fun l ↦ iSup_le fun D ↦ iSup_le fun hl ↦ iSup_le fun hD ↦
    iSup_le fun x ↦ iSup_le fun hx ↦ ?_
  subst l
  have hc := card_onlineLabel_changes_le enc d tic Dfix j D x hx
  have hs : D.size ≤ s := by omega
  have hc' : (Finset.univ.filter fun y : Y ↦
      onlineLabel (multiExtract enc d) ![tic] Dfix j (Function.update D x (some y)) ≠
        onlineLabel (multiExtract enc d) ![tic] Dfix j D).card ≤ 2 * s + 1 := by omega
  gcongr
  exact_mod_cast hc'

end SaltedMerkle

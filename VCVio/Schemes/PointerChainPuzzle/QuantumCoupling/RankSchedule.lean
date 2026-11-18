/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumCoupling.Programming

/-!
# Rank-cutoff raw oracle schedules

A prefix oracle programs only path responses received by the honest solver through a given
rank. It depends on the full raw words of that rank prefix, including every mask tail. The
complete programmed table differs from it only at inputs of later path values, even when
path inputs repeat.

Typed-label resampling keeps all raw tails fixed and preserves the public commitment. This
preserves prefix oracles without making the commitment input available before its rank.
-/

public section

open OracleSpec OracleComp Quantum

namespace PointerChainPuzzle.LeanSeal

variable {b n m B : ℕ}

section Schedule

variable [NeZero n]

/-- Program only the raw path responses received through rank `r`, with earlier writes taking
priority when path inputs repeat. Raw responses include every mask tail. -/
@[expose]
def prefixProgram (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b) (r : ℕ)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32) :
    ByteArray.Bounded B → Bytes 32 :=
  Equiv.tableLabelProgram (rawPathInput hb hB salt x z)
    (fun _ ↦ (Equiv.prodPUnit (Bytes 32) : Bytes 32 × Unit ≃ Bytes 32).symm)
    ((PathValue.order n m).filter fun v ↦ decide (v.rho ≤ r)) H W

/-- Encoded path inputs whose honest receipt rank exceeds `r`. -/
@[expose]
def futureRawPathInputs (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (W : PathValue n m → Bytes 32) (r : ℕ) : Set (ByteArray.Bounded B) :=
  {d | ∃ v : PathValue n m, r < v.rho ∧ d = rawPathInput hb hB salt x z v W}

/-- Future raw path inputs are precisely the encodings of the corresponding typed inputs. -/
theorem futureRawPathInputs_eq_image (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (W : PathValue n m → Bytes 32) (r : ℕ) :
    futureRawPathInputs hb hB salt x z W r = hashInputWindow hB ''
      futurePathInputs m (ctx b n m) id (labelPuzzle salt x z (pathLabels hb W))
        (pathLabels hb W) r := by
  ext d
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- Agreement of raw words through rank `r` preserves every path input available in round
`r + 1`. The input is independent of the public commitment label. -/
theorem rawPathInput_eq_of_eq_on_rankPrefix (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    {W W' : PathValue n m → Bytes 32} {r : ℕ} {v : PathValue n m}
    (hv : v.rho ≤ r + 1)
    (h : ∀ w ∈ PathValue.rankPrefix n m r, W w = W' w) :
    rawPathInput hb hB salt x z v W = rawPathInput hb hB salt x z v W' := by
  unfold rawPathInput pathWindowInput
  congr 1
  rw [pathInput_labelPuzzle m (ctx b n m) id salt x z (pathLabels hb W) (pathLabels hb W')]
  apply pathInput_eq_of_eq_on_rankPrefix _ hv
  intro w hw
  exact congrArg (fun a ↦ (splitPath hb w a).1) (h w hw)

/-- A rank-cutoff oracle depends only on full raw responses in its rank prefix. -/
theorem prefixProgram_eq_of_eq_on_rankPrefix (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b) (r : ℕ)
    (H : ByteArray.Bounded B → Bytes 32) {W W' : PathValue n m → Bytes 32}
    (h : ∀ v ∈ PathValue.rankPrefix n m r, W v = W' v) :
    prefixProgram hb hB salt x z r H W = prefixProgram hb hB salt x z r H W' := by
  unfold prefixProgram
  apply Equiv.tableLabelProgram_congr
  · intro v hv
    have hvr : v.rho ≤ r := by simpa using (List.mem_filter.mp hv).2
    exact rawPathInput_eq_of_eq_on_rankPrefix hb hB salt x z (hvr.trans (Nat.le_succ _)) h
  · intro v hv
    exact h v (by simpa using (List.mem_filter.mp hv).2)

/-- Updating any raw response of later rank leaves a cutoff oracle unchanged. Later output
labels, including the key and commitment labels, do not influence an earlier cutoff oracle. -/
theorem prefixProgram_update_of_lt_rho (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b) (r : ℕ)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (v : PathValue n m) (hv : r < v.rho) (a : Bytes 32) :
    prefixProgram hb hB salt x z r H (Function.update W v a) =
      prefixProgram hb hB salt x z r H W := by
  apply prefixProgram_eq_of_eq_on_rankPrefix
  intro w hw
  apply Function.update_of_ne
  intro he
  subst w
  exact (not_lt_of_ge (PathValue.mem_rankPrefix.mp hw)) hv

/-- Complete and rank-cutoff programming agree outside the encoded future path inputs.
No distinctness or collision-freedom assumption is needed. -/
theorem programPath_eq_prefixProgram_of_avoids_future (hb : b ≤ 32)
    (hB : hashInputBound b ≤ B) (salt : Bytes 16) (x : Bytes b)
    (z : Fin (n - 1) → Bytes b) (r : ℕ)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (d : ByteArray.Bounded B) (hd : d ∉ futureRawPathInputs hb hB salt x z W r) :
    programPath hb hB salt x z H W d = prefixProgram hb hB salt x z r H W d := by
  apply Equiv.tableLabelProgram_filter_apply_of_avoids
  intro v _ hv he
  apply hd
  exact ⟨v, by simpa using hv, he.symm⟩

end Schedule

/-- Resample typed labels outside `R`, retaining the public commitment and every raw tail. -/
@[expose]
def mixPathWords (hb : b ≤ 32) (R : Finset (PathValue n m))
    (W : PathValue n m → Bytes 32) (ℓ' : Labels n m (Bytes 32) (Bytes b)) :
    PathValue n m → Bytes 32 :=
  (pathLabelEquiv hb).symm
    (mixLabels R (pathLabels hb W) ℓ', (pathLabelEquiv hb W).2)

/-- The typed projections of mixed raw words are the prescribed mixed typed labels. -/
@[simp]
theorem pathLabels_mixPathWords (hb : b ≤ 32) (R : Finset (PathValue n m))
    (W : PathValue n m → Bytes 32) (ℓ' : Labels n m (Bytes 32) (Bytes b)) :
    pathLabels hb (mixPathWords hb R W ℓ') = mixLabels R (pathLabels hb W) ℓ' :=
  congrArg Prod.fst ((pathLabelEquiv hb).apply_symm_apply _)

/-- Resampling typed labels leaves every complementary raw tail unchanged. -/
theorem splitPath_snd_mixPathWords (hb : b ≤ 32) (R : Finset (PathValue n m))
    (W : PathValue n m → Bytes 32) (ℓ' : Labels n m (Bytes 32) (Bytes b))
    (v : PathValue n m) :
    (splitPath hb v (mixPathWords hb R W ℓ' v)).2 = (splitPath hb v (W v)).2 := by
  exact congrFun (congrArg Prod.snd ((pathLabelEquiv hb).apply_symm_apply
    (mixLabels R (pathLabels hb W) ℓ', (pathLabelEquiv hb W).2))) v

/-- A preserved typed label and raw tail together preserve its complete raw response. -/
theorem mixPathWords_of_mem (hb : b ≤ 32) (R : Finset (PathValue n m))
    (W : PathValue n m → Bytes 32) (ℓ' : Labels n m (Bytes 32) (Bytes b))
    {v : PathValue n m} (hv : v ∈ R) : mixPathWords hb R W ℓ' v = W v := by
  apply (splitPath hb v).injective
  apply Prod.ext
  · exact (congrFun (pathLabels_mixPathWords hb R W ℓ') v).trans (mixLabels_of_mem hv)
  · exact splitPath_snd_mixPathWords hb R W ℓ' v

/-- Resampling keeps the public commitment's full raw response. -/
@[simp]
theorem mixPathWords_commit (hb : b ≤ 32) (R : Finset (PathValue n m))
    (W : PathValue n m → Bytes 32) (ℓ' : Labels n m (Bytes 32) (Bytes b)) :
    mixPathWords hb R W ℓ' .commit = W .commit := by
  apply (splitPath (n := n) (m := m) hb .commit).injective
  apply Prod.ext
  · exact (congrFun (pathLabels_mixPathWords hb R W ℓ') .commit).trans
      (mixLabels_commit R (pathLabels hb W) ℓ')
  · exact splitPath_snd_mixPathWords hb R W ℓ' .commit

/-- The public puzzle is unchanged when typed labels are resampled with fixed raw tails. -/
theorem labelPuzzle_pathLabels_mixPathWords (hb : b ≤ 32) (salt : Bytes 16)
    (x : Bytes b) (z : Fin (n - 1) → Bytes b) (R : Finset (PathValue n m))
    (W : PathValue n m → Bytes 32) (ℓ' : Labels n m (Bytes 32) (Bytes b)) :
    labelPuzzle salt x z (pathLabels hb (mixPathWords hb R W ℓ')) =
      labelPuzzle salt x z (pathLabels hb W) := by
  rw [pathLabels_mixPathWords, labelPuzzle_mixLabels]

/-- Resampling beyond a larger rank prefix, with every raw tail fixed, preserves an earlier
cutoff oracle. -/
theorem prefixProgram_mixPathWords_of_le [NeZero n] (hb : b ≤ 32)
    (hB : hashInputBound b ≤ B) (salt : Bytes 16) (x : Bytes b)
    (z : Fin (n - 1) → Bytes b) {r s : ℕ} (hrs : r ≤ s)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (ℓ' : Labels n m (Bytes 32) (Bytes b)) :
    prefixProgram hb hB salt x z r H (mixPathWords hb (PathValue.rankPrefix n m s) W ℓ') =
      prefixProgram hb hB salt x z r H W := by
  apply prefixProgram_eq_of_eq_on_rankPrefix
  exact fun _ hv ↦ mixPathWords_of_mem hb _ W ℓ' (PathValue.rankPrefix_mono hrs hv)

/-- Resampling beyond a rank prefix, with every raw tail fixed, preserves its cutoff oracle. -/
theorem prefixProgram_mixPathWords [NeZero n] (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b) (r : ℕ)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (ℓ' : Labels n m (Bytes 32) (Bytes b)) :
    prefixProgram hb hB salt x z r H (mixPathWords hb (PathValue.rankPrefix n m r) W ℓ') =
      prefixProgram hb hB salt x z r H W := by
  apply prefixProgram_eq_of_eq_on_rankPrefix
  exact fun _ hv ↦ mixPathWords_of_mem hb _ W ℓ' hv

end PointerChainPuzzle.LeanSeal

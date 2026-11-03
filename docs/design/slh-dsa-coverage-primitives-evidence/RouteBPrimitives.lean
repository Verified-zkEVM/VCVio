/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentrationSharper
public import HashSig.SLHDSA.SHAKE128s.Proof.BlockViews

/-! # Uniform FORS load tails and fixed-first-view symmetry -/

public section
open MeasureTheory ProbabilityTheory OracleComp OracleSpec
open scoped NNReal ENNReal

namespace SLHDSA.SHAKE128s.ForsConcentration

set_option exponentiation.threshold 1024 in
/-- The exact mean leaves enough room below 2^102 for a sixth-moment bound. -/
private theorem poisson_load_tail_nine_eighths :
    poissonLoads (2 ^ 63) {loads | (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads} ≤
      (1 : ENNReal) / (16 * 2 ^ 128) := by
  let gap : ℝ := 9 * 2 ^ 99 - 2 ^ 63 * 461101962108
  let threshold : ℝ := gap ^ 6
  let bound : ℝ := (2 ^ 63 : ℝ) * 2 ^ 359 +
    15 * (2 ^ 63) ^ 2 * 2 ^ 219 * 2 ^ 92 +
    10 * (2 ^ 63) ^ 2 * 2 ^ 308 +
    15 * (2 ^ 63) ^ 3 * (2 ^ 92) ^ 3
  have hgap : 0 < gap := by norm_num [gap]
  have ht : 0 < threshold := pow_pos hgap _
  have hsubset : {loads : Fin (2 ^ 63) → Nat | (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads} ⊆
      {loads | threshold ≤ centeredLoadSum loads ^ 6} := by
    intro loads hl
    change (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads at hl
    have hcenter : gap ≤ centeredLoadSum loads := by
      rw [centeredLoadSum_eq, touchard_fourteen_three]
      simpa only [gap, Nat.cast_pow, Nat.cast_ofNat] using
        sub_le_sub_right hl ((2 ^ 63 : ℝ) * 461101962108)
    exact pow_le_pow_left₀ hgap.le hcenter 6
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := poissonLoads (2 ^ 63))
    (f := fun loads => centeredLoadSum loads ^ 6)
    (Filter.Eventually.of_forall (fun loads =>
      (show Even 6 by decide).pow_nonneg (centeredLoadSum loads)))
    (poisson_centered_sum_moments (2 ^ 63) 6 (by decide)).1 threshold
  have hprob : (poissonLoads (2 ^ 63)).real
      {loads | (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads} ≤ bound / threshold := by
    apply (le_div_iff₀ ht).mpr
    calc
      _ ≤ (poissonLoads (2 ^ 63)).real
          {loads | threshold ≤ centeredLoadSum loads ^ 6} * threshold :=
        mul_le_mul_of_nonneg_right (measureReal_mono hsubset) ht.le
      _ ≤ ∫ loads, centeredLoadSum loads ^ 6 ∂poissonLoads (2 ^ 63) := by
        simpa only [mul_comm] using hmarkov
      _ ≤ bound := poisson_sixth_sum_bound
  have hscalar : bound / threshold < (1 : ℝ) / (16 * 2 ^ 128) := by
    norm_num [bound, threshold, gap]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  change (poissonLoads (2 ^ 63)).real {loads | (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads} ≤ _
  simpa using hprob.trans hscalar.le

set_option exponentiation.threshold 1024 in
/-- Uniform FORS loads exceed the cap with probability at most `1/(8*2^128)`. -/
theorem uniform_load_tail_nine_eighths_of_le
    (requests : Nat) (hrequests : requests ≤ 5 * 2 ^ 62) :
    uniformLoads (2 ^ 63) requests
      {loads | 9 * 2 ^ 99 < ∑ part, loads part ^ 14} ≤
        (1 : ℝ≥0∞) / (8 * 2 ^ 128) := by
  have hup : ∀ {a b : Fin (2 ^ 63) → Nat}, a ≤ b →
      (9 * 2 ^ 99 : ℝ) ≤ loadPotential a → (9 * 2 ^ 99 : ℝ) ≤ loadPotential b := by
    intro a b hab ha
    refine ha.trans (Finset.sum_le_sum (fun i _ => ?_))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (hab i)) 14
  have hcouple := uniformLoads_mul_poisson_tail_le (2 ^ 63) (5 * 2 ^ 62)
    {loads | (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads} hup
  have hhalf := mul_le_mul_right poisson_count_tail_extended_half
    (uniformLoads (2 ^ 63) (5 * 2 ^ 62) {loads | (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads})
  have hbound := hhalf.trans (hcouple.trans poisson_load_tail_nine_eighths)
  have htail : uniformLoads (2 ^ 63) (5 * 2 ^ 62)
      {loads | (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads} ≤ (1 : ENNReal) / (8 * 2 ^ 128) := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    have hreal := ENNReal.toReal_mono (by finiteness) hbound
    norm_num only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at hreal ⊢
    linarith
  have hsub : {loads : Fin (2 ^ 63) → Nat | 9 * 2 ^ 99 < ∑ i, loads i ^ 14} ⊆
      {loads | (9 * 2 ^ 99 : ℝ) ≤ loadPotential loads} := by
    intro loads hloads
    change (9 * 2 ^ 99 : ℝ) ≤ ∑ i, (loads i : ℝ) ^ 14
    exact_mod_cast Nat.le_of_lt hloads
  exact (measure_mono hsub).trans
    ((uniformLoads_monotone (2 ^ 63) _ hup hrequests).trans htail)

end SLHDSA.SHAKE128s.ForsConcentration

namespace SLHDSA.SHAKE128s.ForsDisclosureTape

private def swapTail {n : Nat} (a b : Instance) (tail : Tape n) : Tape n :=
  fun j => (Equiv.swap a b (tail j).1, (tail j).2)

private theorem swapTail_involutive (n : Nat) (a b : Instance) :
    Function.Involutive (swapTail (n := n) a b) := by
  intro tail
  funext j
  exact Prod.ext (Equiv.swap_apply_self _ _ _) rfl

private theorem loads_swapTail {n : Nat} (first second : View) (tail : Tape n)
    (i : Instance) :
    loads (Fin.cons second (swapTail first.1 second.1 tail))
      (Equiv.swap first.1 second.1 i) = loads (Fin.cons first tail) i := by
  unfold loads
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine Fin.cases ?_ (fun k => ?_) j
  · change second.1 = Equiv.swap first.1 second.1 i ↔ first.1 = i
    have hs := Equiv.swap_apply_left first.1 second.1
    calc second.1 = Equiv.swap first.1 second.1 i ↔
        Equiv.swap first.1 second.1 first.1 = Equiv.swap first.1 second.1 i := by
          rw [hs]
      _ ↔ first.1 = i := (Equiv.swap first.1 second.1).injective.eq_iff
  · exact (Equiv.swap first.1 second.1).injective.eq_iff

private theorem loadSum_swapTail {n : Nat} (first second : View) (tail : Tape n) :
    (∑ i, loads (Fin.cons second (swapTail first.1 second.1 tail)) i ^ 14) =
      ∑ i, loads (Fin.cons first tail) i ^ 14 := by
  classical
  exact Fintype.sum_equiv (Equiv.swap first.1 second.1)
    (fun i => loads (Fin.cons second (swapTail first.1 second.1 tail)) i ^ 14)
    (fun i => loads (Fin.cons first tail) i ^ 14) fun i => by
      have hi := loads_swapTail first second tail (Equiv.swap first.1 second.1 i)
      simpa only [Equiv.swap_apply_self] using congrArg (fun n : Nat => n ^ 14) hi

private theorem fixed_head_eq (remaining cutoff : Nat) (first second : View) :
    Pr{let tail ← ($ᵗ (Tape remaining) : ProbComp (Tape remaining))}[
      cutoff < ∑ i, loads (Fin.cons first tail) i ^ 14] =
    Pr{let tail ← ($ᵗ (Tape remaining) : ProbComp (Tape remaining))}[
      cutoff < ∑ i, loads (Fin.cons second tail) i ^ 14] := by
  rw [← SampleableType.prEvent_uniformSample_comp_of_bijective
    (swapTail_involutive remaining first.1 second.1).bijective
    (fun tail : Tape remaining => cutoff < ∑ i, loads (Fin.cons second tail) i ^ 14)]
  exact prEvent_congr _ _ _ fun tail => by rw [loadSum_swapTail]

private theorem view_cons_bijective (remaining : Nat) :
    Function.Bijective (fun pair : View × Tape remaining =>
      (Fin.cons pair.1 pair.2 : Tape (remaining + 1))) := by
  constructor
  · intro left right hsame
    have hhead := congrFun hsame 0
    have htail : ∀ index : Fin remaining, left.2 index = right.2 index := fun index => by
      have := congrFun hsame index.succ
      simpa using this
    exact Prod.ext (by simpa using hhead) (funext htail)
  · intro word
    exact ⟨(word 0, Fin.tail word), Fin.cons_self_tail word⟩

/-- Fixing the first digest view leaves a symmetric load-tail probability unchanged. -/
theorem prEvent_uniform_tail_load_gt_eq_uniform_tape
    (remaining cutoff : Nat) (first : View) :
    Pr{let tail ← ($ᵗ (Tape remaining) : ProbComp (Tape remaining))}[
      cutoff < ∑ part, loads (Fin.cons first tail) part ^ 14] =
    Pr{let tape ← ($ᵗ (Tape (remaining + 1)) : ProbComp (Tape (remaining + 1)))}[
      cutoff < ∑ part, loads tape part ^ 14] := by
  calc
    _ = Pr{let _ ← $ᵗ View; let tail ← $ᵗ (Tape remaining)}[
          cutoff < ∑ i, loads (Fin.cons first tail) i ^ 14] := by
      simpa only [map_bind] using (OracleComp.prEvent_bind_const ($ᵗ View)
        ((fun tail : Tape remaining => cutoff < ∑ i, loads (Fin.cons first tail) i ^ 14)
          <$> ($ᵗ (Tape remaining) : ProbComp (Tape remaining)))).symm
    _ = Pr{let head ← $ᵗ View; let tail ← $ᵗ (Tape remaining)}[
          cutoff < ∑ i, loads (Fin.cons head tail) i ^ 14] := by
      simpa only [map_bind] using prEvent_bind_congr_of_support ($ᵗ View)
        (fun _ => (fun tail : Tape remaining =>
          cutoff < ∑ i, loads (Fin.cons first tail) i ^ 14) <$> ($ᵗ (Tape remaining)))
        (fun head => (fun tail : Tape remaining =>
          cutoff < ∑ i, loads (Fin.cons head tail) i ^ 14) <$> ($ᵗ (Tape remaining)))
        (fun head _ => fixed_head_eq remaining cutoff first head)
    _ = _ := SampleableType.prEvent_uniformSample_pair_of_bijective
      (α := View) (β := Tape remaining) (γ := Tape (remaining + 1))
      (g := fun (head : View) (tail : Tape remaining) => Fin.cons head tail)
      (view_cons_bijective remaining)
      (fun tape : Tape (remaining + 1) => cutoff < ∑ i, loads tape i ^ 14)

end SLHDSA.SHAKE128s.ForsDisclosureTape

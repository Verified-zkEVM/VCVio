/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.Oracle.Compressed.LocalPotential
public import VCVio.Quantum.Comp.Potential

/-!
# A charged population potential for collision detection

The calibration `a_h = 1`, `b_h = t/h` of bounds-note (NOTE) equations (87)–(89), (91)
admits an explicit quadratic upper bound on its charged recursion. This schedule and its
7/4 coefficient formalize NOTE's refinement of ePrint 2025/2166 §9.3's collision-event
argument (Lemma 9.6, p. 61; event bound, pp. 64–65). The paper uses
the size projection, Corollaries 5.8/5.6, and a coefficient-80 per-database bound.
Corollaries 5.6 and 5.8 appear on pp. 31 and 33.
At call index `n > 0`, use `(t-n)c(c-1)/(2n)`; at index zero use `tc(c+1)/2`.
These functions are nonnegative and nondecreasing on integer populations, vanish at the
terminal index, and start at zero on the empty database. The per-call charge is `t/2`.
The population counts database entries only; recording registers are excluded.

`posSemidef_collisionCellDrop` and `posSemidef_collisionCellLeak` verify the local hypotheses.
`QuantumRuntime.eventWeight_le_of_collisionCertificate` specializes the general runtime
certificate to the finite coefficient `(7t+5)t/(4N)`, retaining the original mass through
`min w t`. The concrete collision predicate and the operator assembly for the old oracle
with extraction and recording are in `VCVio.Quantum.VC.Proof.Offline`; its theorem
`Quantum.collisionEvent_compressedVCOracle_le` supplies these trace hypotheses.
-/

public section

namespace Quantum

/-- The charged quadratic population potential, with zero-based call indices. -/
@[expose]
noncomputable def collisionPotential (t n c : ℕ) : ℝ :=
  if n = 0 then (t : ℝ) / 2 * c * (c + 1)
  else ((t - n : ℕ) : ℝ) / (2 * n) * c * (c - 1)

/-- A natural population has nonnegative second falling factorial. -/
theorem population_mul_pred_nonneg (c : ℕ) : 0 ≤ (c : ℝ) * (c - 1) := by
  rcases c with _ | c
  · norm_num
  · simp only [Nat.cast_succ, add_sub_cancel_right]
    positivity

/-- The population potential is nonnegative, including outside the call horizon. -/
theorem collisionPotential_nonneg (t n c : ℕ) : 0 ≤ collisionPotential t n c := by
  unfold collisionPotential
  split_ifs
  · positivity
  · rw [mul_assoc]
    exact mul_nonneg (by positivity) (population_mul_pred_nonneg c)

/-- The population potential is nondecreasing in the database population. -/
theorem collisionPotential_mono (t n : ℕ) : Monotone (collisionPotential t n) := by
  apply monotone_nat_of_le_succ
  intro c
  unfold collisionPotential
  split_ifs <;> push_cast
  · nlinarith [show 0 ≤ (t : ℝ) / 2 by positivity]
  · have hp : 0 ≤ ((t - n : ℕ) : ℝ) / (2 * n) := by positivity
    nlinarith [mul_nonneg hp (Nat.cast_nonneg' c)]

/-- The initial potential of an empty database is zero. -/
@[simp]
theorem collisionPotential_zero (t : ℕ) : collisionPotential t 0 0 = 0 := by
  simp [collisionPotential]

/-- The terminal potential vanishes on every database. -/
@[simp]
theorem collisionPotential_terminal (t c : ℕ) : collisionPotential t t c = 0 := by
  rcases t with _ | t <;> simp [collisionPotential]

/-- Consecutive integer distances have nonnegative product. -/
theorem population_gap_mul_succ_nonneg (n c : ℕ) :
    0 ≤ ((n : ℝ) - c) * (n + 1 - c) := by
  by_cases h : c ≤ n
  · have h' : (c : ℝ) ≤ n := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)
  · have h' : (n : ℝ) + 1 ≤ c := by exact_mod_cast (show n + 1 ≤ c by omega)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- The potential pays the growth reward and charge of equation (89). -/
theorem collisionPotential_growth {t n : ℕ} (hn : n < t) (c : ℕ) :
    (c : ℝ) + collisionPotential t (n + 1) (c + 1) ≤
      collisionPotential t n c + (t : ℝ) / 2 := by
  have ht : 1 ≤ t := by omega
  by_cases hzero : n = 0
  · subst n
    simp only [collisionPotential, Nat.succ_ne_zero, ite_false, ite_true,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, mul_one,
      add_sub_cancel_right, Nat.cast_sub ht]
    have hc := population_mul_pred_nonneg c
    nlinarith [show (0 : ℝ) ≤ t by positivity]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hzero)
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have heq : collisionPotential t n c + (t : ℝ) / 2 -
        ((c : ℝ) + collisionPotential t (n + 1) (c + 1)) =
        t * (((n : ℝ) - c) * (n + 1 - c)) / (2 * n * (n + 1)) := by
      simp only [collisionPotential, hzero, ite_false, Nat.succ_ne_zero,
        Nat.cast_sub (Nat.le_of_lt hn), Nat.cast_sub hn, Nat.cast_succ]
      field_simp
      ring
    have hpos : 0 ≤ (t : ℝ) * (((n : ℝ) - c) * (n + 1 - c)) /
        (2 * n * (n + 1)) :=
      div_nonneg (mul_nonneg (by positivity) (population_gap_mul_succ_nonneg n c))
        (by positivity)
    linarith

/-- The potential pays the filled-source reward and charge of equation (89). -/
theorem collisionPotential_stay {t n : ℕ} (hn : n < t) (c : ℕ) :
    ((t : ℝ) / (n + 1)) * c + collisionPotential t (n + 1) c ≤
      collisionPotential t n c + (t : ℝ) / 2 := by
  have heq : (c : ℝ) + collisionPotential t (n + 1) (c + 1) =
      ((t : ℝ) / (n + 1)) * c + collisionPotential t (n + 1) c := by
    simp only [collisionPotential, Nat.succ_ne_zero, ite_false, Nat.cast_sub hn,
      Nat.cast_succ]
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    field_simp
    ring
  rw [← heq]
  exact collisionPotential_growth hn c

/-- Idle, extraction, and recording operations need no charge when they preserve population. -/
theorem collisionPotential_idle {t n : ℕ} (hn : n < t) (c : ℕ) :
    collisionPotential t (n + 1) c ≤ collisionPotential t n c := by
  by_cases hzero : n = 0
  · subst n
    have ht : 1 ≤ t := by omega
    simp only [collisionPotential, Nat.succ_ne_zero, ite_false, ite_true,
      Nat.cast_one, Nat.cast_zero, zero_add, mul_one, Nat.cast_sub ht]
    have hc := population_mul_pred_nonneg c
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ t by positivity)
      (show (0 : ℝ) ≤ c by positivity)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hzero)
    have heq : collisionPotential t n c - collisionPotential t (n + 1) c =
        t / (2 * (n : ℝ) * (n + 1)) * (c * (c - 1)) := by
      simp only [collisionPotential, hzero, ite_false, Nat.succ_ne_zero,
        Nat.cast_sub (Nat.le_of_lt hn), Nat.cast_sub hn, Nat.cast_succ]
      field_simp
      ring
    have hpos : 0 ≤ (t : ℝ) / (2 * n * (n + 1)) * (c * (c - 1)) :=
      mul_nonneg (by positivity) (population_mul_pred_nonneg c)
    linarith

/-- The round-6 local rate, with zero-based call index and answer-space size `N`. -/
@[expose]
noncomputable def collisionRate (t n : ℕ) (N : ℝ) : ℝ :=
  (1 + 5 * (n + 1) / t) / N

/-- The collision rate is nonnegative for a nonnegative answer-space size. -/
theorem collisionRate_nonneg (t n : ℕ) {N : ℝ} (hN : 0 ≤ N) :
    0 ≤ collisionRate t n N := by unfold collisionRate; positivity

/-- The exact sum of the round-6 rates, equation (89). -/
theorem sum_collisionRate {t : ℕ} (ht : 0 < t) (N : ℝ) :
    ∑ n ∈ Finset.range t, collisionRate t n N = (7 * t + 5) / (2 * N) := by
  have hsum (k : ℕ) : (∑ n ∈ Finset.range k, ((n : ℝ) + 1)) = k * (k + 1) / 2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [collisionRate, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hsum]
  field_simp
  ring

/-- The charged potential and the rate sum give the finite `7/4` numerator. -/
theorem sum_collisionRate_mul_charge {t : ℕ} (ht : 0 < t) (N w : ℝ) :
    (∑ n ∈ Finset.range t, collisionRate t n N) * ((t : ℝ) / 2 * min w t) =
      (7 * t + 5) * t * min w t / (4 * N) := by
  rw [sum_collisionRate ht]
  ring

open Matrix
open scoped ComplexOrder

/-- The two-level potential at one queried cell, with `c` other occupied database entries. -/
@[expose]
noncomputable def collisionCellPotential (Y : Type*) [DecidableEq Y] (t n c : ℕ) :
    Matrix (Option Y) (Option Y) ℂ :=
  cellDiag (collisionPotential t n c) (collisionPotential t n (c + 1))

/-- A compressed query's potential drop dominates its empty/filled population reward.
This includes the charge `t/2` on that ordinary-query selector. -/
theorem posSemidef_collisionCellDrop {Y : Type*} [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (χ : AddChar Y ℂ) {t n : ℕ} (hn : n < t) (c : ℕ) :
    (collisionCellPotential Y t n c + ((t : ℝ) / 2) • 1 -
      (phaseCell Y χ)ᴴ * collisionCellPotential Y t (n + 1) c * phaseCell Y χ -
        cellDiag c ((t : ℝ) / (n + 1) * (c + 1))).PosSemidef := by
  have h₀ := collisionPotential_growth hn c
  have h₁ := collisionPotential_stay hn (c + 1)
  have hm := collisionPotential_mono t (n + 1) (Nat.le_succ c)
  have h := posSemidef_cellDrop χ
    (p₀ := collisionPotential t n c - c)
    (p₁ := collisionPotential t n (c + 1) - (t : ℝ) / (n + 1) * (c + 1))
    (u := collisionPotential t (n + 1) c)
    (v := collisionPotential t (n + 1) (c + 1))
    (θ := (t : ℝ) / 2) (by linarith) (by push_cast at h₁; linarith) hm
  have heq : (cellDiag (collisionPotential t n c - c)
      (collisionPotential t n (c + 1) - (t : ℝ) / (n + 1) * (c + 1)) :
      Matrix (Option Y) (Option Y) ℂ) = collisionCellPotential Y t n c -
        cellDiag c ((t : ℝ) / (n + 1) * (c + 1)) := by
    ext a b
    rcases a with _ | a <;>
      simp [collisionCellPotential, cellDiag, diagonal_apply, ite_sub_ite]
  rw [heq] at h
  convert h using 1
  dsimp [collisionCellPotential]
  abel

/-- Multiplying both values of a two-level potential multiplies its matrix. -/
theorem smul_cellDiag {Y : Type*} [DecidableEq Y] (r u v : ℝ) :
    r • (cellDiag u v : Matrix (Option Y) (Option Y) ℂ) = cellDiag (r * u) (r * v) := by
  ext a b
  rcases a with _ | a <;> simp [cellDiag, diagonal_apply, smul_ite]

/-- Coordinatewise ordering of two-level potentials is positive-operator ordering. -/
theorem posSemidef_cellDiag_sub {Y : Type*} [DecidableEq Y] {u v u' v' : ℝ}
    (hu : u' ≤ u) (hv : v' ≤ v) :
    ((cellDiag u v : Matrix (Option Y) (Option Y) ℂ) - cellDiag u' v').PosSemidef := by
  have heq : (cellDiag u v : Matrix (Option Y) (Option Y) ℂ) - cellDiag u' v' =
      cellDiag (u - u') (v - v') := by
    ext a b
    rcases a with _ | a <;> simp [cellDiag, diagonal_apply, ite_sub_ite]
  rw [heq]
  exact posSemidef_cellDiag (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)

/-- A binary event with at most `c` changing answers has its local leak paid by the
round-6 rate times the population reward. -/
theorem posSemidef_collisionCellLeak {Y : Type*} [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (χ : AddChar Y ℂ) (fl : Finset Y) {t n c : ℕ}
    (hn : n < t) (hfl : fl.card ≤ c) :
    (collisionRate t n (Fintype.card Y) •
        cellDiag c ((t : ℝ) / (n + 1) * (c + 1)) -
      (flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl)ᴴ *
        (flipCell fl * phaseCell Y χ - phaseCell Y χ * flipCell fl)).PosSemidef := by
  let N : ℝ := Fintype.card Y
  let β : ℝ := fl.card / N
  let b : ℝ := t / (n + 1)
  let r : ℝ := 1 + 5 * (n + 1) / t
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hb : 1 ≤ b := by
    apply (le_div_iff₀ hn1).mpr
    simpa only [one_mul] using
      (show (n : ℝ) + 1 ≤ t by exact_mod_cast (show n + 1 ≤ t by omega))
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hβ : 0 ≤ β := by positivity
  have hr : 0 ≤ r := by positivity
  have heq : 1⁻¹ + 5 * b⁻¹ = r := by
    simp only [b, r, inv_one, inv_div]
    ring
  have hl := posSemidef_smul_cellDiag_sub_flip χ fl
    (mul_nonneg hβ (by positivity : 0 ≤ 1⁻¹ + 5 * b⁻¹)) (by norm_num) hb0.le
    (leakBound_of_pos_of_le zero_lt_one hb hβ)
  rw [heq] at hl
  have hβc : β ≤ c / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hfl) hN.le
  have h₀ : β * r ≤ collisionRate t n N * c := by
    calc β * r ≤ (c / N) * r := mul_le_mul_of_nonneg_right hβc hr
      _ = _ := by dsimp [r, collisionRate]; ring
  have hlam : 0 ≤ collisionRate t n N := collisionRate_nonneg t n hN.le
  have h₁ : β * r * b ≤ collisionRate t n N * (b * (c + 1)) := by
    nlinarith [mul_le_mul_of_nonneg_right h₀ hb0.le, mul_nonneg hlam hb0.le]
  have hdiag := posSemidef_cellDiag_sub (Y := Y) h₀ h₁
  have he : collisionRate t n N • cellDiag c (b * (c + 1)) -
      (β * r) • (cellDiag 1 b : Matrix (Option Y) (Option Y) ℂ) =
      cellDiag (collisionRate t n N * c) (collisionRate t n N * (b * (c + 1))) -
        cellDiag (β * r) (β * r * b) := by rw [smul_cellDiag, smul_cellDiag, mul_one]
  rw [← he] at hdiag
  convert hdiag.add hl using 1
  dsimp [N, β, b]
  abel

/-! ## The charged event certificate -/

open scoped ENNReal Kronecker

namespace QuantumRuntime

variable {spec : QuantumOracleSpec} {L : LocalSig} (I : L.Interp)
  {X : QReg → Type*} {A D : QReg} {Z : Type*} [Fintype Z]
  {s : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  {Q : Matrix D D ℂ}

/-- The `7/4` numerical specialization of the runtime certificate, NOTE (87)–(89), (91).
This supports NOTE's refinement of the paper's §9.3 collision-event argument
(Lemma 9.6, p. 61; event bound, pp. 64–65). The hypotheses are local
trace inequalities, an initially zero potential and event, and a bound on the original mass.
Concrete compressed-oracle applications must establish these hypotheses for their database
population; this statement does not identify an arbitrary runtime with a compressed oracle. -/
theorem eventWeight_le_of_collisionCertificate
    (hU : ∀ i r, (s i).branch r = MatrixMap.conj (U i r))
    (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (σ₀ : SubState D)
    (x : QuantumComp L spec X A) {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (ports : Finset spec.Port) (hports : ∀ i ∉ ports, b i = 0)
    {t : ℕ} (ht : 0 < t) (hcount : ∑ i ∈ ports, b i ≤ t)
    (N : ℝ) (hN : 0 < N) (K : ℕ → Matrix Z D ℂ)
    (δ : ℕ → ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞)
    (mass : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞)
    (hdrop : ∀ n < t, ∀ i σ, σ.PosSemidef →
      δ n i σ + ∑' r, potential (K (n + 1)) ((s i).branch r σ) ≤
        potential (K n) σ + ENNReal.ofReal ((t : ℝ) / 2) * mass i σ)
    (hleak : ∀ n < t, ∀ i σ, σ.PosSemidef →
      ∑' r, ENNReal.ofReal (MatrixMap.conj ((1 ⊗ₖ Q) * U i r -
        U i r * (1 ⊗ₖ Q)) σ).trace.re ≤ ENNReal.ofReal (collisionRate t n N) * δ n i σ)
    {ρ : Matrix (A × D) (A × D) ℂ} (hρ : ρ.PosSemidef)
    (hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ = 0)
    (hinit : potential (K 0) ρ = 0) (w : ℝ≥0∞)
    (hmass : ∑ n ∈ Finset.range t,
      (QuantumRuntime.mk D σ₀ s).queryWeight I mass x ρ n ≤ min w t) :
    (QuantumRuntime.mk D σ₀ s).eventWeight I Q x ρ ≤
      ENNReal.ofReal ((7 * t + 5) * t / (4 * N)) * min w t := by
  have h := eventWeight_le_of_potential I hU hQ hQQ σ₀ x hx ports hports hcount K δ
    (fun _ i σ ↦ ENNReal.ofReal ((t : ℝ) / 2) * mass i σ)
    (fun n ↦ ENNReal.ofReal (collisionRate t n N)) hdrop hleak hρ hρQ
  have hsum : (∑ n ∈ Finset.range t, ENNReal.ofReal (collisionRate t n N)) =
      ENNReal.ofReal ((7 * t + 5) / (2 * N)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ ↦ collisionRate_nonneg t n hN.le),
      sum_collisionRate ht]
  simp only [hinit, zero_add, queryWeight_const_mul, ← Finset.mul_sum, hsum] at h
  refine h.trans ?_
  calc _ ≤ ENNReal.ofReal ((7 * t + 5) / (2 * N)) *
        (ENNReal.ofReal ((t : ℝ) / 2) * min w t) := by gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      ring

end QuantumRuntime

end Quantum

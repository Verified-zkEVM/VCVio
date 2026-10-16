/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Salted.Instability
public import VCVio.Quantum.VC.Proof.OnlineSecurity

/-!
# Joint-label instability for salted Merkle recording

A list of `n` recorded extraction keys contributes at most `n` roots at an affected oracle.
All keys share the same half-preimage set, giving the bound `(n + 2 * D.size) / |Y|`.
The empty list has zero instability. No collision-freeness hypothesis is needed.

These bounds prove online indistinguishability as in ePrint 2025/2166, Lemma 9.7, pp. 65–70.
The sharper
joint-budget count and the time-dependent sum are from the bounds note, equations (24)–(25)
and (30), and the repair note, equation (2). The final theorem includes the probability cap.
-/

public section

open Quantum OracleSpec
open scoped ENNReal

namespace SaltedMerkle

variable {Y : Type} [LinearOrder Y] {k : ℕ}

/-- The roots of a valid extraction tuple at one affected oracle. Repeated-index tuples have
constant extraction output, so they contribute no roots. -/
@[expose]
noncomputable def onlineRoots (tic : TpIC k Y) (j : Fin k) : Finset Y :=
  open Classical in
  if Function.Injective tic.idx then
    (Finset.univ.filter fun i ↦ (tic.2 i).1 = j).image fun i ↦ (tic.2 i).2
  else ∅

/-- Each extraction tuple contributes at most one root at an affected oracle. -/
theorem card_onlineRoots_le (tic : TpIC k Y) (j : Fin k) : (onlineRoots tic j).card ≤ 1 := by
  classical
  unfold onlineRoots
  split_ifs with hinj
  · refine Finset.card_le_one.mpr ?_
    intro y hy z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
    have he : a = b := hinj ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    rw [he]
  · simp

/-- A list of extraction keys has at most as many relevant roots as keys. -/
theorem card_biUnion_onlineRoots_le {n : ℕ} (tics : Fin n → TpIC k Y) (j : Fin k) :
    (Finset.univ.biUnion fun a ↦ onlineRoots (tics a) j).card ≤ n := by
  classical
  calc _ ≤ ∑ a : Fin n, (onlineRoots (tics a) j).card := Finset.card_biUnion_le
    _ ≤ ∑ _a : Fin n, 1 := Finset.sum_le_sum fun a _ ↦ card_onlineRoots_le (tics a) j
    _ = n := by simp

variable {X Msg Salt : Type} [DecidableEq X] [Fintype Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  (enc : Encoding X Y Msg Salt) (d : Fin k → ℕ)

/-- A fresh answer outside the relevant roots and shared half-preimages preserves every
extraction in a list, including tuples with repeated indices. -/
theorem onlineLabel_list_update_eq {n : ℕ} (tics : Fin n → TpIC k Y)
    (Dfix : Fin k → Database X Y) (j : Fin k) (D : Database X Y) (x : X) (y : Y)
    (hx : D x = none) (hy : y ∉ halfPreimages enc D)
    (hroot : ∀ a, y ∉ onlineRoots (tics a) j) :
    onlineLabel (multiExtract enc d) tics Dfix j (Function.update D x (some y)) =
      onlineLabel (multiExtract enc d) tics Dfix j D := by
  classical
  funext a
  by_cases hinj : Function.Injective (tics a).idx
  · have hs (i : Fin (tics a).1.len) (hi : ((tics a).2 i).1 = j) :
        y ∉ insert ((tics a).2 i).2 (halfPreimages enc D) := by
      simp only [Set.mem_insert_iff, not_or]
      refine ⟨?_, hy⟩
      intro he
      apply hroot a
      simp only [onlineRoots, hinj, ↓reduceIte]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, he.symm⟩
    have h := multiExtract_update_eq enc d (tics a) (Function.update Dfix j D) j
      (by simpa using hx) (by simpa using hs)
    simpa [onlineLabel, Function.update_idem] using h
  · simp [onlineLabel, multiExtract, hinj]

open scoped Classical in
/-- A list of `n` keys shares its half-preimage contribution: its changing answers number at
most `n + 2 * D.size`, rather than `n * (1 + 2 * D.size)`. -/
theorem card_onlineLabel_list_changes_le [Fintype X] {n : ℕ} (tics : Fin n → TpIC k Y)
    (Dfix : Fin k → Database X Y) (j : Fin k) (D : Database X Y) (x : X)
    (hx : D x = none) :
    (Finset.univ.filter fun y : Y ↦
      onlineLabel (multiExtract enc d) tics Dfix j (Function.update D x (some y)) ≠
        onlineLabel (multiExtract enc d) tics Dfix j D).card ≤ n + 2 * D.size := by
  classical
  let roots := Finset.univ.biUnion fun a ↦ onlineRoots (tics a) j
  have hsub : (Finset.univ.filter fun y : Y ↦
      onlineLabel (multiExtract enc d) tics Dfix j (Function.update D x (some y)) ≠
        onlineLabel (multiExtract enc d) tics Dfix j D) ⊆
        roots ∪ (halfPreimages enc D).toFinset := by
    intro y hy
    by_contra hn
    simp only [Finset.mem_union, Set.mem_toFinset, not_or] at hn
    apply (Finset.mem_filter.mp hy).2
    apply onlineLabel_list_update_eq enc d tics Dfix j D x y hx hn.2
    intro a ha
    exact hn.1 (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, ha⟩)
  have hh := ncard_halfPreimages_le_of_finite enc D
  rw [ncard_support_eq_size, Set.ncard_eq_toFinset_card'] at hh
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (card_biUnion_onlineRoots_le tics j) hh))

/-- The joint-label instability for `n` extraction keys at databases of size at most `s`. -/
theorem instability_onlineLabel_list_le [Finite X] [UniformAnswerMeasure (X →ₒ Y)]
    {n : ℕ} (tics : Fin n → TpIC k Y) (Dfix : Fin k → Database X Y)
    (j : Fin k) (s : ℕ) :
    Database.instability (onlineLabel (multiExtract enc d) tics Dfix j) (s + 1) ≤
      min 1 ((n + 2 * s : ℝ≥0∞) / Fintype.card Y) := by
  classical
  let _ := Fintype.ofFinite X
  refine le_min (Database.instability_le_one _ _) ?_
  rw [Database.instability_eq_iSup]
  refine iSup_le fun l ↦ iSup_le fun D ↦ iSup_le fun hl ↦ iSup_le fun hD ↦
    iSup_le fun x ↦ iSup_le fun hx ↦ ?_
  subst l
  have hc := card_onlineLabel_list_changes_le enc d tics Dfix j D x hx
  have hs : D.size ≤ s := by omega
  have hc' : (Finset.univ.filter fun y : Y ↦
      onlineLabel (multiExtract enc d) tics Dfix j (Function.update D x (some y)) ≠
        onlineLabel (multiExtract enc d) tics Dfix j D).card ≤ n + 2 * s := by omega
  gcongr
  exact_mod_cast hc'

/-- The empty list has zero instability at every population bound. -/
theorem instability_onlineLabel_empty [AnswerMeasure (X →ₒ Y)]
    (tics : Fin 0 → TpIC k Y) (Dfix : Fin k → Database X Y) (j : Fin k) (s : ℕ) :
    Database.instability (onlineLabel (multiExtract enc d) tics Dfix j) s = 0 := by
  have he : onlineLabel (multiExtract enc d) tics Dfix j =
      fun _ : Database X Y ↦ fun a : Fin 0 ↦ Fin.elim0 a := by
    funext D a
    exact Fin.elim0 a
  rw [he, Database.instability_const]

/-- The joint-budget arithmetic in the bounds note, equation (30): a nonempty record set
and the remaining database fit into the budget before the active query. -/
theorem online_joint_count_le {n r h : ℕ} (hn : 1 ≤ n) (hcost : r + n ≤ h - 1) :
    n + 2 * r ≤ 2 * h - 3 := by
  omega

/-- The list instability at a joint database/record budget. The zero database cutoff is
included, and a nonempty list uses the odd coefficient from the bounds note, equation (30). -/
theorem instability_onlineLabel_list_le_jointBudget [Finite X]
    [UniformAnswerMeasure (X →ₒ Y)] {n s h : ℕ} (tics : Fin n → TpIC k Y)
    (Dfix : Fin k → Database X Y) (j : Fin k) (hn : 1 ≤ n) (hcost : s + n ≤ h) :
    Database.instability (onlineLabel (multiExtract enc d) tics Dfix j) s ≤
      min 1 ((2 * h - 3 : ℕ) / (Fintype.card Y : ℝ≥0∞)) := by
  cases s with
  | zero => simp only [Database.instability_zero]; exact zero_le
  | succ s =>
    refine (instability_onlineLabel_list_le enc d tics Dfix j s).trans ?_
    apply min_le_min le_rfl
    have hc := online_joint_count_le hn (show s + n ≤ h - 1 by omega)
    gcongr
    exact_mod_cast hc

section operatorBound

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

variable [Fintype X] [AddCommGroup Y] [UniformAnswerMeasure (X →ₒ Y)]
  {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The generalized commutator on a joint-budget block has squared norm at most
`24*(2*h-3)/|Y|`. The controls may act on the entire block: their label preservation,
unitarity, and commutation with the truncated oracle are explicit hypotheses.
The coefficient 24 is from the bounds note, equation (30), and the repair note, equation (2),
using ePrint 2025/2166, Theorem 5.4, p. 31, in its generalized form. -/
theorem l2_opNorm_online_commutator_sq_le {n s h : ℕ} (tics : Fin n → TpIC k Y)
    (Dfix : Fin k → Database X Y) (j : Fin k) (hn : 1 ≤ n) (hcost : s + n ≤ h)
    (W : (∀ a : Fin n,
      TpDLen k (DmOf (fun i ↦ 2 ^ d i) Msg fun i ↦ Td Y Salt (d i)) (tics a).1) →
        Matrix (((X × Y) × Database X Y) × Aux) (((X × Y) × Database X Y) × Aux) ℂ)
    (hW : ∀ l a b, W l a b ≠ 0 →
      onlineLabel (multiExtract enc d) tics Dfix j a.1.2 =
        onlineLabel (multiExtract enc d) tics Dfix j b.1.2)
    (hU : ∀ l, W l ∈ unitaryGroup _ ℂ)
    (hA : ∀ l, W l * (truncatedOracle X Y s ⊗ₖ (1 : Matrix Aux Aux ℂ)) =
      (truncatedOracle X Y s ⊗ₖ (1 : Matrix Aux Aux ℂ)) * W l) :
    ‖labelControlled (fun a ↦ onlineLabel (multiExtract enc d) tics Dfix j a.1.2) W *
          (truncatedOracle X Y s ⊗ₖ (1 : Matrix Aux Aux ℂ)) -
        (truncatedOracle X Y s ⊗ₖ (1 : Matrix Aux Aux ℂ)) *
          labelControlled (fun a ↦ onlineLabel (multiExtract enc d) tics Dfix j a.1.2) W‖ ^ 2 ≤
      24 * (2 * h - 3 : ℕ) / (Fintype.card Y : ℝ) := by
  have hi := (instability_onlineLabel_list_le_jointBudget enc d tics Dfix j hn hcost).trans
    (min_le_right _ _)
  have hr := ENNReal.toReal_mono (by finiteness) hi
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hr
  have hc := l2_opNorm_commutator_truncatedOracle_sq_le_twentyFour_mul
    (onlineLabel (multiExtract enc d) tics Dfix j) s hW hU hA
  apply hc.trans
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 24)

end operatorBound

end SaltedMerkle

namespace Quantum

/-- The local weight of the query at zero-based position `j`. The first query has weight zero;
the later weights are the odd numbers in the bounds note, equation (30). -/
@[expose]
def onlineStepWeight (j : ℕ) : ℕ := 2 * j - 1

/-- The time-dependent local weights sum to the square of the number of later queries. -/
theorem sum_onlineStepWeight (t : ℕ) :
    ∑ j ∈ Finset.range t, onlineStepWeight j = (t - 1) ^ 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    unfold onlineStepWeight
    cases t with
    | zero => norm_num
    | succ t =>
      simp only [Nat.add_sub_cancel]
      have he : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
      rw [he]
      ring

/-- Weighted Cauchy–Schwarz gives the exact constant in the bounds note, equation (30).
The masses are arbitrary nonnegative reals; relating them to a recording execution is a
separate operator argument. -/
theorem online_weighted_sum_sq_le (t : ℕ) (mass : ℕ → ℝ) (hmass : ∀ j, 0 ≤ mass j)
    (w N : ℝ) (hN : 0 < N) (hw : ∑ j ∈ Finset.range t, mass j ≤ w) :
    (24 / N) * (∑ j ∈ Finset.range t,
      Real.sqrt ((onlineStepWeight j : ℝ) * mass j)) ^ 2 ≤
      24 * w * (t - 1 : ℕ) ^ 2 / N := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range t)
    (fun j ↦ Real.sqrt (onlineStepWeight j)) (fun j ↦ Real.sqrt (mass j))
  simp only [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (hmass _)] at hc
  have he : ∑ j ∈ Finset.range t, (onlineStepWeight j : ℝ) = (t - 1 : ℕ) ^ 2 := by
    exact_mod_cast sum_onlineStepWeight t
  rw [he] at hc
  simp only [← Real.sqrt_mul (Nat.cast_nonneg _)] at hc
  calc
    _ ≤ (24 / N) * ((t - 1 : ℕ) ^ 2 * w) := by
      gcongr
      exact hc.trans (mul_le_mul_of_nonneg_left hw (by positivity))
    _ = _ := by ring

/-- The square-root accumulation in extended nonnegative reals, including infinite mass
bounds. Its coefficient and odd-weight schedule are the bounds note, equation (30). -/
theorem online_weighted_rpow_sum_le (t N : ℕ) (mass : ℕ → ℝ≥0∞) (w : ℝ≥0∞)
    (hw : ∑ j ∈ Finset.range t, mass j ≤ w) :
    ∑ j ∈ Finset.range t, ((24 / N : ℝ≥0∞) * onlineStepWeight j * mass j) ^ (2⁻¹ : ℝ) ≤
      (24 * w * (t - 1 : ℕ) ^ 2 / N) ^ (2⁻¹ : ℝ) := by
  have hc := ENNReal.inner_le_Lp_mul_Lq (Finset.range t)
    (fun j ↦ ((24 / N : ℝ≥0∞) * onlineStepWeight j) ^ (2⁻¹ : ℝ))
    (fun j ↦ mass j ^ (2⁻¹ : ℝ)) Real.HolderConjugate.two_two
  simp only [rpow_inv_two_rpow_two, one_div] at hc
  simp_rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)] at hc
  have he : ∑ j ∈ Finset.range t, (onlineStepWeight j : ℝ≥0∞) = (t - 1 : ℕ) ^ 2 := by
    exact_mod_cast sum_onlineStepWeight t
  rw [← Finset.mul_sum, he] at hc
  refine hc.trans ?_
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  calc
    _ ≤ (24 / N : ℝ≥0∞) * (t - 1 : ℕ) ^ 2 * w := by gcongr
    _ = _ := by simp only [div_eq_mul_inv]; ac_rfl

/-- The exact sum of real local rates, converted to the extended nonnegative reals used
by runtime query weights. The hash range has positive cardinality. -/
theorem sum_onlineRate {N : ℕ} (hN : 0 < N) (t : ℕ) :
    ∑ j ∈ Finset.range t, ENNReal.ofReal (24 * (onlineStepWeight j : ℝ) / N) =
      (24 * (t - 1 : ℕ) ^ 2 / N : ℝ≥0∞) := by
  have hr (j : ℕ) : ENNReal.ofReal (24 * (onlineStepWeight j : ℝ) / N) =
      (24 * onlineStepWeight j / N : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_mul (by norm_num)]
    simp
  simp_rw [hr, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  exact_mod_cast sum_onlineStepWeight t

open Matrix
open scoped Kronecker ComplexOrder

/-- Time-dependent discrepancy weights along an actual coherent execution have the exact
online square-root bound of the bounds note, equation (30). The port hypothesis is a local
squared operator bound on inputs of grade `j`; it does not assume an execution comparison.
Applying it to the recording swap requires discharging this operator hypothesis. -/
theorem EmulatedOracle.tsum_rpow_queryWeight_conj_le_online
    {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} (E : EmulatedOracle P In)
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (EmulatedOracle.cohSpec In) W A} {t N : ℕ} (hN : 0 < N)
    (hx : x.IsQueryBound fun _ ↦ t) {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : ρ.PosSemidef)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic 0) ρ)
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ) (selected : P → Bool)
    (hC : ∀ j < t, ∀ p,
      ((if selected p then 24 * (onlineStepWeight j : ℝ) / N else 0) •
          (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))ᴴ *
          (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))).PosSemidef) :
    ∑' j, E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (EmulatedOracle.coherentBlocks C) σ).trace.re)
        x ρ j ^ (2⁻¹ : ℝ) ≤
      (24 * E.selectedTotalMass I selected x ρ * (t - 1 : ℕ) ^ 2 / N) ^ (2⁻¹ : ℝ) := by
  have h := E.tsum_rpow_queryWeight_conj_le_of_grade g hE I hx hρ hgrade C selected
    (fun j ↦ 24 * (onlineStepWeight j : ℝ) / N) (fun j _ ↦ by positivity) hC
  rw [sum_onlineRate hN] at h
  refine h.trans_eq ?_
  congr 1
  simp only [div_eq_mul_inv]
  ac_rfl

/-- The capped numerical online error from the bounds note, equation (30), and the repair
note, equation (2). The final `SaltedMerkle.merkle_online` theorem attains this error. -/
@[expose]
noncomputable def merkleOnlineError (N t : ℕ) (w : ℝ≥0∞) : ℝ≥0∞ :=
  min 1 (24 * w * (t - 1 : ℕ) ^ 2 / N)

/-- The numerical error is always at most one. -/
theorem merkleOnlineError_le_one (N t : ℕ) (w : ℝ≥0∞) : merkleOnlineError N t w ≤ 1 :=
  min_le_left _ _

/-- Zero queries have zero numerical online error, including infinite mass budgets. -/
@[simp]
theorem merkleOnlineError_zero (N : ℕ) (w : ℝ≥0∞) : merkleOnlineError N 0 w = 0 := by
  simp [merkleOnlineError]

/-- A single query has zero numerical online error, including infinite mass budgets. -/
@[simp]
theorem merkleOnlineError_one (N : ℕ) (w : ℝ≥0∞) : merkleOnlineError N 1 w = 0 := by
  simp [merkleOnlineError]

end Quantum

namespace SaltedMerkle
variable {X Y Msg Salt : Type} {k : ℕ} [DecidableEq X] [Finite X] [LinearOrder Y]
  [Fintype Y] [Nonempty Y] [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  [UniformAnswerMeasure (X →ₒ Y)]
/-- Finite occupied-key sets satisfy the joint-budget instability bound. The coefficient
24 and odd schedule are the bounds note, equation (30), and the repair note, equation (2). -/
theorem instability_online_keys_le (enc : Encoding X Y Msg Salt) (d : Fin k → ℕ)
    (keys : Finset (TpIC k Y)) (Dfix : Fin k → Database X Y) (i : Fin k)
    (t : ℕ) (hn : 1 ≤ keys.card) (ht : keys.card ≤ t) :
    24 * (Database.instability
      (fun D ↦ fun q : keys ↦ (multiExtract enc d).extract q.1 (Function.update Dfix i D))
      (t - keys.card + 1)).toReal ≤ 24 * (onlineStepWeight t : ℝ) / Fintype.card Y := by
  classical
  let tics : Fin keys.card → TpIC k Y := fun a ↦ (keys.equivFin.symm a).1
  have hc := Database.instability_le_of_eq_imp
    (fun D ↦ fun q : keys ↦ (multiExtract enc d).extract q.1 (Function.update Dfix i D))
    (onlineLabel (multiExtract enc d) tics Dfix i) (fun D D' h ↦ ?_) (t - keys.card + 1)
  · have hb := (instability_onlineLabel_list_le_jointBudget enc d tics Dfix i hn
        (h := t + 1) (s := t - keys.card + 1) (by omega)).trans (min_le_right _ _)
    have hr := ENNReal.toReal_mono (by finiteness) (hc.trans hb)
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hr
    have he : 2 * (t + 1) - 3 = onlineStepWeight t := by unfold onlineStepWeight; omega
    rw [he] at hr
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 24)
  · funext q
    obtain ⟨a, rfl⟩ := keys.equivFin.symm.surjective q
    exact congrFun h a
end SaltedMerkle

namespace SaltedMerkle
universe v w
variable {X Y Msg Salt Z : Type} {k : ℕ} [Fintype X] [DecidableEq X]
  [Fintype Y] [LinearOrder Y] [AddCommGroup Y]
  [Fintype Msg] [LinearOrder Msg] [Fintype Salt] [LinearOrder Salt]
  [Fintype Z] [DecidableEq Z] [AddGroup Z]
  [UniformAnswerMeasure (X →ₒ Y)]
open scoped Classical in
/-- Salted Merkle recording satisfies P5 with error
`min 1 (24 * wVC * (t - 1)^2 / |Y|)` in its two-sided square-root form.
The coefficient 24 and joint-budget schedule are the bounds note, equation (30), and the
repair note, equation (2). This instantiates ePrint 2025/2166, Definition 7.3, P5, pp. 50–51,
and Lemma 9.7, pp. 65–70, for arbitrary coherent adaptive programs, local instruments and
subnormalized workspace states. No collision-freeness assumption is required. -/
theorem merkle_online (enc : Encoding X Y Msg Salt) (d : Fin k → ℕ)
    (code : TpDCode k (DmOf (fun i ↦ 2 ^ d i) Msg fun i ↦ Td Y Salt (d i)) Z) :
    OnlineIndistinguishable.{v, w} (compressedVCOracle k X Y) (multiExtract enc d) code
      (fun t wVC _ _ ↦ merkleOnlineError (Fintype.card Y) t wVC) := by
  have h := compressed_online_of_instability.{v, w} (multiExtract enc d) code
    (fun j ↦ 24 * (onlineStepWeight j : ℝ) / Fintype.card Y) (fun _ ↦ by positivity)
    (fun t i keys hn ht Dfix ↦ instability_online_keys_le enc d keys Dfix i t hn ht)
  apply h.mono
  intro t wVC wME wRec
  dsimp only
  rw [sum_onlineRate (Fintype.card_pos (α := Y))]
  unfold merkleOnlineError
  apply le_of_eq
  congr 1
  simp only [div_eq_mul_inv]
  ac_rfl
end SaltedMerkle

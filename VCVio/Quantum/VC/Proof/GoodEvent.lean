/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Quantum.VC.Proof.Offline
import VCVio.Quantum.Oracle.Compressed.BinaryPartition
import VCVio.Quantum.Oracle.Compressed.ProjectorEvent

/-!
# Good database events before verification

The ordinary/extraction execution preserves good databases except at ordinary oracle calls.
The event weight on its final state is bounded by `24 t min(w,t) I_off(t)`, with total
call budget `t` and ordinary mass `w`. The family projector also identifies the collision
bound as an alternative input to offline extractability.
-/

public section

open Matrix Quantum.EmulatedOracle OracleSpec
open scoped Kronecker ComplexOrder ENNReal Matrix.Norms.L2Operator

namespace Quantum

section projectors

variable {k : ℕ} {X Y : Type} [Fintype X] [DecidableEq Y]

/-- The compressed-basis projector onto families in which every database is good. -/
@[expose]
noncomputable def familyGoodProjector (Pgood : Set (Database X Y))
    [DecidablePred (· ∈ Pgood)] : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  labelProjector (fun D ↦ decide (∀ i, D i ∈ Pgood)) true

/-- The event that at least one database is bad, before any challenger reads. -/
@[expose]
noncomputable def familyBadProjector (Pgood : Set (Database X Y))
    [DecidablePred (· ∈ Pgood)] : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ :=
  labelProjector (fun D ↦ decide (∀ i, D i ∈ Pgood)) false

/-- Bad and good are complementary compressed-basis events. -/
theorem familyBadProjector_eq_one_sub (Pgood : Set (Database X Y))
    [DecidablePred (· ∈ Pgood)] :
    familyBadProjector (k := k) Pgood = 1 - familyGoodProjector Pgood := by
  exact (one_sub_labelProjector_bool _ true).symm

/-- The good-database event is an orthogonal projection. -/
theorem isStarProjection_familyGoodProjector (Pgood : Set (Database X Y))
    [DecidablePred (· ∈ Pgood)] [DecidableEq X] [Fintype Y] :
    IsStarProjection (familyGoodProjector (k := k) Pgood) :=
  isStarProjection_labelProjector _ _

/-- The bad-database event is an orthogonal projection. -/
theorem isStarProjection_familyBadProjector (Pgood : Set (Database X Y))
    [DecidablePred (· ∈ Pgood)] [DecidableEq X] [Fintype Y] :
    IsStarProjection (familyBadProjector (k := k) Pgood) :=
  isStarProjection_labelProjector _ _

/-- For collision-free databases, the bad event is the canonical family collision event. -/
theorem familyBadProjector_collisionFree
    [DecidablePred (fun D : Database X Y ↦ D.CollisionFree)] :
    familyBadProjector (k := k) {D : Database X Y | D.CollisionFree} =
      familyCollisionProjector (k := k) (X := X) (Y := Y) := by
  classical
  rw [familyBadProjector, familyCollisionProjector, labelProjector, labelProjector]
  congr 1
  funext D
  by_cases h : ∀ i, (D i).CollisionFree <;>
    simp [Database.allCollisionLabel, Database.AllCollisionFree, h]

end projectors

section localBound

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [UniformAnswerMeasure (X →ₒ Y)]

private theorem label_commutator_bound (π : Database X Y → Bool) (n : ℕ) :
    let Q := labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) false
    ‖Q * truncatedOracle X Y n - truncatedOracle X Y n * Q‖ ^ 2 ≤
      24 * (Database.instability π n).toReal := by
  exact (l2_opNorm_labelProjector_commutator_truncatedOracle_sq_le_six_mul π n false).trans
    (mul_le_mul_of_nonneg_right (by norm_num) ENNReal.toReal_nonneg)

private theorem label_source_bound (π : Database X Y → Bool) (n : ℕ) :
    let Q := labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) false
    ‖(Q * compressedOracle X Y - compressedOracle X Y * Q) * sizeProjector X Y n‖ ^ 2 ≤
      24 * (Database.instability π (n + 1)).toReal := by
  dsimp only
  let Q := labelProjector (fun m : (X × Y) × Database X Y ↦ π m.2) false (α := ℂ)
  have he : (Q * compressedOracle X Y - compressedOracle X Y * Q) * sizeProjector X Y n =
      (Q * truncatedOracle X Y (n + 1) - truncatedOracle X Y (n + 1) * Q) *
        sizeProjector X Y n := by
    ext a b
    simp only [Q, labelProjector, Matrix.sub_apply, diagonal_mul, mul_diagonal,
      sizeProjector, truncatedOracle]
    by_cases hb : b.2.size ≤ n
    · by_cases hz : compressedOracle X Y a b = 0
      · simp [hz]
      · have ha := (size_le_of_compressedOracle_apply_ne_zero hz).trans (Nat.add_le_add_right hb 1)
        simp [hb, ha, Nat.le_succ_of_le hb]
    · simp [hb]
  have hp := l2_opNorm_sizeProjector_le_one (X := X) (Y := Y) n
  rw [he]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    ((l2_opNorm_mul _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hp)) 2).trans
      (label_commutator_bound π (n + 1))

end localBound

namespace EmulatedOracle

section chargedComparison

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg}
  (E : EmulatedOracle P In)

/-- A grade-restricted squared port bound controls the discrepancy weight at an actual query
prefix by its selected coherent input mass. The bound is tested at grade `t+j`, so it can
vary with time without changing the execution or measuring the recording register. -/
private theorem queryWeight_conj_le_selectedMass_of_grade
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec In) W A) {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : ρ.PosSemidef) (t j : ℕ)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic t) ρ)
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (selected : P → Bool) {r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ p,
      ((if selected p then r else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ t + j then (1 : ℂ) else 0))ᴴ *
          (C p * (1 ⊗ₖ diagonal fun d ↦
          if g d ≤ t + j then (1 : ℂ) else 0))).PosSemidef) :
    E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) x ρ j ≤
      ENNReal.ofReal r * E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ E.selectedMass selected σ) x ρ j := by
  rw [← QuantumRuntime.queryWeight_const_mul]
  refine E.coherent.toRuntime.queryWeight_mono_of_grade I g
    (E.coherent.querySupportedOn_toRuntime_step g (E.coherent_U_grade g hE))
    x hρ t j hgrade fun _ σ hσ hsupp ↦ ?_
  refine E.ofReal_trace_coherentBlocks_conj_le_selectedMass C _ selected hr hC hσ ?_
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  exact hsupp.conj_diagonal_eq_self fun m hm ↦ by simp [Set.mem_Iic.mp hm]

/-- A time-dependent family of grade-restricted port bounds accumulates against the actual
selected query mass. This is the Cauchy–Schwarz step of the online hybrid, before identifying
the discrepancy operators with a recording-swap comparison. -/
private theorem tsum_rpow_queryWeight_conj_le_of_grade
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (cohSpec In) W A} {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic 0) ρ)
    (C : ∀ p, Matrix (In p × E.S) (In p × E.S) ℂ)
    (selected : P → Bool) (r : ℕ → ℝ) (hr : ∀ j < t, 0 ≤ r j)
    (hC : ∀ j < t, ∀ p,
      ((if selected p then r j else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))ᴴ *
          (C p * (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0))).PosSemidef) :
    ∑' j, E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) x ρ j ^
          (2⁻¹ : ℝ) ≤
      ((∑ j ∈ Finset.range t, ENNReal.ofReal (r j)) *
        min (E.selectedTotalMass I selected x ρ) t) ^ (2⁻¹ : ℝ) := by
  let m := fun j ↦ E.coherent.toRuntime.queryWeight I
    (fun _ σ ↦ E.selectedMass selected σ) x ρ j
  have hz : ∀ j ∉ Finset.range t,
      E.coherent.toRuntime.queryWeight I
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) x ρ j ^
          (2⁻¹ : ℝ) = 0 := by
    intro j hj
    rw [E.coherent.toRuntime.queryWeight_eq_zero_of_isQueryBound I hx Finset.univ
      (by simp) (by simpa using hj) ρ, ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz]
  calc
    _ ≤ ∑ j ∈ Finset.range t, ENNReal.ofReal (r j) ^ (2⁻¹ : ℝ) * m j ^ (2⁻¹ : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact E.queryWeight_conj_le_selectedMass_of_grade g hE I x hρ 0 j hgrade C selected
        (hr j (Finset.mem_range.mp hj)) (by simpa using hC j (Finset.mem_range.mp hj))
    _ ≤ _ := by
      refine (ENNReal.inner_le_Lp_mul_Lq _ _ _ Real.HolderConjugate.two_two).trans ?_
      simp only [rpow_inv_two_rpow_two, one_div]
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      gcongr
      exact E.sum_queryWeight_selectedMass_le I selected (hx ()) hρ htr


private theorem eventWeight_le_of_graded_commutators
    (g : E.S → ℕ)
    (hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 → g d' ≤ g d + 1)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    {x : QuantumComp L (cohSpec In) W A} {t : ℕ} (hx : x.IsQueryBound fun _ ↦ t)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (hgrade : QuerySupportedOn (fun m : A × E.S ↦ g m.2) (Set.Iic 0) ρ)
    (Q : Matrix E.S E.S ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q)
    (hρQ : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q) ρ = 0)
    (selected : P → Bool) {r : ℝ} (hr : 0 ≤ r)
    (hC : ∀ j < t, ∀ p,
      let C := ((1 ⊗ₖ Q) * E.U p - E.U p * (1 ⊗ₖ Q)) *
        (1 ⊗ₖ diagonal fun d ↦ if g d ≤ j then (1 : ℂ) else 0)
      ((if selected p then r else 0) • (1 : Matrix (In p × E.S) (In p × E.S) ℂ) -
        Cᴴ * C).PosSemidef) :
    E.coherent.toRuntime.eventWeight I Q x ρ ≤
      t * ENNReal.ofReal r * min (E.selectedTotalMass I selected x ρ) t := by
  classical
  have hhyb := QuantumRuntime.rpow_inv_two_eventWeight_le_commutators I
    E.coherent.toRuntime_step_branch hQ hQQ E.init x hρ hρQ
  let C := fun p ↦ ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ Q) * E.U p -
    E.U p * ((1 : Matrix (In p) (In p) ℂ) ⊗ₖ Q)
  have hc : coherentBlocks C = ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ Q) * E.coherent.U () -
      E.coherent.U () * ((1 : Matrix (cohIn In) (cohIn In) ℂ) ⊗ₖ Q) := by
    change coherentBlocks ((fun p ↦ 1 ⊗ₖ Q) * E.U - E.U * (fun p ↦ 1 ⊗ₖ Q)) = _
    rw [coherentBlocks_sub, coherentBlocks_mul, coherentBlocks_mul,
      coherentBlocks_database, coherentBlocks_unitary]
  have hw : QuantumRuntime.krausWeight (spec := cohSpec In) (D := E.S)
      (fun i (_ : Unit) ↦ (1 ⊗ₖ Q) * E.coherent.U i - E.coherent.U i * (1 ⊗ₖ Q)) =
      (fun (_ : Unit) σ ↦ ENNReal.ofReal (MatrixMap.conj (coherentBlocks C) σ).trace.re) := by
    funext i σ
    rw [QuantumRuntime.krausWeight]
    cases i
    simp only [tsum_fintype, Fintype.sum_unique, hc]
  rw [hw] at hhyb
  have hb := E.tsum_rpow_queryWeight_conj_le_of_grade g hE I hx hρ htr hgrade C selected
    (fun _ ↦ r) (fun _ _ ↦ hr) hC
  have hh := ENNReal.rpow_le_rpow (hhyb.trans hb) (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [QuantumRuntime.eventWeight, rpow_inv_two_rpow_two,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh

end chargedComparison

end EmulatedOracle


section familyBound

variable {k : ℕ} {X Y Cm Z : Type} [Fintype X] {Dm : Fin k → Type}

private def databaseGrade (D : Fin k → Database X Y) : ℕ :=
  Finset.univ.sup (fun i ↦ (D i).size)

private theorem databaseGrade_le (D : Fin k → Database X Y) (n : ℕ) :
    databaseGrade D ≤ n ↔ ∀ i, (D i).size ≤ n := by
  simp [databaseGrade, Finset.sup_le_iff]

private theorem forall_split {B : Type*} (P : B → Prop) (i : Fin k)
    (d : B) (r : {j // j ≠ i} → B) :
    (∀ j, P ((Equiv.funSplitAt i B).symm (d, r) j)) ↔ P d ∧ ∀ j, P (r j) := by
  constructor
  · intro h
    exact ⟨by simpa using h i, fun j ↦ by simpa [j.property] using h j⟩
  · rintro ⟨hd, hr⟩ j
    by_cases h : j = i
    · subst j; simpa using hd
    · simpa [h] using hr ⟨j, h⟩

variable [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Cm] [DecidableEq Cm]
  [Fintype Z] [DecidableEq Z] [AddGroup Z]
  (ME : MultiExtractor k Cm Dm (Fin k → Database X Y)) (code : TpDCode k Dm Z)

variable [AddCommGroup Y] (Pgood : Set (Database X Y)) [DecidablePred (· ∈ Pgood)]
  [UniformAnswerMeasure (X →ₒ Y)]

private theorem good_port_bound (n : ℕ) (p : Fin k ⊕ Unit) :
    let U : Matrix (extIn k X Y Cm Z p × (Fin k → Database X Y))
        (extIn k X Y Cm Z p × (Fin k → Database X Y)) ℂ :=
      ((compressedVCOracle k X Y).withExtract ME code).U p
    let Q := (1 : Matrix (extIn k X Y Cm Z p) (extIn k X Y Cm Z p) ℂ) ⊗ₖ
      familyBadProjector (k := k) Pgood
    let C := (Q * U - U * Q) * (1 ⊗ₖ diagonal fun D ↦
      if databaseGrade D ≤ n then (1 : ℂ) else 0)
    ((if p.isLeft then 24 * (Database.instability (offlineLabel Pgood) (n + 1)).toReal else 0) •
      (1 : Matrix (extIn k X Y Cm Z p × (Fin k → Database X Y))
        (extIn k X Y Cm Z p × (Fin k → Database X Y)) ℂ) - Cᴴ * C).PosSemidef := by
  classical
  rcases p with i | u
  · let e := splitAt (X × Y) (Database X Y) i
    let π (r : {j // j ≠ i} → Database X Y) (d : Database X Y) :=
      decide (d ∈ Pgood ∧ ∀ j, r j ∈ Pgood)
    let Q (r : {j // j ≠ i} → Database X Y) :=
      labelProjector (fun m : (X × Y) × Database X Y ↦ π r m.2) false (α := ℂ)
    let P (r : {j // j ≠ i} → Database X Y) :=
      if ∀ j, (r j).size ≤ n then sizeProjector X Y n else 0
    let U (_ : {j // j ≠ i} → Database X Y) := compressedOracle X Y
    have hq : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ familyBadProjector (k := k) Pgood =
        liftBlocks e Q := by
      rw [familyBadProjector, labelProjector, ← diagonal_one, diagonal_kronecker_diagonal]
      simp only [one_mul]
      rw [← liftBlocks_diagonal e]
      congr 1
      funext r
      congr 1
      funext m
      change (if decide (∀ j, (Equiv.funSplitAt i (Database X Y)).symm (m.2, r) j ∈ Pgood) =
        false then (1 : ℂ) else 0) = _
      simp only [forall_split, π]
    have hp : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        diagonal (fun D : Fin k → Database X Y ↦ if databaseGrade D ≤ n then (1 : ℂ) else 0) =
        liftBlocks e P := by
      rw [← diagonal_one, diagonal_kronecker_diagonal]
      simp only [one_mul]
      rw [← liftBlocks_diagonal e]
      congr 1
      funext r
      dsimp only [P]
      split_ifs with hr
      · rw [sizeProjector]
        congr 1
        funext m
        change (if databaseGrade ((Equiv.funSplitAt i (Database X Y)).symm (m.2, r)) ≤ n
          then (1 : ℂ) else 0) = _
        simp only [databaseGrade_le, forall_split (fun d : Database X Y ↦ d.size ≤ n),
          hr, implies_true, and_true]
      · apply diagonal_eq_zero.mpr
        funext m
        change (if databaseGrade ((Equiv.funSplitAt i (Database X Y)).symm (m.2, r)) ≤ n
          then (1 : ℂ) else 0) = 0
        simp only [databaseGrade_le, forall_split (fun d : Database X Y ↦ d.size ≤ n), hr,
          and_false, ite_false]
    have hu : ((compressedVCOracle k X Y).withExtract ME code).U (.inl i) = liftBlocks e U := by
      rw [liftBlocks_const]; rfl
    have hb (r : {j // j ≠ i} → Database X Y) :
        ((24 * (Database.instability (offlineLabel Pgood) (n + 1)).toReal) •
          (1 : Matrix ((X × Y) × Database X Y) ((X × Y) × Database X Y) ℂ) -
          ((Q r * U r - U r * Q r) * P r)ᴴ * ((Q r * U r - U r * Q r) * P r)).PosSemidef := by
      apply MatrixMap.posSemidef_scalar_sub_gram_of_norm_sq_le
      dsimp only [P]
      split_ifs with hr
      · have hi : Database.instability (π r) (n + 1) ≤
            Database.instability (offlineLabel Pgood) (n + 1) := by
          have he : π r = (fun b : Bool ↦ b && decide (∀ j, r j ∈ Pgood)) ∘ offlineLabel Pgood := by
            funext d
            simp [π, offlineLabel]
          rw [he]
          exact Database.instability_comp_le _ _ _
        exact (label_source_bound (π r) n).trans (by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
            (Database.instability_le_one _ _)) hi)
      · simp only [Matrix.mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]
        positivity
    have hh := posSemidef_liftBlocks e hb
    change (liftBlocks e ((24 * (Database.instability (offlineLabel Pgood) (n + 1)).toReal) • 1 -
      (fun r ↦ (((Q * U - U * Q) * P) r)ᴴ) * ((Q * U - U * Q) * P))).PosSemidef at hh
    rw [liftBlocks_sub, liftBlocks_smul, liftBlocks_one] at hh
    change (_ - liftBlocks e ((fun r ↦ (((Q * U - U * Q) * P) r)ᴴ) *
      ((Q * U - U * Q) * P))).PosSemidef at hh
    rw [liftBlocks_mul, liftBlocks_adjoint, liftBlocks_mul, liftBlocks_sub,
      liftBlocks_mul, liftBlocks_mul, ← hq, ← hp, ← hu] at hh
    exact hh
  · cases u
    have hc := extractUnitary_commute_diagonal ME code
      (fun D ↦ if decide (∀ i, D i ∈ Pgood) = false then (1 : ℂ) else 0)
    dsimp only
    simp only [Sum.isLeft_inr, Bool.false_eq_true, ite_false]
    let Q := (1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ
      familyBadProjector (k := k) Pgood
    let P := (1 : Matrix (TpIC k Cm × Z) (TpIC k Cm × Z) ℂ) ⊗ₖ
      diagonal (fun D : Fin k → Database X Y ↦ if databaseGrade D ≤ n then (1 : ℂ) else 0)
    change ((0 : ℝ) • (1 : Matrix ((TpIC k Cm × Z) × (Fin k → Database X Y)) _ ℂ) -
      ((Q * extractUnitary ME code - extractUnitary ME code * Q) * P)ᴴ *
      ((Q * extractUnitary ME code - extractUnitary ME code * Q) * P)).PosSemidef
    have hc' : Q * extractUnitary ME code = extractUnitary ME code * Q := hc
    rw [hc', sub_self, Matrix.zero_mul, conjTranspose_zero, Matrix.zero_mul,
      zero_smul, sub_zero]
    exact PosSemidef.zero


/-- The bad-database event on the post-adversary state has weight at most
`24 t min(w,t) I_off(t)`. Extraction counts towards the total call budget and preserves
this event. Only ordinary calls contribute to `w`, including coherently selected calls. -/
theorem badEvent_compressedWithExtract_le (hgood : Database.empty ∈ Pgood)
    {L : LocalSig} (I : L.Interp) {W : QReg → Type*} {A : QReg}
    (x : QuantumComp L (cohSpec (extIn k X Y Cm Z)) W A)
    {t : ℕ} (hx : x.IsQueryBound (fun _ ↦ t)) (ρ : SubState A) :
    let E := (compressedVCOracle k X Y).withExtract ME code
    let σ := ρ.matrix ⊗ₖ E.init.matrix
    let w := ∑ i : Fin k, E.totalMass I x σ (.inl i)
    E.coherent.toRuntime.eventWeight I (familyBadProjector (k := k) Pgood) x σ ≤
      24 * t * min w t * Database.instability (offlineLabel Pgood) t := by
  classical
  let E := (compressedVCOracle k X Y).withExtract ME code
  let Q : Matrix E.S E.S ℂ := familyBadProjector (k := k) Pgood
  let r := 24 * (Database.instability (offlineLabel Pgood) t).toReal
  have hi : Database.instability (offlineLabel Pgood) t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (Database.instability_le_one _ _)
  have hq := isStarProjection_labelProjector (α := ℂ)
    (fun D : Fin k → Database X Y ↦ decide (∀ i, D i ∈ Pgood)) false
  have hgrade : QuerySupportedOn (fun m : A × E.S ↦ databaseGrade m.2) (Set.Iic 0)
      (ρ.matrix ⊗ₖ E.init.matrix) := by
    change QuerySupportedOn (fun m : A × (Fin k → Database X Y) ↦ databaseGrade m.2)
      (Set.Iic 0) (ρ.matrix ⊗ₖ (SubState.basis fun _ : Fin k ↦
        (Database.empty : Database X Y)).matrix)
    intro m m' hm
    change (ρ.matrix ⊗ₖ (SubState.basis fun _ : Fin k ↦ (Database.empty : Database X Y)).matrix)
      m m' ≠ 0 at hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · change databaseGrade m.2 ≤ 0 ∧ databaseGrade m'.2 ≤ 0
      rw [← he.1, ← he.2]
      constructor <;> exact (databaseGrade_le _ _).mpr (by simp)
    · exact False.elim (h rfl)
  have hzero : MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ Q)
      (ρ.matrix ⊗ₖ E.init.matrix) = 0 := by
    have hz : Q * E.init.matrix = 0 := by
      change familyBadProjector (k := k) Pgood *
        (SubState.basis fun _ : Fin k ↦ (Database.empty : Database X Y)).matrix =
          (0 : Matrix (Fin k → Database X Y) (Fin k → Database X Y) ℂ)
      rw [familyBadProjector, labelProjector]
      rw [SubState.matrix_basis]
      ext a b
      rw [diagonal_mul, Matrix.single_apply]
      by_cases h : (fun _ : Fin k ↦ (Database.empty : Database X Y)) = a ∧
          (fun _ : Fin k ↦ (Database.empty : Database X Y)) = b
      · rcases h with ⟨rfl, rfl⟩
        simp [hgood]
      · simp [h]
    rw [MatrixMap.conj_apply, ← mul_kronecker_mul, hz, kronecker_zero, Matrix.zero_mul]
  have hE : ∀ p a a' d d', E.U p (a', d') (a, d) ≠ 0 →
      databaseGrade d' ≤ databaseGrade d + 1 := by
    intro p a a' d d' h
    apply (databaseGrade_le _ _).mpr
    intro i
    exact (compressedVCOracle_withExtract_U_size_le ME code i p a a' d d' h).trans
      (Nat.add_le_add_right ((databaseGrade_le d _).mp le_rfl i) 1)
  have hC : ∀ j < t, ∀ p,
      let C := ((1 ⊗ₖ Q) * E.U p - E.U p * (1 ⊗ₖ Q)) *
        (1 ⊗ₖ diagonal fun d ↦ if databaseGrade d ≤ j then (1 : ℂ) else 0)
      ((if p.isLeft then r else 0) • (1 : Matrix (extIn k X Y Cm Z p × E.S)
        (extIn k X Y Cm Z p × E.S) ℂ) - Cᴴ * C).PosSemidef := by
    intro j hj p
    have h := good_port_bound ME code Pgood j p
    change ((if p.isLeft then 24 * (Database.instability (offlineLabel Pgood) (j + 1)).toReal
      else 0) • (1 : Matrix (extIn k X Y Cm Z p × E.S) (extIn k X Y Cm Z p × E.S) ℂ) -
      (((1 ⊗ₖ Q) * E.U p - E.U p * (1 ⊗ₖ Q)) *
        (1 ⊗ₖ diagonal fun d ↦ if databaseGrade d ≤ j then (1 : ℂ) else 0))ᴴ *
      (((1 ⊗ₖ Q) * E.U p - E.U p * (1 ⊗ₖ Q)) *
        (1 ⊗ₖ diagonal fun d ↦ if databaseGrade d ≤ j then (1 : ℂ) else 0))).PosSemidef at h
    have hr : 24 * (Database.instability (offlineLabel Pgood) (j + 1)).toReal ≤ r := by
      dsimp only [r]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact ENNReal.toReal_mono hi (Database.instability_mono (Nat.succ_le_of_lt hj))
    have hs : 0 ≤ (if p.isLeft then r else 0) -
        (if p.isLeft then 24 * (Database.instability (offlineLabel Pgood) (j + 1)).toReal
          else 0) := by
      split_ifs <;> simp_all
    have hh := h.add ((PosSemidef.one (n := extIn k X Y Cm Z p × E.S) (R := ℂ)).smul hs)
    dsimp only at hh ⊢
    convert hh using 1
    module
  have hb := E.eventWeight_le_of_graded_commutators databaseGrade hE I hx
    (ρ.prod E.init).posSemidef (ρ.prod E.init).trace_re_le_one hgrade Q
    hq.isSelfAdjoint hq.isIdempotentElem hzero Sum.isLeft (r := r) (by positivity) hC
  have hm : E.selectedTotalMass I Sum.isLeft x (ρ.matrix ⊗ₖ E.init.matrix) =
      ∑ i : Fin k, E.totalMass I x (ρ.matrix ⊗ₖ E.init.matrix) (.inl i) := by
    simp [selectedTotalMass, Fintype.sum_sum_type]
  rw [SubState.matrix_prod, hm] at hb
  have hr : ENNReal.ofReal r = 24 * Database.instability (offlineLabel Pgood) t := by
    dsimp only [r]
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hi]
    norm_num
  rw [hr] at hb
  convert hb using 1
  ring

end familyBound

end Quantum

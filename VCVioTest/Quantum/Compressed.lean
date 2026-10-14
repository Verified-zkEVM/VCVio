/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Action
public import VCVio.Quantum.Oracle.Compressed.Measurement
public import VCVio.Quantum.Oracle.Compressed.Truncation
public import VCVioTest.Quantum.Oracle

/-!
# Compressed-oracle regression tests

Functions `Fin 2 → Fin 2`, queried on the register `Fin 2 × Fin 2`, and `Fin 3 → Fin 2`.

* The one-cell compression on `ℂ^(Option (Fin 2)) ≅ ℂ³`, written out as a `3 × 3` matrix in the
  basis `|⊥⟩, |0⟩, |1⟩`.
* One query of `|x, 0⟩` against the empty database `|⊥, ⊥⟩`, by the one-cell formula.
* Deutsch's algorithm, as a program, has the same law against the compressed runtime as in the
  quantum random-oracle model.
* **An adaptive program**, for oracles `Fin 3 → Fin 2`, calls the oracle, measures the response
  bit, and on `1` calls again and returns the bit measured after the second call. It makes at
  most two calls on every path. Its law against the compressed runtime, against the runtime
  truncated at two of the three cells, and after the database is measured, is the law of the
  quantum random-oracle model; it ends with at most two nonempty cells.
* **A final register that depends on an outcome.** The keep-or-discard program of
  `VCVioTest.QuantumOracle`, whose leaves sit on different registers, has the law of the quantum
  random-oracle model against the compressed runtime, ends with at most one of two cells
  nonempty, and is unchanged by truncation at one cell.
* **A cutoff below the number of calls loses mass.** One call truncated at zero cells keeps half
  the trace of `|0, 0⟩|∅⟩`.
-/

public section

open Quantum Matrix MeasureTheory
open scoped ENNReal

namespace VCVioTest.QuantumCompressed

open VCVioTest.QuantumOracle

/-! ## The one-cell compression on `ℂ³` -/

/-- The one-cell compression for `Y = Fin 2` in the basis `|⊥⟩, |0⟩, |1⟩`. -/
example :
    (cellCompress (Fin 2)).submatrix ![none, some 0, some 1] ![none, some 0, some 1] =
      (!![0, (((Real.sqrt 2)⁻¹ : ℝ) : ℂ), (((Real.sqrt 2)⁻¹ : ℝ) : ℂ);
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ), 1 / 2, -1 / 2;
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ), -1 / 2, 1 / 2] : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cellAmp]

/-- The one-cell compression for `Y = Fin 2` is an involution. -/
example : cellCompress (Fin 2) * cellCompress (Fin 2) = 1 :=
  cellCompress_mul_self (Fin 2)

/-! ## One query against the empty database -/

/-- One query of `|x, 0⟩` against the empty database: with `c = 2^(-1/2)`,
`cO |x, 0⟩|⊥, ⊥⟩ = ∑ v, (½ |x, v⟩|⊥, ⊥⟩ + ∑ v'', (δ v'' v - ½) c |x, v⟩|D[x ↦ v'']⟩)`. -/
example (x : Fin 2) :
    compressedOracle (Fin 2) (Fin 2) *ᵥ Pi.single ((x, 0), Database.empty) 1 =
      ∑ v : Fin 2, ((2 : ℂ)⁻¹ • Pi.single ((x, v), Database.empty) 1 +
        ∑ v'' : Fin 2, (((if v'' = v then 1 else 0) - (2 : ℂ)⁻¹) * ((Real.sqrt 2)⁻¹ : ℝ)) •
          Pi.single ((x, v), Function.update Database.empty x (some v'')) 1) := by
  rw [compressedOracle_mulVec_single_of_eq_none 0 rfl]
  simp [cellAmp]

/-! ## Deutsch's algorithm against the compressed runtime -/

/-- Deutsch's algorithm, as a program, has the same law against the compressed runtime as in the
quantum random-oracle model. -/
example :
    (compressedRuntime (Fin 2) (Fin 2)).outcomeLaw₂ .instruments deutschComp deutsch.init =
      qromLaw₂ .instruments deutschComp deutsch.init :=
  outcomeLaw₂_compressedRuntime _ _ _

/-! ## An adaptive program -/

/-- The register `Fin 3 × Fin 2` of queries to an oracle `Fin 3 → Fin 2`. Its databases have up to
three nonempty cells, more than the two calls of the program below. -/
abbrev Reg3 : Type := Fin 3 × Fin 2

/-- The random-oracle signature for oracles `Fin 3 → Fin 2`. -/
noncomputable abbrev qrom32 : QuantumOracleSpec :=
  qromSpec (Fin 3) (Fin 2)

/-- One call on the whole register `Fin 3 × Fin 2`, with the trivial remainder. -/
noncomputable def callReg : QComp qrom32 (QReg.of Reg3) (QReg.of Reg3) Unit :=
  (QuantumComp₂.query (L := LocalSig.instruments) () (QReg.of Unit)
      (Equiv.prodPUnit Reg3).symm).bind fun _ ↦
    QComp.act (B := QReg.of Reg3) (SubInstrument.relabel (Equiv.prodPUnit Reg3))

theorem isQueryBound_callReg : callReg.IsQueryBound fun _ ↦ 1 :=
  (QuantumComp₂.isQueryBound_bind
    ((QuantumComp₂.isQueryBound_query_iff _ _ _ (fun _ ↦ 1)).mpr Nat.one_pos)
      fun _ ↦ QComp.isQueryBound_act _ 0).mono fun _ ↦ by simp

/-- Measure the response bit. -/
noncomputable def measureBit : QComp qrom32 (QReg.of Reg3) (QReg.of Reg3) (Fin 2) :=
  QComp.act (SubInstrument.classical id fun m : Reg3 ↦ m.2)

/-- Call the oracle and measure the response bit; on `1`, call the oracle again and return the
response bit measured after the second call, otherwise return `0`. The second call depends on the
measured result of the first, and the returned bit depends on the second call: from `|x, 0⟩` the
first call reads `H x`, and on `H x = 1` the second call resets the response to `0`. -/
noncomputable def queryMeasureQuery : QComp qrom32 (QReg.of Reg3) (QReg.of Reg3) (Fin 2) :=
  callReg.bind fun _ ↦
    measureBit.bind fun b ↦
      if b = 1 then callReg.bind fun _ ↦ measureBit else QuantumComp₂.pure b

/-- The adaptive program makes at most two calls on every path. -/
theorem isQueryBound_queryMeasureQuery : queryMeasureQuery.IsQueryBound fun _ ↦ 2 := by
  refine (QuantumComp₂.isQueryBound_bind (b₂ := fun _ ↦ 1) isQueryBound_callReg fun _ ↦ ?_).mono
    fun _ ↦ le_rfl
  rw [measureBit, QComp.isQueryBound_act_bind_iff]
  intro b
  split_ifs
  · exact (QuantumComp₂.isQueryBound_bind (b₂ := 0) isQueryBound_callReg
      fun _ ↦ QComp.isQueryBound_act _ _).mono fun _ ↦ by simp
  · exact QuantumComp₂.isQueryBound_pure _ _

/-- Against the compressed runtime, the adaptive program has the law of the quantum random-oracle
model. -/
example (ρ : SubState (QReg.of Reg3)) :
    (compressedRuntime (Fin 3) (Fin 2)).outcomeLaw₂ .instruments queryMeasureQuery ρ =
      qromLaw₂ .instruments queryMeasureQuery ρ :=
  outcomeLaw₂_compressedRuntime _ _ _

/-- The adaptive program ends with at most two nonempty cells, out of three. -/
example (ρ : SubState (QReg.of Reg3)) (b : Fin 2) :
    DatabaseSupportedOn 2
      ((compressedRuntime (Fin 3) (Fin 2)).jointPost₂ .instruments queryMeasureQuery ρ b).matrix :=
  databaseSupportedOn_jointPost_compressedRuntime (W := QuantumComp₂.Leaf (QReg.of Reg3) (Fin 2))
    _ isQueryBound_queryMeasureQuery _ _

/-- Truncating the database at two of the three cells does not change the law of the adaptive
program (ePrint 2025/2166, §4.3). -/
example (ρ : SubState (QReg.of Reg3)) :
    (truncatedRuntime (Fin 3) (Fin 2) 2).outcomeLaw₂ .instruments queryMeasureQuery ρ =
      qromLaw₂ .instruments queryMeasureQuery ρ :=
  outcomeLaw₂_truncatedRuntime_eq_qromLaw₂ _ isQueryBound_queryMeasureQuery le_rfl _

/-- Measuring the database after the adaptive program leaves the law of its value unchanged. -/
example [MeasurableSpace (Database (Fin 3) (Fin 2))] (ρ : SubState (QReg.of Reg3)) :
    (compressedJointLaw .instruments queryMeasureQuery ρ).map Prod.fst =
      qromLaw₂ .instruments queryMeasureQuery ρ :=
  map_fst_compressedJointLaw_eq_qromLaw _ _ _

/-! ## A final register that depends on an outcome -/

/-- The program of `VCVioTest.QuantumOracle` that calls the oracle with an ancilla, then keeps the
ancilla on `0` and discards it on `1`, so that its two leaves sit on different registers. Against
the compressed runtime it has the law of the quantum random-oracle model. -/
example [MeasurableSpace (Σ u, {b : Fin 2 // ancReg b = u})]
    (ρ : SubState (QReg.of (Reg × Fin 2))) :
    (compressedRuntime (Fin 2) (Fin 2)).outcomeLaw .instruments queryKeepOrDiscard ρ =
      qromLaw .instruments queryKeepOrDiscard ρ :=
  outcomeLaw_compressedRuntime _ _ _

/-- At both of its leaves, on different registers, the keep-or-discard program ends with at most
one nonempty cell, out of two. -/
example (ρ : SubState (QReg.of (Reg × Fin 2))) (p : Σ u, {b : Fin 2 // ancReg b = u}) :
    DatabaseSupportedOn 1
      ((compressedRuntime (Fin 2) (Fin 2)).jointPost .instruments queryKeepOrDiscard ρ p).matrix :=
  databaseSupportedOn_jointPost_compressedRuntime _ isQueryBound_queryKeepOrDiscard _ _

/-- Truncating the database at one of the two cells does not change the post-state of the
keep-or-discard program at either leaf. -/
example (ρ : SubState (QReg.of (Reg × Fin 2))) (p : Σ u, {b : Fin 2 // ancReg b = u}) :
    (truncatedRuntime (Fin 2) (Fin 2) 1).jointPost .instruments queryKeepOrDiscard ρ p =
      (compressedRuntime (Fin 2) (Fin 2)).jointPost .instruments queryKeepOrDiscard ρ p :=
  jointPost_truncatedRuntime _ isQueryBound_queryKeepOrDiscard le_rfl _ _

/-! ## A cutoff below the number of calls loses mass -/

/-- Truncating at zero cells and querying `|x, y⟩` against the empty database keeps only the
components that leave the database empty: `O^(0) |x, y⟩|∅⟩ = ∑ v, |Y|⁻¹ |x, y + v⟩|∅⟩`. -/
theorem truncatedOracle_zero_mulVec_single_empty {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y] (x : X) (y : Y) :
    truncatedOracle X Y 0 *ᵥ Pi.single ((x, y), Database.empty) 1 =
      ∑ v : Y, (Fintype.card Y : ℂ)⁻¹ • Pi.single ((x, y + v), Database.empty) 1 := by
  have hP (p : (X × Y) × Database X Y) :
      sizeProjector X Y 0 *ᵥ Pi.single p (1 : ℂ) =
        if p.2.size = 0 then Pi.single p 1 else 0 := by
    ext q
    rw [sizeProjector, mulVec_diagonal]
    by_cases hq : q = p
    · subst hq
      split_ifs <;> simp_all
    · split_ifs <;> simp [hq]
  have hs (v : Y) :
      Database.size (Function.update (Database.empty : Database X Y) x (some v)) ≠ 0 := by
    rw [Database.size]
    exact (Finset.card_pos.mpr ⟨x, by simp⟩).ne'
  rw [truncatedOracle, ← mulVec_mulVec, ← mulVec_mulVec, hP]
  simp only [Database.size_empty, eq_self, ite_true]
  rw [compressedOracle_mulVec_single_of_eq_none y (Database.empty_apply x)]
  simp [mulVec_sum, mulVec_add, mulVec_smul, hP, Database.size_empty, hs]

/-- **Truncation at `t < q` loses mass.** One call to the oracle truncated at zero cells, the step
of `truncatedRuntime (Fin 3) (Fin 2) 0`, keeps only half the trace of `|0, 0⟩|∅⟩`: the other
half is the weight of the databases with one nonempty cell. A program with one call therefore
does not have the same law against the runtime truncated at `0` as in the quantum random-oracle
model. -/
example :
    (((truncatedRuntime (Fin 3) (Fin 2) 0).step ()).branch ()
      (Matrix.single (((0 : Fin 3), (0 : Fin 2)), Database.empty)
        (((0 : Fin 3), (0 : Fin 2)), Database.empty) 1)).trace = 2⁻¹ := by
  have hψ := truncatedOracle_zero_mulVec_single_empty (0 : Fin 3) (0 : Fin 2)
  rw [Matrix.mulVec_single_one] at hψ
  rw [truncatedRuntime_step, branch_truncatedQuery_apply]
  simp only [Matrix.trace, Matrix.diag, conj_single_apply]
  have hK (b : Reg3 × Database (Fin 3) (Fin 2)) :
      truncatedOracle (Fin 3) (Fin 2) 0 b ((0, 0), Database.empty) =
        (2⁻¹ : ℂ) * (if b = ((0, 0), Database.empty) then 1 else 0) +
          (2⁻¹ : ℂ) * (if b = ((0, 1), Database.empty) then 1 else 0) := by
    have := congrFun hψ b
    rw [Matrix.col_apply] at this
    rw [this, Finset.sum_apply, Fin.sum_univ_two]
    simp [Pi.single_apply]
  simp only [hK]
  have hne : (((0 : Fin 3), (0 : Fin 2)), (Database.empty : Database (Fin 3) (Fin 2))) ≠
      ((0, 1), Database.empty) := by simp
  simp only [mul_ite, mul_one, mul_zero, star_add, apply_ite star, star_zero, add_mul, mul_add,
    ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, hne, Ne.symm hne, ite_false]
  norm_num

end VCVioTest.QuantumCompressed

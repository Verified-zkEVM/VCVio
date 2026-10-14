/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Observe

/-!
# Qubit measurement regression tests

The computational-basis measurement of one qubit, built from its two diagonal projectors, is
lossless, also when framed by an ancilla; measuring twice never reports two different outcomes;
and on the state `|+⟩⟨+|` each outcome has weight `1 / 2`, for total mass one under the bundled
semantics.

A measurement whose output register depends on the outcome, keeping the qubit on outcome `0` and
discarding it to `Unit` on outcome `1`, is a lossless dependent subinstrument with the uniform
outcome law on `|+⟩⟨+|`. Sequencing it with a continuation whose input register depends on the
first outcome is lossless, and the computational-basis measurement transported along the
constant-codomain equivalence keeps its losslessness and its outcome law.

Outcomes need not be finitely many: the instrument on a qubit that reports `n : ℕ` with weight
`2^{-(n+1)}` and leaves the state unchanged, built directly as a summable family, is lossless,
and on `|+⟩⟨+|` it gives the outcome `n` mass `2^{-(n+1)}`.
-/

public section

open Quantum Matrix MeasureTheory
open scoped ComplexOrder

namespace VCVioTest.QuantumBasic

/-- The projector onto the computational-basis state `i` of a qubit. -/
def proj (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single i i 1

/-- The computational-basis projectors satisfy the completeness relation. -/
theorem sum_conjTranspose_proj_mul_proj : ∑ i, (proj i)ᴴ * proj i = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj, Matrix.sum_apply, Matrix.single_apply]

/-- Measurement of a qubit in the computational basis. -/
noncomputable def measureZ : SubInstrument (Fin 2) (Fin 2) (Fin 2) :=
  SubInstrument.ofKraus proj sum_conjTranspose_proj_mul_proj

/-- The computational-basis measurement is lossless. -/
theorem lossless_measureZ : measureZ.Lossless :=
  SubInstrument.lossless_ofKraus _ _

/-- Framing the measurement by a three-level ancilla keeps it lossless. -/
example : (measureZ.frame (Fin 3)).Lossless :=
  lossless_measureZ.frame _

/-- Measuring twice never reports two different outcomes. -/
example (a b : Fin 2) (h : a ≠ b) :
    (do
      let x ← measureZ
      let y ← measureZ
      pure (x, y) : SubInstrument (Fin 2) (Fin 2) (Fin 2 × Fin 2)).branch (a, b) = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [measureZ, SubInstrument.branch_bind_apply_univ, Fin.sum_univ_two,
      SubInstrument.branch_pure, Pi.single_apply, ← MatrixMap.conj_mul, proj] at h ⊢

/-- The state `|+⟩⟨+|`. -/
noncomputable def plus : SubState (Fin 2) where
  matrix := Matrix.of fun _ _ ↦ 1 / 2
  posSemidef := by
    have h : (Matrix.of fun _ _ ↦ 1 / 2 : Matrix (Fin 2) (Fin 2) ℂ) =
        (Matrix.of fun _ _ ↦ 1 / 2)ᴴ * Matrix.of fun _ _ ↦ 1 / 2 := by
      ext i j
      simp [Matrix.mul_apply]
    rw [h]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_re_le_one := by
    simp [Matrix.trace]

/-- On `|+⟩⟨+|`, each outcome of the computational-basis measurement has weight `1 / 2`. -/
example (a : Fin 2) : (measureZ.branch a plus.matrix).trace = 1 / 2 := by
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-- On `|+⟩⟨+|`, the outcome measure gives each outcome mass `1 / 2`. -/
example (a : Fin 2) : measureZ.outcomeMeasure plus {a} = ENNReal.ofReal (1 / 2) := by
  rw [SubInstrument.outcomeMeasure_apply_singleton]
  congr 1
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-- Under the bundled semantics started from `|+⟩⟨+|`, the measurement has total mass one. -/
example : (SubInstrument.semanticsVia plus).evalDist measureZ Set.univ = 1 := by
  rw [SubInstrument.semanticsVia_evalDist, lossless_measureZ.outcomeMeasure_apply_univ]
  simp [plus, Matrix.trace]

/-! ## Outcome-dependent registers -/

/-- The register after measuring a qubit: the qubit on outcome `0`, nothing on outcome `1`. -/
@[expose]
def keepReg : Fin 2 → Type
  | 0 => Fin 2
  | 1 => Unit

instance instFintypeKeepReg : (i : Fin 2) → Fintype (keepReg i)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | 1 => inferInstanceAs (Fintype Unit)

/-- The bra `⟨1|`, a Kraus operator from a qubit to the trivial register. -/
def braOne : Matrix Unit (Fin 2) ℂ :=
  Matrix.of fun _ j ↦ if j = 1 then 1 else 0

/-- Kraus operators: project onto `|0⟩` and keep the qubit, or project onto `|1⟩` and discard
it. -/
def keepKraus : (i : Fin 2) → Matrix (keepReg i) (Fin 2) ℂ
  | 0 => proj 0
  | 1 => braOne

/-- The keep-or-discard Kraus operators satisfy the completeness relation. -/
theorem sum_keepKraus : ∑ i, (keepKraus i)ᴴ * keepKraus i = 1 := by
  rw [Fin.sum_univ_two]
  change (proj 0)ᴴ * proj 0 + braOneᴴ * braOne = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [proj, braOne, Matrix.mul_apply]

/-- Measure a qubit in the computational basis; keep it on outcome `0`, discard it on `1`. -/
noncomputable def measureKeep : DSubInstrument (Fin 2) (Fin 2) keepReg :=
  DSubInstrument.ofKraus keepKraus sum_keepKraus

/-- The keep-or-discard measurement is lossless. -/
theorem lossless_measureKeep : measureKeep.Lossless :=
  DSubInstrument.lossless_ofKraus _ _

/-- On `|+⟩⟨+|`, the keep-or-discard measurement gives each outcome mass `1 / 2`. -/
example (i : Fin 2) : measureKeep.outcomeMeasure plus {i} = ENNReal.ofReal (1 / 2) := by
  rw [DSubInstrument.outcomeMeasure_apply_singleton]
  congr 1
  fin_cases i
  · change (proj 0 * plus.matrix * (proj 0)ᴴ).trace.re = 1 / 2
    simp [proj, plus, Matrix.trace]
  · change (braOne * plus.matrix * braOneᴴ).trace.re = 1 / 2
    simp [braOne, plus, Matrix.trace, Matrix.mul_apply]

/-- The continuation of the keep-or-discard measurement: measure the kept qubit again, or do
nothing on the trivial register. Its input register depends on the first outcome. -/
noncomputable def remeasure : (i : Fin 2) → DSubInstrument (keepReg i) (Fin 2) keepReg
  | 0 => measureKeep
  | 1 => DSubInstrument.ret keepReg 1

/-- Measuring and then remeasuring the kept qubit is lossless. -/
example : (measureKeep.bind remeasure).Lossless :=
  lossless_measureKeep.bind fun
    | 0 => lossless_measureKeep
    | 1 => DSubInstrument.lossless_ret keepReg 1

/-- Returning an outcome and then remeasuring selects the continuation at that outcome. -/
example : (DSubInstrument.ret keepReg 0).bind remeasure = measureKeep :=
  DSubInstrument.ret_bind _ _

/-! ## The constant-codomain equivalence -/

/-- The computational-basis measurement as a dependent subinstrument is lossless. -/
example : (SubInstrument.toD measureZ).Lossless :=
  SubInstrument.lossless_toD_iff.mpr lossless_measureZ

/-- Transporting the measurement along the equivalence and back gives the measurement. -/
example : SubInstrument.equivD.symm (SubInstrument.equivD measureZ) = measureZ :=
  SubInstrument.equivD.symm_apply_apply _

/-- The measurement as a dependent subinstrument is the dependent Kraus measurement. -/
example : SubInstrument.toD measureZ =
    DSubInstrument.ofKraus (B := fun _ ↦ Fin 2) proj sum_conjTranspose_proj_mul_proj :=
  SubInstrument.toD_ofKraus _ _

/-- On `|+⟩⟨+|`, the outcome law of the transported measurement is that of the measurement, so
each outcome has mass `1 / 2`. -/
example (a : Fin 2) :
    (SubInstrument.toD measureZ).outcomeMeasure plus {a} = ENNReal.ofReal (1 / 2) := by
  rw [SubInstrument.outcomeMeasure_toD, SubInstrument.outcomeMeasure_apply_singleton]
  congr 1
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-! ## Outcomes on all of `ℕ` -/

/-- The weight `2^{-(n+1)}` of the outcome `n`. -/
noncomputable def geomWeight (n : ℕ) : ℝ :=
  (1 / 2) ^ (n + 1)

/-- The weights are nonnegative. -/
theorem geomWeight_nonneg (n : ℕ) : 0 ≤ geomWeight n := by
  unfold geomWeight
  positivity

/-- The weights sum to one. -/
theorem hasSum_geomWeight : HasSum geomWeight 1 := by
  have h := hasSum_geometric_two.mul_left (1 / 2 : ℝ)
  rw [show (1 / 2 : ℝ) * 2 = 1 by norm_num] at h
  change HasSum (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1)) 1
  simp_rw [pow_succ']
  exact h

/-- A nonnegative real multiple of the identity map is completely positive. -/
theorem isCP_ofReal_smul_id {r : ℝ} (hr : 0 ≤ r) :
    ((r : ℂ) • LinearMap.id : MatrixMap (Fin 2) (Fin 2)).IsCP := fun k ρ hρ ↦ by
  have h : ((r : ℂ) • LinearMap.id : MatrixMap (Fin 2) (Fin 2)).amplify (Fin k) ρ =
      (r : ℂ) • ρ := by
    ext x y
    simp
  rw [h]
  exact hρ.smul (Complex.zero_le_real.mpr hr)

/-- The instrument on a qubit that reports the outcome `n : ℕ` with weight `2^{-(n+1)}` and leaves
the state unchanged. Every outcome has positive weight, so it is not finitely supported. -/
@[expose]
noncomputable def geometric : SubInstrument (Fin 2) (Fin 2) ℕ where
  branch n := (geomWeight n : ℂ) • LinearMap.id
  isCP_branch n := isCP_ofReal_smul_id (geomWeight_nonneg n)
  isTNI_sum s ρ hρ := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.id_apply, Matrix.trace_sum,
      Matrix.trace_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left hρ.trace_re_nonneg
      (sum_le_hasSum s (fun n _ ↦ geomWeight_nonneg n) hasSum_geomWeight)

/-- The branch of the geometric instrument at `n` scales the state by `2^{-(n+1)}`. -/
theorem geometric_branch_apply (n : ℕ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    geometric.branch n ρ = (geomWeight n : ℂ) • ρ :=
  rfl

/-- Every outcome of the geometric instrument has a nonzero branch. -/
example (n : ℕ) : geometric.branch n ≠ 0 := fun h ↦ by
  have h1 := congrArg (fun Φ : MatrixMap (Fin 2) (Fin 2) ↦ (Φ 1).trace) h
  simp only [geometric_branch_apply, LinearMap.zero_apply, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_zero, Matrix.trace_one, Fintype.card_fin] at h1
  have h2 : (0 : ℝ) < geomWeight n := by
    unfold geomWeight
    positivity
  norm_num at h1
  exact h2.ne' h1

/-- The geometric instrument is lossless. -/
theorem lossless_geometric : geometric.Lossless := fun ρ ↦ by
  rw [SubInstrument.trace_total_apply]
  simp only [geometric_branch_apply, Matrix.trace_smul, smul_eq_mul]
  rw [tsum_mul_right, ← Complex.ofReal_tsum, hasSum_geomWeight.tsum_eq, Complex.ofReal_one,
    one_mul]

/-- On `|+⟩⟨+|`, the geometric instrument gives the outcome `n` mass `2^{-(n+1)}`. -/
example (n : ℕ) : geometric.outcomeMeasure plus {n} = ENNReal.ofReal ((1 / 2) ^ (n + 1)) := by
  rw [SubInstrument.outcomeMeasure_apply_singleton, geometric_branch_apply]
  congr 1
  simp only [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, geomWeight]
  simp [plus, Matrix.trace]

/-- On `|+⟩⟨+|`, the outcome law of the geometric instrument has total mass one. -/
example : geometric.outcomeMeasure plus Set.univ = 1 := by
  rw [lossless_geometric.outcomeMeasure_apply_univ]
  simp [plus, Matrix.trace]

end VCVioTest.QuantumBasic

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Semantics

/-!
# Qubit measurement regression tests

The computational-basis measurement of one qubit, built from its two diagonal projectors, is
lossless, also when framed by an ancilla; measuring twice never reports two different outcomes;
and on the state `|+⟩⟨+|` each outcome has weight `1 / 2`, for total mass one under the bundled
semantics. Complex phase gates distinguish adjoints from transposes, and the two orders of
noncommuting gates distinguish sequencing order. Computational-basis measurement of the first
qubit of Bell and flipped-Bell states checks system/reference order. Remeasuring a subnormalized
post-state gives exactly `½ δ₀`, preserving its missing mass.

A measurement whose output register depends on the outcome, keeping the qubit on outcome `0` and
discarding it to `Unit` on outcome `1`, is a lossless dependent subinstrument with the uniform
outcome measure on `|+⟩⟨+|`. Sequencing it with a continuation whose input register depends on the
first outcome is lossless, and the computational-basis measurement is directly a dependent
subinstrument with a constant output system, with the same losslessness and outcome measure.

Outcomes need not be finitely many: the instrument on a qubit that reports `n : ℕ` with weight
`2^{-(n+1)}` scales its post-state by that weight, preserving the normalized conditional state.
Built directly as a summable family, it is lossless, and on `|+⟩⟨+|` it gives outcome `n` mass
`2^{-(n+1)}`. For subnormalized inputs the outcome weight also includes the input trace.

Relabelling it into the reals gives an instrument with an uncountable outcome type and countably
many nonzero branches; relabelling it to a single outcome sums an infinite fibre, giving the
identity map; and its outcomes may live in a higher universe, also as a dependent subinstrument.

The laws of Kleisli composition of families of matrix maps need only the convergence of the sums
involved: associativity holds for a finite family that is not trace nonincreasing.
-/

public section

open Quantum Matrix MeasureTheory
open scoped ComplexOrder

namespace VCVioTest.QuantumBasic

/-! ## Constant-output API through ordinary imports -/

noncomputable section constantOutput

variable {A B C R α β : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype R]

/-- Relabelling infers its output system from the input subinstrument. -/
example (p : SubInstrument A B α) (f : α → β) := p.map f

/-- The facade exposes the cast-free fibre sum to rewriting. -/
example (p : SubInstrument A B α) (f : α → β) (b : β) (ρ : Matrix A A ℂ) :
    (p.map f).branch b ρ = ∑' a : f ⁻¹' {b}, p.branch a ρ := by
  rw [SubInstrument.branch_map_apply]

/-- Observing a relabelled computation infers its output system. -/
example [MeasurableSpace β] (p : SubInstrument A B α) (f : α → β) (ρ : SubState A) :=
  (p.map f).outcomeMeasure ρ

/-- Losslessness supports relabelling without a family annotation. -/
example (p : SubInstrument A B α) (hp : p.Lossless) (f : α → β) :
    (p.map f).Lossless := hp.map f

/-- The constant right unit law rewrites the bind facade. -/
example (p : SubInstrument A B α) : p.bind SubInstrument.pure = p := by
  rw [SubInstrument.bind_pure]

/-- The dependent losslessness theorem applies directly to constant return. -/
example (a : α) : (SubInstrument.pure a : SubInstrument A A α).Lossless :=
  DSubInstrument.lossless_ret _ a

/-- The constant left unit law rewrites the bind facade. -/
example (a : α) (k : α → SubInstrument A B β) : (SubInstrument.pure a).bind k = k a := by
  rw [SubInstrument.pure_bind]

/-- The returned outcome leaves the input substate unchanged. -/
example (a : α) (ρ : SubState A) : (SubInstrument.pure a).post ρ a = ρ := by
  simp only [DSubInstrument.post_ret_self]

/-- Return has the dependent point-mass outcome measure. -/
example [MeasurableSpace α] (a : α) (ρ : SubState A) :
    (SubInstrument.pure a).outcomeMeasure ρ =
      ENNReal.ofReal ρ.matrix.trace.re • Measure.dirac a := by
  simp only [DSubInstrument.outcomeMeasure_ret]

/-- Framing constant return agrees with return on the extended register. -/
example (a : α) : (SubInstrument.pure a : SubInstrument A A α).frame R =
    (SubInstrument.pure a : SubInstrument (A × R) (A × R) α) := by
  rw [SubInstrument.frame_pure]

/-- Framing commutes with the constant mapping facade by rewriting. -/
example (p : SubInstrument A B α) (f : α → β) : (p.map f).frame R = (p.frame R).map f := by
  rw [SubInstrument.frame_map]

/-- Framing constant failure gives failure by rewriting. -/
example : (SubInstrument.fail : SubInstrument A B α).frame R = SubInstrument.fail := by
  rw [SubInstrument.frame_fail]

/-- The dependent total-map law simplifies the constant mapping facade. -/
example (p : SubInstrument A B α) (f : α → β) : (p.map f).total = p.total := by
  simp only [DSubInstrument.total_map]

/-- A composite with a constant output system has a total map by field notation. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β) := (p.bind k).total

/-- A framed constant-output computation has a total map by field notation. -/
example (p : SubInstrument A B α) := (p.frame R).total

/-- Mapping a composite infers the constant output system without an expected type. -/
example {γ : Type*} (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (g : β → γ) := (p.bind k).map g

/-- Mapping a framed computation infers the extended output system. -/
example (p : SubInstrument A B α) (f : α → β) := (p.frame R).map f

/-- Losslessness proofs support sequencing followed by relabelling without annotations. -/
example {γ : Type*} (p : SubInstrument A B α) (k : α → SubInstrument B C β)
    (hp : p.Lossless) (hk : ∀ a, (k a).Lossless) (g : β → γ) := (hp.bind hk).map g

/-- Losslessness proofs support framing followed by relabelling without annotations. -/
example (p : SubInstrument A B α) (hp : p.Lossless) (f : α → β) := (hp.frame R).map f

/-- The dependent trace identity is available through field notation. -/
example (p : SubInstrument A B α) := p.familyTrace_branch

/-- Simplification recognizes the right unit law through the constant facade. -/
example (p : SubInstrument A B α) : p.bind SubInstrument.pure = p := by
  simp

/-- Dependent branch equations rewrite through the constant bind facade. -/
example (p : SubInstrument A B α) (k : α → SubInstrument B C β) (b : β) :
    (p.bind k).branch b = MatrixMap.familyBind p.branch (fun a ↦ (k a).branch) b := by
  rw [DSubInstrument.branch_bind]

end constantOutput

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
  DSubInstrument.lossless_ofKraus proj sum_conjTranspose_proj_mul_proj

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
    simp [measureZ, DSubInstrument.branch_bind_apply_univ, Fin.sum_univ_two,
      SubInstrument.branch_pure, Pi.single_apply, ← MatrixMap.conj_mul, proj] at h ⊢

/-- The density matrix of `|+⟩ = (|0⟩ + |1⟩) / √2`: all four entries are `1 / 2`. Measuring it
in the computational basis gives each outcome probability `1 / 2`, and leaves the unnormalized
post-state `(1 / 2) • |a⟩⟨a|` on outcome `a`. -/
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
  rw [DSubInstrument.outcomeMeasure_apply_singleton]
  congr 1
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-- Under the bundled semantics started from `|+⟩⟨+|`, the measurement has total mass one. -/
example : (SubInstrument.semanticsVia plus).evalDist measureZ Set.univ = 1 := by
  rw [SubInstrument.semanticsVia_evalDist, lossless_measureZ.outcomeMeasure_apply_univ]
  simp [plus, Matrix.trace]

/-- The phase operator `S = diag(1, i)` on a qubit. -/
def phaseOp : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.I]

/-- The phase operator satisfies the single-Kraus completeness relation. -/
theorem phaseOp_complete : ∑ _ : Unit, phaseOpᴴ * phaseOp = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseOp, Matrix.mul_apply, Fin.sum_univ_two]

/-- The phase gate as a single-outcome quantum channel. -/
noncomputable def phaseGate : SubInstrument (Fin 2) (Fin 2) Unit :=
  SubInstrument.ofKraus (fun _ ↦ phaseOp) phaseOp_complete

/-- The phase gate sends `½ [[1,1],[1,1]]` to `½ [[1,-i],[i,1]]`.
The imaginary off-diagonal entries distinguish conjugate transpose from transpose. -/
theorem phaseGate_plus :
    phaseGate.branch () plus.matrix = !![1 / 2, -Complex.I / 2; Complex.I / 2, 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phaseGate, phaseOp, plus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail] <;> ring_nf
  norm_num

/-- The bit-flip operator `X = [[0,1],[1,0]]` on a qubit. -/
def flipOp : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The bit-flip operator satisfies the single-Kraus completeness relation. -/
theorem flipOp_complete : ∑ _ : Unit, flipOpᴴ * flipOp = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipOp, Matrix.mul_apply, Fin.sum_univ_two]

/-- The bit flip as a single-outcome quantum channel. -/
noncomputable def flipGate : SubInstrument (Fin 2) (Fin 2) Unit :=
  SubInstrument.ofKraus (fun _ ↦ flipOp) flipOp_complete

/-- Applying `S` then `X` to `|+⟩` gives `½ [[1,i],[-i,1]]`, the state of `(i,1)/√2`. -/
example : (phaseGate.bind fun _ ↦ flipGate).branch () plus.matrix =
    !![1 / 2, Complex.I / 2; -Complex.I / 2, 1 / 2] := by
  rw [DSubInstrument.branch_bind_apply_univ]
  simp only [Fintype.sum_unique, LinearMap.comp_apply]
  change flipGate.branch () (phaseGate.branch () plus.matrix) = _
  rw [phaseGate_plus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipGate, flipOp, Matrix.mul_apply, Fin.sum_univ_two]

/-- Applying `X` then `S` to `|+⟩` gives `½ [[1,-i],[i,1]]`, the state of `(1,i)/√2`.
This differs from the reverse order, so the bind tests detect reversed composition. -/
example : (flipGate.bind fun _ ↦ phaseGate).branch () plus.matrix =
    !![1 / 2, -Complex.I / 2; Complex.I / 2, 1 / 2] := by
  rw [DSubInstrument.branch_bind_apply_univ]
  simp only [Fintype.sum_unique, LinearMap.comp_apply]
  have h : flipGate.branch () plus.matrix = plus.matrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [flipGate, flipOp, plus, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.vecHead, Matrix.vecTail]
  rw [h, phaseGate_plus]

/-- The Bell state `( |00⟩ + |11⟩ ) / √2`, with system first and reference second.
In the basis `00, 01, 10, 11`, its matrix is `½ [[1,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,1]]`. -/
noncomputable def bell : SubState (Fin 2 × Fin 2) where
  matrix := Matrix.of fun x y ↦ if x.1 = x.2 ∧ y.1 = y.2 then 1 / 2 else 0
  posSemidef := by
    let ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.of fun x y ↦ if x.1 = x.2 ∧ y.1 = y.2 then 1 / 2 else 0
    have h : ρ = ρᴴ * ρ := by
      ext ⟨i, r⟩ ⟨j, s⟩
      fin_cases i <;> fin_cases r <;> fin_cases j <;> fin_cases s <;>
        norm_num [ρ, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, map_ofNat]
    change ρ.PosSemidef
    rw [h]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  trace_re_le_one := by
    change (∑ x : Fin 2 × Fin 2,
      (if x.1 = x.2 ∧ x.1 = x.2 then (1 / 2 : ℂ) else 0)).re ≤ 1
    rw [Fintype.sum_prod_type]
    norm_num [Fin.sum_univ_two]

/-- Measuring the first Bell qubit gives `½ |aa⟩⟨aa|` in branch `a`:
`diag(½,0,0,0)` for `0`, and `diag(0,0,0,½)` for `1` in the basis `00,01,10,11`.
The conditioned reference changes too. Positivity on isolated inputs cannot justify applying
an operation to this entangled input; the framed instrument uses complete positivity. -/
theorem frame_measureZ_bell (a : Fin 2) :
    (measureZ.frame (Fin 2)).branch a bell.matrix = Matrix.single (a, a) (a, a) (1 / 2) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  fin_cases a <;> fin_cases i <;> fin_cases r <;> fin_cases j <;> fin_cases s <;>
    simp [measureZ, proj, bell, MatrixMap.amplify_apply]

/-- Measuring the first qubit of the Bell state in the computational basis gives each outcome
probability `½`. -/
example (a : Fin 2) :
    (measureZ.frame (Fin 2)).outcomeMeasure bell {a} = ENNReal.ofReal (1 / 2) := by
  rw [DSubInstrument.outcomeMeasure_apply_singleton, frame_measureZ_bell]
  fin_cases a <;> norm_num [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Flipping one Bell qubit gives `( |01⟩ + |10⟩ ) / √2`. Measuring the first factor then
returns `½ |01⟩⟨01|` at `0` and `½ |10⟩⟨10|` at `1`. These unequal factors distinguish
system-first framing from reference-first framing; the symmetric Bell branches alone do not. -/
example (a : Fin 2) :
    (measureZ.frame (Fin 2)).branch a ((flipGate.frame (Fin 2)).post bell ()).matrix =
      Matrix.single (a, 1 - a) (a, 1 - a) (1 / 2) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  fin_cases a <;> fin_cases i <;> fin_cases r <;> fin_cases j <;> fin_cases s <;>
    simp [measureZ, proj, flipGate, flipOp, bell, MatrixMap.amplify_apply,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Remeasuring the subnormalized state `½ |0⟩⟨0|` gives exactly `½ δ₀`.
The input is the unnormalized zero branch on `|+⟩`; its missing half is not restored. -/
theorem measureZ_post_zero_outcomeMeasure :
    measureZ.outcomeMeasure (measureZ.post plus 0) =
      ENNReal.ofReal (1 / 2) • Measure.dirac 0 := by
  rw [DSubInstrument.outcomeMeasure_eq_sum_univ, Fin.sum_univ_two]
  simp [measureZ, proj, plus, Matrix.trace]

/-- The total mass after remeasurement is exactly `½`, strictly less than one. -/
example : measureZ.outcomeMeasure (measureZ.post plus 0) Set.univ = ENNReal.ofReal (1 / 2) ∧
    measureZ.outcomeMeasure (measureZ.post plus 0) Set.univ < 1 := by
  rw [measureZ_post_zero_outcomeMeasure]
  norm_num

/-! ## Outcome-dependent registers -/

/-- The register after measuring a qubit: the qubit on outcome `0`, nothing on outcome `1`.
"Nothing" is the one-point basis `Unit`, whose state space `ℂ` is one-dimensional: it carries
only the weight of the branch. -/
@[expose]
def keepReg : Fin 2 → Type
  | 0 => Fin 2
  | 1 => Unit

/-- Each outcome of the keep-or-discard measurement has a finite output register. -/
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

/-! ## The constant-codomain specialization -/

/-- The computational-basis measurement is directly a lossless dependent subinstrument. -/
example : (measureZ : DSubInstrument (Fin 2) (Fin 2) (fun _ ↦ Fin 2)).Lossless :=
  lossless_measureZ

/-- The constant unit law rewrites a constant-codomain measurement directly. -/
example : measureZ.bind SubInstrument.pure = measureZ := by
  rw [SubInstrument.bind_pure]

/-- The constant-codomain measurement is definitionally the dependent Kraus measurement. -/
example : measureZ =
    DSubInstrument.ofKraus (B := fun _ ↦ Fin 2) proj sum_conjTranspose_proj_mul_proj :=
  rfl

/-- Direct dependent observation gives each computational-basis outcome mass one half. -/
example (a : Fin 2) :
    (measureZ : DSubInstrument (Fin 2) (Fin 2) (fun _ ↦ Fin 2)).outcomeMeasure plus {a} =
      ENNReal.ofReal (1 / 2) := by
  rw [DSubInstrument.outcomeMeasure_apply_singleton]
  congr 1
  fin_cases a <;> simp [measureZ, proj, plus, Matrix.trace]

/-- The finite-sum constructor preserves branches and their trace-nonincreasing bound. -/
example : SubInstrument.ofIsTNISum measureZ.branch measureZ.isCP_branch measureZ.isTNI_sum =
    measureZ := by
  ext
  rfl

/-- Losslessness of the measurement also gives trace preservation of its total map. -/
example : measureZ.total.IsTP :=
  measureZ.lossless_iff_isTP_total.mp lossless_measureZ

/-- Do notation on a fixed register sequences quantum computations with the usual unit law. -/
example : (do
    let a ← measureZ
    pure a : SubInstrument (Fin 2) (Fin 2) (Fin 2)) = measureZ := by
  simp

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

/-- The instrument with branches `Φ_n(ρ) = 2^{-(n+1)} • ρ`. On a normalized input, outcome
`n : ℕ` has probability `2^{-(n+1)}` and its normalized conditional state equals the input.
The stored post-state is scaled by that probability. Every branch map is nonzero, so the
instrument is not finitely supported. For subnormalized inputs the outcome weight also includes
the input trace. -/
@[expose]
noncomputable def geometric : SubInstrument (Fin 2) (Fin 2) ℕ where
  branch n := (geomWeight n : ℂ) • LinearMap.id
  isCP_branch n := isCP_ofReal_smul_id (geomWeight_nonneg n)
  trace_le s ρ hρ := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul]
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
  rw [geometric.isCPTNIFamily.familyTrace_apply]
  simp only [geometric_branch_apply, Matrix.trace_smul, smul_eq_mul]
  rw [tsum_mul_right, ← Complex.ofReal_tsum, hasSum_geomWeight.tsum_eq, Complex.ofReal_one,
    one_mul]

/-- On `|+⟩⟨+|`, the geometric instrument gives the outcome `n` mass `2^{-(n+1)}`. -/
example (n : ℕ) : geometric.outcomeMeasure plus {n} = ENNReal.ofReal ((1 / 2) ^ (n + 1)) := by
  rw [DSubInstrument.outcomeMeasure_apply_singleton, geometric_branch_apply]
  congr 1
  simp only [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, geomWeight]
  simp [plus, Matrix.trace]

/-- On `|+⟩⟨+|`, the outcome measure of the geometric instrument has total mass one. -/
example : geometric.outcomeMeasure plus Set.univ = 1 := by
  rw [lossless_geometric.outcomeMeasure_apply_univ]
  simp [plus, Matrix.trace]

/-! ## Family laws beyond subinstruments -/

/-- Twice the identity map on a qubit, as a one-member family. It is not trace nonincreasing. -/
noncomputable def twice : Unit → MatrixMap (Fin 2) (Fin 2) :=
  fun _ ↦ (2 : ℂ) • LinearMap.id

/-- Kleisli composition of families of matrix maps is associative whenever the sums involved
converge, with no positivity or trace condition: here every family is finite. -/
example :
    MatrixMap.familyBind (MatrixMap.familyBind twice fun _ ↦ twice) (fun _ ↦ twice) =
      MatrixMap.familyBind twice fun _ ↦ MatrixMap.familyBind twice fun _ ↦ twice :=
  MatrixMap.familyBind_assoc_of_summable (fun _ _ ↦ .of_finite) (fun _ _ _ ↦ .of_finite)
    fun _ _ ↦ .of_finite

/-! ## Uncountable, infinite-fibre and higher-universe outcomes -/

/-- The geometric instrument relabelled into the reals: an uncountable outcome type. -/
noncomputable def geometricReal : SubInstrument (Fin 2) (Fin 2) ℝ :=
  geometric.map fun n : ℕ ↦ (n : ℝ)

/-- Relabelling keeps the geometric instrument lossless on the reals. -/
example : geometricReal.Lossless :=
  lossless_geometric.map (fun n : ℕ ↦ (n : ℝ))

/-- Only countably many real outcomes carry a nonzero branch. -/
example : (Function.support geometricReal.branch).Countable :=
  geometricReal.countable_support_branch

/-- A real outcome off the range of the relabelling, here `-1`, has the zero branch. -/
example : geometricReal.branch (-1) = 0 := by
  refine LinearMap.ext fun ρ ↦ ?_
  have h : (fun n : ℕ ↦ (n : ℝ)) ⁻¹' {-1} = ∅ :=
    Set.eq_empty_of_forall_notMem fun n (hn : (n : ℝ) = -1) ↦ by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
  rw [geometricReal, SubInstrument.branch_map_apply, h, tsum_empty, LinearMap.zero_apply]

/-- As a dependent subinstrument on the reals, the relabelled instrument also has countably many
nonzero branches. -/
example : {x : ℝ | geometricReal.branch x ≠ 0}.Countable :=
  geometricReal.countable_support_branch

/-- Relabelling the geometric instrument to a single outcome sums the infinite fibre `ℕ`: the
branch at that outcome is the identity map. -/
example : (geometric.map fun _ : ℕ ↦ ()).branch () = LinearMap.id := by
  refine LinearMap.ext fun ρ ↦ ?_
  have h : (fun _ : ℕ ↦ ()) ⁻¹' {()} = Set.univ := Set.eq_univ_of_forall fun _ ↦ rfl
  have hs : HasSum (fun n ↦ (geomWeight n : ℂ) • ρ) (((1 : ℝ) : ℂ) • ρ) :=
    (Complex.hasSum_ofReal.mpr hasSum_geomWeight).smul_const ρ
  rw [SubInstrument.branch_map_apply, h, tsum_univ (f := fun n ↦ geometric.branch n ρ)]
  simp only [geometric_branch_apply]
  rw [hs.tsum_eq, Complex.ofReal_one, one_smul, LinearMap.id_apply]

/-- The geometric instrument with outcomes in the higher universe `Type 1`. -/
noncomputable def geometricULift : SubInstrument (Fin 2) (Fin 2) (ULift.{1} ℕ) :=
  geometric.map ULift.up

/-- Relabelling into a higher universe keeps the instrument lossless. -/
example : geometricULift.Lossless :=
  lossless_geometric.map ULift.up

/-- The dependent geometric instrument with outcomes in `Type 1`, restricted back to `ℕ` along
the bijection `ULift.up`, is lossless. -/
example : (geometricULift.comap ULift.up ULift.up_injective).Lossless :=
  (lossless_geometric.map ULift.up).comap ULift.up_bijective

/-- The dependent geometric instrument with outcomes in `Type 1` has countably many nonzero
branches. -/
example : {x : ULift.{1} ℕ | geometricULift.branch x ≠ 0}.Countable :=
  geometricULift.countable_support_branch

end VCVioTest.QuantumBasic

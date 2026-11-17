/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.Quantum.Comp.Parallel
public import VCVio.Quantum.Oracle.Model

/-!
# Parallel queries to the quantum random oracle

A width-k query applies the additive function oracle to k register pairs at once. Inputs
may repeat and the register pairs may be entangled. Width is a classical port index, so
different calls of a program may choose different widths.

The runtime is constructed by ordered batching of the sequential oracle with one private
register. Its step is proved equal to the simultaneous basis permutation. The QROM law
samples one function H for the whole program, not a separate function per slot or round.

## References

* K.-M. Chung, S. Fehr, Y.-H. Huang, T.-N. Liao, On the Compressed-Oracle Technique, and
  Post-Quantum Security of Proofs of Sequential Work, arXiv:2010.11658v4, §4.4.
-/

public section

open Matrix MeasureTheory
open scoped ENNReal Kronecker

universe u v w

namespace Quantum

section permutation

variable {X Y : Type} [AddGroup Y]

/-- Apply the additive oracle of H to every register pair in a width-k query. -/
@[expose]
def parallelOracleEquiv (H : X → Y) (k : ℕ) :
    (Fin k → X × Y) ≃ (Fin k → X × Y) :=
  Equiv.piCongrRight fun _ ↦ oracleEquiv H

/-- Each slot receives the same function H applied to its own input. -/
@[simp]
theorem parallelOracleEquiv_apply (H : X → Y) (k : ℕ)
    (x : Fin k → X × Y) (i : Fin k) :
    parallelOracleEquiv H k x i = ((x i).1, (x i).2 + H (x i).1) :=
  rfl

/-- The inverse parallel oracle subtracts the function value in every slot. -/
@[simp]
theorem parallelOracleEquiv_symm_apply (H : X → Y) (k : ℕ)
    (x : Fin k → X × Y) (i : Fin k) :
    (parallelOracleEquiv H k).symm x i = ((x i).1, (x i).2 - H (x i).1) :=
  rfl

/-- A width-zero query is the identity permutation. -/
@[simp]
theorem parallelOracleEquiv_zero_width (H : X → Y) :
    parallelOracleEquiv H 0 = Equiv.refl (Fin 0 → X × Y) :=
  Subsingleton.elim _ _

/-- A query to the zero function leaves every slot unchanged. -/
@[simp]
theorem parallelOracleEquiv_zero (k : ℕ) :
    parallelOracleEquiv (0 : X → Y) k = Equiv.refl (Fin k → X × Y) := by
  ext x i <;> simp

/-- Parallel addition of two functions composes their oracle permutations. -/
theorem parallelOracleEquiv_add (H H' : X → Y) (k : ℕ) :
    parallelOracleEquiv (H + H') k =
      (parallelOracleEquiv H k).trans (parallelOracleEquiv H' k) := by
  ext x i <;> simp [add_assoc]

/-- Negating the function gives the inverse parallel permutation. -/
theorem parallelOracleEquiv_neg (H : X → Y) (k : ℕ) :
    parallelOracleEquiv (-H) k = (parallelOracleEquiv H k).symm := by
  ext x i <;> simp [sub_eq_add_neg]

end permutation

section unitary

variable {X Y : Type} [DecidableEq X] [DecidableEq Y] [AddCommGroup Y]

/-- The matrix of the simultaneous additive oracle on k register pairs. -/
@[expose]
def parallelOracleUnitary (H : X → Y) (k : ℕ) :
    Matrix (Fin k → X × Y) (Fin k → X × Y) ℂ :=
  basisMatrix (parallelOracleEquiv H k)

/-- The parallel oracle is a unitary matrix. -/
theorem parallelOracleUnitary_mem_unitaryGroup [Fintype X] [Fintype Y]
    (H : X → Y) (k : ℕ) :
    parallelOracleUnitary H k ∈ Matrix.unitaryGroup (Fin k → X × Y) ℂ :=
  basisMatrix_perm_mem_unitaryGroup _

/-- The matrix of a width-zero query is the identity. -/
@[simp]
theorem parallelOracleUnitary_zero_width (H : X → Y) :
    parallelOracleUnitary H 0 = 1 := by
  simp [parallelOracleUnitary]

/-- The matrix of a query to the zero function is the identity. -/
@[simp]
theorem parallelOracleUnitary_zero (k : ℕ) :
    parallelOracleUnitary (0 : X → Y) k = 1 := by
  simp [parallelOracleUnitary]

/-- The adjoint of a parallel oracle queries the negated function. -/
theorem conjTranspose_parallelOracleUnitary (H : X → Y) (k : ℕ) :
    (parallelOracleUnitary H k)ᴴ = parallelOracleUnitary (-H) k := by
  simp only [parallelOracleUnitary, conjTranspose_basisMatrix_equiv,
    parallelOracleEquiv_neg]

/-- A parallel oracle acts on basis states by adding H in each response slot. -/
theorem parallelOracleUnitary_mulVec_single [Fintype X] [Fintype Y]
    (H : X → Y) (k : ℕ) (x : Fin k → X × Y) :
    parallelOracleUnitary H k *ᵥ Pi.single x 1 =
      Pi.single (fun i ↦ ((x i).1, (x i).2 + H (x i).1)) 1 :=
  basisMatrix_mulVec_single _ _

/-- Conjugating by the parallel oracle subtracts H in both indices of a density matrix. -/
theorem conj_parallelOracleUnitary_apply [Fintype X] [Fintype Y] (H : X → Y) (k : ℕ)
    (ρ : Matrix (Fin k → X × Y) (Fin k → X × Y) ℂ) :
    MatrixMap.conj (parallelOracleUnitary H k) ρ =
      ρ.submatrix (fun x i ↦ ((x i).1, (x i).2 - H (x i).1))
        (fun x i ↦ ((x i).1, (x i).2 - H (x i).1)) :=
  conj_basisMatrix_equiv _ _

/-- Splitting the tuple into input and response functions identifies a parallel oracle
with an ordinary additive oracle whose output group is a product group. Sampling `H` does not
in general induce the uniform law on `(Fin k → X) → (Fin k → Y)` for the derived function
`xs ↦ H ∘ xs`. The distribution in `qromBatchEvalDist` samples `H : X → Y`. -/
theorem parallelOracleUnitary_eq_oracleUnitary_submatrix (H : X → Y) (k : ℕ) :
    parallelOracleUnitary H k =
      (oracleUnitary (fun xs : Fin k → X ↦ H ∘ xs)).submatrix
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ X) (fun _ ↦ Y))
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ X) (fun _ ↦ Y)) := by
  let e := Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ X) (fun _ ↦ Y)
  ext x y
  change (if x = parallelOracleEquiv H k y then (1 : ℂ) else 0) =
    if e x = e (parallelOracleEquiv H k y) then 1 else 0
  simp only [e.injective.eq_iff]

variable [Fintype X] [Fintype Y]

/-- A parallel query as a lossless, one-result subinstrument. -/
@[expose]
noncomputable def parallelOracleQuery (H : X → Y) (k : ℕ) :
    SubInstrument (Fin k → X × Y) (Fin k → X × Y) Unit :=
  SubInstrument.relabel (parallelOracleEquiv H k)

/-- A branch of a parallel query is conjugation by its simultaneous unitary. -/
@[simp]
theorem branch_parallelOracleQuery (H : X → Y) (k : ℕ) (u : Unit) :
    (parallelOracleQuery H k).branch u = MatrixMap.conj (parallelOracleUnitary H k) :=
  SubInstrument.branch_relabel _ _

/-- Parallel queries preserve trace. -/
theorem lossless_parallelOracleQuery (H : X → Y) (k : ℕ) :
    (parallelOracleQuery H k).Lossless :=
  SubInstrument.lossless_relabel _

/-- A width-zero query leaves its state unchanged. -/
@[simp]
theorem parallelOracleQuery_zero_width (H : X → Y) :
    parallelOracleQuery H 0 = SubInstrument.pure () := by
  simp [parallelOracleQuery]

/-- Ordered sequential calls on disjoint slots agree with a simultaneous parallel query.
The private register is shared and left untouched. -/
theorem batch_oracleQuery (H : X → Y) (k : ℕ) (D : QReg) :
    SubInstrument.batch (QReg.of (X × Y)) D ((oracleQuery H).frame D) k =
      (parallelOracleQuery H k).frame D := by
  change SubInstrument.batch (QReg.of (X × Y)) D
    ((SubInstrument.relabel (oracleEquiv H)).frame D) k = _
  exact SubInstrument.batch_relabel_frame _ _ _ _

end unitary

section runtime

variable (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Variable-width QROM ports: port `((), k)` submits k input/response register pairs
in one round. -/
@[expose, reducible]
def qromBatchSpec : QuantumOracleSpec.{0, 0} :=
  uBatchSpec Unit fun _ ↦ QReg.of (X × Y)

variable {X Y} [AddCommGroup Y]

/-- Ordered batching of the fixed-function additive runtime, with one private register
shared by all slots and rounds. -/
@[expose]
noncomputable def parallelOracleRuntime (H : X → Y) :
    QuantumRuntime (qromBatchSpec X Y) :=
  (additiveOracleRuntime H).batch

/-- Each runtime step is the simultaneous additive oracle of the requested width. -/
theorem parallelOracleRuntime_step (H : X → Y) (k : ℕ) :
    (parallelOracleRuntime H).step ((), k) = (parallelOracleQuery H k).frame Unit :=
  batch_oracleQuery H k (QReg.of Unit)

/-- A width-zero runtime call is the identity, including its private memory. -/
@[simp]
theorem parallelOracleRuntime_step_zero (H : X → Y) :
    (parallelOracleRuntime H).step ((), 0) = SubInstrument.pure () := by
  rw [parallelOracleRuntime_step, parallelOracleQuery_zero_width, SubInstrument.frame_pure]
  rfl

/-- Every step of a parallel oracle runtime is lossless. -/
theorem lossless_parallelOracleRuntime_step (H : X → Y) (k : ℕ) :
    ((parallelOracleRuntime H).step ((), k)).Lossless := by
  rw [parallelOracleRuntime_step]
  exact (lossless_parallelOracleQuery H k).frame Unit

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- A lossless program remains lossless against the parallel oracle runtime. -/
theorem lossless_run_parallelOracleRuntime (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X Y) W A} (hx : x.Lossless I) (H : X → Y) :
    ((parallelOracleRuntime H).run I x).Lossless :=
  (parallelOracleRuntime H).lossless_run I hx (fun ik ↦ lossless_parallelOracleRuntime_step H ik.2)

/-- The output law of a parallel QROM program, sampling H once for the whole run. -/
@[expose]
noncomputable def qromBatchEvalDist [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) :
    Measure (Σ u, W u) :=
  sampledEvalDist parallelOracleRuntime I x ρ

/-- The parallel QROM law averages runs over the original random-function space X → Y. -/
theorem qromBatchEvalDist_eq_sum [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec X Y) W A) (ρ : SubState A) :
    qromBatchEvalDist I x ρ =
      ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ •
        ∑ H : X → Y, (parallelOracleRuntime H).evalDist I x ρ := by
  rw [qromBatchEvalDist, sampledEvalDist_eq_sum, Fintype.card_fun, Nat.cast_pow]

/-- A lossless parallel QROM program has total mass equal to the trace of its input. -/
theorem qromBatchEvalDist_apply_univ [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    {x : QuantumComp L (qromBatchSpec X Y) W A} (hx : x.Lossless I) (ρ : SubState A) :
    qromBatchEvalDist I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  simpa [qromBatchEvalDist] using sampledEvalDist_apply_univ
    (fun H ↦ lossless_run_parallelOracleRuntime I hx H)
    (c := 1) (fun _ ↦ congrArg Complex.re (SubState.trace_basis (A := Unit) ())) ρ

end runtime

end Quantum

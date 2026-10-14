/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Oracle.Compressed.Oracle
public import VCVio.Quantum.Oracle.Comb
public import VCVio.Quantum.Oracle.Model

/-!
# The compressed oracle is perfectly indistinguishable from a random function

The compressed oracle of Zhandry (*How to Record Quantum Queries, and Applications to Quantum
Indifferentiability*, Crypto 2019), in the presentation of Chiesa, Di, Hu and Zheng
(*How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions*, ePrint 2025/2166,
§4.3), is a runtime for the
signature `Quantum.qromSpec X Y` of a random oracle:

* `Quantum.compressedRuntime X Y` keeps the database register `Quantum.Database X Y`, started
  with every cell empty, and answers each call with the compressed oracle
  (`Quantum.compressedQuery X Y`);
* `Quantum.purifiedRuntime X Y` keeps the register of total functions `X → Y`, started in the
  uniform superposition over all functions, and answers each call with the table oracle that
  reads the function off that register (the purified random oracle).

The main theorem, `Quantum.outcomeLawWith_compressedRuntime` (Lemma 4.4 of ePrint 2025/2166,
Lemma 4 of Zhandry), says that every program, observed
through any function of its leaf, has the same law against the compressed runtime as in the
quantum random-oracle model (`Quantum.qromLawWith`). It holds for general programs
(`Quantum.QuantumComp`): adaptive, with their own local operations and registers, whose final
register may depend on the outcome, and with any number of calls on each path. The fixed-register
forms (`Quantum.outcomeLaw₂_compressedRuntime`, `Quantum.outcomeLaw₂_map_compressedRuntime`) and
the form for combs (`Quantum.outcomeMeasure_run_frame_compressedRuntime`) are derived from it; no
fixed number of query slots is assumed.

The proof passes through the purified runtime.

1. Compressing every cell after tabulating a total function, `S^{⊗X} E` with
   `E |H⟩ = |Quantum.Database.ofFun H⟩`, is an isometry from the function register to the
   database register. It sends the uniform superposition over functions to the empty database
   and intertwines the purified oracle with the compressed oracle. By simulation
   (`Quantum.QuantumRuntime.trace_jointPost_eq_of_simulation`) every leaf of every program has the
   same weight against the two runtimes (`Quantum.trace_jointPost_compressedRuntime`).
2. The purified oracle is block diagonal in the function register, acting on the block of `H`
   as the oracle unitary of `H`. Reading the function register at `H`, the row `⟨H|`, intertwines
   the purified runtime with `Quantum.xorRuntime H` and sends the uniform superposition to
   `|Y|^(-|X|)` times the initial state of `Quantum.xorRuntime H`. Summing over `H` recovers the
   trace, so the weight of each leaf against the purified runtime is the average over `H` of its
   weights against the oracle unitaries (`Quantum.trace_jointPost_purifiedRuntime`).

## Main definitions

* `Quantum.uniformColumn X Y` and `Quantum.uniformFunctionState X Y`: the uniform superposition
  over the functions `X → Y`.
* `Quantum.purifiedRuntime X Y` and `Quantum.compressedRuntime X Y`.

## Main results

* `Quantum.outcomeLawWith_compressedRuntime`, with `Quantum.outcomeLaw_compressedRuntime`,
  `Quantum.outcomeLaw₂_compressedRuntime` and `Quantum.outcomeLaw₂_map_compressedRuntime`.
* `Quantum.outcomeLawWith_purifiedRuntime`: the purified runtime realizes the quantum
  random-oracle model.
-/

public section

open MeasureTheory Matrix
open scoped Kronecker ENNReal

universe u v w

namespace Quantum

/-! ## Basis matrices on basis states -/

/-- The column of the basis state at `b`, times its adjoint, is the basis state at `b`. -/
theorem basisMatrix_const_mul_conjTranspose {B : Type*} [DecidableEq B] (b : B) :
    basisMatrix (fun _ : Unit ↦ b) * (basisMatrix fun _ : Unit ↦ b)ᴴ = Matrix.single b b 1 := by
  ext c c'
  by_cases h : c = b <;> by_cases h' : c' = b <;>
    simp [Matrix.mul_apply, Matrix.single_apply, h, h'] <;> grind

/-- The gate of a basis matrix sends the basis state at `a` to the basis state at `f a`. -/
theorem conj_basisMatrix_single {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (f : A → B) (a : A) :
    MatrixMap.conj (basisMatrix f) (Matrix.single a a 1) = Matrix.single (f a) (f a) 1 := by
  rw [← basisMatrix_const_mul_conjTranspose a, MatrixMap.conj_apply,
    ← Matrix.mul_assoc (basisMatrix f), Matrix.mul_assoc (basisMatrix f * _),
    ← Matrix.conjTranspose_mul, ← basisMatrix_comp]
  exact basisMatrix_const_mul_conjTranspose (f a)

/-! ## The uniform superposition over functions -/

section uniform

variable (X Y : Type*) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The uniform superposition `|Y|^(-|X|/2) ∑ H, |H⟩` over the functions `X → Y`, as a column. -/
@[expose]
noncomputable def uniformColumn : Matrix (X → Y) Unit ℂ :=
  Matrix.of fun _ _ ↦ cellAmp Y ^ Fintype.card X

omit [DecidableEq X] [DecidableEq Y] in
@[simp]
theorem uniformColumn_apply (H : X → Y) (u : Unit) :
    uniformColumn X Y H u = cellAmp Y ^ Fintype.card X :=
  rfl

omit [DecidableEq Y] in
/-- For nonempty `Y`, the uniform superposition over functions is a unit vector. -/
theorem conjTranspose_uniformColumn_mul_self [Nonempty Y] :
    (uniformColumn X Y)ᴴ * uniformColumn X Y = 1 := by
  have hN : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext ⟨⟩ ⟨⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, uniformColumn_apply, star_pow,
    star_cellAmp, ← mul_pow, cellAmp_mul_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, nsmul_eq_mul, Matrix.one_apply_eq, Nat.cast_pow]
  rw [mul_inv_cancel₀ hN, one_pow]

/-- For nonempty `Y`, the register of functions `X → Y` in the uniform superposition over all
functions. -/
@[expose]
noncomputable def uniformFunctionState [Nonempty Y] : SubState (X → Y) :=
  (SubInstrument.ofIsometry (uniformColumn X Y) (conjTranspose_uniformColumn_mul_self X Y)).post
    (SubState.basis ()) ()

omit [DecidableEq Y] in
theorem matrix_uniformFunctionState [Nonempty Y] :
    (uniformFunctionState X Y).matrix =
      MatrixMap.conj (uniformColumn X Y) (Matrix.single () () 1) := by
  rw [uniformFunctionState, SubInstrument.matrix_post, SubInstrument.branch_ofIsometry_apply,
    SubState.matrix_basis]

/-- Tabulating the uniform superposition over functions gives the empty database with every cell
compressed: `E |φ⟩ = S^{⊗X} |∅⟩`. -/
theorem basisMatrix_ofFun_mul_uniformColumn :
    basisMatrix (Database.ofFun : (X → Y) → Database X Y) * uniformColumn X Y =
      compressAll X Y * basisMatrix fun _ : Unit ↦ (Database.empty : Database X Y) := by
  ext D u
  rw [mul_basisMatrix_apply, compressAll_apply_empty]
  simp only [Matrix.mul_apply, basisMatrix_apply, uniformColumn_apply, boole_mul]
  split_ifs with h
  · obtain ⟨H, rfl⟩ := Database.exists_ofFun_eq h
    simp [Database.ofFun_injective.eq_iff]
  · refine Finset.sum_eq_zero fun H _ ↦ ?_
    simp only [ite_eq_right_iff]
    rintro rfl
    exact absurd (fun x ↦ by simp) h

end uniform

/-! ## Compression and reading the function register -/

section compression

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Reading the function register at `H`: the row `⟨H|`. -/
@[expose]
def evalRow (H : X → Y) : Matrix Unit (X → Y) ℂ :=
  Matrix.of fun _ H' ↦ if H' = H then 1 else 0

/-- The trace of the block of `H`, read off with the row `⟨H|`, is the trace of the diagonal
block of `H`. -/
theorem trace_amplifyLeft_conj_evalRow {B : Type*} [Fintype B] (H : X → Y)
    (M : Matrix (B × (X → Y)) (B × (X → Y)) ℂ) :
    ((MatrixMap.conj (evalRow H)).amplifyLeft B M).trace = ∑ b, M (b, H) (b, H) := by
  simp [Matrix.trace, Matrix.mul_apply, evalRow, Fintype.sum_prod_type]

/-- The diagonal blocks of the function register, summed over all functions, give the trace. -/
theorem sum_trace_amplifyLeft_conj_evalRow {B : Type*} [Fintype B]
    (M : Matrix (B × (X → Y)) (B × (X → Y)) ℂ) :
    ∑ H : X → Y, ((MatrixMap.conj (evalRow H)).amplifyLeft B M).trace = M.trace := by
  simp only [trace_amplifyLeft_conj_evalRow]
  rw [Matrix.trace, Fintype.sum_prod_type_right]
  rfl

variable [Nonempty Y]

/-- Compressing every cell after tabulating a total function is an isometry. -/
theorem conjTranspose_compressAll_mul_basisMatrix_mul_self :
    (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y))ᴴ *
      (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y)) = 1 := by
  rw [conjTranspose_mul, conjTranspose_compressAll, Matrix.mul_assoc,
    ← Matrix.mul_assoc (compressAll X Y), compressAll_mul_self, Matrix.one_mul,
    conjTranspose_basisMatrix_mul_self Database.ofFun_injective]

/-- Compressing every cell after tabulating a total function sends the uniform superposition over
functions to the empty database. -/
theorem conj_compressAll_mul_basisMatrix_uniformFunctionState :
    MatrixMap.conj (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y))
        (uniformFunctionState X Y).matrix =
      (SubState.basis (Database.empty : Database X Y)).matrix := by
  rw [matrix_uniformFunctionState, ← LinearMap.comp_apply, ← MatrixMap.conj_mul,
    Matrix.mul_assoc, basisMatrix_ofFun_mul_uniformColumn, ← Matrix.mul_assoc,
    compressAll_mul_self, Matrix.one_mul, conj_basisMatrix_single, SubState.matrix_basis]

/-- Reading the uniform superposition over functions at `H` leaves the weight `|Y|^(-|X|)`. -/
theorem conj_evalRow_uniformFunctionState (H : X → Y) :
    MatrixMap.conj (evalRow H) (uniformFunctionState X Y).matrix =
      ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) • (SubState.basis ()).matrix := by
  rw [matrix_uniformFunctionState, ← LinearMap.comp_apply, ← MatrixMap.conj_mul,
    SubState.matrix_basis]
  ext ⟨⟩ ⟨⟩
  simp [Matrix.mul_apply, evalRow, star_pow, ← mul_pow, cellAmp_mul_self]

end compression

/-! ## The runtimes -/

section runtimes

variable (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The purified random oracle: the private register holds a total function `X → Y`, started in
the uniform superposition over all functions, and each call applies the table oracle
`|x, y⟩|H⟩ ↦ |x, y + H x⟩|H⟩`. -/
@[expose]
noncomputable def purifiedRuntime : QuantumRuntime (qromSpec X Y) where
  D := QReg.of (X → Y)
  init := uniformFunctionState X Y
  step _ := SubInstrument.ofIsometry (tableOracle (id : (X → Y) → X → Y))
    (conjTranspose_tableOracle_mul_self (id : (X → Y) → X → Y))

/-- The compressed oracle: the private register is the database register, started with every
cell empty, and each call applies the compressed oracle to the query register and the
database. It is reducible, so that its register is reducibly the database register and an
operator on `A × Database X Y` can be fed to its runs. -/
@[expose, reducible]
noncomputable def compressedRuntime : QuantumRuntime (qromSpec X Y) where
  D := QReg.of (Database X Y)
  init := SubState.basis Database.empty
  step _ := compressedQuery X Y

theorem purifiedRuntime_init : (purifiedRuntime X Y).init = uniformFunctionState X Y :=
  rfl

theorem compressedRuntime_init : (compressedRuntime X Y).init = SubState.basis Database.empty :=
  rfl

theorem compressedRuntime_step (i : Unit) : (compressedRuntime X Y).step i = compressedQuery X Y :=
  rfl

/-- The steps of the purified runtime are lossless. -/
theorem lossless_purifiedRuntime_step (i : Unit) : ((purifiedRuntime X Y).step i).Lossless :=
  SubInstrument.lossless_ofIsometry _ (conjTranspose_tableOracle_mul_self (id : (X → Y) → X → Y))

/-- The steps of the compressed runtime are lossless. -/
theorem lossless_compressedRuntime_step (i : Unit) : ((compressedRuntime X Y).step i).Lossless :=
  lossless_compressedQuery

end runtimes

/-! ## The compressed runtime simulates the purified runtime -/

section compressedPurified

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Compressing every cell after tabulating a total function intertwines the purified oracle
with the compressed oracle: `cO (1 ⊗ S^{⊗X} E) = (1 ⊗ S^{⊗X} E) StO`. -/
theorem compressedOracle_mul_one_kronecker_compressAll_mul_basisMatrix :
    compressedOracle X Y * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y))) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y))) *
        tableOracle (id : (X → Y) → X → Y) := by
  have hsplit : (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y)) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
          basisMatrix (Database.ofFun : (X → Y) → Database X Y)) := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
  have hE : standardOracle X Y * ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
      basisMatrix (Database.ofFun : (X → Y) → Database X Y)) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
        basisMatrix (Database.ofFun : (X → Y) → Database X Y)) *
        tableOracle (id : (X → Y) → X → Y) :=
    tableOracle_mul_one_kronecker_basisMatrix fun H ↦ Database.lookup_ofFun H
  rw [hsplit]
  calc compressedOracle X Y * (((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) *
          ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
            basisMatrix (Database.ofFun : (X → Y) → Database X Y)))
    _ = ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) * standardOracle X Y *
          (((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) *
            ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y)) *
          ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
            basisMatrix (Database.ofFun : (X → Y) → Database X Y)) := by
        rw [compressedOracle]
        simp only [Matrix.mul_assoc]
    _ = ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ compressAll X Y) * (standardOracle X Y *
          ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
            basisMatrix (Database.ofFun : (X → Y) → Database X Y))) := by
        rw [one_kronecker_compressAll_mul_self, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hE, Matrix.mul_assoc]

end compressedPurified

section compressedPurifiedRuntime

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Against the compressed runtime and the purified runtime, every leaf of every program has the
same weight. -/
theorem trace_jointPost_compressedRuntime (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (p : Σ u, W u) :
    ((compressedRuntime X Y).jointPost I x ρ p).matrix.trace =
      ((purifiedRuntime X Y).jointPost I x ρ p).matrix.trace := by
  refine QuantumRuntime.trace_jointPost_eq_of_simulation (R₁ := purifiedRuntime X Y)
    (R₂ := compressedRuntime X Y)
    (V := MatrixMap.conj
      (compressAll X Y * basisMatrix (Database.ofFun : (X → Y) → Database X Y)))
    I (fun i r ↦ ?_) (MatrixMap.isTP_conj conjTranspose_compressAll_mul_basisMatrix_mul_self)
    conj_compressAll_mul_basisMatrix_uniformFunctionState x ρ p
  change MatrixMap.conj (compressedOracle X Y) ∘ₗ
      (MatrixMap.conj (compressAll X Y * basisMatrix Database.ofFun)).amplifyLeft (X × Y) =
    (MatrixMap.conj (compressAll X Y * basisMatrix Database.ofFun)).amplifyLeft (X × Y) ∘ₗ
      MatrixMap.conj (tableOracle (id : (X → Y) → X → Y))
  rw [MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul,
    compressedOracle_mul_one_kronecker_compressAll_mul_basisMatrix]

/-- Against the compressed runtime and the purified runtime, every program has the same observed
law, whatever the observation. -/
theorem outcomeLawWith_compressedRuntime_eq_purifiedRuntime {γ : Type*} [MeasurableSpace γ]
    (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A)
    (f : (Σ u, W u) → γ) :
    (compressedRuntime X Y).outcomeLawWith I x ρ f =
      (purifiedRuntime X Y).outcomeLawWith I x ρ f := by
  simp only [QuantumRuntime.outcomeLawWith]
  refine congrArg Measure.sum (funext fun p ↦ ?_)
  rw [trace_jointPost_compressedRuntime]

end compressedPurifiedRuntime

/-! ## The purified runtime is the quantum random-oracle model -/

section purifiedQrom

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- Reading the function register at `H` intertwines the purified oracle with the oracle unitary
of `H`: `(U_H ⊗ 1) (1 ⊗ ⟨H|) = (1 ⊗ ⟨H|) StO`. -/
theorem oracleUnitary_kronecker_one_mul_one_kronecker_evalRow (H : X → Y) :
    (oracleUnitary H ⊗ₖ (1 : Matrix Unit Unit ℂ)) *
        ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ evalRow H) =
      ((1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ evalRow H) * tableOracle (id : (X → Y) → X → Y) := by
  ext ⟨m, u⟩ ⟨m', H'⟩
  by_cases hH : H' = H
  · subst hH
    simp [Matrix.mul_apply, Fintype.sum_prod_type, evalRow, oracleUnitary_apply,
      tableOracle_apply, Matrix.one_apply]
    split_ifs <;> simp
  · simp [Matrix.mul_apply, Fintype.sum_prod_type, evalRow, oracleUnitary_apply,
      tableOracle_apply, Matrix.one_apply, hH, Ne.symm hH]

end purifiedQrom

section purifiedQromRuntime

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Against the purified runtime, the weight of every leaf of every program is the average, over
all functions `H`, of its weights against the oracle unitaries of `H`. -/
theorem trace_jointPost_purifiedRuntime (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (p : Σ u, W u) :
    ((purifiedRuntime X Y).jointPost I x ρ p).matrix.trace =
      ∑ H : X → Y, (Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X *
        ((xorRuntime H).jointPost I x ρ p).matrix.trace := by
  refine (sum_trace_amplifyLeft_conj_evalRow (B := p.1)
    ((purifiedRuntime X Y).jointPost I x ρ p).matrix).symm.trans
    (Finset.sum_congr rfl fun H _ ↦ ?_)
  have hsim := QuantumRuntime.simulation (R₁ := purifiedRuntime X Y) (R₂ := xorRuntime H)
    (V := MatrixMap.conj (evalRow H)) I (fun i r ↦ by
      change (MatrixMap.conj (oracleUnitary H)).amplify Unit ∘ₗ
          (MatrixMap.conj (evalRow H)).amplifyLeft (X × Y) =
        (MatrixMap.conj (evalRow H)).amplifyLeft (X × Y) ∘ₗ
          MatrixMap.conj (tableOracle (id : (X → Y) → X → Y))
      rw [MatrixMap.amplify_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
        ← MatrixMap.conj_mul, oracleUnitary_kronecker_one_mul_one_kronecker_evalRow]) x p
  have h : ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) •
      ((xorRuntime H).run I x).branch p (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) =
      (MatrixMap.conj (evalRow H)).amplifyLeft p.1
        (((purifiedRuntime X Y).run I x).branch p
          (ρ.matrix ⊗ₖ (purifiedRuntime X Y).init.matrix)) := by
    have h' := LinearMap.congr_fun hsim (ρ.matrix ⊗ₖ (purifiedRuntime X Y).init.matrix)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_kronecker] at h'
    refine Eq.trans ?_ h'
    rw [← map_smul]
    refine congrArg (((xorRuntime H).run I x).branch p) ?_
    have hk : ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) •
        (ρ.matrix ⊗ₖ (SubState.basis ()).matrix : Matrix (A × Unit) (A × Unit) ℂ) =
        ρ.matrix ⊗ₖ MatrixMap.conj (evalRow H) (uniformFunctionState X Y).matrix := by
      rw [conj_evalRow_uniformFunctionState, kronecker_smul]
    exact hk
  have ht := congrArg Matrix.trace h
  rw [Matrix.trace_smul, smul_eq_mul] at ht
  exact ht.symm

/-- The weights of the leaves against the purified runtime, as extended nonnegative reals. -/
theorem ofReal_trace_jointPost_purifiedRuntime (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (p : Σ u, W u) :
    ENNReal.ofReal ((purifiedRuntime X Y).jointPost I x ρ p).matrix.trace.re =
      ∑ H : X → Y, ((Fintype.card Y : ℝ≥0∞) ^ Fintype.card X)⁻¹ *
        ENNReal.ofReal ((xorRuntime H).jointPost I x ρ p).matrix.trace.re := by
  have hc : ((Fintype.card Y : ℂ)⁻¹ ^ Fintype.card X) =
      (((Fintype.card Y : ℝ)⁻¹ ^ Fintype.card X : ℝ) : ℂ) := by
    push_cast
    rfl
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  rw [trace_jointPost_purifiedRuntime, Complex.re_sum]
  simp only [hc, Complex.re_ofReal_mul]
  rw [ENNReal.ofReal_sum_of_nonneg fun H _ ↦
    mul_nonneg (pow_nonneg (inv_nonneg.mpr hN.le) _) (SubState.trace_re_nonneg _)]
  refine Finset.sum_congr rfl fun H _ ↦ ?_
  rw [ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hN.le) _),
    ENNReal.ofReal_pow (inv_nonneg.mpr hN.le), ENNReal.ofReal_inv_of_pos hN,
    ENNReal.ofReal_natCast, ENNReal.inv_pow]

variable [SampleableType (X → Y)]

/-- **The purified runtime realizes the quantum random-oracle model.** Every program, observed
through any function of its leaf, has the same law against the purified runtime as in the quantum
random-oracle model. -/
theorem outcomeLawWith_purifiedRuntime {γ : Type*} [MeasurableSpace γ] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (purifiedRuntime X Y).outcomeLawWith I x ρ f = qromLawWith I x ρ fun _ ↦ f := by
  refine Measure.ext fun s hs ↦ ?_
  rw [qromLawWith_eq_sum, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul, QuantumRuntime.outcomeLawWith_apply _ _ _ _ _ hs]
  simp only [QuantumRuntime.outcomeLawWith_apply _ _ _ _ _ hs,
    ofReal_trace_jointPost_purifiedRuntime, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable, Finset.mul_sum]
  simp only [ENNReal.tsum_mul_left]

end purifiedQromRuntime

/-! ## The main theorem -/

section main

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [SampleableType (X → Y)] {L : LocalSig.{u, v}} {W : QReg → Type w} {A B : QReg}
  {α β : Type w}

/-- **The compressed oracle is perfectly indistinguishable from a random function.** Every
program, observed through any function of its leaf, has the same law against the compressed
runtime, started with every cell of the database empty, as in the quantum random-oracle model.
Programs are general: adaptive, with their own local operations and registers, with a final
register that may depend on the outcome, and with any number of calls on each path. -/
theorem outcomeLawWith_compressedRuntime {γ : Type*} [MeasurableSpace γ] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (compressedRuntime X Y).outcomeLawWith I x ρ f = qromLawWith I x ρ fun _ ↦ f := by
  rw [outcomeLawWith_compressedRuntime_eq_purifiedRuntime, outcomeLawWith_purifiedRuntime]

/-- The law of the leaf against the compressed runtime is the law of the quantum random-oracle
model. -/
theorem outcomeLaw_compressedRuntime [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) :
    (compressedRuntime X Y).outcomeLaw I x ρ = qromLaw I x ρ := by
  rw [← QuantumRuntime.outcomeLawWith_id, outcomeLawWith_compressedRuntime, qromLawWith_id]

/-- The law of the value of a fixed-register program against the compressed runtime is its law
in the quantum random-oracle model. -/
theorem outcomeLaw₂_compressedRuntime [MeasurableSpace α] (I : L.Interp)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    (compressedRuntime X Y).outcomeLaw₂ I x ρ = qromLaw₂ I x ρ := by
  rw [QuantumRuntime.outcomeLaw₂_eq_outcomeLawWith, qromLaw₂_eq_qromLawWith]
  exact outcomeLawWith_compressedRuntime (W := QuantumComp₂.Leaf B α) I x ρ _

/-- The law of a relabelled value of a fixed-register program against the compressed runtime is
its relabelled law in the quantum random-oracle model. -/
theorem outcomeLaw₂_map_compressedRuntime [MeasurableSpace β] (I : L.Interp) (g : α → β)
    (x : QuantumComp₂ L (qromSpec X Y) A B α) (ρ : SubState A) :
    (compressedRuntime X Y).outcomeLaw₂ I (x.map g) ρ = qromLawWith₂ I x ρ fun _ ↦ g := by
  rw [QuantumRuntime.outcomeLaw₂_map_eq_outcomeLawWith, qromLawWith₂_eq_qromLawWith]
  exact outcomeLawWith_compressedRuntime (W := QuantumComp₂.Leaf B α) I x ρ _

/-- **Combs.** A comb on `M` whose queries go through `ℓ` and `ℓ'`, framed by the database
register started empty and run against the compressed query step, has the law of its program in
the quantum random-oracle model. -/
theorem outcomeMeasure_run_frame_compressedRuntime {M : Type} [Fintype M] [DecidableEq M]
    {α' : Type} [MeasurableSpace α'] {q : ℕ} (c : QuantumComb M α' q) (E : QReg)
    (ℓ : M ≃ (qromSpec X Y).In () × E) (ℓ' : (qromSpec X Y).Out () × E ≃ M) :
    ((c.frame (compressedRuntime X Y).D (compressedRuntime X Y).init).run
        ((compressedRuntime X Y).combQuery () E ℓ ℓ')).outcomeMeasure
        (c.frame (compressedRuntime X Y).D (compressedRuntime X Y).init).init =
      qromLaw₂ .instruments (c.toComp () E ℓ ℓ') c.init := by
  rw [← QuantumComb.outcomeLaw_toComp, outcomeLaw₂_compressedRuntime]

end main

end Quantum

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import PolyFun.IPFunctor.Free.Bound.Substitution
public import VCVio.Quantum.Comp.Combinators
public import VCVio.Quantum.Comp.HybridIndex
public import VCVio.Quantum.Comp.QueryMass
public import VCVio.Quantum.Oracle.Basis

/-!
# Emulated oracles

An *emulated oracle* (ePrint 2025/2166, §4.1, p. 28) is a pair `EO = (Init, (U_i)_i)`: a
private register `S` prepared by `Init`, and for each port `i` a unitary `U_i` on the port's
register `X_i` and `S`. The adversary queries it with a coherent index: a query on the registers
`(I, X)` applies `U = ∑ᵢ |i⟩⟨i|_I ⊗ (U_i)_{X_i S}` (p. 28).

`Quantum.EmulatedOracle P In` records the unitaries. Everything else is derived from them:

* `Quantum.EmulatedOracle.toRuntime`: the runtime over the signature of unitary ports
  `Quantum.uSpec P In`, one classical port per unitary; each step is the gate of `U_i`.
* `Quantum.EmulatedOracle.coherent`: the emulated oracle with one port, whose register
  `Σ i, In i` carries the index, and whose unitary is the block-diagonal `∑ᵢ |i⟩⟨i| ⊗ U_i`. This
  is the paper's query interface, and the definitions of security quantify over programs run
  against `E.coherent.toRuntime`.
* `Quantum.EmulatedOracle.extend` and `Quantum.EmulatedOracle.addRegister`: further unitary ports
  on the same private register, and an untouched register beside it. They agree with the general
  runtime combinators `Quantum.QuantumRuntime.extend` and `Quantum.QuantumRuntime.addRegister`.

## Masses

The query mass `mass(A, i, j)` of Definition 4.1 (p. 28) is `‖P_mass^(i) |ψ_j⟩‖²`, with
`P_mass^(i)` the projector of the index register onto `i` and `|ψ_j⟩` the joint state before the
`j`-th query; the total mass `TotalMass(A, i)` of Definition 4.3 (p. 29) sums it over the
queries. `Quantum.EmulatedOracle.totalMass` is the case of a general program and a general
(mixed, subnormalised) state: the summed trace of the index-`i` component of the input of each
call to the coherent port, a query weight in the sense of `VCVio.Quantum.Comp.QueryMass`.

It is an index mass of `VCVio.Quantum.Comp.QueryMass`: the projector onto `i` is
`Quantum.EmulatedOracle.cohIndexProj In i ⊗ 1`, with `Quantum.EmulatedOracle.cohIndexProj` the
projector onto the fibre `Quantum.fiberProj` of `i` under the index of the coherent register, and
`Quantum.EmulatedOracle.totalMass_eq_indexMass` identifies the two masses. These projectors form
a coherent index (`Quantum.EmulatedOracle.isCoherentIndex_cohIndexProj`) that the coherent unitary
respects (`Quantum.EmulatedOracle.respectsIndex_coherent_U`), so the square-root hybrid bounds of
`VCVio.Quantum.Comp.HybridIndex` apply to emulated oracles with these masses.

## Main statements

* `Quantum.EmulatedOracle.toRuntime_step_branch`: each step is the Kraus map of its unitary, the
  form used by the square-root hybrid (`VCVio.Quantum.Comp.Hybrid`).
* `Quantum.EmulatedOracle.toRuntime_addRegister`: the two ways of adjoining a register agree.
* `Quantum.EmulatedOracle.sum_totalMass` (Remark 4.2, p. 28): the masses on the indices
  add up to the query mass of the coherent port, which a `t`-query program bounds by `t` times
  the trace of the initial state (`Quantum.EmulatedOracle.sum_totalMass_le`).
* `Quantum.EmulatedOracle.totalMass_bind`: masses add under sequencing, from the general
  `Quantum.QuantumRuntime.totalWeight_bind`.
* `Quantum.EmulatedOracle.totalMass_eq_indexMass`: the mass on `i` is the total index mass of the
  block `⟨(), i⟩`; `Quantum.EmulatedOracle.sum_totalMass` follows from
  `Quantum.QuantumRuntime.tsum_indexMass_eq_queryMass`.

## Calls through a basis embedding

`Quantum.QuantumComp.embedCalls` makes the calls of a program over a signature of unitary ports
through one port on a register `T`, along a basis embedding `Quantum.PortEmbedding` of each port
register into `T` beside a further register: an isometry before each call, its adjoint after it.
When the unitary on `T`, compressed along the embedding, is the unitary of each port:

* `Quantum.EmulatedOracle.run_embedCalls`, `Quantum.EmulatedOracle.outcomeLawWith_embedCalls`:
  the translation runs as the original program and has its observed laws;
* `Quantum.EmulatedOracle.queryWeight_embedCalls`: query weights of a diagonal form are kept,
  call by call;
* `Quantum.QuantumComp.isQueryBound_embedCalls`: a budget `b` becomes the budget `∑ q, b q`.

## Classical-port programs

A program over `Quantum.uSpec P In`, which names the port of each call classically, translates to
a coherent program: `Quantum.QuantumComp.toCoherent` embeds the input of each call of port `i`
into the summand `i` of the coherent register, calls the coherent port, and reads the summand
back.

* `Quantum.EmulatedOracle.run_toCoherent`, `Quantum.EmulatedOracle.outcomeLawWith_toCoherent`:
  the translation runs as the original program and has its observed laws.
* `Quantum.EmulatedOracle.totalMass_toCoherent`: its mass on `i` is the query mass of port `i`.
* `Quantum.QuantumComp.isQueryBound_toCoherent`: a budget `b` becomes the budget `∑ i, b i`.
* `Quantum.EmulatedOracle.lossless_run_toCoherent`: a lossless program runs losslessly after
  translation.

A statement about programs against `E.coherent.toRuntime` therefore specialises to
classical-port programs against `E.toRuntime` when its hypotheses on the program are about its
run, its observed laws, its masses or its query budget, with per-port query masses in place of
total masses. Syntactic losslessness (`Quantum.QuantumComp.Lossless`) is not preserved: the
read-back after a call is a contraction that is not trace preserving on the whole coherent
register. Losslessness of the run is preserved (`Quantum.EmulatedOracle.lossless_run_toCoherent`).
The translation is defined for programs over `Quantum.LocalSig.instruments`.

## Implementation notes

The paper's query register is `I ⊗ X_1 ⊗ ⋯ ⊗ X_k`, with `U_i` acting on `X_i`; ours is the direct
sum `Σ i, In i`. `VCVio.Quantum.Oracle.EmulatedTensor` defines the tensor-product interface and
proves the two interfaces equivalent: programs translate in both directions by calls through
basis embeddings, preserving runs, observed laws, masses and query budgets (the direction into
the tensor-product interface needs every port register to be nonempty).
-/

public section

open MeasureTheory Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u u' v u₁ v₁ uL vL w w₁

namespace Quantum

/-! ## Summed query weights -/

namespace QuantumRuntime

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{uL, vL}}
  (I : L.Interp) {X : QReg → Type w} {Y : QReg → Type w₁} {A : QReg}

/-- The weight `w` summed over all calls of `x` run against `R` from `ρ`. The total query mass
`Quantum.QuantumRuntime.queryMass` is the case of the trace on one port. -/
@[expose]
noncomputable def totalWeight (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) : ℝ≥0∞ :=
  ∑' j, R.queryWeight I w x ρ j

variable {w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}

/-- A program that stops at once has no weight. -/
@[simp]
theorem totalWeight_pure (y : X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I w (QuantumComp.pure (L := L) (spec := spec) y) ρ = 0 := by
  simp [totalWeight]

/-- The weight of a local operation followed by a continuation is the weight of the
continuations, from the branches of the operation. -/
theorem totalWeight_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I w (QuantumComp.primBind o k) ρ =
      ∑' b, R.totalWeight I w (k b) (((I o).frame R.D).branch b ρ) := by
  simp only [totalWeight, queryWeight_primBind]
  exact ENNReal.tsum_comm

/-- A call followed by a continuation adds the weight of the call's input to the weight of the
continuations. -/
theorem totalWeight_queryBind (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.totalWeight I w (QuantumComp.queryBind i E ℓ k) ρ =
      w i (callInput ℓ R.D ρ) + ∑' r, R.totalWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ) := by
  rw [totalWeight, tsum_eq_zero_add' ENNReal.summable, queryWeight_queryBind_zero]
  simp only [queryWeight_queryBind_succ, totalWeight]
  rw [ENNReal.tsum_comm]

open Classical in
/-- The total query mass is the summed weight of the trace on one port. -/
theorem queryMass_eq_totalWeight (x : QuantumComp L spec X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (i : spec.Port) :
    R.queryMass I x ρ i =
      R.totalWeight I (fun i' σ ↦ if i' = i then ENNReal.ofReal σ.trace.re else 0) x ρ :=
  rfl

section cp

variable {K : spec.Port → Type*} [∀ i, Fintype (K i)] {Φ : ∀ i, MatrixMap (spec.In i × R.D) (K i)}

/-- A weight given by the trace of a completely positive map is countably additive on summable
families of positive semidefinite operators. -/
theorem ofReal_trace_re_tsum_of_isCP (hΦ : ∀ i, (Φ i).IsCP) {ι : Type*} (i : spec.Port)
    (g : ι → Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ) (hg : Summable g)
    (hpos : ∀ b, (g b).PosSemidef) :
    ENNReal.ofReal (Φ i (∑' b, g b)).trace.re = ∑' b, ENNReal.ofReal (Φ i (g b)).trace.re := by
  rw [MatrixMap.map_tsum _ hg]
  exact ofReal_trace_re_tsum (MatrixMap.summable_comp _ hg) fun b ↦ (hΦ i).posSemidef (hpos b)

/-- On positive semidefinite inputs, the summed weight of the trace of completely positive maps
is countably additive in the state. -/
theorem totalWeight_tsum_state (hΦ : ∀ i, (Φ i).IsCP) (x : QuantumComp L spec X A) {ι : Type*}
    {f : ι → Matrix (A × R.D) (A × R.D) ℂ} (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef) :
    R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x (∑' b, f b) =
      ∑' b, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x (f b) := by
  refine (tsum_congr fun j ↦ R.queryWeight_tsum_state I
    (w := fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re)
    (fun i g hg hgpos ↦ R.ofReal_trace_re_tsum_of_isCP hΦ i g hg hgpos) x hf hpos j).trans ?_
  exact ENNReal.tsum_comm

/-- **Summed weights add under sequencing.** For a weight given by the trace of completely
positive maps, the summed weight of `x.bind k` is the summed weight of `x` plus, for every leaf
`p` of `x`, the summed weight of the continuation `k p.1 p.2` from the branch of the run of `x`
at `p`. This is the general form of `Quantum.QuantumRuntime.queryMass_bind`. -/
theorem totalWeight_bind (hΦ : ∀ i, (Φ i).IsCP) (x : QuantumComp L spec X A)
    (k : ∀ u, X u → QuantumComp L spec Y u) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) :
    R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (x.bind k) ρ =
      R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) x ρ +
        ∑' p, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (k p.1 p.2)
          ((R.run I x).branch p ρ) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    rw [QuantumComp.pure_bind, totalWeight_pure, zero_add, run_pure,
      tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, totalWeight,
          ENNReal.tsum_eq_zero]
        exact fun j ↦ R.queryWeight_zero I (fun i ↦ by simp) _ j,
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
  | primBind _ o k' ih =>
    have hb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    rw [QuantumComp.primBind_bind, totalWeight_primBind, totalWeight_primBind, run_primBind]
    simp only [fun b ↦ ih b (hb b), DSubInstrument.branch_bind_apply]
    rw [ENNReal.tsum_add]
    congr 1
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun p ↦ (R.totalWeight_tsum_state I hΦ _
      ((((I o).frame R.D).isCPTNIFamily.comp_eval
        (fun b ↦ (R.run I (k' b)).isCPTNIFamily) p).summable_apply ρ)
      (fun b ↦ (R.run I (k' b)).posSemidef_branch_apply p (hb b))).symm
  | queryBind _ i' E ℓ k' ih =>
    have hb := fun r ↦ (R.queryStep i' E ℓ).posSemidef_branch_apply r hρ
    have hrun : ∀ p, (R.run I (QuantumComp.queryBind i' E ℓ k')).branch p ρ =
        ∑' r, (R.run I (k' r)).branch p ((R.queryStep i' E ℓ).branch r ρ) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
    have htail : ∑' p, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (k p.1 p.2)
          ((R.run I (QuantumComp.queryBind i' E ℓ k')).branch p ρ) =
        ∑' r, ∑' p, R.totalWeight I (fun i σ ↦ ENNReal.ofReal (Φ i σ).trace.re) (k p.1 p.2)
          ((R.run I (k' r)).branch p ((R.queryStep i' E ℓ).branch r ρ)) := by
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun p ↦ ?_
      rw [hrun p]
      exact R.totalWeight_tsum_state I hΦ _
        ((((R.queryStep i' E ℓ)).isCPTNIFamily.comp_eval
          (fun r ↦ (R.run I (k' r)).isCPTNIFamily) p).summable_apply ρ)
        (fun r ↦ (R.run I (k' r)).posSemidef_branch_apply p (hb r))
    rw [QuantumComp.queryBind_bind, htail, totalWeight_queryBind, totalWeight_queryBind, add_assoc,
      ← ENNReal.tsum_add]
    simp only [fun r ↦ ih r (hb r)]

end cp

end QuantumRuntime

/-! ## Emulated oracles -/

/-- **Emulated oracle** (ePrint 2025/2166, §4.1, p. 28): a private register `S` with an
initial substate `init`, and for each port `i` a unitary `U i` on the port's register `In i` and
`S`. -/
structure EmulatedOracle (P : Type u) (In : P → QReg) where
  /-- The private register of the oracle (the paper's `S`). -/
  S : QReg
  /-- The initial substate of the private register (the output of the paper's `Init`). -/
  init : SubState S
  /-- The unitary of port `i` on `In i × S` (the paper's `U_i`). -/
  U : ∀ i, Matrix (In i × S) (In i × S) ℂ
  /-- Each `U i` is unitary. -/
  unitary : ∀ i, U i ∈ Matrix.unitaryGroup (In i × S) ℂ

/-- A matrix moved along a bijection of its basis stays unitary. -/
theorem reindex_mem_unitaryGroup {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) {M : Matrix m m ℂ} (hM : M ∈ Matrix.unitaryGroup m ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hM ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hM,
    Matrix.submatrix_one_equiv]

/-- A block-diagonal matrix of unitaries is unitary. -/
theorem blockDiagonal'_mem_unitaryGroup {o : Type*} [Fintype o] [DecidableEq o]
    {m : o → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {M : ∀ i, Matrix (m i) (m i) ℂ}
    (hM : ∀ i, M i ∈ Matrix.unitaryGroup (m i) ℂ) :
    Matrix.blockDiagonal' M ∈ Matrix.unitaryGroup (Σ i, m i) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
  simp_rw [← Matrix.star_eq_conjTranspose, fun i ↦ Matrix.mem_unitaryGroup_iff'.mp (hM i)]
  exact Matrix.blockDiagonal'_one

/-- The Kraus map of a matrix moved along a bijection of its basis moves the input back, applies
the Kraus map of the matrix, and moves the result forward. -/
theorem MatrixMap.conj_reindex_apply {m n : Type*} [Fintype m] [Fintype n] (e : m ≃ n)
    (M : Matrix m m ℂ) (ρ : Matrix n n ℂ) :
    MatrixMap.conj (Matrix.reindex e e M) ρ =
      (M * ρ.submatrix e e * Mᴴ).submatrix e.symm e.symm := by
  rw [MatrixMap.conj_apply, Matrix.conjTranspose_reindex, Matrix.reindex_apply,
    Matrix.reindex_apply]
  have h : ρ = (ρ.submatrix e e).submatrix e.symm e.symm := by simp
  conv_lhs => rw [h]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- The Kraus map of `U ⊗ 1`, regrouped along `Equiv.prodAssoc`, in the form of the steps of
`Quantum.QuantumRuntime.addRegister`. -/
private theorem conj_reindex_prodAssoc_kronecker_one {a s g : Type*} [Fintype a] [Fintype s]
    [Fintype g] [DecidableEq g] (U : Matrix (a × s) (a × s) ℂ)
    (ρ : Matrix (a × s × g) (a × s × g) ℂ) :
    MatrixMap.conj (Matrix.reindex (Equiv.prodAssoc a s g) (Equiv.prodAssoc a s g)
      (U ⊗ₖ (1 : Matrix g g ℂ))) ρ =
      ((MatrixMap.conj U).amplify g (ρ.submatrix (Equiv.prodAssoc a s g)
        (Equiv.prodAssoc a s g))).submatrix (Equiv.prodAssoc a s g).symm
        (Equiv.prodAssoc a s g).symm := by
  rw [MatrixMap.amplify_conj, MatrixMap.conj_apply]
  exact MatrixMap.conj_reindex_apply _ _ ρ

/-! ## Projectors onto the fibres of a labelling -/

section fiberProj

variable {J K : Type*} [DecidableEq J] [DecidableEq K]

/-- The orthogonal projector onto the basis vectors of `J` labelled `k` by `f : J → K`: the
diagonal matrix with entry `1` at `a` when `f a = k`, and `0` otherwise. When `f` reads the index
carried by a query register, it is the paper's `P_mass^(k) = |k⟩⟨k|_I` (ePrint 2025/2166,
p. 28). -/
@[expose]
noncomputable def fiberProj (f : J → K) (k : K) : Matrix J J ℂ :=
  Matrix.diagonal fun a ↦ if f a = k then 1 else 0

/-- Projectors onto fibres are self-adjoint. -/
@[simp]
theorem conjTranspose_fiberProj (f : J → K) (k : K) : (fiberProj f k)ᴴ = fiberProj f k := by
  rw [fiberProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : f a = k <;> simp [h]

/-- Projectors onto fibres are idempotent. -/
@[simp]
theorem fiberProj_mul_self [Fintype J] (f : J → K) (k : K) :
    fiberProj f k * fiberProj f k = fiberProj f k := by
  rw [fiberProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : f a = k <;> simp [h]

/-- Projectors onto distinct fibres are orthogonal. -/
theorem fiberProj_mul_of_ne [Fintype J] (f : J → K) {k k' : K} (h : k ≠ k') :
    fiberProj f k * fiberProj f k' = 0 := by
  rw [fiberProj, fiberProj, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
  congr 1
  funext a
  by_cases ha : f a = k
  · simp [ha, h]
  · simp [ha]

/-- The projectors onto the fibres add up to the identity. -/
theorem sum_fiberProj [Fintype K] (f : J → K) : ∑ k, fiberProj f k = 1 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [fiberProj, Matrix.sum_apply]
  · simp [fiberProj, Matrix.sum_apply, hab]

/-- The projectors onto the fibres form a complete family: `∑ₖ (P k)ᴴ P k = 1`. -/
theorem sum_conjTranspose_mul_fiberProj [Fintype J] [Fintype K] (f : J → K) :
    ∑ k, (fiberProj f k)ᴴ * fiberProj f k = 1 := by
  simp only [conjTranspose_fiberProj, fiberProj_mul_self, sum_fiberProj]

/-- A projector onto a fibre beside an identity is the projector onto the fibre of the labelling
read from the first factor. -/
theorem fiberProj_kronecker_one {D : Type*} [DecidableEq D] (f : J → K) (k : K) :
    fiberProj f k ⊗ₖ (1 : Matrix D D ℂ) = fiberProj (fun a : J × D ↦ f a.1) k := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases hab : a = b
  · subst hab
    by_cases hcd : c = d
    · subst hcd
      simp [fiberProj]
    · simp [fiberProj, hcd]
  · simp [fiberProj, hab]

/-- **Basis labels of the port registers form a coherent index.** On a signature of unitary
ports, the projectors onto the fibres of labellings `f i` of the port registers are a coherent
index (`Quantum.Hybrid.IsCoherentIndex`), with the same projectors on input and output. -/
theorem isCoherentIndex_fiberProj {P : Type u} {In : P → QReg} {κ : P → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (f : ∀ i, In i → κ i) :
    Hybrid.IsCoherentIndex (spec := uSpec P In) (fun i ↦ fiberProj (f i))
      (fun i ↦ fiberProj (f i)) where
  sum_eq_one i := sum_fiberProj (f i)
  mul_self i k := fiberProj_mul_self (f i) k
  conjTranspose_mul_of_ne i a b h := by
    rw [conjTranspose_fiberProj, fiberProj_mul_of_ne _ (Ne.symm h)]

end fiberProj

namespace EmulatedOracle

variable {P : Type u} {In : P → QReg} (E : EmulatedOracle P In)

/-- The unitaries of an emulated oracle are isometries. -/
theorem conjTranspose_mul_self (i : P) : (E.U i)ᴴ * E.U i = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp (E.unitary i)

/-- **The runtime of an emulated oracle**, one classical port per unitary: the private register
`S` starts in `init`, and a call of port `i` applies the gate of `U i`
(`Quantum.SubInstrument.ofIsometry`). -/
@[expose, reducible]
noncomputable def toRuntime : QuantumRuntime (uSpec P In) where
  D := E.S
  init := E.init
  step i := SubInstrument.ofIsometry (E.U i) (E.conjTranspose_mul_self i)

/-- The private register of the runtime is the private register of the oracle. -/
theorem toRuntime_D : E.toRuntime.D = E.S :=
  rfl

/-- The runtime starts in the initial substate of the oracle. -/
theorem toRuntime_init : E.toRuntime.init = E.init :=
  rfl

/-- **Each step is the Kraus map of its unitary.** This is the form of the steps assumed by the
square-root hybrid (`VCVio.Quantum.Comp.Hybrid`), so Lemma 5.7 of ePrint 2025/2166 applies to
emulated oracles. -/
theorem toRuntime_step_branch (i : P) (r : Unit) :
    (E.toRuntime.step i).branch r = MatrixMap.conj (E.U i) :=
  rfl

/-- The steps of the runtime of an emulated oracle are lossless. -/
theorem lossless_toRuntime_step (i : P) : (E.toRuntime.step i).Lossless :=
  SubInstrument.lossless_ofIsometry _ (E.conjTranspose_mul_self i)

/-! ### Extension by further ports -/

/-- Add unitary ports `U' j` on the same private register (the step from `EO` to `EO^(Ext)` of
ePrint 2025/2166, p. 50). -/
@[expose]
def extend {P' : Type u'} {In' : P' → QReg} (U' : ∀ j, Matrix (In' j × E.S) (In' j × E.S) ℂ)
    (hU' : ∀ j, U' j ∈ Matrix.unitaryGroup (In' j × E.S) ℂ) :
    EmulatedOracle (P ⊕ P') (Sum.elim In In') where
  S := E.S
  init := E.init
  U
    | .inl i => E.U i
    | .inr j => U' j
  unitary
    | .inl i => E.unitary i
    | .inr j => hU' j

section extend

variable {P' : Type u'} {In' : P' → QReg} (U' : ∀ j, Matrix (In' j × E.S) (In' j × E.S) ℂ)
  (hU' : ∀ j, U' j ∈ Matrix.unitaryGroup (In' j × E.S) ℂ)

/-- The old ports of an extended oracle are answered as before. Port-wise agreement with
`Quantum.QuantumRuntime.extend`: `uSpec (P ⊕ P') _` and `(uSpec P In).sum (uSpec P' In')` differ
in the form of their result types, which are equal but not definitionally, so the agreement is
stated per port. -/
theorem toRuntime_extend_step_inl (i : P) :
    (E.extend U' hU').toRuntime.step (.inl i) = E.toRuntime.step i :=
  rfl

/-- The new ports of an extended oracle are answered by the gates of the added unitaries. -/
theorem toRuntime_extend_step_inr (j : P') :
    (E.extend U' hU').toRuntime.step (.inr j) =
      SubInstrument.ofIsometry (U' j) (Matrix.mem_unitaryGroup_iff'.mp (hU' j)) :=
  rfl

end extend

/-! ### An untouched register -/

/-- Adjoin a register `G` in the substate `σ` beside the private register; the ports act as
`U i ⊗ 1_G` (the step from `Init` to `Init′` of ePrint 2025/2166, p. 51). -/
@[expose]
noncomputable def addRegister (G : QReg) (σ : SubState G) : EmulatedOracle P In where
  S := QReg.of (E.S × G)
  init := E.init.prod σ
  U i := Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
    (E.U i ⊗ₖ (1 : Matrix G G ℂ))
  unitary i := reindex_mem_unitaryGroup _
    (Matrix.kronecker_mem_unitary (E.unitary i) (one_mem _))

/-- **The two ways of adjoining a register agree**: the runtime of `E.addRegister G σ` is the
runtime of `E` with the register `G` added by `Quantum.QuantumRuntime.addRegister`. -/
theorem toRuntime_addRegister (G : QReg) (σ : SubState G) :
    (E.addRegister G σ).toRuntime = E.toRuntime.addRegister G σ := by
  refine congrArg (QuantumRuntime.mk _ _) (funext fun i ↦ DSubInstrument.ext <| funext fun r ↦
    LinearMap.ext fun ρ ↦ ?_)
  exact (conj_reindex_prodAssoc_kronecker_one (E.U i) ρ).trans
    (QuantumRuntime.addRegister_step_branch_apply E.toRuntime G σ i r ρ).symm

/-! ### The coherent index -/

section coherent

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} (E : EmulatedOracle P In)

/-- The coherent query register `Σ i, In i`: the index together with the register of the indexed
port. It is the direct-sum form of the paper's `I ⊗ X_1 ⊗ … ⊗ X_k` (see the module docstring). -/
@[expose, reducible]
def cohIn (In : P → QReg) : QReg :=
  QReg.of (Σ i, In i)

/-- The signature of the coherent index: one unitary port on `cohIn In`. -/
@[expose, reducible]
def cohSpec (In : P → QReg) : QuantumOracleSpec.{0, 0} :=
  uSpec Unit fun _ ↦ cohIn In

/-- **The coherent oracle** (ePrint 2025/2166, p. 28): one port on the coherent register,
answered by `U = ∑ᵢ |i⟩⟨i| ⊗ U_i`, the block-diagonal matrix of the unitaries. -/
@[expose, reducible]
noncomputable def coherent : EmulatedOracle Unit fun _ ↦ cohIn In where
  S := E.S
  init := E.init
  U _ := Matrix.reindex (Equiv.sigmaProdDistrib _ _).symm (Equiv.sigmaProdDistrib _ _).symm
    (Matrix.blockDiagonal' E.U)
  unitary _ := reindex_mem_unitaryGroup _
    (blockDiagonal'_mem_unitaryGroup E.unitary)

/-- The projector of the coherent register onto the index `i`, tensored with the identity on the
private register (the paper's `P_mass^(i) = |i⟩⟨i|_I`, p. 28). -/
@[expose]
noncomputable def indexProj (i : P) : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ :=
  Matrix.diagonal fun a ↦ if a.1.1 = i then 1 else 0

/-- The projector of the coherent register onto the index `i`, on the input register of the
coherent port alone (the paper's `|i⟩⟨i|_I`, p. 28): the projector onto the fibre of `i` under
`Sigma.fst`. These are the blocks of the coherent index of `Quantum.EmulatedOracle.cohSpec`
(`Quantum.EmulatedOracle.isCoherentIndex_cohIndexProj`). -/
@[expose, reducible]
noncomputable def cohIndexProj (In : P → QReg) (i : P) : Matrix (cohIn In) (cohIn In) ℂ :=
  fiberProj (fun a : cohIn In ↦ a.1) i

/-- The projector onto an index, with the private register, is the projector of the coherent
register beside the identity. -/
theorem indexProj_eq_kronecker (i : P) :
    E.indexProj i = cohIndexProj In i ⊗ₖ (1 : Matrix E.S E.S ℂ) := by
  rw [cohIndexProj, fiberProj_kronecker_one]
  rfl

/-- The projectors onto the indices form a coherent index on the signature of the coherent
oracle, so the square-root hybrid bounds of `VCVio.Quantum.Comp.HybridIndex` apply to it. -/
theorem isCoherentIndex_cohIndexProj :
    Hybrid.IsCoherentIndex (spec := cohSpec In) (fun _ ↦ cohIndexProj In)
      (fun _ ↦ cohIndexProj In) :=
  isCoherentIndex_fiberProj fun _ (a : cohIn In) ↦ a.1

/-- The weight of the index-`i` component of an operator: the trace of its compression by the
projector onto `i`, the squared norm `‖P_mass^(i) |ψ⟩‖²` for a pure state. -/
theorem trace_conj_indexProj (i : P) (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) :
    (MatrixMap.conj (E.indexProj i) σ).trace = ∑ a, if a.1.1 = i then σ a a else 0 := by
  simp only [MatrixMap.conj_apply, indexProj, Matrix.diagonal_conjTranspose, Matrix.trace,
    Matrix.diag_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h : a.1.1 = i <;> simp [h]

/-- The weights of the index components add up to the trace. -/
theorem sum_trace_conj_indexProj (σ : Matrix (cohIn In × E.S) (cohIn In × E.S) ℂ) :
    ∑ i, (MatrixMap.conj (E.indexProj i) σ).trace = σ.trace := by
  calc ∑ i, (MatrixMap.conj (E.indexProj i) σ).trace
      = ∑ i, ∑ a, if a.1.1 = i then σ a a else 0 :=
        Finset.sum_congr rfl fun i _ ↦ E.trace_conj_indexProj i σ
    _ = ∑ a, ∑ i, if a.1.1 = i then σ a a else 0 := Finset.sum_comm
    _ = σ.trace := Finset.sum_congr rfl fun a _ ↦ by simp

/-- **Total query mass** (ePrint 2025/2166, Definitions 4.1 and 4.3, pp. 28–29): the weight of
the index-`i` component of the input of every call of `x` to the coherent oracle, summed over
the calls, for `x` run from the joint operator `ρ` on `A × S`. -/
@[expose]
noncomputable def totalMass {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w}
    {A : QReg} (x : QuantumComp L (cohSpec In) W A) (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    ℝ≥0∞ :=
  ∑' j, E.coherent.toRuntime.queryWeight I
    (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re) x ρ j

variable {L : LocalSig.{uL, vL}} (I : L.Interp) {W : QReg → Type w} {A : QReg}

/-- **Total masses are index masses.** The mass on `i` is the total index mass
`Quantum.QuantumRuntime.indexMass` of the block `⟨(), i⟩` for the projectors
`Quantum.EmulatedOracle.cohIndexProj`, the masses consumed by the square-root hybrid bounds of
`VCVio.Quantum.Comp.HybridIndex`. -/
theorem totalMass_eq_indexMass (x : QuantumComp L (cohSpec In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    E.totalMass I x ρ i =
      E.coherent.toRuntime.indexMass I (fun _ ↦ cohIndexProj In) x ρ ⟨(), i⟩ := by
  refine tsum_congr fun j ↦ congrArg (fun w ↦ E.coherent.toRuntime.queryWeight I w x ρ j)
    (funext fun _ ↦ funext fun σ ↦ ?_)
  rw [tsum_eq_single i fun k hk ↦ by simp [hk], ite_eq_left rfl, indexProj_eq_kronecker]

/-- **Remark 4.2** (p. 28): on a positive semidefinite input, the masses on the indices add
up to the query mass of the coherent port. It is the completeness of the index projectors in
`Quantum.QuantumRuntime.tsum_indexMass_eq_queryMass`. -/
theorem sum_totalMass (x : QuantumComp L (cohSpec In) W A) {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : ρ.PosSemidef) :
    ∑ i, E.totalMass I x ρ i = E.coherent.toRuntime.queryMass I x ρ () := by
  simp only [E.totalMass_eq_indexMass I x ρ]
  rw [← tsum_fintype (L := .unconditional P)]
  exact E.coherent.toRuntime.tsum_indexMass_eq_queryMass I (fun _ ↦ cohIndexProj In) ()
    (sum_conjTranspose_mul_fiberProj _) x hρ

/-- The mass on one index is at most the query mass of the coherent port. -/
theorem totalMass_le_queryMass (x : QuantumComp L (cohSpec In) W A)
    {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) (i : P) :
    E.totalMass I x ρ i ≤ E.coherent.toRuntime.queryMass I x ρ () := by
  rw [← E.sum_totalMass I x hρ]
  exact Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ i)

/-- **Masses and query budgets.** A program making at most `t` queries has masses on the indices
adding up to at most `t` times the trace of the initial state. -/
theorem sum_totalMass_le {x : QuantumComp L (cohSpec In) W A} {t : ℕ}
    (hx : x.IsQueryBoundAt () t) {ρ : Matrix (A × E.S) (A × E.S) ℂ} (hρ : ρ.PosSemidef) :
    ∑ i, E.totalMass I x ρ i ≤ t * ENNReal.ofReal ρ.trace.re := by
  rw [E.sum_totalMass I x hρ]
  exact E.coherent.toRuntime.queryMass_le_of_isQueryBoundAt I hx hρ

/-- **Masses add under sequencing.** The mass of `x.bind k` on `i` is the mass of `x` plus, for
every leaf `p` of `x`, the mass of the continuation from the branch of the run of `x` at `p`. -/
theorem totalMass_bind {Y : QReg → Type w₁} (x : QuantumComp L (cohSpec In) W A)
    (k : ∀ u, W u → QuantumComp L (cohSpec In) Y u) {ρ : Matrix (A × E.S) (A × E.S) ℂ}
    (hρ : ρ.PosSemidef) (i : P) :
    E.totalMass I (x.bind k) ρ i =
      E.totalMass I x ρ i +
        ∑' p, E.totalMass I (k p.1 p.2) ((E.coherent.toRuntime.run I x).branch p ρ) i :=
  E.coherent.toRuntime.totalWeight_bind I (Φ := fun _ ↦ MatrixMap.conj (E.indexProj i))
    (fun _ ↦ MatrixMap.isCP_conj _) x k hρ

end coherent

end EmulatedOracle

/-! ## Matrix helpers for the coherent bridge -/

section matrixHelpers

variable {l m n o : Type*}

/-- Compressing by basis matrices picks out a submatrix. -/
theorem conjTranspose_basisMatrix_mul_mul_basisMatrix [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (f : l → m) (g : o → n) (M : Matrix m n ℂ) :
    (basisMatrix f)ᴴ * M * basisMatrix g = M.submatrix f g := by
  ext a b
  simp [Matrix.mul_apply, apply_ite (star : ℂ → ℂ), ite_mul, mul_ite, Finset.sum_ite_eq']

/-- The basis matrix of a bijection is the adjoint of the basis matrix of its inverse. -/
theorem basisMatrix_equiv_eq_conjTranspose [DecidableEq m] [DecidableEq n] (e : m ≃ n) :
    basisMatrix e = (basisMatrix e.symm)ᴴ := by
  rw [conjTranspose_basisMatrix_equiv, Equiv.symm_symm]

/-- A basis matrix beside an identity is the basis matrix of the product map. -/
theorem basisMatrix_kronecker_one [DecidableEq m] [DecidableEq n] (f : l → m) :
    basisMatrix f ⊗ₖ (1 : Matrix n n ℂ) = basisMatrix (Prod.map f id) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases h1 : a = f b <;> by_cases h2 : c = d <;> simp [h1, h2]

/-- If `K * Kᴴ = 1`, then `Kᴴ * K` is a projector, so `1 - Kᴴ * K` is positive semidefinite. -/
theorem posSemidef_one_sub_conjTranspose_mul_self [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n]
    {K : Matrix m n ℂ} (hK : K * Kᴴ = 1) : (1 - Kᴴ * K).PosSemidef := by
  have hQ : Kᴴ * K * (Kᴴ * K) = Kᴴ * K := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc K, hK, Matrix.one_mul]
  have h : (1 - Kᴴ * K)ᴴ * (1 - Kᴴ * K) = 1 - Kᴴ * K := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hQ, sub_self, sub_zero]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

end matrixHelpers

/-- A call whose step is a Kraus map is the Kraus map of the regrouped step beside the identity
on the remainder. -/
theorem QuantumRuntime.queryStep_branch_eq_conj {spec : QuantumOracleSpec.{u₁, v₁}}
    (R : QuantumRuntime spec) {i : spec.Port} {r : spec.Result i}
    {M : Matrix (spec.Out i × R.D) (spec.In i × R.D) ℂ}
    (hM : (R.step i).branch r = MatrixMap.conj M) (F : QReg) {A : QReg}
    (ℓ : A ≃ spec.In i × F) :
    (R.queryStep i F ℓ).branch r =
      MatrixMap.conj (basisMatrix (QuantumRuntime.queryEquivOut (spec.Out i) R.D F) *
        (M ⊗ₖ (1 : Matrix F F ℂ)) * basisMatrix (QuantumRuntime.queryEquivIn ℓ R.D)) := by
  refine LinearMap.ext fun ρ ↦ ?_
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply, hM,
    MatrixMap.amplify_conj, SubInstrument.branch_relabel, SubInstrument.branch_relabel,
    MatrixMap.conj_mul, MatrixMap.conj_mul]
  rfl


/-! ## Calls through a basis embedding

A call of a port `q` of a signature of unitary ports can be made through a single port on a
register `T`, given a basis injection of the register of `q` into `T` beside a register `G q`:
move the input into `T` by the isometry of the injection, call the port on `T`, and read the
result back by the adjoint of the isometry. When the unitary on `T`, compressed along the
injection, is the unitary of `q`, this translation preserves runs, query weights of a diagonal
form, and query budgets. The classical-port translation `Quantum.QuantumComp.toCoherent` below
and the translations between the coherent and the tensor-product interfaces
(`VCVio.Quantum.Oracle.EmulatedTensor`) are instances. -/

namespace EmulatedOracle

/-- The emulated oracle with one port on `T`, answered by the unitary `U`, with the private
register and the initial substate of `E`. -/
@[expose, reducible]
def onePort {P : Type u} {In : P → QReg} (E : EmulatedOracle P In) {T : QReg}
    (U : Matrix (T × E.S) (T × E.S) ℂ) (hU : U ∈ Matrix.unitaryGroup (T × E.S) ℂ) :
    EmulatedOracle Unit fun _ ↦ T where
  S := E.S
  init := E.init
  U _ := U
  unitary _ := hU

end EmulatedOracle

/-- **A basis embedding of port registers** into one register `T`: for each port `q`, a register
`G q` and an injection of the basis of the register `J q` into the basis of `T × G q`. -/
structure PortEmbedding {Q : Type u} (J : Q → QReg) (T : QReg) where
  /-- The register that receives, beside `T`, the rest of the input of the port `q`. -/
  G : Q → QReg
  /-- The basis map of the port `q`. -/
  toFun : ∀ q, J q → T × G q
  /-- Each basis map is injective. -/
  injective : ∀ q, Function.Injective (toFun q)

namespace PortEmbedding

variable {Q : Type u} {J : Q → QReg} {T : QReg} (ι : PortEmbedding J T)

/-- The basis map of the port `q` beside a remainder `F`: `|y, f⟩ ↦ |t, (g, f)⟩` for
`ι q y = (t, g)`. -/
@[expose]
def call (q : Q) (F : Type*) : J q × F → T × (ι.G q × F) :=
  fun p ↦ ((ι.toFun q p.1).1, ((ι.toFun q p.1).2, p.2))

/-- The basis map beside a remainder is injective. -/
theorem call_injective (q : Q) (F : Type*) : Function.Injective (ι.call q F) := by
  rintro ⟨y, f⟩ ⟨y', f'⟩ h
  simp only [call, Prod.mk.injEq] at h
  rw [ι.injective q (Prod.ext h.1 h.2.1), h.2.2]

/-- The basis map of the port `q` beside the private register `D` of a runtime, grouped as the
input of a call on `T`: `|y, d⟩ ↦ |(t, d), g⟩` for `ι q y = (t, g)`. -/
@[expose]
def withPrivate (q : Q) (D : Type*) : J q × D → (T × D) × ι.G q :=
  fun p ↦ (((ι.toFun q p.1).1, p.2), (ι.toFun q p.1).2)

/-- Before a call of the port `q` made through the port on `T`: the isometry that moves the input
`J q`, exposed by `ℓ`, into `T`, with the rest in `G q` beside the remainder `F`. -/
@[expose]
noncomputable def embed (q : Q) (F : QReg) {A : QReg} (ℓ : A ≃ J q × F) :
    SubInstrument A (T × QReg.of (ι.G q × F)) PUnit.{v + 1} :=
  SubInstrument.ofMap (MatrixMap.conj (basisMatrix (ι.call q F ∘ ℓ))) (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (by
      rw [conjTranspose_basisMatrix_mul_self ((ι.call_injective q F).comp ℓ.injective), sub_self]
      exact Matrix.PosSemidef.zero))

/-- After a call of the port `q` made through the port on `T`: the contraction that reads the
image of the basis map of `q` back into `J q`. -/
@[expose]
noncomputable def project (q : Q) (F : QReg) :
    SubInstrument (T × QReg.of (ι.G q × F)) (J q × F) PUnit.{v + 1} :=
  SubInstrument.ofMap (MatrixMap.conj (basisMatrix (ι.call q F))ᴴ)
    (MatrixMap.isCP_conj _)
    (MatrixMap.isTNI_conj (posSemidef_one_sub_conjTranspose_mul_self (by
      rw [Matrix.conjTranspose_conjTranspose,
        conjTranspose_basisMatrix_mul_self (ι.call_injective q F)])))

end PortEmbedding

namespace QuantumComp

variable {Q : Type u} {J : Q → QReg} {T : QReg} {W : QReg → Type w}

/-- Replace each command by local operations or a call through its basis embedding. -/
@[expose]
noncomputable def embedCallsSubstitution (ι : PortEmbedding J T) :
    IPFunctor.CommandSubstitution (toIPFunctor LocalSig.instruments.{v} (uSpec Q J))
      (toIPFunctor LocalSig.instruments.{v} (uSpec Unit fun _ ↦ T))
  | _, .prim o => QuantumComp.primBind o fun b ↦ QuantumComp.pure ⟨ULift.up b, rfl⟩
  | _, .query q F ℓ =>
      QuantumComp.primBind (L := LocalSig.instruments.{v})
        ⟨PUnit, fun _ ↦ QReg.of (T × QReg.of (ι.G q × F)), (ι.embed q F ℓ)⟩
        fun _ ↦ QuantumComp.queryBind (A := QReg.of (T × QReg.of (ι.G q × F))) ()
          (QReg.of (ι.G q × F)) (Equiv.refl _) fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{v})
            ⟨PUnit, fun _ ↦ QReg.of (J q × F), (ι.project q F)⟩ fun _ ↦
            QuantumComp.pure ⟨ULift.up (), rfl⟩

/-- **Calls through a basis embedding.** A call of the port `q` on `J q × F` becomes a call of the
single port on `T` with the remainder `G q × F`: before it, the isometry
`Quantum.PortEmbedding.embed` moves the input into `T`; after it, the contraction
`Quantum.PortEmbedding.project` reads it back. Local operations are kept. -/
@[expose]
noncomputable def embedCalls (ι : PortEmbedding J T) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec Q J) W A) :
    QuantumComp LocalSig.instruments.{v} (uSpec Unit fun _ ↦ T) W A :=
  IPFunctor.IFreeM.substitute (embedCallsSubstitution ι) x

variable (ι : PortEmbedding J T)

/-- A leaf is translated to itself. -/
@[simp]
theorem embedCalls_pure {A : QReg} (y : W A) :
    (QuantumComp.pure (L := LocalSig.instruments.{v}) (spec := uSpec Q J) y).embedCalls ι =
      QuantumComp.pure y :=
  rfl

/-- Local operations are kept. -/
@[simp]
theorem embedCalls_primBind {A : QReg} (o : LocalSig.instruments.{v}.Op A)
    (k : (b : LocalSig.instruments.{v}.Outcome o) →
      QuantumComp LocalSig.instruments.{v} (uSpec Q J) W (LocalSig.instruments.{v}.next o b)) :
    (QuantumComp.primBind o k).embedCalls ι =
      QuantumComp.primBind o fun b ↦ (k b).embedCalls ι :=
  rfl

/-- A call of the port `q` becomes an embedding, a call of the port on `T` and a projection. -/
theorem embedCalls_queryBind {A : QReg} (q : Q) (F : QReg) (ℓ : A ≃ J q × F)
    (k : Unit → QuantumComp LocalSig.instruments.{v} (uSpec Q J) W (QReg.of (J q × F))) :
    (QuantumComp.queryBind (spec := uSpec Q J) q F ℓ k).embedCalls ι =
      QuantumComp.primBind (L := LocalSig.instruments.{v})
        ⟨PUnit, fun _ ↦ QReg.of (T × QReg.of (ι.G q × F)), (ι.embed q F ℓ)⟩
        fun _ ↦ QuantumComp.queryBind (A := QReg.of (T × QReg.of (ι.G q × F))) ()
          (QReg.of (ι.G q × F)) (Equiv.refl _) fun _ ↦
          QuantumComp.primBind (L := LocalSig.instruments.{v})
            ⟨PUnit, fun _ ↦ QReg.of (J q × F), (ι.project q F)⟩ fun _ ↦
            (k ()).embedCalls ι :=
  rfl

/-- **Budgets of calls through an embedding.** A program within the budget `b` makes at most the
total budget `∑ q, b q` of calls to the port on `T`. -/
theorem isQueryBound_embedCalls [Fintype Q] {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} (uSpec Q J) W A} {b : Q → ℕ}
    (hx : x.IsQueryBound b) : (x.embedCalls ι).IsQueryBound fun _ ↦ ∑ q, b q := by
  classical
  intro i
  apply IPFunctor.IFreeM.IsChargeBound.substitute (embedCallsSubstitution ι)
    (c := fun A c ↦ ∑ q, queryCharge q A c) ?_
    (IPFunctor.IFreeM.isChargeBound_sum _ b hx)
  intro A c
  change IsQueryBoundAt (embedCallsSubstitution ι A c) i _
  cases c with
  | prim o =>
    simp [embedCallsSubstitution, queryCharge, isQueryBoundAt_primBind_iff]
  | query q F ℓ =>
    cases i
    simp [embedCallsSubstitution, queryCharge, isQueryBoundAt_primBind_iff,
      isQueryBoundAt_queryBind_iff]

end QuantumComp

/-- The weight of the input of a call on the diagonal entries selected by `c` is the weight of the
state on the diagonal entries whose port input `c` selects. -/
theorem QuantumRuntime.sum_ite_callInput_apply {A J E : Type*} [Fintype A] [Fintype J]
    [Fintype E] [DecidableEq A] [DecidableEq J] [DecidableEq E] (ℓ : A ≃ J × E) {D : Type*}
    [Fintype D] [DecidableEq D] (c : J → Prop) [DecidablePred c] (ρ : Matrix (A × D) (A × D) ℂ) :
    (∑ a : J × D, if c a.1 then QuantumRuntime.callInput ℓ D ρ a a else 0) =
      ∑ a : A × D, if c (ℓ a.1).1 then ρ a a else 0 := by
  have hc : ∀ b : (J × D) × E, b.1.1 = (ℓ ((QuantumRuntime.queryEquivIn ℓ D).symm b).1).1 :=
    fun b ↦ by
      conv_lhs => rw [← (QuantumRuntime.queryEquivIn ℓ D).apply_symm_apply b]
      rfl
  conv_rhs => rw [← (QuantumRuntime.queryEquivIn ℓ D).symm.sum_comp
    (fun a : A × D ↦ if c (ℓ a.1).1 then ρ a a else 0), Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun a ↦ ?_
  simp only [QuantumRuntime.callInput, LinearMap.comp_apply, MatrixMap.traceRight_apply,
    SubInstrument.relabel_branch_apply, Matrix.submatrix_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun f _ ↦ ?_
    rw [← hc (a, f)]
    simp [h]
  · refine (Finset.sum_eq_zero fun f _ ↦ ?_).symm
    rw [← hc (a, f)]
    simp [h]

namespace EmulatedOracle

section embed

variable {Q : Type u} {J : Q → QReg} (E : EmulatedOracle Q J) {T : QReg}
  (ι : PortEmbedding J T) {U : Matrix (T × E.S) (T × E.S) ℂ}
  (hU : U ∈ Matrix.unitaryGroup (T × E.S) ℂ) {W : QReg → Type w}

/-- The matrix identity behind calls through an embedding: if the unitary `U` on `T`, beside
`G q` and compressed along the basis map of `q`, is the unitary of `q`, then the call on `T`,
regrouped for a call on `T × (G q × F)` and compressed along the basis map of `q` beside `F`, is
the call of `q`. -/
theorem embedCall_matrix
    (hcomp : ∀ q, (U ⊗ₖ (1 : Matrix (ι.G q) (ι.G q) ℂ)).submatrix (ι.withPrivate q E.S)
      (ι.withPrivate q E.S) = E.U q)
    (q : Q) (F : QReg) {A : QReg} (ℓ : A ≃ J q × F) :
    ((basisMatrix (ι.call q F))ᴴ ⊗ₖ (1 : Matrix E.S E.S ℂ)) *
        (basisMatrix (QuantumRuntime.queryEquivOut T E.S (QReg.of (ι.G q × F))) *
          (U ⊗ₖ (1 : Matrix (QReg.of (ι.G q × F)) (QReg.of (ι.G q × F)) ℂ)) *
          basisMatrix (QuantumRuntime.queryEquivIn (Equiv.refl (T × QReg.of (ι.G q × F))) E.S)) *
        (basisMatrix (ι.call q F ∘ ℓ) ⊗ₖ (1 : Matrix E.S E.S ℂ)) =
      basisMatrix (QuantumRuntime.queryEquivOut (J q) E.S F) * (E.U q ⊗ₖ (1 : Matrix F F ℂ)) *
        basisMatrix (QuantumRuntime.queryEquivIn ℓ E.S) := by
  rw [← Matrix.conjTranspose_one, ← Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    basisMatrix_kronecker_one, basisMatrix_kronecker_one,
    basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut T E.S _),
    basisMatrix_equiv_eq_conjTranspose (QuantumRuntime.queryEquivOut (J q) E.S F),
    conjTranspose_basisMatrix_mul_mul_basisMatrix, conjTranspose_basisMatrix_mul_mul_basisMatrix,
    conjTranspose_basisMatrix_mul_mul_basisMatrix, ← hcomp q]
  ext ⟨⟨y, f⟩, d⟩ ⟨a, d'⟩
  simp only [Matrix.submatrix_apply, Function.comp_apply, Prod.map, id, Matrix.kroneckerMap_apply,
    Matrix.one_apply, PortEmbedding.call, PortEmbedding.withPrivate,
    QuantumRuntime.queryEquivOut, QuantumRuntime.queryEquivIn, Equiv.symm_trans_apply,
    Equiv.prodAssoc_symm_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply,
    Equiv.prodComm_apply, Equiv.refl_apply, Prod.swap, Equiv.trans_apply, Equiv.symm_symm]
  by_cases hg : (ι.toFun q y).2 = (ι.toFun q (ℓ a).1).2 <;>
    by_cases hf : f = (ℓ a).2 <;> simp [hg, hf]

/-- **One call through an embedding.** Embedding the input of a call of the port `q`, calling
the port on `T`, and projecting back is the call of `q`. -/
theorem branch_project_comp_queryStep_comp_embed
    (hcomp : ∀ q, (U ⊗ₖ (1 : Matrix (ι.G q) (ι.G q) ℂ)).submatrix (ι.withPrivate q E.S)
      (ι.withPrivate q E.S) = E.U q)
    (q : Q) (F : QReg) {A : QReg} (ℓ : A ≃ J q × F) :
    ((ι.project.{u, v} q F).frame E.S).branch PUnit.unit ∘ₗ
      (((E.onePort U hU).toRuntime.queryStep (A := QReg.of (T × QReg.of (ι.G q × F))) ()
        (QReg.of (ι.G q × F)) (Equiv.refl _)).branch () ∘ₗ
        ((ι.embed.{u, v} q F ℓ).frame E.S).branch PUnit.unit) =
      (E.toRuntime.queryStep q F ℓ).branch () := by
  rw [(E.onePort U hU).toRuntime.queryStep_branch_eq_conj (M := U) rfl,
    E.toRuntime.queryStep_branch_eq_conj (M := E.U q) rfl, DSubInstrument.branch_frame_apply,
    DSubInstrument.branch_frame_apply]
  change LinearMap.comp ((MatrixMap.conj _).amplify E.S)
    (LinearMap.comp _ ((MatrixMap.conj _).amplify E.S)) = _
  rw [MatrixMap.amplify_conj, MatrixMap.amplify_conj, ← MatrixMap.conj_mul, ← MatrixMap.conj_mul]
  exact congrArg MatrixMap.conj
    ((Matrix.mul_assoc _ _ _).symm.trans (E.embedCall_matrix ι hcomp q F ℓ))

/-- **Calls through an embedding run as the original program**, when the unitary on `T`
compressed along each basis map is the unitary of the port. -/
theorem run_embedCalls
    (hcomp : ∀ q, (U ⊗ₖ (1 : Matrix (ι.G q) (ι.G q) ℂ)).submatrix (ι.withPrivate q E.S)
      (ι.withPrivate q E.S) = E.U q)
    {A : QReg} (x : QuantumComp LocalSig.instruments.{v} (uSpec Q J) W A) :
    (E.onePort U hU).toRuntime.run .instruments (x.embedCalls ι) =
      E.toRuntime.run .instruments x := by
  induction x using QuantumComp.inductionOn with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    exact congrArg (((LocalSig.Interp.instruments o).frame E.S).bind) (funext ih)
  | queryBind _ q F ℓ k ih =>
    simp only [QuantumComp.embedCalls_queryBind, QuantumRuntime.run_primBind,
      QuantumRuntime.run_queryBind]
    refine DSubInstrument.ext (funext fun p ↦ ?_)
    simp only [ih, DSubInstrument.branch_bind_apply_univ, Fintype.sum_unique, LinearMap.comp_assoc]
    exact congrArg (LinearMap.comp _)
      (branch_project_comp_queryStep_comp_embed.{u, v} E ι hU hcomp q F ℓ)

/-- **Calls through an embedding change no observed law.** -/
theorem outcomeLawWith_embedCalls
    (hcomp : ∀ q, (U ⊗ₖ (1 : Matrix (ι.G q) (ι.G q) ℂ)).submatrix (ι.withPrivate q E.S)
      (ι.withPrivate q E.S) = E.U q)
    {A : QReg} (x : QuantumComp LocalSig.instruments.{v} (uSpec Q J) W A) {γ : Type*}
    [MeasurableSpace γ] (ρ : SubState A) (f : (Σ u, W u) → γ) :
    (E.onePort U hU).toRuntime.evalDistMap .instruments (x.embedCalls ι) ρ f =
      E.toRuntime.evalDistMap .instruments x ρ f := by
  simp only [QuantumRuntime.evalDistMap, QuantumRuntime.jointPost,
    E.run_embedCalls ι hU hcomp x]

/-- **Calls through an embedding run losslessly** when the original program is lossless. The
translation itself is not syntactically lossless: the read-back after each call is a
contraction. -/
theorem lossless_run_embedCalls
    (hcomp : ∀ q, (U ⊗ₖ (1 : Matrix (ι.G q) (ι.G q) ℂ)).submatrix (ι.withPrivate q E.S)
      (ι.withPrivate q E.S) = E.U q)
    {A : QReg} {x : QuantumComp LocalSig.instruments.{v} (uSpec Q J) W A}
    (hx : x.Lossless .instruments) :
    ((E.onePort U hU).toRuntime.run .instruments (x.embedCalls ι)).Lossless := by
  rw [E.run_embedCalls ι hU hcomp x]
  exact E.toRuntime.lossless_run .instruments hx E.lossless_toRuntime_step

/-- The input of a call made through an embedding, weighted on the diagonal entries of `T × D`
selected by `c`, has the weight of the input of the original call on the entries whose image
under the basis map `c` selects. -/
theorem _root_.Quantum.PortEmbedding.sum_ite_callInput_embed (c : T → Prop) [DecidablePred c]
    (q : Q) (F : QReg) {A : QReg} (ℓ : A ≃ J q × F) {D : Type*} [Fintype D] [DecidableEq D]
    (ρ : Matrix (A × D) (A × D) ℂ) :
    (∑ a : T × D, if c a.1 then QuantumRuntime.callInput (Equiv.refl (T × QReg.of (ι.G q × F)))
      D (((ι.embed.{u, v} q F ℓ).frame D).branch PUnit.unit ρ) a a else 0) =
      ∑ a : J q × D, if c (ι.toFun q a.1).1 then QuantumRuntime.callInput ℓ D ρ a a else 0 := by
  refine (QuantumRuntime.sum_ite_callInput_apply (Equiv.refl _) c _).trans (Eq.trans ?_
    (QuantumRuntime.sum_ite_callInput_apply ℓ (fun y ↦ c (ι.toFun q y).1) ρ).symm)
  set g : A × D → (T × QReg.of (ι.G q × F)) × D := Prod.map (ι.call q F ∘ ℓ) id
  have hg : Function.Injective g :=
    ((ι.call_injective q F).comp ℓ.injective).prodMap Function.injective_id
  have h2 : ((ι.embed.{u, v} q F ℓ).frame D).branch PUnit.unit ρ =
      MatrixMap.conj (basisMatrix g) ρ := by
    rw [DSubInstrument.branch_frame_apply]
    change (MatrixMap.conj _).amplify D ρ = _
    rw [MatrixMap.amplify_conj, basisMatrix_kronecker_one]
  set w : (T × QReg.of (ι.G q × F)) × D → ℂ := fun b ↦ if c b.1.1 then 1 else 0
  have h3 : ∀ σ : Matrix ((T × QReg.of (ι.G q × F)) × D) ((T × QReg.of (ι.G q × F)) × D) ℂ,
      (∑ b : (T × QReg.of (ι.G q × F)) × D, if c ((Equiv.refl _) b.1).1 then σ b b else 0) =
        (Matrix.diagonal w * σ).trace := fun σ ↦ by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, w, ite_mul, one_mul,
      zero_mul, Equiv.refl_apply]
    rfl
  rw [h3, h2, MatrixMap.conj_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    conjTranspose_basisMatrix_mul_mul_basisMatrix, Matrix.submatrix_diagonal _ _ hg]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  refine Fintype.sum_congr _ _ fun a ↦ ?_
  change (if c (ι.toFun q (ℓ a.1).1).1 then (1 : ℂ) else 0) * ρ a a = _
  split_ifs <;> simp

/-- **Query weights of calls through an embedding, call by call.** For weights of the diagonal
form selected by `c` on `T`, and by `c` after the basis maps on the ports, the weight of the
`j`-th call of `x.embedCalls ι` is the weight of the `j`-th call of `x`. -/
theorem queryWeight_embedCalls
    (hcomp : ∀ q, (U ⊗ₖ (1 : Matrix (ι.G q) (ι.G q) ℂ)).submatrix (ι.withPrivate q E.S)
      (ι.withPrivate q E.S) = E.U q)
    (c : T → Prop) [DecidablePred c] {w₂ : Matrix (T × E.S) (T × E.S) ℂ → ℝ≥0∞}
    (hw₂ : ∀ σ, w₂ σ = ENNReal.ofReal (∑ a, if c a.1 then σ a a else 0).re)
    {w₁ : ∀ q, Matrix (J q × E.S) (J q × E.S) ℂ → ℝ≥0∞}
    (hw₁ : ∀ q σ, w₁ q σ = ENNReal.ofReal (∑ a, if c (ι.toFun q a.1).1 then σ a a else 0).re)
    {A : QReg} (x : QuantumComp LocalSig.instruments.{v} (uSpec Q J) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (j : ℕ) :
    (E.onePort U hU).toRuntime.queryWeight .instruments (fun _ ↦ w₂) (x.embedCalls ι) ρ j =
      E.toRuntime.queryWeight .instruments w₁ x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih => exact tsum_congr fun b ↦ ih b _ j
  | queryBind _ q F ℓ k ih =>
    cases j with
    | zero =>
      change ∑' b : PUnit.{v + 1}, w₂ (QuantumRuntime.callInput
          (Equiv.refl (T × QReg.of (ι.G q × F))) E.S
            (((ι.embed.{u, v} q F ℓ).frame E.S).branch b ρ)) =
        w₁ q (QuantumRuntime.callInput ℓ E.S ρ)
      rw [tsum_fintype, Fintype.sum_unique, hw₂, hw₁]
      exact congrArg (fun z : ℂ ↦ ENNReal.ofReal z.re)
        (PortEmbedding.sum_ite_callInput_embed.{u, v} ι c q F ℓ ρ)
    | succ j =>
      change ∑' b : PUnit.{v + 1}, ∑' r : Unit, ∑' b' : PUnit.{v + 1},
          (E.onePort U hU).toRuntime.queryWeight .instruments (fun _ ↦ w₂)
            ((k ()).embedCalls ι) (((ι.project.{u, v} q F).frame E.S).branch b'
              (((E.onePort U hU).toRuntime.queryStep
                (A := QReg.of (T × QReg.of (ι.G q × F))) () (QReg.of (ι.G q × F))
                (Equiv.refl _)).branch r (((ι.embed.{u, v} q F ℓ).frame E.S).branch b ρ))) j =
        ∑' r : Unit, E.toRuntime.queryWeight .instruments w₁ (k r)
          ((E.toRuntime.queryStep q F ℓ).branch r ρ) j
      simp only [tsum_fintype, Fintype.sum_unique]
      exact (congrArg (fun σ ↦ (E.onePort U hU).toRuntime.queryWeight .instruments
          (fun _ ↦ w₂) ((k ()).embedCalls ι) σ j)
        (LinearMap.congr_fun
          (branch_project_comp_queryStep_comp_embed.{u, v} E ι hU hcomp q F ℓ) ρ)).trans
        (ih () _ j)

/-- **Query masses of calls through an embedding.** The query mass of the port on `T` is the
summed query mass of the ports. -/
theorem queryMass_embedCalls
    (hcomp : ∀ q, (U ⊗ₖ (1 : Matrix (ι.G q) (ι.G q) ℂ)).submatrix (ι.withPrivate q E.S)
      (ι.withPrivate q E.S) = E.U q)
    {A : QReg} (x : QuantumComp LocalSig.instruments.{v} (uSpec Q J) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) :
    (E.onePort U hU).toRuntime.queryMass .instruments (x.embedCalls ι) ρ () =
      ∑' j, E.toRuntime.queryWeight .instruments (fun _ σ ↦ ENNReal.ofReal σ.trace.re) x ρ j := by
  rw [QuantumRuntime.queryMass_eq_totalWeight]
  refine tsum_congr fun j ↦ (congrArg (fun w ↦ (E.onePort U hU).toRuntime.queryWeight
    .instruments w (x.embedCalls ι) ρ j) (funext fun i' ↦ funext fun σ ↦ ?_)).trans
    (E.queryWeight_embedCalls ι hU hcomp (fun _ ↦ True)
      (w₂ := fun σ ↦ ENNReal.ofReal σ.trace.re) (fun σ ↦ ?_) (fun q σ ↦ ?_) x ρ j) <;>
    simp [Matrix.trace]

end embed

end EmulatedOracle

/-! ## Classical-port programs as coherent programs -/

namespace EmulatedOracle

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The embedding of the port registers into the coherent register: the basis vector `|x⟩` of
the port `i` goes to `|⟨i, x⟩⟩`, with nothing beside it. -/
@[expose]
def sigmaEmbedding (In : P → QReg) : PortEmbedding In (cohIn In) where
  G _ := QReg.of Unit
  toFun i x := (⟨i, x⟩, ())
  injective i := by
    rintro x x' h
    simp only [Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and, and_true] at h
    exact h

variable {In : P → QReg} (E : EmulatedOracle P In)

/-- The entries of the coherent unitary on a summand are the entries of the unitary of the
port. -/
theorem coherent_U_apply_self (i : P) (a a' : In i) (d d' : E.S) :
    E.coherent.U () (⟨i, a⟩, d) (⟨i, a'⟩, d') = E.U i (a, d) (a', d') := by
  change Matrix.blockDiagonal' E.U ⟨i, (a, d)⟩ ⟨i, (a', d')⟩ = _
  exact Matrix.blockDiagonal'_apply_eq _ _ _ _

/-- The coherent unitary does not mix different summands. -/
theorem coherent_U_apply_of_ne {i i' : P} (h : i ≠ i') (a : In i) (a' : In i') (d d' : E.S) :
    E.coherent.U () (⟨i, a⟩, d) (⟨i', a'⟩, d') = 0 := by
  change Matrix.blockDiagonal' E.U ⟨i, (a, d)⟩ ⟨i', (a', d')⟩ = _
  exact Matrix.blockDiagonal'_apply_ne _ _ _ h

/-- **The coherent unitary respects the index**: it sends the block of each index into itself,
`(Pᵢ ⊗ 1) U (Pᵢ ⊗ 1) = U (Pᵢ ⊗ 1)` for the projectors `Quantum.EmulatedOracle.cohIndexProj`. By
`Quantum.Hybrid.RespectsIndex.sub`, so does the difference of two coherent unitaries, as the
square-root hybrid bounds of `VCVio.Quantum.Comp.HybridIndex` require. -/
theorem respectsIndex_coherent_U :
    Hybrid.RespectsIndex (spec := cohSpec In) (fun _ ↦ cohIndexProj In)
      (fun _ ↦ cohIndexProj In) fun _ _ ↦ E.coherent.U () := fun _ _ i ↦ by
  beta_reduce
  rw [← indexProj_eq_kronecker]
  ext ⟨⟨k, a⟩, d⟩ ⟨⟨k', a'⟩, d'⟩
  rw [indexProj, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : k = k'
  · subst h
    by_cases hk : k = i <;> simp [hk]
  · rw [E.coherent_U_apply_of_ne h]
    simp

/-- The coherent unitary compressed on the summand `i` is the unitary of the port `i`. -/
theorem coherent_compress_sigmaEmbedding (i : P) :
    (E.coherent.U () ⊗ₖ (1 : Matrix ((sigmaEmbedding In).G i) ((sigmaEmbedding In).G i) ℂ)
      ).submatrix ((sigmaEmbedding In).withPrivate i E.S)
        ((sigmaEmbedding In).withPrivate i E.S) = E.U i := by
  ext ⟨y, d⟩ ⟨y', d'⟩
  change E.coherent.U () (⟨i, y⟩, d) (⟨i, y'⟩, d') * (1 : Matrix Unit Unit ℂ) () () = _
  rw [Matrix.one_apply_eq, mul_one]
  exact E.coherent_U_apply_self i y y' d d'

end EmulatedOracle

namespace QuantumComp

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} {W : QReg → Type w}

open EmulatedOracle in
/-- **Classical-port programs as coherent programs** (design §2.5). A call of the port `i` on
`In i × F` becomes a call of the coherent port: before it, the input is moved into the summand `i`
of the coherent register; after it, the summand `i` is read back
(`Quantum.QuantumComp.embedCalls` along `Quantum.EmulatedOracle.sigmaEmbedding`). No weight is
lost, since the coherent unitary preserves the summand `i`
(`Quantum.EmulatedOracle.run_toCoherent`). The read-back is not trace preserving on the whole
coherent register, so `toCoherent` is not syntactically lossless, even though its runs are those
of the original program. -/
@[expose]
noncomputable def toCoherent {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A) :
    QuantumComp LocalSig.instruments.{v} (cohSpec In) W A :=
  x.embedCalls (sigmaEmbedding In)

/-- **Budgets of the coherent translation.** A program within the budget `b` makes, through the
coherent port, at most the total budget `∑ i, b i` of calls. -/
theorem isQueryBound_toCoherent {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A} {b : P → ℕ}
    (hx : x.IsQueryBound b) : x.toCoherent.IsQueryBound fun _ ↦ ∑ i, b i :=
  isQueryBound_embedCalls _ hx

end QuantumComp

namespace EmulatedOracle

section bridge

variable {P : Type} [Fintype P] [DecidableEq P] {In : P → QReg} (E : EmulatedOracle P In)
  {W : QReg → Type w}

/-- **The coherent translation runs as the original program.** Run against the coherent oracle,
`x.toCoherent` has the branches that `x` has against the runtime with one port per unitary. -/
theorem run_toCoherent {A : QReg} (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A) :
    E.coherent.toRuntime.run .instruments x.toCoherent = E.toRuntime.run .instruments x :=
  E.run_embedCalls (sigmaEmbedding In) (E.coherent.unitary ()) E.coherent_compress_sigmaEmbedding x

/-- **The coherent translation changes no observed law.** -/
theorem outcomeLawWith_toCoherent {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A) {γ : Type*} [MeasurableSpace γ]
    (ρ : SubState A) (f : (Σ u, W u) → γ) :
    E.coherent.toRuntime.evalDistMap .instruments x.toCoherent ρ f =
      E.toRuntime.evalDistMap .instruments x ρ f :=
  E.outcomeLawWith_embedCalls (sigmaEmbedding In) (E.coherent.unitary ())
    E.coherent_compress_sigmaEmbedding x ρ f

/-- **The coherent translation of a lossless program runs losslessly.** -/
theorem lossless_run_toCoherent {A : QReg}
    {x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A} (hx : x.Lossless .instruments) :
    (E.coherent.toRuntime.run .instruments x.toCoherent).Lossless :=
  E.lossless_run_embedCalls (sigmaEmbedding In) (E.coherent.unitary ())
    E.coherent_compress_sigmaEmbedding hx

/-- **Masses of the coherent translation, call by call.** For a weight on the ports of `x` that
is the trace on the port `i` and zero elsewhere, the weight of the `j`-th call of `x` is the
mass on `i` of the `j`-th call of `x.toCoherent`. -/
theorem queryWeight_toCoherent (i : P)
    {w : ∀ i', Matrix ((uSpec P In).In i' × E.S) ((uSpec P In).In i' × E.S) ℂ → ℝ≥0∞}
    (hw : ∀ i' σ, w i' σ = if i' = i then ENNReal.ofReal σ.trace.re else 0) {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (j : ℕ) :
    E.coherent.toRuntime.queryWeight .instruments
        (fun _ σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re) x.toCoherent ρ j =
      E.toRuntime.queryWeight .instruments w x ρ j := by
  refine E.queryWeight_embedCalls (sigmaEmbedding In) (E.coherent.unitary ())
    E.coherent_compress_sigmaEmbedding (fun a ↦ a.1 = i)
    (w₂ := fun σ ↦ ENNReal.ofReal (MatrixMap.conj (E.indexProj i) σ).trace.re)
    (fun σ ↦ by rw [E.trace_conj_indexProj]) (fun i' σ ↦ ?_) x ρ j
  rw [hw]
  by_cases h : i' = i <;> simp [h, sigmaEmbedding, Matrix.trace]

/-- **Masses of the coherent translation** (design §2.5): the total mass on `i` of
`x.toCoherent` against the coherent oracle is the query mass of the port `i` of `x` against the
runtime with one port per unitary. -/
theorem totalMass_toCoherent {A : QReg}
    (x : QuantumComp LocalSig.instruments.{v} (uSpec P In) W A)
    (ρ : Matrix (A × E.S) (A × E.S) ℂ) (i : P) :
    E.totalMass .instruments x.toCoherent ρ i = E.toRuntime.queryMass .instruments x ρ i := by
  rw [QuantumRuntime.queryMass_eq_totalWeight]
  exact tsum_congr fun j ↦ E.queryWeight_toCoherent i
    (fun i' σ ↦ by by_cases h : i' = i <;> simp [h]) x ρ j

end bridge

end EmulatedOracle

end Quantum

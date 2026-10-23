/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.QueryMass
public import VCVio.Quantum.Comp.Simulation
public import VCVio.Quantum.Comp.Subsystem
public import VCVio.Quantum.MatrixMap.Kraus
public import VCVio.Quantum.MatrixMap.Norm

/-!
# The square-root hybrid bound for general programs

Two runtimes on the same private register `D` whose steps are Kraus maps, `s₀ i` with branches
`conj (U i r)` and `s₁ i` with branches `conj (W i r)`, run the same program to nearby states.
For any observable, the square roots of the two observed weights differ by at most the sum over
the calls `j` of the square roots of the *Kraus weights* `∑ᵣ tr ((U − W) σ (U − W)ᴴ)` of the
inputs `σ` of the `j`-th calls of the program run against the first runtime
(`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le`). This is the core of the
square-root hybrid argument of ePrint 2025/2166 (Lemma 5.7), for general programs: adaptive,
with local operations interpreted as arbitrary instruments with countably many outcomes, and
against runtimes whose branches are contractions.

A Kraus weight is at most the query mass times `∑ᵣ ‖U i r − W i r‖²` for the `ℓ²` operator norm
(`Quantum.QuantumRuntime.krausWeight_le`), which gives the bound in terms of the query masses of
the ports (`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le_mass`). The masses of
ePrint 2025/2166, §4.2, are those of a coherent index register, with the operator norm of each
block; that form is in `VCVio.Quantum.Comp.HybridIndex`.

## The controlled runtime

The paper compares the pure states of the two runs. A program with mixed local operations has no
pure state to compare, so the proof runs both runtimes coherently instead: the controlled runtime
on `D × Bool` applies `U i r` on the branch `false` and `W i r` on the branch `true`. Its
branches reduce to the two runtimes (`Quantum.QuantumRuntime.simulation`), and the square root of
the trace of the difference of its two branches obeys a triangle inequality at every call. The
countably many outcomes of local operations and calls are handled by the `ℓ²` Minkowski
inequality for series (`Quantum.rpow_inv_two_tsum_le_of_le_add_tsum`), so the bound needs no
finiteness hypothesis.

## Main definitions

* `Quantum.QuantumRuntime.krausWeight F`: the weight `∑ᵣ tr (F i r σ (F i r)ᴴ)` of a family of
  operators on the inputs of the calls of port `i`.

## Main statements

* `Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le` and its converse
  `rpow_inv_two_tsum_trace_conj_run_le'`: the square-root hybrid bound for observables given by
  contractions on the leaves.
* `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le` and its converse: the bound for the
  laws of observations of the leaves.
* `Quantum.QuantumRuntime.krausWeight_le`, and the bound in terms of the query masses of every
  call, `Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le_mass`.
* `Quantum.QuantumRuntime.tsum_rpow_inv_two_queryWeight_le_of_isQueryBound` (Cauchy–Schwarz over
  the calls of a program within a query budget) and the resulting bound by total masses,
  `Quantum.QuantumRuntime.rpow_inv_two_outcomeLawWith_le_of_isQueryBound`.
-/

public section

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

universe u v u₁ v₁ w

namespace Quantum

/-! ## Two-branch block matrices -/

namespace Hybrid

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The isometry `|d⟩ ↦ |d, b⟩` of `D` onto the branch `b` of `D × Bool`. -/
@[expose]
def inj (D : Type*) [DecidableEq D] (b : Bool) : Matrix (D × Bool) D ℂ :=
  Matrix.of fun p d ↦ if p = (d, b) then 1 else 0

/-- The two branch isometries are orthogonal. -/
theorem conjTranspose_inj_mul_inj (b c : Bool) :
    (inj D b)ᴴ * inj D c = if b = c then 1 else 0 := by
  ext d d'
  by_cases hbc : b = c
  · subst hbc
    by_cases hd : d = d'
    · subst hd
      simp [inj, Matrix.mul_apply]
    · simp [inj, Matrix.mul_apply, hd, Ne.symm hd]
  · simp [inj, Matrix.mul_apply, hbc, Ne.symm hbc]

/-- The two branch isometries cover `D × Bool`. -/
theorem inj_mul_conjTranspose_add :
    inj D false * (inj D false)ᴴ + inj D true * (inj D true)ᴴ = 1 := by
  ext ⟨d, b⟩ ⟨d', b'⟩
  cases b <;> cases b' <;> by_cases hd : d = d' <;>
    simp [inj, Matrix.mul_apply, Matrix.one_apply, hd]

variable (Y : Type*) [Fintype Y] [DecidableEq Y]

/-- The co-isometry of `Y × (D × Bool)` onto the branch `b`: `1 ⊗ (inj b)ᴴ`. -/
@[expose]
def sel (b : Bool) : Matrix (Y × D) (Y × (D × Bool)) ℂ :=
  (1 : Matrix Y Y ℂ) ⊗ₖ (inj D b)ᴴ

/-- The difference of the two branch co-isometries. -/
@[expose]
def seld : Matrix (Y × D) (Y × (D × Bool)) ℂ :=
  (1 : Matrix Y Y ℂ) ⊗ₖ (inj D false - inj D true)ᴴ

variable {Y}

omit [Fintype D] [Fintype Y] in
theorem seld_eq : seld (D := D) Y = sel Y false - sel Y true := by
  ext ⟨y, d⟩ ⟨y', p⟩
  simp [seld, sel, Matrix.kroneckerMap_apply, mul_sub]

theorem sel_mul_conjTranspose_sel (b c : Bool) :
    sel (D := D) Y b * (sel Y c)ᴴ = (if b = c then 1 else 0 : Matrix (Y × D) (Y × D) ℂ) := by
  rw [sel, sel, conjTranspose_kronecker, conjTranspose_one, conjTranspose_conjTranspose,
    ← mul_kronecker_mul, Matrix.one_mul, conjTranspose_inj_mul_inj]
  split_ifs <;> simp

theorem conjTranspose_sel_mul_sel_add :
    (sel (D := D) Y false)ᴴ * sel Y false + (sel Y true)ᴴ * sel Y true =
      (1 : Matrix (Y × (D × Bool)) (Y × (D × Bool)) ℂ) := by
  simp only [sel, conjTranspose_kronecker, conjTranspose_one, conjTranspose_conjTranspose,
    ← mul_kronecker_mul, Matrix.one_mul, ← kronecker_add, inj_mul_conjTranspose_add,
    one_kronecker_one]

theorem conj_sel (b : Bool) :
    MatrixMap.conj (sel (D := D) Y b) = (MatrixMap.conj (inj D b)ᴴ).amplifyLeft Y :=
  (MatrixMap.amplifyLeft_conj _).symm

theorem conj_seld :
    MatrixMap.conj (seld (D := D) Y) =
      (MatrixMap.conj (inj D false - inj D true)ᴴ).amplifyLeft Y :=
  (MatrixMap.amplifyLeft_conj _).symm

variable {O J : Type*} [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]

/-- The controlled operator that applies `K₀` on the branch `false` and `K₁` on the branch
`true`. -/
@[expose]
def ctrl (K₀ K₁ : Matrix (O × D) (J × D) ℂ) : Matrix (O × (D × Bool)) (J × (D × Bool)) ℂ :=
  (sel O false)ᴴ * K₀ * sel J false + (sel O true)ᴴ * K₁ * sel J true

theorem sel_false_mul_ctrl (K₀ K₁ : Matrix (O × D) (J × D) ℂ) :
    sel O false * ctrl K₀ K₁ = K₀ * sel J false := by
  simp only [ctrl, Matrix.mul_add, ← Matrix.mul_assoc, sel_mul_conjTranspose_sel]
  simp

theorem sel_true_mul_ctrl (K₀ K₁ : Matrix (O × D) (J × D) ℂ) :
    sel O true * ctrl K₀ K₁ = K₁ * sel J true := by
  simp only [ctrl, Matrix.mul_add, ← Matrix.mul_assoc, sel_mul_conjTranspose_sel]
  simp

theorem conjTranspose_ctrl_mul_ctrl (K₀ K₁ : Matrix (O × D) (J × D) ℂ) :
    (ctrl K₀ K₁)ᴴ * ctrl K₀ K₁ =
      (sel J false)ᴴ * (K₀ᴴ * K₀) * sel J false + (sel J true)ᴴ * (K₁ᴴ * K₁) * sel J true := by
  have h : (ctrl K₀ K₁)ᴴ =
      (sel J false)ᴴ * K₀ᴴ * sel O false + (sel J true)ᴴ * K₁ᴴ * sel O true := by
    simp [ctrl, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [h, Matrix.add_mul, Matrix.mul_assoc _ (sel O false), sel_false_mul_ctrl,
    Matrix.mul_assoc _ (sel O true), sel_true_mul_ctrl]
  simp only [Matrix.mul_assoc]

theorem seld_mul_ctrl (K₀ K₁ : Matrix (O × D) (J × D) ℂ) :
    seld O * ctrl K₀ K₁ = (K₀ - K₁) * sel J false + K₁ * seld J := by
  rw [seld_eq, seld_eq, Matrix.sub_mul, sel_false_mul_ctrl, sel_true_mul_ctrl, Matrix.sub_mul,
    Matrix.mul_sub]
  abel

theorem posSemidef_one_sub_sum_ctrl {α : Type*} (s : Finset α)
    {K₀ K₁ : α → Matrix (O × D) (J × D) ℂ}
    (h₀ : (1 - ∑ r ∈ s, (K₀ r)ᴴ * K₀ r).PosSemidef)
    (h₁ : (1 - ∑ r ∈ s, (K₁ r)ᴴ * K₁ r).PosSemidef) :
    (1 - ∑ r ∈ s, (ctrl (K₀ r) (K₁ r))ᴴ * ctrl (K₀ r) (K₁ r)).PosSemidef := by
  have h : 1 - ∑ r ∈ s, (ctrl (K₀ r) (K₁ r))ᴴ * ctrl (K₀ r) (K₁ r) =
      (sel J false)ᴴ * (1 - ∑ r ∈ s, (K₀ r)ᴴ * K₀ r) * sel J false +
        (sel J true)ᴴ * (1 - ∑ r ∈ s, (K₁ r)ᴴ * K₁ r) * sel J true := by
    simp only [conjTranspose_ctrl_mul_ctrl, Finset.sum_add_distrib, Matrix.mul_sum,
      Matrix.sum_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [← conjTranspose_sel_mul_sel_add (D := D) (Y := J)]
    abel
  rw [h]
  exact (h₀.conjTranspose_mul_mul_same _).add (h₁.conjTranspose_mul_mul_same _)

/-- The Kraus operators of a subinstrument whose branches are Kraus maps have
`1 - ∑ r ∈ s, (K r)ᴴ * K r` positive semidefinite on every finite set of outcomes. -/
theorem _root_.Quantum.SubInstrument.posSemidef_one_sub_sum_of_branch_eq_conj {A B α : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] (p : SubInstrument A B α) {K : α → Matrix B A ℂ}
    (hK : ∀ r, p.branch r = MatrixMap.conj (K r)) (s : Finset α) :
    (1 - ∑ r ∈ s, (K r)ᴴ * K r).PosSemidef := by
  have h := p.isTNI_sum s
  simp_rw [hK] at h
  rw [← Finset.sum_coe_sort s] at h ⊢
  exact MatrixMap.isTNI_sum_conj_iff.mp h

/-- The controlled step: the subinstrument with branches `conj (ctrl (K₀ r) (K₁ r))`. -/
@[expose]
noncomputable def ctrlStep {α : Type*} (K₀ K₁ : α → Matrix (O × D) (J × D) ℂ)
    (h₀ : ∀ s : Finset α, (1 - ∑ r ∈ s, (K₀ r)ᴴ * K₀ r).PosSemidef)
    (h₁ : ∀ s : Finset α, (1 - ∑ r ∈ s, (K₁ r)ᴴ * K₁ r).PosSemidef) :
    SubInstrument (J × (D × Bool)) (O × (D × Bool)) α :=
  SubInstrument.ofIsTNISum (fun r ↦ MatrixMap.conj (ctrl (K₀ r) (K₁ r)))
    (fun _ ↦ MatrixMap.isCP_conj _) fun s ↦ by
    rw [← Finset.sum_coe_sort s]
    refine MatrixMap.isTNI_sum_conj_iff.mpr ?_
    rw [Finset.sum_coe_sort s (fun r ↦ (ctrl (K₀ r) (K₁ r))ᴴ * ctrl (K₀ r) (K₁ r))]
    exact posSemidef_one_sub_sum_ctrl s (h₀ s) (h₁ s)

/-- The squared distance between the two branches of an operator on `Y × (D × Bool)`: the trace
of `seld Y * Z * (seld Y)ᴴ`. -/
@[expose]
noncomputable def branchDist (Z : Matrix (Y × (D × Bool)) (Y × (D × Bool)) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (MatrixMap.conj (seld Y) Z).trace.re

theorem branchDist_zero :
    branchDist (D := D) (0 : Matrix (Y × (D × Bool)) (Y × (D × Bool)) ℂ) = 0 := by
  simp [branchDist]

theorem branchDist_tsum {ι : Type*} {f : ι → Matrix (Y × (D × Bool)) (Y × (D × Bool)) ℂ}
    (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef) :
    branchDist (∑' b, f b) = ∑' b, branchDist (f b) := by
  rw [branchDist, MatrixMap.map_tsum _ hf]
  exact ofReal_trace_re_tsum (MatrixMap.summable_comp _ hf)
    fun b ↦ (hpos b).mul_mul_conjTranspose_same _

end Hybrid

namespace MatrixMap

variable {A B R S : Type*} [Fintype A] [Fintype B] [Fintype R]

/-- Kraus maps of `1 ⊗ K` commute with amplification on the left factor. -/
theorem conj_one_kronecker_amplify_apply [DecidableEq A] [DecidableEq B] (K : Matrix S R ℂ)
    (Φ : MatrixMap A B)
    (Z : Matrix (A × R) (A × R) ℂ) :
    conj ((1 : Matrix B B ℂ) ⊗ₖ K) (Φ.amplify R Z) =
      Φ.amplify S (conj ((1 : Matrix A A ℂ) ⊗ₖ K) Z) := by
  rw [← amplifyLeft_conj, ← amplifyLeft_conj, ← LinearMap.comp_apply,
    ← amplify_comp_amplifyLeft, LinearMap.comp_apply]

/-- The trace of a Kraus map of `X ⊗ 1` is the trace of the Kraus map of `X` on the partial
trace. -/
theorem trace_conj_kronecker_one_apply [DecidableEq R] (X : Matrix B A ℂ)
    (Z : Matrix (A × R) (A × R) ℂ) :
    (conj (X ⊗ₖ (1 : Matrix R R ℂ)) Z).trace = (conj X (traceRight A R Z)).trace := by
  rw [← amplify_conj, ← trace_traceRight, ← LinearMap.comp_apply, traceRight_comp_amplify,
    LinearMap.comp_apply]

omit [Fintype A] [Fintype B] in
theorem mul_kronecker_one {C : Type*} [Fintype C] [DecidableEq R] (X : Matrix B C ℂ)
    (Y : Matrix C A ℂ) :
    (X * Y) ⊗ₖ (1 : Matrix R R ℂ) = (X ⊗ₖ (1 : Matrix R R ℂ)) * (Y ⊗ₖ (1 : Matrix R R ℂ)) := by
  rw [← mul_kronecker_mul, Matrix.one_mul]

end MatrixMap

namespace Hybrid

variable {D : Type*} [Fintype D] [DecidableEq D] {Y Y' : Type*} [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

/-- The squared distance of the branches after a map on the other factor. -/
theorem branchDist_amplify (Φ : MatrixMap Y Y') (Z : Matrix (Y × (D × Bool)) (Y × (D × Bool)) ℂ) :
    branchDist (Φ.amplify (D × Bool) Z) =
      ENNReal.ofReal (Φ.amplify D (MatrixMap.conj (seld Y) Z)).trace.re := by
  rw [branchDist, seld, seld, MatrixMap.conj_one_kronecker_amplify_apply]

/-- Selecting a branch commutes with a map on the other factor. -/
theorem conj_sel_amplify (Φ : MatrixMap Y Y') (b : Bool)
    (Z : Matrix (Y × (D × Bool)) (Y × (D × Bool)) ℂ) :
    MatrixMap.conj (sel Y' b) (Φ.amplify (D × Bool) Z) =
      Φ.amplify D (MatrixMap.conj (sel Y b) Z) :=
  MatrixMap.conj_one_kronecker_amplify_apply _ _ _

/-- Both branches of `T ρ Tᴴ`, for `T = (sel Y false)ᴴ + (sel Y true)ᴴ`, are `ρ`. -/
theorem conj_sel_conj_add (b : Bool) (ρ : Matrix (Y × D) (Y × D) ℂ) :
    MatrixMap.conj (sel Y b) (MatrixMap.conj ((sel Y false)ᴴ + (sel Y true)ᴴ) ρ) = ρ := by
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul, Matrix.mul_add, sel_mul_conjTranspose_sel,
    sel_mul_conjTranspose_sel]
  cases b <;> simp [MatrixMap.conj_one]

/-- The two branches of `T ρ Tᴴ`, for `T = (sel Y false)ᴴ + (sel Y true)ᴴ`, are at distance
zero. -/
theorem conj_seld_conj_add (ρ : Matrix (Y × D) (Y × D) ℂ) :
    MatrixMap.conj (seld Y) (MatrixMap.conj ((sel Y false)ᴴ + (sel Y true)ᴴ) ρ) = 0 := by
  rw [← LinearMap.comp_apply, ← MatrixMap.conj_mul]
  simp [seld_eq, Matrix.sub_mul, Matrix.mul_add, sel_mul_conjTranspose_sel, MatrixMap.conj_zero]

variable {Z : Type*} [Fintype Z] (K : Matrix Z (Y × D) ℂ) (hK : (1 - Kᴴ * K).PosSemidef)
  {Γ : Matrix (Y × (D × Bool)) (Y × (D × Bool)) ℂ} (hΓ : Γ.PosSemidef)
include hK hΓ

theorem re_trace_conj_mul_seld_le :
    (MatrixMap.conj (K * seld Y) Γ).trace.re ≤ (MatrixMap.conj (seld Y) Γ).trace.re := by
  rw [MatrixMap.conj_mul, LinearMap.comp_apply]
  exact MatrixMap.isTNI_conj hK _ (hΓ.mul_mul_conjTranspose_same _)

/-- **At a leaf.** For a contraction `K`, the square root of the weight of `K` on the branch
`false` is at most that on the branch `true` plus the square root of the squared distance of the
branches. -/
theorem ofReal_trace_conj_sel_false_rpow_le :
    ENNReal.ofReal (MatrixMap.conj K (MatrixMap.conj (sel Y false) Γ)).trace.re ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (MatrixMap.conj K (MatrixMap.conj (sel Y true) Γ)).trace.re ^ (2⁻¹ : ℝ) +
        branchDist Γ ^ (2⁻¹ : ℝ) := by
  rw [← LinearMap.comp_apply (MatrixMap.conj K), ← MatrixMap.conj_mul,
    ← LinearMap.comp_apply (MatrixMap.conj K), ← MatrixMap.conj_mul]
  have he : K * sel Y false = K * sel Y true + K * seld Y := by
    rw [seld_eq, Matrix.mul_sub]
    abel
  rw [he]
  refine (MatrixMap.ofReal_trace_conj_add_rpow_le hΓ _ _).trans (add_le_add le_rfl ?_)
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (re_trace_conj_mul_seld_le K hK hΓ))
    (by norm_num)

/-- **At a leaf**, the converse bound. -/
theorem ofReal_trace_conj_sel_true_rpow_le :
    ENNReal.ofReal (MatrixMap.conj K (MatrixMap.conj (sel Y true) Γ)).trace.re ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (MatrixMap.conj K (MatrixMap.conj (sel Y false) Γ)).trace.re ^ (2⁻¹ : ℝ) +
        branchDist Γ ^ (2⁻¹ : ℝ) := by
  rw [← LinearMap.comp_apply (MatrixMap.conj K), ← MatrixMap.conj_mul,
    ← LinearMap.comp_apply (MatrixMap.conj K), ← MatrixMap.conj_mul]
  have he : K * sel Y true = K * sel Y false - K * seld Y := by
    rw [seld_eq, Matrix.mul_sub]
    abel
  rw [he]
  refine (MatrixMap.ofReal_trace_conj_sub_rpow_le hΓ _ _).trans (add_le_add le_rfl ?_)
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (re_trace_conj_mul_seld_le K hK hΓ))
    (by norm_num)

end Hybrid

namespace QuantumRuntime

open Hybrid SubInstrument

/-! ## Kraus weights -/

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {X : QReg → Type w} {A : QReg}

/-- **Kraus weight.** For a family `F i r` of operators from the input to the output of port
`i`, the weight `∑ᵣ tr (F i r σ (F i r)ᴴ)` of an input `σ` of a call of `i`. With `F = U - W`
the difference of the Kraus operators of two steps, it measures how far apart the two steps take
`σ`. -/
@[expose]
noncomputable def krausWeight {D : QReg}
    (F : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ) (i : spec.Port)
    (σ : Matrix (spec.In i × D) (spec.In i × D) ℂ) : ℝ≥0∞ :=
  ∑' r, ENNReal.ofReal (MatrixMap.conj (F i r) σ).trace.re

section L2Operator

open scoped Matrix.Norms.L2Operator

/-- **Kraus weights by operator norms.** On a positive semidefinite input, the Kraus weight of
`F` is at most `∑ᵣ ‖F i r‖²` times the trace of the input, for the `ℓ²` operator norm. -/
theorem krausWeight_le {D : QReg}
    (F : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ) (i : spec.Port)
    {σ : Matrix (spec.In i × D) (spec.In i × D) ℂ} (hσ : σ.PosSemidef) :
    krausWeight F i σ ≤ (∑' r, ENNReal.ofReal (‖F i r‖ ^ 2)) * ENNReal.ofReal σ.trace.re := by
  rw [krausWeight, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun r ↦ ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (MatrixMap.re_trace_conj_le _ hσ)

end L2Operator

/-! ## Programs within a query budget -/

/-- **Cauchy–Schwarz over the calls.** For a program within a finite query budget `b` that
vanishes outside `t`, the sum over the calls of the square roots of the weights is at most the
square root of the number `q = ∑ i ∈ t, b i` of calls times the summed weights. -/
theorem tsum_rpow_inv_two_queryWeight_le_of_isQueryBound (R : QuantumRuntime spec)
    {w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    ∑' j, R.queryWeight I w x ρ j ^ (2⁻¹ : ℝ) ≤
      (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' j, R.queryWeight I w x ρ j) ^ (2⁻¹ : ℝ) := by
  have hz : ∀ j ∉ Finset.range (∑ i ∈ t, b i), R.queryWeight I w x ρ j ^ (2⁻¹ : ℝ) = 0 :=
    fun j hj ↦ by
      rw [R.queryWeight_eq_zero_of_isQueryBound I hx t ht (by simpa using hj) ρ,
        ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [tsum_eq_sum hz, ENNReal.le_rpow_inv_iff (by norm_num)]
  calc (∑ j ∈ Finset.range (∑ i ∈ t, b i), R.queryWeight I w x ρ j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)
      ≤ ((Finset.range (∑ i ∈ t, b i)).card : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
          ∑ j ∈ Finset.range (∑ i ∈ t, b i), (R.queryWeight I w x ρ j ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ (by norm_num)
    _ = ((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) *
          ∑ j ∈ Finset.range (∑ i ∈ t, b i), R.queryWeight I w x ρ j := by
        simp only [Finset.card_range, rpow_inv_two_rpow_two]
        norm_num
    _ ≤ _ := by
        gcongr
        exact ENNReal.sum_le_tsum _

/-! ## The controlled runtime -/

section Core

variable {D : QReg} {s₀ s₁ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}

/-- The controlled runtime on `D × Bool`, which answers a call with `U i r` on the branch
`false` and with `W i r` on the branch `true`. -/
@[reducible, expose]
noncomputable def ctrlRuntime (σ : SubState (QReg.of (D × Bool)))
    (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
    (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r)) : QuantumRuntime spec where
  D := QReg.of (D × Bool)
  init := σ
  step i := ctrlStep (U i) (W i) ((s₀ i).posSemidef_one_sub_sum_of_branch_eq_conj (hU i))
    ((s₁ i).posSemidef_one_sub_sum_of_branch_eq_conj (hW i))

variable (σ : SubState (QReg.of (D × Bool))) (σ₀ σ₁ : SubState D)
  (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
  (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))

/-- The branch `false` of the controlled runtime simulates the first runtime. -/
theorem ctrlRuntime_simulation_false (i : spec.Port) (r : spec.Result i) :
    ((QuantumRuntime.mk D σ₀ s₀).step i).branch r ∘ₗ
        (MatrixMap.conj (inj D false)ᴴ).amplifyLeft (spec.In i) =
      (MatrixMap.conj (inj D false)ᴴ).amplifyLeft (spec.Out i) ∘ₗ
        ((ctrlRuntime σ hU hW).step i).branch r := by
  change (s₀ i).branch r ∘ₗ _ = _ ∘ₗ MatrixMap.conj (ctrl (U i r) (W i r))
  rw [hU, MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
    ← MatrixMap.conj_mul]
  exact congrArg _ (sel_false_mul_ctrl (U i r) (W i r)).symm

/-- The branch `true` of the controlled runtime simulates the second runtime. -/
theorem ctrlRuntime_simulation_true (i : spec.Port) (r : spec.Result i) :
    ((QuantumRuntime.mk D σ₁ s₁).step i).branch r ∘ₗ
        (MatrixMap.conj (inj D true)ᴴ).amplifyLeft (spec.In i) =
      (MatrixMap.conj (inj D true)ᴴ).amplifyLeft (spec.Out i) ∘ₗ
        ((ctrlRuntime σ hU hW).step i).branch r := by
  change (s₁ i).branch r ∘ₗ _ = _ ∘ₗ MatrixMap.conj (ctrl (U i r) (W i r))
  rw [hW, MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj, ← MatrixMap.conj_mul,
    ← MatrixMap.conj_mul]
  exact congrArg _ (sel_true_mul_ctrl (U i r) (W i r)).symm

/-- **One call.** The squared distances of the two branches after a call of the controlled
runtime are bounded, under square roots, by the squared distance before the call plus the Kraus
weight of `U - W` on the input of the call in the branch `false`. -/
theorem tsum_dist_queryStep_le (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    {Γ : Matrix (A × (D × Bool)) (A × (D × Bool)) ℂ} (hΓ : Γ.PosSemidef) :
    (∑' r, branchDist (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ)) ^ (2⁻¹ : ℝ) ≤
      branchDist Γ ^ (2⁻¹ : ℝ) +
        krausWeight (fun i r ↦ U i r - W i r) i
          (callInput ℓ D (MatrixMap.conj (sel A false) Γ)) ^ (2⁻¹ : ℝ) := by
  set Γ' := (relabel (queryEquivIn ℓ (D × Bool))).branch () Γ with hΓ'
  have hΓ'pos : Γ'.PosSemidef := (relabel _).posSemidef_branch_apply () hΓ
  set Γm := (relabel (queryEquivIn ℓ D)).branch () (MatrixMap.conj (seld A) Γ) with hΓm
  have hΓmpos : Γm.PosSemidef :=
    (relabel _).posSemidef_branch_apply () (hΓ.mul_mul_conjTranspose_same _)
  have hd : ∀ r, branchDist (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ) =
      ENNReal.ofReal (MatrixMap.conj
        (((U i r - W i r) * sel (spec.In i) false) ⊗ₖ (1 : Matrix E E ℂ) +
          (W i r * seld (spec.In i)) ⊗ₖ (1 : Matrix E E ℂ)) Γ').trace.re := by
    intro r
    rw [branchDist, queryStep_branch_apply, seld, ← MatrixMap.amplifyLeft_conj,
      ← LinearMap.comp_apply (MatrixMap.amplifyLeft _ _),
      ← intertwines_relabel_queryEquivOut _ (spec.Out i) E (), LinearMap.comp_apply,
      trace_relabel_branch_apply, ← hΓ']
    change ENNReal.ofReal ((((MatrixMap.conj (inj D false - inj D true)ᴴ).amplifyLeft
      (spec.Out i)).amplify E ((MatrixMap.conj (ctrl (U i r) (W i r))).amplify E Γ')).trace.re) = _
    rw [← LinearMap.comp_apply, ← MatrixMap.amplify_comp, MatrixMap.amplifyLeft_conj,
      ← MatrixMap.conj_mul, ← seld, seld_mul_ctrl, MatrixMap.amplify_conj, add_kronecker]
  have h₀in : ((MatrixMap.conj (inj D false)ᴴ).amplifyLeft (spec.In i)).amplify E Γ' =
      (relabel (queryEquivIn ℓ D)).branch () ((MatrixMap.conj (inj D false)ᴴ).amplifyLeft A Γ) :=
    (LinearMap.congr_fun (intertwines_relabel_queryEquivIn _ ℓ ()) Γ).symm
  have hdin : ((MatrixMap.conj (inj D false - inj D true)ᴴ).amplifyLeft (spec.In i)).amplify E
      Γ' = (relabel (queryEquivIn ℓ D)).branch ()
        ((MatrixMap.conj (inj D false - inj D true)ᴴ).amplifyLeft A Γ) :=
    (LinearMap.congr_fun (intertwines_relabel_queryEquivIn _ ℓ ()) Γ).symm
  have ha : ∀ r, (MatrixMap.conj (((U i r - W i r) * sel (spec.In i) false) ⊗ₖ
      (1 : Matrix E E ℂ)) Γ').trace =
        (MatrixMap.conj (U i r - W i r)
          (callInput ℓ D (MatrixMap.conj (sel A false) Γ))).trace := by
    intro r
    rw [MatrixMap.mul_kronecker_one, MatrixMap.conj_mul, LinearMap.comp_apply,
      MatrixMap.trace_conj_kronecker_one_apply, ← MatrixMap.amplify_conj (sel (spec.In i) false)]
    simp only [conj_sel, h₀in]
    rfl
  have hb : ∀ r, (MatrixMap.conj ((W i r * seld (spec.In i)) ⊗ₖ (1 : Matrix E E ℂ)) Γ').trace =
      (((s₁ i).frame E).branch r Γm).trace := by
    intro r
    rw [MatrixMap.mul_kronecker_one, MatrixMap.conj_mul, LinearMap.comp_apply,
      ← MatrixMap.amplify_conj (seld (spec.In i)), ← MatrixMap.amplify_conj (W i r),
      DSubInstrument.branch_frame_apply, hW, hΓm]
    simp only [conj_seld, hdin]
  rw [add_comm]
  refine (rpow_inv_two_tsum_le_of_le_add (t := fun r ↦ branchDist
    (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ))
    (a := fun r ↦ ENNReal.ofReal (MatrixMap.conj (U i r - W i r)
      (callInput ℓ D (MatrixMap.conj (sel A false) Γ))).trace.re)
    (b := fun r ↦ ENNReal.ofReal (((s₁ i).frame E).branch r Γm).trace.re) fun r ↦ ?_).trans ?_
  · rw [hd, ← ha, ← hb]
    exact MatrixMap.ofReal_trace_conj_add_rpow_le hΓ'pos _ _
  · refine add_le_add le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num))
    refine ((s₁ i).frame E).isCPTNIFamily.tsum_ofReal_trace_re_le hΓmpos |>.trans_eq ?_
    rw [branchDist, hΓm, trace_relabel_branch_apply]

/-- **The hybrid induction.** Along the run of the controlled runtime from `Γ`, the square root of
the summed squared distances of the two branches at the leaves is at most that of `Γ`, plus the
sum over the calls of the square roots of the Kraus weights of `U - W` on their inputs in the
branch `false`, which runs the first runtime. -/
theorem rpow_inv_two_tsum_dist_run_le (x : QuantumComp L spec X A)
    {Γ : Matrix (A × (D × Bool)) (A × (D × Bool)) ℂ} (hΓ : Γ.PosSemidef) :
    (∑' p, branchDist (((ctrlRuntime σ hU hW).run I x).branch p Γ)) ^ (2⁻¹ : ℝ) ≤
      branchDist Γ ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight fun i r ↦ U i r - W i r) x
          (MatrixMap.conj (sel A false) Γ) j ^ (2⁻¹ : ℝ) := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, branchDist_zero],
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
    exact le_self_add
  | primBind B o k ih =>
    have hΓb := fun b ↦ ((I o).frame (ctrlRuntime σ hU hW).D).posSemidef_branch_apply b hΓ
    have hL : ∀ p, branchDist (((ctrlRuntime σ hU hW).run I (QuantumComp.primBind o k)).branch p
        Γ) = ∑' b, branchDist (((ctrlRuntime σ hU hW).run I (k b)).branch p
          (((I o).frame (ctrlRuntime σ hU hW).D).branch b Γ)) := fun p ↦ by
      rw [run_primBind, DSubInstrument.branch_bind_apply]
      exact branchDist_tsum ((((I o).frame _).isCPTNIFamily.comp_eval
        (fun b ↦ ((ctrlRuntime σ hU hW).run I (k b)).isCPTNIFamily) p).summable_apply Γ)
        fun b ↦ ((ctrlRuntime σ hU hW).run I (k b)).posSemidef_branch_apply p (hΓb b)
    simp only [hL, queryWeight_primBind]
    rw [ENNReal.tsum_comm]
    refine (rpow_inv_two_tsum_le_of_le_add_tsum fun b ↦ ih b (hΓb b)).trans
      (add_le_add (ENNReal.rpow_le_rpow ?_ (by norm_num)) (le_of_eq ?_))
    · calc ∑' b, branchDist (((I o).frame (ctrlRuntime σ hU hW).D).branch b Γ)
          = ∑' b, ENNReal.ofReal
              (((I o).frame D).branch b (MatrixMap.conj (seld B) Γ)).trace.re :=
            tsum_congr fun b ↦ branchDist_amplify ((I o).branch b) Γ
        _ ≤ branchDist Γ :=
            ((I o).frame D).isCPTNIFamily.tsum_ofReal_trace_re_le
              (hΓ.mul_mul_conjTranspose_same _)
    · refine tsum_congr fun j ↦ congrArg (· ^ (2⁻¹ : ℝ)) (tsum_congr fun b ↦ ?_)
      exact congrArg (fun M ↦ (QuantumRuntime.mk D σ₀ s₀).queryWeight I _ (k b) M j)
        (conj_sel_amplify ((I o).branch b) false Γ)
  | queryBind B i E ℓ k ih =>
    have hΓr := fun r ↦ ((ctrlRuntime σ hU hW).queryStep i E ℓ).posSemidef_branch_apply r hΓ
    have hL : ∀ p, branchDist (((ctrlRuntime σ hU hW).run I
        (QuantumComp.queryBind i E ℓ k)).branch p Γ) =
          ∑' r, branchDist (((ctrlRuntime σ hU hW).run I (k r)).branch p
            (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ)) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
      exact branchDist_tsum
        ((((ctrlRuntime σ hU hW).queryStep i E ℓ).isCPTNIFamily.comp_eval
        (fun r ↦ ((ctrlRuntime σ hU hW).run I (k r)).isCPTNIFamily) p).summable_apply Γ)
        fun r ↦ ((ctrlRuntime σ hU hW).run I (k r)).posSemidef_branch_apply p (hΓr r)
    have hsel : ∀ r, MatrixMap.conj (sel (QReg.of (spec.Out i × E)) false)
        (((ctrlRuntime σ hU hW).queryStep i E ℓ).branch r Γ) =
          ((QuantumRuntime.mk D σ₀ s₀).queryStep i E ℓ).branch r
            (MatrixMap.conj (sel B false) Γ) := fun r ↦ by
      have h := LinearMap.congr_fun (intertwines_queryStep (R₁ := ctrlRuntime σ hU hW)
        (R₂ := QuantumRuntime.mk D σ₀ s₀) (V := MatrixMap.conj (inj D false)ᴴ)
        (ctrlRuntime_simulation_false σ σ₀ hU hW i) E ℓ r) Γ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      rw [conj_sel, conj_sel]
      exact h.symm
    simp only [hL]
    rw [ENNReal.tsum_comm]
    refine (rpow_inv_two_tsum_le_of_le_add_tsum fun r ↦ ih r (hΓr r)).trans ?_
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable, queryWeight_queryBind_zero, ← add_assoc]
    simp only [queryWeight_queryBind_succ, hsel]
    exact add_le_add (tsum_dist_queryStep_le σ hU hW i E ℓ hΓ) le_rfl

end Core

/-! ## The square-root hybrid bound -/

section Bound

open scoped Matrix.Norms.L2Operator

variable {D : QReg} {s₀ s₁ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
  {U W : ∀ i, spec.Result i → Matrix (spec.Out i × D) (spec.In i × D) ℂ}
  (σ₀ σ₁ : SubState D)
  (hU : ∀ i r, (s₀ i).branch r = MatrixMap.conj (U i r))
  (hW : ∀ i r, (s₁ i).branch r = MatrixMap.conj (W i r))
include hU hW

/-- The zero substate, the initial state of the controlled runtime in the proofs: it is never
used, since the controlled runtime is run from a given joint operator. -/
private noncomputable def zeroState (B : QReg) : SubState B :=
  ⟨0, Matrix.PosSemidef.zero, by simp⟩

/-- The leaves of the two runtimes as the two branches of the controlled runtime started from
`T ρ Tᴴ`, `T = (sel A false)ᴴ + (sel A true)ᴴ`. -/
private theorem run_branch_eq_conj_sel_ctrl (x : QuantumComp L spec X A)
    (ρ : Matrix (A × D) (A × D) ℂ) (p : Σ u, X u) :
    ((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ =
        MatrixMap.conj (sel p.1 false) (((ctrlRuntime (zeroState _) hU hW).run I x).branch p
          (MatrixMap.conj ((sel A false)ᴴ + (sel A true)ᴴ) ρ)) ∧
      ((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ =
        MatrixMap.conj (sel p.1 true) (((ctrlRuntime (zeroState _) hU hW).run I x).branch p
          (MatrixMap.conj ((sel A false)ᴴ + (sel A true)ᴴ) ρ)) := by
  have h₀ := LinearMap.congr_fun
    (simulation I (R₁ := ctrlRuntime (zeroState _) hU hW) (R₂ := QuantumRuntime.mk D σ₀ s₀)
      (V := MatrixMap.conj (inj D false)ᴴ)
      (ctrlRuntime_simulation_false (zeroState _) σ₀ hU hW) x p)
    (MatrixMap.conj ((sel A false)ᴴ + (sel A true)ᴴ) ρ)
  have h₁ := LinearMap.congr_fun
    (simulation I (R₁ := ctrlRuntime (zeroState _) hU hW) (R₂ := QuantumRuntime.mk D σ₁ s₁)
      (V := MatrixMap.conj (inj D true)ᴴ)
      (ctrlRuntime_simulation_true (zeroState _) σ₁ hU hW) x p)
    (MatrixMap.conj ((sel A false)ᴴ + (sel A true)ᴴ) ρ)
  simp only [LinearMap.comp_apply, ← conj_sel, conj_sel_conj_add] at h₀ h₁
  exact ⟨h₀, h₁⟩

/-- **The square-root hybrid bound** (ePrint 2025/2166, Lemma 5.7, for general programs). Let the
steps of two runtimes on the same register `D` be the Kraus maps of `U i r` and `W i r`, and let
`O p` be a contraction on the joint register at every leaf `p`. Then the square root of the
summed weights `tr (O p ρ_p (O p)ᴴ)` of the leaves of a run against the first runtime is at most
that against the second, plus the sum over the calls `j` of the square roots of the Kraus weights
of `U - W` on the inputs of the `j`-th calls of the run against the first runtime.

The program is arbitrary: adaptive, with any interpretation of its local operations and with
countably many outcomes. Both runs start from the same joint operator `ρ` on `A × D`. -/
theorem rpow_inv_two_tsum_trace_conj_run_le (x : QuantumComp L spec X A)
    {Z : (Σ u, X u) → Type*} [∀ p, Fintype (Z p)] (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ)
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : ρ.PosSemidef) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
        (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
          (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight fun i r ↦ U i r - W i r) x
          ρ j ^ (2⁻¹ : ℝ) := by
  have hΓ : (MatrixMap.conj ((sel (D := D) A false)ᴴ + (sel A true)ᴴ) ρ).PosSemidef :=
    hρ.mul_mul_conjTranspose_same _
  simp only [fun p ↦ (run_branch_eq_conj_sel_ctrl I σ₀ σ₁ hU hW x ρ p).1,
    fun p ↦ (run_branch_eq_conj_sel_ctrl I σ₀ σ₁ hU hW x ρ p).2]
  refine (rpow_inv_two_tsum_le_of_le_add fun p ↦ ofReal_trace_conj_sel_false_rpow_le (O p) (hO p)
    (((ctrlRuntime (zeroState _) hU hW).run I x).posSemidef_branch_apply p hΓ)).trans
    (add_le_add le_rfl ?_)
  refine (rpow_inv_two_tsum_dist_run_le I (zeroState _) σ₀ hU hW x hΓ).trans_eq ?_
  rw [branchDist, conj_seld_conj_add, conj_sel_conj_add]
  simp

/-- **The square-root hybrid bound**, converse direction: the weights of the second runtime are
bounded by those of the first plus the same sum over the calls of the first runtime. -/
theorem rpow_inv_two_tsum_trace_conj_run_le' (x : QuantumComp L spec X A)
    {Z : (Σ u, X u) → Type*} [∀ p, Fintype (Z p)] (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ)
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : ρ.PosSemidef) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
        (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
          (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight fun i r ↦ U i r - W i r) x
          ρ j ^ (2⁻¹ : ℝ) := by
  have hΓ : (MatrixMap.conj ((sel (D := D) A false)ᴴ + (sel A true)ᴴ) ρ).PosSemidef :=
    hρ.mul_mul_conjTranspose_same _
  simp only [fun p ↦ (run_branch_eq_conj_sel_ctrl I σ₀ σ₁ hU hW x ρ p).1,
    fun p ↦ (run_branch_eq_conj_sel_ctrl I σ₀ σ₁ hU hW x ρ p).2]
  refine (rpow_inv_two_tsum_le_of_le_add fun p ↦ ofReal_trace_conj_sel_true_rpow_le (O p) (hO p)
    (((ctrlRuntime (zeroState _) hU hW).run I x).posSemidef_branch_apply p hΓ)).trans
    (add_le_add le_rfl ?_)
  refine (rpow_inv_two_tsum_dist_run_le I (zeroState _) σ₀ hU hW x hΓ).trans_eq ?_
  rw [branchDist, conj_seld_conj_add, conj_sel_conj_add]
  simp

/-- **The square-root hybrid bound by query masses**: the Kraus weight of the `j`-th call is at
most the masses of the `j`-th call weighted by `∑ᵣ ‖U i r - W i r‖²`, for the `ℓ²` operator
norm (ePrint 2025/2166, Lemma 5.7, with the masses of the classical ports). The bound with the
masses of a coherent index, as in §4.2, is
`Quantum.QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le_indexMass`. -/
theorem rpow_inv_two_tsum_trace_conj_run_le_mass (x : QuantumComp L spec X A)
    {Z : (Σ u, X u) → Type*} [∀ p, Fintype (Z p)] (O : ∀ p : Σ u, X u, Matrix (Z p) (p.1 × D) ℂ)
    (hO : ∀ p, (1 - (O p)ᴴ * O p).PosSemidef) {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : ρ.PosSemidef) :
    (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
        (((QuantumRuntime.mk D σ₀ s₀).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) ≤
      (∑' p, ENNReal.ofReal (MatrixMap.conj (O p)
          (((QuantumRuntime.mk D σ₁ s₁).run I x).branch p ρ)).trace.re) ^ (2⁻¹ : ℝ) +
        ∑' j, (∑' i, (∑' r, ENNReal.ofReal (‖U i r - W i r‖ ^ 2)) *
          (QuantumRuntime.mk D σ₀ s₀).queryMassAt I x ρ i j) ^ (2⁻¹ : ℝ) :=
  (rpow_inv_two_tsum_trace_conj_run_le I σ₀ σ₁ hU hW x O hO hρ).trans <| add_le_add le_rfl <|
    ENNReal.tsum_le_tsum fun j ↦ ENNReal.rpow_le_rpow
      ((QuantumRuntime.mk D σ₀ s₀).queryWeight_le_tsum_mul_queryMassAt I _
        (fun i _ hσ ↦ krausWeight_le _ i hσ) x hρ j) (by norm_num)

omit hU hW in
/-- The observable of a set of leaves: the identity on the leaves observed in `s`, zero on the
others. -/
private theorem ofReal_trace_mul_indicator {γ : Type*} (f : (Σ u, X u) → γ) (s : Set γ)
    [DecidablePred (· ∈ s)] (p : Σ u, X u) (M : Matrix (p.1 × D) (p.1 × D) ℂ) :
    ENNReal.ofReal M.trace.re * s.indicator 1 (f p) =
      ENNReal.ofReal (MatrixMap.conj
        (if f p ∈ s then (1 : Matrix (p.1 × D) (p.1 × D) ℂ) else 0) M).trace.re := by
  by_cases h : f p ∈ s <;> simp [h]

omit hU hW in
private theorem posSemidef_one_sub_indicator {γ : Type*} (f : (Σ u, X u) → γ) (s : Set γ)
    [DecidablePred (· ∈ s)] (p : Σ u, X u) :
    (1 - (if f p ∈ s then (1 : Matrix (p.1 × D) (p.1 × D) ℂ) else 0)ᴴ *
      (if f p ∈ s then (1 : Matrix (p.1 × D) (p.1 × D) ℂ) else 0)).PosSemidef := by
  by_cases h : f p ∈ s <;> simp [h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero]

/-- **The square-root hybrid bound for events** (ePrint 2025/2166, Lemma 5.7, for general
programs). Two runtimes with the same register and initial state `σ` and steps the Kraus maps
of `U i r` and `W i r` give laws of any observation `f` of the leaves whose square roots differ,
on every measurable set, by at most the sum over the calls of the square roots of the Kraus
weights of `U - W` on the inputs of the calls of the run against the first runtime. -/
theorem rpow_inv_two_outcomeLawWith_le {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight fun i r ↦ U i r - W i r) x
          (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) := by
  classical
  rw [evalDistMap_apply _ _ _ _ _ hs, evalDistMap_apply _ _ _ _ _ hs]
  simp only [matrix_jointPost, ofReal_trace_mul_indicator f s]
  exact rpow_inv_two_tsum_trace_conj_run_le I σ₀ σ₀ hU hW x _
    (posSemidef_one_sub_indicator f s) (ρ.prod σ₀).posSemidef

/-- **The square-root hybrid bound for events**, converse direction. -/
theorem rpow_inv_two_outcomeLawWith_le' {γ : Type*} [MeasurableSpace γ]
    (x : QuantumComp L spec X A) (ρ : SubState A) (f : (Σ u, X u) → γ) {s : Set γ}
    (hs : MeasurableSet s) :
    (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        ∑' j, (QuantumRuntime.mk D σ₀ s₀).queryWeight I (krausWeight fun i r ↦ U i r - W i r) x
          (ρ.matrix ⊗ₖ σ₀.matrix) j ^ (2⁻¹ : ℝ) := by
  classical
  rw [evalDistMap_apply _ _ _ _ _ hs, evalDistMap_apply _ _ _ _ _ hs]
  simp only [matrix_jointPost, ofReal_trace_mul_indicator f s]
  exact rpow_inv_two_tsum_trace_conj_run_le' I σ₀ σ₀ hU hW x _
    (posSemidef_one_sub_indicator f s) (ρ.prod σ₀).posSemidef

/-- **The square-root hybrid bound for events, for programs within a query budget**: with at
most `q = ∑ i ∈ t, b i` calls, the sum over the calls is at most `√(q · ∑ᵢ Cᵢ · mass i)`, where
`Cᵢ = ∑ᵣ ‖U i r - W i r‖²` and `mass i` is the total query mass of port `i` (ePrint 2025/2166,
Lemma 5.7, with Cauchy–Schwarz as in Cor 5.8). -/
theorem rpow_inv_two_outcomeLawWith_le_of_isQueryBound {γ : Type*} [MeasurableSpace γ]
    {x : QuantumComp L spec X A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (t : Finset spec.Port) (ht : ∀ i ∉ t, b i = 0) (ρ : SubState A) (f : (Σ u, X u) → γ)
    {s : Set γ} (hs : MeasurableSet s) :
    (QuantumRuntime.mk D σ₀ s₀).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) ≤
      (QuantumRuntime.mk D σ₀ s₁).evalDistMap I x ρ f s ^ (2⁻¹ : ℝ) +
        (((∑ i ∈ t, b i : ℕ) : ℝ≥0∞) * ∑' i, (∑' r, ENNReal.ofReal (‖U i r - W i r‖ ^ 2)) *
          (QuantumRuntime.mk D σ₀ s₀).queryMass I x (ρ.matrix ⊗ₖ σ₀.matrix) i) ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_outcomeLawWith_le I σ₀ hU hW x ρ f hs).trans (add_le_add le_rfl ?_)
  refine (tsum_rpow_inv_two_queryWeight_le_of_isQueryBound I _ hx t ht _).trans ?_
  gcongr
  exact (QuantumRuntime.mk D σ₀ s₀).tsum_queryWeight_le_tsum_mul_queryMass I _
    (fun i _ hσ ↦ krausWeight_le _ i hσ) x (ρ.prod σ₀).posSemidef

end Bound

end QuantumRuntime

end Quantum

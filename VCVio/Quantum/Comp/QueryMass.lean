/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.Comp.QueryBound

/-!
# Query mass of quantum programs

The *query mass* of a program on a port is the total weight with which the program calls that
port: run the program, and at every call of the port add the trace of the state that reaches the
call. Query mass is the bookkeeping device of the square-root hybrid argument (ePrint 2025/2166,
§4.2 and Lemma 5.7; Zhandry, *How to record quantum queries*, CRYPTO 2019; Hamoudi, 2025). A
change of the answers of the ports costs, for each call `j`, the square root of the masses of
that call weighted by the squared operator norms `Cᵢ` of the change, and these costs add up over
the calls: the error is `∑ⱼ √(∑ᵢ Cᵢ · mass(i, j))`. The total mass alone does not bound it,
since small changes accumulate over many calls. For a program making at most `q` calls,
Cauchy–Schwarz over the calls gives the consequence `√(q · ∑ᵢ Cᵢ · TotalMass(i))`, which is
`C · √(q · TotalMass)` for a single port with `C² = Cᵢ`.

## Classical ports and coherent indices

ePrint 2025/2166 defines `mass(A, i, j) = ‖P_mass^(i) |ψ_j⟩‖²`, where `|ψ_j⟩` is the state just
before the `j`-th query and `P_mass^(i)` projects a coherent index register onto `i`, so that
`∑ᵢ mass(A, i, j) = 1`. The ports of a signature are classical: the program decides which port it
calls, possibly depending on classical outcomes. The mass on port `i` before the `j`-th call is
therefore the trace of the state reaching the `j`-th call when that call is on port `i`, and zero
otherwise. This is the specialisation of the paper's mass to a classical index.

Coherent access to several oracles is a port whose input register carries the index. Its masses
are the *index masses* `indexMassAt B x ρ ⟨i, k⟩ j`: for operators `B i k` on the input register
of port `i`, typically the projections `|k⟩⟨k| ⊗ 1` onto the values of the index, the trace of
`(B i k ⊗ 1) σ (B i k ⊗ 1)ᴴ` for the input `σ` of the `j`-th call. They are query weights, and
with a single port they are exactly the masses of the paper. When the blocks of a port are
complete they add up to its query mass (`tsum_indexMassAt_eq_queryMassAt`). The square-root
hybrid bounds in terms of index masses, with the operator norms of the change on each block, are
in `VCVio.Quantum.Comp.HybridIndex`.

## Weights

The general object is a *query weight*. Given, for every port `i`, a function `w i` of operators
on the port's input register and the runtime register, `R.queryWeight I w x ρ j` evaluates `w` on
the input of the `j`-th call along every path of `x` run from `ρ`, and adds the results over the
paths. Calls are counted along each path over all ports, so `j` is the paper's query index, and
for adaptive programs the `j`-th call may be on different ports on different paths. The input of
a call through `ℓ : A ≃ In i × E` is the joint operator on `In i × D`, with the rest `E` of the
program register traced out (`Quantum.QuantumRuntime.callInput`).

* With `w i σ = tr σ` on port `i` and `0` on the other ports, the weight is the query mass
  `queryMassAt x ρ i j`, and its sum over `j` is the total query mass `queryMass x ρ i`.
* The square-root hybrid of ePrint 2025/2166 consumes the Kraus weight
  `∑ᵣ tr (F r σ F rᴴ)` of the difference `F` of two steps, bounded by the query mass times
  `∑ᵣ ‖F r‖²` (`Quantum.QuantumRuntime.queryWeight_le_tsum_mul_queryMassAt`).

Weights and masses are extended nonnegative reals, so that sums over countably many outcomes of
the local operations are always defined.

## Main definitions

* `Quantum.QuantumRuntime.callInput ℓ D`: the input of a call, on `In i × D`.
* `Quantum.QuantumRuntime.queryWeight R I w x ρ j`: the weight `w` of the `j`-th call.
* `Quantum.QuantumRuntime.queryMassAt R I x ρ i j`: the mass on port `i` of the `j`-th call.
* `Quantum.QuantumRuntime.queryMass R I x ρ i`: the total query mass on port `i`.
* `Quantum.QuantumRuntime.indexMassAt R I B x ρ c j`, `Quantum.QuantumRuntime.indexMass`: the
  masses of a coherent index, on the block `c = ⟨i, k⟩`.

## Main statements

* Recursion lemmas for all three, mirroring `Quantum.QuantumRuntime.run`.
* `queryWeight_tsum_state`: on positive semidefinite inputs, weights are countably additive in
  the state when `w` is.
* `queryWeight_le_tsum_mul_queryMassAt`: a weight bounded by `C i · tr` on port `i` is bounded by
  the masses weighted by `C`; summed over the calls, by the total masses
  (`tsum_queryWeight_le_tsum_mul_queryMass`).
* `tsum_queryMassAt_le` (the analogue of Remark 4.2 of ePrint 2025/2166): the masses of the
  `j`-th call over all ports add up to at most the trace of the initial state.
* `queryWeight_eq_zero_of_isQueryBound`: a program within a finite budget makes no call beyond
  it.
* `queryMass_le_of_isQueryBoundAt`: the mass on port `i` is at most the budget of `i` times the
  trace of the initial state.
* `queryMass_bind`: masses add under sequencing.
* `queryWeight_le_tsum_mul_indexMassAt` and `tsum_queryWeight_le_tsum_mul_indexMass`: a weight
  bounded block by block is bounded by the index masses; `tsum_indexMassAt_eq_queryMassAt`: index
  masses refine query masses.
-/

public section

open IPFunctor
open scoped ENNReal ComplexOrder Kronecker Matrix

universe u v u₁ v₁ w w₁

namespace Quantum

/-! ## Traces of families of positive semidefinite matrices -/

namespace MatrixMap.IsCPTNIFamily

variable {ι : Type*} {A : Type*} [Fintype A] {B : ι → Type*} [∀ i, Fintype (B i)]
  {Φ : (i : ι) → MatrixMap A (B i)}

/-- On a positive semidefinite input, the traces of the members of a completely positive family
with trace-nonincreasing partial sums add up to at most the trace of the input, in `ℝ≥0∞`. -/
theorem tsum_ofReal_trace_re_le (h : IsCPTNIFamily Φ) {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    ∑' i, ENNReal.ofReal (Φ i ρ).trace.re ≤ ENNReal.ofReal ρ.trace.re := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ h.trace_re_apply_nonneg i hρ)
    (h.summable_trace_re_apply hρ)]
  exact ENNReal.ofReal_le_ofReal (h.tsum_trace_re_apply_le hρ)

end MatrixMap.IsCPTNIFamily

/-- The trace of the sum of a summable family of positive semidefinite matrices is the sum of
the traces, in `ℝ≥0∞`. -/
theorem ofReal_trace_re_tsum {ι n : Type*} [Fintype n] {f : ι → Matrix n n ℂ} (hf : Summable f)
    (hpos : ∀ b, (f b).PosSemidef) :
    ENNReal.ofReal (∑' b, f b).trace.re = ∑' b, ENNReal.ofReal (f b).trace.re := by
  rw [Matrix.trace_tsum hf, Complex.re_tsum (Matrix.summable_trace hf)]
  exact ENNReal.ofReal_tsum_of_nonneg (fun b ↦ (hpos b).trace_re_nonneg)
    (Complex.reCLM.summable (Matrix.summable_trace hf))

namespace QuantumRuntime

/-! ## The input of a call -/

section callInput

variable {A J E : Type*} [Fintype A] [Fintype J] [Fintype E] [DecidableEq A] [DecidableEq J]
  [DecidableEq E]

/-- The input of a call through `ℓ : A ≃ J × E`: the joint operator on the port's input register
`J` and the runtime register `D`, with the rest `E` of the program register traced out. -/
@[expose]
noncomputable def callInput (ℓ : A ≃ J × E) (D : Type*) [Fintype D] [DecidableEq D] :
    MatrixMap (A × D) (J × D) :=
  MatrixMap.traceRight (J × D) E ∘ₗ (SubInstrument.relabel (queryEquivIn ℓ D)).branch ()

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The input of a call has the trace of the state. -/
@[simp]
theorem trace_callInput (ℓ : A ≃ J × E) (ρ : Matrix (A × D) (A × D) ℂ) :
    (callInput ℓ D ρ).trace = ρ.trace := by
  rw [callInput, LinearMap.comp_apply, MatrixMap.trace_traceRight,
    SubInstrument.relabel_branch_apply]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact (queryEquivIn ℓ D).symm.sum_comp fun a ↦ ρ a a

/-- The input of a call on a positive semidefinite state is positive semidefinite. -/
theorem posSemidef_callInput (ℓ : A ≃ J × E) {ρ : Matrix (A × D) (A × D) ℂ}
    (hρ : ρ.PosSemidef) : (callInput ℓ D ρ).PosSemidef :=
  ((SubInstrument.relabel (queryEquivIn ℓ D)).posSemidef_branch_apply () hρ).traceRight

end callInput

/-! ## Query weights -/

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {X : QReg → Type w} {Y : QReg → Type w₁} {A : QReg}

/-- The weight `w` of the `j`-th call along the paths of a program tree, folded into functions
of the input state and query index. -/
@[expose]
noncomputable def queryWeightAux
    (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞) :
    {A : QReg} → IFreeM (QuantumComp.toIPFunctor L spec) X A →
      Matrix (A × R.D) (A × R.D) ℂ → ℕ → ℝ≥0∞ :=
  fun {_} x ↦ IFreeM.fold (P := QuantumComp.toIPFunctor L spec)
    (D := fun A ↦ Matrix (A × R.D) (A × R.D) ℂ → ℕ → ℝ≥0∞)
    (fun _ _ _ _ ↦ 0)
    (fun _ cmd next ↦ match cmd with
      | .prim o => fun ρ j ↦ ∑' b, next (ULift.up b) (((I o).frame R.D).branch b ρ) j
      | .query i E ℓ => fun ρ j ↦ match j with
        | 0 => w i (callInput ℓ R.D ρ)
        | j + 1 => ∑' r, next (ULift.up r) ((R.queryStep i E ℓ).branch r ρ) j) x

/-- **Query weight.** For a weight `w i` on the inputs of the calls of each port `i`, the sum
over the paths of `x`, run against `R` from the joint operator `ρ` on `A × R.D`, of the weight
of the input of the `j`-th call (counting calls of all ports, from `0`). Paths that stop before
their `j`-th call contribute nothing.

From a substate `ρ` of the program register, with the runtime register in `R.init`, the state is
`ρ.matrix ⊗ₖ R.init.matrix`.

To compare weights against two runtimes on a pure program or at a first call, rewrite with
`queryWeight_pure` or `queryWeight_queryBind_zero` rather than closing by `rfl`: definitional
unfolding can compare the two unused fold algebras first. -/
@[expose]
noncomputable def queryWeight (w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) : ℝ≥0∞ :=
  R.queryWeightAux I w x ρ j

variable {w : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}

/-- A program that stops at once makes no call. -/
@[simp]
theorem queryWeight_pure (y : X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I w (QuantumComp.pure (L := L) (spec := spec) y) ρ j = 0 :=
  rfl

/-- The calls of a local operation followed by a continuation are those of the continuations,
from the branches of the operation. -/
@[simp]
theorem queryWeight_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I w (QuantumComp.primBind o k) ρ j =
      ∑' b, R.queryWeight I w (k b) (((I o).frame R.D).branch b ρ) j :=
  rfl

/-- The first call of a program that starts with a call is that call. -/
@[simp]
theorem queryWeight_queryBind_zero (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.queryWeight I w (QuantumComp.queryBind i E ℓ k) ρ 0 = w i (callInput ℓ R.D ρ) :=
  rfl

/-- The later calls of a program that starts with a call are those of the continuations, from the
branches of the call. -/
@[simp]
theorem queryWeight_queryBind_succ (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I w (QuantumComp.queryBind i E ℓ k) ρ (j + 1) =
      ∑' r, R.queryWeight I w (k r) ((R.queryStep i E ℓ).branch r ρ) j :=
  rfl

/-- On the zero state every weight that vanishes at zero is zero. -/
theorem queryWeight_zero (hw : ∀ i, w i 0 = 0) (x : QuantumComp L spec X A) (j : ℕ) :
    R.queryWeight I w x 0 j = 0 := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih => simp [ih]
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero => simp [hw]
    | succ j => simp [ih]

/-- **Countable additivity in the state.** If every `w i` is countably additive on summable
families of positive semidefinite operators, so is the weight of every call. -/
theorem queryWeight_tsum_state {ι : Type*}
    (hw : ∀ i (g : ι → Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      Summable g → (∀ b, (g b).PosSemidef) → w i (∑' b, g b) = ∑' b, w i (g b))
    (x : QuantumComp L spec X A) {f : ι → Matrix (A × R.D) (A × R.D) ℂ}
    (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef) (j : ℕ) :
    R.queryWeight I w x (∑' b, f b) j = ∑' b, R.queryWeight I w x (f b) j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun c ↦ ?_
    rw [MatrixMap.map_tsum _ hf]
    exact ih c (MatrixMap.summable_comp _ hf)
      (fun b ↦ ((I o).frame R.D).posSemidef_branch_apply c (hpos b)) j
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero =>
      simp only [queryWeight_queryBind_zero]
      rw [MatrixMap.map_tsum _ hf]
      exact hw i _ (MatrixMap.summable_comp _ hf) fun b ↦ posSemidef_callInput ℓ (hpos b)
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun r ↦ ?_
      rw [MatrixMap.map_tsum _ hf]
      exact ih r (MatrixMap.summable_comp _ hf)
        (fun b ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r (hpos b)) j

/-- On positive semidefinite inputs, weights are monotone in `w`. -/
theorem queryWeight_mono {w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (h : ∀ i σ, σ.PosSemidef → w i σ ≤ w' i σ) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (j : ℕ) :
    R.queryWeight I w x ρ j ≤ R.queryWeight I w' x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact ENNReal.tsum_le_tsum fun b ↦
      ih b (((I o).frame R.D).posSemidef_branch_apply b hρ) j
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero => exact h i _ (posSemidef_callInput ℓ hρ)
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      exact ENNReal.tsum_le_tsum fun r ↦
        ih r ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ) j

/-- On positive semidefinite inputs, weights depend only on the values of `w` on positive
semidefinite operators. -/
theorem queryWeight_congr {w' : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (h : ∀ i σ, σ.PosSemidef → w i σ = w' i σ) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (j : ℕ) :
    R.queryWeight I w x ρ j = R.queryWeight I w' x ρ j :=
  le_antisymm (R.queryWeight_mono I (fun i σ hσ ↦ (h i σ hσ).le) x hρ j)
    (R.queryWeight_mono I (fun i σ hσ ↦ (h i σ hσ).ge) x hρ j)

/-- Weights are countably additive in `w`. -/
theorem tsum_queryWeight {κ : Type*}
    (w : κ → ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    ∑' c, R.queryWeight I (w c) x ρ j = R.queryWeight I (fun i σ ↦ ∑' c, w c i σ) x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun b ↦ ih b _ j
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      rw [ENNReal.tsum_comm]
      exact tsum_congr fun r ↦ ih r _ j

/-- Weights are homogeneous in `w`. -/
theorem queryWeight_const_mul (c : ℝ≥0∞) (x : QuantumComp L spec X A)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I (fun i σ ↦ c * w i σ) x ρ j = c * R.queryWeight I w x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind, ih, ENNReal.tsum_mul_left]
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero => rfl
    | succ j => simp only [queryWeight_queryBind_succ, ih, ENNReal.tsum_mul_left]

/-- A weight bounded by the trace is bounded, at every call, by the trace of the initial state:
the inputs of the `j`-th calls on the different paths come from disjoint branches of a
trace-nonincreasing run. -/
theorem queryWeight_le_ofReal_trace
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ ENNReal.ofReal σ.trace.re) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (j : ℕ) :
    R.queryWeight I w x ρ j ≤ ENNReal.ofReal ρ.trace.re := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => simp
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact (ENNReal.tsum_le_tsum fun b ↦
      ih b (((I o).frame R.D).posSemidef_branch_apply b hρ) j).trans
      ((((I o).frame R.D).isCPTNIFamily).tsum_ofReal_trace_re_le hρ)
  | queryBind _ i E ℓ k ih =>
    cases j with
    | zero =>
      simpa using hw i _ (posSemidef_callInput ℓ hρ)
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      exact (ENNReal.tsum_le_tsum fun r ↦
        ih r ((R.queryStep i E ℓ).posSemidef_branch_apply r hρ) j).trans
        ((R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ)

/-- A program within a finite query budget makes no call beyond it: if `x` calls each port `i`
at most `b i` times, `b` vanishes outside a finite set `s` of ports, and `j ≥ ∑ i ∈ s, b i`,
then no path reaches a `j`-th call. -/
theorem queryWeight_eq_zero_of_isQueryBound {x : QuantumComp L spec X A} {b : spec.Port → ℕ}
    (hx : x.IsQueryBound b) (s : Finset spec.Port) (hs : ∀ i ∉ s, b i = 0) {j : ℕ}
    (hj : ∑ i ∈ s, b i ≤ j) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.queryWeight I w x ρ j = 0 := by
  classical
  induction x using QuantumComp.inductionOn generalizing j b with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    simp only [queryWeight_primBind]
    exact ENNReal.tsum_eq_zero.mpr fun c ↦
      ih c ((QuantumComp.isQueryBound_primBind_iff o k b).mp hx c) hs hj _
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hi, hk⟩ := (QuantumComp.isQueryBound_queryBind_iff i E ℓ k b).mp hx
    have his : i ∈ s := by
      by_contra h
      exact (hs i h ▸ hi).false
    have h1 := Finset.sum_update_of_mem his b (b i - 1)
    have h2 := Finset.sum_eq_add_sum_sdiff_singleton_of_mem his b
    cases j with
    | zero => omega
    | succ j =>
      simp only [queryWeight_queryBind_succ]
      refine ENNReal.tsum_eq_zero.mpr fun r ↦ ih r (hk r) (fun i' hi' ↦ ?_) (by omega) _
      rw [Function.update_of_ne (by rintro rfl; exact hi' his), hs i' hi']

/-! ## Query mass -/

open Classical in
/-- **Query mass of the `j`-th call** (ePrint 2025/2166, §4.2, for the classical ports; the
paper's coherent index is `Quantum.QuantumRuntime.indexMassAt`). The trace of the state reaching
the `j`-th call of `x`, run against `R` from `ρ`, on the paths where that call is on port `i`.
Calls are counted over all ports, from `0`. -/
@[expose]
noncomputable def queryMassAt (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ)
    (i : spec.Port) (j : ℕ) : ℝ≥0∞ :=
  R.queryWeight I (fun i' σ ↦ if i' = i then ENNReal.ofReal σ.trace.re else 0) x ρ j

/-- A program that stops at once has no mass. -/
@[simp]
theorem queryMassAt_pure (y : X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (i : spec.Port) (j : ℕ) :
    R.queryMassAt I (QuantumComp.pure (L := L) (spec := spec) y) ρ i j = 0 :=
  rfl

/-- The masses of a local operation followed by a continuation are those of the continuations,
from the branches of the operation. -/
@[simp]
theorem queryMassAt_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (i : spec.Port) (j : ℕ) :
    R.queryMassAt I (QuantumComp.primBind o k) ρ i j =
      ∑' b, R.queryMassAt I (k b) (((I o).frame R.D).branch b ρ) i j :=
  rfl

/-- A program that starts with a call of port `i` puts the trace of the state on its first call
of `i`. -/
@[simp]
theorem queryMassAt_queryBind_self_zero (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.queryMassAt I (QuantumComp.queryBind i E ℓ k) ρ i 0 = ENNReal.ofReal ρ.trace.re := by
  simp [queryMassAt]

/-- A program that starts with a call of another port puts no mass on `i` at its first call. -/
theorem queryMassAt_queryBind_of_ne_zero {i' i : spec.Port} (h : i' ≠ i) (E : QReg)
    (ℓ : A ≃ spec.In i' × E)
    (k : spec.Result i' → QuantumComp L spec X (QReg.of (spec.Out i' × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.queryMassAt I (QuantumComp.queryBind i' E ℓ k) ρ i 0 = 0 := by
  simp [queryMassAt, h]

/-- The masses of the later calls of a program that starts with a call are those of the
continuations, from the branches of the call. -/
@[simp]
theorem queryMassAt_queryBind_succ (i' : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i' × E)
    (k : spec.Result i' → QuantumComp L spec X (QReg.of (spec.Out i' × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (i : spec.Port) (j : ℕ) :
    R.queryMassAt I (QuantumComp.queryBind i' E ℓ k) ρ i (j + 1) =
      ∑' r, R.queryMassAt I (k r) ((R.queryStep i' E ℓ).branch r ρ) i j :=
  rfl

/-- The sum over ports of the mass weights is the trace. -/
private theorem tsum_ite_ofReal_trace {n : Type*} [Fintype n] (i' : spec.Port)
    (σ : Matrix n n ℂ) [∀ i : spec.Port, Decidable (i' = i)] :
    ∑' i : spec.Port, (if i' = i then ENNReal.ofReal σ.trace.re else 0) =
      ENNReal.ofReal σ.trace.re :=
  (tsum_eq_single i' fun _ h ↦ by simp [Ne.symm h]).trans (by simp)

/-- **Weights by masses.** If the weight of a call of port `i` is at most `C i` times its trace,
the weight of the `j`-th call is at most the masses of the `j`-th call weighted by `C`. -/
theorem queryWeight_le_tsum_mul_queryMassAt (C : spec.Port → ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ C i * ENNReal.ofReal σ.trace.re)
    (x : QuantumComp L spec X A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (j : ℕ) : R.queryWeight I w x ρ j ≤ ∑' i, C i * R.queryMassAt I x ρ i j := by
  classical
  refine (R.queryWeight_mono I hw x hρ j).trans_eq ?_
  simp only [queryMassAt, ← queryWeight_const_mul, tsum_queryWeight]
  congr 1
  funext i' σ
  rw [tsum_eq_single i' fun c h ↦ by simp [Ne.symm h]]
  simp

/-- **The masses of a call add up to at most the trace** (the analogue of Remark 4.2 of
ePrint 2025/2166, where the masses of each query add up to one): over all ports, the masses of
the `j`-th call are at most the trace of the initial state. -/
theorem tsum_queryMassAt_le (x : QuantumComp L spec X A) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : ρ.PosSemidef) (j : ℕ) :
    ∑' i, R.queryMassAt I x ρ i j ≤ ENNReal.ofReal ρ.trace.re := by
  classical
  simp only [queryMassAt, tsum_queryWeight]
  refine R.queryWeight_le_ofReal_trace I (fun i' σ _ ↦ ?_) x hρ j
  rw [tsum_ite_ofReal_trace]

/-- On the zero state there is no mass. -/
theorem queryMassAt_zero (x : QuantumComp L spec X A) (i : spec.Port) (j : ℕ) :
    R.queryMassAt I x 0 i j = 0 :=
  R.queryWeight_zero I (fun _ ↦ by simp) x j

/-- On positive semidefinite inputs, masses are countably additive in the state. -/
theorem queryMassAt_tsum_state (x : QuantumComp L spec X A) {ι : Type*}
    {f : ι → Matrix (A × R.D) (A × R.D) ℂ} (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef)
    (i : spec.Port) (j : ℕ) :
    R.queryMassAt I x (∑' b, f b) i j = ∑' b, R.queryMassAt I x (f b) i j := by
  classical
  refine R.queryWeight_tsum_state I (fun i' g hg hgpos ↦ ?_) x hf hpos j
  split_ifs
  · exact ofReal_trace_re_tsum hg hgpos
  · simp

/-- **Total query mass** (ePrint 2025/2166, §4.2, for the classical ports): the sum over all
calls of the masses on port `i`, that is the total trace with which `x`, run against `R` from
`ρ`, calls port `i`. -/
@[expose]
noncomputable def queryMass (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ)
    (i : spec.Port) : ℝ≥0∞ :=
  ∑' j, R.queryMassAt I x ρ i j

/-- **Summed weights by total masses.** If the weight of a call of port `i` is at most `C i`
times its trace, the weights summed over all calls are at most the total masses weighted by
`C`. -/
theorem tsum_queryWeight_le_tsum_mul_queryMass (C : spec.Port → ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ C i * ENNReal.ofReal σ.trace.re)
    (x : QuantumComp L spec X A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' j, R.queryWeight I w x ρ j ≤ ∑' i, C i * R.queryMass I x ρ i := by
  refine (ENNReal.tsum_le_tsum fun j ↦
    R.queryWeight_le_tsum_mul_queryMassAt I C hw x hρ j).trans_eq ?_
  rw [ENNReal.tsum_comm]
  simp only [queryMass, ENNReal.tsum_mul_left]

/-- A program that stops at once has no mass. -/
@[simp]
theorem queryMass_pure (y : X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (i : spec.Port) :
    R.queryMass I (QuantumComp.pure (L := L) (spec := spec) y) ρ i = 0 := by
  simp [queryMass]

/-- The mass of a local operation followed by a continuation is the mass of the continuations,
from the branches of the operation. -/
@[simp]
theorem queryMass_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (i : spec.Port) :
    R.queryMass I (QuantumComp.primBind o k) ρ i =
      ∑' b, R.queryMass I (k b) (((I o).frame R.D).branch b ρ) i := by
  simp only [queryMass, queryMassAt_primBind]
  exact ENNReal.tsum_comm

/-- A call of port `i` followed by a continuation adds the trace of the state to the mass of the
continuations. -/
theorem queryMass_queryBind_self (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.queryMass I (QuantumComp.queryBind i E ℓ k) ρ i =
      ENNReal.ofReal ρ.trace.re + ∑' r, R.queryMass I (k r) ((R.queryStep i E ℓ).branch r ρ) i := by
  rw [queryMass, tsum_eq_zero_add' ENNReal.summable, queryMassAt_queryBind_self_zero]
  simp only [queryMassAt_queryBind_succ, queryMass]
  rw [ENNReal.tsum_comm]

/-- A call of another port followed by a continuation adds nothing to the mass on `i`. -/
theorem queryMass_queryBind_of_ne {i' i : spec.Port} (h : i' ≠ i) (E : QReg)
    (ℓ : A ≃ spec.In i' × E)
    (k : spec.Result i' → QuantumComp L spec X (QReg.of (spec.Out i' × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    R.queryMass I (QuantumComp.queryBind i' E ℓ k) ρ i =
      ∑' r, R.queryMass I (k r) ((R.queryStep i' E ℓ).branch r ρ) i := by
  rw [queryMass, tsum_eq_zero_add' ENNReal.summable, queryMassAt_queryBind_of_ne_zero R I h,
    zero_add]
  simp only [queryMassAt_queryBind_succ, queryMass]
  rw [ENNReal.tsum_comm]

/-- On the zero state there is no mass. -/
theorem queryMass_zero (x : QuantumComp L spec X A) (i : spec.Port) :
    R.queryMass I x 0 i = 0 := by
  simp [queryMass, queryMassAt_zero]

/-- On positive semidefinite inputs, the total mass is countably additive in the state. -/
theorem queryMass_tsum_state (x : QuantumComp L spec X A) {ι : Type*}
    {f : ι → Matrix (A × R.D) (A × R.D) ℂ} (hf : Summable f) (hpos : ∀ b, (f b).PosSemidef)
    (i : spec.Port) :
    R.queryMass I x (∑' b, f b) i = ∑' b, R.queryMass I x (f b) i := by
  simp only [queryMass, R.queryMassAt_tsum_state I x hf hpos]
  exact ENNReal.tsum_comm

/-- **Mass and query budgets** (the analogue of Remark 4.2 of ePrint 2025/2166). A program that
calls port `i` at most `n` times on every path has mass at most `n` times the trace of the
initial state on `i`. -/
theorem queryMass_le_of_isQueryBoundAt {x : QuantumComp L spec X A} {i : spec.Port} {n : ℕ}
    (hx : x.IsQueryBoundAt i n) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.queryMass I x ρ i ≤ n * ENNReal.ofReal ρ.trace.re := by
  induction x using QuantumComp.inductionOn generalizing n with
  | pure _ _ => simp
  | primBind _ o k ih =>
    rw [QuantumComp.isQueryBoundAt_primBind_iff] at hx
    rw [queryMass_primBind]
    refine (ENNReal.tsum_le_tsum fun b ↦
      ih b (hx b) (((I o).frame R.D).posSemidef_branch_apply b hρ)).trans ?_
    rw [ENNReal.tsum_mul_left]
    have := (((I o).frame R.D).isCPTNIFamily).tsum_ofReal_trace_re_le hρ
    gcongr
  | queryBind _ i' E ℓ k ih =>
    rw [QuantumComp.isQueryBoundAt_queryBind_iff] at hx
    have hstep := (R.queryStep i' E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    by_cases h : i' = i
    · subst h
      obtain ⟨hn, hk⟩ := hx.1 rfl
      rw [queryMass_queryBind_self]
      refine (add_le_add le_rfl (ENNReal.tsum_le_tsum fun r ↦
        ih r (hk r) ((R.queryStep i' E ℓ).posSemidef_branch_apply r hρ))).trans ?_
      rw [ENNReal.tsum_mul_left]
      calc ENNReal.ofReal ρ.trace.re + ((n - 1 : ℕ) : ℝ≥0∞) *
            ∑' r, ENNReal.ofReal ((R.queryStep i' E ℓ).branch r ρ).trace.re
          ≤ ENNReal.ofReal ρ.trace.re + ((n - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re :=
            by gcongr
        _ = n * ENNReal.ofReal ρ.trace.re := by
            rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' hn]
    · rw [queryMass_queryBind_of_ne R I h]
      refine (ENNReal.tsum_le_tsum fun r ↦
        ih r (hx.2 h r) ((R.queryStep i' E ℓ).posSemidef_branch_apply r hρ)).trans ?_
      rw [ENNReal.tsum_mul_left]
      gcongr

/-- **Masses add under sequencing.** The mass of `x.bind k` on port `i` is the mass of `x` plus,
for every leaf `p` of `x`, the mass of the continuation `k p.1 p.2` from the branch of the run of
`x` at `p`. -/
theorem queryMass_bind (x : QuantumComp L spec X A) (k : ∀ u, X u → QuantumComp L spec Y u)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (i : spec.Port) :
    R.queryMass I (x.bind k) ρ i =
      R.queryMass I x ρ i + ∑' p, R.queryMass I (k p.1 p.2) ((R.run I x).branch p ρ) i := by
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    rw [QuantumComp.pure_bind, queryMass_pure, zero_add, run_pure,
      tsum_eq_single (⟨_, y⟩ : Σ u, X u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply, queryMass_zero],
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
  | primBind _ o k' ih =>
    have hb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    rw [QuantumComp.primBind_bind, queryMass_primBind, queryMass_primBind, run_primBind]
    simp only [fun b ↦ ih b (hb b), DSubInstrument.branch_bind_apply]
    rw [ENNReal.tsum_add]
    congr 1
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun p ↦ (R.queryMass_tsum_state I _
      ((((I o).frame R.D).isCPTNIFamily.comp_eval
        (fun b ↦ (R.run I (k' b)).isCPTNIFamily) p).summable_apply ρ)
      (fun b ↦ (R.run I (k' b)).posSemidef_branch_apply p (hb b)) i).symm
  | queryBind _ i' E ℓ k' ih =>
    have hb := fun r ↦ (R.queryStep i' E ℓ).posSemidef_branch_apply r hρ
    have hrun : ∀ p, (R.run I (QuantumComp.queryBind i' E ℓ k')).branch p ρ =
        ∑' r, (R.run I (k' r)).branch p ((R.queryStep i' E ℓ).branch r ρ) := fun p ↦ by
      rw [run_queryBind, DSubInstrument.branch_bind_apply]
    have htail : ∑' p, R.queryMass I (k p.1 p.2)
          ((R.run I (QuantumComp.queryBind i' E ℓ k')).branch p ρ) i =
        ∑' r, ∑' p, R.queryMass I (k p.1 p.2)
          ((R.run I (k' r)).branch p ((R.queryStep i' E ℓ).branch r ρ)) i := by
      rw [ENNReal.tsum_comm]
      refine tsum_congr fun p ↦ ?_
      rw [hrun p]
      exact R.queryMass_tsum_state I _
        (((R.queryStep i' E ℓ).isCPTNIFamily.comp_eval
          (fun r ↦ (R.run I (k' r)).isCPTNIFamily) p).summable_apply ρ)
        (fun r ↦ (R.run I (k' r)).posSemidef_branch_apply p (hb r)) i
    rw [QuantumComp.queryBind_bind, htail]
    by_cases h : i' = i
    · subst h
      rw [queryMass_queryBind_self, queryMass_queryBind_self, add_assoc, ← ENNReal.tsum_add]
      simp only [fun r ↦ ih r (hb r)]
    · rw [queryMass_queryBind_of_ne R I h, queryMass_queryBind_of_ne R I h, ← ENNReal.tsum_add]
      simp only [fun r ↦ ih r (hb r)]


/-! ## Index masses -/

section IndexMass

variable {κ : spec.Port → Type*} (B : ∀ i, κ i → Matrix (spec.In i) (spec.In i) ℂ)

open Classical in
/-- **Index mass of the `j`-th call** (ePrint 2025/2166, §4.1–4.2, for a coherent index). For
operators `B i k` on the input register of each port `i`, typically the orthogonal projections
onto the values `k` of an index register carried by the input, the weight of the `j`-th call of
`x`, run against `R` from `ρ`, in the block `k` of port `i`: the trace of
`(B i k ⊗ 1) σ (B i k ⊗ 1)ᴴ` for the input `σ` of the call, on the paths where that call is on
port `i`. Index masses are labelled by the pairs `c = ⟨i, k⟩`.

With a single port and the projections `|k⟩⟨k| ⊗ 1` of the index register, these are the masses
`mass(A, k, j) = ‖P_mass^(k) |ψ_j⟩‖²` of the paper. With one block per port and `B i k = 1` they
are the query masses (`tsum_indexMassAt_eq_queryMassAt`). -/
@[expose]
noncomputable def indexMassAt (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ)
    (c : Σ i, κ i) (j : ℕ) : ℝ≥0∞ :=
  R.queryWeight I (fun i σ ↦ ∑' k : κ i, if (⟨i, k⟩ : Σ i, κ i) = c then
    ENNReal.ofReal (MatrixMap.conj (B i k ⊗ₖ (1 : Matrix R.D R.D ℂ)) σ).trace.re else 0) x ρ j

/-- **Total index mass** (ePrint 2025/2166, §4.2, `TotalMass` for a coherent index): the sum
over all calls of the index masses of the block `c = ⟨i, k⟩`. -/
@[expose]
noncomputable def indexMass (x : QuantumComp L spec X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ)
    (c : Σ i, κ i) : ℝ≥0∞ :=
  ∑' j, R.indexMassAt I B x ρ c j

/-- A program that stops at once has no index mass. -/
@[simp]
theorem indexMassAt_pure (y : X A) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (c : Σ i, κ i) (j : ℕ) :
    R.indexMassAt I B (QuantumComp.pure (L := L) (spec := spec) y) ρ c j = 0 :=
  rfl

/-- The index masses of a local operation followed by a continuation are those of the
continuations, from the branches of the operation. -/
@[simp]
theorem indexMassAt_primBind (o : L.Op A)
    (k : (b : L.Outcome o) → QuantumComp L spec X (L.next o b))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (c : Σ i, κ i) (j : ℕ) :
    R.indexMassAt I B (QuantumComp.primBind o k) ρ c j =
      ∑' b, R.indexMassAt I B (k b) (((I o).frame R.D).branch b ρ) c j :=
  rfl

/-- A program that starts with a call of port `i` puts on the block `k` of its first call the
weight of the block in the input of the call. -/
theorem indexMassAt_queryBind_self_zero (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (b : κ i) :
    R.indexMassAt I B (QuantumComp.queryBind i E ℓ k) ρ ⟨i, b⟩ 0 =
      ENNReal.ofReal (MatrixMap.conj (B i b ⊗ₖ (1 : Matrix R.D R.D ℂ))
        (callInput ℓ R.D ρ)).trace.re := by
  classical
  rw [indexMassAt, queryWeight_queryBind_zero, tsum_eq_single b fun b' hb' ↦ by simp [hb']]
  simp

/-- The index masses of the later calls of a program that starts with a call are those of the
continuations, from the branches of the call. -/
@[simp]
theorem indexMassAt_queryBind_succ (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E)
    (k : spec.Result i → QuantumComp L spec X (QReg.of (spec.Out i × E)))
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (c : Σ i, κ i) (j : ℕ) :
    R.indexMassAt I B (QuantumComp.queryBind i E ℓ k) ρ c (j + 1) =
      ∑' r, R.indexMassAt I B (k r) ((R.queryStep i E ℓ).branch r ρ) c j :=
  rfl

omit B in
open Classical in
/-- The blocks of a port, summed against constants. -/
private theorem tsum_mul_tsum_ite_sigma (C : (Σ i, κ i) → ℝ≥0∞) (i : spec.Port) (f : κ i → ℝ≥0∞) :
    ∑' c, C c * ∑' k : κ i, (if (⟨i, k⟩ : Σ i, κ i) = c then f k else 0) =
      ∑' k, C ⟨i, k⟩ * f k := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k ↦ ?_
  rw [tsum_eq_single ⟨i, k⟩ fun c hc ↦ by simp [Ne.symm hc]]
  simp

/-- **Weights by index masses.** If the weight of a call of port `i` is at most the weights
`tr ((B i k ⊗ 1) σ (B i k ⊗ 1)ᴴ)` of its blocks, weighted by `C ⟨i, k⟩`, the weight of the `j`-th
call is at most the index masses of the `j`-th call weighted by `C`. -/
theorem queryWeight_le_tsum_mul_indexMassAt (C : (Σ i, κ i) → ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ ∑' k, C ⟨i, k⟩ *
      ENNReal.ofReal (MatrixMap.conj (B i k ⊗ₖ (1 : Matrix R.D R.D ℂ)) σ).trace.re)
    (x : QuantumComp L spec X A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (j : ℕ) : R.queryWeight I w x ρ j ≤ ∑' c, C c * R.indexMassAt I B x ρ c j := by
  classical
  refine (R.queryWeight_mono I hw x hρ j).trans_eq ?_
  simp only [indexMassAt, ← queryWeight_const_mul, tsum_queryWeight]
  congr 1
  funext i σ
  exact (tsum_mul_tsum_ite_sigma C i _).symm

/-- **Summed weights by total index masses.** Under the hypothesis of
`queryWeight_le_tsum_mul_indexMassAt`, the weights summed over all calls are at most the total
index masses weighted by `C`. -/
theorem tsum_queryWeight_le_tsum_mul_indexMass (C : (Σ i, κ i) → ℝ≥0∞)
    (hw : ∀ i σ, σ.PosSemidef → w i σ ≤ ∑' k, C ⟨i, k⟩ *
      ENNReal.ofReal (MatrixMap.conj (B i k ⊗ₖ (1 : Matrix R.D R.D ℂ)) σ).trace.re)
    (x : QuantumComp L spec X A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' j, R.queryWeight I w x ρ j ≤ ∑' c, C c * R.indexMass I B x ρ c := by
  refine (ENNReal.tsum_le_tsum fun j ↦
    R.queryWeight_le_tsum_mul_indexMassAt I B C hw x hρ j).trans_eq ?_
  rw [ENNReal.tsum_comm]
  simp only [indexMass, ENNReal.tsum_mul_left]

omit B in
/-- The blocks of a complete family `∑ₖ (B k)ᴴ B k = 1` split the trace. -/
theorem tsum_ofReal_trace_conj_kronecker_one {J D : Type*} [Fintype J] [DecidableEq J]
    [Fintype D] [DecidableEq D] {K : Type*} [Fintype K] {B : K → Matrix J J ℂ}
    (hB : ∑ k, (B k)ᴴ * B k = 1) {σ : Matrix (J × D) (J × D) ℂ} (hσ : σ.PosSemidef) :
    ∑' k, ENNReal.ofReal (MatrixMap.conj (B k ⊗ₖ (1 : Matrix D D ℂ)) σ).trace.re =
      ENNReal.ofReal σ.trace.re := by
  have hnn : ∀ k, 0 ≤ (MatrixMap.conj (B k ⊗ₖ (1 : Matrix D D ℂ)) σ).trace.re := fun k ↦
    (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
  have h1 : ∑ k, (B k ⊗ₖ (1 : Matrix D D ℂ))ᴴ * (B k ⊗ₖ (1 : Matrix D D ℂ)) = 1 := by
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul]
    rw [← Matrix.one_kronecker_one, ← hB]
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [Matrix.sum_apply, Finset.sum_mul]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ hnn k]
  congr 1
  simp only [MatrixMap.trace_conj_apply, ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    h1, Matrix.one_mul]

/-- **Index masses refine query masses** (the analogue of Remark 4.2 of ePrint 2025/2166 for a
coherent index): if the blocks of port `i` are complete, `∑ₖ (B i k)ᴴ B i k = 1`, the index
masses of its blocks at the `j`-th call add up to its query mass. -/
theorem tsum_indexMassAt_eq_queryMassAt (i : spec.Port) [Fintype (κ i)]
    (hB : ∑ k, (B i k)ᴴ * B i k = 1) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) (j : ℕ) :
    ∑' k, R.indexMassAt I B x ρ ⟨i, k⟩ j = R.queryMassAt I x ρ i j := by
  classical
  simp only [indexMassAt, queryMassAt, tsum_queryWeight]
  refine R.queryWeight_congr I (fun i' σ hσ ↦ ?_) x hρ j
  by_cases h : i' = i
  · subst h
    simp only [↓reduceIte]
    rw [ENNReal.tsum_comm, ← tsum_ofReal_trace_conj_kronecker_one hB hσ]
    refine tsum_congr fun k ↦ ?_
    rw [tsum_eq_single k fun k' hk' ↦ by simp [Ne.symm hk']]
    simp
  · simp [h]

/-- **Total index masses refine total query masses**: under the hypothesis of
`tsum_indexMassAt_eq_queryMassAt`, the total index masses of the blocks of port `i` add up to
its total query mass. -/
theorem tsum_indexMass_eq_queryMass (i : spec.Port) [Fintype (κ i)]
    (hB : ∑ k, (B i k)ᴴ * B i k = 1) (x : QuantumComp L spec X A)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    ∑' k, R.indexMass I B x ρ ⟨i, k⟩ = R.queryMass I x ρ i := by
  simp only [indexMass, queryMass]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun j ↦ R.tsum_indexMassAt_eq_queryMassAt I B i hB x hρ j

end IndexMass

end QuantumRuntime

end Quantum

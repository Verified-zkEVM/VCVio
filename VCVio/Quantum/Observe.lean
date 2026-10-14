/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import ToMathlib.MeasureTheory.Measure.Subprobability
public import VCVio.Quantum.DSubInstrument
public import VCVio.Quantum.SubInstrument

/-!
# Observing quantum computations

Running a subinstrument on a state produces a classical outcome with a weight, the trace of the
corresponding branch applied to the state. `Quantum.SubInstrument.outcomeMeasure` collects these
weights into a Mathlib measure on the outcome type, the sum `Measure.sum` of the weighted point
masses over all outcomes, and `Quantum.SubInstrument.post` is the unnormalized state left after a
given outcome. The outcome type carries any measurable structure; the weight of a single outcome
is read off under `MeasurableSingletonClass`
(`Quantum.SubInstrument.outcomeMeasure_apply_singleton`). Since the branch family is summable
rather than finitely supported, the outcome measure may charge infinitely many outcomes.

States are subnormalized (`Quantum.SubState`): trace at most one, the deficit being the weight of
failure so far. The outcome measure therefore has total mass at most one, and the chain rule
`Quantum.SubInstrument.outcomeMeasure_bind` expresses the outcome measure of a composite through
the post-branch substates of its first part, with no renormalization.

The bundled semantics built from the outcome measure, `Quantum.SubInstrument.semanticsVia`, is
in `VCVio.Quantum.Semantics`.

Dependent subinstruments are observed in the same way. `Quantum.DSubInstrument.post` is the
family of post-branch substates, one on the system `B i` for each outcome `i`, and
`Quantum.DSubInstrument.outcomeMeasure` has the chain rule
`Quantum.DSubInstrument.outcomeMeasure_bind`. Under the constant-codomain equivalence both agree
with the versions for subinstruments (`Quantum.SubInstrument.post_toD`,
`Quantum.SubInstrument.outcomeMeasure_toD`).
-/

public section

open MeasureTheory
open scoped ComplexOrder

namespace Quantum

/-- A subnormalized state of the system with basis `A`: a positive semidefinite matrix of trace
at most one. Trace below one records the weight of failure. -/
@[ext]
structure SubState (A : Type*) [Fintype A] where
  /-- The unnormalized density matrix. -/
  matrix : Matrix A A ℂ
  /-- The density matrix is positive semidefinite. -/
  posSemidef : matrix.PosSemidef
  /-- The density matrix has trace at most one. -/
  trace_re_le_one : matrix.trace.re ≤ 1

/-- A substate has nonnegative trace. -/
theorem SubState.trace_re_nonneg {A : Type*} [Fintype A] (ρ : SubState A) :
    0 ≤ ρ.matrix.trace.re :=
  ρ.posSemidef.trace_re_nonneg

namespace SubInstrument

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {α β : Type*}

/-! ## Post-branch substates -/

/-- The substate left after the subinstrument reports outcome `a` on `ρ`: the unnormalized
state `p.branch a ρ`, whose trace is the weight of that outcome. -/
@[expose]
def post (p : SubInstrument A B α) (ρ : SubState A) (a : α) : SubState B where
  matrix := p.branch a ρ.matrix
  posSemidef := p.posSemidef_branch_apply a ρ.posSemidef
  trace_re_le_one := (p.trace_re_branch_apply_le a ρ.posSemidef).trans ρ.trace_re_le_one

/-- The matrix of the post-branch substate at `a` is the branch at `a` applied to the input. -/
@[simp]
theorem matrix_post (p : SubInstrument A B α) (ρ : SubState A) (a : α) :
    (p.post ρ a).matrix = p.branch a ρ.matrix :=
  rfl

/-- After `pure a` reports `a`, the substate is unchanged. -/
@[simp]
theorem post_pure_self (a : α) (ρ : SubState A) :
    (SubInstrument.pure a : SubInstrument A A α).post ρ a = ρ :=
  SubState.ext <| by simp

/-! ## Outcome measures -/

/-- The measure of classical outcomes of a subinstrument run on the substate `ρ`: outcome `a`
has weight the trace of `p.branch a ρ`, and the outcome measure is the sum of the weighted point
masses over all outcomes. Its total mass is the trace of the total map on `ρ`, and missing mass is
failure. -/
@[expose]
noncomputable def outcomeMeasure [MeasurableSpace α] (p : SubInstrument A B α)
    (ρ : SubState A) : Measure α :=
  Measure.sum fun a ↦ ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac a

section outcomeMeasure

variable [MeasurableSpace α]

/-- The outcome measure as a sum of weighted point masses over all outcomes. -/
theorem outcomeMeasure_eq_sum (p : SubInstrument A B α) (ρ : SubState A) :
    p.outcomeMeasure ρ =
      Measure.sum fun a ↦ ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac a :=
  rfl

/-- The outcome measure of a measurable set sums the weights of the outcomes in it. -/
theorem outcomeMeasure_apply (p : SubInstrument A B α) (ρ : SubState A) {s : Set α}
    (hs : MeasurableSet s) :
    p.outcomeMeasure ρ s =
      ∑' a, ENNReal.ofReal (p.branch a ρ.matrix).trace.re * s.indicator 1 a := by
  simp only [outcomeMeasure, Measure.sum_apply _ hs, Measure.smul_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]

/-- The outcome measure as a sum over any finite set of outcomes containing the support of the
branch family. -/
theorem outcomeMeasure_eq_sum_of_subset (p : SubInstrument A B α) (ρ : SubState A)
    {s : Finset α} (hs : Function.support p.branch ⊆ s) :
    p.outcomeMeasure ρ =
      ∑ a ∈ s, ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac a := by
  ext t ht
  rw [outcomeMeasure_apply _ _ ht, Measure.coe_finsetSum, Finset.sum_apply,
    tsum_eq_sum (s := s) fun a ha ↦ by
      rw [Function.notMem_support.mp fun h ↦ ha (hs h), LinearMap.zero_apply, Matrix.trace_zero,
        Complex.zero_re, ENNReal.ofReal_zero, zero_mul]]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ ht, smul_eq_mul]

/-- The outcome measure as a sum of weighted point masses over a finite type of outcomes. -/
theorem outcomeMeasure_eq_sum_univ [Fintype α] (p : SubInstrument A B α) (ρ : SubState A) :
    p.outcomeMeasure ρ =
      ∑ a, ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac a :=
  p.outcomeMeasure_eq_sum_of_subset ρ fun a _ ↦ Finset.mem_coe.mpr (Finset.mem_univ a)

/-- The total mass of the outcome measure is the trace of the total map on the substate. -/
theorem outcomeMeasure_apply_univ (p : SubInstrument A B α) (ρ : SubState A) :
    p.outcomeMeasure ρ Set.univ = ENNReal.ofReal (p.total ρ.matrix).trace.re := by
  rw [outcomeMeasure_apply _ _ MeasurableSet.univ, trace_re_total_apply,
    ENNReal.ofReal_tsum_of_nonneg (fun a ↦ p.trace_re_branch_apply_nonneg a ρ.posSemidef)
      (p.isCPTNIFamily.summable_trace_re_apply ρ.posSemidef)]
  simp

/-- The outcome measure has total mass at most one. -/
theorem outcomeMeasure_apply_univ_le_one (p : SubInstrument A B α) (ρ : SubState A) :
    p.outcomeMeasure ρ Set.univ ≤ 1 := by
  rw [outcomeMeasure_apply_univ]
  exact ENNReal.ofReal_le_one.mpr ((p.isTNI_total _ ρ.posSemidef).trans ρ.trace_re_le_one)

/-- Outcome measures are subprobability measures. -/
instance outcomeMeasure.instIsSubprobabilityMeasure (p : SubInstrument A B α) (ρ : SubState A) :
    IsSubprobabilityMeasure (p.outcomeMeasure ρ) :=
  ⟨p.outcomeMeasure_apply_univ_le_one ρ⟩

/-- A lossless subinstrument preserves total mass: its outcome measure has the trace of the
input substate as total mass. -/
theorem Lossless.outcomeMeasure_apply_univ {p : SubInstrument A B α} (hp : p.Lossless)
    (ρ : SubState A) : p.outcomeMeasure ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [SubInstrument.outcomeMeasure_apply_univ, hp ρ.matrix]

/-- The weight of a single outcome is the trace of its post-branch substate. -/
theorem outcomeMeasure_apply_singleton [MeasurableSingletonClass α] (p : SubInstrument A B α)
    (ρ : SubState A) (a : α) :
    p.outcomeMeasure ρ {a} = ENNReal.ofReal (p.branch a ρ.matrix).trace.re := by
  rw [outcomeMeasure_apply _ _ (measurableSet_singleton a),
    tsum_eq_single a fun b hb ↦ by simp [hb]]
  simp

/-- The outcome measure of `pure a` is the point mass at `a` weighted by the trace of the
substate. -/
@[simp]
theorem outcomeMeasure_pure (a : α) (ρ : SubState A) :
    (SubInstrument.pure a : SubInstrument A A α).outcomeMeasure ρ =
      ENNReal.ofReal ρ.matrix.trace.re • Measure.dirac a := by
  rw [outcomeMeasure_eq_sum_of_subset _ ρ (s := {a}) fun a' ha' ↦ Finset.mem_coe.mpr <|
      Finset.mem_singleton.mpr <| Classical.byContradiction fun h ↦ ha' (branch_pure_of_ne h),
    Finset.sum_singleton, branch_pure_self, LinearMap.id_apply]

/-- The outcome measure of the failing subinstrument is zero. -/
@[simp]
theorem outcomeMeasure_fail (ρ : SubState A) :
    (SubInstrument.fail : SubInstrument A B α).outcomeMeasure ρ = 0 := by
  rw [outcomeMeasure_eq_sum_of_subset _ ρ (s := ∅) fun a ha ↦ (ha rfl).elim, Finset.sum_empty]

end outcomeMeasure

/-- Chain rule: the outcome measure of a composite sums, over the outcomes of the first
subinstrument, the outcome measure of the continuation on the post-branch substate. -/
theorem outcomeMeasure_bind [MeasurableSpace β] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) (ρ : SubState A) :
    (p.bind k).outcomeMeasure ρ = Measure.sum fun a ↦ (k a).outcomeMeasure (p.post ρ a) := by
  ext t ht
  rw [outcomeMeasure_apply _ _ ht, Measure.sum_apply _ ht]
  simp_rw [outcomeMeasure_apply _ _ ht, matrix_post]
  have h := p.isCPTNIFamily.comp_eval fun a ↦ (k a).isCPTNIFamily
  rw [← ENNReal.tsum_comm]
  refine tsum_congr fun b ↦ ?_
  rw [branch_bind, MatrixMap.trace_re_familyBind_apply p.isCPTNIFamily
      (fun a ↦ (k a).isCPTNIFamily),
    ENNReal.ofReal_tsum_of_nonneg (f := fun a ↦ ((k a).branch b (p.branch a ρ.matrix)).trace.re)
      (fun a ↦ (h b).trace_re_apply_nonneg a ρ.posSemidef)
      ((h b).summable_trace_re_apply ρ.posSemidef), ENNReal.tsum_mul_right]

end SubInstrument

/-! ## Dependent subinstruments -/

namespace DSubInstrument

variable {A : Type*} [Fintype A] {ι κ : Type*} {B : ι → Type*} [∀ i, Fintype (B i)]
  {C : κ → Type*} [∀ c, Fintype (C c)]

/-! ### Post-branch substates -/

/-- The substate left after the dependent subinstrument reports outcome `i` on `ρ`: the
unnormalized state `p.branch i ρ` of the system `B i`, whose trace is the weight of that
outcome. -/
@[expose]
def post (p : DSubInstrument A ι B) (ρ : SubState A) (i : ι) : SubState (B i) where
  matrix := p.branch i ρ.matrix
  posSemidef := p.posSemidef_branch_apply i ρ.posSemidef
  trace_re_le_one := (p.trace_re_branch_apply_le i ρ.posSemidef).trans ρ.trace_re_le_one

/-- The matrix of the post-branch substate at `i` is the branch at `i` applied to the input. -/
@[simp]
theorem matrix_post (p : DSubInstrument A ι B) (ρ : SubState A) (i : ι) :
    (p.post ρ i).matrix = p.branch i ρ.matrix :=
  rfl

/-- After `ret B i` reports `i`, the substate is unchanged. -/
@[simp]
theorem post_ret_self (i : ι) (ρ : SubState (B i)) : (ret B i).post ρ i = ρ :=
  SubState.ext <| by simp

/-! ### Outcome measures -/

/-- The measure of classical outcomes of a dependent subinstrument run on the substate `ρ`:
outcome `i` has weight the trace of `p.branch i ρ`, and the outcome measure is the sum of the
weighted point masses over all outcomes. Its total mass is the trace functional of the branches at
`ρ`, and missing mass is failure. -/
@[expose]
noncomputable def outcomeMeasure [MeasurableSpace ι] (p : DSubInstrument A ι B)
    (ρ : SubState A) : Measure ι :=
  Measure.sum fun i ↦ ENNReal.ofReal (p.branch i ρ.matrix).trace.re • Measure.dirac i

section outcomeMeasure

variable [MeasurableSpace ι]

/-- The outcome measure as a sum of weighted point masses over all outcomes. -/
theorem outcomeMeasure_eq_sum (p : DSubInstrument A ι B) (ρ : SubState A) :
    p.outcomeMeasure ρ =
      Measure.sum fun i ↦ ENNReal.ofReal (p.branch i ρ.matrix).trace.re • Measure.dirac i :=
  rfl

/-- The outcome measure of a measurable set sums the weights of the outcomes in it. -/
theorem outcomeMeasure_apply (p : DSubInstrument A ι B) (ρ : SubState A) {s : Set ι}
    (hs : MeasurableSet s) :
    p.outcomeMeasure ρ s =
      ∑' i, ENNReal.ofReal (p.branch i ρ.matrix).trace.re * s.indicator 1 i := by
  simp only [outcomeMeasure, Measure.sum_apply _ hs, Measure.smul_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul]

/-- The outcome measure as a sum of weighted point masses over any finite set of outcomes
outside which the branches vanish. -/
theorem outcomeMeasure_eq_sum_of_forall_notMem (p : DSubInstrument A ι B) (ρ : SubState A)
    {s : Finset ι} (hs : ∀ i ∉ s, p.branch i = 0) :
    p.outcomeMeasure ρ =
      ∑ i ∈ s, ENNReal.ofReal (p.branch i ρ.matrix).trace.re • Measure.dirac i := by
  ext t ht
  rw [outcomeMeasure_apply _ _ ht, Measure.coe_finsetSum, Finset.sum_apply,
    tsum_eq_sum (s := s) fun i hi ↦ by
      rw [hs i hi, LinearMap.zero_apply, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero,
        zero_mul]]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ ht, smul_eq_mul]

/-- The outcome measure as a sum of weighted point masses over a finite type of outcomes. -/
theorem outcomeMeasure_eq_sum_univ [Fintype ι] (p : DSubInstrument A ι B) (ρ : SubState A) :
    p.outcomeMeasure ρ =
      ∑ i, ENNReal.ofReal (p.branch i ρ.matrix).trace.re • Measure.dirac i :=
  p.outcomeMeasure_eq_sum_of_forall_notMem ρ fun i hi ↦ absurd (Finset.mem_univ i) hi

/-- The total mass of the outcome measure is the trace functional of the branches at the
substate. -/
theorem outcomeMeasure_apply_univ (p : DSubInstrument A ι B) (ρ : SubState A) :
    p.outcomeMeasure ρ Set.univ =
      ENNReal.ofReal (MatrixMap.familyTrace p.branch ρ.matrix).re := by
  rw [outcomeMeasure_apply _ _ MeasurableSet.univ, p.isCPTNIFamily.familyTrace_apply,
    p.isCPTNIFamily.re_tsum_trace_apply,
    ENNReal.ofReal_tsum_of_nonneg (fun i ↦ p.trace_re_branch_apply_nonneg i ρ.posSemidef)
      (p.isCPTNIFamily.summable_trace_re_apply ρ.posSemidef)]
  simp

/-- The outcome measure has total mass at most one. -/
theorem outcomeMeasure_apply_univ_le_one (p : DSubInstrument A ι B) (ρ : SubState A) :
    p.outcomeMeasure ρ Set.univ ≤ 1 := by
  rw [outcomeMeasure_apply_univ, p.isCPTNIFamily.familyTrace_apply,
    p.isCPTNIFamily.re_tsum_trace_apply]
  exact ENNReal.ofReal_le_one.mpr ((p.tsum_trace_re_le ρ.posSemidef).trans ρ.trace_re_le_one)

/-- Outcome measures of dependent subinstruments are subprobability measures. -/
instance outcomeMeasure.instIsSubprobabilityMeasure (p : DSubInstrument A ι B)
    (ρ : SubState A) : IsSubprobabilityMeasure (p.outcomeMeasure ρ) :=
  ⟨p.outcomeMeasure_apply_univ_le_one ρ⟩

/-- A lossless dependent subinstrument preserves total mass: its outcome measure has the trace
of the input substate as total mass. -/
theorem Lossless.outcomeMeasure_apply_univ {p : DSubInstrument A ι B} (hp : p.Lossless)
    (ρ : SubState A) : p.outcomeMeasure ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [DSubInstrument.outcomeMeasure_apply_univ, hp ρ.matrix]

/-- The weight of a single outcome is the trace of its post-branch substate. -/
theorem outcomeMeasure_apply_singleton [MeasurableSingletonClass ι] (p : DSubInstrument A ι B)
    (ρ : SubState A) (i : ι) :
    p.outcomeMeasure ρ {i} = ENNReal.ofReal (p.branch i ρ.matrix).trace.re := by
  rw [outcomeMeasure_apply _ _ (measurableSet_singleton i),
    tsum_eq_single i fun j hj ↦ by simp [hj]]
  simp

/-- The outcome measure of `ret B i` is the point mass at `i` weighted by the trace of the
substate. -/
@[simp]
theorem outcomeMeasure_ret (i : ι) (ρ : SubState (B i)) :
    (ret B i).outcomeMeasure ρ = ENNReal.ofReal ρ.matrix.trace.re • Measure.dirac i := by
  rw [outcomeMeasure_eq_sum_of_forall_notMem _ ρ (s := {i})
      fun j hj ↦ branch_ret_of_ne B (Finset.notMem_singleton.mp hj),
    Finset.sum_singleton, branch_ret_self, LinearMap.id_apply]

/-- The outcome measure of the failing dependent subinstrument is zero. -/
@[simp]
theorem outcomeMeasure_fail (ρ : SubState A) :
    (DSubInstrument.fail : DSubInstrument A ι B).outcomeMeasure ρ = 0 := by
  rw [outcomeMeasure_eq_sum_of_forall_notMem _ ρ (s := ∅) fun _ _ ↦ rfl, Finset.sum_empty]

end outcomeMeasure

/-- Chain rule: the outcome measure of a composite sums, over the outcomes of the first
dependent subinstrument, the outcome measure of the continuation on the post-branch
substate. -/
theorem outcomeMeasure_bind [MeasurableSpace κ] (p : DSubInstrument A ι B)
    (k : (i : ι) → DSubInstrument (B i) κ C) (ρ : SubState A) :
    (p.bind k).outcomeMeasure ρ = Measure.sum fun i ↦ (k i).outcomeMeasure (p.post ρ i) := by
  ext t ht
  rw [outcomeMeasure_apply _ _ ht, Measure.sum_apply _ ht]
  simp_rw [outcomeMeasure_apply _ _ ht, matrix_post]
  have h := p.isCPTNIFamily.comp_eval fun i ↦ (k i).isCPTNIFamily
  rw [← ENNReal.tsum_comm]
  refine tsum_congr fun c ↦ ?_
  rw [branch_bind, MatrixMap.trace_re_familyBind_apply p.isCPTNIFamily
      (fun i ↦ (k i).isCPTNIFamily),
    ENNReal.ofReal_tsum_of_nonneg (f := fun i ↦ ((k i).branch c (p.branch i ρ.matrix)).trace.re)
      (fun i ↦ (h c).trace_re_apply_nonneg i ρ.posSemidef)
      ((h c).summable_trace_re_apply ρ.posSemidef), ENNReal.tsum_mul_right]

end DSubInstrument

/-! ### The constant-codomain case -/

namespace SubInstrument

variable {A B : Type*} [Fintype A] [Fintype B] {α : Type*}

/-- Post-branch substates agree under the constant-codomain equivalence. -/
@[simp]
theorem post_toD (p : SubInstrument A B α) (ρ : SubState A) (a : α) :
    (toD p).post ρ a = p.post ρ a :=
  rfl

/-- Outcome measures agree under the constant-codomain equivalence. -/
@[simp]
theorem outcomeMeasure_toD [MeasurableSpace α] (p : SubInstrument A B α) (ρ : SubState A) :
    (toD p).outcomeMeasure ρ = p.outcomeMeasure ρ :=
  rfl

end SubInstrument

end Quantum

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

A quantum computation is observed once, at the end, by the probabilities of its classical
outcomes. Running the subinstrument `p` on the state `ρ` reports outcome `a` with weight
`tr (p.branch a ρ)`. This is the Born rule. `Quantum.DSubInstrument.outcomeMeasure p ρ` collects
these weights into a Mathlib measure on the outcomes, the sum (`Measure.sum`) of weighted point
masses, and `Quantum.DSubInstrument.post p ρ a = p.branch a ρ` is the state left behind after
outcome `a`.

## Unnormalized post-states

`post p ρ a` is not divided by the probability of `a`: its trace is that probability. When the
probability is positive, the conditional state in the usual sense is `post p ρ a` divided by its
trace. Keeping the weight inside the state has two consequences. Outcomes of probability zero need
no separate case, since their post-state is zero. And the chain rule
`Quantum.DSubInstrument.outcomeMeasure_bind` evaluates the continuation on the unnormalized
post-state, so the weight of the first outcome is already included and is not multiplied in again.

## Subnormalized states and failure

States are subnormalized (`Quantum.SubState`): their trace is at most one, and the deficit is the
probability that the computation has already failed. The outcome measure has total mass
`tr (p.total ρ) ≤ tr ρ ≤ 1`. Its deficit from one is the failure before `p` plus the trace `p`
loses.

The outcome type may carry any measurable structure. The defining sum has only countably many
nonzero weights; with measurable singletons these are the nonzero singleton masses
(`Quantum.DSubInstrument.outcomeMeasure_apply_singleton`). Measurable events have the corresponding
sums of weights. The weighted Dirac sum does not describe a nonatomic measurement law.

Dependent subinstruments are observed in the same way. `Quantum.DSubInstrument.post` is the
family of post-states, one on the system `B i` for each outcome `i`, and
`Quantum.DSubInstrument.outcomeMeasure` has the chain rule
`Quantum.DSubInstrument.outcomeMeasure_bind`. The same API applies directly to the
constant-codomain abbreviation `SubInstrument`. The bundled semantics built from the outcome
measure,
`Quantum.SubInstrument.semanticsVia`, is in `VCVio.Quantum.Semantics`.

## References

* J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018.
  PDF page numbers are 1-based. Density matrices: Definition 2.5, printed p. 62,
  [full PDF p. 70](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=70).
  Instruments, outcome probabilities and post-measurement states in the normalized, finite case:
  equations (2.258)–(2.261), printed p. 112,
  [full PDF p. 120](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf#page=120).
-/

public section

open MeasureTheory
open scoped ComplexOrder

namespace Quantum

/-- A subnormalized state of the system `A`: a positive semidefinite matrix `ρ` with
`tr ρ ≤ 1`. Its trace is real and nonnegative because `ρ` is positive semidefinite. Trace one
is a density matrix in the usual sense (Watrous, Definition 2.5, printed p. 62, full PDF p. 70;
see the module references); trace zero forces `ρ = 0`. The deficit `1 - tr ρ` is the probability
that the computation has already failed. -/
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

namespace DSubInstrument

variable {A : Type*} [Fintype A] {ι κ : Type*} {B : ι → Type*} [∀ i, Fintype (B i)]
  {C : κ → Type*} [∀ c, Fintype (C c)]

/-! ### Post-branch substates -/

/-- The state left after `p` reports outcome `i` on `ρ`: the unnormalized matrix `p.branch i ρ` of
the system `B i`. Its trace is the probability of `i`, which is therefore already included. When
that probability `w` is positive, the conditional state in the usual sense is `p.branch i ρ / w`; no
division happens here, so an outcome of probability zero leaves the zero substate. -/
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

/-- The Born outcome measure `μ_ρ = ∑ i, tr (p.branch i ρ) • δ_i`, implemented as a
`Measure.sum`. For normalized `ρ` the coefficients are outcome probabilities; for subnormalized
`ρ` they also include the input's successful mass.

The total mass is `Re (MatrixMap.familyTrace p.branch ρ) ≤ tr ρ ≤ 1`, so missing mass includes
failure before and during `p`. Only countably many coefficients are nonzero. For any measurable
structure on the outcomes, measurable events have the corresponding sums of coefficients. With
`MeasurableSingletonClass`, each singleton has its branch's coefficient
(`outcomeMeasure_apply_singleton`). -/
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

/-- Sum the outcome measure over a finite set containing every nonzero branch. -/
theorem outcomeMeasure_eq_sum_of_subset (p : DSubInstrument A ι B) (ρ : SubState A)
    {s : Finset ι} (hs : {i | p.branch i ≠ 0} ⊆ s) :
    p.outcomeMeasure ρ =
      ∑ i ∈ s, ENNReal.ofReal (p.branch i ρ.matrix).trace.re • Measure.dirac i :=
  p.outcomeMeasure_eq_sum_of_forall_notMem ρ fun _ hi ↦
    Classical.not_not.mp fun hn ↦ hi (hs hn)

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

namespace SubInstrument

variable {A B : Type*} [Fintype A] [Fintype B] {α : Type*} [MeasurableSpace α]

/-- The total outcome mass is the trace of the total map on the substate. -/
theorem outcomeMeasure_apply_univ (p : SubInstrument A B α) (ρ : SubState A) :
    p.outcomeMeasure ρ Set.univ = ENNReal.ofReal (p.total ρ.matrix).trace.re := by
  rw [DSubInstrument.outcomeMeasure_apply_univ, DSubInstrument.familyTrace_branch,
    LinearMap.comp_apply]
  rfl

end SubInstrument

end Quantum

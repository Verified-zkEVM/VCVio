/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.EvalDist.Defs.Semantics.Core
public import VCVio.Quantum.SubInstrument

/-!
# Observing quantum computations

Running a subinstrument on a state produces a classical outcome with a weight, the trace of the
corresponding branch applied to the state. `Quantum.SubInstrument.outcomeMeasure` collects these
weights into a Mathlib measure on the outcome type, and `Quantum.SubInstrument.post` is the
unnormalized state left after a given outcome.

States are subnormalized (`Quantum.SubState`): trace at most one, the deficit being the weight of
failure so far. The outcome measure therefore has total mass at most one, and the chain rule
`Quantum.SubInstrument.outcomeMeasure_bind` expresses the outcome measure of a composite through
the post-branch substates of its first part, with no renormalization.

`Quantum.SubInstrument.semanticsVia` packages the outcome measure from a fixed initial substate
as a bundled `SemanticsVia` on the monad `SubInstrument M M`. Observation fixes the initial state
and discards the final one, so it is not a monad morphism.
-/

public section

open MeasureTheory
open scoped ComplexOrder

universe u w

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
has weight the trace of `p.branch a ρ`. Its total mass is the trace of the total map on `ρ`, and
missing mass is failure. -/
@[expose]
noncomputable def outcomeMeasure [MeasurableSpace α] (p : SubInstrument A B α)
    (ρ : SubState A) : Measure α :=
  p.branch.sum fun a Φ ↦ ENNReal.ofReal (Φ ρ.matrix).trace.re • Measure.dirac a

section outcomeMeasure

variable [MeasurableSpace α]

/-- The outcome measure as a sum of weighted point masses over the support of the branch
family. -/
theorem outcomeMeasure_eq_sum (p : SubInstrument A B α) (ρ : SubState A) :
    p.outcomeMeasure ρ =
      ∑ a ∈ p.branch.support, ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac a :=
  rfl

/-- The outcome measure as a sum over any finite set of outcomes containing the support of the
branch family. -/
theorem outcomeMeasure_eq_sum_of_subset (p : SubInstrument A B α) (ρ : SubState A)
    {s : Finset α} (hs : p.branch.support ⊆ s) :
    p.outcomeMeasure ρ =
      ∑ a ∈ s, ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac a :=
  Finsupp.sum_of_support_subset _ hs _ fun a _ ↦ by simp

/-- The outcome measure as a sum of weighted point masses over a finite type of outcomes. -/
theorem outcomeMeasure_eq_sum_univ [Fintype α] (p : SubInstrument A B α) (ρ : SubState A) :
    p.outcomeMeasure ρ =
      ∑ a, ENNReal.ofReal (p.branch a ρ.matrix).trace.re • Measure.dirac a :=
  p.outcomeMeasure_eq_sum_of_subset ρ (Finset.subset_univ _)

/-- The total mass of the outcome measure is the trace of the total map on the substate. -/
theorem outcomeMeasure_apply_univ (p : SubInstrument A B α) (ρ : SubState A) :
    p.outcomeMeasure ρ Set.univ = ENNReal.ofReal (p.total ρ.matrix).trace.re := by
  rw [outcomeMeasure_eq_sum, Measure.coe_finsetSum, Finset.sum_apply, total_eq_sum,
    LinearMap.sum_apply, Matrix.trace_sum, Complex.re_sum,
    ENNReal.ofReal_sum_of_nonneg fun a _ ↦ p.trace_re_branch_apply_nonneg a ρ.posSemidef]
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
  classical
  rw [outcomeMeasure_eq_sum, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton a),
    smul_eq_mul, Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · simp [not_not.mp h]

/-- The outcome measure of `pure a` is the point mass at `a` weighted by the trace of the
substate. -/
@[simp]
theorem outcomeMeasure_pure (a : α) (ρ : SubState A) :
    (SubInstrument.pure a : SubInstrument A A α).outcomeMeasure ρ =
      ENNReal.ofReal ρ.matrix.trace.re • Measure.dirac a :=
  Finsupp.sum_single_index (by simp)

/-- The outcome measure of the failing subinstrument is zero. -/
@[simp]
theorem outcomeMeasure_fail (ρ : SubState A) :
    (SubInstrument.fail : SubInstrument A B α).outcomeMeasure ρ = 0 :=
  Finsupp.sum_zero_index

end outcomeMeasure

/-- Chain rule: the outcome measure of a composite sums, over the outcomes of the first
subinstrument, the outcome measure of the continuation on the post-branch substate. -/
theorem outcomeMeasure_bind [MeasurableSpace β] (p : SubInstrument A B α)
    (k : α → SubInstrument B C β) (ρ : SubState A) :
    (p.bind k).outcomeMeasure ρ =
      ∑ a ∈ p.branch.support, (k a).outcomeMeasure (p.post ρ a) := by
  classical
  have h₁ := (p.bind k).outcomeMeasure_eq_sum_of_subset ρ
    (Finsupp.support_lbind_subset p.branch fun a ↦ (k a).branch)
  have h₂ : ∀ a ∈ p.branch.support, (k a).outcomeMeasure (p.post ρ a) = _ := fun a ha ↦
    (k a).outcomeMeasure_eq_sum_of_subset (p.post ρ a)
      (Finset.subset_biUnion_of_mem (fun a ↦ (k a).branch.support) ha)
  rw [h₁, Finset.sum_congr rfl h₂, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Finset.sum_smul, branch_bind_apply, LinearMap.sum_apply, Matrix.trace_sum,
    Complex.re_sum]
  simp only [LinearMap.comp_apply, matrix_post]
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ ↦
    (k a).trace_re_branch_apply_nonneg b (p.posSemidef_branch_apply a ρ.posSemidef)]

end SubInstrument

/-! ## Bundled semantics -/

namespace SubInstrument

variable {M : Type u} [Fintype M]

/-- The bundled semantics of subinstruments on the register `M` started from the substate `ρ₀`:
a subinstrument is observed through the measure of its classical results, and the final state
of the register is discarded. -/
@[expose]
noncomputable def semanticsVia (ρ₀ : SubState M) : SemanticsVia (SubInstrument.{u, u, w} M M) where
  Sem := SubInstrument M M
  instMonadSem := inferInstance
  interpret := MonadHom.id (SubInstrument M M)
  observe := fun p ↦ p.outcomeMeasure ρ₀
  observe_apply_univ_le_one := fun p ↦ p.outcomeMeasure_apply_univ_le_one ρ₀

/-- The denotation of a subinstrument under `Quantum.SubInstrument.semanticsVia ρ₀` is its
outcome measure from `ρ₀`. -/
@[simp]
theorem semanticsVia_evalDist (ρ₀ : SubState M) {α : Type w} [MeasurableSpace α]
    (p : SubInstrument M M α) : (semanticsVia ρ₀).evalDist p = p.outcomeMeasure ρ₀ :=
  rfl

end SubInstrument

end Quantum

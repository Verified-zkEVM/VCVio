/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.CountingOracle.Core
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.MeasureTheory.MeasurableSpace.TypeTags
public import ToMathlib.Control.WriterT
public import ToMathlib.Probability.TailSums
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Writer Cost Accounting

This file collects reusable `AddWriterT` facts for pathwise and expected cost reasoning.
It also equips `QueryImpl` with additive writer-cost instrumentation.
-/

@[expose] public section

open OracleSpec

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type*}

section addCost

variable [Monad m]

/-- Instrument an implementation with additive cost accumulation in an `AddWriterT` layer. -/
def withAddCost {ω : Type} [AddMonoid ω]
    (impl : QueryImpl spec m) (costFn : spec.Domain → ω) :
    QueryImpl spec (AddWriterT ω m) :=
  QueryImpl.withCost (spec := spec) (m := m) impl
    (fun t ↦ Multiplicative.ofAdd (costFn t))

@[simp]
lemma withAddCost_apply {ω : Type} [AddMonoid ω]
    (impl : QueryImpl spec m) (costFn : spec.Domain → ω) (t : spec.Domain) :
    impl.withAddCost costFn t =
      (do AddWriterT.addTell (M := m) (costFn t); liftM (impl t)) := by
  simp [withAddCost, AddWriterT.addTell, QueryImpl.withCost]

/-- Cost instrumentation on a left-summand query, with the component response type exposed. -/
lemma withAddCost_apply_inl {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {ω : Type} [AddMonoid ω] (impl : QueryImpl (spec₁ + spec₂) m)
    (costFn : (spec₁ + spec₂).Domain → ω) (t : spec₁.Domain) :
    impl.withAddCost costFn (Sum.inl t) = (do
      AddWriterT.addTell (costFn (Sum.inl t))
      liftM (impl.restrictLeft t)) := by
  rw [withAddCost_apply, restrictLeft_apply]

/-- Cost instrumentation on a right-summand query, with the component response type exposed. -/
lemma withAddCost_apply_inr {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {ω : Type} [AddMonoid ω] (impl : QueryImpl (spec₁ + spec₂) m)
    (costFn : (spec₁ + spec₂).Domain → ω) (t : spec₂.Domain) :
    impl.withAddCost costFn (Sum.inr t) = (do
      AddWriterT.addTell (costFn (Sum.inr t))
      liftM (impl.restrictRight t)) := by
  rw [withAddCost_apply, restrictRight_apply]

/-- Instrument an implementation with unit additive cost for every query. -/
def withUnitCost (impl : QueryImpl spec m) :
    QueryImpl spec (AddWriterT ℕ m) :=
  impl.withAddCost (fun _ ↦ 1)

@[simp]
lemma withUnitCost_apply (impl : QueryImpl spec m) (t : spec.Domain) :
    impl.withUnitCost t =
      (do AddWriterT.addTell (M := m) 1; liftM (impl t)) := by
  simp [withUnitCost]

end addCost

end QueryImpl

namespace AddWriterT

variable {m : Type → Type*} {α β : Type}

section pathwiseCost

variable [MonadAttach m]

/-- Pathwise upper bound for an `AddWriterT` computation: every reachable execution result carries
additive cost at most `w`. -/
def PathwiseCostAtMost {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  ∀ z ∈ support oa.run, Multiplicative.toAdd z.2 ≤ w

/-- Pathwise lower bound for an `AddWriterT` computation: every reachable execution result carries
additive cost at least `w`. -/
def PathwiseCostAtLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  ∀ z ∈ support oa.run, w ≤ Multiplicative.toAdd z.2

/-- Pathwise exactness on support for an `AddWriterT` computation: every reachable execution result
carries exactly the additive cost `w`.

This is the weak extensional notion of pathwise exactness. If `oa.run` has empty support, it holds
vacuously for every `w`. Use [`AddWriterT.PathwiseHasCost`] when the intended meaning is that `oa`
has an exact pathwise cost and admits at least one reachable execution. -/
def PathwiseCostEqOnSupport {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  PathwiseCostAtMost oa w ∧ PathwiseCostAtLeast oa w

@[simp] lemma pathwiseCostEqOnSupport_iff {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) :
    PathwiseCostEqOnSupport oa w ↔ PathwiseCostAtMost oa w ∧ PathwiseCostAtLeast oa w :=
  Iff.rfl

/-- Pathwise exact cost for an `AddWriterT` computation: `oa` has at least one reachable execution,
and every reachable execution result carries exactly the additive cost `w`.

This is the strong semantic notion of exact cost over execution paths.
Unlike [`AddWriterT.HasCost`], it does not require cost to be recoverable
from the final output alone. Unlike
[`AddWriterT.PathwiseCostEqOnSupport`], it is not vacuous on computations with empty support. -/
def PathwiseHasCost {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) : Prop :=
  (support oa.run).Nonempty ∧ PathwiseCostEqOnSupport oa w

@[simp] lemma pathwiseHasCost_iff {ω : Type} [AddMonoid ω] [Preorder ω]
    (oa : AddWriterT ω m α) (w : ω) :
    PathwiseHasCost oa w ↔
      (support oa.run).Nonempty ∧ PathwiseCostEqOnSupport oa w :=
  Iff.rfl

lemma PathwiseHasCost.nonempty {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    (support oa.run).Nonempty :=
  h.1

lemma PathwiseCostEqOnSupport.atMost {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostAtMost oa w :=
  h.1

lemma PathwiseCostEqOnSupport.atLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostAtLeast oa w :=
  h.2

lemma PathwiseHasCost.eqOnSupport {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostEqOnSupport oa w :=
  h.2

lemma PathwiseHasCost.atMost {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostAtMost oa w :=
  h.2.1

lemma PathwiseHasCost.atLeast {ω : Type} [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} (h : PathwiseHasCost oa w) :
    PathwiseCostAtLeast oa w :=
  h.2.2

lemma PathwiseHasCost.unique {ω : Type} [AddMonoid ω] [PartialOrder ω]
    {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h₁ : PathwiseHasCost oa w₁) (h₂ : PathwiseHasCost oa w₂) :
    w₁ = w₂ := by
  obtain ⟨z, hz⟩ := h₁.nonempty
  exact le_antisymm ((h₁.atLeast z hz).trans (h₂.atMost z hz))
    ((h₂.atLeast z hz).trans (h₁.atMost z hz))

variable [Monad m] [ExactMonadAttach m]

lemma pathwiseCostAtMost_of_hasCost {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : AddWriterT ω m α} {w b : ω}
    (h : AddWriterT.HasCost oa w) (hwb : w ≤ b) :
    PathwiseCostAtMost oa b := by
  intro z hz
  have hzCost : Multiplicative.toAdd z.2 ∈ support oa.costs := by
    rw [AddWriterT.costs_def, support_map]
    exact ⟨z, hz, rfl⟩
  rw [h, support_map] at hzCost
  obtain ⟨_, _, hzCost⟩ := hzCost
  simpa [hzCost] using hwb

lemma pathwiseCostAtLeast_of_hasCost {ω : Type} [AddMonoid ω] [Preorder ω] [LawfulMonad m]
    {oa : AddWriterT ω m α} {w b : ω}
    (h : AddWriterT.HasCost oa w) (hbw : b ≤ w) :
    PathwiseCostAtLeast oa b := by
  intro z hz
  have hzCost : Multiplicative.toAdd z.2 ∈ support oa.costs := by
    rw [AddWriterT.costs_def, support_map]
    exact ⟨z, hz, rfl⟩
  rw [h, support_map] at hzCost
  obtain ⟨_, _, hzCost⟩ := hzCost
  simpa [hzCost] using hbw

end pathwiseCost

section expectedCost

variable {ω : Type} [Monad m] [EvalDistSemantics m]

/-- An event depending only on cost can observe either the cost marginal or the joint run.
No measurable space on the discarded outputs is required. -/
lemma prEvent_costs [LawfulMonad m] (oa : AddWriterT ω m α) (p : ω → Prop) :
    Pr{let c ← oa.costs}[p c] = Pr{let z ← oa.run}[p (Multiplicative.toAdd z.2)] := by
  simp only [costs_def, bind_map_left]

variable [MeasurableSpace ω]

/-- The expected additive cost of an `AddWriterT` computation, obtained by taking the expectation
of its cost marginal.

This is a Lebesgue integral against the base monad's successful-output measure. If the underlying
computation can fail, the missing mass contributes `0`. -/
noncomputable def expectedCost
    (oa : AddWriterT ω m α) (val : ω → ENNReal) : ENNReal :=
  ∫⁻ w, val w ∂𝒟[oa.costs]

/-- Markov's inequality for the cost marginal, without a measurable space on discarded outputs. -/
lemma prEvent_cost_gt_mul_le_expectedCost [LawfulMonad m] [LawfulEvalDistSemantics m]
    (oa : AddWriterT ω m α) {val : ω → ENNReal} (hval : Measurable val) (t : ENNReal) :
    Pr{let c ← oa.costs}[t < val c] * t ≤ expectedCost oa val := by
  rw [prEvent_eq_evalDist _ _
    (measurableSet_setOfPred.mp (measurableSet_lt measurable_const hval))]
  calc
    𝒟[oa.costs] {c | t < val c} * t = t * 𝒟[oa.costs] {c | t < val c} := mul_comm _ _
    _ ≤ t * 𝒟[oa.costs] {c | t ≤ val c} := by
      gcongr
      exact fun hc ↦ hc.le
    _ ≤ expectedCost oa val := MeasureTheory.mul_meas_ge_le_lintegral hval t

/-- Markov's inequality for valued cost, in division form. -/
lemma prEvent_cost_gt_le_expectedCost_div [LawfulMonad m] [LawfulEvalDistSemantics m]
    (oa : AddWriterT ω m α) {val : ω → ENNReal} (hval : Measurable val)
    {t : ENNReal} (ht : 0 < t) (ht' : t ≠ ⊤) :
    Pr{let c ← oa.costs}[t < val c] ≤ expectedCost oa val / t :=
  (ENNReal.le_div_iff_mul_le (.inl ht.ne') (.inl ht')).mpr
    (prEvent_cost_gt_mul_le_expectedCost oa hval t)

/-- Expected cost integrates the cost projection of the joint output/writer measure. -/
lemma expectedCost_eq_lintegral_run
    [LawfulMonad m] [LawfulEvalDistSemantics m] [MeasurableSpace α]
    (oa : AddWriterT ω m α) (val : ω → ENNReal) (hval : Measurable val) :
    expectedCost oa val = ∫⁻ z, val (Multiplicative.toAdd z.2) ∂𝒟[oa.run] := by
  rw [expectedCost, AddWriterT.costs_def]
  exact lintegral_evalDist_map oa.run
    (f := fun z ↦ Multiplicative.toAdd z.2)
    (Multiplicative.measurable_toAdd.comp measurable_snd) hval

/-- A measurable family of cost measures has a measurable expected valuation. Such a family
is exactly the data needed by `evalDistKernel` on the cost marginal. -/
@[fun_prop]
lemma measurable_expectedCost {ρ : Type*} [MeasurableSpace ρ]
    (oa : ρ → AddWriterT ω m α) {val : ω → ENNReal}
    (hoa : Measurable fun r ↦ 𝒟[(oa r).costs]) (hval : Measurable val) :
    Measurable fun r ↦ expectedCost (oa r) val :=
  (MeasureTheory.Measure.measurable_lintegral hval).comp hoa

/-- Convenience specialization of [`AddWriterT.expectedCost`] to natural-valued additive costs. -/
noncomputable abbrev expectedCostNat
    (oa : AddWriterT ℕ m α) : ENNReal :=
  expectedCost oa (fun n ↦ ↑n)

/-- The successful mass of the cost marginal, under its chosen measurable space. -/
noncomputable def costMass (oa : AddWriterT ω m α) : ENNReal :=
  𝒟[oa.costs] Set.univ

/-- The mass assigned to a particular cost, under the chosen measurable space. -/
noncomputable def costMassAt (oa : AddWriterT ω m α) (w : ω) : ENNReal :=
  𝒟[oa.costs] {w}

/-- Expected cost is monotone in its valuation. -/
@[gcongr]
theorem expectedCost_mono (oa : AddWriterT ω m α) {val₁ val₂ : ω → ENNReal}
    (h : ∀ w, val₁ w ≤ val₂ w) :
    expectedCost oa val₁ ≤ expectedCost oa val₂ := by
  exact MeasureTheory.lintegral_mono h

/-- A zero valuation has zero expected cost. -/
@[simp]
theorem expectedCost_zero (oa : AddWriterT ω m α) :
    expectedCost oa (fun _ => 0) = 0 := by
  simp [expectedCost]

/-- The expectation of a constant is that constant times the successful mass. -/
@[simp]
theorem expectedCost_const (oa : AddWriterT ω m α) (c : ENNReal) :
    expectedCost oa (fun _ => c) = c * costMass oa := by
  simp [expectedCost, costMass, MeasureTheory.lintegral_const]

/-- A pure writer computation has its initial zero cost in expectation. -/
@[simp]
theorem expectedCost_pure [AddMonoid ω] [LawfulMonad m] [LawfulEvalDistSemantics m]
    (x : α) (val : ω → ENNReal) (hval : Measurable val) :
    expectedCost (pure x : AddWriterT ω m α) val = val 0 := by
  rw [expectedCost, costs_pure, evalDist_pure]
  exact MeasureTheory.lintegral_dirac' _ hval

/-- The cost of `oa` is at most `w` almost everywhere under its denotational semantics. -/
noncomputable def AECostAtMost [Preorder ω] (oa : AddWriterT ω m α) (w : ω) : Prop :=
  ∀ᵐ c ∂𝒟[oa.costs], c ≤ w

/-- The cost of `oa` is at least `w` almost everywhere under its denotational semantics. -/
noncomputable def AECostAtLeast [Preorder ω] (oa : AddWriterT ω m α) (w : ω) : Prop :=
  ∀ᵐ c ∂𝒟[oa.costs], w ≤ c

/-- An almost-everywhere bound on the valued cost bounds its expectation. -/
theorem expectedCost_le_of_ae_le
    (oa : AddWriterT ω m α) {val : ω → ENNReal} {c : ENNReal}
    (h : ∀ᵐ w ∂𝒟[oa.costs], val w ≤ c) :
    expectedCost oa val ≤ c := by
  calc
    expectedCost oa val ≤ ∫⁻ _w : ω, c ∂𝒟[oa.costs] :=
      MeasureTheory.lintegral_mono_ae h
    _ = c * 𝒟[oa.costs] Set.univ := MeasureTheory.lintegral_const _
    _ ≤ c * 1 :=
      mul_le_mul_of_nonneg_left (evalDist_apply_univ_le_one oa.costs) zero_le
    _ = c := mul_one _

/-- The expected cost is its usual mass-weighted sum on a countable cost space. -/
theorem expectedCost_eq_tsum [Countable ω] [MeasurableSingletonClass ω]
    (oa : AddWriterT ω m α) (val : ω → ENNReal) :
    expectedCost oa val = ∑' w : ω, costMassAt oa w * val w := by
  simp only [expectedCost, costMassAt]
  rw [MeasureTheory.lintegral_countable']
  exact tsum_congr fun w ↦ mul_comm _ _

/-- An almost-everywhere cost bound bounds the expected value of every monotone valuation. -/
theorem expectedCost_le_of_aeCostAtMost [Preorder ω]
    (oa : AddWriterT ω m α) {w : ω} {val : ω → ENNReal}
    (h : AECostAtMost oa w) (hval : Monotone val) :
    expectedCost oa val ≤ val w :=
  expectedCost_le_of_ae_le oa (h.mono fun _c hc ↦ hval hc)

/-- A lower almost-everywhere cost bound gives a lower expected-cost bound for a lossless
computation. -/
theorem le_expectedCost_of_aeCostAtLeast [Preorder ω]
    (oa : AddWriterT ω m α) {w : ω} {val : ω → ENNReal}
    (h : AECostAtLeast oa w) (hval : Monotone val)
    (hmass : costMass oa = 1) :
    val w ≤ expectedCost oa val := by
  simp only [AECostAtLeast] at h
  simp only [costMass] at hmass
  calc
    val w = ∫⁻ _c : ω, val w ∂𝒟[oa.costs] := by
      rw [MeasureTheory.lintegral_const, hmass, mul_one]
    _ ≤ expectedCost oa val :=
      MeasureTheory.lintegral_mono_ae (h.mono fun c hc ↦ hval hc)

section tailBounds

/-- Tail-sum formula for the natural-valued expected cost of an `AddWriterT` computation:

`E[cost] = ∑ i, Pr[i < cost]`.

This specializes `MeasureTheory.lintegral_coe_nat_eq_tsum` to the writer-cost marginal. -/
lemma expectedCostNat_eq_tsum_tail_probs
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    (oa : AddWriterT ℕ m α) :
    expectedCostNat oa = ∑' i : ℕ, Pr{let c ← oa.costs}[i < c] := by
  unfold expectedCostNat expectedCost
  refine (MeasureTheory.lintegral_coe_nat_eq_tsum
    (f := fun n : ℕ ↦ n) measurable_id 𝒟[oa.costs]).trans ?_
  refine tsum_congr fun i ↦ ?_
  exact (prEvent_eq_evalDist_of_discrete oa.costs (fun c ↦ i < c)).symm

/-- Tail domination bounds the expected natural-valued writer cost.

If the tail probability `Pr[i < cost]` is bounded by `a i` for every `i`, then
`E[cost] ≤ ∑ i, a i`. -/
lemma expectedCostNat_le_tsum_of_tail_probs_le
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    (oa : AddWriterT ℕ m α) {a : ℕ → ENNReal}
    (h : ∀ i : ℕ, Pr{let c ← oa.costs}[i < c] ≤ a i) :
    expectedCostNat oa ≤ ∑' i : ℕ, a i :=
  (expectedCostNat_eq_tsum_tail_probs oa).trans_le (ENNReal.tsum_le_tsum h)

end tailBounds

/-- Finite tail-sum formula for natural-valued writer cost under a pathwise upper bound.

If every execution path of `oa` incurs cost at most `n`, then the tail probabilities vanish above
`n`, so the infinite tail sum truncates to `Finset.range n`. -/
lemma expectedCostNat_eq_sum_tail_probs_of_pathwiseCostAtMost
    [MonadAttach m] [ExactMonadAttach m]
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : PathwiseCostAtMost oa n) :
    expectedCostNat oa = ∑ i ∈ Finset.range n, Pr{let c ← oa.costs}[i < c] := by
  rw [expectedCostNat_eq_tsum_tail_probs]
  symm
  rw [tsum_eq_sum (s := Finset.range n) (fun b hb ↦ ?_)]
  have hnb : n ≤ b := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hb)
  rw [prEvent_eq_evalDist_of_discrete]
  apply evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete
  intro c hc
  rw [AddWriterT.costs_def, support_map] at hc
  rcases hc with ⟨z, hz, rfl⟩
  exact not_lt_of_ge (le_trans (h z hz) hnb)

/-- A measurable valuation bounded on reachable costs bounds its expectation. -/
lemma expectedCost_le_of_support_bound
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (oa : AddWriterT ω m α) (val : ω → ENNReal) (c : ENNReal)
    (hval : Measurable val) (h : ∀ w ∈ support oa.costs, val w ≤ c) :
    expectedCost oa val ≤ c :=
  expectedCost_le_of_ae_le oa
    (evalDist.ae_of_forall_mem_support oa.costs _
      (measurableSet_le hval measurable_const) h)

lemma expectedCost_le_of_pathwiseCostAtMost [AddMonoid ω]
    [MonadAttach m] [ExactMonadAttach m]
    [LawfulMonad m] [LawfulEvalDistSemantics m] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω} {val : ω → ENNReal}
    (h : PathwiseCostAtMost oa w) (hval : Monotone val) (hvalMeas : Measurable val) :
    expectedCost oa val ≤ val w := by
  refine expectedCost_le_of_support_bound oa val (val w) hvalMeas fun c hc ↦ ?_
  rw [AddWriterT.costs_def, support_map] at hc
  rcases hc with ⟨z, hz, rfl⟩
  exact hval (h z hz)

lemma le_expectedCost_of_pathwiseCostAtLeast [AddMonoid ω] [Preorder ω]
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [ExactMonadAttach m]
    {oa : AddWriterT ω m α} [MeasureTheory.IsProbabilityMeasure 𝒟[oa.costs]]
    {w : ω} {val : ω → ENNReal}
    (h : PathwiseCostAtLeast oa w) (hval : Monotone val) (hvalMeas : Measurable val) :
    val w ≤ expectedCost oa val := by
  have hae : ∀ᵐ c ∂𝒟[oa.costs], val w ≤ val c := by
    apply evalDist.ae_of_forall_mem_support _ _
      (measurableSet_le measurable_const hvalMeas)
    intro c hc
    rw [AddWriterT.costs_def, support_map] at hc
    obtain ⟨z, hz, rfl⟩ := hc
    exact hval (h z hz)
  calc
    val w = ∫⁻ _c : ω, val w ∂𝒟[oa.costs] := by
      rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
    _ ≤ expectedCost oa val := MeasureTheory.lintegral_mono_ae hae

/-- If cost is a measurable function of the output, its expectation is the integral of that
function over the output measure. -/
lemma expectedCost_eq_lintegral_outputs_of_costsAs
    [LawfulMonad m] [LawfulEvalDistSemantics m] [MeasurableSpace α]
    {oa : AddWriterT ω m α} {f : α → ω} {val : ω → ENNReal}
    (h : oa.CostsAs f) (hf : Measurable f) (hval : Measurable val) :
    expectedCost oa val = ∫⁻ a, val (f a) ∂𝒟[oa.outputs] := by
  rw [expectedCost, h, lintegral_evalDist_map oa.outputs hf hval]

/-- On a countable output space, output-indexed expected cost is a mass-weighted sum. -/
lemma expectedCost_eq_tsum_outputs_of_costsAs
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    {oa : AddWriterT ω m α} {f : α → ω} {val : ω → ENNReal}
    (h : oa.CostsAs f) (hf : Measurable f) (hval : Measurable val) :
    expectedCost oa val = ∑' a : α, 𝒟[oa.outputs] {a} * val (f a) := by
  rw [expectedCost_eq_lintegral_outputs_of_costsAs h hf hval,
    MeasureTheory.lintegral_countable']
  exact tsum_congr fun a ↦ mul_comm _ _

/-- A measurable pathwise upper bound holds almost everywhere under lawful measure semantics. -/
lemma aeCostAtMost_of_pathwiseCostAtMost
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [ExactMonadAttach m] [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω}
    (h : PathwiseCostAtMost oa w) (hmeas : MeasurableSet {c | c ≤ w}) :
    AECostAtMost oa w := by
  apply evalDist.ae_of_forall_mem_support oa.costs _ hmeas
  intro c hc
  rw [AddWriterT.costs_def, support_map] at hc
  obtain ⟨z, hz, rfl⟩ := hc
  exact h z hz

/-- A measurable pathwise lower bound holds almost everywhere under lawful measure semantics. -/
lemma aeCostAtLeast_of_pathwiseCostAtLeast
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [ExactMonadAttach m] [AddMonoid ω] [Preorder ω]
    {oa : AddWriterT ω m α} {w : ω}
    (h : PathwiseCostAtLeast oa w) (hmeas : MeasurableSet {c | w ≤ c}) :
    AECostAtLeast oa w := by
  apply evalDist.ae_of_forall_mem_support oa.costs _ hmeas
  intro c hc
  rw [AddWriterT.costs_def, support_map] at hc
  obtain ⟨z, hz, rfl⟩ := hc
  exact h z hz

/-- A measurable valuation constant on reachable costs integrates to its value times successful
mass. This includes computations with failure. -/
lemma expectedCost_eq_mul_costMass_of_support
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (oa : AddWriterT ω m α) {w : ω} (val : ω → ENNReal) (hval : Measurable val)
    (h : ∀ c ∈ support oa.costs, val c = val w) :
    expectedCost oa val = val w * costMass oa := by
  have hae := evalDist.ae_of_forall_mem_support oa.costs _
    (measurableSet_eq_fun hval measurable_const) h
  exact (MeasureTheory.lintegral_congr_ae hae).trans (MeasureTheory.lintegral_const _)

/-- Constant cost integrates to its valuation times successful mass. Structural constant cost
requires neither attachment nor a measurable space on the discarded output. -/
lemma expectedCost_eq_mul_costMass_of_hasCost
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    (oa : AddWriterT ω m α) {w : ω} (val : ω → ENNReal) (hval : Measurable val)
    (h : HasCost oa w) : expectedCost oa val = val w * costMass oa := by
  have hmap : (fun _ : ω ↦ w) <$> oa.costs = oa.costs := by
    rw [h, Functor.map_map]
  rw [expectedCost, ← hmap, lintegral_evalDist_map oa.costs measurable_const hval,
    MeasureTheory.lintegral_const]
  rfl

/-- A lossless computation with constant cost has that cost's expected valuation. -/
lemma expectedCost_eq_of_hasCost
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    (oa : AddWriterT ω m α) [MeasureTheory.IsProbabilityMeasure 𝒟[oa.costs]]
    {w : ω} (val : ω → ENNReal) (hval : Measurable val) (h : HasCost oa w) :
    expectedCost oa val = val w := by
  simpa only [costMass, MeasureTheory.measure_univ, mul_one] using
    expectedCost_eq_mul_costMass_of_hasCost oa val hval h

/-- A lossless computation with pathwise exact cost has that cost's expected valuation. -/
lemma expectedCost_eq_of_pathwiseCostEqOnSupport
    [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MonadAttach m] [ExactMonadAttach m] [AddMonoid ω] [PartialOrder ω]
    (oa : AddWriterT ω m α) [MeasureTheory.IsProbabilityMeasure 𝒟[oa.costs]]
    {w : ω} (val : ω → ENNReal) (hval : Measurable val)
    (h : PathwiseCostEqOnSupport oa w) :
    expectedCost oa val = val w := by
  have hc : expectedCost oa val = val w * costMass oa := by
    apply expectedCost_eq_mul_costMass_of_support oa val hval
    intro c hc
    rw [AddWriterT.costs_def, support_map] at hc
    obtain ⟨z, hz, rfl⟩ := hc
    exact congrArg val (le_antisymm (h.atMost z hz) (h.atLeast z hz))
  simpa only [costMass, MeasureTheory.measure_univ, mul_one] using hc

end expectedCost

section weightedPathwiseBounds

variable [MonadAttach m] {ω : Type} [AddCommMonoid ω] [PartialOrder ω]

@[gcongr]
lemma pathwiseCostAtMost_mono {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h : PathwiseCostAtMost oa w₁) (hw : w₁ ≤ w₂) :
    PathwiseCostAtMost oa w₂ :=
  fun z hz ↦ (h z hz).trans hw

lemma pathwiseCostAtLeast_mono {oa : AddWriterT ω m α} {w₁ w₂ : ω}
    (h : PathwiseCostAtLeast oa w₂) (hw : w₁ ≤ w₂) :
    PathwiseCostAtLeast oa w₁ :=
  fun z hz ↦ hw.trans (h z hz)

variable [Monad m] [ExactMonadAttach m]

lemma pathwiseCostAtMost_pure [LawfulMonad m] (x : α) :
    PathwiseCostAtMost (pure x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtMost]

lemma pathwiseCostAtLeast_pure [LawfulMonad m] (x : α) :
    PathwiseCostAtLeast (pure x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtLeast]

lemma pathwiseCostEqOnSupport_pure [LawfulMonad m] (x : α) :
    PathwiseCostEqOnSupport (pure x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_pure (m := m) (ω := ω) x,
    pathwiseCostAtLeast_pure (m := m) (ω := ω) x⟩

lemma pathwiseHasCost_pure [LawfulMonad m] (x : α) :
    PathwiseHasCost (pure x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_pure (m := m) (ω := ω) x,
    pathwiseCostAtLeast_pure (m := m) (ω := ω) x⟩⟩
  rw [WriterT.run_pure, support_pure]
  exact ⟨(x, 1), by simp⟩

lemma pathwiseCostAtMost_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostAtMost (monadLift x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtMost]

lemma pathwiseCostAtLeast_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostAtLeast (monadLift x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtLeast]

lemma pathwiseCostEqOnSupport_monadLift [LawfulMonad m] (x : m α) :
    PathwiseCostEqOnSupport (monadLift x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_monadLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_monadLift (m := m) (ω := ω) x⟩

lemma pathwiseHasCost_monadLift_of_supportNonempty [LawfulMonad m] (x : m α)
    (hx : (support x).Nonempty) :
    PathwiseHasCost (monadLift x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_monadLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_monadLift (m := m) (ω := ω) x⟩⟩
  rcases hx with ⟨a, ha⟩
  refine ⟨(a, 1), ?_⟩
  rw [WriterT.run_monadLift, support_map]
  exact ⟨a, ha, rfl⟩

lemma pathwiseCostAtMost_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostAtMost (liftM x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtMost]

lemma pathwiseCostAtLeast_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostAtLeast (liftM x : AddWriterT ω m α) 0 := by
  simp [PathwiseCostAtLeast]

lemma pathwiseCostEqOnSupport_liftM [LawfulMonad m] (x : m α) :
    PathwiseCostEqOnSupport (liftM x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_liftM (m := m) (ω := ω) x,
    pathwiseCostAtLeast_liftM (m := m) (ω := ω) x⟩

lemma pathwiseHasCost_liftM_of_supportNonempty [LawfulMonad m] (x : m α)
    (hx : (support x).Nonempty) :
    PathwiseHasCost (liftM x : AddWriterT ω m α) 0 := by
  refine ⟨?_, ⟨pathwiseCostAtMost_liftM (m := m) (ω := ω) x,
    pathwiseCostAtLeast_liftM (m := m) (ω := ω) x⟩⟩
  rcases hx with ⟨a, ha⟩
  refine ⟨(a, 1), ?_⟩
  rw [WriterT.liftM_def, WriterT.run_mk, support_map]
  exact ⟨a, ha, rfl⟩

lemma pathwiseCostAtMost_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m] (x : ProbComp α) :
    PathwiseCostAtMost (monadLift x : AddWriterT ω m α) 0 :=
  pathwiseCostAtMost_monadLift (m := m) (x := (liftM x : m α))

lemma pathwiseCostAtLeast_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m] (x : ProbComp α) :
    PathwiseCostAtLeast (monadLift x : AddWriterT ω m α) 0 :=
  pathwiseCostAtLeast_monadLift (m := m) (x := (liftM x : m α))

lemma pathwiseCostEqOnSupport_probCompLift [LawfulMonad m] [MonadLiftT ProbComp m]
    (x : ProbComp α) :
    PathwiseCostEqOnSupport (monadLift x : AddWriterT ω m α) 0 :=
  ⟨pathwiseCostAtMost_probCompLift (m := m) (ω := ω) x,
    pathwiseCostAtLeast_probCompLift (m := m) (ω := ω) x⟩

lemma pathwiseHasCost_probCompLift_of_supportNonempty [LawfulMonad m] [MonadLiftT ProbComp m]
    (x : ProbComp α) (hx : (support (liftM x : m α)).Nonempty) :
    PathwiseHasCost (monadLift x : AddWriterT ω m α) 0 :=
  pathwiseHasCost_monadLift_of_supportNonempty (m := m) (ω := ω) (x := (liftM x : m α)) hx

lemma pathwiseCostAtMost_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostAtMost (AddWriterT.addTell (M := m) w) w := by
  simp [PathwiseCostAtMost]

lemma pathwiseCostAtLeast_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostAtLeast (AddWriterT.addTell (M := m) w) w := by
  simp [PathwiseCostAtLeast]

lemma pathwiseCostEqOnSupport_addTell [LawfulMonad m] (w : ω) :
    PathwiseCostEqOnSupport (AddWriterT.addTell (M := m) w) w :=
  ⟨pathwiseCostAtMost_addTell (m := m) w, pathwiseCostAtLeast_addTell (m := m) w⟩

lemma pathwiseHasCost_addTell [LawfulMonad m] (w : ω) :
    PathwiseHasCost (AddWriterT.addTell (M := m) w) w := by
  refine ⟨?_, ⟨pathwiseCostAtMost_addTell (m := m) w, pathwiseCostAtLeast_addTell (m := m) w⟩⟩
  rw [AddWriterT.run_addTell, support_pure]
  exact ⟨(PUnit.unit, Multiplicative.ofAdd w), by simp⟩

lemma pathwiseCostAtMost_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostAtMost oa w) :
    PathwiseCostAtMost (f <$> oa) w := by
  intro z hz
  rw [WriterT.run_map, support_map] at hz
  rcases hz with ⟨z', hz', rfl⟩
  exact h z' hz'

lemma pathwiseCostAtLeast_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostAtLeast oa w) :
    PathwiseCostAtLeast (f <$> oa) w := by
  intro z hz
  rw [WriterT.run_map, support_map] at hz
  rcases hz with ⟨z', hz', rfl⟩
  exact h z' hz'

lemma pathwiseCostEqOnSupport_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseCostEqOnSupport oa w) :
    PathwiseCostEqOnSupport (f <$> oa) w :=
  ⟨pathwiseCostAtMost_map f h.atMost, pathwiseCostAtLeast_map f h.atLeast⟩

lemma pathwiseHasCost_map [LawfulMonad m] {oa : AddWriterT ω m α} {w : ω}
    (f : α → β) (h : PathwiseHasCost oa w) :
    PathwiseHasCost (f <$> oa) w := by
  refine ⟨?_, ⟨pathwiseCostAtMost_map f h.atMost, pathwiseCostAtLeast_map f h.atLeast⟩⟩
  rcases h.nonempty with ⟨z, hz⟩
  refine ⟨Prod.map f id z, ?_⟩
  rw [WriterT.run_map, support_map]
  exact ⟨z, hz, rfl⟩

lemma pathwiseCostAtMost_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostAtMost oa w₁) (h₂ : ∀ a, PathwiseCostAtMost (f a) w₂) :
    PathwiseCostAtMost (oa >>= f) (w₁ + w₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  rcases (mem_support_bind_iff
    (mx := oa.run)
    (my := fun aw ↦ Prod.map id (aw.2 * ·) <$> (f aw.1).run)
    (y := z)).1 hz with ⟨⟨a, wa⟩, haw, hz⟩
  rw [support_map] at hz
  rcases hz with ⟨⟨b, wb⟩, hbw, rfl⟩
  simpa using add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)

lemma pathwiseCostAtLeast_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostAtLeast oa w₁) (h₂ : ∀ a, PathwiseCostAtLeast (f a) w₂) :
    PathwiseCostAtLeast (oa >>= f) (w₁ + w₂) := by
  intro z hz
  rw [WriterT.run_bind] at hz
  rcases (mem_support_bind_iff
    (mx := oa.run)
    (my := fun aw ↦ Prod.map id (aw.2 * ·) <$> (f aw.1).run)
    (y := z)).1 hz with ⟨⟨a, wa⟩, haw, hz⟩
  rw [support_map] at hz
  rcases hz with ⟨⟨b, wb⟩, hbw, rfl⟩
  simpa using add_le_add (h₁ (a, wa) haw) (h₂ a (b, wb) hbw)

lemma pathwiseCostEqOnSupport_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseCostEqOnSupport oa w₁) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) w₂) :
    PathwiseCostEqOnSupport (oa >>= f) (w₁ + w₂) :=
  ⟨pathwiseCostAtMost_bind h₁.atMost (fun a ↦ (h₂ a).atMost),
    pathwiseCostAtLeast_bind h₁.atLeast (fun a ↦ (h₂ a).atLeast)⟩

lemma pathwiseHasCost_bind [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w₁ w₂ : ω}
    (h₁ : PathwiseHasCost oa w₁) (h₂ : ∀ a, PathwiseHasCost (f a) w₂) :
    PathwiseHasCost (oa >>= f) (w₁ + w₂) := by
  refine ⟨?_, ⟨pathwiseCostAtMost_bind h₁.atMost (fun a ↦ (h₂ a).atMost),
    pathwiseCostAtLeast_bind h₁.atLeast (fun a ↦ (h₂ a).atLeast)⟩⟩
  rcases h₁.nonempty with ⟨⟨a, wa⟩, haw⟩
  rcases (h₂ a).nonempty with ⟨⟨b, wb⟩, hbw⟩
  refine ⟨(b, wa * wb), ?_⟩
  rw [WriterT.run_bind, mem_support_bind_iff]
  refine ⟨(a, wa), haw, ?_⟩
  rw [support_map]
  exact ⟨(b, wb), hbw, rfl⟩

lemma pathwiseHasCost_bind_zero_left [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseHasCost oa 0) (h₂ : ∀ a, PathwiseHasCost (f a) w) :
    PathwiseHasCost (oa >>= f) w := by
  simpa [zero_add] using pathwiseHasCost_bind (w₁ := 0) (w₂ := w) h₁ h₂

lemma pathwiseHasCost_bind_zero_right [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseHasCost oa w) (h₂ : ∀ a, PathwiseHasCost (f a) 0) :
    PathwiseHasCost (oa >>= f) w := by
  simpa [add_zero] using pathwiseHasCost_bind (w₁ := w) (w₂ := 0) h₁ h₂

lemma pathwiseCostEqOnSupport_bind_zero_left [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseCostEqOnSupport oa 0) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) w) :
    PathwiseCostEqOnSupport (oa >>= f) w := by
  simpa [zero_add] using pathwiseCostEqOnSupport_bind (w₁ := 0) (w₂ := w) h₁ h₂

lemma pathwiseCostEqOnSupport_bind_zero_right [LawfulMonad m] [IsOrderedAddMonoid ω]
    {oa : AddWriterT ω m α} {f : α → AddWriterT ω m β} {w : ω}
    (h₁ : PathwiseCostEqOnSupport oa w) (h₂ : ∀ a, PathwiseCostEqOnSupport (f a) 0) :
    PathwiseCostEqOnSupport (oa >>= f) w := by
  simpa [add_zero] using pathwiseCostEqOnSupport_bind (w₁ := w) (w₂ := 0) h₁ h₂

lemma pathwiseCostAtMost_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseCostAtMost (f i) k) :
    PathwiseCostAtMost (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      have hf : f = (Fin.elim0 : Fin 0 → AddWriterT ω m α) := funext fun i => Fin.elim0 i
      subst f
      rw [Fin.mOfFn, zero_nsmul]
      exact pathwiseCostAtMost_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α))
  | succ n ih =>
      simp only [Fin.mOfFn, succ_nsmul']
      simpa [add_comm] using
        (pathwiseCostAtMost_bind (w₁ := k) (w₂ := n • k)
          (by simpa using h 0)
          (fun a ↦ pathwiseCostAtMost_map (Fin.cons a) (ih (fun i ↦ h i.succ))))

lemma pathwiseCostAtLeast_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseCostAtLeast (f i) k) :
    PathwiseCostAtLeast (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      have hf : f = (Fin.elim0 : Fin 0 → AddWriterT ω m α) := funext fun i => Fin.elim0 i
      subst f
      rw [Fin.mOfFn, zero_nsmul]
      exact pathwiseCostAtLeast_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α))
  | succ n ih =>
      simp only [Fin.mOfFn, succ_nsmul']
      simpa [add_comm] using
        (pathwiseCostAtLeast_bind (w₁ := k) (w₂ := n • k)
          (by simpa using h 0)
          (fun a ↦ pathwiseCostAtLeast_map (Fin.cons a) (ih (fun i ↦ h i.succ))))

lemma pathwiseHasCost_fin_mOfFn [LawfulMonad m] [IsOrderedAddMonoid ω] {n : ℕ} {k : ω}
    {f : Fin n → AddWriterT ω m α} (h : ∀ i, PathwiseHasCost (f i) k) :
    PathwiseHasCost (Fin.mOfFn n f) (n • k) := by
  induction n with
  | zero =>
      simpa [Fin.mOfFn, zero_nsmul] using
        (pathwiseHasCost_pure (m := m) (ω := ω) (x := (Fin.elim0 : Fin 0 → α)))
  | succ n ih =>
      let consA : α → (Fin n → α) → Fin n.succ → α :=
        fun a ↦ @Fin.cons n (fun _ : Fin n.succ ↦ α) a
      simpa [Fin.mOfFn, succ_nsmul', add_comm, consA] using
        pathwiseHasCost_bind (m := m) (ω := ω) (w₁ := k) (w₂ := n • k) (h 0)
          (fun a ↦ pathwiseHasCost_map (f := consA a) (ih (fun i ↦ h i.succ)))

end weightedPathwiseBounds

section unitCostBounds

variable [MonadAttach m]

/-- Pathwise upper bound for a unit-cost `AddWriterT` computation. -/
def QueryBoundedAboveBy (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostAtMost oa n

/-- Pathwise lower bound for a unit-cost `AddWriterT` computation. -/
def QueryBoundedBelowBy (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostAtLeast oa n

@[gcongr]
lemma queryBoundedAboveBy_mono {oa : AddWriterT ℕ m α} {n₁ n₂ : ℕ}
    (h : QueryBoundedAboveBy oa n₁) (hn : n₁ ≤ n₂) :
    QueryBoundedAboveBy oa n₂ :=
  pathwiseCostAtMost_mono h hn

lemma queryBoundedBelowBy_mono {oa : AddWriterT ℕ m α} {n₁ n₂ : ℕ}
    (h : QueryBoundedBelowBy oa n₂) (hn : n₁ ≤ n₂) :
    QueryBoundedBelowBy oa n₁ :=
  pathwiseCostAtLeast_mono h hn

/-- Pathwise exact cost for a unit-cost `AddWriterT` computation: every reachable execution
carries exactly `n` unit queries. -/
def QueryCostExactly (oa : AddWriterT ℕ m α) (n : ℕ) : Prop :=
  PathwiseCostEqOnSupport oa n

lemma QueryCostExactly.toAbove {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryCostExactly oa n) : QueryBoundedAboveBy oa n := h.atMost

lemma QueryCostExactly.toBelow {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryCostExactly oa n) : QueryBoundedBelowBy oa n := h.atLeast

variable [Monad m] [ExactMonadAttach m]

lemma queryBoundedAboveBy_pure [LawfulMonad m] (x : α) :
    QueryBoundedAboveBy (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtMost_pure x

lemma queryBoundedBelowBy_pure [LawfulMonad m] (x : α) :
    QueryBoundedBelowBy (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtLeast_pure x

lemma queryBoundedAboveBy_monadLift [LawfulMonad m] (x : m α) :
    QueryBoundedAboveBy (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtMost_monadLift x

lemma queryBoundedBelowBy_monadLift [LawfulMonad m] (x : m α) :
    QueryBoundedBelowBy (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostAtLeast_monadLift x

lemma queryBoundedAboveBy_addTell [LawfulMonad m] (w : ℕ) :
    QueryBoundedAboveBy (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostAtMost_addTell w

lemma queryBoundedBelowBy_addTell [LawfulMonad m] (w : ℕ) :
    QueryBoundedBelowBy (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostAtLeast_addTell w

lemma queryBoundedAboveBy_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ} (f : α → β)
    (h : QueryBoundedAboveBy oa n) :
    QueryBoundedAboveBy (f <$> oa) n :=
  pathwiseCostAtMost_map f h

lemma queryBoundedBelowBy_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ} (f : α → β)
    (h : QueryBoundedBelowBy oa n) :
    QueryBoundedBelowBy (f <$> oa) n :=
  pathwiseCostAtLeast_map f h

lemma queryBoundedAboveBy_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryBoundedAboveBy oa n₁) (h₂ : ∀ a, QueryBoundedAboveBy (f a) n₂) :
    QueryBoundedAboveBy (oa >>= f) (n₁ + n₂) :=
  pathwiseCostAtMost_bind h₁ h₂

lemma queryBoundedBelowBy_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryBoundedBelowBy oa n₁) (h₂ : ∀ a, QueryBoundedBelowBy (f a) n₂) :
    QueryBoundedBelowBy (oa >>= f) (n₁ + n₂) :=
  pathwiseCostAtLeast_bind h₁ h₂

lemma queryBoundedAboveBy_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryBoundedAboveBy (f i) k) :
    QueryBoundedAboveBy (Fin.mOfFn n f) (n * k) :=
  pathwiseCostAtMost_fin_mOfFn h

lemma queryBoundedBelowBy_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryBoundedBelowBy (f i) k) :
    QueryBoundedBelowBy (Fin.mOfFn n f) (n * k) :=
  pathwiseCostAtLeast_fin_mOfFn h

lemma queryCostExactly_pure [LawfulMonad m] (x : α) :
    QueryCostExactly (pure x : AddWriterT ℕ m α) 0 :=
  pathwiseCostEqOnSupport_pure (m := m) (ω := ℕ) x

lemma queryCostExactly_monadLift [LawfulMonad m] (x : m α) :
    QueryCostExactly (monadLift x : AddWriterT ℕ m α) 0 :=
  pathwiseCostEqOnSupport_monadLift (m := m) (ω := ℕ) x

lemma queryCostExactly_addTell [LawfulMonad m] (w : ℕ) :
    QueryCostExactly (AddWriterT.addTell (M := m) w) w :=
  pathwiseCostEqOnSupport_addTell (m := m) w

lemma queryCostExactly_map [LawfulMonad m] {oa : AddWriterT ℕ m α} {n : ℕ}
    (f : α → β) (h : QueryCostExactly oa n) :
    QueryCostExactly (f <$> oa) n :=
  pathwiseCostEqOnSupport_map f h

lemma queryCostExactly_bind [LawfulMonad m]
    {oa : AddWriterT ℕ m α} {f : α → AddWriterT ℕ m β} {n₁ n₂ : ℕ}
    (h₁ : QueryCostExactly oa n₁) (h₂ : ∀ a, QueryCostExactly (f a) n₂) :
    QueryCostExactly (oa >>= f) (n₁ + n₂) :=
  pathwiseCostEqOnSupport_bind h₁ h₂

lemma queryCostExactly_fin_mOfFn [LawfulMonad m] {n k : ℕ}
    {f : Fin n → AddWriterT ℕ m α} (h : ∀ i, QueryCostExactly (f i) k) :
    QueryCostExactly (Fin.mOfFn n f) (n * k) :=
  ⟨queryBoundedAboveBy_fin_mOfFn (fun i ↦ (h i).toAbove),
    queryBoundedBelowBy_fin_mOfFn (fun i ↦ (h i).toBelow)⟩

end unitCostBounds

section expectedUnitCost

variable [Monad m] [MonadAttach m] [ExactMonadAttach m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]

lemma expectedCostNat_le_of_queryBoundedAboveBy
    {oa : AddWriterT ℕ m α} {n : ℕ}
    (h : QueryBoundedAboveBy oa n) :
    expectedCostNat oa ≤ n := by
  simpa using expectedCost_le_of_pathwiseCostAtMost
    (oa := oa) (val := fun k ↦ (k : ENNReal)) h Nat.mono_cast Measurable.of_discrete

lemma le_expectedCostNat_of_queryBoundedBelowBy
    {oa : AddWriterT ℕ m α} [MeasureTheory.IsProbabilityMeasure 𝒟[oa.costs]] {n : ℕ}
    (h : QueryBoundedBelowBy oa n) :
    (n : ENNReal) ≤ expectedCostNat oa :=
  le_expectedCost_of_pathwiseCostAtLeast h Nat.mono_cast Measurable.of_discrete

lemma expectedCostNat_eq_of_queryCostExactly
    {oa : AddWriterT ℕ m α} [MeasureTheory.IsProbabilityMeasure 𝒟[oa.costs]] {n : ℕ}
    (h : QueryCostExactly oa n) :
    expectedCostNat oa = n :=
  le_antisymm
    (expectedCostNat_le_of_queryBoundedAboveBy h.toAbove)
    (le_expectedCostNat_of_queryBoundedBelowBy h.toBelow)

end expectedUnitCost

end AddWriterT

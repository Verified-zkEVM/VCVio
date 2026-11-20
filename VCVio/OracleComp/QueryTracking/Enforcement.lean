/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.ProbabilityNotation
public import PolyFun.PFunctor.Handler.Charge
public import VCVio.OracleComp.QueryTracking.ObservationOracle
public import VCVio.OracleComp.QueryTracking.WriterCost
public import Mathlib.Algebra.Order.Monoid.Prod
import VCVio.OracleComp.SimSemantics.StateT.UntilBad
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Enforcement Oracle

Oracle wrapper that enforces a query budget by silently dropping queries beyond
the budget. This implements EasyCrypt's `Enforce`/`Bounder` pattern.

`QueryImpl.guardQueryBudget` enforces cumulative additive cost with an absorbing abort flag.
It checks the complete proposed cost before delegation and freezes state after overflow.
Its laws retain full output, cache, accepted cost and abort observations.

## Main Definitions

- `enforceOracle`: Oracle that tracks remaining budget via `StateT` and returns
  `default` for queries exceeding the budget.

## Main Results

- `enforceOracle.run_simulateQ_sub_eq`: Enforcement is PolyFun's budget gate with fallback,
  `PFunctor.Handler.withBudgetOr`, for that charge and the same `default` fallback. Enforcement
  keeps the remaining budget `qb - spent` as state where `withBudgetOr` keeps the amount spent.
- `enforceOracle.fst_map_run_simulateQ`: Enforcement is transparent for computations
  within their query bound (`PFunctor.Handler.run_liftM_withBudgetOr_of_isChargeBound`).
-/

@[expose] public section

open OracleSpec OracleComp

universe u

open scoped OracleSpec.PrimitiveQuery

variable {ι : Type u} {spec : OracleSpec ι} {α : Type u}

/-- Enforcement oracle: wraps the original oracle with a per-index budget tracked via `StateT`.
When the remaining budget for the queried oracle is positive, the query is forwarded and
the budget decremented. When the budget is exhausted, `default` is returned silently. -/
def OracleSpec.enforceOracle [DecidableEq ι] [∀ t, Inhabited (spec.Range t)] :
    QueryImpl spec (StateT (ι → ℕ) (OracleComp spec)) :=
  fun t => StateT.mk fun budget =>
    if 0 < budget t then
      (·, Function.update budget t (budget t - 1)) <$> liftM (query t)
    else
      pure (default, budget)

namespace enforceOracle

variable [DecidableEq ι] [∀ t, Inhabited (spec.Range t)]

@[simp]
lemma run_apply (t : ι) (budget : ι → ℕ) :
    (spec.enforceOracle t).run budget =
      if 0 < budget t then
        (·, Function.update budget t (budget t - 1)) <$> liftM (query t)
      else
        pure (default, budget) := rfl

/-- **Remaining and spent budgets.** Enforcement from the remaining budget `qb - spent` is
PolyFun's budget gate with fallback from the amount `spent`, charging `Pi.single t 1` for a query
at `t` against the budget `qb` and answering `default` past it, with the final state read back as
the remaining budget. The correspondence needs `spent ≤ qb`: the gate compares every index, while
enforcement checks only the queried one. -/
theorem run_simulateQ_sub_eq [DecidableLE (ι → ℕ)] (oa : OracleComp spec α)
    {qb spent : ι → ℕ} (hspent : spent ≤ qb) :
    (simulateQ spec.enforceOracle oa).run (qb - spent) =
      Prod.map id (qb - ·) <$> (simulateQ (PFunctor.Handler.withBudgetOr (P := spec.toPFunctor)
        (QueryImpl.ofLift spec (OracleComp spec)) (fun t => Pi.single t 1) qb
        (fun _ => default)) oa).run spent := by
  induction oa using OracleComp.inductionOn generalizing spent with
  | pure x => simp
  | query_bind t mx ih =>
    rw [run_simulateQ_query_bind, run_simulateQ_query_bind, run_apply]
    by_cases h : spent + Pi.single t 1 ≤ qb
    · have hpos : 0 < (qb - spent) t := by
        have := h t
        simp at this ⊢
        omega
      have hupd : Function.update (qb - spent) t ((qb - spent) t - 1) =
          qb - (spent + Pi.single t 1) := by
        funext j
        by_cases hj : j = t
        · subst hj; simp; omega
        · simp [hj]
      simp only [ite_eq_left hpos, ite_eq_left h, PFunctor.Handler.withBudgetOr, StateT.run, hupd,
        bind_map_left, map_bind]
      exact bind_congr fun u => ih u h
    · have hpos : ¬ 0 < (qb - spent) t := by
        refine fun hlt => h fun j => ?_
        by_cases hj : j = t
        · subst hj; simp at hlt ⊢; omega
        · simpa [Pi.single_apply, hj] using hspent j
      simp only [ite_eq_right hpos, ite_eq_right h, PFunctor.Handler.withBudgetOr, StateT.run,
        pure_bind]
      exact ih default hspent

/-- When the computation is within its query bound, enforcement is transparent:
the output distribution is identical to running without enforcement. -/
theorem fst_map_run_simulateQ {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) :
    Prod.fst <$> (simulateQ enforceOracle oa).run qb = oa := by
  classical
  have hrun := run_simulateQ_sub_eq oa (qb := qb) (spent := 0) zero_le
  rw [tsub_zero] at hrun
  rw [hrun, Functor.map_map,
    show (fun z : α × (ι → ℕ) => (Prod.map id (qb - ·) z).1) = Prod.fst from rfl, simulateQ,
    PFunctor.Handler.run_liftM_withBudgetOr_of_isChargeBound _ _ _
      ((isPerIndexQueryBound_iff_isChargeBound oa qb).1 h),
    PFunctor.Handler.fst_map_run_liftM_withCharge]
  exact simulateQ_ofLift_eq_self oa

section Probability

variable {ι : Type} {spec : OracleSpec ι} {α : Type} [DecidableEq ι]
  [AnswerMeasure spec]

/-- A structural query bound makes its budget check redundant in the counting event. -/
theorem prEvent_counting_budget_eq {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr{let z ← countingOracle.simulate oa 0}[p z.1 ∧ z.2 ≤ qb] =
      Pr{let x ← oa}[p x] := by
  rw [prEvent_congr_of_support (countingOracle.simulate oa 0)
    (fun z => p z.1 ∧ z.2 ≤ qb) (fun z => p z.1)
    (fun z hz => and_iff_left (h.counting_bounded hz))]
  have hproj : Prod.fst <$> countingOracle.simulate oa 0 = oa := by
    simp [countingOracle.simulate]
  exact (prEvent_map (m := OracleComp spec) (countingOracle.simulate oa 0)
    Prod.fst p).symm.trans
      (congrArg (fun comp : OracleComp spec α => Pr{let x ← comp}[p x]) hproj)

variable [∀ t, Inhabited (spec.Range t)]

/-- Under a structural query bound, the counting event agrees with the enforcement event. -/
theorem prEvent_counting_budget_eq_enforce {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr{let z ← countingOracle.simulate oa 0}[p z.1 ∧ z.2 ≤ qb] =
      Pr{let x ← Prod.fst <$> (simulateQ enforceOracle oa).run qb}[p x] := by
  rw [fst_map_run_simulateQ h]
  exact prEvent_counting_budget_eq h p

/-- Structural boundedness implies the counting-to-enforcement event inequality. -/
theorem prEvent_counting_budget_le_enforce {oa : OracleComp spec α} {qb : ι → ℕ}
    (h : IsPerIndexQueryBound oa qb) (p : α → Prop) :
    Pr{let z ← countingOracle.simulate oa 0}[p z.1 ∧ z.2 ≤ qb] ≤
      Pr{let x ← Prod.fst <$> (simulateQ enforceOracle oa).run qb}[p x] := by
  rw [prEvent_counting_budget_eq_enforce h p]

end Probability

end enforceOracle


/-! ## Absorbing weighted query budgets -/

namespace QueryImpl

universe v

/-- Admit a query when its proposed accumulated cost fits the cap. Overflow freezes the
physical state and accepted cost, and makes all subsequent requests return the supplied fallback. -/
def guardQueryBudget
    {ι Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [Add C] [LE C] [DecidableLE C]
    {m : Type → Type v} [Monad m]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache m))
    (fallback : (input : spec.Domain) → spec.Range input) :
    QueryImpl spec (StateT (Cache × (C × Bool)) m) :=
  fun input => StateT.mk fun state =>
    if state.2.2 then pure (fallback input, state)
    else
      let proposed := state.2.1 + cost input
      if proposed ≤ caps then
        (fun result => (result.1, (result.2, (proposed, false)))) <$>
          (handler input).run state.1
      else pure (fallback input, (state.1, (state.2.1, true)))


/-- Every supported guarded execution respects its accumulated cost cap. -/
theorem guardQueryBudget_counts_le_caps
    {ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input)
    (program : OracleComp spec α) (initial : Cache)
    (result : α × (Cache × (C × Bool)))
    (hresult : result ∈ support
      ((simulateQ (guardQueryBudget caps cost handler fallback) program).run
        (initial, (0, false)))) :
    result.2.2.1 ≤ caps := by
  let P : Cache × (C × Bool) → Prop :=
    fun state => state.2.1 ≤ caps
  have hinv : PreservesInv (guardQueryBudget caps cost handler fallback) P := by
    intro input state hs result hr
    simp only [guardQueryBudget, StateT.run_mk] at hr
    split_ifs at hr with hflag hcap
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst result
      exact hs
    · rw [support_map] at hr
      obtain ⟨out, _, rfl⟩ := hr
      exact hcap
    · simp only [support_pure, Set.mem_singleton_iff] at hr
      subst result
      exact hs
  exact simulateQ_run_preservesInv _ P hinv program _ (by simp [P]) result hresult

private def sourceCounted {ι Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [Add C] [LE C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp)) :
    QueryImpl spec (StateT (Cache × (C × Bool)) ProbComp) :=
  handler.extendState fun input _ _ _ observed =>
    let proposed := observed.1 + cost input
    (proposed, observed.2 || decide (¬(proposed ≤ caps)))

private theorem source_agrees {ι Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [Add C] [LE C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input) :
    AgreeUntilBad (guardQueryBudget caps cost handler fallback)
      (sourceCounted caps cost handler) (fun state => state.2.2 = true) := by
  apply AgreeUntilBad.of_run_eq_or_bad
  intro input state hgood
  have hf : state.2.2 = false := by cases h : state.2.2 <;> simp_all
  by_cases hc : state.2.1 + cost input ≤ caps
  · left
    simp [guardQueryBudget, sourceCounted, extendState_apply, hf, hc]
  · right
    constructor
    · intro result hr
      have heq : result = (fallback input, (state.1, (state.2.1, true))) := by
        simpa [guardQueryBudget, hf, hc] using hr
      rw [heq]
    · intro result hr
      unfold sourceCounted at hr
      rw [mem_support_extendState_run_iff] at hr
      have heq := congrArg Prod.snd hr.2
      have hb : decide (¬(state.2.1 + cost input ≤ caps)) = true := by
        simpa only [decide_eq_true_eq] using hc
      simpa only [hf, hb, Bool.false_or] using heq

private theorem source_bad_persists {ι Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [Add C] [LE C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input) :
    PreservesInv (guardQueryBudget caps cost handler fallback)
      (fun state => state.2.2 = true) ∧
    PreservesInv (sourceCounted caps cost handler) (fun state => state.2.2 = true) := by
  constructor
  · intro input state hs result hr
    have heq : result = (fallback input, state) := by
      simpa [guardQueryBudget, hs] using hr
    rw [heq]
    exact hs
  · intro input state hs result hr
    unfold sourceCounted at hr
    rw [mem_support_extendState_run_iff] at hr
    have equality := congrArg Prod.snd hr.2
    simpa [hs] using equality

private theorem source_bad_counts {ι Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp)) :
    PreservesInv (sourceCounted caps cost handler)
      (fun state => state.2.2 = true → ¬(state.2.1 ≤ caps)) := by
  intro input state hs result hr
  unfold sourceCounted at hr
  rw [mem_support_extendState_run_iff] at hr
  rw [hr.2]
  intro hflag hcap
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hflag
  rcases hflag with hold | hnew
  · apply hs hold
    exact le_self_add.trans hcap
  · exact hnew hcap

private theorem source_run_cost {ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [LE C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (program : OracleComp spec α) (cache : Cache) (counts : C) (flag : Bool) :
    (fun result => ((result.1, result.2.2.1), result.2.1)) <$>
      (simulateQ (sourceCounted caps cost handler) program).run (cache, (counts, flag)) =
      (fun result => ((result.1.1, counts + result.1.2), result.2)) <$>
        ((simulateQ (handler.withAddCost cost) program).runAdd).run cache := by
  induction program using OracleComp.inductionOn generalizing cache counts flag with
  | pure value => simp
  | query_bind input next ih =>
    suffices h :
        ((handler input).run cache >>= fun result =>
          (fun out => ((out.1, out.2.2.1), out.2.1)) <$>
            (simulateQ (sourceCounted caps cost handler) (next result.1)).run
              (result.2, (counts + cost input,
                flag || decide (¬(counts + cost input ≤ caps))))) =
        ((handler input).run cache >>= fun result =>
          (fun out => ((out.1.1, counts + (cost input + out.1.2)), out.2)) <$>
            ((simulateQ (handler.withAddCost cost) (next result.1)).runAdd).run result.2) by
      simpa [sourceCounted, extendState_apply, withAddCost_apply, AddWriterT.runAdd_bind,
        StateT.run_bind, map_bind, monad_norm] using h
    apply bind_congr
    rintro ⟨answer, nextCache⟩
    simpa only [add_assoc] using ih answer nextCache (counts + cost input)
      (flag || decide (¬(counts + cost input ≤ caps)))

/-- Under the actual mixed-source cap, the guarded execution preserves the complete joint law. -/
theorem evalDist_guardQueryBudget_eq_of_ae_caps
    {ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input)
    (program : OracleComp spec α) (initial : ProbComp Cache)
    (hcap : Pr{let result ←
      (initial >>= fun cache =>
        ((simulateQ (handler.withAddCost cost) program).runAdd).run
          cache)}[result.1.2 ≤ caps] = 1) :
    let source := do
      let cache ← initial
      ((simulateQ (handler.withAddCost cost) program).runAdd).run cache
    let guarded := do
      let cache ← initial
      (simulateQ (guardQueryBudget caps cost handler fallback) program).run
        (cache, (0, false))
    letI : MeasurableSpace (Option α × (Cache × (C × Bool))) := ⊤
    𝒟[(fun result =>
      (if result.2.2.2 then none else some result.1, result.2)) <$> guarded] =
      𝒟[(fun result =>
        (some result.1.1, (result.2, (result.1.2, false)))) <$> source] := by
  dsimp only
  let : MeasurableSpace (Option α × (Cache × (C × Bool))) := ⊤
  let sourceRun := fun cache =>
    (simulateQ (sourceCounted caps cost handler) program).run (cache, ((0 : C), false))
  let guardedRun := fun cache =>
    (simulateQ (guardQueryBudget caps cost handler fallback) program).run
      (cache, ((0 : C), false))
  let observedRun := fun cache =>
    ((simulateQ (handler.withAddCost cost) program).runAdd).run cache
  let final := fun result : α × (Cache × (C × Bool)) =>
    (if result.2.2.2 then none else some result.1, result.2)
  let tagged := fun result : (α × C) × Cache =>
    (some result.1.1, (result.2, (result.1.2, false)))
  let project := fun result : α × (Cache × (C × Bool)) =>
    ((result.1, result.2.2.1), result.2.1)
  let restore := fun result : (α × C) × Cache =>
    (some result.1.1, (result.2, (result.1.2, false)))
  have hbound := (prEvent_eq_one_iff _ _).mp hcap
  have hsame := source_agrees caps cost handler fallback
  obtain ⟨hguardBad, hsourceBad⟩ := source_bad_persists caps cost handler fallback
  have hlocal : ∀ cache ∈ support initial,
      final <$> guardedRun cache =ᵈ tagged <$> observedRun cache := by
    intro cache hcache
    have hcost : project <$> sourceRun cache =
        (fun result => ((result.1.1, result.1.2), result.2)) <$>
          observedRun cache := by
      simpa only [project, sourceRun, observedRun,
        zero_add] using
        source_run_cost caps cost handler program cache (0 : C) false
    have hgood : ∀ result ∈ support (sourceRun cache), result.2.2.2 ≠ true := by
      intro result hresult hbad
      have hproj : project result ∈ support (project <$> sourceRun cache) := by
        rw [support_map]
        exact ⟨result, hresult, rfl⟩
      rw [hcost, support_map] at hproj
      obtain ⟨value, hvalue, heq⟩ := hproj
      have hvalueBound := hbound value
        ((MonadAttach.mem_support_bind).mpr ⟨cache, hcache, hvalue⟩)
      have hcounts : result.2.2.1 ≤ caps := by
        have heqCounts := congrArg (fun out => out.1.2) heq
        change value.1.2 = result.2.2.1 at heqCounts
        rw [heqCounts] at hvalueBound
        exact hvalueBound
      exact simulateQ_run_preservesInv _ _ (source_bad_counts caps cost handler)
        program (cache, ((0 : C), false)) (by simp) result hresult hbad hcounts
    have hz : Pr{let result ← sourceRun cache}[result.2.2.2 = true] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ hgood
    have hgzero : Pr{let result ← guardedRun cache}[result.2.2.2 = true] = 0 :=
      (hsame.prEvent_simulateQ_run_bad_eq hguardBad hsourceBad program
        (cache, ((0 : C), false))).trans hz
    have hggood := (prEvent_eq_zero_iff _ _).mp hgzero
    have hraw : guardedRun cache =ᵈ sourceRun cache := by
      apply EvalDistEq.of_forall_prEvent_eq
      intro predicate
      calc
        _ = Pr{let result ← guardedRun cache}[predicate result ∧ result.2.2.2 ≠ true] :=
          prEvent_congr_of_support _ _ _ fun result hr =>
            (and_iff_left (hggood result hr)).symm
        _ = Pr{let result ← sourceRun cache}[predicate result ∧ result.2.2.2 ≠ true] :=
          hsame.prEvent_simulateQ_run_and_not_bad_eq hguardBad hsourceBad program
            (cache, ((0 : C), false)) predicate
        _ = _ := prEvent_congr_of_support _ _ _ fun result hr =>
          and_iff_left (hgood result hr)
    refine (hraw.map final).trans ?_
    apply EvalDistEq.of_forall_prEvent_eq
    intro predicate
    rw [prEvent_map, prEvent_map]
    have hfinal : Pr{let result ← sourceRun cache}[predicate (final result)] =
        Pr{let result ← sourceRun cache}[predicate (restore (project result))] := by
      apply prEvent_congr_of_support
      intro result hr
      rcases result with ⟨value, cache', counts, flag⟩
      have hf : flag = false := Bool.eq_false_iff.mpr (hgood _ hr)
      subst flag
      rfl
    rw [hfinal]
    have hproject := congrArg (fun computation =>
      Pr{let result ← computation}[predicate (restore result)]) hcost
    simpa only [prEvent_map, restore, tagged] using hproject
  change 𝒟[final <$> (initial >>= guardedRun)] = 𝒟[tagged <$> (initial >>= observedRun)]
  rw [map_bind, map_bind]
  exact evalDist_bind_congr_of_support initial _ _ fun cache hcache =>
    (hlocal cache hcache).evalDist_eq


/-! ## Event-restricted preservation -/

private theorem source_not_aborted_iff_caps
    {ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (program : OracleComp spec α) (cache : Cache)
    (result : α × (Cache × (C × Bool)))
    (hr : result ∈ support ((simulateQ (sourceCounted caps cost handler) program).run
      (cache, ((0 : C), false)))) :
    result.2.2.2 = false ↔ result.2.2.1 ≤ caps := by
  have hgood : PreservesInv (sourceCounted caps cost handler)
      (fun state => state.2.2 = false →
        state.2.1 ≤ caps) := by
    intro input state _ next hnext
    unfold sourceCounted at hnext
    rw [mem_support_extendState_run_iff] at hnext
    rw [hnext.2]
    intro hf
    by_contra hc
    have hd : decide (¬(state.2.1 + cost input ≤ caps)) = true := by
      simpa only [decide_eq_true_eq] using hc
    change (state.2.2 || decide (¬(state.2.1 + cost input ≤ caps))) = false at hf
    rw [hd] at hf
    simp at hf
  constructor
  · exact simulateQ_run_preservesInv _ _ hgood program
      (cache, ((0 : C), false)) (by simp) result hr
  · intro hc
    apply Bool.eq_false_iff.mpr
    intro hf
    exact simulateQ_run_preservesInv _ _ (source_bad_counts caps cost handler)
      program (cache, ((0 : C), false)) (by simp) result hr hf hc

/-- Non-aborted guarded events equal counted source events restricted to the final caps. -/
theorem prEvent_guardQueryBudget_and_not_aborted_eq_source_and_caps
    {ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input)
    (program : OracleComp spec α) (initial : ProbComp Cache)
    (event : (α × C) × Cache → Prop) :
    Pr{let result ← (do
      let cache ← initial
      (simulateQ (guardQueryBudget caps cost handler fallback) program).run
        (cache, (0, false)))}[
      event ((result.1, result.2.2.1), result.2.1) ∧ result.2.2.2 = false] =
    Pr{let result ← (do
      let cache ← initial
      ((simulateQ (handler.withAddCost cost) program).runAdd).run cache)}[
      event result ∧ result.1.2 ≤ caps] := by
  let project : α × (Cache × (C × Bool)) → (α × C) × Cache :=
    fun result => ((result.1, result.2.2.1), result.2.1)
  let sourceRun := fun cache =>
    (simulateQ (sourceCounted caps cost handler) program).run (cache, ((0 : C), false))
  let guardedRun := fun cache =>
    (simulateQ (guardQueryBudget caps cost handler fallback) program).run
      (cache, ((0 : C), false))
  let countedRun := fun cache =>
    ((simulateQ (handler.withAddCost cost) program).runAdd).run cache
  have hsame := source_agrees caps cost handler fallback
  obtain ⟨hguardBad, hsourceBad⟩ := source_bad_persists caps cost handler fallback
  have hlocal : ∀ cache,
      Pr{let result ← guardedRun cache}[event (project result) ∧ result.2.2.2 = false] =
      Pr{let result ← countedRun cache}[
        event result ∧ result.1.2 ≤ caps] := by
    intro cache
    have hcost : project <$> sourceRun cache =
        (fun result => ((result.1.1, result.1.2), result.2)) <$> countedRun cache := by
      simpa only [project, sourceRun, countedRun,
        zero_add] using
        source_run_cost caps cost handler program cache (0 : C) false
    calc
      _ = Pr{let result ← guardedRun cache}[
          event (project result) ∧ result.2.2.2 ≠ true] := by
        apply prEvent_congr
        intro result
        exact and_congr_right fun _ => Bool.eq_false_iff
      _ = Pr{let result ← sourceRun cache}[
          event (project result) ∧ result.2.2.2 ≠ true] :=
        hsame.prEvent_simulateQ_run_and_not_bad_eq hguardBad hsourceBad program
          (cache, ((0 : C), false)) (fun result => event (project result))
      _ = Pr{let result ← sourceRun cache}[
          event (project result) ∧ result.2.2.1 ≤ caps] := by
        apply prEvent_congr_of_support
        intro result hr
        exact and_congr_right fun _ => Bool.eq_false_iff.symm.trans
          (source_not_aborted_iff_caps caps cost handler program cache result hr)
      _ = _ := by
        have hproject := congrArg (fun computation =>
          Pr{let result ← computation}[
            event result ∧ result.1.2 ≤ caps]) hcost
        simpa only [prEvent_map, project] using hproject
  change prEvent ((fun result => event (project result) ∧ result.2.2.2 = false) <$>
      (initial >>= guardedRun)) =
    prEvent ((fun result => event result ∧ result.1.2 ≤ caps) <$>
      (initial >>= countedRun))
  rw [map_bind, map_bind]
  exact prEvent_bind_congr_of_support initial _ _ fun cache _ => hlocal cache

/-! ### Sampled source prefixes -/

/-- A sampled prefix retains the joint seed, output, cost and cache in capped source events. -/
theorem prEvent_bind_guardQueryBudget_and_not_aborted_eq_source_and_caps
    {Seed ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (seedSampler : ProbComp Seed) (caps : Seed → C) (cost : Seed → spec.Domain → C)
    (handler : Seed → QueryImpl spec (StateT Cache ProbComp))
    (fallback : (seed : Seed) → (input : spec.Domain) → spec.Range input)
    (program : Seed → OracleComp spec α) (initial : Seed → ProbComp Cache)
    (event : Seed → (α × C) × Cache → Prop) :
    let guarded : ProbComp (Seed × (α × (Cache × (C × Bool)))) := do
      let seed ← seedSampler
      let cache ← initial seed
      let result ← (simulateQ (guardQueryBudget (caps seed) (cost seed)
        (handler seed) (fallback seed)) (program seed)).run (cache, (0, false))
      pure (seed, result)
    let source : ProbComp (Seed × ((α × C) × Cache)) := do
      let seed ← seedSampler
      let cache ← initial seed
      let result ← ((simulateQ ((handler seed).withAddCost (cost seed))
        (program seed)).runAdd).run cache
      pure (seed, result)
    Pr{let out ← guarded}[
      event out.1 ((out.2.1, out.2.2.2.1), out.2.2.1) ∧ out.2.2.2.2 = false] =
      Pr{let out ← source}[event out.1 out.2 ∧ out.2.1.2 ≤ caps out.1] := by
  dsimp only
  simp only [map_bind, bind_pure_comp, Functor.map_map]
  apply prEvent_bind_congr_of_support seedSampler
  intro seed _
  simpa only [map_bind, bind_pure_comp, Functor.map_map, Function.comp_def, map_pure] using
    prEvent_guardQueryBudget_and_not_aborted_eq_source_and_caps
      (caps seed) (cost seed) (handler seed) (fallback seed)
      (program seed) (initial seed) (event seed)

/-- One global source event-to-cap law suffices after an arbitrary sampled prefix.

The cap is required only when the source event holds; other source branches may exceed it.
-/
theorem prEvent_bind_guardQueryBudget_and_not_aborted_eq_source_of_ae_event_caps
    {Seed ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [AddMonoid C] [Preorder C] [CanonicallyOrderedAdd C] [DecidableLE C]
    (seedSampler : ProbComp Seed) (caps : Seed → C) (cost : Seed → spec.Domain → C)
    (handler : Seed → QueryImpl spec (StateT Cache ProbComp))
    (fallback : (seed : Seed) → (input : spec.Domain) → spec.Range input)
    (program : Seed → OracleComp spec α) (initial : Seed → ProbComp Cache)
    (event : Seed → (α × C) × Cache → Prop) :
    let source : ProbComp (Seed × ((α × C) × Cache)) := do
      let seed ← seedSampler
      let cache ← initial seed
      let result ← ((simulateQ ((handler seed).withAddCost (cost seed))
        (program seed)).runAdd).run cache
      pure (seed, result)
    Pr{let out ← source}[event out.1 out.2 → out.2.1.2 ≤ caps out.1] = 1 →
    let guarded : ProbComp (Seed × (α × (Cache × (C × Bool)))) := do
      let seed ← seedSampler
      let cache ← initial seed
      let result ← (simulateQ (guardQueryBudget (caps seed) (cost seed)
        (handler seed) (fallback seed)) (program seed)).run (cache, (0, false))
      pure (seed, result)
    Pr{let out ← guarded}[
      event out.1 ((out.2.1, out.2.2.2.1), out.2.2.1) ∧ out.2.2.2.2 = false] =
      Pr{let out ← source}[event out.1 out.2] := by
  dsimp only
  intro hcaps
  rw [prEvent_bind_guardQueryBudget_and_not_aborted_eq_source_and_caps
    seedSampler caps cost handler fallback program initial event]
  apply prEvent_congr_of_support
  intro out hout
  exact ⟨And.left, fun hevent =>
    ⟨hevent, (prEvent_eq_one_iff _ _).mp hcaps out hout hevent⟩⟩

/-- Interpreting the free guarded program preserves the complete guarded state and output. -/
theorem map_run_simulateQ_guardQueryBudget_free_eq
    {ι α Cache C : Type} {spec : OracleSpec.{0, 0} ι}
    [Add C] [LE C] [DecidableLE C]
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    (caps : C) (cost : spec.Domain → C)
    (handler : QueryImpl spec (StateT Cache m))
    (fallback : (input : spec.Domain) → spec.Range input)
    (program : OracleComp spec α)
    (initialCache : Cache) (initialCounts : C) (initialAborted : Bool) :
    let forwarder : QueryImpl spec (StateT PUnit (OracleComp spec)) :=
      (QueryImpl.id' spec).liftTarget (StateT PUnit (OracleComp spec))
    let freeGuarded : OracleComp spec (α × (PUnit × (C × Bool))) :=
      (simulateQ (guardQueryBudget caps cost forwarder fallback) program).run
        (PUnit.unit, (initialCounts, initialAborted))
    (fun result : (α × (PUnit × (C × Bool))) × Cache =>
      (result.1.1, (result.2, result.1.2.2))) <$>
      (simulateQ handler freeGuarded).run initialCache =
        (simulateQ (guardQueryBudget caps cost handler fallback) program).run
          (initialCache, (initialCounts, initialAborted)) := by
  dsimp only
  let forwarder : QueryImpl spec (StateT PUnit (OracleComp spec)) :=
    (QueryImpl.id' spec).liftTarget (StateT PUnit (OracleComp spec))
  let inner := guardQueryBudget caps cost forwarder fallback
  let project : ((PUnit × (C × Bool)) × Cache) →
      Cache × (C × Bool) := fun state => (state.2, state.1.2)
  have hstep : ∀ input state,
      Prod.map id project <$>
        (((handler.mapStateTBase inner).flattenStateT input).run state) =
        (guardQueryBudget caps cost handler fallback input).run (project state) := by
    intro input state
    rcases state with ⟨⟨token, counts, flag⟩, cache⟩
    cases flag with
    | false =>
      by_cases hcap : counts + cost input ≤ caps
      · simp [flattenStateT_mapStateTBase_apply_run, inner, guardQueryBudget, project,
          hcap, forwarder, id'_apply, Functor.map_map]
      · simp [flattenStateT_mapStateTBase_apply_run, inner, guardQueryBudget, project, hcap]
    | true =>
      simp [flattenStateT_mapStateTBase_apply_run, inner, guardQueryBudget, project]
  have hfold := map_run_simulateQ_eq_of_query_map_eq
    (handler.mapStateTBase inner).flattenStateT
    (guardQueryBudget caps cost handler fallback) project hstep program
    ((PUnit.unit, (initialCounts, initialAborted)), initialCache)
  change (fun result : (α × (PUnit × (C × Bool))) × Cache =>
      (result.1.1, (result.2, result.1.2.2))) <$>
      (simulateQ handler ((simulateQ inner program).run
        (PUnit.unit, (initialCounts, initialAborted)))).run initialCache = _
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have hproject : Prod.map id project =
      (fun result : α × ((PUnit × (C × Bool)) × Cache) =>
        (result.1, (result.2.2, result.2.1.2))) := by
    funext result
    rfl
  rw [hproject] at hfold
  simpa only [Functor.map_map, Function.comp_def] using hfold

/-- Equal weighted steps and coherent fallback commute with the complete guard. -/
theorem guarded_query_transport :
  ∀ {ιa ιb Cache : Type} {specA : OracleSpec.{0, 0} ιa}
    {specB : OracleSpec.{0, 0} ιb} {m : Type → Type} [Monad m] [LawfulMonad m]
    (C : Type) [Add C] [LE C] [DecidableLE C]
    (inputA : specA.Domain) (inputB : specB.Domain)
    (decode : specB.Range inputB → specA.Range inputA)
    (handlerA : QueryImpl specA (StateT Cache m))
    (handlerB : QueryImpl specB (StateT Cache m))
    (fallbackA : (input : specA.Domain) → specA.Range input)
    (fallbackB : (input : specB.Domain) → specB.Range input)
    (costA : specA.Domain → C) (costB : specB.Domain → C)
    (_cost : costA inputA = costB inputB)
    (_step : ∀ state : Cache,
      (handlerA inputA).run state =
        Prod.map decode id <$> (handlerB inputB).run state)
    (_fallback : fallbackA inputA = decode (fallbackB inputB))
    (caps initialCounts : C) (initialAborted : Bool) (initialCache : Cache),
    ((QueryImpl.guardQueryBudget caps costA handlerA fallbackA) inputA).run
        (initialCache, (initialCounts, initialAborted)) =
      Prod.map decode id <$>
        ((QueryImpl.guardQueryBudget caps costB handlerB fallbackB) inputB).run
          (initialCache, (initialCounts, initialAborted)) := by
  intro ιa ιb Cache specA specB m _ _ C _ _ _ inputA inputB decode handlerA handlerB
    fallbackA fallbackB costA costB hcost hstep hfallback caps initialCounts
    initialAborted initialCache
  dsimp only [QueryImpl.guardQueryBudget, StateT.run_mk]
  rw [hcost]
  split_ifs
  · simp only [map_pure, hfallback, Prod.map_apply, id_eq]
  · rw [hstep initialCache]
    simp only [Functor.map_map, Prod.map_apply, Prod.map_fst, Prod.map_snd, id_eq]
  · simp only [map_pure, hfallback, Prod.map_apply, id_eq]

/-- A zero-cost inert observation can be omitted before a zero-cost native query. -/
theorem guarded_inert_observation :
  ∀ {ι Event Cache : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (C : Type) [AddZeroClass C] [LE C] [DecidableLE C]
    (handler : QueryImpl (spec + ObsSpec Event) (StateT Cache m))
    (fallback : (input : (spec + ObsSpec Event).Domain) →
      (spec + ObsSpec Event).Range input)
    (cost : (spec + ObsSpec Event).Domain → C)
    (event : Event) (native : spec.Domain)
    (_markerZero : cost (.inr event) = 0)
    (_nativeZero : cost (.inl native) = 0)
    (caps initialCounts : C) (initialAborted : Bool) (initialCache : Cache)
    (_inert : initialAborted = false → initialCounts ≤ caps →
      (handler (.inr event)).run initialCache = pure (PUnit.unit, initialCache)),
    let guarded := QueryImpl.guardQueryBudget caps cost handler fallback
    (simulateQ guarded (do
      let _ ← (liftM ((spec + ObsSpec Event).query (.inr event)) :
        OracleComp (spec + ObsSpec Event) PUnit)
      (liftM ((spec + ObsSpec Event).query (.inl native)) :
        OracleComp (spec + ObsSpec Event) (spec.Range native)))).run
          (initialCache, (initialCounts, initialAborted)) =
      (guarded (.inl native)).run (initialCache, (initialCounts, initialAborted)) := by
  intro ι Event Cache spec m _ _ C _ _ _ handler fallback cost event native
    hmarkerZero hnativeZero caps initialCounts initialAborted initialCache hinert guarded
  rw [simulateQ_bind, simulateQ_spec_query]
  simp only [StateT.run_bind, simulateQ_spec_query]
  dsimp only [guarded]
  cases initialAborted with
  | true => simp [QueryImpl.guardQueryBudget]
  | false =>
      by_cases fits : initialCounts ≤ caps
      · have marker := hinert rfl fits
        simp [QueryImpl.guardQueryBudget, hmarkerZero, hnativeZero, fits, marker]
      · simp [QueryImpl.guardQueryBudget, hmarkerZero, hnativeZero, fits]

end QueryImpl

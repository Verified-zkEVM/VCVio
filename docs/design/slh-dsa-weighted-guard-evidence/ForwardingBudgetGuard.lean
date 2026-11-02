/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad

/-! # Weighted query-budget guards -/

@[expose] public section

open OracleComp OracleSpec

universe v

namespace QueryImpl

/-- Admit queries within both counter caps and preserve their complete delegated effects.
Overflow sets an absorbing flag and freezes effects; final loss is observed through Option. -/
def guardQueryBudget
    {ι Cache : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type v} [Monad m]
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
    (handler : QueryImpl spec (StateT Cache m))
    (fallback : (input : spec.Domain) → spec.Range input) :
    QueryImpl spec (StateT (Cache × ((Nat × Nat) × Bool)) m) :=
  fun input => StateT.mk fun state =>
    if state.2.2 then pure (fallback input, state)
    else
      let proposed := state.2.1 + cost input
      if proposed.1 ≤ caps.1 ∧ proposed.2 ≤ caps.2 then
        (fun result => (result.1, (result.2, (proposed, false)))) <$>
          (handler input).run state.1
      else pure (fallback input, (state.1, (state.2.1, true)))

/-- Every supported guarded execution respects both declared counter caps. -/
theorem guardQueryBudget_counts_le_caps
    {ι α Cache : Type} {spec : OracleSpec.{0, 0} ι}
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input)
    (program : OracleComp spec α) (initial : Cache)
    (result : α × (Cache × ((Nat × Nat) × Bool)))
    (hresult : result ∈ support
      ((simulateQ (guardQueryBudget caps cost handler fallback) program).run
        (initial, ((0, 0), false)))) :
    result.2.2.1.1 ≤ caps.1 ∧ result.2.2.1.2 ≤ caps.2 := by
  let P : Cache × ((Nat × Nat) × Bool) → Prop :=
    fun state => state.2.1.1 ≤ caps.1 ∧ state.2.1.2 ≤ caps.2
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

private def sourceCounted {ι Cache : Type} {spec : OracleSpec.{0, 0} ι}
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
    (handler : QueryImpl spec (StateT Cache ProbComp)) :
    QueryImpl spec (StateT (Cache × ((Nat × Nat) × Bool)) ProbComp) :=
  handler.extendState fun input _ _ _ observed =>
    let proposed := observed.1 + cost input
    (proposed, observed.2 || decide (¬(proposed.1 ≤ caps.1 ∧ proposed.2 ≤ caps.2)))

private theorem source_agrees {ι Cache : Type} {spec : OracleSpec.{0, 0} ι}
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input) :
    AgreeUntilBad (guardQueryBudget caps cost handler fallback)
      (sourceCounted caps cost handler) (fun state => state.2.2 = true) := by
  apply AgreeUntilBad.of_run_eq_or_bad
  intro input state hgood
  have hf : state.2.2 = false := by cases h : state.2.2 <;> simp_all
  by_cases hc : state.2.1.1 + (cost input).1 ≤ caps.1 ∧
      state.2.1.2 + (cost input).2 ≤ caps.2
  · left
    simp [guardQueryBudget, sourceCounted, extendState_apply, hf, hc.1, hc.2,
      not_lt_of_ge hc.2]
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
      have hb : decide (¬((state.2.1 + cost input).1 ≤ caps.1 ∧
          (state.2.1 + cost input).2 ≤ caps.2)) = true := by
        simpa only [Prod.fst_add, Prod.snd_add, decide_eq_true_eq] using hc
      simpa only [hf, hb, Bool.false_or] using heq

private theorem source_bad_persists {ι Cache : Type} {spec : OracleSpec.{0, 0} ι}
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
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

private theorem source_bad_counts {ι Cache : Type} {spec : OracleSpec.{0, 0} ι}
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
    (handler : QueryImpl spec (StateT Cache ProbComp)) :
    PreservesInv (sourceCounted caps cost handler)
      (fun state => state.2.2 = true → ¬(state.2.1.1 ≤ caps.1 ∧ state.2.1.2 ≤ caps.2)) := by
  intro input state hs result hr
  unfold sourceCounted at hr
  rw [mem_support_extendState_run_iff] at hr
  rw [hr.2]
  intro hflag hcap
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hflag
  rcases hflag with hold | hnew
  · apply hs hold
    exact ⟨(Nat.le_add_right state.2.1.1 (cost input).1).trans hcap.1,
      (Nat.le_add_right state.2.1.2 (cost input).2).trans hcap.2⟩
  · exact hnew hcap

private theorem source_run_cost {ι α Cache : Type} {spec : OracleSpec.{0, 0} ι}
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (program : OracleComp spec α) (cache : Cache) (counts : Nat × Nat) (flag : Bool) :
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
                flag || decide (¬((counts + cost input).1 ≤ caps.1 ∧
                  (counts + cost input).2 ≤ caps.2))))) =
        ((handler input).run cache >>= fun result =>
          (fun out => ((out.1.1, counts + (cost input + out.1.2)), out.2)) <$>
            ((simulateQ (handler.withAddCost cost) (next result.1)).runAdd).run result.2) by
      simpa [sourceCounted, extendState_apply, withAddCost_apply, AddWriterT.runAdd_bind,
        StateT.run_bind, map_bind, monad_norm] using h
    apply bind_congr
    rintro ⟨answer, nextCache⟩
    simpa only [add_assoc] using ih answer nextCache (counts + cost input)
      (flag || decide (¬((counts + cost input).1 ≤ caps.1 ∧
        (counts + cost input).2 ≤ caps.2)))

/-- Under the actual mixed-source cap, the guarded execution preserves the complete joint law. -/
theorem evalDist_guardQueryBudget_eq_of_ae_caps
    {ι α Cache : Type} {spec : OracleSpec.{0, 0} ι}
    (caps : Nat × Nat) (cost : spec.Domain → Nat × Nat)
    (handler : QueryImpl spec (StateT Cache ProbComp))
    (fallback : (input : spec.Domain) → spec.Range input)
    (program : OracleComp spec α) (initial : ProbComp Cache)
    (hcap : Pr{let result ←
      (initial >>= fun cache =>
        ((simulateQ (handler.withAddCost cost) program).runAdd).run
          cache)}[result.1.2.1 ≤ caps.1 ∧ result.1.2.2 ≤ caps.2] = 1) :
    let source := do
      let cache ← initial
      ((simulateQ (handler.withAddCost cost) program).runAdd).run cache
    let guarded := do
      let cache ← initial
      (simulateQ (guardQueryBudget caps cost handler fallback) program).run
        (cache, ((0, 0), false))
    letI : MeasurableSpace (Option α × (Cache × ((Nat × Nat) × Bool))) := ⊤
    𝒟[(fun result =>
      (if result.2.2.2 then none else some result.1, result.2)) <$> guarded] =
      𝒟[(fun result =>
        (some result.1.1, (result.2, (result.1.2, false)))) <$> source]
 := by
  dsimp only
  let : MeasurableSpace (Option α × (Cache × ((Nat × Nat) × Bool))) := ⊤
  let sourceRun := fun cache =>
    (simulateQ (sourceCounted caps cost handler) program).run (cache, ((0, 0), false))
  let guardedRun := fun cache =>
    (simulateQ (guardQueryBudget caps cost handler fallback) program).run
      (cache, ((0, 0), false))
  let observedRun := fun cache =>
    ((simulateQ (handler.withAddCost cost) program).runAdd).run cache
  let final := fun result : α × (Cache × ((Nat × Nat) × Bool)) =>
    (if result.2.2.2 then none else some result.1, result.2)
  let tagged := fun result : (α × (Nat × Nat)) × Cache =>
    (some result.1.1, (result.2, (result.1.2, false)))
  let project := fun result : α × (Cache × ((Nat × Nat) × Bool)) =>
    ((result.1, result.2.2.1), result.2.1)
  let restore := fun result : (α × (Nat × Nat)) × Cache =>
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
        show (0, 0) = (0 : Nat × Nat) from rfl, zero_add] using
        source_run_cost caps cost handler program cache (0, 0) false
    have hgood : ∀ result ∈ support (sourceRun cache), result.2.2.2 ≠ true := by
      intro result hresult hbad
      have hproj : project result ∈ support (project <$> sourceRun cache) := by
        rw [support_map]
        exact ⟨result, hresult, rfl⟩
      rw [hcost, support_map] at hproj
      obtain ⟨value, hvalue, heq⟩ := hproj
      have hvalueBound := hbound value
        ((MonadAttach.mem_support_bind).mpr ⟨cache, hcache, hvalue⟩)
      have hcounts : result.2.2.1.1 ≤ caps.1 ∧ result.2.2.1.2 ≤ caps.2 := by
        have heqCounts := congrArg (fun out => out.1.2) heq
        change value.1.2 = result.2.2.1 at heqCounts
        rw [heqCounts] at hvalueBound
        exact hvalueBound
      exact simulateQ_run_preservesInv _ _ (source_bad_counts caps cost handler)
        program (cache, ((0, 0), false)) (by simp) result hresult hbad hcounts
    have hz : Pr{let result ← sourceRun cache}[result.2.2.2 = true] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ hgood
    have hgzero : Pr{let result ← guardedRun cache}[result.2.2.2 = true] = 0 :=
      (hsame.prEvent_simulateQ_run_bad_eq hguardBad hsourceBad program
        (cache, ((0, 0), false))).trans hz
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
            (cache, ((0, 0), false)) predicate
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


#check @guardQueryBudget
#print axioms guardQueryBudget
#check @guardQueryBudget_counts_le_caps
#print axioms guardQueryBudget_counts_le_caps
#check @evalDist_guardQueryBudget_eq_of_ae_caps
#print axioms evalDist_guardQueryBudget_eq_of_ae_caps

end QueryImpl

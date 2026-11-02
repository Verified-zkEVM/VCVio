/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Weighted cost bounds through oracle substitution

Each source query is implemented by an actual target-oracle program. When every completed run of
that implementation fits the source query's charge, substitution preserves the source program's
weighted bound. Costs may be vectors or any ordered additive commutative monoid.

The support refinement retains the returned value and compares the charges of the two runs. It
does not identify their probability distributions. Bounds concern completed runs only: an
implementation with no completed run satisfies every such bound. Availability and termination
therefore require separate hypotheses where those properties are needed.
-/

public section

open OracleSpec OracleComp

variable {ι κ α ω : Type} {source : OracleSpec ι} {target : OracleSpec κ}
  [AddCommMonoid ω]

/-- A chosen response extends any supported continuation with the query's designated charge. -/
theorem mem_support_costDist_query_bind (query : source.Domain)
    (next : source.Range query → OracleComp source α) (response : source.Range query)
    (cm : CostModel source ω) (result : α × Multiplicative ω)
    (member : result ∈ support (costDist (next response) cm)) :
    (result.1, Multiplicative.ofAdd (cm.queryCost query) * result.2) ∈
      support (costDist ((source.query query : OracleComp source _) >>= next) cm) := by
  rw [costDist_query_bind]
  apply (mem_support_bind_iff _ _ _).mpr
  refine ⟨response, by simp, ?_⟩
  rw [support_map]
  exact ⟨result, member, rfl⟩

section Ordered

variable [Preorder ω] [IsOrderedAddMonoid ω]

/-- Every completed substituted run has a source run with the same result and at least its charge.
The source query charge must bound the entire implementing program, including repeated queries. -/
theorem mem_support_costDist_simulateQ
    (route : QueryImpl source (OracleComp target)) (program : OracleComp source α)
    (sourceCost : CostModel source ω) (targetCost : CostModel target ω)
    (hstep : ∀ query, WorstCaseCostBound (route query) targetCost (sourceCost.queryCost query))
    (result : α × Multiplicative ω)
    (member : result ∈ support (costDist (simulateQ route program) targetCost)) :
    ∃ charge : ω, (result.1, Multiplicative.ofAdd charge) ∈ support (costDist program sourceCost) ∧
      Multiplicative.toAdd result.2 ≤ charge := by
  induction program using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp only [simulateQ_pure, costDist, instrumentedRun, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at member
      subst result
      exact ⟨0, by simp [costDist, instrumentedRun], le_rfl⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, costDist_bind] at member
      rcases (mem_support_bind_iff _ _ _).mp member with ⟨step, stepMember, restMember⟩
      rcases (mem_support_bind_iff _ _ _).mp restMember with ⟨tail, tailMember, finalMember⟩
      rw [mem_support_pure_iff] at finalMember
      subst result
      obtain ⟨charge, sourceMember, htail⟩ := ih step.1 tail tailMember
      refine ⟨sourceCost.queryCost query + charge, ?_,
        add_le_add (hstep query step stepMember) htail⟩
      exact mem_support_costDist_query_bind query next step.1 sourceCost
        (tail.1, Multiplicative.ofAdd charge) sourceMember

/-- A source weighted bound transfers through the same handler programs whose costs are bounded. -/
theorem WorstCaseCostBound.simulateQ
    {program : OracleComp source α} {sourceCost : CostModel source ω}
    {targetCost : CostModel target ω} {budget : ω}
    (hprogram : WorstCaseCostBound program sourceCost budget)
    (route : QueryImpl source (OracleComp target))
    (hstep : ∀ query, WorstCaseCostBound (route query) targetCost (sourceCost.queryCost query)) :
    WorstCaseCostBound (simulateQ route program) targetCost budget := by
  intro result member
  obtain ⟨charge, sourceMember, hcharge⟩ :=
    mem_support_costDist_simulateQ route program sourceCost targetCost hstep result member
  exact hcharge.trans (hprogram _ sourceMember)

end Ordered
